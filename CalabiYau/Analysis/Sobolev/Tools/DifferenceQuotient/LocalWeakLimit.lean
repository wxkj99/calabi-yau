-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Tools/DifferenceQuotient/LocalWeakLimit.lean
-- Locally modified.
module
public import CalabiYau.Mathlib.Geometry.Manifold.PartitionOfUnity.CompactSupport
public import CalabiYau.Analysis.Sobolev.Euclidean.WeakDerivative.Distribution
public import CalabiYau.Analysis.Sobolev.Tools.DifferenceQuotient
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

noncomputable section

open MeasureTheory Metric Filter Topology Set Function Sobolev Sobolev.Euclidean
open scoped ENNReal NNReal Convolution Pointwise BigOperators InnerProductSpace
  RealInnerProductSpace

namespace CalabiYau
namespace Analysis
namespace Sobolev

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

private lemma smoothCompactlySupportedIn_zero_mem (Ω'' : Set E) :
    ContDiff ℝ (⊤ : ℕ∞) (0 : E → ℝ) ∧
      HasCompactSupport (0 : E → ℝ) ∧
      tsupport (0 : E → ℝ) ⊆ Ω'' := by
  refine ⟨contDiff_const, HasCompactSupport.zero, ?_⟩
  have h_support : Function.support (0 : E → ℝ) = ∅ := by
    ext x; simp
  rw [tsupport, h_support, closure_empty]
  exact empty_subset _

private lemma smoothCompactlySupportedIn_add_mem
    {Ω'' : Set E}
    {φ ψ : E → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω'')
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ Ω'') :
    ContDiff ℝ (⊤ : ℕ∞) (φ + ψ) ∧
      HasCompactSupport (φ + ψ) ∧
      tsupport (φ + ψ) ⊆ Ω'' := by
  refine ⟨hφ.1.add hψ.1, hφ.2.1.add hψ.2.1, ?_⟩
  refine subset_trans (tsupport_add (f := φ) (g := ψ)) ?_
  exact union_subset hφ.2.2 hψ.2.2

private lemma smoothCompactlySupportedIn_smul_mem
    {Ω'' : Set E}
    (c : ℝ) {φ : E → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω'') :
    ContDiff ℝ (⊤ : ℕ∞) (c • φ) ∧
      HasCompactSupport (c • φ) ∧
      tsupport (c • φ) ⊆ Ω'' := by
  refine ⟨contDiff_const.smul hφ.1, hφ.2.1.smul_left, ?_⟩
  refine subset_trans ?_ hφ.2.2
  have hsubset : Function.support (c • φ) ⊆ Function.support φ := by
    intro x hx
    rw [Function.mem_support] at hx ⊢
    intro hφx
    apply hx
    change c • φ x = 0
    rw [hφx]; simp
  exact closure_mono hsubset

variable [NeZero d] in
private def smoothCompactlySupportedInSubmodule (Ω'' : Set E) : Submodule ℝ (E → ℝ) where
  carrier := {φ | ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
    tsupport φ ⊆ Ω''}
  add_mem' := fun hφ hψ => smoothCompactlySupportedIn_add_mem (Ω'' := Ω'') hφ hψ
  zero_mem' := smoothCompactlySupportedIn_zero_mem (Ω'' := Ω'')
  smul_mem' := fun c _ hφ => smoothCompactlySupportedIn_smul_mem (Ω'' := Ω'') c hφ

@[simp] private lemma mem_smoothCompactlySupportedInSubmodule {Ω'' : Set E} {φ : E → ℝ} :
    φ ∈ (smoothCompactlySupportedInSubmodule (d := d) Ω'') ↔
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω'' :=
  Iff.rfl

private lemma memLp_two_restrict_of_smoothCompactlySupported
    {Ω'' : Set E}
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_support : HasCompactSupport φ) :
    MemLp φ 2 ((volume : Measure E).restrict Ω'') :=
  (hφ.continuous.memLp_of_hasCompactSupport hφ_support).restrict _

variable [NeZero d] in
private def smoothCompactlySupportedInToLp (Ω'' : Set E) :
    smoothCompactlySupportedInSubmodule (d := d) Ω'' →ₗ[ℝ]
      Lp ℝ 2 ((volume : Measure E).restrict Ω'') where
  toFun φ :=
    (memLp_two_restrict_of_smoothCompactlySupported (d := d) (Ω'' := Ω'') φ.2.1 φ.2.2.1).toLp φ.1
  map_add' φ ψ := by
    refine Lp.ext ?_
    have h1 : ⇑((memLp_two_restrict_of_smoothCompactlySupported (d := d)
        (Ω'' := Ω'') (φ + ψ).2.1 (φ + ψ).2.2.1).toLp ((φ + ψ).1)) =ᵐ[
          (volume : Measure E).restrict Ω''] (φ + ψ).1 :=
      MemLp.coeFn_toLp _
    have h2 : ⇑((memLp_two_restrict_of_smoothCompactlySupported (d := d)
        (Ω'' := Ω'') φ.2.1 φ.2.2.1).toLp φ.1 +
        (memLp_two_restrict_of_smoothCompactlySupported (d := d)
          (Ω'' := Ω'') ψ.2.1 ψ.2.2.1).toLp ψ.1) =ᵐ[
          (volume : Measure E).restrict Ω'']
          ⇑((memLp_two_restrict_of_smoothCompactlySupported (d := d)
              (Ω'' := Ω'') φ.2.1 φ.2.2.1).toLp φ.1) +
            ⇑((memLp_two_restrict_of_smoothCompactlySupported (d := d)
              (Ω'' := Ω'') ψ.2.1 ψ.2.2.1).toLp ψ.1) :=
      Lp.coeFn_add _ _
    have h3 : ⇑((memLp_two_restrict_of_smoothCompactlySupported (d := d)
        (Ω'' := Ω'') φ.2.1 φ.2.2.1).toLp φ.1) =ᵐ[
          (volume : Measure E).restrict Ω''] φ.1 :=
      MemLp.coeFn_toLp _
    have h4 : ⇑((memLp_two_restrict_of_smoothCompactlySupported (d := d)
        (Ω'' := Ω'') ψ.2.1 ψ.2.2.1).toLp ψ.1) =ᵐ[
          (volume : Measure E).restrict Ω''] ψ.1 :=
      MemLp.coeFn_toLp _
    have h_add_coe : ((φ + ψ :
        (smoothCompactlySupportedInSubmodule (d := d) Ω'')).1 : E → ℝ) =
        φ.1 + ψ.1 := rfl
    refine h1.trans ?_
    refine (h2.trans ?_).symm
    rw [h_add_coe]
    filter_upwards [h3, h4] with x hx3 hx4
    simp only [Pi.add_apply]
    rw [hx3, hx4]
  map_smul' c φ := by
    refine Lp.ext ?_
    have h1 : ⇑((memLp_two_restrict_of_smoothCompactlySupported (d := d)
        (Ω'' := Ω'') (c • φ).2.1 (c • φ).2.2.1).toLp
          ((c • φ).1)) =ᵐ[(volume : Measure E).restrict Ω''] (c • φ).1 :=
      MemLp.coeFn_toLp _
    have h2 : ⇑(c • (memLp_two_restrict_of_smoothCompactlySupported (d := d)
        (Ω'' := Ω'') φ.2.1 φ.2.2.1).toLp φ.1)
        =ᵐ[(volume : Measure E).restrict Ω'']
          c • ⇑((memLp_two_restrict_of_smoothCompactlySupported (d := d)
            (Ω'' := Ω'') φ.2.1 φ.2.2.1).toLp φ.1) :=
      Lp.coeFn_smul c _
    have h3 : ⇑((memLp_two_restrict_of_smoothCompactlySupported (d := d)
        (Ω'' := Ω'') φ.2.1 φ.2.2.1).toLp φ.1) =ᵐ[
          (volume : Measure E).restrict Ω''] φ.1 :=
      MemLp.coeFn_toLp _
    have h_smul_coe : ((c • φ :
        (smoothCompactlySupportedInSubmodule (d := d) Ω'')).1 : E → ℝ) =
        c • φ.1 := rfl
    refine h1.trans ?_
    rw [h_smul_coe]
    have h_id_eq :
        (RingHom.id ℝ) c • (memLp_two_restrict_of_smoothCompactlySupported (d := d)
            (Ω'' := Ω'') φ.2.1 φ.2.2.1).toLp φ.1
          = c • (memLp_two_restrict_of_smoothCompactlySupported (d := d)
            (Ω'' := Ω'') φ.2.1 φ.2.2.1).toLp φ.1 := rfl
    rw [show ⇑((RingHom.id ℝ) c •
        (memLp_two_restrict_of_smoothCompactlySupported (d := d)
          (Ω'' := Ω'') φ.2.1 φ.2.2.1).toLp φ.1) =
        ⇑(c • (memLp_two_restrict_of_smoothCompactlySupported (d := d)
          (Ω'' := Ω'') φ.2.1 φ.2.2.1).toLp φ.1) from by
      rw [h_id_eq]]
    filter_upwards [h2, h3] with x hx2 hx3
    rw [hx2, Pi.smul_apply, Pi.smul_apply, hx3]

@[simp] private lemma smoothCompactlySupportedInToLp_apply
    (Ω'' : Set E) (φ : smoothCompactlySupportedInSubmodule (d := d) Ω'') :
    smoothCompactlySupportedInToLp (d := d) Ω'' φ =
      (memLp_two_restrict_of_smoothCompactlySupported (d := d)
        (Ω'' := Ω'') φ.2.1 φ.2.2.1).toLp φ.1 := rfl

private lemma denseRange_smoothCompactlySupportedInToLp
    {Ω'' : Set E} (hΩ''_open : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω'')) :
    DenseRange (smoothCompactlySupportedInToLp (d := d) Ω'') := by
  classical
  have hΩ''_meas : MeasurableSet Ω'' := hΩ''_open.measurableSet
  have : IsFiniteMeasure ((volume : Measure E).restrict Ω'') := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact lt_of_le_of_lt (measure_mono subset_closure)
      hΩ''_compact_closure.measure_lt_top
  intro f
  rw [Metric.mem_closure_iff]
  intro ε hε
  set ε' : ℝ := ε / 4 with hε'_def
  have hε' : 0 < ε' := by rw [hε'_def]; linarith
  obtain ⟨g₀, hg₀_cs, hg₀_smooth, hg₀_close⟩ :=
    MeasureTheory.MemLp.exist_eLpNorm_sub_le
      (μ := (volume : Measure E).restrict Ω'')
      (p := 2) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (Lp.memLp f) hε'
  obtain ⟨B, hB⟩ :=
    hg₀_smooth.continuous.bounded_above_of_compact_support hg₀_cs
  set Bp : ℝ := max B 0 + 1 with hBp_def
  have hBp_pos : 0 < Bp := by
    rw [hBp_def]; have := le_max_right B 0; linarith
  have hBp_nn : 0 ≤ Bp := hBp_pos.le
  set δ : ℝ := (ε' / Bp) ^ 2 with hδ_def
  have hδ_pos : 0 < δ := by
    rw [hδ_def]
    have : 0 < ε' / Bp := div_pos hε' hBp_pos
    positivity
  have hδ_ennreal_pos : 0 < ENNReal.ofReal δ := by
    rwa [ENNReal.ofReal_pos]
  have hK_exists :
      ∃ K : Set E, IsCompact K ∧ K ⊆ Ω'' ∧
        ((volume : Measure E).restrict Ω'') (Ω'' \ K) ≤ ENNReal.ofReal δ := by
    have h_meas_full : ((volume : Measure E).restrict Ω'') Ω'' < ⊤ := by
      rw [Measure.restrict_apply hΩ''_meas, Set.inter_self]
      exact lt_of_le_of_lt (measure_mono subset_closure)
        hΩ''_compact_closure.measure_lt_top
    have h_inner :=
      MeasurableSet.exists_isCompact_lt_add
        (μ := (volume : Measure E).restrict Ω'')
        hΩ''_meas h_meas_full.ne hδ_ennreal_pos.ne'
    obtain ⟨K, hK_sub, hK_compact, hK_lt⟩ := h_inner
    refine ⟨K, hK_compact, hK_sub, ?_⟩
    have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
    have h_diff_meas : MeasurableSet (Ω'' \ K) := hΩ''_meas.diff hK_meas
    have h_disj : Disjoint K (Ω'' \ K) := disjoint_sdiff_self_right
    have h_union : Ω'' = K ∪ (Ω'' \ K) := (Set.union_sdiff_cancel hK_sub).symm
    have h_meas_split :
        ((volume : Measure E).restrict Ω'') Ω'' =
          ((volume : Measure E).restrict Ω'') K +
            ((volume : Measure E).restrict Ω'') (Ω'' \ K) := by
      have h := MeasureTheory.measure_union (μ := (volume : Measure E).restrict Ω'')
        h_disj h_diff_meas
      rw [← h_union] at h
      exact h
    have hK_le : ((volume : Measure E).restrict Ω'') K ≠ ⊤ :=
      ne_top_of_le_ne_top h_meas_full.ne (measure_mono hK_sub)
    have h_le_K_plus_delta :
        ((volume : Measure E).restrict Ω'') Ω'' <
          ((volume : Measure E).restrict Ω'') K + ENNReal.ofReal δ := hK_lt
    rw [h_meas_split] at h_le_K_plus_delta
    have h_eq : ((volume : Measure E).restrict Ω'') K +
            ((volume : Measure E).restrict Ω'') (Ω'' \ K) <
          ((volume : Measure E).restrict Ω'') K + ENNReal.ofReal δ :=
      h_le_K_plus_delta
    exact (ENNReal.add_lt_add_iff_left hK_le).mp h_eq |>.le
  obtain ⟨K, hK_compact, hK_sub, hK_meas_diff⟩ := hK_exists
  obtain ⟨η, hη_smooth, hη_cs, hη_one_nhds, hη_tsupp_in, hη_range⟩ :=
    CalabiYau.exists_bump_compact hK_compact hΩ''_open hK_sub
  have hη_one_on_K : ∀ x ∈ K, η x = 1 := fun x hx =>
    hη_one_nhds.self_of_nhdsSet hx
  set g : E → ℝ := fun x => η x * g₀ x with hg_def
  have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g := hη_smooth.mul hg₀_smooth
  have hg_cs : HasCompactSupport g := hη_cs.mul_right
  have hg_tsupp_in_Ω'' : tsupport g ⊆ Ω'' := by
    refine subset_trans ?_ hη_tsupp_in
    have hsupport_sub : Function.support g ⊆ Function.support η := by
      intro x hx
      rw [Function.mem_support] at hx ⊢
      intro hηx
      apply hx
      change η x * g₀ x = 0
      rw [hηx]; ring
    exact closure_mono hsupport_sub
  have h_pt_bd : ∀ᵐ x ∂((volume : Measure E).restrict Ω''),
      ‖(g : E → ℝ) x - g₀ x‖ ≤ Bp *
        (Ω'' \ K).indicator (fun _ => (1 : ℝ)) x := by
    rw [ae_restrict_iff' hΩ''_meas]
    refine Filter.Eventually.of_forall ?_
    intro x hx
    by_cases hxK : x ∈ K
    · have hηx : η x = 1 := hη_one_on_K x hxK
      have h_g_eq : g x = g₀ x := by
        change η x * g₀ x = g₀ x; rw [hηx]; ring
      rw [show (g : E → ℝ) x - g₀ x = g₀ x - g₀ x from by
          show g x - g₀ x = g₀ x - g₀ x; rw [h_g_eq]]
      rw [sub_self, norm_zero]
      have hxnotin : x ∉ Ω'' \ K := fun ⟨_, hnotK⟩ => hnotK hxK
      rw [Set.indicator_of_notMem hxnotin]
      simp
    · have h_diff_eq : (g : E → ℝ) x - g₀ x = (η x - 1) * g₀ x := by
        change η x * g₀ x - g₀ x = (η x - 1) * g₀ x; ring
      rw [h_diff_eq, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hg₀_bd : |g₀ x| ≤ max B 0 :=
        (le_trans (hB x) (le_max_left _ _))
      have hη_in : η x ∈ Set.Icc (0 : ℝ) 1 := hη_range ⟨x, rfl⟩
      have hη_diff : |η x - 1| ≤ 1 := by
        rcases hη_in with ⟨h1, h2⟩
        have h_le_zero : η x - 1 ≤ 0 := by linarith
        have h_ge_neg1 : -(1 : ℝ) ≤ η x - 1 := by linarith
        rw [abs_of_nonpos h_le_zero]
        linarith
      have hx_in_diff : x ∈ Ω'' \ K := ⟨hx, hxK⟩
      rw [Set.indicator_of_mem hx_in_diff]
      have h_max_pos : 0 ≤ max B 0 := le_max_right _ _
      have h_g0_nn : 0 ≤ |g₀ x| := abs_nonneg _
      calc |η x - 1| * |g₀ x|
          ≤ 1 * (max B 0) := by
            refine mul_le_mul hη_diff hg₀_bd h_g0_nn (by linarith)
        _ = max B 0 := by ring
        _ ≤ Bp * 1 := by rw [hBp_def]; linarith
  have h_meas_diff : MeasurableSet (Ω'' \ K) :=
    hΩ''_meas.diff hK_compact.isClosed.measurableSet
  have h_g_minus_g0_le :
      eLpNorm ((g : E → ℝ) - g₀) 2 ((volume : Measure E).restrict Ω'') ≤
        ENNReal.ofReal Bp *
          (((volume : Measure E).restrict Ω'') (Ω'' \ K)) ^ ((1 : ℝ) / 2) := by
    have h_indicator_eLpNorm :
        eLpNorm ((Ω'' \ K).indicator (fun _ : E => Bp)) 2
          ((volume : Measure E).restrict Ω'') =
        ENNReal.ofReal Bp *
          (((volume : Measure E).restrict Ω'') (Ω'' \ K)) ^ ((1 : ℝ) / 2) := by
      have hp_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
      have hp_ne_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
      rw [eLpNorm_indicator_const h_meas_diff.nullMeasurableSet hp_ne_zero hp_ne_top]
      have h_two_toReal : ((2 : ℝ≥0∞) : ℝ≥0∞).toReal = 2 := by simp
      rw [h_two_toReal]
      rw [Real.enorm_eq_ofReal hBp_nn]
    refine le_trans ?_ (le_of_eq h_indicator_eLpNorm)
    refine eLpNorm_mono_ae
      (hg_smooth.continuous.sub hg₀_smooth.continuous).aestronglyMeasurable ?_
    refine h_pt_bd.mono ?_
    intro x hx
    have h_sub_apply : ((g : E → ℝ) - g₀) x = g x - g₀ x := rfl
    rw [h_sub_apply]
    by_cases hxd : x ∈ Ω'' \ K
    · rw [Set.indicator_of_mem hxd] at hx
      rw [Set.indicator_of_mem hxd]
      rw [Real.norm_eq_abs] at *
      rw [show ‖(Bp : ℝ)‖ = |Bp| from rfl, abs_of_nonneg hBp_nn]
      linarith
    · rw [Set.indicator_of_notMem hxd] at hx
      rw [Set.indicator_of_notMem hxd]
      have h_zero_bd : Bp * 0 = (0 : ℝ) := by ring
      rw [h_zero_bd] at hx
      have h_norm_nn : 0 ≤ ‖g x - g₀ x‖ := norm_nonneg _
      have h_lhs_eq : ‖g x - g₀ x‖ = 0 :=
        le_antisymm hx h_norm_nn
      rw [h_lhs_eq]
      simp
  refine ⟨smoothCompactlySupportedInToLp (d := d) Ω''
    ⟨g, hg_smooth, hg_cs, hg_tsupp_in_Ω''⟩, ?_, ?_⟩
  · exact ⟨⟨g, hg_smooth, hg_cs, hg_tsupp_in_Ω''⟩, rfl⟩
  · rw [dist_comm, Lp.dist_def]
    have h_g_eq_ae : ⇑(smoothCompactlySupportedInToLp (d := d) Ω''
        ⟨g, hg_smooth, hg_cs, hg_tsupp_in_Ω''⟩) =ᵐ[
          (volume : Measure E).restrict Ω''] g := by
      simp only [smoothCompactlySupportedInToLp_apply]
      exact MemLp.coeFn_toLp _
    have h_eLpNorm_eq :
        eLpNorm (⇑(smoothCompactlySupportedInToLp (d := d) Ω''
            ⟨g, hg_smooth, hg_cs, hg_tsupp_in_Ω''⟩) - ⇑f) 2
          ((volume : Measure E).restrict Ω'') =
        eLpNorm ((g : E → ℝ) - ⇑f) 2 ((volume : Measure E).restrict Ω'') := by
      refine eLpNorm_congr_ae ?_
      filter_upwards [h_g_eq_ae] with x hx
      change (⇑(smoothCompactlySupportedInToLp (d := d) Ω''
          ⟨g, hg_smooth, hg_cs, hg_tsupp_in_Ω''⟩)) x - (⇑f) x =
        g x - (⇑f) x
      rw [hx]
    rw [h_eLpNorm_eq]
    have h_eLpNorm_diff_le :
        eLpNorm ((g : E → ℝ) - ⇑f) 2 ((volume : Measure E).restrict Ω'') ≤
          eLpNorm ((g : E → ℝ) - g₀) 2 ((volume : Measure E).restrict Ω'') +
            eLpNorm ((g₀ : E → ℝ) - ⇑f) 2 ((volume : Measure E).restrict Ω'') := by
      have h_split : (g : E → ℝ) - ⇑f =
          ((g : E → ℝ) - g₀) + (g₀ - ⇑f) := by
        ext x
        change g x - (⇑f) x = (g x - g₀ x) + (g₀ x - (⇑f) x)
        ring
      rw [h_split]
      exact eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have h_meas_le :
        (((volume : Measure E).restrict Ω'') (Ω'' \ K)) ^ ((1 : ℝ) / 2) ≤
          (ENNReal.ofReal δ) ^ ((1 : ℝ) / 2) := by
      refine ENNReal.rpow_le_rpow hK_meas_diff (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have h_diff_size :
        eLpNorm ((g : E → ℝ) - g₀) 2 ((volume : Measure E).restrict Ω'') ≤
          ENNReal.ofReal ε' := by
      refine le_trans h_g_minus_g0_le ?_
      calc ENNReal.ofReal Bp *
            (((volume : Measure E).restrict Ω'') (Ω'' \ K)) ^ ((1 : ℝ) / 2) ≤
          ENNReal.ofReal Bp *
            (ENNReal.ofReal δ) ^ ((1 : ℝ) / 2) := by gcongr
        _ = ENNReal.ofReal (Bp * δ ^ ((1 : ℝ) / 2)) := by
              rw [show (ENNReal.ofReal δ) ^ ((1 : ℝ) / 2) =
                  ENNReal.ofReal (δ ^ ((1 : ℝ) / 2)) from
                ENNReal.ofReal_rpow_of_pos hδ_pos]
              rw [← ENNReal.ofReal_mul hBp_nn]
        _ ≤ ENNReal.ofReal ε' := by
              refine ENNReal.ofReal_le_ofReal ?_
              have h_sqrt : δ ^ ((1 : ℝ) / 2) = ε' / Bp := by
                rw [hδ_def]
                rw [show ((ε' / Bp) ^ 2 : ℝ) = (ε' / Bp) ^ (2 : ℕ) from rfl]
                rw [← Real.rpow_natCast (ε' / Bp) 2]
                have h_pos : 0 < ε' / Bp := div_pos hε' hBp_pos
                rw [← Real.rpow_mul h_pos.le]
                rw [show ((2 : ℕ) : ℝ) * ((1 : ℝ) / 2) = 1 from by norm_num]
                rw [Real.rpow_one]
              rw [h_sqrt]
              rw [show Bp * (ε' / Bp) = ε' from by
                  field_simp]
    have h_g0_close :
        eLpNorm ((g₀ : E → ℝ) - ⇑f) 2 ((volume : Measure E).restrict Ω'') ≤
          ENNReal.ofReal ε' := by
      have hcalc : eLpNorm ((fun x => g₀ x - (⇑f) x)) 2
          ((volume : Measure E).restrict Ω'') =
        eLpNorm ((fun x => (⇑f) x - g₀ x)) 2
          ((volume : Measure E).restrict Ω'') := by
        rw [show (fun x => g₀ x - (⇑f) x) = -(fun x => (⇑f) x - g₀ x) from by
          ext x; simp]
        exact eLpNorm_neg _ _ _
      have h_sub_eq : ((g₀ : E → ℝ) - ⇑f) = fun x => g₀ x - (⇑f) x := rfl
      rw [h_sub_eq, hcalc]
      have h_eq : (fun x => (⇑f) x - g₀ x) = (⇑f - g₀ : E → ℝ) := rfl
      rw [h_eq]
      exact hg₀_close
    have h_total_le :
        eLpNorm ((g : E → ℝ) - ⇑f) 2 ((volume : Measure E).restrict Ω'') ≤
          ENNReal.ofReal ε' + ENNReal.ofReal ε' := by
      refine le_trans h_eLpNorm_diff_le ?_
      exact add_le_add h_diff_size h_g0_close
    have h_total_le_e2 :
        eLpNorm ((g : E → ℝ) - ⇑f) 2 ((volume : Measure E).restrict Ω'') ≤
          ENNReal.ofReal (ε / 2) := by
      refine le_trans h_total_le ?_
      rw [← ENNReal.ofReal_add hε'.le hε'.le]
      have : ε' + ε' = ε / 2 := by rw [hε'_def]; ring
      rw [this]
    have h_eLpNorm_lt_top :
        eLpNorm ((g : E → ℝ) - ⇑f) 2 ((volume : Measure E).restrict Ω'') < ⊤ :=
      lt_of_le_of_lt h_total_le_e2 ENNReal.ofReal_lt_top
    have h_dist_le : (eLpNorm ((g : E → ℝ) - ⇑f) 2
          ((volume : Measure E).restrict Ω'')).toReal ≤ ε / 2 := by
      have := ENNReal.toReal_mono (a := eLpNorm
          ((g : E → ℝ) - ⇑f) 2 ((volume : Measure E).restrict Ω''))
        (b := ENNReal.ofReal (ε / 2))
        (ENNReal.ofReal_ne_top : ENNReal.ofReal (ε / 2) ≠ ⊤) h_total_le_e2
      have hε2 : 0 ≤ ε / 2 := by linarith
      rw [ENNReal.toReal_ofReal hε2] at this
      exact this
    linarith

variable [NeZero d] in
private def smoothTestFunctionalLocal
    {Ω Ω'' : Set E} {w : E → ℝ}
    (hw_l2 : MemLp w 2 ((volume : Measure E).restrict Ω))
    (k : Fin d) :
    smoothCompactlySupportedInSubmodule (d := d) Ω'' →ₗ[ℝ] ℝ where
  toFun φ :=
    -∫ x in Ω, w x * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1)
      ∂(volume : Measure E)
  map_add' φ ψ := by
    change
      -∫ x in Ω, w x *
        (fderiv ℝ ((φ + ψ : smoothCompactlySupportedInSubmodule (d := d) Ω'').1) x)
          (EuclideanSpace.single k 1) ∂(volume : Measure E) =
      (-∫ x in Ω, w x * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1)
          ∂(volume : Measure E)) +
      (-∫ x in Ω, w x * (fderiv ℝ ψ.1 x) (EuclideanSpace.single k 1)
          ∂(volume : Measure E))
    have hφ_diff : Differentiable ℝ φ.1 := φ.2.1.differentiable (by simp)
    have hψ_diff : Differentiable ℝ ψ.1 := ψ.2.1.differentiable (by simp)
    have h_fderiv_sum : ∀ x : E,
        (fderiv ℝ ((φ + ψ : smoothCompactlySupportedInSubmodule (d := d) Ω'').1) x)
            (EuclideanSpace.single k 1) =
          (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1) +
            (fderiv ℝ ψ.1 x) (EuclideanSpace.single k 1) := by
      intro x
      have hcoe : ((φ + ψ : smoothCompactlySupportedInSubmodule (d := d) Ω'').1 : E → ℝ) =
          φ.1 + ψ.1 := rfl
      rw [hcoe]
      rw [show (φ.1 + ψ.1 : E → ℝ) = fun y => φ.1 y + ψ.1 y from rfl]
      rw [fderiv_fun_add (hφ_diff.differentiableAt) (hψ_diff.differentiableAt)]
      simp
    have hint_sum : ∀ x : E,
        w x * (fderiv ℝ ((φ + ψ : smoothCompactlySupportedInSubmodule (d := d) Ω'').1) x)
              (EuclideanSpace.single k 1) =
          w x * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1) +
            w x * (fderiv ℝ ψ.1 x) (EuclideanSpace.single k 1) := by
      intro x; rw [h_fderiv_sum x]; ring
    have hφ_int := Euclidean.integrable_mul_fderiv_apply_of_memLp
      hw_l2 φ.2.1 φ.2.2.1 k
    have hψ_int := Euclidean.integrable_mul_fderiv_apply_of_memLp
      hw_l2 ψ.2.1 ψ.2.2.1 k
    have h_int_eq :
        ∫ x in Ω, w x *
            (fderiv ℝ ((φ + ψ : smoothCompactlySupportedInSubmodule (d := d) Ω'').1) x)
              (EuclideanSpace.single k 1) ∂(volume : Measure E) =
          (∫ x in Ω, w x * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1)
              ∂(volume : Measure E)) +
            ∫ x in Ω, w x * (fderiv ℝ ψ.1 x) (EuclideanSpace.single k 1)
              ∂(volume : Measure E) := by
      rw [show (fun x => w x *
          (fderiv ℝ ((φ + ψ : smoothCompactlySupportedInSubmodule (d := d) Ω'').1) x)
            (EuclideanSpace.single k 1)) =
        (fun x =>
            w x * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1) +
              w x * (fderiv ℝ ψ.1 x) (EuclideanSpace.single k 1)) from by
          ext x; exact hint_sum x]
      exact integral_add hφ_int hψ_int
    rw [h_int_eq]; ring
  map_smul' c φ := by
    change
      -∫ x in Ω, w x *
        (fderiv ℝ ((c • φ : smoothCompactlySupportedInSubmodule (d := d) Ω'').1) x)
          (EuclideanSpace.single k 1) ∂(volume : Measure E) =
      c • (-∫ x in Ω, w x * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1)
            ∂(volume : Measure E))
    have hφ_diff : Differentiable ℝ φ.1 := φ.2.1.differentiable (by simp)
    have h_fderiv_smul : ∀ x : E,
        (fderiv ℝ ((c • φ : smoothCompactlySupportedInSubmodule (d := d) Ω'').1) x)
            (EuclideanSpace.single k 1) =
          c * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1) := by
      intro x
      have hcoe : ((c • φ : smoothCompactlySupportedInSubmodule (d := d) Ω'').1
          : E → ℝ) = c • φ.1 := rfl
      rw [hcoe]
      have heq2 : (c • φ.1 : E → ℝ) = fun y => c * φ.1 y := by ext y; rfl
      rw [heq2]
      rw [fderiv_const_mul (hφ_diff.differentiableAt) c]
      simp
    have hint_smul : ∀ x : E,
        w x * (fderiv ℝ ((c • φ : smoothCompactlySupportedInSubmodule (d := d) Ω'').1) x)
              (EuclideanSpace.single k 1) =
          c * (w x * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1)) := by
      intro x; rw [h_fderiv_smul x]; ring
    have h_int_eq :
        ∫ x in Ω, w x * (fderiv ℝ ((c • φ : smoothCompactlySupportedInSubmodule
            (d := d) Ω'').1) x)
              (EuclideanSpace.single k 1) ∂(volume : Measure E) =
          c * ∫ x in Ω, w x * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1)
            ∂(volume : Measure E) := by
      rw [show (fun x => w x *
          (fderiv ℝ ((c • φ : smoothCompactlySupportedInSubmodule (d := d) Ω'').1) x)
            (EuclideanSpace.single k 1)) =
        (fun x => c * (w x * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1)))
          from by ext x; exact hint_smul x]
      exact integral_const_mul _ _
    rw [h_int_eq]
    rw [smul_eq_mul]; ring

@[simp] private lemma smoothTestFunctional_local_apply
    {Ω Ω'' : Set E} {w : E → ℝ}
    (hw_l2 : MemLp w 2 ((volume : Measure E).restrict Ω))
    (k : Fin d) (φ : smoothCompactlySupportedInSubmodule (d := d) Ω'') :
    smoothTestFunctionalLocal (d := d) (Ω := Ω) (Ω'' := Ω'') hw_l2 k φ =
      -∫ x in Ω, w x * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1)
        ∂(volume : Measure E) := rfl

private lemma diffQuot_eq_zero_of_notMem_cthickening_local
    {φ : E → ℝ} (_hφ_support : HasCompactSupport φ)
    (k : Fin d) {h₀ : ℝ} (_hh₀ : 0 ≤ h₀) {h : ℝ} (hh_bd : |h| ≤ h₀) :
    ∀ x : E, x ∉ Metric.cthickening h₀ (tsupport φ) →
      diffQuot k h φ x = 0 := by
  intro x hx
  have hxnot : x ∉ tsupport φ := fun h => hx (Metric.self_subset_cthickening _ h)
  have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hxnot
  have hxhe : x + h • EuclideanSpace.single k 1 ∉ tsupport φ := by
    intro hin
    apply hx
    have hnorm :
        dist x (x + h • EuclideanSpace.single k 1) = |h| := by
      rw [dist_eq_norm]
      have heq : x - (x + h • EuclideanSpace.single k 1) =
          -(h • EuclideanSpace.single k 1) := by abel
      rw [heq, norm_neg, norm_smul]
      rw [show ‖(EuclideanSpace.single k (1 : ℝ) : E)‖ = 1 by simp]
      rw [Real.norm_eq_abs, mul_one]
    have h_dist_le : dist x (x + h • EuclideanSpace.single k 1) ≤ h₀ := by
      rw [hnorm]; exact hh_bd
    exact Metric.mem_cthickening_of_dist_le x
      (x + h • EuclideanSpace.single k 1) h₀ (tsupport φ) hin h_dist_le
  have hφxhe : φ (x + h • EuclideanSpace.single k 1) = 0 :=
    image_eq_zero_of_notMem_tsupport hxhe
  by_cases hh : h = 0
  · rw [hh]; simp [diffQuot]
  · rw [diffQuot_apply_of_ne (d := d) k hh φ x]
    rw [hφx, hφxhe]
    simp

private lemma tendsto_integral_w_diffQuot_phi_local
    {Ω : Set E} {w : E → ℝ}
    (hw_l2 : MemLp w 2 ((volume : Measure E).restrict Ω))
    {φ : E → ℝ} (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_support : HasCompactSupport φ) (k : Fin d)
    {hₙ : ℕ → ℝ} (hₙ_ne : ∀ n, hₙ n ≠ 0)
    (hₙ_tendsto : Tendsto hₙ atTop (𝓝 0)) :
    Tendsto (fun n =>
        ∫ x in Ω, w x * diffQuot k (-(hₙ n)) φ x ∂(volume : Measure E))
      atTop
      (𝓝 (∫ x in Ω, w x * (fderiv ℝ φ x) (EuclideanSpace.single k 1)
        ∂(volume : Measure E))) := by
  have hφ_C1 : ContDiff ℝ 1 φ := hφ_smooth.of_le (by norm_cast)
  have h_lip : ∃ L : ℝ, 0 ≤ L ∧ ∀ h : ℝ, ∀ x : E, |diffQuot k h φ x| ≤ L := by
    obtain ⟨L, hL_nn, hLip⟩ :=
      lipschitz_of_contDiff_compactSupport (d := d) hφ_C1 hφ_support
    refine ⟨L, hL_nn, fun h x => ?_⟩
    by_cases hh : h = 0
    · rw [hh, diffQuot_zero_h]; simpa using hL_nn
    · rw [diffQuot_apply_of_ne (d := d) k hh φ x]
      have hLip_apply :
          ‖φ (x + h • EuclideanSpace.single k 1) - φ x‖ ≤
            L * ‖x + h • EuclideanSpace.single k 1 - x‖ := hLip _ _
      have hsimp : x + h • EuclideanSpace.single k 1 - x =
          h • EuclideanSpace.single k 1 := by
        rw [add_sub_cancel_left]
      rw [hsimp] at hLip_apply
      have hsing_norm :
          ‖(EuclideanSpace.single k (1 : ℝ) : E)‖ = 1 := by simp
      have hnorm_smul :
          ‖h • EuclideanSpace.single k (1 : ℝ)‖ = |h| := by
        rw [norm_smul, hsing_norm, mul_one, Real.norm_eq_abs]
      rw [hnorm_smul] at hLip_apply
      rw [abs_div]
      have habs_h : 0 < |h| := abs_pos.mpr hh
      rw [div_le_iff₀ habs_h]
      have h_lhs_norm :
          |φ (x + h • EuclideanSpace.single k 1) - φ x| =
            ‖φ (x + h • EuclideanSpace.single k 1) - φ x‖ :=
        (Real.norm_eq_abs _).symm
      rw [h_lhs_norm]
      exact hLip_apply
  obtain ⟨L, _hL_nn, hLip⟩ := h_lip
  set h₀ : ℝ := 1 with h₀_def
  have hh₀_nn : (0 : ℝ) ≤ h₀ := by simp [h₀_def]
  have hN : ∀ᶠ n in atTop, |hₙ n| ≤ h₀ := by
    have hAbs : Tendsto (fun n => |hₙ n|) atTop (𝓝 0) := by
      have := hₙ_tendsto.abs; simpa using this
    have h_ev :
        ∀ᶠ n in atTop, dist (|hₙ n|) 0 < 1 :=
      hAbs.eventually (Metric.ball_mem_nhds 0 (by norm_num))
    filter_upwards [h_ev] with n hn
    have h_dist : dist (|hₙ n|) 0 = |hₙ n| := by
      rw [Real.dist_eq, sub_zero, abs_abs]
    rw [h_dist] at hn
    exact hn.le
  set K_thick : Set E := Metric.cthickening h₀ (tsupport φ) with hKt_def
  have hK_compact : IsCompact (tsupport φ) := hφ_support
  have hK_thick_compact : IsCompact K_thick := hK_compact.cthickening
  have hK_thick_meas : MeasurableSet K_thick :=
    hK_thick_compact.measurableSet
  set bound : E → ℝ := fun x => K_thick.indicator (fun y => L * |w y|) x
  have hw_meas : AEStronglyMeasurable w ((volume : Measure E).restrict Ω) :=
    hw_l2.aestronglyMeasurable
  have h_indicator_memLp_2 :
      MemLp (fun x : E => K_thick.indicator (fun _ => (1 : ℝ)) x) 2
        ((volume : Measure E).restrict Ω) := by
    have h_finite : ((volume : Measure E).restrict Ω) K_thick ≠ ∞ := by
      have h₁ : ((volume : Measure E).restrict Ω) K_thick ≤
          (volume : Measure E) K_thick := Measure.restrict_le_self _
      exact ne_top_of_le_ne_top hK_thick_compact.measure_lt_top.ne h₁
    refine memLp_indicator_const _ hK_thick_meas (1 : ℝ) (Or.inr h_finite)
  have h_abs_eq_norm : (fun x => |w x|) = fun x => ‖w x‖ := by
    funext x; rw [Real.norm_eq_abs]
  have h_abs_w_memLp : MemLp (fun x => |w x|) 2
      ((volume : Measure E).restrict Ω) := by
    rw [h_abs_eq_norm]
    exact hw_l2.norm
  have h_Labsw_memLp :
      MemLp (fun x => L * |w x|) 2 ((volume : Measure E).restrict Ω) :=
    h_abs_w_memLp.const_mul L
  have h_bound_eq :
      bound = (fun x => (L * |w x|) *
        K_thick.indicator (fun _ => (1 : ℝ)) x) := by
    funext x
    simp only [bound]
    by_cases hx : x ∈ K_thick
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, mul_one]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]
  have h_bound_int : Integrable bound ((volume : Measure E).restrict Ω) := by
    rw [h_bound_eq]
    exact MemLp.integrable_mul h_Labsw_memLp h_indicator_memLp_2
  have h_pointwise_bound :
      ∀ᶠ n in atTop, ∀ᵐ x ∂((volume : Measure E).restrict Ω),
        ‖w x * diffQuot k (-(hₙ n)) φ x‖ ≤ bound x := by
    filter_upwards [hN] with n hn
    refine Filter.Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ K_thick
    · simp only [bound, Set.indicator_of_mem hx]
      rw [Real.norm_eq_abs, abs_mul]
      have hL_dq : |diffQuot k (-(hₙ n)) φ x| ≤ L := hLip _ x
      have h_abs_w_nn : 0 ≤ |w x| := abs_nonneg _
      have h_LL : |w x| * |diffQuot k (-(hₙ n)) φ x| ≤ |w x| * L :=
        mul_le_mul_of_nonneg_left hL_dq h_abs_w_nn
      linarith
    · have h_neg_h_bd : |-(hₙ n)| ≤ h₀ := by rw [abs_neg]; exact hn
      have hdq_zero : diffQuot k (-(hₙ n)) φ x = 0 :=
        diffQuot_eq_zero_of_notMem_cthickening_local (d := d) hφ_support k hh₀_nn
          h_neg_h_bd x hx
      rw [hdq_zero, mul_zero, norm_zero]
      simp [bound, Set.indicator_of_notMem hx]
  have h_pointwise_convergence :
      ∀ᵐ x ∂((volume : Measure E).restrict Ω),
        Tendsto (fun n => w x * diffQuot k (-(hₙ n)) φ x) atTop
          (𝓝 (w x * (fderiv ℝ φ x) (EuclideanSpace.single k 1))) := by
    refine Filter.Eventually.of_forall fun x => ?_
    have h_minus_tendsto : Tendsto (fun n => -(hₙ n)) atTop (𝓝 0) := by
      have := hₙ_tendsto.neg; simpa using this
    have h_minus_ne : ∀ n, -(hₙ n) ≠ 0 := fun n hn =>
      hₙ_ne n (neg_eq_zero.mp hn)
    have h_dq_nhdsWithin :
        Tendsto (fun h : ℝ => diffQuot k h φ x) (𝓝[≠] 0)
          (𝓝 ((fderiv ℝ φ x) (EuclideanSpace.single k 1))) :=
      tendsto_diffQuot_of_contDiff (d := d) hφ_C1 k x
    have h_tendsto_within :
        Tendsto (fun n => -(hₙ n)) atTop (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨h_minus_tendsto, ?_⟩
      exact Filter.Eventually.of_forall fun n => h_minus_ne n
    have h_dq_tendsto :
        Tendsto (fun n => diffQuot k (-(hₙ n)) φ x) atTop
          (𝓝 ((fderiv ℝ φ x) (EuclideanSpace.single k 1))) :=
      h_dq_nhdsWithin.comp h_tendsto_within
    exact h_dq_tendsto.const_mul (w x)
  have h_aesm_seq : ∀ n, AEStronglyMeasurable
      (fun x => w x * diffQuot k (-(hₙ n)) φ x)
      ((volume : Measure E).restrict Ω) := by
    intro n
    have hdq_global : AEStronglyMeasurable (diffQuot k (-(hₙ n)) φ)
        (volume : Measure E) :=
      aestronglyMeasurable_diffQuot (d := d) k _
        hφ_smooth.continuous.aestronglyMeasurable
    have hdq_meas : AEStronglyMeasurable (diffQuot k (-(hₙ n)) φ)
        ((volume : Measure E).restrict Ω) := hdq_global.restrict
    exact hw_meas.mul hdq_meas
  exact tendsto_integral_filter_of_dominated_convergence
    bound (Filter.Eventually.of_forall h_aesm_seq)
    h_pointwise_bound h_bound_int h_pointwise_convergence

private lemma abs_integral_mul_le_eLpNorm_two_local
    {μ : Measure E} {f g : E → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ENNReal.ofReal |∫ x, f x * g x ∂μ| ≤ eLpNorm f 2 μ * eLpNorm g 2 μ := by
  have h_abs_le_lintegral :
      ENNReal.ofReal |∫ x, f x * g x ∂μ| ≤ ∫⁻ x, ‖f x * g x‖ₑ ∂μ := by
    rw [← Real.norm_eq_abs]
    have hint : ‖∫ x, f x * g x ∂μ‖ₑ ≤ ∫⁻ x, ‖f x * g x‖ₑ ∂μ :=
      enorm_integral_le_lintegral_enorm _
    have hofreal : ENNReal.ofReal ‖∫ x, f x * g x ∂μ‖ = ‖∫ x, f x * g x ∂μ‖ₑ :=
      ofReal_norm _
    rw [hofreal]; exact hint
  have h_lintegral_eq :
      ∫⁻ x, ‖f x * g x‖ₑ ∂μ = eLpNorm (fun x => g x * f x) 1 μ := by
    rw [eLpNorm_one_eq_lintegral_enorm (f := fun x => g x * f x)
      (hg.aestronglyMeasurable.mul hf.aestronglyMeasurable)]
    refine lintegral_congr (fun x => ?_)
    simp [enorm_mul, mul_comm]
  have : ENNReal.HolderTriple (2 : ℝ≥0∞) (2 : ℝ≥0∞) 1 := by
    constructor
    rw [show (1 : ℝ≥0∞)⁻¹ = 1 from inv_one]
    rw [ENNReal.inv_two_add_inv_two]
  have h_smul_bound :
      eLpNorm (fun x => g x * f x) 1 μ ≤ eLpNorm g 2 μ * eLpNorm f 2 μ := by
    have h_mul_eq :
        (fun x => g x * f x) = (g : E → ℝ) • (f : E → ℝ) := by
      funext x; simp [smul_eq_mul]
    rw [h_mul_eq]
    have : ENNReal.HolderTriple (2 : ℝ≥0∞) (2 : ℝ≥0∞) 1 := inferInstance
    exact eLpNorm_smul_le_mul_eLpNorm hg.aestronglyMeasurable hf.aestronglyMeasurable
  calc
    ENNReal.ofReal |∫ x, f x * g x ∂μ|
        ≤ ∫⁻ x, ‖f x * g x‖ₑ ∂μ := h_abs_le_lintegral
    _ = eLpNorm (fun x => g x * f x) 1 μ := h_lintegral_eq
    _ ≤ eLpNorm g 2 μ * eLpNorm f 2 μ := h_smul_bound
    _ = eLpNorm f 2 μ * eLpNorm g 2 μ := mul_comm _ _

private lemma abs_integral_mul_le_norm_lp_mul_norm_lp_local
    {μ : Measure E} {f g : E → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤
      (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
  have h_ennreal := abs_integral_mul_le_eLpNorm_two_local (μ := μ) hf hg
  have h_finite_f : eLpNorm f 2 μ ≠ ∞ := hf.eLpNorm_lt_top.ne
  have h_finite_g : eLpNorm g 2 μ ≠ ∞ := hg.eLpNorm_lt_top.ne
  have h_finite : eLpNorm f 2 μ * eLpNorm g 2 μ ≠ ∞ :=
    ENNReal.mul_ne_top h_finite_f h_finite_g
  have h_toReal := ENNReal.toReal_mono h_finite h_ennreal
  have hnn : 0 ≤ |∫ x, f x * g x ∂μ| := abs_nonneg _
  rw [ENNReal.toReal_ofReal hnn] at h_toReal
  rw [ENNReal.toReal_mul] at h_toReal
  exact h_toReal

private lemma abs_smoothTestFunctional_local_le
    {Ω : Set E} (hΩ_open : IsOpen Ω)
    {Ω'' : Set E} (hΩ''_open : IsOpen Ω'')
    {h₀ : ℝ} (hh₀ : 0 < h₀)
    (h_room : Metric.cthickening h₀ (closure Ω'') ⊆ Ω)
    {w : E → ℝ}
    (hw_l2 : MemLp w 2 ((volume : Measure E).restrict Ω))
    (k : Fin d) {M : ℝ} (hM_nn : 0 ≤ M)
    (h_bdd : ∀ h : ℝ, 0 < |h| → |h| ≤ h₀ →
      eLpNorm (diffQuot k h w) 2 ((volume : Measure E).restrict Ω'')
        ≤ ENNReal.ofReal M)
    (φ : smoothCompactlySupportedInSubmodule (d := d) Ω'') :
    |smoothTestFunctionalLocal (d := d) (Ω := Ω) (Ω'' := Ω'') hw_l2 k φ| ≤
      M * (eLpNorm φ.1 2 ((volume : Measure E).restrict Ω'')).toReal := by
  rw [smoothTestFunctional_local_apply]
  rw [abs_neg]
  set hₙ : ℕ → ℝ := fun n => h₀ / (n + 1)
  have hₙ_pos : ∀ n, 0 < hₙ n := fun n => by
    apply div_pos hh₀
    have : (0 : ℝ) < n + 1 := by exact_mod_cast Nat.zero_lt_succ n
    exact this
  have hₙ_ne : ∀ n, hₙ n ≠ 0 := fun n => (hₙ_pos n).ne'
  have hₙ_bd : ∀ n, |hₙ n| ≤ h₀ := fun n => by
    rw [abs_of_pos (hₙ_pos n)]
    have h1 : (1 : ℝ) ≤ n + 1 := by
      have h0 : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le (n := n)
      linarith
    rw [div_le_iff₀ (by exact_mod_cast Nat.zero_lt_succ n : (0 : ℝ) < n + 1)]
    have : h₀ ≤ h₀ * (n + 1) := by nlinarith [hh₀.le]
    linarith
  have hₙ_pos_abs : ∀ n, 0 < |hₙ n| := fun n => by
    rw [abs_of_pos (hₙ_pos n)]; exact hₙ_pos n
  have hₙ_tendsto : Tendsto hₙ atTop (𝓝 0) := by
    have hh0 : Tendsto (fun n : ℕ => (1 : ℝ) / (↑n + 1)) atTop (𝓝 (0 : ℝ)) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      exact this
    have h_eq : ∀ n, hₙ n = h₀ * (1 / ((n : ℝ) + 1)) := fun n => by
      simp only [hₙ]; ring
    rw [show hₙ = fun n : ℕ => h₀ * (1 / ((↑n : ℝ) + 1)) from funext h_eq]
    have hmul := hh0.const_mul h₀
    simpa using hmul
  have hφ_memLp : MemLp φ.1 2 ((volume : Measure E).restrict Ω'') :=
    memLp_two_restrict_of_smoothCompactlySupported (d := d) (Ω'' := Ω'') φ.2.1 φ.2.2.1
  have hφ_memLp_global : MemLp φ.1 2 (volume : Measure E) :=
    φ.2.1.continuous.memLp_of_hasCompactSupport φ.2.2.1
  have h_convergence : Tendsto (fun n =>
      ∫ x in Ω, w x * diffQuot k (-(hₙ n)) φ.1 x ∂(volume : Measure E)) atTop
      (𝓝 (∫ x in Ω, w x * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1)
        ∂(volume : Measure E))) :=
    tendsto_integral_w_diffQuot_phi_local (d := d) hw_l2 φ.2.1 φ.2.2.1 k hₙ_ne hₙ_tendsto
  have h_dq_l2_bound : ∀ n,
      eLpNorm (diffQuot k (hₙ n) w) 2 ((volume : Measure E).restrict Ω'')
        ≤ ENNReal.ofReal M := fun n =>
    h_bdd (hₙ n) (hₙ_pos_abs n) (hₙ_bd n)
  set w_ext : E → ℝ := fun x => Ω.indicator w x with hw_ext_def
  have hw_ext_eq_w_on_Ω : ∀ x ∈ Ω, w_ext x = w x := by
    intro x hx
    simp only [w_ext, Set.indicator_of_mem hx]
  have hw_ext_zero_off_Ω : ∀ x ∉ Ω, w_ext x = 0 := by
    intro x hx
    simp only [w_ext, Set.indicator_of_notMem hx]
  have hw_ext_memLp : MemLp w_ext 2 (volume : Measure E) := by
    apply memLp_iff.mpr
    have h_eLpNorm_eq :
        eLpNorm w_ext 2 (volume : Measure E) =
          eLpNorm w 2 ((volume : Measure E).restrict Ω) := by
      rw [show w_ext = fun x => Ω.indicator w x from rfl]
      rw [show eLpNorm w 2 ((volume : Measure E).restrict Ω) =
          eLpNorm (Ω.indicator w) 2 (volume : Measure E) from
        (eLpNorm_indicator_eq_eLpNorm_restrict hΩ_open.measurableSet).symm]
    rw [h_eLpNorm_eq]
    exact hw_l2.eLpNorm_lt_top
  have h_dq_eq_on_tsupport : ∀ n : ℕ, ∀ x ∈ tsupport φ.1,
      diffQuot k (hₙ n) w_ext x = diffQuot k (hₙ n) w x := by
    intro n x hx
    have hx_Ω'' : x ∈ Ω'' := φ.2.2.2 hx
    have hx_closure_Ω'' : x ∈ closure Ω'' := subset_closure hx_Ω''
    have hx_in_Ω : x ∈ Ω := by
      have h1 : x ∈ Metric.cthickening h₀ (closure Ω'') :=
        Metric.self_subset_cthickening _ hx_closure_Ω''
      exact h_room h1
    have hx_he_in_Ω : x + (hₙ n) • EuclideanSpace.single k 1 ∈ Ω := by
      have h_dist : dist x (x + (hₙ n) • EuclideanSpace.single k 1) = |hₙ n| := by
        rw [dist_eq_norm]
        have heq : x - (x + (hₙ n) • EuclideanSpace.single k 1) =
            -((hₙ n) • EuclideanSpace.single k 1) := by abel
        rw [heq, norm_neg, norm_smul]
        rw [show ‖(EuclideanSpace.single k (1 : ℝ) : E)‖ = 1 by simp]
        rw [Real.norm_eq_abs, mul_one]
      have h_in_thick : x + (hₙ n) • EuclideanSpace.single k 1 ∈
          Metric.cthickening h₀ (closure Ω'') := by
        refine Metric.mem_cthickening_of_dist_le _ x h₀ (closure Ω'') hx_closure_Ω'' ?_
        rw [dist_comm]; rw [h_dist]; exact hₙ_bd n
      exact h_room h_in_thick
    have h_dq_apply : diffQuot k (hₙ n) w_ext x =
        (w_ext (x + (hₙ n) • EuclideanSpace.single k 1) - w_ext x) / (hₙ n) := by
      rw [diffQuot_apply_of_ne (d := d) k (hₙ_ne n) w_ext x]
    have h_dq_w_apply : diffQuot k (hₙ n) w x =
        (w (x + (hₙ n) • EuclideanSpace.single k 1) - w x) / (hₙ n) := by
      rw [diffQuot_apply_of_ne (d := d) k (hₙ_ne n) w x]
    rw [h_dq_apply, h_dq_w_apply]
    rw [hw_ext_eq_w_on_Ω _ hx_in_Ω, hw_ext_eq_w_on_Ω _ hx_he_in_Ω]
  have h_neg_h_int_eq_restrict : ∀ n,
      ∫ x, w_ext x * diffQuot k (-(hₙ n)) φ.1 x ∂(volume : Measure E) =
        ∫ x in Ω, w x * diffQuot k (-(hₙ n)) φ.1 x ∂(volume : Measure E) := by
    intro n
    have h_compl_zero : ∀ x ∉ Ω, w_ext x * diffQuot k (-(hₙ n)) φ.1 x = 0 := by
      intro x hx
      rw [hw_ext_zero_off_Ω x hx, zero_mul]
    have h_split : ∫ x, w_ext x * diffQuot k (-(hₙ n)) φ.1 x
          ∂(volume : Measure E) =
        ∫ x in Ω, w_ext x * diffQuot k (-(hₙ n)) φ.1 x
          ∂(volume : Measure E) := by
      symm
      rw [show (∫ x in Ω, w_ext x * diffQuot k (-(hₙ n)) φ.1 x
            ∂(volume : Measure E)) =
          ∫ x, Ω.indicator (fun y => w_ext y * diffQuot k (-(hₙ n)) φ.1 y) x
            ∂(volume : Measure E) from
        (integral_indicator hΩ_open.measurableSet).symm]
      refine integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro x
      by_cases hx : x ∈ Ω
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx]
        exact (h_compl_zero x hx).symm
    rw [h_split]
    refine integral_congr_ae ?_
    have h_ae : ∀ᵐ x ∂((volume : Measure E).restrict Ω),
        w_ext x * diffQuot k (-(hₙ n)) φ.1 x = w x * diffQuot k (-(hₙ n)) φ.1 x := by
      rw [ae_restrict_iff' hΩ_open.measurableSet]
      refine Filter.Eventually.of_forall ?_
      intro x hx
      rw [hw_ext_eq_w_on_Ω x hx]
    exact h_ae
  have hIBP : ∀ n,
      ∫ x, diffQuot k (hₙ n) w_ext x * φ.1 x ∂(volume : Measure E) =
        -∫ x, w_ext x * diffQuot k (-(hₙ n)) φ.1 x ∂(volume : Measure E) := by
    intro n
    exact integral_diffQuot_mul_eq_neg_integral_mul_diffQuot
      (d := d) k (hₙ_ne n) hw_ext_memLp hφ_memLp_global
  have h_LHS_restrict : ∀ n,
      ∫ x, diffQuot k (hₙ n) w_ext x * φ.1 x ∂(volume : Measure E) =
        ∫ x in Ω'', diffQuot k (hₙ n) w_ext x * φ.1 x
          ∂(volume : Measure E) := by
    intro n
    symm
    rw [show (∫ x in Ω'', diffQuot k (hₙ n) w_ext x * φ.1 x
          ∂(volume : Measure E)) =
        ∫ x, Ω''.indicator (fun y => diffQuot k (hₙ n) w_ext y * φ.1 y) x
          ∂(volume : Measure E) from
      (integral_indicator hΩ''_open.measurableSet).symm]
    refine integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    by_cases hx : x ∈ Ω''
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      have hxnot : x ∉ tsupport φ.1 := fun hxt => hx (φ.2.2.2 hxt)
      have hφx : φ.1 x = 0 := image_eq_zero_of_notMem_tsupport hxnot
      change (0 : ℝ) = diffQuot k (hₙ n) w_ext x * φ.1 x
      rw [hφx, mul_zero]
  have h_LHS_on_tsupport : ∀ n,
      ∫ x in Ω'', diffQuot k (hₙ n) w_ext x * φ.1 x ∂(volume : Measure E) =
        ∫ x in Ω'', diffQuot k (hₙ n) w x * φ.1 x
          ∂(volume : Measure E) := by
    intro n
    refine integral_congr_ae ?_
    have h_ae : ∀ᵐ x ∂((volume : Measure E).restrict Ω''),
        diffQuot k (hₙ n) w_ext x * φ.1 x = diffQuot k (hₙ n) w x * φ.1 x := by
      rw [ae_restrict_iff' hΩ''_open.measurableSet]
      refine Filter.Eventually.of_forall ?_
      intro x _hx
      by_cases hxt : x ∈ tsupport φ.1
      · rw [h_dq_eq_on_tsupport n x hxt]
      · have hφx : φ.1 x = 0 := image_eq_zero_of_notMem_tsupport hxt
        rw [hφx, mul_zero, mul_zero]
    exact h_ae
  have h_dq_aesm_global : ∀ n, AEStronglyMeasurable (diffQuot k (hₙ n) w_ext)
      (volume : Measure E) :=
    fun n => aestronglyMeasurable_diffQuot (d := d) k _ hw_ext_memLp.aestronglyMeasurable
  have h_dq_aesm_restrict : ∀ n, AEStronglyMeasurable (diffQuot k (hₙ n) w_ext)
      ((volume : Measure E).restrict Ω'') :=
    fun n => (h_dq_aesm_global n).restrict
  have h_dq_eq_on_Ω'' : ∀ n : ℕ, ∀ x ∈ Ω'',
      diffQuot k (hₙ n) w_ext x = diffQuot k (hₙ n) w x := by
    intro n x hx_Ω''
    have hx_closure : x ∈ closure Ω'' := subset_closure hx_Ω''
    have hx_in_Ω : x ∈ Ω :=
      h_room (Metric.self_subset_cthickening _ hx_closure)
    have hx_he_in_Ω : x + (hₙ n) • EuclideanSpace.single k 1 ∈ Ω := by
      have h_dist : dist x (x + (hₙ n) • EuclideanSpace.single k 1) = |hₙ n| := by
        rw [dist_eq_norm]
        have heq : x - (x + (hₙ n) • EuclideanSpace.single k 1) =
            -((hₙ n) • EuclideanSpace.single k 1) := by abel
        rw [heq, norm_neg, norm_smul]
        rw [show ‖(EuclideanSpace.single k (1 : ℝ) : E)‖ = 1 by simp]
        rw [Real.norm_eq_abs, mul_one]
      have h_in_thick : x + (hₙ n) • EuclideanSpace.single k 1 ∈
          Metric.cthickening h₀ (closure Ω'') := by
        refine Metric.mem_cthickening_of_dist_le _ x h₀ (closure Ω'') hx_closure ?_
        rw [dist_comm]; rw [h_dist]; exact hₙ_bd n
      exact h_room h_in_thick
    have h_dq_apply : diffQuot k (hₙ n) w_ext x =
        (w_ext (x + (hₙ n) • EuclideanSpace.single k 1) - w_ext x) / (hₙ n) := by
      rw [diffQuot_apply_of_ne (d := d) k (hₙ_ne n) w_ext x]
    have h_dq_w_apply : diffQuot k (hₙ n) w x =
        (w (x + (hₙ n) • EuclideanSpace.single k 1) - w x) / (hₙ n) := by
      rw [diffQuot_apply_of_ne (d := d) k (hₙ_ne n) w x]
    rw [h_dq_apply, h_dq_w_apply]
    rw [hw_ext_eq_w_on_Ω _ hx_in_Ω, hw_ext_eq_w_on_Ω _ hx_he_in_Ω]
  have h_dq_ae_eq_restrict : ∀ n, diffQuot k (hₙ n) w_ext =ᵐ[
        (volume : Measure E).restrict Ω''] diffQuot k (hₙ n) w := by
    intro n
    rw [Filter.EventuallyEq, ae_restrict_iff' hΩ''_open.measurableSet]
    refine Filter.Eventually.of_forall ?_
    intro x hx
    exact h_dq_eq_on_Ω'' n x hx
  have h_dq_aesm_restrict_w : ∀ n, AEStronglyMeasurable (diffQuot k (hₙ n) w)
      ((volume : Measure E).restrict Ω'') := fun n =>
    (h_dq_aesm_restrict n).congr (h_dq_ae_eq_restrict n)
  have h_dq_memLp_restrict_w : ∀ n, MemLp (diffQuot k (hₙ n) w) 2
      ((volume : Measure E).restrict Ω'') := fun n =>
    memLp_iff.mpr (lt_of_le_of_lt (h_dq_l2_bound n) ENNReal.ofReal_lt_top)
  have h_CS_bound : ∀ n,
      |∫ x in Ω'', diffQuot k (hₙ n) w x * φ.1 x ∂(volume : Measure E)| ≤
        M * (eLpNorm φ.1 2 ((volume : Measure E).restrict Ω'')).toReal := by
    intro n
    have h_cs := abs_integral_mul_le_norm_lp_mul_norm_lp_local
      (μ := (volume : Measure E).restrict Ω'') (h_dq_memLp_restrict_w n) hφ_memLp
    have h_dq_bound :
        (eLpNorm (diffQuot k (hₙ n) w) 2 ((volume : Measure E).restrict Ω'')).toReal
          ≤ M := by
      have hMto : (ENNReal.ofReal M).toReal = M := ENNReal.toReal_ofReal hM_nn
      calc (eLpNorm (diffQuot k (hₙ n) w) 2 ((volume : Measure E).restrict Ω'')).toReal
          ≤ (ENNReal.ofReal M).toReal := by
            refine ENNReal.toReal_mono ENNReal.ofReal_ne_top ?_
            exact h_dq_l2_bound n
        _ = M := hMto
    have h_phi_nn : 0 ≤ (eLpNorm φ.1 2 ((volume : Measure E).restrict Ω'')).toReal :=
      ENNReal.toReal_nonneg
    have hMul :
        (eLpNorm (diffQuot k (hₙ n) w) 2 ((volume : Measure E).restrict Ω'')).toReal *
            (eLpNorm φ.1 2 ((volume : Measure E).restrict Ω'')).toReal ≤
          M * (eLpNorm φ.1 2 ((volume : Measure E).restrict Ω'')).toReal :=
      mul_le_mul_of_nonneg_right h_dq_bound h_phi_nn
    have h_int_eq :
        ∫ x in Ω'', diffQuot k (hₙ n) w x * φ.1 x ∂(volume : Measure E) =
          ∫ x, diffQuot k (hₙ n) w x * φ.1 x ∂((volume : Measure E).restrict Ω'') :=
      rfl
    rw [h_int_eq]
    linarith
  have h_dual_bound : ∀ n,
      |∫ x, w_ext x * diffQuot k (-(hₙ n)) φ.1 x ∂(volume : Measure E)| ≤
        M * (eLpNorm φ.1 2 ((volume : Measure E).restrict Ω'')).toReal := by
    intro n
    have h_IBP_n := hIBP n
    have h_LHS_eq : ∫ x, diffQuot k (hₙ n) w_ext x * φ.1 x ∂(volume : Measure E) =
        ∫ x in Ω'', diffQuot k (hₙ n) w x * φ.1 x ∂(volume : Measure E) := by
      rw [h_LHS_restrict n, h_LHS_on_tsupport n]
    have h_LHS_abs : |∫ x, diffQuot k (hₙ n) w_ext x * φ.1 x ∂(volume : Measure E)| =
        |∫ x in Ω'', diffQuot k (hₙ n) w x * φ.1 x ∂(volume : Measure E)| := by
      rw [h_LHS_eq]
    have h_LHS_le_bound :
        |∫ x, diffQuot k (hₙ n) w_ext x * φ.1 x ∂(volume : Measure E)| ≤
          M * (eLpNorm φ.1 2 ((volume : Measure E).restrict Ω'')).toReal := by
      rw [h_LHS_abs]; exact h_CS_bound n
    have h_RHS_eq_LHS : |∫ x, w_ext x * diffQuot k (-(hₙ n)) φ.1 x ∂(volume : Measure E)| =
        |∫ x, diffQuot k (hₙ n) w_ext x * φ.1 x ∂(volume : Measure E)| := by
      rw [h_IBP_n, abs_neg]
    rw [h_RHS_eq_LHS]
    exact h_LHS_le_bound
  have h_dual_bound_restrict : ∀ n,
      |∫ x in Ω, w x * diffQuot k (-(hₙ n)) φ.1 x ∂(volume : Measure E)| ≤
        M * (eLpNorm φ.1 2 ((volume : Measure E).restrict Ω'')).toReal := by
    intro n
    rw [← h_neg_h_int_eq_restrict n]
    exact h_dual_bound n
  have h_abs_convergence :
      Tendsto (fun n =>
          |∫ x in Ω, w x * diffQuot k (-(hₙ n)) φ.1 x ∂(volume : Measure E)|)
        atTop
        (𝓝 |∫ x in Ω, w x * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1)
          ∂(volume : Measure E)|) := by
    have := h_convergence.abs
    simpa using this
  exact le_of_tendsto_of_tendsto'
    h_abs_convergence tendsto_const_nhds (fun n => h_dual_bound_restrict n)

private lemma abs_smoothTestFunctional_local_le_lpNorm
    {Ω : Set E} (hΩ_open : IsOpen Ω)
    {Ω'' : Set E} (hΩ''_open : IsOpen Ω'')
    {h₀ : ℝ} (hh₀ : 0 < h₀)
    (h_room : Metric.cthickening h₀ (closure Ω'') ⊆ Ω)
    {w : E → ℝ}
    (hw_l2 : MemLp w 2 ((volume : Measure E).restrict Ω))
    (k : Fin d) {M : ℝ} (hM_nn : 0 ≤ M)
    (h_bdd : ∀ h : ℝ, 0 < |h| → |h| ≤ h₀ →
      eLpNorm (diffQuot k h w) 2 ((volume : Measure E).restrict Ω'')
        ≤ ENNReal.ofReal M)
    (φ : smoothCompactlySupportedInSubmodule (d := d) Ω'') :
    |smoothTestFunctionalLocal (d := d) (Ω := Ω) (Ω'' := Ω'') hw_l2 k φ| ≤
      M * ‖smoothCompactlySupportedInToLp (d := d) Ω'' φ‖ := by
  have h := abs_smoothTestFunctional_local_le (d := d) hΩ_open hΩ''_open
    hh₀ h_room hw_l2 k hM_nn h_bdd φ
  have h_norm_eq :
      ‖smoothCompactlySupportedInToLp (d := d) Ω'' φ‖ =
        (eLpNorm φ.1 2 ((volume : Measure E).restrict Ω'')).toReal := by
    rw [show (smoothCompactlySupportedInToLp (d := d) Ω'' φ :
        Lp ℝ 2 ((volume : Measure E).restrict Ω'')) =
      (memLp_two_restrict_of_smoothCompactlySupported (d := d) (Ω'' := Ω'') φ.2.1 φ.2.2.1).toLp
        φ.1 from rfl]
    exact Lp.norm_toLp _ _
  rw [h_norm_eq]
  exact h

variable [NeZero d] in
private def smoothTestFunctionalLocalExt
    {Ω Ω'' : Set E}
    {w : E → ℝ}
    (hw_l2 : MemLp w 2 ((volume : Measure E).restrict Ω))
    (k : Fin d) :
    Lp ℝ 2 ((volume : Measure E).restrict Ω'') →L[ℝ] ℝ :=
  (smoothTestFunctionalLocal (d := d) (Ω := Ω) (Ω'' := Ω'') hw_l2 k).extendOfNorm
    (smoothCompactlySupportedInToLp (d := d) Ω'')

private lemma opNorm_smoothTestFunctional_local_ext_le
    {Ω : Set E} (hΩ_open : IsOpen Ω)
    {Ω'' : Set E} (hΩ''_open : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    {h₀ : ℝ} (hh₀ : 0 < h₀)
    (h_room : Metric.cthickening h₀ (closure Ω'') ⊆ Ω)
    {w : E → ℝ}
    (hw_l2 : MemLp w 2 ((volume : Measure E).restrict Ω))
    (k : Fin d) {M : ℝ} (hM_nn : 0 ≤ M)
    (h_bdd : ∀ h : ℝ, 0 < |h| → |h| ≤ h₀ →
      eLpNorm (diffQuot k h w) 2 ((volume : Measure E).restrict Ω'')
        ≤ ENNReal.ofReal M) :
    ‖smoothTestFunctionalLocalExt (d := d) (Ω := Ω) (Ω'' := Ω'') hw_l2 k‖ ≤ M := by
  unfold smoothTestFunctionalLocalExt
  refine LinearMap.opNorm_extendOfNorm_le
    (denseRange_smoothCompactlySupportedInToLp (d := d) hΩ''_open hΩ''_compact_closure)
    hM_nn ?_
  intro φ
  exact abs_smoothTestFunctional_local_le_lpNorm (d := d) hΩ_open hΩ''_open hh₀ h_room hw_l2 k hM_nn h_bdd φ

private lemma smoothTestFunctional_local_ext_apply
    {Ω : Set E} (hΩ_open : IsOpen Ω)
    {Ω'' : Set E} (hΩ''_open : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    {h₀ : ℝ} (hh₀ : 0 < h₀)
    (h_room : Metric.cthickening h₀ (closure Ω'') ⊆ Ω)
    {w : E → ℝ}
    (hw_l2 : MemLp w 2 ((volume : Measure E).restrict Ω))
    (k : Fin d) {M : ℝ} (hM_nn : 0 ≤ M)
    (h_bdd : ∀ h : ℝ, 0 < |h| → |h| ≤ h₀ →
      eLpNorm (diffQuot k h w) 2 ((volume : Measure E).restrict Ω'')
        ≤ ENNReal.ofReal M)
    (φ : smoothCompactlySupportedInSubmodule (d := d) Ω'') :
    smoothTestFunctionalLocalExt (d := d) (Ω := Ω) (Ω'' := Ω'') hw_l2 k
        (smoothCompactlySupportedInToLp (d := d) Ω'' φ) =
      smoothTestFunctionalLocal (d := d) (Ω := Ω) (Ω'' := Ω'') hw_l2 k φ := by
  unfold smoothTestFunctionalLocalExt
  refine LinearMap.extendOfNorm_eq
    (denseRange_smoothCompactlySupportedInToLp (d := d) hΩ''_open hΩ''_compact_closure)
    ⟨M, ?_⟩ φ
  intro ψ
  exact abs_smoothTestFunctional_local_le_lpNorm (d := d) hΩ_open hΩ''_open hh₀ h_room hw_l2 k hM_nn h_bdd ψ

variable [NeZero d] in
private def smoothTestFunctionalLocalRiesz
    {Ω Ω'' : Set E}
    {w : E → ℝ}
    (hw_l2 : MemLp w 2 ((volume : Measure E).restrict Ω))
    (k : Fin d) :
    Lp ℝ 2 ((volume : Measure E).restrict Ω'') :=
  (InnerProductSpace.toDual ℝ
      (Lp ℝ 2 ((volume : Measure E).restrict Ω''))).symm
    (smoothTestFunctionalLocalExt (d := d) (Ω := Ω) (Ω'' := Ω'') hw_l2 k)

private lemma norm_smoothTestFunctional_local_riesz
    {Ω Ω'' : Set E}
    {w : E → ℝ}
    (hw_l2 : MemLp w 2 ((volume : Measure E).restrict Ω))
    (k : Fin d) :
    ‖smoothTestFunctionalLocalRiesz (d := d) (Ω := Ω) (Ω'' := Ω'') hw_l2 k‖ =
      ‖smoothTestFunctionalLocalExt (d := d) (Ω := Ω) (Ω'' := Ω'') hw_l2 k‖ := by
  unfold smoothTestFunctionalLocalRiesz
  exact (InnerProductSpace.toDual ℝ
    (Lp ℝ 2 ((volume : Measure E).restrict Ω''))).symm.norm_map _

private lemma smoothTestFunctional_local_ext_eq_inner
    {Ω Ω'' : Set E}
    {w : E → ℝ}
    (hw_l2 : MemLp w 2 ((volume : Measure E).restrict Ω))
    (k : Fin d)
    (f : Lp ℝ 2 ((volume : Measure E).restrict Ω'')) :
    smoothTestFunctionalLocalExt (d := d) (Ω := Ω) (Ω'' := Ω'') hw_l2 k f =
      ⟪smoothTestFunctionalLocalRiesz (d := d) (Ω := Ω) (Ω'' := Ω'') hw_l2 k, f⟫_ℝ := by
  unfold smoothTestFunctionalLocalRiesz
  rw [InnerProductSpace.toDual_symm_apply]

theorem hasWeakPartialDeriv_of_diffQuot_uniform_bound_local
    {Ω : Set E} (hΩ_open : IsOpen Ω)
    {Ω'' : Set E} (hΩ''_open : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    {h₀ : ℝ} (hh₀ : 0 < h₀)
    (h_room : Metric.cthickening h₀ (closure Ω'') ⊆ Ω)
    {w : E → ℝ}
    (hw_l2 : MemLp w 2 ((volume : Measure E).restrict Ω))
    (k : Fin d) {M : ℝ} (hM_nn : 0 ≤ M)
    (h_bdd : ∀ h : ℝ, 0 < |h| → |h| ≤ h₀ →
      eLpNorm (diffQuot k h w) 2 ((volume : Measure E).restrict Ω'')
        ≤ ENNReal.ofReal M) :
    ∃ g : E → ℝ,
      MemLp g 2 ((volume : Measure E).restrict Ω'') ∧
      Sobolev.Euclidean.HasWeakPartialDeriv (d := d) k g w Ω'' ∧
      eLpNorm g 2 ((volume : Measure E).restrict Ω'') ≤ ENNReal.ofReal M := by
  have h_closure_in_room :
      closure Ω'' ⊆ Metric.cthickening h₀ (closure Ω'') := by
    intro x hx
    exact Metric.self_subset_cthickening (δ := h₀) (closure Ω'') hx
  have hΩ''_in_Ω : closure Ω'' ⊆ Ω := h_closure_in_room.trans h_room
  set g_lp : Lp ℝ 2 ((volume : Measure E).restrict Ω'') :=
    smoothTestFunctionalLocalRiesz (d := d) (Ω := Ω) (Ω'' := Ω'') hw_l2 k with hg_lp_def
  refine ⟨⇑g_lp, ?_, ?_, ?_⟩
  · exact Lp.memLp g_lp
  · intro φ hφ_smooth hφ_support hφ_support_in
    set φ_cs : smoothCompactlySupportedInSubmodule (d := d) Ω'' :=
      ⟨φ, hφ_smooth, hφ_support, hφ_support_in⟩ with hφ_cs_def
    have h_ext_apply :=
      smoothTestFunctional_local_ext_apply (d := d) hΩ_open hΩ''_open
        hΩ''_compact_closure hh₀ h_room hw_l2 k hM_nn h_bdd φ_cs
    have h_ext_inner :=
      smoothTestFunctional_local_ext_eq_inner (d := d) (Ω := Ω) (Ω'' := Ω'') hw_l2 k
        (smoothCompactlySupportedInToLp (d := d) Ω'' φ_cs)
    have h_func_val :
        smoothTestFunctionalLocal (d := d) (Ω := Ω) (Ω'' := Ω'') hw_l2 k φ_cs =
          -∫ x in Ω, w x * (fderiv ℝ φ x) (EuclideanSpace.single k 1)
            ∂(volume : Measure E) := by
      rw [smoothTestFunctional_local_apply]
    have h_inner_def := L2.inner_def (𝕜 := ℝ) g_lp
      (smoothCompactlySupportedInToLp (d := d) Ω'' φ_cs)
    have h_coeFn_phi :
        ⇑(smoothCompactlySupportedInToLp (d := d) Ω'' φ_cs) =ᵐ[
          (volume : Measure E).restrict Ω''] φ := by
      simp only [smoothCompactlySupportedInToLp_apply]
      exact MemLp.coeFn_toLp _
    have h_int_eq :
        ∫ x, ⟪g_lp x, (smoothCompactlySupportedInToLp (d := d) Ω'' φ_cs) x⟫_ℝ
          ∂((volume : Measure E).restrict Ω'') =
          ∫ x in Ω'', g_lp x * φ x ∂(volume : Measure E) := by
      have h_eq : ∫ x, ⟪g_lp x,
            (smoothCompactlySupportedInToLp (d := d) Ω'' φ_cs) x⟫_ℝ
          ∂((volume : Measure E).restrict Ω'') =
          ∫ x, g_lp x * φ x ∂((volume : Measure E).restrict Ω'') := by
        refine integral_congr_ae ?_
        filter_upwards [h_coeFn_phi] with x hx
        have h_inner_eq :
            ⟪(g_lp x : ℝ), (smoothCompactlySupportedInToLp (d := d) Ω'' φ_cs) x⟫_ℝ =
              (smoothCompactlySupportedInToLp (d := d) Ω'' φ_cs) x * (g_lp x : ℝ) :=
          RCLike.inner_apply (𝕜 := ℝ) (g_lp x)
            ((smoothCompactlySupportedInToLp (d := d) Ω'' φ_cs) x)
        rw [h_inner_eq, hx]; ring
      rw [h_eq]
    have h_chain :
        smoothTestFunctionalLocal (d := d) (Ω := Ω) (Ω'' := Ω'') hw_l2 k φ_cs =
          ∫ x in Ω'', g_lp x * φ x ∂(volume : Measure E) := by
      rw [← h_ext_apply, h_ext_inner, h_inner_def, h_int_eq]
    rw [h_func_val] at h_chain
    have h_int_Ω_eq_Ω'' :
        ∫ x in Ω, w x * (fderiv ℝ φ x) (EuclideanSpace.single k 1)
            ∂(volume : Measure E) =
          ∫ x in Ω'', w x * (fderiv ℝ φ x) (EuclideanSpace.single k 1)
            ∂(volume : Measure E) := by
      have h_partial_zero_off_Ω'' : ∀ x ∉ Ω'',
          (fderiv ℝ φ x) (EuclideanSpace.single k 1) = 0 := by
        intro x hx
        have hxnot : x ∉ tsupport φ := fun hxt => hx (hφ_support_in hxt)
        have h_eq_zero : φ =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
          have h_open := isClosed_tsupport φ |>.isOpen_compl
          have h_nhd := h_open.mem_nhds hxnot
          filter_upwards [h_nhd] with y hy
          have hy_support : y ∉ Function.support φ := fun hy_in_support =>
            hy (subset_tsupport _ hy_in_support)
          rwa [Function.mem_support, not_not] at hy_support
        have h_fderiv_eq : fderiv ℝ φ x = fderiv ℝ (fun _ : E => (0 : ℝ)) x :=
          h_eq_zero.fderiv_eq
        rw [h_fderiv_eq]
        simp
      have h_split : ∫ x in Ω,
            w x * (fderiv ℝ φ x) (EuclideanSpace.single k 1)
              ∂(volume : Measure E) =
          ∫ x in Ω'',
            w x * (fderiv ℝ φ x) (EuclideanSpace.single k 1)
              ∂(volume : Measure E) := by
        have h_zero_on_diff : ∀ x ∉ Ω'',
            w x * (fderiv ℝ φ x) (EuclideanSpace.single k 1) = 0 := by
          intro x hx
          rw [h_partial_zero_off_Ω'' x hx, mul_zero]
        have h_int_E_Ω : ∫ x in Ω,
              w x * (fderiv ℝ φ x) (EuclideanSpace.single k 1)
                ∂(volume : Measure E) =
            ∫ x, Ω.indicator (fun y => w y *
                (fderiv ℝ φ y) (EuclideanSpace.single k 1)) x
              ∂(volume : Measure E) :=
          (integral_indicator hΩ_open.measurableSet).symm
        have h_int_E_Ω'' : ∫ x in Ω'',
              w x * (fderiv ℝ φ x) (EuclideanSpace.single k 1)
                ∂(volume : Measure E) =
            ∫ x, Ω''.indicator (fun y => w y *
                (fderiv ℝ φ y) (EuclideanSpace.single k 1)) x
              ∂(volume : Measure E) :=
          (integral_indicator hΩ''_open.measurableSet).symm
        rw [h_int_E_Ω, h_int_E_Ω'']
        refine integral_congr_ae ?_
        refine Filter.Eventually.of_forall ?_
        intro x
        by_cases hx_Ω'' : x ∈ Ω''
        · have hx_Ω : x ∈ Ω := hΩ''_in_Ω (subset_closure hx_Ω'')
          rw [Set.indicator_of_mem hx_Ω, Set.indicator_of_mem hx_Ω'']
        · rw [Set.indicator_of_notMem hx_Ω'']
          by_cases hx_Ω : x ∈ Ω
          · rw [Set.indicator_of_mem hx_Ω]
            exact h_zero_on_diff x hx_Ω''
          · rw [Set.indicator_of_notMem hx_Ω]
      exact h_split
    rw [h_int_Ω_eq_Ω''] at h_chain
    linarith
  · have h_norm_eq := norm_smoothTestFunctional_local_riesz (d := d) (Ω := Ω)
      (Ω'' := Ω'') hw_l2 k
    have h_op_le := opNorm_smoothTestFunctional_local_ext_le (d := d) hΩ_open
      hΩ''_open hΩ''_compact_closure hh₀ h_room hw_l2 k hM_nn h_bdd
    have h_g_lp_le : ‖g_lp‖ ≤ M := by
      rw [hg_lp_def]
      rw [h_norm_eq]
      exact h_op_le
    have h_g_lp_nn : 0 ≤ ‖g_lp‖ := norm_nonneg _
    have h_enorm_le : (‖g_lp‖ₑ : ℝ≥0∞) ≤ ENNReal.ofReal M := by
      have hofreal : (‖g_lp‖ₑ : ℝ≥0∞) = ENNReal.ofReal ‖g_lp‖ :=
        (ofReal_norm _).symm
      rw [hofreal]
      exact ENNReal.ofReal_le_ofReal h_g_lp_le
    have h_enorm_eq : ‖g_lp‖ₑ =
        eLpNorm (⇑g_lp) 2 ((volume : Measure E).restrict Ω'') :=
      Lp.enorm_def g_lp
    rw [← h_enorm_eq]
    exact h_enorm_le

end Sobolev
end Analysis
end CalabiYau
