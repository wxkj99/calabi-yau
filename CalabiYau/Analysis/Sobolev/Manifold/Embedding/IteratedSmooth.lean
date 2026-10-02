-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Manifold/Embedding/IteratedSmooth.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Manifold.Embedding.Iterated
public import CalabiYau.Analysis.Sobolev.Manifold.Morrey.HigherOrder
public import CalabiYau.Analysis.Sobolev.Euclidean.Embedding.Morrey.HigherOrder

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal
open _root_.CalabiYau.Analysis.Sobolev.Chart

namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private noncomputable def witnessOrderC0 (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] : ℕ :=
  Module.finrank ℝ E + 1

private lemma witnessOrderC0_pos {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] :
    1 ≤ witnessOrderC0 E := by
  unfold witnessOrderC0
  omega

private lemma witnessOrderC0_two_gt_dim {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] :
    (Module.finrank ℝ E : ℝ) < (witnessOrderC0 E : ℝ) * 2 := by
  unfold witnessOrderC0
  push_cast
  linarith [show (0 : ℝ) ≤ Module.finrank ℝ E from Nat.cast_nonneg _]

def HasSupercriticalChartSobolevRegularity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] (m : ℕ) (u : M → ℝ) : Prop :=
  ∃ p : ℝ, 1 ≤ p ∧ (Module.finrank ℝ E : ℝ) < p ∧
    MemWkpChart (I := I) (M := M) (m + 1) (ENNReal.ofReal p) u

theorem memWkpChart_forall_implies_contMDiff_m_representative
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] (g : CalabiYau.SmoothRiemannianMetric I M)
    (m : ℕ)
    {u : M → ℝ} (hu_meas : Measurable u)
    (h_witness : HasSupercriticalChartSobolevRegularity (I := I) (M := M) m u)
    (h_bridge :
      ∀ {p : ℝ}, (Module.finrank ℝ E : ℝ) < p →
        ∀ {v : M → ℝ}, Measurable v →
          MemWkpChart (I := I) (M := M) (m + 1) (ENNReal.ofReal p) v →
            ∃ v_smooth : M → ℝ,
              ContMDiff I 𝓘(ℝ, ℝ) m v_smooth ∧
              v_smooth =ᵐ[CalabiYau.RiemannianVolume.riemannianVolumeMeasure
                (I := I) (M := M) g] v) :
    ∃ u_smooth : M → ℝ,
      ContMDiff I 𝓘(ℝ, ℝ) m u_smooth ∧
      u_smooth =ᵐ[CalabiYau.RiemannianVolume.riemannianVolumeMeasure
        (I := I) (M := M) g] u := by
  obtain ⟨p, _hp_one, hp_dim, hu_super⟩ := h_witness
  exact h_bridge hp_dim hu_meas hu_super

namespace SupercriticalChartEmbedding

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
variable [NeZero (Module.finrank ℝ E)]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

end SupercriticalChartEmbedding

namespace SupercriticalExponentIteration

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
variable [NeZero (Module.finrank ℝ E)]

private theorem chain_to_supercritical
    (g : CalabiYau.SmoothRiemannianMetric I M)
    (m : ℕ) :
    ∀ (s : ℕ) {p : ℝ}, 1 ≤ p →
      _root_.CalabiYau.Analysis.Sobolev.Chart.RegularExponent.IsRegular
        (Module.finrank ℝ E : ℝ) p (s + 1) →
      (Module.finrank ℝ E : ℝ) < ((s + 1 : ℕ) : ℝ) * p →
      ∀ {u : M → ℝ},
        MemWkpChart (I := I) (M := M) (m + 1 + s) (ENNReal.ofReal p) u →
          ∃ q : ℝ, 1 ≤ q ∧ (Module.finrank ℝ E : ℝ) < q ∧
            MemWkpChart (I := I) (M := M) (m + 1) (ENNReal.ofReal q) u := by
  intro s
  induction s with
  | zero =>
      intro p hp_one _hreg hkp u hu
      have hp_dim : (Module.finrank ℝ E : ℝ) < p := by
        have : ((0 + 1 : ℕ) : ℝ) = 1 := by norm_num
        rw [this, one_mul] at hkp
        exact hkp
      refine ⟨p, hp_one, hp_dim, ?_⟩
      simpa using hu
  | succ s ih =>
      intro p hp_one hreg hkp u hu
      have hp_ne_n : p ≠ (Module.finrank ℝ E : ℝ) :=
        hreg.p_ne_n_of_one_le (by omega)
      rcases lt_or_gt_of_ne hp_ne_n with hp_lt | hp_gt
      · have hp_pos : 0 < p := by linarith
        obtain ⟨_C, _hC_nn, h_step⟩ :=
          wkpNormChart_succ_subcritical_step (I := I) (M := M) g (k := m + 1 + s)
            hp_one hp_lt
        have hu' : MemWkpChart (I := I) (M := M) ((m + 1 + s) + 1)
            (ENNReal.ofReal p) u := by
          have : m + 1 + (s + 1) = (m + 1 + s) + 1 := by ring
          rw [this] at hu
          exact hu
        obtain ⟨h_mem_p1, _h_norm_p1⟩ := h_step hu'
        set p_1 : ℝ := (Module.finrank ℝ E : ℝ) * p /
          ((Module.finrank ℝ E : ℝ) - p) with hp_1_def
        have hd_pos : 0 < (Module.finrank ℝ E : ℝ) := by
          have : 0 < Module.finrank ℝ E := NeZero.pos _
          exact_mod_cast this
        have hd_p_pos : 0 < (Module.finrank ℝ E : ℝ) - p := by linarith
        have hp_1_ge_p : p ≤ p_1 := by
          rw [hp_1_def, le_div_iff₀ hd_p_pos]
          nlinarith [hp_pos]
        have hp_1_one : 1 ≤ p_1 := le_trans hp_one hp_1_ge_p
        have hkp_next : (Module.finrank ℝ E : ℝ) < ((s + 1 : ℕ) : ℝ) * p_1 := by
          have h_form : (Module.finrank ℝ E : ℝ) < ((s + 1 : ℕ) + 1 : ℝ) * p := by
            have hkp_cast : ((s + 1 + 1 : ℕ) : ℝ) * p =
                ((s + 1 : ℕ) + 1 : ℝ) * p := by push_cast; ring
            rw [hkp_cast] at hkp
            exact hkp
          have h_id :=
            _root_.CalabiYau.Analysis.Sobolev.Chart.IterationCalc.kp1_real_gt_d_of_kp1p_gt_d
              (Module.finrank ℝ E) (s + 1) p hp_pos hp_lt h_form
          rw [hp_1_def]
          exact h_id
        have hreg_p_1 :
            _root_.CalabiYau.Analysis.Sobolev.Chart.RegularExponent.IsRegular
              (Module.finrank ℝ E : ℝ) p_1 (s + 1) := by
          rw [hp_1_def]
          exact hreg.tower_step hp_one hp_lt
        have h_mem_p1' : MemWkpChart (I := I) (M := M) (m + 1 + s)
            (ENNReal.ofReal p_1) u := by
          rw [hp_1_def]; exact h_mem_p1
        exact ih hp_1_one hreg_p_1 hkp_next h_mem_p1'
      · have hu_order : MemWkpChart (I := I) (M := M) (m + 1) (ENNReal.ofReal p) u :=
          MemWkpChart.le_of_le (by omega) hu
        exact ⟨p, hp_one, hp_gt, hu_order⟩

end SupercriticalExponentIteration

theorem hasSupercriticalChartSobolevRegularity_of_all_even_orders
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    (m : ℕ)
    {u : M → ℝ}
    (h_all : ∀ k : ℕ, MemWkpChart (I := I) (M := M) (2 * k) 2 u) :
    HasSupercriticalChartSobolevRegularity (I := I) (M := M) m u := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  have hn_pos : 0 < n := NeZero.pos _
  set s_max : ℕ := n with hs_max_def
  have hp_2_strict : (1 : ℝ) < 2 := by norm_num
  have hs_max_succ_pos : 1 ≤ s_max + 1 := by omega
  have h_n_lt_kp_2 : (n : ℝ) < ((s_max + 1 : ℕ) : ℝ) * 2 := by
    have : (n : ℝ) < (2 * (n + 1) : ℕ) := by
      push_cast; linarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
    have heq : ((s_max + 1 : ℕ) : ℝ) * 2 = (2 * (n + 1) : ℕ) := by
      rw [hs_max_def]; push_cast; ring
    rw [heq]; exact this
  obtain ⟨p₀, hp₀_one, hp₀_lt, h_n_lt_kp₀, hp₀_regularity⟩ :=
    _root_.CalabiYau.Analysis.Sobolev.Chart.RegularExponent.exists_regular_exponent_below
      (n : ℝ) (s_max + 1) hs_max_succ_pos hp_2_strict h_n_lt_kp_2
  set k₀ : ℕ := m + n + 1 with hk₀_def
  have h2k₀_ge : m + 1 + s_max ≤ 2 * k₀ := by
    rw [hs_max_def, hk₀_def]; omega
  have hu_at_2k₀ : MemWkpChart (I := I) (M := M) (2 * k₀) 2 u := h_all k₀
  have hu_order : MemWkpChart (I := I) (M := M) (m + 1 + s_max) 2 u :=
    MemWkpChart.le_of_le h2k₀_ge hu_at_2k₀
  have h_two_eq : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num]
    rw [ENNReal.ofReal_natCast]
    rfl
  have hu_order' : MemWkpChart (I := I) (M := M) (m + 1 + s_max)
      (ENNReal.ofReal 2) u := by rw [← h_two_eq]; exact hu_order
  have hp₀_one_enn : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p₀ := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal hp₀_one
  have hp₀_le_two_enn : ENNReal.ofReal p₀ ≤ ENNReal.ofReal 2 :=
    ENNReal.ofReal_le_ofReal hp₀_lt.le
  have hu_p₀ : MemWkpChart (I := I) (M := M) (m + 1 + s_max)
      (ENNReal.ofReal p₀) u :=
    _root_.CalabiYau.Analysis.Sobolev.Chart.ChartLevelMonoExp.memWkpChart_mono_exponent
      (I := I) (M := M) hp₀_one_enn hp₀_le_two_enn hu_order'
  exact SupercriticalExponentIteration.chain_to_supercritical (I := I) (M := M) g m s_max
    hp₀_one hp₀_regularity h_n_lt_kp₀ hu_p₀

namespace SupercriticalChartEmbedding

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
variable [NeZero (Module.finrank ℝ E)]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [CompactSpace M] [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
private lemma chartPushed_apply_toE_extChartAt
    (α : M) (u : M → ℝ) {x : M} (hx : x ∈ (chartAt H α).source) :
    chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u
        ((toEuclidean (E := E)) (extChartAt I α x)) =
      ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x) * u x := by
  classical
  unfold chartPushed
  have h_x_source : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source (I := I)]; exact hx
  have h_inv :
      (extChartAt I α).symm
        ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I α x))) = x := by
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact (extChartAt I α).left_inv h_x_source
  rw [h_inv]

omit [CompactSpace M] [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
private lemma continuousOn_chartPushed_of_continuous
    (α : M) {ũ : M → ℝ} (hũ_cont : Continuous ũ) :
    ContinuousOn (chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α ũ)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  unfold chartPushed
  have h_inv_cont : ContinuousOn
      (fun y : EuclN =>
        (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
      (chartTargetEuclid (I := I) (M := M) α) :=
    continuousOn_symm_toEuclideanSymm (I := I) (M := M) α
  have hρ_cont : Continuous
      ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
    (CalabiYau.RiemannianVolume.chartAtlasPOU I M α).contMDiff.continuous
  exact (hρ_cont.comp_continuousOn h_inv_cont).mul (hũ_cont.comp_continuousOn h_inv_cont)

omit [IsManifold I ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    [NeZero (Module.finrank ℝ E)] in
private lemma exists_ball_subset_chartTargetEuclid
    (α : M) {y₀ : EuclN} (hy₀ : y₀ ∈ chartTargetEuclid (I := I) (M := M) α) :
    ∃ R : ℝ, 0 < R ∧ Metric.ball y₀ R ⊆ chartTargetEuclid (I := I) (M := M) α := by
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  exact Metric.isOpen_iff.mp hopen y₀ hy₀

theorem exists_contMDiff_representative_of_supercritical_chart_sobolev
    (g : CalabiYau.SmoothRiemannianMetric I M)
    (m : ℕ)
    {p : ℝ} (hp : (Module.finrank ℝ E : ℝ) < p)
    {u : M → ℝ} (hu_meas : Measurable u)
    (hu : MemWkpChart (I := I) (M := M) (m + 1) (ENNReal.ofReal p) u) :
    ∃ u_smooth : M → ℝ,
      ContMDiff I 𝓘(ℝ, ℝ) m u_smooth ∧
      u_smooth =ᵐ[CalabiYau.RiemannianVolume.riemannianVolumeMeasure
        (I := I) (M := M) g] u := by
  classical
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  let : MeasurableSpace M := borel M
  have : BorelSpace M := ⟨rfl⟩
  have hn_pos : 0 < Module.finrank ℝ E := NeZero.pos _
  have hn_real_pos : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by exact_mod_cast hn_pos
  have hn_one : 1 ≤ Module.finrank ℝ E := hn_pos
  have hn_real_one : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by exact_mod_cast hn_one
  have hp_pos : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg _) hp
  have hp_one : 1 ≤ p := le_trans hn_real_one hp.le
  have hp_one_strict : 1 < p := lt_of_le_of_lt hn_real_one hp
  have hp_enn_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal hp_one
  have h_m1_pos : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have h_kp_gt_n : (Module.finrank ℝ E : ℝ) < ((m + 1 : ℕ) : ℝ) * p := by
    have h_m1_real_pos : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
      push_cast; linarith
    have h_le : p ≤ ((m + 1 : ℕ) : ℝ) * p := by
      have := mul_le_mul_of_nonneg_right h_m1_real_pos hp_pos.le
      simpa using this
    linarith
  have h_side : 2 ≤ Module.finrank ℝ E ∨ 1 < p := Or.inr hp_one_strict
  obtain ⟨ũ, _C, hũ_cont, _hC_nn, hũ_ae, _hũ_bound⟩ :=
    iterated_sobolev_embedding_chart_C0
      (I := I) (M := M) g h_m1_pos hp_one h_kp_gt_n h_side hu_meas hu
  have hũ_meas : Measurable ũ := hũ_cont.measurable
  refine ⟨ũ, ?_, ?_⟩
  · refine contMDiff_of_locally_contMDiffOn ?_
    intro x
    have hρ_pos : ∃ α : M, 0 <
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x :=
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M).exists_pos_of_mem
        (Set.mem_univ _)
    obtain ⟨α, hρα_pos⟩ := hρ_pos
    have hx_source : x ∈ (chartAt H α).source := by
      refine CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate
        (I := I) (M := M) α ?_
      exact subset_tsupport _ (by exact ne_of_gt hρα_pos)
    have hρα_cont : Continuous (fun y : M =>
        ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) y) :=
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M α).contMDiff.continuous
    set c : ℝ := ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) x / 2 with hc_def
    have hc_pos : 0 < c := by
      have h_pos_x : 0 <
        ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) x := hρα_pos
      rw [hc_def]; linarith
    have hc_lt : c <
        ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) x := by
      have h_pos_x : 0 <
        ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) x := hρα_pos
      rw [hc_def]; linarith
    have h_set_open : IsOpen {y : M | c <
        ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) y} :=
      hρα_cont.isOpen_preimage _ isOpen_Ioi
    set V : Set M := (chartAt H α).source ∩ {y : M | c <
        ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) y} with hV_def
    have hVopen : IsOpen V := (chartAt H α).open_source.inter h_set_open
    have hxV : x ∈ V := ⟨hx_source, hc_lt⟩
    have hVsource : V ⊆ (chartAt H α).source := fun y hy => hy.1
    have hc_bound : ∀ y ∈ V, c ≤
        ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) y := fun y hy => le_of_lt hy.2
    set y₀ : EuclN := (toEuclidean (E := E)) (extChartAt I α x) with hy₀_def
    have hy₀_in : y₀ ∈ chartTargetEuclid (I := I) (M := M) α := by
      have hx_ext_source : x ∈ (extChartAt I α).source := by
        rw [extChartAt_source (I := I)]; exact hx_source
      refine ⟨extChartAt I α x, (extChartAt I α).map_source hx_ext_source, ?_⟩
      rfl
    obtain ⟨R, hR_pos, hR_subset⟩ :=
      exists_ball_subset_chartTargetEuclid (I := I) (M := M) α hy₀_in
    have h_chart_mem :
        Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) (m + 1) (ENNReal.ofReal p)
          (chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
          (chartTargetEuclid (I := I) (M := M) α) :=
      hu α
    have h_ball_open : IsOpen (Metric.ball y₀ R) := Metric.isOpen_ball
    have h_chart_target_open :
        IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    have h_chart_mem_ball :
        Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) (m + 1) (ENNReal.ofReal p)
          (chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
          (Metric.ball y₀ R) :=
      Sobolev.Euclidean.MemWkp.mono_set
        (d := Module.finrank ℝ E) hp_enn_one h_ball_open
        hR_subset h_chart_mem
    obtain ⟨u_α, hu_α_cdiff, hu_α_ae⟩ :=
      _root_.CalabiYau.Analysis.Sobolev.EuclideanMorrey.morrey_iteratedFDeriv_representative
        (d := Module.finrank ℝ E) (p := p) (x₀ := y₀) (R := R) hp hR_pos m h_chart_mem_ball
    have hũ_ae_u :
        ũ =ᵐ[CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M)] u :=
      hũ_ae
    have h_pushed_ae :
        chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α ũ
          =ᵐ[(volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)]
          chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u :=
      chartPushed_aeEq_of_ae_eq_riemannianMeasure (I := I) (M := M)
        g α hũ_meas hu_meas hũ_ae_u
    have h_ball_quarter_open : IsOpen (Metric.ball y₀ (R / 4)) := Metric.isOpen_ball
    have h_ball_quarter_subset_ball : Metric.ball y₀ (R / 4) ⊆ Metric.ball y₀ R := by
      intro z hz
      rw [Metric.mem_ball] at hz ⊢
      have hR_quarter_lt : R / 4 ≤ R := by linarith
      exact lt_of_lt_of_le hz hR_quarter_lt
    have h_ball_quarter_subset_target :
        Metric.ball y₀ (R / 4) ⊆ chartTargetEuclid (I := I) (M := M) α :=
      h_ball_quarter_subset_ball.trans hR_subset
    have h_pushed_ae_quarter :
        chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α ũ
          =ᵐ[(volume : Measure EuclN).restrict (Metric.ball y₀ (R / 4))]
          chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u := by
      have hMeas_target : MeasurableSet
          (chartTargetEuclid (I := I) (M := M) α) :=
        h_chart_target_open.measurableSet
      have hMeas_ball : MeasurableSet (Metric.ball y₀ (R / 4)) :=
        h_ball_quarter_open.measurableSet
      rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' hMeas_ball]
      rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' hMeas_target] at h_pushed_ae
      filter_upwards [h_pushed_ae] with z hz hz_in
      exact hz (h_ball_quarter_subset_target hz_in)
    have h_ũ_pushed_ae_u_α :
        chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α ũ
          =ᵐ[(volume : Measure EuclN).restrict (Metric.ball y₀ (R / 4))]
          u_α := h_pushed_ae_quarter.trans hu_α_ae
    have h_ũ_pushed_contOn :
        ContinuousOn (chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α ũ)
          (Metric.ball y₀ (R / 4)) := by
      have h_full : ContinuousOn (chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α ũ)
          (chartTargetEuclid (I := I) (M := M) α) :=
        continuousOn_chartPushed_of_continuous (I := I) (M := M) α hũ_cont
      exact h_full.mono h_ball_quarter_subset_target
    have h_u_α_contOn : ContinuousOn u_α (Metric.ball y₀ (R / 4)) :=
      hu_α_cdiff.continuous.continuousOn
    have h_pushed_eq_u_α_on_ball :
        Set.EqOn (chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α ũ)
          u_α (Metric.ball y₀ (R / 4)) :=
      MeasureTheory.Measure.eqOn_open_of_ae_eq h_ũ_pushed_ae_u_α
        h_ball_quarter_open h_ũ_pushed_contOn h_u_α_contOn
    set Q : Set M :=
      (chartAt H α).source ∩ extChartAt I α ⁻¹'
        ((toEuclidean (E := E)).symm '' Metric.ball y₀ (R / 4))
      with hQ_def
    have hQ_open : IsOpen Q := by
      refine isOpen_extChartAt_preimage (I := I) α ?_
      have : IsOpen ((toEuclidean (E := E)).symm '' Metric.ball y₀ (R / 4)) :=
        (toEuclidean (E := E)).symm.toHomeomorph.isOpenMap _ h_ball_quarter_open
      exact this
    set W : Set M := V ∩ Q with hW_def
    have hW_open : IsOpen W := hVopen.inter hQ_open
    have hxQ : x ∈ Q := by
      refine ⟨hx_source, ?_⟩
      refine ⟨y₀, ?_, ?_⟩
      · rw [Metric.mem_ball]
        change dist y₀ y₀ < R / 4
        simp; linarith
      · exact (toEuclidean (E := E)).symm_apply_apply (extChartAt I α x)
    have hxW : x ∈ W := ⟨hxV, hxQ⟩
    refine ⟨W, hW_open, hxW, ?_⟩
    have h_ext_smooth : ContMDiffOn I 𝓘(ℝ, E) m (extChartAt I α) W := by
      have h_ext_chart_smooth : ContMDiffOn I 𝓘(ℝ, E) (∞ : WithTop ℕ∞)
          (extChartAt I α) (chartAt H α).source :=
        contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)
      have h_finite : ContMDiffOn I 𝓘(ℝ, E) m (extChartAt I α) (chartAt H α).source := by
        refine h_ext_chart_smooth.of_le ?_
        change ((m : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top
      exact h_finite.mono (fun z hz => hVsource hz.1)
    have h_toE_smooth : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclN) m
        ((toEuclidean : E ≃L[ℝ] EuclN) : E → EuclN) :=
      ContinuousLinearMap.contMDiff
        (toEuclidean : E ≃L[ℝ] EuclN).toContinuousLinearMap
    have h_toE_ext_smooth : ContMDiffOn I 𝓘(ℝ, EuclN) m
        (fun y : M => (toEuclidean (E := E)) (extChartAt I α y)) W := by
      intro y hy
      exact h_toE_smooth.contMDiffAt.comp_contMDiffWithinAt y (h_ext_smooth y hy)
    have hu_α_contMDiff : ContMDiff 𝓘(ℝ, EuclN) 𝓘(ℝ, ℝ) m u_α :=
      hu_α_cdiff.contMDiff
    have h_uα_comp_smooth : ContMDiffOn I 𝓘(ℝ, ℝ) m
        (fun y : M => u_α ((toEuclidean (E := E)) (extChartAt I α y))) W := by
      intro y hy
      exact hu_α_contMDiff.contMDiffAt.comp_contMDiffWithinAt y
        (h_toE_ext_smooth y hy)
    have h_rho_smooth : ContMDiff I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
        ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M α).contMDiff
    have h_rho_smooth_m : ContMDiff I 𝓘(ℝ, ℝ) m
        ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
      refine h_rho_smooth.of_le ?_
      change ((m : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top
    have h_rho_pos_on_W : ∀ y ∈ W, 0 <
        ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) y := by
      intro y hy
      have hyV : y ∈ V := hy.1
      exact lt_of_lt_of_le hc_pos (hc_bound y hyV)
    have h_eq_on_W : Set.EqOn ũ
        (fun y : M =>
          u_α ((toEuclidean (E := E)) (extChartAt I α y)) /
            ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) : M → ℝ) y) W := by
      intro y hy
      have hy_source : y ∈ (chartAt H α).source := hVsource hy.1
      have h_push_eq :
          chartPushed (I := I) (M := M)
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α ũ
              ((toEuclidean (E := E)) (extChartAt I α y)) =
            ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) : M → ℝ) y * ũ y :=
        chartPushed_apply_toE_extChartAt (I := I) (M := M) α ũ hy_source
      have hyQ : y ∈ Q := hy.2
      have hyQ_in_ball : (toEuclidean (E := E)) (extChartAt I α y) ∈
          Metric.ball y₀ (R / 4) := by
        rcases hyQ.2 with ⟨z', hz'_in, hz'_eq⟩
        have h_toE_eq :
            (toEuclidean (E := E)) (extChartAt I α y) = z' := by
          rw [← hz'_eq]
          exact (toEuclidean (E := E)).apply_symm_apply z'
        rw [h_toE_eq]
        exact hz'_in
      have h_push_eq_uα :
          chartPushed (I := I) (M := M)
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α ũ
              ((toEuclidean (E := E)) (extChartAt I α y)) =
            u_α ((toEuclidean (E := E)) (extChartAt I α y)) :=
        h_pushed_eq_u_α_on_ball hyQ_in_ball
      rw [h_push_eq] at h_push_eq_uα
      have hρ_pos : 0 <
          ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) y :=
        h_rho_pos_on_W y hy
      have hρ_ne : ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) y ≠ 0 := ne_of_gt hρ_pos
      rw [eq_div_iff hρ_ne, mul_comm]
      exact h_push_eq_uα
    have h_rho_smooth_on : ContMDiffOn I 𝓘(ℝ, ℝ) m
        ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) W := h_rho_smooth_m.contMDiffOn
    have h_quot_smooth : ContMDiffOn I 𝓘(ℝ, ℝ) m
        (fun y : M =>
          u_α ((toEuclidean (E := E)) (extChartAt I α y)) /
            ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) : M → ℝ) y) W := by
      have h_div : ContMDiffOn I 𝓘(ℝ, ℝ) m
          ((fun y : M => u_α ((toEuclidean (E := E)) (extChartAt I α y))) /
            (fun y : M =>
              ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
                : C^∞⟮I, M; ℝ⟯) : M → ℝ) y)) W :=
        h_uα_comp_smooth.div₀ h_rho_smooth_on
          (fun y hy => ne_of_gt (h_rho_pos_on_W y hy))
      exact h_div
    refine h_quot_smooth.congr ?_
    intro y hy
    exact (h_eq_on_W hy)
  · rw [CalabiYau.RiemannianVolume.riemannianVolumeMeasure_def]
    exact hũ_ae

end SupercriticalChartEmbedding

theorem exists_contMDiff_representative_of_all_even_chart_sobolev_orders
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    (m : ℕ)
    {u : M → ℝ} (hu_meas : Measurable u)
    (h_all : ∀ k : ℕ, MemWkpChart (I := I) (M := M) (2 * k) 2 u) :
    ∃ u_smooth : M → ℝ,
      ContMDiff I 𝓘(ℝ, ℝ) m u_smooth ∧
      u_smooth =ᵐ[CalabiYau.RiemannianVolume.riemannianVolumeMeasure
        (I := I) (M := M) g] u := by
  refine memWkpChart_forall_implies_contMDiff_m_representative
    (I := I) (M := M) g m hu_meas
    (hasSupercriticalChartSobolevRegularity_of_all_even_orders (I := I) (M := M) g m h_all) ?_
  intro p hp_dim v hv_meas hv
  exact SupercriticalChartEmbedding.exists_contMDiff_representative_of_supercritical_chart_sobolev
    (I := I) (M := M) g m hp_dim hv_meas hv

theorem sobolev_smooth_representative_of_memWkpChart_forall
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {u : M → ℝ} (hu_meas : Measurable u)
    (h_all : ∀ k : ℕ, MemWkpChart (I := I) (M := M) (2 * k) 2 u) :
    ∃ u_smooth : M → ℝ,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ u_smooth ∧
      u_smooth =ᵐ[CalabiYau.RiemannianVolume.riemannianVolumeMeasure
        (I := I) (M := M) g] u := by
  classical
  have h_choice : ∀ m : ℕ, ∃ u_m : M → ℝ,
      ContMDiff I 𝓘(ℝ, ℝ) m u_m ∧
      u_m =ᵐ[CalabiYau.RiemannianVolume.riemannianVolumeMeasure
        (I := I) (M := M) g] u := fun m =>
    exists_contMDiff_representative_of_all_even_chart_sobolev_orders
      (I := I) (M := M) g m hu_meas h_all
  choose u_fam hu_fam_smooth hu_fam_ae using h_choice
  set u_smooth : M → ℝ := u_fam 0 with hu_smooth_def
  have h_pos : (CalabiYau.RiemannianVolume.riemannianVolumeMeasure
      (I := I) (M := M) g).IsOpenPosMeasure :=
    CalabiYau.RiemannianVolume.riemannianVolumeMeasure_isOpenPosMeasure
      (I := I) (M := M) g
  have h_eq : ∀ m : ℕ, u_fam m = u_smooth := by
    intro m
    have h_fam_cont : Continuous (u_fam m) := (hu_fam_smooth m).continuous
    have h_smooth_cont : Continuous u_smooth := (hu_fam_smooth 0).continuous
    have h_ae : u_fam m =ᵐ[CalabiYau.RiemannianVolume.riemannianVolumeMeasure
        (I := I) (M := M) g] u_smooth :=
      (hu_fam_ae m).trans (hu_fam_ae 0).symm
    exact (Continuous.ae_eq_iff_eq _ h_fam_cont h_smooth_cont).mp h_ae
  refine ⟨u_smooth, ?_, ?_⟩
  · refine contMDiff_infty.mpr ?_
    intro m
    have := hu_fam_smooth m
    rw [h_eq m] at this
    exact this
  · exact hu_fam_ae 0

end Chart
end Sobolev
