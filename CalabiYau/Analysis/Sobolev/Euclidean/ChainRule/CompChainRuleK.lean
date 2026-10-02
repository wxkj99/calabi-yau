-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Euclidean/ChainRule/CompChainRuleK.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Euclidean.ChainRule.Defs
public import CalabiYau.Analysis.Sobolev.Euclidean.ChainRule.ChainRuleHigherK
public import CalabiYau.Analysis.Sobolev.Euclidean.Density
public import CalabiYau.Analysis.Sobolev.Euclidean.Completeness.IteratedSobolevBanach
public import CalabiYau.Analysis.Sobolev.Euclidean.Multiplication.Multiply
public import CalabiYau.Analysis.Sobolev.Euclidean.WeakDerivative.Closedness
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Data.Nat.Choose.Bounds

@[expose] public section

-- Private declarations used in public declarations require the compatibility option below.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open MeasureTheory Set Filter Topology Metric Function
open scoped ENNReal NNReal

namespace Sobolev
namespace Euclidean

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
theorem norm_iterClassicalPartial_le_iteratedFDeriv :
    ∀ (j : ℕ) (β : Fin j → Fin d) {f : E → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) f → ∀ x : E,
        ‖iterClassicalPartial (d := d) j β f x‖ ≤ ‖iteratedFDeriv ℝ j f x‖ := by
  intro j
  induction j with
  | zero =>
      intro β f _ x
      simp [iterClassicalPartial_zero, norm_iteratedFDeriv_zero]
  | succ j ih =>
      intro β f hf x
      rw [iterClassicalPartial_succ]
      set g : E → ℝ :=
        fun y => (fderiv ℝ f y) (EuclideanSpace.single (β 0) 1) with hg_def
      have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g := by
        have hf_top : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f := by simpa using hf
        have hfd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ f) := by
          refine hf_top.fderiv_right (m := (⊤ : ℕ∞)) ?_
          simp
        have hfd' : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := by simpa using hfd
        exact hfd'.clm_apply contDiff_const
      have h_ih :=
        ih (fun i : Fin j => β i.succ) (f := g) hg_smooth x
      have h_step :=
        norm_iteratedFDeriv_partial_le (d := d) (η := f) hf (β 0) j x
      exact h_ih.trans h_step

omit [NeZero d] in
private theorem chosenWeakPartial_smooth_ae
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ_open : IsOpen Ω)
    {ψ : E → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_W : DeGiorgi.MemW1p p ψ Ω) (i : Fin d) :
    chosenWeakPartialOrZero p i ψ Ω
      =ᵐ[volume.restrict Ω]
      (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) := by
  have h_chosen : DeGiorgi.HasWeakPartialDeriv i (chosenWeakPartialOrZero p i ψ Ω) ψ Ω :=
    chosenWeakPartialOrZero_isWeakPartial_of_mem hψ_W i
  have h_classical : DeGiorgi.HasWeakPartialDeriv i
      (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) ψ Ω :=
    DeGiorgi.HasWeakPartialDeriv.of_contDiff hΩ_open
      (hψ_smooth.of_le (by norm_cast))
  have h_chosen_local : LocallyIntegrable (chosenWeakPartialOrZero p i ψ Ω)
      (volume.restrict Ω) :=
    (chosenWeakPartialOrZero_memLp_of_mem hψ_W i).locallyIntegrable hp
  have h_classical_local : LocallyIntegrable
      (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) (volume.restrict Ω) := by
    have h_cont : Continuous (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) :=
      (hψ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
    exact h_cont.locallyIntegrable.mono_measure Measure.restrict_le_self
  exact DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ_open h_chosen h_classical
    h_chosen_local h_classical_local

omit [NeZero d] in
private theorem MemWkp_of_smooth_compactSupport_local
    {Ω : Set E} (hΩ_open : IsOpen Ω)
    {ψ : E → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_compact : HasCompactSupport ψ) (hψ_support : tsupport ψ ⊆ Ω)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (k : ℕ) :
    MemWkp (d := d) k p ψ Ω := by
  classical
  induction k generalizing ψ with
  | zero =>
      rw [MemWkp_zero]
      exact (hψ_smooth.continuous.memLp_of_hasCompactSupport
        (μ := (volume : Measure E)) hψ_compact).restrict _
  | succ k ih =>
      rw [MemWkp_succ]
      have hψ_W1p : DeGiorgi.MemW1p p ψ Ω := by
        refine ⟨(hψ_smooth.continuous.memLp_of_hasCompactSupport
          (μ := (volume : Measure E)) hψ_compact).restrict _, ?_⟩
        intro i
        refine ⟨fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1), ?_, ?_⟩
        · have h_cont : Continuous
              (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) :=
            (hψ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
          have h_compact : HasCompactSupport
              (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) :=
            hψ_compact.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
          exact (h_cont.memLp_of_hasCompactSupport
            (μ := (volume : Measure E)) h_compact).restrict _
        · exact DeGiorgi.HasWeakPartialDeriv.of_contDiff hΩ_open
            (hψ_smooth.of_le (by norm_cast))
      refine ⟨hψ_W1p, ?_⟩
      intro i
      have h_ae := chosenWeakPartial_smooth_ae (d := d) hp hΩ_open hψ_smooth hψ_W1p i
      have h_classical_smooth : ContDiff ℝ (⊤ : ℕ∞)
          (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) :=
        (hψ_smooth.fderiv_right (m := (⊤ : ℕ∞))
          (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))).clm_apply
            contDiff_const
      have h_classical_compact : HasCompactSupport
          (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) :=
        hψ_compact.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
      have h_classical_support :
          tsupport (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) ⊆ Ω := by
        refine subset_trans ?_ hψ_support
        exact tsupport_fderiv_apply_subset (𝕜 := ℝ) (EuclideanSpace.single i 1)
      have h_ih_classical := ih h_classical_smooth h_classical_compact h_classical_support
      exact (MemWkp_congr_ae (d := d) hp hΩ_open h_ae).mpr h_ih_classical

omit [NeZero d] in
private theorem iterWeakPartial_smooth_ae_eq_iterClassicalPartial_local
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ_open : IsOpen Ω) :
    ∀ (j : ℕ) (β : Fin j → Fin d) {ψ : E → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      iterWeakPartial (d := d) p j β ψ Ω
        =ᵐ[volume.restrict Ω] iterClassicalPartial (d := d) j β ψ := by
  intro j
  induction j with
  | zero =>
      intro β ψ _ _ _
      simp [iterWeakPartial_zero, iterClassicalPartial_zero]
  | succ j ih =>
      intro β ψ hψ_smooth hψ_compact hψ_support
      rw [iterWeakPartial_succ, iterClassicalPartial_succ]
      have hψ_W1p : DeGiorgi.MemW1p p ψ Ω := by
        have hψ_Wk : MemWkp (d := d) 1 p ψ Ω :=
          MemWkp_of_smooth_compactSupport_local (d := d) hΩ_open hψ_smooth hψ_compact
            hψ_support hp 1
        rwa [MemWkp.one_iff_memW1p] at hψ_Wk
      have h_ae := chosenWeakPartial_smooth_ae (d := d) hp hΩ_open hψ_smooth hψ_W1p (β 0)
      have h_classical_smooth : ContDiff ℝ (⊤ : ℕ∞)
          (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single (β 0) 1)) :=
        (hψ_smooth.fderiv_right (m := (⊤ : ℕ∞))
          (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))).clm_apply
            contDiff_const
      have h_classical_compact : HasCompactSupport
          (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single (β 0) 1)) :=
        hψ_compact.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single (β 0) 1)
      have h_classical_support :
          tsupport (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single (β 0) 1)) ⊆ Ω :=
        (tsupport_fderiv_apply_subset (𝕜 := ℝ)
          (EuclideanSpace.single (β 0) 1)).trans hψ_support
      have h_ih := ih (fun i : Fin j => β i.succ)
        h_classical_smooth h_classical_compact h_classical_support
      have h_iter_congr := iterWeakPartial_ae_congr (d := d) hp hΩ_open j
        (fun i : Fin j => β i.succ) h_ae
      exact h_iter_congr.trans h_ih

omit [NeZero d] in
private lemma exists_cutoff_for_comp
    {Ωsource Ωtarget : Set E}
    (Φ : SmoothDiffeoBounded d Ωsource Ωtarget) (hΩ_open : IsOpen Ωsource)
    {ψ : E → ℝ} (hψ_compact : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ Ωtarget) :
    ∃ (η : E → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) η ∧
      HasCompactSupport η ∧
      tsupport η ⊆ Ωsource ∧
      (∀ x ∈ Ωsource, η x * ψ (Φ.toFun x) = ψ (Φ.toFun x)) := by
  classical
  set Ktarget : Set E := tsupport ψ with hKtarget_def
  have hKtarget_compact : IsCompact Ktarget := hψ_compact
  have hKtargetΩtarget : Ktarget ⊆ Ωtarget := hψ_support
  set Ksource : Set E := Φ.invFun '' Ktarget with hKsource_def
  have hKsource_compact : IsCompact Ksource :=
    hKtarget_compact.image Φ.continuous_invFun
  have hKsourceΩsource : Ksource ⊆ Ωsource := by
    intro x hx
    rcases hx with ⟨y, hy_in, hxy⟩
    rw [← hxy]
    exact Φ.mapsTo_invFun (hKtargetΩtarget hy_in)
  obtain ⟨δ, η, hδ_pos, _hδ_subset, hη_smooth, hη_compact, _hη_range, hη_one, hη_support⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := d) hKsource_compact hΩ_open
      hKsourceΩsource
  refine ⟨η, hη_smooth, hη_compact, hη_support, ?_⟩
  intro x hx
  by_cases hxK : x ∈ Ksource
  · have hx_cthick : x ∈ Metric.cthickening δ Ksource :=
      Metric.self_subset_cthickening _ hxK
    have hη_x : η x = 1 := hη_one x hx_cthick
    rw [hη_x, one_mul]
  · have h_φx_not_Ktarget : Φ.toFun x ∉ Ktarget := by
      intro h_in
      apply hxK
      refine ⟨Φ.toFun x, h_in, ?_⟩
      exact Φ.left_inv hx
    have hψ_zero : ψ (Φ.toFun x) = 0 :=
      image_eq_zero_of_notMem_tsupport h_φx_not_Ktarget
    rw [hψ_zero, mul_zero]

omit [NeZero d] in
private theorem comp_smooth_compactSupport_memWkp
    {Ωsource Ωtarget : Set E}
    (Φ : SmoothDiffeoBounded d Ωsource Ωtarget) (hΩ_open : IsOpen Ωsource)
    {ψ : E → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_compact : HasCompactSupport ψ) (hψ_support : tsupport ψ ⊆ Ωtarget)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (k : ℕ) :
    MemWkp (d := d) k p (fun x => ψ (Φ.toFun x)) Ωsource := by
  classical
  obtain ⟨η, hη_smooth, hη_compact, hη_support, h_eq_on_Ω⟩ :=
    exists_cutoff_for_comp (d := d) Φ hΩ_open hψ_compact hψ_support
  let g : E → ℝ := fun x => η x * ψ (Φ.toFun x)
  have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g :=
    hη_smooth.mul (Φ.comp_toFun_contDiff hψ_smooth)
  have hg_compact : HasCompactSupport g :=
    HasCompactSupport.mul_right hη_compact
  have hg_support : tsupport g ⊆ Ωsource :=
    (tsupport_mul_subset_left (f := η) (g := fun x => ψ (Φ.toFun x))).trans hη_support
  have hg_mem : MemWkp (d := d) k p g Ωsource :=
    MemWkp_of_smooth_compactSupport_local (d := d) hΩ_open hg_smooth hg_compact hg_support hp k
  have h_ae : (fun x => ψ (Φ.toFun x)) =ᵐ[volume.restrict Ωsource] g := by
    refine (ae_restrict_iff' hΩ_open.measurableSet).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro x hx
    change ψ (Φ.toFun x) = η x * ψ (Φ.toFun x)
    rw [h_eq_on_Ω x hx]
  exact (MemWkp_congr_ae (d := d) hp hΩ_open h_ae).mpr hg_mem

omit [NeZero d] in
private lemma norm_iteratedFDeriv_comp_toFun_le_sum
    {Ωsource Ωtarget : Set E}
    (Φ : SmoothDiffeoBounded d Ωsource Ωtarget)
    {ψ : E → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (fun y => ψ (Φ.toFun y)) x‖ ≤
      j.factorial * Φ.derivBoundMaxOne ^ j *
        ∑ n ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖ := by
  classical
  set C : ℝ := ∑ n ∈ Finset.range (j + 1),
      ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖ with hC_def
  have hC_bound : ∀ i, i ≤ j → ‖iteratedFDeriv ℝ i ψ (Φ.toFun x)‖ ≤ C := by
    intro i hi
    have hi_mem : i ∈ Finset.range (j + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
    exact Finset.single_le_sum
      (f := fun n => ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖)
      (fun n _ => norm_nonneg _) hi_mem
  have h := SmoothDiffeoBounded.norm_iteratedFDeriv_comp_toFun_le (d := d) Φ
    (u := ψ) hψ_smooth j x (C := C) hC_bound
  have h_rearrange : (j.factorial : ℝ) * C * Φ.derivBoundMaxOne ^ j =
      j.factorial * Φ.derivBoundMaxOne ^ j * C := by ring
  rw [h_rearrange] at h
  exact h

omit [NeZero d] in
private lemma norm_iteratedFDeriv_cutoff_comp_le
    {Ωsource Ωtarget : Set E}
    (Φ : SmoothDiffeoBounded d Ωsource Ωtarget)
    {η ψ : E → ℝ}
    (hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η)
    (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {Mη : ℝ} (hMη_nonneg : 0 ≤ Mη)
    (k : ℕ)
    (hη_bound : ∀ i, i ≤ k → ∀ y : E, ‖iteratedFDeriv ℝ i η y‖ ≤ Mη)
    (j : ℕ) (hj : j ≤ k) (x : E) :
    ‖iteratedFDeriv ℝ j (fun y => η y * ψ (Φ.toFun y)) x‖ ≤
      ((k + 1 : ℕ) : ℝ) * (2 ^ k : ℝ) * Mη * (k.factorial : ℝ) *
          Φ.derivBoundMaxOne ^ k *
        ∑ n ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖ := by
  classical
  set D : ℝ := Φ.derivBoundMaxOne with hD_def
  have hD_pos : 0 < D := Φ.derivBoundMaxOne_pos
  have hD_ge_1 : 1 ≤ D := Φ.derivBoundMaxOne_ge_one
  have hD_nonneg : 0 ≤ D := hD_pos.le
  set S_x : ℝ := ∑ n ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖ with hSx_def
  have hSx_nonneg : 0 ≤ S_x := Finset.sum_nonneg (fun n _ => norm_nonneg _)
  have h_pt_psi_comp : ∀ m, m ≤ k → ∀ y : E,
      ‖iteratedFDeriv ℝ m (fun z => ψ (Φ.toFun z)) y‖ ≤
        (k.factorial : ℝ) * D ^ k *
          ∑ n ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ n ψ (Φ.toFun y)‖ := by
    intro m hm y
    have h_base := norm_iteratedFDeriv_comp_toFun_le_sum (d := d) Φ hψ_smooth m y
    have h_fact_le : (m.factorial : ℝ) ≤ (k.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le hm
    have h_pow_le : D ^ m ≤ D ^ k :=
      pow_le_pow_right₀ hD_ge_1 hm
    have h_inner_sum_le :
        ∑ n ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ n ψ (Φ.toFun y)‖ ≤
        ∑ n ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ n ψ (Φ.toFun y)‖ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        rw [Finset.mem_range] at hn ⊢; omega
      · intro _ _ _; exact norm_nonneg _
    have h_fact_nn : (0 : ℝ) ≤ (m.factorial : ℝ) := by exact_mod_cast Nat.zero_le _
    have h_powm_nn : (0 : ℝ) ≤ D ^ m := pow_nonneg hD_nonneg m
    have h_sum_inner_nn : (0 : ℝ) ≤
        ∑ n ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ n ψ (Φ.toFun y)‖ :=
      Finset.sum_nonneg (fun n _ => norm_nonneg _)
    have h_sum_outer_nn : (0 : ℝ) ≤
        ∑ n ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ n ψ (Φ.toFun y)‖ :=
      Finset.sum_nonneg (fun n _ => norm_nonneg _)
    have h_step1 :
        (m.factorial : ℝ) * D ^ m *
          ∑ n ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ n ψ (Φ.toFun y)‖ ≤
        (k.factorial : ℝ) * D ^ m *
          ∑ n ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ n ψ (Φ.toFun y)‖ := by
      have h_left_le : (m.factorial : ℝ) * D ^ m ≤ (k.factorial : ℝ) * D ^ m :=
        mul_le_mul_of_nonneg_right h_fact_le h_powm_nn
      exact mul_le_mul_of_nonneg_right h_left_le h_sum_inner_nn
    have h_step2 :
        (k.factorial : ℝ) * D ^ m *
          ∑ n ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ n ψ (Φ.toFun y)‖ ≤
        (k.factorial : ℝ) * D ^ k *
          ∑ n ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ n ψ (Φ.toFun y)‖ := by
      have h_kfact_nn : (0 : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast Nat.zero_le _
      have h_left_le : (k.factorial : ℝ) * D ^ m ≤ (k.factorial : ℝ) * D ^ k :=
        mul_le_mul_of_nonneg_left h_pow_le h_kfact_nn
      exact mul_le_mul_of_nonneg_right h_left_le h_sum_inner_nn
    have h_step3 :
        (k.factorial : ℝ) * D ^ k *
          ∑ n ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ n ψ (Φ.toFun y)‖ ≤
        (k.factorial : ℝ) * D ^ k *
          ∑ n ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ n ψ (Φ.toFun y)‖ := by
      have h_kfact_pow_nn : (0 : ℝ) ≤ (k.factorial : ℝ) * D ^ k :=
        mul_nonneg (by exact_mod_cast Nat.zero_le _) (pow_nonneg hD_nonneg k)
      exact mul_le_mul_of_nonneg_left h_inner_sum_le h_kfact_pow_nn
    exact h_base.trans (h_step1.trans (h_step2.trans h_step3))
  have hcomp_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => ψ (Φ.toFun y)) :=
    Φ.comp_toFun_contDiff hψ_smooth
  have hN : (j : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)
  have h_mul := norm_iteratedFDeriv_mul_le (𝕜 := ℝ)
    (f := η) (g := fun y : E => ψ (Φ.toFun y))
    hη_smooth hcomp_smooth (x := x) (n := j) hN
  have h_term_bound : ∀ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i η x‖ *
        ‖iteratedFDeriv ℝ (j - i) (fun y => ψ (Φ.toFun y)) x‖ ≤
      (j.choose i : ℝ) * (Mη * (k.factorial : ℝ) * D ^ k * S_x) := by
    intro i hi
    have hi_le_j : i ≤ j := by rw [Finset.mem_range] at hi; omega
    have hi_le_k : i ≤ k := hi_le_j.trans hj
    have hji_le_k : j - i ≤ k := by omega
    have hη_x_bound : ‖iteratedFDeriv ℝ i η x‖ ≤ Mη := hη_bound i hi_le_k x
    have h_psi_phi_bound :=
      h_pt_psi_comp (j - i) hji_le_k x
    have h_choose_ge : (0 : ℝ) ≤ (j.choose i : ℝ) := by exact_mod_cast Nat.zero_le _
    have h_step_a :
        (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i η x‖ *
          ‖iteratedFDeriv ℝ (j - i) (fun y => ψ (Φ.toFun y)) x‖ ≤
        (j.choose i : ℝ) * Mη *
          ‖iteratedFDeriv ℝ (j - i) (fun y => ψ (Φ.toFun y)) x‖ := by
      have h_left : (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i η x‖ ≤
          (j.choose i : ℝ) * Mη :=
        mul_le_mul_of_nonneg_left hη_x_bound h_choose_ge
      exact mul_le_mul_of_nonneg_right h_left (norm_nonneg _)
    have h_step_b :
        (j.choose i : ℝ) * Mη *
          ‖iteratedFDeriv ℝ (j - i) (fun y => ψ (Φ.toFun y)) x‖ ≤
        (j.choose i : ℝ) * Mη *
          ((k.factorial : ℝ) * D ^ k * S_x) := by
      have h_left_nn : (0 : ℝ) ≤ (j.choose i : ℝ) * Mη :=
        mul_nonneg h_choose_ge hMη_nonneg
      exact mul_le_mul_of_nonneg_left h_psi_phi_bound h_left_nn
    have h_combined :
        (j.choose i : ℝ) * Mη *
          ((k.factorial : ℝ) * D ^ k * S_x) =
        (j.choose i : ℝ) * (Mη * (k.factorial : ℝ) * D ^ k * S_x) := by ring
    exact (h_step_a.trans h_step_b).trans h_combined.le
  have h_sum_le := Finset.sum_le_sum h_term_bound
  have h_factor :
      ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * (Mη * (k.factorial : ℝ) * D ^ k * S_x) =
      (Mη * (k.factorial : ℝ) * D ^ k * S_x) *
        ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) := by
    have h_eq : ∀ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * (Mη * (k.factorial : ℝ) * D ^ k * S_x) =
        (Mη * (k.factorial : ℝ) * D ^ k * S_x) * (j.choose i : ℝ) := fun i _ => by ring
    rw [Finset.sum_congr rfl h_eq, ← Finset.mul_sum]
  rw [h_factor] at h_sum_le
  have h_sum_choose_eq :
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) = (2 ^ j : ℝ) := by
    have h_nat : ∑ i ∈ Finset.range (j + 1), j.choose i = 2 ^ j :=
      Nat.sum_range_choose j
    have h_cast : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) =
        ((∑ i ∈ Finset.range (j + 1), j.choose i : ℕ) : ℝ) := by push_cast; rfl
    rw [h_cast, h_nat]; push_cast; rfl
  have h_sum_choose_le : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) ≤ (2 ^ k : ℝ) := by
    rw [h_sum_choose_eq]
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj
  have h_factor_nn : (0 : ℝ) ≤ Mη * (k.factorial : ℝ) * D ^ k * S_x := by
    have h_kfact_nn : (0 : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast Nat.zero_le _
    have h_pow_nn : (0 : ℝ) ≤ D ^ k := pow_nonneg hD_nonneg k
    refine mul_nonneg (mul_nonneg (mul_nonneg hMη_nonneg h_kfact_nn) h_pow_nn) hSx_nonneg
  have h_factor_choose_le :
      (Mη * (k.factorial : ℝ) * D ^ k * S_x) *
        ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) ≤
      (Mη * (k.factorial : ℝ) * D ^ k * S_x) * (2 ^ k : ℝ) :=
    mul_le_mul_of_nonneg_left h_sum_choose_le h_factor_nn
  have h_align :
      (Mη * (k.factorial : ℝ) * D ^ k * S_x) * (2 ^ k : ℝ) ≤
      ((k + 1 : ℕ) : ℝ) * (2 ^ k : ℝ) * Mη * (k.factorial : ℝ) * D ^ k * S_x := by
    have h_one_le : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
      have h := Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero k)
      exact_mod_cast h
    have h_eq : (Mη * (k.factorial : ℝ) * D ^ k * S_x) * (2 ^ k : ℝ) =
        1 * (2 ^ k : ℝ) * Mη * (k.factorial : ℝ) * D ^ k * S_x := by ring
    have h_eq2 : ((k + 1 : ℕ) : ℝ) * (2 ^ k : ℝ) * Mη * (k.factorial : ℝ) * D ^ k * S_x =
        ((k + 1 : ℕ) : ℝ) * (2 ^ k : ℝ) * Mη * (k.factorial : ℝ) * D ^ k * S_x := rfl
    rw [h_eq]
    have h_two_pow_nn : (0 : ℝ) ≤ (2 ^ k : ℝ) := by positivity
    have h_left_pos : (0 : ℝ) ≤
        (2 ^ k : ℝ) * Mη * (k.factorial : ℝ) * D ^ k * S_x := by
      have h_kfact_nn : (0 : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast Nat.zero_le _
      have h_pow_nn : (0 : ℝ) ≤ D ^ k := pow_nonneg hD_nonneg k
      refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h_two_pow_nn hMη_nonneg)
        h_kfact_nn) h_pow_nn) hSx_nonneg
    nlinarith
  exact h_mul.trans (h_sum_le.trans (h_factor_choose_le.trans h_align))

omit [NeZero d] in
private lemma euclidean_coord_le_norm
    (v : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    |v i| ≤ ‖v‖ := by
  classical
  have h_sq : (v i)^2 ≤ ‖v‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have h_le := Finset.single_le_sum
      (f := fun j : Fin d => (v j)^2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    convert h_le
  have hv_norm_nn : 0 ≤ ‖v‖ := norm_nonneg _
  have h_abs_sq : |v i|^2 = (v i)^2 := sq_abs _
  rw [show |v i| = Real.sqrt ((v i)^2) from (Real.sqrt_sq_eq_abs _).symm]
  rw [show ‖v‖ = Real.sqrt (‖v‖^2) from (Real.sqrt_sq hv_norm_nn).symm]
  exact Real.sqrt_le_sqrt h_sq

omit [NeZero d] in
private lemma continuousMultilinearMap_norm_le_sum_basis
    {n : ℕ}
    (f : ContinuousMultilinearMap ℝ
      (fun _ : Fin n => EuclideanSpace ℝ (Fin d)) ℝ) :
    ‖f‖ ≤ ∑ β : Fin n → Fin d,
      |f (fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ))| := by
  classical
  set M : ℝ := ∑ β : Fin n → Fin d,
      |f (fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ))| with hM_def
  have hM_nonneg : 0 ≤ M :=
    Finset.sum_nonneg (fun β _ => abs_nonneg _)
  refine ContinuousMultilinearMap.opNorm_le_bound hM_nonneg ?_
  intro m
  have h_expand : ∀ i : Fin n, m i =
      ∑ α : Fin d, (m i α) • EuclideanSpace.single α (1 : ℝ) := by
    intro i
    have h := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr (m i)
    rw [show (fun α : Fin d => (m i α) • EuclideanSpace.single α (1 : ℝ)) =
      (fun α : Fin d => (EuclideanSpace.basisFun (Fin d) ℝ).repr (m i) α •
        (EuclideanSpace.basisFun (Fin d) ℝ) α) from ?_, h]
    funext α
    rw [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
  have h_f_expand :
      f m = ∑ β : Fin n → Fin d,
        (∏ i : Fin n, m i (β i)) *
          f (fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ)) := by
    have h_step1 : f m = f (fun i : Fin n =>
        ∑ α : Fin d, (m i α) • EuclideanSpace.single α (1 : ℝ)) := by
      congr; funext i; exact h_expand i
    rw [h_step1]
    have h_mult_sum :
        (f.toMultilinearMap fun i : Fin n =>
          ∑ α : Fin d, (m i α) • EuclideanSpace.single α (1 : ℝ)) =
        ∑ β : Fin n → Fin d,
          f.toMultilinearMap fun i : Fin n =>
            (m i (β i)) • EuclideanSpace.single (β i) (1 : ℝ) := by
      exact f.toMultilinearMap.map_sum
        (fun (i : Fin n) (α : Fin d) =>
          (m i α) • EuclideanSpace.single α (1 : ℝ))
    change f.toMultilinearMap _ = _
    rw [h_mult_sum]
    refine Finset.sum_congr rfl ?_
    intro β _
    rw [f.toMultilinearMap.map_smul_univ
      (c := fun i : Fin n => m i (β i))
      (m := fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ))]
    rw [smul_eq_mul]
    rfl
  rw [Real.norm_eq_abs]
  rw [h_f_expand]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h_inner_bound : ∀ β : Fin n → Fin d,
      |(∏ i : Fin n, m i (β i)) *
          f (fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ))| ≤
        (∏ i : Fin n, ‖m i‖) *
          |f (fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ))| := by
    intro β
    rw [abs_mul]
    have h_prod_le : |∏ i : Fin n, m i (β i)| ≤ ∏ i : Fin n, ‖m i‖ := by
      rw [Finset.abs_prod]
      refine Finset.prod_le_prod ?_ ?_
      · intro i _; exact abs_nonneg _
      · intro i _; exact euclidean_coord_le_norm (d := d) (m i) (β i)
    exact mul_le_mul_of_nonneg_right h_prod_le (abs_nonneg _)
  refine (Finset.sum_le_sum (fun β _ => h_inner_bound β)).trans ?_
  have h_factor :
      ∑ β : Fin n → Fin d,
        (∏ i : Fin n, ‖m i‖) *
          |f (fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ))| =
      (∏ i : Fin n, ‖m i‖) * M := by
    rw [← Finset.mul_sum]
  rw [h_factor]
  exact le_of_eq (mul_comm _ _)

omit [NeZero d] in
private lemma norm_iteratedFDeriv_le_sum_basis
    (n : ℕ) {ψ : E → ℝ} (y : E) :
    ‖iteratedFDeriv ℝ n ψ y‖ ≤
      ∑ β : Fin n → Fin d,
        |iteratedFDeriv ℝ n ψ y
          (fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ))| :=
  continuousMultilinearMap_norm_le_sum_basis (d := d) (iteratedFDeriv ℝ n ψ y)

omit [NeZero d] in
private lemma iteratedFDeriv_clm_apply_basis
    {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → F →L[ℝ] ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (v : F)
    (β : Fin n → Fin d) (y : E) :
    iteratedFDeriv ℝ n g y
      (fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ)) v =
    iteratedFDeriv ℝ n (fun y' => g y' v) y
      (fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ)) := by
  have h := iteratedFDeriv_clm_apply_const_apply (𝕜 := ℝ)
    (n := (⊤ : ℕ∞)) (c := g) (u := v) (i := n) (x := y)
    (m := fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ))
    hg (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  exact h.symm

omit [NeZero d] in
private lemma iteratedFDeriv_basis_eq_iterClassicalPartial_rev :
    ∀ (n : ℕ) (β : Fin n → Fin d) {f : E → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) f → ∀ y : E,
        iteratedFDeriv ℝ n f y
          (fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ)) =
        iterClassicalPartial (d := d) n (fun i : Fin n => β i.rev) f y := by
  intro n
  induction n with
  | zero =>
      intro β f _ y
      simp [iteratedFDeriv_zero_apply, iterClassicalPartial_zero]
  | succ n ih =>
      intro β f hf y
      rw [show (fun i : Fin (n + 1) => EuclideanSpace.single (β i) (1 : ℝ)) =
        Fin.snoc (fun i : Fin n => EuclideanSpace.single (β i.castSucc) (1 : ℝ))
          (EuclideanSpace.single (β (Fin.last n)) (1 : ℝ)) by
        ext i
        induction i using Fin.lastCases with
        | last => simp
        | cast j => simp]
      rw [iteratedFDeriv_succ_apply_right]
      rw [Fin.init_snoc, Fin.snoc_last]
      have hfd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := by
        have hf_top : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f := by simpa using hf
        have h := hf_top.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
        simpa using h
      rw [iteratedFDeriv_clm_apply_basis (d := d)
        (g := fderiv ℝ f) hfd (EuclideanSpace.single (β (Fin.last n)) (1 : ℝ))
        (β := fun i : Fin n => β i.castSucc) y]
      have h_inner_smooth : ContDiff ℝ (⊤ : ℕ∞)
          (fun y' : E => (fderiv ℝ f y') (EuclideanSpace.single (β (Fin.last n)) (1 : ℝ))) :=
        hfd.clm_apply contDiff_const
      rw [ih (fun i : Fin n => β i.castSucc) h_inner_smooth y]
      rw [iterClassicalPartial_succ]
      have h_index_eq :
          (fun i : Fin n => β i.rev.castSucc) =
          (fun i : Fin n => β i.succ.rev) := by
        funext i
        rw [Fin.rev_succ]
      have h_first_eq : β (Fin.last n) = β (Fin.rev 0) := by
        rw [Fin.rev_zero]
      rw [h_index_eq, h_first_eq]

omit [NeZero d] in
private lemma norm_iteratedFDeriv_le_sum_iterClassicalPartial
    (n : ℕ) {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (y : E) :
    ‖iteratedFDeriv ℝ n f y‖ ≤
      ∑ β : Fin n → Fin d, |iterClassicalPartial (d := d) n β f y| := by
  classical
  have h1 := norm_iteratedFDeriv_le_sum_basis (d := d) n (ψ := f) y
  have h2 : ∀ β : Fin n → Fin d,
      |iteratedFDeriv ℝ n f y
        (fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ))| =
      |iterClassicalPartial (d := d) n (fun i : Fin n => β i.rev) f y| := by
    intro β
    rw [iteratedFDeriv_basis_eq_iterClassicalPartial_rev (d := d) n β hf y]
  have h3 : ∑ β : Fin n → Fin d,
      |iteratedFDeriv ℝ n f y
        (fun i : Fin n => EuclideanSpace.single (β i) (1 : ℝ))| =
      ∑ β : Fin n → Fin d,
        |iterClassicalPartial (d := d) n (fun i : Fin n => β i.rev) f y| :=
    Finset.sum_congr rfl (fun β _ => h2 β)
  rw [h3] at h1
  have h_equiv :
      ∑ β : Fin n → Fin d,
        |iterClassicalPartial (d := d) n (fun i : Fin n => β i.rev) f y| =
      ∑ β : Fin n → Fin d, |iterClassicalPartial (d := d) n β f y| := by
    have h_invol : ∀ β : Fin n → Fin d,
        (fun i : Fin n => (fun j : Fin n => β j.rev) i.rev) = β := by
      intro β
      funext i
      simp [Fin.rev_rev]
    refine Finset.sum_bij (fun β _ => fun i : Fin n => β i.rev) ?_ ?_ ?_ ?_
    · intro β _; exact Finset.mem_univ _
    · intro β1 _ β2 _ h
      have h_apply : ∀ i : Fin n,
          (fun j : Fin n => β1 j.rev) i = (fun j : Fin n => β2 j.rev) i :=
        fun i => congrFun h i
      funext i
      have := h_apply i.rev
      simpa [Fin.rev_rev] using this
    · intro β _
      refine ⟨fun i : Fin n => β i.rev, Finset.mem_univ _, ?_⟩
      funext i
      simp [Fin.rev_rev]
    · intro β _; rfl
  rw [h_equiv] at h1
  exact h1

omit [NeZero d] in
private lemma eLpNorm_iteratedFDeriv_le_sum_iterClassicalPartial
    (n : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f : E → ℝ} (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f)
    (Ω : Set E) :
    eLpNorm (fun y => ‖iteratedFDeriv ℝ n f y‖) p (volume.restrict Ω) ≤
      ∑ β : Fin n → Fin d,
        eLpNorm (iterClassicalPartial (d := d) n β f) p (volume.restrict Ω) := by
  classical
  have h_pt : ∀ y, ‖iteratedFDeriv ℝ n f y‖ ≤
      ∑ β : Fin n → Fin d, |iterClassicalPartial (d := d) n β f y| :=
    fun y => norm_iteratedFDeriv_le_sum_iterClassicalPartial (d := d) n hf_smooth y
  have h_eLp_le :
      eLpNorm (fun y => ‖iteratedFDeriv ℝ n f y‖) p (volume.restrict Ω) ≤
      eLpNorm (fun y => ∑ β : Fin n → Fin d,
        |iterClassicalPartial (d := d) n β f y|) p (volume.restrict Ω) := by
    refine eLpNorm_mono_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro y
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg]
    · exact h_pt y
    · exact Finset.sum_nonneg (fun β _ => abs_nonneg _)
  refine h_eLp_le.trans ?_
  have h_strong_meas : ∀ β : Fin n → Fin d,
      AEStronglyMeasurable
        (fun y => |iterClassicalPartial (d := d) n β f y|) (volume.restrict Ω) := by
    intro β
    have h_smooth : ContDiff ℝ (⊤ : ℕ∞)
        (iterClassicalPartial (d := d) n β f) :=
      contDiff_iterClassicalPartial (d := d) n β hf_smooth
    have h_aem : AEStronglyMeasurable
        (iterClassicalPartial (d := d) n β f) (volume.restrict Ω) :=
      h_smooth.continuous.aestronglyMeasurable
    have h_norm := h_aem.norm
    refine h_norm.congr (Filter.Eventually.of_forall ?_)
    intro y
    exact (Real.norm_eq_abs _).symm
  have h_triangle :
      eLpNorm (fun y => ∑ β : Fin n → Fin d,
        |iterClassicalPartial (d := d) n β f y|) p (volume.restrict Ω) ≤
      ∑ β : Fin n → Fin d,
        eLpNorm (fun y => |iterClassicalPartial (d := d) n β f y|) p (volume.restrict Ω) := by
    have hsum := eLpNorm_sum_le
      (μ := volume.restrict Ω) (p := p)
      (s := (Finset.univ : Finset (Fin n → Fin d)))
      (f := fun β y => |iterClassicalPartial (d := d) n β f y|)
      (fun β _ => h_strong_meas β) hp
    have h_eq : (fun y => ∑ β : Fin n → Fin d,
        |iterClassicalPartial (d := d) n β f y|) =
        ((Finset.univ : Finset (Fin n → Fin d)).sum
          (fun β => fun y => |iterClassicalPartial (d := d) n β f y|)) := by
      funext y; rw [Finset.sum_apply]
    rw [h_eq]
    exact hsum
  refine h_triangle.trans ?_
  refine Finset.sum_le_sum (fun β _ => ?_)
  refine eLpNorm_mono_ae ?_
  refine Filter.Eventually.of_forall ?_
  intro y
  rw [Real.norm_eq_abs, abs_abs]
  exact le_of_eq rfl

omit [NeZero d] in
lemma eLpNorm_iteratedFDeriv_le_wkpNorm
    {Ω : Set E} (hΩ_open : IsOpen Ω)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    (k : ℕ)
    {ψ : E → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_compact : HasCompactSupport ψ) (hψ_support : tsupport ψ ⊆ Ω) :
    ∑ n ∈ Finset.range (k + 1),
      eLpNorm (fun y => ‖iteratedFDeriv ℝ n ψ y‖) p (volume.restrict Ω) ≤
    iteratedWeakSobolevNorm (d := d) k p ψ Ω := by
  classical
  have h_per_n : ∀ n, n ≤ k →
      eLpNorm (fun y => ‖iteratedFDeriv ℝ n ψ y‖) p (volume.restrict Ω) ≤
      ∑ β : Fin n → Fin d,
        eLpNorm (iterClassicalPartial (d := d) n β ψ) p (volume.restrict Ω) := fun n _ =>
    eLpNorm_iteratedFDeriv_le_sum_iterClassicalPartial (d := d) n hp_one
      hψ_smooth Ω
  have h_iter_eq : ∀ n β,
      eLpNorm (iterClassicalPartial (d := d) n β ψ) p (volume.restrict Ω) =
      eLpNorm (iterWeakPartial (d := d) p n β ψ Ω) p (volume.restrict Ω) := fun n β => by
    refine eLpNorm_congr_ae ?_
    exact (iterWeakPartial_smooth_ae_eq_iterClassicalPartial_local
      (d := d) hp_one hΩ_open n β hψ_smooth hψ_compact hψ_support).symm
  unfold iteratedWeakSobolevNorm
  refine Finset.sum_le_sum ?_
  intro n hn
  have hn_le : n ≤ k := by rw [Finset.mem_range] at hn; omega
  refine (h_per_n n hn_le).trans ?_
  refine Finset.sum_le_sum ?_
  intro β _
  rw [h_iter_eq]

end Euclidean
end Sobolev

namespace Sobolev
namespace Euclidean

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private lemma jacobian_lower_pointwise_bound
    {Ω Ω' : Set E}
    (Φ : SmoothDiffeoBounded d Ω Ω') {q : ℝ}
    (f : E → ℝ) :
    ∀ x ∈ Ω,
      ENNReal.ofReal Φ.jacobianLowerBound * ‖f (Φ.toFun x)‖ₑ ^ q ≤
        ENNReal.ofReal |(fderiv ℝ Φ.toFun x).det| * ‖f (Φ.toFun x)‖ₑ ^ q := by
  intro x hx
  have h_le : ENNReal.ofReal Φ.jacobianLowerBound ≤
      ENNReal.ofReal |(fderiv ℝ Φ.toFun x).det| :=
    ENNReal.ofReal_le_ofReal (Φ.jacobian_lower x hx)
  exact mul_le_mul_of_nonneg_right h_le (zero_le)

omit [NeZero d] in
private lemma lintegral_rpow_enorm_comp_le
    {p : ℝ≥0∞}
    {Ω Ω' : Set E} (hΩ : IsOpen Ω)
    (Φ : SmoothDiffeoBounded d Ω Ω')
    (f : E → ℝ) :
    ENNReal.ofReal Φ.jacobianLowerBound *
        ∫⁻ x, ‖f (Φ.toFun x)‖ₑ ^ p.toReal ∂(volume.restrict Ω) ≤
      ∫⁻ y, ‖f y‖ₑ ^ p.toReal ∂(volume.restrict Ω') := by
  classical
  set q := p.toReal with hq_def
  have hjLB_ne_top : ENNReal.ofReal Φ.jacobianLowerBound ≠ ⊤ := ENNReal.ofReal_ne_top
  have hΩ_meas : MeasurableSet Ω := hΩ.measurableSet
  have hint_le :
      ENNReal.ofReal Φ.jacobianLowerBound *
          ∫⁻ x, ‖f (Φ.toFun x)‖ₑ ^ q ∂(volume.restrict Ω) ≤
        ∫⁻ x,
          ENNReal.ofReal |(fderiv ℝ Φ.toFun x).det| * ‖f (Φ.toFun x)‖ₑ ^ q
            ∂(volume.restrict Ω) := by
    rw [← MeasureTheory.lintegral_const_mul' _ _ hjLB_ne_top]
    refine MeasureTheory.lintegral_mono_ae ?_
    rw [MeasureTheory.ae_restrict_iff' hΩ_meas]
    refine Filter.Eventually.of_forall ?_
    intro x hx
    exact jacobian_lower_pointwise_bound (d := d) Φ (q := q) f x hx
  refine hint_le.trans ?_
  have hchg := Φ.lintegral_image_eq hΩ (fun y => ‖f y‖ₑ ^ q)
  rw [← hchg]

omit [NeZero d] in
theorem eLpNorm_comp_toFun_le_const
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    {Ω Ω' : Set E} (hΩ : IsOpen Ω)
    (Φ : SmoothDiffeoBounded d Ω Ω')
    (f : E → ℝ) :
    eLpNorm (fun x => f (Φ.toFun x)) p (volume.restrict Ω) ≤
      ENNReal.ofReal
          ((1 / Φ.jacobianLowerBound) ^ (1 / p.toReal)) *
        eLpNorm f p (volume.restrict Ω') := by
  classical
  have hp_zero : p ≠ 0 := by
    intro hpz; rw [hpz] at hp_one
    exact absurd hp_one (by norm_num)
  set q := p.toReal with hq_def
  have hq_pos : 0 < q := ENNReal.toReal_pos hp_zero hp_top
  have hjLB_pos : 0 < Φ.jacobianLowerBound := Φ.jacobian_lower_bound_pos
  have h_lint :=
    lintegral_rpow_enorm_comp_le (d := d) (p := p) hΩ Φ f
  have h_LHS_pow_eq :
      ∫⁻ x, ‖f (Φ.toFun x)‖ₑ ^ q ∂(volume.restrict Ω) =
        eLpNorm (fun x => f (Φ.toFun x)) p (volume.restrict Ω) ^ q := by
    rw [eLpNorm_eq_eLpNorm' hp_zero hp_top, hq_def]
    exact lintegral_rpow_enorm_eq_rpow_eLpNorm' hq_pos
  have h_RHS_pow_eq :
      ∫⁻ y, ‖f y‖ₑ ^ q ∂(volume.restrict Ω') =
        eLpNorm f p (volume.restrict Ω') ^ q := by
    rw [eLpNorm_eq_eLpNorm' hp_zero hp_top, hq_def]
    exact lintegral_rpow_enorm_eq_rpow_eLpNorm' hq_pos
  rw [h_LHS_pow_eq, h_RHS_pow_eq] at h_lint
  set A : ℝ≥0∞ := eLpNorm (fun x => f (Φ.toFun x)) p (volume.restrict Ω)
    with hA_def
  set B : ℝ≥0∞ := eLpNorm f p (volume.restrict Ω') with hB_def
  set j : ℝ≥0∞ := ENNReal.ofReal Φ.jacobianLowerBound with hj_def
  have hj_pos : 0 < j := by rw [hj_def]; exact ENNReal.ofReal_pos.mpr hjLB_pos
  have hj_ne_zero : j ≠ 0 := hj_pos.ne'
  have hj_ne_top : j ≠ ⊤ := by rw [hj_def]; exact ENNReal.ofReal_ne_top
  have h_Aq_le : A ^ q ≤ j⁻¹ * B ^ q := by
    have h1 : A ^ q = j⁻¹ * (j * A ^ q) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hj_ne_zero hj_ne_top, one_mul]
    rw [h1]
    gcongr
  have h_1q_nonneg : (0 : ℝ) ≤ 1 / q := by positivity
  have h_pow_le : (A ^ q) ^ (1 / q) ≤ (j⁻¹ * B ^ q) ^ (1 / q) :=
    ENNReal.rpow_le_rpow h_Aq_le h_1q_nonneg
  have h_LHS_simp : (A ^ q) ^ (1 / q) = A := by
    rw [← ENNReal.rpow_mul, mul_one_div, div_self hq_pos.ne', ENNReal.rpow_one]
  have h_RHS_simp : (j⁻¹ * B ^ q) ^ (1 / q) = j⁻¹ ^ (1 / q) * B := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ h_1q_nonneg]
    congr 1
    rw [← ENNReal.rpow_mul, mul_one_div, div_self hq_pos.ne', ENNReal.rpow_one]
  rw [h_LHS_simp, h_RHS_simp] at h_pow_le
  have h_inv_real : j⁻¹ = ENNReal.ofReal (1 / Φ.jacobianLowerBound) := by
    change (ENNReal.ofReal Φ.jacobianLowerBound)⁻¹ =
      ENNReal.ofReal (1 / Φ.jacobianLowerBound)
    rw [← ENNReal.ofReal_inv_of_pos hjLB_pos, one_div]
  rw [h_inv_real,
      ENNReal.ofReal_rpow_of_pos
        (by positivity : (0 : ℝ) < 1 / Φ.jacobianLowerBound)] at h_pow_le
  exact h_pow_le

omit [NeZero d] in
private lemma iterClassicalPartial_eqOn_of_eqOn
    {Ω : Set E} (hΩ_open : IsOpen Ω) :
    ∀ (j : ℕ) (β : Fin j → Fin d) {g h : E → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) g → ContDiff ℝ (⊤ : ℕ∞) h →
      Set.EqOn g h Ω →
      Set.EqOn (iterClassicalPartial (d := d) j β g)
        (iterClassicalPartial (d := d) j β h) Ω := by
  intro j
  induction j with
  | zero =>
      intro β g h _ _ hgh x hx
      simpa [iterClassicalPartial_zero] using hgh hx
  | succ j ih =>
      intro β g h hg_smooth hh_smooth hgh x hx
      rw [iterClassicalPartial_succ, iterClassicalPartial_succ]
      have h_partial_eqOn :
          Set.EqOn (fun y => (fderiv ℝ g y) (EuclideanSpace.single (β 0) 1))
            (fun y => (fderiv ℝ h y) (EuclideanSpace.single (β 0) 1)) Ω := by
        intro y hy
        have hy_eq : g =ᶠ[𝓝 y] h := by
          rw [Filter.eventuallyEq_iff_exists_mem]
          exact ⟨Ω, hΩ_open.mem_nhds hy, hgh⟩
        have hfd : fderiv ℝ g y = fderiv ℝ h y := hy_eq.fderiv_eq
        simp [hfd]
      have h_inner_g_smooth : ContDiff ℝ (⊤ : ℕ∞)
          (fun y => (fderiv ℝ g y) (EuclideanSpace.single (β 0) 1)) :=
        (hg_smooth.fderiv_right (m := (⊤ : ℕ∞))
          (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))).clm_apply
            contDiff_const
      have h_inner_h_smooth : ContDiff ℝ (⊤ : ℕ∞)
          (fun y => (fderiv ℝ h y) (EuclideanSpace.single (β 0) 1)) :=
        (hh_smooth.fderiv_right (m := (⊤ : ℕ∞))
          (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))).clm_apply
            contDiff_const
      exact ih (fun i : Fin j => β i.succ)
        h_inner_g_smooth h_inner_h_smooth h_partial_eqOn hx

omit [NeZero d] in
private theorem iterWeakPartial_comp_smooth_ae_eq_iterClassicalPartial
    {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {Ω Ω' : Set E} (hΩ : IsOpen Ω)
    (Φ : SmoothDiffeoBounded d Ω Ω')
    (j : ℕ) (β : Fin j → Fin d)
    {ψ : E → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_compact : HasCompactSupport ψ) (hψ_support : tsupport ψ ⊆ Ω') :
    iterWeakPartial (d := d) p j β (fun x => ψ (Φ.toFun x)) Ω
      =ᵐ[volume.restrict Ω]
      iterClassicalPartial (d := d) j β (fun x => ψ (Φ.toFun x)) := by
  classical
  obtain ⟨η, hη_smooth, hη_compact, hη_support, h_eq_on_Ω⟩ :=
    exists_cutoff_for_comp (d := d) Φ hΩ hψ_compact hψ_support
  let g : E → ℝ := fun x => η x * ψ (Φ.toFun x)
  let comp_smooth : E → ℝ := fun x => ψ (Φ.toFun x)
  have hcomp_smooth_smooth : ContDiff ℝ (⊤ : ℕ∞) comp_smooth :=
    Φ.comp_toFun_contDiff hψ_smooth
  have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g :=
    hη_smooth.mul hcomp_smooth_smooth
  have hg_compact : HasCompactSupport g :=
    HasCompactSupport.mul_right hη_compact
  have hg_support : tsupport g ⊆ Ω :=
    (tsupport_mul_subset_left (f := η) (g := comp_smooth)).trans hη_support
  have h_g_ae :=
    iterWeakPartial_smooth_ae_eq_iterClassicalPartial_local
      (d := d) hp_one hΩ j β hg_smooth hg_compact hg_support
  have h_comp_ae_g : comp_smooth =ᵐ[volume.restrict Ω] g := by
    refine (ae_restrict_iff' hΩ.measurableSet).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro x hx
    change ψ (Φ.toFun x) = η x * ψ (Φ.toFun x)
    rw [h_eq_on_Ω x hx]
  have h_weak_ae :=
    iterWeakPartial_ae_congr (d := d) hp_one hΩ j β h_comp_ae_g
  have h_classical_eqOn :
      Set.EqOn (iterClassicalPartial (d := d) j β g)
        (iterClassicalPartial (d := d) j β comp_smooth) Ω := by
    have h_g_eqOn_comp : Set.EqOn g comp_smooth Ω := by
      intro x hx
      change η x * ψ (Φ.toFun x) = ψ (Φ.toFun x)
      exact h_eq_on_Ω x hx
    exact iterClassicalPartial_eqOn_of_eqOn (d := d) hΩ j β
      hg_smooth hcomp_smooth_smooth h_g_eqOn_comp
  refine h_weak_ae.trans (h_g_ae.trans ?_)
  refine (ae_restrict_iff' hΩ.measurableSet).mpr ?_
  refine Filter.Eventually.of_forall ?_
  intro x hx
  exact h_classical_eqOn hx

omit [NeZero d] in
private lemma norm_iterClassicalPartial_comp_le_uniform
    {Ω Ω' : Set E}
    (Φ : SmoothDiffeoBounded d Ω Ω')
    {ψ : E → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (k : ℕ) :
    ∀ (j : ℕ) (β : Fin j → Fin d), j ≤ k → ∀ x : E,
      ‖iterClassicalPartial (d := d) j β (fun y => ψ (Φ.toFun y)) x‖ ≤
        (k.factorial : ℝ) * Φ.derivBoundMaxOne ^ k *
          ∑ n ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖ := by
  classical
  intro j β hj x
  have hcomp_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => ψ (Φ.toFun y)) :=
    Φ.comp_toFun_contDiff hψ_smooth
  have h1 := norm_iterClassicalPartial_le_iteratedFDeriv (d := d) j β hcomp_smooth x
  have h2 := norm_iteratedFDeriv_comp_toFun_le_sum (d := d) Φ hψ_smooth j x
  have h3 := h1.trans h2
  set D : ℝ := Φ.derivBoundMaxOne with hD_def
  have hD_ge_1 : 1 ≤ D := Φ.derivBoundMaxOne_ge_one
  have hD_nonneg : 0 ≤ D := (lt_of_lt_of_le zero_lt_one hD_ge_1).le
  have h_fact_le : (j.factorial : ℝ) ≤ (k.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le hj
  have h_pow_le : D ^ j ≤ D ^ k := pow_le_pow_right₀ hD_ge_1 hj
  have h_inner_sum_le :
      ∑ n ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖ ≤
      ∑ n ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn; rw [Finset.mem_range] at hn ⊢; omega
    · intro _ _ _; exact norm_nonneg _
  have h_fact_nn : (0 : ℝ) ≤ (j.factorial : ℝ) := by exact_mod_cast Nat.zero_le _
  have h_pow_nn : (0 : ℝ) ≤ D ^ j := pow_nonneg hD_nonneg j
  have h_sum_inner_nn : (0 : ℝ) ≤
      ∑ n ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖ :=
    Finset.sum_nonneg (fun n _ => norm_nonneg _)
  have h_left_le :
      (j.factorial : ℝ) * D ^ j ≤ (k.factorial : ℝ) * D ^ k := by
    have h_step : (j.factorial : ℝ) * D ^ j ≤ (k.factorial : ℝ) * D ^ j :=
      mul_le_mul_of_nonneg_right h_fact_le h_pow_nn
    refine h_step.trans ?_
    have h_kf_nn : (0 : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast Nat.zero_le _
    exact mul_le_mul_of_nonneg_left h_pow_le h_kf_nn
  refine h3.trans ?_
  have h_left_step : (j.factorial : ℝ) * D ^ j *
      ∑ n ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖ ≤
      (k.factorial : ℝ) * D ^ k *
        ∑ n ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖ :=
    mul_le_mul_of_nonneg_right h_left_le h_sum_inner_nn
  refine h_left_step.trans ?_
  have h_outer_nn : (0 : ℝ) ≤ (k.factorial : ℝ) * D ^ k := by
    have h_kf_nn : (0 : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast Nat.zero_le _
    exact mul_nonneg h_kf_nn (pow_nonneg hD_nonneg k)
  exact mul_le_mul_of_nonneg_left h_inner_sum_le h_outer_nn

omit [NeZero d] in
private lemma eLpNorm_iterWeakPartial_comp_le
    {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {Ω Ω' : Set E} (hΩ : IsOpen Ω)
    (Φ : SmoothDiffeoBounded d Ω Ω')
    (k : ℕ)
    {ψ : E → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_compact : HasCompactSupport ψ) (hψ_support : tsupport ψ ⊆ Ω')
    (j : ℕ) (β : Fin j → Fin d) (hj : j ≤ k) :
    eLpNorm
        (iterWeakPartial (d := d) p j β (fun x => ψ (Φ.toFun x)) Ω) p
        (volume.restrict Ω) ≤
      ENNReal.ofReal ((k.factorial : ℝ) * Φ.derivBoundMaxOne ^ k) *
        ∑ n ∈ Finset.range (k + 1),
          eLpNorm
            (fun x => ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖) p
            (volume.restrict Ω) := by
  classical
  have h_eq := iterWeakPartial_comp_smooth_ae_eq_iterClassicalPartial
    (d := d) hp_one hΩ Φ j β hψ_smooth hψ_compact hψ_support
  rw [eLpNorm_congr_ae h_eq]
  have h_pt := norm_iterClassicalPartial_comp_le_uniform
    (d := d) Φ hψ_smooth k j β hj
  set D := Φ.derivBoundMaxOne with hD_def
  set Const : ℝ := (k.factorial : ℝ) * D ^ k with hConst_def
  have hConst_nonneg : 0 ≤ Const := by
    refine mul_nonneg ?_ ?_
    · exact_mod_cast Nat.zero_le _
    · exact pow_nonneg
        (lt_of_lt_of_le zero_lt_one Φ.derivBoundMaxOne_ge_one).le k
  have h_eLp_le :
      eLpNorm (iterClassicalPartial (d := d) j β
          (fun x => ψ (Φ.toFun x))) p (volume.restrict Ω) ≤
        eLpNorm (fun x => Const *
          ∑ n ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖) p
          (volume.restrict Ω) := by
    refine eLpNorm_mono_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    have h_rhs_nonneg : 0 ≤ Const *
        ∑ n ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖ := by
      refine mul_nonneg hConst_nonneg ?_
      exact Finset.sum_nonneg (fun n _ => norm_nonneg _)
    rw [Real.norm_eq_abs (Const * _)]
    rw [abs_of_nonneg h_rhs_nonneg]
    exact (h_pt x).trans_eq rfl
  refine h_eLp_le.trans ?_
  have h_smul_eq : (fun x => Const *
      ∑ n ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖) =
      (Const : ℝ) • (fun x => ∑ n ∈ Finset.range (k + 1),
        ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖) := by
    funext x; simp [Pi.smul_apply, smul_eq_mul]
  rw [h_smul_eq, eLpNorm_const_smul]
  have hConst_norm : (‖Const‖ₑ : ℝ≥0∞) = ENNReal.ofReal Const :=
    Real.enorm_of_nonneg hConst_nonneg
  rw [hConst_norm]
  refine mul_le_mul_of_nonneg_left ?_ (zero_le)
  have h_strong_meas : ∀ n ∈ Finset.range (k + 1),
      AEStronglyMeasurable
        (fun x => ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖) (volume.restrict Ω) := by
    intro n _
    have h_inner :
        Continuous (fun x => ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖) := by
      have hψ_iter : Continuous (fun y => iteratedFDeriv ℝ n ψ y) :=
        hψ_smooth.continuous_iteratedFDeriv (m := n) (by exact_mod_cast le_top)
      exact (hψ_iter.comp Φ.continuous_toFun).norm
    exact h_inner.aestronglyMeasurable
  have h_pointwise_eq : (fun x => ∑ n ∈ Finset.range (k + 1),
        ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖) =
      ∑ n ∈ Finset.range (k + 1),
        (fun x => ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖) := by
    funext x; rw [Finset.sum_apply]
  rw [h_pointwise_eq]
  exact eLpNorm_sum_le h_strong_meas hp_one

omit [NeZero d] in
private lemma eLpNorm_iteratedFDeriv_comp_le
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    {Ω Ω' : Set E} (hΩ : IsOpen Ω)
    (Φ : SmoothDiffeoBounded d Ω Ω')
    {ψ : E → ℝ} (n : ℕ) :
    eLpNorm (fun x => ‖iteratedFDeriv ℝ n ψ (Φ.toFun x)‖) p
        (volume.restrict Ω) ≤
      ENNReal.ofReal
        ((1 / Φ.jacobianLowerBound) ^ (1 / p.toReal)) *
      eLpNorm (fun y => ‖iteratedFDeriv ℝ n ψ y‖) p (volume.restrict Ω') :=
  eLpNorm_comp_toFun_le_const (d := d) hp_one hp_top hΩ Φ
    (fun y => ‖iteratedFDeriv ℝ n ψ y‖)

noncomputable def wkpCompConst
    {Ω Ω' : Set E}
    (Φ : SmoothDiffeoBounded d Ω Ω') (k : ℕ) (p : ℝ≥0∞) : ℝ :=
  ((Finset.range (k + 1)).sum (fun j => (Fintype.card (Fin j → Fin d) : ℝ))) *
    ((k.factorial : ℝ) * Φ.derivBoundMaxOne ^ k) *
    ((1 / Φ.jacobianLowerBound) ^ (1 / p.toReal)) *
    ((k + 1 : ℕ) : ℝ)

private lemma wkpComp_const_card_sum_pos (k : ℕ) :
    0 < (Finset.range (k + 1)).sum
      (fun j => (Fintype.card (Fin j → Fin d) : ℝ)) := by
  have h_zero_in : (0 : ℕ) ∈ Finset.range (k + 1) :=
    Finset.mem_range.mpr (Nat.zero_lt_succ _)
  have h_at_zero : (Fintype.card (Fin 0 → Fin d) : ℝ) = 1 := by
    have h_card : Fintype.card (Fin 0 → Fin d) = 1 := by
      rw [Fintype.card_fun]; simp
    exact_mod_cast h_card
  have h_le := Finset.single_le_sum (s := Finset.range (k + 1))
    (f := fun j => (Fintype.card (Fin j → Fin d) : ℝ))
    (fun j _ => by positivity) h_zero_in
  rw [h_at_zero] at h_le
  linarith

private lemma wkpComp_const_card_sum_ge_one (k : ℕ) :
    1 ≤ (Finset.range (k + 1)).sum
      (fun j => (Fintype.card (Fin j → Fin d) : ℝ)) := by
  have h_zero_in : (0 : ℕ) ∈ Finset.range (k + 1) :=
    Finset.mem_range.mpr (Nat.zero_lt_succ _)
  have h_at_zero : (Fintype.card (Fin 0 → Fin d) : ℝ) = 1 := by
    have h_card : Fintype.card (Fin 0 → Fin d) = 1 := by
      rw [Fintype.card_fun]; simp
    exact_mod_cast h_card
  have h_le := Finset.single_le_sum (s := Finset.range (k + 1))
    (f := fun j => (Fintype.card (Fin j → Fin d) : ℝ))
    (fun j _ => by positivity) h_zero_in
  rw [h_at_zero] at h_le
  exact h_le

private lemma wkpComp_const_pos
    {Ω Ω' : Set E}
    (Φ : SmoothDiffeoBounded d Ω Ω') (k : ℕ) (p : ℝ≥0∞)
    (hp_one : 1 ≤ p) (hp_top : p ≠ ∞) :
    0 < wkpCompConst (d := d) Φ k p := by
  have hp_zero : p ≠ 0 := by
    intro hpz; rw [hpz] at hp_one
    exact absurd hp_one (by norm_num)
  have hq_pos : 0 < p.toReal := ENNReal.toReal_pos hp_zero hp_top
  have hjLB_pos : 0 < Φ.jacobianLowerBound := Φ.jacobian_lower_bound_pos
  have hjLB_inv_pos : 0 < 1 / Φ.jacobianLowerBound := by positivity
  have hKchg_pos : 0 < (1 / Φ.jacobianLowerBound) ^ (1 / p.toReal) :=
    Real.rpow_pos_of_pos hjLB_inv_pos _
  unfold wkpCompConst
  have h_card_pos := wkpComp_const_card_sum_pos (d := d) k
  have h_kfact_D_pos : 0 < (k.factorial : ℝ) * Φ.derivBoundMaxOne ^ k := by
    refine mul_pos ?_ ?_
    · exact_mod_cast Nat.factorial_pos k
    · exact pow_pos Φ.derivBoundMaxOne_pos k
  have h_k1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.zero_lt_succ k
  positivity

end Euclidean
end Sobolev
