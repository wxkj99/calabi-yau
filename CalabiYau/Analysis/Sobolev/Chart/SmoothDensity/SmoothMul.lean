-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Chart/SmoothDensity/SmoothMul.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Chart.Defs
public import CalabiYau.Analysis.Sobolev.Euclidean.Multiplication.Multiply
public import CalabiYau.Analysis.Sobolev.Approximation.Density.Smooth
public import CalabiYau.Analysis.Sobolev.Tools.StrictStrongSupport
public import CalabiYau.Geometry.Riemannian.Volume.Chart.MeasureComparison
public import CalabiYau.Geometry.Riemannian.Volume.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic

@[expose] public section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function Sobolev.Chart
open scoped Manifold ContDiff ENNReal NNReal

namespace CalabiYau
namespace Analysis
namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

lemma exists_chart_cutoff_M
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] (α : M) :
    ∃ b : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ b ∧
      Set.range b ⊆ Set.Icc (0 : ℝ) 1 ∧
      (∀ x ∈ tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU
        I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ), b x = 1) ∧
      tsupport b ⊆ (chartAt H α).source := by
  classical
  obtain ⟨K, hK_compact, hK_chart, h_tsupp_in_int_K⟩ :=
    Sobolev.Chart.exists_compact_neighborhood_of_tsupport_pou
      (I := I) (M := M) α
  obtain ⟨η, hη_smooth, hη_range, _hη_support, hη_one_on_tsupp, hη_tsupport_in_K⟩ :=
    Sobolev.Chart.exists_manifold_cutoff_one_on_tsupport_pou
      (I := I) (M := M) α hK_compact h_tsupp_in_int_K
  refine ⟨η, hη_smooth, hη_range, hη_one_on_tsupp, ?_⟩
  exact hη_tsupport_in_K.trans hK_chart

def smoothExtensionScalar (α : M) (f : M → ℝ) : EuclN → ℝ := by
  classical
  exact fun y =>
    if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    else 0

omit [IsManifold I ∞ M] in
private lemma smoothExtensionScalar_apply_of_mem_target
    (α : M) (f : M → ℝ) {y : EuclN}
    (hy : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target) :
    smoothExtensionScalar (I := I) (M := M) α f y =
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  classical
  change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    else 0) = f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
  rw [if_pos hy]

omit [IsManifold I ∞ M] in
private lemma smoothExtensionScalar_apply_of_notMem_target
    (α : M) (f : M → ℝ) {y : EuclN}
    (hy : (toEuclidean (E := E)).symm y ∉ (extChartAt I α).target) :
    smoothExtensionScalar (I := I) (M := M) α f y = 0 := by
  classical
  change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    else 0) = 0
  rw [if_neg hy]

omit [IsManifold I ∞ M] in
private lemma smoothExtensionScalar_apply_of_mem_chartTargetEuclid
    (α : M) (f : M → ℝ) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    smoothExtensionScalar (I := I) (M := M) α f y =
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  apply smoothExtensionScalar_apply_of_mem_target
  rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
  exact hy

omit [IsManifold I ∞ M] in
private lemma smoothExtensionScalar_apply_of_notMem_chartTargetEuclid
    (α : M) (f : M → ℝ) {y : EuclN}
    (hy : y ∉ chartTargetEuclid (I := I) (M := M) α) :
    smoothExtensionScalar (I := I) (M := M) α f y = 0 := by
  apply smoothExtensionScalar_apply_of_notMem_target
  rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
  exact hy

private lemma contDiffOn_smoothExtensionScalar_formula
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContDiffOn ℝ ∞
        (fun y : EuclN =>
          f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hscalar : ContDiffOn ℝ ∞
      (fun y : E => f ((extChartAt I α).symm y))
      (extChartAt I α).target :=
    CalabiYau.DivergenceTheorem.scalarOnE_contDiffOn
      (I := I) α hf
  have htoEuc_symm_smooth : ContDiff ℝ ∞ ((toEuclidean (E := E)).symm) :=
    ContinuousLinearEquiv.contDiff _
  have hmaps : Set.MapsTo ((toEuclidean (E := E)).symm)
      (chartTargetEuclid (I := I) (M := M) α) (extChartAt I α).target := by
    intro y hy
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  exact hscalar.comp htoEuc_symm_smooth.contDiffOn hmaps

private lemma contDiffAt_smoothExtensionScalar_of_mem_target
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    [I.Boundaryless] {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    ContDiffAt ℝ ∞ (smoothExtensionScalar (I := I) (M := M) α f) y := by
  classical
  have hOpen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hContDiffOn := contDiffOn_smoothExtensionScalar_formula (I := I) (M := M) α hf
  have hContDiffAt_formula : ContDiffAt ℝ ∞
      (fun y : EuclN => f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) y := by
    have hwithin : ContDiffWithinAt ℝ ∞
        (fun y : EuclN => f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (chartTargetEuclid (I := I) (M := M) α) y := hContDiffOn y hy
    exact hwithin.contDiffAt (hOpen.mem_nhds hy)
  apply hContDiffAt_formula.congr_of_eventuallyEq
  filter_upwards [hOpen.mem_nhds hy] with z hz
  rw [smoothExtensionScalar_apply_of_mem_chartTargetEuclid (I := I) (M := M) α f hz]

omit [IsManifold I ∞ M] in
private lemma smoothExtensionScalar_eq_zero_off_image_tsupport
    (α : M) {f : M → ℝ}
    (_hf_support : tsupport f ⊆ (chartAt H α).source) {y : EuclN}
    (hy_off : y ∉ (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport f))) :
    smoothExtensionScalar (I := I) (M := M) α f y = 0 := by
  classical
  by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
  · obtain ⟨z, hz_target, hzy⟩ := hy_target
    have hy_target' : y ∈ chartTargetEuclid (I := I) (M := M) α := ⟨z, hz_target, hzy⟩
    have hy_symm : (toEuclidean (E := E)).symm y = z := by
      rw [← hzy]; exact (toEuclidean (E := E)).symm_apply_apply z
    rw [smoothExtensionScalar_apply_of_mem_chartTargetEuclid (I := I) (M := M) α f hy_target',
      hy_symm]
    by_contra hne
    apply hy_off
    have hsymm_in_support : (extChartAt I α).symm z ∈ tsupport f :=
      subset_tsupport _ (Function.mem_support.mpr hne)
    have hz_eq : (extChartAt I α) ((extChartAt I α).symm z) = z :=
      (extChartAt I α).right_inv hz_target
    refine ⟨z, ⟨(extChartAt I α).symm z, hsymm_in_support, hz_eq⟩, hzy⟩
  · exact smoothExtensionScalar_apply_of_notMem_chartTargetEuclid
      (I := I) (M := M) α f hy_target

omit [IsManifold I ∞ M] in
private lemma image_extChartAt_tsupport_isCompact_local
    [CompactSpace M] {f : M → ℝ} {α : M}
    (hf_support : tsupport f ⊆ (chartAt H α).source) :
    IsCompact ((toEuclidean (E := E)) ''
      ((extChartAt I α) '' (tsupport f))) := by
  have hKE :=
    Sobolev.Chart.image_extChartAt_tsupport_compact_subset_target
      (I := I) (M := M) (u := f) (α := α) hf_support
  exact hKE.1.image (toEuclidean (E := E)).continuous

omit [IsManifold I ∞ M] in
private lemma image_extChartAt_tsupport_subset_chartTargetEuclid_local
    {f : M → ℝ} {α : M}
    (hf_support : tsupport f ⊆ (chartAt H α).source) :
    (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport f)) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
  Sobolev.Chart.image_toEuclidean_extChartAt_tsupport_subset_chartTargetEuclid
    (I := I) (M := M) (u := f) (α := α) hf_support

lemma contDiff_smoothExtensionScalar
    [CompactSpace M] [I.Boundaryless]
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_support : tsupport f ⊆ (chartAt H α).source) :
    ContDiff ℝ ∞ (smoothExtensionScalar (I := I) (M := M) α f) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
  · exact contDiffAt_smoothExtensionScalar_of_mem_target (I := I) (M := M) α hf hy_target
  · have hy_off : y ∉ (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport f)) := by
      intro hy_in
      apply hy_target
      exact image_extChartAt_tsupport_subset_chartTargetEuclid_local
        (I := I) (M := M) (f := f) (α := α) hf_support hy_in
    have hK_compact : IsCompact ((toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport f))) :=
      image_extChartAt_tsupport_isCompact_local
        (I := I) (M := M) (f := f) (α := α) hf_support
    have hK_compl_open : IsOpen _ := hK_compact.isClosed.isOpen_compl
    apply ContDiffAt.congr_of_eventuallyEq
      (f := fun _ : EuclN => (0 : ℝ)) contDiffAt_const
    filter_upwards [hK_compl_open.mem_nhds hy_off] with z hz
    exact smoothExtensionScalar_eq_zero_off_image_tsupport
      (I := I) (M := M) α (f := f) hf_support hz

omit [IsManifold I ∞ M] in
private lemma hasCompactSupport_smoothExtensionScalar
    [CompactSpace M] (α : M) {f : M → ℝ}
    (hf_support : tsupport f ⊆ (chartAt H α).source) :
    HasCompactSupport (smoothExtensionScalar (I := I) (M := M) α f) := by
  classical
  set K : Set EuclN :=
    (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f)) with hK_def
  have hK_compact : IsCompact K :=
    image_extChartAt_tsupport_isCompact_local (I := I) (M := M) (f := f) (α := α) hf_support
  apply HasCompactSupport.of_support_subset_isCompact hK_compact
  intro y hy_support
  by_contra hyK
  apply hy_support
  exact smoothExtensionScalar_eq_zero_off_image_tsupport
    (I := I) (M := M) α (f := f) hf_support hyK

omit [FiniteDimensional ℝ E] in
private lemma iteratedFDeriv_uniformBound_of_compactSupport
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ ∞ ψ) (hψ_compact : HasCompactSupport ψ)
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ k, ∀ y : EuclN, ‖iteratedFDeriv ℝ j ψ y‖ ≤ C := by
  classical
  induction k with
  | zero =>
      have h_iterCont : Continuous (fun y : EuclN => iteratedFDeriv ℝ 0 ψ y) :=
        hψ_smooth.continuous_iteratedFDeriv (m := 0) (by exact_mod_cast le_top)
      have h_iter_support : HasCompactSupport (fun y : EuclN => iteratedFDeriv ℝ 0 ψ y) :=
        hψ_compact.iteratedFDeriv (𝕜 := ℝ) 0
      obtain ⟨C, hC⟩ := h_iterCont.bounded_above_of_compact_support h_iter_support
      refine ⟨max C 0, le_max_right _ _, ?_⟩
      intro j hj y
      interval_cases j
      exact (hC y).trans (le_max_left _ _)
  | succ k ih =>
      obtain ⟨C, hC_nn, hC⟩ := ih
      have h_iterCont : Continuous (fun y : EuclN => iteratedFDeriv ℝ (k+1) ψ y) :=
        hψ_smooth.continuous_iteratedFDeriv (m := k+1) (by exact_mod_cast le_top)
      have h_iter_support : HasCompactSupport (fun y : EuclN => iteratedFDeriv ℝ (k+1) ψ y) :=
        hψ_compact.iteratedFDeriv (𝕜 := ℝ) (k+1)
      obtain ⟨D, hD⟩ := h_iterCont.bounded_above_of_compact_support h_iter_support
      refine ⟨max C (max D 0), ?_, ?_⟩
      · exact le_trans hC_nn (le_max_left _ _)
      intro j hj y
      by_cases hjk : j ≤ k
      · exact (hC j hjk y).trans (le_max_left _ _)
      · have hj_eq : j = k + 1 := by omega
        rw [hj_eq]
        refine (hD y).trans ?_
        exact le_trans (le_max_left _ _) (le_max_right _ _)

lemma smoothExtensionScalar_iteratedFDeriv_bound
    [CompactSpace M] [I.Boundaryless]
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_support : tsupport f ⊆ (chartAt H α).source) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ k, ∀ y : EuclN,
      ‖iteratedFDeriv ℝ j (smoothExtensionScalar (I := I) (M := M) α f) y‖ ≤ C := by
  classical
  have hψ_smooth : ContDiff ℝ ∞ (smoothExtensionScalar (I := I) (M := M) α f) :=
    contDiff_smoothExtensionScalar (I := I) (M := M) α hf hf_support
  have hψ_compact : HasCompactSupport (smoothExtensionScalar (I := I) (M := M) α f) :=
    hasCompactSupport_smoothExtensionScalar (I := I) (M := M) α hf_support
  exact iteratedFDeriv_uniformBound_of_compactSupport hψ_smooth hψ_compact k

end Chart
end Sobolev
end Analysis
end CalabiYau

end
