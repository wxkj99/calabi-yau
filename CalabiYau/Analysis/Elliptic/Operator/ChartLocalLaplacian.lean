-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Operator/ChartLocalLaplacian.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.MetricExtension
public import CalabiYau.Analysis.Elliptic.Operator.ChartMeasureEquiv
public import CalabiYau.Geometry.Riemannian.Operator.Gradient.Basic
public import CalabiYau.Geometry.Riemannian.Operator.Laplacian.Basic
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Green.Identities
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Topology.Algebra.Support

@[expose] public section
open CalabiYau.Riemannian

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators

namespace CalabiYau
namespace Analysis
namespace Laplacian
namespace ChartLocalLaplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Laplacian.MetricExtension
open Sobolev.NirenbergEuclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in
def chartPullback (α : M) (f : M → ℝ) : EuclN → ℝ :=
  fun y => (chartTargetEuclid (I := I) (M := M) α).indicator
    (fun z => f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))) y

variable [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] in
@[simp] lemma chartPullback_apply_of_mem (α : M) (f : M → ℝ) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPullback (I := I) α f y =
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) :=
  Set.indicator_of_mem hy _

variable [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] in
@[simp] lemma chartPullback_apply_of_notMem (α : M) (f : M → ℝ) {y : EuclN}
    (hy : y ∉ chartTargetEuclid (I := I) (M := M) α) :
    chartPullback (I := I) α f y = 0 :=
  Set.indicator_of_notMem hy _

variable [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in
def euclideanChartImageOfTsupport (α : M) (f : M → ℝ) : Set EuclN :=
  (toEuclidean (E := E)) '' ((extChartAt I α) '' tsupport f)

section

variable [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
lemma euclideanChartImageOfTsupport_isCompact
    (α : M) {f : M → ℝ} (hf_cs : HasCompactSupport f)
    (hf_support : tsupport f ⊆ (chartAt H α).source) :
    IsCompact (euclideanChartImageOfTsupport (I := I) (M := M) α f) := by
  unfold euclideanChartImageOfTsupport
  have hcontOn : ContinuousOn (extChartAt I α) (tsupport f) := by
    refine (continuousOn_extChartAt (I := I) α).mono ?_
    intro x hx
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hf_support hx
  have hImage1 : IsCompact ((extChartAt I α) '' tsupport f) :=
    (hf_cs : IsCompact (tsupport f)).image_of_continuousOn hcontOn
  have hcont_toE : Continuous (toEuclidean (E := E)) :=
    (toEuclidean (E := E)).continuous
  exact hImage1.image hcont_toE

lemma euclideanChartImageOfTsupport_isClosed
    (α : M) {f : M → ℝ} (hf_cs : HasCompactSupport f)
    (hf_support : tsupport f ⊆ (chartAt H α).source) :
    IsClosed (euclideanChartImageOfTsupport (I := I) (M := M) α f) :=
  (euclideanChartImageOfTsupport_isCompact (I := I) (M := M) α hf_cs hf_support).isClosed

lemma euclideanChartImageOfTsupport_subset_chartTargetEuclid
    (α : M) {f : M → ℝ} (hf_support : tsupport f ⊆ (chartAt H α).source) :
    euclideanChartImageOfTsupport (I := I) (M := M) α f ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  intro y hy
  rcases hy with ⟨z, hz_target, hz_eq⟩
  rcases hz_target with ⟨x, hx_support, hx_eq⟩
  refine ⟨z, ?_, hz_eq⟩
  rw [← hx_eq]
  have hxsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hf_support hx_support
  exact (extChartAt I α).map_source hxsrc

lemma chartPullback_support_subset
    (α : M) (f : M → ℝ) :
    Function.support (chartPullback (I := I) α f) ⊆
      euclideanChartImageOfTsupport (I := I) (M := M) α f := by
  intro y hy
  rw [Function.mem_support] at hy
  by_cases hyT : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [chartPullback_apply_of_mem (I := I) α f hyT] at hy
    have hsymm_support : (extChartAt I α).symm ((toEuclidean (E := E)).symm y)
        ∈ tsupport f := subset_tsupport _ hy
    refine ⟨(extChartAt I α) ((extChartAt I α).symm
        ((toEuclidean (E := E)).symm y)), ?_, ?_⟩
    · exact ⟨_, hsymm_support, rfl⟩
    · rcases hyT with ⟨z, hz_target, hz_eq⟩
      have h1 : (extChartAt I α) ((extChartAt I α).symm z) = z :=
        (extChartAt I α).right_inv hz_target
      have hsymm_eq : (toEuclidean (E := E)).symm y = z := by
        rw [← hz_eq]; simp
      rw [hsymm_eq, h1, hz_eq]
  · rw [chartPullback_apply_of_notMem (I := I) α f hyT] at hy
    exact (hy rfl).elim

lemma chartPullback_tsupport_subset
    (α : M) {f : M → ℝ} (hf_cs : HasCompactSupport f)
    (hf_support : tsupport f ⊆ (chartAt H α).source) :
    tsupport (chartPullback (I := I) α f) ⊆
      euclideanChartImageOfTsupport (I := I) (M := M) α f := by
  refine closure_minimal (chartPullback_support_subset (I := I) α f) ?_
  exact euclideanChartImageOfTsupport_isClosed (I := I) (M := M) α hf_cs hf_support

lemma chartPullback_tsupport_subset_chartTargetEuclid
    (α : M) {f : M → ℝ} (hf_cs : HasCompactSupport f)
    (hf_support : tsupport f ⊆ (chartAt H α).source) :
    tsupport (chartPullback (I := I) α f) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
  (chartPullback_tsupport_subset (I := I) α hf_cs hf_support).trans
    (euclideanChartImageOfTsupport_subset_chartTargetEuclid (I := I) (M := M) α hf_support)

private lemma chartPullback_eq_compose_on_chartTargetEuclid
    (α : M) (f : M → ℝ) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPullback (I := I) α f y =
      scalarOnE (I := I) α f ((toEuclidean (E := E)).symm y) := by
  rw [chartPullback_apply_of_mem (I := I) α f hy]
  rfl

end

variable [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in
lemma chartPullback_contDiffOn_chartTargetEuclid
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContDiffOn ℝ ∞ (chartPullback (I := I) α f)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have hsmooth : ContDiffOn ℝ ∞
      (fun y : EuclN =>
        scalarOnE (I := I) α f ((toEuclidean (E := E)).symm y))
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_toE_symm_cd : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclN => (toEuclidean (E := E)).symm y) :=
      (toEuclidean (E := E)).symm.contDiff
    have h_toE_symm : ContDiffOn ℝ ∞
        (fun y : EuclN => (toEuclidean (E := E)).symm y)
        (chartTargetEuclid (I := I) (M := M) α) :=
      h_toE_symm_cd.contDiffOn
    have h_scalar : ContDiffOn ℝ ∞ (scalarOnE (I := I) α f)
        (extChartAt I α).target :=
      scalarOnE_contDiffOn (I := I) α hf
    have h_maps : Set.MapsTo (fun y : EuclN => (toEuclidean (E := E)).symm y)
        (chartTargetEuclid (I := I) (M := M) α) (extChartAt I α).target := by
      intro y hy
      exact toEuclidean_symm_mem_target (I := I) hy
    exact h_scalar.comp h_toE_symm h_maps
  refine hsmooth.congr ?_
  intro y hy
  exact chartPullback_eq_compose_on_chartTargetEuclid (I := I) α f hy

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in
private lemma contDiff_of_smooth_on_open_zero_outside
    {U : Set EuclN} (hU : IsOpen U) {K : Set EuclN} (hK : IsClosed K)
    (hKU : K ⊆ U) {f : EuclN → ℝ}
    (hf_smooth : ContDiffOn ℝ ∞ f U)
    (hf_zero : ∀ y, y ∉ K → f y = 0) :
    ContDiff ℝ ∞ f := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ U
  · exact (hf_smooth.contDiffWithinAt hy).contDiffAt (hU.mem_nhds hy)
  · have hyK : y ∉ K := fun h => hy (hKU h)
    have hKc_open : IsOpen Kᶜ := hK.isOpen_compl
    have hf_zero_on : Kᶜ ∈ 𝓝 y := hKc_open.mem_nhds hyK
    have hzero_at : ContDiffAt ℝ ∞ (fun _ : EuclN => (0 : ℝ)) y :=
      contDiff_const.contDiffAt
    refine hzero_at.congr_of_eventuallyEq ?_
    filter_upwards [hf_zero_on] with z hz
    exact hf_zero z hz

section

variable [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
lemma chartPullback_contDiff [I.Boundaryless]
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_cs : HasCompactSupport f)
    (hf_support : tsupport f ⊆ (chartAt H α).source) :
    ContDiff ℝ ∞ (chartPullback (I := I) α f) := by
  refine contDiff_of_smooth_on_open_zero_outside
    (U := chartTargetEuclid (I := I) (M := M) α)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (K := euclideanChartImageOfTsupport (I := I) (M := M) α f)
    (euclideanChartImageOfTsupport_isClosed (I := I) (M := M) α hf_cs hf_support)
    (euclideanChartImageOfTsupport_subset_chartTargetEuclid (I := I) (M := M) α hf_support)
    ?_ ?_
  · exact chartPullback_contDiffOn_chartTargetEuclid (I := I) α hf
  · intro y hy
    by_cases hyT : y ∈ chartTargetEuclid (I := I) (M := M) α
    · rw [chartPullback_apply_of_mem (I := I) α f hyT]
      by_contra hne
      have hsymm_support : (extChartAt I α).symm ((toEuclidean (E := E)).symm y)
          ∈ tsupport f := subset_tsupport _ hne
      refine hy ?_
      refine ⟨(extChartAt I α) ((extChartAt I α).symm
          ((toEuclidean (E := E)).symm y)), ?_, ?_⟩
      · exact ⟨_, hsymm_support, rfl⟩
      · rcases hyT with ⟨z, hz_target, hz_eq⟩
        have h1 : (extChartAt I α) ((extChartAt I α).symm z) = z :=
          (extChartAt I α).right_inv hz_target
        have hsymm_eq : (toEuclidean (E := E)).symm y = z := by
          rw [← hz_eq]; simp
        rw [hsymm_eq, h1, hz_eq]
    · exact chartPullback_apply_of_notMem (I := I) α f hyT

def negDensityLaplacianPullback [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (α : M) : EuclN → ℝ :=
  fun y => (chartTargetEuclid (I := I) (M := M) α).indicator
    (fun z => -(densityOnEuclid (I := I) g α z) *
      (ΔG (I := I) g ⟨_, hf⟩) ((extChartAt I α).symm
        ((toEuclidean (E := E)).symm z))) y

@[simp] lemma negDensityLaplacianPullback_apply_of_mem [I.Boundaryless] (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (α : M) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    negDensityLaplacianPullback (I := I) g hf α y =
      -(densityOnEuclid (I := I) g α y) *
        (ΔG (I := I) g ⟨_, hf⟩) ((extChartAt I α).symm
          ((toEuclidean (E := E)).symm y)) :=
  Set.indicator_of_mem hy _

@[simp] lemma negDensityLaplacianPullback_apply_of_notMem [I.Boundaryless] (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (α : M) {y : EuclN}
    (hy : y ∉ chartTargetEuclid (I := I) (M := M) α) :
    negDensityLaplacianPullback (I := I) g hf α y = 0 :=
  Set.indicator_of_notMem hy _

end

variable [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in
theorem exists_chart_metric_bilinearForm
    [I.Boundaryless] (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ Ω' : Set EuclN,
      IsOpen Ω' ∧ K ⊆ Ω' ∧ IsCompact (closure Ω') ∧
      closure Ω' ⊆ chartTargetEuclid (I := I) (M := M) α ∧
    ∃ B : SmoothEllipticBilinearForm (Module.finrank ℝ E) (Set.univ : Set EuclN),
      (∀ y ∈ K, ∀ i j : Fin (Module.finrank ℝ E),
        B.a y i j = weightedInvGramOnEuclid (I := I) g α i j y) ∧
      B.c = (fun _ : EuclN => (0 : ℝ)) :=
  exists_smooth_metric_extension (I := I) (M := M) g α hK hK_target

variable [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in
theorem chart_pulled_smooth_weak_solution_of_chartIdentity
    [I.Boundaryless] (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_cs : HasCompactSupport f)
    (hf_support : tsupport f ⊆ (chartAt H α).source)
    (B : SmoothEllipticBilinearForm (Module.finrank ℝ E) (Set.univ : Set EuclN))
    (hbilin :
      ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        B.bilin (chartPullback (I := I) α f) ψ =
          ∫ y, negDensityLaplacianPullback (I := I) g hf α y * ψ y) :
    B.IsSmoothWeakSolution (chartPullback (I := I) α f)
      (negDensityLaplacianPullback (I := I) g hf α) := by
  refine ⟨chartPullback_contDiff (I := I) α hf hf_cs hf_support, ?_⟩
  intro ψ hψ hψ_cs _hψ_support
  rw [MeasureTheory.setIntegral_univ]
  exact hbilin ψ hψ hψ_cs

variable [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in
def chartTestPullback (α : M) (ψ : EuclN → ℝ) : M → ℝ :=
  fun x => (chartAt H α).source.indicator
    (fun y => ψ (toEuclidean (E := E) ((extChartAt I α) y))) x

variable [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] in
@[simp] lemma chartTestPullback_apply_of_mem
    (α : M) (ψ : EuclN → ℝ) {x : M} (hx : x ∈ (chartAt H α).source) :
    chartTestPullback (I := I) α ψ x =
      ψ (toEuclidean (E := E) ((extChartAt I α) x)) :=
  Set.indicator_of_mem hx _

variable [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] in
@[simp] lemma chartTestPullback_apply_of_notMem
    (α : M) (ψ : EuclN → ℝ) {x : M} (hx : x ∉ (chartAt H α).source) :
    chartTestPullback (I := I) α ψ x = 0 :=
  Set.indicator_of_notMem hx _

end ChartLocalLaplacian
end Laplacian
end Analysis
end CalabiYau
