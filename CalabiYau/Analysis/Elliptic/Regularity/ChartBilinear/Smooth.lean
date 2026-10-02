-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/ChartBilinear/Smooth.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Calculus.Cutoff.Compact
public import CalabiYau.Analysis.Elliptic.Operator.ChartLocalLaplacian
public import CalabiYau.Analysis.Elliptic.Operator.ChartMeasureEquiv
public import CalabiYau.Analysis.Elliptic.MetricExtension
public import CalabiYau.Geometry.Riemannian.Operator.Gradient.Coordinates
public import CalabiYau.Geometry.Riemannian.Operator.Laplacian.Basic
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Green.Identities
public import CalabiYau.Geometry.Riemannian.Volume.Chart.Density
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Map

@[expose] public section
open CalabiYau.Riemannian

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators

namespace CalabiYau
namespace Analysis
namespace Laplacian
namespace ChartBilinearSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Laplacian.MetricExtension
open CalabiYau.Analysis.Laplacian.ChartLocalLaplacian
open CalabiYau.Laplacian.ChartMeasureEquiv
open Sobolev.NirenbergEuclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private def manifoldTestSupport (α : M) (ψ : EuclN → ℝ) : Set M :=
  ((extChartAt I α).symm) '' ((toEuclidean (E := E)).symm '' tsupport ψ)

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
private lemma manifoldTestSupport_isCompact (α : M)
    {ψ : EuclN → ℝ} (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    IsCompact (manifoldTestSupport (I := I) (M := M) α ψ) := by
  classical
  have h1 : IsCompact ((toEuclidean (E := E)).symm '' tsupport ψ) :=
    (hψ_cs : IsCompact (tsupport ψ)).image (toEuclidean (E := E)).symm.continuous
  have hmaps : ((toEuclidean (E := E)).symm '' tsupport ψ) ⊆ (extChartAt I α).target := by
    intro z hz
    rcases hz with ⟨y, hy_support, hy_eq⟩
    have hy_in : y ∈ chartTargetEuclid (I := I) (M := M) α := hψ_support hy_support
    rw [← hy_eq]
    exact toEuclidean_symm_mem_target (I := I) hy_in
  have hcontOn : ContinuousOn (extChartAt I α).symm
      ((toEuclidean (E := E)).symm '' tsupport ψ) := by
    refine (continuousOn_extChartAt_symm (I := I) α).mono hmaps
  exact h1.image_of_continuousOn hcontOn

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
private lemma manifoldTestSupport_subset_source (α : M) (ψ : EuclN → ℝ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    manifoldTestSupport (I := I) (M := M) α ψ ⊆ (chartAt H α).source := by
  intro x hx
  rcases hx with ⟨z, hz_im, hz_eq⟩
  rcases hz_im with ⟨y, hy_support, hy_eq⟩
  have hy_in : y ∈ chartTargetEuclid (I := I) (M := M) α := hψ_support hy_support
  have hz_target : z ∈ (extChartAt I α).target := by
    rw [← hy_eq]
    exact toEuclidean_symm_mem_target (I := I) hy_in
  have hx_in_source : x ∈ (extChartAt I α).source := by
    rw [← hz_eq]
    exact (extChartAt I α).map_target hz_target
  rwa [extChartAt_source_eq_chartAt_source (I := I)] at hx_in_source

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
private lemma manifoldTestSupport_isClosed [T2Space M] (α : M)
    {ψ : EuclN → ℝ} (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    IsClosed (manifoldTestSupport (I := I) (M := M) α ψ) :=
  (manifoldTestSupport_isCompact (I := I) (M := M) α hψ_cs hψ_support).isClosed

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
private lemma chartTestPullback_support_subset (α : M) (ψ : EuclN → ℝ) :
    Function.support (chartTestPullback (I := I) (M := M) α ψ) ⊆
      manifoldTestSupport (I := I) (M := M) α ψ := by
  intro x hx
  rw [Function.mem_support] at hx
  by_cases hx_source : x ∈ (chartAt H α).source
  · rw [chartTestPullback_apply_of_mem (I := I) α ψ hx_source] at hx
    have hψ_support : (toEuclidean (E := E)) ((extChartAt I α) x) ∈ tsupport ψ :=
      subset_tsupport _ hx
    have hsymm_E :
        (toEuclidean (E := E)).symm ((toEuclidean (E := E)) ((extChartAt I α) x)) =
          (extChartAt I α) x :=
      (toEuclidean (E := E)).symm_apply_apply _
    refine ⟨(extChartAt I α) x, ?_, ?_⟩
    · refine ⟨(toEuclidean (E := E)) ((extChartAt I α) x), hψ_support, hsymm_E⟩
    · have hx_source' : x ∈ (extChartAt I α).source := by
        rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx_source
      exact (extChartAt I α).left_inv hx_source'
  · rw [chartTestPullback_apply_of_notMem (I := I) α ψ hx_source] at hx
    exact (hx rfl).elim

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
private lemma chartTestPullback_tsupport_subset [T2Space M] (α : M)
    {ψ : EuclN → ℝ} (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    tsupport (chartTestPullback (I := I) (M := M) α ψ) ⊆
      manifoldTestSupport (I := I) (M := M) α ψ :=
  closure_minimal (chartTestPullback_support_subset (I := I) (M := M) α ψ)
    (manifoldTestSupport_isClosed (I := I) (M := M) α hψ_cs hψ_support)

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
private lemma chartTestPullback_hasCompactSupport [T2Space M] (α : M)
    {ψ : EuclN → ℝ} (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    HasCompactSupport (chartTestPullback (I := I) (M := M) α ψ) :=
  HasCompactSupport.of_support_subset_isCompact
    (manifoldTestSupport_isCompact (I := I) (M := M) α hψ_cs hψ_support)
    (chartTestPullback_support_subset (I := I) (M := M) α ψ)

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
private lemma chartTestPullback_tsupport_subset_chart_source [T2Space M] (α : M)
    {ψ : EuclN → ℝ} (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    tsupport (chartTestPullback (I := I) (M := M) α ψ) ⊆ (chartAt H α).source :=
  (chartTestPullback_tsupport_subset (I := I) (M := M) α hψ_cs hψ_support).trans
    (manifoldTestSupport_subset_source (I := I) (M := M) α ψ hψ_support)

omit [NeZero (Module.finrank ℝ E)] in
private lemma compose_psi_contMDiffOn_chart_source (α : M)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => ψ ((toEuclidean (E := E)) ((extChartAt I α) x)))
      (chartAt H α).source := by
  have h_ext : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
      (chartAt H α).source := contMDiffOn_extChartAt
  have h_toE_cd : ContDiff ℝ (⊤ : ℕ∞) (toEuclidean (E := E)) :=
    (toEuclidean (E := E)).contDiff
  have h_toE_M : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclN) ∞ (toEuclidean (E := E)) :=
    (contMDiff_iff_contDiff (n := (⊤ : ℕ∞))).mpr h_toE_cd
  have h_psi_M : ContMDiff 𝓘(ℝ, EuclN) 𝓘(ℝ, ℝ) ∞ ψ :=
    (contMDiff_iff_contDiff (n := (⊤ : ℕ∞))).mpr hψ
  have h_toE_M_univ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, EuclN) ∞ (toEuclidean (E := E)) Set.univ :=
    h_toE_M.contMDiffOn
  have h_psi_M_univ : ContMDiffOn 𝓘(ℝ, EuclN) 𝓘(ℝ, ℝ) ∞ ψ Set.univ :=
    h_psi_M.contMDiffOn
  have hMaps1 : Set.MapsTo (extChartAt I α : M → E) (chartAt H α).source Set.univ :=
    fun _ _ => Set.mem_univ _
  have hMaps2 : Set.MapsTo (toEuclidean (E := E) : E → EuclN) Set.univ Set.univ :=
    fun _ _ => Set.mem_univ _
  have h1 : ContMDiffOn I 𝓘(ℝ, EuclN) ∞
      (fun x : M => (toEuclidean (E := E)) ((extChartAt I α) x))
      (chartAt H α).source :=
    h_toE_M_univ.comp h_ext hMaps1
  exact h_psi_M_univ.comp h1 (fun _ _ => Set.mem_univ _)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
private lemma contMDiff_of_smoothOn_open_zero_outside
    {U : Set M} (hU : IsOpen U) {K : Set M} (hK : IsClosed K)
    (hKU : K ⊆ U) {f : M → ℝ}
    (hf_smooth : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U)
    (hf_zero : ∀ y, y ∉ K → f y = 0) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ f := by
  intro y
  by_cases hy : y ∈ U
  · exact (hf_smooth y hy).contMDiffAt (hU.mem_nhds hy)
  · have hyK : y ∉ K := fun h => hy (hKU h)
    have hKc_open : IsOpen Kᶜ := hK.isOpen_compl
    have hf_zero_on : Kᶜ ∈ 𝓝 y := hKc_open.mem_nhds hyK
    have hzero_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun _ : M => (0 : ℝ)) y :=
      contMDiff_const.contMDiffAt
    refine hzero_at.congr_of_eventuallyEq ?_
    filter_upwards [hf_zero_on] with z hz
    exact hf_zero z hz

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartTestPullback_contMDiff [T2Space M] (α : M)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (chartTestPullback (I := I) (M := M) α ψ) := by
  refine contMDiff_of_smoothOn_open_zero_outside
    (U := (chartAt H α).source)
    (chartAt H α).open_source
    (K := manifoldTestSupport (I := I) (M := M) α ψ)
    (manifoldTestSupport_isClosed (I := I) (M := M) α hψ_cs hψ_support)
    (manifoldTestSupport_subset_source (I := I) (M := M) α ψ hψ_support)
    ?_ ?_
  · have hcompose : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun x : M => ψ ((toEuclidean (E := E)) ((extChartAt I α) x)))
        (chartAt H α).source :=
      compose_psi_contMDiffOn_chart_source (I := I) (M := M) α hψ
    refine hcompose.congr ?_
    intro x hx
    exact chartTestPullback_apply_of_mem (I := I) α ψ hx
  · intro y hy
    by_cases hy_source : y ∈ (chartAt H α).source
    · rw [chartTestPullback_apply_of_mem (I := I) α ψ hy_source]
      by_contra hne
      have hin_tsupp : (toEuclidean (E := E)) ((extChartAt I α) y) ∈ tsupport ψ :=
        subset_tsupport _ hne
      refine hy ?_
      refine ⟨(extChartAt I α) y, ?_, ?_⟩
      · refine ⟨(toEuclidean (E := E)) ((extChartAt I α) y), hin_tsupp, ?_⟩
        exact (toEuclidean (E := E)).symm_apply_apply _
      · have hy_source' : y ∈ (extChartAt I α).source := by
          rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hy_source
        exact (extChartAt I α).left_inv hy_source'
    · exact chartTestPullback_apply_of_notMem (I := I) α ψ hy_source

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
private lemma chartPullback_chartTestPullback_eq (α : M) (ψ : EuclN → ℝ)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPullback (I := I) α (chartTestPullback (I := I) (M := M) α ψ) y = ψ y := by
  classical
  have h_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
    toEuclidean_symm_mem_target (I := I) hy
  set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
  have hx_source : x ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target h_target
  have hx_chart_source : x ∈ (chartAt H α).source := by
    rwa [extChartAt_source_eq_chartAt_source (I := I)] at hx_source
  rw [chartPullback_apply_of_mem (I := I) α (chartTestPullback (I := I) (M := M) α ψ) hy]
  change chartTestPullback (I := I) (M := M) α ψ x = ψ y
  rw [chartTestPullback_apply_of_mem (I := I) α ψ hx_chart_source]
  have h_right_inv :
      (extChartAt I α) ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
        (toEuclidean (E := E)).symm y :=
    (extChartAt I α).right_inv h_target
  have h_apply_inv :
      (toEuclidean (E := E)) ((toEuclidean (E := E)).symm y) = y :=
    (toEuclidean (E := E)).apply_symm_apply y
  change ψ ((toEuclidean (E := E)) ((extChartAt I α) x)) = ψ y
  rw [h_right_inv, h_apply_inv]

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
private lemma fderiv_chartPullback_eq_partialDeriv_scalarOnE
    [I.Boundaryless] (α : M) (f : M → ℝ)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α)
    (i : Fin (Module.finrank ℝ E)) :
    fderiv ℝ (chartPullback (I := I) α f) y (EuclideanSpace.single i (1 : ℝ)) =
      CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (scalarOnE (I := I) α f)
        ((toEuclidean (E := E)).symm y) := by
  classical
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_eq_eventually :
      chartPullback (I := I) α f =ᶠ[𝓝 y]
        (fun z : EuclN => scalarOnE (I := I) α f ((toEuclidean (E := E)).symm z)) := by
    filter_upwards [h_open.mem_nhds hy] with z hz
    rw [chartPullback_apply_of_mem (I := I) α f hz]; rfl
  have h_fderiv_eq :
      fderiv ℝ (chartPullback (I := I) α f) y =
        fderiv ℝ
          (fun z : EuclN => scalarOnE (I := I) α f ((toEuclidean (E := E)).symm z)) y :=
    Filter.EventuallyEq.fderiv_eq h_eq_eventually
  rw [h_fderiv_eq]
  have h_eq_compose :
      (fun z : EuclN => scalarOnE (I := I) α f ((toEuclidean (E := E)).symm z)) =
        scalarOnE (I := I) α f ∘ ((toEuclidean (E := E)).symm) := by
    funext z; rfl
  rw [h_eq_compose]
  rw [(toEuclidean (E := E)).symm.comp_right_fderiv]
  rw [ContinuousLinearMap.coe_comp, Function.comp_apply]
  have h_iso_apply :
      ((toEuclidean (E := E)).symm : EuclN →L[ℝ] E)
        (EuclideanSpace.single i (1 : ℝ)) = (CalabiYau.Tensor.Coordinates.chartModelBasis E) i := by
    rw [CalabiYau.Tensor.Coordinates.chartModelBasis_apply]
    rfl
  rw [h_iso_apply]
  rfl

private theorem densityOnEuclid_inner_grad_eq_principalIntegrand
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ}
    {ψ : EuclN → ℝ}
    (B : SmoothEllipticBilinearForm (Module.finrank ℝ E) (Set.univ : Set EuclN))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α)
    (hB_match : ∀ i j : Fin (Module.finrank ℝ E),
      B.a y i j = weightedInvGramOnEuclid (I := I) g α i j y) :
    densityOnEuclid (I := I) g α y *
      g.inner ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (gradFun (I := I) g f
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (gradFun (I := I) g (chartTestPullback (I := I) (M := M) α ψ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) =
      B.principalIntegrand (chartPullback (I := I) α f) ψ y := by
  classical
  set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
  have h_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
    toEuclidean_symm_mem_target (I := I) hy
  have hx_source : x ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target h_target
  have hx_chart_source : x ∈ (chartAt H α).source := by
    rwa [extChartAt_source_eq_chartAt_source (I := I)] at hx_source
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]; exact hx_chart_source
  have hx_int : extChartAt I α x ∈ interior (extChartAt I α).target := by
    have h_φx : extChartAt I α x = (toEuclidean (E := E)).symm y := by
      rw [hx_def]; exact (extChartAt I α).right_inv h_target
    rw [h_φx]
    exact extChartAt_target_subset_interior_of_boundaryless (I := I) α h_target
  have h_step1 := inner_gradFun_eq_chartInvGram_sum
    (I := I) g α f (chartTestPullback (I := I) (M := M) α ψ) hx_base hx_int
  rw [h_step1]
  rw [show densityOnEuclid (I := I) g α y *
        ∑ i, ∑ j, chartInvGramMatrix (I := I) g α x i j *
          CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) *
          CalabiYau.Tensor.Coordinates.partialDeriv (E := E) j
            (scalarOnE (I := I) α (chartTestPullback (I := I) (M := M) α ψ))
            (extChartAt I α x)
        =
      ∑ i, ∑ j, (densityOnEuclid (I := I) g α y *
            chartInvGramMatrix (I := I) g α x i j) *
          CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) *
          CalabiYau.Tensor.Coordinates.partialDeriv (E := E) j
            (scalarOnE (I := I) α (chartTestPullback (I := I) (M := M) α ψ))
            (extChartAt I α x) from ?_]
  swap
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  have h_weight_eq : ∀ i j : Fin (Module.finrank ℝ E),
      densityOnEuclid (I := I) g α y * chartInvGramMatrix (I := I) g α x i j =
        weightedInvGramOnEuclid (I := I) g α i j y := by
    intro i j; rfl
  have hφx_eq : extChartAt I α x = (toEuclidean (E := E)).symm y := by
    rw [hx_def]; exact (extChartAt I α).right_inv h_target
  have h_partial_f : ∀ i : Fin (Module.finrank ℝ E),
      CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) =
        fderiv ℝ (chartPullback (I := I) α f) y (EuclideanSpace.single i (1 : ℝ)) := by
    intro i
    rw [hφx_eq]
    rw [fderiv_chartPullback_eq_partialDeriv_scalarOnE
      (I := I) α f hy i]
  have h_partial_psi : ∀ j : Fin (Module.finrank ℝ E),
      CalabiYau.Tensor.Coordinates.partialDeriv (E := E) j
        (scalarOnE (I := I) α (chartTestPullback (I := I) (M := M) α ψ))
        (extChartAt I α x) =
      fderiv ℝ ψ y (EuclideanSpace.single j (1 : ℝ)) := by
    intro j
    have h1 : fderiv ℝ (chartPullback (I := I) α
            (chartTestPullback (I := I) (M := M) α ψ)) y
          (EuclideanSpace.single j (1 : ℝ)) =
        CalabiYau.Tensor.Coordinates.partialDeriv (E := E) j
          (scalarOnE (I := I) α (chartTestPullback (I := I) (M := M) α ψ))
          ((toEuclidean (E := E)).symm y) :=
      fderiv_chartPullback_eq_partialDeriv_scalarOnE
        (I := I) α (chartTestPullback (I := I) (M := M) α ψ) hy j
    have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    have h_ev : chartPullback (I := I) α (chartTestPullback (I := I) (M := M) α ψ)
        =ᶠ[𝓝 y] ψ := by
      filter_upwards [h_open.mem_nhds hy] with z hz
      exact chartPullback_chartTestPullback_eq (I := I) (M := M) α ψ hz
    have h_fderiv_eq :
        fderiv ℝ (chartPullback (I := I) α (chartTestPullback (I := I) (M := M) α ψ)) y =
          fderiv ℝ ψ y :=
      Filter.EventuallyEq.fderiv_eq h_ev
    rw [hφx_eq, ← h1, h_fderiv_eq]
  unfold SmoothEllipticBilinearForm.principalIntegrand
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [h_weight_eq i j, h_partial_f i, h_partial_psi j, hB_match i j]

private theorem bilinear_identity_of_support_in_chartTarget
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_cs : HasCompactSupport f)
    (hf_support : tsupport f ⊆ (chartAt H α).source)
    (B : SmoothEllipticBilinearForm (Module.finrank ℝ E) (Set.univ : Set EuclN))
    (hB_c : B.c = (fun _ : EuclN => (0 : ℝ)))
    (hB_match : ∀ y ∈ euclideanChartImageOfTsupport (I := I) (M := M) α f,
      ∀ i j : Fin (Module.finrank ℝ E),
        B.a y i j = weightedInvGramOnEuclid (I := I) g α i j y)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    B.bilin (chartPullback (I := I) α f) ψ =
      ∫ y, negDensityLaplacianPullback (I := I) g hf α y * ψ y := by
  classical
  have h_zero : ∀ y : EuclN, B.c y * (chartPullback (I := I) α f) y * ψ y = 0 := by
    intro y; rw [hB_c]; simp
  have h_bilin_simplify :
      B.bilin (chartPullback (I := I) α f) ψ =
        ∫ y, B.principalIntegrand (chartPullback (I := I) α f) ψ y := by
    unfold SmoothEllipticBilinearForm.bilin
    rw [MeasureTheory.setIntegral_univ]
    refine MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun y => ?_))
    change B.principalIntegrand (chartPullback (I := I) α f) ψ y +
        B.c y * chartPullback (I := I) α f y * ψ y =
      B.principalIntegrand (chartPullback (I := I) α f) ψ y
    rw [h_zero y]; ring
  rw [h_bilin_simplify]
  have hψM : ContMDiff I 𝓘(ℝ, ℝ) ∞ (chartTestPullback (I := I) (M := M) α ψ) :=
    chartTestPullback_contMDiff (I := I) (M := M) α hψ hψ_cs hψ_support
  have h_green := green_first_integral_inner_grad_eq_neg_integral_smul_laplacian
    (I := I) g hψM hf hf_cs
  have h_LHS_swap_eq : ∀ x : M,
      g.inner x ((gradG (I := I) g ⟨_, hf⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((gradG (I := I) g ⟨_, hψM⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      g.inner x ((gradG (I := I) g ⟨_, hψM⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((gradG (I := I) g ⟨_, hf⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) :=
    fun x => g.symm x _ _
  have h_green_swap :
      ∫ x, g.inner x ((gradG (I := I) g ⟨_, hf⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((gradG (I := I) g ⟨_, hψM⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      -∫ x, chartTestPullback (I := I) (M := M) α ψ x * ΔG (I := I) g ⟨_, hf⟩ x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h_LHS_swap_eq)]
    exact h_green
  set u : M → ℝ := fun x => g.inner x
      ((gradG (I := I) g ⟨_, hf⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
      ((gradG (I := I) g ⟨_, hψM⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) with hu_def
  set v : M → ℝ := fun x =>
      chartTestPullback (I := I) (M := M) α ψ x * ΔG (I := I) g ⟨_, hf⟩ x with hv_def
  have hu_cont : Continuous u := by
    have h_eq_action : u = tangentSectionAction (I := I)
        (gradG (I := I) g ⟨_, hψM⟩) f := by
      funext x
      rw [hu_def]
      change g.inner x
        ((gradG (I := I) g (⟨f, hf⟩ : C^∞⟮I, M; ℝ⟯) :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g
          (⟨chartTestPullback α ψ, hψM⟩ : C^∞⟮I, M; ℝ⟯) : Cₛ^∞⟮I; E,
          (TangentSpace I : M → Type _)⟯) x) =
        mfderiv I 𝓘(ℝ, ℝ) f x
          ((gradG (I := I) g
            (⟨chartTestPullback α ψ, hψM⟩ : C^∞⟮I, M; ℝ⟯) :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
      rw [grad_g_apply (I := I) g (⟨f, hf⟩ : C^∞⟮I, M; ℝ⟯) x]
      rw [grad_g_apply (I := I) g
        (⟨chartTestPullback α ψ, hψM⟩ : C^∞⟮I, M; ℝ⟯) x]
      change g.inner x (gradFun (I := I) g f x)
          (gradFun (I := I) g (chartTestPullback (I := I) (M := M) α ψ) x) =
        mfderiv I 𝓘(ℝ, ℝ) f x (gradFun (I := I) g (chartTestPullback (I := I) (M := M) α ψ) x)
      rw [g.symm x (gradFun (I := I) g f x) _]
      exact inner_gradFun_right (I := I) g f x
        (gradFun (I := I) g (chartTestPullback (I := I) (M := M) α ψ) x)
    rw [h_eq_action]
    exact (tangentSectionAction_contMDiff (I := I)
      (gradG (I := I) g ⟨_, hψM⟩) hf).continuous
  have hu_support : tsupport u ⊆ (chartAt H α).source := by
    have h_subset_grad_f :
        Function.support u ⊆ Function.support
          (fun x : M => ((gradG (I := I) g ⟨_, hf⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)) := by
      intro x hx
      change u x ≠ 0 at hx
      change ((gradG (I := I) g (⟨f, hf⟩ : C^∞⟮I, M; ℝ⟯) :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) ≠ 0
      intro hx_zero
      apply hx
      rw [hu_def]
      change g.inner x
        ((gradG (I := I) g ⟨_, hf⟩ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g ⟨_, hψM⟩ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) = 0
      rw [hx_zero]
      rw [ContinuousLinearMap.map_zero]
      rfl
    have h_grad_f_support_sub : Function.support
        (fun x : M => ((gradG (I := I) g ⟨_, hf⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)) ⊆
        tsupport f := by
      intro x hx
      change x ∈ Function.support (gradFun (I := I) g f) at hx
      exact support_gradFun_subset (I := I) g f hx
    exact (closure_minimal (h_subset_grad_f.trans h_grad_f_support_sub)
      (isClosed_tsupport _)).trans hf_support
  have hv_cont : Continuous v := by
    have h_test_cont : Continuous (chartTestPullback (I := I) (M := M) α ψ) :=
      hψM.continuous
    have h_lap_cont : Continuous (ΔG (I := I) g ⟨_, hf⟩) :=
      (Δ_g_contMDiff (I := I) g ⟨_, hf⟩).continuous
    exact h_test_cont.mul h_lap_cont
  have hv_support : tsupport v ⊆ (chartAt H α).source := by
    have h_support_v : Function.support v ⊆
        tsupport (chartTestPullback (I := I) (M := M) α ψ) := by
      intro x hx
      rw [Function.mem_support] at hx
      apply subset_tsupport
      rw [Function.mem_support]
      intro hx_zero
      apply hx
      change chartTestPullback (I := I) (M := M) α ψ x * ΔG (I := I) g ⟨_, hf⟩ x = 0
      rw [hx_zero]; ring
    exact (closure_minimal h_support_v (isClosed_tsupport _)).trans
      (chartTestPullback_tsupport_subset_chart_source
        (I := I) (M := M) α hψ_cs hψ_support)
  have h_pull_LHS :=
    integral_riemannianVolumeMeasure_eq_euclidean_chartTarget
      (I := I) (M := M) g α (f := u) hu_cont hu_support
  have h_pull_RHS :=
    integral_riemannianVolumeMeasure_eq_euclidean_chartTarget
      (I := I) (M := M) g α (f := v) hv_cont hv_support
  have h_LHS_integrand_eq : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y *
        u ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      B.principalIntegrand (chartPullback (I := I) α f) ψ y := by
    intro y hy
    by_cases hy_in_Kmain : y ∈ euclideanChartImageOfTsupport (I := I) (M := M) α f
    · rw [hu_def]
      exact densityOnEuclid_inner_grad_eq_principalIntegrand
        (I := I) g α B hy (hB_match y hy_in_Kmain)
    · set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
      have h_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
        toEuclidean_symm_mem_target (I := I) hy
      have hx_not_in_tsupp_f : x ∉ tsupport f := by
        intro hx_in
        apply hy_in_Kmain
        refine ⟨(extChartAt I α) x, ?_, ?_⟩
        · refine ⟨x, hx_in, rfl⟩
        · rw [hx_def, (extChartAt I α).right_inv h_target]
          exact (toEuclidean (E := E)).apply_symm_apply y
      have h_grad_zero :
          ((gradG (I := I) g ⟨_, hf⟩ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
            (0 : TangentSpace I x) := by
        change gradFun (I := I) g f x = (0 : TangentSpace I x)
        by_contra h
        have hx_in_support : x ∈ Function.support (gradFun (I := I) g f) := h
        exact hx_not_in_tsupp_f
          (support_gradFun_subset (I := I) g f hx_in_support)
      have h_u_zero : u x = 0 := by
        rw [hu_def]
        change g.inner x
          ((gradG (I := I) g ⟨_, hf⟩ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((gradG (I := I) g ⟨_, hψM⟩ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) = 0
        rw [h_grad_zero, ContinuousLinearMap.map_zero]
        rfl
      have hy_not_in_chartPull_tsupp :
          y ∉ tsupport (chartPullback (I := I) α f) := fun h =>
        hy_in_Kmain (chartPullback_tsupport_subset (I := I) α hf_cs hf_support h)
      have h_compl_open : IsOpen (tsupport (chartPullback (I := I) α f))ᶜ :=
        (isClosed_tsupport _).isOpen_compl
      have h_ev : chartPullback (I := I) α f =ᶠ[𝓝 y]
          (fun _ : EuclN => (0 : ℝ)) := by
        filter_upwards [h_compl_open.mem_nhds hy_not_in_chartPull_tsupp] with z hz
        by_contra hne
        exact hz (subset_tsupport _ hne)
      have h_fderiv_zero : fderiv ℝ (chartPullback (I := I) α f) y = 0 := by
        rw [Filter.EventuallyEq.fderiv_eq h_ev]
        exact fderiv_const_apply _
      have h_principal_zero :
          B.principalIntegrand (chartPullback (I := I) α f) ψ y = 0 := by
        unfold SmoothEllipticBilinearForm.principalIntegrand
        refine Finset.sum_eq_zero ?_
        intro i _
        refine Finset.sum_eq_zero ?_
        intro j _
        rw [h_fderiv_zero]
        change B.a y i j * (0 : EuclN →L[ℝ] ℝ) (EuclideanSpace.single i 1) *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1) = 0
        rw [zero_apply]; ring
      rw [h_u_zero, mul_zero, h_principal_zero]
  have h_LHS_setInt_eq :
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          u ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        ∂(MeasureTheory.Measure.map (toEuclidean : E → EuclN)
            (modelHaar (E := E))) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        B.principalIntegrand (chartPullback (I := I) α f) ψ y
        ∂(MeasureTheory.Measure.map (toEuclidean : E → EuclN)
            (modelHaar (E := E))) := by
    apply MeasureTheory.setIntegral_congr_fun
    · exact (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
    · intro y hy
      exact h_LHS_integrand_eq y hy
  have h_RHS_integrand_eq : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y *
        v ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      -negDensityLaplacianPullback (I := I) g hf α y * ψ y := by
    intro y hy
    rw [hv_def]
    set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
    have h_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
      toEuclidean_symm_mem_target (I := I) hy
    have hx_source : x ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target h_target
    have hx_chart_source : x ∈ (chartAt H α).source := by
      rwa [extChartAt_source_eq_chartAt_source (I := I)] at hx_source
    have h_test_at_x :
        chartTestPullback (I := I) (M := M) α ψ x =
          ψ ((toEuclidean (E := E)) ((extChartAt I α) x)) :=
      chartTestPullback_apply_of_mem (I := I) α ψ hx_chart_source
    have h_φx_eq : extChartAt I α x = (toEuclidean (E := E)).symm y := by
      rw [hx_def]; exact (extChartAt I α).right_inv h_target
    have h_apply_inv :
        (toEuclidean (E := E)) ((toEuclidean (E := E)).symm y) = y :=
      (toEuclidean (E := E)).apply_symm_apply y
    have h_test_simp : chartTestPullback (I := I) (M := M) α ψ x = ψ y := by
      rw [h_test_at_x, h_φx_eq, h_apply_inv]
    have h_negDens :
        negDensityLaplacianPullback (I := I) g hf α y =
          -(densityOnEuclid (I := I) g α y) *
            (ΔG (I := I) g ⟨_, hf⟩) ((extChartAt I α).symm
              ((toEuclidean (E := E)).symm y)) :=
      negDensityLaplacianPullback_apply_of_mem (I := I) g hf α hy
    change densityOnEuclid (I := I) g α y *
          (chartTestPullback (I := I) (M := M) α ψ x * ΔG (I := I) g ⟨_, hf⟩ x) =
        -negDensityLaplacianPullback (I := I) g hf α y * ψ y
    rw [h_test_simp, h_negDens]
    change densityOnEuclid (I := I) g α y *
          (ψ y * ΔG (I := I) g ⟨_, hf⟩ x) =
        -(-(densityOnEuclid (I := I) g α y) * ΔG (I := I) g ⟨_, hf⟩ x) * ψ y
    ring
  have h_RHS_setInt_eq :
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          v ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        ∂(MeasureTheory.Measure.map (toEuclidean : E → EuclN)
            (modelHaar (E := E))) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        -negDensityLaplacianPullback (I := I) g hf α y * ψ y
        ∂(MeasureTheory.Measure.map (toEuclidean : E → EuclN)
            (modelHaar (E := E))) := by
    apply MeasureTheory.setIntegral_congr_fun
    · exact (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
    · intro y hy
      exact h_RHS_integrand_eq y hy
  have hctE_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  have h_LHS_volume :
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        B.principalIntegrand (chartPullback (I := I) α f) ψ y
        ∂(MeasureTheory.Measure.map (toEuclidean : E → EuclN)
            (modelHaar (E := E))) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        B.principalIntegrand (chartPullback (I := I) α f) ψ y ∂volume := by
    rw [map_toEuclidean_modelHaar_eq_volume]
  have h_RHS_volume :
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        -negDensityLaplacianPullback (I := I) g hf α y * ψ y
        ∂(MeasureTheory.Measure.map (toEuclidean : E → EuclN)
            (modelHaar (E := E))) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        -negDensityLaplacianPullback (I := I) g hf α y * ψ y ∂volume := by
    rw [map_toEuclidean_modelHaar_eq_volume]
  have h_principal_zero_off : ∀ y ∉ chartTargetEuclid (I := I) (M := M) α,
      B.principalIntegrand (chartPullback (I := I) α f) ψ y = 0 := by
    intro y hy_not
    have hy_not_support : y ∉ tsupport (chartPullback (I := I) α f) := fun hy_support =>
      hy_not (chartPullback_tsupport_subset_chartTargetEuclid
        (I := I) α hf_cs hf_support hy_support)
    have h_open : IsOpen (tsupport (chartPullback (I := I) α f))ᶜ :=
      (isClosed_tsupport _).isOpen_compl
    have h_ev : chartPullback (I := I) α f =ᶠ[𝓝 y]
        (fun _ : EuclN => (0 : ℝ)) := by
      filter_upwards [h_open.mem_nhds hy_not_support] with z hz
      by_contra hne
      have hz_support : z ∈ tsupport (chartPullback (I := I) α f) :=
        subset_tsupport _ hne
      exact hz hz_support
    have h_fderiv_zero : fderiv ℝ (chartPullback (I := I) α f) y = 0 := by
      rw [Filter.EventuallyEq.fderiv_eq h_ev]
      exact fderiv_const_apply _
    unfold SmoothEllipticBilinearForm.principalIntegrand
    refine Finset.sum_eq_zero ?_
    intro i _
    refine Finset.sum_eq_zero ?_
    intro j _
    rw [h_fderiv_zero]
    change B.a y i j * (0 : EuclN →L[ℝ] ℝ) (EuclideanSpace.single i 1) *
        (fderiv ℝ ψ y) (EuclideanSpace.single j 1) = 0
    rw [zero_apply]; ring
  have h_LHS_setInt_to_int :
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        B.principalIntegrand (chartPullback (I := I) α f) ψ y ∂volume =
      ∫ y, B.principalIntegrand (chartPullback (I := I) α f) ψ y ∂volume := by
    rw [show (∫ y in chartTargetEuclid (I := I) (M := M) α,
              B.principalIntegrand (chartPullback (I := I) α f) ψ y ∂volume) =
            ∫ y, (chartTargetEuclid (I := I) (M := M) α).indicator
                (fun z => B.principalIntegrand (chartPullback (I := I) α f) ψ z) y ∂volume from
      (MeasureTheory.integral_indicator hctE_meas).symm]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro y
    by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, h_principal_zero_off y hy]
  have h_negDens_zero_off : ∀ y ∉ chartTargetEuclid (I := I) (M := M) α,
      -negDensityLaplacianPullback (I := I) g hf α y * ψ y = 0 := by
    intro y hy_not
    rw [negDensityLaplacianPullback_apply_of_notMem (I := I) g hf α hy_not]
    ring
  have h_RHS_setInt_to_int :
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        -negDensityLaplacianPullback (I := I) g hf α y * ψ y ∂volume =
      ∫ y, -negDensityLaplacianPullback (I := I) g hf α y * ψ y ∂volume := by
    rw [show (∫ y in chartTargetEuclid (I := I) (M := M) α,
              -negDensityLaplacianPullback (I := I) g hf α y * ψ y ∂volume) =
            ∫ y, (chartTargetEuclid (I := I) (M := M) α).indicator
                (fun z => -negDensityLaplacianPullback (I := I) g hf α z * ψ z) y ∂volume from
      (MeasureTheory.integral_indicator hctE_meas).symm]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro y
    change (chartTargetEuclid (I := I) (M := M) α).indicator
        (fun z => -negDensityLaplacianPullback (I := I) g hf α z * ψ z) y =
      -negDensityLaplacianPullback (I := I) g hf α y * ψ y
    by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, h_negDens_zero_off y hy]
  have h_LHS_M_to_volume :
      ∫ x, u x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ y, B.principalIntegrand (chartPullback (I := I) α f) ψ y ∂volume := by
    rw [h_pull_LHS, h_LHS_setInt_eq, h_LHS_volume, h_LHS_setInt_to_int]
  have h_RHS_M_to_volume :
      ∫ x, v x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ y, -negDensityLaplacianPullback (I := I) g hf α y * ψ y ∂volume := by
    rw [h_pull_RHS, h_RHS_setInt_eq, h_RHS_volume, h_RHS_setInt_to_int]
  have h_combine : ∫ y, B.principalIntegrand (chartPullback (I := I) α f) ψ y ∂volume =
      -∫ y, -negDensityLaplacianPullback (I := I) g hf α y * ψ y ∂volume := by
    rw [← h_LHS_M_to_volume, ← h_RHS_M_to_volume]
    exact h_green_swap
  rw [h_combine]
  rw [show (∫ y, -negDensityLaplacianPullback (I := I) g hf α y * ψ y ∂volume) =
        -∫ y, negDensityLaplacianPullback (I := I) g hf α y * ψ y ∂volume from ?_]
  · ring
  · rw [show (fun y => -negDensityLaplacianPullback (I := I) g hf α y * ψ y) =
          (fun y => -(negDensityLaplacianPullback (I := I) g hf α y * ψ y)) from ?_]
    · rw [MeasureTheory.integral_neg]
    · funext y; ring

omit [NeZero (Module.finrank ℝ E)] in
private lemma negDensityLaplacianPullback_support_subset
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    Function.support (negDensityLaplacianPullback (I := I) g hf α) ⊆
      euclideanChartImageOfTsupport (I := I) (M := M) α f := by
  intro y hy
  rw [Function.mem_support] at hy
  by_cases hy_in : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [negDensityLaplacianPullback_apply_of_mem (I := I) g hf α hy_in] at hy
    set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
    have h_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
      toEuclidean_symm_mem_target (I := I) hy_in
    have h_lap_ne : (ΔG (I := I) g ⟨_, hf⟩) x ≠ 0 := by
      intro h0
      apply hy
      rw [h0]; ring
    have hx_in_tsupp_lap : x ∈ tsupport (ΔG (I := I) g ⟨_, hf⟩) :=
      subset_tsupport _ h_lap_ne
    have h_lap_support_sub_grad :
        tsupport (ΔG (I := I) g ⟨_, hf⟩) ⊆ tsupport
          (fun x : M => ((gradG (I := I) g ⟨_, hf⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)) := by
      change tsupport (divergenceG (I := I) g (gradG (I := I) g ⟨_, hf⟩)) ⊆
        tsupport
          (fun x : M => ((gradG (I := I) g ⟨_, hf⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
      exact tsupport_divergence_g_subset (I := I) g _
    have h_grad_support_sub_tsupp_f :
        tsupport (fun x : M => ((gradG (I := I) g ⟨_, hf⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)) ⊆ tsupport f := by
      have h_subset : Function.support (fun x : M => ((gradG (I := I) g ⟨_, hf⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)) ⊆ tsupport f := by
        intro x hx
        change x ∈ Function.support (gradFun (I := I) g f) at hx
        exact support_gradFun_subset (I := I) g f hx
      exact closure_minimal h_subset (isClosed_tsupport _)
    have hx_in_tsupp_f : x ∈ tsupport f :=
      h_grad_support_sub_tsupp_f (h_lap_support_sub_grad hx_in_tsupp_lap)
    refine ⟨(extChartAt I α) x, ?_, ?_⟩
    · refine ⟨x, hx_in_tsupp_f, rfl⟩
    · rw [hx_def]
      rw [(extChartAt I α).right_inv h_target]
      exact (toEuclidean (E := E)).apply_symm_apply y
  · rw [negDensityLaplacianPullback_apply_of_notMem (I := I) g hf α hy_in] at hy
    exact (hy rfl).elim

omit [FiniteDimensional ℝ E] in
private lemma principalIntegrand_cutoff_eq
    (B : SmoothEllipticBilinearForm (Module.finrank ℝ E) (Set.univ : Set EuclN))
    {f : EuclN → ℝ} {ψ ρ : EuclN → ℝ}
    {U : Set EuclN} (hU_open : IsOpen U)
    (hU_cover : tsupport f ⊆ U)
    (hρ_one_on_U : ∀ y ∈ U, ρ y = 1)
    (y : EuclN) :
    B.principalIntegrand f ψ y = B.principalIntegrand f (fun z => ρ z * ψ z) y := by
  classical
  by_cases hy_in_U : y ∈ U
  · have h_ev : (fun z : EuclN => ρ z * ψ z) =ᶠ[𝓝 y] ψ := by
      filter_upwards [hU_open.mem_nhds hy_in_U] with z hz
      rw [hρ_one_on_U z hz, one_mul]
    have h_fderiv_eq :
        fderiv ℝ (fun z : EuclN => ρ z * ψ z) y = fderiv ℝ ψ y :=
      Filter.EventuallyEq.fderiv_eq h_ev
    unfold SmoothEllipticBilinearForm.principalIntegrand
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [h_fderiv_eq]
  · have hy_not_support : y ∉ tsupport f := fun hy_support => hy_in_U (hU_cover hy_support)
    have h_open_compl : IsOpen (tsupport f)ᶜ :=
      (isClosed_tsupport _).isOpen_compl
    have h_ev : f =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := by
      filter_upwards [h_open_compl.mem_nhds hy_not_support] with z hz
      by_contra hne
      exact hz (subset_tsupport _ hne)
    have h_fderiv_f_zero : fderiv ℝ f y = 0 := by
      rw [Filter.EventuallyEq.fderiv_eq h_ev]
      exact fderiv_const_apply _
    unfold SmoothEllipticBilinearForm.principalIntegrand
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [h_fderiv_f_zero]
    change B.a y i j * (0 : EuclN →L[ℝ] ℝ) (EuclideanSpace.single i 1) *
        (fderiv ℝ ψ y) (EuclideanSpace.single j 1) =
      B.a y i j * (0 : EuclN →L[ℝ] ℝ) (EuclideanSpace.single i 1) *
        (fderiv ℝ (fun z : EuclN => ρ z * ψ z) y) (EuclideanSpace.single j 1)
    rw [zero_apply]; ring

private theorem bilinear_identity_of_smooth
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_cs : HasCompactSupport f)
    (hf_support : tsupport f ⊆ (chartAt H α).source)
    (B : SmoothEllipticBilinearForm (Module.finrank ℝ E) (Set.univ : Set EuclN))
    (hB_c : B.c = (fun _ : EuclN => (0 : ℝ)))
    (hB_match : ∀ y ∈ euclideanChartImageOfTsupport (I := I) (M := M) α f,
      ∀ i j : Fin (Module.finrank ℝ E),
        B.a y i j = weightedInvGramOnEuclid (I := I) g α i j y)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (_hψ_cs : HasCompactSupport ψ) :
    B.bilin (chartPullback (I := I) α f) ψ =
      ∫ y, negDensityLaplacianPullback (I := I) g hf α y * ψ y := by
  classical
  set K_main : Set EuclN := euclideanChartImageOfTsupport (I := I) (M := M) α f with hKmain_def
  have hK_main_compact : IsCompact K_main :=
    euclideanChartImageOfTsupport_isCompact (I := I) (M := M) α hf_cs hf_support
  have hK_main_in_chart : K_main ⊆ chartTargetEuclid (I := I) (M := M) α :=
    euclideanChartImageOfTsupport_subset_chartTargetEuclid (I := I) (M := M) α hf_support
  have hOmega_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    hK_main_compact.exists_cthickening_subset_open hOmega_open hK_main_in_chart
  set K1 : Set EuclN := Metric.cthickening δ K_main with hK1_def
  set U : Set EuclN := Metric.thickening δ K_main with hU_def
  have hK1_compact : IsCompact K1 := hK_main_compact.cthickening (r := δ)
  have hU_open : IsOpen U := Metric.isOpen_thickening
  have hKmain_in_U : K_main ⊆ U := Metric.self_subset_thickening hδ_pos K_main
  have hU_in_K1 : U ⊆ K1 := Metric.thickening_subset_cthickening δ K_main
  have hK1_in_chart : K1 ⊆ chartTargetEuclid (I := I) (M := M) α := hδ
  obtain ⟨ρ, hρ_smooth, hρ_cs, hρ_one_nhds, hρ_tsupp, _hρ_range⟩ :=
    CalabiYau.exists_bump_compact
      (K := K1) (U := chartTargetEuclid (I := I) (M := M) α)
      hK1_compact hOmega_open hK1_in_chart
  have hρ_one : ∀ x ∈ K1, ρ x = 1 := fun _ hx =>
    hρ_one_nhds.self_of_nhdsSet hx
  have hρ_one_on_Kmain : ∀ y ∈ K_main, ρ y = 1 := fun y hy =>
    hρ_one y (hU_in_K1 (hKmain_in_U hy))
  have hρ_one_on_U : ∀ y ∈ U, ρ y = 1 := fun y hy =>
    hρ_one y (hU_in_K1 hy)
  have hChartPull_tsupp_in_Kmain :
      tsupport (chartPullback (I := I) α f) ⊆ K_main :=
    chartPullback_tsupport_subset (I := I) α hf_cs hf_support
  set ψ' : EuclN → ℝ := fun y => ρ y * ψ y with hψ'_def
  have hψ'_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ' := hρ_smooth.mul hψ
  have hψ'_cs : HasCompactSupport ψ' := by
    apply hρ_cs.mul_right
  have hψ'_support : tsupport ψ' ⊆ chartTargetEuclid (I := I) (M := M) α := by
    have hs : Function.support ψ' ⊆ tsupport ρ := by
      intro y hy
      rw [Function.mem_support] at hy
      apply subset_tsupport
      rw [Function.mem_support]
      intro h
      apply hy
      change ρ y * ψ y = 0
      rw [h, zero_mul]
    exact (closure_minimal hs (isClosed_tsupport _)).trans hρ_tsupp
  have h_step3 : B.bilin (chartPullback (I := I) α f) ψ' =
      ∫ y, negDensityLaplacianPullback (I := I) g hf α y * ψ' y :=
    bilinear_identity_of_support_in_chartTarget
      (I := I) (M := M) g α hf hf_cs hf_support B hB_c hB_match
      hψ'_smooth hψ'_cs hψ'_support
  have h_LHS_invariant :
      B.bilin (chartPullback (I := I) α f) ψ =
      B.bilin (chartPullback (I := I) α f) ψ' := by
    have h_zero : ∀ y : EuclN,
        B.c y * (chartPullback (I := I) α f) y * ψ y = 0 := by
      intro y; rw [hB_c]; simp
    have h_zero' : ∀ y : EuclN,
        B.c y * (chartPullback (I := I) α f) y * ψ' y = 0 := by
      intro y; rw [hB_c]; simp
    have h_LHS_simplify :
        B.bilin (chartPullback (I := I) α f) ψ =
          ∫ y, B.principalIntegrand (chartPullback (I := I) α f) ψ y := by
      unfold SmoothEllipticBilinearForm.bilin
      rw [MeasureTheory.setIntegral_univ]
      refine MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall (fun y => ?_))
      change B.principalIntegrand (chartPullback (I := I) α f) ψ y +
          B.c y * chartPullback (I := I) α f y * ψ y =
        B.principalIntegrand (chartPullback (I := I) α f) ψ y
      rw [h_zero y]; ring
    have h_LHS_simplify' :
        B.bilin (chartPullback (I := I) α f) ψ' =
          ∫ y, B.principalIntegrand (chartPullback (I := I) α f) ψ' y := by
      unfold SmoothEllipticBilinearForm.bilin
      rw [MeasureTheory.setIntegral_univ]
      refine MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall (fun y => ?_))
      change B.principalIntegrand (chartPullback (I := I) α f) ψ' y +
          B.c y * chartPullback (I := I) α f y * ψ' y =
        B.principalIntegrand (chartPullback (I := I) α f) ψ' y
      rw [h_zero' y]; ring
    rw [h_LHS_simplify, h_LHS_simplify']
    refine MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun y => ?_))
    have hU_cover : tsupport (chartPullback (I := I) α f) ⊆ U :=
      hChartPull_tsupp_in_Kmain.trans hKmain_in_U
    exact principalIntegrand_cutoff_eq B hU_open hU_cover hρ_one_on_U y
  have h_RHS_invariant :
      (∫ y, negDensityLaplacianPullback (I := I) g hf α y * ψ y) =
      ∫ y, negDensityLaplacianPullback (I := I) g hf α y * ψ' y := by
    refine MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun y => ?_))
    change negDensityLaplacianPullback (I := I) g hf α y * ψ y =
      negDensityLaplacianPullback (I := I) g hf α y * ψ' y
    by_cases hy_negDens_zero : negDensityLaplacianPullback (I := I) g hf α y = 0
    · rw [hy_negDens_zero]; ring
    · have hy_in_support : y ∈ Function.support
          (negDensityLaplacianPullback (I := I) g hf α) := hy_negDens_zero
      have hy_in_Kmain : y ∈ K_main :=
        negDensityLaplacianPullback_support_subset (I := I) g α hf hy_in_support
      have hρ_y : ρ y = 1 := hρ_one_on_Kmain y hy_in_Kmain
      change negDensityLaplacianPullback (I := I) g hf α y * ψ y =
          negDensityLaplacianPullback (I := I) g hf α y * (ρ y * ψ y)
      rw [hρ_y]; ring
  rw [h_LHS_invariant, h_step3, h_RHS_invariant]

theorem chart_pulled_smooth_weak_solution
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_cs : HasCompactSupport f)
    (hf_support : tsupport f ⊆ (chartAt H α).source) :
    ∃ B : SmoothEllipticBilinearForm (Module.finrank ℝ E) (Set.univ : Set EuclN),
      (∀ y ∈ euclideanChartImageOfTsupport (I := I) (M := M) α f,
        ∀ i j : Fin (Module.finrank ℝ E),
          B.a y i j = weightedInvGramOnEuclid (I := I) g α i j y) ∧
      B.c = (fun _ : EuclN => (0 : ℝ)) ∧
      B.IsSmoothWeakSolution (chartPullback (I := I) α f)
        (negDensityLaplacianPullback (I := I) g hf α) := by
  classical
  set K : Set EuclN := euclideanChartImageOfTsupport (I := I) (M := M) α f with hK_def
  have hK_compact : IsCompact K :=
    euclideanChartImageOfTsupport_isCompact (I := I) (M := M) α hf_cs hf_support
  have hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    euclideanChartImageOfTsupport_subset_chartTargetEuclid (I := I) (M := M) α hf_support
  obtain ⟨_, _, _, _, _, B, hB_match, hB_c⟩ :=
    exists_chart_metric_bilinearForm (I := I) (M := M) g α hK_compact hK_target
  refine ⟨B, hB_match, hB_c, ?_⟩
  refine chart_pulled_smooth_weak_solution_of_chartIdentity
    (I := I) (M := M) g α hf hf_cs hf_support B ?_
  intro ψ hψ hψ_cs
  exact bilinear_identity_of_smooth (I := I) (M := M) g α hf hf_cs hf_support B hB_c hB_match
    hψ hψ_cs

end ChartBilinearSmooth
end Laplacian
end Analysis
end CalabiYau
