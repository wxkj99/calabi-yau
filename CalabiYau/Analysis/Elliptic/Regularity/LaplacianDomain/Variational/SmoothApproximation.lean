-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/LaplacianDomain/Variational/SmoothApproximation.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.ChartBilinear.H1Compl
public import CalabiYau.Analysis.Elliptic.Regularity.ChartBilinear.Smooth
public import CalabiYau.Analysis.Elliptic.Regularity.ChartBilinear.H1ComplFromDom
public import CalabiYau.Analysis.Elliptic.Regularity.H1Compl.GradientH1LipschitzBound
public import CalabiYau.Analysis.Elliptic.Regularity.H1Compl.ChartLp
public import CalabiYau.Analysis.Elliptic.Regularity.H1Compl.WeakPartialLimit
public import CalabiYau.Analysis.Elliptic.Regularity.ChartPushed.WeakPartialOnVolume
public import CalabiYau.Analysis.Elliptic.Regularity.LaplacianDomain.Multiplication.LeibnizSource
public import CalabiYau.Analysis.Elliptic.Regularity.GradInner.CLM.Defs
public import CalabiYau.Analysis.Elliptic.Regularity.SmoothScalar.MulLp
public import CalabiYau.Analysis.Elliptic.Operator.SmoothResolvent
public import CalabiYau.Analysis.Elliptic.Operator.VariationalLaplacian
public import CalabiYau.Geometry.Riemannian.Operator.Gradient.Basic
public import CalabiYau.Geometry.Riemannian.Operator.Laplacian.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section
open CalabiYau.Riemannian

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace CalabiYau
namespace Analysis
namespace Laplacian
namespace LaplacianDomainVariationalLimit

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Laplacian.MetricExtension
  hiding chartTargetEuclid
open CalabiYau.Analysis.Laplacian.ChartLocalLaplacian
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.ChartBilinearH1ComplFromDom
open CalabiYau.Analysis.Laplacian.ChartBilinearSmooth
open CalabiYau.Analysis.Laplacian.H1ComplGradientChartBridge
open CalabiYau.Analysis.Laplacian.H1ComplGradientH1LipschitzBound
open CalabiYau.Analysis.Laplacian.H1ComplToLpChartBridge
open CalabiYau.Analysis.Laplacian.H1ComplWeakPartialLimit
open CalabiYau.Analysis.Laplacian.ChartPushedWeakPartialOnVolume
open Sobolev.Chart
open Sobolev.NirenbergEuclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [T2Space M] [CompactSpace M] in
noncomputable def pouScalar
    {g : SmoothRiemannianMetric I M} (α : M) (v : SmoothScalar g) :
    SmoothScalar g where
  toFun := fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * v.toFun x
  smooth :=
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff).mul v.smooth

section

variable [T2Space M] [CompactSpace M]

private lemma pouScalar_toFun
    {g : SmoothRiemannianMetric I M} (α : M) (v : SmoothScalar g) :
    (pouScalar (I := I) (M := M) α v).toFun =
      fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * v.toFun x := rfl

private lemma pouScalar_hasCompactSupport
    {g : SmoothRiemannianMetric I M} (α : M) (v : SmoothScalar g) :
    HasCompactSupport (pouScalar (I := I) (M := M) α v).toFun :=
  HasCompactSupport.of_compactSpace _

private lemma pouScalar_tsupport_subset_chartSource
    {g : SmoothRiemannianMetric I M} (α : M) (v : SmoothScalar g) :
    tsupport (pouScalar (I := I) (M := M) α v).toFun ⊆ (chartAt H α).source := by
  rw [pouScalar_toFun]
  classical
  have h_support_sub : Function.support
      (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * v.toFun x) ⊆
        Function.support fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x := by
    intro x hx
    simp only [Function.mem_support] at hx
    by_contra hρ_zero
    apply hx
    simp only [Function.mem_support, not_not] at hρ_zero
    rw [hρ_zero]; ring
  have h_tsupp_sub :
      tsupport (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
          v.toFun x) ⊆
        tsupport fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x :=
    closure_mono h_support_sub
  exact h_tsupp_sub.trans
    ((CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M) α)

private lemma chartPullback_pouScalar_eq_chartPushed
    {g : SmoothRiemannianMetric I M} (α : M) (v : SmoothScalar g) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPullback (I := I) α (pouScalar (I := I) (M := M) α v).toFun y =
      chartPushed (I := I) (M := M) (chartAtlasPOU I M) α v.toFun y := by
  rw [chartPullback_apply_of_mem (I := I) α _ hy]
  rfl

end

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Laplacian.MetricExtension
  hiding chartTargetEuclid
open CalabiYau.Analysis.Laplacian.ChartLocalLaplacian
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.ChartBilinearH1ComplFromDom
open CalabiYau.Analysis.Laplacian.ChartBilinearSmooth
open CalabiYau.Analysis.Laplacian.H1ComplGradientChartBridge
open CalabiYau.Analysis.Laplacian.H1ComplGradientH1LipschitzBound
open CalabiYau.Analysis.Laplacian.H1ComplToLpChartBridge
open CalabiYau.Analysis.Laplacian.H1ComplWeakPartialLimit
open CalabiYau.Analysis.Laplacian.ChartPushedWeakPartialOnVolume
open Sobolev.Chart
open Sobolev.NirenbergEuclidean
attribute [local instance] instMeasurableSpace_calabiYau instBorelSpace_calabiYau instMeasurableSpace_calabiYau_1 instBorelSpace_calabiYau_1
local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [CompactSpace M] in
private theorem smooth_principal_identity
    {g : SmoothRiemannianMetric I M} (α : M) (v : SmoothScalar g)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (_hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        weightedInvGramOnEuclid (I := I) g α i j y *
          chartPushedPartial (I := I) (M := M) g α i v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN) =
    -∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y *
        (ΔG (I := I) g ⟨(pouScalar (I := I) (M := M) α v).toFun,
          (pouScalar (I := I) (M := M) α v).smooth⟩)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
        ψ y
      ∂(volume : Measure EuclN) := by
  classical
  set f : M → ℝ := (pouScalar (I := I) (M := M) α v).toFun with hf_def
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := (pouScalar (I := I) (M := M) α v).smooth
  have hf_cs : HasCompactSupport f :=
    pouScalar_hasCompactSupport (I := I) (M := M) α v
  have hf_support : tsupport f ⊆ (chartAt H α).source :=
    pouScalar_tsupport_subset_chartSource (I := I) (M := M) α v
  obtain ⟨B, hB_match, hB_c, hB_solv⟩ :=
    chart_pulled_smooth_weak_solution (I := I) (M := M) g α hf_smooth hf_cs hf_support
  obtain ⟨_hB_cd, hB_solv⟩ := hB_solv
  have h_bilin : B.bilin (chartPullback (I := I) α f) ψ =
      ∫ y in (Set.univ : Set EuclN),
        negDensityLaplacianPullback (I := I) g hf_smooth α y * ψ y :=
    hB_solv ψ hψ hψ_cs (Set.subset_univ _)
  rw [MeasureTheory.setIntegral_univ] at h_bilin
  set K_main : Set EuclN :=
    euclideanChartImageOfTsupport (I := I) (M := M) α f with hK_main_def
  have hK_main_subset_target :
      K_main ⊆ chartTargetEuclid (I := I) (M := M) α :=
    euclideanChartImageOfTsupport_subset_chartTargetEuclid (I := I) (M := M) α hf_support
  have h_bilin_univ : B.bilin (chartPullback (I := I) α f) ψ =
      ∫ y, B.principalIntegrand (chartPullback (I := I) α f) ψ y := by
    unfold SmoothEllipticBilinearForm.bilin
    rw [MeasureTheory.setIntegral_univ]
    refine MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun y => ?_))
    change B.principalIntegrand (chartPullback (I := I) α f) ψ y +
        B.c y * chartPullback (I := I) α f y * ψ y =
      B.principalIntegrand (chartPullback (I := I) α f) ψ y
    rw [hB_c]; simp
  rw [h_bilin_univ] at h_bilin
  have h_chartPull_tsupp_in_K_main :
      tsupport (chartPullback (I := I) α f) ⊆ K_main :=
    chartPullback_tsupport_subset (I := I) α hf_cs hf_support
  have h_principal_zero_off_K_main : ∀ y, y ∉ K_main →
      B.principalIntegrand (chartPullback (I := I) α f) ψ y = 0 := by
    intro y hy_not_K
    have hy_not_support : y ∉ tsupport (chartPullback (I := I) α f) := fun h =>
      hy_not_K (h_chartPull_tsupp_in_K_main h)
    have h_compl_open : IsOpen (tsupport (chartPullback (I := I) α f))ᶜ :=
      (isClosed_tsupport _).isOpen_compl
    have h_ev : chartPullback (I := I) α f =ᶠ[𝓝 y]
        (fun _ : EuclN => (0 : ℝ)) := by
      filter_upwards [h_compl_open.mem_nhds hy_not_support] with z hz
      by_contra hne
      exact hz (subset_tsupport _ hne)
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
  have h_negDens_zero_off : ∀ y, y ∉ chartTargetEuclid (I := I) (M := M) α →
      negDensityLaplacianPullback (I := I) g hf_smooth α y * ψ y = 0 := by
    intro y hy
    rw [negDensityLaplacianPullback_apply_of_notMem (I := I) g hf_smooth α hy]
    ring
  have h_chartTarget_meas :
      MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  have h_LHS_set : ∫ y, B.principalIntegrand (chartPullback (I := I) α f) ψ y =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        B.principalIntegrand (chartPullback (I := I) α f) ψ y := by
    rw [← MeasureTheory.integral_indicator h_chartTarget_meas]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro y
    by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      change B.principalIntegrand (chartPullback (I := I) α f) ψ y = 0
      exact h_principal_zero_off_K_main y
        (fun h => hy (hK_main_subset_target h))
  have h_RHS_set :
      ∫ y, negDensityLaplacianPullback (I := I) g hf_smooth α y * ψ y =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        negDensityLaplacianPullback (I := I) g hf_smooth α y * ψ y := by
    rw [← MeasureTheory.integral_indicator h_chartTarget_meas]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro y
    by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      change negDensityLaplacianPullback (I := I) g hf_smooth α y * ψ y = 0
      exact h_negDens_zero_off y hy
  have h_principalIntegrand_eq :
      ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
        B.principalIntegrand (chartPullback (I := I) α f) ψ y =
        ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            chartPushedPartial (I := I) (M := M) g α i v y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1) := by
    intro y hy
    by_cases hy_K : y ∈ K_main
    · unfold SmoothEllipticBilinearForm.principalIntegrand
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [hB_match y hy_K i j]
      have hOpen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
        Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α
      have h_ev :
          chartPullback (I := I) α f =ᶠ[𝓝 y]
            (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α v.toFun) := by
        filter_upwards [hOpen.mem_nhds hy] with z hz
        exact chartPullback_pouScalar_eq_chartPushed (I := I) (M := M) α v hz
      have h_fderiv :
          fderiv ℝ (chartPullback (I := I) α f) y =
            fderiv ℝ (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α v.toFun) y :=
        Filter.EventuallyEq.fderiv_eq h_ev
      rw [h_fderiv]
      change weightedInvGramOnEuclid g α i j y *
          (fderiv ℝ _ y) (EuclideanSpace.single i 1) *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1) =
        weightedInvGramOnEuclid g α i j y *
          chartPushedPartial g α i v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
      rw [chartPushedPartial_def]
    · have h_principal_zero :
          B.principalIntegrand (chartPullback (I := I) α f) ψ y = 0 :=
        h_principal_zero_off_K_main y hy_K
      rw [h_principal_zero]
      have hy_not_support : y ∉ tsupport (chartPullback (I := I) α f) := fun h =>
        hy_K (h_chartPull_tsupp_in_K_main h)
      have h_compl_open : IsOpen (tsupport (chartPullback (I := I) α f))ᶜ :=
        (isClosed_tsupport _).isOpen_compl
      have h_ev : chartPullback (I := I) α f =ᶠ[𝓝 y]
          (fun _ : EuclN => (0 : ℝ)) := by
        filter_upwards [h_compl_open.mem_nhds hy_not_support] with z hz
        by_contra hne
        exact hz (subset_tsupport _ hne)
      have hOpen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
        Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α
      have h_ev2 :
          chartPushed (I := I) (M := M) (chartAtlasPOU I M) α v.toFun =ᶠ[𝓝 y]
            (fun _ : EuclN => (0 : ℝ)) := by
        filter_upwards [hOpen.mem_nhds hy, h_compl_open.mem_nhds hy_not_support] with z hz_T hz_support
        have h_pull_zero : chartPullback (I := I) α f z = 0 := by
          by_contra hne
          exact hz_support (subset_tsupport _ hne)
        have h_eq := chartPullback_pouScalar_eq_chartPushed (I := I) (M := M) α v hz_T
        rw [← h_eq]; exact h_pull_zero
      have h_fderiv_zero :
          fderiv ℝ (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α v.toFun) y = 0 := by
        rw [Filter.EventuallyEq.fderiv_eq h_ev2]
        exact fderiv_const_apply _
      refine (Finset.sum_eq_zero ?_).symm
      intro i _
      refine Finset.sum_eq_zero ?_
      intro j _
      change weightedInvGramOnEuclid g α i j y *
          chartPushedPartial g α i v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1) = 0
      rw [chartPushedPartial_def]
      rw [h_fderiv_zero]
      change weightedInvGramOnEuclid g α i j y *
          (0 : EuclN →L[ℝ] ℝ) (EuclideanSpace.single i 1) *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1) = 0
      rw [zero_apply]; ring
  have h_negDens_eq :
      ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
        negDensityLaplacianPullback (I := I) g hf_smooth α y * ψ y =
        - (densityOnEuclid (I := I) g α y *
          (ΔG (I := I) g ⟨_, hf_smooth⟩)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) * ψ y) := by
    intro y hy
    rw [negDensityLaplacianPullback_apply_of_mem (I := I) g hf_smooth α hy]
    ring
  have h_LHS_final :
      ∫ y, B.principalIntegrand (chartPullback (I := I) α f) ψ y =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            chartPushedPartial (I := I) (M := M) g α i v y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1) := by
    rw [h_LHS_set]
    apply MeasureTheory.setIntegral_congr_fun h_chartTarget_meas
    exact h_principalIntegrand_eq
  have h_RHS_final :
      ∫ y, negDensityLaplacianPullback (I := I) g hf_smooth α y * ψ y =
      -∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (ΔG (I := I) g ⟨_, hf_smooth⟩)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          ψ y := by
    rw [h_RHS_set]
    rw [show (∫ y in chartTargetEuclid (I := I) (M := M) α,
              negDensityLaplacianPullback (I := I) g hf_smooth α y * ψ y) =
            ∫ y in chartTargetEuclid (I := I) (M := M) α,
              -(densityOnEuclid (I := I) g α y *
                (ΔG (I := I) g ⟨_, hf_smooth⟩)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
                ψ y) from ?_]
    · rw [MeasureTheory.integral_neg]
    · apply MeasureTheory.setIntegral_congr_fun h_chartTarget_meas
      intro y hy
      exact h_negDens_eq y hy
  rw [← h_LHS_final, h_bilin, h_RHS_final]

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Laplacian.MetricExtension
  hiding chartTargetEuclid
open CalabiYau.Analysis.Laplacian.ChartLocalLaplacian
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.ChartBilinearH1ComplFromDom
open CalabiYau.Analysis.Laplacian.ChartBilinearSmooth
open CalabiYau.Analysis.Laplacian.H1ComplGradientChartBridge
open CalabiYau.Analysis.Laplacian.H1ComplGradientH1LipschitzBound
open CalabiYau.Analysis.Laplacian.H1ComplToLpChartBridge
open CalabiYau.Analysis.Laplacian.H1ComplWeakPartialLimit
open CalabiYau.Analysis.Laplacian.ChartPushedWeakPartialOnVolume
open Sobolev.Chart
open Sobolev.NirenbergEuclidean
attribute [local instance] instMeasurableSpace_calabiYau instBorelSpace_calabiYau instMeasurableSpace_calabiYau_1 instBorelSpace_calabiYau_1
local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] in
private lemma integrable_density_pull_mul_test
    {g : SmoothRiemannianMetric I M} (α : M)
    {h : M → ℝ} (hh_cont : Continuous h)
    {ψ : EuclN → ℝ} (hψ_cont : Continuous ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    IntegrableOn (fun y : EuclN =>
      densityOnEuclid (I := I) g α y *
        h ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) * ψ y)
      (chartTargetEuclid (I := I) (M := M) α) volume := by
  classical
  have h_density_cont : ContinuousOn (densityOnEuclid (I := I) g α)
      (chartTargetEuclid (I := I) (M := M) α) :=
    (densityOnEuclid_contDiffOn (I := I) g α).continuousOn
  have h_symm_cont : ContinuousOn (fun y : EuclN =>
      (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
      (chartTargetEuclid (I := I) (M := M) α) :=
    (contMDiffOn_chart_symm (I := I) (M := M) α).continuousOn
  have h_pull_h_cont : ContinuousOn (fun y : EuclN =>
      h ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
      (chartTargetEuclid (I := I) (M := M) α) :=
    hh_cont.continuousOn.comp h_symm_cont (Set.mapsTo_univ _ _)
  have hcontOn : ContinuousOn (fun y : EuclN =>
      densityOnEuclid (I := I) g α y *
        h ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) * ψ y)
      (chartTargetEuclid (I := I) (M := M) α) := by
    refine (h_density_cont.mul h_pull_h_cont).mul ?_
    exact hψ_cont.continuousOn
  have h_chartTarget_meas :
      MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  have h_global_cont : Continuous (fun y : EuclN =>
      (chartTargetEuclid (I := I) (M := M) α).indicator
        (fun z => densityOnEuclid (I := I) g α z *
          h ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) * ψ z) y) := by
    refine continuous_iff_continuousAt.mpr fun y => ?_
    by_cases hy : y ∈ tsupport ψ
    · have hyT : y ∈ chartTargetEuclid (I := I) (M := M) α := hψ_support hy
      have hOpen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
        Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α
      have h_ev_indicator :
          (fun y => (chartTargetEuclid (I := I) (M := M) α).indicator
              (fun z => densityOnEuclid (I := I) g α z *
                h ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) * ψ z) y) =ᶠ[𝓝 y]
            (fun z => densityOnEuclid (I := I) g α z *
              h ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) * ψ z) := by
        filter_upwards [hOpen.mem_nhds hyT] with z hz
        exact Set.indicator_of_mem hz _
      refine ContinuousAt.congr ?_ h_ev_indicator.symm
      exact hcontOn.continuousAt (hOpen.mem_nhds hyT)
    · have hOpen_compl : IsOpen (tsupport ψ)ᶜ := (isClosed_tsupport _).isOpen_compl
      have h_ev_indicator :
          (fun y => (chartTargetEuclid (I := I) (M := M) α).indicator
              (fun z => densityOnEuclid (I := I) g α z *
                h ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) * ψ z) y) =ᶠ[𝓝 y]
            (fun _ => (0 : ℝ)) := by
        filter_upwards [hOpen_compl.mem_nhds hy] with z hz
        have hψ_z : ψ z = 0 := image_eq_zero_of_notMem_tsupport hz
        by_cases hzT : z ∈ chartTargetEuclid (I := I) (M := M) α
        · rw [Set.indicator_of_mem hzT]
          change densityOnEuclid (I := I) g α z *
              h ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) * ψ z = 0
          rw [hψ_z]; ring
        · rw [Set.indicator_of_notMem hzT]
      refine ContinuousAt.congr ?_ h_ev_indicator.symm
      exact continuousAt_const
  have h_support_in_tsupp : Function.support
      (fun y : EuclN =>
        (chartTargetEuclid (I := I) (M := M) α).indicator
          (fun z => densityOnEuclid (I := I) g α z *
            h ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) * ψ z) y) ⊆
        tsupport ψ := by
    intro y hy
    rw [Function.mem_support] at hy
    by_contra hyψ
    apply hy
    have hψ_y : ψ y = 0 := image_eq_zero_of_notMem_tsupport hyψ
    by_cases hyT : y ∈ chartTargetEuclid (I := I) (M := M) α
    · rw [Set.indicator_of_mem hyT]
      change densityOnEuclid (I := I) g α y *
          h ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) * ψ y = 0
      rw [hψ_y]; ring
    · rw [Set.indicator_of_notMem hyT]
  have h_int_global : Integrable
      (fun y : EuclN =>
        (chartTargetEuclid (I := I) (M := M) α).indicator
          (fun z => densityOnEuclid (I := I) g α z *
            h ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) * ψ z) y)
      volume := by
    apply h_global_cont.integrable_of_hasCompactSupport
    refine HasCompactSupport.intro hψ_cs ?_
    intro y hy
    by_contra hne
    have hy_support : y ∈ Function.support _ := hne
    exact hy (h_support_in_tsupp hy_support)
  rw [MeasureTheory.IntegrableOn]
  rw [show Integrable (fun y : EuclN => densityOnEuclid (I := I) g α y *
        h ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) * ψ y)
        (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) =
      Integrable (fun y : EuclN =>
        (chartTargetEuclid (I := I) (M := M) α).indicator
          (fun z => densityOnEuclid (I := I) g α z *
            h ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) * ψ z) y)
        volume from ?_]
  · exact h_int_global
  · rw [MeasureTheory.integrable_indicator_iff h_chartTarget_meas]
    rfl

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Laplacian.MetricExtension
  hiding chartTargetEuclid
open CalabiYau.Analysis.Laplacian.ChartLocalLaplacian
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.ChartBilinearH1ComplFromDom
open CalabiYau.Analysis.Laplacian.ChartBilinearSmooth
open CalabiYau.Analysis.Laplacian.H1ComplGradientChartBridge
open CalabiYau.Analysis.Laplacian.H1ComplGradientH1LipschitzBound
open CalabiYau.Analysis.Laplacian.H1ComplToLpChartBridge
open CalabiYau.Analysis.Laplacian.H1ComplWeakPartialLimit
open CalabiYau.Analysis.Laplacian.ChartPushedWeakPartialOnVolume
open Sobolev.Chart
open Sobolev.NirenbergEuclidean
attribute [local instance] instMeasurableSpace_calabiYau instBorelSpace_calabiYau instMeasurableSpace_calabiYau_1 instBorelSpace_calabiYau_1
local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

section

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

private theorem smooth_variational_identity
    {g : SmoothRiemannianMetric I M} (α : M) (v : SmoothScalar g)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        weightedInvGramOnEuclid (I := I) g α i j y *
          chartPushedPartial (I := I) (M := M) g α i v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y *
        chartPushed (I := I) (M := M) (chartAtlasPOU I M) α v.toFun y * ψ y
      ∂(volume : Measure EuclN)) =
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y *
        ((pouScalar (I := I) (M := M) α v).oneSubLapClassical.toFun)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
        ψ y
      ∂(volume : Measure EuclN) := by
  classical
  have h_principal :=
    smooth_principal_identity (I := I) (M := M) α v hψ hψ_cs hψ_support
  set f_pou : M → ℝ := (pouScalar (I := I) (M := M) α v).toFun with hf_pou_def
  set H : M → ℝ := f_pou -
      ΔG (I := I) g ⟨(pouScalar (I := I) (M := M) α v).toFun,
        (pouScalar (I := I) (M := M) α v).smooth⟩ with hH_def
  have h_chartTarget_meas :
      MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  have h_u_mass_eq :
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          chartPushed (I := I) (M := M) (chartAtlasPOU I M) α v.toFun y * ψ y) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          f_pou ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) * ψ y :=
    rfl
  rw [h_u_mass_eq, h_principal]
  have h_density_cont : ContinuousOn (densityOnEuclid (I := I) g α)
      (chartTargetEuclid (I := I) (M := M) α) :=
    (densityOnEuclid_contDiffOn (I := I) g α).continuousOn
  have hψ_cont : Continuous ψ := hψ.continuous
  have h_symm_cont : ContinuousOn (fun y : EuclN =>
      (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
      (chartTargetEuclid (I := I) (M := M) α) :=
    (contMDiffOn_chart_symm (I := I) (M := M) α).continuousOn
  have hf_pou_cont : Continuous f_pou :=
    (pouScalar (I := I) (M := M) α v).smooth.continuous
  have h_pull_f_cont :
      ContinuousOn (fun y : EuclN =>
        f_pou ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (chartTargetEuclid (I := I) (M := M) α) :=
    hf_pou_cont.continuousOn.comp h_symm_cont (Set.mapsTo_univ _ _)
  have h_Δ_cont : Continuous
      (ΔG (I := I) g ⟨(pouScalar (I := I) (M := M) α v).toFun,
        (pouScalar (I := I) (M := M) α v).smooth⟩) :=
    (Δ_g_contMDiff (I := I) g ⟨(pouScalar (I := I) (M := M) α v).toFun,
      (pouScalar (I := I) (M := M) α v).smooth⟩).continuous
  have h_pull_Δ_cont :
      ContinuousOn (fun y : EuclN =>
        (ΔG (I := I) g ⟨(pouScalar (I := I) (M := M) α v).toFun,
          (pouScalar (I := I) (M := M) α v).smooth⟩)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (chartTargetEuclid (I := I) (M := M) α) :=
    h_Δ_cont.continuousOn.comp h_symm_cont (Set.mapsTo_univ _ _)
  have hint_f : IntegrableOn (fun y : EuclN =>
      densityOnEuclid (I := I) g α y *
        f_pou ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) * ψ y)
      (chartTargetEuclid (I := I) (M := M) α) volume :=
    integrable_density_pull_mul_test (I := I) (M := M) α
      hf_pou_cont hψ_cont hψ_cs hψ_support
  have hint_Δ : IntegrableOn (fun y : EuclN =>
      densityOnEuclid (I := I) g α y *
        (ΔG (I := I) g ⟨(pouScalar (I := I) (M := M) α v).toFun,
          (pouScalar (I := I) (M := M) α v).smooth⟩)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) * ψ y)
      (chartTargetEuclid (I := I) (M := M) α) volume :=
    integrable_density_pull_mul_test (I := I) (M := M) α
      h_Δ_cont hψ_cont hψ_cs hψ_support
  have h_RHS_split : ∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y *
        (pouScalar (I := I) (M := M) α v).oneSubLapClassical.toFun
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
        ψ y =
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          f_pou ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) * ψ y) -
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (ΔG (I := I) g ⟨(pouScalar (I := I) (M := M) α v).toFun,
            (pouScalar (I := I) (M := M) α v).smooth⟩)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) * ψ y := by
    rw [← MeasureTheory.integral_sub hint_f hint_Δ]
    apply MeasureTheory.setIntegral_congr_fun h_chartTarget_meas
    intro y _hy
    change densityOnEuclid (I := I) g α y *
        (f_pou ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) -
          (ΔG (I := I) g ⟨(pouScalar (I := I) (M := M) α v).toFun,
            (pouScalar (I := I) (M := M) α v).smooth⟩)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) * ψ y =
      densityOnEuclid (I := I) g α y *
        f_pou ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) * ψ y -
      densityOnEuclid (I := I) g α y *
        (ΔG (I := I) g ⟨(pouScalar (I := I) (M := M) α v).toFun,
          (pouScalar (I := I) (M := M) α v).smooth⟩)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) * ψ y
    ring
  rw [h_RHS_split]
  ring

theorem laplacianDomain_variational_identity_smooth_case
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        weightedInvGramOnEuclid (I := I) g α i j y *
          chartPushedPartial (I := I) (M := M) g α i v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y *
        chartPushed (I := I) (M := M) (chartAtlasPOU I M) α v.toFun y * ψ y
      ∂(volume : Measure EuclN)) =
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y *
        ((pouScalar (I := I) (M := M) α v).oneSubLapClassical.toFun)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
        ψ y
      ∂(volume : Measure EuclN) :=
  smooth_variational_identity (I := I) (M := M) α v hψ hψ_cs hψ_support

end

end

end LaplacianDomainVariationalLimit
end Laplacian
end Analysis
end CalabiYau

end
