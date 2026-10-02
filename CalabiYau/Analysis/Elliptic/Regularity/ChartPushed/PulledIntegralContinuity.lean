-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/ChartPushed/PulledIntegralContinuity.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.LaplacianDomain.Multiplication.LeibnizSource
public import CalabiYau.Analysis.Elliptic.Regularity.LaplacianDomain.Variational.SmoothApproximation
public import CalabiYau.Analysis.Elliptic.Regularity.LaplacianDomain.Variational.ArbitraryTest
public import CalabiYau.Analysis.Elliptic.Regularity.ChartBilinear.H1ComplFromDom
public import CalabiYau.Analysis.Elliptic.Operator.ChartMeasureEquiv
public import CalabiYau.Geometry.Riemannian.Volume.Chart.MeasureComparison

@[expose] public section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace CalabiYau
namespace Analysis
namespace Laplacian
namespace ChartPulledIntegralContinuity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Laplacian.MetricExtension
  hiding chartTargetEuclid
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open CalabiYau.Laplacian.ChartMeasureEquiv
open CalabiYau.Analysis.Laplacian.LaplacianDomainVariationalLimit
open CalabiYau.Analysis.Laplacian.LaplacianDomainVariationalLimitGeneral
open CalabiYau.Analysis.Laplacian.ChartBilinearH1ComplFromDom
open _root_.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

private def chartSourcePreimage (α : M) (θ : EuclN → ℝ) : Set M :=
  (fun y : EuclN => (extChartAt I α).symm ((toEuclidean (E := E)).symm y)) ''
    (tsupport θ)

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [I.Boundaryless] [T2Space M]
    [CompactSpace M] in
private lemma chartSourcePreimage_isCompact
    (α : M) {θ : EuclN → ℝ} (hθ_cs : HasCompactSupport θ)
    (hθ_support : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    IsCompact (chartSourcePreimage (I := I) (M := M) α θ) := by
  classical
  unfold chartSourcePreimage
  exact (hθ_cs : IsCompact (tsupport θ)).image_of_continuousOn
    ((continuousOn_symm_toEuclideanSymm (I := I) (M := M) α).mono hθ_support)

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [I.Boundaryless] [T2Space M]
    [CompactSpace M] in
private lemma chartSourcePreimage_subset_chartSource
    (α : M) {θ : EuclN → ℝ}
    (hθ_support : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    chartSourcePreimage (I := I) (M := M) α θ ⊆ (chartAt H α).source := by
  classical
  unfold chartSourcePreimage
  intro x hx
  rcases hx with ⟨y, hy_support, hxy⟩
  rw [← hxy]
  exact symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α (hθ_support hy_support)

noncomputable def chartPulledIntegralWeight
    (g : SmoothRiemannianMetric I M) (α : M) (θ : EuclN → ℝ) : M → ℝ := by
  classical
  exact fun x : M =>
    if hx : x ∈ (chartAt H α).source then
      θ ((toEuclidean (E := E)) ((extChartAt I α) x)) / chartDensity g α x
    else 0

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [CompactSpace M] in
lemma chartPulledIntegralWeight_apply_of_mem
    (g : SmoothRiemannianMetric I M) (α : M) (θ : EuclN → ℝ) {x : M}
    (hx : x ∈ (chartAt H α).source) :
    chartPulledIntegralWeight (I := I) (M := M) g α θ x =
      θ ((toEuclidean (E := E)) ((extChartAt I α) x)) / chartDensity g α x := by
  classical
  unfold chartPulledIntegralWeight
  exact dif_pos hx

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [CompactSpace M] in
private lemma chartPulledIntegralWeight_apply_of_notMem
    (g : SmoothRiemannianMetric I M) (α : M) (θ : EuclN → ℝ) {x : M}
    (hx : x ∉ (chartAt H α).source) :
    chartPulledIntegralWeight (I := I) (M := M) g α θ x = 0 := by
  classical
  unfold chartPulledIntegralWeight
  exact dif_neg hx

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [CompactSpace M] in
private lemma chartPulledIntegralWeight_apply_zero_off_preimage
    (g : SmoothRiemannianMetric I M) (α : M) {θ : EuclN → ℝ} {x : M}
    (hx_source : x ∈ (chartAt H α).source)
    (hx_off : x ∉ chartSourcePreimage (I := I) (M := M) α θ) :
    chartPulledIntegralWeight (I := I) (M := M) g α θ x = 0 := by
  classical
  rw [chartPulledIntegralWeight_apply_of_mem (I := I) (M := M) g α θ hx_source]
  have hTx_not_in : (toEuclidean (E := E)) ((extChartAt I α) x) ∉ tsupport θ := by
    intro h_in
    apply hx_off
    refine ⟨(toEuclidean (E := E)) ((extChartAt I α) x), h_in, ?_⟩
    change (extChartAt I α).symm
        ((toEuclidean (E := E)).symm ((toEuclidean (E := E))
          ((extChartAt I α) x))) = x
    have hsymm_inv : (toEuclidean (E := E)).symm ((toEuclidean (E := E))
        ((extChartAt I α) x)) = (extChartAt I α) x :=
      (toEuclidean (E := E)).symm_apply_apply _
    rw [hsymm_inv]
    have hxE : x ∈ (extChartAt I α).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]
      exact hx_source
    exact (extChartAt I α).left_inv hxE
  have hθ_zero : θ ((toEuclidean (E := E)) ((extChartAt I α) x)) = 0 :=
    image_eq_zero_of_notMem_tsupport hTx_not_in
  rw [hθ_zero, zero_div]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [CompactSpace M] in
private lemma chartPulledIntegralWeight_support_subset
    (g : SmoothRiemannianMetric I M) (α : M) (θ : EuclN → ℝ) :
    Function.support (chartPulledIntegralWeight (I := I) (M := M) g α θ) ⊆
      chartSourcePreimage (I := I) (M := M) α θ := by
  classical
  intro x hx
  rw [Function.mem_support] at hx
  by_cases hx_source : x ∈ (chartAt H α).source
  · by_contra hx_not
    have h_zero := chartPulledIntegralWeight_apply_zero_off_preimage
      (I := I) (M := M) g α (θ := θ) hx_source hx_not
    exact hx h_zero
  · have h_zero := chartPulledIntegralWeight_apply_of_notMem
      (I := I) (M := M) g α θ hx_source
    exact (hx h_zero).elim

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M] in
private lemma chartPulledIntegralWeight_tsupport_subset
    (g : SmoothRiemannianMetric I M) (α : M) {θ : EuclN → ℝ}
    (hθ_cs : HasCompactSupport θ)
    (hθ_support : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    tsupport (chartPulledIntegralWeight (I := I) (M := M) g α θ) ⊆
      chartSourcePreimage (I := I) (M := M) α θ := by
  classical
  refine closure_minimal
    (chartPulledIntegralWeight_support_subset (I := I) (M := M) g α θ) ?_
  exact (chartSourcePreimage_isCompact (I := I) (M := M) α hθ_cs hθ_support).isClosed

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M] in
private lemma chartPulledIntegralWeight_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (α : M) {θ : EuclN → ℝ}
    (hθ_cs : HasCompactSupport θ)
    (hθ_support : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    HasCompactSupport (chartPulledIntegralWeight (I := I) (M := M) g α θ) :=
  HasCompactSupport.of_support_subset_isCompact
    (chartSourcePreimage_isCompact (I := I) (M := M) α hθ_cs hθ_support)
    (chartPulledIntegralWeight_support_subset (I := I) (M := M) g α θ)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M] in
private lemma chartPulledIntegralWeight_tsupport_subset_chartSource
    (g : SmoothRiemannianMetric I M) (α : M) {θ : EuclN → ℝ}
    (hθ_cs : HasCompactSupport θ)
    (hθ_support : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    tsupport (chartPulledIntegralWeight (I := I) (M := M) g α θ) ⊆
      (chartAt H α).source :=
  (chartPulledIntegralWeight_tsupport_subset (I := I) (M := M) g α
      hθ_cs hθ_support).trans
    (chartSourcePreimage_subset_chartSource (I := I) (M := M) α hθ_support)

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [I.Boundaryless] [T2Space M]
    [CompactSpace M] in
private lemma chart_map_continuousOn (α : M) :
    ContinuousOn (fun x : M => (toEuclidean (E := E)) ((extChartAt I α) x))
      (chartAt H α).source := by
  have h_ext : ContinuousOn (extChartAt I α) (chartAt H α).source := by
    have h_source : (chartAt H α).source = (extChartAt I α).source :=
      (CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
        (I := I) (M := M) α).symm
    rw [h_source]; exact continuousOn_extChartAt α
  exact (toEuclidean (E := E)).continuous.continuousOn.comp h_ext (Set.mapsTo_univ _ _)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [CompactSpace M] in
private lemma chartPulledIntegralWeight_continuousOn_chartSource
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) :
    ContinuousOn (chartPulledIntegralWeight (I := I) (M := M) g α θ)
      (chartAt H α).source := by
  classical
  have h_eq : EqOn (chartPulledIntegralWeight (I := I) (M := M) g α θ)
      (fun x : M => θ ((toEuclidean (E := E)) ((extChartAt I α) x)) /
        chartDensity g α x)
      (chartAt H α).source := by
    intro x hx
    exact chartPulledIntegralWeight_apply_of_mem (I := I) (M := M) g α θ hx
  refine ContinuousOn.congr ?_ h_eq
  have h_num_cont : ContinuousOn (fun x : M =>
      θ ((toEuclidean (E := E)) ((extChartAt I α) x))) (chartAt H α).source :=
    hθ_cont.continuousOn.comp (chart_map_continuousOn (I := I) (M := M) α)
      (Set.mapsTo_univ _ _)
  have h_dens_cont : ContinuousOn (chartDensity g α) (chartAt H α).source := by
    rw [show (chartAt H α).source =
        (trivializationAt E (TangentSpace I) α).baseSet from
      (CalabiYau.RiemannianVolume.trivializationAt_baseSet_eq_chartAt_source
        (I := I) (M := M) α).symm]
    exact CalabiYau.RiemannianVolume.chartDensity_continuousOn
      (I := I) (M := M) g α
  have h_dens_ne_zero : ∀ x ∈ (chartAt H α).source, chartDensity g α x ≠ 0 := by
    intro x hx
    have hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [CalabiYau.RiemannianVolume.trivializationAt_baseSet_eq_chartAt_source
        (I := I) (M := M)]
      exact hx
    exact (CalabiYau.RiemannianVolume.chartDensity_pos
      (I := I) g α hx_base).ne'
  exact h_num_cont.div h_dens_cont h_dens_ne_zero

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M] in
lemma chartPulledIntegralWeight_continuous
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) (hθ_cs : HasCompactSupport θ)
    (hθ_support : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Continuous (chartPulledIntegralWeight (I := I) (M := M) g α θ) := by
  classical
  refine continuous_iff_continuousAt.mpr fun x => ?_
  by_cases hx_in : x ∈ (chartAt H α).source
  · have h_open : IsOpen ((chartAt H α).source) := (chartAt H α).open_source
    have h_contOn := chartPulledIntegralWeight_continuousOn_chartSource
      (I := I) (M := M) g α (θ := θ) hθ_cont
    exact h_contOn.continuousAt (h_open.mem_nhds hx_in)
  · have h_support_sub : tsupport (chartPulledIntegralWeight (I := I) (M := M) g α θ) ⊆
        (chartAt H α).source :=
      chartPulledIntegralWeight_tsupport_subset_chartSource
        (I := I) (M := M) g α hθ_cs hθ_support
    have hx_not_support : x ∉ tsupport (chartPulledIntegralWeight (I := I) (M := M) g α θ) :=
      fun h_in => hx_in (h_support_sub h_in)
    have h_compl_open : IsOpen
        (tsupport (chartPulledIntegralWeight (I := I) (M := M) g α θ))ᶜ :=
      (isClosed_tsupport _).isOpen_compl
    have h_zero : EqOn (chartPulledIntegralWeight (I := I) (M := M) g α θ)
        (fun _ => (0 : ℝ))
        (tsupport (chartPulledIntegralWeight (I := I) (M := M) g α θ))ᶜ := by
      intro y hy
      have hy_off : y ∉ Function.support
          (chartPulledIntegralWeight (I := I) (M := M) g α θ) := by
        intro h_support
        exact hy (subset_tsupport _ h_support)
      exact Function.notMem_support.mp hy_off
    have h_ev : (chartPulledIntegralWeight (I := I) (M := M) g α θ) =ᶠ[𝓝 x]
        (fun _ : M => (0 : ℝ)) := by
      filter_upwards [h_compl_open.mem_nhds hx_not_support] with y hy
      exact h_zero hy
    refine ContinuousAt.congr ?_ h_ev.symm
    exact continuousAt_const

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma chartPulledIntegralWeight_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) (hθ_cs : HasCompactSupport θ)
    (hθ_support : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (chartPulledIntegralWeight (I := I) (M := M) g α θ) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  have : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  exact (chartPulledIntegralWeight_continuous (I := I) (M := M) g α
      hθ_cont hθ_cs hθ_support).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

noncomputable def chartPulledIntegralWeightLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) (hθ_cs : HasCompactSupport θ)
    (hθ_support : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (chartPulledIntegralWeight_memLp (I := I) (M := M) g α
    hθ_cont hθ_cs hθ_support).toLp _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M] in
private lemma weight_smul_continuous
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) (hθ_cs : HasCompactSupport θ)
    (hθ_support : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α)
    {v : M → ℝ} (hv_cont : Continuous v) :
    Continuous (fun x : M => chartPulledIntegralWeight (I := I) (M := M) g α θ x *
      v x) :=
  (chartPulledIntegralWeight_continuous (I := I) (M := M) g α
    hθ_cont hθ_cs hθ_support).mul hv_cont

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M] in
private lemma weight_smul_tsupport_subset_chartSource
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cs : HasCompactSupport θ)
    (hθ_support : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (v : M → ℝ) :
    tsupport (fun x : M => chartPulledIntegralWeight (I := I) (M := M) g α θ x *
      v x) ⊆ (chartAt H α).source := by
  classical
  have h_support_sub : Function.support
      (fun x : M => chartPulledIntegralWeight (I := I) (M := M) g α θ x *
        v x) ⊆
      Function.support (chartPulledIntegralWeight (I := I) (M := M) g α θ) := by
    intro x hx
    rw [Function.mem_support] at hx
    by_contra h_w
    apply hx
    have h_w_zero : chartPulledIntegralWeight (I := I) (M := M) g α θ x = 0 :=
      Function.notMem_support.mp h_w
    rw [h_w_zero, zero_mul]
  refine (closure_mono h_support_sub).trans ?_
  exact chartPulledIntegralWeight_tsupport_subset_chartSource
    (I := I) (M := M) g α hθ_cs hθ_support

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [CompactSpace M] in
private lemma density_mul_weight_eq_theta
    (g : SmoothRiemannianMetric I M) (α : M) (θ : EuclN → ℝ) {x : M}
    (hx : x ∈ (chartAt H α).source) :
    chartDensity g α x * chartPulledIntegralWeight (I := I) (M := M) g α θ x =
      θ ((toEuclidean (E := E)) ((extChartAt I α) x)) := by
  classical
  rw [chartPulledIntegralWeight_apply_of_mem (I := I) (M := M) g α θ hx]
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [CalabiYau.RiemannianVolume.trivializationAt_baseSet_eq_chartAt_source
      (I := I) (M := M)]
    exact hx
  have h_dens_pos : 0 < chartDensity g α x :=
    CalabiYau.RiemannianVolume.chartDensity_pos (I := I) g α hx_base
  field_simp

omit [NeZero (Module.finrank ℝ E)] in
private lemma integral_weight_smul_eq_chartPulled
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) (hθ_cs : HasCompactSupport θ)
    (hθ_support : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α)
    {v : M → ℝ} (hv_cont : Continuous v) :
    ∫ x, chartPulledIntegralWeight (I := I) (M := M) g α θ x * v x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        v ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) * θ y
        ∂(volume : Measure EuclN) := by
  classical
  set f : M → ℝ := fun x : M =>
    chartPulledIntegralWeight (I := I) (M := M) g α θ x * v x with hf_def
  have hf_cont : Continuous f :=
    weight_smul_continuous (I := I) (M := M) g α hθ_cont hθ_cs hθ_support hv_cont
  have hf_support : tsupport f ⊆ (chartAt H α).source :=
    weight_smul_tsupport_subset_chartSource (I := I) (M := M) g α hθ_cs hθ_support v
  have h_main := integral_riemannianVolumeMeasure_eq_euclidean_chartTarget
    (I := I) (M := M) g α (f := f) hf_cont hf_support
  rw [h_main]
  rw [CalabiYau.RiemannianVolume.map_toEuclidean_modelHaar_eq_volume]
  refine MeasureTheory.setIntegral_congr_fun
    (Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α).measurableSet ?_
  intro y hy
  have hy_source : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
      (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  have h_density_eq : densityOnEuclid (I := I) g α y =
      chartDensity g α ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := rfl
  have hy_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
    toEuclidean_symm_mem_target (I := I) hy
  have h_inv1 : (extChartAt I α) ((extChartAt I α).symm
      ((toEuclidean (E := E)).symm y)) = (toEuclidean (E := E)).symm y :=
    (extChartAt I α).right_inv hy_target
  have h_inv2 : (toEuclidean (E := E)) ((toEuclidean (E := E)).symm y) = y :=
    (toEuclidean (E := E)).apply_symm_apply y
  have h_pw := density_mul_weight_eq_theta (I := I) (M := M) g α θ hy_source
  have h_pw' : chartDensity g α ((extChartAt I α).symm
      ((toEuclidean (E := E)).symm y)) *
      chartPulledIntegralWeight (I := I) (M := M) g α θ
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) = θ y := by
    rw [h_pw]
    rw [h_inv1, h_inv2]
  change densityOnEuclid (I := I) g α y *
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
    v ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) * θ y
  rw [h_density_eq]
  rw [hf_def]
  rw [show chartDensity g α ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
      (chartPulledIntegralWeight (I := I) (M := M) g α θ
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
        v ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) =
      (chartDensity g α ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
        chartPulledIntegralWeight (I := I) (M := M) g α θ
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
        v ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) from by ring]
  rw [h_pw']
  ring

noncomputable def chartPulledIntegralCLM
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) (hθ_cs : HasCompactSupport θ)
    (hθ_support : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ] ℝ :=
  (innerSL ℝ : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ] ℝ)
    (chartPulledIntegralWeightLp (I := I) (M := M) g α hθ_cont hθ_cs hθ_support)

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPulledIntegralCLM_smoothToLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) (hθ_cs : HasCompactSupport θ)
    (hθ_support : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (v : SmoothScalar g) :
    chartPulledIntegralCLM (I := I) (M := M) g α hθ_cont hθ_cs hθ_support
        (smoothToLp (I := I) (M := M) g v) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        v.toFun ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          θ y ∂(volume : Measure EuclN) := by
  classical
  unfold chartPulledIntegralCLM
  rw [innerSL_apply_apply]
  rw [L2.inner_def
    (chartPulledIntegralWeightLp (I := I) (M := M) g α hθ_cont hθ_cs hθ_support)
    (smoothToLp (I := I) (M := M) g v)]
  have hae_w : (chartPulledIntegralWeightLp (I := I) (M := M) g α
      hθ_cont hθ_cs hθ_support : Lp ℝ 2 _) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      chartPulledIntegralWeight (I := I) (M := M) g α θ :=
    MemLp.coeFn_toLp (chartPulledIntegralWeight_memLp
      (I := I) (M := M) g α hθ_cont hθ_cs hθ_support)
  have hae_v : (smoothToLp (I := I) (M := M) g v : Lp ℝ 2 _) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g] v.toFun :=
    MemLp.coeFn_toLp v.memLp_two
  have h_int_eq : ∫ a, @inner ℝ _ _
        ((chartPulledIntegralWeightLp (I := I) (M := M) g α
          hθ_cont hθ_cs hθ_support : Lp ℝ 2 _) a)
        ((smoothToLp (I := I) (M := M) g v : Lp ℝ 2 _) a)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ a, chartPulledIntegralWeight (I := I) (M := M) g α θ a * v.toFun a
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hae_w, hae_v] with a hwa hva
    rw [hwa, hva]
    rw [show @inner ℝ _ _ (chartPulledIntegralWeight (I := I) (M := M) g α θ a)
          (v.toFun a) =
        v.toFun a * chartPulledIntegralWeight (I := I) (M := M) g α θ a from
      RCLike.inner_apply _ _]
    ring
  rw [h_int_eq]
  exact integral_weight_smul_eq_chartPulled (I := I) (M := M) g α
    hθ_cont hθ_cs hθ_support v.smooth.continuous

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem chartPulledIntegralCLM_continuous
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) (hθ_cs : HasCompactSupport θ)
    (hθ_support : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Continuous (chartPulledIntegralCLM (I := I) (M := M) g α
      hθ_cont hθ_cs hθ_support) :=
  (chartPulledIntegralCLM (I := I) (M := M) g α hθ_cont hθ_cs hθ_support).continuous

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem chartPulledIntegralCLM_tendsto
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) (hθ_cs : HasCompactSupport θ)
    (hθ_support : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α)
    {F : ℕ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    {F_lim : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (h_tendsto : Tendsto F atTop (𝓝 F_lim)) :
    Tendsto (fun n => chartPulledIntegralCLM (I := I) (M := M) g α
      hθ_cont hθ_cs hθ_support (F n)) atTop
      (𝓝 (chartPulledIntegralCLM (I := I) (M := M) g α
        hθ_cont hθ_cs hθ_support F_lim)) :=
  ((chartPulledIntegralCLM_continuous (I := I) (M := M) g α
    hθ_cont hθ_cs hθ_support).tendsto _).comp h_tendsto

omit [NeZero (Module.finrank ℝ E)] in
lemma smoothToLp_pouScalar_oneSubLap_eq_fHLeibniz
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    smoothToLp (I := I) (M := M) g
        (pouScalar (I := I) (M := M) α v).oneSubLapClassical =
      leibnizCompensatedSource (I := I) (M := M) g α
        (smoothToH1Compl (I := I) (M := M) g v)
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) := by
  classical
  apply MeasureTheory.Lp.ext
  have h_lhs_aeeq : (smoothToLp (I := I) (M := M) g
      (pouScalar (I := I) (M := M) α v).oneSubLapClassical : Lp ℝ 2 _) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (pouScalar (I := I) (M := M) α v).oneSubLapClassical.toFun :=
    MemLp.coeFn_toLp (pouScalar (I := I) (M := M) α v).oneSubLapClassical.memLp_two
  have h_rhs_aeeq : (pouScalar (I := I) (M := M) α v).oneSubLapClassical.toFun =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      ((leibnizCompensatedSource (I := I) (M := M) g α
          (smoothToH1Compl (I := I) (M := M) g v)
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)
          : Lp ℝ 2 _) : M → ℝ) :=
    pouScalar_oneSubLap_aeEq_fHLeibniz_smooth (I := I) (M := M) g α v
  exact h_lhs_aeeq.trans h_rhs_aeeq

end ChartPulledIntegralContinuity
end Laplacian
end Analysis
end CalabiYau

end
