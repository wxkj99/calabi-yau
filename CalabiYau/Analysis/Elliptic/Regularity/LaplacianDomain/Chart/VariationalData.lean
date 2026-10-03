-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/LaplacianDomain/Chart/VariationalData.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.ChartBilinear.H1Compl
public import CalabiYau.Analysis.Elliptic.Regularity.ChartBilinear.H1ComplFromDom
public import CalabiYau.Analysis.Elliptic.Regularity.ChartBilinear.Smooth
public import CalabiYau.Analysis.Elliptic.Regularity.ChartPushed.WeakPartialOnVolume
public import CalabiYau.Analysis.Elliptic.Regularity.H1Compl.GradientH1LipschitzBound
public import CalabiYau.Analysis.Elliptic.Regularity.H1Compl.ChartLp
public import CalabiYau.Analysis.Elliptic.Regularity.H1Compl.WeakPartialLimit
public import CalabiYau.Analysis.Elliptic.Regularity.LaplacianDomain.Variational.IntegralIdentity
public import CalabiYau.Analysis.Elliptic.Operator.VariationalLaplacian
public import CalabiYau.Analysis.Sobolev.Manifold.RiemannianRellich
public import CalabiYau.Geometry.Riemannian.Operator.Gradient.Basic
public import CalabiYau.Geometry.Riemannian.Operator.Laplacian.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace CalabiYau
namespace Analysis
namespace Laplacian
namespace LaplacianDomainChartData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Laplacian.MetricExtension
open CalabiYau.Analysis.Laplacian.ChartLocalLaplacian
open CalabiYau.Laplacian.ChartMeasureEquiv
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.ChartBilinearH1ComplFromDom
open CalabiYau.Analysis.Laplacian.ChartBilinearSmooth
open CalabiYau.Analysis.Laplacian.ChartPulledIntegralContinuity
open CalabiYau.Analysis.Laplacian.ChartPushedWeakPartialOnVolume
open CalabiYau.Analysis.Laplacian.H1ComplGradientH1LipschitzBound
open CalabiYau.Analysis.Laplacian.H1ComplToLpChartBridge
open CalabiYau.Analysis.Laplacian.H1ComplWeakPartialLimit
open CalabiYau.Analysis.Laplacian.LaplacianDomainVariationalIdentity
open CalabiYau.Analysis.Laplacian.LaplacianDomainVariationalIdentityIntegralForm
open _root_.Sobolev.NirenbergEuclidean
open _root_.Sobolev.Chart

local instance : MeasurableSpace M := borel M
local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless] [T2Space M] [CompactSpace M] in

private noncomputable def extChartAtSymmGlobal (α : M) : E → M := by
  classical
  exact (extChartAt I α).target.piecewise
    (fun y : E => (extChartAt I α).symm y)
    (fun _ : E => α)

private lemma extChartAtSymmGlobal_eq_on_target (α : M) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    extChartAtSymmGlobal (I := I) (M := M) α y = (extChartAt I α).symm y := by
  classical
  change (extChartAt I α).target.piecewise
    (fun y : E => (extChartAt I α).symm y)
    (fun _ : E => α) y = _
  rw [Set.piecewise_eq_of_mem _ _ _ hy]

private lemma extChartAtSymmGlobal_measurable (α : M) :
    Measurable (extChartAtSymmGlobal (I := I) (M := M) α) := by
  classical
  unfold extChartAtSymmGlobal
  exact ContinuousOn.measurable_piecewise
    (continuousOn_extChartAt_symm (I := I) α)
    continuousOn_const
    (CalabiYau.RiemannianVolume.measurableSet_extChartAt_target
      (I := I) (M := M) α)

variable [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] in
private lemma chartPushedRaw_measurable (α : M) {F : M → ℝ}
    (hF_meas : Measurable F) :
    Measurable (Sobolev.Chart.chartPushedRaw I α F) := by
  classical
  have h_extSymm_meas : Measurable (extChartAtSymmGlobal (I := I) (M := M) α) :=
    extChartAtSymmGlobal_measurable (I := I) (M := M) α
  have h_comp : Measurable
      (fun y : EuclN =>
        F (extChartAtSymmGlobal (I := I) (M := M) α
          ((toEuclidean (E := E)).symm y))) :=
    hF_meas.comp (h_extSymm_meas.comp
      (toEuclidean (E := E)).symm.continuous.measurable)
  have hCT_meas : MeasurableSet
      (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
    Sobolev.Chart.chartTargetEuclid_measurableSet
      (I := I) (M := M) α
  have h_piecewise :
      Sobolev.Chart.chartPushedRaw I α F =
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α).piecewise
          (fun y : EuclN =>
            F (extChartAtSymmGlobal (I := I) (M := M) α
              ((toEuclidean (E := E)).symm y)))
          (fun _ : EuclN => (0 : ℝ)) := by
    funext y
    by_cases hy : y ∈ Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α
    · rw [Set.piecewise_eq_of_mem _ _ _ hy]
      rw [Sobolev.Chart.chartPushedRaw_apply_of_mem
        (I := I) (M := M) α F hy]
      have h_toE_symm_in : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
        rcases hy with ⟨w, hw_target, hwy⟩
        have h_eq : (toEuclidean (E := E)).symm y = w := by
          rw [← hwy]; exact (toEuclidean (E := E)).symm_apply_apply w
        rw [h_eq]; exact hw_target
      rw [extChartAtSymmGlobal_eq_on_target (I := I) (M := M) α h_toE_symm_in]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hy]
      rw [Sobolev.Chart.chartPushedRaw_apply_of_notMem
        (I := I) (M := M) α F hy]
  rw [h_piecewise]
  exact Measurable.piecewise hCT_meas h_comp measurable_const
section

variable [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M]


private lemma lintegral_chartLocalMeasure_le_lintegral_riemannianVolumeMeasure
    (g : SmoothRiemannianMetric I M) (α : M)
    {F : M → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂(chartLocalMeasure (I := I) g α) ≤
      ∫⁻ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  set Ftilde : M → ℝ≥0∞ := (chartAt H α).source.indicator F with hFtilde_def
  have hFtilde_meas : Measurable Ftilde := hF.indicator (chartAt H α).open_source.measurableSet
  have hFtilde_zero_off : ∀ x, x ∉ (chartAt H α).source → Ftilde x = 0 := fun x hx =>
    Set.indicator_of_notMem hx _
  have h_chart_eq_μ :
      ∫⁻ x, Ftilde x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫⁻ x, Ftilde x ∂(chartLocalMeasure (I := I) g α) := by
    change ∫⁻ x, Ftilde x ∂(riemannianMeasure (I := I) g (chartAtlasPOU I M)) =
      ∫⁻ x, Ftilde x ∂(chartLocalMeasure (I := I) g α)
    exact
      riemannianMeasure_lintegral_eq_chartLocalMeasure_of_supportIn
      (I := I) (M := M) g α hFtilde_meas hFtilde_zero_off
  have h_off_zero :
      (chartLocalMeasure (I := I) g α) ((chartAt H α).source)ᶜ = 0 :=
    chartLocalMeasure_apply_of_disjoint_source (I := I) g α
      ((chartAt H α).open_source.measurableSet.compl)
      disjoint_compl_left
  have h_ae_F_eq_Ftilde : F =ᵐ[chartLocalMeasure (I := I) g α] Ftilde := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ h_off_zero
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    have hx' : x ∈ (chartAt H α).sourceᶜ ∨ x ∈ (chartAt H α).source := by
      by_cases h : x ∈ (chartAt H α).source
      · exact Or.inr h
      · exact Or.inl h
    rcases hx' with hxc | hxsrc
    · exact hxc
    · exfalso; apply hx; rw [hFtilde_def, Set.indicator_of_mem hxsrc]
  have h_chartLocal_F_eq_Ftilde :
      ∫⁻ x, F x ∂(chartLocalMeasure (I := I) g α) =
        ∫⁻ x, Ftilde x ∂(chartLocalMeasure (I := I) g α) :=
    MeasureTheory.lintegral_congr_ae h_ae_F_eq_Ftilde
  rw [h_chartLocal_F_eq_Ftilde, ← h_chart_eq_μ]
  refine MeasureTheory.lintegral_mono fun x => ?_
  by_cases hx : x ∈ (chartAt H α).source
  · rw [hFtilde_def, Set.indicator_of_mem hx]
  · rw [hFtilde_def, Set.indicator_of_notMem hx]; exact zero_le

private lemma lintegral_density_chartPushedRaw_pow_le
    (g : SmoothRiemannianMetric I M) (α : M)
    {F : M → ℝ} (hF_meas : Measurable F) {p : ℝ} (_hp_pos : 0 < p) :
    (Sobolev.Chart.euclideanHaarFactor E : ℝ≥0∞) *
      ∫⁻ y in Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
        ENNReal.ofReal (densityOnEuclid (I := I) g α y) *
          ‖Sobolev.Chart.chartPushedRaw I α F y‖ₑ ^ p
        ∂(volume : Measure EuclN) ≤
      ∫⁻ x, ‖F x‖ₑ ^ p
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  have h_target_meas :
      MeasurableSet (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
    Sobolev.Chart.chartTargetEuclid_measurableSet
      (I := I) (M := M) α
  have h_rewrite :
      ∫⁻ y in Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
          ENNReal.ofReal (densityOnEuclid (I := I) g α y) *
            ‖Sobolev.Chart.chartPushedRaw I α F y‖ₑ ^ p
          ∂(volume : Measure EuclN) =
        ∫⁻ y in Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
          ENNReal.ofReal (densityOnEuclid (I := I) g α y) *
            ‖F ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ₑ ^ p
          ∂(volume : Measure EuclN) := by
    refine MeasureTheory.setLIntegral_congr_fun h_target_meas (fun y hy => ?_)
    rw [Sobolev.Chart.chartPushedRaw_apply_of_mem
      (I := I) (M := M) α F hy]
  rw [h_rewrite]
  have h_G_meas : Measurable (fun x : M => ‖F x‖ₑ ^ p) :=
    (hF_meas.enorm).pow_const p
  have h_bridge :
      ∫⁻ x, ‖F x‖ₑ ^ p ∂(chartLocalMeasure (I := I) g α) =
      (Sobolev.Chart.euclideanHaarFactor E : ℝ≥0∞) *
        ∫⁻ y in Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
          ENNReal.ofReal
              (CalabiYau.RiemannianVolume.chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ‖F ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ₑ ^ p
          ∂(volume : Measure EuclN) :=
    Sobolev.Chart.chartLocalMeasure_lintegral_eq_chartTargetEuclid
      (I := I) (M := M) g α h_G_meas
  have h_density_eq : ∀ y : EuclN,
      CalabiYau.RiemannianVolume.chartDensity g α
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
        densityOnEuclid (I := I) g α y := fun y => rfl
  have h_setLInt_eq :
      ∫⁻ y in Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
          ENNReal.ofReal
              (CalabiYau.RiemannianVolume.chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ‖F ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ₑ ^ p
          ∂(volume : Measure EuclN) =
        ∫⁻ y in Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
          ENNReal.ofReal (densityOnEuclid (I := I) g α y) *
            ‖F ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ₑ ^ p
          ∂(volume : Measure EuclN) := by
    refine MeasureTheory.setLIntegral_congr_fun h_target_meas (fun y _ => ?_)
    rw [h_density_eq y]
  rw [h_setLInt_eq] at h_bridge
  rw [← h_bridge]
  exact lintegral_chartLocalMeasure_le_lintegral_riemannianVolumeMeasure
    (I := I) (M := M) g α h_G_meas

end
section

variable [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]
  [T2Space M] [CompactSpace M]


lemma chartPushedRaw_memLp_chartPulledWeighted
    (g : SmoothRiemannianMetric I M) (α : M)
    {F : M → ℝ} (hF_meas : Measurable F)
    (hF_memLp : MemLp F 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    MemLp (Sobolev.Chart.chartPushedRaw I α F) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)) := by
  classical
  apply memLp_iff.mpr
  have h_pushed_meas :=
    (chartPushedRaw_measurable (I := I) (M := M) α hF_meas).aestronglyMeasurable
      (μ := (chartPulledWeightedMeasure (I := I) g α).restrict
        (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α))
  set μ_w : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α)
  have hCT_meas :
      MeasurableSet (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
    Sobolev.Chart.chartTargetEuclid_measurableSet
      (I := I) (M := M) α
  have h_two_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h_two_ne_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have h_two_toReal : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h_two_ne_zero h_two_ne_top h_pushed_meas]
  rw [h_two_toReal]
  refine ENNReal.rpow_lt_top_of_nonneg (by positivity) ?_
  show ∫⁻ y, ‖Sobolev.Chart.chartPushedRaw I α F y‖ₑ ^ (2 : ℝ) ∂μ_w ≠
    ⊤
  have h_lint_eq :
      ∫⁻ y, ‖Sobolev.Chart.chartPushedRaw I α F y‖ₑ ^ (2 : ℝ) ∂μ_w =
        ∫⁻ y in Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
          ENNReal.ofReal (densityOnEuclid (I := I) g α y) *
            ‖Sobolev.Chart.chartPushedRaw I α F y‖ₑ ^ (2 : ℝ)
          ∂(volume : Measure EuclN) := by
    change ∫⁻ y, ‖Sobolev.Chart.chartPushedRaw I α F y‖ₑ ^ (2 : ℝ)
        ∂((chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)) = _
    unfold chartPulledWeightedMeasure
    rw [show
        ((volume : Measure EuclN).withDensity
            (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α) =
          ((volume : Measure EuclN).restrict
            (Sobolev.Chart.chartTargetEuclid
              (I := I) (M := M) α)).withDensity
            (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y)) from
        MeasureTheory.restrict_withDensity hCT_meas _]
    rw [MeasureTheory.lintegral_withDensity_eq_lintegral_mul_non_measurable₀
        ((volume : Measure EuclN).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α))
        (f := fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
        ?_ ?_]
    · simp only [Pi.mul_apply]
    · refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
      exact (densityOnEuclid_continuousOn (I := I) g α).aemeasurable
        (Sobolev.Chart.chartTargetEuclid_isOpen
          (I := I) (M := M) α).measurableSet
    · refine Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [h_lint_eq]
  have h_c_E_pos : (0 : ℝ≥0∞) <
      (Sobolev.Chart.euclideanHaarFactor E : ℝ≥0∞) := by
    exact_mod_cast Sobolev.Chart.euclideanHaarFactor_pos
  have h_c_E_ne_zero : (Sobolev.Chart.euclideanHaarFactor E : ℝ≥0∞) ≠
    0 :=
    ne_of_gt h_c_E_pos
  have h_c_E_ne_top : (Sobolev.Chart.euclideanHaarFactor E : ℝ≥0∞) ≠
    ⊤ :=
    Sobolev.Chart.euclideanHaarFactor_ennreal_ne_top
  have h_bound :=
    lintegral_density_chartPushedRaw_pow_le (I := I) (M := M) g α (p := 2) hF_meas
      (by norm_num : (0 : ℝ) < 2)
  have h_RHS_lt_top : ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) < ⊤ := by
    have h_eLp_lt_top := hF_memLp.eLpNorm_lt_top
    have h_eLp_eq : eLpNorm F 2 (riemannianVolumeMeasure (I := I) (M := M) g) ^ (2 : ℝ) =
        ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h_two_ne_zero h_two_ne_top
        hF_memLp.aestronglyMeasurable]
      rw [h_two_toReal]
      have h2_eq : ((∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) =
          (∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ^ (((1 : ℝ) / 2) * 2) := by
        rw [← ENNReal.rpow_mul]
      rw [h2_eq]
      norm_num
    rw [← h_eLp_eq]
    refine ENNReal.rpow_lt_top_of_nonneg (by positivity) ?_
    exact h_eLp_lt_top.ne
  intro h_contra
  rw [h_contra, ENNReal.mul_top h_c_E_ne_zero] at h_bound
  exact absurd h_bound (not_le.mpr h_RHS_lt_top)

private lemma eLpNorm_chartPushedRaw_le
    (g : SmoothRiemannianMetric I M) (α : M)
    {F : M → ℝ} (hF_meas : Measurable F) :
    eLpNorm (Sobolev.Chart.chartPushedRaw I α F) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)) ≤
      ((Sobolev.Chart.euclideanHaarFactor E : ℝ≥0∞))⁻¹ ^ ((1 : ℝ)/2) *
        eLpNorm F 2 (riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  set c_E := Sobolev.Chart.euclideanHaarFactor E
  have h_c_E_pos : (0 : ℝ≥0∞) < (c_E : ℝ≥0∞) := by
    exact_mod_cast Sobolev.Chart.euclideanHaarFactor_pos
  have h_c_E_ne_zero : (c_E : ℝ≥0∞) ≠ 0 := ne_of_gt h_c_E_pos
  have h_c_E_ne_top : (c_E : ℝ≥0∞) ≠ ⊤ :=
    Sobolev.Chart.euclideanHaarFactor_ennreal_ne_top
  have h_two_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h_two_ne_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have h_two_toReal : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  have hCT_meas :
      MeasurableSet (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
    Sobolev.Chart.chartTargetEuclid_measurableSet
      (I := I) (M := M) α
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h_two_ne_zero h_two_ne_top
    (chartPushedRaw_measurable (I := I) (M := M) α hF_meas).aestronglyMeasurable]
  rw [h_two_toReal]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h_two_ne_zero h_two_ne_top
    hF_meas.aestronglyMeasurable]
  rw [h_two_toReal]
  have h_lint_eq :
      ∫⁻ y, ‖Sobolev.Chart.chartPushedRaw I α F y‖ₑ ^ (2 : ℝ)
        ∂((chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)) =
        ∫⁻ y in Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
          ENNReal.ofReal (densityOnEuclid (I := I) g α y) *
            ‖Sobolev.Chart.chartPushedRaw I α F y‖ₑ ^ (2 : ℝ)
          ∂(volume : Measure EuclN) := by
    unfold chartPulledWeightedMeasure
    rw [show
        ((volume : Measure EuclN).withDensity
            (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α) =
          ((volume : Measure EuclN).restrict
            (Sobolev.Chart.chartTargetEuclid
              (I := I) (M := M) α)).withDensity
            (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y)) from
        MeasureTheory.restrict_withDensity hCT_meas _]
    rw [MeasureTheory.lintegral_withDensity_eq_lintegral_mul_non_measurable₀
        ((volume : Measure EuclN).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α))
        (f := fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
        ?_ ?_]
    · simp only [Pi.mul_apply]
    · refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
      exact (densityOnEuclid_continuousOn (I := I) g α).aemeasurable
        (Sobolev.Chart.chartTargetEuclid_isOpen
          (I := I) (M := M) α).measurableSet
    · refine Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [h_lint_eq]
  have h_bound :=
    lintegral_density_chartPushedRaw_pow_le (I := I) (M := M) g α (p := 2) hF_meas
      (by norm_num : (0 : ℝ) < 2)
  have h_div : ∫⁻ y in Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α,
        ENNReal.ofReal (densityOnEuclid (I := I) g α y) *
          ‖Sobolev.Chart.chartPushedRaw I α F y‖ₑ ^ (2 : ℝ)
        ∂(volume : Measure EuclN) ≤
      (c_E : ℝ≥0∞)⁻¹ *
        ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    have h_inv_mul : (c_E : ℝ≥0∞)⁻¹ * ((c_E : ℝ≥0∞) *
        ∫⁻ y in Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α,
            ENNReal.ofReal (densityOnEuclid (I := I) g α y) *
              ‖Sobolev.Chart.chartPushedRaw I α F y‖ₑ ^ (2 : ℝ)
            ∂(volume : Measure EuclN)) =
        ∫⁻ y in Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α,
            ENNReal.ofReal (densityOnEuclid (I := I) g α y) *
              ‖Sobolev.Chart.chartPushedRaw I α F y‖ₑ ^ (2 : ℝ)
            ∂(volume : Measure EuclN) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel h_c_E_ne_zero h_c_E_ne_top, one_mul]
    calc ∫⁻ y in _, _ ∂_
        = (c_E : ℝ≥0∞)⁻¹ * ((c_E : ℝ≥0∞) *
            ∫⁻ y in Sobolev.Chart.chartTargetEuclid
                (I := I) (M := M) α,
                ENNReal.ofReal (densityOnEuclid (I := I) g α y) *
                  ‖Sobolev.Chart.chartPushedRaw I α F y‖ₑ ^ (2 : ℝ)
                ∂(volume : Measure EuclN)) := h_inv_mul.symm
      _ ≤ (c_E : ℝ≥0∞)⁻¹ * ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
          gcongr
  have h_pow_le : (∫⁻ y in Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α,
        ENNReal.ofReal (densityOnEuclid (I := I) g α y) *
          ‖Sobolev.Chart.chartPushedRaw I α F y‖ₑ ^ (2 : ℝ)
        ∂(volume : Measure EuclN)) ^ ((1 : ℝ) / 2) ≤
      ((c_E : ℝ≥0∞)⁻¹ *
        ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) ∂(riemannianVolumeMeasure (I := I) (M := M) g))
        ^ ((1 : ℝ) / 2) :=
    ENNReal.rpow_le_rpow h_div (by positivity)
  refine h_pow_le.trans ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / 2)]

noncomputable def chartPushedRawLpFromLp
    (g : SmoothRiemannianMetric I M) (α : M)
    (F : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
      (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α)) :=
  (chartPushedRaw_memLp_chartPulledWeighted (I := I) (M := M) g α
    (Lp.stronglyMeasurable F).measurable (Lp.memLp F)).toLp _

lemma chartPushedRawLpFromLp_coeFn
    (g : SmoothRiemannianMetric I M) (α : M)
    (F : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ((chartPushedRawLpFromLp (I := I) (M := M) g α F :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α))) : EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)]
      Sobolev.Chart.chartPushedRaw I α
        ((F : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  unfold chartPushedRawLpFromLp
  exact MemLp.coeFn_toLp _

lemma chartPushedRawLpFromLp_tendsto
    (g : SmoothRiemannianMetric I M) (α : M)
    {F : ℕ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    {F_lim : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (h_tendsto : Tendsto F atTop (𝓝 F_lim)) :
    Tendsto (fun n => chartPushedRawLpFromLp (I := I) (M := M) g α (F n))
      atTop (𝓝 (chartPushedRawLpFromLp (I := I) (M := M) g α F_lim)) := by
  classical
  have h_norm_tendsto :
      Tendsto (fun n => ‖F n - F_lim‖) atTop (𝓝 0) := by
    have h_sub : Tendsto (fun n => F n - F_lim) atTop (𝓝 0) := by
      have := h_tendsto.sub (tendsto_const_nhds (x := F_lim))
      simpa using this
    change Tendsto
      ((fun a : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) => ‖a‖) ∘
        fun n => F n - F_lim) atTop (nhds 0)
    simpa only [norm_zero] using
      (continuous_norm.tendsto (0 :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))).comp h_sub
  have h_two_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h_two_ne_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have h_eLpNorm_eq : ∀ n,
      eLpNorm (((F n - F_lim) : Lp ℝ 2 _) : M → ℝ) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) =
      ENNReal.ofReal ‖F n - F_lim‖ := by
    intro n
    rw [Lp.norm_def]
    rw [ENNReal.ofReal_toReal
      ((Lp.memLp (F n - F_lim)).eLpNorm_lt_top.ne)]
  have h_eLpNorm_tendsto :
      Tendsto (fun n => eLpNorm (((F n - F_lim) : Lp ℝ 2 _) : M → ℝ) 2
        (riemannianVolumeMeasure (I := I) (M := M) g)) atTop (𝓝 0) := by
    have h_funeq : (fun n =>
        eLpNorm (((F n - F_lim) : Lp ℝ 2 _) : M → ℝ) 2
          (riemannianVolumeMeasure (I := I) (M := M) g)) =
        (fun n => ENNReal.ofReal ‖F n - F_lim‖) := funext h_eLpNorm_eq
    rw [h_funeq]
    have h_comp := (ENNReal.continuous_ofReal.tendsto 0).comp h_norm_tendsto
    simp only [Function.comp_def, ENNReal.ofReal_zero] at h_comp
    exact h_comp
  have h_aeEq : ∀ n, (((F n - F_lim) : Lp ℝ 2 _) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x => ((F n : Lp ℝ 2 _) : M → ℝ) x -
        ((F_lim : Lp ℝ 2 _) : M → ℝ) x) := by
    intro n
    have := MeasureTheory.Lp.coeFn_sub (F n) F_lim
    filter_upwards [this] with x hx
    exact hx
  have h_diff_tendsto :
      Tendsto (fun n => eLpNorm
        (fun x => ((F n : Lp ℝ 2 _) : M → ℝ) x - ((F_lim : Lp ℝ 2 _) : M → ℝ) x) 2
        (riemannianVolumeMeasure (I := I) (M := M) g)) atTop (𝓝 0) := by
    have h_funeq : (fun n => eLpNorm
        (fun x => ((F n : Lp ℝ 2 _) : M → ℝ) x - ((F_lim : Lp ℝ 2 _) : M → ℝ) x) 2
        (riemannianVolumeMeasure (I := I) (M := M) g)) =
      (fun n => eLpNorm (((F n - F_lim) : Lp ℝ 2 _) : M → ℝ) 2
        (riemannianVolumeMeasure (I := I) (M := M) g)) := by
      funext n
      exact MeasureTheory.eLpNorm_congr_ae (h_aeEq n).symm
    rw [h_funeq]
    exact h_eLpNorm_tendsto
  have h_meas : ∀ n, Measurable (fun x : M => ((F n : Lp ℝ 2 _) : M → ℝ) x -
      ((F_lim : Lp ℝ 2 _) : M → ℝ) x) := fun n =>
    ((Lp.stronglyMeasurable (F n)).measurable).sub
      (Lp.stronglyMeasurable F_lim).measurable
  have h_chart_eLp_tendsto :
      Tendsto (fun n =>
        eLpNorm (Sobolev.Chart.chartPushedRaw I α
          (fun x => ((F n : Lp ℝ 2 _) : M → ℝ) x - ((F_lim : Lp ℝ 2 _) : M → ℝ) x)) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (Sobolev.Chart.chartTargetEuclid
              (I := I) (M := M) α))) atTop (𝓝 0) := by
    set c := ((Sobolev.Chart.euclideanHaarFactor E : ℝ≥0∞))⁻¹ ^
      ((1 : ℝ)/2)
      with hc_def
    have h_const_tendsto :
        Tendsto (fun n => c *
          eLpNorm
            (fun x : M => ((F n : Lp ℝ 2 _) : M → ℝ) x - ((F_lim : Lp ℝ 2 _) : M → ℝ) x) 2
            (riemannianVolumeMeasure (I := I) (M := M) g)) atTop (𝓝 0) := by
      have h_c_ne_top : c ≠ ⊤ := by
        rw [hc_def]
        refine ENNReal.rpow_ne_top_of_nonneg (by positivity) ?_
        exact ENNReal.inv_ne_top.mpr
          (Sobolev.Chart.euclideanHaarFactor_ennreal_ne_zero
            (E := E))
      have h := ENNReal.Tendsto.const_mul (a := c) (b := 0) h_diff_tendsto (Or.inr h_c_ne_top)
      simpa using h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_const_tendsto
      (fun _ => zero_le)
      (fun n => eLpNorm_chartPushedRaw_le (I := I) (M := M) g α (h_meas n))
  rw [tendsto_iff_dist_tendsto_zero]
  have h_dist_eq : ∀ n,
      dist (chartPushedRawLpFromLp (I := I) (M := M) g α (F n))
          (chartPushedRawLpFromLp (I := I) (M := M) g α F_lim) =
        ENNReal.toReal (eLpNorm
          (Sobolev.Chart.chartPushedRaw I α
            (fun x => ((F n : Lp ℝ 2 _) : M → ℝ) x - ((F_lim : Lp ℝ 2 _) : M → ℝ) x)) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (Sobolev.Chart.chartTargetEuclid
              (I := I) (M := M) α))) := by
    intro n
    rw [dist_eq_norm, Lp.norm_def]
    have h_sub_aeEq := MeasureTheory.Lp.coeFn_sub
      (chartPushedRawLpFromLp (I := I) (M := M) g α (F n))
      (chartPushedRawLpFromLp (I := I) (M := M) g α F_lim)
    have h_coe_n := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α (F n)
    have h_coe_lim := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α F_lim
    have h_diff_ae : (((chartPushedRawLpFromLp (I := I) (M := M) g α (F n) -
            chartPushedRawLpFromLp (I := I) (M := M) g α F_lim) :
            Lp ℝ 2 _) : EuclN → ℝ) =ᵐ[
          (chartPulledWeightedMeasure (I := I) g α).restrict
            (Sobolev.Chart.chartTargetEuclid
              (I := I) (M := M) α)]
        Sobolev.Chart.chartPushedRaw I α
          (fun x => ((F n : Lp ℝ 2 _) : M → ℝ) x - ((F_lim : Lp ℝ 2 _) : M → ℝ) x) := by
      filter_upwards [h_sub_aeEq, h_coe_n, h_coe_lim] with y hy_sub hy_n hy_lim
      rw [hy_sub, Pi.sub_apply, hy_n, hy_lim]
      unfold Sobolev.Chart.chartPushedRaw
      by_cases hy : y ∈ Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α
      · simp [hy]
      · simp [hy]
    rw [MeasureTheory.eLpNorm_congr_ae h_diff_ae]
  rw [show (fun n =>
      dist (chartPushedRawLpFromLp (I := I) (M := M) g α (F n))
        (chartPushedRawLpFromLp (I := I) (M := M) g α F_lim)) =
    (fun n => ENNReal.toReal (eLpNorm
        (Sobolev.Chart.chartPushedRaw I α
          (fun x => ((F n : Lp ℝ 2 _) : M → ℝ) x - ((F_lim : Lp ℝ 2 _) : M → ℝ) x)) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)))) from funext h_dist_eq]
  have h_toReal_tendsto :
      Tendsto (fun n => ENNReal.toReal (eLpNorm
        (Sobolev.Chart.chartPushedRaw I α
          (fun x => ((F n : Lp ℝ 2 _) : M → ℝ) x - ((F_lim : Lp ℝ 2 _) : M → ℝ) x)) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)))) atTop (𝓝 0) := by
    have h_comp := (ENNReal.tendsto_toReal (by norm_num : (0 : ℝ≥0∞) ≠ ⊤)).comp
      h_chart_eLp_tendsto
    change Tendsto (ENNReal.toReal ∘ fun n => eLpNorm
      (Sobolev.Chart.chartPushedRaw I α
        (fun x => ((F n : Lp ℝ 2 _) : M → ℝ) x -
          ((F_lim : Lp ℝ 2 _) : M → ℝ) x)) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α))) atTop (nhds 0)
    exact h_comp
  exact h_toReal_tendsto

private lemma chartPulledIntegralCLM_density_ψ_smoothToLp_eq_setIntegral
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆
      Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α)
    (v : SmoothScalar g) :
    chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
        (smoothToLp (I := I) (M := M) g v) =
      ∫ y in Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          Sobolev.Chart.chartPushedRaw I α v.toFun y *
          ψ y ∂(volume : Measure EuclN) := by
  classical
  have h_clm : chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
        (smoothToLp (I := I) (M := M) g v) =
      ∫ y in Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
        v.toFun ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          (densityOnEuclid (I := I) g α y * ψ y) ∂(volume : Measure EuclN) :=
    chartPulledIntegralCLM_smoothToLp (I := I) (M := M) g α
      (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
      (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
      (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
      v
  rw [h_clm]
  refine MeasureTheory.setIntegral_congr_fun
    (Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α).measurableSet (fun y hy => ?_)
  rw [Sobolev.Chart.chartPushedRaw_apply_of_mem
    (I := I) (M := M) α v.toFun hy]
  ring

end

variable [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in
private lemma psi_memLp_chartPulledWeighted
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆
      Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :
    MemLp ψ 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)) :=
  continuous_compactSupport_memLp_chartPulledWeighted_restrict
    (I := I) (M := M) g α hψ.continuous hψ_cs hψ_support
section

variable [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]


private lemma setIntegral_density_eq_integral_weighted
    (g : SmoothRiemannianMetric I M) (α : M)
    (f ψ : EuclN → ℝ) :
    ∫ y in Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * f y * ψ y
      ∂(volume : Measure EuclN) =
    ∫ y in Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α, f y * ψ y
      ∂(chartPulledWeightedMeasure (I := I) g α) := by
  classical
  have h_meas_chartTarget :
      MeasurableSet (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
    (Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α).measurableSet
  rw [show ∫ y in Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y * f y * ψ y
        ∂(volume : Measure EuclN) =
      ∫ y in Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y * (f y * ψ y)
        ∂(volume : Measure EuclN) from by
      refine MeasureTheory.setIntegral_congr_fun h_meas_chartTarget (fun y _hy => ?_)
      ring]
  rw [← setIntegral_chartPulledWeighted_eq_setIntegral_density_mul_volume
    (I := I) (M := M) g α (fun y => f y * ψ y)]

private lemma setIntegral_density_G_psi_eq_inner
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆
      Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α)
    (G : Lp ℝ 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α))) :
    ∫ y in Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y *
        ((G : EuclN → ℝ) y) * ψ y ∂(volume : Measure EuclN) =
      @inner ℝ _ _
        ((psi_memLp_chartPulledWeighted
          (I := I) (M := M) g α hψ hψ_cs hψ_support).toLp ψ) G := by
  classical
  rw [setIntegral_density_eq_integral_weighted (I := I) (M := M) g α
    ((G : EuclN → ℝ)) ψ]
  rw [L2.inner_def
    ((psi_memLp_chartPulledWeighted (I := I) (M := M) g α
      hψ hψ_cs hψ_support).toLp ψ) G]
  have hae_psi : ((psi_memLp_chartPulledWeighted (I := I) (M := M) g α
      hψ hψ_cs hψ_support).toLp ψ : Lp ℝ 2 _) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)] ψ :=
    MemLp.coeFn_toLp _
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hae_psi] with y hy_psi
  rw [hy_psi]
  rw [show @inner ℝ _ _ (ψ y) ((G : EuclN → ℝ) y) =
      ((G : EuclN → ℝ) y) * ψ y from RCLike.inner_apply _ _]

end
section

variable [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]
  [T2Space M] [CompactSpace M]


lemma chartPushedRaw_aeEq_of_aeEq
    (g : SmoothRiemannianMetric I M) (α : M)
    {f₁ f₂ : M → ℝ} (hf₁ : Measurable f₁) (hf₂ : Measurable f₂)
    (h_ae : f₁ =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g] f₂) :
    Sobolev.Chart.chartPushedRaw I α f₁ =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)]
      Sobolev.Chart.chartPushedRaw I α f₂ := by
  classical
  set d : M → ℝ := fun x => f₁ x - f₂ x with hd_def
  have hd_meas : Measurable d := hf₁.sub hf₂
  have hd_ae_zero : d =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g] (fun _ => (0 : ℝ)) := by
    filter_upwards [h_ae] with x hx
    change f₁ x - f₂ x = 0
    rw [hx, sub_self]
  have h_lint_d_zero : ∫⁻ x, ‖d x‖ₑ ^ (2 : ℝ)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
    have h_eq : (fun x : M => ‖d x‖ₑ ^ (2 : ℝ)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g] (fun _ : M => (0 : ℝ≥0∞)) := by
      filter_upwards [hd_ae_zero] with x hx
      rw [hx]; simp
    rw [MeasureTheory.lintegral_congr_ae h_eq]; simp
  have h_bound :=
    lintegral_density_chartPushedRaw_pow_le (I := I) (M := M) g α
      (F := d) hd_meas (p := 2) (by norm_num)
  rw [h_lint_d_zero] at h_bound
  have h_c_E_pos : (0 : ℝ≥0∞) <
      (Sobolev.Chart.euclideanHaarFactor E : ℝ≥0∞) := by
    exact_mod_cast Sobolev.Chart.euclideanHaarFactor_pos
  have h_c_E_ne_zero :
      (Sobolev.Chart.euclideanHaarFactor E : ℝ≥0∞) ≠ 0 :=
    ne_of_gt h_c_E_pos
  have h_set_lint_zero :
      ∫⁻ y in Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
        ENNReal.ofReal (densityOnEuclid (I := I) g α y) *
          ‖Sobolev.Chart.chartPushedRaw I α d y‖ₑ ^ (2 : ℝ)
        ∂(volume : Measure EuclN) = 0 := by
    have h_mul_eq : (Sobolev.Chart.euclideanHaarFactor E : ℝ≥0∞) *
        (∫⁻ y in Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α,
          ENNReal.ofReal (densityOnEuclid (I := I) g α y) *
            ‖Sobolev.Chart.chartPushedRaw I α d y‖ₑ ^ (2 : ℝ)
          ∂(volume : Measure EuclN)) = 0 := le_antisymm h_bound (zero_le)
    rcases mul_eq_zero.mp h_mul_eq with hzero | hzero
    · exact absurd hzero h_c_E_ne_zero
    · exact hzero
  have h_chartTarget_meas :
      MeasurableSet (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
    (Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α).measurableSet
  have h_density_pos_ae :
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)),
      ENNReal.ofReal (densityOnEuclid (I := I) g α y) > 0 := by
    rw [ae_restrict_iff' h_chartTarget_meas]
    refine Filter.Eventually.of_forall fun y hy => ?_
    exact ENNReal.ofReal_pos.mpr (densityOnEuclid_pos (I := I) g α hy)
  have h_aestrong :
      AEMeasurable (fun y : EuclN => ENNReal.ofReal (densityOnEuclid (I := I) g α y) *
          ‖Sobolev.Chart.chartPushedRaw I α d y‖ₑ ^ (2 : ℝ))
      ((volume : Measure EuclN).restrict
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)) := by
    refine AEMeasurable.mul ?_ ?_
    · refine (ENNReal.measurable_ofReal.comp_aemeasurable ?_)
      exact (densityOnEuclid_continuousOn (I := I) g α).aemeasurable
        h_chartTarget_meas
    · refine AEMeasurable.pow_const ?_ _
      exact (chartPushedRaw_measurable (I := I) (M := M) α hd_meas).enorm.aemeasurable
  have h_integrand_ae_zero :
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)),
      ENNReal.ofReal (densityOnEuclid (I := I) g α y) *
        ‖Sobolev.Chart.chartPushedRaw I α d y‖ₑ ^ (2 : ℝ) = 0 :=
    (MeasureTheory.lintegral_eq_zero_iff' h_aestrong).mp h_set_lint_zero
  have h_chartPushed_d_zero :
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)),
      Sobolev.Chart.chartPushedRaw I α d y = 0 := by
    filter_upwards [h_integrand_ae_zero, h_density_pos_ae] with y hy h_pos
    rcases mul_eq_zero.mp hy with h | h
    · exact absurd h h_pos.ne'
    · have h_enorm_zero : ‖Sobolev.Chart.chartPushedRaw I α d y‖ₑ =
        0 := by
        have : (‖Sobolev.Chart.chartPushedRaw I α d y‖ₑ) ^ (2 : ℝ) =
            ‖Sobolev.Chart.chartPushedRaw I α d y‖ₑ ^ (2 : ℝ) := rfl
        rw [this] at h
        have h_two_pos : (0 : ℝ) < 2 := by norm_num
        have h_rpow := ENNReal.rpow_eq_zero_iff.mp h
        rcases h_rpow with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact h1
        · exact absurd h2 (by norm_num)
      exact (enorm_eq_zero (a := Sobolev.Chart.chartPushedRaw I α d
        y)).mp h_enorm_zero
  have h_abs_cts :
      (chartPulledWeightedMeasure (I := I) g α).restrict
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) ≪
      (volume : Measure EuclN).restrict
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) := by
    unfold chartPulledWeightedMeasure
    rw [show ((volume : Measure EuclN).withDensity
        (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))).restrict
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) =
        ((volume : Measure EuclN).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)).withDensity
          (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
      from MeasureTheory.restrict_withDensity h_chartTarget_meas _]
    exact MeasureTheory.withDensity_absolutelyContinuous _ _
  have h_chartPushed_d_zero_w :=
    h_abs_cts.ae_le h_chartPushed_d_zero
  filter_upwards [h_chartPushed_d_zero_w] with y hy
  by_cases h_in_chart : y ∈ Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α
  · rw [Sobolev.Chart.chartPushedRaw_apply_of_mem
      (I := I) (M := M) α d h_in_chart] at hy
    rw [Sobolev.Chart.chartPushedRaw_apply_of_mem
      (I := I) (M := M) α f₁ h_in_chart]
    rw [Sobolev.Chart.chartPushedRaw_apply_of_mem
      (I := I) (M := M) α f₂ h_in_chart]
    rw [hd_def] at hy
    linarith [sub_eq_zero.mp hy]
  · rw [Sobolev.Chart.chartPushedRaw_apply_of_notMem
      (I := I) (M := M) α f₁ h_in_chart]
    rw [Sobolev.Chart.chartPushedRaw_apply_of_notMem
      (I := I) (M := M) α f₂ h_in_chart]

theorem chartPulledIntegralCLM_density_ψ_eq_setIntegral
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆
      Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α)
    (F : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support) F =
      ∫ y in Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          ((chartPushedRawLpFromLp (I := I) (M := M) g α F :
            Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
              (Sobolev.Chart.chartTargetEuclid
                (I := I) (M := M) α))) : EuclN → ℝ) y *
          ψ y ∂(volume : Measure EuclN) := by
  classical
  obtain ⟨v, h_v_tendsto⟩ :=
    CalabiYau.Analysis.Laplacian.ChartBilinearH1ComplFromDom.exists_smooth_approx_seq_lp
      (I := I) (M := M) g F
  have h_LHS_tendsto :
      Tendsto (fun n =>
        chartPulledIntegralCLM (I := I) (M := M) g α
          (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
          (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
          (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
          (smoothToLp (I := I) (M := M) g (v n))) atTop
      (𝓝 (chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support) F)) :=
    chartPulledIntegralCLM_tendsto (I := I) (M := M) g α
      (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
      (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
      (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
      h_v_tendsto
  have h_smooth_case : ∀ n,
      chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
        (smoothToLp (I := I) (M := M) g (v n)) =
      ∫ y in Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          Sobolev.Chart.chartPushedRaw I α (v n).toFun y *
          ψ y ∂(volume : Measure EuclN) := fun n =>
    chartPulledIntegralCLM_density_ψ_smoothToLp_eq_setIntegral
      (I := I) (M := M) g α hψ hψ_cs hψ_support (v n)
  have h_aeEq : ∀ n,
      ((chartPushedRawLpFromLp (I := I) (M := M) g α
        (smoothToLp (I := I) (M := M) g (v n)) :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α))) : EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)]
      Sobolev.Chart.chartPushedRaw I α (v n).toFun := by
    intro n
    have h_coe := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α
      (smoothToLp (I := I) (M := M) g (v n))
    have h_smoothLp_aeEq :
        ((smoothToLp (I := I) (M := M) g (v n) :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g] (v n).toFun :=
      MemLp.coeFn_toLp (v n).memLp_two
    have h_bridge := chartPushedRaw_aeEq_of_aeEq (I := I) (M := M) g α
      (Lp.stronglyMeasurable _).measurable
      ((v n).smooth.continuous.measurable)
      h_smoothLp_aeEq
    exact h_coe.trans h_bridge
  have h_RHS_v_n_eq : ∀ n,
      ∫ y in Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          Sobolev.Chart.chartPushedRaw I α (v n).toFun y *
          ψ y ∂(volume : Measure EuclN) =
        ∫ y in Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          ((chartPushedRawLpFromLp (I := I) (M := M) g α
            (smoothToLp (I := I) (M := M) g (v n)) :
            Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
              (Sobolev.Chart.chartTargetEuclid
                (I := I) (M := M) α))) : EuclN → ℝ) y *
          ψ y ∂(volume : Measure EuclN) := by
    intro n
    rw [setIntegral_density_eq_integral_weighted (I := I) (M := M) g α
      (Sobolev.Chart.chartPushedRaw I α (v n).toFun) ψ]
    rw [setIntegral_density_eq_integral_weighted (I := I) (M := M) g α
      ((chartPushedRawLpFromLp (I := I) (M := M) g α
        (smoothToLp (I := I) (M := M) g (v n)) :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α))) : EuclN → ℝ) ψ]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [(h_aeEq n).symm] with y hy
    rw [hy]
  have h_inner_v_n : ∀ n,
      chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
        (smoothToLp (I := I) (M := M) g (v n)) =
      @inner ℝ _ _
        ((psi_memLp_chartPulledWeighted
          (I := I) (M := M) g α hψ hψ_cs hψ_support).toLp ψ)
        (chartPushedRawLpFromLp (I := I) (M := M) g α
          (smoothToLp (I := I) (M := M) g (v n))) := by
    intro n
    rw [h_smooth_case n, h_RHS_v_n_eq n]
    rw [setIntegral_density_G_psi_eq_inner (I := I) (M := M) g α
      hψ hψ_cs hψ_support (chartPushedRawLpFromLp (I := I) (M := M) g α
        (smoothToLp (I := I) (M := M) g (v n)))]
  rw [setIntegral_density_G_psi_eq_inner (I := I) (M := M) g α
    hψ hψ_cs hψ_support (chartPushedRawLpFromLp (I := I) (M := M) g α F)]
  have h_chartPushedRaw_tendsto :
      Tendsto (fun n => chartPushedRawLpFromLp (I := I) (M := M) g α
        (smoothToLp (I := I) (M := M) g (v n))) atTop
      (𝓝 (chartPushedRawLpFromLp (I := I) (M := M) g α F)) :=
    chartPushedRawLpFromLp_tendsto (I := I) (M := M) g α h_v_tendsto
  have h_inner_tendsto : Tendsto (fun n => @inner ℝ _ _
      ((psi_memLp_chartPulledWeighted (I := I) (M := M) g α hψ hψ_cs hψ_support).toLp ψ)
      (chartPushedRawLpFromLp (I := I) (M := M) g α
        (smoothToLp (I := I) (M := M) g (v n)))) atTop
    (𝓝 (@inner ℝ _ _
      ((psi_memLp_chartPulledWeighted (I := I) (M := M) g α hψ hψ_cs hψ_support).toLp ψ)
      (chartPushedRawLpFromLp (I := I) (M := M) g α F))) := by
    have h_inner_cont :
        Continuous (fun G => @inner ℝ _ _
          ((psi_memLp_chartPulledWeighted (I := I) (M := M) g α hψ hψ_cs hψ_support).toLp ψ)
          G) := continuous_const.inner continuous_id
    exact (h_inner_cont.tendsto _).comp h_chartPushedRaw_tendsto
  have h_LHS_eq_inner_seq : (fun n =>
      chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
        (smoothToLp (I := I) (M := M) g (v n))) =
      (fun n => @inner ℝ _ _
        ((psi_memLp_chartPulledWeighted (I := I) (M := M) g α hψ hψ_cs hψ_support).toLp ψ)
        (chartPushedRawLpFromLp (I := I) (M := M) g α
          (smoothToLp (I := I) (M := M) g (v n)))) := funext h_inner_v_n
  rw [h_LHS_eq_inner_seq] at h_LHS_tendsto
  exact tendsto_nhds_unique h_LHS_tendsto h_inner_tendsto

theorem hasWeakPartialDeriv_chartPushedWeakPartialLp_on_chartTarget
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (u_h : H1Compl g) :
    Sobolev.Euclidean.HasWeakPartialDeriv (d := Module.finrank ℝ E) j
      (((chartPushedWeakPartialLp (I := I) (M := M) g α j
        (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α j) u_h
       ) : EuclN → ℝ))
      (Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α
        ((h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  classical
  intro φ hφ_smooth hφ_cs hφ_support
  have hΩ_open :
      IsOpen (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
    Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  obtain ⟨δ, hδ_pos, hδ_subset⟩ :
      ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ (tsupport φ) ⊆
        Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α :=
    hφ_cs.exists_cthickening_subset_open hΩ_open hφ_support
  set Ω' : Set EuclN := Metric.thickening δ (tsupport φ) with hΩ'_def
  set K : Set EuclN := Metric.cthickening δ (tsupport φ) with hK_def
  have hΩ'_open : IsOpen Ω' := Metric.isOpen_thickening
  have hK_compact : IsCompact K := hφ_cs.cthickening
  have hΩ'_subset_K : Ω' ⊆ K := Metric.thickening_subset_cthickening δ (tsupport φ)
  have hK_in : K ⊆ Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α := hδ_subset
  have h_tsupport_in_Ω' : tsupport φ ⊆ Ω' :=
    Metric.self_subset_thickening hδ_pos _
  have h_local :=
    hasWeakPartialDeriv_chartPushedWeakPartialLp_on_compact
      (I := I) (M := M) g α j u_h hΩ'_open hK_compact hΩ'_subset_K hK_in
  have h_identity := h_local φ hφ_smooth hφ_cs h_tsupport_in_Ω'
  set f := Sobolev.Chart.chartPushed (I := I) (M := M)
    (chartAtlasPOU I M) α
    ((h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ) with hf_def
  set g_chart := ((chartPushedWeakPartialLp (I := I) (M := M) g α j
    (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α j) u_h
   ) : EuclN → ℝ) with hg_chart_def
  have h_chartTarget_meas :
      MeasurableSet (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := hΩ_open.measurableSet
  have hΩ'_meas : MeasurableSet Ω' := hΩ'_open.measurableSet
  have hΩ'_subset_chartTarget : Ω' ⊆
      Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α := hΩ'_subset_K.trans hK_in
  have h_fderiv_zero : ∀ x ∉ tsupport φ, fderiv ℝ φ x = 0 := by
    intro x hx
    have h_compl_open : IsOpen ((tsupport φ)ᶜ) :=
      (isClosed_tsupport _).isOpen_compl
    have hx_in_compl : x ∈ (tsupport φ)ᶜ := hx
    have hφ_zero_neighborhood : ∀ᶠ y in 𝓝 x, φ y = 0 := by
      filter_upwards [h_compl_open.mem_nhds hx_in_compl] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    have hφ_const_zero : fderiv ℝ φ x = fderiv ℝ (fun _ : EuclN => (0 : ℝ)) x := by
      apply Filter.EventuallyEq.fderiv_eq
      filter_upwards [hφ_zero_neighborhood] with y hy
      rw [hy]
    rw [hφ_const_zero]
    simp
  have h_LHS_eq :
      ∫ x in Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
        f x * (fderiv ℝ φ x) (EuclideanSpace.single j 1) =
      ∫ x in Ω', f x * (fderiv ℝ φ x) (EuclideanSpace.single j 1) := by
    rw [show ∫ x in Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α,
          f x * (fderiv ℝ φ x) (EuclideanSpace.single j 1) =
        ∫ x in Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α,
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α).indicator
            (fun x => f x * (fderiv ℝ φ x) (EuclideanSpace.single j 1)) x
        from by
      refine (MeasureTheory.setIntegral_congr_fun h_chartTarget_meas (fun x hx => ?_)).symm
      rw [Set.indicator_of_mem hx]]
    rw [show ∫ x in Ω', f x * (fderiv ℝ φ x) (EuclideanSpace.single j 1) =
        ∫ x in Ω', (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α).indicator
            (fun x => f x * (fderiv ℝ φ x) (EuclideanSpace.single j 1)) x from by
      refine (MeasureTheory.setIntegral_congr_fun hΩ'_meas (fun x hx => ?_)).symm
      rw [Set.indicator_of_mem (hΩ'_subset_chartTarget hx)]]
    have h_outside_Ω' : ∀ x ∈ (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) \ Ω',
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α).indicator
          (fun x => f x * (fderiv ℝ φ x) (EuclideanSpace.single j 1)) x = 0 := by
      intro x ⟨hx_in_chart, hx_notin_Ω'⟩
      rw [Set.indicator_of_mem hx_in_chart]
      have hx_notin_tsupport : x ∉ tsupport φ := fun hx => hx_notin_Ω' (h_tsupport_in_Ω' hx)
      rw [h_fderiv_zero x hx_notin_tsupport]
      simp
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) (f := _)
      (s := Ω')]
    · rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) (f := _)
      (s := Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)]
      intro x hx
      by_cases hx_in_chart : x ∈ Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α
      · exact absurd hx_in_chart hx
      · rw [Set.indicator_of_notMem hx_in_chart]
    intro x hx
    by_cases hx_in_chart : x ∈ Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α
    · exact h_outside_Ω' x ⟨hx_in_chart, hx⟩
    · rw [Set.indicator_of_notMem hx_in_chart]
  have h_RHS_eq :
      ∫ x in Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
        g_chart x * φ x =
      ∫ x in Ω', g_chart x * φ x := by
    rw [show ∫ x in Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α,
          g_chart x * φ x =
        ∫ x in Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α,
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α).indicator
            (fun x => g_chart x * φ x) x
        from by
      refine (MeasureTheory.setIntegral_congr_fun h_chartTarget_meas (fun x hx => ?_)).symm
      rw [Set.indicator_of_mem hx]]
    rw [show ∫ x in Ω', g_chart x * φ x =
        ∫ x in Ω', (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α).indicator
            (fun x => g_chart x * φ x) x from by
      refine (MeasureTheory.setIntegral_congr_fun hΩ'_meas (fun x hx => ?_)).symm
      rw [Set.indicator_of_mem (hΩ'_subset_chartTarget hx)]]
    have h_outside_Ω' : ∀ x ∈ (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) \ Ω',
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α).indicator
          (fun x => g_chart x * φ x) x = 0 := by
      intro x ⟨hx_in_chart, hx_notin_Ω'⟩
      rw [Set.indicator_of_mem hx_in_chart]
      have hx_notin_tsupport : x ∉ tsupport φ := fun hx => hx_notin_Ω' (h_tsupport_in_Ω' hx)
      have hφ_x_zero : φ x = 0 := image_eq_zero_of_notMem_tsupport hx_notin_tsupport
      rw [hφ_x_zero, mul_zero]
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) (f := _)
      (s := Ω')]
    · rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) (f := _)
      (s := Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)]
      intro x hx
      by_cases hx_in_chart : x ∈ Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α
      · exact absurd hx_in_chart hx
      · rw [Set.indicator_of_notMem hx_in_chart]
    intro x hx
    by_cases hx_in_chart : x ∈ Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α
    · exact h_outside_Ω' x ⟨hx_in_chart, hx⟩
    · rw [Set.indicator_of_notMem hx_in_chart]
  rw [h_LHS_eq, h_RHS_eq]
  exact h_identity

end
section

variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless] [T2Space M] [CompactSpace M]


noncomputable def chartBilinearH1ComplDataOfLaplacianDomain
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    ChartBilinearH1ComplData (I := I) (M := M) g α where
  uChart :=
    ((chartPushedLpFromLp (I := I) (M := M) g α
      (h1ComplToLp (I := I) (M := M) g u_h) :
      Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α))) : EuclN → ℝ)
  fChart :=
    ((chartPushedRawLpFromLp (I := I) (M := M) g α
      (leibnizCompensatedSource (I := I) (M := M) g α u_h hu_h) :
      Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α))) : EuclN → ℝ)
  weakPartial := fun i =>
    ((chartPushedWeakPartialLp (I := I) (M := M) g α i
      (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α i) u_h :
      Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α))) : EuclN → ℝ)
  u_chart_memLp_weighted :=
    Lp.memLp (chartPushedLpFromLp (I := I) (M := M) g α
      (h1ComplToLp (I := I) (M := M) g u_h))
  f_chart_memLp_weighted :=
    Lp.memLp (chartPushedRawLpFromLp (I := I) (M := M) g α
      (leibnizCompensatedSource (I := I) (M := M) g α u_h hu_h))
  weak_partial_locally_memLp := fun i K hK hK_in =>
    chartPushedWeakPartialLp_locally_memLp (I := I) (M := M) g α i u_h hK hK_in
  weak_partial_isWeakPartial := fun i => by
    have h_base := hasWeakPartialDeriv_chartPushedWeakPartialLp_on_chartTarget
      (I := I) (M := M) g α i u_h
    intro φ hφ_smooth hφ_cs hφ_support
    have h_id := h_base φ hφ_smooth hφ_cs hφ_support
    have h_coeFn := chartPushedLpFromLp_coeFn (I := I) (M := M) g α
      (h1ComplToLp (I := I) (M := M) g u_h)
    have h_meas : MeasurableSet
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) :=
      (Sobolev.Chart.chartTargetEuclid_isOpen
        (I := I) (M := M) α).measurableSet
    have h_w_abs : (chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α) ≪
        (volume : Measure EuclN).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α) := by
      unfold chartPulledWeightedMeasure
      rw [show ((volume : Measure EuclN).withDensity
          (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α) =
          ((volume : Measure EuclN).restrict
            (Sobolev.Chart.chartTargetEuclid
              (I := I) (M := M) α)).withDensity
            (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
        from MeasureTheory.restrict_withDensity h_meas _]
      exact MeasureTheory.withDensity_absolutelyContinuous _ _
    have h_v_abs_w :
        (volume : Measure EuclN).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α) ≪
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α) := by
      intro A hA
      unfold chartPulledWeightedMeasure at hA
      rw [show ((volume : Measure EuclN).withDensity
          (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α) =
          ((volume : Measure EuclN).restrict
            (Sobolev.Chart.chartTargetEuclid
              (I := I) (M := M) α)).withDensity
            (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
        from MeasureTheory.restrict_withDensity h_meas _] at hA
      rw [MeasureTheory.withDensity_apply_eq_zero'
        (μ := (volume : Measure EuclN).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α))
        (f := fun y : EuclN => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
        (ENNReal.measurable_ofReal.comp_aemeasurable
          ((densityOnEuclid_continuousOn (I := I) g α).aemeasurable h_meas))] at hA
      rw [Measure.restrict_apply' h_meas]
      rw [Measure.restrict_apply' h_meas] at hA
      refine MeasureTheory.measure_mono_null ?_ hA
      intro y ⟨hy_A, hy_chart⟩
      refine ⟨⟨?_, hy_A⟩, hy_chart⟩
      have h_pos : 0 < densityOnEuclid (I := I) g α y :=
        densityOnEuclid_pos (I := I) g α hy_chart
      exact (ENNReal.ofReal_pos.mpr h_pos).ne'
    have h_coeFn_vol : ((chartPushedLpFromLp (I := I) (M := M) g α
          (h1ComplToLp (I := I) (M := M) g u_h)) : EuclN → ℝ) =ᵐ[
          (volume : Measure EuclN).restrict
            (Sobolev.Chart.chartTargetEuclid
              (I := I) (M := M) α)]
        Sobolev.Chart.chartPushed (I := I) (M := M)
          (chartAtlasPOU I M) α
          ((h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ) :=
      h_v_abs_w.ae_le h_coeFn
    have h_int_eq :
        ∫ x in Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α,
          ((chartPushedLpFromLp (I := I) (M := M) g α
            (h1ComplToLp (I := I) (M := M) g u_h) :
            Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
              (Sobolev.Chart.chartTargetEuclid
                (I := I) (M := M) α))) : EuclN → ℝ) x *
            (fderiv ℝ φ x) (EuclideanSpace.single i 1) =
        ∫ x in Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α,
          Sobolev.Chart.chartPushed (I := I) (M := M)
            (chartAtlasPOU I M) α
            ((h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ) x *
            (fderiv ℝ φ x) (EuclideanSpace.single i 1) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [h_coeFn_vol] with x hx
      rw [hx]
    change ∫ x in Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α,
        ((chartPushedLpFromLp (I := I) (M := M) g α
          (h1ComplToLp (I := I) (M := M) g u_h) :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (Sobolev.Chart.chartTargetEuclid
              (I := I) (M := M) α))) : EuclN → ℝ) x *
          (fderiv ℝ φ x) (EuclideanSpace.single i 1) =
      -∫ x in Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
        ((chartPushedWeakPartialLp (I := I) (M := M) g α i
          (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α i) u_h :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (Sobolev.Chart.chartTargetEuclid
              (I := I) (M := M) α))) : EuclN → ℝ) x * φ x
    rw [h_int_eq]
    exact h_id
  variational_identity := by
    intro ψ hψ hψ_cs hψ_support
    have h_integralForm := laplacianDomain_variational_identity
      (I := I) (M := M) g α hu_h hψ hψ_cs hψ_support
    have h_partA := chartPulledIntegralCLM_density_ψ_eq_setIntegral
      (I := I) (M := M) g α hψ hψ_cs hψ_support
      (leibnizCompensatedSource (I := I) (M := M) g α u_h hu_h)
    rw [h_partA] at h_integralForm
    have h_u_chart_ae := chartPushedLpFromLp_coeFn (I := I) (M := M) g α
      (h1ComplToLp (I := I) (M := M) g u_h)
    rw [setIntegral_density_eq_integral_weighted (I := I) (M := M) g α
      (Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α
        ((h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)) ψ] at h_integralForm
    have h_LHS_mass_eq :
        ∫ y in Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α,
          Sobolev.Chart.chartPushed (I := I) (M := M)
            (chartAtlasPOU I M) α
            ((h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ) y * ψ y
          ∂(chartPulledWeightedMeasure (I := I) g α) =
        ∫ y in Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α,
          ((chartPushedLpFromLp (I := I) (M := M) g α
            (h1ComplToLp (I := I) (M := M) g u_h) :
            Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
              (Sobolev.Chart.chartTargetEuclid
                (I := I) (M := M) α))) : EuclN → ℝ) y * ψ y
          ∂(chartPulledWeightedMeasure (I := I) g α) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [h_u_chart_ae] with y hy
      rw [hy]
    rw [h_LHS_mass_eq] at h_integralForm
    rw [← setIntegral_density_eq_integral_weighted (I := I) (M := M) g α
      ((chartPushedLpFromLp (I := I) (M := M) g α
        (h1ComplToLp (I := I) (M := M) g u_h) :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α))) : EuclN → ℝ) ψ] at h_integralForm
    exact h_integralForm

lemma chartBilinearH1ComplData_of_laplacianDomain_f_chart_def
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α hu_h).fChart =
      ((chartPushedRawLpFromLp (I := I) (M := M) g α
        (leibnizCompensatedSource (I := I) (M := M) g α u_h hu_h) :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α))) : EuclN → ℝ) := rfl

end

end LaplacianDomainChartData
end Laplacian
end Analysis
end CalabiYau
