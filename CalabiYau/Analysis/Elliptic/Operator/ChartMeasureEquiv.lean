-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Operator/ChartMeasureEquiv.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.MetricExtension
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Global.Support
public import CalabiYau.Geometry.Riemannian.Volume.Family.Basic
public import CalabiYau.Geometry.Riemannian.Volume.Chart.Density
public import CalabiYau.Geometry.Riemannian.Volume.Invariance
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff ENNReal Matrix BigOperators

namespace CalabiYau.Laplacian
namespace ChartMeasureEquiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Laplacian.MetricExtension

local instance : MeasurableSpace M := borel M
local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem integral_riemannianVolumeMeasure_eq_modelHaar_chartTarget_of_hasCompactSupport
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf_cont : Continuous f) (hf_cs : HasCompactSupport f)
    (hf_support : tsupport f ⊆ (chartAt H α).source) :
    ∫ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ y in (extChartAt I α).target,
        chartDensity g α ((extChartAt I α).symm y) *
          f ((extChartAt I α).symm y)
        ∂(modelHaar (E := E)) := by
  classical
  have hf_int := integrable_chartLocalMeasure_of_compactSupport_subset_chartSource
    (I := I) (M := M) g α hf_cont hf_cs hf_support
  have h_step1 :=
    (integrable_riemannianVolumeMeasure_and_integral_eq_chartLocalMeasure
      (I := I) (M := M) g α hf_int hf_cs hf_support).2
  rw [h_step1]
  exact integral_chartLocalMeasure (I := I) (M := M) g α f hf_cont.measurable

private def toEuclideanMeasurableEquiv :
    E ≃ᵐ EuclN :=
  (toEuclidean (E := E)).toHomeomorph.toMeasurableEquiv

@[simp] private lemma toEuclideanMeasurableEquiv_apply (y : E) :
    toEuclideanMeasurableEquiv (E := E) y = toEuclidean y := rfl

@[simp] private lemma toEuclideanMeasurableEquiv_symm_apply (y : EuclN) :
    (toEuclideanMeasurableEquiv (E := E)).symm y = (toEuclidean (E := E)).symm y := rfl

omit [IsManifold I ∞ M] in
private lemma toEuclidean_mem_chartTargetEuclid_iff
    (α : M) (y : E) :
    toEuclidean (E := E) y ∈ chartTargetEuclid (I := I) (M := M) α ↔
      y ∈ (extChartAt I α).target := by
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · rcases hy with ⟨z, hz_target, hz_eq⟩
    have hyz : y = z := ((toEuclidean (E := E)).injective hz_eq).symm
    rw [hyz]; exact hz_target
  · exact ⟨y, hy, rfl⟩

omit [IsManifold I ∞ M] in
private lemma chartTargetEuclid_measurableSet (α : M) :
    MeasurableSet (chartTargetEuclid (I := I) (M := M) α) := by
  have htarget_meas : MeasurableSet (extChartAt I α).target :=
    measurableSet_extChartAt_target (I := I) α
  change MeasurableSet (toEuclidean '' (extChartAt I α).target)
  exact (toEuclideanMeasurableEquiv (E := E)).measurableEmbedding.measurableSet_image.mpr
    htarget_meas

theorem integral_riemannianVolumeMeasure_eq_euclidean_chartTarget_of_hasCompactSupport
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf_cont : Continuous f) (hf_cs : HasCompactSupport f)
    (hf_support : tsupport f ⊆ (chartAt H α).source) :
    ∫ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        ∂(MeasureTheory.Measure.map (toEuclidean : E → EuclN)
            (modelHaar (E := E))) := by
  classical
  rw [integral_riemannianVolumeMeasure_eq_modelHaar_chartTarget_of_hasCompactSupport
    (I := I) (M := M) g α hf_cont hf_cs hf_support]
  have htarget_meas : MeasurableSet (extChartAt I α).target :=
    measurableSet_extChartAt_target (I := I) α
  have hctE_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_measurableSet (I := I) (M := M) α
  rw [show
      (∫ y in (extChartAt I α).target,
          chartDensity g α ((extChartAt I α).symm y) *
            f ((extChartAt I α).symm y)
          ∂(modelHaar (E := E))) =
        ∫ y, (extChartAt I α).target.indicator
              (fun y' : E =>
                chartDensity g α ((extChartAt I α).symm y') *
                  f ((extChartAt I α).symm y')) y
            ∂(modelHaar (E := E)) from
        (MeasureTheory.integral_indicator htarget_meas).symm]
  rw [show
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          ∂(MeasureTheory.Measure.map (toEuclidean : E → EuclN)
              (modelHaar (E := E)))) =
        ∫ y',
            (chartTargetEuclid (I := I) (M := M) α).indicator
              (fun y'' : EuclN =>
                densityOnEuclid (I := I) g α y'' *
                  f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y''))) y'
            ∂(MeasureTheory.Measure.map (toEuclidean : E → EuclN)
                (modelHaar (E := E))) from
        (MeasureTheory.integral_indicator hctE_meas).symm]
  rw [show
      (∫ y',
          (chartTargetEuclid (I := I) (M := M) α).indicator
            (fun y'' : EuclN =>
              densityOnEuclid (I := I) g α y'' *
                f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y''))) y'
          ∂(MeasureTheory.Measure.map (toEuclidean : E → EuclN)
              (modelHaar (E := E)))) =
        ∫ y,
          (chartTargetEuclid (I := I) (M := M) α).indicator
            (fun y'' : EuclN =>
              densityOnEuclid (I := I) g α y'' *
                f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y'')))
            (toEuclideanMeasurableEquiv (E := E) y)
          ∂(modelHaar (E := E)) from ?_]
  · refine MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun y => ?_))
    simp only
    by_cases hy : y ∈ (extChartAt I α).target
    · have hctE_y : toEuclideanMeasurableEquiv (E := E) y ∈
          chartTargetEuclid (I := I) (M := M) α :=
        (toEuclidean_mem_chartTargetEuclid_iff (I := I) (M := M) α y).mpr hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hctE_y]
      have h_symm_apply :
          (toEuclidean (E := E)).symm (toEuclidean y) = y :=
        (toEuclidean (E := E)).symm_apply_apply y
      change chartDensity g α ((extChartAt I α).symm y) *
          f ((extChartAt I α).symm y) =
        densityOnEuclid (I := I) g α (toEuclidean y) *
          f ((extChartAt I α).symm
            ((toEuclidean (E := E)).symm (toEuclidean y)))
      rw [h_symm_apply]
      change chartDensity g α ((extChartAt I α).symm y) *
          f ((extChartAt I α).symm y) =
        chartDensity g α ((extChartAt I α).symm
            ((toEuclidean (E := E)).symm (toEuclidean y))) *
          f ((extChartAt I α).symm y)
      rw [h_symm_apply]
    · have hctE_off : toEuclideanMeasurableEquiv (E := E) y ∉
          chartTargetEuclid (I := I) (M := M) α := by
        intro hcontra
        exact hy ((toEuclidean_mem_chartTargetEuclid_iff (I := I) (M := M) α y).mp hcontra)
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hctE_off]
  · exact MeasureTheory.integral_map_equiv
      (μ := modelHaar (E := E))
      (e := toEuclideanMeasurableEquiv (E := E))
      (f := fun y'' : EuclN =>
        (chartTargetEuclid (I := I) (M := M) α).indicator
          (fun y''' : EuclN =>
            densityOnEuclid (I := I) g α y''' *
              f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y'''))) y'')

theorem integral_riemannianVolumeMeasure_eq_euclidean_chartTarget
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf_cont : Continuous f)
    (hf_support : tsupport f ⊆ (chartAt H α).source) :
    ∫ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        ∂(MeasureTheory.Measure.map (toEuclidean : E → EuclN)
            (modelHaar (E := E))) :=
  integral_riemannianVolumeMeasure_eq_euclidean_chartTarget_of_hasCompactSupport
    (I := I) (M := M) g α hf_cont (HasCompactSupport.of_compactSpace f) hf_support

end ChartMeasureEquiv
end CalabiYau.Laplacian
