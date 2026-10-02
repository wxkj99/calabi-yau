-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Integration/Measure/Family/Decomposition.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Riemannian.Volume.Family.Defs
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Topology.Compactness.LocallyFinite

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open Bundle Manifold Set MeasureTheory Matrix
open scoped Manifold Topology ContDiff ENNReal Matrix BigOperators

namespace CalabiYau.RiemannianVolume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem integral_chart_ae
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (h : M → ℝ)
    (hh_meas : AEStronglyMeasurable h (chartLocalMeasure (I := I) g x₀)) :
    ∫ x, h x ∂(chartLocalMeasure (I := I) g x₀)
      = ∫ y in (extChartAt I x₀).target,
          chartDensity g x₀ ((extChartAt I x₀).symm y) *
            h ((extChartAt I x₀).symm y)
          ∂(modelHaar (E := E)) := by
  have htarget_meas : MeasurableSet (extChartAt I x₀).target :=
    measurableSet_extChartAt_target (I := I) x₀
  set μ₀ : MeasureTheory.Measure E :=
    (modelHaar (E := E)).restrict (extChartAt I x₀).target with hμ₀
  set w : E → ℝ≥0∞ :=
    fun y => ENNReal.ofReal
      (chartDensity g x₀ ((extChartAt I x₀).symm y)) with hw
  set μ₁ : MeasureTheory.Measure E := μ₀.withDensity w with hμ₁
  have h_unfold :
      chartLocalMeasure (I := I) g x₀ =
        MeasureTheory.Measure.map (extChartAt I x₀).symm μ₁ := rfl
  have hh_map : AEStronglyMeasurable h
      (MeasureTheory.Measure.map (extChartAt I x₀).symm μ₁) := by
    rw [← h_unfold]
    exact hh_meas
  rw [h_unfold]
  have haem_symm : AEMeasurable ((extChartAt I x₀).symm) μ₁ := by
    have haem_base : AEMeasurable ((extChartAt I x₀).symm) μ₀ :=
      aemeasurable_extChartAt_symm_restrict_target (I := I) (E := E) x₀
    have hac : μ₁ ≪ μ₀ := by
      simpa [hμ₁] using MeasureTheory.withDensity_absolutelyContinuous (μ := μ₀) w
    exact haem_base.mono_ac hac
  have h_integral_map :
      ∫ x, h x ∂(MeasureTheory.Measure.map (extChartAt I x₀).symm μ₁)
        = ∫ y, h ((extChartAt I x₀).symm y) ∂μ₁ := by
    exact MeasureTheory.integral_map haem_symm hh_map
  rw [h_integral_map]
  have hwd_aem : AEMeasurable w μ₀ :=
    aemeasurable_chartDensity_symm_pullback (I := I) g x₀
  have hw_lt_top : ∀ᵐ y ∂μ₀, w y < (⊤ : ℝ≥0∞) := by
    refine Filter.Eventually.of_forall (fun y => ?_)
    simp [hw]
  have h_withDensity :
      ∫ y, h ((extChartAt I x₀).symm y) ∂μ₁
        = ∫ y, (w y).toReal • h ((extChartAt I x₀).symm y) ∂μ₀ := by
    simpa [hμ₁] using
      integral_withDensity_eq_integral_toReal_smul₀ (μ := μ₀)
        (f := w) hwd_aem hw_lt_top
        (g := fun y : E => h ((extChartAt I x₀).symm y))
  rw [h_withDensity]
  have hw_toReal : ∀ y ∈ (extChartAt I x₀).target,
      (w y).toReal = chartDensity g x₀ ((extChartAt I x₀).symm y) := by
    intro y hy
    have hsource : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
      have := (extChartAt I x₀).map_target hy
      rw [extChartAt_source_eq_chartAt_source (I := I)] at this
      exact this
    have hbase : (extChartAt I x₀).symm y ∈
        (trivializationAt E (TangentSpace I) x₀).baseSet := hsource
    have hpos : 0 < chartDensity g x₀ ((extChartAt I x₀).symm y) :=
      chartDensity_pos (I := I) g x₀ hbase
    change (ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y))).toReal
        = chartDensity g x₀ ((extChartAt I x₀).symm y)
    exact ENNReal.toReal_ofReal hpos.le
  have h_restrict :
      ∫ y, (w y).toReal • h ((extChartAt I x₀).symm y) ∂μ₀
        = ∫ y in (extChartAt I x₀).target,
            (w y).toReal • h ((extChartAt I x₀).symm y)
          ∂(modelHaar (E := E)) := by
    simp [hμ₀]
  rw [h_restrict]
  refine setIntegral_congr_fun htarget_meas (fun y hy => ?_)
  rw [hw_toReal y hy, smul_eq_mul]

theorem integral_chartLocalMeasure
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (h : M → ℝ) (hh_meas : Measurable h) :
    ∫ x, h x ∂(chartLocalMeasure (I := I) g x₀)
      = ∫ y in (extChartAt I x₀).target,
          chartDensity g x₀ ((extChartAt I x₀).symm y) *
            h ((extChartAt I x₀).symm y)
          ∂(modelHaar (E := E)) :=
  integral_chart_ae (I := I) g x₀ h hh_meas.aestronglyMeasurable

lemma chartAtlasPOU_finite_support
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] :
    {α : M | (Function.support ((chartAtlasPOU I M) α)).Nonempty}.Finite :=
  LocallyFinite.finite_nonempty_of_compact
    (chartAtlasPOU I M).locallyFinite

noncomputable def chartAtlasPOUFinset
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] : Finset M :=
  (chartAtlasPOU_finite_support (I := I) (M := M)).toFinset

lemma chartAtlasPOU_finset_mem
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] {α : M} :
    α ∈ chartAtlasPOUFinset (I := I) (M := M) ↔
      (Function.support ((chartAtlasPOU I M) α)).Nonempty := by
  unfold chartAtlasPOUFinset
  rw [Set.Finite.mem_toFinset]
  rfl

lemma chartAtlasPOU_weight_zero_of_notMem
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {α : M} (hα : α ∉ chartAtlasPOUFinset (I := I) (M := M)) (x : M) :
    (chartAtlasPOU I M) α x = 0 := by
  rw [chartAtlasPOU_finset_mem] at hα
  rw [Set.not_nonempty_iff_eq_empty] at hα
  by_contra hne
  have hx : x ∈ Function.support ((chartAtlasPOU I M) α) := hne
  rw [hα] at hx
  exact (Set.notMem_empty _) hx

section ChartInvarianceOfTraceTimeDeriv

end ChartInvarianceOfTraceTimeDeriv

end CalabiYau.RiemannianVolume
