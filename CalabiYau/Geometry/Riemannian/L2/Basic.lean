-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Integration/L2/Basic.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Riemannian.Volume.Properties
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Topology.Algebra.Support

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal

namespace CalabiYau.L2

open CalabiYau.RiemannianVolume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem integrable_of_continuous_compactSpace
    [T2Space M] [CompactSpace M]
    {F : Type*} [NormedAddCommGroup F]
    (g : SmoothRiemannianMetric I M)
    {f : M → F} (hf : Continuous f) :
    MeasureTheory.Integrable f (riemannianVolumeMeasure (I := I) (M := M) g) :=
  haveI : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
theorem lpNorm_two_sq_eq_integral_sq
    {μ : MeasureTheory.Measure M} {f : M → ℝ}
    (hf : MeasureTheory.AEStronglyMeasurable f μ) :
    MeasureTheory.lpNorm f 2 μ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
    (by norm_num) (by norm_num) hf]
  norm_num only [ENNReal.toReal_ofNat]
  have hnonneg : 0 ≤ ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ :=
    MeasureTheory.integral_nonneg (fun x => by positivity)
  rw [← Real.sqrt_eq_rpow]
  rw [sq, Real.mul_self_sqrt hnonneg]
  congr 1
  funext x
  rw [Real.norm_eq_abs]
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact sq_abs (f x)

end CalabiYau.L2
