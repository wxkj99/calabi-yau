-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Integration/L2/Pairing/Defs.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Riemannian.Volume.Properties
public import CalabiYau.Geometry.Riemannian.L2.Basic
public import CalabiYau.Geometry.Riemannian.Metric.PointwiseInner.Defs
public import CalabiYau.Geometry.Riemannian.Metric.PointwiseInner.DualMetric
public import CalabiYau.Geometry.Riemannian.Metric.PointwiseInner.Algebra
public import CalabiYau.Geometry.Manifold.Tensor.RSTensor.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

noncomputable section

open Manifold MeasureTheory Set Filter Bundle CalabiYau.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix

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

def MemL2
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : M → TensorRSModel r s ℝ E) : Prop :=
  MeasureTheory.Integrable
    (fun x => tensorInnerPointwise (I := I) (M := M) g r s x (S x) (S x))
    (riemannianVolumeMeasure (I := I) (M := M) g)

theorem MemL2.zero
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    MemL2 (I := I) (M := M) g r s (fun _ : M => (0 : TensorRSModel r s ℝ E)) := by
  unfold MemL2
  have hzero :
      (fun x : M => tensorInnerPointwise (I := I) (M := M) g r s x
          ((fun _ : M => (0 : TensorRSModel r s ℝ E)) x)
          ((fun _ : M => (0 : TensorRSModel r s ℝ E)) x))
        = (fun _ : M => (0 : ℝ)) := by
    funext x
    exact tensorInnerPointwise_zero_left (I := I) (M := M) g r s x 0
  rw [hzero]
  exact MeasureTheory.integrable_zero M ℝ
    (riemannianVolumeMeasure (I := I) (M := M) g)

end CalabiYau.L2

end
