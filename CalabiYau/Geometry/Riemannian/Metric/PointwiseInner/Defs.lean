-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Geometry/Metric/PointwiseInner/Defs.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Riemannian.Metric.PointwiseInner.DualMetric
public import CalabiYau.Geometry.Manifold.Tensor.RSTensor.Defs
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

noncomputable section

open Manifold Set Filter Bundle CalabiYau.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace CalabiYau.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable def covariantTensorInnerPointwise :
    (s : ℕ) → SmoothRiemannianMetric I M → (x : M) →
      ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ →
      ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ → ℝ
  | 0, _g, _x, S, T =>
      S (fun i => Fin.elim0 i) * T (fun i => Fin.elim0 i)
  | s + 1, g, x, S, T =>
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
          covariantTensorInnerPointwise s g x
            (S.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i))
            (T.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j))

lemma tensorInnerPointwise_0s_zero_arity
    (g : SmoothRiemannianMetric I M) (x : M)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ) :
    covariantTensorInnerPointwise (I := I) (M := M) 0 g x S T =
      S (fun i => Fin.elim0 i) * T (fun i => Fin.elim0 i) := rfl

lemma tensorInnerPointwise_0s_succ
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ) :
    covariantTensorInnerPointwise (I := I) (M := M) (s + 1) g x S T =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
          covariantTensorInnerPointwise (I := I) (M := M) s g x
            (S.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i))
            (T.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j)) := rfl

noncomputable def tensorInnerPointwise
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (S T : TensorRSModel r s ℝ E) : ℝ :=
  covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
    (lowerAllUpperIndices (I := I) (M := M) g r s x S)
    (lowerAllUpperIndices (I := I) (M := M) g r s x T)

noncomputable def tensorPointwiseNorm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (S : TensorRSModel r s ℝ E) : ℝ :=
  Real.sqrt (tensorInnerPointwise (I := I) (M := M) g r s x S S)

end CalabiYau.L2

end
