-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Geometry/Metric/TensorInner/Tensor0S/Bundle/SectionRegularity.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Manifold.Tensor.RSTensor.Defs
public import CalabiYau.Geometry.Riemannian.TensorInner.Tangent.Riemannian
public import CalabiYau.Geometry.Riemannian.Metric.PointwiseInner.Defs
public import CalabiYau.Geometry.Riemannian.Metric.PointwiseInner.Algebra
public import CalabiYau.Geometry.Riemannian.Metric.PointwiseInner.DualMetric
public import CalabiYau.Geometry.Riemannian.Metric.Coordinates.ChartGram
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Topology.VectorBundle.Riemannian
public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import CalabiYau.Mathlib.Analysis.InnerProductSpace.Coercivity
public import CalabiYau.Geometry.Riemannian.TensorInner.Tensor0S.Chart.Inner
public import CalabiYau.Geometry.Riemannian.TensorInner.Tensor0S.Coordinates.InnerProduct

@[expose] public section


noncomputable section

open Bundle Set IsManifold ContinuousLinearMap Bornology
open scoped Manifold Topology Bundle ContDiff BigOperators Matrix

namespace CalabiYau
namespace Tensor
namespace Tensor0SRiemannian

open CalabiYau.L2
open CalabiYau.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable {n : ℕ}

private local instance tensor0SModelNormedSpace_local {s : ℕ} :
    NormedSpace ℝ (Tensor0SModel s ℝ E) :=
  Tensor0SBundle.tensor0SModelNormedSpace s

private local instance tensor0SModelNormedAddCommGroup_local {s : ℕ} :
    NormedAddCommGroup (Tensor0SModel s ℝ E) := inferInstance

lemma chartTensorInnerPointwise_0s_contMDiffOn_smooth_args
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∀ (s : ℕ)
    (T S : M → ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
    (_hT : ∀ φ : Fin s → Fin (Module.finrank ℝ E),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => (T b) (fun k : Fin s => (CalabiYau.Tensor.Coordinates.chartModelBasis E) (φ k)))
        (trivializationAt E (TangentSpace I) α).baseSet)
    (_hS : ∀ φ : Fin s → Fin (Module.finrank ℝ E),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => (S b) (fun k : Fin s => (CalabiYau.Tensor.Coordinates.chartModelBasis E) (φ k)))
        (trivializationAt E (TangentSpace I) α).baseSet),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M =>
          chartTensorInnerPointwise0s (I := I) (M := M) s g α b (T b) (S b))
        (trivializationAt E (TangentSpace I) α).baseSet := by
  intro s
  induction s with
  | zero =>
      intro T S hT hS
      have heq : (fun b : M =>
          chartTensorInnerPointwise0s (I := I) (M := M) 0 g α b (T b) (S b)) =
          fun b : M =>
            ((T b) (fun i => Fin.elim0 i)) * ((S b) (fun i => Fin.elim0 i)) := by
        funext b
        rw [chartTensorInnerPointwise_0s_zero]
      rw [heq]
      have hT0 := hT (fun i : Fin 0 => Fin.elim0 i)
      have hS0 := hS (fun i : Fin 0 => Fin.elim0 i)
      have hempty :
          (fun k : Fin 0 => (CalabiYau.Tensor.Coordinates.chartModelBasis E) ((fun i : Fin 0 => Fin.elim0 i) k))
            = (fun i : Fin 0 => (Fin.elim0 i : E)) := by
        funext i
        exact Fin.elim0 i
      have hT_smooth :
          ContMDiffOn I 𝓘(ℝ) ∞
            (fun b : M => (T b) (fun i => Fin.elim0 i))
            (trivializationAt E (TangentSpace I) α).baseSet := by
        have : (fun b : M => (T b) (fun i : Fin 0 => Fin.elim0 i)) =
            (fun b : M => (T b)
              (fun k : Fin 0 =>
                (CalabiYau.Tensor.Coordinates.chartModelBasis E) ((fun i : Fin 0 => Fin.elim0 i) k))) := by
          funext b
          congr 1
          rw [hempty]
        rw [this]
        exact hT0
      have hS_smooth :
          ContMDiffOn I 𝓘(ℝ) ∞
            (fun b : M => (S b) (fun i => Fin.elim0 i))
            (trivializationAt E (TangentSpace I) α).baseSet := by
        have : (fun b : M => (S b) (fun i : Fin 0 => Fin.elim0 i)) =
            (fun b : M => (S b)
              (fun k : Fin 0 =>
                (CalabiYau.Tensor.Coordinates.chartModelBasis E) ((fun i : Fin 0 => Fin.elim0 i) k))) := by
          funext b
          congr 1
          rw [hempty]
        rw [this]
        exact hS0
      exact hT_smooth.mul hS_smooth
  | succ s ih =>
      intro T S hT hS
      have heq : (fun b : M =>
          chartTensorInnerPointwise0s (I := I) (M := M) (s + 1) g α b (T b) (S b)) =
          fun b : M =>
            ∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b)⁻¹ i j *
                  chartTensorInnerPointwise0s (I := I) (M := M) s g α b
                    ((T b).curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i))
                    ((S b).curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j)) := by
        funext b
        rw [chartTensorInnerPointwise_0s_succ]
      rw [heq]
      refine contMDiffOn_finsetSum (fun i _ => ?_)
      refine contMDiffOn_finsetSum (fun j _ => ?_)
      refine ContMDiffOn.mul ?_ ?_
      · exact chartGramMatrix_inv_entry_contMDiffOn (I := I) g α i j
      · refine ih
            (fun b : M => (T b).curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i))
            (fun b : M => (S b).curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j))
            ?_ ?_
        · intro ψ
          set ψ' : Fin (s + 1) → Fin (Module.finrank ℝ E) :=
            Fin.cons (α := fun _ => Fin (Module.finrank ℝ E)) i ψ with hψ'
          have hψ'_zero : ψ' 0 = i := by
            simp [hψ']
          have hψ'_succ : ∀ k : Fin s, ψ' k.succ = ψ k := by
            intro k
            simp [hψ']
          have heq' :
              (fun b : M => ((T b).curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i))
                  (fun k : Fin s => (CalabiYau.Tensor.Coordinates.chartModelBasis E) (ψ k)))
                = fun b : M =>
                    (T b) (fun k : Fin (s + 1) =>
                      (CalabiYau.Tensor.Coordinates.chartModelBasis E) (ψ' k)) := by
            funext b
            rw [ContinuousMultilinearMap.curryLeft_apply]
            congr 1
            funext k
            refine Fin.cases ?_ ?_ k
            · rw [hψ'_zero]
              simp
            · intro k'
              rw [hψ'_succ k']
              simp
          rw [heq']
          exact hT ψ'
        · intro ψ
          set ψ' : Fin (s + 1) → Fin (Module.finrank ℝ E) :=
            Fin.cons (α := fun _ => Fin (Module.finrank ℝ E)) j ψ with hψ'
          have hψ'_zero : ψ' 0 = j := by
            simp [hψ']
          have hψ'_succ : ∀ k : Fin s, ψ' k.succ = ψ k := by
            intro k
            simp [hψ']
          have heq' :
              (fun b : M => ((S b).curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j))
                  (fun k : Fin s => (CalabiYau.Tensor.Coordinates.chartModelBasis E) (ψ k)))
                = fun b : M =>
                    (S b) (fun k : Fin (s + 1) =>
                      (CalabiYau.Tensor.Coordinates.chartModelBasis E) (ψ' k)) := by
            funext b
            rw [ContinuousMultilinearMap.curryLeft_apply]
            congr 1
            funext k
            refine Fin.cases ?_ ?_ k
            · rw [hψ'_zero]; simp
            · intro k'
              rw [hψ'_succ k']; simp
          rw [heq']
          exact hS ψ'

end Tensor0SRiemannian
end Tensor
end CalabiYau

end
