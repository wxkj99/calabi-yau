-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Geometry/Metric/TensorInner/Tensor0S/Chart/Inner.lean
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
public import CalabiYau.Geometry.Riemannian.Operator.Gradient.Basic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
open CalabiYau.Riemannian

noncomputable section

open Bundle Set IsManifold ContinuousLinearMap Bornology
open scoped Manifold Topology Bundle ContDiff BigOperators Matrix

namespace CalabiYau
namespace Tensor
namespace Tensor0SRiemannian

open CalabiYau.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private lemma chartGramMatrix_adjugate_entry_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b).adjugate i j)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have hexp :
      (fun b : M => (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b).adjugate i j)
        = (fun b : M =>
            ((CalabiYau.Tensor.Coordinates.chartGramMatrix g α b).updateRow j (Pi.single i 1)).det) := by
    funext b
    rw [Matrix.adjugate_apply]
  rw [hexp]
  have hexp2 :
      (fun b : M =>
          ((CalabiYau.Tensor.Coordinates.chartGramMatrix g α b).updateRow j (Pi.single i 1)).det)
        = (fun b : M =>
            ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
              (Equiv.Perm.sign σ : ℝ) *
                ∏ k,
                  ((CalabiYau.Tensor.Coordinates.chartGramMatrix g α b).updateRow j (Pi.single i 1))
                    (σ k) k) := by
    funext b
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp2]
  refine contMDiffOn_finsetSum (fun σ _ => ?_)
  refine ContMDiffOn.mul (contMDiffOn_const) ?_
  refine contMDiffOn_finsetProd (fun k _ => ?_)
  by_cases hσkj : σ k = j
  · have heq :
        (fun b : M =>
            ((CalabiYau.Tensor.Coordinates.chartGramMatrix g α b).updateRow j (Pi.single i 1)) (σ k) k)
          = (fun _ : M => (Pi.single i 1 : Fin (Module.finrank ℝ E) → ℝ) k) := by
      funext b
      rw [hσkj, Matrix.updateRow_self]
    rw [heq]
    exact contMDiffOn_const
  · have heq :
        (fun b : M =>
            ((CalabiYau.Tensor.Coordinates.chartGramMatrix g α b).updateRow j (Pi.single i 1)) (σ k) k)
          = (fun b : M => CalabiYau.Tensor.Coordinates.chartGramMatrix g α b (σ k) k) := by
      funext b
      rw [Matrix.updateRow_ne hσkj]
    rw [heq]
    exact CalabiYau.Tensor.Coordinates.chartGramMatrix_entry_contMDiffOn (I := I) g α (σ k) k

lemma chartGramMatrix_inv_entry_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b)⁻¹ i j)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  have hexp :
      (fun b : M => (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b)⁻¹ i j)
        = (fun b : M => (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b).det⁻¹ *
              (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b).adjugate i j) := by
    funext b
    rw [Matrix.inv_def]
    simp [Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [hexp]
  intro b hb
  have hdet := CalabiYau.Tensor.Coordinates.chartGramMatrix_det_contMDiffOn (I := I) g α b hb
  have hadj := chartGramMatrix_adjugate_entry_contMDiffOn (I := I) g α i j b hb
  have hpos : 0 < (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b).det :=
    CalabiYau.Tensor.Coordinates.chartGramMatrix_det_pos (I := I) g α hb
  have hpos_ne : (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b).det ≠ 0 := ne_of_gt hpos
  have hinv : ContMDiffWithinAt I 𝓘(ℝ) ∞
      (fun b' : M => (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b').det⁻¹)
      (trivializationAt E (TangentSpace I) α).baseSet b :=
    ContMDiffWithinAt.inv₀ hdet hpos_ne
  exact hinv.mul hadj

noncomputable def chartTensorInnerPointwise0s :
    (s : ℕ) → SmoothRiemannianMetric I M → (α : M) → (b : M) →
      Tensor0SModel s ℝ E →
      Tensor0SModel s ℝ E → ℝ
  | 0, _g, _α, _b, S, T =>
      S (fun i => Fin.elim0 i) * T (fun i => Fin.elim0 i)
  | s + 1, g, α, b, S, T =>
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b)⁻¹ i j *
          chartTensorInnerPointwise0s s g α b
            (S.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i))
            (T.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j))

lemma chartTensorInnerPointwise_0s_zero
    (g : SmoothRiemannianMetric I M) (α b : M)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ) :
    chartTensorInnerPointwise0s (I := I) (M := M) 0 g α b S T =
      S (fun i => Fin.elim0 i) * T (fun i => Fin.elim0 i) := rfl

lemma chartTensorInnerPointwise_0s_succ
    (g : SmoothRiemannianMetric I M) (α b : M) (s : ℕ)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ) :
    chartTensorInnerPointwise0s (I := I) (M := M) (s + 1) g α b S T =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b)⁻¹ i j *
          chartTensorInnerPointwise0s (I := I) (M := M) s g α b
            (S.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i))
            (T.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j)) := rfl

lemma chartTensorInnerPointwise_0s_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∀ (s : ℕ) (S T : Tensor0SModel s ℝ E),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M =>
          chartTensorInnerPointwise0s (I := I) (M := M) s g α b S T)
        (trivializationAt E (TangentSpace I) α).baseSet := by
  intro s
  induction s with
  | zero =>
      intro S T
      have heq :
          (fun b : M =>
              chartTensorInnerPointwise0s (I := I) (M := M) 0 g α b S T)
            = fun _ : M =>
              S (fun i => Fin.elim0 i) * T (fun i => Fin.elim0 i) := by
        funext b
        rw [chartTensorInnerPointwise_0s_zero]
      rw [heq]
      exact contMDiffOn_const
  | succ s ih =>
      intro S T
      have heq :
          (fun b : M =>
              chartTensorInnerPointwise0s (I := I) (M := M) (s + 1) g α b S T)
            = fun b : M =>
              ∑ i : Fin (Module.finrank ℝ E),
                ∑ j : Fin (Module.finrank ℝ E),
                  (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b)⁻¹ i j *
                    chartTensorInnerPointwise0s (I := I) (M := M) s g α b
                      (S.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i))
                      (T.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j)) := by
        funext b
        rw [chartTensorInnerPointwise_0s_succ]
      rw [heq]
      refine contMDiffOn_finsetSum (fun i _ => ?_)
      refine contMDiffOn_finsetSum (fun j _ => ?_)
      refine ContMDiffOn.mul ?_ ?_
      · exact chartGramMatrix_inv_entry_contMDiffOn (I := I) g α i j
      · exact ih
          (S.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i))
          (T.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j))

lemma chartTensorInnerPointwise_0s_add_left
    (g : SmoothRiemannianMetric I M) (α b : M) (s : ℕ)
    (S₁ S₂ T : Tensor0SModel s ℝ E) :
    chartTensorInnerPointwise0s (I := I) (M := M) s g α b (S₁ + S₂) T =
      chartTensorInnerPointwise0s (I := I) (M := M) s g α b S₁ T +
        chartTensorInnerPointwise0s (I := I) (M := M) s g α b S₂ T := by
  induction s with
  | zero =>
      change (S₁ + S₂) _ * T _ = S₁ _ * T _ + S₂ _ * T _
      rw [add_apply]; ring
  | succ s ih =>
      rw [chartTensorInnerPointwise_0s_succ,
          chartTensorInnerPointwise_0s_succ,
          chartTensorInnerPointwise_0s_succ]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j _
      have hcurry :
          (S₁ + S₂).curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) =
            S₁.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) +
              S₂.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) := by
        ext m
        simp [ContinuousMultilinearMap.curryLeft_apply,
              add_apply]
      rw [hcurry, ih]
      ring

lemma chartTensorInnerPointwise_0s_smul_left
    (g : SmoothRiemannianMetric I M) (α b : M) (s : ℕ)
    (c : ℝ) (S T : Tensor0SModel s ℝ E) :
    chartTensorInnerPointwise0s (I := I) (M := M) s g α b (c • S) T =
      c * chartTensorInnerPointwise0s (I := I) (M := M) s g α b S T := by
  induction s with
  | zero =>
      change (c • S) _ * T _ = c * (S _ * T _)
      rw [smul_apply, smul_eq_mul]; ring
  | succ s ih =>
      rw [chartTensorInnerPointwise_0s_succ,
          chartTensorInnerPointwise_0s_succ,
          Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      have hcurry :
          (c • S).curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) =
            c • S.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) := by
        ext m
        simp [ContinuousMultilinearMap.curryLeft_apply,
              smul_apply]
      rw [hcurry, ih]
      ring

lemma chartTensorInnerPointwise_0s_add_right
    (g : SmoothRiemannianMetric I M) (α b : M) (s : ℕ)
    (S T₁ T₂ : Tensor0SModel s ℝ E) :
    chartTensorInnerPointwise0s (I := I) (M := M) s g α b S (T₁ + T₂) =
      chartTensorInnerPointwise0s (I := I) (M := M) s g α b S T₁ +
        chartTensorInnerPointwise0s (I := I) (M := M) s g α b S T₂ := by
  induction s with
  | zero =>
      change S _ * (T₁ + T₂) _ = S _ * T₁ _ + S _ * T₂ _
      rw [add_apply]; ring
  | succ s ih =>
      rw [chartTensorInnerPointwise_0s_succ,
          chartTensorInnerPointwise_0s_succ,
          chartTensorInnerPointwise_0s_succ]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j _
      have hcurry :
          (T₁ + T₂).curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j) =
            T₁.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j) +
              T₂.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j) := by
        ext m
        simp [ContinuousMultilinearMap.curryLeft_apply,
              add_apply]
      rw [hcurry, ih]
      ring

lemma chartTensorInnerPointwise_0s_smul_right
    (g : SmoothRiemannianMetric I M) (α b : M) (s : ℕ)
    (c : ℝ) (S T : Tensor0SModel s ℝ E) :
    chartTensorInnerPointwise0s (I := I) (M := M) s g α b S (c • T) =
      c * chartTensorInnerPointwise0s (I := I) (M := M) s g α b S T := by
  induction s with
  | zero =>
      change S _ * (c • T) _ = c * (S _ * T _)
      rw [smul_apply, smul_eq_mul]; ring
  | succ s ih =>
      rw [chartTensorInnerPointwise_0s_succ,
          chartTensorInnerPointwise_0s_succ,
          Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      have hcurry :
          (c • T).curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j) =
            c • T.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j) := by
        ext m
        simp [ContinuousMultilinearMap.curryLeft_apply,
              smul_apply]
      rw [hcurry, ih]
      ring

end Tensor0SRiemannian
end Tensor
end CalabiYau

end
