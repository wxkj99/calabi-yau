-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Geometry/Metric/TensorInner/Tensor0S/Coordinates/InnerBridge.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Manifold.Tensor.RSTensor.Defs
public import CalabiYau.Geometry.Riemannian.TensorInner.Tangent.Riemannian
public import CalabiYau.Geometry.Riemannian.Metric.PointwiseInner.Defs
public import CalabiYau.Geometry.Riemannian.Metric.PointwiseInner.Algebra
public import CalabiYau.Geometry.Riemannian.Metric.PointwiseInner.DualMetric
public import CalabiYau.Geometry.Riemannian.Metric.Coordinates.ChartGram
public import CalabiYau.Geometry.Riemannian.TensorInner.Tensor0S.Chart.Inner
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


section

variable [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {n : ℕ}

noncomputable def chartTrivializationLinearMap (α : M) (b : M) : E →L[ℝ] E :=
  ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b).comp
    (tangentSpaceModelContinuousLinearEquiv (I := I) b).symm.toContinuousLinearMap

noncomputable def chartTrivializationLinearMapSymm (α : M) (b : M) : E →L[ℝ] E :=
  (tangentSpaceModelContinuousLinearEquiv (I := I) b).toContinuousLinearMap.comp
    ((trivializationAt E (TangentSpace I) α).symmL ℝ b)

end

section

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {n : ℕ}

lemma chartJ_apply (α : M) (b : M) (v : E) :
    chartTrivializationLinearMap (I := I) (M := M) α b v =
      (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
        ((tangentSpaceModelContinuousLinearEquiv (I := I) b).symm v) := rfl

end

section

variable [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {n : ℕ}

private lemma chartJinv_basis (α : M) (b : M)
    (i : Fin (Module.finrank ℝ E)) :
    chartTrivializationLinearMapSymm (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) =
      tangentSpaceModelContinuousLinearEquiv (I := I) b
        (CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b) := by
  unfold CalabiYau.Tensor.Coordinates.chartBasisVecFiber chartTrivializationLinearMapSymm
  rfl

end

section

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {n : ℕ}

lemma chartJ_chartJinv (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) (v : E) :
    chartTrivializationLinearMap (I := I) (M := M) α b
        (chartTrivializationLinearMapSymm (I := I) (M := M) α b v) = v := by
  change (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
      ((tangentSpaceModelContinuousLinearEquiv (I := I) b).symm
        (tangentSpaceModelContinuousLinearEquiv (I := I) b
          ((trivializationAt E (TangentSpace I) α).symmL ℝ b v))) = v
  calc
    _ = (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
        ((trivializationAt E (TangentSpace I) α).symmL ℝ b v) :=
      congrArg ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b)
        ((tangentSpaceModelContinuousLinearEquiv (I := I) b).symm_apply_apply _)
    _ = v := (trivializationAt E (TangentSpace I) α).continuousLinearMapAt_symmL hb v

lemma chartJinv_chartJ (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) (v : E) :
    chartTrivializationLinearMapSymm (I := I) (M := M) α b
        (chartTrivializationLinearMap (I := I) (M := M) α b v) = v := by
  unfold chartTrivializationLinearMap chartTrivializationLinearMapSymm
  simp only [ContinuousLinearMap.comp_apply]
  rw [(trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt hb]
  exact (tangentSpaceModelContinuousLinearEquiv (I := I) b).apply_symm_apply v

lemma chartJinv_chartJ_self (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) (v : E) :
    chartTrivializationLinearMapSymm (I := I) (M := M) α b
        (chartTrivializationLinearMap (I := I) (M := M) α b v) = v :=
  chartJinv_chartJ (I := I) (M := M) α hb v

end

section

variable [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {n : ℕ}

lemma chartGramMatrix_eq_innerJinv
    (g : SmoothRiemannianMetric I M) (α b : M)
    (i j : Fin (Module.finrank ℝ E)) :
    CalabiYau.Tensor.Coordinates.chartGramMatrix g α b i j =
      modelInnerAt (I := I) (M := M) g b
        (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i))
        (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j)) := by
  rw [CalabiYau.Tensor.Coordinates.chartGramMatrix_apply, modelInnerAt_apply]
  rw [chartJinv_basis (I := I) (M := M), chartJinv_basis (I := I) (M := M)]
  simp only [ContinuousLinearEquiv.symm_apply_apply]

end

section

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {n : ℕ}

private lemma curryLeft_sum {n : ℕ} {s : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ)
    (c : Fin n → ℝ) (v : Fin n → E) :
    T.curryLeft (∑ k : Fin n, c k • v k) =
      ∑ k : Fin n, c k • T.curryLeft (v k) := by
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [map_smul]

private lemma compContinuousLinearMap_curryLeft {s : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ)
    (L : E →L[ℝ] E) (w : E) :
    (T.compContinuousLinearMap (fun _ : Fin (s + 1) => L)).curryLeft w =
      (T.curryLeft (L w)).compContinuousLinearMap (fun _ : Fin s => L) := by
  ext m
  simp only [ContinuousMultilinearMap.curryLeft_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hcons_eq : (fun i : Fin (s + 1) => L ((Fin.cons w m : Fin (s + 1) → E) i)) =
      (Fin.cons (L w) (fun i' : Fin s => L (m i')) : Fin (s + 1) → E) := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp
    · intro i'
      simp
  rw [hcons_eq]

end

section

variable [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {n : ℕ}

private lemma tensorInnerPointwise_0s_sum_left
    (g : SmoothRiemannianMetric I M) (b : M) (s : ℕ) {n : ℕ}
    (c : Fin n → ℝ) (S : Fin n → Tensor0SModel s ℝ E)
    (T : Tensor0SModel s ℝ E) :
    covariantTensorInnerPointwise (I := I) (M := M) s g b
        (∑ k : Fin n, c k • S k) T =
      ∑ k : Fin n, c k *
        covariantTensorInnerPointwise (I := I) (M := M) s g b (S k) T := by
  classical
  induction n with
  | zero =>
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      rw [show (0 : Tensor0SModel s ℝ E) =
        (0 : ℝ) • (0 : Tensor0SModel s ℝ E) from
        (zero_smul _ _).symm]
      rw [tensorInnerPointwise_0s_smul_left, zero_mul]
  | succ n ih =>
      have ih_app := ih (fun k : Fin n => c k.succ) (fun k : Fin n => S k.succ)
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      rw [tensorInnerPointwise_0s_add_left, tensorInnerPointwise_0s_smul_left]
      rw [ih_app]

private lemma tensorInnerPointwise_0s_sum_right
    (g : SmoothRiemannianMetric I M) (b : M) (s : ℕ) {n : ℕ}
    (S : Tensor0SModel s ℝ E)
    (d : Fin n → ℝ) (T : Fin n → Tensor0SModel s ℝ E) :
    covariantTensorInnerPointwise (I := I) (M := M) s g b S
        (∑ l : Fin n, d l • T l) =
      ∑ l : Fin n, d l *
        covariantTensorInnerPointwise (I := I) (M := M) s g b S (T l) := by
  classical
  induction n with
  | zero =>
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      rw [show (0 : Tensor0SModel s ℝ E) =
        (0 : ℝ) • (0 : Tensor0SModel s ℝ E) from
        (zero_smul _ _).symm]
      rw [tensorInnerPointwise_0s_smul_right, zero_mul]
  | succ n ih =>
      have ih_app := ih (fun l : Fin n => d l.succ) (fun l : Fin n => T l.succ)
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      rw [tensorInnerPointwise_0s_add_right, tensorInnerPointwise_0s_smul_right]
      rw [ih_app]

private noncomputable def chartTensorInnerOnChartBasis :
    (s : ℕ) → SmoothRiemannianMetric I M → (α : M) → (b : M) →
      Tensor0SModel s ℝ E →
      Tensor0SModel s ℝ E → ℝ
  | 0, _g, _α, _b, T, S =>
      T (fun i => Fin.elim0 i) * S (fun i => Fin.elim0 i)
  | s + 1, g, α, b, T, S =>
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b)⁻¹ i j *
          chartTensorInnerOnChartBasis s g α b
            (T.curryLeft (chartTrivializationLinearMapSymm
              (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i)))
            (S.curryLeft (chartTrivializationLinearMapSymm
              (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j)))

private lemma chartTensorInnerOnChartBasis_zero
    (g : SmoothRiemannianMetric I M) (α b : M)
    (T S : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ) :
    chartTensorInnerOnChartBasis (I := I) (M := M) 0 g α b T S =
      T (fun i => Fin.elim0 i) * S (fun i => Fin.elim0 i) := rfl

private lemma chartTensorInnerOnChartBasis_succ
    (g : SmoothRiemannianMetric I M) (α b : M) (s : ℕ)
    (T S : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ) :
    chartTensorInnerOnChartBasis (I := I) (M := M) (s + 1) g α b T S =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b)⁻¹ i j *
          chartTensorInnerOnChartBasis (I := I) (M := M) s g α b
            (T.curryLeft (chartTrivializationLinearMapSymm
              (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i)))
            (S.curryLeft (chartTrivializationLinearMapSymm
              (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j))) := rfl

private lemma chartJinv_compose_curry_chartBasis {s : ℕ} (α : M) (b : M)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ)
    (i : Fin (Module.finrank ℝ E)) :
    (T.compContinuousLinearMap (fun _ : Fin (s + 1) =>
        chartTrivializationLinearMapSymm (I := I) (M := M) α b)).curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) =
      (T.curryLeft (chartTrivializationLinearMapSymm
        (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i))).compContinuousLinearMap
        (fun _ : Fin s => chartTrivializationLinearMapSymm (I := I) (M := M) α b) := by
  rw [compContinuousLinearMap_curryLeft]

private theorem chartTensorInnerOnChartBasis_eq_chartTensorInnerPointwise_compose
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) :
    ∀ (s : ℕ) (T S : Tensor0SModel s ℝ E),
      chartTensorInnerOnChartBasis (I := I) (M := M) s g α b T S =
        chartTensorInnerPointwise0s (I := I) (M := M) s g α b
          (T.compContinuousLinearMap (fun _ : Fin s =>
            chartTrivializationLinearMapSymm (I := I) (M := M) α b))
          (S.compContinuousLinearMap (fun _ : Fin s =>
            chartTrivializationLinearMapSymm (I := I) (M := M) α b)) := by
  intro s
  induction s with
  | zero =>
      intro T S
      rw [chartTensorInnerOnChartBasis_zero, chartTensorInnerPointwise_0s_zero]
      simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
      congr 1 <;>
        · congr 1
          funext i
          exact i.elim0
  | succ s ih =>
      intro T S
      rw [chartTensorInnerOnChartBasis_succ, chartTensorInnerPointwise_0s_succ]
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [chartJinv_compose_curry_chartBasis (I := I) (M := M) α b T i,
          chartJinv_compose_curry_chartBasis (I := I) (M := M) α b S j]
      rw [ih (T.curryLeft (chartTrivializationLinearMapSymm
            (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i)))
          (S.curryLeft (chartTrivializationLinearMapSymm
            (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j)))]

private noncomputable def chartTrivializationMatrixInv (α : M) (b : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun a i =>
    ((CalabiYau.Tensor.Coordinates.chartModelBasis E).repr
      (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i))) a

@[simp] private lemma chartJinvMatrix_apply (α : M) (b : M)
    (a i : Fin (Module.finrank ℝ E)) :
    chartTrivializationMatrixInv (I := I) (M := M) α b a i =
      ((CalabiYau.Tensor.Coordinates.chartModelBasis E).repr
        (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i))) a := rfl

private lemma chartBasisVecFiber_eq_sum (α : M) (b : M)
    (i : Fin (Module.finrank ℝ E)) :
    chartTrivializationLinearMapSymm (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) =
      ∑ a : Fin (Module.finrank ℝ E),
        chartTrivializationMatrixInv (I := I) (M := M) α b a i • (CalabiYau.Tensor.Coordinates.chartModelBasis E) a := by
  exact ((CalabiYau.Tensor.Coordinates.chartModelBasis E).sum_repr
    (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i))).symm

private noncomputable def chartTrivializationMatrix (α : M) (b : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun a i =>
    ((CalabiYau.Tensor.Coordinates.chartModelBasis E).repr
      (chartTrivializationLinearMap (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i))) a

@[simp] private lemma chartJMatrix_apply (α : M) (b : M)
    (a i : Fin (Module.finrank ℝ E)) :
    chartTrivializationMatrix (I := I) (M := M) α b a i =
      ((CalabiYau.Tensor.Coordinates.chartModelBasis E).repr
        (chartTrivializationLinearMap (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i))) a := rfl

private lemma chartJ_apply_repr (α : M) (b : M) (v : E)
    (a : Fin (Module.finrank ℝ E)) :
    ((CalabiYau.Tensor.Coordinates.chartModelBasis E).repr (chartTrivializationLinearMap (I := I) (M := M) α b v)) a =
      ∑ k : Fin (Module.finrank ℝ E),
        chartTrivializationMatrix (I := I) (M := M) α b a k *
          ((CalabiYau.Tensor.Coordinates.chartModelBasis E).repr v) k := by
  have hv : v = ∑ k : Fin (Module.finrank ℝ E),
      ((CalabiYau.Tensor.Coordinates.chartModelBasis E).repr v) k • (CalabiYau.Tensor.Coordinates.chartModelBasis E) k :=
    ((CalabiYau.Tensor.Coordinates.chartModelBasis E).sum_repr v).symm
  conv_lhs => rw [hv]
  rw [map_sum, map_sum]
  rw [Finsupp.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [map_smul, map_smul]
  rw [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, chartJMatrix_apply]
  ring

private lemma chartJinv_apply_repr (α : M) (b : M) (v : E)
    (a : Fin (Module.finrank ℝ E)) :
    ((CalabiYau.Tensor.Coordinates.chartModelBasis E).repr (chartTrivializationLinearMapSymm (I := I) (M := M) α b v)) a =
      ∑ k : Fin (Module.finrank ℝ E),
        chartTrivializationMatrixInv (I := I) (M := M) α b a k *
          ((CalabiYau.Tensor.Coordinates.chartModelBasis E).repr v) k := by
  have hv : v = ∑ k : Fin (Module.finrank ℝ E),
      ((CalabiYau.Tensor.Coordinates.chartModelBasis E).repr v) k • (CalabiYau.Tensor.Coordinates.chartModelBasis E) k :=
    ((CalabiYau.Tensor.Coordinates.chartModelBasis E).sum_repr v).symm
  conv_lhs => rw [hv]
  rw [map_sum, map_sum]
  rw [Finsupp.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [map_smul, map_smul]
  rw [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, chartJinvMatrix_apply]
  ring

private lemma chartGramMatrix_eq_matrix_form
    (g : SmoothRiemannianMetric I M) (α b : M) :
    CalabiYau.Tensor.Coordinates.chartGramMatrix g α b =
      (chartTrivializationMatrixInv (I := I) (M := M) α b)ᵀ *
        gramMatrixAt (I := I) (M := M) g b *
        chartTrivializationMatrixInv (I := I) (M := M) α b := by
  ext i j
  rw [chartGramMatrix_eq_innerJinv]
  have hi : chartTrivializationLinearMapSymm (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) =
      ∑ a, chartTrivializationMatrixInv (I := I) (M := M) α b a i • (CalabiYau.Tensor.Coordinates.chartModelBasis E) a := by
    exact chartBasisVecFiber_eq_sum (I := I) (M := M) α b i
  have hj : chartTrivializationLinearMapSymm (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j) =
      ∑ b', chartTrivializationMatrixInv (I := I) (M := M) α b b' j • (CalabiYau.Tensor.Coordinates.chartModelBasis E) b' := by
    exact chartBasisVecFiber_eq_sum (I := I) (M := M) α b j
  rw [hi, hj]
  have hLHS_eq :
      (modelInnerAt (I := I) (M := M) g b (∑ a : Fin (Module.finrank ℝ E),
          chartTrivializationMatrixInv (I := I) (M := M) α b a i • (CalabiYau.Tensor.Coordinates.chartModelBasis E) a))
        (∑ b' : Fin (Module.finrank ℝ E),
          chartTrivializationMatrixInv (I := I) (M := M) α b b' j • (CalabiYau.Tensor.Coordinates.chartModelBasis E) b') =
      ∑ a : Fin (Module.finrank ℝ E),
        ∑ b' : Fin (Module.finrank ℝ E),
          chartTrivializationMatrixInv (I := I) (M := M) α b a i *
            chartTrivializationMatrixInv (I := I) (M := M) α b b' j *
            modelInnerAt (I := I) (M := M) g b
              ((CalabiYau.Tensor.Coordinates.chartModelBasis E) a) ((CalabiYau.Tensor.Coordinates.chartModelBasis E) b') := by
    have hL : modelInnerAt (I := I) (M := M) g b
          (∑ a : Fin (Module.finrank ℝ E),
          chartTrivializationMatrixInv (I := I) (M := M) α b a i • (CalabiYau.Tensor.Coordinates.chartModelBasis E) a) =
        ∑ a : Fin (Module.finrank ℝ E),
          chartTrivializationMatrixInv (I := I) (M := M) α b a i •
            modelInnerAt (I := I) (M := M) g b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) a) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro a _
      exact ContinuousLinearMap.map_smul (modelInnerAt (I := I) (M := M) g b) _ _
    rw [hL, sum_apply]
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [smul_apply, smul_eq_mul]
    rw [show (modelInnerAt (I := I) (M := M) g b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) a))
        (∑ b' : Fin (Module.finrank ℝ E),
          chartTrivializationMatrixInv (I := I) (M := M) α b b' j • (CalabiYau.Tensor.Coordinates.chartModelBasis E) b') =
        ∑ b' : Fin (Module.finrank ℝ E),
          chartTrivializationMatrixInv (I := I) (M := M) α b b' j *
            modelInnerAt (I := I) (M := M) g b
              ((CalabiYau.Tensor.Coordinates.chartModelBasis E) a) ((CalabiYau.Tensor.Coordinates.chartModelBasis E) b') from ?_]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro b' _
      ring
    · rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro b' _
      rw [show (modelInnerAt (I := I) (M := M) g b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) a))
          (chartTrivializationMatrixInv (I := I) (M := M) α b b' j • (CalabiYau.Tensor.Coordinates.chartModelBasis E) b') =
          chartTrivializationMatrixInv (I := I) (M := M) α b b' j •
            (modelInnerAt (I := I) (M := M) g b
              ((CalabiYau.Tensor.Coordinates.chartModelBasis E) a)) ((CalabiYau.Tensor.Coordinates.chartModelBasis E) b') from ?_]
      · rw [smul_eq_mul]
      · exact ContinuousLinearMap.map_smul
          (modelInnerAt (I := I) (M := M) g b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) a)) _ _
  refine hLHS_eq.trans ?_
  rw [Matrix.mul_apply]
  rw [show ∑ b' : Fin (Module.finrank ℝ E),
      ((chartTrivializationMatrixInv (I := I) (M := M) α b)ᵀ *
          gramMatrixAt (I := I) (M := M) g b) i b' *
        chartTrivializationMatrixInv (I := I) (M := M) α b b' j =
        ∑ b' : Fin (Module.finrank ℝ E),
          (∑ a : Fin (Module.finrank ℝ E),
            chartTrivializationMatrixInv (I := I) (M := M) α b a i *
              gramMatrixAt (I := I) (M := M) g b a b') *
            chartTrivializationMatrixInv (I := I) (M := M) α b b' j from ?_]
  · simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro b' _
    rw [gramMatrixAt_apply]
    ring
  · refine Finset.sum_congr rfl ?_
    intro b' _
    rw [Matrix.mul_apply]
    refine congr_arg (· * chartTrivializationMatrixInv (I := I) (M := M) α b b' j) ?_
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [Matrix.transpose_apply]

private lemma chartJinvMatrix_mul_chartJMatrix (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartTrivializationMatrixInv (I := I) (M := M) α b *
        chartTrivializationMatrix (I := I) (M := M) α b = 1 := by
  ext a c
  rw [Matrix.mul_apply]
  have hsum_eq : ∑ k, chartTrivializationMatrixInv (I := I) (M := M) α b a k *
      chartTrivializationMatrix (I := I) (M := M) α b k c =
    ((CalabiYau.Tensor.Coordinates.chartModelBasis E).repr (chartTrivializationLinearMapSymm (I := I) (M := M) α b
      (chartTrivializationLinearMap (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) c)))) a := by
    rw [chartJinv_apply_repr (I := I) (M := M) α b
      (chartTrivializationLinearMap (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) c)) a]
    rfl
  rw [hsum_eq]
  rw [chartJinv_chartJ (I := I) (M := M) α hb]
  rw [Module.Basis.repr_self]
  rw [Finsupp.single_apply]
  rw [Matrix.one_apply]
  by_cases hac : c = a
  · rw [ite_eq_left hac]
    rw [ite_eq_left hac.symm]
  · rw [ite_eq_right hac]
    have : ¬ a = c := fun h => hac h.symm
    rw [ite_eq_right this]

private lemma chartJMatrix_mul_chartJinvMatrix (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartTrivializationMatrix (I := I) (M := M) α b *
        chartTrivializationMatrixInv (I := I) (M := M) α b = 1 := by
  ext a c
  rw [Matrix.mul_apply]
  have hsum_eq : ∑ k, chartTrivializationMatrix (I := I) (M := M) α b a k *
      chartTrivializationMatrixInv (I := I) (M := M) α b k c =
    ((CalabiYau.Tensor.Coordinates.chartModelBasis E).repr (chartTrivializationLinearMap (I := I) (M := M) α b
      (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) c)))) a := by
    rw [chartJ_apply_repr (I := I) (M := M) α b
      (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) c)) a]
    rfl
  rw [hsum_eq]
  rw [chartJ_chartJinv (I := I) (M := M) α hb]
  rw [Module.Basis.repr_self]
  rw [Finsupp.single_apply]
  rw [Matrix.one_apply]
  by_cases hac : c = a
  · rw [ite_eq_left hac]
    rw [ite_eq_left hac.symm]
  · rw [ite_eq_right hac]
    have : ¬ a = c := fun h => hac h.symm
    rw [ite_eq_right this]

private lemma chartJinvMatrix_inv (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    (chartTrivializationMatrixInv (I := I) (M := M) α b)⁻¹ =
      chartTrivializationMatrix (I := I) (M := M) α b := by
  apply Matrix.inv_eq_left_inv
  exact chartJMatrix_mul_chartJinvMatrix (I := I) (M := M) α hb

private lemma chartGramMatrix_isUnit_det
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    IsUnit (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b).det :=
  (CalabiYau.Tensor.Coordinates.chartGramMatrix_det_pos (I := I) g α hb).ne'.isUnit

private lemma chartGramMatrix_isUnit
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    IsUnit (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr
    (chartGramMatrix_isUnit_det (I := I) (M := M) g α hb)

private lemma chartGramMatrix_inv_mul_self_at
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b)⁻¹ *
        CalabiYau.Tensor.Coordinates.chartGramMatrix g α b = 1 :=
  Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).mp
      (chartGramMatrix_isUnit (I := I) (M := M) g α hb))

private lemma chartJinv_chartGramInv_chartJinvT_eq_gramInv_entry
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (a c : Fin (Module.finrank ℝ E)) :
    ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b)⁻¹ i j *
          (chartTrivializationMatrixInv (I := I) (M := M) α b a i *
            chartTrivializationMatrixInv (I := I) (M := M) α b c j) =
      (gramMatrixAt (I := I) (M := M) g b)⁻¹ a c := by
  have hLHS_form :
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b)⁻¹ i j *
            (chartTrivializationMatrixInv (I := I) (M := M) α b a i *
              chartTrivializationMatrixInv (I := I) (M := M) α b c j)) =
      (chartTrivializationMatrixInv (I := I) (M := M) α b *
        (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b)⁻¹ *
        (chartTrivializationMatrixInv (I := I) (M := M) α b)ᵀ) a c := by
    rw [Matrix.mul_apply]
    rw [show ∑ j : Fin (Module.finrank ℝ E),
        (chartTrivializationMatrixInv (I := I) (M := M) α b *
          (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b)⁻¹) a j *
          (chartTrivializationMatrixInv (I := I) (M := M) α b)ᵀ j c =
        ∑ j : Fin (Module.finrank ℝ E),
          (∑ i : Fin (Module.finrank ℝ E),
            chartTrivializationMatrixInv (I := I) (M := M) α b a i *
            (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b)⁻¹ i j) *
          chartTrivializationMatrixInv (I := I) (M := M) α b c j from ?_]
    · simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
    · refine Finset.sum_congr rfl ?_
      intro j _
      rw [Matrix.mul_apply, Matrix.transpose_apply]
  rw [hLHS_form]
  have hJinvMat_inv := chartJinvMatrix_inv (I := I) (M := M) α hb
  have hrhs : (chartTrivializationMatrixInv (I := I) (M := M) α b *
      (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b)⁻¹ *
      (chartTrivializationMatrixInv (I := I) (M := M) α b)ᵀ) *
      gramMatrixAt (I := I) (M := M) g b = 1 := by
    have hGramEq := chartGramMatrix_eq_matrix_form (I := I) (M := M) g α b
    have hJinvMatT_mul_G :
        (chartTrivializationMatrixInv (I := I) (M := M) α b)ᵀ *
            gramMatrixAt (I := I) (M := M) g b =
          CalabiYau.Tensor.Coordinates.chartGramMatrix g α b *
            (chartTrivializationMatrixInv (I := I) (M := M) α b)⁻¹ := by
      rw [hGramEq, hJinvMat_inv]
      rw [Matrix.mul_assoc, Matrix.mul_assoc]
      rw [chartJinvMatrix_mul_chartJMatrix (I := I) (M := M) α hb]
      rw [Matrix.mul_one]
    rw [Matrix.mul_assoc, Matrix.mul_assoc,
      hJinvMatT_mul_G,
      ← Matrix.mul_assoc (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b)⁻¹,
      chartGramMatrix_inv_mul_self_at (I := I) (M := M) g α hb,
      Matrix.one_mul,
      hJinvMat_inv,
      chartJinvMatrix_mul_chartJMatrix (I := I) (M := M) α hb]
  have hMain : chartTrivializationMatrixInv (I := I) (M := M) α b *
      (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b)⁻¹ *
      (chartTrivializationMatrixInv (I := I) (M := M) α b)ᵀ =
      (gramMatrixAt (I := I) (M := M) g b)⁻¹ := by
    exact (Matrix.inv_eq_left_inv hrhs).symm
  rw [hMain]

private theorem tensorInnerPointwise_0s_eq_chartTensorInnerOnChartBasis
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∀ (s : ℕ) {b : M},
      b ∈ (trivializationAt E (TangentSpace I) α).baseSet →
      ∀ (T S : Tensor0SModel s ℝ E),
      covariantTensorInnerPointwise (I := I) (M := M) s g b T S =
        chartTensorInnerOnChartBasis (I := I) (M := M) s g α b T S := by
  intro s
  induction s with
  | zero =>
      intro b _ T S
      rw [tensorInnerPointwise_0s_zero_arity, chartTensorInnerOnChartBasis_zero]
  | succ s ih =>
      intro b hb T S
      rw [tensorInnerPointwise_0s_succ, chartTensorInnerOnChartBasis_succ]
      have step1 :
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b)⁻¹ i j *
                chartTensorInnerOnChartBasis (I := I) (M := M) s g α b
                  (T.curryLeft (chartTrivializationLinearMapSymm
                    (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i)))
                  (S.curryLeft (chartTrivializationLinearMapSymm
                    (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j))) =
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b)⁻¹ i j *
                covariantTensorInnerPointwise (I := I) (M := M) s g b
                  (T.curryLeft (chartTrivializationLinearMapSymm
                    (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i)))
                  (S.curryLeft (chartTrivializationLinearMapSymm
                    (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j))) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [← ih hb _ _]
      rw [step1]
      have step2_T : ∀ i : Fin (Module.finrank ℝ E),
          T.curryLeft (chartTrivializationLinearMapSymm
            (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i)) =
            ∑ a : Fin (Module.finrank ℝ E),
              chartTrivializationMatrixInv (I := I) (M := M) α b a i •
                T.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) a) := by
        intro i
        rw [chartBasisVecFiber_eq_sum (I := I) (M := M) α b i]
        exact curryLeft_sum (E := E) (s := s) T _ _
      have step2_S : ∀ j : Fin (Module.finrank ℝ E),
          S.curryLeft (chartTrivializationLinearMapSymm
            (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j)) =
            ∑ b' : Fin (Module.finrank ℝ E),
              chartTrivializationMatrixInv (I := I) (M := M) α b b' j •
                S.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) b') := by
        intro j
        rw [chartBasisVecFiber_eq_sum (I := I) (M := M) α b j]
        exact curryLeft_sum (E := E) (s := s) S _ _
      have step3 : ∀ i j : Fin (Module.finrank ℝ E),
          covariantTensorInnerPointwise (I := I) (M := M) s g b
              (T.curryLeft (chartTrivializationLinearMapSymm
                (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i)))
              (S.curryLeft (chartTrivializationLinearMapSymm
                (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j))) =
            ∑ a : Fin (Module.finrank ℝ E),
              ∑ b' : Fin (Module.finrank ℝ E),
                chartTrivializationMatrixInv (I := I) (M := M) α b a i *
                  chartTrivializationMatrixInv (I := I) (M := M) α b b' j *
                covariantTensorInnerPointwise (I := I) (M := M) s g b
                  (T.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) a))
                  (S.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) b')) := by
        intro i j
        rw [step2_T i, step2_S j]
        rw [tensorInnerPointwise_0s_sum_left]
        refine Finset.sum_congr rfl ?_
        intro a _
        rw [tensorInnerPointwise_0s_sum_right]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro b' _
        ring
      have step4 :
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b)⁻¹ i j *
                covariantTensorInnerPointwise (I := I) (M := M) s g b
                  (T.curryLeft (chartTrivializationLinearMapSymm
                    (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i)))
                  (S.curryLeft (chartTrivializationLinearMapSymm
                    (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j))) =
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∑ a : Fin (Module.finrank ℝ E),
                ∑ b' : Fin (Module.finrank ℝ E),
                  (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b)⁻¹ i j *
                    (chartTrivializationMatrixInv (I := I) (M := M) α b a i *
                      chartTrivializationMatrixInv (I := I) (M := M) α b b' j) *
                    covariantTensorInnerPointwise (I := I) (M := M) s g b
                      (T.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) a))
                      (S.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) b')) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [step3 i j]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro a _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro b' _
        ring
      rw [step4]
      have step5_0 :
          ∀ (i : Fin (Module.finrank ℝ E)),
            ∑ j : Fin (Module.finrank ℝ E),
              ∑ a : Fin (Module.finrank ℝ E),
                ∑ b' : Fin (Module.finrank ℝ E),
                  (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b)⁻¹ i j *
                    (chartTrivializationMatrixInv (I := I) (M := M) α b a i *
                      chartTrivializationMatrixInv (I := I) (M := M) α b b' j) *
                    covariantTensorInnerPointwise (I := I) (M := M) s g b
                      (T.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) a))
                      (S.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) b')) =
            ∑ a : Fin (Module.finrank ℝ E),
              ∑ b' : Fin (Module.finrank ℝ E),
                ∑ j : Fin (Module.finrank ℝ E),
                  (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b)⁻¹ i j *
                    (chartTrivializationMatrixInv (I := I) (M := M) α b a i *
                      chartTrivializationMatrixInv (I := I) (M := M) α b b' j) *
                    covariantTensorInnerPointwise (I := I) (M := M) s g b
                      (T.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) a))
                      (S.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) b')) := by
        intro i
        rw [Finset.sum_comm (γ := Fin (Module.finrank ℝ E))]
        refine Finset.sum_congr rfl ?_
        intro a _
        rw [Finset.sum_comm (γ := Fin (Module.finrank ℝ E))]
      have step5_1 :
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∑ a : Fin (Module.finrank ℝ E),
                ∑ b' : Fin (Module.finrank ℝ E),
                  (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b)⁻¹ i j *
                    (chartTrivializationMatrixInv (I := I) (M := M) α b a i *
                      chartTrivializationMatrixInv (I := I) (M := M) α b b' j) *
                    covariantTensorInnerPointwise (I := I) (M := M) s g b
                      (T.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) a))
                      (S.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) b')) =
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ a : Fin (Module.finrank ℝ E),
              ∑ b' : Fin (Module.finrank ℝ E),
                ∑ j : Fin (Module.finrank ℝ E),
                  (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b)⁻¹ i j *
                    (chartTrivializationMatrixInv (I := I) (M := M) α b a i *
                      chartTrivializationMatrixInv (I := I) (M := M) α b b' j) *
                    covariantTensorInnerPointwise (I := I) (M := M) s g b
                      (T.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) a))
                      (S.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) b')) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        exact step5_0 i
      have step5 :
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∑ a : Fin (Module.finrank ℝ E),
                ∑ b' : Fin (Module.finrank ℝ E),
                  (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b)⁻¹ i j *
                    (chartTrivializationMatrixInv (I := I) (M := M) α b a i *
                      chartTrivializationMatrixInv (I := I) (M := M) α b b' j) *
                    covariantTensorInnerPointwise (I := I) (M := M) s g b
                      (T.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) a))
                      (S.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) b')) =
          ∑ a : Fin (Module.finrank ℝ E),
            ∑ b' : Fin (Module.finrank ℝ E),
              ∑ i : Fin (Module.finrank ℝ E),
                ∑ j : Fin (Module.finrank ℝ E),
                  (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b)⁻¹ i j *
                    (chartTrivializationMatrixInv (I := I) (M := M) α b a i *
                      chartTrivializationMatrixInv (I := I) (M := M) α b b' j) *
                    covariantTensorInnerPointwise (I := I) (M := M) s g b
                      (T.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) a))
                      (S.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) b')) := by
        rw [step5_1]
        rw [Finset.sum_comm (γ := Fin (Module.finrank ℝ E))]
        refine Finset.sum_congr rfl ?_
        intro a _
        rw [Finset.sum_comm (γ := Fin (Module.finrank ℝ E))]
      rw [step5]
      have step6 :
          ∑ a : Fin (Module.finrank ℝ E),
            ∑ b' : Fin (Module.finrank ℝ E),
              ∑ i : Fin (Module.finrank ℝ E),
                ∑ j : Fin (Module.finrank ℝ E),
                  (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b)⁻¹ i j *
                    (chartTrivializationMatrixInv (I := I) (M := M) α b a i *
                      chartTrivializationMatrixInv (I := I) (M := M) α b b' j) *
                    covariantTensorInnerPointwise (I := I) (M := M) s g b
                      (T.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) a))
                      (S.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) b')) =
          ∑ a : Fin (Module.finrank ℝ E),
            ∑ b' : Fin (Module.finrank ℝ E),
              (∑ i : Fin (Module.finrank ℝ E),
                ∑ j : Fin (Module.finrank ℝ E),
                  (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b)⁻¹ i j *
                    (chartTrivializationMatrixInv (I := I) (M := M) α b a i *
                      chartTrivializationMatrixInv (I := I) (M := M) α b b' j)) *
                covariantTensorInnerPointwise (I := I) (M := M) s g b
                  (T.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) a))
                  (S.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) b')) := by
        refine Finset.sum_congr rfl ?_
        intro a _
        refine Finset.sum_congr rfl ?_
        intro b' _
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [Finset.sum_mul]
      rw [step6]
      have step7 : ∀ (a c : Fin (Module.finrank ℝ E)),
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b)⁻¹ i j *
                (chartTrivializationMatrixInv (I := I) (M := M) α b a i *
                  chartTrivializationMatrixInv (I := I) (M := M) α b c j) =
            (gramMatrixAt (I := I) (M := M) g b)⁻¹ a c := fun a c =>
        chartJinv_chartGramInv_chartJinvT_eq_gramInv_entry
          (I := I) (M := M) g α hb a c
      have step8 :
          ∑ a : Fin (Module.finrank ℝ E),
            ∑ b' : Fin (Module.finrank ℝ E),
              (∑ i : Fin (Module.finrank ℝ E),
                ∑ j : Fin (Module.finrank ℝ E),
                  (CalabiYau.Tensor.Coordinates.chartGramMatrix g α b)⁻¹ i j *
                    (chartTrivializationMatrixInv (I := I) (M := M) α b a i *
                      chartTrivializationMatrixInv (I := I) (M := M) α b b' j)) *
                covariantTensorInnerPointwise (I := I) (M := M) s g b
                  (T.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) a))
                  (S.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) b')) =
          ∑ a : Fin (Module.finrank ℝ E),
            ∑ b' : Fin (Module.finrank ℝ E),
              (gramMatrixAt (I := I) (M := M) g b)⁻¹ a b' *
                covariantTensorInnerPointwise (I := I) (M := M) s g b
                  (T.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) a))
                  (S.curryLeft ((CalabiYau.Tensor.Coordinates.chartModelBasis E) b')) := by
        refine Finset.sum_congr rfl ?_
        intro a _
        refine Finset.sum_congr rfl ?_
        intro b' _
        rw [step7 a b']
      symm
      exact step8

theorem covariantTensorInnerPointwise_eq_chartTensorInnerPointwise_comp
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∀ (s : ℕ) {b : M},
      b ∈ (trivializationAt E (TangentSpace I) α).baseSet →
      ∀ (T S : Tensor0SModel s ℝ E),
      covariantTensorInnerPointwise (I := I) (M := M) s g b T S =
        chartTensorInnerPointwise0s (I := I) (M := M) s g α b
          (T.compContinuousLinearMap (fun _ : Fin s =>
            chartTrivializationLinearMapSymm (I := I) (M := M) α b))
          (S.compContinuousLinearMap (fun _ : Fin s =>
            chartTrivializationLinearMapSymm (I := I) (M := M) α b)) := by
  intro s b hb T S
  rw [tensorInnerPointwise_0s_eq_chartTensorInnerOnChartBasis
      (I := I) (M := M) g α s hb T S]
  rw [chartTensorInnerOnChartBasis_eq_chartTensorInnerPointwise_compose
      (I := I) (M := M) g α b s T S]

end

end Tensor0SRiemannian
end Tensor
end CalabiYau

end
