-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Spectral/Tensor/ChartTensor/Inner/InnerBridge.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Riemannian.TensorInner.ChartTensor.Inner.Defs
public import CalabiYau.Geometry.Riemannian.TensorInner.Tensor0S.Bundle.SectionRegularity
public import CalabiYau.Geometry.Riemannian.Metric.PointwiseInner.Defs
public import CalabiYau.Geometry.Riemannian.Metric.PointwiseInner.DualMetric

@[expose] public section


noncomputable section

open Bundle Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff BigOperators Matrix

namespace CalabiYau.ChartTensor

open CalabiYau.RiemannianVolume
open CalabiYau.L2
open CalabiYau.Tensor
open CalabiYau.Tensor0SBundle
open CalabiYau.Tensor.Tensor0SRiemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

lemma chartGramBilin_eq_innerJinv
    (g : SmoothRiemannianMetric I M) (α b : M) (u w : E) :
    chartGramBilin (I := I) (M := M) g α b u w =
      modelInnerAt (I := I) (M := M) g b
        (chartTrivializationLinearMapSymm (I := I) (M := M) α b u)
        (chartTrivializationLinearMapSymm (I := I) (M := M) α b w) := by
  classical
  rw [chartGramBilin_apply]
  have hrewrite :
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          CalabiYau.Tensor.Coordinates.chartGramMatrix g α b j k *
            (CalabiYau.Tensor.Coordinates.chartModelBasis E).equivFun u j *
            (CalabiYau.Tensor.Coordinates.chartModelBasis E).equivFun w k)
        = ∑ j : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              (CalabiYau.Tensor.Coordinates.chartModelBasis E).equivFun u j *
                (CalabiYau.Tensor.Coordinates.chartModelBasis E).equivFun w k *
                modelInnerAt (I := I) (M := M) g b
                  (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j))
                  (chartTrivializationLinearMapSymm (I := I) (M := M) α b
                    ((CalabiYau.Tensor.Coordinates.chartModelBasis E) k)) := by
    refine Finset.sum_congr rfl ?_
    intro j _
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [chartGramMatrix_eq_innerJinv (I := I) (M := M) g α b j k]
    ring
  rw [hrewrite]
  have hcollapse_inner : ∀ j : Fin (Module.finrank ℝ E),
      (∑ k : Fin (Module.finrank ℝ E),
          (CalabiYau.Tensor.Coordinates.chartModelBasis E).equivFun u j *
            (CalabiYau.Tensor.Coordinates.chartModelBasis E).equivFun w k *
            modelInnerAt (I := I) (M := M) g b
              (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j))
              (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) k)))
        = (CalabiYau.Tensor.Coordinates.chartModelBasis E).equivFun u j *
            modelInnerAt (I := I) (M := M) g b
              (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j))
              (∑ k : Fin (Module.finrank ℝ E),
                (CalabiYau.Tensor.Coordinates.chartModelBasis E).equivFun w k •
                  chartTrivializationLinearMapSymm (I := I) (M := M) α b
                    ((CalabiYau.Tensor.Coordinates.chartModelBasis E) k)) := by
    intro j
    have hRHS_unfold :
        ((modelInnerAt (I := I) (M := M) g b
          (chartTrivializationLinearMapSymm (I := I) (M := M) α b
          ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j)))
            (∑ k : Fin (Module.finrank ℝ E),
              (CalabiYau.Tensor.Coordinates.chartModelBasis E).equivFun w k •
                chartTrivializationLinearMapSymm (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) k)))
          = ∑ k : Fin (Module.finrank ℝ E),
              (CalabiYau.Tensor.Coordinates.chartModelBasis E).equivFun w k *
                modelInnerAt (I := I) (M := M) g b
                  (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j))
                  (chartTrivializationLinearMapSymm (I := I) (M := M) α b
                    ((CalabiYau.Tensor.Coordinates.chartModelBasis E) k)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [ContinuousLinearMap.map_smul, smul_eq_mul]
    rw [hRHS_unfold]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    ring
  rw [show (∑ j : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          (CalabiYau.Tensor.Coordinates.chartModelBasis E).equivFun u j *
            (CalabiYau.Tensor.Coordinates.chartModelBasis E).equivFun w k *
            modelInnerAt (I := I) (M := M) g b
              (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j))
              (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) k)))
        = ∑ j : Fin (Module.finrank ℝ E),
            (CalabiYau.Tensor.Coordinates.chartModelBasis E).equivFun u j *
              modelInnerAt (I := I) (M := M) g b
                (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j))
                (∑ k : Fin (Module.finrank ℝ E),
                  (CalabiYau.Tensor.Coordinates.chartModelBasis E).equivFun w k •
                    chartTrivializationLinearMapSymm (I := I) (M := M) α b
                      ((CalabiYau.Tensor.Coordinates.chartModelBasis E) k)) from
      Finset.sum_congr rfl (fun j _ => hcollapse_inner j)]
  have hwsum :
      (∑ k : Fin (Module.finrank ℝ E),
          (CalabiYau.Tensor.Coordinates.chartModelBasis E).equivFun w k •
            chartTrivializationLinearMapSymm (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) k)) =
        chartTrivializationLinearMapSymm (I := I) (M := M) α b w := by
    have hsum_eq :
        (∑ k : Fin (Module.finrank ℝ E),
            (CalabiYau.Tensor.Coordinates.chartModelBasis E).equivFun w k •
              chartTrivializationLinearMapSymm (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) k))
          = chartTrivializationLinearMapSymm (I := I) (M := M) α b
              (∑ k : Fin (Module.finrank ℝ E),
                (CalabiYau.Tensor.Coordinates.chartModelBasis E).equivFun w k • (CalabiYau.Tensor.Coordinates.chartModelBasis E) k) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [ContinuousLinearMap.map_smul]
    rw [hsum_eq, (CalabiYau.Tensor.Coordinates.chartModelBasis E).sum_equivFun w]
  rw [hwsum]
  have hcollapse_outer :
      (∑ j : Fin (Module.finrank ℝ E),
          (CalabiYau.Tensor.Coordinates.chartModelBasis E).equivFun u j *
            modelInnerAt (I := I) (M := M) g b
              (chartTrivializationLinearMapSymm (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j))
              (chartTrivializationLinearMapSymm (I := I) (M := M) α b w))
        = modelInnerAt (I := I) (M := M) g b
            (∑ j : Fin (Module.finrank ℝ E),
              (CalabiYau.Tensor.Coordinates.chartModelBasis E).equivFun u j •
                chartTrivializationLinearMapSymm (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j))
            (chartTrivializationLinearMapSymm (I := I) (M := M) α b w) := by
    rw [map_sum]
    rw [sum_apply]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [ContinuousLinearMap.map_smul, smul_apply, smul_eq_mul]
  rw [hcollapse_outer]
  have husum :
      (∑ j : Fin (Module.finrank ℝ E),
          (CalabiYau.Tensor.Coordinates.chartModelBasis E).equivFun u j •
            chartTrivializationLinearMapSymm (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j))
        = chartTrivializationLinearMapSymm (I := I) (M := M) α b u := by
    have hsum_eq :
        (∑ j : Fin (Module.finrank ℝ E),
            (CalabiYau.Tensor.Coordinates.chartModelBasis E).equivFun u j •
              chartTrivializationLinearMapSymm (I := I) (M := M) α b ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j))
          = chartTrivializationLinearMapSymm (I := I) (M := M) α b
              (∑ j : Fin (Module.finrank ℝ E),
                (CalabiYau.Tensor.Coordinates.chartModelBasis E).equivFun u j • (CalabiYau.Tensor.Coordinates.chartModelBasis E) j) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [ContinuousLinearMap.map_smul]
    rw [hsum_eq, (CalabiYau.Tensor.Coordinates.chartModelBasis E).sum_equivFun u]
  rw [husum]

lemma chartSeparableFormAt_chartJ_compose
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (r : ℕ) (v_first : Fin r → E) :
    chartSeparableFormAt (I := I) (M := M) g α b r
        (fun k : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b (v_first k))
      = (separableFormAt (I := I) (M := M) g b r v_first).compContinuousLinearMap
          (fun _ : Fin r => chartTrivializationLinearMapSymm (I := I) (M := M) α b) := by
  classical
  refine ContinuousMultilinearMap.ext ?_
  intro w
  rw [chartSeparableFormAt_apply]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply, separableFormAt_apply]
  refine Finset.prod_congr rfl ?_
  intro k _
  rw [chartGramBilin_eq_innerJinv (I := I) (M := M) g α b]
  rw [chartJinv_chartJ_self (I := I) (M := M) α hb (v_first k)]

theorem chartTensorInnerPointwise_0s_eq_tensorInnerPointwise_0s_chartJ
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (s : ℕ) (A B : Tensor0SModel s ℝ E) :
    chartTensorInnerPointwise0s (I := I) (M := M) s g α b A B =
      covariantTensorInnerPointwise (I := I) (M := M) s g b
        (A.compContinuousLinearMap
          (fun _ : Fin s => chartTrivializationLinearMap (I := I) (M := M) α b))
        (B.compContinuousLinearMap
          (fun _ : Fin s => chartTrivializationLinearMap (I := I) (M := M) α b)) := by
  classical
  have hbridge :=
    tensorInnerPointwise_0s_bridge_identity (I := I) (M := M) g α s hb
      (A.compContinuousLinearMap
        (fun _ : Fin s => chartTrivializationLinearMap (I := I) (M := M) α b))
      (B.compContinuousLinearMap
        (fun _ : Fin s => chartTrivializationLinearMap (I := I) (M := M) α b))
  have hAcompose :
      (A.compContinuousLinearMap
          (fun _ : Fin s => chartTrivializationLinearMap (I := I) (M := M) α
            b)).compContinuousLinearMap
        (fun _ : Fin s => chartTrivializationLinearMapSymm (I := I) (M := M) α b) = A := by
    refine ContinuousMultilinearMap.ext ?_
    intro m
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext k
    exact chartJ_chartJinv (I := I) (M := M) α hb (m k)
  have hBcompose :
      (B.compContinuousLinearMap
          (fun _ : Fin s => chartTrivializationLinearMap (I := I) (M := M) α
            b)).compContinuousLinearMap
        (fun _ : Fin s => chartTrivializationLinearMapSymm (I := I) (M := M) α b) = B := by
    refine ContinuousMultilinearMap.ext ?_
    intro m
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext k
    exact chartJ_chartJinv (I := I) (M := M) α hb (m k)
  rw [hAcompose, hBcompose] at hbridge
  exact hbridge.symm

theorem chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise_0s_compChartJ
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (T₀ T₁ : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwiseRsModel (I := I) (M := M) g r s α b T₀ T₁ =
      covariantTensorInnerPointwise (I := I) (M := M) (r + s) g b
        ((chartLowerAllUpperIndicesModel (I := I) (M := M) r s g α b T₀).compContinuousLinearMap
          (fun _ : Fin (r + s) => chartTrivializationLinearMap (I := I) (M := M) α b))
        ((chartLowerAllUpperIndicesModel (I := I) (M := M) r s g α b T₁).compContinuousLinearMap
          (fun _ : Fin (r + s) => chartTrivializationLinearMap (I := I) (M := M) α b)) := by
  rw [chartTensorInnerPointwise_rs_model_def]
  exact chartTensorInnerPointwise_0s_eq_tensorInnerPointwise_0s_chartJ
    (I := I) (M := M) g α hb (r + s) _ _

noncomputable def chartRSTwist
    (α : M) (b : M) (r s : ℕ) (T : TensorRSModel r s ℝ E) :
    TensorRSModel r s ℝ E :=
  (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin s => chartTrivializationLinearMap (I := I) (M := M) α b)).comp <|
    T.comp
      ((ContinuousMultilinearMap.compContinuousLinearMapL
        (fun _ : Fin r => chartTrivializationLinearMapSymm (I := I) (M := M) α b)))

@[simp]
lemma chartRSTwist_apply
    (α b : M) (r s : ℕ) (T : TensorRSModel r s ℝ E)
    (α' : Tensor0SModel r ℝ E) :
    chartRSTwist (I := I) (M := M) α b r s T α' =
      (T (α'.compContinuousLinearMap
            (fun _ : Fin r => chartTrivializationLinearMapSymm (I := I) (M := M) α
              b))).compContinuousLinearMap
        (fun _ : Fin s => chartTrivializationLinearMap (I := I) (M := M) α b) := by
  rfl

lemma chartLowerAllUpperIndices_model_compChartJ
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (T : TensorRSModel r s ℝ E) :
    (chartLowerAllUpperIndicesModel (I := I) (M := M) r s g α b T).compContinuousLinearMap
        (fun _ : Fin (r + s) => chartTrivializationLinearMap (I := I) (M := M) α b)
      = lowerAllUpperIndices (I := I) (M := M) g r s b
          (chartRSTwist (I := I) (M := M) α b r s T) := by
  classical
  refine ContinuousMultilinearMap.ext ?_
  intro v
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    chartLowerAllUpperIndices_model_apply]
  rw [lowerAllUpperIndices_apply]
  rw [chartRSTwist_apply]
  have hsep :
      chartSeparableFormAt (I := I) (M := M) g α b r
          (fun i : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b
            (v (Fin.castAdd s i)))
        = (separableFormAt (I := I) (M := M) g b r
            (fun i : Fin r => v (Fin.castAdd s i))).compContinuousLinearMap
            (fun _ : Fin r => chartTrivializationLinearMapSymm (I := I) (M := M) α b) := by
    have := chartSeparableFormAt_chartJ_compose (I := I) (M := M) g α hb r
      (fun i : Fin r => v (Fin.castAdd s i))
    exact this
  rw [hsep]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]

theorem chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (T₀ T₁ : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwiseRsModel (I := I) (M := M) g r s α b T₀ T₁ =
      tensorInnerPointwise (I := I) (M := M) g r s b
        (chartRSTwist (I := I) (M := M) α b r s T₀)
        (chartRSTwist (I := I) (M := M) α b r s T₁) := by
  rw [chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise_0s_compChartJ
    (I := I) (M := M) g r s α hb T₀ T₁]
  rw [chartLowerAllUpperIndices_model_compChartJ
    (I := I) (M := M) g r s α hb T₀]
  rw [chartLowerAllUpperIndices_model_compChartJ
    (I := I) (M := M) g r s α hb T₁]
  rfl

end CalabiYau.ChartTensor

end
