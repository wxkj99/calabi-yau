module

public import CalabiYau.Geometry.Complex.Forms.Basic
public import CalabiYau.Geometry.Riemannian.TensorInner.ChartTensor.Inner.CoordinateInvariance

/-!
# Fixed-chart representatives of form fields

`FormField.chartRep c z` is the unbundled continuous alternating-map representative of a form
field at `y = (extChartAt c).symm z`, expressed in the single chart centered at `c`. The
Riemannian tensor infrastructure represents the same coordinate transport by `ChartTensor.chartRSTwist`.
This module supplies the coercion from alternating maps to the `r = 0` tensor model and proves
the fixed-chart identity between these representations.

The target-membership hypothesis is explicit: it guarantees that `y` lies in the source of the
chart at `c`, where the chart trivialization is defined. The proof compares the two chart
transitions pointwise and cancels them. In particular, this is not a claim that coefficients in a
chart chosen at the varying point are globally continuous. The statement permits every degree `k`,
including `k = 0` and the zero-dimensional model; no nondegeneracy assumption on `k` is used.

For metric pairings, apply the identity to each form and then use
`ChartTensor.chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise`: the chartwise contraction
of the two fixed-chart representatives is the covariant tensor contraction at `y`. The factorial
normalization for the exterior-power pairing remains the separate `1 / k!` in the form pairing.
-/

@[expose] public section

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {k : ℕ}

namespace FormField

/-- Regard a continuous alternating `k`-form as an `r = 0`, `s = k` tensor model.
The zero-slot linear functional is evaluation on the unique empty tuple. -/
noncomputable def tensorChartModel (η : E [⋀^Fin k]→L[ℝ] ℝ) :
    CalabiYau.Tensor0SBundle.TensorRSModel 0 k ℝ E :=
  ContinuousLinearMap.smulRight
    (continuousMultilinearCurryFin0 ℝ E ℝ).toContinuousLinearMap
    η.toContinuousMultilinearMap

/-- Evaluation of the form tensor model on a zero-slot tensor is scalar multiplication. -/
theorem tensorChartModel_apply (η : E [⋀^Fin k]→L[ℝ] ℝ)
    (T : CalabiYau.Tensor0SBundle.Tensor0SModel 0 ℝ E) :
    tensorChartModel η T = T (fun i => Fin.elim0 i) • η.toContinuousMultilinearMap := by
  change continuousMultilinearCurryFin0 ℝ E ℝ T • η.toContinuousMultilinearMap = _
  rw [continuousMultilinearCurryFin0_apply]
  congr 1
  exact congrArg T (Subsingleton.elim _ _)

end FormField

/-- At a fixed chart, the tensor representative of the continuous alternating map
`FormField.chartRep c z` transports back to the original form value at
`y = (extChartAt c).symm z`. This is the pointwise bridge used with the chartwise tensor-inner
identity. -/
theorem FormField.chartRep_eq_chartRSTwist_tensorChartModel
    (α : FormField E M k) (c : M) {z : E}
    (hz : z ∈ (extChartAt 𝓘(ℝ, E) c).target) :
    (α ((extChartAt 𝓘(ℝ, E) c).symm z)).toContinuousMultilinearMap =
      (CalabiYau.ChartTensor.chartRSTwist (I := 𝓘(ℝ, E)) (M := M) c
        ((extChartAt 𝓘(ℝ, E) c).symm z) 0 k
        (FormField.tensorChartModel (α.chartRep c z)))
        (ContinuousMultilinearMap.uncurry0 ℝ E (1 : ℝ)) := by
  let y := (extChartAt 𝓘(ℝ, E) c).symm z
  have hy : y ∈ (extChartAt 𝓘(ℝ, E) c).source :=
    (extChartAt 𝓘(ℝ, E) c).map_target hz
  have hy' : y ∈ (chartAt E c).source := by
    simpa only [extChartAt_source] using hy
  have hJ : CalabiYau.Tensor.Tensor0SRiemannian.chartTrivializationLinearMap
      (I := 𝓘(ℝ, E)) (M := M) c y =
      tangentCoordChange 𝓘(ℝ, E) y c y := by
    ext v
    rw [CalabiYau.Tensor.Tensor0SRiemannian.chartJ_apply (I := 𝓘(ℝ, E)) (M := M)]
    simp only [CalabiYau.tangentSpaceModelContinuousLinearEquiv_symm_apply]
    rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hy']
    rfl
  have hyself : y ∈ (extChartAt 𝓘(ℝ, E) y).source :=
    mem_extChartAt_source (I := 𝓘(ℝ, E)) y
  have hcoord (v : E) : tangentCoordChange 𝓘(ℝ, E) c y y
      (CalabiYau.Tensor.Tensor0SRiemannian.chartTrivializationLinearMap
        (I := 𝓘(ℝ, E)) (M := M) c y v) = v := by
    calc
      _ = tangentCoordChange 𝓘(ℝ, E) y y y v := by
        rw [hJ]
        exact tangentCoordChange_comp (I := 𝓘(ℝ, E)) (w := y) (x := c) (y := y)
          (z := y) (v := v) ⟨⟨hyself, hy⟩, hyself⟩
      _ = v := tangentCoordChange_self (I := 𝓘(ℝ, E)) hyself
  ext v
  rw [CalabiYau.ChartTensor.chartRSTwist_apply]
  rw [FormField.tensorChartModel_apply]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.uncurry0_apply, one_smul]
  rw [FormField.chartRep]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hval (w : Fin k → E) :
      (α y).toContinuousMultilinearMap w = α y w :=
    congrFun (ContinuousAlternatingMap.coe_toContinuousMultilinearMap (f := α y)) w
  rw [hval, hval]
  congr 1
  funext i
  exact (hcoord (v i)).symm

/-- The full tensor-model identity, not just its evaluation on the unit zero-slot tensor. -/
theorem FormField.chartRSTwist_tensorChartModel_eq
    (α : FormField E M k) (c : M) {z : E}
    (hz : z ∈ (extChartAt 𝓘(ℝ, E) c).target) :
    CalabiYau.ChartTensor.chartRSTwist (I := 𝓘(ℝ, E)) (M := M) c
      ((extChartAt 𝓘(ℝ, E) c).symm z) 0 k
      (FormField.tensorChartModel (α.chartRep c z)) =
      FormField.tensorChartModel (α ((extChartAt 𝓘(ℝ, E) c).symm z)) := by
  apply ContinuousLinearMap.ext
  intro T
  have hT : T = (T (Fin.elim0)) • ContinuousMultilinearMap.uncurry0 ℝ E (1 : ℝ) := by
    apply ContinuousMultilinearMap.ext
    intro v
    have hv : v = Fin.elim0 := Subsingleton.elim _ _
    rw [hv]
    simp
  rw [hT]
  simp only [map_smul]
  rw [FormField.tensorChartModel_apply]
  have hbase := FormField.chartRep_eq_chartRSTwist_tensorChartModel α c hz
  rw [← hbase]
  simp

/-- The fixed-chart tensor inner product of the two form representatives is the pointwise
covariant tensor inner product of the forms at the represented point. The usual exterior pairing
is obtained by dividing both sides by `k!`. -/
theorem FormField.chartRep_chartTensorInner_eq_tensorInnerPointwise
    (g : CalabiYau.SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (α β : FormField E M k) (c : M) {z : E}
    (hz : z ∈ (extChartAt 𝓘(ℝ, E) c).target) :
    CalabiYau.ChartTensor.chartTensorInnerPointwiseRsModel
        (I := 𝓘(ℝ, E)) (M := M) g 0 k c ((extChartAt 𝓘(ℝ, E) c).symm z)
        (FormField.tensorChartModel (α.chartRep c z))
        (FormField.tensorChartModel (β.chartRep c z)) =
      CalabiYau.L2.tensorInnerPointwise (I := 𝓘(ℝ, E)) (M := M) g 0 k
        ((extChartAt 𝓘(ℝ, E) c).symm z)
        (FormField.tensorChartModel (α ((extChartAt 𝓘(ℝ, E) c).symm z)))
        (FormField.tensorChartModel (β ((extChartAt 𝓘(ℝ, E) c).symm z))) := by
  let y := (extChartAt 𝓘(ℝ, E) c).symm z
  have hy : y ∈ (chartAt E c).source := by
    rw [← extChartAt_source (I := 𝓘(ℝ, E))]
    exact (extChartAt 𝓘(ℝ, E) c).map_target hz
  have hb : y ∈ (trivializationAt E (TangentSpace (𝓘(ℝ, E))) c).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hy
  rw [CalabiYau.ChartTensor.chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise
    (I := 𝓘(ℝ, E)) (M := M) g 0 k c hb]
  rw [FormField.chartRSTwist_tensorChartModel_eq α c hz]
  rw [FormField.chartRSTwist_tensorChartModel_eq β c hz]
