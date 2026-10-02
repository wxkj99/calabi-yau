module

public import CalabiYau.Geometry.Complex.DDBar.HermitianAdjoint
import CalabiYau.Geometry.Complex.Forms.TensorCoordinates
import CalabiYau.Geometry.Riemannian.TensorInner.ChartTensor.Inner.Defs
import CalabiYau.Geometry.Riemannian.TensorInner.ChartTensor.Inner.InnerJointCont

/-!
# Continuity of the pointwise Hermitian pairing of smooth forms

The forms are the project's unbundled `ComplexFormField` fields, rather than fixed-coordinate
coefficient tuples. Chart transport is required when proving continuity of their metric contraction.
Source: Morita, *Geometry of Differential Forms*, Ch. 4 §4.2.
-/

@[expose] public section

open Filter
open scoped Manifold ContDiff Topology

namespace ComplexFormField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable {k : ℕ}

private theorem chartTensorInnerPointwise_continuousOn_of_continuous_fields
    (g : CalabiYau.SmoothRiemannianMetric 𝓘(ℝ, E) M) (r s : ℕ) (c : M)
    (T U : E → CalabiYau.Tensor0SBundle.TensorRSModel r s ℝ E)
    (hT : ContinuousOn T (extChartAt 𝓘(ℝ, E) c).target)
    (hU : ContinuousOn U (extChartAt 𝓘(ℝ, E) c).target) :
    ContinuousOn
      (fun z : E => CalabiYau.ChartTensor.chartTensorInnerPointwiseRsModel
        (I := 𝓘(ℝ, E)) (M := M) g r s c
        ((extChartAt 𝓘(ℝ, E) c).symm z) (T z) (U z))
      (extChartAt 𝓘(ℝ, E) c).target := by
  let target := (extChartAt 𝓘(ℝ, E) c).target
  let baseSet := (trivializationAt E (TangentSpace (𝓘(ℝ, E))) c).baseSet
  have hsymm : ContinuousOn (extChartAt 𝓘(ℝ, E) c).symm target :=
    (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, E)) (n := ∞) c).continuousOn
  have hQ (V : E → CalabiYau.Tensor0SBundle.TensorRSModel r s ℝ E)
      (hV : ContinuousOn V target) :
      ContinuousOn (fun z : E =>
        CalabiYau.ChartTensor.chartTensorInnerPointwiseRsModel
          (I := 𝓘(ℝ, E)) (M := M) g r s c
          ((extChartAt 𝓘(ℝ, E) c).symm z) (V z) (V z)) target := by
    have hpairV : ContinuousOn (fun z : E =>
        ((extChartAt 𝓘(ℝ, E) c).symm z, V z)) target := hsymm.prodMk hV
    have hsubsetV : Set.MapsTo
        (fun z : E => ((extChartAt 𝓘(ℝ, E) c).symm z, V z)) target
        (baseSet ×ˢ Set.univ) := by
      intro z hz
      refine ⟨?_, Set.mem_univ _⟩
      change (extChartAt 𝓘(ℝ, E) c).symm z ∈
        (trivializationAt E (TangentSpace (𝓘(ℝ, E))) c).baseSet
      rw [TangentBundle.trivializationAt_baseSet,
        ← extChartAt_source (I := 𝓘(ℝ, E))]
      exact (extChartAt 𝓘(ℝ, E) c).map_target hz
    exact
      (CalabiYau.ChartTensor.chartTensorInnerPointwise_rs_model_quadratic_continuousOn
        (I := 𝓘(ℝ, E)) (M := M) g r s c).comp hpairV hsubsetV
  have hQT := hQ T hT
  have hQU := hQ U hU
  have hsum : ContinuousOn (fun z : E => T z + U z) target := hT.add hU
  have hQsum := hQ (fun z => T z + U z) hsum
  have hpolar (z : E) :
      CalabiYau.ChartTensor.chartTensorInnerPointwiseRsModel
          (I := 𝓘(ℝ, E)) (M := M) g r s c
          ((extChartAt 𝓘(ℝ, E) c).symm z) (T z) (U z) =
        (CalabiYau.ChartTensor.chartTensorInnerPointwiseRsModel
            (I := 𝓘(ℝ, E)) (M := M) g r s c
            ((extChartAt 𝓘(ℝ, E) c).symm z) (T z + U z) (T z + U z) -
          CalabiYau.ChartTensor.chartTensorInnerPointwiseRsModel
            (I := 𝓘(ℝ, E)) (M := M) g r s c
            ((extChartAt 𝓘(ℝ, E) c).symm z) (T z) (T z) -
          CalabiYau.ChartTensor.chartTensorInnerPointwiseRsModel
            (I := 𝓘(ℝ, E)) (M := M) g r s c
            ((extChartAt 𝓘(ℝ, E) c).symm z) (U z) (U z)) / 2 := by
    rw [CalabiYau.ChartTensor.chartTensorInnerPointwise_rs_model_add_left,
      CalabiYau.ChartTensor.chartTensorInnerPointwise_rs_model_add_right,
      CalabiYau.ChartTensor.chartTensorInnerPointwise_rs_model_add_right]
    rw [CalabiYau.ChartTensor.chartTensorInnerPointwise_rs_model_symm
      (I := 𝓘(ℝ, E)) (M := M) g r s c ((extChartAt 𝓘(ℝ, E) c).symm z) (U z) (T z)]
    ring
  rw [show (fun z : E =>
      CalabiYau.ChartTensor.chartTensorInnerPointwiseRsModel
        (I := 𝓘(ℝ, E)) (M := M) g r s c
        ((extChartAt 𝓘(ℝ, E) c).symm z) (T z) (U z)) =
      fun z => (CalabiYau.ChartTensor.chartTensorInnerPointwiseRsModel
            (I := 𝓘(ℝ, E)) (M := M) g r s c
            ((extChartAt 𝓘(ℝ, E) c).symm z) (T z + U z) (T z + U z) -
          CalabiYau.ChartTensor.chartTensorInnerPointwiseRsModel
            (I := 𝓘(ℝ, E)) (M := M) g r s c
            ((extChartAt 𝓘(ℝ, E) c).symm z) (T z) (T z) -
          CalabiYau.ChartTensor.chartTensorInnerPointwiseRsModel
            (I := 𝓘(ℝ, E)) (M := M) g r s c
            ((extChartAt 𝓘(ℝ, E) c).symm z) (U z) (U z)) / 2 from funext hpolar]
  exact ((hQsum.sub hQT).sub hQU).div_const 2

private theorem chartTensorModel_continuousOn_of_smooth
    {k : ℕ} (α : FormField E M k) (hα : α.IsSmooth) (c : M) :
    ContinuousOn
      (fun z : E => FormField.tensorChartModel (α.chartRep c z))
      (extChartAt 𝓘(ℝ, E) c).target := by
  have hchart : ContinuousOn (fun z : E => α.chartRep c z)
      (extChartAt 𝓘(ℝ, E) c).target := (hα c).continuousOn
  let L : (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ]
      CalabiYau.Tensor0SBundle.TensorRSModel 0 k ℝ E :=
    (ContinuousLinearMap.smulRightL ℝ
      (CalabiYau.Tensor0SBundle.Tensor0SModel 0 ℝ E)
      (ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ)
      (continuousMultilinearCurryFin0 ℝ E ℝ).toContinuousLinearMap).comp
      (ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ)
  have hmap : Continuous
      (fun η : E [⋀^Fin k]→L[ℝ] ℝ => FormField.tensorChartModel η) := by
    change Continuous (fun η => L η)
    exact L.continuous
  exact hmap.comp_continuousOn hchart

private theorem lower_tensorChartModel_eq_form
    (g : CalabiYau.SmoothRiemannianMetric 𝓘(ℝ, E) M) (x : M)
    (η : E [⋀^Fin k]→L[ℝ] ℝ) :
    CalabiYau.L2.lowerAllUpperIndices (I := 𝓘(ℝ, E)) (M := M) g 0 k x
      (FormField.tensorChartModel η) =
        η.toContinuousMultilinearMap.domDomCongr
          ((Fin.castOrderIso (Nat.zero_add k)).symm.toEquiv) := by
  ext v
  simp [CalabiYau.L2.lowerAllUpperIndices_apply, FormField.tensorChartModel_apply]
  congr 1
  funext i
  congr 1
  apply Fin.ext
  simp [Fin.natAdd, Fin.castOrderIso]

private theorem covariantTensorInner_zeroAdd
    (g : CalabiYau.SmoothRiemannianMetric 𝓘(ℝ, E) M) (x : M)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) :
    CalabiYau.L2.covariantTensorInnerPointwise (I := 𝓘(ℝ, E)) (M := M) k g x S T =
      CalabiYau.L2.covariantTensorInnerPointwise (I := 𝓘(ℝ, E)) (M := M) (0 + k) g x
        (S.domDomCongr ((Fin.castOrderIso (Nat.zero_add k)).symm.toEquiv))
        (T.domDomCongr ((Fin.castOrderIso (Nat.zero_add k)).symm.toEquiv)) := by
  induction k with
  | zero => simp [CalabiYau.L2.covariantTensorInnerPointwise, Fin.castOrderIso]
  | succ n ih =>
      unfold CalabiYau.L2.covariantTensorInnerPointwise
      have hCurry (A : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => E) ℝ)
          (b : E) :
          (A.domDomCongr ((Fin.castOrderIso (Nat.zero_add (n + 1))).symm.toEquiv)).curryLeft b =
            (A.curryLeft b).domDomCongr
              ((Fin.castOrderIso (Nat.zero_add n)).symm.toEquiv) := by
        apply ContinuousMultilinearMap.ext
        intro v
        apply congrArg A
        funext i
        cases i using Fin.cases <;> simp [Fin.cons, Fin.castOrderIso]
      apply congrArg (fun t : ℝ => t)
      refine Finset.sum_congr rfl ?_
      intro i hi
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [hCurry, hCurry, ih]
      rfl

private theorem pointwiseRealInner_eq_tensorChartModel_inner
    (g : CalabiYau.SmoothRiemannianMetric 𝓘(ℝ, E) M) (x : M)
    (α β : FormField E M k) :
    FormField.pointwiseRealInner g k x α β =
      CalabiYau.L2.tensorInnerPointwise (I := 𝓘(ℝ, E)) (M := M) g 0 k x
        (FormField.tensorChartModel (α x)) (FormField.tensorChartModel (β x)) /
          (Nat.factorial k : ℝ) := by
  rw [FormField.pointwiseRealInner, CalabiYau.L2.tensorInnerPointwise]
  rw [lower_tensorChartModel_eq_form g x (α x),
    lower_tensorChartModel_eq_form g x (β x)]
  congr 1
  exact covariantTensorInner_zeroAdd g x
    (α x).toContinuousMultilinearMap (β x).toContinuousMultilinearMap

private theorem pointwiseRealInner_continuousOn_chart_of_smooth
    (g : CalabiYau.SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {α β : FormField E M k} (hα : α.IsSmooth) (hβ : β.IsSmooth) (c : M) :
    ContinuousOn
      (fun z : E => FormField.pointwiseRealInner g k
        ((extChartAt 𝓘(ℝ, E) c).symm z) α β)
      (extChartAt 𝓘(ℝ, E) c).target := by
  let target := (extChartAt 𝓘(ℝ, E) c).target
  let T : E → CalabiYau.Tensor0SBundle.TensorRSModel 0 k ℝ E :=
    fun z => FormField.tensorChartModel (α.chartRep c z)
  let U : E → CalabiYau.Tensor0SBundle.TensorRSModel 0 k ℝ E :=
    fun z => FormField.tensorChartModel (β.chartRep c z)
  have hT := chartTensorModel_continuousOn_of_smooth α hα c
  have hU := chartTensorModel_continuousOn_of_smooth β hβ c
  have hpair := chartTensorInnerPointwise_continuousOn_of_continuous_fields
    g 0 k c T U hT hU
  have hcont : ContinuousOn (fun z : E =>
      CalabiYau.ChartTensor.chartTensorInnerPointwiseRsModel
        (I := 𝓘(ℝ, E)) (M := M) g 0 k c
        ((extChartAt 𝓘(ℝ, E) c).symm z) (T z) (U z) /
          (Nat.factorial k : ℝ)) target := hpair.div_const _
  refine hcont.congr ?_
  intro z hz
  have hreal := pointwiseRealInner_eq_tensorChartModel_inner
    g ((extChartAt 𝓘(ℝ, E) c).symm z) α β
  simp only [T, U]
  rw [hreal]
  rw [← FormField.chartRep_chartTensorInner_eq_tensorInnerPointwise
    g α β c hz]

private theorem pointwiseRealInner_continuous_of_smooth
    (g : CalabiYau.SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {α β : FormField E M k} (hα : α.IsSmooth) (hβ : β.IsSmooth) :
    Continuous (fun x => FormField.pointwiseRealInner g k x α β) := by
  let f : M → ℝ := fun x => FormField.pointwiseRealInner g k x α β
  rw [continuous_iff_continuousAt]
  intro x
  let e := extChartAt 𝓘(ℝ, E) x
  have ht : e x ∈ e.target := mem_extChartAt_target x
  have hopen : e.target ∈ 𝓝 (e x) := (isOpen_extChartAt_target x).mem_nhds ht
  have hf : ContinuousAt (fun z : E => f (e.symm z)) (e x) := by
    exact (pointwiseRealInner_continuousOn_chart_of_smooth g hα hβ x).continuousAt hopen
  have hcomp : ContinuousAt (fun y : M => f (e.symm (e y))) x :=
    hf.comp (continuousAt_extChartAt x)
  have heq : (fun y : M => f (e.symm (e y))) =ᶠ[𝓝 x] f := by
    filter_upwards [extChartAt_source_mem_nhds (I := 𝓘(ℝ, E)) x] with y hy
    have hxy : (extChartAt 𝓘(ℝ, E) x).symm
        ((extChartAt 𝓘(ℝ, E) x) y) = y := (extChartAt 𝓘(ℝ, E) x).left_inv hy
    simpa [e] using congrArg f hxy
  exact hcomp.congr_of_eventuallyEq heq.symm

/-- Smooth complex forms have a continuous pointwise Hermitian contraction with a smooth metric.
The two complex components are real smooth form fields on the *actual* tangent model. -/
theorem continuous_pointwiseHermitianInner
    (g : CalabiYau.SmoothRiemannianMetric 𝓘(ℝ, E) M) (k : ℕ)
    (α β : ComplexFormField E M k) (hα : α.IsSmooth) (hβ : β.IsSmooth) :
    Continuous (fun x : M => pointwiseHermitianInner g k x α β) := by
  have h₁ := pointwiseRealInner_continuous_of_smooth g hα.1 hβ.1
  have h₂ := pointwiseRealInner_continuous_of_smooth g hα.2 hβ.2
  have h₃ := pointwiseRealInner_continuous_of_smooth g hα.1 hβ.2
  have h₄ := pointwiseRealInner_continuous_of_smooth g hα.2 hβ.1
  unfold pointwiseHermitianInner
  fun_prop

end ComplexFormField
