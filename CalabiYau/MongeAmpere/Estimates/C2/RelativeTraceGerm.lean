module

public import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.NormalCoordinates
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The relative scalar trace in a genuine normal-frame germ

Székelyhidi §3.2, proof of Lemma 3.7, p.41: the normal-coordinate reduction
identifies the intrinsic scalar with the pulled-back matrix trace before taking
its mixed Hessian. Equality only at the center, or only of first derivatives,
cannot justify that operation. The identity here holds on a neighborhood.

The coefficient pullback convention is `J.transpose * H * J.map star`.
The open frame domain and the nonsingular center Jacobian are hypotheses carried
by `F`; continuity makes the Jacobian nonsingular on a smaller neighborhood.
-/

open scoped Manifold ContDiff ComplexOrder MatrixOrder Topology
open ContinuousAlternatingMap Filter

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

private noncomputable def tangentCoordChange_complex_equiv (x y : M)
    (hyx : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source) :
    EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n) := by
  let C := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y
  let D := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y x y
  have hxy : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source := by simp
  have hCleft (v : EuclideanSpace ℂ (Fin n)) : D (C v) = v := by
    calc
      _ = tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x x y v := by
        exact tangentCoordChange_comp
          (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n))) (w := x) (x := y) (y := x)
          (z := y) ⟨⟨hyx, hxy⟩, hyx⟩
      _ = v := tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n))) hyx
  have hCright (v : EuclideanSpace ℂ (Fin n)) : C (D v) = v := by
    calc
      _ = tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y y y v := by
        exact tangentCoordChange_comp
          (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n))) (w := y) (x := x) (y := y)
          (z := y) ⟨⟨hxy, hyx⟩, hxy⟩
      _ = v := tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n))) hxy
  let eLin := LinearEquiv.ofBijective (C : EuclideanSpace ℂ (Fin n) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin n)) ⟨by
        intro v w h
        calc
          v = D (C v) := (hCleft v).symm
          _ = D (C w) := congrArg D h
          _ = w := hCleft w
      , by
        intro v
        exact ⟨D v, hCright v⟩⟩
  exact eLin.toContinuousLinearEquivOfContinuous
    eLin.toLinearMap.continuous_of_finiteDimensional

private theorem relativeTrace_eq_chartRep
    (ω₀ ω₁ : KahlerForm n M) (x : M)
    (z : EuclideanSpace ℂ (Fin n))
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    relTrace (ω₀ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z))
      (ω₁ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z)) =
    RCLike.re ((ω₀.metricInChart x z)⁻¹ * ω₁.metricInChart x z).trace := by
  let y := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z
  have hyxR : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source :=
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).map_target hz
  have hyxC : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source := by
    simpa [extChartAt_real_eq, ← extChartAt_source] using hyxR
  have hyyC : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source := by simp
  let C := tangentCoordChange_complex_equiv x y hyxC
  have hCreal : tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y =
      (C : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ := by
    change tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y =
      (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y).restrictScalars ℝ
    exact tangentCoordChange_real_eq ⟨hyxC, hyyC⟩
  have hω₀ : (ω₀ y).IsOneOne := (ContinuousAlternatingMap.isPositive_iff.mp
    (ω₀.isPositive y)).1
  have hω₁ : (ω₁ y).IsOneOne := (ContinuousAlternatingMap.isPositive_iff.mp
    (ω₁.isPositive y)).1
  have hcomp := ContinuousAlternatingMap.relTrace_compContinuousLinearMap hω₀ hω₁ C
  have hrep₀ : ω₀.toFormField.chartRep x z =
      (ω₀ y).compContinuousLinearMap
        ((C : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ) := by
    change (ω₀ y).compContinuousLinearMap
      (tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y) = _
    rw [hCreal]
  have hrep₁ : ω₁.toFormField.chartRep x z =
      (ω₁ y).compContinuousLinearMap
        ((C : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ) := by
    change (ω₁ y).compContinuousLinearMap
      (tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y) = _
    rw [hCreal]
  rw [← hrep₀, ← hrep₁] at hcomp
  change ContinuousAlternatingMap.relTrace (ω₀.toFormField.chartRep x z)
    (ω₁.toFormField.chartRep x z) = _ at hcomp
  change ContinuousAlternatingMap.relTrace (ω₀.toFormField y) (ω₁.toFormField y) =
    ContinuousAlternatingMap.relTrace (ω₀.toFormField.chartRep x z)
      (ω₁.toFormField.chartRep x z)
  exact hcomp.symm

private noncomputable def complexJacobian_equiv_of_det
    (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hdet : (EuclideanSpace.clmMatrix A).det ≠ 0) :
    EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n) := by
  let b : Module.Basis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)) :=
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
  have hC : EuclideanSpace.clmMatrix A =
      LinearMap.toMatrix b b (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) := by
    ext i j
    simp [EuclideanSpace.clmMatrix, LinearMap.toMatrix_apply, b,
      EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
  have hUnit : IsUnit (LinearMap.toMatrix b b
      (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))).det := by
    rw [← hC]
    exact isUnit_iff_ne_zero.mpr hdet
  let eLin := LinearEquiv.ofIsUnitDet (v := b) (v' := b)
    (f := (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))) hUnit
  exact eLin.toContinuousLinearEquivOfContinuous
    eLin.toLinearMap.continuous_of_finiteDimensional

private theorem relativeTrace_eq_pulledBack_frame_metric
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x)
    (w : EuclideanSpace ℂ (Fin n)) (hw : w ∈ F.domain)
    (hdet : (holomorphicJacobianMatrix F.map w).det ≠ 0) :
    relTrace (ω₀ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm (F.map w)))
      (ω₁ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm (F.map w))) =
    RCLike.re ((pulledBackMetricInChart ω₀ x F.map w)⁻¹ *
      pulledBackMetricInChart ω₁ x F.map w).trace := by
  let z := F.map w
  let y := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z
  have hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target :=
    F.maps_into_chart w hw
  have hchart := relativeTrace_eq_chartRep ω₀ ω₁ x z hz
  let J : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    fderiv ℂ F.map w
  let A := complexJacobian_equiv_of_det J hdet
  have hyxR : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source :=
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).map_target hz
  have hyxC : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source := by
    simpa [extChartAt_real_eq, ← extChartAt_source] using hyxR
  have hyyC : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source := by simp
  let Cclm := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y
  let CEquiv := tangentCoordChange_complex_equiv x y hyxC
  have hCreal : tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y =
      Cclm.restrictScalars ℝ := by
    change tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y =
      (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y).restrictScalars ℝ
    exact tangentCoordChange_real_eq ⟨hyxC, hyyC⟩
  have htype0 : ((ω₀.toFormField y).compContinuousLinearMap
      (Cclm.restrictScalars ℝ)).IsOneOne :=
    ((ContinuousAlternatingMap.isPositive_iff.mp (ω₀.isPositive y)).1).compContinuousLinearMap CEquiv
  have htype1 : ((ω₁.toFormField y).compContinuousLinearMap
      (Cclm.restrictScalars ℝ)).IsOneOne :=
    ((ContinuousAlternatingMap.isPositive_iff.mp (ω₁.isPositive y)).1).compContinuousLinearMap CEquiv
  have hrep0 : ω₀.toFormField.chartRep x z =
      (ω₀.toFormField y).compContinuousLinearMap (Cclm.restrictScalars ℝ) := by
    change (ω₀.toFormField y).compContinuousLinearMap
      (tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y) = _
    rw [hCreal]
  have hrep1 : ω₁.toFormField.chartRep x z =
      (ω₁.toFormField y).compContinuousLinearMap (Cclm.restrictScalars ℝ) := by
    change (ω₁.toFormField y).compContinuousLinearMap
      (tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y) = _
    rw [hCreal]
  have hrepType0 : (ω₀.toFormField.chartRep x z).IsOneOne := by
    rw [hrep0]
    exact htype0
  have hrepType1 : (ω₁.toFormField.chartRep x z).IsOneOne := by
    rw [hrep1]
    exact htype1
  have hcoeff0 : ((ω₀.toFormField.chartRep x z).compContinuousLinearMap
      ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)).coeffMatrix =
      pulledBackMetricInChart ω₀ x F.map w := by
    rw [ContinuousAlternatingMap.IsOneOne.coeffMatrix_compContinuousLinearMap hrepType0 A]
    rfl
  have hcoeff1 : ((ω₁.toFormField.chartRep x z).compContinuousLinearMap
      ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)).coeffMatrix =
      pulledBackMetricInChart ω₁ x F.map w := by
    rw [ContinuousAlternatingMap.IsOneOne.coeffMatrix_compContinuousLinearMap hrepType1 A]
    rfl
  have htrace := ContinuousAlternatingMap.relTrace_compContinuousLinearMap hrepType0 hrepType1 A
  change RCLike.re (((ω₀.toFormField.chartRep x z).compContinuousLinearMap
      ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)).coeffMatrix⁻¹ *
        ((ω₁.toFormField.chartRep x z).compContinuousLinearMap
          ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)).coeffMatrix).trace =
    RCLike.re ((ω₀.toFormField.chartRep x z).coeffMatrix⁻¹ *
      (ω₁.toFormField.chartRep x z).coeffMatrix).trace at htrace
  rw [hcoeff0, hcoeff1] at htrace
  change RCLike.re ((pulledBackMetricInChart ω₀ x F.map w)⁻¹ *
      pulledBackMetricInChart ω₁ x F.map w).trace =
    RCLike.re ((ω₀.metricInChart x z)⁻¹ * ω₁.metricInChart x z).trace at htrace
  calc
    relTrace (ω₀ y) (ω₁ y) =
        RCLike.re ((ω₀.metricInChart x z)⁻¹ * ω₁.metricInChart x z).trace := hchart
    _ = RCLike.re ((pulledBackMetricInChart ω₀ x F.map w)⁻¹ *
        pulledBackMetricInChart ω₁ x F.map w).trace := htrace.symm

open scoped Topology in
private theorem frame_jacobian_det_eventually_ne_zero
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x) :
    ∀ᶠ w in 𝓝 F.center,
      (holomorphicJacobianMatrix F.map w).det ≠ 0 := by
  let Jreal : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ := fun w =>
    Matrix.of fun i j => fderiv ℝ F.map w (EuclideanSpace.single j 1) i
  have hFat : ContDiffAt ℝ 1 F.map F.center :=
    (F.smooth_map.contDiffAt (F.isOpen_domain.mem_nhds F.center_mem)).of_le (by norm_num)
  have hFfd : ContinuousAt (fderiv ℝ F.map) F.center :=
    hFat.continuousAt_fderiv (by norm_num)
  have hJreal : ContinuousAt Jreal F.center := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    fun_prop (disch := assumption)
  have hJeq : ∀ᶠ w in 𝓝 F.center,
      holomorphicJacobianMatrix F.map w = Jreal w := by
    filter_upwards [F.isOpen_domain.mem_nhds F.center_mem] with w hw
    have hhol : DifferentiableAt ℂ F.map w :=
      (F.holomorphic_map w hw).differentiableAt (F.isOpen_domain.mem_nhds hw)
    have hderiv : fderiv ℝ F.map w = (fderiv ℂ F.map w).restrictScalars ℝ :=
      hhol.fderiv_restrictScalars ℝ
    ext i j
    simp [holomorphicJacobianMatrix, Jreal, EuclideanSpace.clmMatrix, hderiv]
  have hdetcont : ContinuousAt (fun w => (Jreal w).det) F.center := by
    fun_prop
  have hdetval : (Jreal F.center).det ≠ 0 := by
    have h := hJeq.self_of_nhds
    rw [← h]
    exact F.jacobian_det_ne_zero
  filter_upwards [hdetcont.eventually_ne hdetval, hJeq] with w hdet hmatrix
  rw [hmatrix]
  exact hdet

open scoped Topology in
private theorem relativeTrace_eq_pulledBack_matrix_eventually
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x) :
    ∀ᶠ w in 𝓝 F.center,
      relTrace (ω₀ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm (F.map w)))
        (ω₁ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm (F.map w))) =
      RCLike.re ((pulledBackMetricInChart ω₀ x F.map w)⁻¹ *
        pulledBackMetricInChart ω₁ x F.map w).trace := by
  have hdet := frame_jacobian_det_eventually_ne_zero ω₀ ω₁ x F
  filter_upwards [F.isOpen_domain.mem_nhds F.center_mem, hdet] with w hw hdet
  exact relativeTrace_eq_pulledBack_frame_metric ω₀ ω₁ x F w hw hdet

/-- The intrinsic relative trace and the real pulled-back matrix trace agree as
scalar germs at the normal center. All chart and holomorphic-map assumptions are
explicit fields of the genuine frame hypothesis `F`. -/
public theorem normalFrame_relative_trace_eventually_eq_matrix_trace
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x) :
    (fun z ↦ relTrace (ω₀ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm
        (F.map z))) (ω₁ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm
        (F.map z)))) =ᶠ[𝓝 F.center]
      fun z ↦ (((pulledBackMetricInChart ω₀ x F.map z)⁻¹ *
        pulledBackMetricInChart ω₁ x F.map z).trace).re := by
  have h := relativeTrace_eq_pulledBack_matrix_eventually ω₀ ω₁ x F
  filter_upwards [h] with z hz
  simpa [Complex.re] using hz

end KahlerForm
