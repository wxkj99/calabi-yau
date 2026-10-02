module

public import CalabiYau.Geometry.Kahler.Laplacian
public import CalabiYau.Geometry.Kahler.Ricci
public import CalabiYau.Geometry.Complex.Forms.OneOne
public import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.NormalFrameJets
import CalabiYau.MongeAmpere.Estimates.C2.NormalFrameLogDet

/-!
# Intrinsic Ricci and relative-volume coordinate bridge

This theorem identifies the intrinsic scalar
`-(tr_{ω₀}Ric(ω₀)-Δ_{ω₀}log relDet(ω₀,ω₁))` to the normal-frame coordinate Hessian of the
varying metric's log determinant.  The Ricci form is `-i∂∂̄ log det g`; the relative determinant
is the quotient of the varying and reference determinants.  Their reference log-determinant terms
cancel, leaving only the varying log determinant in reference normal coordinates.

The coordinate map in `YauNormalFrame` is holomorphic and has nonsingular Jacobian.  Under its
pullback the determinant acquires the squared norm of the holomorphic Jacobian.  The logarithm of
that factor is pluriharmonic, so its mixed complex Hessian vanishes.  This is why the coordinate
Hessian below is independent of the chosen realization of the normal frame, while the sign on the
left remains tied to the convention `Ric=-i∂∂̄ log det`.

This is a geometric bridge, separate from finite-dimensional differentiation of `log det`.  No
curvature bound or Monge–Ampère equation is used.  For `n=0`, the relative determinant is one and
both sides vanish; in `n=1` the determinant transition is the ordinary squared Jacobian norm.  The
pullback coefficient order is `J.transpose * G * J.map star`, with `J=i` preserving the unit
coefficient in the one-dimensional audit.
-/

@[expose] public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder Topology
open ContinuousAlternatingMap Filter

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

private theorem relTrace_eq_sum_of_normalized_pullback_trace
    (ωref η : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n))
    (hω : ωref.IsOneOne) (hα : η.IsOneOne)
    (hunit : (ωref.compContinuousLinearMap
        ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)).coeffMatrix = 1) :
    relTrace ωref η = ∑ p, RCLike.re
      ((η.compContinuousLinearMap
        ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)).coeffMatrix p p) := by
  have htrace := relTrace_compContinuousLinearMap hω hα A
  rw [← htrace]
  simp [relTrace, hunit, Matrix.trace]

private theorem normalFrame_jacobian_equiv
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x) :
    ∃ A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n),
      (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) =
        fderiv ℂ F.map F.center := by
  let A := fderiv ℂ F.map F.center
  have hmatrix : (EuclideanSpace.clmMatrix A).det ≠ 0 := by
    simpa [A, holomorphicJacobianMatrix] using F.jacobian_det_ne_zero
  have hclmMatrix : EuclideanSpace.clmMatrix A =
      LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
        (EuclideanSpace.basisFun (Fin n) ℂ).toBasis A.toLinearMap := by
    ext i j
    simp [EuclideanSpace.clmMatrix, LinearMap.toMatrix_apply,
      EuclideanSpace.basisFun_apply]
  have hdetEq : LinearMap.det A.toLinearMap = (EuclideanSpace.clmMatrix A).det := by
    calc
      LinearMap.det A.toLinearMap =
          Matrix.det (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
            (EuclideanSpace.basisFun (Fin n) ℂ).toBasis A.toLinearMap) :=
        (LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
          A.toLinearMap).symm
      _ = (EuclideanSpace.clmMatrix A).det := by rw [← hclmMatrix]
  have hdet : LinearMap.det A.toLinearMap ≠ 0 := fun h ↦ hmatrix (hdetEq ▸ h)
  have hker : LinearMap.ker A.toLinearMap = ⊥ := by
    by_contra hk
    have hzero : LinearMap.det A.toLinearMap = 0 :=
      (LinearMap.det_eq_zero_iff_ker_ne_bot).2 hk
    exact hdet hzero
  have hinj : Function.Injective A.toLinearMap := LinearMap.ker_eq_bot.mp hker
  have hsurj : Function.Surjective A.toLinearMap :=
    LinearMap.surjective_of_injective hinj
  let eLin := LinearEquiv.ofBijective A.toLinearMap ⟨hinj, hsurj⟩
  exact ⟨eLin.toContinuousLinearEquivOfContinuous
    eLin.toLinearMap.continuous_of_finiteDimensional, rfl⟩

private theorem normalFrame_relTrace_eq_sum
    (ω₀ ω₁ : KahlerForm n M) (η : FormField (EuclideanSpace ℂ (Fin n)) M 2)
    (x : M) (F : YauNormalFrame ω₀ ω₁ x) (hη : (η x).IsOneOne) :
    ∃ A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n),
      (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) =
        fderiv ℂ F.map F.center ∧
      relTrace (ω₀ x) (η x) = ∑ p, RCLike.re
        (((η x).compContinuousLinearMap
          ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)).coeffMatrix p p) := by
  obtain ⟨A, hA⟩ := normalFrame_jacobian_equiv ω₀ ω₁ x F
  have hcenter : F.map F.center = extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x :=
    F.center_eq_chart_center
  have hmetric : ω₀.metricInChart x (F.map F.center) = (ω₀ x).coeffMatrix := by
    rw [hcenter, ω₀.metricInChart_self]
  have hJ : holomorphicJacobianMatrix F.map F.center = EuclideanSpace.clmMatrix A := by
    simp [holomorphicJacobianMatrix, hA]
  have hnormal := F.reference_normalized
  change Matrix.transpose (holomorphicJacobianMatrix F.map F.center) *
      ω₀.metricInChart x (F.map F.center) *
      (holomorphicJacobianMatrix F.map F.center).map star = 1 at hnormal
  rw [hJ, hmetric] at hnormal
  have hunit : ((ω₀ x).compContinuousLinearMap
      ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)).coeffMatrix = 1 := by
    calc
      _ = Matrix.transpose (EuclideanSpace.clmMatrix A) * (ω₀ x).coeffMatrix *
          (EuclideanSpace.clmMatrix A).map star :=
        (ω₀.isOneOne x).coeffMatrix_compContinuousLinearMap A
      _ = 1 := hnormal
  refine ⟨A, hA, ?_⟩
  exact relTrace_eq_sum_of_normalized_pullback_trace (ω₀ x) (η x) A
    (ω₀.isOneOne x) hη hunit

private theorem normalFrame_ricci_pullback
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x)
    (A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n))
    (hA : (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) =
      fderiv ℂ F.map F.center) :
    (ω₁.ricciForm x).compContinuousLinearMap
        ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ) =
      -ddbar ((ω₁.logDetInChart x) ∘ F.map) F.center := by
  have hcenter : F.map F.center = extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x :=
    F.center_eq_chart_center
  have hFrameTarget : F.map F.center ∈
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target :=
    F.maps_into_chart F.center F.center_mem
  have hlogCenter : ContDiffAt ℝ 2 (ω₁.logDetInChart x)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) := by
    exact (ω₁.contDiffOn_logDetInChart x).contDiffAt
      (extChartAt_target_mem_nhds x) |>.of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hlog : ContDiffAt ℝ 2 (ω₁.logDetInChart x) (F.map F.center) := by
    rw [hcenter]
    exact hlogCenter
  have hψhol : ∀ᶠ z in 𝓝 F.center, DifferentiableAt ℂ F.map z := by
    filter_upwards [F.isOpen_domain.mem_nhds F.center_mem] with z hz
    exact (F.holomorphic_map z hz).differentiableAt (F.isOpen_domain.mem_nhds hz)
  have hRicciAt : ω₁.ricciForm x =
      -ddbar (ω₁.logDetInChart x) (F.map F.center) := by
    calc
      ω₁.ricciForm x =
          ω₁.ricciForm.chartRep x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) :=
        (FormField.chartRep_self ω₁.ricciForm x).symm
      _ = ω₁.ricciForm.chartRep x (F.map F.center) := by rw [← hcenter]
      _ = -ddbar (ω₁.logDetInChart x) (F.map F.center) :=
        ω₁.chartRep_ricciForm x hFrameTarget
  have hricciComp := congrArg (fun β : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ =>
      β.compContinuousLinearMap
        ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)) hRicciAt
  calc
    (ω₁.ricciForm x).compContinuousLinearMap
        ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ) =
      (-ddbar (ω₁.logDetInChart x) (F.map F.center)).compContinuousLinearMap
        ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ) := hricciComp
    _ = -(ddbar (ω₁.logDetInChart x) (F.map F.center)).compContinuousLinearMap
        ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ) := by
      ext v
      simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    _ = -ddbar ((ω₁.logDetInChart x) ∘ F.map) F.center := by
      rw [hA, ddbar_comp_holomorphic hψhol hlog]

private theorem normalFrame_ricci_composed_logdet_mixed
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x)
    (A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n))
    (hA : (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) =
      fderiv ℂ F.map F.center) (p : Fin n) :
    -RCLike.re (((ω₁.ricciForm x).compContinuousLinearMap
      ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)).coeffMatrix p p) =
      (chartPartialZComplex
        (fun z ↦ chartPartialBar ((ω₁.logDetInChart x) ∘ F.map) z p)
        F.center p).re := by
  let f : EuclideanSpace ℂ (Fin n) → ℝ := (ω₁.logDetInChart x) ∘ F.map
  have hFrameTarget : F.map F.center ∈
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target :=
    F.maps_into_chart F.center F.center_mem
  have hlogCenter : ContDiffAt ℝ 2 (ω₁.logDetInChart x)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) := by
    exact (ω₁.contDiffOn_logDetInChart x).contDiffAt
      (extChartAt_target_mem_nhds x) |>.of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hlog : ContDiffAt ℝ 2 (ω₁.logDetInChart x) (F.map F.center) := by
    rw [F.center_eq_chart_center]
    exact hlogCenter
  have hmap : ContDiffAt ℝ 2 F.map F.center := by
    exact (F.smooth_map.contDiffAt
      (F.isOpen_domain.mem_nhds F.center_mem)).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hf : ContDiffAt ℝ 2 f F.center := hlog.comp F.center hmap
  have hpull := normalFrame_ricci_pullback ω₀ ω₁ x F A hA
  have hc := congrArg (fun β : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ =>
    β.coeffMatrix p p) hpull
  have hcoeff : ((ω₁.ricciForm x).compContinuousLinearMap
      ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)).coeffMatrix p p =
      -complexHessian f F.center p p := by
    simpa [f, complexHessian] using hc
  rw [hcoeff]
  change (-(-((complexHessian f F.center p p).re))) = _
  rw [neg_neg, chartPartialZComplex_chartPartialBar f F.center hf p p]

private theorem normalFrame_ricci_logdet_diagonal
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x)
    (A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n))
    (hA : (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) =
      fderiv ℂ F.map F.center) (p : Fin n) :
    -RCLike.re (((ω₁.ricciForm x).compContinuousLinearMap
      ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)).coeffMatrix p p) =
      normalFrameLogDetSecondReal ω₀ ω₁ x F p := by
  let f : EuclideanSpace ℂ (Fin n) → ℝ := (ω₁.logDetInChart x) ∘ F.map
  have hlogCenter : ContDiffAt ℝ 2 (ω₁.logDetInChart x)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) := by
    exact (ω₁.contDiffOn_logDetInChart x).contDiffAt
      (extChartAt_target_mem_nhds x) |>.of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hlog : ContDiffAt ℝ 2 (ω₁.logDetInChart x) (F.map F.center) := by
    rw [F.center_eq_chart_center]
    exact hlogCenter
  have hmap : ContDiffAt ℝ 2 F.map F.center := by
    exact (F.smooth_map.contDiffAt
      (F.isOpen_domain.mem_nhds F.center_mem)).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hf : ContDiffAt ℝ 2 f F.center := hlog.comp F.center hmap
  have hψ : ContDiffAt ℝ 3 F.map F.center := by
    exact (F.smooth_map.contDiffAt
      (F.isOpen_domain.mem_nhds F.center_mem)).of_le
      (WithTop.coe_le_coe.mpr (show (3 : ℕ∞) ≤ ⊤ from le_top))
  have hψhol : ∀ᶠ z in 𝓝 F.center, DifferentiableAt ℂ F.map z := by
    filter_upwards [F.isOpen_domain.mem_nhds F.center_mem] with z hz
    exact (F.holomorphic_map z hz).differentiableAt (F.isOpen_domain.mem_nhds hz)
  have hchart : F.map F.center ∈
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target :=
    F.maps_into_chart F.center F.center_mem
  have hjet := pulledBackMetricInChart_log_det_mixed_second_real
    ω₁ x F.map F.center hψ hψhol hchart F.jacobian_det_ne_zero p
  have hjet' : normalFrameLogDetSecondReal ω₀ ω₁ x F p =
      (complexHessian f F.center p p).re := by
    simpa [normalFrameLogDetSecondReal, f] using hjet
  have hRicciJet := normalFrame_ricci_composed_logdet_mixed ω₀ ω₁ x F A hA p
  have hcofactor := chartPartialZComplex_chartPartialBar f F.center hf p p
  have hRicciHessian :
      -RCLike.re (((ω₁.ricciForm x).compContinuousLinearMap
        ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)).coeffMatrix p p) =
        (complexHessian f F.center p p).re := by
    rw [← hcofactor]
    exact hRicciJet
  exact hRicciHessian.trans hjet'.symm

/-- The reference Ricci and relative-volume terms reduce to the diagonal mixed Hessian of the
varying metric's log determinant in any Yau normal frame. -/
theorem normalFrame_relative_determinant_ricci_bridge
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x) :
    -(relTrace (ω₀ x) (ω₀.ricciForm x) -
        ω₀.laplacian (fun y ↦ Real.log (relDet (ω₀ y) (ω₁ y))) x) =
      ∑ p, normalFrameLogDetSecondReal ω₀ ω₁ x F p := by
  have hRicciForm : ω₁.ricciForm x =
      ω₀.ricciForm x - mddbar n (fun y ↦ Real.log (relDet (ω₀ y) (ω₁ y))) x :=
    congrFun (KahlerForm.ricciForm_eq_sub_mddbar ω₀ ω₁) x
  have hRicci := congrArg (relTrace (ω₀ x)) hRicciForm
  rw [ContinuousAlternatingMap.relTrace_sub] at hRicci
  have hFrameTarget : F.map F.center ∈
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target :=
    F.maps_into_chart F.center F.center_mem
  have hRicciCoordinate := congrArg
    (fun η : FormField (EuclideanSpace ℂ (Fin n)) M 2 => η.chartRep x (F.map F.center))
    (KahlerForm.ricciForm_eq_sub_mddbar ω₀ ω₁)
  have hsubCoordinate : (ω₀.ricciForm -
      mddbar n (fun y ↦ Real.log (relDet (ω₀ y) (ω₁ y)))).chartRep x (F.map F.center) =
      ω₀.ricciForm.chartRep x (F.map F.center) -
        (mddbar n (fun y ↦ Real.log (relDet (ω₀ y) (ω₁ y)))).chartRep x (F.map F.center) := by
    rw [sub_eq_add_neg, FormField.chartRep_add]
    change ω₀.ricciForm.chartRep x (F.map F.center) +
        (-mddbar n (fun y ↦ Real.log (relDet (ω₀ y) (ω₁ y)))).chartRep x
          (F.map F.center) = _
    rw [show -mddbar n (fun y ↦ Real.log (relDet (ω₀ y) (ω₁ y))) =
      (-1 : ℝ) • mddbar n (fun y ↦ Real.log (relDet (ω₀ y) (ω₁ y))) by simp,
      FormField.chartRep_smul]
    rw [sub_eq_add_neg, neg_one_smul]
    rfl
  rw [hsubCoordinate] at hRicciCoordinate
  have hlogRel := KahlerForm.contMDiff_log_relDet ω₀ ω₁
  have hRicciCoordinate' :
      -ddbar (ω₁.logDetInChart x) (F.map F.center) =
        -ddbar (ω₀.logDetInChart x) (F.map F.center) -
          ddbar ((fun y ↦ Real.log (relDet (ω₀ y) (ω₁ y))) ∘
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) (F.map F.center) := by
    rw [ω₁.chartRep_ricciForm x hFrameTarget, ω₀.chartRep_ricciForm x hFrameTarget,
      chartRep_mddbar hlogRel x hFrameTarget] at hRicciCoordinate
    exact hRicciCoordinate
  have hlap : ω₀.laplacian (fun y ↦ Real.log (relDet (ω₀ y) (ω₁ y))) x =
      relTrace (ω₀ x) (mddbar n (fun y ↦ Real.log (relDet (ω₀ y) (ω₁ y))) x) := rfl
  have hreduce : -(relTrace (ω₀ x) (ω₀.ricciForm x) -
      ω₀.laplacian (fun y ↦ Real.log (relDet (ω₀ y) (ω₁ y))) x) =
      -relTrace (ω₀ x) (ω₁.ricciForm x) := by
    rw [hlap]
    linarith
  rw [hreduce]
  have hlogAt : ContDiffAt ℝ 2 (ω₁.logDetInChart x)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) := by
    exact (ω₁.contDiffOn_logDetInChart x).contDiffAt
      (extChartAt_target_mem_nhds x) |>.of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hRicciOneOne : (ω₁.ricciForm x).IsOneOne := by
    change (-ddbar (ω₁.logDetInChart x)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x)).IsOneOne
    intro u v
    simp only [ContinuousAlternatingMap.neg_apply]
    exact congrArg Neg.neg (isOneOne_ddbar hlogAt u v)
  obtain ⟨A, hA, htrace⟩ := normalFrame_relTrace_eq_sum
    ω₀ ω₁ ω₁.ricciForm x F hRicciOneOne
  rw [htrace]
  calc
    -(∑ p, RCLike.re (((ω₁.ricciForm x).compContinuousLinearMap
        ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)).coeffMatrix p p)) =
        ∑ p, -RCLike.re (((ω₁.ricciForm x).compContinuousLinearMap
          ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)).coeffMatrix p p) := by
      simp
    _ = ∑ p, normalFrameLogDetSecondReal ω₀ ω₁ x F p := by
      apply Finset.sum_congr rfl
      intro p hp
      exact normalFrame_ricci_logdet_diagonal ω₀ ω₁ x F A hA p

end KahlerForm
