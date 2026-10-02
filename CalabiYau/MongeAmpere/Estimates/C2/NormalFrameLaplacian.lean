module

public import CalabiYau.Geometry.Kahler.Laplacian
public import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.NormalCoordinates

/-!
# The scalar Laplacian in a holomorphic normal frame

This module transports the intrinsic complex Laplacian to the diagonal coordinates of a genuine
holomorphic normal frame. The local regularity assumption is only at the point of evaluation.
-/

@[expose] public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder
open ContinuousAlternatingMap Filter

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- A complex-linear continuous equivalence representing the differential of a holomorphic normal
frame at its center. -/
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

private theorem normalFrame_varying_metric_coeffMatrix
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x) :
    ∃ A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n),
      (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) =
        fderiv ℂ F.map F.center ∧
      ((ω₁ x).compContinuousLinearMap
        ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)).coeffMatrix =
        Matrix.diagonal (RCLike.ofReal ∘ F.eigenvalue) := by
  obtain ⟨A, hA⟩ := normalFrame_jacobian_equiv ω₀ ω₁ x F
  have hcenter : F.map F.center =
      extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x := F.center_eq_chart_center
  have hmetric : ω₁.metricInChart x (F.map F.center) = (ω₁ x).coeffMatrix := by
    rw [hcenter, ω₁.metricInChart_self]
  have hJ : holomorphicJacobianMatrix F.map F.center = EuclideanSpace.clmMatrix A := by
    simp [holomorphicJacobianMatrix, hA]
  have hnormal := F.varying_diagonal
  change Matrix.transpose (holomorphicJacobianMatrix F.map F.center) *
      ω₁.metricInChart x (F.map F.center) *
        (holomorphicJacobianMatrix F.map F.center).map star = _ at hnormal
  rw [hJ, hmetric] at hnormal
  refine ⟨A, hA, ?_⟩
  calc
    ((ω₁ x).compContinuousLinearMap
        ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)).coeffMatrix =
      Matrix.transpose (EuclideanSpace.clmMatrix A) * (ω₁ x).coeffMatrix *
        (EuclideanSpace.clmMatrix A).map star :=
      (ω₁.isOneOne x).coeffMatrix_compContinuousLinearMap A
    _ = Matrix.diagonal (RCLike.ofReal ∘ F.eigenvalue) := hnormal

private theorem relTrace_eq_sum_of_diagonal_coeffMatrix
    (α β : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (eig : Fin n → ℝ) (heig : ∀ p, 0 < eig p)
    (hdiag : α.coeffMatrix = Matrix.diagonal (RCLike.ofReal ∘ eig)) :
    relTrace α β = ∑ p, RCLike.re (β.coeffMatrix p p) / eig p := by
  rw [relTrace, hdiag, Matrix.inv_diagonal]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  simp only [Matrix.diagonal_apply]
  simp
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  let v : Fin n → ℂ := Complex.ofReal ∘ eig
  let w : Fin n → ℂ := fun q ↦ (v q)⁻¹
  have hvw : v * w = 1 := by
    ext q
    simp [v, w, Function.comp_apply, ne_of_gt (heig q)]
  have hunit : IsUnit v := (isUnit_iff_exists_inv).2 ⟨w, hvw⟩
  have hinv : Ring.inverse (Complex.ofReal ∘ eig) =
      fun q ↦ Complex.ofReal ((eig q)⁻¹) := by
    rw [show (Complex.ofReal ∘ eig) = v by rfl, Ring.inverse_of_isUnit hunit]
    ext q
    simp [v]
  rw [hinv]
  simp [Complex.ofReal_re, Complex.ofReal_im, div_eq_mul_inv]
  field_simp [ne_of_gt (heig p)]

private theorem normalFrame_mddbar_pullback
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x)
    (f : M → ℝ) (hf : ContDiffAt ℝ 2
      (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
      (F.map F.center))
    (A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n))
    (hA : (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) =
      fderiv ℂ F.map F.center) :
    (mddbar n f x).compContinuousLinearMap
        ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ) =
      ddbar ((f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) ∘ F.map)
        F.center := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let g := f ∘ e.symm
  have hcenter : F.map F.center = e x := F.center_eq_chart_center
  have hhol : ∀ᶠ z in nhds F.center, DifferentiableAt ℂ F.map z := by
    filter_upwards [F.isOpen_domain.mem_nhds F.center_mem] with z hz
    exact (F.holomorphic_map z hz).differentiableAt (F.isOpen_domain.mem_nhds hz)
  change (ddbar g (e x)).compContinuousLinearMap
      ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ) =
    ddbar (g ∘ F.map) F.center
  rw [← hcenter, hA]
  exact (ddbar_comp_holomorphic hhol hf).symm

private theorem normalFrame_laplacian_eq_pulledback_relTrace
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x)
    (f : M → ℝ) (hf : ContDiffAt ℝ 2
      (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
      (F.map F.center))
    (A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n))
    (hA : (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) =
      fderiv ℂ F.map F.center) :
      ω₁.laplacian f x = relTrace
        ((ω₁ x).compContinuousLinearMap
          ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ))
        (ddbar ((f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) ∘ F.map)
          F.center) := by
  have hη : (mddbar n f x).IsOneOne := by
    change (ddbar (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x)).IsOneOne
    rw [← F.center_eq_chart_center]
    exact isOneOne_ddbar hf
  have htrace := relTrace_compContinuousLinearMap (ω₁.isOneOne x) hη A
  calc
    ω₁.laplacian f x = relTrace (ω₁ x) (mddbar n f x) := rfl
    _ = relTrace
        ((ω₁ x).compContinuousLinearMap
          ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ))
        ((mddbar n f x).compContinuousLinearMap
          ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)) :=
      htrace.symm
    _ = relTrace
        ((ω₁ x).compContinuousLinearMap
          ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ))
        (ddbar ((f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) ∘ F.map)
          F.center) := by
      rw [normalFrame_mddbar_pullback ω₀ ω₁ x F f hf A hA]

/-- In holomorphic normal-frame coordinates the complex Laplacian is the diagonal sum of the
mixed complex Hessian divided by the eigenvalues of the varying metric. -/
theorem normalFrame_laplacian_eq_hessian_sum
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x) (f : M → ℝ)
    (hf : ContDiffAt ℝ 2
      (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
      (F.map F.center)) :
    ω₁.laplacian f x = ∑ p,
      RCLike.re (complexHessian
        ((f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) ∘ F.map)
        F.center p p) / F.eigenvalue p := by
  obtain ⟨A, hA, hdiag⟩ := normalFrame_varying_metric_coeffMatrix ω₀ ω₁ x F
  have hlap := normalFrame_laplacian_eq_pulledback_relTrace ω₀ ω₁ x F f hf A hA
  rw [hlap]
  simpa [complexHessian] using
    (relTrace_eq_sum_of_diagonal_coeffMatrix
      ((ω₁ x).compContinuousLinearMap
        ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ))
      (ddbar ((f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) ∘ F.map)
        F.center) F.eigenvalue F.eigenvalue_pos hdiag)

end KahlerForm
