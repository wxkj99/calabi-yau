module

public import CalabiYau.Geometry.Kahler.Laplacian
public import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.NormalCoordinates

/-!
# The scalar gradient in a holomorphic normal frame

This module transports the intrinsic complex gradient norm to the diagonal coordinates of a genuine
holomorphic normal frame. The local regularity assumption is only at the point of evaluation.
-/

@[expose] public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder
open ContinuousAlternatingMap Filter

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

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

private theorem normalFrame_mdWedgeDBar_pullback
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x)
    (f : M → ℝ) (hf : ContDiffAt ℝ 1
      (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
      (F.map F.center))
    (A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n))
    (hA : (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) =
      fderiv ℂ F.map F.center) :
    (mdWedgeDBar n f x).compContinuousLinearMap
        ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ) =
      dWedgeDBar (fderiv ℝ
        (fun z ↦ f ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm (F.map z))) F.center) := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let g := f ∘ e.symm
  have hcenter : F.map F.center = e x := F.center_eq_chart_center
  have hmap : DifferentiableAt ℂ F.map F.center :=
    (F.holomorphic_map F.center F.center_mem).differentiableAt
      (F.isOpen_domain.mem_nhds F.center_mem)
  have hmapR : HasFDerivAt F.map
      ((fderiv ℂ F.map F.center).restrictScalars ℝ) F.center :=
    hmap.hasFDerivAt.restrictScalars ℝ
  have hAreal : fderiv ℝ F.map F.center =
      (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ := by
    rw [hA]
    exact hmap.fderiv_restrictScalars ℝ
  have hchain := fderiv_comp (f := F.map) (g := g) (x := F.center)
    (hf.differentiableAt (by norm_num)) hmapR.differentiableAt
  rw [hcenter, hAreal] at hchain
  have hchain' : fderiv ℝ (fun z ↦ f (e.symm (F.map z))) F.center =
      (fderiv ℝ g (e x)).comp
        ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ) := by
    simpa only [g, e, Function.comp_def] using hchain
  have heval (ℓ : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ)
      (u v : EuclideanSpace ℂ (Fin n)) :
      (dWedgeDBar ℓ) ![u, v] = (ℓ (Complex.I • u) * ℓ v -
        ℓ (Complex.I • v) * ℓ u) / 2 := by
    change ((1 / 2 : ℝ) • ContinuousAlternatingMap.alternatizeUncurryFin
      ((ℓ.comp (Complex.I • ContinuousLinearMap.id ℝ (EuclideanSpace ℂ (Fin n)))).smulRight
        (ofSubsingleton ℝ (EuclideanSpace ℂ (Fin n)) ℝ (0 : Fin 1) ℓ))) ![u, v] = _
    simp [ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.removeNth]
    ring
  have hnatural (ℓ : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) :
      dWedgeDBar (ℓ.comp
        ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)) =
        (dWedgeDBar ℓ).compContinuousLinearMap
          ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ) := by
    ext v
    have hv : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hv, ContinuousAlternatingMap.compContinuousLinearMap_apply, heval]
    have htuple :
        ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ) ∘
            ![v 0, v 1] =
          ![((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)
              (v 0),
            ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)
              (v 1)] := by
      funext i
      fin_cases i <;> rfl
    rw [htuple, heval]
    simp [ContinuousLinearMap.comp_apply]
  change (dWedgeDBar (fderiv ℝ g (e x))).compContinuousLinearMap
      ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ) = _
  rw [hchain']
  exact (hnatural (fderiv ℝ g (e x))).symm

/-- In holomorphic normal-frame coordinates the complex gradient norm is the diagonal sum of the
squared first derivatives divided by the eigenvalues of the varying metric. -/
theorem normalFrame_gradNormSq_eq_firstDerivative_sum
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x) (f : M → ℝ)
    (hf : ContDiffAt ℝ 1
      (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
      (F.map F.center)) :
    ω₁.gradNormSq f x = ∑ p,
      ‖chartPartialZ
        ((f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) ∘ F.map)
        F.center p‖ ^ 2 / F.eigenvalue p := by
  obtain ⟨A, hA, hdiag⟩ := normalFrame_varying_metric_coeffMatrix ω₀ ω₁ x F
  have hα : (mdWedgeDBar n f x).IsOneOne :=
    (isNonneg_dWedgeDBar _).1
  have htrace := ContinuousAlternatingMap.relTrace_compContinuousLinearMap
    (ω₁.isOneOne x) hα A
  let q : EuclideanSpace ℂ (Fin n) → ℝ :=
    fun z ↦ f ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm (F.map z))
  calc
    ω₁.gradNormSq f x = relTrace (ω₁ x) (mdWedgeDBar n f x) := rfl
    _ = relTrace
        ((ω₁ x).compContinuousLinearMap
          ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ))
        ((mdWedgeDBar n f x).compContinuousLinearMap
          ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)) :=
      htrace.symm
    _ = relTrace
        ((ω₁ x).compContinuousLinearMap
          ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ))
        (dWedgeDBar (fderiv ℝ q F.center)) := by
      rw [normalFrame_mdWedgeDBar_pullback ω₀ ω₁ x F f hf A hA]
    _ = ∑ p, RCLike.re ((dWedgeDBar (fderiv ℝ q F.center)).coeffMatrix p p) /
          F.eigenvalue p :=
      relTrace_eq_sum_of_diagonal_coeffMatrix _ _ F.eigenvalue F.eigenvalue_pos hdiag
    _ = ∑ p,
        ‖chartPartialZ
          ((f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) ∘ F.map)
          F.center p‖ ^ 2 / F.eigenvalue p := by
      apply Finset.sum_congr rfl
      intro p hp
      have hbar : chartPartialBar q F.center p = star (chartPartialZ q F.center p) := by
        simp [chartPartialBar, chartPartialZ, div_eq_mul_inv]
      have hreal : RCLike.re (chartPartialZ q F.center p *
          star (chartPartialZ q F.center p)) = Complex.normSq (chartPartialZ q F.center p) := by
        have hc := congrArg Complex.re
          (Complex.normSq_eq_conj_mul_self (z := chartPartialZ q F.center p))
        simpa [Complex.ofReal_re, mul_comm] using hc.symm
      have hcoeff : (dWedgeDBar (fderiv ℝ q F.center)).coeffMatrix p p =
          chartPartialZ q F.center p * chartPartialBar q F.center p := by
        rw [coeffMatrix_dWedgeDBar]
        simp [Matrix.vecMulVec, chartPartialZ, chartPartialBar]
      calc
        RCLike.re ((dWedgeDBar (fderiv ℝ q F.center)).coeffMatrix p p) /
            F.eigenvalue p =
          Complex.normSq (chartPartialZ q F.center p) / F.eigenvalue p := by
            rw [hcoeff, hbar, hreal]
        _ = ‖chartPartialZ q F.center p‖ ^ 2 / F.eigenvalue p := by
          rw [Complex.normSq_eq_norm_sq]
        _ = ‖chartPartialZ
              ((f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) ∘ F.map)
              F.center p‖ ^ 2 / F.eigenvalue p := by
          rfl

end KahlerForm
