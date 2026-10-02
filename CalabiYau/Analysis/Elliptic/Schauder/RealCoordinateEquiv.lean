module

public import CalabiYau.Analysis.Elliptic.Schauder.Realification
public import CalabiYau.Analysis.Elliptic.Schauder.VariableCoefficient.Basic

/-!
# Real coordinates for the complex elliptic operator

The realification of `EuclideanSpace ℂ (Fin n)` uses the order `(j,0) = Re zⱼ`,
`(j,1) = Im zⱼ`. The coefficient matrix from `Realification` is therefore read against the
standard real basis indexed by `Fin n × Fin 2`. Its factor `1/4` is the one in
`complexHessian_apply`.

The extracted `variableMatrixLap` requires its coordinate index type to be nonempty. Thus its
variable-operator specialization is stated for `0 < n`; the pointwise `matrixLap` comparison has no
such restriction and includes `n = 0`.
-/

@[expose] public section

open scoped NNReal RealInnerProductSpace
open CalabiYau.Schauder

/-- The real coordinate isometry for `ℂⁿ`, ordered by complex coordinate and then real/imaginary
part. -/
noncomputable def complexToRealCoordinateEquiv {n : ℕ} :
    EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n × Fin 2) := by
  exact ((Pi.orthonormalBasis (fun _ : Fin n => Complex.orthonormalBasisOneI)).reindex
    (Equiv.sigmaEquivProd (Fin n) (Fin 2))).repr

/-- In the coordinate isometry, index `(j,0)` is the real part and `(j,1)` is the imaginary part. -/
theorem complexToRealCoordinateEquiv_apply {n : ℕ}
    (z : EuclideanSpace ℂ (Fin n)) (p : Fin n × Fin 2) :
    complexToRealCoordinateEquiv z p = Complex.basisOneI.repr (z p.1) p.2 := by
  simp [complexToRealCoordinateEquiv, Equiv.sigmaEquivProd, Pi.orthonormalBasis,
    Sigma.uncurry]

/-- The second derivative of a function pulled back by the real coordinate isometry is the
original real Hessian evaluated on the inverse images of the real directions. -/
theorem complexToRealCoordinateEquiv_hessian_apply {n : ℕ}
    (u : EuclideanSpace ℂ (Fin n) → ℝ) (z : EuclideanSpace ℂ (Fin n))
    (hu : ContDiffAt ℝ 2 u z) (v w : EuclideanSpace ℝ (Fin n × Fin 2)) :
    fderiv ℝ
        (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n × Fin 2) =>
          u ((complexToRealCoordinateEquiv).symm y)))
        (complexToRealCoordinateEquiv z) v w =
      fderiv ℝ (fderiv ℝ u) z
        ((complexToRealCoordinateEquiv).symm v) ((complexToRealCoordinateEquiv).symm w) := by
  let e := complexToRealCoordinateEquiv (n := n)
  let eL : EuclideanSpace ℝ (Fin n × Fin 2) ≃L[ℝ] EuclideanSpace ℂ (Fin n) :=
    e.symm.toContinuousLinearEquiv
  let f : EuclideanSpace ℝ (Fin n × Fin 2) → ℝ := fun y => u (eL y)
  have heL : ContDiffAt ℝ 2 (eL : EuclideanSpace ℝ (Fin n × Fin 2) →
      EuclideanSpace ℂ (Fin n)) (e z) := by
    fun_prop
  have heL1 : ContDiffAt ℝ 1 (eL : EuclideanSpace ℝ (Fin n × Fin 2) →
      EuclideanSpace ℂ (Fin n)) (e z) := heL.of_le (by norm_num)
  have hu' : ContDiffAt ℝ 2 u (eL (e z)) := by
    simpa [eL] using hu
  have hf : ContDiffAt ℝ 2 f (e z) := by
    exact ContDiffAt.comp (x := e z) hu' heL
  have hfu : ContDiffAt ℝ 1 (fderiv ℝ u) z :=
    hu.fderiv_right (by norm_num)
  have hfu' : ContDiffAt ℝ 1 (fderiv ℝ u) (eL (e z)) := by
    simpa [eL] using hfu
  have hfc : ContDiffAt ℝ 1 (fderiv ℝ f) (e z) :=
    hf.fderiv_right (by norm_num)
  have hc : DifferentiableAt ℝ (fun y => fderiv ℝ f y) (e z) :=
    hfc.differentiableAt (by norm_num [minSmoothness])
  have hc' : DifferentiableAt ℝ (fun y => fderiv ℝ u (eL y)) (e z) := by
    exact (ContDiffAt.comp (x := e z) hfu' heL1).differentiableAt
      (by norm_num [minSmoothness])
  have hpull (y : EuclideanSpace ℝ (Fin n × Fin 2)) :
      fderiv ℝ f y = (fderiv ℝ u (eL y)).comp (eL :
        EuclideanSpace ℝ (Fin n × Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin n)) := by
    dsimp [f]
    exact eL.comp_right_fderiv
  have heval :
      (fun y => fderiv ℝ f y w) = (fun y => fderiv ℝ u (eL y) (eL w)) := by
    funext y
    rw [hpull]
    rfl
  calc
    fderiv ℝ (fderiv ℝ f) (e z) v w =
        fderiv ℝ (fun y => fderiv ℝ f y w) (e z) v := by
          symm
          rw [fderiv_clm_apply hc (differentiableAt_const _)]
          simp
    _ = fderiv ℝ (fun y => fderiv ℝ u (eL y) (eL w)) (e z) v := by
          rw [heval]
    _ = fderiv ℝ (fun y => fderiv ℝ u (eL y)) (e z) v (eL w) := by
          rw [fderiv_clm_apply hc' (differentiableAt_const _)]
          simp
    _ = fderiv ℝ (fderiv ℝ u) z (eL v) (eL w) := by
          change fderiv ℝ ((fun y => fderiv ℝ u y) ∘ eL) (e z) v (eL w) = _
          rw [eL.comp_right_fderiv]
          simp [eL]

private theorem complexToRealCoordinateEquiv_symm_basis {n : ℕ}
    (p : Fin n × Fin 2) :
    (complexToRealCoordinateEquiv).symm (EuclideanSpace.basisFun (Fin n × Fin 2) ℝ p) =
      complexRealCoordinateBasis p := by
  classical
  apply complexToRealCoordinateEquiv.injective
  rw [complexToRealCoordinateEquiv.apply_symm_apply]
  ext q
  rcases p with ⟨i, a⟩
  rcases q with ⟨j, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [complexToRealCoordinateEquiv_apply, complexRealCoordinateBasis,
      Complex.coe_basisOneI_repr, EuclideanSpace.basisFun_apply] <;>
    split_ifs <;> simp

/-- In real coordinates the complex principal operator is the extracted constant-matrix Laplacian
with coefficient `(1/4) • realify Aᵀ`. This formula also holds in dimension zero. -/
theorem complexPrincipalOperator_eq_matrixLap {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (u : EuclideanSpace ℂ (Fin n) → ℝ)
    (z : EuclideanSpace ℂ (Fin n)) (hu : ContDiffAt ℝ 2 u z) :
    complexPrincipalOperator A u z =
      HeatEquation.matrixLap (realPrincipalCoefficient A)
        (fderiv ℝ
          (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n × Fin 2) =>
            u ((complexToRealCoordinateEquiv).symm y)))
          (complexToRealCoordinateEquiv z)) := by
  rw [complexPrincipalOperator_eq_realHessianContraction A u z hu]
  simp only [realHessianContraction, HeatEquation.matrixLap]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  rw [complexToRealCoordinateEquiv_hessian_apply u z hu
    (EuclideanSpace.basisFun (Fin n × Fin 2) ℝ p)
    (EuclideanSpace.basisFun (Fin n × Fin 2) ℝ q)]
  rw [complexToRealCoordinateEquiv_symm_basis p,
    complexToRealCoordinateEquiv_symm_basis q]
  simp [smul_eq_mul]

/-- For `A = 1` and `u(z) = ‖z‖²`, the realified matrix Laplacian has value `n`, fixing the
normalization in every dimension, including `n = 0`. -/
theorem matrixLap_one_normSq {n : ℕ} (z : EuclideanSpace ℂ (Fin n)) :
    HeatEquation.matrixLap (realPrincipalCoefficient (1 : Matrix (Fin n) (Fin n) ℂ))
      (fderiv ℝ
        (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n × Fin 2) =>
          ‖(complexToRealCoordinateEquiv).symm y‖ ^ 2))
        (complexToRealCoordinateEquiv z)) = n := by
  have hu : ContDiffAt ℝ 2 (fun w : EuclideanSpace ℂ (Fin n) => ‖w‖ ^ 2) z := by
    exact contDiffAt_id.norm_sq ℝ
  calc
    _ = complexPrincipalOperator (1 : Matrix (Fin n) (Fin n) ℂ)
          (fun w => ‖w‖ ^ 2) z :=
      (complexPrincipalOperator_eq_matrixLap (1 : Matrix (Fin n) (Fin n) ℂ)
        (fun w => ‖w‖ ^ 2) z hu).symm
    _ = n := complexPrincipalOperator_one_normSq z

/-- Evaluation of the extracted variable-matrix Laplacian agrees with the complex operator when
its real coefficients are the pulled-back real principal matrix and its jet is the pulled-back
complex Hessian. The nonempty coordinate index requires `0 < n`; the matrix-Laplacian identity
above remains valid for `n = 0`. -/
theorem variableMatrixLap_eq_complexPrincipalOperator {n : ℕ} (hn : 0 < n)
    (a : (Fin n × Fin 2) → (Fin n × Fin 2) →
      BoundedContinuousFunction (EuclideanSpace ℝ (Fin n × Fin 2)) ℝ)
    (d2u : BoundedContinuousFunction (EuclideanSpace ℝ (Fin n × Fin 2))
      (EuclideanSpace ℝ (Fin n × Fin 2) →L[ℝ]
        EuclideanSpace ℝ (Fin n × Fin 2) →L[ℝ] ℝ))
    (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (u : EuclideanSpace ℂ (Fin n) → ℝ) (z : EuclideanSpace ℂ (Fin n))
    (hu : ContDiffAt ℝ 2 u z)
    (hA : ∀ p q, a p q (complexToRealCoordinateEquiv z) =
      realPrincipalCoefficient (A z) p q)
    (h₂ : d2u (complexToRealCoordinateEquiv z) =
      fderiv ℝ
        (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n × Fin 2) =>
          u ((complexToRealCoordinateEquiv).symm y)))
        (complexToRealCoordinateEquiv z)) :
    CalabiYau.Schauder.variableMatrixLap a d2u (complexToRealCoordinateEquiv z) =
      complexPrincipalOperator (A z) u z := by
  let : Nonempty (Fin n × Fin 2) := ⟨(⟨0, hn⟩, 0)⟩
  rw [variableMatrixLap_apply, h₂]
  have hcoeff : (fun p q => a p q (complexToRealCoordinateEquiv z)) =
      realPrincipalCoefficient (A z) := by
    ext p q
    exact hA p q
  rw [hcoeff]
  exact (complexPrincipalOperator_eq_matrixLap (A z) u z hu).symm
