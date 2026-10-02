module

public import CalabiYau.Geometry.Complex.Forms.ComplexHessian
public import CalabiYau.LinearAlgebra.Matrix.Realification

/-!
# Realification of the complex elliptic principal symbol

For the convention `complexHessian_apply`, the real principal coefficient matrix is one quarter of
`realify Aᵀ`. Its rows and columns are indexed in the order `(j, 0) = Re zⱼ`,
`(j, 1) = Im zⱼ`. The transpose is essential: `complexEllipticOp` contracts `Aᵢⱼ` with
`(complexHessian u)ⱼᵢ`.

This file states the exact real-Hessian contraction and the transfer of a complex lower ellipticity
bound to the real coefficient matrix. For `A = 1`, the real principal coefficient is `1/4` times
the identity; for `u(z) = ‖z‖²`, the complex Hessian is the identity, fixing the normalization.
-/

@[expose] public section

open scoped ComplexOrder

/-- The real coordinate vector corresponding to the complex coordinate `zⱼ`, ordered as real then
imaginary part. -/
noncomputable def complexRealCoordinateBasis {n : ℕ} (p : Fin n × Fin 2) :
    EuclideanSpace ℂ (Fin n) :=
  if p.2 = 0 then EuclideanSpace.single p.1 1
  else Complex.I • EuclideanSpace.single p.1 1

/-- The real coefficient matrix for `re tr (A * complexHessian u)`. Its coordinate order is
`(j, 0) = Re zⱼ`, `(j, 1) = Im zⱼ`; the transpose records the reversed Hessian indices in the
matrix trace. -/
noncomputable def realPrincipalCoefficient {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ :=
  (1 / 4 : ℝ) • Matrix.realify A.transpose

/-- The real-coordinate Hessian contraction associated to a real coefficient matrix. -/
noncomputable def realHessianContraction {n : ℕ}
    (B : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)
    (u : EuclideanSpace ℂ (Fin n) → ℝ) (z : EuclideanSpace ℂ (Fin n)) : ℝ :=
  ∑ p, ∑ q, B p q *
    fderiv ℝ (fderiv ℝ u) z (complexRealCoordinateBasis p) (complexRealCoordinateBasis q)

/-- The complex second-order operator with the trace/index convention of the Schauder provider. -/
noncomputable def complexPrincipalOperator {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (u : EuclideanSpace ℂ (Fin n) → ℝ) (z : EuclideanSpace ℂ (Fin n)) : ℝ :=
  (A * complexHessian u z).trace.re

private theorem realQuadratic_transpose {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (v : Fin n → ℂ) :
    RCLike.re (dotProduct (star v) (Matrix.mulVec A.transpose v)) =
      RCLike.re (dotProduct (star (star v)) (Matrix.mulVec A (star v))) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, star_star]
  simp_rw [Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Exact conversion of the complex trace contraction to the real Hessian contraction. The factor
`1/4` and transpose are fixed by `complexHessian_apply`. -/
theorem complexPrincipalOperator_eq_realHessianContraction {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (u : EuclideanSpace ℂ (Fin n) → ℝ)
    (z : EuclideanSpace ℂ (Fin n)) (hu : ContDiffAt ℝ 2 u z) :
    complexPrincipalOperator A u z =
      realHessianContraction (realPrincipalCoefficient A) u z := by
  classical
  simp [complexPrincipalOperator, realHessianContraction, realPrincipalCoefficient,
    Matrix.trace, Matrix.mul_apply, complexHessian_apply hu, Matrix.realify_apply,
    complexRealCoordinateBasis, Fintype.sum_prod_type, Fin.sum_univ_two,
    Complex.mul_re, Complex.mul_im, Complex.re_sum]
  ring_nf
  simp_rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  conv_rhs => rw [Finset.sum_comm]
  ring_nf

/-- A Hermitian complex coefficient matrix bounded below by `λ` gives a real coefficient matrix
bounded below by `λ / 4`. The real quadratic form uses coordinates `(j,0) = Re vⱼ` and
`(j,1) = Im vⱼ`. -/
theorem realPrincipalCoefficient_lower_bound {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (lam : ℝ) (hA : A.IsHermitian)
    (h_lam : ∀ v : Fin n → ℂ,
      lam * ∑ i, ‖v i‖ ^ 2 ≤ RCLike.re (dotProduct (star v) (Matrix.mulVec A v)))
    (x : Fin n × Fin 2 → ℝ) :
    (lam / 4) * ∑ p, x p ^ 2 ≤
      dotProduct x (Matrix.mulVec (realPrincipalCoefficient A) x) := by
  have _hA := hA
  let v : Fin n → ℂ := fun i => (x (i, 0) : ℂ) + x (i, 1) * Complex.I
  have hcoords : (fun p : Fin n × Fin 2 => Complex.basisOneI.repr (v p.1) p.2) = x := by
    funext p
    rcases p with ⟨i, a⟩
    fin_cases a <;> simp [v, Complex.coe_basisOneI_repr]
  have hnorm : ∑ i, ‖star v i‖ ^ 2 = ∑ p, x p ^ 2 := by
    simp [v, Complex.sq_norm, Complex.normSq_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hrealify :
      dotProduct x (Matrix.mulVec (Matrix.realify A.transpose) x) =
        RCLike.re (dotProduct (star v) (Matrix.mulVec A.transpose v)) := by
    rw [← hcoords]
    exact Matrix.dotProduct_realify_mulVec A.transpose v
  have hscale :
      dotProduct x (Matrix.mulVec (realPrincipalCoefficient A) x) =
        (1 / 4 : ℝ) *
          dotProduct x (Matrix.mulVec (Matrix.realify A.transpose) x) := by
    simp only [realPrincipalCoefficient, Matrix.mulVec, dotProduct, Finset.mul_sum,
      Matrix.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring_nf
  have hbound := h_lam (star v)
  rw [hnorm] at hbound
  rw [← realQuadratic_transpose A v] at hbound
  rw [hscale, hrealify]
  nlinarith [hbound]

@[simp]
theorem realPrincipalCoefficient_one {n : ℕ} [DecidableEq (Fin n)] :
    realPrincipalCoefficient (1 : Matrix (Fin n) (Fin n) ℂ) =
      (1 / 4 : ℝ) • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) := by
  simp [realPrincipalCoefficient]

/-- The quadratic potential `‖z‖²` has complex Hessian equal to the identity, so the normalization
of the complex principal operator is exactly `n`. -/
theorem complexPrincipalOperator_one_normSq {n : ℕ}
    (z : EuclideanSpace ℂ (Fin n)) :
    complexPrincipalOperator (1 : Matrix (Fin n) (Fin n) ℂ)
      (fun w ↦ ‖w‖ ^ 2) z = n := by
  simp [complexPrincipalOperator, complexHessian_normSq]
