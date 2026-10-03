module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Basic.Complex.Basic

/-!
# Inverse of a pulled-back Hermitian form

If `B * A = 1`, the inverse of the matrix `Aᵀ G Ā` of the form `G` pulled back along `A` is
`B̄ G⁻¹ Bᵀ`. This is the change-of-coordinates rule for the inverse of a Hermitian metric under a
holomorphic change of frame.
-/

@[expose] public section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem inv_transpose_mul_mul_map_star (A B G : Matrix n n ℂ) (hBA : B * A = 1) :
    (A.transpose * G * A.map star)⁻¹ = B.map star * G⁻¹ * B.transpose := by
  have hInv : A⁻¹ = B := Matrix.inv_eq_left_inv hBA
  have hInvStar : (A.map star)⁻¹ = B.map star := by
    rw [← Matrix.transpose_conjTranspose, ← Matrix.conjTranspose_nonsing_inv,
      ← Matrix.transpose_nonsing_inv, hInv]
    rfl
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hInvStar,
    ← Matrix.transpose_nonsing_inv, hInv, Matrix.mul_assoc]

end Matrix
