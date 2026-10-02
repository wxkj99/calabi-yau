module

public import Mathlib.Data.Matrix.Basic

/-!
# A finite-matrix normal-jet equation

If a matrix `g` has a left inverse after transposition, one can solve for a symmetric
two-index coefficient `C` which cancels a symmetric data tensor `D` under contraction
with `g`. This is the algebraic step used to choose the second jet in normal coordinates.

The proof uses only the explicit left-inverse identity. In particular, it does not require
the coefficient ring to be a field or the inverse matrix to be uniquely determined.
-/

@[expose] public section

open scoped BigOperators

namespace Matrix

/-- Solve the finite normal-jet equation using the supplied left inverse. -/
theorem exists_symmetric_normal_jet {n : ℕ} {R : Type*} [Ring R]
    (g gInv : Matrix (Fin n) (Fin n) R) (hInv : g.transpose * gInv = 1)
    (D : Fin n → Fin n → Fin n → R)
    (hD : ∀ i k j, D i k j = D k i j) :
    ∃ C : Fin n → Fin n → Fin n → R,
      (∀ a i k, C a i k = C a k i) ∧
      (∀ i k j, D i k j + ∑ a, g a j * C a i k = 0) := by
  classical
  let C : Fin n → Fin n → Fin n → R := fun a i k ↦
    -∑ l, gInv a l * D i k l
  refine ⟨C, ?_, ?_⟩
  · intro a i k
    simp [C, hD i k]
  · intro i k j
    let d : Fin n → R := fun l ↦ D i k l
    have hC : (fun a ↦ C a i k) = -(gInv.mulVec d) := by
      funext a
      simp [C, d, Matrix.mulVec, dotProduct]
    have hInvD : g.transpose.mulVec (gInv.mulVec d) = d := by
      calc
        g.transpose.mulVec (gInv.mulVec d) = (g.transpose * gInv).mulVec d := by
          rw [← Matrix.mulVec_mulVec]
        _ = (1 : Matrix (Fin n) (Fin n) R).mulVec d := by rw [hInv]
        _ = d := Matrix.one_mulVec d
    have hvec : g.transpose.mulVec (fun a ↦ C a i k) = -d := by
      rw [hC, Matrix.mulVec_neg, hInvD]
    have hcoord := congrFun hvec j
    have hsum : (∑ a, g a j * C a i k) = -D i k j := by
      simpa [Matrix.mulVec, Matrix.transpose_apply, dotProduct, d] using hcoord
    rw [hsum]
    exact add_neg_cancel _

end Matrix
