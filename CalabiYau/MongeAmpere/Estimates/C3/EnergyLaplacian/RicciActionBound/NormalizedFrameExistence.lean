module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.Matrix.Order

/-!
# Existence of a normalized complex frame

Finite-dimensional Hermitian normalization, with the bilinear matrix convention
used by the Kähler coefficients: `P.transpose * g * P.map star = 1`.
No positive dimension assumption is needed: the empty matrix is allowed.
This is an algebraic prerequisite of the unitary-frame calculation in
Székelyhidi §3.3, following (3.14), printed p. 45.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace KahlerForm

/-- One generic frame-existence statement, used both for the reference and
for the perturbed metric. Positive definiteness is the standing hypothesis. -/
theorem exists_c3NormalizedFrameMatrix {n : ℕ}
    (g : Matrix (Fin n) (Fin n) ℂ) (hg : g.PosDef) :
    ∃ P : Matrix (Fin n) (Fin n) ℂ,
      P.transpose * g * P.map star = 1 := by
  classical
  let s : Matrix (Fin n) (Fin n) ℂ := CFC.sqrt g
  have hg0 : 0 ≤ g := hg.posSemidef.nonneg
  have hs0 : 0 ≤ s := by
    dsimp [s]
    exact CFC.sqrt_nonneg g
  have hss : s * s = g := by
    simpa [s, pow_two] using CFC.sq_sqrt g hg0
  have hspsd : s.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hs0
  have hsinvHerm : s⁻¹.IsHermitian := hspsd.isHermitian.inv
  have hgdet : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).mp hg.isUnit
  have hsdet : s.det ≠ 0 := by
    intro hzero
    apply hgdet.ne_zero
    rw [← hss, Matrix.det_mul, hzero, zero_mul]
  have hsunit : IsUnit s :=
    (Matrix.isUnit_iff_isUnit_det s).mpr (isUnit_iff_ne_zero.mpr hsdet)
  let : Invertible s := hsunit.invertible
  refine ⟨(s⁻¹).map star, ?_⟩
  have htranspose : ((s⁻¹).map star).transpose = s⁻¹ := by
    have h := hsinvHerm.eq
    ext i j
    have hij := congrFun (congrFun h j) i
    simpa [Matrix.conjTranspose, Matrix.transpose_apply] using
      (congrArg star hij).symm
  have hmap : ((s⁻¹).map star).map star = s⁻¹ := by
    ext i j
    simp
  calc
    ((s⁻¹).map star).transpose * g * ((s⁻¹).map star).map star = s⁻¹ * g * s⁻¹ := by
      rw [htranspose, hmap]
    _ = 1 := by
      rw [← hss]
      simp

end KahlerForm
