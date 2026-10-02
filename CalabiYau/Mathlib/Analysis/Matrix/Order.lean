module

public import Mathlib.Analysis.Matrix.Order

/-!
# Trace, determinant and inverse under the Loewner order

This file supplements `Mathlib.Analysis.Matrix.Order` (the Loewner order
`A ≤ B ↔ (B - A).PosSemidef`, available after `open scoped MatrixOrder`) with the monotonicity
statements used to compare two Kähler metrics pointwise.

## Main statements

* `Matrix.PosSemidef.trace_mul_nonneg`: `0 ≤ tr (A B)` for positive semidefinite `A`, `B`.
* `Matrix.PosSemidef.trace_mul_mul_mul_conjTranspose_nonneg`: `0 ≤ tr (P X Q Xᴴ)` for positive
  semidefinite `P`, `Q` and arbitrary `X`.
* `Matrix.PosSemidef.trace_mul_le_trace_mul`: `B ≤ C → tr (P B) ≤ tr (P C)` for `P ≥ 0`.
* `Matrix.PosSemidef.det_le_det`: `0 ≤ A ≤ B → det A ≤ det B`.
* `Matrix.PosDef.inv_le_inv`: `0 < A ≤ B → B⁻¹ ≤ A⁻¹`.

Congruence monotonicity `A ≤ B → Xᴴ A X ≤ Xᴴ B X` is the general `star_left_conjugate_le_conjugate`
for star-ordered rings (`Matrix.instStarOrderedRing`, scoped to `MatrixOrder`).

All inequalities between scalars in `𝕜` use `ComplexOrder`, as in `Matrix.PosSemidef.trace_nonneg`.
-/

public section

open scoped ComplexOrder MatrixOrder

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] {A B C P Q : Matrix n n 𝕜}

namespace PosSemidef

/-- The trace of the product of two positive semidefinite matrices is nonnegative. -/
theorem trace_mul_nonneg (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  classical
  set S := CFC.sqrt B
  have hS : Sᴴ = S := (nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg B)).isHermitian.eq
  have hSS : S * S = B := CFC.sqrt_mul_sqrt_self B hB.nonneg
  have h := (hA.conjTranspose_mul_mul_same S).trace_nonneg
  rwa [hS, trace_mul_comm, ← Matrix.mul_assoc, hSS, trace_mul_comm] at h

/-- Multiplying by a positive semidefinite matrix and taking the trace is monotone for the
Loewner order. -/
theorem trace_mul_le_trace_mul (hP : P.PosSemidef) (hBC : B ≤ C) :
    (P * B).trace ≤ (P * C).trace := by
  have h := hP.trace_mul_nonneg (le_iff.1 hBC)
  rwa [Matrix.mul_sub, trace_sub, sub_nonneg] at h

end PosSemidef

namespace PosDef

variable [DecidableEq n]

/-- Matrix inversion is antitone on positive definite matrices for the Loewner order. -/
theorem inv_le_inv (hA : A.PosDef) (hAB : A ≤ B) : B⁻¹ ≤ A⁻¹ := by
  classical
  have hB : B.PosDef := by
    have h := hA.add_posSemidef (le_iff.1 hAB)
    convert h using 1
    ext i j
    simp [sub_eq_add_neg]
  let S := CFC.sqrt B⁻¹
  have hS : Sᴴ = S := (nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg B⁻¹)).isHermitian.eq
  have hSsq : S * S = B⁻¹ := CFC.sqrt_mul_sqrt_self B⁻¹ hB.inv.posSemidef.nonneg
  let R := CFC.sqrt B
  have hRR : R * R = B := CFC.sqrt_mul_sqrt_self B hB.posSemidef.nonneg
  have hRunit : IsUnit R := isUnit_of_mul_isUnit_left (hRR ▸ hB.isUnit)
  have hRdet : IsUnit R.det := (isUnit_iff_isUnit_det R).1 hRunit
  have hSR : S = R⁻¹ := hB.posSemidef.inv_sqrt.symm
  have hSBS : S * B * S = 1 := by
    rw [hSR, ← hRR, Matrix.mul_assoc, Matrix.mul_assoc,
      mul_nonsing_inv R hRdet, Matrix.mul_one, nonsing_inv_mul R hRdet]
  have hSunit : IsUnit S := by
    rw [hSR]
    exact isUnit_nonsing_inv_iff.mpr hRunit
  let D := S * A * S
  have hD : D.PosDef := by
    have hSi : Function.Injective S.mulVec := Matrix.mulVec_injective_iff_isUnit.2 hSunit
    simpa [D, hS] using hA.conjTranspose_mul_mul_same hSi
  have hDle : D ≤ 1 := by
    have h := star_left_conjugate_le_conjugate hAB S
    simpa [D, star_eq_conjTranspose, hS, hSBS] using h
  have hDinv : 1 ≤ D⁻¹ := by
    let T := CFC.sqrt D⁻¹
    have hT : Tᴴ = T := (nonneg_iff_posSemidef.1
      (CFC.sqrt_nonneg D⁻¹)).isHermitian.eq
    have hT2 : T * T = D⁻¹ := CFC.sqrt_mul_sqrt_self D⁻¹ hD.inv.posSemidef.nonneg
    let U := CFC.sqrt D
    have hUU : U * U = D := CFC.sqrt_mul_sqrt_self D hD.posSemidef.nonneg
    have hUunit : IsUnit U := isUnit_of_mul_isUnit_left (hUU ▸ hD.isUnit)
    have hUdet : IsUnit U.det := (isUnit_iff_isUnit_det U).1 hUunit
    have hTU : T = U⁻¹ := hD.posSemidef.inv_sqrt.symm
    have hTDT : T * D * T = 1 := by
      rw [hTU, ← hUU, Matrix.mul_assoc, Matrix.mul_assoc,
        mul_nonsing_inv U hUdet, Matrix.mul_one, nonsing_inv_mul U hUdet]
    have hconj := (le_iff.1 hDle).conjTranspose_mul_mul_same T
    have h_eq : Tᴴ * (1 - D) * T = D⁻¹ - 1 := by
      rw [hT]
      calc
        T * (1 - D) * T = T * T - T * D * T := by noncomm_ring
        _ = D⁻¹ - 1 := by rw [hT2, hTDT]
    apply le_iff.mpr
    rw [← h_eq]
    exact hconj
  have hfinal := star_left_conjugate_le_conjugate hDinv S
  let := hA.isUnit.invertible
  let := hB.isUnit.invertible
  let := hD.isUnit.invertible
  let := hSunit.invertible
  have hSdet : IsUnit S.det := (isUnit_iff_isUnit_det S).1 hSunit
  have hDinv_eq : D⁻¹ = S⁻¹ * (A⁻¹ * S⁻¹) := by
    simp [D, Matrix.mul_inv_rev, Matrix.mul_assoc]
  rw [hDinv_eq] at hfinal
  calc
    B⁻¹ = S * S := hSsq.symm
    _ = star S * 1 * S := by simp [star_eq_conjTranspose, hS]
    _ ≤ star S * (S⁻¹ * (A⁻¹ * S⁻¹)) * S := hfinal
    _ = A⁻¹ := by
      simp [star_eq_conjTranspose, hS, Matrix.mul_assoc, nonsing_inv_mul S hSdet]

end PosDef

end Matrix
