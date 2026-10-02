module

public import CalabiYau.Mathlib.Analysis.Matrix.Hermitian.SimultaneousDiagonalization
import CalabiYau.Mathlib.Analysis.Matrix.Order
import CalabiYau.Mathlib.Analysis.MeanInequalities

/-!
# Trace and determinant inequalities for a pair of positive definite matrices

For positive definite Hermitian matrices `A` and `B` of size `n`, write `λ₁, …, λₙ > 0` for the
eigenvalues of `A⁻¹ B`, so that `tr (A⁻¹ B) = ∑ λᵢ`, `tr (B⁻¹ A) = ∑ λᵢ⁻¹` and
`det B / det A = ∏ λᵢ`. In Kähler geometry, with `A = g` and `B = g'` two metrics at a point,
`tr (A⁻¹ B) = tr_g g'` and `det B / det A = ω'ⁿ / ωⁿ`. This file records the inequalities between
these quantities used in the a priori estimates for the complex Monge–Ampère equation.

Scalars are compared in `ℝ` through `RCLike.re`, since that is how they enter the estimates.

## Main statements

* `Matrix.PosDef.geom_mean_le_arith_mean_inv_mul`: `(det B / det A)^{1/n} ≤ tr (A⁻¹ B) / n`.
* `Matrix.PosDef.card_sq_le_trace_inv_mul_mul_trace_inv_mul`: `n² ≤ tr (A⁻¹ B) · tr (B⁻¹ A)`.
* `Matrix.PosDef.trace_inv_mul_le_trace_inv_mul_pow_mul_det_div_det`:
  `tr (B⁻¹ A) ≤ tr (A⁻¹ B)^{n-1} · det A / det B`, the inequality
  `tr_{g'} g ≤ (tr_g g')^{n-1} e^{-F}` of the C² estimate.
* `Matrix.PosDef.trace_inv_mul_le_trace_inv_mul`: `B ≤ C → tr (A⁻¹ B) ≤ tr (A⁻¹ C)`.

## References

* S.-T. Yau, *On the Ricci curvature of a compact Kähler manifold and the complex Monge–Ampère
  equation I*, Comm. Pure Appl. Math. 31 (1978), §2.
* G. Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §3.3, proof of Proposition 3.8 and
  Lemma 3.7.
* T. Aubin, *Some Nonlinear Problems in Riemannian Geometry*, §7.2.
-/

public section

open scoped ComplexOrder MatrixOrder

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] {A B C : Matrix n n 𝕜}

namespace PosDef

/-- `tr (A⁻¹ B)` is positive for positive definite `A`, `B` of positive size. -/
theorem trace_inv_mul_pos [Nonempty n] (hA : A.PosDef) (hB : B.PosDef) :
    0 < RCLike.re (A⁻¹ * B).trace := by
  obtain ⟨P, d, hPA, hPB⟩ := hA.exists_simultaneous_diagonalization hB.isHermitian
  have hd := (posDef_iff_forall_pos_of_conjTranspose_mul_mul_eq hPA hPB).1 hB
  rw [re_trace_inv_mul_eq_sum_of_conjTranspose_mul_mul_eq hPA hPB]
  exact Finset.sum_pos (fun i _ ↦ hd i) Finset.univ_nonempty

/-- `tr (A⁻¹ B)` is nonnegative for positive definite `A` and positive semidefinite `B`. -/
theorem trace_inv_mul_nonneg (hA : A.PosDef) (hB : B.PosSemidef) :
    0 ≤ RCLike.re (A⁻¹ * B).trace := by
  simpa using (RCLike.le_iff_re_im.1 (hA.inv.posSemidef.trace_mul_nonneg hB)).1

/-- **AM–GM for relative eigenvalues**: `(det B / det A)^{1/n} ≤ tr (A⁻¹ B) / n`. -/
theorem geom_mean_le_arith_mean_inv_mul [Nonempty n] (hA : A.PosDef) (hB : B.PosSemidef) :
    (RCLike.re B.det / RCLike.re A.det) ^ ((Fintype.card n : ℝ)⁻¹) ≤
      RCLike.re (A⁻¹ * B).trace / Fintype.card n := by
  obtain ⟨P, d, hPA, hPB⟩ := hA.exists_simultaneous_diagonalization hB.isHermitian
  have hd := (posSemidef_iff_forall_nonneg_of_conjTranspose_mul_mul_eq hPA hPB).1 hB
  have hApos : 0 < RCLike.re A.det := (RCLike.pos_iff.1 hA.det_pos).1
  rw [re_det_eq_re_det_mul_prod_of_conjTranspose_mul_mul_eq hPA hPB,
    mul_div_cancel_left₀ _ hApos.ne', re_trace_inv_mul_eq_sum_of_conjTranspose_mul_mul_eq hPA hPB]
  simpa using Real.prod_rpow_inv_card_le_sum_div_card Finset.univ Finset.univ_nonempty
    (fun i _ ↦ hd i)

/-- `n² ≤ tr (A⁻¹ B) · tr (B⁻¹ A)` for positive definite `A`, `B`. -/
theorem card_sq_le_trace_inv_mul_mul_trace_inv_mul (hA : A.PosDef) (hB : B.PosDef) :
    (Fintype.card n : ℝ) ^ 2 ≤ RCLike.re (A⁻¹ * B).trace * RCLike.re (B⁻¹ * A).trace := by
  obtain ⟨P, d, hPA, hPB⟩ := hA.exists_simultaneous_diagonalization hB.isHermitian
  have hd := (posDef_iff_forall_pos_of_conjTranspose_mul_mul_eq hPA hPB).1 hB
  rw [re_trace_inv_mul_eq_sum_of_conjTranspose_mul_mul_eq hPA hPB,
    re_trace_inv_mul_eq_sum_inv_of_conjTranspose_mul_mul_eq hPA hPB fun i ↦ (hd i).ne']
  simpa using Real.card_sq_le_sum_mul_sum_inv Finset.univ fun i _ ↦ hd i

/-- `tr (B⁻¹ A) ≤ tr (A⁻¹ B)^{n-1} / det (A⁻¹ B)` for positive definite `A`, `B`. With `A = g`,
`B = g'` and `det g' = e^F det g` this is `tr_{g'} g ≤ e^{-F} (tr_g g')^{n-1}`. -/
theorem trace_inv_mul_le_trace_inv_mul_pow_mul_det_div_det (hA : A.PosDef) (hB : B.PosDef) :
    RCLike.re (B⁻¹ * A).trace ≤
      RCLike.re (A⁻¹ * B).trace ^ (Fintype.card n - 1) * RCLike.re A.det / RCLike.re B.det := by
  obtain ⟨P, d, hPA, hPB⟩ := hA.exists_simultaneous_diagonalization hB.isHermitian
  have hd := (posDef_iff_forall_pos_of_conjTranspose_mul_mul_eq hPA hPB).1 hB
  have hApos : 0 < RCLike.re A.det := (RCLike.pos_iff.1 hA.det_pos).1
  have hprod : 0 < ∏ i, d i := Finset.prod_pos fun i _ ↦ hd i
  rw [re_trace_inv_mul_eq_sum_of_conjTranspose_mul_mul_eq hPA hPB,
    re_trace_inv_mul_eq_sum_inv_of_conjTranspose_mul_mul_eq hPA hPB (fun i ↦ (hd i).ne'),
    re_det_eq_re_det_mul_prod_of_conjTranspose_mul_mul_eq hPA hPB]
  have h := Real.sum_inv_le_sum_pow_div_prod Finset.univ fun i _ ↦ hd i
  rw [Finset.card_univ] at h
  calc _ ≤ _ := h
    _ = _ := by field_simp

/-- `tr (A⁻¹ B)` is monotone in `B` for the Loewner order. -/
theorem trace_inv_mul_le_trace_inv_mul (hA : A.PosDef) (hBC : B ≤ C) :
    RCLike.re (A⁻¹ * B).trace ≤ RCLike.re (A⁻¹ * C).trace :=
  (RCLike.le_iff_re_im.1 (hA.inv.posSemidef.trace_mul_le_trace_mul hBC)).1

end PosDef

end Matrix
