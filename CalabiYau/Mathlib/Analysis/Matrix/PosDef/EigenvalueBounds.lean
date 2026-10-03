module

public import CalabiYau.Mathlib.Analysis.Matrix.Hermitian.SimultaneousDiagonalization
import CalabiYau.Mathlib.Analysis.Matrix.Order
import CalabiYau.Mathlib.Analysis.MeanInequalities
import CalabiYau.Mathlib.Analysis.Matrix.PosDef.TraceInequalities

/-!
# Two-sided Loewner bounds from trace and determinant

Let `A`, `B` be positive definite Hermitian matrices of size `n` and let `λ₁, …, λₙ > 0` be the
eigenvalues of `A⁻¹ B`. Since `λᵢ ≤ ∑ λⱼ = tr (A⁻¹ B)` and
`λᵢ = ∏ λⱼ / ∏_{j ≠ i} λⱼ ≥ det (A⁻¹ B) / tr (A⁻¹ B)^{n-1}`, an upper bound on the trace and a
lower bound on the determinant give two-sided bounds on all `λᵢ`, i.e. a comparison
`c₁ A ≤ B ≤ c₂ A` in the Loewner order. In the C² estimate for the complex Monge–Ampère equation
`det g' = e^F det g`, a bound `tr_g g' ≤ C` thus gives the uniform equivalence
`(e^{inf F} / C^{n-1}) g ≤ g' ≤ C g`.

The Loewner order is `Matrix.instPartialOrder` (`open scoped MatrixOrder`).

## Main statements

* `Matrix.PosDef.le_trace_inv_mul_smul`: `B ≤ tr (A⁻¹ B) • A`.
* `Matrix.PosDef.det_div_det_div_trace_pow_smul_le`:
  `(det B / det A / tr (A⁻¹ B)^{n-1}) • A ≤ B`.
* `Matrix.PosDef.smul_le_and_le_smul_of_trace_le_of_le_det`: if `tr (A⁻¹ B) ≤ C` and
  `det B ≥ c det A` then `(c / C^{n-1}) • A ≤ B ∧ B ≤ C • A`.
* Converses: `Matrix.PosDef.trace_inv_mul_le_of_le_smul`,
  `Matrix.PosDef.card_mul_le_trace_inv_mul_of_smul_le`,
  `Matrix.PosDef.pow_mul_det_le_det_of_smul_le`,
  and `Matrix.PosDef.inv_le_smul_inv_of_smul_le` for the inverse matrices.

## References

* S.-T. Yau, *On the Ricci curvature of a compact Kähler manifold and the complex Monge–Ampère
  equation I*, Comm. Pure Appl. Math. 31 (1978), §2.
* G. Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §3.3, after Proposition 3.8
  ("the metrics `ω` and `ω_φ` are uniformly equivalent").
-/

public section

open scoped ComplexOrder MatrixOrder

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] {A B : Matrix n n 𝕜}

/-- `(c • A)⁻¹ = c⁻¹ • A⁻¹` for a real scalar `c ≠ 0` and invertible `A`. -/
private theorem inv_real_smul {A : Matrix n n 𝕜} (hA : IsUnit A.det) {c : ℝ} (hc : c ≠ 0) :
    (c • A)⁻¹ = c⁻¹ • A⁻¹ :=
  inv_eq_left_inv (by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul,
      nonsing_inv_mul _ hA])

omit [Fintype n] [DecidableEq n] in
/-- A matrix bounded above or below by a real multiple of a Hermitian matrix is Hermitian. -/
private theorem isHermitian_of_sub_smul {A B : Matrix n n 𝕜} (hA : A.IsHermitian) {c : ℝ}
    (h : (B - c • A).IsHermitian) : B.IsHermitian := by
  have h2 : (c • A).IsHermitian := by
    rw [IsHermitian, conjTranspose_smul, hA.eq, star_trivial]
  simpa using h.add h2

namespace PosDef

/-- Upper Loewner bound by the trace: `B ≤ tr (A⁻¹ B) • A`. -/
theorem le_trace_inv_mul_smul (hA : A.PosDef) (hB : B.PosSemidef) :
    B ≤ RCLike.re (A⁻¹ * B).trace • A := by
  obtain ⟨P, d, hPA, hPB⟩ := hA.exists_simultaneous_diagonalization hB.isHermitian
  have hd := (posSemidef_iff_forall_nonneg_of_conjTranspose_mul_mul_eq hPA hPB).1 hB
  rw [le_smul_iff_forall_le_of_conjTranspose_mul_mul_eq hPA hPB,
    re_trace_inv_mul_eq_sum_of_conjTranspose_mul_mul_eq hPA hPB]
  exact fun i ↦ Finset.single_le_sum (fun j _ ↦ hd j) (Finset.mem_univ i)

/-- Lower Loewner bound by determinant and trace:
`(det B / det A / tr (A⁻¹ B)^{n-1}) • A ≤ B`. -/
theorem det_div_det_div_trace_pow_smul_le (hA : A.PosDef) (hB : B.PosDef) :
    (RCLike.re B.det / RCLike.re A.det / RCLike.re (A⁻¹ * B).trace ^ (Fintype.card n - 1)) • A ≤
      B := by
  obtain ⟨P, d, hPA, hPB⟩ := hA.exists_simultaneous_diagonalization hB.isHermitian
  have hd := (posDef_iff_forall_pos_of_conjTranspose_mul_mul_eq hPA hPB).1 hB
  have hApos : 0 < RCLike.re A.det := (RCLike.pos_iff.1 hA.det_pos).1
  rw [smul_le_iff_forall_le_of_conjTranspose_mul_mul_eq hPA hPB,
    re_trace_inv_mul_eq_sum_of_conjTranspose_mul_mul_eq hPA hPB,
    re_det_eq_re_det_mul_prod_of_conjTranspose_mul_mul_eq hPA hPB, mul_div_cancel_left₀ _ hApos.ne']
  intro i
  simpa using Real.prod_div_sum_pow_le Finset.univ (fun j _ ↦ hd j) (Finset.mem_univ i)

/-- **Uniform equivalence from trace and determinant bounds.** If `tr (A⁻¹ B) ≤ C` and
`det (A⁻¹ B) ≥ c`, then `(c / C^{n-1}) • A ≤ B ≤ C • A`. -/
theorem smul_le_and_le_smul_of_trace_le_of_le_det (hA : A.PosDef) (hB : B.PosDef) {c C : ℝ}
    (htr : RCLike.re (A⁻¹ * B).trace ≤ C) (hdet : c * RCLike.re A.det ≤ RCLike.re B.det) :
    (c / C ^ (Fintype.card n - 1)) • A ≤ B ∧ B ≤ C • A := by
  obtain ⟨P, d, hPA, hPB⟩ := hA.exists_simultaneous_diagonalization hB.isHermitian
  have hd := (posDef_iff_forall_pos_of_conjTranspose_mul_mul_eq hPA hPB).1 hB
  have hApos : 0 < RCLike.re A.det := (RCLike.pos_iff.1 hA.det_pos).1
  rw [re_trace_inv_mul_eq_sum_of_conjTranspose_mul_mul_eq hPA hPB] at htr
  rw [re_det_eq_re_det_mul_prod_of_conjTranspose_mul_mul_eq hPA hPB, mul_comm c] at hdet
  have hprod : c ≤ ∏ i, d i := le_of_mul_le_mul_left hdet hApos
  have hS : 0 ≤ ∑ i, d i := Finset.sum_nonneg fun i _ ↦ (hd i).le
  have hdS : ∀ i, d i ≤ ∑ j, d j := fun i ↦
    Finset.single_le_sum (fun j _ ↦ (hd j).le) (Finset.mem_univ i)
  rw [smul_le_iff_forall_le_of_conjTranspose_mul_mul_eq hPA hPB,
    le_smul_iff_forall_le_of_conjTranspose_mul_mul_eq hPA hPB]
  refine ⟨fun i ↦ ?_, fun i ↦ (hdS i).trans htr⟩
  rcases le_or_gt c 0 with hc | hc
  · exact (div_nonpos_of_nonpos_of_nonneg hc (pow_nonneg (hS.trans htr) _)).trans (hd i).le
  · have key := Real.prod_div_sum_pow_le Finset.univ (fun j _ ↦ hd j) (Finset.mem_univ i)
    rw [Finset.card_univ] at key
    refine le_trans ?_ key
    exact div_le_div₀ (hc.le.trans hprod) hprod
      (pow_pos (Finset.sum_pos (fun j _ ↦ hd j) ⟨i, Finset.mem_univ i⟩) _)
      (pow_le_pow_left₀ hS htr _)

/-- An upper Loewner bound `B ≤ c • A` bounds the trace: `tr (A⁻¹ B) ≤ n c`. -/
theorem trace_inv_mul_le_of_le_smul (hA : A.PosDef) {c : ℝ} (h : B ≤ c • A) :
    RCLike.re (A⁻¹ * B).trace ≤ Fintype.card n * c := by
  have hB := isHermitian_of_sub_smul hA.isHermitian (by simpa using (le_iff.1 h).isHermitian.neg)
  obtain ⟨P, d, hPA, hPB⟩ := hA.exists_simultaneous_diagonalization hB
  rw [le_smul_iff_forall_le_of_conjTranspose_mul_mul_eq hPA hPB] at h
  rw [re_trace_inv_mul_eq_sum_of_conjTranspose_mul_mul_eq hPA hPB]
  simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ h i

/-- A lower Loewner bound `c • A ≤ B` bounds the trace: `n c ≤ tr (A⁻¹ B)`. -/
theorem card_mul_le_trace_inv_mul_of_smul_le (hA : A.PosDef) {c : ℝ} (h : c • A ≤ B) :
    Fintype.card n * c ≤ RCLike.re (A⁻¹ * B).trace := by
  have hB := isHermitian_of_sub_smul hA.isHermitian (le_iff.1 h).isHermitian
  obtain ⟨P, d, hPA, hPB⟩ := hA.exists_simultaneous_diagonalization hB
  rw [smul_le_iff_forall_le_of_conjTranspose_mul_mul_eq hPA hPB] at h
  rw [re_trace_inv_mul_eq_sum_of_conjTranspose_mul_mul_eq hPA hPB]
  simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ h i

/-- A lower Loewner bound `c • A ≤ B` with `c ≥ 0` bounds the determinant: `cⁿ det A ≤ det B`. -/
theorem pow_mul_det_le_det_of_smul_le (hA : A.PosDef) {c : ℝ} (hc : 0 ≤ c) (h : c • A ≤ B) :
    c ^ Fintype.card n * RCLike.re A.det ≤ RCLike.re B.det := by
  have hB := isHermitian_of_sub_smul hA.isHermitian (le_iff.1 h).isHermitian
  obtain ⟨P, d, hPA, hPB⟩ := hA.exists_simultaneous_diagonalization hB
  have hApos : 0 < RCLike.re A.det := (RCLike.pos_iff.1 hA.det_pos).1
  rw [smul_le_iff_forall_le_of_conjTranspose_mul_mul_eq hPA hPB] at h
  rw [re_det_eq_re_det_mul_prod_of_conjTranspose_mul_mul_eq hPA hPB, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ hApos.le
  simpa using Finset.prod_le_prod₀ (fun i (_ : i ∈ Finset.univ) ↦ hc) fun i _ ↦ h i

/-- A lower Loewner bound `c • A ≤ B` with `c > 0` gives the upper bound `B⁻¹ ≤ c⁻¹ • A⁻¹` for the
inverse matrices (the inverse metrics `g'^{i j̄} ≤ c⁻¹ g^{i j̄}`). -/
theorem inv_le_smul_inv_of_smul_le (hA : A.PosDef) {c : ℝ} (hc : 0 < c) (h : c • A ≤ B) :
    B⁻¹ ≤ c⁻¹ • A⁻¹ := by
  have hcA : (c • A).PosDef := hA.smul hc
  rw [← inv_real_smul ((isUnit_iff_isUnit_det A).1 hA.isUnit) hc.ne']
  exact hcA.inv_le_inv h

/-- An upper Loewner bound `B ≤ c • A` with `B` positive definite gives the lower bound
`c⁻¹ • A⁻¹ ≤ B⁻¹` for the inverse matrices. -/
theorem smul_inv_le_inv_of_le_smul (hA : A.PosDef) (hB : B.PosDef) {c : ℝ} (h : B ≤ c • A) :
    c⁻¹ • A⁻¹ ≤ B⁻¹ := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact le_of_eq (Subsingleton.elim _ _)
  have hc : 0 < c := by
    have h1 := trace_inv_mul_le_of_le_smul hA h
    have h2 := trace_inv_mul_pos hA hB
    have h3 : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
    nlinarith
  rw [← inv_real_smul ((isUnit_iff_isUnit_det A).1 hA.isUnit) hc.ne']
  exact hB.inv_le_inv h

end PosDef

end Matrix
