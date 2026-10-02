module

public import CalabiYau.Geometry.Complex.Forms.OneOne
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CalabiYau.Mathlib.Analysis.Matrix.PosDef.TraceInequalities
import CalabiYau.Mathlib.Analysis.Matrix.PosDef.EigenvalueBounds

/-!
# Inequalities between positive `(1,1)`-forms

Pointwise trace and determinant inequalities for positive `(1,1)`-forms on `ℂⁿ`, in the language
of `relTrace` (`tr_ω α`) and `relDet` (`αⁿ / ωⁿ`). They are the forms-level versions of the
Hermitian matrix inequalities of `CalabiYau.LinearAlgebra.Hermitian` (applied to the coefficient
matrices, `isPositive_iff`), and are what the `C⁰` and `C²` estimates consume:

* AM–GM: `(αⁿ/ωⁿ)^{1/n} ≤ tr_ω α / n`;
* `n² ≤ tr_ω α · tr_α ω` and `tr_α ω ≤ (tr_ω α)ⁿ⁻¹ · ωⁿ/αⁿ` (Aubin–Yau `C²` estimate);
* `α ≤ (tr_ω α) ω`;
* monotonicity of `α ↦ αⁿ⁻¹` against semipositive forms:
  `tr_ω β ≤ (αⁿ/ωⁿ) tr_α β` when `α ≥ ω` and `β ≥ 0`, i.e. `β ∧ ωⁿ⁻¹ ≤ β ∧ αⁿ⁻¹`
  (Yau's `C⁰` estimate; this is the monotonicity of the adjugate on positive semidefinite
  matrices).
-/

@[expose] public section

namespace ContinuousAlternatingMap

open scoped ComplexOrder MatrixOrder
open Matrix

variable {n : ℕ} {α β ω : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ}

theorem relTrace_smul_left (hω : ω.IsPositive) {c : ℝ} (hc : 0 < c) :
    relTrace (c • ω) α = c⁻¹ * relTrace ω α := by
  have hA : (ω.coeffMatrix).PosDef := (isPositive_iff.mp hω).2
  have hunit : IsUnit ω.coeffMatrix.det := (Matrix.isUnit_iff_isUnit_det ω.coeffMatrix).1 hA.isUnit
  have hinv : (c • ω.coeffMatrix)⁻¹ = c⁻¹ • ω.coeffMatrix⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc.ne', one_smul,
      Matrix.nonsing_inv_mul _ hunit]
  simp only [relTrace, coeffMatrix_smul, hinv, Matrix.smul_mul]
  simp [Complex.real_smul]

theorem relDet_smul_left (hω : ω.IsPositive) {c : ℝ} (hc : 0 < c) :
    relDet (c • ω) α = (c ^ n)⁻¹ * relDet ω α := by
  have hdet : (c • ω.coeffMatrix).det = (c : ℂ) ^ n * ω.coeffMatrix.det := by
    simp
  have hden : RCLike.re ((c : ℂ) ^ n * ω.coeffMatrix.det) =
      c ^ n * RCLike.re ω.coeffMatrix.det := by
    have hc_pow : (c : ℂ) ^ n = ((c ^ n : ℝ) : ℂ) := by push_cast; rfl
    rw [hc_pow]
    change (↑(c ^ n) * ω.coeffMatrix.det).re = c ^ n * ω.coeffMatrix.det.re
    exact Complex.re_ofReal_mul _ _
  change RCLike.re α.coeffMatrix.det / RCLike.re (coeffMatrix (c • ω)).det =
    (c ^ n)⁻¹ * (RCLike.re α.coeffMatrix.det / RCLike.re ω.coeffMatrix.det)
  rw [coeffMatrix_smul, hdet, hden]
  have hωdet : RCLike.re ω.coeffMatrix.det ≠ 0 :=
    ((RCLike.pos_iff.1 ((isPositive_iff (α := ω)).mp hω).2.det_pos).1).ne'
  field_simp [pow_ne_zero _ hc.ne', hωdet]

/-- AM–GM: `(αⁿ/ωⁿ)^{1/n} ≤ tr_ω α / n`. -/
theorem relDet_rpow_le_relTrace_div [NeZero n] (hω : ω.IsPositive) (hα : α.IsNonneg) :
    relDet ω α ^ ((n : ℝ)⁻¹) ≤ relTrace ω α / n := by
  have hn : (Fintype.card (Fin n) : ℝ) = n := by simp
  simpa [relDet, relTrace, hn] using
    (Matrix.PosDef.geom_mean_le_arith_mean_inv_mul
      ((isPositive_iff (α := ω)).mp hω).2 ((isNonneg_iff (α := α)).mp hα).2)

theorem sq_le_relTrace_mul_relTrace (hω : ω.IsPositive) (hα : α.IsPositive) :
    (n : ℝ) ^ 2 ≤ relTrace ω α * relTrace α ω := by
  have hn : (Fintype.card (Fin n) : ℝ) = n := by simp
  simpa [relTrace, hn] using
    (Matrix.PosDef.card_sq_le_trace_inv_mul_mul_trace_inv_mul
      ((isPositive_iff (α := ω)).mp hω).2 ((isPositive_iff (α := α)).mp hα).2)

/-- `tr_α ω ≤ (tr_ω α)ⁿ⁻¹ · ωⁿ/αⁿ`. -/
theorem relTrace_le_relTrace_pow_div_relDet (hω : ω.IsPositive) (hα : α.IsPositive) :
    relTrace α ω ≤ relTrace ω α ^ (n - 1) / relDet ω α := by
  have hn : (Fintype.card (Fin n) : ℝ) = n := by simp
  simpa [relTrace, relDet, hn, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    (Matrix.PosDef.trace_inv_mul_le_trace_inv_mul_pow_mul_det_div_det
      ((isPositive_iff (α := ω)).mp hω).2 ((isPositive_iff (α := α)).mp hα).2)

/-- `α ≤ (tr_ω α) ω` for semipositive `α`. -/
theorem isNonneg_relTrace_smul_sub (hω : ω.IsPositive) (hα : α.IsNonneg) :
    (relTrace ω α • ω - α).IsNonneg := by
  have h := Matrix.PosDef.le_trace_inv_mul_smul
    ((isPositive_iff (α := ω)).mp hω).2 ((isNonneg_iff (α := α)).mp hα).2
  apply (isNonneg_sub_iff (α := relTrace ω α • ω) (ω := α)
    (hω.1.smul _) hα.1).2
  simpa [coeffMatrix_smul, relTrace] using h

/-- If `α ≤ c ω` then `tr_ω α ≤ n c`. -/
theorem relTrace_le_of_isNonneg_smul_sub (hω : ω.IsPositive) (hα : α.IsOneOne) {c : ℝ}
    (h : (c • ω - α).IsNonneg) : relTrace ω α ≤ n * c := by
  have hmat := (isNonneg_sub_iff (α := c • ω) (ω := α)
    (hω.1.smul c) hα).mp h
  have h' := Matrix.PosDef.trace_inv_mul_le_of_le_smul ((isPositive_iff (α := ω)).mp hω).2
    (by simpa [coeffMatrix_smul] using hmat)
  simpa [relTrace, hncast] using h'
  where hncast : (Fintype.card (Fin n) : ℝ) = n := by simp

/-- If `c ω ≤ α` with `c ≥ 0` then `cⁿ ≤ αⁿ/ωⁿ`. -/
theorem pow_le_relDet_of_isNonneg_sub_smul (hω : ω.IsPositive) (hα : α.IsOneOne) {c : ℝ}
    (hc : 0 ≤ c) (h : (α - c • ω).IsNonneg) : c ^ n ≤ relDet ω α := by
  have hmat := (isNonneg_sub_iff (α := α) (ω := c • ω) hα (hω.1.smul c)).mp h
  have h' := Matrix.PosDef.pow_mul_det_le_det_of_smul_le
    ((isPositive_iff (α := ω)).mp hω).2 hc (by simpa [coeffMatrix_smul] using hmat)
  have hdet : 0 < RCLike.re (ω.coeffMatrix).det :=
    (RCLike.pos_iff.1 ((isPositive_iff (α := ω)).mp hω).2.det_pos).1
  have hn : (Fintype.card (Fin n) : ℝ) = n := by simp
  rw [relDet]
  exact (le_div_iff₀ hdet).2 (by simpa [hn] using h')

/-- Two-sided bound from a trace bound and a determinant lower bound:
`tr_ω α ≤ Λ` and `αⁿ/ωⁿ ≥ δ` imply `(δ / Λⁿ⁻¹) ω ≤ α ≤ Λ ω`. -/
theorem isNonneg_sub_smul_of_relTrace_le_of_le_relDet (hω : ω.IsPositive) (hα : α.IsPositive)
    {δ Λ : ℝ} (htr : relTrace ω α ≤ Λ) (hdet : δ ≤ relDet ω α) :
    (α - (δ / Λ ^ (n - 1)) • ω).IsNonneg ∧ (Λ • ω - α).IsNonneg := by
  have hbounds := Matrix.PosDef.smul_le_and_le_smul_of_trace_le_of_le_det
    ((isPositive_iff (α := ω)).mp hω).2 ((isPositive_iff (α := α)).mp hα).2
    htr (by
      have hdet' := (le_div_iff₀ ((RCLike.pos_iff.1 ((isPositive_iff (α := ω)).mp hω).2.det_pos).1)).mp hdet
      simpa [relDet, mul_comm] using hdet')
  have hn : (Fintype.card (Fin n) : ℝ) = n := by simp
  constructor
  · apply (isNonneg_sub_iff (α := α) (ω := (δ / Λ ^ (n - 1)) • ω)
      hα.1 (hω.1.smul _)).2
    simpa [coeffMatrix_smul, hn] using hbounds.1
  · apply (isNonneg_sub_iff (α := Λ • ω) (ω := α)
      (hω.1.smul _) hα.1).2
    simpa [coeffMatrix_smul] using hbounds.2

/-- Monotonicity of `α ↦ αⁿ⁻¹` against semipositive forms: if `ω ≤ α` and `β ≥ 0` then
`tr_ω β ≤ (αⁿ/ωⁿ) tr_α β`, i.e. `β ∧ ωⁿ⁻¹ ≤ β ∧ αⁿ⁻¹`. -/
theorem relTrace_le_relDet_mul_relTrace (hω : ω.IsPositive) (hωα : (α - ω).IsNonneg)
    (hβ : β.IsNonneg) : relTrace ω β ≤ relDet ω α * relTrace α β := by
  classical
  let G := ω.coeffMatrix
  let B := α.coeffMatrix
  let C := β.coeffMatrix
  have hα11 : α.IsOneOne := by
    have h := hωα.1.add hω.1
    simpa [sub_add_cancel] using h
  have hG : G.PosDef := (isPositive_iff.mp hω).2
  have hBherm : B.IsHermitian := hα11.isHermitian_coeffMatrix
  have hC : C.PosSemidef := (isNonneg_iff.mp hβ).2
  have hGleB : G ≤ B := (isNonneg_sub_iff hα11 hω.1).mp hωα
  obtain ⟨P, d, hPA, hPB⟩ := hG.exists_simultaneous_diagonalization hBherm
  have hd : ∀ i, 1 ≤ d i := by
    exact (Matrix.smul_le_iff_forall_le_of_conjTranspose_mul_mul_eq hPA hPB 1).mp
      (by simpa [G, B] using hGleB)
  let Dinv : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun i ↦ ((d i)⁻¹ : ℝ)
  have hD : Dinv * Matrix.diagonal (RCLike.ofReal ∘ d) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    simp [(lt_of_lt_of_le zero_lt_one (hd i)).ne']
  have h1 : P * (Pᴴ * G) = 1 := mul_eq_one_comm.1 hPA
  have hGinv : G⁻¹ = P * Pᴴ := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.mul_assoc]
    exact h1
  have hBinv : B⁻¹ = P * Dinv * Pᴴ := by
    apply Matrix.inv_eq_left_inv
    calc
      P * Dinv * Pᴴ * B = P * Dinv * Pᴴ * B * (P * (Pᴴ * G)) := by rw [h1, Matrix.mul_one]
      _ = P * (Dinv * (Pᴴ * B * P)) * (Pᴴ * G) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPB, hD, Matrix.mul_one, h1]
  let X := Pᴴ * C * P
  have hX : X.PosSemidef := hC.conjTranspose_mul_mul_same P
  have hXdiag : ∀ i, 0 ≤ RCLike.re (X i i) := by
    intro i
    exact (RCLike.le_iff_re_im.1 hX.diag_nonneg).1
  have hTraceG : relTrace ω β = ∑ i, RCLike.re (X i i) := by
    change RCLike.re (G⁻¹ * C).trace = _
    rw [hGinv, Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
    simp [X, Matrix.trace]
  have hTraceB : relTrace α β = ∑ i, (d i)⁻¹ * RCLike.re (X i i) := by
    change RCLike.re (B⁻¹ * C).trace = _
    rw [hBinv, Matrix.mul_assoc (P * Dinv), Matrix.trace_mul_cycle]
    simp [X, Dinv, Matrix.trace, mul_comm]
  have hDet : relDet ω α = ∏ i, d i := by
    have hGdet : 0 < RCLike.re G.det := (RCLike.pos_iff.1 hG.det_pos).1
    change RCLike.re B.det / RCLike.re G.det = _
    rw [Matrix.re_det_eq_re_det_mul_prod_of_conjTranspose_mul_mul_eq hPA hPB]
    exact mul_div_cancel_left₀ _ hGdet.ne'
  have hcoef : ∀ i, 1 ≤ (∏ j, d j) * (d i)⁻¹ := by
    intro i
    rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin n)) d (Finset.mem_univ i)]
    field_simp [(lt_of_lt_of_le zero_lt_one (hd i)).ne']
    calc
      1 = ∏ _j ∈ (Finset.univ.erase i), (1 : ℝ) := by simp
      _ ≤ ∏ j ∈ (Finset.univ.erase i), d j := by
        apply Finset.prod_le_prod
        · intro j hj
          exact zero_le_one
        · intro j hj
          exact hd j
  have hsum : (∑ i, RCLike.re (X i i)) ≤
      (∏ i, d i) * (∑ i, (d i)⁻¹ * RCLike.re (X i i)) := by
    calc
      (∑ i, RCLike.re (X i i)) = ∑ i, 1 * RCLike.re (X i i) := by simp
      _ ≤ ∑ i, ((∏ j, d j) * (d i)⁻¹) * RCLike.re (X i i) :=
        Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right (hcoef i) (hXdiag i)
      _ = (∏ i, d i) * (∑ i, (d i)⁻¹ * RCLike.re (X i i)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  rw [hTraceG, hTraceB, hDet]
  exact hsum

end ContinuousAlternatingMap
