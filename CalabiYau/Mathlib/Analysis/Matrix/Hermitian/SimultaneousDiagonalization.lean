module

public import Mathlib.Analysis.Matrix.Order

/-!
# Simultaneous diagonalization of a positive definite and a Hermitian matrix

Let `A` be a positive definite and `B` a Hermitian matrix over `𝕜 = ℝ` or `ℂ`. Then there is an
invertible matrix `P` with `Pᴴ A P = 1` and `Pᴴ B P = diagonal d` for a real vector `d`. The
entries `dᵢ` are the eigenvalues of `A⁻¹ B` (equivalently of the Hermitian matrix
`A^{-1/2} B A^{-1/2}`); in Kähler geometry, with `A = (g_{i j̄})` and `B = (g'_{i j̄})` two
Hermitian metrics at a point, this is the choice of coordinates in which `g` is the identity and
`g'` is diagonal.

Rather than introducing a definition for the relative eigenvalues, the statements below take an
arbitrary diagonalizing pair `(P, d)` as hypotheses `Pᴴ * A * P = 1` and
`Pᴴ * B * P = diagonal (RCLike.ofReal ∘ d)`, and translate trace, determinant, definiteness and
the Loewner order into statements about `d`. Every matrix inequality in
`CalabiYau.LinearAlgebra.Hermitian.TraceInequality` and
`CalabiYau.LinearAlgebra.Hermitian.EigenvalueBound` is proved by this reduction.

## Main statements

* `Matrix.PosDef.exists_simultaneous_diagonalization`: existence of `P` and `d`.
* `Matrix.PosDef.exists_unitary_diagonalization`: the unitary-congruence form, with the explicit
  choice `P = A^{-1/2} U` for a unitary `U` diagonalizing `A^{-1/2} B A^{-1/2}`.
* `Matrix.PosDef.spectrum_inv_mul_subset_range_ofReal`: the eigenvalues of `A⁻¹ B` are real.
* `Matrix.trace_inv_mul_eq_sum_of_conjTranspose_mul_mul_eq`,
  `Matrix.det_eq_det_mul_prod_of_conjTranspose_mul_mul_eq`,
  `Matrix.smul_le_iff_forall_le_of_conjTranspose_mul_mul_eq`, …: the dictionary, with real forms
  `Matrix.re_trace_inv_mul_eq_sum_of_conjTranspose_mul_mul_eq`, … .

## References

* R. A. Horn, C. R. Johnson, *Matrix Analysis*, 2nd ed., Theorem 7.6.4.
* G. Székelyhidi, *An Introduction to Extremal Kähler Metrics*, proof of Lemma 3.7
  ("choose coordinates such that `g` is the identity and `g'` is diagonal").
-/

public section

open scoped ComplexOrder MatrixOrder

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] {A B P : Matrix n n 𝕜} {d : n → ℝ}

/-! ### Existence -/

namespace PosDef

/-- **Simultaneous diagonalization**, unitary-congruence form: with `U` a unitary matrix
diagonalizing the Hermitian matrix `A^{-1/2} B A^{-1/2}`, the congruence by `P = A^{-1/2} U`
brings `A` to `1` and `B` to a real diagonal matrix. -/
theorem exists_unitary_diagonalization (hA : A.PosDef) (hB : B.IsHermitian) :
    ∃ (U : unitaryGroup n 𝕜) (d : n → ℝ),
      (CFC.sqrt A⁻¹ * (U : Matrix n n 𝕜))ᴴ * A * (CFC.sqrt A⁻¹ * (U : Matrix n n 𝕜)) = 1 ∧
      (CFC.sqrt A⁻¹ * (U : Matrix n n 𝕜))ᴴ * B * (CFC.sqrt A⁻¹ * (U : Matrix n n 𝕜)) =
        diagonal (RCLike.ofReal ∘ d) := by
  set S := CFC.sqrt A⁻¹
  have hS : Sᴴ = S := (nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg _)).isHermitian.eq
  have hSAS : S * A * S = 1 := by
    set R := CFC.sqrt A
    have hRR : R * R = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
    have hR : IsUnit R.det := by
      have h := (isUnit_iff_isUnit_det A).1 hA.isUnit
      rw [← hRR, det_mul] at h
      exact isUnit_of_mul_isUnit_left h
    have hSR : S = R⁻¹ := hA.posSemidef.inv_sqrt.symm
    rw [hSR, ← hRR, Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv R hR, Matrix.mul_one,
      nonsing_inv_mul R hR]
  have hC : (S * B * S).IsHermitian := by
    simpa only [hS] using isHermitian_conjTranspose_mul_mul S hB
  refine ⟨hC.eigenvectorUnitary, hC.eigenvalues, ?_, ?_⟩
  · have h1 : star (hC.eigenvectorUnitary : Matrix n n 𝕜) * (S * A * S) *
        (hC.eigenvectorUnitary : Matrix n n 𝕜) = 1 := by
      rw [hSAS, Matrix.mul_one, Unitary.coe_star_mul_self]
    rw [conjTranspose_mul, hS, ← star_eq_conjTranspose]
    simpa only [Matrix.mul_assoc] using h1
  · have h := hC.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at h
    rw [← h, conjTranspose_mul, hS, ← star_eq_conjTranspose]
    simp only [Matrix.mul_assoc]

/-- **Simultaneous diagonalization**: a positive definite matrix `A` and a Hermitian matrix `B`
can be brought by one congruence to `1` and to a real diagonal matrix respectively. -/
theorem exists_simultaneous_diagonalization (hA : A.PosDef) (hB : B.IsHermitian) :
    ∃ (P : Matrix n n 𝕜) (d : n → ℝ),
      Pᴴ * A * P = 1 ∧ Pᴴ * B * P = diagonal (RCLike.ofReal ∘ d) :=
  let ⟨_, d, h⟩ := hA.exists_unitary_diagonalization hB
  ⟨_, d, h⟩

end PosDef

/-! ### Dictionary for a diagonalizing pair -/

private theorem isUnit_of_conjTranspose_mul_mul_eq_one (hPA : Pᴴ * A * P = 1) : IsUnit P :=
  @isUnit_of_invertible _ _ P (invertibleOfLeftInverse P (Pᴴ * A) hPA)

private theorem inv_eq_of_conjTranspose_mul_mul_eq_one (hPA : Pᴴ * A * P = 1) :
    A⁻¹ = P * Pᴴ :=
  inv_eq_left_inv (by rw [Matrix.mul_assoc]; exact mul_eq_one_comm.1 hPA)

/-- Congruence by an invertible `P` turns `c • A ≤ B` into a statement about `Pᴴ (B - c • A) P`. -/
private theorem smul_le_iff_of_conjTranspose_mul_mul_eq (hPA : Pᴴ * A * P = 1) (c : ℝ) :
    c • A ≤ B ↔ (Pᴴ * B * P - c • (1 : Matrix n n 𝕜)).PosSemidef := by
  rw [le_iff, ← Matrix.IsUnit.posSemidef_star_left_conjugate_iff
    (isUnit_of_conjTranspose_mul_mul_eq_one hPA), star_eq_conjTranspose, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hPA]

section Dictionary

variable (hPA : Pᴴ * A * P = 1) (hPB : Pᴴ * B * P = diagonal (RCLike.ofReal ∘ d))
include hPA hPB

/-- A diagonalizing pair conjugates `A⁻¹ B` to `diagonal d`. -/
theorem inv_mul_eq_of_conjTranspose_mul_mul_eq :
    A⁻¹ * B = P * diagonal (RCLike.ofReal ∘ d) * P⁻¹ := by
  have h1 : P * (Pᴴ * A) = 1 := mul_eq_one_comm.1 hPA
  rw [inv_eq_of_conjTranspose_mul_mul_eq_one hPA, inv_eq_left_inv hPA, ← hPB]
  calc P * Pᴴ * B = P * Pᴴ * B * (P * (Pᴴ * A)) := by rw [h1, Matrix.mul_one]
    _ = P * (Pᴴ * B * P) * (Pᴴ * A) := by simp only [Matrix.mul_assoc]

/-- `tr (A⁻¹ B) = ∑ dᵢ`. -/
theorem trace_inv_mul_eq_sum_of_conjTranspose_mul_mul_eq :
    (A⁻¹ * B).trace = ∑ i, (d i : 𝕜) := by
  rw [inv_mul_eq_of_conjTranspose_mul_mul_eq hPA hPB, trace_mul_cycle, inv_eq_left_inv hPA, hPA,
    Matrix.one_mul, trace_diagonal]
  rfl

/-- `tr (B⁻¹ A) = ∑ dᵢ⁻¹` when all `dᵢ ≠ 0`, i.e. when `B` is invertible. -/
theorem trace_inv_mul_eq_sum_inv_of_conjTranspose_mul_mul_eq (hd : ∀ i, d i ≠ 0) :
    (B⁻¹ * A).trace = ∑ i, ((d i)⁻¹ : 𝕜) := by
  set D' : Matrix n n 𝕜 := diagonal fun i ↦ ((d i)⁻¹ : 𝕜)
  have hDD : D' * diagonal (RCLike.ofReal ∘ d) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (RCLike.ofReal_ne_zero.2 (hd i))
  have h1 : P * (Pᴴ * A) = 1 := mul_eq_one_comm.1 hPA
  have hBinv : B⁻¹ = P * D' * Pᴴ := by
    apply inv_eq_left_inv
    calc P * D' * Pᴴ * B = P * D' * Pᴴ * B * (P * (Pᴴ * A)) := by rw [h1, Matrix.mul_one]
      _ = P * (D' * (Pᴴ * B * P)) * (Pᴴ * A) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPB, hDD, Matrix.mul_one, h1]
  rw [hBinv, Matrix.mul_assoc (P * D'), trace_mul_cycle, hPA, Matrix.one_mul, trace_diagonal]

/-- `det B = det A · ∏ dᵢ`, i.e. `det (A⁻¹ B) = ∏ dᵢ`. -/
theorem det_eq_det_mul_prod_of_conjTranspose_mul_mul_eq :
    B.det = A.det * ∏ i, (d i : 𝕜) := by
  have e1 := congrArg det hPA
  have e2 := congrArg det hPB
  simp only [det_mul, det_one, det_diagonal, Function.comp_apply] at e1 e2
  linear_combination (-B.det) * e1 + A.det * e2

/-- `re tr (A⁻¹ B) = ∑ dᵢ`. -/
theorem re_trace_inv_mul_eq_sum_of_conjTranspose_mul_mul_eq :
    RCLike.re (A⁻¹ * B).trace = ∑ i, d i := by
  rw [trace_inv_mul_eq_sum_of_conjTranspose_mul_mul_eq hPA hPB, ← RCLike.ofReal_sum,
    RCLike.ofReal_re]

/-- `re tr (B⁻¹ A) = ∑ dᵢ⁻¹` when all `dᵢ ≠ 0`. -/
theorem re_trace_inv_mul_eq_sum_inv_of_conjTranspose_mul_mul_eq (hd : ∀ i, d i ≠ 0) :
    RCLike.re (B⁻¹ * A).trace = ∑ i, (d i)⁻¹ := by
  rw [trace_inv_mul_eq_sum_inv_of_conjTranspose_mul_mul_eq hPA hPB hd]
  simp_rw [← RCLike.ofReal_inv]
  rw [← RCLike.ofReal_sum, RCLike.ofReal_re]

/-- `re (det B) = re (det A) · ∏ dᵢ`. -/
theorem re_det_eq_re_det_mul_prod_of_conjTranspose_mul_mul_eq :
    RCLike.re B.det = RCLike.re A.det * ∏ i, d i := by
  rw [det_eq_det_mul_prod_of_conjTranspose_mul_mul_eq hPA hPB, ← RCLike.ofReal_prod,
    RCLike.re_mul_ofReal]

/-- `B` is positive definite iff all `dᵢ > 0`. -/
theorem posDef_iff_forall_pos_of_conjTranspose_mul_mul_eq : B.PosDef ↔ ∀ i, 0 < d i := by
  rw [← Matrix.IsUnit.posDef_star_left_conjugate_iff (isUnit_of_conjTranspose_mul_mul_eq_one hPA),
    star_eq_conjTranspose, hPB, posDef_diagonal_iff]
  simp

/-- `B` is positive semidefinite iff all `dᵢ ≥ 0`. -/
theorem posSemidef_iff_forall_nonneg_of_conjTranspose_mul_mul_eq :
    B.PosSemidef ↔ ∀ i, 0 ≤ d i := by
  rw [← Matrix.IsUnit.posSemidef_star_left_conjugate_iff
    (isUnit_of_conjTranspose_mul_mul_eq_one hPA), star_eq_conjTranspose, hPB,
    posSemidef_diagonal_iff]
  simp

/-- `c A ≤ B` in the Loewner order iff `c ≤ dᵢ` for all `i`. -/
theorem smul_le_iff_forall_le_of_conjTranspose_mul_mul_eq (c : ℝ) :
    c • A ≤ B ↔ ∀ i, c ≤ d i := by
  rw [smul_le_iff_of_conjTranspose_mul_mul_eq hPA, hPB, ← diagonal_one, ← diagonal_smul,
    diagonal_sub, posSemidef_diagonal_iff]
  refine forall_congr' fun i ↦ ?_
  simp only [Function.comp_apply, Pi.smul_apply, RCLike.real_smul_eq_coe_mul, mul_one, sub_nonneg]
  exact RCLike.ofReal_le_ofReal

/-- `B ≤ c A` in the Loewner order iff `dᵢ ≤ c` for all `i`. -/
theorem le_smul_iff_forall_le_of_conjTranspose_mul_mul_eq (c : ℝ) :
    B ≤ c • A ↔ ∀ i, d i ≤ c := by
  rw [le_iff, ← Matrix.IsUnit.posSemidef_star_left_conjugate_iff
    (isUnit_of_conjTranspose_mul_mul_eq_one hPA), star_eq_conjTranspose, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hPA, hPB, ← diagonal_one, ← diagonal_smul,
    diagonal_sub, posSemidef_diagonal_iff]
  refine forall_congr' fun i ↦ ?_
  simp only [Function.comp_apply, Pi.smul_apply, RCLike.real_smul_eq_coe_mul, mul_one, sub_nonneg]
  exact RCLike.ofReal_le_ofReal

end Dictionary

namespace PosDef

end PosDef

end Matrix
