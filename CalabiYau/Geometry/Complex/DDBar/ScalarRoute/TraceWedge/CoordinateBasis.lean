module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import CalabiYau.Geometry.Complex.Forms.OneOne
public import CalabiYau.Geometry.Manifold.Tensor.Alternating.Wedge

/-!
# Real coordinate pieces of the flat Kähler form

In unitary coordinates, `i dzⱼ ∧ dbar zⱼ = 2 dxⱼ ∧ dyⱼ`. The real
continuous alternating two-form `eta j` realizes this piece using the
project's factorial-normalized wedge and the continuous covectors `dx j`
and `dy j`. The sum `omegaFlat` has coefficient matrix one; sums weighted
by arbitrary real coefficients give all diagonal real `(1,1)`-forms.

Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics*,
Chapter 1, local unitary-coordinate formula for the Kähler form;
`CalabiYau.Geometry.Complex.Forms.OneOne`, coefficient and positivity
conventions; the upstream normalized alternating wedge in
`CalabiYau.Geometry.Manifold.Tensor.Alternating.Wedge`.
-/

@[expose] public section

open Matrix
open scoped ComplexOrder MatrixOrder

namespace ContinuousAlternatingMap

abbrev V (n : ℕ) := EuclideanSpace ℂ (Fin n)
abbrev Form (n k : ℕ) := V n [⋀^Fin k]→L[ℝ] ℝ

/-- The real part of complex coordinate `j`, as a real continuous covector. -/
noncomputable def dx {n : ℕ} (j : Fin n) : V n →L[ℝ] ℝ :=
  Complex.reCLM.comp ((EuclideanSpace.proj j).restrictScalars ℝ)

/-- The imaginary part of complex coordinate `j`, as a real continuous covector. -/
noncomputable def dy {n : ℕ} (j : Fin n) : V n →L[ℝ] ℝ :=
  Complex.imCLM.comp ((EuclideanSpace.proj j).restrictScalars ℝ)

/-- `i dzⱼ ∧ dbar zⱼ = 2 dxⱼ ∧ dyⱼ`, with the one-forms embedded by
`ofSubsingleton`. -/
noncomputable def eta {n : ℕ} (j : Fin n) : Form n 2 :=
  (2 : ℝ) • ((ContinuousAlternatingMap.ofSubsingleton ℝ (V n) ℝ (0 : Fin 1) (dx j)) ∧[ℝ]
    (ContinuousAlternatingMap.ofSubsingleton ℝ (V n) ℝ (0 : Fin 1) (dy j)))

private theorem wedge_covectors {n : ℕ} (p q : V n →L[ℝ] ℝ) (u v : V n) :
    ((ContinuousAlternatingMap.ofSubsingleton ℝ (V n) ℝ (0 : Fin 1) p) ∧[ℝ]
      (ContinuousAlternatingMap.ofSubsingleton ℝ (V n) ℝ (0 : Fin 1) q)) ![u, v] =
      p u * q v - p v * q u := by
  rw [ContinuousAlternatingMap.wedge_product_eq_alternatization,
    MultilinearMap.alternatization_apply]
  simp only [Nat.factorial_one, mul_one, Nat.cast_one, inv_one, one_smul]
  have hperms : (Finset.univ : Finset (Equiv.Perm (Fin 2))) =
      {1, Equiv.swap (0 : Fin 2) 1} := by decide
  rw [hperms]
  simp only [Finset.sum_insert (by decide : (1 : Equiv.Perm (Fin 2)) ∉ ({Equiv.swap 0 1} : Finset _)),
    Finset.sum_singleton]
  simp only [Equiv.Perm.sign_one, one_smul, Equiv.Perm.sign_swap',
    show (0 : Fin 2) ≠ 1 by decide, ↓reduceIte]
  simp only [MultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.coe_coe]
  rw [ContinuousAlternatingMap.tensorProductMap_apply,
    ContinuousAlternatingMap.tensorProductMap_apply]
  simp [Equiv.swap_apply_def]
  ring

/-- The `j`th coordinate piece has the positive orientation and factor two. -/
theorem eta_apply {n : ℕ} (j : Fin n) (u v : V n) :
    eta j ![u,v] = 2 * ((u j).re * (v j).im - (v j).re * (u j).im) := by
  rw [eta, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    wedge_covectors]
  rfl

/-- Each real coordinate area piece is of type `(1,1)`. -/
theorem eta_isOneOne {n : ℕ} (j : Fin n) : (eta j).IsOneOne := by
  intro u v
  rw [eta_apply, eta_apply]
  simp
  ring

/-- `eta j` has precisely one diagonal Hermitian coefficient, equal to one. -/
theorem eta_coeffMatrix {n : ℕ} (j : Fin n) :
    (eta j).coeffMatrix = Matrix.diagonal (fun i : Fin n => if i = j then (1 : ℂ) else 0) := by
  ext a b
  by_cases hja : j = a <;> by_cases hjb : j = b
  · subst a
    subst b
    simp [ContinuousAlternatingMap.coeffMatrix, eta_apply]
  · subst a
    simp [ContinuousAlternatingMap.coeffMatrix, eta_apply, hjb]
  · subst b
    have haj : a ≠ j := Ne.symm hja
    simp [ContinuousAlternatingMap.coeffMatrix, eta_apply, hja, haj]
  · simp [ContinuousAlternatingMap.coeffMatrix, eta_apply, Matrix.diagonal_apply,
      hja, hjb, Ne.symm hja]

/-- The flat Kähler form `i ∑ⱼ dzⱼ ∧ dbar zⱼ = 2 ∑ⱼ dxⱼ ∧ dyⱼ`. -/
noncomputable def omegaFlat {n : ℕ} : Form n 2 := ∑ j : Fin n, eta j

/-- The flat form has type `(1,1)`, also when `n = 0`. -/
theorem omegaFlat_isOneOne {n : ℕ} : (omegaFlat (n := n)).IsOneOne := by
  intro u v
  change (∑ j : Fin n, eta j) ![Complex.I • u, Complex.I • v] =
    (∑ j : Fin n, eta j) ![u,v]
  simp only [ContinuousAlternatingMap.sum_apply]
  exact Finset.sum_congr rfl (fun j _ => eta_isOneOne j u v)

private theorem coeffMatrix_finset_sum {n : ℕ} (s : Finset (Fin n))
    (f : Fin n → Form n 2) :
    (s.sum f).coeffMatrix = s.sum (fun j => (f j).coeffMatrix) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ContinuousAlternatingMap.coeffMatrix_zero]
  | @insert j s hj ih =>
      simp only [Finset.sum_insert hj, ContinuousAlternatingMap.coeffMatrix_add, ih]

/-- The flat Kähler form has the identity Hermitian coefficient matrix. -/
theorem omegaFlat_coeffMatrix {n : ℕ} :
    (omegaFlat (n := n)).coeffMatrix = (1 : Matrix (Fin n) (Fin n) ℂ) := by
  classical
  rw [omegaFlat, coeffMatrix_finset_sum]
  ext a b
  simp [eta_coeffMatrix, Matrix.sum_apply, Matrix.diagonal_apply, Matrix.one_apply]

/-- A real `(1,1)`-form with identity coefficient matrix is the flat form. -/
theorem omegaFlat_eq_of_coeffMatrix_one {n : ℕ} (ω : Form n 2)
    (hω : ω.IsOneOne) (hωI : ω.coeffMatrix = 1) : ω = omegaFlat := by
  apply hω.ext omegaFlat_isOneOne
  rw [hωI, omegaFlat_coeffMatrix]

/-- The coordinate form with arbitrary real diagonal Hermitian coefficients. -/
noncomputable def diagonalForm {n : ℕ} (d : Fin n → ℝ) : Form n 2 :=
  ∑ j : Fin n, d j • eta j

/-- Real diagonal coordinate forms have type `(1,1)`. -/
theorem diagonalForm_isOneOne {n : ℕ} (d : Fin n → ℝ) :
    (diagonalForm d).IsOneOne := by
  intro u v
  change (∑ j : Fin n, d j • eta j) ![Complex.I • u, Complex.I • v] =
    (∑ j : Fin n, d j • eta j) ![u,v]
  simp only [ContinuousAlternatingMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  simp [eta_isOneOne j u v]

/-- Weighted coordinate pieces realize precisely the diagonal coefficient matrix. -/
theorem diagonalForm_coeffMatrix {n : ℕ} (d : Fin n → ℝ) :
    (diagonalForm d).coeffMatrix = Matrix.diagonal (fun i : Fin n => (d i : ℂ)) := by
  classical
  rw [diagonalForm, coeffMatrix_finset_sum]
  ext a b
  simp [ContinuousAlternatingMap.coeffMatrix_smul, eta_coeffMatrix,
    Matrix.sum_apply, Matrix.diagonal_apply, Matrix.smul_apply]

/-- Every real `(1,1)`-form with diagonal coefficients is its coordinate expansion. -/
theorem diagonalForm_eq_of_coeffMatrix_diagonal {n : ℕ}
    (α : Form n 2) (hα : α.IsOneOne) (d : Fin n → ℝ)
    (hαD : α.coeffMatrix = Matrix.diagonal (fun i : Fin n => (d i : ℂ))) :
    α = diagonalForm d := by
  apply hα.ext (diagonalForm_isOneOne d)
  rw [hαD, diagonalForm_coeffMatrix]

-- Dimension zero has an empty coordinate sum and a 0×0 identity matrix.
private example : (omegaFlat (n := 0)).coeffMatrix = 1 := omegaFlat_coeffMatrix

-- On the flat complex line, the coefficient-one form evaluates to two, not one.
private example :
    (omegaFlat (n := 1)) ![EuclideanSpace.single 0 1,
      Complex.I • EuclideanSpace.single 0 1] = 2 := by
  simp [omegaFlat, eta_apply]

-- Two complex coordinates give the sum of two positively oriented real area blocks.
private example : omegaFlat (n := 2) = eta 0 + eta 1 := by
  simp [omegaFlat, Fin.sum_univ_two]

-- A complex-linear frame transforms coefficients by A transpose times g times conjugate A.
private example {n : ℕ} (A : V n →L[ℂ] V n) :
    (omegaFlat.compContinuousLinearMap (A.restrictScalars ℝ)).coeffMatrix =
      (EuclideanSpace.clmMatrix A)ᵀ *
        (1 : Matrix (Fin n) (Fin n) ℂ) * (EuclideanSpace.clmMatrix A).map star := by
  simpa [omegaFlat_coeffMatrix] using
    omegaFlat_isOneOne.coeffMatrix_compContinuousLinearMap A

end ContinuousAlternatingMap
