module

public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Holder

/-!
# Hölder control of inverse matrix entries

For a matrix field whose entries are Hölder and whose inverse entries are uniformly bounded,
the inverse entries inherit a Hölder bound. The proof uses the resolvent identity and expands each
matrix product entry as a finite double sum.
-/

@[expose] public section

open scoped NNReal

namespace KahlerForm

/-- Matrix inversion preserves a quantitative entrywise Hölder bound when all inverse entries are
uniformly bounded. The constant records the `n²` summands and the two inverse factors. -/
theorem holderOnWith_matrix_inv_entry_of_norm_bound {E : Type*}
    [PseudoMetricSpace E] {n : ℕ} {α C B : ℝ≥0} {U : Set E}
    (A : E → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, HolderOnWith C α (fun z ↦ A z i j) U)
    (hUnit : ∀ z ∈ U, IsUnit (A z))
    (hInv : ∀ z ∈ U, ∀ i j, ‖(A z)⁻¹ i j‖ ≤ B) (i j : Fin n) :
    HolderOnWith ((n : ℝ≥0) ^ 2 * B ^ 2 * C) α
      (fun z ↦ (A z)⁻¹ i j) U := by
  intro x hx y hy
  have hiden : (A x)⁻¹ - (A y)⁻¹ = (A x)⁻¹ * (A y - A x) * (A y)⁻¹ := by
    have hxdet : IsUnit (Matrix.det (A x)) :=
      (Matrix.isUnit_iff_isUnit_det (A x)).mp (hUnit x hx)
    have hydet : IsUnit (Matrix.det (A y)) :=
      (Matrix.isUnit_iff_isUnit_det (A y)).mp (hUnit y hy)
    calc
      (A x)⁻¹ - (A y)⁻¹ = (A x)⁻¹ * 1 - 1 * (A y)⁻¹ := by simp
      _ = (A x)⁻¹ * (A y * (A y)⁻¹) -
          ((A x)⁻¹ * (A x)) * (A y)⁻¹ := by
        rw [Matrix.mul_nonsing_inv _ hydet, Matrix.nonsing_inv_mul _ hxdet]
      _ = (A x)⁻¹ * (A y - A x) * (A y)⁻¹ := by
        rw [Matrix.mul_sub, Matrix.sub_mul]
        simp only [Matrix.mul_assoc]
  have hentry (k l : Fin n) :
      ‖A y k l - A x k l‖ ≤ (C : ℝ) * dist x y ^ (α : ℝ) := by
    have h := (hA k l).edist_le hx hy
    rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) α.coe_nonneg,
      ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)] at h
    have h' : dist (A x k l) (A y k l) ≤
        (C : ℝ) * dist x y ^ (α : ℝ) :=
      (ENNReal.ofReal_le_ofReal_iff
        (p := dist (A x k l) (A y k l))
        (q := (C : ℝ) * dist x y ^ (α : ℝ)) (by positivity)).mp h
    rw [dist_eq_norm] at h'
    simpa [norm_sub_rev] using h'
  have hnorm : ‖((A x)⁻¹) i j - ((A y)⁻¹) i j‖ ≤
      ((n : ℝ) ^ 2) * (B : ℝ) ^ 2 * (C : ℝ) * dist x y ^ (α : ℝ) := by
    rw [show ((A x)⁻¹) i j - ((A y)⁻¹) i j =
        ∑ k : Fin n, ∑ l : Fin n,
          (A x)⁻¹ i k * (A y k l - A x k l) * (A y)⁻¹ l j by
      rw [← Matrix.sub_apply, hiden]
      simp only [Matrix.mul_apply, Matrix.sub_apply, Finset.sum_mul]
      rw [Finset.sum_comm]]
    calc
      ‖∑ k : Fin n, ∑ l : Fin n,
          (A x)⁻¹ i k * (A y k l - A x k l) * (A y)⁻¹ l j‖ ≤
          ∑ k : Fin n, ∑ l : Fin n,
            ‖(A x)⁻¹ i k * (A y k l - A x k l) * (A y)⁻¹ l j‖ := by
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk ↦ norm_sum_le _ _)
      _ ≤ ∑ k : Fin n, ∑ l : Fin n,
          (B : ℝ) * ((C : ℝ) * dist x y ^ (α : ℝ)) * (B : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        apply Finset.sum_le_sum
        intro l hl
        calc
          ‖(A x)⁻¹ i k * (A y k l - A x k l) * (A y)⁻¹ l j‖ ≤
              ‖(A x)⁻¹ i k‖ * ‖A y k l - A x k l‖ * ‖(A y)⁻¹ l j‖ := by
            exact (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
          _ ≤ (B : ℝ) * ((C : ℝ) * dist x y ^ (α : ℝ)) * (B : ℝ) := by
            gcongr
            · exact hInv x hx i k
            · exact hentry k l
            · exact hInv y hy l j
      _ = ((n : ℝ) ^ 2) * (B : ℝ) ^ 2 * (C : ℝ) *
          dist x y ^ (α : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
  change edist (((A x)⁻¹) i j) (((A y)⁻¹) i j) ≤
      (((n : ℝ≥0) ^ 2 * B ^ 2 * C : ℝ≥0) : ENNReal) * edist x y ^ (α : ℝ)
  rw [edist_dist]
  calc
    ENNReal.ofReal (dist (((A x)⁻¹) i j) (((A y)⁻¹) i j)) =
        ENNReal.ofReal ‖((A x)⁻¹) i j - ((A y)⁻¹) i j‖ := by rw [dist_eq_norm]
    _ ≤ ENNReal.ofReal (((n : ℝ) ^ 2) * (B : ℝ) ^ 2 * (C : ℝ) *
        dist x y ^ (α : ℝ)) := ENNReal.ofReal_le_ofReal hnorm
    _ = (((n : ℝ≥0) ^ 2 * B ^ 2 * C : ℝ≥0) : ENNReal) * edist x y ^ (α : ℝ) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      rw [← ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) α.coe_nonneg, ← edist_dist]
      rw [ENNReal.ofReal_eq_coe_nnreal (by positivity)]
      norm_cast

end KahlerForm

end
