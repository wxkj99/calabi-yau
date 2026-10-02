module

public import CalabiYau.MongeAmpere.Estimates.C3.TraceLaplacian.Refined.PositiveEnergyComparison

/-!
# Diagonal eigenvalue bounds from two relative traces

When the reference metric is the identity and the perturbed metric is
`diag(lam)`, the forward and reverse relative traces are `∑ lamᵢ` and
`∑ lamᵢ⁻¹`. Each term is nonnegative, so uniform upper bounds on both traces
give the explicit lower and upper eigenvalue bounds `B⁻¹ ≤ lamᵢ ≤ B` used
in the positive energy and curvature comparisons. In dimension zero the
indexwise conclusion is empty; the stated positive bound still makes sense.

Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §3.2,
Lemma 3.8, p. 43, and §3.3, Lemma 3.10, pp. 45–46.
-/

@[expose] public section

open scoped BigOperators ComplexOrder MatrixOrder

namespace KahlerForm

variable {n : ℕ}

/-- Two-sided relative-trace control is a pointwise eigenvalue comparison
in a reference-normal diagonal frame. No determinant equation is needed at
this last finite-dimensional step. -/
theorem c3RefinedTrace_diagonal_eigenvalue_bounds_of_trace_bounds
    (lam : Fin n → ℝ) {B : ℝ} (hB : 0 < B)
    (hpos : ∀ i, 0 < lam i)
    (hforward : (∑ i : Fin n, lam i) ≤ B)
    (hreverse : (∑ i : Fin n, (lam i)⁻¹) ≤ B) :
    ∀ i, B⁻¹ ≤ lam i ∧ lam i ≤ B := by
  intro i
  have hle : lam i ≤ B := by
    have hi : lam i ≤ ∑ j : Fin n, lam j :=
      Finset.single_le_sum (fun j _ ↦ (hpos j).le) (Finset.mem_univ i)
    exact hi.trans hforward
  have hleInv : (lam i)⁻¹ ≤ B := by
    have hi : (lam i)⁻¹ ≤ ∑ j : Fin n, (lam j)⁻¹ :=
      Finset.single_le_sum (fun j _ ↦ inv_nonneg.mpr (hpos j).le) (Finset.mem_univ i)
    exact hi.trans hreverse
  have hlow : B⁻¹ ≤ lam i := by
    simpa using (inv_le_inv₀ hB (inv_pos.mpr (hpos i))).mpr hleInv
  exact ⟨hlow, hle⟩

/-- In normal coordinates the two ordered matrix traces are exactly the
sums in `c3RefinedTrace_diagonal_eigenvalue_bounds_of_trace_bounds`. The inverse has the
same diagonal order because the metric entries are positive real scalars. -/
theorem c3RefinedTrace_relativeMatrixTrace_diagonal
    (g h : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (lam : Fin n → ℝ)
    (hg : g z = 1)
    (hh : h z = Matrix.diagonal (fun i ↦ (lam i : ℂ)))
    (hlam : ∀ i, 0 < lam i) :
    RCLike.re (((g z)⁻¹ * h z).trace) = ∑ i : Fin n, lam i ∧
      RCLike.re (((h z)⁻¹ * g z).trace) = ∑ i : Fin n, (lam i)⁻¹ := by
  constructor
  · simp [hg, hh, Matrix.trace_diagonal]
  · have hinv : (Matrix.diagonal (fun i : Fin n ↦ (lam i : ℂ)))⁻¹ =
        Matrix.diagonal (fun i : Fin n ↦ (lam i : ℂ)⁻¹) := by
      apply Matrix.inv_eq_left_inv
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact inv_mul_cancel₀ (by exact_mod_cast (ne_of_gt (hlam i)))
    simp only [hg, hh, Matrix.mul_one, hinv, Matrix.trace_diagonal]
    change (∑ i : Fin n, (lam i : ℂ)⁻¹).re = _
    rw [Complex.re_sum]
    simp [← Complex.ofReal_inv]

/-- The ordered forward and reverse matrix traces imply the two-sided
eigenvalue bound once the intrinsic relative traces are expressed in a chart. -/
theorem c3RefinedTrace_diagonal_eigenvalue_bounds_of_matrix_traces
    (g h : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (lam : Fin n → ℝ)
    {B : ℝ} (hB : 0 < B)
    (hg : g z = 1)
    (hh : h z = Matrix.diagonal (fun i ↦ (lam i : ℂ)))
    (hlam : ∀ i, 0 < lam i)
    (hforward : RCLike.re (((g z)⁻¹ * h z).trace) ≤ B)
    (hreverse : RCLike.re (((h z)⁻¹ * g z).trace) ≤ B) :
    ∀ i, B⁻¹ ≤ lam i ∧ lam i ≤ B := by
  obtain ⟨htrace, htraceRev⟩ := c3RefinedTrace_relativeMatrixTrace_diagonal g h z lam hg hh hlam
  exact c3RefinedTrace_diagonal_eigenvalue_bounds_of_trace_bounds lam hB hlam
    (htrace ▸ hforward) (htraceRev ▸ hreverse)

end KahlerForm
