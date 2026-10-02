module

public import CalabiYau.MongeAmpere.Estimates.C3.CalabiEnergy

/-!
# Positive trace-Hessian term controls the Calabi energy

At a reference-normal coordinate center, the positive third-derivative term
in the Laplacian of `tr(g₀⁻¹gφ)` is the squared norm of the connection
 difference. The norm comparison below isolates the finite-dimensional
coercivity needed when the two Hermitian metrics are only uniformly equivalent.
It is separate from the trace-Hessian identity and from curvature or potential
error bounds.

Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §3.3,
Lemma 3.10, pp. 45–46; the positivity of the third-derivative term in
Aubin–Yau's trace computation.
-/

@[expose] public section

open scoped BigOperators Manifold ContDiff NNReal ComplexOrder MatrixOrder
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ}

/-- In reference-normal coordinates with a diagonal perturbed metric
`h_{j k̄} = λⱼ δⱼₖ`, the positive term of the trace Hessian is
`∑ₚⱼₖ |∂ₚh_{j k̄}|²/(λⱼλₖ)`, whereas the Calabi energy has one additional
inverse factor `λₚ⁻¹`. This is the exact diagonal comparison needed before
adding the bounded curvature and `∂∂̄G` errors. -/
theorem c3RefinedTrace_diagonalEnergy_lower_of_metric_lower
    (lam : Fin n → ℝ) (A : Fin n → Fin n → Fin n → ℂ)
    {c : ℝ} (hc : 0 < c) (hlam : ∀ p, c ≤ lam p) :
    c * (∑ p : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      ‖A p j k‖ ^ (2 : ℕ) / (lam p * lam j * lam k)) ≤
      ∑ p : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        ‖A p j k‖ ^ (2 : ℕ) / (lam j * lam k) := by
  have hpos (i : Fin n) : 0 < lam i := hc.trans_le (hlam i)
  simp_rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  apply Finset.sum_le_sum
  intro j hj
  apply Finset.sum_le_sum
  intro k hk
  have hden : 0 < lam j * lam k := mul_pos (hpos j) (hpos k)
  have hval : 0 ≤ ‖A p j k‖ ^ (2 : ℕ) / (lam j * lam k) := by positivity
  have hquot : c / lam p ≤ 1 := (div_le_iff₀ (hpos p)).mpr (by simpa using hlam p)
  calc
    c * (‖A p j k‖ ^ (2 : ℕ) / (lam p * lam j * lam k)) =
        (c / lam p) * (‖A p j k‖ ^ (2 : ℕ) / (lam j * lam k)) := by
      field_simp
    _ ≤ 1 * (‖A p j k‖ ^ (2 : ℕ) / (lam j * lam k)) :=
      mul_le_mul_of_nonneg_right hquot hval
    _ = _ := by ring

end KahlerForm
