module

public import Mathlib.Data.ENNReal.BigOperators

public section

open scoped ENNReal

namespace MoserIteration

/-- Iterating a one-step multiplicative bound gives the corresponding finite product bound.

This statement is formulated in `ℝ≥0∞`, so it also covers zero and infinite values without
additional hypotheses. -/
theorem sequence_le_prod_mul_initial {u w : ℕ → ℝ≥0∞}
    (hstep : ∀ k, u (k + 1) ≤ w k * u k) (N : ℕ) :
    u N ≤ (∏ k ∈ Finset.range N, w k) * u 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
      calc
        u (N + 1) ≤ w N * u N := hstep N
        _ ≤ w N * ((∏ k ∈ Finset.range N, w k) * u 0) :=
          mul_le_mul_right ih (w N)
        _ = (∏ k ∈ Finset.range (N + 1), w k) * u 0 := by
          rw [Finset.prod_range_succ]
          ac_rfl

/-- A uniform upper bound for the finite products gives the corresponding bound for every term. -/
theorem sequence_le_of_uniform_prod {u w : ℕ → ℝ≥0∞} {B : ℝ≥0∞}
    (hstep : ∀ k, u (k + 1) ≤ w k * u k)
    (hprod : ∀ N, (∏ k ∈ Finset.range N, w k) ≤ B) (N : ℕ) :
    u N ≤ B * u 0 := by
  calc
    u N ≤ (∏ k ∈ Finset.range N, w k) * u 0 :=
      sequence_le_prod_mul_initial hstep N
    _ ≤ B * u 0 := mul_le_mul_left (hprod N) (u 0)

end MoserIteration
