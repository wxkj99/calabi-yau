module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Integration of uniformly convergent densities

On a finite measure space, uniform convergence controls the difference of integrals by the total
measure times the uniform error.  The explicit integrability hypotheses allow the result to be used
for the smooth approximants and their finite-regularity limit without assuming that the volume is
nonzero.
-/

@[expose] public section

open MeasureTheory Filter

namespace KahlerForm

/-- Uniform convergence of integrable real-valued functions on a finite measure space implies
convergence of their integrals. -/
theorem integral_tendsto_of_uniform_convergence
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : ℕ → X → ℝ) (g : X → ℝ)
    (hf : ∀ j, Integrable (f j) μ) (hg : Integrable g μ)
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ j, N ≤ j → ∀ x,
      |f j x - g x| ≤ ε) :
    Tendsto (fun j => ∫ x, f j x ∂μ) atTop (nhds (∫ x, g x ∂μ)) := by
  apply Metric.tendsto_atTop.mpr
  intro δ hδ
  let C := μ.real Set.univ
  let ε := δ / (2 * (C + 1))
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hden : 0 < 2 * (C + 1) := by positivity
  have hε : 0 < ε := div_pos hδ hden
  have hprod : ε * C < δ := by
    calc
      ε * C ≤ ε * (C + 1) := mul_le_mul_of_nonneg_left (by linarith) hε.le
      _ = δ / 2 := by dsimp [ε]; field_simp
      _ < δ := by linarith
  obtain ⟨N, hN⟩ := hconv ε hε
  refine ⟨N, fun j hj => ?_⟩
  have hpoint := hN j hj
  have hbound : ∀ᵐ x ∂μ, ‖f j x - g x‖ ≤ ε :=
    Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hpoint x
  have hnorm := norm_integral_le_of_norm_le_const (f := fun x => f j x - g x) hbound
  rw [dist_eq_norm, ← integral_sub (hf j) hg]
  simpa [Real.norm_eq_abs, C] using lt_of_le_of_lt hnorm hprod

end KahlerForm
