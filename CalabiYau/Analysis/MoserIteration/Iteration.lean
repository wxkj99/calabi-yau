module

public import CalabiYau.Mathlib.Analysis.SpecialFunctions.Pow.GeometricIteration
public import CalabiYau.Mathlib.MeasureTheory.Function.LpSpace.EssSupLimit

public section

open Filter
open scoped NNReal ENNReal

namespace MeasureTheory

/-- A one-step multiplicative recurrence for `Lᵖ` seminorms, together with a uniform
bound on the recurrence products, bounds the essential supremum by the initial seminorm
scaled by that product bound. -/
theorem eLpNormEssSup_le_of_eLpNorm_recurrence
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    {p w : ℕ → ℝ≥0∞} {C : ℝ≥0∞}
    (hf : AEStronglyMeasurable f μ)
    (hp0 : ∀ k, p k ≠ 0)
    (hpTop : ∀ k, p k ≠ ∞)
    (hp_tendsto : Tendsto (fun k => (p k).toReal) atTop atTop)
    (hstep : ∀ k, eLpNorm f (p (k + 1)) μ ≤ w k * eLpNorm f (p k) μ)
    (hprod : ∀ N, (∏ k ∈ Finset.range N, w k) ≤ C) :
    eLpNormEssSup f μ ≤ C * eLpNorm f (p 0) μ := by
  apply eLpNormEssSup_le_of_eLpNorm_le_of_tendsto hf hp0 hpTop hp_tendsto
  intro k
  exact MoserIteration.sequence_le_of_uniform_prod hstep hprod k

end MeasureTheory
