module

public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.SourceInterpolation.Basic
public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.SourceInterpolation.BudgetChoice
public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.SourceInterpolation.BudgetScale
public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.SourceInterpolation.BudgetData

/-!
# Certified assembly of the separated q-scaled interpolation budget

Source: Constantin, Schauder Estimates, intermediate interpolation p. 8 and
segment gradient estimate p. 9. Each scalar closure is a separate small leaf.
-/

@[expose] public section

open scoped NNReal ContDiff Topology

namespace CalabiYau.Schauder

/-- Choose a uniform data coefficient before the patch radius and equation data. -/
theorem realBallSource_separated_budget
    {α A : ℝ≥0} (hα₁ : α < 1) (k : ℕ)
    (hkα : 3 + (α : ℝ) ≤ (k : ℝ) * (1 - (α : ℝ))) :
    ∀ θ : ℝ≥0, 0 < θ → ∃ C : ℝ≥0,
      ∀ δ : ℝ, 0 < δ → ∃ eps₁ eps₂ : ℝ≥0,
        0 < eps₁ ∧ 0 < eps₂ ∧ eps₁ ≤ Real.toNNReal δ / 2 ∧ eps₂ ≤ 1 ∧
        ∀ K₀ K₁ H : ℝ≥0,
          let G := realBallLowerGradientBound K₀ H eps₁
          let V := realBallLowerValueHolderBound α K₀ G eps₂
          let W := realBallLowerGradientHolderBound α H G eps₂
          A * realBallSourceScale δ ^ (3 + (α : ℝ)) * (K₁ + K₀ + G + V + W) ≤
            C * realBallSourceScale δ ^ (2 * k + 8) * (K₁ + K₀) + θ * H := by
  intro θ hθ
  obtain ⟨a, b, ha, haHalf, hb, hbOne, hchoice⟩ :=
    realBallSource_budget_choice (A := A) hα₁ θ hθ
  refine ⟨realBallSourceBudgetDataConst α A a b, ?_⟩
  intro δ hδ
  obtain ⟨heps₁, heps₂, hbuffer, heps₂One, hgauge⟩ :=
    realBallSource_budget_scales hα₁ k hkα ha haHalf hb hbOne hchoice hδ
  refine ⟨a * realBallSourceScale δ ^ (-((k : ℝ) + 4)),
    b * realBallSourceScale δ ^ (-(k : ℝ)), heps₁, heps₂, hbuffer, heps₂One, ?_⟩
  have hq : 1 ≤ realBallSourceScale δ := by
    dsimp [realBallSourceScale]
    exact le_add_of_nonneg_right (by positivity)
  exact realBallSource_budget_data hα₁ k hkα hq ha hb hgauge

end CalabiYau.Schauder
