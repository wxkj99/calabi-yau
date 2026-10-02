module

public import CalabiYau.MongeAmpere.Continuity.Openness.LaplacianInverse.GlobalSchauder.LocalEstimate

/-!
# Finite-gauge mean-zero control target

The finite-gauge premise is essential: taking `ENNReal.toReal` at `⊤` would otherwise conceal
failure of a norm estimate. This target is shared by the normalization lemma and the parent theorem.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology
open MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- On smooth mean-zero functions, the supremum norm is controlled by the order-zero gauge of the
Laplacian. The finite-gauge premise prevents a `toReal` estimate from becoming vacuous at `⊤`. -/
def HasMeanZeroLaplacianC0Control (ω₁ : KahlerForm n M)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M) (α : ℝ≥0) : Prop :=
  ∃ C : ℝ≥0, ∀ f : M → ℝ,
    ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f →
    (∫ x, f x ∂ω₁.volume = 0) →
    finiteChartHolderGauge cover 0 α (ω₁.laplacian f) < ⊤ →
    ∀ x, |f x| ≤ (C : ℝ) * (finiteChartHolderGauge cover 0 α (ω₁.laplacian f)).toReal

end KahlerForm
