module

public import CalabiYau.MongeAmpere.Continuity.Openness.SmoothBootstrap.DifferenceQuotientBounds

/-!
# Assemble the local difference-quotient Schauder data

The exact translated equation and the uniform coefficient/forcing estimates are independent
analytic inputs.  This module glues them into the package consumed by the first Schauder gain.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- Exact `C²` nonzero-step equations together with uniform ellipticity and Hölder bounds. -/
def HasDifferenceQuotientSchauderData (ω₀ : KahlerForm n M) (G φ : M → ℝ)
    (α : ℝ≥0) : Prop :=
  HasExactDifferenceQuotientData ω₀ G φ ∧
    HasUniformDifferenceQuotientBounds ω₀ G φ α

/-- The chart equation, finite `C^{2,α}` gauge, and smooth data produce the complete Schauder
input by gluing the exact quotient equation to its uniform bounds. -/
theorem solvesMongeAmpereC2_hasDifferenceQuotientSchauderData
    (ω₀ : KahlerForm n M) (α : ℝ≥0) (hα₀ : 0 < α) (hα₁ : α < 1)
    {G φ : M → ℝ}
    (hG : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G)
    (hφ : ω₀.SolvesMongeAmpereC2 G φ)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (hφGauge : HasFiniteChartHolderGauge cover 2 α φ)
    (hEquation : HasChartLogDetEquation ω₀ G φ) :
    HasDifferenceQuotientSchauderData ω₀ G φ α := by
  exact
    ⟨solvesMongeAmpereC2_hasExactDifferenceQuotientData ω₀ hφ hEquation,
      solvesMongeAmpereC2_hasUniformDifferenceQuotientBounds
        ω₀ α hα₀ hα₁ hG hφ cover hφGauge hEquation⟩

end KahlerForm
