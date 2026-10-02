module

public import CalabiYau.MongeAmpere.Continuity.Openness.C2MassNormalization
public import CalabiYau.Geometry.Manifold.Holder.ChartNorm
public import CalabiYau.Analysis.Elliptic.Schauder
public import CalabiYau.MongeAmpere.Continuity.Openness.SmoothBootstrap.ChartLogDetEquation
public import CalabiYau.MongeAmpere.Continuity.Openness.SmoothBootstrap.DifferenceQuotientEquation
public import CalabiYau.MongeAmpere.Continuity.Openness.SmoothBootstrap.SchauderInduction

/-!
# Smooth regularity for finite-regularity path solutions

Once the implicit-function theorem produces a `C²` solution, the regularity half of the interior
Schauder estimate applies to the linearized complex Monge–Ampère operator.  Repeating the estimate
on relatively compact chart pieces upgrades the potential to `C^k` for every finite `k`, hence to
a smooth potential.  This is the regularity theorem for a priori `C²` solutions; it does not use
the higher estimates whose hypotheses already assume smoothness.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M] in
/-- A `C²` Monge–Ampère solution is smooth when the right-hand side is smooth and the interior
Schauder regularity estimate holds. -/
theorem solvesMongeAmpere_of_c2 (hSch : InteriorSchauderEstimate n)
    (ω₀ : KahlerForm n M) (α : ℝ≥0) (hα₀ : 0 < α) (hα₁ : α < 1)
    {G φ : M → ℝ}
    (hG : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G)
    (hφ : ω₀.SolvesMongeAmpereC2 G φ)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (hφGauge : HasFiniteChartHolderGauge cover 2 α φ) :
    ω₀.SolvesMongeAmpere G φ := by
  have hEquation := solvesMongeAmpereC2_hasChartLogDetEquation ω₀ G φ hφ
  have hDifferenceQuotients := solvesMongeAmpereC2_hasDifferenceQuotientSchauderData
    ω₀ α hα₀ hα₁ hG hφ cover hφGauge hEquation
  have hSmooth := solvesMongeAmpereC2_smooth_of_differenceQuotientSchauderData
    hSch ω₀ α hα₀ hα₁ hG hφ cover hφGauge hEquation hDifferenceQuotients
  exact ⟨⟨hSmooth, hφ.1.2⟩, hφ.2⟩

end KahlerForm
