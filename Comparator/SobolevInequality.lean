module

public import CalabiYau.Geometry.Kahler.Sobolev
import CalabiYau.Geometry.Kahler.Sobolev.Existence

/-!
# Compact Kähler Sobolev input

This Comparator theorem packages the compact Sobolev inequality required by the analytic
estimates. The asserted inequality is the one defined on `KahlerForm` in
`CalabiYau.Geometry.Kahler.Sobolev`, with its volume and gradient conventions unchanged.
The compactness assumptions are those needed for a compact complex base; connectedness is not
required. Compactness yields the Sobolev inequality used in the analytic estimates.
-/

@[expose] public section

open scoped Manifold ContDiff

namespace CalabiYau

/-- Every compact Hausdorff complex manifold equipped with a Kähler form admits an inhomogeneous
Sobolev inequality with exponent strictly greater than one. -/
theorem sobolevInequality_of_compact
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M]
    (ω₀ : KahlerForm n M) :
    ∃ κ C_S : ℝ, 1 < κ ∧ ω₀.SobolevInequality κ C_S := by
  let : SigmaCompactSpace M := CompactSpace.sigmaCompact
  obtain ⟨κ, C_S, hκ, _, hSob⟩ := KahlerForm.exists_sobolevInequality ω₀
  exact ⟨κ, C_S, hκ, hSob⟩

end CalabiYau
