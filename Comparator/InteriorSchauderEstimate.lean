module

public import CalabiYau.Geometry.Complex.Schauder.InteriorProvider

/-!
# Interior Schauder estimate provider

This Comparator leaf exposes the dimension-uniform interior Schauder estimate
needed by the Monge–Ampère continuity argument. The imported predicate includes
both regularity and the quantitative Hölder estimate, with its ellipticity,
exponent, and domain assumptions explicit.

The imported all-dimensions theorem supplies this estimate in every complex
Euclidean dimension, with the regularity and quantitative Hölder bound under
the stated ellipticity, exponent, and domain assumptions.
-/

@[expose] public section

namespace CalabiYau

/-- The interior Schauder regularity and estimate hold in every complex
Euclidean dimension. -/
theorem interiorSchauderEstimate_all : ∀ n : ℕ,
    InteriorSchauderEstimate n := by
  exact _root_.interiorSchauderEstimate_all

end CalabiYau
