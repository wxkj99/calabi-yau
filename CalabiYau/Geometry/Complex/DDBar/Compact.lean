module

public import CalabiYau.Geometry.Complex.DDBar.RealOneOne

/-!
# The compact Kähler `∂∂̄` lemma

A compact complex manifold equipped with an explicit Kähler form satisfies the real `(1,1)`
`∂∂̄` property.
-/

@[expose] public section

open scoped Manifold ContDiff

namespace CalabiYau

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- A compact complex manifold equipped with a Kähler form satisfies the real `(1,1)`
`∂∂̄` lemma. -/
theorem satisfiesDDBarLemma_of_compact [T2Space M] [CompactSpace M]
    (ω₀ : KahlerForm n M) :
    SatisfiesDDBarLemma n M := by
  exact KahlerForm.satisfiesDDBarLemma_of_compact ω₀

end CalabiYau
