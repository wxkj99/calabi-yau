module

public import CalabiYau.Geometry.Kahler.Sobolev.PoincareExistence

/-!
# Poincaré inequality on compact connected Kähler manifolds

A compact connected Kähler manifold admits a Poincaré inequality with a positive constant.
-/

@[expose] public section

open scoped Manifold ContDiff

namespace CalabiYau

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M]
  [CompactSpace M] [ConnectedSpace M]

/-- Every compact connected Kähler manifold admits a Poincaré inequality with a positive
constant. -/
theorem poincareInequality_of_compact (ω₀ : KahlerForm n M) :
    ∃ C_P : ℝ, 0 < C_P ∧ ω₀.PoincareInequality C_P := by
  exact KahlerForm.exists_poincareInequality ω₀

end CalabiYau
