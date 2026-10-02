module

public import CalabiYau.Geometry.Kahler.Sobolev

/-!
# Poincaré inequality in complex dimension zero

A compact connected zero-dimensional manifold is a singleton. On a singleton, each integral is
its integrand multiplied by the (finite) mass of the point. If that mass is zero, both sides of the
Poincaré inequality vanish; if it is nonzero, the mean-zero condition forces the function to be
zero. Thus no separate assumption that the manifold is nonempty or that its volume is positive is
needed (in Mathlib, `ConnectedSpace` itself entails nonemptiness).
-/

@[expose] public section

open scoped Manifold ContDiff
open MeasureTheory

namespace KahlerForm

/-- On a compact connected Kähler manifold of complex dimension zero, the Poincaré inequality
holds with the positive constant `1`. -/
theorem exists_poincareInequality_dimension_zero
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin 0)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 0)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M]
    [CompactSpace M] [ConnectedSpace M] (ω₀ : KahlerForm 0 M) :
    ∃ C : ℝ, 0 < C ∧ ω₀.PoincareInequality C := by
  classical
  let : DiscreteTopology (EuclideanSpace ℂ (Fin 0)) := inferInstance
  let : DiscreteTopology M :=
    ChartedSpace.discreteTopology (EuclideanSpace ℂ (Fin 0)) M
  have hsub : Subsingleton M := by
    refine ⟨fun x y => ?_⟩
    have hconn := (connectedSpace_iff_clopen.mp (inferInstance : ConnectedSpace M)).2
    have hcl : IsClopen ({x} : Set M) := isClopen_discrete {x}
    rcases hconn {x} hcl with hempty | huniv
    · have hx : x ∈ ({x} : Set M) := by simp
      rw [hempty] at hx
      simp at hx
    · have hy : y ∈ ({x} : Set M) := by rw [huniv]; simp
      exact hy.symm
  let : Subsingleton M := hsub
  let : Nonempty M := (connectedSpace_iff_clopen.mp (inferInstance : ConnectedSpace M)).1
  let : Unique M :=
    ⟨⟨Classical.choice ‹Nonempty M›⟩, fun a => Subsingleton.elim _ _⟩
  refine ⟨1, by norm_num, ?_⟩
  intro f hf hmean
  have hmean' : ω₀.volume.real Set.univ * f default = 0 := by
    simpa [integral_unique] using hmean
  have hsquare : (∫ x, f x ^ 2 ∂ω₀.volume) =
      ω₀.volume.real Set.univ * f default ^ 2 := by
    simp [integral_unique]
  have hgrad : 0 ≤ ∫ x, ω₀.gradNormSq f x ∂ω₀.volume :=
    integral_nonneg fun x => ω₀.gradNormSq_nonneg f x
  rcases mul_eq_zero.mp hmean' with hmass | hvalue
  · rw [hsquare, hmass]
    simpa using hgrad
  · rw [hsquare, hvalue]
    simpa using hgrad

end KahlerForm
