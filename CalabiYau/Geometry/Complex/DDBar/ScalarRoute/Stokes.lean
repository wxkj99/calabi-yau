module

public import CalabiYau.Geometry.Complex.DDBar.ScalarRoute.Stokes.Even
public import CalabiYau.Geometry.Complex.DDBar.ScalarRoute.Stokes.Odd

/-!
# The graded Leibniz rule for the project's exterior product

The real rule follows by the even/odd split in Bott–Tu; its extension to the
complex pair model is componentwise and uses the *same* ordered normalized
shuffle wedge throughout. No boundary, compactness, or orientation hypothesis
enters this differential identity.

Source: Bott–Tu, *Differential Forms in Algebraic Topology*, Chapter I, §1,
Proposition 1.3 (antiderivation of the de Rham complex).
-/

@[expose] public section

open scoped Manifold ContDiff

namespace FormField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {k l : ℕ}

/-- The normalized-shuffle exterior product obeys the graded differential rule. -/
theorem extDeriv_wedge {α : FormField E M k} {β : FormField E M l}
    (hα : α.IsSmooth) (hβ : β.IsSmooth) :
    (wedge α β).extDeriv =
      derivWedgeLeft α β + (-1 : ℝ) ^ k • derivWedgeRight α β := by
  rcases Nat.even_or_odd k with hk | hk
  · simpa only [hk.neg_one_pow, one_smul] using extDeriv_wedge_even hα hβ hk
  · simpa only [hk.neg_one_pow, neg_one_smul, sub_eq_add_neg] using
      extDeriv_wedge_odd hα hβ hk

end FormField

namespace ComplexFormField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {k l : ℕ}

end ComplexFormField
