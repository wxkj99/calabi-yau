module

public import CalabiYau.Geometry.Complex.DDBar.Forms.Wedge

/-!
# Degree-aligned wedge products for the exterior-derivative rule

The project uses the *normalized shuffle* wedge of `Forms/Wedge`, not pointwise
multiplication or an unnormalized alternatization. The two terms of the graded
Leibniz rule have degrees `(k + 1) + l` and `k + (l + 1)`, respectively. These
are transported to the degree `(k + l) + 1` of the derivative of the product;
the transports only reassociate natural-number indices and introduce no sign.

Source: Bott–Tu, *Differential Forms in Algebraic Topology*, Chapter I, §1,
Proposition 1.3 (the exterior derivative is an antiderivation).
-/

@[expose] public section

open scoped Manifold ContDiff

namespace FormField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {k l : ℕ}

/-- `dα ∧ β`, reindexed to have the degree of `d(α ∧ β)`. -/
noncomputable def derivWedgeLeft (α : FormField E M k) (β : FormField E M l) :
    FormField E M ((k + l) + 1) :=
  cast (congrArg (FormField E M) (Nat.add_right_comm k 1 l)) (wedge α.extDeriv β)

/-- `α ∧ dβ`, reindexed to have the degree of `d(α ∧ β)`. -/
noncomputable def derivWedgeRight (α : FormField E M k) (β : FormField E M l) :
    FormField E M ((k + l) + 1) :=
  cast (congrArg (FormField E M) (Nat.add_assoc k l 1).symm) (wedge α β.extDeriv)

end FormField

namespace ComplexFormField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {k l : ℕ}

end ComplexFormField
