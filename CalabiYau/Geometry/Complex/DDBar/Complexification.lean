module

public import CalabiYau.Geometry.Complex.Forms.Basic
public import Mathlib.Analysis.Complex.Basic

/-!
# Complex-valued forms from real forms

A real differential form can be viewed as a complex-valued form by composing its values
with the canonical inclusion `ℝ → ℂ`. This file records the pointwise algebraic bridge used
when comparing real `(1,1)`-forms with complex type components.
-/

@[expose] public section

open scoped Manifold ContDiff

namespace ContinuousAlternatingMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}

end ContinuousAlternatingMap

/-- A complex-valued differential form field, represented by its real and imaginary real form
fields. This representation keeps the existing real chart calculus as the single source of truth. -/
abbrev ComplexFormField (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Type*) (k : ℕ) := FormField E M k × FormField E M k

namespace ComplexFormField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {k : ℕ}

/-- Smoothness of a complex form means smoothness of both real components. -/
def IsSmooth (α : ComplexFormField E M k) : Prop :=
  α.1.IsSmooth ∧ α.2.IsSmooth

/-- The exterior derivative of a complex form is defined componentwise. -/
noncomputable def extDeriv (α : ComplexFormField E M k) : ComplexFormField E M (k + 1) :=
  (α.1.extDeriv, α.2.extDeriv)

/-- A complex form is exact when its real and imaginary parts arise as one complex form field's
exterior derivative. -/
def IsExact (α : ComplexFormField E M (k + 1)) : Prop :=
  ∃ β : ComplexFormField E M k, β.IsSmooth ∧ β.extDeriv = α

/-- A complex-valued real two-form is of type `(1,1)` when each real component is invariant
under the complex structure `J`. -/
def IsOneOne (J : E →L[ℝ] E) (α : ComplexFormField E M 2) : Prop :=
  ∀ x u v, (α.1 x) ![J u, J v] = (α.1 x) ![u, v] ∧
    (α.2 x) ![J u, J v] = (α.2 x) ![u, v]

end ComplexFormField
