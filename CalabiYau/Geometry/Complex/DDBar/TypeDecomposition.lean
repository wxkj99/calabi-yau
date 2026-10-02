module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Complex.Basic

/-!
# Type decomposition of complex-valued covectors

On the real tangent space underlying `ℂⁿ`, multiplication by `Complex.I` is the complex
structure. A complex-valued real-linear covector splits into its `+i` and `-i` eigencovectors.
These are the `(1,0)` and `(0,1)` components in degree one.
-/

@[expose] public section

open Complex

/-- The real-linear complex structure on the Euclidean model of a complex tangent space. -/
noncomputable def complexTangentJ (n : ℕ) :
    EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) :=
  Complex.I • ContinuousLinearMap.id ℝ (EuclideanSpace ℂ (Fin n))

