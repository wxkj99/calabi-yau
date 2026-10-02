module

public import CalabiYau.Geometry.Complex.DDBar.Complexification
public import CalabiYau.Geometry.Manifold.DifferentialForm.Model
public import CalabiYau.Geometry.Manifold.Tensor.Product.Defs
public import Mathlib.Analysis.Normed.Group.Defs

/-!
# Exterior products of complex form fields

The pair representation `ComplexFormField = (real part, imaginary part)` carries the usual
complex-bilinear wedge, formed from the ordinary real wedge by the multiplication rule
`(a + i b) ∧ (c + i d) = (a ∧ c - b ∧ d) + i (a ∧ d + b ∧ c)`.
The underlying `ContinuousAlternatingMap.wedgeProduct` uses the normalized shuffle product,
not an extra factorial. Smoothness follows from chartwise bilinearity and naturality under
linear changes of coordinates. There is no exterior-derivative Leibniz rule
in the local `FormField` or extracted `DifferentialForm` API yet.

Source: Wells, *Differential Analysis on Complex Manifolds*, Chapter IV §5 (complex form
algebra and exterior differential); Morita, *Geometry of Differential Forms*, Chapter 5
(exterior products in the Hodge/Stokes calculus).
-/

@[expose] public section

open scoped Manifold ContDiff

namespace FormField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {k l : ℕ} in
/-- Pointwise real wedge, with the standard shuffle normalization on alternating maps. -/
noncomputable def wedge (α : FormField E M k) (β : FormField E M l) :
    FormField E M (k + l) := fun x =>
  ContinuousAlternatingMap.wedgeProduct (α x) (β x) (ContinuousLinearMap.mul ℝ ℝ)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*}
    {k l : ℕ} in
theorem wedge_apply (α : FormField E M k) (β : FormField E M l) (x : M) :
    wedge α β x = ContinuousAlternatingMap.wedgeProduct (α x) (β x)
      (ContinuousLinearMap.mul ℝ ℝ) := rfl

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {k l : ℕ}
theorem wedge_comp (α : E [⋀^Fin k]→L[ℝ] ℝ) (β : E [⋀^Fin l]→L[ℝ] ℝ)
    (L : E →L[ℝ] E) :
    (ContinuousAlternatingMap.wedgeProduct α β (ContinuousLinearMap.mul ℝ ℝ)).compContinuousLinearMap L =
      ContinuousAlternatingMap.wedgeProduct (α.compContinuousLinearMap L)
        (β.compContinuousLinearMap L) (ContinuousLinearMap.mul ℝ ℝ) := by
  exact (CalabiYau.DifferentialForm.wedge_product_compContinuousLinearMap
    (g := α) (h := β) (A := L))

theorem chartRep_wedge (α : FormField E M k) (β : FormField E M l) (x : M) :
    (wedge α β).chartRep x = fun z =>
      ContinuousAlternatingMap.wedgeProduct (α.chartRep x z) (β.chartRep x z)
        (ContinuousLinearMap.mul ℝ ℝ) := by
  funext z
  simp only [FormField.chartRep, wedge]
  exact wedge_comp _ _ _

theorem IsSmooth.wedge {α : FormField E M k} {β : FormField E M l}
    (hα : α.IsSmooth) (hβ : β.IsSmooth) : (wedge α β).IsSmooth := by
  intro x
  rw [chartRep_wedge]
  exact (ContinuousAlternatingMap.isBoundedBilinearMap_wedgeProduct
    (m := k) (n := l) (M := E) (ContinuousLinearMap.mul ℝ ℝ)).contDiff.comp₂_contDiffOn
      (hα x) (hβ x)

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*}
    {k l : ℕ}
theorem wedge_add (α : FormField E M k) (β γ : FormField E M l) :
    wedge α (β + γ) = wedge α β + wedge α γ := by
  funext x
  exact ContinuousAlternatingMap.wedge_add (α x) (β x) (γ x) (ContinuousLinearMap.mul ℝ ℝ)

theorem wedge_smul (a : ℝ) (α : FormField E M k) (β : FormField E M l) :
    wedge α (a • β) = a • wedge α β := by
  funext x
  exact ContinuousAlternatingMap.wedge_smul a (α x) (β x) (ContinuousLinearMap.mul ℝ ℝ)

theorem smul_wedge (a : ℝ) (α : FormField E M k) (β : FormField E M l) :
    wedge (a • α) β = a • wedge α β := by
  funext x
  exact ContinuousAlternatingMap.smul_wedge a (α x) (β x) (ContinuousLinearMap.mul ℝ ℝ)

end

end FormField

namespace ComplexFormField

/- Scalar multiplication on the pair model, displaying the actual complex action rather than
relying on an implicit module instance. Multiplication by `i` sends `(a,b)` to `(-b,a)`. -/

end ComplexFormField

-- In degree zero the real wedge is ordinary scalar multiplication, without a factorial.
example (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α β : E [⋀^Fin 0]→L[ℝ] ℝ) :
    (ContinuousAlternatingMap.wedgeProduct α β (ContinuousLinearMap.mul ℝ ℝ)) ![] =
      α ![] * β ![] := by
  rw [ContinuousAlternatingMap.wedge_product_eq_alternatization]
  simp [MultilinearMap.alternatization_apply]
  rw [ContinuousAlternatingMap.tensorProductMap_apply]
  simp
