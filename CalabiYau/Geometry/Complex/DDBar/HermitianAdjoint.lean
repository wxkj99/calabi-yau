module

public import CalabiYau.Geometry.Complex.DDBar.Complexification
public import CalabiYau.Geometry.Riemannian.Metric.PointwiseInner.Algebra

/-!
# Metric pairings on complex form fields

The project represents real form fields by alternating maps on the real model tangent spaces and
complex form fields by pairs of real and imaginary parts.  The pointwise real pairing below applies
the extracted metric contraction to those actual alternating forms.  Its Hermitian extension is
therefore tied to project form types and to the supplied Riemannian metric, rather than to an
unidentified coordinate coefficient space.

This is fiberwise algebra only.  No Hodge star, global codifferential, or integration-by-parts
identity is asserted here.  A Hodge bridge still needs an orientation/volume form and a star on
exterior powers satisfying `α ∧ ⋆β = ⟪α, β⟫_g vol_g`; it must check the complex-coordinate sign
normalization and the dimension-zero case before a global adjoint theorem is attempted.
-/

@[expose] public section

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

namespace FormField

/-- The real pointwise pairing on project `k`-form fields, induced by the Riemannian metric's
inverse Gram contraction on covariant tensors and divided by `k!` to give the standard exterior-power
normalization. -/
noncomputable def pointwiseRealInner
    (g : CalabiYau.SmoothRiemannianMetric 𝓘(ℝ, E) M) (k : ℕ) (x : M)
    (α β : FormField E M k) : ℝ :=
  CalabiYau.L2.covariantTensorInnerPointwise (I := 𝓘(ℝ, E)) (M := M) k g x
    (α x).toContinuousMultilinearMap (β x).toContinuousMultilinearMap /
      (Nat.factorial k : ℝ)

/-- For two-forms, the exterior pairing is half the ordered covariant-tensor contraction.  In
complex dimension one this is the normalization for `ω = i dz ∧ dbarz = 2 dx ∧ dy`: with the
associated metric `g(v,w) = ω(v,Jw)`, the form `ω` has squared norm one. -/
theorem pointwiseRealInner_degree_two
    (g : CalabiYau.SmoothRiemannianMetric 𝓘(ℝ, E) M) (x : M)
    (α β : FormField E M 2) :
    pointwiseRealInner g 2 x α β =
      CalabiYau.L2.covariantTensorInnerPointwise (I := 𝓘(ℝ, E)) (M := M) 2 g x
        (α x).toContinuousMultilinearMap (β x).toContinuousMultilinearMap / 2 := by
  simp [pointwiseRealInner]

/-- The metric-induced real pairing on form fields is symmetric at each point. -/
theorem pointwiseRealInner_symm
    (g : CalabiYau.SmoothRiemannianMetric 𝓘(ℝ, E) M) (k : ℕ) (x : M)
    (α β : FormField E M k) :
    pointwiseRealInner g k x α β = pointwiseRealInner g k x β α := by
  unfold pointwiseRealInner
  rw [CalabiYau.L2.tensorInnerPointwise_0s_symm (I := 𝓘(ℝ, E)) (M := M)
    g x k (α x).toContinuousMultilinearMap (β x).toContinuousMultilinearMap]

/-- The metric-induced real pairing of a form with itself is nonnegative at each point. -/
theorem pointwiseRealInner_self_nonneg
    (g : CalabiYau.SmoothRiemannianMetric 𝓘(ℝ, E) M) (k : ℕ) (x : M)
    (α : FormField E M k) :
    0 ≤ pointwiseRealInner g k x α α := by
  unfold pointwiseRealInner
  apply div_nonneg
  · exact CalabiYau.L2.tensorInnerPointwise_0s_nonneg (I := 𝓘(ℝ, E)) (M := M)
      g x k (α x).toContinuousMultilinearMap
  · positivity

end FormField

namespace ComplexFormField

/-- The Hermitian extension of the real metric pairing to the project's pair representation of
complex form fields. The convention matches Mathlib's `InnerProductSpace` convention: conjugate-
linear in the first argument and linear in the second. For `α = a + i b` and `β = c + i d`, this is
`(a,c) + (b,d) + i ((a,d) - (b,c))`. -/
noncomputable def pointwiseHermitianInner
    (g : CalabiYau.SmoothRiemannianMetric 𝓘(ℝ, E) M) (k : ℕ) (x : M)
    (α β : ComplexFormField E M k) : ℂ :=
  ((FormField.pointwiseRealInner g k x α.1 β.1 +
      FormField.pointwiseRealInner g k x α.2 β.2 : ℝ) : ℂ) +
    Complex.I *
      ((FormField.pointwiseRealInner g k x α.1 β.2 -
        FormField.pointwiseRealInner g k x α.2 β.1 : ℝ) : ℂ)

/-- The pointwise complex pairing is Hermitian: conjugate symmetry holds when the arguments are
swapped. -/
theorem pointwiseHermitianInner_star_symm
    (g : CalabiYau.SmoothRiemannianMetric 𝓘(ℝ, E) M) (k : ℕ) (x : M)
    (α β : ComplexFormField E M k) :
    pointwiseHermitianInner g k x α β = star (pointwiseHermitianInner g k x β α) := by
  simp [pointwiseHermitianInner, FormField.pointwiseRealInner_symm]; ring

/-- The real part of the Hermitian self-pairing is nonnegative. -/
theorem re_pointwiseHermitianInner_self_nonneg
    (g : CalabiYau.SmoothRiemannianMetric 𝓘(ℝ, E) M) (k : ℕ) (x : M)
    (α : ComplexFormField E M k) :
    0 ≤ (pointwiseHermitianInner g k x α α).re := by
  simp only [pointwiseHermitianInner, Complex.add_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  have h₁ := FormField.pointwiseRealInner_self_nonneg g k x α.1
  have h₂ := FormField.pointwiseRealInner_self_nonneg g k x α.2
  nlinarith [h₁, h₂]

end ComplexFormField
