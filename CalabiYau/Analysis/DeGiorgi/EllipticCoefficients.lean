-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/External/DeGiorgi/EllipticCoefficients.lean
-- Locally modified.
-- Modified 2026-04-28: updated internal import paths for project namespace
module
public import CalabiYau.Analysis.DeGiorgi.Foundations

@[expose] public section

/-!
# Chapter 03: Coefficients

This chapter defines the elliptic coefficient structures used throughout the
development.

It uses a unified coefficient structure with measurable coefficients, lower
ellipticity on `a` and `a⁻¹`, and derived mixed and upper bounds recorded as
theorems rather than primitive fields.
-/

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace DeGiorgi

/-- The ambient Euclidean space used by the elliptic regularity development. -/
abbrev AmbientSpace (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Matrix action on the ambient Euclidean space. -/
def matMulE {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (ξ : AmbientSpace d) : AmbientSpace d :=
  WithLp.toLp 2 (Matrix.mulVec M ξ.ofLp)

@[simp] theorem matMulE_ofLp {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (ξ : AmbientSpace d) :
    (matMulE M ξ).ofLp = Matrix.mulVec M ξ.ofLp :=
  rfl

@[simp] theorem matMulE_apply {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (ξ : AmbientSpace d) (i : Fin d) :
    matMulE M ξ i = Matrix.mulVec M ξ.ofLp i :=
  rfl

/-- Unified nonsymmetric elliptic coefficient field for the elliptic regularity
development.

It is designed to serve both:

- the variational / weak-solution branch, which needs measurability;
- the De Giorgi / Moser branch, which uses coercivity of `a⁻¹` to derive mixed
  and upper bounds.

The upper bounds are intentionally not primitive fields in this structure. -/
structure EllipticCoeff (d : ℕ) [NeZero d] (Ω : Set (AmbientSpace d)) where
  /-- Matrix-valued coefficient field. -/
  a : AmbientSpace d → Matrix (Fin d) (Fin d) ℝ
  /-- Lower ellipticity constant. -/
  lam : ℝ
  /-- Upper ellipticity constant. -/
  Λ : ℝ
  /-- Componentwise measurability of the coefficient field. -/
  measurable_comp : ∀ i j, Measurable (fun x => a x i j)
  /-- Positivity of the lower ellipticity constant. -/
  hlam : 0 < lam
  /-- Comparison of lower and upper ellipticity scales. -/
  hΛ : lam ≤ Λ
  /-- Coercivity on `a`, stated almost everywhere on `Ω`. -/
  coercive : ∀ᵐ x ∂(MeasureTheory.volume.restrict Ω), ∀ ξ : AmbientSpace d,
    lam * ‖ξ‖ ^ 2 ≤ ⟪ξ, matMulE (a x) ξ⟫_ℝ
  /-- Coercivity on `a⁻¹`, stated almost everywhere on `Ω`. -/
  coercive_inv : ∀ᵐ x ∂(MeasureTheory.volume.restrict Ω), ∀ ξ : AmbientSpace d,
    Λ⁻¹ * ‖ξ‖ ^ 2 ≤ ⟪ξ, matMulE ((a x)⁻¹) ξ⟫_ℝ

/-- Optional normalized view of the unified coefficient structure. -/
abbrev NormalizedEllipticCoeff (d : ℕ) [NeZero d] (Ω : Set (AmbientSpace d)) :=
  {A : EllipticCoeff d Ω // A.lam = 1}

namespace EllipticCoeff

variable {d : ℕ} [NeZero d] {Ω : Set (AmbientSpace d)} (A : EllipticCoeff d Ω)

end EllipticCoeff

namespace NormalizedEllipticCoeff

variable {d : ℕ} [NeZero d] {Ω : Set (AmbientSpace d)}
  (A : NormalizedEllipticCoeff d Ω)

end NormalizedEllipticCoeff

end DeGiorgi
