module

public import CalabiYau.MongeAmpere.Estimates.C3.CalabiEnergy

/-!
# Ordered matrix jets for the relative trace

The normal-coordinate and fixed-chart Hessian calculations share the same
Wirtinger and matrix-entry conventions. Place these definitions below both
the inverse differentiation and matrix-product differentiation children so
they can be proved independently. Both Wirtinger operators carry `1/2`.

Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §3.3,
Lemma 3.10, pp. 45–46.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ}

/-- Antiholomorphic Wirtinger derivative `(Dₓ + iDᵧ)/2`. -/
noncomputable def c3RefinedTracePartialBar (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n) : ℂ :=
  (fderiv ℝ f z (EuclideanSpace.single j 1) +
    Complex.I * fderiv ℝ f z (Complex.I • EuclideanSpace.single j 1)) / 2

/-- Entrywise holomorphic derivative of a matrix-valued coordinate field. -/
noncomputable def c3RefinedTraceMatrixPartialZ
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (p : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j ↦ c3PartialZ (fun w ↦ g w i j) z p

/-- Entrywise antiholomorphic derivative of a matrix-valued coordinate field. -/
noncomputable def c3RefinedTraceMatrixPartialBar
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (q : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j ↦ c3RefinedTracePartialBar (fun w ↦ g w i j) z q

/-- Entrywise mixed derivative `∂ₚ∂̄q g` of a matrix-valued coordinate field. -/
noncomputable def c3RefinedTraceMatrixMixedPartial
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (p q : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  c3RefinedTraceMatrixPartialZ (fun w ↦ c3RefinedTraceMatrixPartialBar g w q) z p

/-- Complex trace of `g⁻¹h` prior to taking its real part. -/
noncomputable def c3RefinedTraceRelativeMatrixTrace
    (g h : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) : ℂ :=
  ((g z)⁻¹ * h z).trace

end KahlerForm
