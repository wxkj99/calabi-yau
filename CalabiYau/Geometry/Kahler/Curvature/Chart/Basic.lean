module

public import CalabiYau.Geometry.Kahler.Basic
public import CalabiYau.Geometry.Kahler.Laplacian.Cofactor

/-!
# Coordinate antiholomorphic derivative and curvature

The definitions retain their original qualified names and mathematical bodies.
The two `expose` attributes permit the extracted calculus proofs to unfold them.
Székelyhidi, §3.3, proof of Lemma 3.9, PDF p.48 (book p.45).
-/

public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder

namespace KahlerForm

variable {n : ℕ}

/-- The antiholomorphic complex coordinate derivative on a complex-valued function, with
normalization `∂̄ⱼ = (Dₓⱼ + i Dᵧⱼ) / 2`. -/
@[expose] noncomputable def chartPartialBarComplex (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n) : ℂ :=
  (fderiv ℝ f z (EuclideanSpace.single j 1) +
    Complex.I * fderiv ℝ f z (Complex.I • EuclideanSpace.single j 1)) / 2

/-- The Kähler curvature components in a holomorphic coordinate chart, with convention
`R_{p q̄ j k̄} = -∂ₚ∂̄q g_{j k̄} + g^{a b̄}(∂ₚ g_{j b̄})(∂̄q g_{a k̄})`.
The matrix inverse uses entry `[b,a]` because `g` has holomorphic indices in rows and
antiholomorphic indices in columns. This convention has curvature `-∂∂̄g` in holomorphic
normal coordinates. -/
@[expose] noncomputable def chartCurvature
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (p q j k : Fin n) : ℂ :=
  -chartPartialZComplex (fun w => chartPartialBarComplex (fun v => g v j k) w q) z p +
    ∑ a, ∑ b, (g z)⁻¹ b a *
      chartPartialZComplex (fun w => g w j b) z p *
      chartPartialBarComplex (fun w => g w a k) z q

end KahlerForm
