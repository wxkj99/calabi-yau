module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceCurvatureDerivative

/-!
# Concrete contractions in the Calabi Bochner calculation

Székelyhidi, §3.3, proof of Lemma 3.9, printed pp. 44–45, (3.14) and the
following commutator/Bianchi calculation. This is the streamlined tensor proof
of the third-order estimate, not its Kähler–Einstein specialization (3.11).

All inverse entries are row-antiholomorphic/column-holomorphic. The complex
Laplacian is `g⁻¹ q p ∂p∂̄q`, not the real Laplacian (twice this operator).
These are definitions, not hypotheses asserting that a remainder is bounded.
-/

@[expose] public section

open scoped Manifold ContDiff BigOperators

namespace KahlerForm

/-- Antiholomorphic Wirtinger derivative, with its own factor `1/2`. -/
noncomputable def c3PartialBar {n : ℕ} (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n) : ℂ :=
  (fderiv ℝ f z (EuclideanSpace.single j 1) +
    Complex.I * fderiv ℝ f z (Complex.I • EuclideanSpace.single j 1)) / 2

/-- Hermitian pairing of tensors of type `(1,2)`, linear in the first factor. -/
noncomputable def c3Pair {n : ℕ}
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (T U : Fin n → Fin n → Fin n → ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
    g z i a * (g z)⁻¹ b j * (g z)⁻¹ c k * T i j k * star (U a b c)

/-- The two positive derivative contractions; the derivative slot of `D` is
holomorphic and that of `B` is antiholomorphic, hence the opposite inverse orders. -/
noncomputable def c3DerivativeSquares {n : ℕ}
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (D B : Fin n → Fin n → Fin n → Fin n → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) : ℝ :=
  (∑ p, ∑ q, (g z)⁻¹ q p * c3Pair g z (D p) (D q) +
    ∑ p, ∑ q, (g z)⁻¹ p q * c3Pair g z (B p) (B q)).re

/-- Holomorphic covariant derivative of a tensor with one upper and two lower
holomorphic indices. There is no antiholomorphic connection coefficient. -/
noncomputable def c3TensorCovariantZ {n : ℕ}
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (T : EuclideanSpace ℂ (Fin n) → Fin n → Fin n → Fin n → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (p i j k : Fin n) : ℂ :=
  c3PartialZ (fun w ↦ T w i j k) z p +
    ∑ r, c3ChristoffelInChart g z i p r * T z r j k -
    ∑ r, c3ChristoffelInChart g z r p j * T z i r k -
    ∑ r, c3ChristoffelInChart g z r p k * T z i j r

/-- Ricci components, contracting the curvature in the first two slots. -/
noncomputable def c3RicciInChart {n : ℕ}
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (j l : Fin n) : ℂ :=
  ∑ p, ∑ q, (g z)⁻¹ q p * chartCurvature g z p q j l

/-- Ricci with its antiholomorphic index raised. -/
noncomputable def c3RicciEndomorphism {n : ℕ}
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (i j : Fin n) : ℂ :=
  ∑ l, (g z)⁻¹ l i * c3RicciInChart g z j l

/-- The commutator acts negatively on the upper index and positively on the
lower indices, exactly as in the commutation line following (3.14). -/
noncomputable def c3RicciTensorAction {n : ℕ}
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (T : Fin n → Fin n → Fin n → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (i j k : Fin n) : ℂ :=
  -(∑ r, c3RicciEndomorphism g z i r * T r j k) +
    ∑ r, c3RicciEndomorphism g z r j * T i r k +
    ∑ r, c3RicciEndomorphism g z r k * T i j r

/-- Raised covariant derivative `∇k Ricⁱⱼ`; only the holomorphic lower index
receives a connection correction before raising with the parallel metric. -/
noncomputable def c3RaisedRicciDerivative {n : ℕ}
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (i j k : Fin n) : ℂ :=
  ∑ l, (g z)⁻¹ l i *
    (c3PartialZ (fun w ↦ c3RicciInChart g w j l) z k -
      ∑ r, c3ChristoffelInChart g z r k j * c3RicciInChart g z r l)

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

/-- Perturbed metric expression, defined even away from the chart target. All
identities below are asserted only at the centre, which lies in that target. -/
noncomputable def c3PerturbedMetricInChart (ω₀ : KahlerForm n M)
    (φ : M → ℝ) (x : M) (z : EuclideanSpace ℂ (Fin n)) :
    Matrix (Fin n) (Fin n) ℂ :=
  ω₀.metricInChart x z +
    complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z

/-- Contracted ordered derivative `g^{p q̄} ∇p ∂̄q T`. -/
noncomputable def c3ConnectionTensorLaplacian (ω₀ : KahlerForm n M)
    (φ : M → ℝ) (x : M) (z : EuclideanSpace ℂ (Fin n)) (i j k : Fin n) : ℂ :=
  let g := c3PerturbedMetricInChart ω₀ φ x
  let T := c3ConnectionDifferenceInChart ω₀ φ x
  ∑ p, ∑ q, (g z)⁻¹ q p *
    c3TensorCovariantZ g (fun w a b c ↦ c3PartialBar (fun v ↦ T v a b c) w q) z p i j k

/-- Reference curvature with its last antiholomorphic index raised by `g₀`. -/
noncomputable def c3RaisedReferenceCurvature (ω₀ : KahlerForm n M)
    (x : M) (z : EuclideanSpace ℂ (Fin n)) (i j k q : Fin n) : ℂ :=
  ∑ l, (ω₀.metricInChart x z)⁻¹ l i *
    chartCurvature (ω₀.metricInChart x) z j q k l

/-- `gφ^{p q̄} ∇φp(g₀⁻¹ R₀)`: the fixed `∇₀R₀` term and the three
connection-difference corrections. The antiholomorphic index `q` has no correction. -/
noncomputable def c3ReferenceTensorDrift (ω₀ : KahlerForm n M)
    (φ : M → ℝ) (x : M) (z : EuclideanSpace ℂ (Fin n)) (i j k : Fin n) : ℂ :=
  let g := c3PerturbedMetricInChart ω₀ φ x
  let T := c3ConnectionDifferenceInChart ω₀ φ x
  let U := c3RaisedReferenceCurvature ω₀ x z
  ∑ p, ∑ q, (g z)⁻¹ q p *
    ((∑ l, (ω₀.metricInChart x z)⁻¹ l i *
      c3ReferenceCurvatureCovariantDerivativeInChart ω₀ x z p j q k l) +
    (∑ r, T z i p r * U r j k q) -
    (∑ r, T z r p j * U i r k q) -
    (∑ r, T z r p k * U i j r q))

/-- Scalar terms in the Bochner formula, evaluated in the centre chart. -/
noncomputable def c3BochnerConnectionTerm (ω₀ : KahlerForm n M) (φ : M → ℝ) (x : M) : ℝ :=
  let z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x
  (c3Pair (c3PerturbedMetricInChart ω₀ φ x) z
    (c3ConnectionTensorLaplacian ω₀ φ x z) (c3ConnectionDifferenceInChart ω₀ φ x z)).re

noncomputable def c3BochnerRicciActionTerm (ω₀ : KahlerForm n M) (φ : M → ℝ) (x : M) : ℝ :=
  let z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x
  let g := c3PerturbedMetricInChart ω₀ φ x
  let T := c3ConnectionDifferenceInChart ω₀ φ x z
  (c3Pair g z (c3RicciTensorAction g T z) T).re

noncomputable def c3BochnerRicciDerivativeTerm (ω₀ : KahlerForm n M) (φ : M → ℝ) (x : M) : ℝ :=
  let z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x
  let g := c3PerturbedMetricInChart ω₀ φ x
  (c3Pair g z (c3RaisedRicciDerivative g z) (c3ConnectionDifferenceInChart ω₀ φ x z)).re

noncomputable def c3BochnerReferenceTerm (ω₀ : KahlerForm n M) (φ : M → ℝ) (x : M) : ℝ :=
  let z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x
  (c3Pair (c3PerturbedMetricInChart ω₀ φ x) z
    (c3ReferenceTensorDrift ω₀ φ x z) (c3ConnectionDifferenceInChart ω₀ φ x z)).re

noncomputable def c3BochnerDerivativeSquares (ω₀ : KahlerForm n M) (φ : M → ℝ) (x : M) : ℝ :=
  let z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x
  let g := c3PerturbedMetricInChart ω₀ φ x
  let T := c3ConnectionDifferenceInChart ω₀ φ x
  c3DerivativeSquares g (c3TensorCovariantZ g T z)
    (fun q i j k ↦ c3PartialBar (fun w ↦ T w i j k) z q) z

end KahlerForm
