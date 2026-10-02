module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.BochnerTensors
public import CalabiYau.Geometry.Kahler.Ricci
public import CalabiYau.Geometry.Kahler.Curvature.ReferenceBound

/-!
# Reference-frame jets in the differentiated Ricci estimate

Székelyhidi, §1.4, Lemma 1.22, pp. 12–13, and §3.3, proof of Lemma 3.9,
p. 45. These are concrete coefficient contractions, not analytic hypotheses.
The reference covariant derivative acts on the holomorphic slot of a (1,1)
covariant tensor. Changing to the perturbed connection subtracts one T*Q term.
-/

@[expose] public section

open scoped Manifold ContDiff BigOperators

namespace KahlerForm

noncomputable def c3TwoCovariantFrame {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℂ) (Q : Fin n → Fin n → ℂ)
    (j l : Fin n) : ℂ :=
  ∑ a, ∑ b, P a j * star (P b l) * Q a b

noncomputable def c3ThreeCovariantFrame {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℂ) (D : Fin n → Fin n → Fin n → ℂ)
    (k j l : Fin n) : ℂ :=
  ∑ a, ∑ b, ∑ c, P a k * P b j * star (P c l) * D a b c

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

/-- The reference derivative of a covariant tensor with one holomorphic and
one antiholomorphic slot. There is no holomorphic connection on the latter. -/
noncomputable def c3ReferenceCovariantTwoTensorZ (ω₀ : KahlerForm n M) (x : M)
    (Q : EuclideanSpace ℂ (Fin n) → Fin n → Fin n → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (k j l : Fin n) : ℂ :=
  c3PartialZ (fun w ↦ Q w j l) z k -
    ∑ r, c3ChristoffelInChart (ω₀.metricInChart x) z r k j * Q z r l

noncomputable def c3ForcingHessianInChart (G : M → ℝ) (x : M)
    (z : EuclideanSpace ℂ (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  complexHessian (G ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z

/-- Separate component bounds for the Hessian and its reference covariant
holomorphic derivative, both evaluated in the specified (possibly fixed) chart. -/
def c3ForcingFrameBound (ω₀ : KahlerForm n M) (G : M → ℝ) (x : M)
    (z : EuclideanSpace ℂ (Fin n)) (P : Matrix (Fin n) (Fin n) ℂ) (A : ℝ) : Prop :=
  (∀ j l, ‖c3TwoCovariantFrame P (c3ForcingHessianInChart G x z) j l‖ ≤ A) ∧
  (∀ k j l, ‖c3ThreeCovariantFrame P
    (c3ReferenceCovariantTwoTensorZ ω₀ x (c3ForcingHessianInChart G x) z) k j l‖ ≤ A)

omit [T2Space M] [CompactSpace M] in
theorem c3ForcingFrameBound_mono (ω₀ : KahlerForm n M) (G : M → ℝ) (x : M)
    (z : EuclideanSpace ℂ (Fin n)) (P : Matrix (Fin n) (Fin n) ℂ)
    {A B : ℝ} (h : c3ForcingFrameBound ω₀ G x z P A) (hAB : A ≤ B) :
    c3ForcingFrameBound ω₀ G x z P B :=
  ⟨fun j l ↦ (h.1 j l).trans hAB, fun k j l ↦ (h.2 k j l).trans hAB⟩

/-- Corresponding bounds for the fixed reference Ricci tensor and its derivative. -/
def c3ReferenceRicciFrameBound (ω₀ : KahlerForm n M) (x : M)
    (z : EuclideanSpace ℂ (Fin n)) (P : Matrix (Fin n) (Fin n) ℂ) (A : ℝ) : Prop :=
  (∀ j l, ‖c3TwoCovariantFrame P (c3RicciInChart (ω₀.metricInChart x) z) j l‖ ≤ A) ∧
  (∀ k j l, ‖c3ThreeCovariantFrame P
    (c3ReferenceCovariantTwoTensorZ ω₀ x (c3RicciInChart (ω₀.metricInChart x)) z)
      k j l‖ ≤ A)

/-- The explicit differentiated general-MA remainder: reference derivative of
`Ric0-Hess G`, minus the T correction, raised and paired using the perturbed metric. -/
noncomputable def c3RicciDerivativeError (ω₀ : KahlerForm n M)
    (G φ : M → ℝ) (x : M) : ℝ :=
  let z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x
  let g := c3PerturbedMetricInChart ω₀ φ x
  let T := c3ConnectionDifferenceInChart ω₀ φ x
  let R := c3RicciInChart (ω₀.metricInChart x)
  let H := c3ForcingHessianInChart G x
  let D : Fin n → Fin n → Fin n → ℂ := fun i j k ↦
    ∑ l, (g z)⁻¹ l i *
      (c3ReferenceCovariantTwoTensorZ ω₀ x R z k j l -
        c3ReferenceCovariantTwoTensorZ ω₀ x H z k j l -
        ∑ r, T z r k j * (R z r l - H z r l))
  (c3Pair g z D (T z)).re

end KahlerForm
