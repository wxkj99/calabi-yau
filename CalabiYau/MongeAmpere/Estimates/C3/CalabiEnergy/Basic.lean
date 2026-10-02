module

public import CalabiYau.MongeAmpere.Operator
public import CalabiYau.Mathlib.Geometry.Manifold.Holder

/-!
# Definitions for the Calabi third-order energy

In holomorphic coordinates, the difference of the two Kähler connections has components
`Tⁱⱼₖ = Γ(gφ)ⁱⱼₖ - Γ(g₀)ⁱⱼₖ`. Contract its squared norm with the perturbed metric.
See Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §3.3, (3.13), p. 45.
The smoothness, chart invariance and nonnegativity properties are developed in separate modules.
-/

@[expose] public section

open scoped BigOperators Manifold ContDiff NNReal
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

/-- Holomorphic coordinate derivative, `∂/∂z_j = (∂/∂x_j - i∂/∂y_j)/2`. -/
noncomputable def wirtingerDerivInChart (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n) : ℂ :=
  (fderiv ℝ f z (EuclideanSpace.single j 1) -
    Complex.I * fderiv ℝ f z (Complex.I • EuclideanSpace.single j 1)) / 2

/-- Holomorphic Christoffel coefficients, determined by
`∑ᵢ Γⁱⱼₖ gᵢₗ̄ = ∂ⱼ gₖₗ̄`. The inverse entry is `(g⁻¹)ₗᵢ`, not `(g⁻¹)ᵢₗ`. -/
noncomputable def christoffelInChart
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (i j k : Fin n) : ℂ :=
  ∑ l, (g z)⁻¹ l i * wirtingerDerivInChart (fun w ↦ g w k l) z j

/-- Components of the difference between the perturbed and reference Kähler connections. -/
noncomputable def connectionDifferenceInChart (ω₀ : KahlerForm n M)
    (φ : M → ℝ) (x₀ : M) (z : EuclideanSpace ℂ (Fin n))
    (i j k : Fin n) : ℂ :=
  let ψ := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm
  let g₀ : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w ↦ ω₀.metricInChart x₀ w
  let gφ : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w ↦ g₀ w + complexHessian (φ ∘ ψ) w
  christoffelInChart gφ z i j k - christoffelInChart g₀ z i j k

/-- The squared norm of the connection-difference tensor in a holomorphic chart.
For `Tⁱⱼₖ`, the Hermitian contractions are `gᵢₐ̄ (g⁻¹)ᵦⱼ (g⁻¹)ᶜₖ Tⁱⱼₖ · conj(Tᵃᵦᶜ)`;
the dual contractions reverse the matrix entry indices. -/
noncomputable def calabiEnergyInChart (ω₀ : KahlerForm n M) (φ : M → ℝ)
    (x₀ : M) (z : EuclideanSpace ℂ (Fin n)) : ℝ := by
  let ψ := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm
  let g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ := fun w ↦
    ω₀.metricInChart x₀ w + complexHessian (φ ∘ ψ) w
  let T : Fin n → Fin n → Fin n → ℂ := fun i j k ↦
    connectionDifferenceInChart ω₀ φ x₀ z i j k
  exact RCLike.re <| ∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
    g z i a * (g z)⁻¹ b j * (g z)⁻¹ c k * T i j k * star (T a b c)

/-- Globally defined squared norm of the connection-difference tensor. -/
noncomputable def calabiEnergy (ω₀ : KahlerForm n M) (φ : M → ℝ) : M → ℝ :=
  fun x ↦ calabiEnergyInChart ω₀ φ x
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x)

end KahlerForm
