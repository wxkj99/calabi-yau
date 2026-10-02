module

public import CalabiYau.MongeAmpere.Estimates.C3.CalabiEnergy

/-!
# Smoothness and positivity of the perturbed relative trace

The identity `tr_ω₀(ω₀ + i∂∂̄φ) = n + Δ_ω₀ φ` reduces smoothness to the
smoothness of the complex Laplacian. Positivity follows directly from the
positivity of the reference and perturbed Kähler forms. The dimension-zero
case gives trace zero without introducing a positivity hypothesis on `n`.

Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §3.2,
Lemma 3.8 and §3.3, Lemma 3.10, pp. 41–46.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- The trace input for the C³ maximum principle is smooth and nonnegative
for each positive Monge–Ampère solution, without assuming `n > 0`. -/
theorem c3RefinedTrace_relTrace_perturb_smooth_nonneg (ω₀ : KahlerForm n M)
    (G φ : M → ℝ) (hsol : ω₀.SolvesMongeAmpere G φ) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (fun x ↦ relTrace (ω₀ x) (ω₀ x + mddbar n φ x)) ∧
      ∀ x, 0 ≤ relTrace (ω₀ x) (ω₀ x + mddbar n φ x) := by
  have htrace : (fun x ↦ relTrace (ω₀ x) (ω₀ x + mddbar n φ x)) =
      fun x ↦ (n : ℝ) + ω₀.laplacian φ x := by
    funext x
    rw [ContinuousAlternatingMap.relTrace_add,
      ContinuousAlternatingMap.relTrace_self (ω₀.isPositive x)]
    rfl
  constructor
  · rw [htrace]
    exact contMDiff_const.add (ω₀.contMDiff_laplacian hsol.1.1)
  · intro x
    exact ContinuousAlternatingMap.relTrace_nonneg
      (ω₀.isPositive x) (hsol.1.2 x).isNonneg

end KahlerForm
