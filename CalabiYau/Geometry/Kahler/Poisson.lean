module

public import CalabiYau.Geometry.Kahler.Laplacian

/-!
# The Poisson equation on a compact Kähler manifold (hypothesis)

`KahlerForm.PoissonSolvable ω₀` states that `Δ_ω₀ u = f` has a smooth solution for every smooth
`f` of mean zero with respect to `ω₀ⁿ`. This is the surjectivity half of the invertibility of the
linearized Monge–Ampère operator used in the openness step of the continuity method; it follows
from Hodge theory / Fredholm theory for elliptic operators on compact manifolds together with
elliptic regularity.

It is **not proved here**: the openness step takes it as an explicit hypothesis (for all Kähler
forms, since it is applied to `ω₀ + i∂∂̄φₜ`), and track S (global Schauder theory, or the
`PoissonExistence` development of the extracted library) is expected to provide
`∀ ω₀ : KahlerForm n M, ω₀.PoissonSolvable` for compact connected `M`.

The necessity of the mean-zero condition and uniqueness up to constants follow from Green's
formula and are proved here.
-/

@[expose] public section

open scoped Manifold ContDiff
open MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [SigmaCompactSpace M] (ω₀ : KahlerForm n M)

/-- Solvability of the Poisson equation `Δ_ω₀ u = f` for smooth `f` of mean zero. -/
def PoissonSolvable : Prop :=
  ∀ f : M → ℝ, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f →
    ∫ x, f x ∂ω₀.volume = 0 →
      ∃ u : M → ℝ, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u ∧ ω₀.laplacian u = f

variable {ω₀} [CompactSpace M]

/-- The mean-zero condition is necessary. -/
theorem integral_eq_zero_of_laplacian_eq {u f : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u) (h : ω₀.laplacian u = f) :
    ∫ x, f x ∂ω₀.volume = 0 := by
  rw [← h]
  exact ω₀.integral_laplacian hu

omit [SigmaCompactSpace M] in
/-- Solutions of the Poisson equation are unique up to an additive constant. -/
theorem eq_add_const_of_laplacian_eq [ConnectedSpace M] {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ v)
    (h : ω₀.laplacian u = ω₀.laplacian v) : ∃ c : ℝ, ∀ x, v x = u x + c := by
  have hsub : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (v - u) := hv.sub hu
  have hsub_lap : ω₀.laplacian (v - u) = 0 := by
    rw [sub_eq_add_neg]
    change ω₀.laplacian (v + (fun x ↦ -u x)) = 0
    rw [ω₀.laplacian_add hv hu.neg]
    have hneg : (fun x ↦ -u x) = (-1 : ℝ) • u := by ext x; simp
    rw [hneg]
    rw [ω₀.laplacian_smul hu (-1)]
    rw [h]
    ext x
    simp
  obtain ⟨c, hc⟩ := ω₀.eq_const_of_laplacian_eq_zero hsub hsub_lap
  refine ⟨c, fun x ↦ ?_⟩
  have hx := hc x
  change v x - u x = c at hx
  linarith

end KahlerForm
