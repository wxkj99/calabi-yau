module

public import CalabiYau.MongeAmpere.Estimates.C3.CalabiEnergy.Basic
public import CalabiYau.MongeAmpere.Estimates.C3.CalabiEnergy.Smoothness
public import CalabiYau.MongeAmpere.Estimates.C3.CalabiEnergy.ChartInvariance
public import CalabiYau.MongeAmpere.Estimates.C3.CalabiEnergy.Nonnegativity

/-!
# The Calabi third-order energy

The definitions live in a low-level module so smoothness, chart invariance and positivity can be
proved independently. The public endpoint below packages all three properties needed by the C³
estimate; its statement is the energy estimate.
See Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §3.3, (3.13), p. 45.
-/

@[expose] public section

open scoped Manifold ContDiff

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

omit [T2Space M] [CompactSpace M] in
/-- The local expression is intrinsic, smooth, and nonnegative for a positive solution.
Székelyhidi, §3.3, (3.13), p. 45. -/
theorem calabiEnergy_chartFormula_is_intrinsic (ω₀ : KahlerForm n M)
    (φ G : M → ℝ)
    (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ φ)
    (hsol : ω₀.SolvesMongeAmpere G φ) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (calabiEnergy ω₀ φ) ∧
      (∀ x₀ z, z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target →
        calabiEnergy ω₀ φ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm z) =
          calabiEnergyInChart ω₀ φ x₀ z) ∧
      (∀ x, 0 ≤ calabiEnergy ω₀ φ x) := by
  have hpot : ω₀.IsPotential φ := ⟨hφ, hsol.1.2⟩
  exact ⟨calabiEnergy_contMDiff ω₀ hpot,
    calabiEnergy_chartFormula ω₀ hpot,
    calabiEnergy_nonneg ω₀ hpot⟩

end KahlerForm
