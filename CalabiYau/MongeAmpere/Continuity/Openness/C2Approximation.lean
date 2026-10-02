module

public import CalabiYau.MongeAmpere.Continuity.Openness.HolderSpaces
public import CalabiYau.MongeAmpere.Continuity.Openness.C2Approximation.HolderConvergence
public import CalabiYau.MongeAmpere.Continuity.Openness.C2Approximation.Positivity

/-!
# Smooth approximation of a positive C² potential

The C² mass identity is obtained by smoothing the potential in a fixed finite chart cover.  The
data below makes that approximation and its convergence in chartwise C² seminorms explicit, so the
finite-regularity passage requires a separate argument.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [T2Space M] [CompactSpace M]

/-- A smooth, positive sequence converging to a positive `C²` potential in the fixed finite-chart
`C²` topology.  The convergence bounds all coordinate derivatives through order two uniformly
over every compact chart piece. -/
structure SmoothC2PotentialApproximationData (ω₀ : KahlerForm n M) (φ : M → ℝ)
    (hφ : ω₀.IsC2Potential φ) where
  cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M
  approx : ℕ → M → ℝ
  smooth : ∀ j, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (approx j)
  potential : ∀ j, ω₀.IsPotential (approx j)
  convergesInC2 : ∀ ε : ℝ≥0, 0 < ε →
    ∃ N, ∀ j, N ≤ j → ∀ i,
      HolderBoundOn 2 0 ε (cover.piece i)
        ((approx j - φ) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
          (cover.base i)).symm)

/-- Smooth positive potentials approximate any positive `C²` potential in chartwise `C²`. -/
theorem exists_smoothC2Potential_approximation (ω₀ : KahlerForm n M) {φ : M → ℝ}
    (hφ : ω₀.IsC2Potential φ) :
    Nonempty (SmoothC2PotentialApproximationData ω₀ φ hφ) := by
  classical
  obtain ⟨A⟩ := exists_chartwiseC2Smoothing ω₀ hφ
  obtain ⟨Npos, hpos⟩ := A.eventually_isPotential ω₀ hφ
  refine ⟨{ cover := A.cover
            approx := fun j => A.approximation (Npos + j)
            smooth := fun j => A.smooth (Npos + j)
            potential := ?_
            convergesInC2 := ?_ }⟩
  · intro j
    exact hpos (Npos + j) (by omega)
  · intro ε hε
    obtain ⟨Nconv, hconv⟩ := A.eventually_holderBoundOn ε hε
    refine ⟨Nconv, ?_⟩
    intro j hj i
    apply hconv (Npos + j) ?_ i
    omega

end KahlerForm
