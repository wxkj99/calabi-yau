module

public import CalabiYau.MongeAmpere.Continuity.Basic
public import CalabiYau.Geometry.Kahler.Sobolev
public import CalabiYau.Geometry.Kahler.Poisson
public import CalabiYau.Geometry.Complex.Schauder
import CalabiYau.MongeAmpere.Continuity.Openness
import CalabiYau.MongeAmpere.Continuity.Closedness

/-!
# Existence of solutions of the complex Monge–Ampère equation

**Theorem (Yau).** Let `(M, ω₀)` be a compact connected Kähler manifold and `F` a smooth function
with `∫ e^F ω₀ⁿ = ∫ ω₀ⁿ`. Then there is a smooth `φ` with `ω₀ + i∂∂̄φ > 0` and
`(ω₀ + i∂∂̄φ)ⁿ = e^F ω₀ⁿ`.

The result is proved **conditionally** on explicit global analytic hypotheses:
the Sobolev and Poincaré inequalities for `ω₀`, the interior Schauder estimate, and solvability
of the Poisson equation for Kähler forms on `M`.

## Proof

The continuity set `ω₀.continuitySet F ⊆ [0, 1]` contains `0` (`zero_mem_continuitySet`), is open
in `[0, 1]` (`continuitySet_mem_nhdsWithin`) and closed (`isClosed_continuitySet`), so it contains
`1` (`one_mem_continuitySet_of_isClosed`); conclude by
`solvesMongeAmpere_of_one_mem_continuitySet`. (If `M` is empty there is nothing to prove.)
-/

@[expose] public section

open scoped Manifold ContDiff

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- **Yau's theorem, existence**, conditional on the global analytic inputs. -/
theorem mongeAmpereSolvable (hSch : InteriorSchauderEstimate n)
    (hPoisson : ∀ ω₁ : KahlerForm n M, ω₁.PoissonSolvable) (ω₀ : KahlerForm n M)
    {κ C_S C_P : ℝ} (hκ : 1 < κ) (hS : ω₀.SobolevInequality κ C_S)
    (hP : ω₀.PoincareInequality C_P) : ω₀.MongeAmpereSolvable := by
  classical
  change ∀ F : M → ℝ, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F →
    ∫ x, Real.exp (F x) ∂ω₀.volume = ω₀.volume.real Set.univ → ∃ φ, ω₀.SolvesMongeAmpere F φ
  intro F hF hMass
  by_cases hM : Nonempty M
  · have hclosed : IsClosed (ω₀.continuitySet F) :=
      isClosed_continuitySet hSch ω₀ hκ hS hP hF
    exact solvesMongeAmpere_of_one_mem_continuitySet hMass
      (one_mem_continuitySet_of_isClosed
        (fun t ht => continuitySet_mem_nhdsWithin hSch hPoisson ω₀ hF ht) hclosed)
  · let : IsEmpty M := not_nonempty_iff.mp hM
    refine ⟨0, ?_⟩
    constructor
    · exact ω₀.isPotential_zero
    · intro x
      exact isEmptyElim x

end KahlerForm
