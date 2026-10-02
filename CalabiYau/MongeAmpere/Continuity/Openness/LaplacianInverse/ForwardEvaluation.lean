module

public import CalabiYau.MongeAmpere.Continuity.Openness.LaplacianInverse.ForwardEvaluation.SmoothCoreExtension
public import CalabiYau.MongeAmpere.Continuity.Openness.LaplacianInverse.ForwardEvaluation.LaplacianFormula

/-!
# Completed forward evaluation

Compose the completed extension of the bounded smooth-core forward map with the
completed Laplacian formula. The result follows by composing these maps and identities.

The flat complex one-dimensional check is `Δω cos (2πx) = -π² cos (2πx)` under
`Δω=(1/4)ΔR`. The composed identity must preserve both the sign and the factor `1/4`.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology
open Set MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]

omit [ConnectedSpace M] in
/-- The bounded smooth-core forward operator extends to the completions with its pointwise
Laplacian evaluation identity. The order-two jet-limit compatibility is included, rather than being an
implicit consequence of C² regularity alone. -/
theorem exists_completed_forward_laplacian [Nonempty M]
    (ω₁ : KahlerForm n M) (α : ℝ≥0)
    [P : ContinuityHolderPair ω₁ α]
    (hForward : HasBoundedForwardLaplacian ω₁ P.finiteChartCover α)
    (hvol : 0 < ω₁.volume.real Set.univ) :
    ∃ A : P.C2 →L[ℝ] P.C0,
      ∀ u, P.evalC0 (A u) = ω₁.laplacian (P.evalC2 u) := by
  obtain ⟨A, hCore⟩ := exists_smoothCore_laplacian_extension ω₁ α hForward
  exact ⟨A, completed_forward_laplacian_formula ω₁ α A hCore hvol⟩

end KahlerForm
