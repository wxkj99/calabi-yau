module

public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderEvaluation
public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderJets
import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderC2Regularity.CompletedChartJets.BoundaryJetIdentity
import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderC2Regularity.CompletedChartJets.CompletedJetHolderWith

/-!
# Top-jet Hölder bound on a fixed chart piece

The finite-chart gauge controls both the sup norms of all jets and the Hölder seminorm of the
order-two jet. This child retains the top-jet seminorm needed for fixed-cover `HolderBoundOn`
conclusions; the pointwise jet norm estimate alone would not provide it.
-/

@[expose] public section

noncomputable section

open scoped Manifold ContDiff NNReal Topology

namespace KahlerForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]

omit [FiniteDimensional ℝ E] in
/-- The order-two evaluation on each fixed chart piece satisfies the full `HolderBoundOn` gauge,
including the top-jet Hölder seminorm, with the supplied completion norm as bound. -/
theorem smoothChartHolderCompletedTopJetHolderBoundOn
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover 2 α)
    (u : LittleHolder cover 2 α N) (i) :
    HolderBoundOn 2 α ‖u‖₊ (cover.piece i)
      ((smoothChartHolderContinuousMapExtension cover 2 α N u : M → ℝ) ∘
        (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) := by
  rcases smoothChartHolderCompletedJetHolderWith cover α N u i with
    ⟨hjet, hholder⟩
  refine ⟨?_, ?_⟩
  · intro j hj z hz
    rw [smoothChartHolderCompletedBoundaryJetIdentity cover α N u j hj i z hz]
    exact hjet j hj ⟨z, hz⟩
  · intro z hz w hw
    rw [smoothChartHolderCompletedBoundaryJetIdentity cover α N u 2 le_rfl i z hz,
      smoothChartHolderCompletedBoundaryJetIdentity cover α N u 2 le_rfl i w hw]
    simpa using hholder ⟨z, hz⟩ ⟨w, hw⟩

end KahlerForm
