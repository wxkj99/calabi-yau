module

public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderEvaluation
public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderC2Regularity.ChartJets

/-!
# C² regularity of the little-Hölder evaluation extension

The order-two little-Hölder completion is the closure of smooth functions in the finite-chart
`C^{2,α}` gauge. Its evaluation extension is therefore C²; this is the regularity statement needed
to place the completed carrier into the potential space used by the openness argument.
-/

@[expose] public section

noncomputable section

open scoped Manifold ContDiff NNReal Topology

namespace KahlerForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]

/-- The evaluated function represented by an order-two little-Hölder completion element. -/
noncomputable def littleHolderOrderTwoEvaluation
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover 2 α)
    (u : LittleHolder cover 2 α N) : M → ℝ :=
  smoothChartHolderContinuousMapExtension cover 2 α N u

/-- For `0 < α < 1`, evaluation of the order-two little-Hölder completion is C². A Cauchy
sequence in the gauge converges uniformly with each chart jet through order two; the local
uniform-derivative limit theorem on the interiors of the cover identifies those limits as the
derivatives of the evaluated function. -/
theorem littleHolderOrderTwoEvaluation_contMDiff
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (_hα₀ : 0 < α) (_hα₁ : α < 1)
    (N : SmoothChartHolderNormedData cover 2 α)
    (u : LittleHolder cover 2 α N) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) 2
      (littleHolderOrderTwoEvaluation cover α N u) := by
  exact smoothChartHolderContinuousMapExtension_contMDiff_orderTwo_of_completedJets
    cover α N u
    (fun j hj i z hz =>
      smoothChartHolderContinuousMapExtension_completedJet_eq
        cover α N u j hj i z hz)
    (fun j hj i z hz =>
      smoothChartHolderContinuousMapExtension_completedJet_norm_le
        cover α N u j hj i z hz)

end KahlerForm
