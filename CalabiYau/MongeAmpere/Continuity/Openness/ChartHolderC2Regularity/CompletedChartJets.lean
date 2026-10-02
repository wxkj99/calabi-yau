module

public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderEvaluation
public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderJets
public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderC2Regularity.CompletedChartJets.Identity
public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderC2Regularity.CompletedChartJets.NormBound
public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderC2Regularity.CompletedChartJets.TopJetHolderBound

/-!
# Completed chart jets on the interior of a chart piece

The continuous evaluation of an order-two little-Hölder completion has the completed chart jets as
its coordinate derivatives. The canonical jet extension also retains the unit operator-norm bound
of the smooth-core jet map.
-/

@[expose] public section

noncomputable section

open scoped Manifold ContDiff NNReal Topology

namespace KahlerForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]

/-- On the interior of a compact chart piece, every coordinate derivative through order two of the
completed evaluation is the corresponding canonical completed chart jet. -/
theorem smoothChartHolderContinuousMapExtension_completedJet_eq
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover 2 α)
    (u : LittleHolder cover 2 α N)
    (j : ℕ) (hj : j ≤ 2) (i) (z : E)
    (hz : z ∈ interior (cover.piece i)) :
    iteratedFDeriv ℝ j
      ((smoothChartHolderContinuousMapExtension cover 2 α N u : M → ℝ) ∘
        (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z =
      smoothChartHolderJetCanonicalExtension cover 2 α N j hj u i
        ⟨z, interior_subset hz⟩ := by
  exact smoothChartHolderCompletedJetIdentity cover α N u j hj i z hz

/-- The completed chart jet at an interior point is bounded by the little-Hölder norm. -/
theorem smoothChartHolderContinuousMapExtension_completedJet_norm_le
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover 2 α)
    (u : LittleHolder cover 2 α N)
    (j : ℕ) (hj : j ≤ 2) (i) (z : E)
    (hz : z ∈ interior (cover.piece i)) :
    ‖smoothChartHolderJetCanonicalExtension cover 2 α N j hj u i
      ⟨z, interior_subset hz⟩‖ ≤ ‖u‖ := by
  exact smoothChartHolderCompletedJetNormBound cover α N u j hj i z hz

/-- The fixed-cover estimate retains the top-order Hölder seminorm in addition to all jet sup
bounds. -/
theorem smoothChartHolderContinuousMapExtension_holderBoundOn
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover 2 α)
    (u : LittleHolder cover 2 α N) (i) :
    HolderBoundOn 2 α ‖u‖₊ (cover.piece i)
      ((smoothChartHolderContinuousMapExtension cover 2 α N u : M → ℝ) ∘
        (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) := by
  exact smoothChartHolderCompletedTopJetHolderBoundOn cover α N u i

/-- For smooth-core elements, the completed-jet identity reduces to the defining chart jet. This
coercion check is valid for every `α`, including `α = 0`. -/
private theorem smoothChartHolderContinuousMapExtension_completedJet_eq_smoothCore
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover 2 α)
    (f : SmoothChartHolderCore cover 2 α)
    (j : ℕ) (hj : j ≤ 2) (i) (z : E)
    (hz : z ∈ interior (cover.piece i)) :
    iteratedFDeriv ℝ j
      ((smoothChartHolderContinuousMapExtension cover 2 α N
        (f : LittleHolder cover 2 α N) : M → ℝ) ∘
        (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z =
      smoothChartHolderJetCanonicalExtension cover 2 α N j hj
        (f : LittleHolder cover 2 α N) i ⟨z, interior_subset hz⟩ := by
  rw [smoothChartHolderContinuousMapExtension_coe,
    smoothChartHolderJetCanonicalExtension_coe]
  rfl

end KahlerForm
