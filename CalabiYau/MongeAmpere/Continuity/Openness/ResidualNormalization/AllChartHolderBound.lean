module

public import CalabiYau.MongeAmpere.Continuity.Openness.ResidualNormalization.LittleHolderResidual
public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderC2Regularity.CompletedChartJets.TopJetHolderBound
public import CalabiYau.MongeAmpere.Continuity.Openness.ResidualNormalization.AllChartHolderBound.ChartTransitionTransfer

/-!
# Transfer the fixed-cover carrier bound to arbitrary charts

The C² carrier norm is defined using its selected finite compact chart cover.  The continuity
argument needs a `HolderBoundedInCharts` statement quantified over every chart, so transfer the
fixed-cover derivative and Hölder bounds through chart changes.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M]

omit [ConnectedSpace M] in
/-- Every in-radius C² carrier perturbation has a finite Hölder bound on every chart, not only the
fixed cover used to define the carrier. -/
theorem centeredResidual_carrier_allChartHolderBound (ω₀ : KahlerForm n M) (F : M → ℝ)
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F)
    (t : ℝ) (φ : M → ℝ)
    (hsol : ω₀.SolvesMongeAmpere (fun x ↦ t * F x + ω₀.pathConstant F t) φ)
    (α : ℝ≥0) (hα₁ : α < 1)
    [P : ContinuityHolderPair (ω₀.perturb φ hsol.1) α]
    (D : CenteredPathResidualCarrierData ω₀ F hF t φ hsol α)
    (u : P.C2) (hu : ‖u‖ < D.radius) :
    HolderBoundedInCharts (EuclideanSpace ℂ (Fin n)) 2 α
      {φ + P.evalC2 u} := by
  let cover := P.finiteChartCover
  let N := P.normedDataC2
  let φCore : SmoothChartHolderCore cover 2 α := ⟨⟨φ, hsol.1.1⟩⟩
  let carrier : LittleHolder cover 2 α N :=
    (φCore : LittleHolder cover 2 α N) + ((u : P.C2) : LittleHolder cover 2 α N)
  have heval :
      (smoothChartHolderContinuousMapExtension cover 2 α N carrier : M → ℝ) =
        φ + P.evalC2 u := by
    funext x
    change smoothChartHolderContinuousMapExtension cover 2 α N
        ((φCore : LittleHolder cover 2 α N) + ((u : P.C2) : LittleHolder cover 2 α N)) x =
      φ x + smoothChartHolderContinuousMapExtension cover 2 α N
        ((u : P.C2) : LittleHolder cover 2 α N) x
    rw [map_add]
    simp [φCore, smoothChartHolderContinuousMapExtension_coe,
      smoothChartHolderContinuousMapLinearMap]
  have hfixed : HolderBoundedOnFiniteChartCover cover 2 α
      ({φ + P.evalC2 u} : Set (M → ℝ)) := by
    refine ⟨‖carrier‖₊, ?_⟩
    intro f hf i
    have hf' : f = φ + P.evalC2 u := Set.mem_singleton_iff.mp hf
    subst f
    simpa [heval] using
      smoothChartHolderCompletedTopJetHolderBoundOn cover α N carrier i
  exact holderBoundedInCharts_of_fixedCoverBound cover (φ + P.evalC2 u)
    (D.radius_potential_sum u hu).1 (le_of_lt hα₁) hfixed

end KahlerForm
