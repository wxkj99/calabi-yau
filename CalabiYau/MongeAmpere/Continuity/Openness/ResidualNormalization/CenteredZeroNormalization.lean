module

public import CalabiYau.MongeAmpere.Continuity.Openness.C2MassNormalization
public import CalabiYau.MongeAmpere.Continuity.Openness.ResidualNormalization.LittleHolderResidual
public import CalabiYau.MongeAmpere.Continuity.Openness.ResidualNormalization.ResidualMassEquation
public import CalabiYau.MongeAmpere.Continuity.Openness.ResidualNormalization.AllChartHolderBound

/-!
# Normalize a centered zero to the continuity-path equation

A zero of the mean-zero residual makes the uncentered logarithmic residual spatially constant.
Finite-regularity Monge–Ampère mass invariance and the normalized path mass force this constant to
vanish.  The conclusion also records the chartwise regularity needed by the closedness argument.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology
open Set MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M]

omit [ConnectedSpace M] in
/-- A zero of the centered little-Hölder residual gives the exact finite-regularity path equation.
The all-chart bound is included: the carrier is defined using one fixed compact chart cover, while
this conclusion is used by the global continuity argument. -/
theorem centeredPathResidual_zero_to_solution (ω₀ : KahlerForm n M) (F : M → ℝ)
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F)
    (t : ℝ) (φ : M → ℝ)
    (hsol : ω₀.SolvesMongeAmpere (fun x ↦ t * F x + ω₀.pathConstant F t) φ)
    (α : ℝ≥0) (hα₁ : α < 1)
    [P : ContinuityHolderPair (ω₀.perturb φ hsol.1) α]
    (D : CenteredPathResidualCarrierData ω₀ F hF t φ hsol α)
    (u : P.C2) (δ : ℝ) (hu : ‖u‖ < D.radius)
    (hzero : D.residual (u, δ) = 0) :
    HolderBoundedInCharts (EuclideanSpace ℂ (Fin n)) 2 α
        {φ + P.evalC2 u} ∧
      ω₀.SolvesMongeAmpereC2
        (fun x ↦ (t + δ) * F x + ω₀.pathConstant F (t + δ))
        (φ + P.evalC2 u) := by
  constructor
  · exact centeredResidual_carrier_allChartHolderBound ω₀ F hF t φ hsol α hα₁ D u hu
  · exact centeredResidual_zero_implies_path_equation ω₀ F hF t φ hsol α
      D u δ hu hzero

end KahlerForm
