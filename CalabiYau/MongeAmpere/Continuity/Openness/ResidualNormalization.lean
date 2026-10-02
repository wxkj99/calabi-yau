module

public import CalabiYau.MongeAmpere.Continuity.Openness.C2MassNormalization
public import CalabiYau.MongeAmpere.Continuity.Openness.PotentialStability
public import CalabiYau.MongeAmpere.Continuity.Openness.ResidualNormalization.LittleHolderResidual
public import CalabiYau.MongeAmpere.Continuity.Openness.ResidualNormalization.CenteredZeroNormalization

/-!
# The centered path residual and its normalization

For a fixed smooth solution at time `t`, subtract its log Monge–Ampère equation from the equation
at `t + δ`.  Project this difference to mean zero using the perturbed volume.  A zero of the
projected residual has constant unprojected residual; invariance of the Monge–Ampère mass and the
definition of `pathConstant` force that constant to be zero.  The radius in the data keeps the
perturbed form positive.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology
open Set MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- Banach-valued realization of the centered residual and its normalization conclusion.

The map has values in the mean-zero target `C^{0,α}`.  On a ball in `C^{2,α}`, it represents the
pointwise centered residual above, and a zero gives an actual `C²` path solution. -/
structure CenteredPathResidualData (ω₀ : KahlerForm n M) (F : M → ℝ)
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F)
    (t : ℝ) (φ : M → ℝ)
    (hsol : ω₀.SolvesMongeAmpere (fun x ↦ t * F x + ω₀.pathConstant F t) φ)
    (α : ℝ≥0) [P : ContinuityHolderPair (ω₀.perturb φ hsol.1) α] where
  radius : ℝ
  radius_pos : 0 < radius
  /-- Every potential in the residual ball preserves positivity, so its logarithmic
  Monge–Ampère density is defined throughout the domain used by the implicit-function theorem. -/
  radius_potential : ∀ (u : P.C2), ‖u‖ < radius →
    (ω₀.perturb φ hsol.1).IsC2Potential (P.evalC2 u)
  residual : P.C2 × ℝ → P.C0
  eval_residual : ∀ (u : P.C2) (δ : ℝ), ‖u‖ < radius → ∀ x,
    P.evalC0 (residual (u, δ)) x =
      centeredContinuityPathResidual ω₀ F t φ hsol (P.evalC2 u) δ x
  residual_base : residual (0, 0) = 0
  residual_zero_solution : ∀ (u : P.C2) (δ : ℝ), ‖u‖ < radius →
    residual (u, δ) = 0 →
      HolderBoundedInCharts (EuclideanSpace ℂ (Fin n)) 2 α
        {φ + P.evalC2 u} ∧
      ω₀.SolvesMongeAmpereC2
        (fun x ↦ (t + δ) * F x + ω₀.pathConstant F (t + δ))
        (φ + P.evalC2 u)

/-- Realize the centered path residual in the little Hölder target, with the mass normalization
that turns its small zeros into finite-regularity Monge–Ampère solutions. -/
theorem exists_centeredPathResidualData (ω₀ : KahlerForm n M) (F : M → ℝ)
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F)
    (t : ℝ) (φ : M → ℝ)
    (hsol : ω₀.SolvesMongeAmpere (fun x ↦ t * F x + ω₀.pathConstant F t) φ)
    (α : ℝ≥0) (hα₀ : 0 < α) (hα₁ : α < 1)
    [P : ContinuityHolderPair (ω₀.perturb φ hsol.1) α] :
    Nonempty (CenteredPathResidualData ω₀ F hF t φ hsol α) := by
  obtain ⟨D⟩ :=
    exists_centeredPathResidualCarrierData ω₀ F hF t φ hsol α hα₀ hα₁
  refine ⟨{
    radius := D.radius
    radius_pos := D.radius_pos
    radius_potential := D.radius_potential
    residual := D.residual
    eval_residual := D.eval_residual
    residual_base := D.residual_base
    residual_zero_solution := ?_
  }⟩
  intro u δ hu hzero
  exact centeredPathResidual_zero_to_solution ω₀ F hF t φ hsol α hα₁ D u δ hu hzero

end KahlerForm
