module

public import CalabiYau.MongeAmpere.Continuity.Openness.ResidualNormalization
public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderC2Regularity.CompletedChartJets
import CalabiYau.MongeAmpere.Continuity.Openness.ResidualDerivative.LogDetMatrixRemainder
import CalabiYau.MongeAmpere.Continuity.Openness.ResidualDerivative.LogDetBaseVariation
import CalabiYau.MongeAmpere.Continuity.Openness.ResidualDerivative.LogDetRemainder.ChartwiseTransfer

/-!
# Chartwise Hölder bound for the centered residual remainder

The fixed-base and variable-base matrix remainders, together with completed chart jets and Hölder
bilinear estimates, give a pairwise order-zero HolderBoundOn estimate on each compact chart piece.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology
open MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- Uniform chartwise `C^{0,α}` control of the evaluated pairwise centered-residual remainder. -/
theorem exists_centeredResidual_chartwiseRemainderBound
    (ω₀ : KahlerForm n M) (F : M → ℝ)
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F)
    (t : ℝ) (φ : M → ℝ)
    (hsol : ω₀.SolvesMongeAmpere (fun x ↦ t * F x + ω₀.pathConstant F t) φ)
    (α : ℝ≥0) (hα₀ : 0 < α) (hα₁ : α < 1)
    [P : ContinuityHolderPair (ω₀.perturb φ hsol.1) α]
    (D : CenteredPathResidualData ω₀ F hF t φ hsol α)
    (L : P.C2 ≃L[ℝ] P.C0)
    (hL : ∀ u, P.evalC0 (L u) = (ω₀.perturb φ hsol.1).laplacian (P.evalC2 u))
    (b : P.C0)
    (hb : ∀ x, P.evalC0 b x =
      (∫ y, F y ∂(ω₀.perturb φ hsol.1).volume) /
        (ω₀.perturb φ hsol.1).volume.real Set.univ - F x) :
    ∃ C : ℝ≥0, ∃ r : ℝ, 0 < r ∧
      ∀ p q : P.C2 × ℝ, ‖p‖ < r → ‖q‖ < r →
        ‖p.1‖ < D.radius → ‖q.1‖ < D.radius →
        ∀ i, HolderBoundOn 0 α
          (C * (‖p‖₊ + ‖q‖₊) * ‖p - q‖₊)
          (P.finiteChartCover.piece i)
          ((P.evalC0 (D.residual p - D.residual q -
            (L (p.1 - q.1) + (p.2 - q.2) • b))) ∘
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
              (P.finiteChartCover.base i)).symm) := by
  exact exists_centeredResidual_chartwiseRemainderBound_transfer
    ω₀ F hF t φ hsol α hα₀ hα₁ D L hL b hb
    (fun A X Y μ hμ hA hAinv hsegment hsegmentInv =>
      Matrix.logDetTaylorRemainder_sub_bound A X Y μ hμ hA hAinv hsegment hsegmentInv)
    (fun Mbound hMbound =>
      Matrix.exists_logDetTaylorRemainder_baseVariation_bound Mbound hMbound)
    (fun u i => by
      change HolderBoundOn 2 α ‖u‖₊ (P.finiteChartCover.piece i)
        ((smoothChartHolderContinuousMapExtension P.finiteChartCover 2 α
          P.normedDataC2
          (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2) : M → ℝ) ∘
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
            (P.finiteChartCover.base i)).symm)
      exact smoothChartHolderContinuousMapExtension_holderBoundOn
        P.finiteChartCover α P.normedDataC2
        (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2) i)
    CalabiYau.Schauder.holderWith_bilinear_of_norm_le

end KahlerForm
