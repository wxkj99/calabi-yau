module

public import CalabiYau.MongeAmpere.Continuity.Openness.ResidualNormalization
import CalabiYau.MongeAmpere.Continuity.Openness.ResidualDerivative.LogDetRemainder.ChartwiseBound
import CalabiYau.MongeAmpere.Continuity.Openness.ResidualDerivative.LogDetRemainder.C0NormFromHolder

/-!
# The little-Hölder log-determinant remainder

The chartwise log-determinant linearization has a uniform quadratic remainder in the little
C^{0,α} norm on a common positive cone. The pairwise form below is the strict-differentiability
remainder; its two-point estimate is stronger than a pointwise Taylor estimate at the base point.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology
open MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- Uniform pairwise quadratic Taylor control for the centered Monge–Ampère residual in the
little-Hölder target. Faithfulness of completed evaluation is used to identify target elements from
their chartwise pointwise formulas. -/
theorem exists_centeredResidual_logDetRemainder (ω₀ : KahlerForm n M) (F : M → ℝ)
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F)
    (t : ℝ) (φ : M → ℝ)
    (hsol : ω₀.SolvesMongeAmpere (fun x ↦ t * F x + ω₀.pathConstant F t) φ)
    (α : ℝ≥0) (hα₁ : α < 1)
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
        ‖D.residual p - D.residual q -
          (L (p.1 - q.1) + (p.2 - q.2) • b)‖ ≤
            (C : ℝ) * (‖p‖ + ‖q‖) * ‖p - q‖ := by
  obtain ⟨C, r, hr, hchart⟩ := exists_centeredResidual_chartwiseRemainderBound
    ω₀ F hF t φ hsol α hα₁ D L hL b hb
  refine ⟨C + C, r, hr, ?_⟩
  intro p q hp hq hpD hqD
  let v : P.C0 := D.residual p - D.residual q -
    (L (p.1 - q.1) + (p.2 - q.2) • b)
  have hHolder : ∀ i, HolderBoundOn 0 α
      (C * (‖p‖₊ + ‖q‖₊) * ‖p - q‖₊)
      (P.finiteChartCover.piece i)
      (P.evalC0 v ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
        (P.finiteChartCover.base i)).symm) := by
    intro i
    simpa [v] using hchart p q hp hq hpD hqD i
  let K : ℝ≥0 := C * (‖p‖₊ + ‖q‖₊) * ‖p - q‖₊
  have hnorm := meanZeroC0_norm_le_of_chartHolderBound
    (ω₀.perturb φ hsol.1) α v K hHolder
  have hKreal : (K : ℝ) =
      (C : ℝ) * (‖p‖ + ‖q‖) * ‖p - q‖ := by
    simp [K]
  calc
    ‖D.residual p - D.residual q -
        (L (p.1 - q.1) + (p.2 - q.2) • b)‖ = ‖v‖ := rfl
    _ ≤ 2 * (K : ℝ) := hnorm
    _ = ((C + C : ℝ≥0) : ℝ) * (‖p‖ + ‖q‖) * ‖p - q‖ := by
      rw [hKreal]
      simp only [NNReal.coe_add]
      ring

end KahlerForm
