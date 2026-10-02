module

public import CalabiYau.MongeAmpere.Continuity.Openness.ResidualNormalization
import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderMeanZero
import CalabiYau.MongeAmpere.Continuity.Openness.ResidualDerivative.MeanZeroDirection
import CalabiYau.MongeAmpere.Continuity.Openness.ResidualDerivative.LogDetRemainder

/-!
# Strict differentiability of the centered residual

The derivative at the base point is the Laplacian in the potential direction and the centered
parameter direction `avg(F) - F`.  In chart coordinates the first part is
`hasDerivAt_log_mongeAmpere_of_contMDiff_two`; the Hölder algebra estimates lift this pointwise
linearization to strict differentiability between the little Hölder Banach spaces.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology
open MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M] [Nonempty M]

/-- The strict derivative of the centered log-Monge–Ampère residual, including its normalized
time direction.  The derivative formula is `L u + δ • (avg(F) - F)`. -/
theorem exists_centeredResidual_strictDerivative (ω₀ : KahlerForm n M) (F : M → ℝ)
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F)
    (t : ℝ) (φ : M → ℝ)
    (hsol : ω₀.SolvesMongeAmpere (fun x ↦ t * F x + ω₀.pathConstant F t) φ)
    (α : ℝ≥0) (hα₀ : 0 < α) (hα₁ : α < 1)
    [P : ContinuityHolderPair (ω₀.perturb φ hsol.1) α]
    (D : CenteredPathResidualData ω₀ F hF t φ hsol α)
    (L : P.C2 ≃L[ℝ] P.C0)
    (hL : ∀ u, P.evalC0 (L u) = (ω₀.perturb φ hsol.1).laplacian (P.evalC2 u)) :
    ∃ b : P.C0, (∀ x,
        P.evalC0 b x =
          (∫ y, F y ∂(ω₀.perturb φ hsol.1).volume) /
            (ω₀.perturb φ hsol.1).volume.real Set.univ - F x) ∧
      ∃ T : (P.C2 × ℝ) →L[ℝ] P.C0,
        (∀ u δ, T (u, δ) = L u + δ • b) ∧
          HasStrictFDerivAt D.residual T (0, 0) := by
  classical
  let ω₁ := ω₀.perturb φ hsol.1
  have hvol : 0 < ω₁.volume.real Set.univ := by
    have hint : Integrable (fun x : M ↦ Real.exp ((0 : ℝ) : ℝ)) ω₁.volume := by
      simp
    have h := integral_exp_pos (μ := ω₁.volume) (f := fun _ : M ↦ (0 : ℝ)) hint
    simp at h ⊢
  obtain ⟨b, hb⟩ := exists_centeredResidual_meanZeroDirection
    ω₁ F hF α hvol
  let B : ℝ →L[ℝ] P.C0 := (1 : ℝ →L[ℝ] ℝ).smulRight b
  let T : (P.C2 × ℝ) →L[ℝ] P.C0 :=
    L.toContinuousLinearMap.comp (ContinuousLinearMap.fst ℝ P.C2 ℝ) +
      B.comp (ContinuousLinearMap.snd ℝ P.C2 ℝ)
  have hT : ∀ u δ, T (u, δ) = L u + δ • b := by
    intro u δ
    simp [T, B]
  have hEval : Function.Injective P.evalC0 := by
    intro x y hxy
    apply littleHolderMeanZeroEvaluationC0CLM_injective
      ω₁ P.finiteChartCover α P.normedDataC0
    ext z
    exact congrFun hxy z
  obtain ⟨C, r, hr, hrem⟩ := exists_centeredResidual_logDetRemainder
    ω₀ F hF t φ hsol α hα₁ D L hL b hb
  refine ⟨b, hb, T, hT, ?_⟩
  rw [hasStrictFDerivAt_iff_isLittleO]
  apply Asymptotics.isLittleO_iff.2
  intro ε hε
  let ρ : ℝ := min (min r D.radius) (ε / (2 * ((C : ℝ) + 1)))
  have hρ : 0 < ρ := by
    dsimp [ρ]
    positivity [D.radius_pos]
  have hρr : ρ ≤ r := by
    dsimp [ρ]
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hρD : ρ ≤ D.radius := by
    dsimp [ρ]
    exact (min_le_left _ _).trans (min_le_right _ _)
  have hρeps : ρ ≤ ε / (2 * ((C : ℝ) + 1)) := by
    dsimp [ρ]
    exact min_le_right _ _
  have hden : 0 < 2 * ((C : ℝ) + 1) := by
    positivity
  filter_upwards [Metric.ball_mem_nhds ((0 : (P.C2 × ℝ) × (P.C2 × ℝ))) hρ]
    with z hz
  have hz_norm : ‖z‖ < ρ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hp_norm : ‖z.1‖ < r :=
    (norm_fst_le z).trans_lt (hz_norm.trans_le hρr)
  have hq_norm : ‖z.2‖ < r :=
    (norm_snd_le z).trans_lt (hz_norm.trans_le hρr)
  have hp_radius : ‖z.1.1‖ < D.radius := by
    calc
      ‖z.1.1‖ ≤ ‖z.1‖ := norm_fst_le _
      _ ≤ ‖z‖ := norm_fst_le z
      _ < ρ := hz_norm
      _ ≤ D.radius := hρD
  have hq_radius : ‖z.2.1‖ < D.radius := by
    calc
      ‖z.2.1‖ ≤ ‖z.2‖ := norm_fst_le _
      _ ≤ ‖z‖ := norm_snd_le z
      _ < ρ := hz_norm
      _ ≤ D.radius := hρD
  have hnorm_small : ‖z‖ < ε / (2 * ((C : ℝ) + 1)) :=
    hz_norm.trans_le hρeps
  have hcoef : (C : ℝ) * (‖z.1‖ + ‖z.2‖) ≤ ε := by
    have hsum : ‖z.1‖ + ‖z.2‖ ≤ 2 * ‖z‖ := by
      calc
        ‖z.1‖ + ‖z.2‖ ≤ ‖z‖ + ‖z‖ := add_le_add (norm_fst_le z) (norm_snd_le z)
        _ = 2 * ‖z‖ := by ring
    have hscaled : 2 * ((C : ℝ) + 1) * ‖z‖ < ε := by
      have h' := (lt_div_iff₀ hden).mp hnorm_small
      nlinarith [h']
    have hC_nonneg : 0 ≤ (C : ℝ) := C.2
    calc
      (C : ℝ) * (‖z.1‖ + ‖z.2‖) ≤ (C : ℝ) * (2 * ‖z‖) :=
        mul_le_mul_of_nonneg_left hsum hC_nonneg
      _ ≤ ((C : ℝ) + 1) * (2 * ‖z‖) := by
        gcongr
        linarith [hC_nonneg]
      _ ≤ ε := le_of_lt (by nlinarith)
  have hpair := hrem z.1 z.2 hp_norm hq_norm hp_radius hq_radius
  have hTpair : T (z.1 - z.2) =
      L (z.1.1 - z.2.1) + (z.1.2 - z.2.2) • b := by
    calc
      T (z.1 - z.2) = T z.1 - T z.2 := map_sub T _ _
      _ = (L z.1.1 + z.1.2 • b) - (L z.2.1 + z.2.2 • b) := by
        rw [hT z.1.1 z.1.2, hT z.2.1 z.2.2]
      _ = L (z.1.1 - z.2.1) + (z.1.2 - z.2.2) • b := by
        rw [map_sub, sub_smul]
        abel
  calc
    ‖D.residual z.1 - D.residual z.2 - T (z.1 - z.2)‖ =
        ‖D.residual z.1 - D.residual z.2 -
          (L (z.1.1 - z.2.1) + (z.1.2 - z.2.2) • b)‖ := by
      exact congrArg
        (fun y : P.C0 => ‖D.residual z.1 - D.residual z.2 - y‖)
        hTpair
    _ ≤ (C : ℝ) * (‖z.1‖ + ‖z.2‖) * ‖z.1 - z.2‖ := hpair
    _ ≤ ε * ‖z.1 - z.2‖ := mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)

end KahlerForm
