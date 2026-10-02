module

public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.ComplexSmoothBall.Basic
public import CalabiYau.Analysis.Elliptic.Schauder.Cutoff.Elliptic.BallHessian
public import CalabiYau.Mathlib.Analysis.Holder.Localization
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import CalabiYau.Mathlib.Analysis.Holder.Bilinear
public import CalabiYau.Analysis.Parabolic.Euclidean.Duhamel.FrozenPositiveDefinite
public import CalabiYau.Analysis.Parabolic.Euclidean.HeatPotential.Estimate
public import CalabiYau.Mathlib.Analysis.Holder.Scaling
public import CalabiYau.Analysis.Parabolic.Euclidean.HeatSemigroup.Schauder
public import CalabiYau.Analysis.Estimates.Absorption
public import CalabiYau.Mathlib.Analysis.Holder.Interpolation
public import CalabiYau.Analysis.Elliptic.Schauder.VariableCoefficient.Basic
import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.SourceInterpolation.PatchGeometry
import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.SourceInterpolation.PatchLowerJet
import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.SourceInterpolation.CutoffSourceFormula
import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.SourceInterpolation.CutoffSourceHolderBound
import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.SourceInterpolation.EquationSourceNormBound
import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.SourceInterpolation.GapPowerBound
import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.SourceInterpolation.SeparatedBudget
import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.SourceInterpolation.SourceMasterBound
import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.SourceInterpolationProofs.GapBudget

/-!
# Cutoff-source interpolation bounds

Source: Constantin, Schauder Estimates, Theorem 3 and equation (9), p. 7;
localization and intermediate-jet interpolation, pp. 8–9. The parent is certified
assembly of independently reviewable source, profile, geometry and scalar leaves.
The final small coefficient multiplies the finite outer gauge, not a local gauge.
-/

@[expose] public section

open Set Matrix
open scoped NNReal ContDiff Topology

namespace CalabiYau.Schauder

private theorem realBallCutoffSourceBounds_fixedExponent
    {n : ℕ} (hn : 0 < n) (α lam K : ℝ≥0) (hα₀ : 0 < α) (hα₁ : α < 1)
    (_hlam : 0 < lam) (R d : ℝ) (M : ℝ≥0) (hR : 0 < R) (hd : 0 < d)
    (_hM : 1 ≤ M) (k : ℕ)
    (hkα : 3 + (α : ℝ) ≤ (k : ℝ) * (1 - (α : ℝ))) :
    ∀ θ : ℝ≥0, 0 < θ →
    ∃ C : ℝ≥0, ∀ {U : Set (RealBallModel n)} {c : RealBallModel n}
      {a : RealBallModel n → Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ}
      {u : RealBallModel n → ℝ} {K₀ K₁ : ℝ≥0},
      IsOpen U → Metric.closedBall c R ⊆ U →
      RealSmoothBallData α lam K K₀ K₁ U a u →
      ∀ (r t : ℝ), 0 ≤ r → r < t → t ≤ R →
      ∀ x ∈ Metric.closedBall c r,
      let δ := min d ((t - r) / 4)
      ∀ (coeff : RealBallCoefficientExtension a x δ)
        (jet : RealBallCutoffJet α x δ u),
      ∃ Kf Bf : ℝ≥0,
        ‖variableMatrixLap coeff.coefficient jet.second‖ ≤ (Bf : ℝ) ∧
        HolderWith Kf α
          (variableMatrixLap coeff.coefficient jet.second : RealBallModel n → ℝ) ∧
        M * (Kf + Bf + ‖jet.value‖₊) * realBallPatchFactor α δ ≤
          C * (Real.toNNReal (t - r))⁻¹ ^ (2 * k + 8) * (K₁ + K₀) +
            θ * realBallGauge α c t u := by
  intro θ hθ
  let A := realBallSourceMasterConst n α K M
  obtain ⟨C₀, hC₀⟩ := realBallSource_separated_budget (A := A) hα₁ k hkα θ hθ
  let D : ℝ≥0 := Real.toNNReal (R + R / d + 4)
  let C : ℝ≥0 := C₀ * D ^ (2 * k + 8)
  refine ⟨C, ?_⟩
  intro U c a u K₀ K₁ hU houter hdata r t hr hrt htR x hx
  dsimp only
  let δ := min d ((t - r) / 4)
  intro coeff jet
  obtain ⟨hδ, hsmooth, huNorm, hHess, hsourceHolder, _hsourceNorm,
    hcoeffHolder, hcoeffNorm⟩ :=
    realBallSource_patch_geometry hα₁ hd hU houter hdata hr hrt htR hx coeff
  have hpatchU : Metric.closedBall x δ ⊆ U := by
    intro y hy
    apply houter
    rw [Metric.mem_closedBall] at hx hy ⊢
    calc
      dist y c ≤ dist y x + dist x c := dist_triangle _ _ _
      _ ≤ δ + r := add_le_add hy hx
      _ ≤ R := by dsimp [δ]; nlinarith [min_le_right d ((t - r) / 4)]
  have hsourceNorm : ∀ y ∈ Metric.ball x δ, ‖realBallSource a u y‖ ≤ K₁ := by
    intro y hy
    have h := hdata.source_holder.1 0 (by omega) y
      (hpatchU (Metric.ball_subset_closedBall hy))
    simpa only [norm_iteratedFDeriv_zero] using h
  obtain ⟨eps₁, eps₂, heps₁, heps₂, hbuffer, _heps₂One, hsmall⟩ := hC₀ δ hδ
  let H := realBallGauge α c t u
  let G := realBallLowerGradientBound K₀ H eps₁
  let V := realBallLowerValueHolderBound α K₀ G eps₂
  let W := realBallLowerGradientHolderBound α H G eps₂
  obtain ⟨hgradNorm, hvalueHolder, hgradHolder⟩ :=
    realBallSource_patch_lower_jet hα₁ hδ eps₁ eps₂ heps₁ heps₂ hbuffer
      hsmooth huNorm hHess
  have hballSub : Metric.ball x δ ⊆ Metric.ball x (2 * δ) :=
    Metric.ball_subset_ball (by linarith)
  have huNormPatch : ∀ y ∈ Metric.ball x δ, ‖u y‖ ≤ K₀ :=
    fun y hy => huNorm y (hballSub hy)
  have hformula := realBallCutoffSource_formula hδ coeff jet hsmooth
  have hholder := realBallCutoffSource_holder_value_bound hn hδ hα₀ hα₁ coeff jet
    hsourceHolder hsourceNorm hcoeffHolder hcoeffNorm huNormPatch hgradNorm
    hvalueHolder hgradHolder hformula
  have hnorm := realBallCutoffJet_equation_source_norm_bound hδ coeff jet
    hformula hsourceNorm hcoeffNorm huNormPatch hgradNorm
  let hhalf : 0 ≤ δ / 2 := by positivity
  let hhalfLt : δ / 2 < δ := by linarith
  let Kχv := ballCutoffHolderConst (δ / 2) δ
  let Kχ := ballCutoffFDerivHolderConst (δ / 2) δ
  let Kχ₂ := ballCutoffFDeriv2HolderConst x hhalf hhalfLt
  let Mχ := ‖ballCutoffFDerivBoundedContinuousFunction x hhalf hhalfLt‖₊
  let Mχ₂ := ‖ballCutoffFDeriv2BoundedContinuousFunction x hhalf hhalfLt‖₊
  let Kf := K₁ * Kχv + K₁ +
    realBallSourceCommutatorHolderConst n K K₀ G V W Kχ Mχ Kχ₂ Mχ₂
  let Bf := K₁ + realBallSourcePairCount n * K * (2 * Mχ * G + Mχ₂ * K₀)
  change HolderWith Kf α
    (variableMatrixLap coeff.coefficient jet.second : RealBallModel n → ℝ) ∧
      ‖jet.value‖₊ ≤ K₀ at hholder
  change ‖variableMatrixLap coeff.coefficient jet.second‖ ≤ (Bf : ℝ) at hnorm
  have hmaster := realBallCutoffSource_canonical_master_bound
    (α := α) (K := K) (M := M) (K₀ := K₀) (K₁ := K₁)
    (G := G) (V := V) (W := W) x hδ
  change M * (Kf + Bf + K₀) * realBallPatchFactor α δ ≤
    A * realBallSourceScale δ ^ (3 + (α : ℝ)) * (K₁ + K₀ + G + V + W) at hmaster
  have hgap := realBallSource_gap_power_bound hR hd (2 * k + 8) hr hrt htR
  have hgapWeighted :
      C₀ * realBallSourceScale δ ^ (2 * k + 8) * (K₁ + K₀) + θ * H ≤
        C * (Real.toNNReal (t - r))⁻¹ ^ (2 * k + 8) * (K₁ + K₀) + θ * H := by
    calc
      _ ≤ C₀ * (D ^ (2 * k + 8) *
          (Real.toNNReal (t - r))⁻¹ ^ (2 * k + 8)) * (K₁ + K₀) + θ * H :=
        add_le_add (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hgap (show 0 ≤ C₀ from bot_le))
          (show 0 ≤ K₁ + K₀ from bot_le)) le_rfl
      _ = _ := by dsimp [C]; ring
  refine ⟨Kf, Bf, hnorm, hholder.1, ?_⟩
  calc
    _ ≤ M * (Kf + Bf + K₀) * realBallPatchFactor α δ := by
      gcongr
      exact hholder.2
    _ ≤ A * realBallSourceScale δ ^ (3 + (α : ℝ)) * (K₁ + K₀ + G + V + W) := hmaster
    _ ≤ C₀ * realBallSourceScale δ ^ (2 * k + 8) * (K₁ + K₀) + θ * H :=
      hsmall K₀ K₁ H
    _ ≤ C * (Real.toNNReal (t - r))⁻¹ ^ (2 * k + 8) * (K₁ + K₀) + θ * H := hgapWeighted

/-- Canonical cutoff-source controls with arbitrary small outer-gauge coefficient.
The loss exponent is chosen before the absorption parameter and all equation data. -/
theorem exists_realBallCutoffSourceBounds :
    ∀ {n : ℕ}, 0 < n → ∀ (α lam K : ℝ≥0), 0 < α → α < 1 → 0 < lam →
  ∀ (R d : ℝ) (M : ℝ≥0), 0 < R → 0 < d → 1 ≤ M →
  ∃ p : ℕ, 0 < p ∧ ∀ θ : ℝ≥0, 0 < θ →
    ∃ C : ℝ≥0, ∀ {U : Set (RealBallModel n)} {c : RealBallModel n}
      {a : RealBallModel n → Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ}
      {u : RealBallModel n → ℝ} {K₀ K₁ : ℝ≥0},
      IsOpen U → Metric.closedBall c R ⊆ U →
      RealSmoothBallData α lam K K₀ K₁ U a u →
      ∀ (r t : ℝ), 0 ≤ r → r < t → t ≤ R →
      ∀ x ∈ Metric.closedBall c r,
      let δ := min d ((t - r) / 4)
      ∀ (coeff : RealBallCoefficientExtension a x δ)
        (jet : RealBallCutoffJet α x δ u),
      ∃ Kf Bf : ℝ≥0,
        ‖variableMatrixLap coeff.coefficient jet.second‖ ≤ (Bf : ℝ) ∧
        HolderWith Kf α
          (variableMatrixLap coeff.coefficient jet.second : RealBallModel n → ℝ) ∧
        M * (Kf + Bf + ‖jet.value‖₊) * realBallPatchFactor α δ ≤
          C * (Real.toNNReal (t - r))⁻¹ ^ p * (K₁ + K₀) +
            θ * realBallGauge α c t u := by
  intro n hn α lam K hα₀ hα₁ hlam R d M hR hd hM
  obtain ⟨k, _, hkα⟩ := SourceInterpolationProofs.realBallExists_polynomial_small_theta_power hα₁
  have hp : 0 < 2 * k + 8 := by omega
  refine ⟨2 * k + 8, hp, ?_⟩
  exact realBallCutoffSourceBounds_fixedExponent hn α lam K hα₀ hα₁ hlam
    R d M hR hd hM k hkα

end CalabiYau.Schauder
