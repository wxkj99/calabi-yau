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

/-!
# Canonical inner cutoff jet identities, finite smooth outer gauge and lower-jet interpolation.

Proof-preserving extraction from the committed SourceInterpolation module
073d0f59b03ec37cc921b9792875e063bec3fb01.
Source: Constantin, Schauder Estimates, equation (9), p. 7 and localization/
lower-jet interpolation, pp. 8–9. Only visibility and namespace are changed.
-/

@[expose] public section

open Set Matrix
open scoped NNReal ContDiff Topology

namespace CalabiYau.Schauder.SourceInterpolationProofs

theorem realBallHessian_norm_le_of_finiteGauge
    {n : ℕ} {α : ℝ≥0} {c : RealBallModel n} {R : ℝ}
    {u : RealBallModel n → ℝ}
    (hfinite : eContDiffHolderGaugeOn 2 α (Metric.closedBall c R) u ≠ ⊤) :
    ∀ x ∈ Metric.closedBall c R,
      ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ realBallGauge α c R u := by
  have hcoe : (realBallGauge α c R u : ENNReal) =
      eContDiffHolderGaugeOn 2 α (Metric.closedBall c R) u := by
    dsimp [realBallGauge]
    exact ENNReal.coe_toNNReal hfinite
  have hbound : eContDiffHolderGaugeOn 2 α (Metric.closedBall c R) u ≤
      (realBallGauge α c R u : ENNReal) := by
    rw [hcoe]
  intro x hx
  have hjet := spatialJet_norm_le hbound (j := 2) le_rfl hx
  calc
    ‖fderiv ℝ (fderiv ℝ u) x‖ =
        ‖hessianCurryEquiv (RealBallModel n) ℝ (iteratedFDeriv ℝ 2 u x)‖ := by
          rw [hessianCurryEquiv_iteratedFDeriv_two_eq_fderiv]
    _ = ‖iteratedFDeriv ℝ 2 u x‖ := by
          rw [(hessianCurryEquiv (RealBallModel n) ℝ).norm_map]
    _ ≤ realBallGauge α c R u := by exact_mod_cast hjet
theorem realBallLowerJet_interpolation
    {n : ℕ} {α M H : ℝ≥0} {c : RealBallModel n} {r R : ℝ}
    {u : RealBallModel n → ℝ} (hα : α < 1)
    (eps₁ eps₂ : ℝ≥0) (heps₁ : 0 < eps₁) (heps₂ : 0 < eps₂)
    (hbuffer : r + (eps₁ : ℝ) < R)
    (hsmooth : ContDiffOn ℝ 2 u (Metric.ball c R))
    (huNorm : ∀ z ∈ Metric.ball c R, ‖u z‖ ≤ M)
    (hHess : ∀ z ∈ Metric.ball c R, ‖fderiv ℝ (fderiv ℝ u) z‖ ≤ H) :
    (∀ x ∈ Metric.closedBall c r,
      ‖fderiv ℝ u x‖ ≤ 2 * M / eps₁ + H * eps₁) ∧
    HolderWith (H * eps₂ ^ ((1 : ℝ≥0) - α : ℝ) +
      2 * (2 * M / eps₁ + H * eps₁) / eps₂ ^ (α : ℝ)) α
      ((Metric.closedBall c r).domRestrict (fderiv ℝ u)) ∧
    HolderWith ((2 * M / eps₁ + H * eps₁) * eps₂ ^ ((1 : ℝ≥0) - α : ℝ) +
      2 * M / eps₂ ^ (α : ℝ)) α ((Metric.closedBall c r).domRestrict u) := by
  let S := Metric.ball c R
  let G : ℝ≥0 := 2 * M / eps₁ + H * eps₁
  have hgradCont : ∀ z ∈ S, ContDiffAt ℝ 1 (fderiv ℝ u) z := by
    intro z hz
    exact (hsmooth.contDiffAt (Metric.isOpen_ball.mem_nhds hz)).fderiv_right (by norm_num)
  have hgradDiff : ∀ z ∈ S, DifferentiableAt ℝ (fderiv ℝ u) z := by
    intro z hz
    exact (hgradCont z hz).differentiableAt (by norm_num)
  have hgradDeriv : ∀ z ∈ S, ‖fderiv ℝ (fderiv ℝ u) z‖₊ ≤ H := by
    intro z hz
    exact_mod_cast hHess z hz
  have hgradLip : LipschitzOnWith H (fderiv ℝ u) S :=
    Convex.lipschitzOnWith_of_nnnorm_fderiv_le hgradDiff hgradDeriv (convex_ball c R)
  have hgradHolder1 : HolderOnWith H 1 (fderiv ℝ u) S := hgradLip.holderOnWith
  have huDiff : ∀ z ∈ S, DifferentiableAt ℝ u z := by
    intro z hz
    exact (hsmooth.contDiffAt (Metric.isOpen_ball.mem_nhds hz)).differentiableAt (by norm_num)
  have hrR : r < R := by
    calc
      r < r + (eps₁ : ℝ) := lt_add_of_pos_right r (by exact_mod_cast heps₁)
      _ < R := hbuffer
  have hstep : ∀ x ∈ Metric.closedBall c r, ∀ v : RealBallModel n,
      ‖v‖ = 1 → x + (eps₁ : ℝ) • v ∈ S := by
    intro x hx v hv
    rw [Metric.mem_ball]
    calc
      dist (x + (eps₁ : ℝ) • v) c ≤
          dist (x + (eps₁ : ℝ) • v) x + dist x c := dist_triangle _ _ _
      _ = eps₁ + dist x c := by
        rw [dist_eq_norm]
        simp only [add_sub_cancel_left, norm_smul, hv, mul_one]
        rw [Real.norm_of_nonneg (by exact_mod_cast heps₁.le)]
      _ ≤ eps₁ + r := by
        gcongr
        exact Metric.mem_closedBall.mp hx
      _ < R := by linarith [hbuffer]
  have hgradBound : ∀ x ∈ Metric.closedBall c r,
      ‖fderiv ℝ u x‖ ≤ (G : ℝ) := by
    intro x hx
    have hxS : x ∈ S := by
      rw [Metric.mem_ball]
      exact (Metric.mem_closedBall.mp hx).trans_lt hrR
    have hraw := norm_fderiv_le_at_scale_on (convex_ball c R) huDiff
      hgradHolder1 huNorm (by exact_mod_cast heps₁) hxS (hstep x hx)
    change ‖fderiv ℝ u x‖ ≤ 2 * (M : ℝ) / (eps₁ : ℝ) +
      (H : ℝ) * (eps₁ : ℝ) ^ (1 : ℝ) at hraw
    rw [Real.rpow_one] at hraw
    simpa only [G, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_div,
      NNReal.coe_ofNat] using hraw
  have hgradLipInner : LipschitzOnWith H (fderiv ℝ u) (Metric.closedBall c r) :=
    hgradLip.mono (Metric.closedBall_subset_ball hrR)
  have hgradHolder := holderWith_restrict_of_norm_le_of_lipschitzOnWith
    (epsilon := eps₂) heps₂ hα.le
    (fun x hx => by exact_mod_cast hgradBound x hx) hgradLipInner
  have huLip : LipschitzOnWith G u (Metric.closedBall c r) := by
    apply (convex_closedBall c r).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    · intro z hz
      exact huDiff z (Metric.closedBall_subset_ball hrR hz)
    · intro z hz
      exact_mod_cast hgradBound z hz
  have huHolder := holderWith_restrict_of_norm_le_of_lipschitzOnWith
    (epsilon := eps₂) heps₂ hα.le
    (fun z hz => huNorm z (Metric.closedBall_subset_ball hrR hz)) huLip
  refine ⟨hgradBound, ?_, ?_⟩
  · simpa only [NNReal.coe_rpow, NNReal.coe_sub, NNReal.coe_one] using hgradHolder
  · simpa only [NNReal.coe_rpow, NNReal.coe_sub, NNReal.coe_one] using huHolder

end CalabiYau.Schauder.SourceInterpolationProofs
