module

public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.ComplexSmoothBall.Basic
public import CalabiYau.Analysis.Elliptic.Schauder.VariableCoefficient.BallInterior
public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.SourceInterpolationProofs.LowerJet

/-!
# Cutoff Hessian bounds, source-radius geometry and patch lower-jet control.

Proof-preserving extraction from the committed SourceInterpolation module
073d0f59b03ec37cc921b9792875e063bec3fb01.
Source: Constantin, Schauder Estimates, equation (9), p. 7 and localization/
lower-jet interpolation, pp. 8–9. Only visibility and namespace are changed.
-/

@[expose] public section

open Set Matrix
open scoped NNReal ContDiff Topology

namespace CalabiYau.Schauder.SourceInterpolationProofs

theorem realBallSourceRadius_bounds
    {r t d : ℝ} (hd : 0 < d) (hr : 0 ≤ r) (hrt : r < t) :
    let δ := min d ((t - r) / 4)
    0 < δ ∧ δ ≤ d ∧ δ ≤ (t - r) / 4 ∧ δ / 4 ≤ t := by
  dsimp
  have hgap : 0 < (t - r) / 4 := by linarith
  refine ⟨lt_min hd hgap, ?_⟩
  refine ⟨min_le_left _ _, ?_⟩
  refine ⟨min_le_right _ _, ?_⟩
  have ht : 0 < t := lt_of_le_of_lt hr hrt
  nlinarith [min_le_right d ((t - r) / 4)]

theorem realBallHessian_norm_le_bigSourceBall
    {n : ℕ} {α : ℝ≥0} {c x : RealBallModel n} {r t d : ℝ}
    {u : RealBallModel n → ℝ}
    (hrt : r < t)
    (hfinite : eContDiffHolderGaugeOn 2 α (Metric.closedBall c t) u ≠ ⊤)
    (hx : x ∈ Metric.closedBall c r) :
    ∀ y ∈ Metric.ball x (2 * min d ((t-r)/4)),
      ‖fderiv ℝ (fderiv ℝ u) y‖ ≤ realBallGauge α c t u := by
  have hδt : min d ((t-r)/4) ≤ (t-r)/4 := min_le_right _ _
  have hball : Metric.ball x (2 * min d ((t-r)/4)) ⊆ Metric.closedBall c t := by
    intro y hy
    rw [Metric.mem_closedBall]
    have hyx := Metric.mem_ball.mp hy
    have hxc := Metric.mem_closedBall.mp hx
    have hyt : dist y c < t := by
      calc
        dist y c ≤ dist y x + dist x c := dist_triangle y x c
        _ < 2 * min d ((t-r)/4) + r := by linarith
        _ ≤ t := by nlinarith [hrt, hδt, hxc]
    exact hyt.le
  intro y hy
  exact realBallHessian_norm_le_of_finiteGauge hfinite y (hball hy)

end CalabiYau.Schauder.SourceInterpolationProofs
