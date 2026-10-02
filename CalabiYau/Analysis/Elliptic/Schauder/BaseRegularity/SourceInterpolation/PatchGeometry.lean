module

public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.SourceInterpolation.Basic
public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.ComplexSmoothBall.GaugeFiniteness
public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.SourceInterpolationProofs.SourceControl
public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.SourceInterpolationProofs.PatchJet

/-!
# Nested-patch geometry and equation data

Source: Constantin, Schauder Estimates, localization p. 8; the finite-gauge
bridge precedes every conversion from ENNReal to NNReal.
-/

@[expose] public section

open Set Matrix
open scoped NNReal ContDiff Topology

namespace CalabiYau.Schauder

/-- All local witnesses used by the source assembly, on the doubled patch. -/
theorem realBallSource_patch_geometry
    {n : ℕ} {α lam K K₀ K₁ : ℝ≥0} {R d r t : ℝ}
    {U : Set (RealBallModel n)} {c x : RealBallModel n}
    {a : RealBallModel n → Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ}
    {u : RealBallModel n → ℝ}
    (hα : α < 1) (hd : 0 < d) (hU : IsOpen U)
    (houter : Metric.closedBall c R ⊆ U)
    (hdata : RealSmoothBallData α lam K K₀ K₁ U a u)
    (hr : 0 ≤ r) (hrt : r < t) (htR : t ≤ R)
    (hx : x ∈ Metric.closedBall c r)
    (coeff : RealBallCoefficientExtension a x (min d ((t - r) / 4))) :
    let δ := min d ((t - r) / 4)
    0 < δ ∧
    ContDiffOn ℝ 2 u (Metric.ball x (2 * δ)) ∧
    (∀ y ∈ Metric.ball x (2 * δ), ‖u y‖ ≤ K₀) ∧
    (∀ y ∈ Metric.ball x (2 * δ),
      ‖fderiv ℝ (fderiv ℝ u) y‖ ≤ realBallGauge α c t u) ∧
    HolderWith K₁ α ((Metric.ball x δ).domRestrict (realBallSource a u)) ∧
    (∀ y ∈ Metric.ball x δ, ‖realBallSource a u y‖ ≤ K₁) ∧
    (∀ i j, HolderWith K α
      ((Metric.ball x δ).domRestrict (coeff.coefficient i j : RealBallModel n → ℝ))) ∧
    (∀ i j y, y ∈ Metric.ball x δ → ‖coeff.coefficient i j y‖ ≤ K) := by
  dsimp
  let δ := min d ((t - r) / 4)
  have hrad := SourceInterpolationProofs.realBallSourceRadius_bounds hd hr hrt
  have hgapδ : δ ≤ (t - r) / 4 := hrad.2.2.1
  have htRball : Metric.closedBall c t ⊆ Metric.closedBall c R :=
    Metric.closedBall_subset_closedBall htR
  have hpatch : Metric.closedBall x (2 * δ) ⊆ Metric.closedBall c t := by
    intro y hy
    rw [Metric.mem_closedBall] at hy ⊢
    have hyx : dist y x ≤ 2 * δ := Metric.mem_closedBall.mp hy
    have hxc : dist x c ≤ r := Metric.mem_closedBall.mp hx
    calc
      dist y c ≤ dist y x + dist x c := dist_triangle y x c
      _ ≤ 2 * δ + r := add_le_add hyx hxc
      _ ≤ t := by nlinarith [hrt, hgapδ]
  have hpatchU : Metric.ball x (2 * δ) ⊆ U :=
    Metric.ball_subset_closedBall.trans (hpatch.trans (htRball.trans houter))
  have hsourceBall : Metric.closedBall x δ ⊆ U := by
    intro y hy
    have hsmall : y ∈ Metric.closedBall x (2 * δ) := by
      rw [Metric.mem_closedBall] at hy ⊢
      exact hy.trans (by nlinarith [hrad.1])
    exact houter (htRball (hpatch hsmall))
  have hsmooth : ContDiffOn ℝ 2 u (Metric.ball x (2 * δ)) := by
    intro y hy
    have h := hdata.potential_smooth.mono hpatchU y hy
    exact h.of_le (by
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  have huNorm : ∀ y ∈ Metric.ball x (2 * δ), ‖u y‖ ≤ K₀ := by
    intro y hy
    have hb := hdata.potential_bound y (hpatchU hy)
    simpa only [Real.norm_eq_abs] using hb
  have hfinite := smooth_realBallGauge_ne_top hα hU (htRball.trans houter)
    hdata.potential_smooth
  have hHess : ∀ y ∈ Metric.ball x (2 * δ),
      ‖fderiv ℝ (fderiv ℝ u) y‖ ≤ realBallGauge α c t u := by
    intro y hy
    exact SourceInterpolationProofs.realBallHessian_norm_le_bigSourceBall hrt hfinite hx y hy
  have hsource := SourceInterpolationProofs.realBallSource_local_control hsourceBall hdata
  have hcoeffHolder := SourceInterpolationProofs.realBallCoefficientExtension_control hsourceBall
    hdata.coefficient_holder coeff
  have hcoeffNorm := SourceInterpolationProofs.realBallCoefficientExtension_norm_control hsourceBall
    hdata.coefficient_holder coeff
  exact ⟨hrad.1, hsmooth, huNorm, hHess, hsource.1, hsource.2,
    hcoeffHolder, hcoeffNorm⟩

end CalabiYau.Schauder
