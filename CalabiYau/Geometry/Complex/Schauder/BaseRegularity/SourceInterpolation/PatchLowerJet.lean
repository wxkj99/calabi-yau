module

public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.SourceInterpolation.Basic
public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.SourceInterpolationProofs.LowerJet

/-!
# Lower-jet controls on a doubled source patch

Source: Constantin, Schauder Estimates, intermediate interpolation p. 8 and
segment gradient estimate p. 9. The two epsilon scales are independent.
-/

@[expose] public section

open scoped NNReal ContDiff Topology

namespace CalabiYau.Schauder

/-- The strict doubled-ball buffer follows from eps₁ ≤ δ/2, not eps₂ ≤ eps₁. -/
theorem realBallSource_patch_lower_jet
    {n : ℕ} {α K₀ H : ℝ≥0} {x : RealBallModel n} {δ : ℝ}
    {u : RealBallModel n → ℝ}
    (hα : α < 1) (hδ : 0 < δ)
    (eps₁ eps₂ : ℝ≥0) (heps₁ : 0 < eps₁) (heps₂ : 0 < eps₂)
    (hbuffer : eps₁ ≤ Real.toNNReal δ / 2)
    (hsmooth : ContDiffOn ℝ 2 u (Metric.ball x (2 * δ)))
    (hu : ∀ y ∈ Metric.ball x (2 * δ), ‖u y‖ ≤ K₀)
    (hsecond : ∀ y ∈ Metric.ball x (2 * δ), ‖fderiv ℝ (fderiv ℝ u) y‖ ≤ H) :
    let G := realBallLowerGradientBound K₀ H eps₁
    let V := realBallLowerValueHolderBound α K₀ G eps₂
    let W := realBallLowerGradientHolderBound α H G eps₂
    (∀ y ∈ Metric.ball x δ, ‖fderiv ℝ u y‖ ≤ G) ∧
      HolderWith V α ((Metric.ball x δ).domRestrict u) ∧
      HolderWith W α ((Metric.ball x δ).domRestrict (fderiv ℝ u)) := by
  dsimp
  have heps₁R : (eps₁ : ℝ) ≤ δ / 2 := by
    have hbufferR : (eps₁ : ℝ) ≤ (Real.toNNReal δ : ℝ) / 2 := by
      exact_mod_cast hbuffer
    rw [Real.coe_toNNReal δ (le_of_lt hδ)] at hbufferR
    exact hbufferR
  have hbuffer' : δ + (eps₁ : ℝ) < 2 * δ := by linarith
  have hinterp := SourceInterpolationProofs.realBallLowerJet_interpolation
    (c := x) (r := δ) (R := 2 * δ) (M := K₀) (H := H) (u := u)
    hα eps₁ eps₂ heps₁ heps₂ hbuffer' hsmooth hu hsecond
  rcases hinterp with ⟨hgrad, hgradHolder, hvalueHolder⟩
  have hball : Metric.ball x δ ⊆ Metric.closedBall x δ := Metric.ball_subset_closedBall
  have hvalue : HolderWith
      (realBallLowerValueHolderBound α K₀
        (realBallLowerGradientBound K₀ H eps₁) eps₂) α
      ((Metric.ball x δ).domRestrict u) :=
    ((HolderWith.restrict_iff.mp hvalueHolder).mono hball).holderWith
  have hgradient : HolderWith
      (realBallLowerGradientHolderBound α H
        (realBallLowerGradientBound K₀ H eps₁) eps₂) α
      ((Metric.ball x δ).domRestrict (fderiv ℝ u)) :=
    ((HolderWith.restrict_iff.mp hgradHolder).mono hball).holderWith
  exact ⟨fun y hy => hgrad y (Metric.ball_subset_closedBall hy), hvalue, hgradient⟩

end CalabiYau.Schauder
