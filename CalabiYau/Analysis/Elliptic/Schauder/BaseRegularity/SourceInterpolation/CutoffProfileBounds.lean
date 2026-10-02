module

public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.SourceInterpolation.CutoffLowerOrderBounds
public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.SourceInterpolation.CutoffThirdDerivativeFormula
public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.SourceInterpolation.CutoffThirdDerivativeNorm

/-!
# Certified assembly of the canonical cutoff majorants

Source: Constantin, *Schauder Estimates*, smooth-cutoff localization p. 8.
The third-derivative formula, its norm estimate, and all lower-order bounds are
separate estimates. Together they imply the stated bounds.
-/

@[expose] public section

open scoped NNReal ContDiff Topology

namespace CalabiYau.Schauder

/-- All six canonical cutoff majorants.
In particular Kχ₂ uses H₂ while Mχ₂ uses Cχ. -/
theorem realBallCutoffProfile_bounds
    {n : ℕ} (x : RealBallModel n) (α : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    let hr : 0 ≤ δ / 2 := by positivity
    let hrR : δ / 2 < δ := by linarith
    let q := realBallSourceScale δ
    ballCutoffHolderConst (δ / 2) δ ≤ realBallCutoffScalarProfileConst * q ∧
    ballCutoffFDerivHolderConst (δ / 2) δ ≤
      realBallCutoffLowerProfileConst * q ^ (3 : ℕ) ∧
    ‖ballCutoffFDerivBoundedContinuousFunction x hr hrR‖₊ ≤
      realBallCutoffLowerProfileConst * q ^ (3 : ℕ) ∧
    ballCutoffFDeriv2HolderConst x hr hrR ≤
      realBallCutoffSecondHolderProfileConst * q ^ (3 : ℕ) ∧
    ‖ballCutoffFDeriv2BoundedContinuousFunction x hr hrR‖₊ ≤
      realBallCutoffLowerProfileConst * q ^ (3 : ℕ) ∧
    realBallPatchFactor α δ ≤ realBallCutoffPatchProfileConst α * q ^ (α : ℝ) := by
  obtain ⟨hχv, hχ, hMχ, hMχ₂, hraw, hpatch⟩ :=
    realBallCutoffLowerOrder_bounds x α hδ
  have hthird := realBallCutoffThirdDerivative_norm_bound x hδ
    (fun y => realBallCutoffThirdDerivative_formula x hδ y)
  have hsecond : ballCutoffFDeriv2HolderConst x
      (show 0 ≤ δ / 2 by positivity) (by linarith : δ / 2 < δ) ≤
      realBallCutoffSecondHolderProfileConst * realBallSourceScale δ ^ (3 : ℕ) := by
    rw [ballCutoffFDeriv2HolderConst, realBallCutoffSecondHolderProfileConst]
    apply max_le
    · calc
        2 * Real.toNNReal (ballCutoffFDeriv2Bound (δ / 2) δ) ≤
            2 * (realBallCutoffSecondSupProfileConst * realBallSourceScale δ ^ (3 : ℕ)) :=
          mul_le_mul_of_nonneg_left hraw (by positivity)
        _ = (2 * realBallCutoffSecondSupProfileConst) *
            realBallSourceScale δ ^ (3 : ℕ) := by ring
        _ ≤ max (2 * realBallCutoffSecondSupProfileConst) realBallCutoffThirdProfileConst *
            realBallSourceScale δ ^ (3 : ℕ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    · exact hthird.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  exact ⟨hχv, hχ, hMχ, hsecond, hMχ₂, hpatch⟩

end CalabiYau.Schauder
