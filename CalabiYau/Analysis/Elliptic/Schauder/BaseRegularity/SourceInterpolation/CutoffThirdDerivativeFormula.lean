module

public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.SourceInterpolation.Basic

/-!
# Canonical cutoff third-derivative tensor

This is the chain-rule infrastructure for the smooth-cutoff localization in
Constantin, *Schauder Estimates*, p. 8. The exact tensor belongs to the canonical
repository cutoff and is not quoted as a textbook normalization.
-/

@[expose] public section

open scoped NNReal ContDiff Topology

namespace CalabiYau.Schauder

/-- The exact three-term tensor formula for the canonical D³χ BCF.
There is no nontriviality assumption: the zero-dimensional space is allowed.
The inner quadratic argument has zero third derivative, but the profile does not.
The three mixed terms must all remain, even when tested in one dimension. -/
theorem realBallCutoffThirdDerivative_formula
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (center : E) {δ : ℝ} (hδ : 0 < δ) (y : E) :
    ballCutoffFDeriv3BoundedContinuousFunction center
      (show 0 ≤ δ / 2 by positivity) (by linarith : δ / 2 < δ) y =
        realBallCutoffThirdTensor center δ y := by
  rw [ballCutoffFDeriv3BoundedContinuousFunction_apply]
  let r : ℝ := δ / 2
  let R : ℝ := δ
  let a (z : E) := ballCutoffArgument center r R z
  let p (z : E) : E →L[ℝ] ℝ := ballCutoffArgumentFDeriv center r R z
  let Q : E →L[ℝ] E →L[ℝ] ℝ := ballCutoffArgumentFDeriv2 r R
  let B := ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)
  let a₁ (z : E) := deriv CutoffProfile.value (a z)
  let a₂ (z : E) := deriv (deriv CutoffProfile.value) (a z)
  let c₃ (z : E) := deriv (deriv (deriv CutoffProfile.value)) (a z)
  have hle3 : (3 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
    have h : ((3 : ℕ∞) : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
      exact_mod_cast (le_top : (3 : ℕ∞) ≤ ⊤)
    exact h
  have hle2 : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
    have h : ((2 : ℕ∞) : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
      exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
    exact h
  have harg : HasFDerivAt (a) (p y) y := by
    simpa only [a, p, r, R] using
      hasFDerivAt_ballCutoffArgument center (δ / 2) δ y
  have hp : HasFDerivAt (p) Q y := by
    simpa only [p, Q, r, R] using
      hasFDerivAt_ballCutoffArgumentFDeriv center (δ / 2) δ y
  have hC2 : ContDiff ℝ (2 : WithTop ℕ∞) CutoffProfile.value :=
    CutoffProfile.contDiff.of_le hle2
  have hprofile2 : HasDerivAt (deriv CutoffProfile.value)
      (deriv (deriv CutoffProfile.value) (a y)) (a y) := by
    exact hC2.deriv' (n := 1) |>.differentiable (by simp) (a y) |>.hasDerivAt
  have ha₁ : HasFDerivAt a₁ (a₂ y • p y) y := by
    simpa only [a₁, a₂, Function.comp_def] using
      hprofile2.comp_hasFDerivAt y harg
  have hprofile3 : HasDerivAt (deriv (deriv CutoffProfile.value))
      (deriv (deriv (deriv CutoffProfile.value)) (a y)) (a y) :=
    ((CutoffProfile.contDiff.of_le hle3).deriv' (n := 2)).deriv' (n := 1)
      |>.differentiable (by simp) (a y) |>.hasDerivAt
  have ha₂ : HasFDerivAt a₂ (c₃ y • p y) y := by
    simpa only [a₂, c₃, Function.comp_def] using
      hprofile3.comp_hasFDerivAt y harg
  have hfirst := ha₁.smul_const Q
  have hinner := ha₂.smul hp
  have houter := B.hasFDerivAt_of_bilinear hinner hp
  have hresult := hfirst.add houter
  have hfun :
      (fun z : E => a₁ z • Q + B (a₂ z • p z) (p z)) =
        ballCutoffFDeriv2 center r R := by
    funext z
    ext v w
    simp [ballCutoffFDeriv2, a₁, a₂, p, Q, B]
    ring
  have hresult' : HasFDerivAt (ballCutoffFDeriv2 center r R)
      ((a₂ y • p y).smulRight Q +
        (((ContinuousLinearMap.precompR E B) (a₂ y • p y)) Q +
          ((ContinuousLinearMap.precompL E B)
            (a₂ y • Q + (c₃ y • p y).smulRight (p y))) (p y))) y := by
    rw [← hfun]
    change HasFDerivAt
      ((fun z : E => a₁ z • Q) + fun z : E => B (a₂ z • p z) (p z))
      _ y
    exact hresult
  convert hresult'.fderiv using 1
  · ext v w
    simp [realBallCutoffThirdTensor, B, a, p, Q, a₂, c₃, r, R]
    ring

end CalabiYau.Schauder
