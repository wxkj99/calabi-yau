module

public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.ComplexSmoothBall.Basic
public import CalabiYau.Analysis.Elliptic.Schauder.Cutoff.Elliptic.BallHessian

/-!
# Constants for canonical cutoff-source interpolation

The localization and lower-jet absorption follow Constantin, *Schauder Estimates*,
equation (9), p. 7, and pp. 8–9. The explicit profile constants below belong to the
repository's canonical cutoff, not to an asserted optimal textbook normalization.
-/

@[expose] public section

open scoped NNReal ContDiff Topology

namespace CalabiYau.Schauder

noncomputable section

def realBallSourceScale (δ : ℝ) : ℝ≥0 := 1 + (Real.toNNReal δ)⁻¹

def realBallCutoffScalarProfileConst : ℝ≥0 :=
  Real.toNNReal (max 2 (8 / 3 * CutoffProfile.derivBound))

def realBallCutoffLowerProfileConst : ℝ≥0 :=
  Real.toNNReal (max (16 / 3 * CutoffProfile.derivBound)
    (88 / 9 * CutoffProfile.derivBound))

def realBallCutoffSecondSupProfileConst : ℝ≥0 :=
  Real.toNNReal (88 / 9 * CutoffProfile.derivBound)

def realBallCutoffThirdProfileConst : ℝ≥0 :=
  Real.toNNReal (64 / 3 * CutoffProfile.derivBound +
    512 / 27 * CutoffProfile.deriv3Bound)

def realBallCutoffSecondHolderProfileConst : ℝ≥0 :=
  max (2 * realBallCutoffSecondSupProfileConst) realBallCutoffThirdProfileConst

def realBallCutoffPatchProfileConst (α : ℝ≥0) : ℝ≥0 :=
  4 + 2 * (4 : ℝ≥0) ^ (α : ℝ)

def realBallSourcePairCount (n : ℕ) : ℝ≥0 :=
  (Fintype.card (Fin n × Fin 2) : ℝ≥0) ^ 2

def realBallSourceMasterConst (n : ℕ) (α K M : ℝ≥0) : ℝ≥0 :=
  M * realBallCutoffPatchProfileConst α *
    (realBallCutoffScalarProfileConst + 3 + realBallSourcePairCount n * K *
      (realBallCutoffSecondHolderProfileConst + 8 * realBallCutoffLowerProfileConst))

/-- The actual double-sum constant, retaining both coefficient-Hölder contributions. -/
def realBallSourceCommutatorHolderConst (n : ℕ)
    (K K₀ G V W Kχ Mχ Kχ₂ Mχ₂ : ℝ≥0) : ℝ≥0 :=
  ∑ _i : Fin n × Fin 2, ∑ _j : Fin n × Fin 2,
    (2 * (K * (G * Kχ + Mχ * W) + (G * Mχ) * K) +
      (K * (K₀ * Kχ₂ + Mχ₂ * V) + (K₀ * Mχ₂) * K))

def realBallLowerGradientBound (K₀ H eps₁ : ℝ≥0) : ℝ≥0 :=
  2 * K₀ / eps₁ + H * eps₁

def realBallLowerValueHolderBound (α K₀ G eps₂ : ℝ≥0) : ℝ≥0 :=
  G * eps₂ ^ ((1 : ℝ≥0) - α : ℝ) + 2 * K₀ / eps₂ ^ (α : ℝ)

def realBallLowerGradientHolderBound (α H G eps₂ : ℝ≥0) : ℝ≥0 :=
  H * eps₂ ^ ((1 : ℝ≥0) - α : ℝ) + 2 * G / eps₂ ^ (α : ℝ)

/-- The two gradient terms are separate; no symmetry of the coefficients is assumed. -/
def realBallCutoffCommutator {n : ℕ} {x : RealBallModel n} {δ : ℝ}
    {a : RealBallModel n → Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ}
    (coeff : RealBallCoefficientExtension a x δ) (u : RealBallModel n → ℝ) :
    RealBallModel n → ℝ := fun y =>
  ∑ i : Fin n × Fin 2, ∑ j : Fin n × Fin 2,
    ((coeff.coefficient i j y * ballCutoffFDeriv x (δ / 2) δ y
      (EuclideanSpace.basisFun (Fin n × Fin 2) ℝ i)) * fderiv ℝ u y
        (EuclideanSpace.basisFun (Fin n × Fin 2) ℝ j) +
      (coeff.coefficient i j y * ballCutoffFDeriv x (δ / 2) δ y
        (EuclideanSpace.basisFun (Fin n × Fin 2) ℝ j)) * fderiv ℝ u y
          (EuclideanSpace.basisFun (Fin n × Fin 2) ℝ i) +
      (coeff.coefficient i j y * ballCutoffFDeriv2 x (δ / 2) δ y
        (EuclideanSpace.basisFun (Fin n × Fin 2) ℝ i)
        (EuclideanSpace.basisFun (Fin n × Fin 2) ℝ j)) * u y)

/-- Three quadratic-argument chain-rule terms, with the same argument order as D²χ. -/
def realBallCutoffThirdTensor {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (center : E) (δ : ℝ) (y : E) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  let a₂ := deriv (deriv CutoffProfile.value) (ballCutoffArgument center (δ / 2) δ y)
  let p := ballCutoffArgumentFDeriv center (δ / 2) δ
  let Q := ballCutoffArgumentFDeriv2 (E := E) (δ / 2) δ
  let c₃ := deriv (deriv (deriv CutoffProfile.value))
    (ballCutoffArgument center (δ / 2) δ y)
  let B := ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)
  (a₂ • p y).smulRight Q + B.precompR E (a₂ • p y) Q +
    B.precompL E (a₂ • Q + (c₃ • p y).smulRight (p y)) (p y)

end

end CalabiYau.Schauder
