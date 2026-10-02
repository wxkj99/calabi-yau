-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Schauder/Cutoff/Elliptic/Ball.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Calculus.Cutoff.Ball
public import CalabiYau.Analysis.Parabolic.Euclidean.Duhamel.Frozen
public import CalabiYau.Analysis.Elliptic.Schauder.Cutoff.Elliptic.Existence
public import CalabiYau.Analysis.Holder.Localization

@[expose] public section


set_option autoImplicit false

noncomputable section

open Real
open scoped ContDiff RealInnerProductSpace

namespace CalabiYau.Schauder

open HeatEquation

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]

def ballCutoffHolderConst (r R : Real) : NNReal :=
  max 2 (Real.toNNReal (ballCutoffFDerivBound r R))

def ballCutoffFDerivHolderConst (r R : Real) : NNReal :=
  max (2 * Real.toNNReal (ballCutoffFDerivBound r R))
    (Real.toNNReal (ballCutoffFDeriv2Bound r R))

omit [FiniteDimensional Real V] in
theorem ballCutoff_holderWith
    {center : V} {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    {alpha : NNReal} (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1) :
    HolderWith (ballCutoffHolderConst r R) alpha
      (ballCutoff center r R) := by
  have hN := ballCutoffFDerivBound_nonneg hr hrR
  have h : HolderWith
      (max (2 * (1 : NNReal))
        (Real.toNNReal (ballCutoffFDerivBound r R))) alpha
      (ballCutoff center r R) := by
    apply holderWith_of_hasFDerivAt_of_norm_le
      (M := (1 : NNReal))
      (N := Real.toNNReal (ballCutoffFDerivBound r R))
      halpha0 halpha1
    · exact hasFDerivAt_ballCutoff center r R
    · intro x
      rw [Real.norm_eq_abs,
        abs_of_nonneg (ballCutoff_mem_Icc center r R x).1]
      exact (ballCutoff_mem_Icc center r R x).2
    · intro x
      rw [Real.coe_toNNReal _ hN]
      exact norm_ballCutoffFDeriv_le hr hrR x
  simpa only [ballCutoffHolderConst, mul_one] using h

omit [FiniteDimensional Real V] in
theorem ballCutoffFDeriv_holderWith
    {center : V} {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    {alpha : NNReal} (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1) :
    HolderWith (ballCutoffFDerivHolderConst r R) alpha
      (ballCutoffFDeriv center r R) := by
  have hM := ballCutoffFDerivBound_nonneg hr hrR
  have hN := ballCutoffFDeriv2Bound_nonneg hr hrR
  apply holderWith_of_hasFDerivAt_of_norm_le
    (M := Real.toNNReal (ballCutoffFDerivBound r R))
    (N := Real.toNNReal (ballCutoffFDeriv2Bound r R))
    halpha0 halpha1
  · exact hasFDerivAt_ballCutoffFDeriv center r R
  · intro x
    rw [Real.coe_toNNReal _ hM]
    exact norm_ballCutoffFDeriv_le hr hrR x
  · intro x
    rw [Real.coe_toNNReal _ hN]
    exact norm_ballCutoffFDeriv2_le hr hrR x

def ballCutoffBoundedContinuousFunction
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R) :
    BoundedContinuousFunction V Real :=
  compactSupportBoundedContinuousFunction (ballCutoff center r R)
    (ballCutoff_contDiff center r R).continuous
    (ballCutoff_hasCompactSupport hr hrR)

def ballCutoffFDerivBoundedContinuousFunction
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R) :
    BoundedContinuousFunction V (V →L[Real] Real) :=
  compactSupportBoundedContinuousFunction (ballCutoffFDeriv center r R)
    (ballCutoffFDeriv_contDiff center r R).continuous
    (ballCutoffFDeriv_hasCompactSupport hr hrR)

def ballCutoffFDeriv2BoundedContinuousFunction
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R) :
    BoundedContinuousFunction V (V →L[Real] V →L[Real] Real) :=
  compactSupportBoundedContinuousFunction (ballCutoffFDeriv2 center r R)
    (ballCutoffFDeriv2_contDiff center r R).continuous
    (ballCutoffFDeriv2_hasCompactSupport hr hrR)

@[simp]
theorem ballCutoffBoundedContinuousFunction_apply
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R) (x : V) :
    ballCutoffBoundedContinuousFunction center hr hrR x = ballCutoff center r R x := rfl

@[simp]
theorem ballCutoffFDerivBoundedContinuousFunction_apply
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R) (x : V) :
    ballCutoffFDerivBoundedContinuousFunction center hr hrR x =
      ballCutoffFDeriv center r R x := rfl

@[simp]
theorem ballCutoffFDeriv2BoundedContinuousFunction_apply
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R) (x : V) :
    ballCutoffFDeriv2BoundedContinuousFunction center hr hrR x =
      ballCutoffFDeriv2 center r R x := rfl


end CalabiYau.Schauder

end
