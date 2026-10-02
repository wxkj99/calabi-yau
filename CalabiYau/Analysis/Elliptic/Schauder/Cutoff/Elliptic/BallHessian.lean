-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Schauder/Cutoff/Elliptic/BallHessian.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Schauder.Cutoff.Elliptic.Ball

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open Real
open scoped ContDiff NNReal RealInnerProductSpace

namespace CalabiYau.Schauder

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]

private abbrev Hess (V : Type*) [NormedAddCommGroup V] [NormedSpace Real V] :=
  V →L[Real] V →L[Real] Real

private abbrev Third (V : Type*) [NormedAddCommGroup V] [NormedSpace Real V] :=
  V →L[Real] Hess V

local instance : NormedAddCommGroup (Hess V) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance : NormedSpace Real (Hess V) :=
  ContinuousLinearMap.toNormedSpace

local instance : NormedAddCommGroup (Third V) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance : NormedSpace Real (Third V) :=
  ContinuousLinearMap.toNormedSpace

def ballCutoffFDeriv3BoundedContinuousFunction
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R) :
    BoundedContinuousFunction V (Third V) :=
  compactSupportBoundedContinuousFunction
    (fderiv Real (ballCutoffFDeriv2 center r R))
    (by
      exact ((ballCutoffFDeriv2_contDiff center r R).fderiv_right
        (m := ∞) (by simp)).continuous)
    ((ballCutoffFDeriv2_hasCompactSupport hr hrR).fderiv Real)

@[simp]
theorem ballCutoffFDeriv3BoundedContinuousFunction_apply
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R) (x : V) :
    ballCutoffFDeriv3BoundedContinuousFunction center hr hrR x =
      fderiv Real (ballCutoffFDeriv2 center r R) x := rfl

def ballCutoffFDeriv2HolderConst
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R) : NNReal :=
  max (2 * Real.toNNReal (ballCutoffFDeriv2Bound r R))
    ‖ballCutoffFDeriv3BoundedContinuousFunction center hr hrR‖₊

theorem ballCutoffFDeriv2_holderWith
    {center : V} {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    {alpha : NNReal} (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1) :
    HolderWith (ballCutoffFDeriv2HolderConst center hr hrR) alpha
      (ballCutoffFDeriv2 center r R) := by
  let d3chi := ballCutoffFDeriv3BoundedContinuousFunction center hr hrR
  have hd2chi : ∀ x, HasFDerivAt (ballCutoffFDeriv2 center r R)
      (d3chi x) x := by
    intro x
    change HasFDerivAt (ballCutoffFDeriv2 center r R)
      (fderiv Real (ballCutoffFDeriv2 center r R) x) x
    exact ((ballCutoffFDeriv2_contDiff center r R).differentiable
      (by simp) x).hasFDerivAt
  apply holderWith_of_hasFDerivAt_of_norm_le
    (M := Real.toNNReal (ballCutoffFDeriv2Bound r R))
    (N := ‖d3chi‖₊) halpha0 halpha1 hd2chi
  · intro x
    rw [Real.coe_toNNReal _ (ballCutoffFDeriv2Bound_nonneg hr hrR)]
    exact norm_ballCutoffFDeriv2_le hr hrR x
  · exact fun x ↦ by simpa using d3chi.norm_coe_le_norm x

end CalabiYau.Schauder

end
