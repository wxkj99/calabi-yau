-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Schauder/Holder/Scaling.lean
-- Locally modified.
module
public import CalabiYau.Mathlib.Analysis.Holder.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

@[expose] public section

-- and its private helpers occur in public declarations.

noncomputable section

open Set
open scoped NNReal

namespace CalabiYau.Schauder

def parabolicDilation {V : Type*} [SMul Real V]
    (r : NNReal) (p : ParabolicPoint V) : ParabolicPoint V :=
  parabolicPoint ((r : Real) ^ 2 * p.time) ((r : Real) • p.space)

def parabolicTranslation {V : Type*} [Add V]
    (p0 p : ParabolicPoint V) : ParabolicPoint V :=
  parabolicPoint (p0.time + p.time) (p0.space + p.space)

def parabolicDilationAt {V : Type*} [Add V] [SMul Real V]
    (r : NNReal) (p0 p : ParabolicPoint V) : ParabolicPoint V :=
  parabolicTranslation p0 (parabolicDilation r p)

def parabolicTimeCenteredDilationAt {V : Type*} [Add V] [SMul Real V]
    (tau : Real) (r : NNReal) (p0 p : ParabolicPoint V) :
    ParabolicPoint V :=
  parabolicDilationAt r p0 (parabolicPoint (p.time - tau) p.space)

def parabolicInverseDilationAt {V : Type*} [AddGroup V] [SMul Real V]
    (r : NNReal) (p0 p : ParabolicPoint V) : ParabolicPoint V :=
  parabolicPoint ((p.time - p0.time) / (r : Real) ^ 2)
    ((r : Real)⁻¹ • (p.space - p0.space))

@[simp]
theorem parabolicDilation_time {V : Type*} [SMul Real V]
    (r : NNReal) (p : ParabolicPoint V) :
    (parabolicDilation r p).time = (r : Real) ^ 2 * p.time := rfl

@[simp]
theorem parabolicDilation_space {V : Type*} [SMul Real V]
    (r : NNReal) (p : ParabolicPoint V) :
    (parabolicDilation r p).space = (r : Real) • p.space := rfl

@[simp]
theorem parabolicTranslation_time {V : Type*} [Add V]
    (p0 p : ParabolicPoint V) :
    (parabolicTranslation p0 p).time = p0.time + p.time := rfl

@[simp]
theorem parabolicTranslation_space {V : Type*} [Add V]
    (p0 p : ParabolicPoint V) :
    (parabolicTranslation p0 p).space = p0.space + p.space := rfl

@[simp]
theorem parabolicDilationAt_time {V : Type*} [Add V] [SMul Real V]
    (r : NNReal) (p0 p : ParabolicPoint V) :
    (parabolicDilationAt r p0 p).time =
      p0.time + (r : Real) ^ 2 * p.time := rfl

@[simp]
theorem parabolicDilationAt_space {V : Type*} [Add V] [SMul Real V]
    (r : NNReal) (p0 p : ParabolicPoint V) :
    (parabolicDilationAt r p0 p).space =
      p0.space + (r : Real) • p.space := rfl

@[simp]
theorem parabolicTimeCenteredDilationAt_time
    {V : Type*} [Add V] [SMul Real V]
    (tau : Real) (r : NNReal) (p0 p : ParabolicPoint V) :
    (parabolicTimeCenteredDilationAt tau r p0 p).time =
      p0.time + (r : Real) ^ 2 * (p.time - tau) :=
  rfl

@[simp]
theorem parabolicTimeCenteredDilationAt_space
    {V : Type*} [Add V] [SMul Real V]
    (tau : Real) (r : NNReal) (p0 p : ParabolicPoint V) :
    (parabolicTimeCenteredDilationAt tau r p0 p).space =
      p0.space + (r : Real) • p.space :=
  rfl

@[simp]
theorem parabolicTimeCenteredDilationAt_center
    {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    (tau : Real) (r : NNReal) (p0 : ParabolicPoint V) :
    parabolicTimeCenteredDilationAt tau r p0
        (parabolicPoint tau 0) = p0 := by
  rw [← parabolicPoint_time_space p0]
  apply Prod.ext
  · apply Metric.Snowflaking.ext
    change p0.time + (r : Real) ^ 2 * (tau - tau) = p0.time
    ring
  · change p0.space + (r : Real) • (0 : V) = p0.space
    simp

@[simp]
theorem parabolicInverseDilationAt_time
    {V : Type*} [AddGroup V] [SMul Real V]
    (r : NNReal) (p0 p : ParabolicPoint V) :
    (parabolicInverseDilationAt r p0 p).time =
      (p.time - p0.time) / (r : Real) ^ 2 := rfl

@[simp]
theorem parabolicInverseDilationAt_space
    {V : Type*} [AddGroup V] [SMul Real V]
    (r : NNReal) (p0 p : ParabolicPoint V) :
    (parabolicInverseDilationAt r p0 p).space =
      (r : Real)⁻¹ • (p.space - p0.space) := rfl

@[simp]
theorem parabolicDilation_zero {V : Type*} [NormedAddCommGroup V]
    [NormedSpace Real V] (p : ParabolicPoint V) :
    parabolicDilation 0 p = parabolicPoint 0 0 := by
  rcases p with ⟨⟨t⟩, x⟩
  apply Prod.ext
  · apply Metric.Snowflaking.ext
    change (0 : Real) ^ 2 * t = 0
    norm_num
  · change (0 : Real) • x = 0
    simp

@[simp]
theorem parabolicDilation_one {V : Type*} [NormedAddCommGroup V]
    [NormedSpace Real V] (p : ParabolicPoint V) :
    parabolicDilation 1 p = p := by
  rcases p with ⟨⟨t⟩, x⟩
  apply Prod.ext
  · apply Metric.Snowflaking.ext
    change (1 : Real) ^ 2 * t = t
    ring
  · change (1 : Real) • x = x
    simp

@[simp]
theorem parabolicDilationAt_origin {V : Type*} [NormedAddCommGroup V]
    [NormedSpace Real V] (r : NNReal) (p0 : ParabolicPoint V) :
    parabolicDilationAt r p0 (parabolicPoint 0 0) = p0 := by
  rw [← parabolicPoint_time_space p0]
  simp [parabolicDilationAt, parabolicTranslation, parabolicDilation]

@[simp]
theorem parabolicDilationAt_inverseDilationAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    (r : NNReal) (hr : 0 < r) (p0 p : ParabolicPoint V) :
    parabolicDilationAt r p0 (parabolicInverseDilationAt r p0 p) = p := by
  rcases p0 with ⟨⟨t0⟩, x0⟩
  rcases p with ⟨⟨t⟩, x⟩
  apply Prod.ext
  · apply Metric.Snowflaking.ext
    change t0 + (r : Real) ^ 2 * ((t - t0) / (r : Real) ^ 2) = t
    field_simp
    ring
  · change x0 + (r : Real) • ((r : Real)⁻¹ • (x - x0)) = x
    rw [smul_smul]
    simp [hr.ne']

@[simp]
theorem parabolicInverseDilationAt_dilationAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    (r : NNReal) (hr : 0 < r) (p0 p : ParabolicPoint V) :
    parabolicInverseDilationAt r p0 (parabolicDilationAt r p0 p) = p := by
  rcases p0 with ⟨⟨t0⟩, x0⟩
  rcases p with ⟨⟨t⟩, x⟩
  apply Prod.ext
  · apply Metric.Snowflaking.ext
    change (t0 + (r : Real) ^ 2 * t - t0) / (r : Real) ^ 2 = t
    field_simp
    ring
  · change (r : Real)⁻¹ • (x0 + (r : Real) • x - x0) = x
    simp [hr.ne']

@[simp]
theorem parabolicInverseDilationAt_center
    {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    (r : NNReal) (p0 : ParabolicPoint V) :
    parabolicInverseDilationAt r p0 p0 = parabolicPoint 0 0 := by
  rcases p0 with ⟨⟨t0⟩, x0⟩
  apply Prod.ext
  · apply Metric.Snowflaking.ext
    change (t0 - t0) / (r : Real) ^ 2 = 0
    simp
  · change (r : Real)⁻¹ • (x0 - x0) = 0
    simp

theorem parabolicDilationAt_inverse_eq_inverseDilationAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    (r : NNReal) (hr : 0 < r) (p0 p : ParabolicPoint V) :
    parabolicDilationAt r⁻¹
        (parabolicInverseDilationAt r p0 (parabolicPoint 0 0)) p =
      parabolicInverseDilationAt r p0 p := by
  rcases p0 with ⟨⟨t0⟩, x0⟩
  rcases p with ⟨⟨t⟩, x⟩
  apply Prod.ext
  · apply Metric.Snowflaking.ext
    change (0 - t0) / (r : Real) ^ 2 +
      ((r⁻¹ : NNReal) : Real) ^ 2 * t =
        (t - t0) / (r : Real) ^ 2
    simp only [NNReal.coe_inv]
    field_simp
    ring
  · change (r : Real)⁻¹ • (0 - x0) +
      ((r⁻¹ : NNReal) : Real) • x =
        (r : Real)⁻¹ • (x - x0)
    simp only [NNReal.coe_inv, zero_sub, smul_neg, smul_sub]
    abel

def parabolicRescale {V F : Type*} [SMul Real V]
    (r : NNReal) (u : Real → V → F) : Real → V → F :=
  fun t x ↦ u ((r : Real) ^ 2 * t) ((r : Real) • x)

def parabolicRescaleAt {V F : Type*} [Add V] [SMul Real V]
    (r : NNReal) (p0 : ParabolicPoint V) (u : Real → V → F) :
    Real → V → F :=
  fun t x ↦ u (p0.time + (r : Real) ^ 2 * t)
    (p0.space + (r : Real) • x)

def parabolicSpatialAffineContinuousMap
    {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    (r : NNReal) (p0 : ParabolicPoint V) : C(V, V) :=
  ⟨fun x ↦ p0.space + (r : Real) • x,
    continuous_const.add (continuous_id.const_smul (r : Real))⟩

def boundedContinuousFunctionConstSMul
    {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (c : Real) (f : BoundedContinuousFunction X F) :
    BoundedContinuousFunction X F :=
  f.comp (fun y ↦ c • y)
    ((c • ContinuousLinearMap.id Real F).lipschitzWith)

@[simp]
private theorem boundedContinuousFunctionConstSMul_apply
    {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (c : Real) (f : BoundedContinuousFunction X F) (x : X) :
    boundedContinuousFunctionConstSMul c f x = c • f x :=
  rfl

namespace BoundedContinuousFunction

def parabolicRescaleAt
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup F]
    (r : NNReal) (p0 : ParabolicPoint V)
    (u : Real → BoundedContinuousFunction V F) :
    Real → BoundedContinuousFunction V F :=
  fun t ↦ (u (p0.time + (r : Real) ^ 2 * t)).compContinuous
    (parabolicSpatialAffineContinuousMap r p0)

def parabolicTimeDerivativeRescaleAt
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (r : NNReal) (p0 : ParabolicPoint V)
    (dtimeU : Real → BoundedContinuousFunction V F) :
    Real → BoundedContinuousFunction V F :=
  fun t ↦ boundedContinuousFunctionConstSMul ((r : Real) ^ 2)
    (parabolicRescaleAt r p0 dtimeU t)

def parabolicSpatialDerivativeRescaleAt
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (r : NNReal) (p0 : ParabolicPoint V)
    (du : Real → BoundedContinuousFunction V (V →L[Real] F)) :
    Real → BoundedContinuousFunction V (V →L[Real] F) :=
  fun t ↦ boundedContinuousFunctionConstSMul (r : Real)
    (parabolicRescaleAt r p0 du t)

def parabolicSpatialSecondDerivativeRescaleAt
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (r : NNReal) (p0 : ParabolicPoint V)
    (d2u : Real → BoundedContinuousFunction V
      (V →L[Real] V →L[Real] F)) :
    Real → BoundedContinuousFunction V (V →L[Real] V →L[Real] F) :=
  fun t ↦ boundedContinuousFunctionConstSMul ((r : Real) ^ 2)
    (parabolicRescaleAt (V := V) (F := V →L[Real] V →L[Real] F)
      r p0 d2u t)

def parabolicTimeCenteredRescaleAt
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup F]
    (tau : Real) (r : NNReal) (p0 : ParabolicPoint V)
    (u : Real → BoundedContinuousFunction V F) :
    Real → BoundedContinuousFunction V F :=
  fun t ↦ parabolicRescaleAt r p0 u (t - tau)

def parabolicTimeCenteredTimeDerivativeRescaleAt
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (tau : Real) (r : NNReal) (p0 : ParabolicPoint V)
    (dtimeU : Real → BoundedContinuousFunction V F) :
    Real → BoundedContinuousFunction V F :=
  fun t ↦ parabolicTimeDerivativeRescaleAt r p0 dtimeU (t - tau)

def parabolicTimeCenteredSpatialDerivativeRescaleAt
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (tau : Real) (r : NNReal) (p0 : ParabolicPoint V)
    (du : Real → BoundedContinuousFunction V (V →L[Real] F)) :
    Real → BoundedContinuousFunction V (V →L[Real] F) :=
  fun t ↦ parabolicSpatialDerivativeRescaleAt r p0 du (t - tau)

def parabolicTimeCenteredSpatialSecondDerivativeRescaleAt
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (tau : Real) (r : NNReal) (p0 : ParabolicPoint V)
    (d2u : Real → BoundedContinuousFunction V
      (V →L[Real] V →L[Real] F)) :
    Real → BoundedContinuousFunction V (V →L[Real] V →L[Real] F) :=
  fun t ↦ parabolicSpatialSecondDerivativeRescaleAt r p0 d2u (t - tau)

@[simp]
theorem parabolicRescaleAt_apply
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup F]
    (r : NNReal) (p0 : ParabolicPoint V)
    (u : Real → BoundedContinuousFunction V F) (t : Real) (x : V) :
    parabolicRescaleAt r p0 u t x =
      u (p0.time + (r : Real) ^ 2 * t)
        (p0.space + (r : Real) • x) :=
  rfl

@[simp]
theorem parabolicTimeDerivativeRescaleAt_apply
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (r : NNReal) (p0 : ParabolicPoint V)
    (dtimeU : Real → BoundedContinuousFunction V F) (t : Real) (x : V) :
    parabolicTimeDerivativeRescaleAt r p0 dtimeU t x =
      (r : Real) ^ 2 • dtimeU
        (p0.time + (r : Real) ^ 2 * t)
        (p0.space + (r : Real) • x) :=
  rfl

@[simp]
theorem parabolicSpatialDerivativeRescaleAt_apply
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (r : NNReal) (p0 : ParabolicPoint V)
    (du : Real → BoundedContinuousFunction V (V →L[Real] F))
    (t : Real) (x : V) :
    parabolicSpatialDerivativeRescaleAt r p0 du t x =
      (r : Real) • du (p0.time + (r : Real) ^ 2 * t)
        (p0.space + (r : Real) • x) :=
  rfl

@[simp]
theorem parabolicSpatialSecondDerivativeRescaleAt_apply
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (r : NNReal) (p0 : ParabolicPoint V)
    (d2u : Real → BoundedContinuousFunction V
      (V →L[Real] V →L[Real] F)) (t : Real) (x : V) :
    parabolicSpatialSecondDerivativeRescaleAt r p0 d2u t x =
      (r : Real) ^ 2 • d2u (p0.time + (r : Real) ^ 2 * t)
        (p0.space + (r : Real) • x) :=
  rfl

@[simp]
theorem parabolicTimeCenteredRescaleAt_apply
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup F]
    (tau : Real) (r : NNReal) (p0 : ParabolicPoint V)
    (u : Real → BoundedContinuousFunction V F) (t : Real) (x : V) :
    parabolicTimeCenteredRescaleAt tau r p0 u t x =
      u (p0.time + (r : Real) ^ 2 * (t - tau))
        (p0.space + (r : Real) • x) :=
  rfl

@[simp]
theorem parabolicTimeCenteredTimeDerivativeRescaleAt_apply
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (tau : Real) (r : NNReal) (p0 : ParabolicPoint V)
    (dtimeU : Real → BoundedContinuousFunction V F)
    (t : Real) (x : V) :
    parabolicTimeCenteredTimeDerivativeRescaleAt
        tau r p0 dtimeU t x =
      (r : Real) ^ 2 •
        dtimeU (p0.time + (r : Real) ^ 2 * (t - tau))
          (p0.space + (r : Real) • x) :=
  rfl

@[simp]
theorem parabolicTimeCenteredSpatialDerivativeRescaleAt_apply
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (tau : Real) (r : NNReal) (p0 : ParabolicPoint V)
    (du : Real → BoundedContinuousFunction V (V →L[Real] F))
    (t : Real) (x : V) :
    parabolicTimeCenteredSpatialDerivativeRescaleAt tau r p0 du t x =
      (r : Real) •
        du (p0.time + (r : Real) ^ 2 * (t - tau))
          (p0.space + (r : Real) • x) :=
  rfl

@[simp]
theorem parabolicTimeCenteredSpatialSecondDerivativeRescaleAt_apply
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (tau : Real) (r : NNReal) (p0 : ParabolicPoint V)
    (d2u : Real → BoundedContinuousFunction V
      (V →L[Real] V →L[Real] F))
    (t : Real) (x : V) :
    parabolicTimeCenteredSpatialSecondDerivativeRescaleAt
        tau r p0 d2u t x =
      (r : Real) ^ 2 •
        d2u (p0.time + (r : Real) ^ 2 * (t - tau))
          (p0.space + (r : Real) • x) :=
  rfl

end BoundedContinuousFunction

def parabolicSourceRescaleAt
    {V F : Type*} [Add V] [SMul Real V] [SMul Real F]
    (r : NNReal) (p0 : ParabolicPoint V) (f : ParabolicPoint V → F) :
    ParabolicPoint V → F :=
  fun p ↦ (r : Real) ^ 2 • f (parabolicDilationAt r p0 p)

def parabolicTimeCenteredSourceRescaleAt
    {V F : Type*} [Add V] [SMul Real V] [SMul Real F]
    (tau : Real) (r : NNReal) (p0 : ParabolicPoint V)
    (f : ParabolicPoint V → F) : ParabolicPoint V → F :=
  fun p ↦ (r : Real) ^ 2 •
    f (parabolicTimeCenteredDilationAt tau r p0 p)

@[simp]
theorem parabolicRescale_apply {V F : Type*} [SMul Real V]
    (r : NNReal) (u : Real → V → F) (t : Real) (x : V) :
    parabolicRescale r u t x =
      u ((r : Real) ^ 2 * t) ((r : Real) • x) := rfl

@[simp]
theorem parabolicRescaleAt_apply {V F : Type*} [Add V] [SMul Real V]
    (r : NNReal) (p0 : ParabolicPoint V) (u : Real → V → F)
    (t : Real) (x : V) :
    parabolicRescaleAt r p0 u t x =
      u (p0.time + (r : Real) ^ 2 * t)
        (p0.space + (r : Real) • x) := rfl

@[simp]
theorem parabolicRescaleAt_inverse_rescaleAt
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    (r : NNReal) (hr : 0 < r) (p0 : ParabolicPoint V)
    (u : Real → V → F) :
    parabolicRescaleAt r⁻¹
        (parabolicInverseDilationAt r p0 (parabolicPoint 0 0))
        (parabolicRescaleAt r p0 u) = u := by
  funext t x
  change u
      (parabolicDilationAt r p0
        (parabolicDilationAt r⁻¹
          (parabolicInverseDilationAt r p0 (parabolicPoint 0 0))
          (parabolicPoint t x))).time
      (parabolicDilationAt r p0
        (parabolicDilationAt r⁻¹
          (parabolicInverseDilationAt r p0 (parabolicPoint 0 0))
          (parabolicPoint t x))).space = u t x
  rw [parabolicDilationAt_inverse_eq_inverseDilationAt r hr,
    parabolicDilationAt_inverseDilationAt r hr]
  rfl

@[simp]
theorem parabolicSourceRescaleAt_apply
    {V F : Type*} [Add V] [SMul Real V] [SMul Real F]
    (r : NNReal) (p0 : ParabolicPoint V) (f : ParabolicPoint V → F)
    (p : ParabolicPoint V) :
    parabolicSourceRescaleAt r p0 f p =
      (r : Real) ^ 2 • f (parabolicDilationAt r p0 p) := rfl

@[simp]
theorem parabolicTimeCenteredSourceRescaleAt_apply
    {V F : Type*} [Add V] [SMul Real V] [SMul Real F]
    (tau : Real) (r : NNReal) (p0 : ParabolicPoint V)
    (f : ParabolicPoint V → F) (p : ParabolicPoint V) :
    parabolicTimeCenteredSourceRescaleAt tau r p0 f p =
      (r : Real) ^ 2 •
        f (parabolicTimeCenteredDilationAt tau r p0 p) :=
  rfl

namespace BoundedContinuousFunction

end BoundedContinuousFunction

def parabolicLinearMap {V W : Type*} [NormedAddCommGroup V]
    [NormedSpace Real V] [NormedAddCommGroup W] [NormedSpace Real W]
    (L : V →L[Real] W) (p : ParabolicPoint V) : ParabolicPoint W :=
  parabolicPoint p.time (L p.space)

@[simp]
theorem parabolicLinearMap_time {V W : Type*} [NormedAddCommGroup V]
    [NormedSpace Real V] [NormedAddCommGroup W] [NormedSpace Real W]
    (L : V →L[Real] W) (p : ParabolicPoint V) :
    (parabolicLinearMap L p).time = p.time := rfl

@[simp]
theorem parabolicLinearMap_space {V W : Type*} [NormedAddCommGroup V]
    [NormedSpace Real V] [NormedAddCommGroup W] [NormedSpace Real W]
    (L : V →L[Real] W) (p : ParabolicPoint V) :
    (parabolicLinearMap L p).space = L p.space := rfl

def parabolicLinearPreimage {V W : Type*} [NormedAddCommGroup V]
    [NormedSpace Real V] [NormedAddCommGroup W] [NormedSpace Real W]
    (L : V →L[Real] W) (Q : Set (ParabolicPoint W)) : Set (ParabolicPoint V) :=
  parabolicLinearMap L ⁻¹' Q

@[simp]
theorem parabolicLinearPreimage_cylinder_univ
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup W] [NormedSpace Real W]
    (L : V →L[Real] W) (J : Set Real) :
    parabolicLinearPreimage L (parabolicCylinder J Set.univ) =
      parabolicCylinder J Set.univ := by
  ext p
  simp [parabolicLinearPreimage, parabolicCylinder]

theorem lipschitzWith_compContinuousLinearMapL
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (j : Nat) (L : V →L[Real] V) :
    LipschitzWith (∏ _ : Fin j, ‖L‖₊)
      (ContinuousMultilinearMap.compContinuousLinearMapL
        (F := F) (fun _ : Fin j => L)) := by
  apply LipschitzWith.of_dist_le_mul
  intro B C
  rw [dist_eq_norm, ← map_sub]
  simpa only [dist_eq_norm, NNReal.coe_prod, coe_nnnorm, mul_comm,
    ContinuousMultilinearMap.compContinuousLinearMapL_apply] using
    ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (B - C) (fun _ : Fin j => L)

def contDiffHolderLinearEquivConst
    {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    (L : V ≃L[Real] V) (alpha C : NNReal) : NNReal :=
  let R := max 1 ‖(L.symm : V →L[Real] V)‖₊
  C + R * C + R ^ 2 * C + R ^ 2 * (C * R ^ (alpha : Real))

theorem eContDiffHolderGaugeOn_linearEquiv_le
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (L : V ≃L[Real] V) (alpha C : NNReal) (u : V → F)
    (h : eContDiffHolderGaugeOn 2 alpha Set.univ (fun x ↦ u (L x)) ≤ C) :
    eContDiffHolderGaugeOn 2 alpha Set.univ u ≤
      contDiffHolderLinearEquivConst L alpha C := by
  let v : V → F := fun x ↦ u (L x)
  let R : NNReal := max 1 ‖(L.symm : V →L[Real] V)‖₊
  let Cspatial : Nat → NNReal := fun j ↦
    match j with
    | 0 => C
    | 1 => R * C
    | _ => R ^ 2 * C
  have h' : eContDiffHolderGaugeOn 2 alpha Set.univ v ≤ C := h
  have hR : ‖(L.symm : V →L[Real] V)‖₊ ≤ R := le_max_right _ _
  have hspatial : ∀ j ≤ 2, ∀ x ∈ (Set.univ : Set V),
      ‖iteratedFDeriv Real j u x‖ ≤ Cspatial j := by
    intro j hj x hx
    let q := L.symm x
    have heq : iteratedFDeriv Real j u x =
        (iteratedFDeriv Real j v q).compContinuousLinearMap
          (fun _ ↦ (L.symm : V →L[Real] V)) := by
      have hlin := L.symm.iteratedFDerivWithin_comp_right v
        uniqueDiffOn_univ (mem_univ (L.symm x)) j
      have hfun : v ∘ L.symm = u := by
        funext y
        simp only [v, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
      rw [hfun] at hlin
      simpa only [v, q, preimage_univ, iteratedFDerivWithin_univ,
        Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] using! hlin
    rw [heq]
    have hnorm := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv Real j v q)
      (fun _ : Fin j ↦ (L.symm : V →L[Real] V))
    have hadapt := spatialJet_norm_le h' hj (Set.mem_univ q)
    interval_cases j
    · calc
        ‖(iteratedFDeriv Real 0 v q).compContinuousLinearMap
            (fun _ ↦ (L.symm : V →L[Real] V))‖ ≤
            ‖iteratedFDeriv Real 0 v q‖ * 1 := by
          simpa only [Finset.prod_fin_eq_prod_range,
            Finset.prod_range_zero] using! hnorm
        _ = ‖iteratedFDeriv Real 0 v q‖ := mul_one _
        _ ≤ (Cspatial 0 : Real) := by simpa only [Cspatial] using! hadapt
    · calc
        ‖(iteratedFDeriv Real 1 v q).compContinuousLinearMap
            (fun _ ↦ (L.symm : V →L[Real] V))‖ ≤
            ‖iteratedFDeriv Real 1 v q‖ *
              ‖(L.symm : V →L[Real] V)‖ := by
          simpa only [Fin.prod_univ_one] using! hnorm
        _ ≤ C * (R : Real) := by
          exact mul_le_mul hadapt (by exact_mod_cast hR)
            (norm_nonneg _) C.coe_nonneg
        _ = (Cspatial 1 : Real) := by
          simp only [Cspatial, NNReal.coe_mul]
          ring
    · calc
        ‖(iteratedFDeriv Real 2 v q).compContinuousLinearMap
            (fun _ ↦ (L.symm : V →L[Real] V))‖ ≤
            ‖iteratedFDeriv Real 2 v q‖ *
              (‖(L.symm : V →L[Real] V)‖ *
                ‖(L.symm : V →L[Real] V)‖) := by
          simpa only [Fin.prod_univ_two] using! hnorm
        _ ≤ C * ((R : Real) * R) := by
          apply mul_le_mul hadapt
          · exact mul_le_mul (by exact_mod_cast hR) (by exact_mod_cast hR)
              (norm_nonneg _) R.coe_nonneg
          · positivity
          · exact C.coe_nonneg
        _ = (Cspatial 2 : Real) := by
          simp only [Cspatial, NNReal.coe_mul, NNReal.coe_pow]
          ring
  have hholder : HolderWith (R ^ 2 * (C * R ^ (alpha : Real))) alpha
      ((Set.univ : Set V).domRestrict (iteratedFDeriv Real 2 u)) := by
    have hadapt := topSpatialJet_holderWith_restrict h'
    have hadaptGlobal : HolderWith C alpha (iteratedFDeriv Real 2 v) :=
      holderOnWith_univ.mp (HolderWith.restrict_iff.mp hadapt)
    have hdomain : HolderWith (C * R ^ (alpha : Real)) alpha
        ((Set.univ : Set V).domRestrict
          (iteratedFDeriv Real 2 v ∘ L.symm)) := by
      have hraw := hadaptGlobal.comp L.symm.lipschitzWith.holderWith
      have hraw' : HolderWith
          (C * ‖(L.symm : V →L[Real] V)‖₊ ^ (alpha : Real)) alpha
          (iteratedFDeriv Real 2 v ∘ L.symm) := by
        simpa only [mul_one] using! hraw
      have hweak : HolderWith (C * R ^ (alpha : Real)) alpha
          (iteratedFDeriv Real 2 v ∘ L.symm) :=
        hraw'.mono (by gcongr)
      have hrestrict := (hweak.holderOnWith (Set.univ : Set V)).holderWith
      simpa only [Function.comp_apply, Set.domRestrict_apply, mul_one] using! hrestrict
    let P := ContinuousMultilinearMap.compContinuousLinearMapL
      (F := F) (fun _ : Fin 2 ↦ (L.symm : V →L[Real] V))
    have hP0 := lipschitzWith_compContinuousLinearMapL
      (F := F) 2 (L.symm : V →L[Real] V)
    have hprod : (∏ _ : Fin 2, ‖(L.symm : V →L[Real] V)‖₊) ≤ R ^ 2 := by
      simpa only [Fin.prod_univ_two, pow_two] using!
        mul_le_mul hR hR (by positivity) (by positivity)
    have hP : LipschitzWith (R ^ 2) P := hP0.weaken hprod
    have hcomp := hP.holderWith.comp hdomain
    have hcomp' : HolderWith (R ^ 2 * (C * R ^ (alpha : Real))) alpha
        (P ∘ (Set.univ : Set V).domRestrict
          (iteratedFDeriv Real 2 v ∘ L.symm)) := by
      simpa only [NNReal.coe_one, NNReal.rpow_one, one_mul] using! hcomp
    have hfun : (Set.univ : Set V).domRestrict (iteratedFDeriv Real 2 u) =
        P ∘ (Set.univ : Set V).domRestrict
          (iteratedFDeriv Real 2 v ∘ L.symm) := by
      funext x
      have hlin := L.symm.iteratedFDerivWithin_comp_right v
        uniqueDiffOn_univ (mem_univ (L.symm x.1)) 2
      have hv : v ∘ L.symm = u := by
        funext y
        simp only [v, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
      rw [hv] at hlin
      simpa only [P, v, Function.comp_apply, Set.domRestrict_apply,
        preimage_univ, iteratedFDerivWithin_univ,
        ContinuousLinearEquiv.apply_symm_apply] using! hlin
    rw [hfun]
    exact hcomp'
  have hresult := eContDiffHolderGaugeOn_le Cspatial
    (R ^ 2 * (C * R ^ (alpha : Real))) hspatial hholder
  unfold contDiffHolderLinearEquivConst
  simpa only [R, Cspatial, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow,
    NNReal.coe_rpow] using! hresult

end CalabiYau.Schauder
