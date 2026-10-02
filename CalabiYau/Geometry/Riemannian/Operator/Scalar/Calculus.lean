-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Geometry/Operator/Scalar/Calculus.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Riemannian.Metric.Comparison.BallMonotonicity
public import CalabiYau.Geometry.Riemannian.Metric.Basic
public import CalabiYau.Geometry.Manifold.Bundle.PartialMfderiv.Basic
public import CalabiYau.Geometry.Manifold.Bundle.PartialMfderiv.ModelMixed
public import CalabiYau.Geometry.Manifold.Coordinates.Calculus.FixedBaseDerivative
public import CalabiYau.Geometry.Riemannian.Operator.Gradient.Basic
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Trace

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace CalabiYau.Riemannian

noncomputable section

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {Time : Type*}

private instance tangentSpace_finiteDimensional (x : M) :
    FiniteDimensional Real (TangentSpace I x) :=
  inferInstanceAs (FiniteDimensional Real E)

def metricFlatEquiv (g : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x ≃ₗ[Real] Module.Dual Real (TangentSpace I x) :=
  metricFlatMap (I := I) g x

@[simp] theorem metricFlatEquiv_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    metricFlatEquiv (I := I) g x v w = g.inner x v w := by
  rfl

theorem metricSharp_eq
    (g : SmoothRiemannianMetric I M) (x : M)
    (alpha : Module.Dual Real (TangentSpace I x)) :
    metricSharp (I := I) g x alpha =
      (metricFlatEquiv (I := I) g x).symm alpha := by
  rfl

def gradientFun (g : SmoothRiemannianMetric I M) (f : M -> Real) (x : M) :
    TangentSpace I x :=
  metricSharp (I := I) g x (mvfderiv (I := I) f x).toLinearMap

@[simp] theorem gradientFun_eq
    (g : SmoothRiemannianMetric I M) (f : M -> Real) (x : M) :
    gradientFun (I := I) g f x =
      metricSharp (I := I) g x (mvfderiv (I := I) f x).toLinearMap := by
  rfl

theorem inner_gradientFun
    (g : SmoothRiemannianMetric I M) (f : M -> Real) (x : M)
    (v : TangentSpace I x) :
    g.inner x (gradientFun (I := I) g f x) v =
      mvfderiv (I := I) f x v := by
  simpa [gradientFun] using
    inner_metricSharp (I := I) g x
      (mvfderiv (I := I) f x).toLinearMap v

theorem gradientFun_eq_of_flat
    (g : SmoothRiemannianMetric I M) {f : M -> Real} {x : M}
    {v : TangentSpace I x}
    (hf : (mvfderiv (I := I) f x).toLinearMap =
      metricFlatEquiv (I := I) g x v) :
    gradientFun (I := I) g f x = v := by
  unfold gradientFun metricSharp
  rw [hf]
  exact LinearEquiv.symm_apply_apply (metricFlatEquiv (I := I) g x) v

theorem gradientFun_eq_zero_of_mfderiv_eq_zero
    (g : SmoothRiemannianMetric I M) (f : M -> Real) {x : M}
    (hf : mfderiv I 𝓘(Real, Real) f x = 0) :
    gradientFun (I := I) g f x = 0 := by
  unfold gradientFun metricSharp
  have hmv : mvfderiv (I := I) f x = 0 := by
    simp [mvfderiv, hf]
  have hto :
      (mvfderiv (I := I) f x).toLinearMap =
        (0 : Module.Dual Real (TangentSpace I x)) := by
    rw [hmv]
    rfl
  rw [hto]
  exact LinearEquiv.map_zero (metricFlatEquiv (I := I) g x).symm

theorem gradientFun_eq_zero_of_isLocalMin
    [I.Boundaryless] (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M}
    (hmin : IsLocalMin f x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    gradientFun (I := I) g f x = 0 := by
  apply gradientFun_eq_zero_of_mfderiv_eq_zero
  have hmin_chart :
      IsLocalMin (fun y : E => f ((extChartAt I x).symm y))
        ((extChartAt I x) x) := by
    have hmin' :
        IsLocalMin f ((extChartAt I x).symm ((extChartAt I x) x)) := by
      simpa only [mfld_simps] using hmin
    change IsLocalMin (f ∘ (extChartAt I x).symm) ((extChartAt I x) x)
    exact hmin'.comp_continuous (continuousAt_extChartAt_symm (I := I) x)
  have hderiv_chart :
      fderiv Real (fun y : E => f ((extChartAt I x).symm y))
        ((extChartAt I x) x) = 0 :=
    hmin_chart.fderiv_eq_zero
  have hrange : Set.range I ∈ nhds ((extChartAt I x) x) := by
    rw [ModelWithCorners.Boundaryless.range_eq_univ (I := I)]
    exact Filter.univ_mem
  apply ContinuousLinearMap.ext
  intro v
  apply (NormedSpace.fromTangentSpace (f x)).injective
  simp only [zero_apply, map_zero]
  rw [← mvfderiv_real_eq_mfderiv]
  rw [mvfderiv_eq_fderiv_of_writtenInExtChartAt_eventuallyEq
    hf Filter.EventuallyEq.rfl]
  change fderiv Real (fun y : E => f ((extChartAt I x).symm y))
    ((extChartAt I x) x) v = 0
  rw [hderiv_chart]
  rfl

theorem gradientFun_eq_zero_of_isLocalMax
    [I.Boundaryless] (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M}
    (hmax : IsLocalMax f x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    gradientFun (I := I) g f x = 0 := by
  apply gradientFun_eq_zero_of_mfderiv_eq_zero
  have hmax_chart :
      IsLocalMax (fun y : E => f ((extChartAt I x).symm y))
        ((extChartAt I x) x) := by
    have hmax' :
        IsLocalMax f ((extChartAt I x).symm ((extChartAt I x) x)) := by
      simpa only [mfld_simps] using hmax
    change IsLocalMax (f ∘ (extChartAt I x).symm) ((extChartAt I x) x)
    exact hmax'.comp_continuous (continuousAt_extChartAt_symm (I := I) x)
  have hderiv_chart :
      fderiv Real (fun y : E => f ((extChartAt I x).symm y))
        ((extChartAt I x) x) = 0 :=
    hmax_chart.fderiv_eq_zero
  have hrange : Set.range I ∈ nhds ((extChartAt I x) x) := by
    rw [ModelWithCorners.Boundaryless.range_eq_univ (I := I)]
    exact Filter.univ_mem
  apply ContinuousLinearMap.ext
  intro v
  apply (NormedSpace.fromTangentSpace (f x)).injective
  simp only [zero_apply, map_zero]
  rw [← mvfderiv_real_eq_mfderiv]
  rw [mvfderiv_eq_fderiv_of_writtenInExtChartAt_eventuallyEq
    hf Filter.EventuallyEq.rfl]
  change fderiv Real (fun y : E => f ((extChartAt I x).symm y))
    ((extChartAt I x) x) v = 0
  rw [hderiv_chart]
  rfl

theorem gradientFun_const
    (g : SmoothRiemannianMetric I M) (c : Real) (x : M) :
    gradientFun (I := I) g (fun _ : M => c) x = 0 := by
  apply gradientFun_eq_zero_of_mfderiv_eq_zero
  exact mfderiv_const

theorem gradientFun_const_smul
    (g : SmoothRiemannianMetric I M) (a : Real)
    {f : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    gradientFun (I := I) g (a • f) x =
      a • gradientFun (I := I) g f x := by
  unfold gradientFun metricSharp
  rw [show a • f = (fun _ : M => a) • f by rfl]
  rw [_root_.mvfderiv_smul (mdifferentiableAt_const (c := a)) hf]
  rw [_root_.mvfderiv_const, ContinuousLinearMap.zero_smulRight, add_zero]
  let e := (metricFlatEquiv (I := I) g x).symm
  exact e.map_smul a (mvfderiv (I := I) f x).toLinearMap

theorem gradientFun_neg
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    gradientFun (I := I) g (-f) x =
      -gradientFun (I := I) g f x := by
  rw [show -f = (-1 : Real) • f by
    ext y
    simp]
  rw [gradientFun_const_smul (I := I) g (-1) hf]
  simp

theorem gradientFun_add
    (g : SmoothRiemannianMetric I M)
    {f h : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hh : MDifferentiableAt I 𝓘(Real, Real) h x) :
    gradientFun (I := I) g (fun y : M => f y + h y) x =
      gradientFun (I := I) g f x + gradientFun (I := I) g h x := by
  change gradientFun (I := I) g (f + h) x =
      gradientFun (I := I) g f x + gradientFun (I := I) g h x
  unfold gradientFun metricSharp
  rw [_root_.mvfderiv_add hf hh]
  let e := (metricFlatEquiv (I := I) g x).symm
  exact e.map_add (mvfderiv (I := I) f x).toLinearMap
    (mvfderiv (I := I) h x).toLinearMap

theorem gradientFun_sum {κ : Type*}
    (g : SmoothRiemannianMetric I M) (s : Finset κ)
    {f : κ -> M -> Real} {x : M}
    (hf : ∀ i ∈ s, MDifferentiableAt I 𝓘(Real, Real) (f i) x) :
    gradientFun (I := I) g (∑ i ∈ s, f i) x =
      ∑ i ∈ s, gradientFun (I := I) g (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change gradientFun (I := I) g (fun _ : M => (0 : Real)) x = 0
      exact gradientFun_const (I := I) g 0 x
  | insert a s ha ih =>
      have hfa : MDifferentiableAt I 𝓘(Real, Real) (f a) x :=
        hf a (Finset.mem_insert_self a s)
      have hfs : ∀ i ∈ s, MDifferentiableAt I 𝓘(Real, Real) (f i) x := by
        intro i hi
        exact hf i (Finset.mem_insert_of_mem hi)
      have htail : MDifferentiableAt I 𝓘(Real, Real) (∑ i ∈ s, f i) x :=
        mdifferentiableAt_finset_sum s f hfs
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      calc
        gradientFun (I := I) g (f a + ∑ i ∈ s, f i) x
            = gradientFun (I := I) g (f a) x +
                gradientFun (I := I) g (∑ i ∈ s, f i) x := by
              change gradientFun (I := I) g
                (fun y : M => f a y + (∑ i ∈ s, f i) y) x = _
              rw [gradientFun_add (I := I) g hfa htail]
        _ = gradientFun (I := I) g (f a) x +
              ∑ i ∈ s, gradientFun (I := I) g (f i) x := by
              rw [ih hfs]

theorem gradientFun_sum_smul {κ : Type*}
    (g : SmoothRiemannianMetric I M) (s : Finset κ) (c : κ -> Real)
    {f : κ -> M -> Real} {x : M}
    (hf : ∀ i ∈ s, MDifferentiableAt I 𝓘(Real, Real) (f i) x) :
    gradientFun (I := I) g (∑ i ∈ s, c i • f i) x =
      ∑ i ∈ s, c i • gradientFun (I := I) g (f i) x := by
  classical
  have hsum := gradientFun_sum (I := I) g s
    (f := fun i => c i • f i) (x := x) (by
      intro i hi
      exact (hf i hi).const_smul (c i))
  calc
    gradientFun (I := I) g (∑ i ∈ s, c i • f i) x
        = ∑ i ∈ s, gradientFun (I := I) g (c i • f i) x := hsum
    _ = ∑ i ∈ s, c i • gradientFun (I := I) g (f i) x := by
          apply Finset.sum_congr rfl
          intro i hi
          exact gradientFun_const_smul (I := I) g (c i) (hf i hi)

theorem gradientFun_sub
    (g : SmoothRiemannianMetric I M)
    {f h : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hh : MDifferentiableAt I 𝓘(Real, Real) h x) :
    gradientFun (I := I) g (fun y : M => f y - h y) x =
      gradientFun (I := I) g f x - gradientFun (I := I) g h x := by
  change gradientFun (I := I) g (f - h) x =
      gradientFun (I := I) g f x - gradientFun (I := I) g h x
  unfold gradientFun metricSharp
  rw [_root_.mvfderiv_sub hf hh]
  let e := (metricFlatEquiv (I := I) g x).symm
  exact e.map_sub (mvfderiv (I := I) f x).toLinearMap
    (mvfderiv (I := I) h x).toLinearMap

theorem gradientFun_comp
    (g : SmoothRiemannianMetric I M)
    {φ : Real -> Real} {f : M -> Real} {x : M}
    (hφ : DifferentiableAt Real φ (f x))
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    gradientFun (I := I) g (fun y : M => φ (f y)) x =
      deriv φ (f x) • gradientFun (I := I) g f x := by
  have hmvcomp :
      mvfderiv (I := I) (φ ∘ f) x =
        deriv φ (f x) • mvfderiv (I := I) f x := by
    ext v
    have hchain := mvfderiv_comp_apply (I := 𝓘(Real, Real)) (I' := I)
      (f := f) (g := φ) x hφ.mdifferentiableAt hf v
    rw [mvfderiv_real_model_eq_fderiv,
      hφ.hasDerivAt.hasFDerivAt.fderiv] at hchain
    rw [← mvfderiv_real_eq_mfderiv I f x v] at hchain
    simpa [Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply,
      smul_eq_mul, mul_comm] using hchain
  rw [show (fun y : M => φ (f y)) = φ ∘ f by rfl]
  unfold gradientFun metricSharp
  rw [hmvcomp]
  exact LinearEquiv.map_smul (metricFlatEquiv (I := I) g x).symm
    (deriv φ (f x)) (mvfderiv (I := I) f x).toLinearMap

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem mvfderiv_mul
    {f h : M -> Real} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hh : MDifferentiableAt I 𝓘(Real, Real) h x) :
    mvfderiv (I := I) (fun y : M => f y * h y) x v =
      f x * mvfderiv (I := I) h x v +
        mvfderiv (I := I) f x v * h x := by
  change mvfderiv (I := I) (f • h) x v =
      f x * mvfderiv (I := I) h x v +
        mvfderiv (I := I) f x v * h x
  have hprod := DFunLike.congr_fun (_root_.mvfderiv_mul hf hh) v
  simpa [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using hprod

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem mvfderiv_const_mul_apply
    (a : Real) {f : M -> Real} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    mvfderiv (I := I) (fun y : M => a * f y) x v =
      a * mvfderiv (I := I) f x v := by
  have h := CalabiYau.mvfderiv_const_mul (I := I) a hf
  have hv := DFunLike.congr_fun h v
  simpa [Pi.smul_apply, smul_eq_mul] using hv

theorem gradientFun_mul
    (g : SmoothRiemannianMetric I M)
    {f h : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hh : MDifferentiableAt I 𝓘(Real, Real) h x) :
    gradientFun (I := I) g (fun y : M => f y * h y) x =
      f x • gradientFun (I := I) g h x +
        h x • gradientFun (I := I) g f x := by
  apply metricFlatLinear_injective (I := I) g x
  ext v
  have hprod := mvfderiv_mul (I := I) (f := f) (h := h) v hf hh
  have hmul :
      g.inner x (gradientFun (I := I) g (fun y : M => f y * h y) x) v =
        f x * g.inner x (gradientFun (I := I) g h x) v +
          g.inner x (gradientFun (I := I) g f x) v * h x := by
    rw [inner_gradientFun (I := I) g (fun y : M => f y * h y) x v]
    have hhinner :
        mvfderiv (I := I) h x v =
          g.inner x (gradientFun (I := I) g h x) v := by
      exact (inner_gradientFun (I := I) g h x v).symm
    have hfinner :
        mvfderiv (I := I) f x v =
          g.inner x (gradientFun (I := I) g f x) v := by
      exact (inner_gradientFun (I := I) g f x v).symm
    rw [hprod, hhinner, hfinner]
  calc
    metricFlatLinear (I := I) g x
        (gradientFun (I := I) g (fun y : M => f y * h y) x) v =
        f x * g.inner x (gradientFun (I := I) g h x) v +
          g.inner x (gradientFun (I := I) g f x) v * h x := by
          simpa [metricFlatLinear_apply] using hmul
    _ = metricFlatLinear (I := I) g x
        (f x • gradientFun (I := I) g h x +
          h x • gradientFun (I := I) g f x) v := by
          simp [metricFlatLinear_apply, mul_comm]

theorem gradientFun_pow
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M} (n : Nat)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    gradientFun (I := I) g (fun y : M => f y ^ (n + 1)) x =
      (((n + 1 : Nat) : Real) * f x ^ n) •
        gradientFun (I := I) g f x := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpow :
          MDifferentiableAt I 𝓘(Real, Real)
            (fun y : M => f y ^ (n + 1)) x :=
        hf.pow (n + 1)
      calc
        gradientFun (I := I) g
            (fun y : M => f y ^ (Nat.succ n + 1)) x =
            gradientFun (I := I) g
              (fun y : M => f y ^ (n + 1) * f y) x := by
                apply congrArg (fun q : M -> Real => gradientFun (I := I) g q x)
                funext y
                rw [show Nat.succ n + 1 = (n + 1) + 1 by omega, pow_succ]
        _ = f x ^ (n + 1) • gradientFun (I := I) g f x +
              f x • gradientFun (I := I) g
                (fun y : M => f y ^ (n + 1)) x :=
              gradientFun_mul (I := I) g hpow hf
        _ = (((Nat.succ n + 1 : Nat) : Real) * f x ^ Nat.succ n) •
              gradientFun (I := I) g f x := by
              rw [ih, smul_smul, ← add_smul]
              congr 1
              push_cast
              rw [show f x ^ (n + 1) = f x ^ n * f x by rw [pow_succ]]
              ring

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem mvfderiv_rpow
    {f : M -> Real} {x : M} (p : Real) (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hpos : 0 < f x) :
    mvfderiv (I := I) (fun y : M => f y ^ p) x v =
      (p * f x ^ (p - 1)) * mvfderiv (I := I) f x v := by
  let coeff : Real := p * f x ^ (p - 1)
  have hp := Real.hasDerivAt_rpow_const (p := p) (Or.inl hpos.ne')
  have hchain := mvfderiv_comp_apply (I := 𝓘(Real, Real)) (I' := I)
    (f := f) (g := fun z : Real => z ^ p)
    x hp.differentiableAt.mdifferentiableAt hf v
  rw [mvfderiv_real_model_eq_fderiv, hp.hasFDerivAt.fderiv] at hchain
  rw [← mvfderiv_real_eq_mfderiv I f x v] at hchain
  simpa [Function.comp_def, coeff, ContinuousLinearMap.toSpanSingleton_apply,
    mul_comm] using hchain

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem mdifferentiableAt_rpow
    {f : M -> Real} {x : M} (p : Real)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hpos : 0 < f x) :
    MDifferentiableAt I 𝓘(Real, Real) (fun y : M => f y ^ p) x := by
  have hp :
      MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, Real)
        (fun z : Real => z ^ p) (f x) := by
    exact (Real.differentiableAt_rpow_const_of_ne p hpos.ne').mdifferentiableAt
  exact hp.comp x hf

theorem gradientFun_rpow
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M} (p : Real)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hpos : 0 < f x) :
    gradientFun (I := I) g (fun y : M => f y ^ p) x =
      (p * f x ^ (p - 1)) • gradientFun (I := I) g f x := by
  apply metricFlatLinear_injective (I := I) g x
  ext v
  have hrpow := mvfderiv_rpow (I := I) (f := f) p v hf hpos
  have hfinner :
      mvfderiv (I := I) f x v =
        g.inner x (gradientFun (I := I) g f x) v := by
    exact (inner_gradientFun (I := I) g f x v).symm
  calc
    metricFlatLinear (I := I) g x
        (gradientFun (I := I) g (fun y : M => f y ^ p) x) v =
        (p * f x ^ (p - 1)) *
          g.inner x (gradientFun (I := I) g f x) v := by
          rw [metricFlatLinear_apply, inner_gradientFun]
          rw [hrpow, hfinner]
    _ = metricFlatLinear (I := I) g x
        ((p * f x ^ (p - 1)) • gradientFun (I := I) g f x) v := by
          simp [metricFlatLinear_apply]

theorem gradientFun_log
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hpos : 0 < f x) :
    gradientFun (I := I) g (fun y : M => Real.log (f y)) x =
      (f x)⁻¹ • gradientFun (I := I) g f x := by
  apply metricFlatLinear_injective (I := I) g x
  ext v
  let coeff : Real := (f x)⁻¹
  have hlog_ext :
      mvfderiv (I := I) (fun y : M => Real.log (f y)) x v =
        coeff * mvfderiv (I := I) f x v := by
    have hlog := Real.hasDerivAt_log hpos.ne'
    have hchain := mvfderiv_comp_apply (I := 𝓘(Real, Real)) (I' := I)
      (f := f) (g := Real.log) x hlog.differentiableAt.mdifferentiableAt hf v
    rw [mvfderiv_real_model_eq_fderiv, hlog.hasFDerivAt.fderiv] at hchain
    rw [← mvfderiv_real_eq_mfderiv I f x v] at hchain
    simpa [Function.comp_def, coeff, ContinuousLinearMap.toSpanSingleton_apply,
      mul_comm] using hchain
  have hfinner :
      mvfderiv (I := I) f x v =
        g.inner x (gradientFun (I := I) g f x) v := by
    exact (inner_gradientFun (I := I) g f x v).symm
  calc
    metricFlatLinear (I := I) g x
        (gradientFun (I := I) g (fun y : M => Real.log (f y)) x) v =
        coeff * g.inner x (gradientFun (I := I) g f x) v := by
          rw [metricFlatLinear_apply, inner_gradientFun]
          rw [hlog_ext, hfinner]
    _ = metricFlatLinear (I := I) g x
        ((f x)⁻¹ • gradientFun (I := I) g f x) v := by
          simp [coeff, metricFlatLinear_apply]

theorem gradientFun_mul_self
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    gradientFun (I := I) g (fun y : M => f y * f y) x =
      (2 * f x) • gradientFun (I := I) g f x := by
  rw [gradientFun_mul (I := I) g hf hf]
  rw [← add_smul]
  congr 1
  ring

def divergence
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : (x : M) -> TangentSpace I x) (x : M) : Real :=
  LinearMap.trace Real (TangentSpace I x) (cov X x).toLinearMap

omit [FiniteDimensional ℝ E] in
@[simp] theorem divergence_eq
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : (x : M) -> TangentSpace I x) (x : M) :
    divergence (I := I) cov X x =
      LinearMap.trace Real (TangentSpace I x) (cov X x).toLinearMap := by
  rfl

def laplacian
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (f : M -> Real) (x : M) : Real :=
  divergence (I := I) cov (gradientFun (I := I) g f) x

@[simp] theorem laplacian_eq
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (f : M -> Real) (x : M) :
    laplacian (I := I) cov g f x =
      divergence (I := I) cov (gradientFun (I := I) g f) x := by
  rfl

section AlgebraicRules

variable [VectorBundle Real E (TangentSpace I : M -> Type _)]

omit [FiniteDimensional ℝ E] in
theorem divergence_zero
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x : M) :
    divergence (I := I) cov (0 : (x : M) -> TangentSpace I x) x = 0 := by
  simp [divergence]

omit [FiniteDimensional ℝ E]
  [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem divergence_add
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (_hVB : VectorBundle ℝ E (TangentSpace I : M → Type _))
    {X Y : (x : M) -> TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    divergence (I := I) cov (X + Y) x =
      divergence (I := I) cov X x + divergence (I := I) cov Y x := by
  let _ := _hVB
  let := _hVB
  unfold divergence
  rw [cov.isCovariantDerivativeOnUniv.add hX hY]
  simp

omit [FiniteDimensional ℝ E]
  [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem divergence_const_smul
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (_hVB : VectorBundle ℝ E (TangentSpace I : M → Type _))
    (a : Real) {X : (x : M) -> TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) :
    divergence (I := I) cov (a • X) x =
      a * divergence (I := I) cov X x := by
  let _ := _hVB
  let := _hVB
  unfold divergence
  rw [cov.isCovariantDerivativeOnUniv.smul_const a hX]
  simp

omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem divergence_smul
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (_hVB : VectorBundle ℝ E (TangentSpace I : M → Type _))
    {f : M -> Real} {X : (x : M) -> TangentSpace I x} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hX : MDiffAt (T% X) x) :
    divergence (I := I) cov (f • X) x =
      f x * divergence (I := I) cov X x +
        mvfderiv (I := I) f x (X x) := by
  let _ := _hVB
  let := _hVB
  unfold divergence
  rw [cov.isCovariantDerivativeOnUniv.leibniz hX hf]
  rw [ContinuousLinearMap.toLinearMap_add]
  rw [map_add]
  change
      LinearMap.trace Real (TangentSpace I x) (f x • (cov X x).toLinearMap) +
          LinearMap.trace Real (TangentSpace I x)
            ((mvfderiv (I := I) f x).toLinearMap.smulRight (X x)) =
        f x * LinearMap.trace Real (TangentSpace I x) (cov X x).toLinearMap +
          mvfderiv (I := I) f x (X x)
  rw [map_smul, LinearMap.trace_smulRight]
  simp [smul_eq_mul]

omit [FiniteDimensional ℝ E] in
theorem divergence_sub
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    {X Y : (x : M) -> TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    divergence (I := I) cov (X - Y) x =
      divergence (I := I) cov X x - divergence (I := I) cov Y x := by
  unfold divergence
  rw [sub_eq_add_neg,
    cov.isCovariantDerivativeOnUniv.add hX (mdifferentiableAt_neg_section hY)]
  have hneg : cov (-Y) x = (-1 : Real) • cov Y x := by
    simpa using cov.isCovariantDerivativeOnUniv.smul_const (-1 : Real) hY
  rw [hneg]
  rw [ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul]
  rw [map_add, map_smul]
  simp [sub_eq_add_neg]

theorem laplacian_const
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M) (c : Real) (x : M) :
    laplacian (I := I) cov g (fun _ : M => c) x = 0 := by
  have hgrad :
      gradientFun (I := I) g (fun _ : M => c) =
        (0 : (x : M) -> TangentSpace I x) := by
    funext y
    exact gradientFun_const (I := I) g c y
  simp [laplacian, hgrad]

omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem laplacian_add_const
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (c : Real) {f : M -> Real} {x : M}
    (hf : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x) :
    laplacian (I := I) cov g (fun y : M => c + f y) x =
      laplacian (I := I) cov g f x := by
  have hgrad_eq :
      (fun y : M => gradientFun (I := I) g (fun z : M => c + f z) y) =ᶠ[nhds x]
        (fun y : M => gradientFun (I := I) g f y) := by
    filter_upwards [hf] with y hy
    calc
      gradientFun (I := I) g (fun z : M => c + f z) y =
          gradientFun (I := I) g (fun _ : M => c) y +
            gradientFun (I := I) g f y := by
        exact gradientFun_add (I := I) g mdifferentiableAt_const hy
      _ = gradientFun (I := I) g f y := by
        rw [gradientFun_const, zero_add]
  have hgrad_total :
      (T% fun y : M => gradientFun (I := I) g (fun z : M => c + f z) y) =ᶠ[nhds x]
        (T% fun y : M => gradientFun (I := I) g f y) := by
    filter_upwards [hgrad_eq] with y hy
    change TotalSpace.mk' E y
        (gradientFun (I := I) g (fun z : M => c + f z) y) =
      TotalSpace.mk' E y (gradientFun (I := I) g f y)
    rw [hy]
  have hgrad_add :
      MDiffAt
        (T% fun y : M => gradientFun (I := I) g (fun z : M => c + f z) y) x :=
    hgrad.congr_of_eventuallyEq hgrad_total
  have hcov :
      cov.toFun (fun y : M =>
          gradientFun (I := I) g (fun z : M => c + f z) y) x =
        cov.toFun (fun y : M => gradientFun (I := I) g f y) x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hgrad_add hgrad Filter.univ_mem hgrad_eq
  unfold laplacian divergence
  rw [hcov]

omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem laplacian_sub_const
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} (c : Real)
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (x : M) :
    laplacian (I := I) cov g (fun y : M => f y - c) x =
      laplacian (I := I) cov g f x := by
  have hgrad :
      gradientFun (I := I) g (fun y : M => f y - c) =
        gradientFun (I := I) g f := by
    funext y
    calc
      gradientFun (I := I) g (fun y : M => f y - c) y =
          gradientFun (I := I) g f y -
            gradientFun (I := I) g (fun _ : M => c) y := by
        exact gradientFun_sub (I := I) g (hf y) mdifferentiableAt_const
      _ = gradientFun (I := I) g f y - 0 := by
        rw [gradientFun_const]
      _ = gradientFun (I := I) g f y := by simp
  simp [laplacian, hgrad]

theorem laplacian_sub
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {f h : M -> Real} {x : M}
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hh : forall y : M, MDifferentiableAt I 𝓘(Real, Real) h y)
    (hgradf : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x)
    (hgradh : MDiffAt (T% fun y : M => gradientFun (I := I) g h y) x) :
    laplacian (I := I) cov g (fun y : M => f y - h y) x =
      laplacian (I := I) cov g f x -
        laplacian (I := I) cov g h x := by
  have hgrad :
      gradientFun (I := I) g (fun y : M => f y - h y) =
        fun y : M => gradientFun (I := I) g f y -
          gradientFun (I := I) g h y := by
    funext y
    exact gradientFun_sub (I := I) g (hf y) (hh y)
  calc
    laplacian (I := I) cov g (fun y : M => f y - h y) x =
        divergence (I := I) cov
          (fun y : M => gradientFun (I := I) g f y -
            gradientFun (I := I) g h y) x := by
          simp [laplacian, hgrad]
    _ = laplacian (I := I) cov g f x -
        laplacian (I := I) cov g h x := by
          change divergence (I := I) cov
              ((fun y : M => gradientFun (I := I) g f y) -
                fun y : M => gradientFun (I := I) g h y) x =
            divergence (I := I) cov (gradientFun (I := I) g f) x -
              divergence (I := I) cov (gradientFun (I := I) g h) x
          exact divergence_sub (I := I) cov hgradf hgradh

theorem laplacian_add_at
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (g : SmoothRiemannianMetric I M)
    {f h : M → Real} {x : M}
    (hf : ∀ᶠ y in nhds x,
      MDifferentiableAt I 𝓘(Real, Real) f y)
    (hh : ∀ᶠ y in nhds x,
      MDifferentiableAt I 𝓘(Real, Real) h y)
    (hgradf : MDiffAt
      (T% fun y : M => gradientFun (I := I) g f y) x)
    (hgradh : MDiffAt
      (T% fun y : M => gradientFun (I := I) g h y) x) :
    laplacian (I := I) cov g (fun y : M => f y + h y) x =
      laplacian (I := I) cov g f x +
        laplacian (I := I) cov g h x := by
  have hgrad_eq :
      (fun y : M => gradientFun (I := I) g (fun z : M => f z + h z) y) =ᶠ[nhds x]
        (fun y : M =>
          gradientFun (I := I) g f y + gradientFun (I := I) g h y) := by
    filter_upwards [hf, hh] with y hfy hhy
    exact gradientFun_add (I := I) g hfy hhy
  have hadd :
      MDiffAt
        (T% fun y : M =>
          gradientFun (I := I) g f y + gradientFun (I := I) g h y) x :=
    mdifferentiableAt_add_section hgradf hgradh
  have hgrad_total :
      (T% fun y : M => gradientFun (I := I) g (fun z : M => f z + h z) y) =ᶠ[nhds x]
        (T% fun y : M =>
          gradientFun (I := I) g f y + gradientFun (I := I) g h y) := by
    filter_upwards [hgrad_eq] with y hy
    change TotalSpace.mk' E y
        (gradientFun (I := I) g (fun z : M => f z + h z) y) =
      TotalSpace.mk' E y
        (gradientFun (I := I) g f y + gradientFun (I := I) g h y)
    rw [hy]
  have hgrad_add :
      MDiffAt
        (T% fun y : M => gradientFun (I := I) g (fun z : M => f z + h z) y) x :=
    hadd.congr_of_eventuallyEq hgrad_total
  have hcov :
      cov.toFun
          (fun y : M => gradientFun (I := I) g (fun z : M => f z + h z) y) x =
        cov.toFun
          (fun y : M =>
            gradientFun (I := I) g f y + gradientFun (I := I) g h y) x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hgrad_add hadd Filter.univ_mem hgrad_eq
  calc
    laplacian (I := I) cov g (fun y : M => f y + h y) x =
        divergence (I := I) cov
          (fun y : M =>
            gradientFun (I := I) g f y + gradientFun (I := I) g h y) x := by
      unfold laplacian divergence
      rw [hcov]
    _ = divergence (I := I) cov
          ((fun y : M => gradientFun (I := I) g f y) +
            fun y : M => gradientFun (I := I) g h y) x := by
      rfl
    _ = laplacian (I := I) cov g f x +
        laplacian (I := I) cov g h x := by
      simpa only [laplacian] using
        (divergence_add (I := I) cov inferInstance hgradf hgradh)

theorem laplacian_sub_at
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {f h : M -> Real} {x : M}
    (hf : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hh : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(Real, Real) h y)
    (hgradf : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x)
    (hgradh : MDiffAt (T% fun y : M => gradientFun (I := I) g h y) x) :
    laplacian (I := I) cov g (fun y : M => f y - h y) x =
      laplacian (I := I) cov g f x -
        laplacian (I := I) cov g h x := by
  have hgrad_eq :
      (fun y : M => gradientFun (I := I) g (fun z => f z - h z) y) =ᶠ[nhds x]
        fun y : M => gradientFun (I := I) g f y -
          gradientFun (I := I) g h y := by
    filter_upwards [hf, hh] with y hyf hyh
    exact gradientFun_sub (I := I) g hyf hyh
  have hgrad_total :
      (T% fun y : M => gradientFun (I := I) g (fun z => f z - h z) y) =ᶠ[nhds x]
        (T% fun y : M => gradientFun (I := I) g f y -
          gradientFun (I := I) g h y) := by
    filter_upwards [hgrad_eq] with y hy
    rw [hy]
  have hgrad_sub :
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) g (fun z => f z - h z) y) x :=
    (mdifferentiableAt_sub_section hgradf hgradh).congr_of_eventuallyEq hgrad_total
  have hcov :
      cov (fun y : M => gradientFun (I := I) g (fun z => f z - h z) y) x =
        cov (fun y : M => gradientFun (I := I) g f y -
          gradientFun (I := I) g h y) x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hgrad_sub (mdifferentiableAt_sub_section hgradf hgradh)
      Filter.univ_mem hgrad_eq
  unfold laplacian divergence
  rw [hcov]
  exact divergence_sub (I := I) cov hgradf hgradh

theorem laplacian_const_smul
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (a : Real) {f : M -> Real} {x : M}
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x) :
    laplacian (I := I) cov g (a • f) x =
      a * laplacian (I := I) cov g f x := by
  have hgrad_eq :
      gradientFun (I := I) g (a • f) =
        a • gradientFun (I := I) g f := by
    funext y
    exact gradientFun_const_smul (I := I) g a (hf y)
  calc
    laplacian (I := I) cov g (a • f) x =
        divergence (I := I) cov (a • gradientFun (I := I) g f) x := by
      simp [laplacian, hgrad_eq]
    _ = a * laplacian (I := I) cov g f x := by
      rw [divergence_const_smul (I := I) cov inferInstance a hgrad]
      rfl

theorem laplacian_smul_at
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (g : SmoothRiemannianMetric I M)
    (a : Real) {f : M → Real} {x : M}
    (hf : ∀ᶠ y in nhds x,
      MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt
      (T% fun y : M => gradientFun (I := I) g f y) x) :
    laplacian (I := I) cov g (a • f) x =
      a * laplacian (I := I) cov g f x := by
  have hgrad_eq :
      (fun y : M => gradientFun (I := I) g (a • f) y) =ᶠ[nhds x]
        (fun y : M => a • gradientFun (I := I) g f y) := by
    filter_upwards [hf] with y hy
    exact gradientFun_const_smul (I := I) g a hy
  have hscaled :
      MDiffAt
        (T% fun y : M => a • gradientFun (I := I) g f y) x := by
    simpa only [Pi.smul_apply] using
      hgrad.smul_const_section (a := a)
  have hgrad_total :
      (T% fun y : M => gradientFun (I := I) g (a • f) y) =ᶠ[nhds x]
        (T% fun y : M => a • gradientFun (I := I) g f y) := by
    filter_upwards [hgrad_eq] with y hy
    change TotalSpace.mk' E y
        (gradientFun (I := I) g (a • f) y) =
      TotalSpace.mk' E y
        (a • gradientFun (I := I) g f y)
    rw [hy]
  have hgrad_smul :
      MDiffAt
        (T% fun y : M => gradientFun (I := I) g (a • f) y) x :=
    hscaled.congr_of_eventuallyEq hgrad_total
  have hcov :
      cov.toFun
          (fun y : M => gradientFun (I := I) g (a • f) y) x =
        cov.toFun
          (fun y : M => a • gradientFun (I := I) g f y) x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hgrad_smul hscaled Filter.univ_mem hgrad_eq
  calc
    laplacian (I := I) cov g (a • f) x =
        divergence (I := I) cov
          (fun y : M => a • gradientFun (I := I) g f y) x := by
      unfold laplacian divergence
      rw [hcov]
    _ = divergence (I := I) cov
          (a • fun y : M => gradientFun (I := I) g f y) x := by
      rfl
    _ = a * laplacian (I := I) cov g f x := by
      simpa only [laplacian] using
        (divergence_const_smul (I := I) cov inferInstance a hgrad)
theorem divergence_smul_gradientFun
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x) :
    divergence (I := I) cov (f • fun y : M => gradientFun (I := I) g f y) x =
      f x * laplacian (I := I) cov g f x +
        g.inner x (gradientFun (I := I) g f x) (gradientFun (I := I) g f x) := by
  rw [divergence_smul (I := I) cov inferInstance hf hgrad]
  have hinner := inner_gradientFun (I := I) g f x (gradientFun (I := I) g f x)
  simpa [mvfderiv] using congrArg id hinner.symm

theorem divergence_smul_gradientFun_pair
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {f h : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g h y) x) :
    divergence (I := I) cov (f • fun y : M => gradientFun (I := I) g h y) x =
      f x * laplacian (I := I) cov g h x +
        g.inner x (gradientFun (I := I) g f x)
          (gradientFun (I := I) g h x) := by
  rw [divergence_smul (I := I) cov inferInstance hf hgrad]
  have hinner := inner_gradientFun (I := I) g f x (gradientFun (I := I) g h x)
  simpa [mvfderiv] using congrArg id hinner.symm

omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem laplacian_comp_of_eventually_differentiable
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (g : SmoothRiemannianMetric I M)
    {phi : Real → Real} {f : M → Real} {x : M}
    (hphi : ∀ᶠ z in nhds (f x), DifferentiableAt ℝ phi z)
    (hphi' : DifferentiableAt Real (deriv phi) (f x))
    (hf : ∀ᶠ y in nhds x,
      MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt
      (T% fun y : M => gradientFun (I := I) g f y) x) :
    laplacian (I := I) cov g (fun y : M => phi (f y)) x =
      deriv phi (f x) * laplacian (I := I) cov g f x +
        deriv (deriv phi) (f x) *
          g.inner x (gradientFun (I := I) g f x)
            (gradientFun (I := I) g f x) := by
  let coeffFun : M → Real := fun y => deriv phi (f y)
  have hfx : MDifferentiableAt I 𝓘(Real, Real) f x :=
    hf.self_of_nhds
  have hcoeff : MDifferentiableAt I 𝓘(Real, Real) coeffFun x :=
    hphi'.mdifferentiableAt.comp x hfx
  have hgrad_eq :
      (fun y : M => gradientFun (I := I) g (fun z : M => phi (f z)) y) =ᶠ[nhds x]
        (fun y : M =>
          coeffFun y • gradientFun (I := I) g f y) := by
    filter_upwards [hf, hfx.continuousAt.eventually hphi] with y hfy hphiy
    exact gradientFun_comp (I := I) g hphiy hfy
  have hscaled :
      MDiffAt
        (T% fun y : M => coeffFun y • gradientFun (I := I) g f y) x :=
    hcoeff.smul_section hgrad
  have hgrad_total :
      (T% fun y : M => gradientFun (I := I) g (fun z : M => phi (f z)) y) =ᶠ[nhds x]
        (T% fun y : M =>
          coeffFun y • gradientFun (I := I) g f y) := by
    filter_upwards [hgrad_eq] with y hy
    change TotalSpace.mk' E y
        (gradientFun (I := I) g (fun z : M => phi (f z)) y) =
      TotalSpace.mk' E y
        (coeffFun y • gradientFun (I := I) g f y)
    rw [hy]
  have hgrad_comp :
      MDiffAt
        (T% fun y : M => gradientFun (I := I) g (fun z : M => phi (f z)) y) x :=
    hscaled.congr_of_eventuallyEq hgrad_total
  have hcov :
      cov.toFun
          (fun y : M => gradientFun (I := I) g (fun z : M => phi (f z)) y) x =
        cov.toFun
          (fun y : M => coeffFun y • gradientFun (I := I) g f y) x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hgrad_comp hscaled Filter.univ_mem hgrad_eq
  calc
    laplacian (I := I) cov g (fun y : M => phi (f y)) x =
        divergence (I := I) cov
          (fun y : M => coeffFun y • gradientFun (I := I) g f y) x := by
      unfold laplacian divergence
      rw [hcov]
    _ = coeffFun x * laplacian (I := I) cov g f x +
          g.inner x (gradientFun (I := I) g coeffFun x)
            (gradientFun (I := I) g f x) := by
      exact divergence_smul_gradientFun_pair (I := I) cov g hcoeff hgrad
    _ = deriv phi (f x) * laplacian (I := I) cov g f x +
          deriv (deriv phi) (f x) *
            g.inner x (gradientFun (I := I) g f x)
              (gradientFun (I := I) g f x) := by
      rw [gradientFun_comp (I := I) g hphi' hfx]
      simp [coeffFun]

omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem laplacian_comp
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {φ : Real -> Real} {f : M -> Real} {x : M}
    (hφ : Differentiable Real φ)
    (hφ' : DifferentiableAt Real (deriv φ) (f x))
    (hf : ∀ y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt
      (T% fun y : M => gradientFun (I := I) g f y) x) :
    laplacian (I := I) cov g (fun y : M => φ (f y)) x =
      deriv φ (f x) * laplacian (I := I) cov g f x +
        deriv (deriv φ) (f x) *
          g.inner x (gradientFun (I := I) g f x)
            (gradientFun (I := I) g f x) := by
  exact laplacian_comp_of_eventually_differentiable (I := I) cov g
    (Filter.Eventually.of_forall hφ) hφ' (Filter.Eventually.of_forall hf) hgrad

omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem laplacian_comp_at
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (g : SmoothRiemannianMetric I M)
    {phi : Real → Real} {f : M → Real} {x : M}
    (hphi : Differentiable Real phi)
    (hphi' : DifferentiableAt Real (deriv phi) (f x))
    (hf : ∀ᶠ y in nhds x,
      MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt
      (T% fun y : M => gradientFun (I := I) g f y) x) :
    laplacian (I := I) cov g (fun y : M => phi (f y)) x =
      deriv phi (f x) * laplacian (I := I) cov g f x +
        deriv (deriv phi) (f x) *
          g.inner x (gradientFun (I := I) g f x)
            (gradientFun (I := I) g f x) := by
  exact laplacian_comp_of_eventually_differentiable (I := I) cov g
    (Filter.Eventually.of_forall hphi) hphi' hf hgrad

theorem laplacian_mul
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {f h : M -> Real} {x : M}
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hh : forall y : M, MDifferentiableAt I 𝓘(Real, Real) h y)
    (hgradf : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x)
    (hgradh : MDiffAt (T% fun y : M => gradientFun (I := I) g h y) x)
    (hfgradh : MDiffAt
      (T% (f • fun y : M => gradientFun (I := I) g h y)) x)
    (hhgradf : MDiffAt
      (T% (h • fun y : M => gradientFun (I := I) g f y)) x) :
    laplacian (I := I) cov g (fun y : M => f y * h y) x =
      f x * laplacian (I := I) cov g h x +
        h x * laplacian (I := I) cov g f x +
          2 * g.inner x
            (gradientFun (I := I) g f x)
            (gradientFun (I := I) g h x) := by
  have hgrad_eq :
      gradientFun (I := I) g (fun y : M => f y * h y) =
        fun y : M =>
          f y • gradientFun (I := I) g h y +
            h y • gradientFun (I := I) g f y := by
    funext y
    exact gradientFun_mul (I := I) g (hf y) (hh y)
  calc
    laplacian (I := I) cov g (fun y : M => f y * h y) x =
        divergence (I := I) cov
          (fun y : M =>
            f y • gradientFun (I := I) g h y +
              h y • gradientFun (I := I) g f y) x := by
          simp [laplacian, hgrad_eq]
    _ =
        divergence (I := I) cov
            (f • fun y : M => gradientFun (I := I) g h y) x +
          divergence (I := I) cov
            (h • fun y : M => gradientFun (I := I) g f y) x := by
          change divergence (I := I) cov
              ((f • fun y : M => gradientFun (I := I) g h y) +
                (h • fun y : M => gradientFun (I := I) g f y)) x = _
          exact divergence_add (I := I) cov inferInstance hfgradh hhgradf
    _ =
        (f x * laplacian (I := I) cov g h x +
            g.inner x (gradientFun (I := I) g f x)
              (gradientFun (I := I) g h x)) +
          (h x * laplacian (I := I) cov g f x +
            g.inner x (gradientFun (I := I) g h x)
              (gradientFun (I := I) g f x)) := by
          rw [divergence_smul_gradientFun_pair (I := I) cov g (hf x) hgradh]
          rw [divergence_smul_gradientFun_pair (I := I) cov g (hh x) hgradf]
    _ =
        f x * laplacian (I := I) cov g h x +
          h x * laplacian (I := I) cov g f x +
            2 * g.inner x
              (gradientFun (I := I) g f x)
              (gradientFun (I := I) g h x) := by
          rw [g.symm x (gradientFun (I := I) g h x)
            (gradientFun (I := I) g f x)]
          ring_nf

theorem laplacian_mul_at
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (g : SmoothRiemannianMetric I M)
    {f h : M → Real} {x : M}
    (hf : ∀ᶠ y in nhds x,
      MDifferentiableAt I 𝓘(Real, Real) f y)
    (hh : ∀ᶠ y in nhds x,
      MDifferentiableAt I 𝓘(Real, Real) h y)
    (hgradf : MDiffAt
      (T% fun y : M => gradientFun (I := I) g f y) x)
    (hgradh : MDiffAt
      (T% fun y : M => gradientFun (I := I) g h y) x) :
    laplacian (I := I) cov g (fun y : M => f y * h y) x =
      f x * laplacian (I := I) cov g h x +
        h x * laplacian (I := I) cov g f x +
          2 * g.inner x
            (gradientFun (I := I) g f x)
            (gradientFun (I := I) g h x) := by
  have hfx : MDifferentiableAt I 𝓘(Real, Real) f x :=
    hf.self_of_nhds
  have hhx : MDifferentiableAt I 𝓘(Real, Real) h x :=
    hh.self_of_nhds
  have hleft : MDiffAt
      (T% (f • fun y : M => gradientFun (I := I) g h y)) x :=
    hfx.smul_section hgradh
  have hright : MDiffAt
      (T% (h • fun y : M => gradientFun (I := I) g f y)) x :=
    hhx.smul_section hgradf
  have hsum : MDiffAt
      (T% fun y : M =>
        f y • gradientFun (I := I) g h y +
          h y • gradientFun (I := I) g f y) x :=
    mdifferentiableAt_add_section hleft hright
  have hgrad_eq :
      (fun y : M => gradientFun (I := I) g (fun z : M => f z * h z) y) =ᶠ[nhds x]
        (fun y : M =>
          f y • gradientFun (I := I) g h y +
            h y • gradientFun (I := I) g f y) := by
    filter_upwards [hf, hh] with y hfy hhy
    exact gradientFun_mul (I := I) g hfy hhy
  have hgrad_total :
      (T% fun y : M =>
        gradientFun (I := I) g (fun z : M => f z * h z) y) =ᶠ[nhds x]
        (T% fun y : M =>
          f y • gradientFun (I := I) g h y +
            h y • gradientFun (I := I) g f y) := by
    filter_upwards [hgrad_eq] with y hy
    change TotalSpace.mk' E y
        (gradientFun (I := I) g (fun z : M => f z * h z) y) =
      TotalSpace.mk' E y
        (f y • gradientFun (I := I) g h y +
          h y • gradientFun (I := I) g f y)
    rw [hy]
  have hgrad_mul : MDiffAt
      (T% fun y : M =>
        gradientFun (I := I) g (fun z : M => f z * h z) y) x :=
    hsum.congr_of_eventuallyEq hgrad_total
  have hcov :
      cov.toFun
          (fun y : M => gradientFun (I := I) g (fun z : M => f z * h z) y) x =
        cov.toFun
          (fun y : M =>
            f y • gradientFun (I := I) g h y +
              h y • gradientFun (I := I) g f y) x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hgrad_mul hsum Filter.univ_mem hgrad_eq
  calc
    laplacian (I := I) cov g (fun y : M => f y * h y) x =
        divergence (I := I) cov
          (fun y : M =>
            f y • gradientFun (I := I) g h y +
              h y • gradientFun (I := I) g f y) x := by
      unfold laplacian divergence
      rw [hcov]
    _ = divergence (I := I) cov
          (f • fun y : M => gradientFun (I := I) g h y) x +
        divergence (I := I) cov
          (h • fun y : M => gradientFun (I := I) g f y) x := by
      exact divergence_add (I := I) cov inferInstance hleft hright
    _ = (f x * laplacian (I := I) cov g h x +
          g.inner x (gradientFun (I := I) g f x)
            (gradientFun (I := I) g h x)) +
        (h x * laplacian (I := I) cov g f x +
          g.inner x (gradientFun (I := I) g h x)
            (gradientFun (I := I) g f x)) := by
      rw [divergence_smul_gradientFun_pair (I := I) cov g hfx hgradh]
      rw [divergence_smul_gradientFun_pair (I := I) cov g hhx hgradf]
    _ = f x * laplacian (I := I) cov g h x +
        h x * laplacian (I := I) cov g f x +
          2 * g.inner x
            (gradientFun (I := I) g f x)
            (gradientFun (I := I) g h x) := by
      rw [g.symm x (gradientFun (I := I) g h x)
        (gradientFun (I := I) g f x)]
      ring

theorem laplacian_rpow_at
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M} (p : Real)
    (hf : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hpos : 0 < f x)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x) :
    laplacian (I := I) cov g (fun y : M => f y ^ p) x =
      (p * f x ^ (p - 1)) * laplacian (I := I) cov g f x +
        (p * (p - 1) * f x ^ (p - 2)) *
          g.inner x (gradientFun (I := I) g f x)
            (gradientFun (I := I) g f x) := by
  have hfx := hf.self_of_nhds
  have hpos_near : ∀ᶠ y in nhds x, 0 < f y :=
    hfx.continuousAt.eventually (lt_mem_nhds hpos)
  let coeffFun : M -> Real := fun y => p * f y ^ (p - 1)
  have hcoeff :
      MDifferentiableAt I 𝓘(Real, Real) coeffFun x := by
    have hrpow :
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M => f y ^ (p - 1)) x :=
      mdifferentiableAt_rpow (I := I) (p - 1) hfx hpos
    change MDifferentiableAt I 𝓘(Real, Real)
      ((fun _ : M => p) * fun y : M => f y ^ (p - 1)) x
    exact mdifferentiableAt_const.mul hrpow
  have hcoeffgrad :
      MDiffAt
        (T% (coeffFun • fun y : M => gradientFun (I := I) g f y)) x := by
    exact hcoeff.smul_section hgrad
  have hgrad_eq :
      (fun y : M => gradientFun (I := I) g (fun z => f z ^ p) y) =ᶠ[nhds x]
        (fun y : M => coeffFun y • gradientFun (I := I) g f y) := by
    filter_upwards [hf, hpos_near] with y hfy hpy
    change gradientFun (I := I) g (fun z => f z ^ p) y =
      (p * f y ^ (p - 1)) • gradientFun (I := I) g f y
    exact gradientFun_rpow (I := I) g p hfy hpy
  have hgrad_total :
      (T% fun y : M => gradientFun (I := I) g (fun z => f z ^ p) y) =ᶠ[nhds x]
        (T% (coeffFun • fun y : M => gradientFun (I := I) g f y)) := by
    filter_upwards [hgrad_eq] with y hy
    exact congrArg (TotalSpace.mk' E y) hy
  have hgrad_pow : MDiffAt
      (T% fun y : M => gradientFun (I := I) g (fun z => f z ^ p) y) x :=
    hcoeffgrad.congr_of_eventuallyEq hgrad_total
  have hcov :
      cov (fun y : M => gradientFun (I := I) g (fun z => f z ^ p) y) x =
        cov (coeffFun • fun y : M => gradientFun (I := I) g f y) x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      hgrad_pow hcoeffgrad Filter.univ_mem hgrad_eq
  have hcoeff_ext :
      mvfderiv (I := I) coeffFun x (gradientFun (I := I) g f x) =
        (p * (p - 1) * f x ^ (p - 2)) *
          g.inner x (gradientFun (I := I) g f x)
            (gradientFun (I := I) g f x) := by
    have hrpow :=
      mvfderiv_rpow (I := I) (f := f) (p - 1)
        (gradientFun (I := I) g f x) hfx hpos
    have hrpow_diff :
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M => f y ^ (p - 1)) x :=
      mdifferentiableAt_rpow (I := I) (p - 1) hfx hpos
    have hconst :=
      mvfderiv_const_mul_apply (I := I) p
        (f := fun y : M => f y ^ (p - 1))
        (gradientFun (I := I) g f x) hrpow_diff
    have hfinner :
        mvfderiv (I := I) f x (gradientFun (I := I) g f x) =
          g.inner x (gradientFun (I := I) g f x)
            (gradientFun (I := I) g f x) := by
      exact (inner_gradientFun (I := I) g f x
        (gradientFun (I := I) g f x)).symm
    calc
      mvfderiv (I := I) coeffFun x (gradientFun (I := I) g f x) =
          p * mvfderiv (I := I) (fun y : M => f y ^ (p - 1)) x
            (gradientFun (I := I) g f x) := by
            simpa [coeffFun] using hconst
      _ = p * (((p - 1) * f x ^ ((p - 1) - 1)) *
            mvfderiv (I := I) f x
              (gradientFun (I := I) g f x)) := by
            rw [hrpow]
      _ = (p * (p - 1) * f x ^ (p - 2)) *
          g.inner x (gradientFun (I := I) g f x)
            (gradientFun (I := I) g f x) := by
            rw [hfinner]
            ring_nf
  calc
    laplacian (I := I) cov g (fun y : M => f y ^ p) x =
        divergence (I := I) cov
          (coeffFun • fun y : M => gradientFun (I := I) g f y) x := by
          unfold laplacian divergence
          rw [hcov]
    _ =
        coeffFun x * laplacian (I := I) cov g f x +
          mvfderiv (I := I) coeffFun x
            (gradientFun (I := I) g f x) := by
          change divergence (I := I) cov
              (coeffFun • gradientFun (I := I) g f) x =
            coeffFun x * divergence (I := I) cov (gradientFun (I := I) g f) x +
              mvfderiv (I := I) coeffFun x (gradientFun (I := I) g f x)
          exact divergence_smul (I := I) cov inferInstance hcoeff hgrad
    _ =
        (p * f x ^ (p - 1)) * laplacian (I := I) cov g f x +
          (p * (p - 1) * f x ^ (p - 2)) *
            g.inner x (gradientFun (I := I) g f x)
              (gradientFun (I := I) g f x) := by
          rw [hcoeff_ext]

theorem laplacian_rpow
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M} (p : Real)
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hpos : forall y : M, 0 < f y)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x) :
    laplacian (I := I) cov g (fun y : M => f y ^ p) x =
      (p * f x ^ (p - 1)) * laplacian (I := I) cov g f x +
        (p * (p - 1) * f x ^ (p - 2)) *
          g.inner x (gradientFun (I := I) g f x)
            (gradientFun (I := I) g f x) :=
  laplacian_rpow_at cov g p (Filter.Eventually.of_forall hf) (hpos x) hgrad

theorem laplacian_log
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M}
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hpos : forall y : M, 0 < f y)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x) :
    laplacian (I := I) cov g (fun y : M => Real.log (f y)) x =
      (f x)⁻¹ * laplacian (I := I) cov g f x -
        (f x ^ 2)⁻¹ *
          g.inner x (gradientFun (I := I) g f x)
            (gradientFun (I := I) g f x) := by
  let coeffFun : M -> Real := fun y => f y ^ (-1 : Real)
  have hcoeff : MDifferentiableAt I 𝓘(Real, Real) coeffFun x := by
    exact mdifferentiableAt_rpow (I := I) (-1 : Real) (hf x) (hpos x)
  have hgrad_eq :
      gradientFun (I := I) g (fun y : M => Real.log (f y)) =
        coeffFun • fun y : M => gradientFun (I := I) g f y := by
    funext y
    simpa [coeffFun, Real.rpow_neg_one] using
      gradientFun_log (I := I) g (hf y) (hpos y)
  have hcoeff_ext :
      mvfderiv (I := I) coeffFun x (gradientFun (I := I) g f x) =
        -(f x ^ 2)⁻¹ *
          g.inner x (gradientFun (I := I) g f x)
            (gradientFun (I := I) g f x) := by
    have hrpow :=
      mvfderiv_rpow (I := I) (f := f) (-1 : Real)
        (gradientFun (I := I) g f x) (hf x) (hpos x)
    have hfinner :
        mvfderiv (I := I) f x (gradientFun (I := I) g f x) =
          g.inner x (gradientFun (I := I) g f x)
            (gradientFun (I := I) g f x) := by
      exact (inner_gradientFun (I := I) g f x
        (gradientFun (I := I) g f x)).symm
    calc
      mvfderiv (I := I) coeffFun x (gradientFun (I := I) g f x) =
          ((-1 : Real) * f x ^ ((-1 : Real) - 1)) *
            mvfderiv (I := I) f x
              (gradientFun (I := I) g f x) := by
            simpa [coeffFun] using hrpow
      _ = -(f x ^ 2)⁻¹ *
          g.inner x (gradientFun (I := I) g f x)
            (gradientFun (I := I) g f x) := by
            rw [hfinner]
            rw [show ((-1 : Real) - 1) = -(2 : Real) by norm_num]
            rw [Real.rpow_neg (hpos x).le]
            rw [Real.rpow_two]
            simp only [neg_one_mul]
  calc
    laplacian (I := I) cov g (fun y : M => Real.log (f y)) x =
        divergence (I := I) cov
          (coeffFun • fun y : M => gradientFun (I := I) g f y) x := by
          simp [laplacian, hgrad_eq]
    _ = coeffFun x * laplacian (I := I) cov g f x +
          mvfderiv (I := I) coeffFun x
            (gradientFun (I := I) g f x) := by
          change divergence (I := I) cov
              (coeffFun • gradientFun (I := I) g f) x =
            coeffFun x * divergence (I := I) cov (gradientFun (I := I) g f) x +
              mvfderiv (I := I) coeffFun x (gradientFun (I := I) g f x)
          exact divergence_smul (I := I) cov inferInstance hcoeff hgrad
    _ = (f x)⁻¹ * laplacian (I := I) cov g f x -
        (f x ^ 2)⁻¹ *
          g.inner x (gradientFun (I := I) g f x)
            (gradientFun (I := I) g f x) := by
          rw [hcoeff_ext]
          simp only [coeffFun, Real.rpow_neg_one, sub_eq_add_neg, neg_mul]

theorem half_laplacian_mul_self_eq_divergence_smul_gradientFun
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M}
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hfg : MDiffAt
      (T% (f • fun y : M => gradientFun (I := I) g f y)) x) :
    (1 / 2 : Real) * laplacian (I := I) cov g (fun y : M => f y * f y) x =
      divergence (I := I) cov
        (f • fun y : M => gradientFun (I := I) g f y) x := by
  have hgrad :
      gradientFun (I := I) g (fun y : M => f y * f y) =
        (2 : Real) •
          (f • fun y : M => gradientFun (I := I) g f y) := by
    funext y
    rw [gradientFun_mul_self (I := I) g (hf y)]
    simp [Pi.smul_apply, smul_smul, mul_comm]
  calc
    (1 / 2 : Real) * laplacian (I := I) cov g (fun y : M => f y * f y) x =
        (1 / 2 : Real) *
          divergence (I := I) cov
            ((2 : Real) •
              (f • fun y : M => gradientFun (I := I) g f y)) x := by
      simp [laplacian, hgrad]
    _ = (1 / 2 : Real) *
        (2 * divergence (I := I) cov
          (f • fun y : M => gradientFun (I := I) g f y) x) := by
      rw [divergence_const_smul (I := I) cov inferInstance (2 : Real) hfg]
    _ = divergence (I := I) cov
        (f • fun y : M => gradientFun (I := I) g f y) x := by
      ring_nf

theorem half_laplacian_mul_self
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M}
    (hf_all : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hf_x : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x)
    (hfg : MDiffAt
      (T% (f • fun y : M => gradientFun (I := I) g f y)) x) :
    (1 / 2 : Real) * laplacian (I := I) cov g (fun y : M => f y * f y) x =
      f x * laplacian (I := I) cov g f x +
        g.inner x (gradientFun (I := I) g f x)
          (gradientFun (I := I) g f x) := by
  rw [half_laplacian_mul_self_eq_divergence_smul_gradientFun
    (I := I) cov g hf_all hfg]
  exact divergence_smul_gradientFun (I := I) cov g hf_x hgrad

end AlgebraicRules

end

end CalabiYau.Riemannian
