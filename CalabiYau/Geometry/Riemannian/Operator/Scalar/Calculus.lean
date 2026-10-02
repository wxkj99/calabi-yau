-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Geometry/Operator/Scalar/Calculus.lean
-- Locally modified.
module
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import CalabiYau.Geometry.Riemannian.Metric.Basic
public import CalabiYau.Geometry.Manifold.Bundle.PartialMfderiv.Basic
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

theorem gradientFun_const
    (g : SmoothRiemannianMetric I M) (c : Real) (x : M) :
    gradientFun (I := I) g (fun _ : M => c) x = 0 := by
  apply gradientFun_eq_zero_of_mfderiv_eq_zero
  exact mfderiv_const

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

variable [VectorBundle Real E (TangentSpace I : M -> Type _)] in
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

variable [VectorBundle Real E (TangentSpace I : M -> Type _)] in
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

end AlgebraicRules

end

end CalabiYau.Riemannian
