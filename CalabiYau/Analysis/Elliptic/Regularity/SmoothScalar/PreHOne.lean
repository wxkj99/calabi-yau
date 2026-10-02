-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/SmoothScalar/PreH1.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Riemannian.Operator.Gradient.Basic
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Green.Identities
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Global.CompactSupport
public import CalabiYau.Geometry.Riemannian.Volume.Properties
public import CalabiYau.Geometry.Riemannian.TensorInner.Tangent.Riemannian
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section
open CalabiYau.Riemannian

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace CalabiYau
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

structure SmoothScalar (g : SmoothRiemannianMetric I M) where
  toFun : M → ℝ
  smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ toFun

namespace SmoothScalar

variable {g : SmoothRiemannianMetric I M}

omit [Module.Finite ℝ E] in
@[ext] theorem ext {f h : SmoothScalar g} (hfh : f.toFun = h.toFun) : f = h := by
  cases f; cases h; congr

instance : Zero (SmoothScalar g) where
  zero := { toFun := fun _ => 0, smooth := contMDiff_const }

instance : Add (SmoothScalar g) where
  add f h := { toFun := f.toFun + h.toFun, smooth := f.smooth.add h.smooth }

instance : Neg (SmoothScalar g) where
  neg f := { toFun := -f.toFun, smooth := f.smooth.neg }

instance : Sub (SmoothScalar g) where
  sub f h := { toFun := f.toFun - h.toFun, smooth := f.smooth.sub h.smooth }

instance : SMul ℝ (SmoothScalar g) where
  smul c f :=
    { toFun := c • f.toFun
      smooth := by
        have h : (c • f.toFun) = (fun x : M => c * f.toFun x) := by
          funext x; rfl
        rw [h]
        exact contMDiff_const.mul f.smooth }

omit [Module.Finite ℝ E] in
@[simp] lemma toFun_zero : (0 : SmoothScalar g).toFun = (fun _ : M => 0) := rfl

omit [Module.Finite ℝ E] in
@[simp] lemma toFun_zero_apply (x : M) : (0 : SmoothScalar g).toFun x = 0 := rfl

omit [Module.Finite ℝ E] in
@[simp] lemma toFun_add (f h : SmoothScalar g) :
    (f + h).toFun = f.toFun + h.toFun := rfl

omit [Module.Finite ℝ E] in
@[simp] lemma toFun_add_apply (f h : SmoothScalar g) (x : M) :
    (f + h).toFun x = f.toFun x + h.toFun x := rfl

omit [Module.Finite ℝ E] in
@[simp] lemma toFun_neg (f : SmoothScalar g) :
    (-f).toFun = -f.toFun := rfl

omit [Module.Finite ℝ E] in
@[simp] lemma toFun_neg_apply (f : SmoothScalar g) (x : M) :
    (-f).toFun x = -f.toFun x := rfl

omit [Module.Finite ℝ E] in
@[simp] lemma toFun_sub (f h : SmoothScalar g) :
    (f - h).toFun = f.toFun - h.toFun := rfl

omit [Module.Finite ℝ E] in
@[simp] lemma toFun_sub_apply (f h : SmoothScalar g) (x : M) :
    (f - h).toFun x = f.toFun x - h.toFun x := rfl

omit [Module.Finite ℝ E] in
@[simp] lemma toFun_smul (c : ℝ) (f : SmoothScalar g) :
    (c • f).toFun = c • f.toFun := rfl

omit [Module.Finite ℝ E] in
@[simp] lemma toFun_smul_apply (c : ℝ) (f : SmoothScalar g) (x : M) :
    (c • f).toFun x = c * f.toFun x := rfl

omit [Module.Finite ℝ E] in
lemma toFun_injective :
    Function.Injective (fun f : SmoothScalar g => f.toFun) := by
  intro f h hfh
  exact ext hfh

instance : SMul ℕ (SmoothScalar g) := ⟨nsmulRec⟩
instance : SMul ℤ (SmoothScalar g) := ⟨zsmulRec⟩

omit [Module.Finite ℝ E] in
@[simp] lemma toFun_nsmul (f : SmoothScalar g) (n : ℕ) :
    (n • f).toFun = n • f.toFun := by
  induction n with
  | zero =>
    change (nsmulRec 0 f).toFun = (0 : ℕ) • f.toFun
    change (0 : SmoothScalar g).toFun = (0 : ℕ) • f.toFun
    rw [toFun_zero, zero_nsmul]
    rfl
  | succ n ih =>
    change (nsmulRec (n + 1) f).toFun = (n + 1) • f.toFun
    change (nsmulRec n f + f).toFun = (n + 1) • f.toFun
    have hn : (nsmulRec n f).toFun = n • f.toFun := ih
    rw [toFun_add, hn, succ_nsmul]

omit [Module.Finite ℝ E] in
@[simp] lemma toFun_zsmul (f : SmoothScalar g) (z : ℤ) :
    (z • f).toFun = z • f.toFun := by
  rcases z with n | n
  · change (n • f).toFun = (Int.ofNat n) • f.toFun
    rw [toFun_nsmul]; simp
  · change (-((n + 1) • f)).toFun = (Int.negSucc n) • f.toFun
    rw [toFun_neg, toFun_nsmul]
    show -((n + 1) • f.toFun) = Int.negSucc n • f.toFun
    rw [show (Int.negSucc n : ℤ) = -((n + 1 : ℕ) : ℤ) from rfl,
      neg_zsmul, natCast_zsmul]

instance : AddCommGroup (SmoothScalar g) :=
  toFun_injective.addCommGroup
    (fun f => f.toFun)
    toFun_zero
    toFun_add
    toFun_neg
    toFun_sub
    toFun_nsmul
    toFun_zsmul

def toFunAddHom : SmoothScalar g →+ (M → ℝ) where
  toFun := fun f => f.toFun
  map_zero' := toFun_zero
  map_add' := toFun_add

instance : Module ℝ (SmoothScalar g) :=
  toFun_injective.module ℝ toFunAddHom toFun_smul

end SmoothScalar

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

omit [T2Space M] [CompactSpace M] in
lemma SmoothScalar.continuous_inner_grad
    {g : SmoothRiemannianMetric I M} (f h : SmoothScalar g) :
    Continuous (fun x : M =>
      g.inner x ((gradG (I := I) g ⟨f.toFun, f.smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g ⟨h.toFun, h.smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)) :=
  TangentBundle.continuous_g_inner_of_smooth_sections (I := I) g
    (gradG (I := I) g ⟨f.toFun, f.smooth⟩) (gradG (I := I) g ⟨h.toFun, h.smooth⟩)

omit [Module.Finite ℝ E] [I.Boundaryless] [T2Space M] [CompactSpace M] in
lemma SmoothScalar.continuous_mul {g : SmoothRiemannianMetric I M}
    (f h : SmoothScalar g) :
    Continuous (fun x : M => f.toFun x * h.toFun x) :=
  f.smooth.continuous.mul h.smooth.continuous

omit [I.Boundaryless] in
lemma SmoothScalar.integrable_mul {g : SmoothRiemannianMetric I M}
    (f h : SmoothScalar g) :
    Integrable (fun x : M => f.toFun x * h.toFun x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  have _ : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  exact (f.continuous_mul h).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma SmoothScalar.integrable_inner_grad {g : SmoothRiemannianMetric I M}
    (f h : SmoothScalar g) :
    Integrable (fun x : M =>
        g.inner x ((gradG (I := I) g ⟨f.toFun, f.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((gradG (I := I) g ⟨h.toFun, h.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  have _ : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  exact (f.continuous_inner_grad h).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

def smoothScalarH1Inner {g : SmoothRiemannianMetric I M}
    (f h : SmoothScalar g) : ℝ :=
  (∫ x, f.toFun x * h.toFun x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
  (∫ x, g.inner x ((gradG (I := I) g ⟨f.toFun, f.smooth⟩ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g ⟨h.toFun, h.smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g))

lemma smoothScalarH1Inner_symm {g : SmoothRiemannianMetric I M}
    (f h : SmoothScalar g) :
    smoothScalarH1Inner (I := I) (M := M) f h =
      smoothScalarH1Inner (I := I) (M := M) h f := by
  unfold smoothScalarH1Inner
  congr 1
  · refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x; exact mul_comm _ _
  · refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x
    exact g.symm x _ _

omit [I.Boundaryless] in
lemma SmoothScalar.integral_mul_self_nonneg {g : SmoothRiemannianMetric I M}
    (f : SmoothScalar g) :
    0 ≤ ∫ x, f.toFun x * f.toFun x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  refine integral_nonneg ?_
  intro x
  exact mul_self_nonneg _

omit [Module.Finite ℝ E] [I.Boundaryless] [T2Space M] [CompactSpace M] in
lemma SmoothRiemannianMetric_inner_self_nonneg
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    0 ≤ g.inner x v v := by
  by_cases hv : v = 0
  · subst hv
    simp [map_zero]
  · exact (g.pos x v hv).le

lemma SmoothScalar.integral_inner_grad_self_nonneg
    {g : SmoothRiemannianMetric I M} (f : SmoothScalar g) :
    0 ≤ ∫ x, g.inner x ((gradG (I := I) g ⟨f.toFun, f.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((gradG (I := I) g ⟨f.toFun, f.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  refine integral_nonneg ?_
  intro x
  exact SmoothRiemannianMetric_inner_self_nonneg g x _

lemma smoothScalarH1Inner_nonneg {g : SmoothRiemannianMetric I M}
    (f : SmoothScalar g) :
    0 ≤ smoothScalarH1Inner (I := I) (M := M) f f := by
  unfold smoothScalarH1Inner
  exact add_nonneg f.integral_mul_self_nonneg f.integral_inner_grad_self_nonneg

omit [I.Boundaryless] in
lemma smoothScalar_integral_mul_add_left {g : SmoothRiemannianMetric I M}
    (f₁ f₂ h : SmoothScalar g) :
    (∫ x, (f₁ + f₂).toFun x * h.toFun x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      (∫ x, f₁.toFun x * h.toFun x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
      (∫ x, f₂.toFun x * h.toFun x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  have hpt : ∀ x : M, (f₁ + f₂).toFun x * h.toFun x =
      f₁.toFun x * h.toFun x + f₂.toFun x * h.toFun x := by
    intro x
    rw [SmoothScalar.toFun_add_apply]
    ring
  rw [show (fun x : M => (f₁ + f₂).toFun x * h.toFun x) =
      (fun x : M => f₁.toFun x * h.toFun x + f₂.toFun x * h.toFun x) from
      funext hpt]
  exact integral_add (f₁.integrable_mul h) (f₂.integrable_mul h)

omit [T2Space M] [CompactSpace M] in
lemma SmoothScalar.grad_g_add_apply {g : SmoothRiemannianMetric I M}
    (f₁ f₂ : SmoothScalar g) (x : M) :
    ((gradG (I := I) g ⟨(f₁ + f₂).toFun, (f₁ + f₂).smooth⟩ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      ((gradG (I := I) g ⟨f₁.toFun, f₁.smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) +
      ((gradG (I := I) g ⟨f₂.toFun, f₂.smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) := by
  have hfun : (f₁ + f₂).toFun = f₁.toFun + f₂.toFun := rfl
  change gradFun (I := I) g (f₁ + f₂).toFun x =
    gradFun (I := I) g f₁.toFun x + gradFun (I := I) g f₂.toFun x
  rw [hfun]
  exact gradFun_add (I := I) g (f₁.smooth.mdifferentiable (by simp) x)
    (f₂.smooth.mdifferentiable (by simp) x)

lemma smoothScalar_integral_inner_grad_add_left
    {g : SmoothRiemannianMetric I M}
    (f₁ f₂ h : SmoothScalar g) :
    (∫ x, g.inner x ((gradG (I := I) g ⟨(f₁ + f₂).toFun, (f₁ + f₂).smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((gradG (I := I) g ⟨h.toFun, h.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      (∫ x, g.inner x ((gradG (I := I) g ⟨f₁.toFun, f₁.smooth⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((gradG (I := I) g ⟨h.toFun, h.smooth⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
      (∫ x, g.inner x ((gradG (I := I) g ⟨f₂.toFun, f₂.smooth⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((gradG (I := I) g ⟨h.toFun, h.smooth⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  have hpt : ∀ x : M, g.inner x
      ((gradG (I := I) g ⟨(f₁ + f₂).toFun, (f₁ + f₂).smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
      ((gradG (I := I) g ⟨h.toFun, h.smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      g.inner x
        ((gradG (I := I) g ⟨f₁.toFun, f₁.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g ⟨h.toFun, h.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) +
      g.inner x
        ((gradG (I := I) g ⟨f₂.toFun, f₂.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g ⟨h.toFun, h.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) := by
    intro x
    rw [SmoothScalar.grad_g_add_apply f₁ ⟨f₂.toFun, f₂.smooth⟩ x]
    rw [map_add, add_apply]
  rw [show (fun x : M => g.inner x
      ((gradG (I := I) g ⟨(f₁ + f₂).toFun, (f₁ + f₂).smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
      ((gradG (I := I) g ⟨h.toFun, h.smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)) =
      (fun x : M => g.inner x
        ((gradG (I := I) g ⟨f₁.toFun, f₁.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g ⟨h.toFun, h.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) +
      g.inner x
        ((gradG (I := I) g ⟨f₂.toFun, f₂.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g ⟨h.toFun, h.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)) from funext hpt]
  exact integral_add (f₁.integrable_inner_grad h) (f₂.integrable_inner_grad h)

lemma smoothScalarH1Inner_add_left {g : SmoothRiemannianMetric I M}
    (f₁ f₂ h : SmoothScalar g) :
    smoothScalarH1Inner (I := I) (M := M) (f₁ + f₂) h =
      smoothScalarH1Inner (I := I) (M := M) f₁ h +
      smoothScalarH1Inner (I := I) (M := M) f₂ h := by
  unfold smoothScalarH1Inner
  rw [smoothScalar_integral_mul_add_left, smoothScalar_integral_inner_grad_add_left]
  ring

omit [T2Space M] [CompactSpace M] in
lemma SmoothScalar.grad_g_smul_apply {g : SmoothRiemannianMetric I M}
    (c : ℝ) (f : SmoothScalar g) (x : M) :
    ((gradG (I := I) g ⟨(c • f).toFun, (c • f).smooth⟩ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      c • ((gradG (I := I) g ⟨f.toFun, f.smooth⟩ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) := by
  change gradFun (I := I) g (c • f).toFun x =
    c • gradFun (I := I) g f.toFun x
  apply metricFlatLinear_injective (I := I) g x
  ext v
  change g.inner x (gradFun (I := I) g (c • f.toFun) x) v =
    g.inner x (c • gradFun (I := I) g f.toFun x) v
  rw [inner_gradFun (I := I) g (c • f.toFun) x v]
  rw [show g.inner x (c • gradFun (I := I) g f.toFun x) v =
      c * g.inner x (gradFun (I := I) g f.toFun x) v from ?_]
  swap
  · rw [map_smul, smul_apply, smul_eq_mul]
  rw [inner_gradFun (I := I) g f.toFun x v]
  set d_f : TangentSpace I x →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) f.toFun x with hd_f_def
  have hHaf : HasMFDerivAt I 𝓘(ℝ, ℝ) f.toFun x d_f := by
    rw [hd_f_def]
    exact (f.smooth.mdifferentiable (by simp) x).hasMFDerivAt
  have hHa_smul : HasMFDerivAt I 𝓘(ℝ, ℝ) (c • f.toFun) x (c • d_f) :=
    hHaf.const_smul c
  have hd_smul : mfderiv I 𝓘(ℝ, ℝ) (c • f.toFun) x = c • d_f :=
    hHa_smul.mfderiv
  rw [hd_smul]
  change (c • d_f) v = c * d_f v
  rw [smul_apply, smul_eq_mul]

omit [I.Boundaryless] in
lemma smoothScalar_integral_mul_smul_left {g : SmoothRiemannianMetric I M}
    (c : ℝ) (f h : SmoothScalar g) :
    (∫ x, (c • f).toFun x * h.toFun x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      c * (∫ x, f.toFun x * h.toFun x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  have hpt : (fun x : M => (c • f).toFun x * h.toFun x) =
      (fun x : M => c * (f.toFun x * h.toFun x)) := by
    funext x; rw [SmoothScalar.toFun_smul_apply]; ring
  rw [hpt]
  rw [integral_const_mul]

lemma smoothScalar_integral_inner_grad_smul_left
    {g : SmoothRiemannianMetric I M} (c : ℝ) (f h : SmoothScalar g) :
    (∫ x, g.inner x ((gradG (I := I) g ⟨(c • f).toFun, (c • f).smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((gradG (I := I) g ⟨h.toFun, h.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      c * (∫ x, g.inner x ((gradG (I := I) g ⟨f.toFun, f.smooth⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((gradG (I := I) g ⟨h.toFun, h.smooth⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  have hpt : (fun x : M => g.inner x
      ((gradG (I := I) g ⟨(c • f).toFun, (c • f).smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
      ((gradG (I := I) g ⟨h.toFun, h.smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)) =
      (fun x : M => c * g.inner x
        ((gradG (I := I) g ⟨f.toFun, f.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g ⟨h.toFun, h.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)) := by
    funext x
    rw [SmoothScalar.grad_g_smul_apply c f x]
    rw [map_smul, smul_apply, smul_eq_mul]
  rw [hpt, integral_const_mul]

lemma smoothScalarH1Inner_smul_left {g : SmoothRiemannianMetric I M}
    (c : ℝ) (f h : SmoothScalar g) :
    smoothScalarH1Inner (I := I) (M := M) (c • f) h =
      c * smoothScalarH1Inner (I := I) (M := M) f h := by
  unfold smoothScalarH1Inner
  rw [smoothScalar_integral_mul_smul_left, smoothScalar_integral_inner_grad_smul_left]
  ring

noncomputable instance instPreInnerProductSpaceCoreSmoothScalar
    {g : SmoothRiemannianMetric I M} :
    PreInnerProductSpace.Core ℝ (SmoothScalar g) where
  inner f h := smoothScalarH1Inner (I := I) (M := M) f h
  conj_inner_symm f h := by
    change (smoothScalarH1Inner (I := I) (M := M) h f : ℝ) =
      smoothScalarH1Inner (I := I) (M := M) f h
    exact smoothScalarH1Inner_symm h f
  re_inner_nonneg f := by
    change (0 : ℝ) ≤ smoothScalarH1Inner (I := I) (M := M) f f
    exact smoothScalarH1Inner_nonneg f
  add_left f₁ f₂ h := by
    change smoothScalarH1Inner (I := I) (M := M) (f₁ + f₂) h =
      smoothScalarH1Inner (I := I) (M := M) f₁ h +
      smoothScalarH1Inner (I := I) (M := M) f₂ h
    exact smoothScalarH1Inner_add_left f₁ f₂ h
  smul_left f h c := by
    change smoothScalarH1Inner (I := I) (M := M) (c • f) h =
      c * smoothScalarH1Inner (I := I) (M := M) f h
    exact smoothScalarH1Inner_smul_left c f h

noncomputable instance instSeminormedAddCommGroupSmoothScalar
    {g : SmoothRiemannianMetric I M} :
    SeminormedAddCommGroup (SmoothScalar g) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ)

noncomputable instance instInnerProductSpaceSmoothScalar
    {g : SmoothRiemannianMetric I M} :
    InnerProductSpace ℝ (SmoothScalar g) :=
  InnerProductSpace.ofCore _

@[simp] lemma SmoothScalar.inner_def {g : SmoothRiemannianMetric I M}
    (f h : SmoothScalar g) :
    @inner ℝ _ _ f h = smoothScalarH1Inner (I := I) (M := M) f h := rfl

end Laplacian
end Analysis

end CalabiYau

end
