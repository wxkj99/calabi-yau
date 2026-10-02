-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Intrinsic/Lp/Basic.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Intrinsic.Defs
public import CalabiYau.Geometry.Riemannian.Operator.Gradient.Basic
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Global.IntegrationByParts
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Local.Formula
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Global.PartitionOfUnity
public import CalabiYau.Geometry.Riemannian.Operator.DirectionalDerivative
public import Mathlib.Geometry.Manifold.DerivationBundle
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Analysis.InnerProductSpace.Dual
public import CalabiYau.Geometry.Manifold.Bundle.Section
public import CalabiYau.Geometry.Manifold.Tensor.RSTensor.Defs
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.RingTheory.Derivation.Lie
public import CalabiYau.Geometry.Riemannian.L2.Basic
public import CalabiYau.Geometry.Riemannian.Volume.Properties
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.ContMDiffMap
public import Mathlib.Geometry.Manifold.SmoothApprox
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import CalabiYau.Geometry.Riemannian.Volume.Basic
public import CalabiYau.Geometry.Riemannian.Volume.Invariance
public import CalabiYau.Geometry.Riemannian.TensorInner.Tangent.Riemannian
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

@[expose] public section

-- Module-system compatibility (see NOTICE): upstream builds with `maxSynthPendingDepth = 3`,
-- and its private helpers occur in public declarations.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Function CalabiYau CalabiYau.Riemannian
open scoped Manifold Topology ContDiff ENNReal NNReal Matrix

namespace Sobolev
namespace IntrinsicLp
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.L2
open Sobolev.Intrinsic

variable [Module.Finite ℝ E] in
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} in
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in
private local instance : MeasurableSpace E := borel E
variable [Module.Finite ℝ E] in
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} in
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in
private local instance : BorelSpace E := ⟨rfl⟩
variable [Module.Finite ℝ E] in
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} in
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in
private local instance : MeasurableSpace M := borel M
variable [Module.Finite ℝ E] in
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} in
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in
private local instance : BorelSpace M := ⟨rfl⟩

section

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private lemma g_inner_add_left
    (g : SmoothRiemannianMetric I M) (x : M) (v w y : TangentSpace I x) :
    g.inner x (v + w) y = g.inner x v y + g.inner x w y := by
  rw [map_add (g.inner x), add_apply]

private lemma g_inner_add_right
    (g : SmoothRiemannianMetric I M) (x : M) (v y w : TangentSpace I x) :
    g.inner x v (y + w) = g.inner x v y + g.inner x v w :=
  ContinuousLinearMap.map_add (g.inner x v) y w

private lemma g_inner_smul_left
    (g : SmoothRiemannianMetric I M) (x : M) (c : ℝ) (v y : TangentSpace I x) :
    g.inner x (c • v) y = c * g.inner x v y := by
  rw [map_smul (g.inner x), smul_apply, smul_eq_mul]

private lemma g_inner_smul_right
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) (c : ℝ)
    (y : TangentSpace I x) :
    g.inner x v (c • y) = c * g.inner x v y := by
  rw [ContinuousLinearMap.map_smul, smul_eq_mul]

private lemma g_inner_zero_left
    (g : SmoothRiemannianMetric I M) (x : M) (y : TangentSpace I x) :
    g.inner x (0 : TangentSpace I x) y = 0 := by
  rw [map_zero, zero_apply]

private lemma g_inner_neg_left
    (g : SmoothRiemannianMetric I M) (x : M) (v y : TangentSpace I x) :
    g.inner x (-v) y = - g.inner x v y := by
  rw [map_neg, neg_apply]

private lemma g_inner_neg_right
    (g : SmoothRiemannianMetric I M) (x : M) (v y : TangentSpace I x) :
    g.inner x v (-y) = - g.inner x v y := by
  rw [ContinuousLinearMap.map_neg]

private lemma g_inner_add_diag
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    g.inner x (v + w) (v + w) =
      g.inner x v v + 2 * g.inner x v w + g.inner x w w := by
  rw [g_inner_add_left g x v w (v + w),
    g_inner_add_right g x v v w, g_inner_add_right g x w v w]
  have hsymm : g.inner x w v = g.inner x v w := g.symm x w v
  rw [hsymm]; ring

private lemma g_inner_smul_add_diag
    (g : SmoothRiemannianMetric I M) (x : M) (t : ℝ) (v w : TangentSpace I x) :
    g.inner x (t • v + w) (t • v + w) =
      t * t * g.inner x v v + 2 * t * g.inner x v w + g.inner x w w := by
  rw [g_inner_add_left g x (t • v) w (t • v + w),
    g_inner_add_right g x (t • v) (t • v) w,
    g_inner_add_right g x w (t • v) w]
  rw [g_inner_smul_left g x t v (t • v), g_inner_smul_right g x v t v,
    g_inner_smul_left g x t v w, g_inner_smul_right g x w t v]
  have hsymm : g.inner x w v = g.inner x v w := g.symm x w v
  rw [hsymm]; ring

private lemma g_inner_cauchy_schwarz
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    |g.inner x v w| ≤ Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) := by
  set a := g.inner x v v
  set b := g.inner x w w
  set c := g.inner x v w
  have ha_nn : 0 ≤ a := by
    rcases eq_or_ne v 0 with hv0 | hv0
    · simp [a, hv0]
    · exact (g.pos x v hv0).le
  have hb_nn : 0 ≤ b := by
    rcases eq_or_ne w 0 with hw0 | hw0
    · simp [b, hw0]
    · exact (g.pos x w hw0).le
  have hquad : ∀ t : ℝ, 0 ≤ t * t * a + 2 * t * c + b := by
    intro t
    have hpos : 0 ≤ g.inner x (t • v + w) (t • v + w) := by
      rcases eq_or_ne (t • v + w) 0 with hz | hnz
      · rw [hz, g_inner_zero_left]
      · exact (g.pos x _ hnz).le
    have h_expand := g_inner_smul_add_diag g x t v w
    rw [h_expand] at hpos
    exact hpos
  have hCS_sq : c ^ 2 ≤ a * b := by
    rcases lt_or_eq_of_le ha_nn with ha_pos | ha_zero
    · have hroot := hquad (-c / a)
      have ha_ne : a ≠ 0 := ne_of_gt ha_pos
      have hsimp : -c / a * (-c / a) * a + 2 * (-c / a) * c + b =
          b - c^2 / a := by field_simp; ring
      rw [hsimp] at hroot
      have hcsa : c ^ 2 / a ≤ b := by linarith
      have h1 : c ^ 2 = a * (c ^ 2 / a) := by field_simp
      rw [h1]
      exact mul_le_mul_of_nonneg_left hcsa ha_nn
    · have ha_eq : a = 0 := ha_zero.symm
      have hv_zero : v = 0 := by
        by_contra hne
        have hpos : 0 < g.inner x v v := g.pos x v hne
        rw [show g.inner x v v = a from rfl, ha_eq] at hpos
        exact lt_irrefl 0 hpos
      have hc_eq : c = 0 := by
        change g.inner x v w = 0
        rw [hv_zero]
        exact g_inner_zero_left g x w
      rw [hc_eq, ha_eq]; simp
  have hC : |c| ≤ Real.sqrt (a * b) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hCS_sq
  have hsqrt_mul : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b :=
    Real.sqrt_mul ha_nn b
  rw [hsqrt_mul] at hC
  exact hC

private lemma g_norm_triangle
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    Real.sqrt (g.inner x (v + w) (v + w)) ≤
      Real.sqrt (g.inner x v v) + Real.sqrt (g.inner x w w) := by
  set a := g.inner x v v
  set b := g.inner x w w
  set c := g.inner x v w
  have ha_nn : 0 ≤ a := by
    rcases eq_or_ne v 0 with hv0 | hv0
    · simp [a, hv0]
    · exact (g.pos x v hv0).le
  have hb_nn : 0 ≤ b := by
    rcases eq_or_ne w 0 with hw0 | hw0
    · simp [b, hw0]
    · exact (g.pos x w hw0).le
  have h_expand := g_inner_add_diag g x v w
  rw [h_expand]
  have hCS : |c| ≤ Real.sqrt a * Real.sqrt b :=
    g_inner_cauchy_schwarz g x v w
  have hc_le : c ≤ Real.sqrt a * Real.sqrt b :=
    (le_abs_self c).trans hCS
  have h_le_sq : a + 2 * c + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    have h_sq_expand : (Real.sqrt a + Real.sqrt b) ^ 2 =
        a + 2 * (Real.sqrt a * Real.sqrt b) + b := by
      have ha_sq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha_nn
      have hb_sq : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb_nn
      nlinarith [ha_sq, hb_sq]
    rw [h_sq_expand]
    linarith
  have h_nn : 0 ≤ Real.sqrt a + Real.sqrt b :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h_sqrt_le := Real.sqrt_le_sqrt h_le_sq
  rw [show Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) = Real.sqrt a + Real.sqrt b
      from Real.sqrt_sq h_nn] at h_sqrt_le
  exact h_sqrt_le

private lemma g_norm_const_smul
    (g : SmoothRiemannianMetric I M) (x : M) (c : ℝ) (v : TangentSpace I x) :
    Real.sqrt (g.inner x (c • v) (c • v)) =
      |c| * Real.sqrt (g.inner x v v) := by
  rw [g_inner_smul_left g x c v (c • v), g_inner_smul_right g x v c v]
  rw [show c * (c * g.inner x v v) = c ^ 2 * g.inner x v v from by ring]
  rw [Real.sqrt_mul (sq_nonneg c)]
  rw [Real.sqrt_sq_eq_abs]

private lemma g_norm_neg
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    Real.sqrt (g.inner x (-v) (-v)) = Real.sqrt (g.inner x v v) := by
  rw [g_inner_neg_left g x v (-v), g_inner_neg_right g x v v]
  simp

private lemma continuous_g_inner_smooth_sections
    (g : SmoothRiemannianMetric I M)
    (G X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Continuous (fun b : M => g.inner b (G b) (X b)) :=
  TangentBundle.continuous_g_inner_of_smooth_sections (I := I) (M := M) g G X

private lemma continuous_g_norm_smooth_section
    (g : SmoothRiemannianMetric I M)
    (G : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Continuous (fun b : M => Real.sqrt (g.inner b (G b) (G b))) :=
  Real.continuous_sqrt.comp (continuous_g_inner_smooth_sections g G G)

end

section

variable [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def HasWeakRiemannianGradLp
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (u : M → ℝ) (G : M → E) : Prop :=
  (∀ Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯,
    AEStronglyMeasurable (fun x : M => g.inner x (G x) (Y x))
      (riemannianVolumeMeasure I M g)) ∧
  ∀ X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯,
    HasCompactSupport (fun x : M => (X x : E)) →
      ∫ x, g.inner x (G x) (X x) ∂(riemannianVolumeMeasure I M g) =
        -∫ x, u x * divergenceG (I := I) g X x
          ∂(riemannianVolumeMeasure I M g)

end

namespace HasWeakRiemannianGradLp


section

variable [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {g : SmoothRiemannianMetric I M} {u : M → ℝ} {G : M → E}

lemma pairing_eq
    [T2Space M] [SigmaCompactSpace M] (h : HasWeakRiemannianGradLp (I := I) (M := M) g u G)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : HasCompactSupport (fun x : M => (X x : E))) :
    ∫ x, g.inner x (G x) (X x) ∂(riemannianVolumeMeasure I M g) =
      -∫ x, u x * divergenceG (I := I) g X x
        ∂(riemannianVolumeMeasure I M g) := h.2 X hX

end

end HasWeakRiemannianGradLp

section

variable [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def MemW1pIntrinsicLp
    [T2Space M] [SigmaCompactSpace M] (g : SmoothRiemannianMetric I M) (p : ℝ≥0∞) (u : M → ℝ) : Prop :=
  MemLp u p (riemannianVolumeMeasure I M g) ∧
  ∃ G : M → E, HasWeakRiemannianGradLp (I := I) (M := M) g u G ∧
      MemLp (fun x : M => Real.sqrt (g.inner x (G x) (G x))) p
        (riemannianVolumeMeasure I M g)

lemma MemW1pIntrinsicLp.memLp_self
    [T2Space M] [SigmaCompactSpace M] {g : SmoothRiemannianMetric I M} {p : ℝ≥0∞} {u : M → ℝ}
    (h : MemW1pIntrinsicLp (I := I) (M := M) g p u) :
    MemLp u p (riemannianVolumeMeasure I M g) := h.1

theorem HasWeakRiemannianGradLp.zero
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) :
    HasWeakRiemannianGradLp (I := I) (M := M) g (fun _ : M => (0 : ℝ))
      (fun _ : M => (0 : E)) := by
  refine ⟨?_, ?_⟩
  · intro Y
    have hcongr : (fun x : M =>
        g.inner x ((fun _ : M => (0 : E)) x) (Y x)) =
        (fun _ : M => (0 : ℝ)) := by
      funext x
      change g.inner x (0 : TangentSpace I x) (Y x) = 0
      exact g_inner_zero_left g x (Y x)
    rw [hcongr]
    exact aestronglyMeasurable_const
  · intro X _
    have h_LHS : (fun x : M =>
        g.inner x ((fun _ : M => (0 : E)) x) (X x)) =
        (fun _ : M => (0 : ℝ)) := by
      funext x
      change g.inner x (0 : TangentSpace I x) (X x) = 0
      exact g_inner_zero_left g x (X x)
    rw [h_LHS]
    rw [show (fun x : M => (0 : ℝ) * divergenceG (I := I) g X x) =
        (fun _ : M => (0 : ℝ)) from by funext x; simp]
    simp [integral_zero]

theorem MemW1pIntrinsicLp.zero
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (p : ℝ≥0∞) :
    MemW1pIntrinsicLp (I := I) (M := M) g p (fun _ : M => (0 : ℝ)) := by
  let _ := (inferInstance : (I.Boundaryless))
  refine ⟨MemLp.zero, (fun _ : M => (0 : E)),
    HasWeakRiemannianGradLp.zero (I := I) (M := M) g, ?_⟩
  have hcongr : (fun x : M => Real.sqrt
      (g.inner x ((fun _ : M => (0 : E)) x) ((fun _ : M => (0 : E)) x))) =
      (fun _ : M => (0 : ℝ)) := by
    funext x
    change Real.sqrt (g.inner x (0 : TangentSpace I x) (0 : TangentSpace I x)) = 0
    rw [g_inner_zero_left g x (0 : TangentSpace I x)]
    exact Real.sqrt_zero
  rw [hcongr]
  exact MemLp.zero

theorem HasWeakRiemannianGradLp.add
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u v : M → ℝ} {G G' : M → E}
    (h₁ : HasWeakRiemannianGradLp (I := I) (M := M) g u G)
    (h₂ : HasWeakRiemannianGradLp (I := I) (M := M) g v G')
    (hu : MemLp u p (riemannianVolumeMeasure I M g))
    (hv : MemLp v p (riemannianVolumeMeasure I M g))
    (hGn : MemLp (fun x : M => Real.sqrt (g.inner x (G x) (G x))) p
      (riemannianVolumeMeasure I M g))
    (hG'n : MemLp (fun x : M => Real.sqrt (g.inner x (G' x) (G' x))) p
      (riemannianVolumeMeasure I M g)) :
    HasWeakRiemannianGradLp (I := I) (M := M) g
      (fun x => u x + v x) (fun x : M => G x + G' x) := by
  have : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  refine ⟨?_, ?_⟩
  · intro Y
    have hcongr : (fun x : M =>
        g.inner x ((fun y : M => G y + G' y) x) (Y x)) =
        (fun x : M => g.inner x (G x) (Y x) +
          g.inner x (G' x) (Y x)) := by
      funext x
      exact g_inner_add_left g x (G x) (G' x) (Y x)
    rw [hcongr]
    exact (h₁.1 Y).add (h₂.1 Y)
  · intro X hX
    have hpt : ∀ x : M,
        g.inner x ((fun y : M => G y + G' y) x) (X x) =
          g.inner x (G x) (X x) + g.inner x (G' x) (X x) := by
      intro x
      exact g_inner_add_left g x (G x) (G' x) (X x)
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    have hX_norm_cont : Continuous (fun x : M =>
        Real.sqrt (g.inner x (X x) (X x))) :=
      continuous_g_norm_smooth_section g X
    obtain ⟨C_X, hC_X⟩ := Intrinsic.exists_bound_continuous_compactSpace hX_norm_cont
    have h_bound_aux : ∀ (W : M → E), ∀ x : M,
        |g.inner x (W x) (X x)| ≤
          C_X * Real.sqrt (g.inner x (W x) (W x)) := by
      intro W x
      have hCS := g_inner_cauchy_schwarz g x (W x) (X x)
      have hX_bd : Real.sqrt (g.inner x (X x) (X x)) ≤ C_X := by
        have h := hC_X x
        have hnn : 0 ≤ Real.sqrt (g.inner x (X x) (X x)) := Real.sqrt_nonneg _
        rw [abs_of_nonneg hnn] at h; exact h
      calc |g.inner x (W x) (X x)|
          ≤ Real.sqrt (g.inner x (W x) (W x)) * Real.sqrt (g.inner x (X x) (X x)) := hCS
        _ ≤ Real.sqrt (g.inner x (W x) (W x)) * C_X :=
              mul_le_mul_of_nonneg_left hX_bd (Real.sqrt_nonneg _)
        _ = C_X * Real.sqrt (g.inner x (W x) (W x)) := by ring
    have h_int_G : Integrable (fun x : M => g.inner x (G x) (X x))
        (riemannianVolumeMeasure I M g) := by
      have hG_one : MemLp (fun x : M =>
          Real.sqrt (g.inner x (G x) (G x))) 1
          (riemannianVolumeMeasure I M g) :=
        hGn.mono_exponent hp
      have hG_int : Integrable (fun x : M =>
          Real.sqrt (g.inner x (G x) (G x)))
          (riemannianVolumeMeasure I M g) :=
        memLp_one_iff_integrable.mp hG_one
      refine Integrable.mono' (g := fun x : M =>
          C_X * Real.sqrt (g.inner x (G x) (G x))) ?_ (h₁.1 X) ?_
      · exact hG_int.const_mul C_X
      · refine Filter.Eventually.of_forall (fun x => ?_)
        rw [Real.norm_eq_abs]
        exact h_bound_aux G x
    have h_int_G' : Integrable (fun x : M => g.inner x (G' x) (X x))
        (riemannianVolumeMeasure I M g) := by
      have hG'_one : MemLp (fun x : M =>
          Real.sqrt (g.inner x (G' x) (G' x))) 1
          (riemannianVolumeMeasure I M g) :=
        hG'n.mono_exponent hp
      have hG'_int : Integrable (fun x : M =>
          Real.sqrt (g.inner x (G' x) (G' x)))
          (riemannianVolumeMeasure I M g) :=
        memLp_one_iff_integrable.mp hG'_one
      refine Integrable.mono' (g := fun x : M =>
          C_X * Real.sqrt (g.inner x (G' x) (G' x))) ?_ (h₂.1 X) ?_
      · exact hG'_int.const_mul C_X
      · refine Filter.Eventually.of_forall (fun x => ?_)
        rw [Real.norm_eq_abs]
        exact h_bound_aux G' x
    rw [integral_add h_int_G h_int_G']
    rw [h₁.pairing_eq X hX, h₂.pairing_eq X hX]
    have h_div_cont : Continuous (divergenceG (I := I) g X) :=
      (divergence_g_contMDiff (I := I) g X).continuous
    have h_int_uX : Integrable (fun x : M => u x * divergenceG (I := I) g X x)
        (riemannianVolumeMeasure I M g) := by
      have hu_one : MemLp u 1 (riemannianVolumeMeasure I M g) :=
        hu.mono_exponent hp
      have hu_int : Integrable u (riemannianVolumeMeasure I M g) :=
        memLp_one_iff_integrable.mp hu_one
      obtain ⟨C, hC⟩ := Intrinsic.exists_bound_continuous_compactSpace h_div_cont
      refine hu_int.mul_bdd (c := C) ?_ ?_
      · exact h_div_cont.aestronglyMeasurable
      · filter_upwards with x
        rw [Real.norm_eq_abs]
        exact hC x
    have h_int_vX : Integrable (fun x : M => v x * divergenceG (I := I) g X x)
        (riemannianVolumeMeasure I M g) := by
      have hv_one : MemLp v 1 (riemannianVolumeMeasure I M g) :=
        hv.mono_exponent hp
      have hv_int : Integrable v (riemannianVolumeMeasure I M g) :=
        memLp_one_iff_integrable.mp hv_one
      obtain ⟨C, hC⟩ := Intrinsic.exists_bound_continuous_compactSpace h_div_cont
      refine hv_int.mul_bdd (c := C) ?_ ?_
      · exact h_div_cont.aestronglyMeasurable
      · filter_upwards with x
        rw [Real.norm_eq_abs]
        exact hC x
    rw [show (-∫ x, u x * divergenceG (I := I) g X x
              ∂(riemannianVolumeMeasure I M g)) +
          (-∫ x, v x * divergenceG (I := I) g X x
              ∂(riemannianVolumeMeasure I M g)) =
        -((∫ x, u x * divergenceG (I := I) g X x
              ∂(riemannianVolumeMeasure I M g)) +
          (∫ x, v x * divergenceG (I := I) g X x
              ∂(riemannianVolumeMeasure I M g))) from by ring]
    rw [← integral_add h_int_uX h_int_vX]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x
    ring

theorem HasWeakRiemannianGradLp.const_smul
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (c : ℝ) {u : M → ℝ} {G : M → E}
    (h : HasWeakRiemannianGradLp (I := I) (M := M) g u G)
    (hu : MemLp u p (riemannianVolumeMeasure I M g)) :
    HasWeakRiemannianGradLp (I := I) (M := M) g (fun x => c * u x)
      (fun x : M => c • G x) := by
  have : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  refine ⟨?_, ?_⟩
  · intro Y
    have hcongr : (fun x : M =>
        g.inner x ((fun y : M => c • G y) x) (Y x)) =
        (fun x : M => c * g.inner x (G x) (Y x)) := by
      funext x
      exact g_inner_smul_left g x c (G x) (Y x)
    rw [hcongr]
    exact (h.1 Y).const_mul c
  · intro X hX
    have hpt : ∀ x : M,
        g.inner x ((fun y : M => c • G y) x) (X x) =
          c * g.inner x (G x) (X x) := by
      intro x
      exact g_inner_smul_left g x c (G x) (X x)
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [integral_const_mul c]
    rw [h.pairing_eq X hX]
    have h_div_cont : Continuous (divergenceG (I := I) g X) :=
      (divergence_g_contMDiff (I := I) g X).continuous
    have h_int_uX : Integrable (fun x : M => u x * divergenceG (I := I) g X x)
        (riemannianVolumeMeasure I M g) := by
      have hu_one : MemLp u 1 (riemannianVolumeMeasure I M g) :=
        hu.mono_exponent hp
      have hu_int : Integrable u (riemannianVolumeMeasure I M g) :=
        memLp_one_iff_integrable.mp hu_one
      obtain ⟨C, hC⟩ := Intrinsic.exists_bound_continuous_compactSpace h_div_cont
      refine hu_int.mul_bdd (c := C) ?_ ?_
      · exact h_div_cont.aestronglyMeasurable
      · filter_upwards with x
        rw [Real.norm_eq_abs]
        exact hC x
    have hcong : (fun x : M => (c * u x) * divergenceG (I := I) g X x) =
        (fun x : M => c * (u x * divergenceG (I := I) g X x)) := by
      funext x; ring
    rw [hcong, integral_const_mul]
    ring

theorem MemW1pIntrinsicLp.const_smul
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (c : ℝ) {u : M → ℝ}
    (hu : MemW1pIntrinsicLp (I := I) (M := M) g p u) :
    MemW1pIntrinsicLp (I := I) (M := M) g p (fun x => c * u x) := by
  obtain ⟨hu_p, G, hG_weak, hG_p⟩ := hu
  refine ⟨hu_p.const_mul c, (fun x : M => c • G x), ?_, ?_⟩
  · exact HasWeakRiemannianGradLp.const_smul (I := I) (M := M) hp c hG_weak hu_p
  · have hcongr : (fun x : M => Real.sqrt
        (g.inner x ((fun y : M => c • G y) x)
          ((fun y : M => c • G y) x))) =
        (fun x : M => |c| * Real.sqrt (g.inner x (G x) (G x))) := by
      funext x
      exact g_norm_const_smul g x c (G x)
    rw [hcongr]
    exact hG_p.const_mul (|c|)

theorem HasWeakRiemannianGradLp.neg
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u : M → ℝ} {G : M → E}
    (h : HasWeakRiemannianGradLp (I := I) (M := M) g u G)
    (hu : MemLp u p (riemannianVolumeMeasure I M g)) :
    HasWeakRiemannianGradLp (I := I) (M := M) g (fun x => -u x)
      (fun x : M => -G x) := by
  have h1 : HasWeakRiemannianGradLp (I := I) (M := M) g (fun x => (-1 : ℝ) * u x)
      (fun x : M => (-1 : ℝ) • G x) :=
    HasWeakRiemannianGradLp.const_smul (I := I) (M := M) hp (-1) h hu
  have h_u : (fun x : M => (-1 : ℝ) * u x) = (fun x => -u x) := by
    funext x; ring
  have h_G : (fun x : M => (-1 : ℝ) • G x) = (fun x : M => -G x) := by
    funext x; rw [neg_one_smul]
  rw [h_u] at h1
  rw [h_G] at h1
  exact h1

theorem MemW1pIntrinsicLp.neg
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u : M → ℝ}
    (hu : MemW1pIntrinsicLp (I := I) (M := M) g p u) :
    MemW1pIntrinsicLp (I := I) (M := M) g p (fun x => -u x) := by
  have h := MemW1pIntrinsicLp.const_smul (I := I) (M := M) hp (-1) hu
  have h_eq : (fun x : M => (-1 : ℝ) * u x) = (fun x => -u x) := by
    funext x; ring
  rw [h_eq] at h
  exact h

theorem HasWeakRiemannianGradLp.pairing_inner_eq
    [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {u : M → ℝ}
    {G G' : M → E}
    (h₁ : HasWeakRiemannianGradLp (I := I) (M := M) g u G)
    (h₂ : HasWeakRiemannianGradLp (I := I) (M := M) g u G')
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : HasCompactSupport (fun x : M => (X x : E))) :
    ∫ x, g.inner x (G x) (X x) ∂(riemannianVolumeMeasure I M g) =
      ∫ x, g.inner x (G' x) (X x) ∂(riemannianVolumeMeasure I M g) := by
  rw [h₁.pairing_eq X hX, h₂.pairing_eq X hX]

theorem HasWeakRiemannianGradLp.pairing_inner_diff_eq_zero
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {u : M → ℝ}
    {G G' : M → E}
    (h₁ : HasWeakRiemannianGradLp (I := I) (M := M) g u G)
    (h₂ : HasWeakRiemannianGradLp (I := I) (M := M) g u G')
    (hG_p : MemLp (fun x : M => Real.sqrt (g.inner x (G x) (G x))) 1
      (riemannianVolumeMeasure I M g))
    (hG'_p : MemLp (fun x : M => Real.sqrt (g.inner x (G' x) (G' x))) 1
      (riemannianVolumeMeasure I M g))
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : HasCompactSupport (fun x : M => (X x : E))) :
    ∫ x, (g.inner x (G x) (X x) - g.inner x (G' x) (X x))
        ∂(riemannianVolumeMeasure I M g) = 0 := by
  have : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hX_norm_cont : Continuous (fun x : M =>
      Real.sqrt (g.inner x (X x) (X x))) :=
    continuous_g_norm_smooth_section g X
  obtain ⟨C_X, hC_X⟩ := Intrinsic.exists_bound_continuous_compactSpace hX_norm_cont
  have h_bound_G : ∀ x : M, |g.inner x (G x) (X x)| ≤
      C_X * Real.sqrt (g.inner x (G x) (G x)) := by
    intro x
    have hCS := g_inner_cauchy_schwarz g x (G x) (X x)
    have hX_bd : Real.sqrt (g.inner x (X x) (X x)) ≤ C_X := by
      have h := hC_X x
      have hnn : 0 ≤ Real.sqrt (g.inner x (X x) (X x)) := Real.sqrt_nonneg _
      rw [abs_of_nonneg hnn] at h; exact h
    calc |g.inner x (G x) (X x)|
        ≤ Real.sqrt (g.inner x (G x) (G x)) * Real.sqrt (g.inner x (X x) (X x)) := hCS
      _ ≤ Real.sqrt (g.inner x (G x) (G x)) * C_X :=
            mul_le_mul_of_nonneg_left hX_bd (Real.sqrt_nonneg _)
      _ = C_X * Real.sqrt (g.inner x (G x) (G x)) := by ring
  have h_int_G : Integrable (fun x : M => g.inner x (G x) (X x))
      (riemannianVolumeMeasure I M g) := by
    have hG_int : Integrable (fun x : M => Real.sqrt (g.inner x (G x) (G x)))
        (riemannianVolumeMeasure I M g) := memLp_one_iff_integrable.mp hG_p
    refine Integrable.mono' (g := fun x : M =>
        C_X * Real.sqrt (g.inner x (G x) (G x))) ?_ (h₁.1 X) ?_
    · exact hG_int.const_mul C_X
    · refine Filter.Eventually.of_forall (fun x => ?_)
      rw [Real.norm_eq_abs]
      exact h_bound_G x
  have h_bound_G' : ∀ x : M, |g.inner x (G' x) (X x)| ≤
      C_X * Real.sqrt (g.inner x (G' x) (G' x)) := by
    intro x
    have hCS := g_inner_cauchy_schwarz g x (G' x) (X x)
    have hX_bd : Real.sqrt (g.inner x (X x) (X x)) ≤ C_X := by
      have h := hC_X x
      have hnn : 0 ≤ Real.sqrt (g.inner x (X x) (X x)) := Real.sqrt_nonneg _
      rw [abs_of_nonneg hnn] at h; exact h
    calc |g.inner x (G' x) (X x)|
        ≤ Real.sqrt (g.inner x (G' x) (G' x)) * Real.sqrt (g.inner x (X x) (X x)) := hCS
      _ ≤ Real.sqrt (g.inner x (G' x) (G' x)) * C_X :=
            mul_le_mul_of_nonneg_left hX_bd (Real.sqrt_nonneg _)
      _ = C_X * Real.sqrt (g.inner x (G' x) (G' x)) := by ring
  have h_int_G' : Integrable (fun x : M => g.inner x (G' x) (X x))
      (riemannianVolumeMeasure I M g) := by
    have hG'_int : Integrable (fun x : M => Real.sqrt (g.inner x (G' x) (G' x)))
        (riemannianVolumeMeasure I M g) := memLp_one_iff_integrable.mp hG'_p
    refine Integrable.mono' (g := fun x : M =>
        C_X * Real.sqrt (g.inner x (G' x) (G' x))) ?_ (h₂.1 X) ?_
    · exact hG'_int.const_mul C_X
    · refine Filter.Eventually.of_forall (fun x => ?_)
      rw [Real.norm_eq_abs]
      exact h_bound_G' x
  rw [integral_sub h_int_G h_int_G']
  rw [HasWeakRiemannianGradLp.pairing_inner_eq h₁ h₂ X hX, sub_self]

end

end IntrinsicLp
end Sobolev

end
