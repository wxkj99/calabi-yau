-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Intrinsic/Defs.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Riemannian.Operator.Gradient.Basic
public import CalabiYau.Geometry.Riemannian.Operator.Laplacian.Basic
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Global.IntegrationByParts
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Local.Formula
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Global.PartitionOfUnity
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Global.Support
public import CalabiYau.Geometry.Riemannian.Operator.DirectionalDerivative
public import CalabiYau.Geometry.Riemannian.L2.CompactSupport
public import CalabiYau.Geometry.Riemannian.Volume.Properties
public import CalabiYau.Geometry.Riemannian.Volume.Basic
public import CalabiYau.Geometry.Riemannian.Volume.Invariance
public import CalabiYau.Geometry.Riemannian.TensorInner.Tangent.Riemannian
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
open CalabiYau.Riemannian
open CalabiYau

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold Topology ContDiff ENNReal NNReal Matrix

namespace Sobolev
namespace Intrinsic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.L2

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [Module.Finite ℝ E] in
private lemma continuous_g_inner_smooth_sections
    (g : SmoothRiemannianMetric I M)
    (G X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Continuous (fun b : M => g.inner b (G b) (X b)) :=
  TangentBundle.continuous_g_inner_of_smooth_sections (I := I) (M := M) g G X

omit [Module.Finite ℝ E] in
private lemma continuous_g_norm_sq_smooth_section
    (g : SmoothRiemannianMetric I M)
    (G : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Continuous (fun b : M => g.inner b (G b) (G b)) :=
  continuous_g_inner_smooth_sections g G G

omit [Module.Finite ℝ E] in
private lemma continuous_g_norm_smooth_section
    (g : SmoothRiemannianMetric I M)
    (G : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Continuous (fun b : M => Real.sqrt (g.inner b (G b) (G b))) :=
  Real.continuous_sqrt.comp (continuous_g_norm_sq_smooth_section g G)

private lemma exists_bound_continuous_compactSpace
    [CompactSpace M] {f : M → ℝ} (hf : Continuous f) :
    ∃ C : ℝ, ∀ x : M, |f x| ≤ C := by
  by_cases hM : Nonempty M
  · have hrange : IsCompact (Set.range f) := isCompact_range hf
    obtain ⟨C₁, hC₁⟩ := hrange.bddAbove
    have hrange_neg : IsCompact (Set.range (-f)) := isCompact_range hf.neg
    obtain ⟨C₂, hC₂⟩ := hrange_neg.bddAbove
    refine ⟨max C₁ C₂, ?_⟩
    intro x
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have : -f x ≤ C₂ := hC₂ ⟨x, rfl⟩
      linarith [le_max_right C₁ C₂]
    · have : f x ≤ C₁ := hC₁ ⟨x, rfl⟩
      linarith [le_max_left C₁ C₂]
  · refine ⟨0, ?_⟩
    intro x
    exact (hM ⟨x⟩).elim

private lemma continuous_memLp_of_compactSpace
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (p : ℝ≥0∞)
    {f : M → ℝ} (hf : Continuous f) :
    MemLp f p (riemannianVolumeMeasure I M g) := by
  have : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hmeas : AEStronglyMeasurable f (riemannianVolumeMeasure I M g) :=
    hf.aestronglyMeasurable
  obtain ⟨C, hC⟩ := exists_bound_continuous_compactSpace hf
  exact MemLp.of_bound hmeas C (Filter.Eventually.of_forall (fun x => hC x))

private lemma continuous_integrable_of_compactSpace
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : Continuous f) :
    Integrable f (riemannianVolumeMeasure I M g) := by
  have : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have h_one : MemLp f 1 (riemannianVolumeMeasure I M g) :=
    continuous_memLp_of_compactSpace g 1 hf
  exact memLp_one_iff_integrable.mp h_one

def HasWeakRiemannianGrad
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (u : M → ℝ)
    (G : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : Prop :=
  ∀ X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯,
    HasCompactSupport (fun x : M => (X x : E)) →
      ∫ x, g.inner x (G x) (X x) ∂(riemannianVolumeMeasure I M g) =
        -∫ x, u x * divergenceG (I := I) g X x
          ∂(riemannianVolumeMeasure I M g)

lemma HasWeakRiemannianGrad.pairing_eq
    [T2Space M] [SigmaCompactSpace M] {g : SmoothRiemannianMetric I M} {u : M → ℝ}
    {G : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (h : HasWeakRiemannianGrad (I := I) (M := M) g u G)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : HasCompactSupport (fun x : M => (X x : E))) :
    ∫ x, g.inner x (G x) (X x) ∂(riemannianVolumeMeasure I M g) =
      -∫ x, u x * divergenceG (I := I) g X x
        ∂(riemannianVolumeMeasure I M g) := h X hX

def MemW1pIntrinsic
    [T2Space M] [SigmaCompactSpace M] (g : SmoothRiemannianMetric I M) (p : ℝ≥0∞) (u : M → ℝ) : Prop :=
  MemLp u p (riemannianVolumeMeasure I M g) ∧
  ∃ G : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯,
    HasWeakRiemannianGrad (I := I) (M := M) g u G ∧
      MemLp (fun x : M => Real.sqrt (g.inner x (G x) (G x))) p
        (riemannianVolumeMeasure I M g)

lemma MemW1pIntrinsic.memLp_self
    [T2Space M] [SigmaCompactSpace M] {g : SmoothRiemannianMetric I M} {p : ℝ≥0∞} {u : M → ℝ}
    (h : MemW1pIntrinsic (I := I) (M := M) g p u) :
    MemLp u p (riemannianVolumeMeasure I M g) := h.1

theorem integral_inner_gradFun_eq_neg_integral_mul_divergence
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : HasCompactSupport (fun x : M => (X x : E))) :
    ∫ x, g.inner x (gradFun (I := I) g u x) (X x)
        ∂(riemannianVolumeMeasure I M g) =
      -∫ x, u x * divergenceG (I := I) g X x
        ∂(riemannianVolumeMeasure I M g) := by
  have hpointwise : ∀ x : M,
      g.inner x (gradFun (I := I) g u x) (X x) =
        tangentSectionAction (I := I) X u x := by
    intro x
    have hsymm := g.symm x (gradFun (I := I) g u x) (X x)
    rw [hsymm]
    exact inner_gradFun_right (I := I) g u x (X x)
  rw [integral_congr_ae (Filter.Eventually.of_forall hpointwise)]
  exact integral_tangentSectionAction_eq_neg_integral_smul_divergence
    (I := I) (M := M) g hu X hX

theorem hasWeakRiemannianGrad_grad_g_of_contMDiff
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    HasWeakRiemannianGrad (I := I) (M := M) g u (gradG (I := I) g ⟨_, hu⟩) := by
  intro X hX
  have hcoe : ∀ x : M,
      ((gradG (I := I) g ⟨_, hu⟩ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
        gradFun (I := I) g u x := fun x => grad_g_apply (I := I) g ⟨_, hu⟩ x
  rw [show (fun x : M =>
        g.inner x ((gradG (I := I) g ⟨_, hu⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) (X x)) =
        (fun x : M => g.inner x (gradFun (I := I) g u x) (X x)) from by
      funext x; rw [hcoe x]]
  exact integral_inner_gradFun_eq_neg_integral_mul_divergence
    (I := I) (M := M) g hu X hX

theorem MemW1pIntrinsic_of_contMDiff
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (p : ℝ≥0∞)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    MemW1pIntrinsic (I := I) (M := M) g p u := by
  refine ⟨?_, gradG (I := I) g ⟨_, hu⟩, ?_, ?_⟩
  · exact continuous_memLp_of_compactSpace g p hu.continuous
  · exact hasWeakRiemannianGrad_grad_g_of_contMDiff (I := I) (M := M) g hu
  · have hcont := continuous_g_norm_smooth_section g (gradG (I := I) g ⟨_, hu⟩)
    exact continuous_memLp_of_compactSpace g p hcont

theorem HasWeakRiemannianGrad.add
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M}
    {u v : M → ℝ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {G G' : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (h₁ : HasWeakRiemannianGrad (I := I) (M := M) g u G)
    (h₂ : HasWeakRiemannianGrad (I := I) (M := M) g v G')
    (hu : MemLp u p (riemannianVolumeMeasure I M g))
    (hv : MemLp v p (riemannianVolumeMeasure I M g)) :
    HasWeakRiemannianGrad (I := I) (M := M) g (fun x => u x + v x) (G + G') := by
  have : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  intro X hX
  have hpt_add : ∀ x : M,
      g.inner x ((G + G' : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) (X x) =
        g.inner x (G x) (X x) + g.inner x (G' x) (X x) := by
    intro x
    change g.inner x (G x + G' x) (X x) =
      g.inner x (G x) (X x) + g.inner x (G' x) (X x)
    rw [map_add (g.inner x), add_apply]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt_add)]
  have h_int_G : Integrable (fun x : M => g.inner x (G x) (X x))
      (riemannianVolumeMeasure I M g) :=
    continuous_integrable_of_compactSpace g
      (continuous_g_inner_smooth_sections g G X)
  have h_int_G' : Integrable (fun x : M => g.inner x (G' x) (X x))
      (riemannianVolumeMeasure I M g) :=
    continuous_integrable_of_compactSpace g
      (continuous_g_inner_smooth_sections g G' X)
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
    obtain ⟨C, hC⟩ := exists_bound_continuous_compactSpace h_div_cont
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
    obtain ⟨C, hC⟩ := exists_bound_continuous_compactSpace h_div_cont
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

theorem MemW1pIntrinsic.add
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u v : M → ℝ}
    (hu : MemW1pIntrinsic (I := I) (M := M) g p u)
    (hv : MemW1pIntrinsic (I := I) (M := M) g p v) :
    MemW1pIntrinsic (I := I) (M := M) g p (fun x => u x + v x) := by
  obtain ⟨hu_p, G, hG_weak, _hG_p⟩ := hu
  obtain ⟨hv_p, G', hG'_weak, _hG'_p⟩ := hv
  refine ⟨hu_p.add hv_p, G + G', ?_, ?_⟩
  · exact HasWeakRiemannianGrad.add (I := I) (M := M) hp hG_weak hG'_weak hu_p hv_p
  · have hcont := continuous_g_norm_smooth_section g (G + G')
    exact continuous_memLp_of_compactSpace g p hcont

theorem HasWeakRiemannianGrad.zero
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) :
    HasWeakRiemannianGrad (I := I) (M := M) g (fun _ => (0 : ℝ))
      (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) := by
  intro X _
  have h_LHS : ∀ x : M,
      g.inner x ((0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) (X x) = 0 := by
    intro x
    change g.inner x (0 : TangentSpace I x) (X x) = 0
    simp
  rw [show (fun x : M =>
      g.inner x ((0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) (X x)) =
      (fun _ : M => (0 : ℝ)) from by funext x; exact h_LHS x]
  rw [show (fun x : M => (0 : ℝ) * divergenceG (I := I) g X x) =
      (fun _ : M => (0 : ℝ)) from by funext x; simp]
  simp [integral_zero]

theorem MemW1pIntrinsic.zero
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (p : ℝ≥0∞) :
    MemW1pIntrinsic (I := I) (M := M) g p (fun _ : M => (0 : ℝ)) := by
  let _ := (inferInstance : (I.Boundaryless))
  refine ⟨?_, (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
    HasWeakRiemannianGrad.zero (I := I) (M := M) g, ?_⟩
  · exact MemLp.zero
  · have hcongr : (fun x : M => Real.sqrt
        (g.inner x ((0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))) =
        (fun _ : M => (0 : ℝ)) := by
      funext x
      change Real.sqrt (g.inner x (0 : TangentSpace I x) (0 : TangentSpace I x)) = 0
      simp
    rw [hcongr]
    exact MemLp.zero

theorem HasWeakRiemannianGrad.const_smul
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (c : ℝ) {u : M → ℝ}
    {G : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (h : HasWeakRiemannianGrad (I := I) (M := M) g u G)
    (hu : MemLp u p (riemannianVolumeMeasure I M g)) :
    HasWeakRiemannianGrad (I := I) (M := M) g (fun x => c * u x) (c • G) := by
  have : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  intro X hX
  have hpt : ∀ x : M,
      g.inner x ((c • G : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) (X x) =
        c * g.inner x (G x) (X x) := by
    intro x
    change g.inner x (c • G x) (X x) = c * g.inner x (G x) (X x)
    rw [map_smul (g.inner x), smul_apply, smul_eq_mul]
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
    obtain ⟨C, hC⟩ := exists_bound_continuous_compactSpace h_div_cont
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

theorem MemW1pIntrinsic.const_smul
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (c : ℝ) {u : M → ℝ}
    (hu : MemW1pIntrinsic (I := I) (M := M) g p u) :
    MemW1pIntrinsic (I := I) (M := M) g p (fun x => c * u x) := by
  obtain ⟨hu_p, G, hG_weak, _hG_p⟩ := hu
  refine ⟨hu_p.const_mul c, c • G, ?_, ?_⟩
  · exact HasWeakRiemannianGrad.const_smul (I := I) (M := M) hp c hG_weak hu_p
  · have hcont := continuous_g_norm_smooth_section g (c • G)
    exact continuous_memLp_of_compactSpace g p hcont

theorem HasWeakRiemannianGrad.pairing_inner_eq
    [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {u : M → ℝ}
    {G G' : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (h₁ : HasWeakRiemannianGrad (I := I) (M := M) g u G)
    (h₂ : HasWeakRiemannianGrad (I := I) (M := M) g u G')
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : HasCompactSupport (fun x : M => (X x : E))) :
    ∫ x, g.inner x (G x) (X x) ∂(riemannianVolumeMeasure I M g) =
      ∫ x, g.inner x (G' x) (X x) ∂(riemannianVolumeMeasure I M g) := by
  rw [h₁.pairing_eq X hX, h₂.pairing_eq X hX]

theorem HasWeakRiemannianGrad.pairing_inner_diff_eq_zero
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {u : M → ℝ}
    {G G' : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (h₁ : HasWeakRiemannianGrad (I := I) (M := M) g u G)
    (h₂ : HasWeakRiemannianGrad (I := I) (M := M) g u G')
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : HasCompactSupport (fun x : M => (X x : E))) :
    ∫ x, (g.inner x (G x) (X x) - g.inner x (G' x) (X x))
        ∂(riemannianVolumeMeasure I M g) = 0 := by
  have : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have h_int_G : Integrable (fun x : M => g.inner x (G x) (X x))
      (riemannianVolumeMeasure I M g) :=
    continuous_integrable_of_compactSpace g
      (continuous_g_inner_smooth_sections g G X)
  have h_int_G' : Integrable (fun x : M => g.inner x (G' x) (X x))
      (riemannianVolumeMeasure I M g) :=
    continuous_integrable_of_compactSpace g
      (continuous_g_inner_smooth_sections g G' X)
  rw [integral_sub h_int_G h_int_G']
  rw [HasWeakRiemannianGrad.pairing_inner_eq h₁ h₂ X hX, sub_self]

def w1pNormIntrinsic
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (p : ℝ≥0∞) (u : M → ℝ) : ℝ≥0∞ :=
  eLpNorm u p (riemannianVolumeMeasure I M g) +
    ⨅ (G : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (_ :
      HasWeakRiemannianGrad (I := I) (M := M) g u G),
        eLpNorm (fun x : M => Real.sqrt (g.inner x (G x) (G x))) p
          (riemannianVolumeMeasure I M g)

private def gradInfimum
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (p : ℝ≥0∞) (u : M → ℝ) : ℝ≥0∞ :=
  ⨅ (G : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (_ :
    HasWeakRiemannianGrad (I := I) (M := M) g u G),
      eLpNorm (fun x : M => Real.sqrt (g.inner x (G x) (G x))) p
        (riemannianVolumeMeasure I M g)

private lemma w1pNormIntrinsic_def
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (p : ℝ≥0∞) (u : M → ℝ) :
    w1pNormIntrinsic (I := I) (M := M) g p u =
      eLpNorm u p (riemannianVolumeMeasure I M g) +
        gradInfimum (I := I) (M := M) g p u := rfl

private lemma gradInfimum_le_of_weakGrad
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) {p : ℝ≥0∞} {u : M → ℝ}
    {G : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (hG : HasWeakRiemannianGrad (I := I) (M := M) g u G) :
    gradInfimum (I := I) (M := M) g p u ≤
      eLpNorm (fun x : M => Real.sqrt (g.inner x (G x) (G x))) p
        (riemannianVolumeMeasure I M g) := by
  unfold gradInfimum
  exact iInf_le_of_le G (iInf_le _ hG)

theorem w1pNormIntrinsic_zero
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (p : ℝ≥0∞) :
    w1pNormIntrinsic (I := I) (M := M) g p (fun _ : M => (0 : ℝ)) = 0 := by
  rw [w1pNormIntrinsic_def]
  rw [show eLpNorm (fun _ : M => (0 : ℝ)) p
        (riemannianVolumeMeasure I M g) = 0 from
      eLpNorm_zero]
  rw [zero_add]
  apply le_antisymm
  · have hzero_grad : HasWeakRiemannianGrad (I := I) (M := M) g
        (fun _ : M => (0 : ℝ))
        (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :=
      HasWeakRiemannianGrad.zero (I := I) (M := M) g
    have h_zero_norm :
        eLpNorm (fun x : M => Real.sqrt
          (g.inner x
            ((0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))) p
          (riemannianVolumeMeasure I M g) = 0 := by
      have hcongr : (fun x : M => Real.sqrt
          (g.inner x
            ((0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))) =
          (fun _ : M => (0 : ℝ)) := by
        funext x
        change Real.sqrt (g.inner x (0 : TangentSpace I x) (0 : TangentSpace I x)) = 0
        simp
      rw [hcongr]
      exact eLpNorm_zero
    refine (gradInfimum_le_of_weakGrad g hzero_grad).trans ?_
    exact le_of_eq h_zero_norm
  · exact bot_le

theorem MemW1pIntrinsic.eLpNorm_lt_top
    [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {p : ℝ≥0∞} {u : M → ℝ}
    (h : MemW1pIntrinsic (I := I) (M := M) g p u) :
    eLpNorm u p (riemannianVolumeMeasure I M g) < ⊤ :=
  h.memLp_self.2

theorem MemW1pIntrinsic.gradInfimum_lt_top
    [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {p : ℝ≥0∞} {u : M → ℝ}
    (h : MemW1pIntrinsic (I := I) (M := M) g p u) :
    gradInfimum (I := I) (M := M) g p u < ⊤ := by
  obtain ⟨_, G, hG_weak, hG_p⟩ := h
  refine lt_of_le_of_lt
    (gradInfimum_le_of_weakGrad g hG_weak) ?_
  exact hG_p.2

theorem MemW1pIntrinsic.w1pNormIntrinsic_lt_top
    [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {p : ℝ≥0∞} {u : M → ℝ}
    (h : MemW1pIntrinsic (I := I) (M := M) g p u) :
    w1pNormIntrinsic (I := I) (M := M) g p u < ⊤ := by
  rw [w1pNormIntrinsic_def]
  exact ENNReal.add_lt_top.mpr ⟨h.eLpNorm_lt_top, h.gradInfimum_lt_top⟩

private lemma gradInfimum_add_le_of_weakGrads
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u v : M → ℝ}
    (hu_p : MemLp u p (riemannianVolumeMeasure I M g))
    (hv_p : MemLp v p (riemannianVolumeMeasure I M g))
    {G G' : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯}
    (hG_weak : HasWeakRiemannianGrad (I := I) (M := M) g u G)
    (hG'_weak : HasWeakRiemannianGrad (I := I) (M := M) g v G') :
    gradInfimum (I := I) (M := M) g p (fun x => u x + v x) ≤
      eLpNorm (fun x : M => Real.sqrt (g.inner x (G x) (G x))) p
          (riemannianVolumeMeasure I M g) +
        eLpNorm (fun x : M => Real.sqrt (g.inner x (G' x) (G' x))) p
          (riemannianVolumeMeasure I M g) := by
  have hsum_weak : HasWeakRiemannianGrad (I := I) (M := M) g
      (fun x : M => u x + v x) (G + G') :=
    HasWeakRiemannianGrad.add (I := I) (M := M) hp hG_weak hG'_weak hu_p hv_p
  have h_triangle_pt : ∀ x : M,
      Real.sqrt
        (g.inner x ((G + G' : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((G + G' : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)) ≤
        Real.sqrt (g.inner x (G x) (G x)) +
          Real.sqrt (g.inner x (G' x) (G' x)) := by
    intro x
    have h_expand :
        g.inner x ((G + G' : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((G + G' : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
        g.inner x (G x) (G x) + 2 * g.inner x (G x) (G' x) +
          g.inner x (G' x) (G' x) := by
      change g.inner x (G x + G' x) (G x + G' x) =
        g.inner x (G x) (G x) + 2 * g.inner x (G x) (G' x) +
          g.inner x (G' x) (G' x)
      have hbilin1 : g.inner x (G x + G' x) =
          g.inner x (G x) + g.inner x (G' x) :=
        (g.inner x).map_add (G x) (G' x)
      rw [hbilin1, add_apply,
        ContinuousLinearMap.map_add, ContinuousLinearMap.map_add]
      have hsymm : g.inner x (G' x) (G x) = g.inner x (G x) (G' x) :=
        g.symm x (G' x) (G x)
      rw [hsymm]; ring
    rw [h_expand]
    set a := g.inner x (G x) (G x)
    set b := g.inner x (G' x) (G' x)
    set c := g.inner x (G x) (G' x)
    have ha_nn : 0 ≤ a := by
      rcases eq_or_ne (G x : E) 0 with hG0 | hG0
      · simp [a, hG0]
      · exact (g.pos x (G x) hG0).le
    have hb_nn : 0 ≤ b := by
      rcases eq_or_ne (G' x : E) 0 with hG0 | hG0
      · simp [b, hG0]
      · exact (g.pos x (G' x) hG0).le
    have hc_bound : c ≤ Real.sqrt a * Real.sqrt b := by
      have hCS_sq : c ^ 2 ≤ a * b := by
        have hquad : ∀ t : ℝ, 0 ≤ t * t * a + 2 * t * c + b := by
          intro t
          have hpos : 0 ≤ g.inner x (t • G x + G' x) (t • G x + G' x) := by
            rcases eq_or_ne (t • G x + G' x : E) 0 with hz | hnz
            · simp [hz]
            · exact (g.pos x _ hnz).le
          have h_expand2 : g.inner x (t • G x + G' x) (t • G x + G' x) =
              t * t * a + 2 * t * c + b := by
            have hbi1 : g.inner x (t • G x + G' x) =
                g.inner x (t • G x) + g.inner x (G' x) :=
              (g.inner x).map_add (t • G x) (G' x)
            have hbi2 : g.inner x (t • G x) = t • g.inner x (G x) :=
              (g.inner x).map_smul t (G x)
            rw [hbi1, hbi2, add_apply,
              smul_apply,
              ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul,
              ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul]
            simp only [smul_eq_mul]
            have hsymm2 : g.inner x (G' x) (G x) = c := by
              change g.inner x (G' x) (G x) = g.inner x (G x) (G' x)
              exact g.symm x (G' x) (G x)
            rw [hsymm2]
            ring
          rw [h_expand2] at hpos
          exact hpos
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
          have hG_zero : (G x : E) = 0 := by
            by_contra hne
            have hpos : 0 < g.inner x (G x) (G x) := g.pos x (G x) hne
            rw [show g.inner x (G x) (G x) = a from rfl, ha_eq] at hpos
            exact lt_irrefl 0 hpos
          have hc_eq : c = 0 := by
            change g.inner x (G x) (G' x) = 0
            have hG0 : (G x : TangentSpace I x) = 0 := hG_zero
            rw [hG0]
            simp
          rw [hc_eq, ha_eq]; simp
      have hC : |c| ≤ Real.sqrt (a * b) := by
        rw [← Real.sqrt_sq_eq_abs]
        refine Real.sqrt_le_sqrt ?_
        exact hCS_sq
      have hsqrt_mul : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b :=
        Real.sqrt_mul ha_nn b
      rw [hsqrt_mul] at hC
      exact (le_abs_self c).trans hC
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
  have hmono : eLpNorm (fun x : M => Real.sqrt
        (g.inner x ((G + G' : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((G + G' : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))) p
        (riemannianVolumeMeasure I M g) ≤
      eLpNorm (fun x : M => Real.sqrt (g.inner x (G x) (G x)) +
          Real.sqrt (g.inner x (G' x) (G' x))) p
        (riemannianVolumeMeasure I M g) := by
    refine eLpNorm_mono ?_
    intro x
    rw [Real.norm_eq_abs (Real.sqrt _)]
    rw [Real.norm_eq_abs (Real.sqrt (g.inner x (G x) (G x)) +
      Real.sqrt (g.inner x (G' x) (G' x)))]
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [abs_of_nonneg (by positivity)]
    exact h_triangle_pt x
  have h_aem_G : AEStronglyMeasurable
      (fun x : M => Real.sqrt (g.inner x (G x) (G x)))
      (riemannianVolumeMeasure I M g) :=
    (continuous_g_norm_smooth_section g G).aestronglyMeasurable
  have h_aem_G' : AEStronglyMeasurable
      (fun x : M => Real.sqrt (g.inner x (G' x) (G' x)))
      (riemannianVolumeMeasure I M g) :=
    (continuous_g_norm_smooth_section g G').aestronglyMeasurable
  have htri : eLpNorm (fun x : M => Real.sqrt (g.inner x (G x) (G x)) +
        Real.sqrt (g.inner x (G' x) (G' x))) p
        (riemannianVolumeMeasure I M g) ≤
      eLpNorm (fun x : M => Real.sqrt (g.inner x (G x) (G x))) p
        (riemannianVolumeMeasure I M g) +
      eLpNorm (fun x : M => Real.sqrt (g.inner x (G' x) (G' x))) p
        (riemannianVolumeMeasure I M g) :=
    eLpNorm_add_le h_aem_G h_aem_G' hp
  refine le_trans ?_ (hmono.trans htri)
  exact gradInfimum_le_of_weakGrad g hsum_weak

theorem w1pNormIntrinsic_add_le
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u v : M → ℝ}
    (hu : MemW1pIntrinsic (I := I) (M := M) g p u)
    (hv : MemW1pIntrinsic (I := I) (M := M) g p v) :
    w1pNormIntrinsic (I := I) (M := M) g p (fun x => u x + v x) ≤
      w1pNormIntrinsic (I := I) (M := M) g p u +
        w1pNormIntrinsic (I := I) (M := M) g p v := by
  rw [w1pNormIntrinsic_def, w1pNormIntrinsic_def, w1pNormIntrinsic_def]
  obtain ⟨hu_p, _, _, _⟩ := hu
  obtain ⟨hv_p, _, _, _⟩ := hv
  have h_eLpNorm_uv :
      eLpNorm (fun x : M => u x + v x) p
        (riemannianVolumeMeasure I M g) ≤
      eLpNorm u p (riemannianVolumeMeasure I M g) +
        eLpNorm v p (riemannianVolumeMeasure I M g) := by
    have h := eLpNorm_add_le hu_p.aestronglyMeasurable hv_p.aestronglyMeasurable hp
    have heq : (fun x : M => u x + v x) = u + v := by funext x; rfl
    rw [heq]
    exact h
  have h_grad_bound :
      gradInfimum (I := I) (M := M) g p (fun x : M => u x + v x) ≤
        gradInfimum (I := I) (M := M) g p u +
          gradInfimum (I := I) (M := M) g p v := by
    unfold gradInfimum
    rw [show
        (⨅ (G_u : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
            (_ : HasWeakRiemannianGrad (I := I) (M := M) g u G_u),
            eLpNorm (fun x : M => Real.sqrt (g.inner x (G_u x) (G_u x))) p
              (riemannianVolumeMeasure I M g)) +
          (⨅ (G_v : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
              (_ : HasWeakRiemannianGrad (I := I) (M := M) g v G_v),
              eLpNorm (fun x : M => Real.sqrt (g.inner x (G_v x) (G_v x))) p
                (riemannianVolumeMeasure I M g))
        = ⨅ (G_u : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
            (⨅ (_ : HasWeakRiemannianGrad (I := I) (M := M) g u G_u),
              eLpNorm (fun x : M => Real.sqrt (g.inner x (G_u x) (G_u x))) p
                (riemannianVolumeMeasure I M g)) +
              (⨅ (G_v : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
                  (_ : HasWeakRiemannianGrad (I := I) (M := M) g v G_v),
                  eLpNorm (fun x : M => Real.sqrt (g.inner x (G_v x) (G_v x))) p
                    (riemannianVolumeMeasure I M g)) from
        ENNReal.iInf_add]
    refine le_iInf ?_
    intro G_u
    rw [show
        (⨅ (_ : HasWeakRiemannianGrad (I := I) (M := M) g u G_u),
            eLpNorm (fun x : M => Real.sqrt (g.inner x (G_u x) (G_u x))) p
              (riemannianVolumeMeasure I M g)) +
          (⨅ (G_v : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
              (_ : HasWeakRiemannianGrad (I := I) (M := M) g v G_v),
              eLpNorm (fun x : M => Real.sqrt (g.inner x (G_v x) (G_v x))) p
                (riemannianVolumeMeasure I M g))
        = ⨅ (_ : HasWeakRiemannianGrad (I := I) (M := M) g u G_u),
            eLpNorm (fun x : M => Real.sqrt (g.inner x (G_u x) (G_u x))) p
              (riemannianVolumeMeasure I M g) +
              (⨅ (G_v : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
                  (_ : HasWeakRiemannianGrad (I := I) (M := M) g v G_v),
                  eLpNorm (fun x : M => Real.sqrt (g.inner x (G_v x) (G_v x))) p
                    (riemannianVolumeMeasure I M g)) from
        ENNReal.iInf_add]
    refine le_iInf ?_
    intro hG_u
    rw [show
        eLpNorm (fun x : M => Real.sqrt (g.inner x (G_u x) (G_u x))) p
            (riemannianVolumeMeasure I M g) +
          (⨅ (G_v : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
              (_ : HasWeakRiemannianGrad (I := I) (M := M) g v G_v),
              eLpNorm (fun x : M => Real.sqrt (g.inner x (G_v x) (G_v x))) p
                (riemannianVolumeMeasure I M g))
        = ⨅ (G_v : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
              eLpNorm (fun x : M => Real.sqrt (g.inner x (G_u x) (G_u x))) p
                (riemannianVolumeMeasure I M g) +
                (⨅ (_ : HasWeakRiemannianGrad (I := I) (M := M) g v G_v),
                  eLpNorm (fun x : M => Real.sqrt (g.inner x (G_v x) (G_v x))) p
                    (riemannianVolumeMeasure I M g)) from
        ENNReal.add_iInf]
    refine le_iInf ?_
    intro G_v
    rw [show
        eLpNorm (fun x : M => Real.sqrt (g.inner x (G_u x) (G_u x))) p
            (riemannianVolumeMeasure I M g) +
          (⨅ (_ : HasWeakRiemannianGrad (I := I) (M := M) g v G_v),
              eLpNorm (fun x : M => Real.sqrt (g.inner x (G_v x) (G_v x))) p
                (riemannianVolumeMeasure I M g))
        = ⨅ (_ : HasWeakRiemannianGrad (I := I) (M := M) g v G_v),
            eLpNorm (fun x : M => Real.sqrt (g.inner x (G_u x) (G_u x))) p
              (riemannianVolumeMeasure I M g) +
              eLpNorm (fun x : M => Real.sqrt (g.inner x (G_v x) (G_v x))) p
                (riemannianVolumeMeasure I M g) from
        ENNReal.add_iInf]
    refine le_iInf ?_
    intro hG_v
    exact gradInfimum_add_le_of_weakGrads g hp hu_p hv_p hG_u hG_v
  calc eLpNorm (fun x : M => u x + v x) p
        (riemannianVolumeMeasure I M g) +
        gradInfimum (I := I) (M := M) g p (fun x : M => u x + v x)
      ≤ (eLpNorm u p (riemannianVolumeMeasure I M g) +
            eLpNorm v p (riemannianVolumeMeasure I M g)) +
          (gradInfimum (I := I) (M := M) g p u +
            gradInfimum (I := I) (M := M) g p v) :=
        add_le_add h_eLpNorm_uv h_grad_bound
    _ = (eLpNorm u p (riemannianVolumeMeasure I M g) +
            gradInfimum (I := I) (M := M) g p u) +
          (eLpNorm v p (riemannianVolumeMeasure I M g) +
            gradInfimum (I := I) (M := M) g p v) := by
        rw [add_assoc, ← add_assoc (eLpNorm v _ _),
          add_comm (eLpNorm v _ _),
          add_assoc, ← add_assoc]

end Intrinsic
end Sobolev

end
