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
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

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

lemma exists_bound_continuous_compactSpace
    [CompactSpace M] {f : M → ℝ} (hf : Continuous f) :
    ∃ C : ℝ, ∀ x : M, |f x| ≤ C := by
  simpa [Real.norm_eq_abs] using isCompact_univ.exists_bound_of_continuousOn hf.continuousOn

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

theorem MemW1pIntrinsic.eLpNorm_lt_top
    [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} {p : ℝ≥0∞} {u : M → ℝ}
    (h : MemW1pIntrinsic (I := I) (M := M) g p u) :
    eLpNorm u p (riemannianVolumeMeasure I M g) < ⊤ :=
  h.memLp_self.2

end Intrinsic
end Sobolev

end
