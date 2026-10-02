-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Intrinsic/Equivalence/ChartToIntrinsic/SmoothMembership.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Intrinsic.Equivalence.Basic
public import CalabiYau.Analysis.Sobolev.Intrinsic.Lp.Basic
public import CalabiYau.Analysis.Sobolev.Approximation.Density.FirstOrder
public import CalabiYau.Geometry.Riemannian.Volume.Chart.MeasureComparison
public import CalabiYau.Analysis.Sobolev.Manifold.Measure.UniformChartComparison
public import CalabiYau.Analysis.Sobolev.Manifold.Embedding.Subcritical
public import CalabiYau.Analysis.Sobolev.Manifold.Morrey.Basic
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Global.IntegrationByParts
public import CalabiYau.Geometry.Riemannian.Operator.Laplacian.Basic
public import CalabiYau.Geometry.Riemannian.Volume.Family.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
open CalabiYau.Riemannian CalabiYau

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace Sobolev
namespace Equivalence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open Sobolev.Chart
open Sobolev.Intrinsic
open Sobolev.IntrinsicLp

private lemma exists_bound_continuous_compactSpace
    [CompactSpace M] {f : M → ℝ} (hf : Continuous f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : M, |f x| ≤ C := by
  by_cases hM : Nonempty M
  · have hrange : IsCompact (Set.range f) := isCompact_range hf
    obtain ⟨C₁, hC₁⟩ := hrange.bddAbove
    have hrange_neg : IsCompact (Set.range (-f)) := isCompact_range hf.neg
    obtain ⟨C₂, hC₂⟩ := hrange_neg.bddAbove
    refine ⟨max (max C₁ C₂) 0, le_max_right _ _, ?_⟩
    intro x
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have h_neg : -f x ≤ C₂ := hC₂ ⟨x, rfl⟩
      have hC₂_le : C₂ ≤ max (max C₁ C₂) 0 :=
        le_trans (le_max_right C₁ C₂) (le_max_left _ _)
      linarith
    · have h_pos : f x ≤ C₁ := hC₁ ⟨x, rfl⟩
      have hC₁_le : C₁ ≤ max (max C₁ C₂) 0 :=
        le_trans (le_max_left C₁ C₂) (le_max_left _ _)
      linarith
  · refine ⟨0, le_refl _, ?_⟩
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
  obtain ⟨C, _hC_nn, hC⟩ := exists_bound_continuous_compactSpace hf
  exact MemLp.of_bound hmeas C (Filter.Eventually.of_forall (fun x => hC x))

lemma continuous_g_norm_gradFun
    [I.Boundaryless]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    Continuous (fun x : M => Real.sqrt
        (g.inner x
          (CalabiYau.Riemannian.gradFun
            (I := I) g u x)
          (CalabiYau.Riemannian.gradFun
            (I := I) g u x))) := by
  have hcont :=
    TangentBundle.continuous_g_inner_of_smooth_sections
      (I := I) (M := M) g
      (CalabiYau.Riemannian.gradG (I := I) g ⟨_, hu⟩)
      (CalabiYau.Riemannian.gradG (I := I) g ⟨_, hu⟩)
  have hcoe : (fun x : M => g.inner x
        ((CalabiYau.Riemannian.gradG (I := I) g ⟨_, hu⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((CalabiYau.Riemannian.gradG (I := I) g ⟨_, hu⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)) =
      (fun x : M => g.inner x
        (CalabiYau.Riemannian.gradFun (I := I) g u x)
        (CalabiYau.Riemannian.gradFun (I := I) g u x)) := by
    funext x
    rw [CalabiYau.Riemannian.grad_g_apply (I := I) g ⟨_, hu⟩ x]
    change g.inner x
        (CalabiYau.Riemannian.gradFun (I := I) g u x)
        (CalabiYau.Riemannian.gradFun (I := I) g u x) =
      g.inner x
        (CalabiYau.Riemannian.gradFun (I := I) g u x)
        (CalabiYau.Riemannian.gradFun (I := I) g u x)
    rfl
  rw [hcoe] at hcont
  exact Real.continuous_sqrt.comp hcont

private lemma exists_bound_g_norm_gradFun
    [CompactSpace M] [I.Boundaryless]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : M,
      Real.sqrt
        (g.inner x
          (CalabiYau.Riemannian.gradFun
            (I := I) g u x)
          (CalabiYau.Riemannian.gradFun
            (I := I) g u x)) ≤ C := by
  have hcont := continuous_g_norm_gradFun (I := I) (M := M) g hu
  obtain ⟨C, hC_nn, hC_bound⟩ := exists_bound_continuous_compactSpace
    (M := M) (f := fun x : M => Real.sqrt
        (g.inner x
          (CalabiYau.Riemannian.gradFun
            (I := I) g u x)
          (CalabiYau.Riemannian.gradFun
            (I := I) g u x))) hcont
  refine ⟨C, hC_nn, fun x => ?_⟩
  have h := hC_bound x
  rw [abs_of_nonneg (Real.sqrt_nonneg _)] at h
  exact h

private lemma eLpNorm_g_norm_gradFun_chart_local_lt_top_smooth
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (_hp_one : 1 ≤ p) (α : M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    eLpNorm (Set.indicator (chartAt H α).source
        (fun x : M => Real.sqrt
          (g.inner x
            (CalabiYau.Riemannian.gradFun
              (I := I) g u x)
            (CalabiYau.Riemannian.gradFun
              (I := I) g u x)))) p
        (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M)) < ⊤ := by
  classical
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  let : MeasurableSpace M := borel M
  have : BorelSpace M := ⟨rfl⟩
  have hcont := continuous_g_norm_gradFun (I := I) (M := M) g hu
  obtain ⟨C, hC_nn, hC_bound⟩ :=
    exists_bound_g_norm_gradFun (I := I) (M := M) g hu
  have hRiemMeas_finite : IsFiniteMeasure
      (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M)) :=
    CalabiYau.RiemannianVolume.riemannianMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M)
      (CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M)
  have h_ae_bound : ∀ᵐ x ∂(CalabiYau.RiemannianVolume.riemannianMeasure
        (I := I) g (CalabiYau.RiemannianVolume.chartAtlasPOU I M)),
        ‖Set.indicator (chartAt H α).source
            (fun x : M => Real.sqrt
              (g.inner x
                (CalabiYau.Riemannian.gradFun
                  (I := I) g u x)
                (CalabiYau.Riemannian.gradFun
                  (I := I) g u x))) x‖ ≤ C := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    by_cases hx : x ∈ (chartAt H α).source
    · rw [Set.indicator_of_mem hx, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      exact hC_bound x
    · rw [Set.indicator_of_notMem hx]
      simpa using hC_nn
  have hmeas : Measurable (Set.indicator (chartAt H α).source
      (fun x : M => Real.sqrt
        (g.inner x
          (CalabiYau.Riemannian.gradFun
            (I := I) g u x)
          (CalabiYau.Riemannian.gradFun
            (I := I) g u x)))) := by
    apply Measurable.indicator
    · exact hcont.measurable
    · exact ((chartAt H α).open_source).measurableSet
  exact (MemLp.of_bound hmeas.aestronglyMeasurable C h_ae_bound).2

lemma memLp_g_norm_gradFun_smooth
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (p : ℝ≥0∞)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    MemLp (fun x : M => Real.sqrt
        (g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g u x))) p
      (riemannianVolumeMeasure I M g) := by
  have hG_cont : Continuous (fun x : M => Real.sqrt
      (g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g u x))) := by
    have hcont := TangentBundle.continuous_g_inner_of_smooth_sections
      (I := I) (M := M) g (gradG (I := I) g ⟨_, hu⟩) (gradG (I := I) g ⟨_, hu⟩)
    have hcoe : (fun x : M =>
        g.inner x ((gradG (I := I) g ⟨_, hu⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((gradG (I := I) g ⟨_, hu⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)) =
        (fun x : M => g.inner x (gradFun (I := I) g u x)
          (gradFun (I := I) g u x)) := by
      funext x
      rw [grad_g_apply (I := I) g ⟨_, hu⟩ x]
      change g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g u x) =
        g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g u x)
      rfl
    rw [hcoe] at hcont
    exact Real.continuous_sqrt.comp hcont
  exact continuous_memLp_of_compactSpace g p hG_cont

lemma hasWeakRiemannianGradLp_gradFun
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    HasWeakRiemannianGradLp (I := I) (M := M) g u (gradFun (I := I) g u) := by
  have h_smooth_gw : Intrinsic.HasWeakRiemannianGrad (I := I) (M := M) g u
      (gradG (I := I) g ⟨_, hu⟩) :=
    Intrinsic.hasWeakRiemannianGrad_grad_g_of_contMDiff
      (I := I) (M := M) g hu
  have h_lp := IntrinsicLp.hasWeakRiemannianGradLp_of_smooth (I := I) (M := M)
    h_smooth_gw
  have h_eq : (fun x : M => ((gradG (I := I) g ⟨_, hu⟩ :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x : E)) =
      (fun x : M => (gradFun (I := I) g u x : E)) := by
    funext x
    exact grad_g_apply (I := I) g ⟨_, hu⟩ x
  rw [h_eq] at h_lp
  exact h_lp

end Equivalence
end Sobolev
