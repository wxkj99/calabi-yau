-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/H1Compl/ToLpChartBridge.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.ChartBilinear.H1Compl
public import CalabiYau.Analysis.Elliptic.Regularity.LaplacianDomain.L2
public import CalabiYau.Analysis.Sobolev.Chart.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Group.NullSubmodule
public import Mathlib.Analysis.Normed.Group.Uniform
public import CalabiYau.Analysis.Sobolev.Euclidean.Completeness.IteratedSobolevBanach
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Topology.UniformSpace.UniformEmbedding
public import CalabiYau.Analysis.Sobolev.Chart.RiemannianMeasureComparison
public import CalabiYau.Analysis.Sobolev.Manifold.Measure.UniformChartComparison
public import CalabiYau.Analysis.Sobolev.Chart.BanachCompleteness.CompletenessLp
public import CalabiYau.Analysis.Sobolev.Euclidean.WeakDerivative.Closedness
public import CalabiYau.Analysis.Sobolev.Manifold.Embedding.Basic
public import CalabiYau.Analysis.Sobolev.Manifold.RiemannianRellich
public import CalabiYau.Geometry.Riemannian.Volume.Family.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import CalabiYau.Geometry.Riemannian.Volume.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import CalabiYau.Geometry.Riemannian.Volume.Invariance
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Measure.WithDensity

@[expose] public section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace CalabiYau
namespace Analysis
namespace Laplacian
namespace H1ComplToLpChartBridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open CalabiYau.RiemannianVolume
open CalabiYau.Laplacian.MetricExtension
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl

variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} in
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in
private local instance : MeasurableSpace E := borel E
variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} in
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in
private local instance : BorelSpace E := ⟨rfl⟩
variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} in
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in
local instance : MeasurableSpace M := borel M
variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} in
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))


section

variable [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M] [CompactSpace M]

private lemma chartAtlasPOU_continuous (α : M) :
    Continuous fun x : M => (chartAtlasPOU I M α : M → ℝ) x :=
  (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff.continuous

private lemma chartAtlasPOU_measurable (α : M) :
    Measurable fun x : M => (chartAtlasPOU I M α : M → ℝ) x :=
  (chartAtlasPOU_continuous (I := I) (M := M) α).measurable

private lemma enorm_pou_mul_le (α : M) (u : M → ℝ) (x : M) :
    ‖(chartAtlasPOU I M α : M → ℝ) x * u x‖ₑ ≤ ‖u x‖ₑ := by
  have h_nn : (0 : ℝ) ≤ (chartAtlasPOU I M α : M → ℝ) x :=
    (chartAtlasPOU I M).nonneg α x
  have h_le : (chartAtlasPOU I M α : M → ℝ) x ≤ 1 :=
    (chartAtlasPOU I M).le_one α x
  have h_abs : |(chartAtlasPOU I M α : M → ℝ) x| ≤ 1 := by
    rw [abs_of_nonneg h_nn]; exact h_le
  have habsmul : |(chartAtlasPOU I M α : M → ℝ) x * u x| ≤ |u x| := by
    rw [abs_mul]
    have h_abs_u_nn : 0 ≤ |u x| := abs_nonneg _
    calc |(chartAtlasPOU I M α : M → ℝ) x| * |u x|
        ≤ 1 * |u x| := by gcongr
      _ = |u x| := one_mul _
  rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal habsmul

private lemma tsupport_pou_mul_subset_chartSource (α : M) (u : M → ℝ) :
    tsupport (fun x : M => (chartAtlasPOU I M α : M → ℝ) x * u x) ⊆
      (chartAt H α).source := by
  classical
  have h_support_sub : Function.support
      (fun x : M => (chartAtlasPOU I M α : M → ℝ) x * u x) ⊆
        Function.support fun x : M => (chartAtlasPOU I M α : M → ℝ) x := by
    intro x hx
    simp only [Function.mem_support] at hx
    by_contra hρ_zero
    apply hx
    simp only [Function.mem_support, not_not] at hρ_zero
    rw [hρ_zero]; ring
  have h_tsupp_sub : tsupport (fun x : M => (chartAtlasPOU I M α : M → ℝ) x * u x) ⊆
      tsupport fun x : M => (chartAtlasPOU I M α : M → ℝ) x :=
    closure_mono h_support_sub
  exact h_tsupp_sub.trans
    ((CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M) α)

private lemma tsupport_pou_mul_subset_tsupport_pou (α : M) (u : M → ℝ) :
    tsupport (fun x : M => (chartAtlasPOU I M α : M → ℝ) x * u x) ⊆
      tsupport fun x : M => (chartAtlasPOU I M α : M → ℝ) x := by
  classical
  have h_support_sub : Function.support
      (fun x : M => (chartAtlasPOU I M α : M → ℝ) x * u x) ⊆
        Function.support fun x : M => (chartAtlasPOU I M α : M → ℝ) x := by
    intro x hx
    simp only [Function.mem_support] at hx
    by_contra hρ_zero
    apply hx
    simp only [Function.mem_support, not_not] at hρ_zero
    rw [hρ_zero]; ring
  exact closure_mono h_support_sub

private lemma chartPushed_eq_chartPushedRaw_on_chartTarget
    (α : M) (u : M → ℝ) {y : EuclN}
    (hy : y ∈ Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α) :
    Sobolev.Chart.chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u y =
      Sobolev.Chart.chartPushedRaw I α
        (fun x : M =>
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M α : M → ℝ) x * u x) y := by
  classical
  unfold Sobolev.Chart.chartPushed
  rw [Sobolev.Chart.chartPushedRaw_apply_of_mem
    (I := I) (M := M) α (fun x : M => (chartAtlasPOU I M α : M → ℝ) x * u x) hy]

end

section

variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M] [CompactSpace M]

private def kαCompact (α : M) : Set EuclN :=
  (toEuclidean : E ≃L[ℝ] EuclN) ''
    ((extChartAt I α) '' (tsupport fun x : M => (chartAtlasPOU I M α : M → ℝ) x))

end

section

variable [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M] [CompactSpace M]

private lemma kαCompact_isCompact (α : M) :
    IsCompact (kαCompact (I := I) (M := M) α) := by
  classical
  unfold kαCompact
  have h_tsupp_compact : IsCompact (tsupport
      fun x : M => (chartAtlasPOU I M α : M → ℝ) x) :=
    isClosed_tsupport _ |>.isCompact
  have h_tsupp_sub_source : tsupport (fun x : M => (chartAtlasPOU I M α : M → ℝ) x) ⊆
      (chartAt H α).source :=
    (CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M) α
  have h_ext_cont : ContinuousOn (extChartAt I α)
      (tsupport fun x : M => (chartAtlasPOU I M α : M → ℝ) x) := by
    have h_source_eq : (chartAt H α).source = (extChartAt I α).source :=
      (CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
        (I := I) (M := M) α).symm
    refine (continuousOn_extChartAt (I := I) α).mono ?_
    rw [← h_source_eq]; exact h_tsupp_sub_source
  have h_ext_image_compact : IsCompact ((extChartAt I α) '' (tsupport
      fun x : M => (chartAtlasPOU I M α : M → ℝ) x)) :=
    h_tsupp_compact.image_of_continuousOn h_ext_cont
  exact h_ext_image_compact.image (toEuclidean (E := E)).continuous

private lemma kαCompact_subset_chartTargetEuclid (α : M) :
    kαCompact (I := I) (M := M) α ⊆
      Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α := by
  classical
  intro y hy
  rcases hy with ⟨z, hz, hzy⟩
  rcases hz with ⟨x, hx, hxz⟩
  have h_tsupp_sub_source : tsupport (fun x : M => (chartAtlasPOU I M α : M → ℝ) x) ⊆
      (chartAt H α).source :=
    (CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M) α
  have hxsrc : x ∈ (extChartAt I α).source := by
    rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
      (I := I) (M := M)]
    exact h_tsupp_sub_source hx
  have hz_target : z ∈ (extChartAt I α).target := by
    rw [← hxz]; exact (extChartAt I α).map_source hxsrc
  refine ⟨z, hz_target, hzy⟩

private lemma chartPushedRaw_pou_mul_support_subset_kα
    (α : M) (u : M → ℝ) :
    Function.support (Sobolev.Chart.chartPushedRaw I α
        fun x : M => (chartAtlasPOU I M α : M → ℝ) x * u x) ⊆
      kαCompact (I := I) (M := M) α := by
  classical
  intro y hy
  have hy_ne : Sobolev.Chart.chartPushedRaw I α
      (fun x : M => (chartAtlasPOU I M α : M → ℝ) x * u x) y ≠ 0 := hy
  by_cases hy_in : y ∈ Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α
  · have h_apply :=
      Sobolev.Chart.chartPushedRaw_apply_of_mem
        (I := I) (M := M) α (fun x : M => (chartAtlasPOU I M α : M → ℝ) x * u x) hy_in
    rw [h_apply] at hy_ne
    have hρα_ne : (chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) ≠ 0 := by
      intro h_ρ_zero
      apply hy_ne
      rw [h_ρ_zero]; ring
    have hp_in_support_ρα : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
        Function.support (fun x : M => (chartAtlasPOU I M α : M → ℝ) x) := hρα_ne
    have hp_in_tsupp : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
        tsupport fun x : M => (chartAtlasPOU I M α : M → ℝ) x :=
      subset_tsupport _ hp_in_support_ρα
    rcases hy_in with ⟨z, hz_target, hzy⟩
    have hyz_symm : (toEuclidean (E := E)).symm y = z := by
      rw [← hzy]; exact (toEuclidean (E := E)).symm_apply_apply z
    have hext_right : (extChartAt I α) ((extChartAt I α).symm z) = z :=
      (extChartAt I α).right_inv hz_target
    refine ⟨z, ⟨(extChartAt I α).symm z, ?_, hext_right⟩, hzy⟩
    rwa [hyz_symm] at hp_in_tsupp
  · exfalso
    apply hy_ne
    exact Sobolev.Chart.chartPushedRaw_apply_of_notMem
      (I := I) (M := M) α (fun x : M => (chartAtlasPOU I M α : M → ℝ) x * u x) hy_in

private lemma chartPushedRaw_pou_mul_tsupport_subset_kα
    (α : M) (u : M → ℝ) :
    tsupport (Sobolev.Chart.chartPushedRaw I α
        fun x : M => (chartAtlasPOU I M α : M → ℝ) x * u x) ⊆
      kαCompact (I := I) (M := M) α := by
  refine closure_minimal (chartPushedRaw_pou_mul_support_subset_kα
    (I := I) (M := M) α u) ?_
  exact (kαCompact_isCompact (I := I) (M := M) α).isClosed

private lemma exists_density_sup_on_kα
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∃ M_sup : ℝ, 0 < M_sup ∧
      ∀ y ∈ kαCompact (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y ≤ M_sup := by
  classical
  by_cases hKne : (kαCompact (I := I) (M := M) α).Nonempty
  · have hK_compact : IsCompact (kαCompact (I := I) (M := M) α) :=
      kαCompact_isCompact (I := I) (M := M) α
    have hK_in : kαCompact (I := I) (M := M) α ⊆
        Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α :=
      kαCompact_subset_chartTargetEuclid (I := I) (M := M) α
    have h_dens_contOn : ContinuousOn (densityOnEuclid (I := I) g α)
        (kαCompact (I := I) (M := M) α) :=
      (densityOnEuclid_continuousOn (I := I) g α).mono hK_in
    obtain ⟨y₀, hy₀_mem, hy₀_max⟩ :=
      hK_compact.exists_isMaxOn hKne h_dens_contOn
    have h_pos : 0 < densityOnEuclid (I := I) g α y₀ :=
      densityOnEuclid_pos (I := I) g α (hK_in hy₀_mem)
    refine ⟨densityOnEuclid (I := I) g α y₀, h_pos, fun y hy => hy₀_max hy⟩
  · refine ⟨1, by norm_num, ?_⟩
    intro y hy
    rw [Set.not_nonempty_iff_eq_empty] at hKne
    rw [hKne] at hy
    exact absurd hy (Set.notMem_empty y)

end

section

variable [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M] [CompactSpace M]

private lemma eLpNorm_chartPulledWeighted_le_density_volume_on_kα
    (g : SmoothRiemannianMetric I M) (α : M)
    (M_sup : ℝ) (hM_sup_pos : 0 < M_sup)
    (hM_sup_bd : ∀ y ∈ kαCompact (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y ≤ M_sup)
    {f : EuclN → ℝ} (hf_support : tsupport f ⊆ kαCompact (I := I) (M := M) α)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤) :
    eLpNorm f p
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)) ≤
      ENNReal.ofReal (M_sup ^ (1 / p.toReal)) *
        eLpNorm f p
          ((volume : Measure EuclN).restrict
            (Sobolev.Chart.chartTargetEuclid (I := I) (M := M)
              α)) := by
  classical
  have hp_ne_zero : p ≠ 0 := by
    intro h; rw [h] at hp_one; exact absurd hp_one (by norm_num)
  have hp_toReal_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_top
  set S : Set EuclN := Sobolev.Chart.chartTargetEuclid
    (I := I) (M := M) α with hS_def
  have hS_open : IsOpen S := Sobolev.Chart.chartTargetEuclid_isOpen
    (I := I) (M := M) α
  have hS_meas : MeasurableSet S := hS_open.measurableSet
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_top]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_top]
  have h_lint_le :
      ∫⁻ y, ‖f y‖ₑ ^ p.toReal
          ∂((chartPulledWeightedMeasure (I := I) g α).restrict S) ≤
        ENNReal.ofReal M_sup *
          ∫⁻ y, ‖f y‖ₑ ^ p.toReal ∂((volume : Measure EuclN).restrict S) := by
    rw [show (chartPulledWeightedMeasure (I := I) g α).restrict S =
        ((volume : Measure EuclN).restrict S).withDensity
          (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y)) by
      unfold chartPulledWeightedMeasure
      exact MeasureTheory.restrict_withDensity hS_meas _]
    rw [MeasureTheory.lintegral_withDensity_eq_lintegral_mul_non_measurable₀]
    rotate_left
    · have hdens_contOn : ContinuousOn (densityOnEuclid (I := I) g α) S :=
        densityOnEuclid_continuousOn (I := I) g α
      exact (hdens_contOn.aemeasurable hS_meas).ennreal_ofReal
    · refine Filter.Eventually.of_forall (fun y => ENNReal.ofReal_lt_top)
    rw [show ENNReal.ofReal M_sup *
          ∫⁻ y, ‖f y‖ₑ ^ p.toReal ∂((volume : Measure EuclN).restrict S) =
        ∫⁻ y, ENNReal.ofReal M_sup * ‖f y‖ₑ ^ p.toReal
          ∂((volume : Measure EuclN).restrict S) from
      (MeasureTheory.lintegral_const_mul' (r := ENNReal.ofReal M_sup) _ ENNReal.ofReal_ne_top).symm]
    refine MeasureTheory.lintegral_mono_ae ?_
    refine Filter.Eventually.of_forall (fun y => ?_)
    by_cases hfy : f y = 0
    · simp [hfy, ENNReal.zero_rpow_of_pos hp_toReal_pos]
    · have hy_in : y ∈ kαCompact (I := I) (M := M) α := hf_support (subset_tsupport _ hfy)
      have h_dens_le : densityOnEuclid (I := I) g α y ≤ M_sup := hM_sup_bd y hy_in
      have h_ofReal_le :
          ENNReal.ofReal (densityOnEuclid (I := I) g α y) ≤ ENNReal.ofReal M_sup :=
        ENNReal.ofReal_le_ofReal h_dens_le
      exact mul_le_mul_left h_ofReal_le _
  have h_pow_le :
      (∫⁻ y, ‖f y‖ₑ ^ p.toReal
          ∂((chartPulledWeightedMeasure (I := I) g α).restrict S)) ^
        (1 / p.toReal) ≤
        (ENNReal.ofReal M_sup *
          ∫⁻ y, ‖f y‖ₑ ^ p.toReal
            ∂((volume : Measure EuclN).restrict S)) ^ (1 / p.toReal) := by
    apply ENNReal.rpow_le_rpow h_lint_le
    positivity
  refine h_pow_le.trans ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / p.toReal)]
  gcongr
  rw [← ENNReal.ofReal_rpow_of_pos hM_sup_pos]

theorem eLpNorm_chartPushed_chartPulledWeightedMeasure_restrict_le
    (g : SmoothRiemannianMetric I M) (α : M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤) :
    ∃ C : ℝ, 0 < C ∧ ∀ {u : M → ℝ}, Measurable u →
      eLpNorm
          (Sobolev.Chart.chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u) p
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
            eLpNorm u p (riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  obtain ⟨M_sup, hM_sup_pos, hM_sup_bd⟩ := exists_density_sup_on_kα (I := I) (M := M) g α
  by_cases hKne : (kαCompact (I := I) (M := M) α).Nonempty
  · have hKα_compact : IsCompact (kαCompact (I := I) (M := M) α) :=
      kαCompact_isCompact (I := I) (M := M) α
    set K_E : Set E := (toEuclidean (E := E)).symm '' (kαCompact (I := I) (M := M) α)
      with hK_E_def
    have hK_E_compact : IsCompact K_E :=
      hKα_compact.image (toEuclidean (E := E)).symm.continuous
    have hK_E_ne : K_E.Nonempty := hKne.image _
    have hK_E_sub_target : K_E ⊆ (extChartAt I α).target := by
      intro x hx
      rcases hx with ⟨y, hy_kα, hxy⟩
      have hy_target : y ∈
          Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α :=
        kαCompact_subset_chartTargetEuclid (I := I) (M := M) α hy_kα
      rcases hy_target with ⟨z, hz_target, hzy⟩
      have h_x_eq : x = z := by
        rw [← hxy, ← hzy]; simp
      rw [h_x_eq]; exact hz_target
    obtain ⟨C_K, hC_K_pos, hC_K_bnd⟩ :=
      Sobolev.Chart.eLpNorm_chartPushedRaw_le_const_mul_eLpNorm_riemannianMeasure_uniform
        (I := I) (M := M) g α hK_E_compact hK_E_ne hK_E_sub_target hp_one hp_top
    refine ⟨M_sup ^ (1 / p.toReal) * C_K, ?_, ?_⟩
    · exact mul_pos (Real.rpow_pos_of_pos hM_sup_pos _) hC_K_pos
    intro u hu_meas
    set v : M → ℝ := fun x : M => (chartAtlasPOU I M α : M → ℝ) x * u x with hv_def
    have hv_meas : Measurable v :=
      (chartAtlasPOU_measurable (I := I) (M := M) α).mul hu_meas
    have hv_support : tsupport v ⊆ (chartAt H α).source :=
      tsupport_pou_mul_subset_chartSource (I := I) (M := M) α u
    have hv_image_sub_K_E : (extChartAt I α) '' (tsupport v) ⊆ K_E := by
      intro z hz
      rcases hz with ⟨x, hx_support_v, hxz⟩
      have hx_support_ρα : x ∈ tsupport fun x : M => (chartAtlasPOU I M α : M → ℝ) x :=
        tsupport_pou_mul_subset_tsupport_pou (I := I) (M := M) α u hx_support_v
      have h_toEz_in_Kα : (toEuclidean (E := E)) z ∈ kαCompact (I := I) (M := M) α := by
        unfold kαCompact
        exact ⟨z, ⟨x, hx_support_ρα, hxz⟩, rfl⟩
      refine ⟨(toEuclidean (E := E)) z, h_toEz_in_Kα, ?_⟩
      simp
    have h_aeeq :
        Sobolev.Chart.chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u =ᵐ[
            (chartPulledWeightedMeasure (I := I) g α).restrict
              (Sobolev.Chart.chartTargetEuclid
                (I := I) (M := M) α)]
          Sobolev.Chart.chartPushedRaw I α v := by
      refine (MeasureTheory.ae_restrict_iff'
        (Sobolev.Chart.chartTargetEuclid_measurableSet
        (I := I) (M := M) α)).mpr ?_
      refine Filter.Eventually.of_forall (fun y hy => ?_)
      exact chartPushed_eq_chartPushedRaw_on_chartTarget (I := I) (M := M) α u hy
    have h_eLp_congr :
        eLpNorm
            (Sobolev.Chart.chartPushed (I := I) (M := M)
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u) p
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (Sobolev.Chart.chartTargetEuclid
                (I := I) (M := M) α)) =
          eLpNorm (Sobolev.Chart.chartPushedRaw I α v) p
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (Sobolev.Chart.chartTargetEuclid
                (I := I) (M := M) α)) := MeasureTheory.eLpNorm_congr_ae h_aeeq
    rw [h_eLp_congr]
    have h_step1 :=
      eLpNorm_chartPulledWeighted_le_density_volume_on_kα
        (I := I) (M := M) g α M_sup hM_sup_pos hM_sup_bd
        (f := Sobolev.Chart.chartPushedRaw I α v)
        (chartPushedRaw_pou_mul_tsupport_subset_kα (I := I) (M := M) α u)
        hp_one hp_top
    have h_step2_raw := hC_K_bnd hv_meas hv_support hv_image_sub_K_E
    have h_step2 : eLpNorm
          (Sobolev.Chart.chartPushedRaw I α v) p
          ((volume : Measure EuclN).restrict
            (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C_K *
            eLpNorm v p (riemannianVolumeMeasure (I := I) (M := M) g) := h_step2_raw
    have h_step3 :
        eLpNorm v p (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          eLpNorm u p (riemannianVolumeMeasure (I := I) (M := M) g) := by
      refine MeasureTheory.eLpNorm_mono_enorm (fun x => ?_)
      exact enorm_pou_mul_le (I := I) (M := M) α u x
    calc eLpNorm (Sobolev.Chart.chartPushedRaw I α v) p
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (Sobolev.Chart.chartTargetEuclid
                (I := I) (M := M) α)) ≤
          ENNReal.ofReal (M_sup ^ (1 / p.toReal)) *
            eLpNorm (Sobolev.Chart.chartPushedRaw I α v) p
              ((volume : Measure EuclN).restrict
                (Sobolev.Chart.chartTargetEuclid
                  (I := I) (M := M) α)) := h_step1
        _ ≤ ENNReal.ofReal (M_sup ^ (1 / p.toReal)) *
              (ENNReal.ofReal C_K *
                eLpNorm v p (riemannianVolumeMeasure (I := I) (M := M) g)) := by
          gcongr
        _ ≤ ENNReal.ofReal (M_sup ^ (1 / p.toReal)) *
              (ENNReal.ofReal C_K *
                eLpNorm u p (riemannianVolumeMeasure (I := I) (M := M) g)) := by
          gcongr
        _ = ENNReal.ofReal (M_sup ^ (1 / p.toReal) * C_K) *
              eLpNorm u p (riemannianVolumeMeasure (I := I) (M := M) g) := by
          rw [← mul_assoc]
          rw [← ENNReal.ofReal_mul (le_of_lt (Real.rpow_pos_of_pos hM_sup_pos _))]
  · refine ⟨1, by norm_num, ?_⟩
    intro u hu_meas
    rw [Set.not_nonempty_iff_eq_empty] at hKne
    have hρα_zero : ∀ x : M, (chartAtlasPOU I M α : M → ℝ) x = 0 := by
      intro x
      have h_support_empty : Function.support
          (fun x : M => (chartAtlasPOU I M α : M → ℝ) x) = ∅ := by
        by_contra h_ne
        have h_ne' : Function.support (fun x : M => (chartAtlasPOU I M α : M → ℝ) x) ≠ ∅ := h_ne
        have h_tsupp_ne : (tsupport fun x : M => (chartAtlasPOU I M α : M → ℝ) x).Nonempty := by
          rw [Set.nonempty_iff_ne_empty]
          intro h_tsupp_empty
          apply h_ne'
          have h_support_sub : Function.support (fun x : M => (chartAtlasPOU I M α : M → ℝ) x) ⊆
              tsupport (fun x : M => (chartAtlasPOU I M α : M → ℝ) x) := subset_tsupport _
          rw [h_tsupp_empty] at h_support_sub
          exact Set.subset_eq_empty h_support_sub rfl
        have hKα_ne : (kαCompact (I := I) (M := M) α).Nonempty := by
          obtain ⟨x, hx⟩ := h_tsupp_ne
          refine ⟨(toEuclidean (E := E)) ((extChartAt I α) x), ?_⟩
          unfold kαCompact
          exact ⟨(extChartAt I α) x, ⟨x, hx, rfl⟩, rfl⟩
        rw [hKne] at hKα_ne
        exact absurd hKα_ne (Set.not_nonempty_empty)
      have hxn : x ∉ Function.support (fun x : M => (chartAtlasPOU I M α : M → ℝ) x) := by
        rw [h_support_empty]; exact Set.notMem_empty x
      exact Function.notMem_support.mp hxn
    have h_chartPushed_zero :
        Sobolev.Chart.chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u =
          fun _ : EuclN => (0 : ℝ) := by
      funext y
      unfold Sobolev.Chart.chartPushed
      rw [hρα_zero]; ring
    rw [h_chartPushed_zero]
    have h_eLpNorm_zero :
        eLpNorm (fun _ : EuclN => (0 : ℝ)) p
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)) =
              0 := by
      have h_zero_eq : (fun _ : EuclN => (0 : ℝ)) = (0 : EuclN → ℝ) := rfl
      rw [h_zero_eq, MeasureTheory.eLpNorm_zero]
    rw [h_eLpNorm_zero]
    exact zero_le

end

section

variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M] [CompactSpace M]

private noncomputable def extChartAtSymmExt (α : M) : E → M := by
  classical
  exact (extChartAt I α).target.piecewise
    (fun y : E => (extChartAt I α).symm y)
    (fun _ : E => α)

end

section

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

private lemma extChartAtSymmExt_eq_on_target (α : M) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    extChartAtSymmExt (I := I) (M := M) α y = (extChartAt I α).symm y := by
  classical
  change (extChartAt I α).target.piecewise
    (fun y : E => (extChartAt I α).symm y)
    (fun _ : E => α) y = _
  rw [Set.piecewise_eq_of_mem _ _ _ hy]

private lemma extChartAtSymmExt_measurable (α : M) :
    Measurable (extChartAtSymmExt (I := I) (M := M) α) := by
  classical
  unfold extChartAtSymmExt
  exact ContinuousOn.measurable_piecewise
    (continuousOn_extChartAt_symm (I := I) α)
    continuousOn_const
    (CalabiYau.RiemannianVolume.measurableSet_extChartAt_target
      (I := I) (M := M) α)

end

section

variable [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M] [CompactSpace M]

theorem chartPushed_memLp_chartPulledWeightedMeasure_restrict_of_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {u : M → ℝ} (hu_meas : Measurable u)
    (hu_memLp : MemLp u 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    MemLp
        (Sobolev.Chart.chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hp_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  obtain ⟨C, hC_pos, hC_bnd⟩ :=
    eLpNorm_chartPushed_chartPulledWeightedMeasure_restrict_le (I := I) (M := M) g α
      (p := 2) hp_one hp_top
  refine ⟨?_, ?_⟩
  · set ψ : EuclN → ℝ := fun y =>
        ((chartAtlasPOU I M α : M → ℝ)
          (extChartAtSymmExt (I := I) (M := M) α ((toEuclidean (E := E)).symm y))) *
        u (extChartAtSymmExt (I := I) (M := M) α ((toEuclidean (E := E)).symm y))
      with hψ_def
    have h_extSymm_meas : Measurable (extChartAtSymmExt (I := I) (M := M) α) :=
      extChartAtSymmExt_measurable (I := I) (M := M) α
    have h_toE_symm_meas : Measurable
        (fun y : EuclN => (toEuclidean (E := E)).symm y) :=
      (toEuclidean (E := E)).symm.continuous.measurable
    have hψ_meas : Measurable ψ := by
      change Measurable (fun y =>
        ((chartAtlasPOU I M α : M → ℝ)
          (extChartAtSymmExt (I := I) (M := M) α ((toEuclidean (E := E)).symm y))) *
        u (extChartAtSymmExt (I := I) (M := M) α ((toEuclidean (E := E)).symm y)))
      refine Measurable.mul ?_ ?_
      · exact (chartAtlasPOU_measurable (I := I) (M := M) α).comp
          (h_extSymm_meas.comp h_toE_symm_meas)
      · exact hu_meas.comp (h_extSymm_meas.comp h_toE_symm_meas)
    have h_ψ_eq_chartPushed : ∀ y ∈ Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α,
        ψ y = Sobolev.Chart.chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u y := by
      intro y hy
      have h_toE_symm_in : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
        rcases hy with ⟨z, hz_target, hzy⟩
        have h_eq : (toEuclidean (E := E)).symm y = z := by
          rw [← hzy]; exact (toEuclidean (E := E)).symm_apply_apply z
        rw [h_eq]; exact hz_target
      change ((chartAtlasPOU I M α : M → ℝ)
          (extChartAtSymmExt (I := I) (M := M) α ((toEuclidean (E := E)).symm y))) *
        u (extChartAtSymmExt (I := I) (M := M) α ((toEuclidean (E := E)).symm y)) =
        Sobolev.Chart.chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u y
      rw [extChartAtSymmExt_eq_on_target (I := I) (M := M) α h_toE_symm_in]
      rfl
    have h_aeeq :
        Sobolev.Chart.chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u =ᵐ[
            (chartPulledWeightedMeasure (I := I) g α).restrict
              (Sobolev.Chart.chartTargetEuclid
                (I := I) (M := M) α)] ψ := by
      refine (MeasureTheory.ae_restrict_iff'
        (Sobolev.Chart.chartTargetEuclid_measurableSet
        (I := I) (M := M) α)).mpr ?_
      refine Filter.Eventually.of_forall (fun y hy => ?_)
      exact (h_ψ_eq_chartPushed y hy).symm
    exact (hψ_meas.aestronglyMeasurable).congr h_aeeq.symm
  · refine lt_of_le_of_lt (hC_bnd hu_meas) ?_
    apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    exact hu_memLp.2

theorem chartPushed_tendsto_chartPulledWeightedMeasure
    (g : SmoothRiemannianMetric I M) (α : M)
    {u : ℕ → M → ℝ} {u_lim : M → ℝ}
    (hu_meas : ∀ n, Measurable (u n)) (hu_lim_meas : Measurable u_lim)
    (h_tendsto : Filter.Tendsto
      (fun n => eLpNorm (fun x => u n x - u_lim x) 2
        (riemannianVolumeMeasure (I := I) (M := M) g)) Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => eLpNorm
        (fun y =>
          Sobolev.Chart.chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α (u n) y -
          Sobolev.Chart.chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u_lim y) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)))
      Filter.atTop (nhds 0) := by
  classical
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hp_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  obtain ⟨C, hC_pos, hC_bnd⟩ :=
    eLpNorm_chartPushed_chartPulledWeightedMeasure_restrict_le (I := I) (M := M) g α
      (p := 2) hp_one hp_top
  have h_chartPushed_sub : ∀ n,
      (fun y =>
        Sobolev.Chart.chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α (u n) y -
        Sobolev.Chart.chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u_lim y) =
      Sobolev.Chart.chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α
        (fun x : M => u n x - u_lim x) := by
    intro n
    funext y
    unfold Sobolev.Chart.chartPushed
    ring
  have h_bnd : ∀ n,
      eLpNorm (fun y =>
          Sobolev.Chart.chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α (u n) y -
          Sobolev.Chart.chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u_lim y) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal C *
          eLpNorm (fun x : M => u n x - u_lim x) 2
            (riemannianVolumeMeasure (I := I) (M := M) g) := by
    intro n
    rw [h_chartPushed_sub n]
    exact hC_bnd ((hu_meas n).sub hu_lim_meas)
  have h_rhs_tendsto :
      Filter.Tendsto (fun n => ENNReal.ofReal C *
          eLpNorm (fun x : M => u n x - u_lim x) 2
            (riemannianVolumeMeasure (I := I) (M := M) g))
        Filter.atTop (nhds (ENNReal.ofReal C * 0)) :=
    ENNReal.Tendsto.const_mul h_tendsto (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_zero] at h_rhs_tendsto
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_rhs_tendsto
    (fun _ => zero_le) ?_
  intro n
  exact h_bnd n

end

end H1ComplToLpChartBridge
end Laplacian
end Analysis
end CalabiYau
