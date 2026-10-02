-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Approximation/Density/FirstOrder.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Approximation.Density.Preliminaries
public import CalabiYau.Analysis.Sobolev.Tools.StrictStrongSupport
public import CalabiYau.Analysis.Sobolev.Euclidean.SupportAndDomain.CrossChartBoundStrictMemWkp
public import CalabiYau.Analysis.Sobolev.Chart.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Group.NullSubmodule
public import Mathlib.Analysis.Normed.Group.Uniform
public import CalabiYau.Analysis.Sobolev.Euclidean.Completeness.IteratedSobolevBanach
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Topology.UniformSpace.UniformEmbedding
public import CalabiYau.Analysis.Sobolev.Chart.BanachCompleteness.CompletenessLp
public import CalabiYau.Analysis.Sobolev.Chart.RiemannianMeasureComparison
public import CalabiYau.Analysis.Sobolev.Manifold.Measure.UniformChartComparison
public import CalabiYau.Analysis.Sobolev.Euclidean.WeakDerivative.Closedness
public import CalabiYau.Analysis.Sobolev.Manifold.Embedding.Basic
public import CalabiYau.Analysis.Sobolev.Manifold.RiemannianRellich
public import CalabiYau.Geometry.Riemannian.Volume.Family.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import CalabiYau.Geometry.Riemannian.Volume.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

@[expose] public section

-- Private declarations used in public declarations require the compatibility option below.

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace Sobolev
namespace Chart

variable {E H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [IsManifold I ∞ M] in
lemma chartPullback_sub (α : M)
    (ψ₁ ψ₂ : EuclN → ℝ) :
    chartPullback I α (fun y => ψ₁ y - ψ₂ y) =
      fun x => chartPullback I α ψ₁ x - chartPullback I α ψ₂ x := by
  classical
  funext x
  by_cases hx : x ∈ (chartAt H α).source
  · simp [chartPullback_apply_of_mem (I := I) (M := M) α _ hx]
  · simp [chartPullback_apply_of_notMem (I := I) (M := M) α _ hx]

lemma fun_eq_finset_sum_chartPullback_chartPushed
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (u : M → ℝ) :
    (fun x : M => u x) =
      fun x =>
        ∑ α ∈ CalabiYau.RiemannianVolume.chartAtlasPOUFinset
            (I := I) (M := M),
          chartPullback I α
            (chartPushed (I := I) (M := M)
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u) x := by
  classical
  funext x
  have h_eq : ∀ α ∈ CalabiYau.RiemannianVolume.chartAtlasPOUFinset
        (I := I) (M := M),
      chartPullback I α
          (chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u) x =
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M α : M → ℝ) x *
          u x := by
    intro α _
    by_cases hxα : x ∈ (chartAt H α).source
    · rw [chartPullback_apply_of_mem (I := I) (M := M) α _ hxα]
      have hx_extchartsource : x ∈ (extChartAt I α).source := by
        rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
          (I := I) (M := M)]
        exact hxα
      have h_symm_toEucl : (toEuclidean (E := E)).symm
          ((toEuclidean (E := E)) ((extChartAt I α) x)) = (extChartAt I α) x :=
        (toEuclidean (E := E)).symm_apply_apply _
      have h_symm_extChart : (extChartAt I α).symm ((extChartAt I α) x) = x :=
        (extChartAt I α).left_inv hx_extchartsource
      unfold chartPushed
      rw [h_symm_toEucl, h_symm_extChart]
    · rw [chartPullback_apply_of_notMem (I := I) (M := M) α _ hxα]
      have h_subord :=
        CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate (I := I) (M := M)
      have h_tsupp : tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU
          I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆ (chartAt H α).source := h_subord α
      have h_x_notin : x ∉ tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU
          I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := fun h => hxα (h_tsupp h)
      have h_rho_zero :
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M α : M → ℝ) x = 0 :=
        image_eq_zero_of_notMem_tsupport h_x_notin
      rw [h_rho_zero]; ring
  rw [Finset.sum_congr rfl h_eq]
  rw [show (∑ α ∈ CalabiYau.RiemannianVolume.chartAtlasPOUFinset
      (I := I) (M := M),
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M α : M → ℝ) x * u x) =
      (∑ α ∈ CalabiYau.RiemannianVolume.chartAtlasPOUFinset
        (I := I) (M := M),
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M α : M → ℝ) x) * u x
      from by rw [Finset.sum_mul]]
  rw [chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x, one_mul]

def tightenedChartPushed
    [T2Space M] [SigmaCompactSpace M]
    (α : M) (η_M : M → ℝ) (u : M → ℝ) : EuclN → ℝ :=
  fun y =>
    chartCutoffEuclidean (I := I) (M := M) α η_M y *
      chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u y

lemma chartPullback_tightenedChartPushed_eq
    [T2Space M] [SigmaCompactSpace M] (α : M) {η_M : M → ℝ}
    (hη_one_on_tsupport :
      ∀ x ∈ tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ), η_M x = 1)
    (u : M → ℝ) :
    chartPullback I α
        (tightenedChartPushed (I := I) (M := M) α η_M u) =
      chartPullback I α
        (chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u) := by
  classical
  funext x
  by_cases hxα : x ∈ (chartAt H α).source
  · rw [chartPullback_apply_of_mem (I := I) (M := M) α _ hxα]
    rw [chartPullback_apply_of_mem (I := I) (M := M) α _ hxα]
    set y : EuclN := (toEuclidean (E := E)) ((extChartAt I α) x) with hy_def
    change tightenedChartPushed (I := I) (M := M) α η_M u y =
      chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u y
    unfold tightenedChartPushed
    have hx_extsource : x ∈ (extChartAt I α).source := by
      rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)]
      exact hxα
    have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α := by
      rw [hy_def]
      exact ⟨extChartAt I α x, (extChartAt I α).map_source hx_extsource, rfl⟩
    have h_symm_toEucl : (toEuclidean (E := E)).symm y = (extChartAt I α) x := by
      rw [hy_def, (toEuclidean (E := E)).symm_apply_apply]
    have h_symm_extChart : (extChartAt I α).symm
        ((toEuclidean (E := E)).symm y) = x := by
      rw [h_symm_toEucl, (extChartAt I α).left_inv hx_extsource]
    have h_chartPushed_eq : chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u y =
        ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * u x := by
      unfold chartPushed
      rw [h_symm_extChart]
    rw [h_chartPushed_eq]
    by_cases h_rho_zero :
        ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * u x = 0
    · rw [h_rho_zero]; ring
    · have h_rho_ne : ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) x ≠ 0 := by
        intro h0
        apply h_rho_zero
        rw [h0]; ring
      have hx_in_support : x ∈ Function.support
          ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
        simp only [Function.mem_support, ne_eq]; exact h_rho_ne
      have hx_in_tsupp : x ∈ tsupport
          ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) := subset_tsupport _ hx_in_support
      have hy_in_image :
          y ∈ (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) ''
            tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
        refine ⟨x, hx_in_tsupp, ?_⟩
        rw [hy_def]
      have hηE_y : chartCutoffEuclidean (I := I) (M := M) α η_M y = 1 :=
        etaEuclid_eq_one_of_eta_eq_one (I := I) (M := M) α η_M
          hη_one_on_tsupport hy_in_image
      rw [hηE_y]; ring
  · rw [chartPullback_apply_of_notMem (I := I) (M := M) α _ hxα]
    rw [chartPullback_apply_of_notMem (I := I) (M := M) α _ hxα]

lemma tsupport_tightenedChartPushed_subset
    [T2Space M] [SigmaCompactSpace M] (α : M) {η_M : M → ℝ}
    (hη_compact : HasCompactSupport η_M)
    (hη_tsupp_chart : tsupport η_M ⊆ (chartAt H α).source)
    {K_α : Set M} (hη_tsupp_K : tsupport η_M ⊆ K_α)
    (u : M → ℝ) :
    tsupport (tightenedChartPushed (I := I) (M := M) α η_M u) ⊆
      (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_α := by
  classical
  have h_support_in_etaEuclid :
      tsupport (tightenedChartPushed (I := I) (M := M) α η_M u) ⊆
        tsupport (chartCutoffEuclidean (I := I) (M := M) α η_M) := by
    refine closure_mono ?_
    intro y hy
    simp only [Function.mem_support, ne_eq] at hy
    have hηE_ne : chartCutoffEuclidean (I := I) (M := M) α η_M y ≠ 0 := by
      intro h0
      apply hy
      change chartCutoffEuclidean (I := I) (M := M) α η_M y *
        chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u y = 0
      rw [h0]; ring
    exact Function.mem_support.mpr hηE_ne
  have h_etaEuclid_support :
      tsupport (chartCutoffEuclidean (I := I) (M := M) α η_M) ⊆
        (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' tsupport η_M :=
    tsupport_etaEuclid_subset_chartImage (I := I) (M := M) α η_M hη_compact hη_tsupp_chart
  have h_image_mono :
      (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' tsupport η_M ⊆
        (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_α :=
    Set.image_mono hη_tsupp_K
  exact h_support_in_etaEuclid.trans (h_etaEuclid_support.trans h_image_mono)

lemma tightenedChartPushed_eq_chartPushed_on_target
    [T2Space M] [SigmaCompactSpace M] (α : M) {η_M : M → ℝ}
    (hη_one_on_tsupport :
      ∀ x ∈ tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ), η_M x = 1)
    (u : M → ℝ) :
    ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      tightenedChartPushed (I := I) (M := M) α η_M u y =
        chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u y := by
  intro y hy_target
  unfold tightenedChartPushed
  by_cases hf_zero : chartPushed (I := I) (M := M)
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u y = 0
  · rw [hf_zero]; ring
  · have hy_in_image' :
        y ∈ (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) ''
          tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
      by_contra hy_off
      apply hf_zero
      have hy_off' : y ∉ chartImagePOUTsupport (I := I) (M := M) α := by
        intro h_in
        apply hy_off
        unfold chartImagePOUTsupport at h_in
        rcases h_in with ⟨z, ⟨x, hx_support, hxz⟩, hzy⟩
        exact ⟨x, hx_support, by rw [← hzy, ← hxz]⟩
      exact chartPushed_eq_zero_off_chartImagePOUTsupport (I := I) (M := M)
        α u hy_target hy_off'
    have hηE_y : chartCutoffEuclidean (I := I) (M := M) α η_M y = 1 :=
      etaEuclid_eq_one_of_eta_eq_one (I := I) (M := M) α η_M
        hη_one_on_tsupport hy_in_image'
    rw [hηE_y]; ring

private lemma tightenedChartPushed_memWkp
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {u : M → ℝ} (hu : MemWkpChart (I := I) (M := M) 1 p u) (α : M)
    {η_M : M → ℝ}
    (hη_M_smooth : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ η_M)
    (hη_M_compact : HasCompactSupport η_M)
    (hη_M_support_chart : tsupport η_M ⊆ (chartAt H α).source) :
    Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 p
      (tightenedChartPushed (I := I) (M := M) α η_M u)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set ηE : EuclN → ℝ := chartCutoffEuclidean (I := I) (M := M) α η_M with hηE_def
  have hηE_smooth : ContDiff ℝ (⊤ : ℕ∞) ηE :=
    contDiff_etaEuclid (I := I) (M := M) α η_M hη_M_smooth hη_M_compact hη_M_support_chart
  have hηE_compact : HasCompactSupport ηE :=
    hasCompactSupport_etaEuclid (I := I) (M := M) α η_M hη_M_compact hη_M_support_chart
  obtain ⟨C_grad, _hC_grad_pos, hC_grad⟩ :=
    exists_grad_bound_of_compactSupport_smooth hηE_smooth hηE_compact
  obtain ⟨C_norm, _hC_norm_pos, hC_norm⟩ :
      ∃ C : ℝ, 0 < C ∧ ∀ x : EuclN, ‖ηE x‖ ≤ C := by
    set f : EuclN → ℝ := fun x => ‖ηE x‖
    have hf_cont : Continuous f := hηE_smooth.continuous.norm
    have h_zero_off : ∀ x : EuclN, x ∉ tsupport ηE → f x = 0 := by
      intro x hx
      change ‖ηE x‖ = 0
      rw [image_eq_zero_of_notMem_tsupport hx]
      simp
    set K : Set EuclN := tsupport ηE with hK_def
    have hK_compact : IsCompact K := hηE_compact
    have h_bdd : ∃ C : ℝ, ∀ x ∈ K, f x ≤ C := by
      by_cases hKn : K.Nonempty
      · obtain ⟨x₀, _hx₀K, hx₀_max⟩ :=
          hK_compact.exists_isMaxOn hKn hf_cont.continuousOn
        exact ⟨f x₀, fun x hx => hx₀_max hx⟩
      · refine ⟨0, ?_⟩
        intro x hx
        exact (hKn ⟨x, hx⟩).elim
    obtain ⟨C₀, hC₀⟩ := h_bdd
    refine ⟨max C₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
    intro x
    by_cases hx : x ∈ K
    · exact (hC₀ x hx).trans (le_max_left _ _)
    · rw [show ‖ηE x‖ = f x from rfl, h_zero_off x hx]
      exact le_trans (le_refl 0) (le_trans zero_le_one (le_max_right _ _))
  set C : ℝ := max C_norm C_grad with hC_def
  have hC_norm_le : ∀ y : EuclN, ‖ηE y‖ ≤ C := fun y =>
    (hC_norm y).trans (le_max_left _ _)
  have hC_grad_le : ∀ y : EuclN, ‖fderiv ℝ ηE y‖ ≤ C := fun y =>
    (hC_grad y).trans (le_max_right _ _)
  have hC_norm_target : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α, ‖ηE y‖ ≤ C :=
    fun y _ => hC_norm_le y
  have hC_grad_target : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      ‖fderiv ℝ ηE y‖ ≤ C := fun y _ => hC_grad_le y
  exact chartCutoff_smul_chartPushed_memWkp (I := I) (M := M) hp_one hu α
    hηE_smooth hC_norm_target hC_grad_target

private lemma wkpNorm_tightenedChartPushed_sub_eq
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    (α : M) {η_M : M → ℝ}
    (hη_one_on_tsupport :
      ∀ x ∈ tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ), η_M x = 1)
    (u : M → ℝ) (χ : EuclN → ℝ) :
    Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) 1 p
      (fun y => tightenedChartPushed (I := I) (M := M) α η_M u y - χ y)
      (chartTargetEuclid (I := I) (M := M) α) =
    Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) 1 p
      (fun y => chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u y - χ y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_target_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  have h_diff_eq : (fun y => tightenedChartPushed (I := I) (M := M) α η_M u y - χ y)
      =ᵐ[volume.restrict (chartTargetEuclid (I := I) (M := M) α)]
      (fun y => chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u y - χ y) := by
    refine (ae_restrict_iff' h_target_meas).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy
    have h_eq := tightenedChartPushed_eq_chartPushed_on_target (I := I) (M := M)
      α hη_one_on_tsupport u y hy
    simp [h_eq]
  exact Sobolev.Euclidean.wkpNorm_congr_ae
    (d := Module.finrank ℝ E) hp_one
    (chartTargetEuclid_isOpen (I := I) (M := M) α) h_diff_eq

private theorem MemWkp_of_cross_chart_pushforward
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (γ α : M) {K_α : Set M} (hK_compact : IsCompact K_α)
    (hK_α_in_α : K_α ⊆ (chartAt H α).source)
    {v : EuclN → ℝ} {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    (hv : Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 1 p v
        (chartTargetEuclid (I := I) (M := M) α))
    (hv_support : tsupport v ⊆
      (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_α) :
    Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 1 p
      (chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) γ
        (chartPullback I α v))
      (chartTargetEuclid (I := I) (M := M) γ) := by
  classical
  set ρ_γ_M : M → ℝ :=
    ((CalabiYau.RiemannianVolume.chartAtlasPOU I M γ
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hρ_γ_M_def
  have hρ_γ_M_smooth : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ ρ_γ_M :=
    (CalabiYau.RiemannianVolume.chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯).contMDiff
  have hρ_γ_M_support_in_chart : tsupport ρ_γ_M ⊆ (chartAt H γ).source :=
    CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M γ
  have hρ_γ_M_compact : HasCompactSupport ρ_γ_M :=
    (isClosed_tsupport _).isCompact
  set K_M : Set M := K_α ∩ tsupport ρ_γ_M with hKM_def
  have hKM_compact : IsCompact K_M :=
    hK_compact.inter_right (isClosed_tsupport _)
  have hKM_in_α : K_M ⊆ (chartAt H α).source := fun x hx => hK_α_in_α hx.1
  have hKM_in_γ : K_M ⊆ (chartAt H γ).source := fun x hx =>
    hρ_γ_M_support_in_chart hx.2
  obtain ⟨Ω_γα, Ω_αγ, hΩγα_open, hΩαγ_open, hΩγα_subset_target, hΩαγ_subset_target,
    hΩγα_subset_overlap, hΩαγ_subset_overlap, hKM_image_in_Ωγα, Φ,
    hΦ_eq_on_Ωγα, hΦ_inv_eq_on_Ωαγ⟩ :=
    chartTransition_smoothDiffeoBoundedAtOrder_strict (I := I) (M := M) γ α
      hKM_compact hKM_in_γ hKM_in_α 1
  set K_E_γ : Set EuclN :=
    (fun x : M => (toEuclidean (E := E)) (extChartAt I γ x)) '' K_M with hKEγ_def
  set K_E_α : Set EuclN :=
    (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_M with hKEα_def
  have hKEγ_compact : IsCompact K_E_γ :=
    chartImage_isCompact_of_compact_in_source (I := I) (M := M) γ hKM_compact hKM_in_γ
  have hKEα_compact : IsCompact K_E_α :=
    chartImage_isCompact_of_compact_in_source (I := I) (M := M) α hKM_compact hKM_in_α
  have hKEγ_subset_target : K_E_γ ⊆ chartTargetEuclid (I := I) (M := M) γ := by
    intro y hy
    rcases hy with ⟨x, hxK, hxy⟩
    have hx_ext : x ∈ (extChartAt I γ).source := by rw [extChartAt_source]; exact hKM_in_γ hxK
    have h_target : extChartAt I γ x ∈ (extChartAt I γ).target :=
      (extChartAt I γ).map_source hx_ext
    rw [← hxy]; exact ⟨extChartAt I γ x, h_target, rfl⟩
  have hKEα_subset_target : K_E_α ⊆ chartTargetEuclid (I := I) (M := M) α := by
    intro y hy
    rcases hy with ⟨x, hxK, hxy⟩
    have hx_ext : x ∈ (extChartAt I α).source := by rw [extChartAt_source]; exact hKM_in_α hxK
    have h_target : extChartAt I α x ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source hx_ext
    rw [← hxy]; exact ⟨extChartAt I α x, h_target, rfl⟩
  set Uγ : Set EuclN := Ω_γα ∩ chartTargetEuclid (I := I) (M := M) γ with hUγ_def
  have hUγ_open : IsOpen Uγ :=
    hΩγα_open.inter (chartTargetEuclid_isOpen (I := I) (M := M) γ)
  have hKEγ_in_Uγ : K_E_γ ⊆ Uγ :=
    Set.subset_inter hKM_image_in_Ωγα hKEγ_subset_target
  obtain ⟨δ_γ, η_γ_local, hδ_γ_pos, _hδγ_subset, hη_γ_local_smooth, hη_γ_local_compact,
    hη_γ_local_range, hη_γ_local_one, hη_γ_local_support⟩ :=
    Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      (d := Module.finrank ℝ E) hKEγ_compact hUγ_open hKEγ_in_Uγ
  have hη_γ_local_support_Ωγα : tsupport η_γ_local ⊆ Ω_γα :=
    fun y hy => (hη_γ_local_support hy).1
  have hη_γ_local_support_target : tsupport η_γ_local ⊆ chartTargetEuclid (I := I) (M := M) γ :=
    fun y hy => (hη_γ_local_support hy).2
  have hη_γ_local_norm_one : ∀ x : EuclN, ‖η_γ_local x‖ ≤ 1 :=
    norm_le_one_of_range_Icc hη_γ_local_range
  obtain ⟨C_η_γ_grad, _hC_η_γ_pos, hC_η_γ_grad⟩ :=
    exists_grad_bound_of_compactSupport_smooth hη_γ_local_smooth hη_γ_local_compact
  have hΦ_eq_KM : ∀ x ∈ K_M, Φ.toFun ((toEuclidean (E := E)) (extChartAt I γ x)) =
      (toEuclidean (E := E)) (extChartAt I α x) := by
    intro x hxK
    set y := (toEuclidean (E := E)) (extChartAt I γ x) with hy_def
    have hy_in_KEγ : y ∈ K_E_γ := ⟨x, hxK, rfl⟩
    have hy_in_Ωγα : y ∈ Ω_γα := hKM_image_in_Ωγα hy_in_KEγ
    have h1 : Φ.toFun y = chartTransitionEuclid (I := I) (M := M) γ α y :=
      hΦ_eq_on_Ωγα y hy_in_Ωγα
    rw [h1]
    have hx_chart : x ∈ (chartAt H γ).source := hKM_in_γ hxK
    rw [hy_def]
    exact chartTransitionEuclid_eq_chartα_image (I := I) (M := M) γ α hx_chart
  have hKEα_eq_Φ_image : K_E_α = Φ.toFun '' K_E_γ := by
    ext z
    refine ⟨?_, ?_⟩
    · rintro ⟨x, hxK, hxz⟩
      refine ⟨(toEuclidean (E := E)) (extChartAt I γ x), ⟨x, hxK, rfl⟩, ?_⟩
      rw [hΦ_eq_KM x hxK]
      simpa using hxz
    · rintro ⟨y, ⟨x, hxK, hxy⟩, hyz⟩
      refine ⟨x, hxK, ?_⟩
      rw [← hyz, ← hxy, hΦ_eq_KM x hxK]
  have hKEα_in_Ωαγ : K_E_α ⊆ Ω_αγ := by
    rw [hKEα_eq_Φ_image]
    intro z hz
    rcases hz with ⟨y, hy, hyz⟩
    have hy_in_Ωγα : y ∈ Ω_γα := hKM_image_in_Ωγα hy
    rw [← hyz]; exact Φ.bijOn.mapsTo hy_in_Ωγα
  set Uα : Set EuclN := Ω_αγ ∩ chartTargetEuclid (I := I) (M := M) α with hUα_def
  have hUα_open : IsOpen Uα :=
    hΩαγ_open.inter (chartTargetEuclid_isOpen (I := I) (M := M) α)
  have hKEα_in_Uα : K_E_α ⊆ Uα :=
    Set.subset_inter hKEα_in_Ωαγ hKEα_subset_target
  obtain ⟨_δα, η_α_local, _hδα_pos, _hδα_subset, hη_α_local_smooth, hη_α_local_compact,
    hη_α_local_range, hη_α_local_one, hη_α_local_support⟩ :=
    Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      (d := Module.finrank ℝ E) hKEα_compact hUα_open hKEα_in_Uα
  have hη_α_local_support_Ωαγ : tsupport η_α_local ⊆ Ω_αγ :=
    fun y hy => (hη_α_local_support hy).1
  have hη_α_local_norm_one : ∀ x : EuclN, ‖η_α_local x‖ ≤ 1 :=
    norm_le_one_of_range_Icc hη_α_local_range
  obtain ⟨C_η_α_grad, _hC_η_α_pos, hC_η_α_grad⟩ :=
    exists_grad_bound_of_compactSupport_smooth hη_α_local_smooth hη_α_local_compact
  set ργE : EuclN → ℝ := chartCutoffEuclidean (I := I) (M := M) γ ρ_γ_M with hργE_def
  have hργE_smooth : ContDiff ℝ (⊤ : ℕ∞) ργE :=
    contDiff_etaEuclid (I := I) (M := M) γ ρ_γ_M hρ_γ_M_smooth hρ_γ_M_compact hρ_γ_M_support_in_chart
  have hργE_norm_one : ∀ y : EuclN, ‖ργE y‖ ≤ 1 := by
    intro y
    have h_range : Set.range (chartCutoffEuclidean (I := I) (M := M) γ ρ_γ_M) ⊆ Set.Icc (0 : ℝ) 1 :=
      etaEuclid_range_Icc (I := I) (M := M) γ ρ_γ_M
        (by
          rintro v ⟨x, hx⟩
          rw [← hx]
          refine ⟨(CalabiYau.RiemannianVolume.chartAtlasPOU I M).nonneg γ x,
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M).le_one γ x⟩)
    exact norm_le_one_of_range_Icc h_range y
  obtain ⟨C_ργE_grad, _hC_ργE_pos, hC_ργE_grad⟩ :=
    exists_grad_bound_etaEuclid (I := I) (M := M) γ ρ_γ_M hρ_γ_M_smooth hρ_γ_M_compact
      hρ_γ_M_support_in_chart
  set η_combined : EuclN → ℝ := fun y => η_γ_local y * ργE y with hη_combined_def
  have hη_combined_smooth : ContDiff ℝ (⊤ : ℕ∞) η_combined :=
    hη_γ_local_smooth.mul hργE_smooth
  have hη_combined_compact : HasCompactSupport η_combined := by
    refine hη_γ_local_compact.of_isClosed_subset (isClosed_tsupport _) ?_
    refine closure_mono ?_
    intro y hy
    simp only [hη_combined_def, Function.mem_support, ne_eq] at hy
    have hη_ne : η_γ_local y ≠ 0 := by
      intro h0; apply hy; rw [h0]; ring
    exact Function.mem_support.mpr hη_ne
  have hη_combined_support_Ωγα : tsupport η_combined ⊆ Ω_γα := by
    refine Set.Subset.trans ?_ hη_γ_local_support_Ωγα
    refine closure_mono ?_
    intro y hy
    simp only [hη_combined_def, Function.mem_support, ne_eq] at hy
    have hη_ne : η_γ_local y ≠ 0 := by
      intro h0; apply hy; rw [h0]; ring
    exact Function.mem_support.mpr hη_ne
  set C_η_comb : ℝ := max 1 (C_η_γ_grad + C_ργE_grad) with hC_η_comb_def
  have hη_combined_norm_one : ∀ y : EuclN, ‖η_combined y‖ ≤ 1 := by
    intro y
    rw [hη_combined_def, norm_mul]
    refine (mul_le_mul (hη_γ_local_norm_one y) (hργE_norm_one y) (norm_nonneg (ργE y))
      (by norm_num : (0 : ℝ) ≤ 1)).trans ?_
    norm_num
  have hη_combined_grad_bound : ∀ y : EuclN, ‖fderiv ℝ η_combined y‖ ≤ C_η_γ_grad + C_ργE_grad := by
    intro y
    have h_diff_η : DifferentiableAt ℝ η_γ_local y :=
      (hη_γ_local_smooth.differentiable (by simp)).differentiableAt
    have h_diff_ργE : DifferentiableAt ℝ ργE y :=
      (hργE_smooth.differentiable (by simp)).differentiableAt
    rw [hη_combined_def, fderiv_fun_mul h_diff_η h_diff_ργE]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖η_γ_local y • fderiv ℝ ργE y‖ ≤ C_ργE_grad := by
      rw [norm_smul]
      refine (mul_le_mul (hη_γ_local_norm_one y) (hC_ργE_grad y)
        (norm_nonneg (fderiv ℝ ργE y)) (by norm_num : (0 : ℝ) ≤ 1)).trans ?_
      simp
    have h2 : ‖ργE y • fderiv ℝ η_γ_local y‖ ≤ C_η_γ_grad := by
      rw [norm_smul]
      refine (mul_le_mul (hργE_norm_one y) (hC_η_γ_grad y)
        (norm_nonneg (fderiv ℝ η_γ_local y)) (by norm_num : (0 : ℝ) ≤ 1)).trans ?_
      simp
    linarith
  have hη_combined_bound : ∀ j ≤ 1, ∀ x ∈ Ω_γα, ‖iteratedFDeriv ℝ j η_combined x‖ ≤ C_η_comb := by
    intro j hj x _
    interval_cases j
    · rw [norm_iteratedFDeriv_zero]
      exact (hη_combined_norm_one x).trans (le_max_left _ _)
    · rw [norm_iteratedFDeriv_one]
      exact (hη_combined_grad_bound x).trans (le_max_right _ _)
  set C_η_α : ℝ := max 1 C_η_α_grad with hC_η_α_def
  have hη_α_local_bound_global : ∀ j ≤ 1, ∀ x : EuclN, ‖iteratedFDeriv ℝ j η_α_local x‖ ≤ C_η_α := by
    intro j hj x
    interval_cases j
    · rw [norm_iteratedFDeriv_zero]
      exact (hη_α_local_norm_one x).trans (le_max_left _ _)
    · rw [norm_iteratedFDeriv_one]
      exact (hC_η_α_grad x).trans (le_max_right _ _)
  have hη_α_local_bound : ∀ j ≤ 1, ∀ x ∈ chartTargetEuclid (I := I) (M := M) α,
      ‖iteratedFDeriv ℝ j η_α_local x‖ ≤ C_η_α :=
    fun j hj x _ => hη_α_local_bound_global j hj x
  set χ_local : EuclN → ℝ := fun y => η_α_local y * v y with hχ_local_def
  have hχ_local_mem_target : Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 p χ_local (chartTargetEuclid (I := I) (M := M) α) := by
    have : (fun y => η_α_local y * v y) = χ_local := rfl
    rw [← this]
    exact Sobolev.Euclidean.MemWkp.smul_smooth_bounded
      (d := Module.finrank ℝ E) 1 hp_one (chartTargetEuclid_isOpen (I := I) (M := M) α)
      hη_α_local_smooth hη_α_local_bound hv
  have hχ_local_support : tsupport χ_local ⊆ Ω_αγ := by
    refine Set.Subset.trans ?_ hη_α_local_support_Ωαγ
    refine closure_mono ?_
    intro y hy
    simp only [hχ_local_def, Function.mem_support, ne_eq] at hy
    have hη_ne : η_α_local y ≠ 0 := by
      intro h0; apply hy; rw [h0]; ring
    exact Function.mem_support.mpr hη_ne
  have hχ_local_compact : HasCompactSupport χ_local := by
    have h_sub_tsupp : tsupport χ_local ⊆ tsupport η_α_local := by
      refine closure_mono ?_
      intro y hy
      have hy' : χ_local y ≠ 0 := by
        simpa [Function.mem_support] using hy
      have hη_ne : η_α_local y ≠ 0 := by
        intro h0; apply hy'; simp [hχ_local_def, h0]
      simpa [Function.mem_support]
    exact hη_α_local_compact.of_isClosed_subset (isClosed_tsupport _) h_sub_tsupp
  obtain ⟨hχ_local_mem_Ωαγ, _⟩ :=
    Sobolev.Euclidean.wkpNorm_eq_of_tsupport_subset_one
      (d := Module.finrank ℝ E) hp_one (chartTargetEuclid_isOpen (I := I) (M := M) α)
      hΩαγ_open hΩαγ_subset_target hχ_local_mem_target hχ_local_support
  have hχ_local_comp_mem : Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 p (fun y => χ_local (Φ.toFun y)) Ω_γα :=
    Sobolev.Euclidean.MemWkp.comp_smoothDiffeoBoundedAtOrder
      (d := Module.finrank ℝ E) 1 (le_refl 1) hp_one hp_top hΩγα_open hΩαγ_open Φ
      hχ_local_mem_Ωαγ hχ_local_compact hχ_local_support
  set ψ : EuclN → ℝ := fun y => η_combined y * χ_local (Φ.toFun y) with hψ_def
  have hψ_mem_Ωγα : Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 p ψ Ω_γα :=
    Sobolev.Euclidean.MemWkp.smul_smooth_bounded
      (d := Module.finrank ℝ E) 1 hp_one hΩγα_open hη_combined_smooth hη_combined_bound
        hχ_local_comp_mem
  have hψ_support_Ωγα : tsupport ψ ⊆ Ω_γα := by
    refine Set.Subset.trans ?_ hη_combined_support_Ωγα
    refine closure_mono ?_
    intro y hy
    simp only [hψ_def, Function.mem_support, ne_eq] at hy
    have hη_ne : η_combined y ≠ 0 := by
      intro h0; apply hy; rw [h0]; ring
    exact Function.mem_support.mpr hη_ne
  have hψ_compact : HasCompactSupport ψ :=
    hη_combined_compact.of_isClosed_subset (isClosed_tsupport _) (by
      refine closure_mono ?_
      intro y hy
      simp only [hψ_def, Function.mem_support, ne_eq] at hy
      have hη_ne : η_combined y ≠ 0 := by
        intro h0; apply hy; rw [h0]; ring
      exact Function.mem_support.mpr hη_ne)
  have hψ_mem_target : Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 p ψ (chartTargetEuclid (I := I) (M := M) γ) :=
    Sobolev.Euclidean.MemWkp.extend_zero
      (d := Module.finrank ℝ E) hp_one hΩγα_open
      (chartTargetEuclid_isOpen (I := I) (M := M) γ) hΩγα_subset_target
      hψ_mem_Ωγα hψ_support_Ωγα hψ_compact
  have h_ae_eq : (chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) γ
        (chartPullback I α v)) =ᵐ[volume.restrict
          (chartTargetEuclid (I := I) (M := M) γ)] ψ := by
    have h_target_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) γ) :=
      (chartTargetEuclid_isOpen (I := I) (M := M) γ).measurableSet
    refine (ae_restrict_iff' h_target_meas).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy_target
    set z : M := (extChartAt I γ).symm ((toEuclidean (E := E)).symm y) with hz_def
    have hsymm_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I γ).target := by
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy_target; exact hy_target
    have hz_source : z ∈ (extChartAt I γ).source :=
      (extChartAt I γ).map_target hsymm_target
    have hz_chartγ : z ∈ (chartAt H γ).source := by
      rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)] at hz_source; exact hz_source
    have h_pushed_eq : chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) γ
        (chartPullback I α v) y = ρ_γ_M z * chartPullback I α v z := rfl
    rw [h_pushed_eq, hψ_def, hχ_local_def]
    have hργE_y : ργE y = ρ_γ_M z := by
      rw [hργE_def]
      exact etaEuclid_apply_of_mem (I := I) (M := M) γ ρ_γ_M hy_target
    simp only [hη_combined_def, hργE_y]
    by_cases hρ_zero : ρ_γ_M z = 0
    · rw [hρ_zero]; simp
    · have hz_in_tsupp_ρ : z ∈ tsupport ρ_γ_M :=
        subset_tsupport _ (by simp [Function.mem_support, hρ_zero])
      by_cases hy_in_support_η_γ : y ∈ tsupport η_γ_local
      · have hy_in_Ωγα : y ∈ Ω_γα := hη_γ_local_support_Ωγα hy_in_support_η_γ
        have hz_chartα : z ∈ (chartAt H α).source := by
          have h_overlap_subset : Ω_γα ⊆ chartOverlapEuclid (I := I) (M := M) γ α :=
            hΩγα_subset_overlap
          have hy_overlap : y ∈ chartOverlapEuclid (I := I) (M := M) γ α :=
            h_overlap_subset hy_in_Ωγα
          unfold chartOverlapEuclid at hy_overlap
          rcases hy_overlap with ⟨a, ⟨w, ⟨hw_γ, hw_α⟩, hwa⟩, hay⟩
          have hy_eq : (toEuclidean (E := E)) (extChartAt I γ w) = y := by
            rw [← hay, ← hwa]
          have hz_eq_w : z = w := by
            have h_w_chart_γ : w ∈ (extChartAt I γ).source := by
              rw [extChartAt_source]; exact hw_γ
            have hy_symm : (toEuclidean (E := E)).symm y = extChartAt I γ w := by
              rw [← hy_eq, (toEuclidean (E := E)).symm_apply_apply]
            have hz_val : z = (extChartAt I γ).symm (extChartAt I γ w) := by
              rw [hz_def, hy_symm]
            rw [hz_val, (extChartAt I γ).left_inv h_w_chart_γ]
          rw [hz_eq_w]; exact hw_α
        have hΦy_eq : Φ.toFun y = chartTransitionEuclid (I := I) (M := M) γ α y :=
          hΦ_eq_on_Ωγα y hy_in_Ωγα
        have h_ext_γ_z : extChartAt I γ z = (toEuclidean (E := E)).symm y := by
          rw [hz_def]
          exact (extChartAt I γ).right_inv hsymm_target
        have hy_eq_w : y = (toEuclidean (E := E)) (extChartAt I γ z) := by
          calc
            y = (toEuclidean (E := E)) ((toEuclidean (E := E)).symm y) := by simp
            _ = (toEuclidean (E := E)) (extChartAt I γ z) := by rw [h_ext_γ_z]
        have hΦy_chartα : Φ.toFun y = (toEuclidean (E := E)) (extChartAt I α z) := by
          rw [hΦy_eq, hy_eq_w]
          exact chartTransitionEuclid_eq_chartα_image (I := I) (M := M) γ α hz_chartγ
        rw [hΦy_chartα]
        rw [chartPullback_apply_of_mem (I := I) (M := M) α v hz_chartα]
        have h_nonzero : ρ_γ_M z ≠ 0 := hρ_zero
        by_cases hv_z : v ((toEuclidean (E := E)) (extChartAt I α z)) = 0
        · rw [hv_z, mul_zero, mul_zero, mul_zero]
        · have h_in_tsupp_v : (toEuclidean (E := E)) (extChartAt I α z) ∈ tsupport v :=
            subset_tsupport _ (by simpa using hv_z)
          have h_in_image_K_α : (toEuclidean (E := E)) (extChartAt I α z) ∈
              (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_α :=
            hv_support h_in_tsupp_v
          rcases h_in_image_K_α with ⟨x', hx'_K_α, hx'_eq⟩
          have hx'_chart : x' ∈ (chartAt H α).source := hK_α_in_α hx'_K_α
          have h_eq_chart : extChartAt I α x' = extChartAt I α z := by
            have h_eu : (toEuclidean (E := E)) (extChartAt I α x') =
                (toEuclidean (E := E)) (extChartAt I α z) := hx'_eq
            exact (toEuclidean (E := E)).injective h_eu
          have hz_in_α_ext : z ∈ (extChartAt I α).source := by
            rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
              (I := I) (M := M)]; exact hz_chartα
          have hx'_α_ext : x' ∈ (extChartAt I α).source := by
            rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
              (I := I) (M := M)]; exact hx'_chart
          have h_inj := (extChartAt I α).injOn hx'_α_ext hz_in_α_ext h_eq_chart
          have hz_in_K_α : z ∈ K_α := by rw [← h_inj]; exact hx'_K_α
          have hz_in_KM : z ∈ K_M := ⟨hz_in_K_α, hz_in_tsupp_ρ⟩
          have hy_in_KEγ : y ∈ K_E_γ := by
            refine ⟨z, hz_in_KM, ?_⟩
            change (toEuclidean (E := E)) (extChartAt I γ z) = y
            have h_z_chart : extChartAt I γ z = (toEuclidean (E := E)).symm y :=
              (extChartAt I γ).right_inv hsymm_target
            rw [h_z_chart]; exact (toEuclidean (E := E)).apply_symm_apply y
          have hη_γ_local_y_one : η_γ_local y = 1 :=
            hη_γ_local_one y (Metric.self_subset_cthickening K_E_γ hy_in_KEγ)
          have h_chartα_z_in_K_E_α :
              (toEuclidean (E := E)) (extChartAt I α z) ∈ K_E_α := ⟨z, hz_in_KM, rfl⟩
          have hη_α_local_eq_one : η_α_local ((toEuclidean (E := E)) (extChartAt I α z)) = 1 :=
            hη_α_local_one ((toEuclidean (E := E)) (extChartAt I α z))
              (Metric.self_subset_cthickening K_E_α h_chartα_z_in_K_E_α)
          rw [hη_γ_local_y_one, hη_α_local_eq_one]
          ring
      · have hη_γ_local_y_zero : η_γ_local y = 0 :=
          image_eq_zero_of_notMem_tsupport hy_in_support_η_γ
        have hz_not_Kα : z ∉ K_α := by
          intro hz_Kα
          apply hy_in_support_η_γ
          have hz_in_KM : z ∈ K_M := ⟨hz_Kα, hz_in_tsupp_ρ⟩
          have hy_in_KEγ : y ∈ K_E_γ := ⟨z, hz_in_KM, by
            have h_ext_γ_z : extChartAt I γ z = (toEuclidean (E := E)).symm y := by
              rw [hz_def]
              exact (extChartAt I γ).right_inv hsymm_target
            calc
              (toEuclidean (E := E)) (extChartAt I γ z)
                  = (toEuclidean (E := E)) ((toEuclidean (E := E)).symm y) := by rw [h_ext_γ_z]
              _ = y := by simp⟩
          have h_one : η_γ_local y = 1 :=
            hη_γ_local_one y (Metric.self_subset_cthickening K_E_γ hy_in_KEγ)
          have h_ne_zero : η_γ_local y ≠ 0 := by linarith
          have hy_support : y ∈ support η_γ_local := by
            simpa [Function.mem_support] using h_ne_zero
          exact subset_tsupport _ hy_support
        have h_cp_zero : chartPullback I α v z = 0 := by
          by_cases hz_α_source : z ∈ (chartAt H α).source
          · rw [chartPullback_apply_of_mem (I := I) (M := M) α v hz_α_source]
            have h_outside : (toEuclidean (E := E)) (extChartAt I α z) ∉ tsupport v := by
              intro h
              have h_image : (toEuclidean (E := E)) (extChartAt I α z) ∈
                  (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_α :=
                hv_support h
              rcases h_image with ⟨x, hx_Kα, hx_eq⟩
              have h_toEucl_inj : Function.Injective (toEuclidean (E := E)) :=
                (toEuclidean (E := E)).injective
              have hx_source : x ∈ (extChartAt I α).source := by
                rw [extChartAt_source (I := I)]
                exact hK_α_in_α hx_Kα
              have hz_ext_source : z ∈ (extChartAt I α).source := by
                rw [extChartAt_source (I := I)]
                exact hz_α_source
              have h_ext_eq : extChartAt I α x = extChartAt I α z :=
                h_toEucl_inj hx_eq
              have h_x_eq_z : x = z :=
                (extChartAt I α).injOn hx_source hz_ext_source h_ext_eq
              rw [h_x_eq_z] at hx_Kα
              exact hz_not_Kα hx_Kα
            exact image_eq_zero_of_notMem_tsupport h_outside
          · exact chartPullback_apply_of_notMem (I := I) (M := M) α v hz_α_source
        simp [hη_γ_local_y_zero, h_cp_zero]
  exact (Sobolev.Euclidean.MemWkp_congr_ae
    (d := Module.finrank ℝ E) hp_one (chartTargetEuclid_isOpen (I := I) (M := M) γ) h_ae_eq).mpr
      hψ_mem_target

theorem contMDiff_dense_in_WkpChart
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {u : M → ℝ} (hu : MemWkpChart (I := I) (M := M) 1 p u)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ v ∧
      wkpNormChart (I := I) (M := M) 1 p (fun x => u x - v x) ≤
        ENNReal.ofReal ε := by
  classical
  set S : Finset M :=
    CalabiYau.RiemannianVolume.chartAtlasPOUFinset (I := I) (M := M)
    with hS_def
  have h_per_chart : ∀ α : S,
      ∃ K_α : Set M, IsCompact K_α ∧ K_α ⊆ (chartAt H (α : M)).source ∧
        tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M
          (α : M) : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆ interior K_α ∧
        ∃ η_M : M → ℝ, ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ η_M ∧
          Set.range η_M ⊆ Set.Icc (0 : ℝ) 1 ∧
          (∀ x ∈ tsupport
            ((CalabiYau.RiemannianVolume.chartAtlasPOU I M (α : M)
              : C^∞⟮I, M; ℝ⟯) : M → ℝ), η_M x = 1) ∧
          tsupport η_M ⊆ K_α := by
    intro α
    obtain ⟨K_α, hK_compact, hK_chart, h_tsupp_in_int_K⟩ :=
      exists_compact_neighborhood_of_tsupport_pou (I := I) (M := M) (α : M)
    obtain ⟨η_M, hη_smooth, hη_range, _hη_support_eq, hη_one_M, hη_tsupp_K⟩ :=
      exists_manifold_cutoff_one_on_tsupport_pou (I := I) (M := M) (α : M)
        hK_compact h_tsupp_in_int_K
    exact ⟨K_α, hK_compact, hK_chart, h_tsupp_in_int_K,
      η_M, hη_smooth, hη_range, hη_one_M, hη_tsupp_K⟩
  let K_choose : S → Set M := fun α => (h_per_chart α).choose
  let K_α : S → Set M := K_choose
  have hK_compact : ∀ α : S, IsCompact (K_α α) := fun α =>
    (h_per_chart α).choose_spec.1
  have hK_chart : ∀ α : S, K_α α ⊆ (chartAt H (α : M)).source := fun α =>
    (h_per_chart α).choose_spec.2.1
  have hK_tsupp_in_int : ∀ α : S, tsupport
      ((CalabiYau.RiemannianVolume.chartAtlasPOU I M (α : M)
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆ interior (K_α α) := fun α =>
    (h_per_chart α).choose_spec.2.2.1
  let η_choose : S → (M → ℝ) := fun α => (h_per_chart α).choose_spec.2.2.2.choose
  let η_M : S → (M → ℝ) := η_choose
  have hη_smooth : ∀ α : S, ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ (η_M α) :=
    fun α => (h_per_chart α).choose_spec.2.2.2.choose_spec.1
  have hη_one_on_tsupport : ∀ α : S, ∀ x ∈ tsupport
      ((CalabiYau.RiemannianVolume.chartAtlasPOU I M (α : M)
        : C^∞⟮I, M; ℝ⟯) : M → ℝ), η_M α x = 1 := fun α =>
    (h_per_chart α).choose_spec.2.2.2.choose_spec.2.2.1
  have hη_tsupp_K : ∀ α : S, tsupport (η_M α) ⊆ K_α α := fun α =>
    (h_per_chart α).choose_spec.2.2.2.choose_spec.2.2.2
  have hη_M_support_chart : ∀ α : S, tsupport (η_M α) ⊆ (chartAt H (α : M)).source :=
    fun α => (hη_tsupp_K α).trans (hK_chart α)
  have hη_M_compact : ∀ α : S, HasCompactSupport (η_M α) := fun α =>
    (hK_compact α).of_isClosed_subset (isClosed_tsupport _) (hη_tsupp_K α)
  have h_per_pair : ∀ γ α : S, ∃ K : ℝ, 0 < K ∧
      ∀ {v : EuclN → ℝ},
        Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) 1 p v
            (chartTargetEuclid (I := I) (M := M) (α : M)) →
        tsupport v ⊆
          (fun x : M => (toEuclidean (E := E)) (extChartAt I (α : M) x)) '' K_α α →
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 p
          (chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) (γ : M)
            (chartPullback I (α : M) v))
          (chartTargetEuclid (I := I) (M := M) (γ : M)) ≤
          ENNReal.ofReal K *
            Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := Module.finrank ℝ E) 1 p v
              (chartTargetEuclid (I := I) (M := M) (α : M)) := fun γ α =>
    cross_chart_bound_strict_strong_memWkp (I := I) (M := M) hp_one hp_top
      (γ : M) (α : M) (hK_compact α) (hK_chart α)
  let K_pair : S → S → ℝ := fun γ α => (h_per_pair γ α).choose
  have hK_pair_pos : ∀ γ α : S, 0 < K_pair γ α := fun γ α =>
    (h_per_pair γ α).choose_spec.1
  have hK_pair_bound : ∀ γ α : S, ∀ {v : EuclN → ℝ},
      Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 1 p v
          (chartTargetEuclid (I := I) (M := M) (α : M)) →
      tsupport v ⊆
        (fun x : M => (toEuclidean (E := E)) (extChartAt I (α : M) x)) '' K_α α →
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 p
        (chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) (γ : M)
          (chartPullback I (α : M) v))
        (chartTargetEuclid (I := I) (M := M) (γ : M)) ≤
        ENNReal.ofReal (K_pair γ α) *
          Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 1 p v
            (chartTargetEuclid (I := I) (M := M) (α : M)) := fun γ α =>
    (h_per_pair γ α).choose_spec.2
  set K_total : ℝ := (∑ γ : S, ∑ α : S, K_pair γ α) + 1 with hK_total_def
  have hK_total_pos : 0 < K_total := by
    rw [hK_total_def]
    have h_sum_nn : 0 ≤ ∑ γ : S, ∑ α : S, K_pair γ α := by
      refine Finset.sum_nonneg ?_
      intro γ _
      refine Finset.sum_nonneg ?_
      intro α _
      exact (hK_pair_pos γ α).le
    linarith
  set ε_per : ℝ := ε / K_total with hε_per_def
  have hε_per_pos : 0 < ε_per := div_pos hε hK_total_pos
  have hK_total_eps_le : K_total * ε_per ≤ ε := by
    rw [hε_per_def, mul_div_assoc']
    rw [div_le_iff₀ hK_total_pos]
    linarith [mul_comm K_total ε]
  have h_chi : ∀ α : S, ∃ χ : EuclN → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆
        (fun x : M => (toEuclidean (E := E)) (extChartAt I (α : M) x)) '' K_α α ∧
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 p
        (fun y => chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) (α : M) u y - χ y)
        (chartTargetEuclid (I := I) (M := M) (α : M)) ≤
        ENNReal.ofReal ε_per := by
    intro α
    obtain ⟨K_α', hK_compact', hK_chart', h_tsupp_in_int_K', hχ⟩ :=
      exists_strict_strong_support_approx (I := I) (M := M) hp_one hp_top (α : M)
    set ηE : EuclN → ℝ := chartCutoffEuclidean (I := I) (M := M) (α : M) (η_M α) with hηE_def
    have hηE_smooth : ContDiff ℝ (⊤ : ℕ∞) ηE :=
      contDiff_etaEuclid (I := I) (M := M) (α : M) (η_M α) (hη_smooth α)
        (hη_M_compact α) (hη_M_support_chart α)
    have hηE_compact : HasCompactSupport ηE :=
      hasCompactSupport_etaEuclid (I := I) (M := M) (α : M) (η_M α)
        (hη_M_compact α) (hη_M_support_chart α)
    have hηE_range : Set.range ηE ⊆ Set.Icc (0 : ℝ) 1 := by
      have hη_range_M : Set.range (η_M α) ⊆ Set.Icc (0 : ℝ) 1 :=
        (h_per_chart α).choose_spec.2.2.2.choose_spec.2.1
      exact etaEuclid_range_Icc (I := I) (M := M) (α : M) (η_M α) hη_range_M
    have hηE_norm_one : ∀ y : EuclN, ‖ηE y‖ ≤ 1 :=
      norm_le_one_of_range_Icc hηE_range
    have hηE_tsupp_in_image_K : tsupport ηE ⊆
        (fun x : M => (toEuclidean (E := E)) (extChartAt I (α : M) x)) '' K_α α := by
      refine subset_trans
        (tsupport_etaEuclid_subset_chartImage (I := I) (M := M) (α : M) (η_M α)
          (hη_M_compact α) (hη_M_support_chart α)) ?_
      exact Set.image_mono (hη_tsupp_K α)
    have hηE_one_on_pou_image :
        ∀ y ∈ (fun x : M => (toEuclidean (E := E)) (extChartAt I (α : M) x)) ''
          tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M (α : M)
            : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ηE y = 1 := fun y hy =>
      etaEuclid_eq_one_of_eta_eq_one (I := I) (M := M) (α : M) (η_M α)
        (hη_one_on_tsupport α) hy
    obtain ⟨Cη, _hCη_pos, hCη_grad⟩ :=
      exists_grad_bound_etaEuclid (I := I) (M := M) (α : M) (η_M α)
        (hη_smooth α) (hη_M_compact α) (hη_M_support_chart α)
    set C : ℝ := max Cη 1 with hC_def
    have hC_one : ∀ y : EuclN, ‖ηE y‖ ≤ C :=
      fun y => (hηE_norm_one y).trans (le_max_right _ _)
    have hC_grad : ∀ y : EuclN, ‖fderiv ℝ ηE y‖ ≤ C :=
      fun y => (hCη_grad y).trans (le_max_left _ _)
    set Ωα : Set EuclN := chartTargetEuclid (I := I) (M := M) (α : M) with hΩα_def
    have hΩα_open : IsOpen Ωα := chartTargetEuclid_isOpen (I := I) (M := M) (α : M)
    have hC_one_on_Ωα : ∀ y ∈ Ωα, ‖ηE y‖ ≤ C := fun y _ => hC_one y
    have hC_grad_on_Ωα : ∀ y ∈ Ωα, ‖fderiv ℝ ηE y‖ ≤ C := fun y _ => hC_grad y
    have hC_nonneg : 0 ≤ C := le_trans zero_le_one (le_max_right _ _)
    have hηE_iter_bound :
        ∀ j ≤ 1, ∀ y ∈ Ωα, ‖iteratedFDeriv ℝ j ηE y‖ ≤ C := by
      intro j hj y hy
      interval_cases j
      · rw [norm_iteratedFDeriv_zero]; exact hC_one_on_Ωα y hy
      · rw [norm_iteratedFDeriv_one]; exact hC_grad_on_Ωα y hy
    obtain ⟨K_leib, hK_leib_pos, hK_leib_bound⟩ :=
      Sobolev.Euclidean.wkpNorm_smul_smooth_bounded_le_one
        1 (le_refl _) (d := Module.finrank ℝ E) hp_one hΩα_open hηE_smooth
        hC_nonneg hηE_iter_bound
    set ε_inner : ℝ := ε_per / (K_leib + 1) with hε_inner_def
    have hε_inner_pos : 0 < ε_inner := by
      apply div_pos hε_per_pos
      linarith
    obtain ⟨ψ, hψ_smooth, hψ_compact, hψ_support, hψ_close⟩ :=
      exists_smooth_strong_support_approx (I := I) (M := M) hp_one hp_top hu (α : M)
        ε_inner hε_inner_pos
    set χ : EuclN → ℝ := fun y => ηE y * ψ y with hχ_def
    have hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ := hηE_smooth.mul hψ_smooth
    have hχ_support_in : tsupport χ ⊆ tsupport ηE := by
      change tsupport (fun y => ηE y * ψ y) ⊆ tsupport ηE
      refine closure_mono ?_
      intro y hy
      simp only [Function.mem_support, ne_eq] at hy
      have hηE_ne : ηE y ≠ 0 := by
        intro h0; apply hy; rw [h0]; ring
      exact Function.mem_support.mpr hηE_ne
    have hχ_compact : HasCompactSupport χ :=
      hηE_compact.of_isClosed_subset (isClosed_tsupport _) hχ_support_in
    have hχ_support_image_K : tsupport χ ⊆
        (fun x : M => (toEuclidean (E := E)) (extChartAt I (α : M) x)) '' K_α α :=
      hχ_support_in.trans hηE_tsupp_in_image_K
    refine ⟨χ, hχ_smooth, hχ_compact, hχ_support_image_K, ?_⟩
    set f : EuclN → ℝ := chartPushed (I := I) (M := M)
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M) (α : M) u with hf_def
    have h_one_minus_ηE_f_zero : ∀ y ∈ Ωα, (1 - ηE y) * f y = 0 := by
      intro y hy
      by_cases hf_zero : f y = 0
      · rw [hf_zero]; ring
      · have hy_in_image : y ∈ chartImagePOUTsupport (I := I) (M := M) (α : M) := by
          by_contra hy_off
          apply hf_zero
          exact chartPushed_eq_zero_off_chartImagePOUTsupport (I := I) (M := M)
            (α : M) u hy hy_off
        have hy_in_image' :
            y ∈ (fun x : M => (toEuclidean (E := E)) (extChartAt I (α : M) x)) ''
              tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M (α : M)
                : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
          unfold chartImagePOUTsupport at hy_in_image
          rcases hy_in_image with ⟨z, ⟨x, hx_support, hxz⟩, hzy⟩
          exact ⟨x, hx_support, by rw [← hzy, ← hxz]⟩
        have hηEy : ηE y = 1 := hηE_one_on_pou_image y hy_in_image'
        rw [hηEy]; ring
    have h_decomp : ∀ y ∈ Ωα, f y - χ y = ηE y * (f y - ψ y) := by
      intro y hy
      have h0 : (1 - ηE y) * f y = 0 := h_one_minus_ηE_f_zero y hy
      change f y - ηE y * ψ y = ηE y * (f y - ψ y)
      have : f y - ηE y * ψ y = ηE y * (f y - ψ y) + (1 - ηE y) * f y := by ring
      rw [this, h0, add_zero]
    have h_target_meas : MeasurableSet Ωα := hΩα_open.measurableSet
    have h_diff_eq : (fun y => f y - χ y) =ᵐ[volume.restrict Ωα]
        (fun y => ηE y * (f y - ψ y)) := by
      refine (ae_restrict_iff' h_target_meas).mpr ?_
      refine Filter.Eventually.of_forall ?_
      intro y hy
      exact h_decomp y hy
    have h_norm_eq :
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 p (fun y => f y - χ y) Ωα =
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 p (fun y => ηE y * (f y - ψ y)) Ωα :=
      Sobolev.Euclidean.wkpNorm_congr_ae
        (d := Module.finrank ℝ E) hp_one hΩα_open h_diff_eq
    have hf_mem :
        Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 1 p f Ωα := hu (α : M)
    have hψ_mem :
        Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 1 p ψ Ωα :=
      Sobolev.Euclidean.MemWkp_of_smooth_compactSupport
        (d := Module.finrank ℝ E) hΩα_open hψ_smooth hψ_compact hψ_support hp_one 1
    have hfψ_mem :
        Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 1 p (fun y => f y - ψ y) Ωα :=
      Sobolev.Euclidean.MemWkp.sub
        (d := Module.finrank ℝ E) hp_one hΩα_open hf_mem hψ_mem
    have h_leib_bound :
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 p (fun y => ηE y * (f y - ψ y)) Ωα ≤
        ENNReal.ofReal K_leib *
          Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 1 p (fun y => f y - ψ y) Ωα :=
      hK_leib_bound hfψ_mem
    rw [h_norm_eq]
    refine h_leib_bound.trans ?_
    have h_step : ENNReal.ofReal K_leib *
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 p (fun y => f y - ψ y) Ωα ≤
        ENNReal.ofReal K_leib * ENNReal.ofReal ε_inner :=
      mul_le_mul_of_nonneg_left hψ_close (by simp : (0 : ℝ≥0∞) ≤ ENNReal.ofReal K_leib)
    refine h_step.trans ?_
    have hK_leib_nn : 0 ≤ K_leib := hK_leib_pos.le
    have hε_inner_nn : 0 ≤ ε_inner := hε_inner_pos.le
    rw [← ENNReal.ofReal_mul hK_leib_nn]
    apply ENNReal.ofReal_le_ofReal
    rw [hε_inner_def]
    rw [mul_div_assoc']
    have hK1_pos : 0 < K_leib + 1 := by linarith
    rw [div_le_iff₀ hK1_pos]
    have : K_leib * ε_per ≤ (K_leib + 1) * ε_per := by
      refine mul_le_mul_of_nonneg_right ?_ hε_per_pos.le
      linarith
    linarith
  let χ : S → (EuclN → ℝ) := fun α => (h_chi α).choose
  have hχ_smooth : ∀ α : S, ContDiff ℝ (⊤ : ℕ∞) (χ α) := fun α =>
    (h_chi α).choose_spec.1
  have hχ_compact : ∀ α : S, HasCompactSupport (χ α) := fun α =>
    (h_chi α).choose_spec.2.1
  have hχ_support : ∀ α : S, tsupport (χ α) ⊆
      (fun x : M => (toEuclidean (E := E)) (extChartAt I (α : M) x)) '' K_α α :=
    fun α => (h_chi α).choose_spec.2.2.1
  have hχ_close : ∀ α : S,
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 p
        (fun y => chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) (α : M) u y -
            χ α y)
        (chartTargetEuclid (I := I) (M := M) (α : M)) ≤
        ENNReal.ofReal ε_per := fun α => (h_chi α).choose_spec.2.2.2
  have hχ_support_target : ∀ α : S, tsupport (χ α) ⊆
      chartTargetEuclid (I := I) (M := M) (α : M) := by
    intro α
    refine (hχ_support α).trans ?_
    intro y hy
    rcases hy with ⟨x, hxK, hxy⟩
    have hx_chart : x ∈ (chartAt H (α : M)).source := hK_chart α hxK
    have hx_ext : x ∈ (extChartAt I (α : M)).source := by
      rw [extChartAt_source]; exact hx_chart
    have h_target : extChartAt I (α : M) x ∈ (extChartAt I (α : M)).target :=
      (extChartAt I (α : M)).map_source hx_ext
    rw [← hxy]
    exact ⟨extChartAt I (α : M) x, h_target, rfl⟩
  set v : M → ℝ := fun x =>
    ∑ α ∈ S.attach, chartPullback I (α : M) (χ α) x with hv_def
  have hv_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ v := by
    refine contMDiff_finsetSum_chartPullback (I := I) (M := M)
      (S := S.attach) (α := fun α : S => (α : M)) (ψ := fun α => χ α) ?_ ?_ ?_
    · intro α _; exact hχ_smooth α
    · intro α _; exact hχ_compact α
    · intro α _; exact hχ_support_target α
  refine ⟨v, hv_smooth, ?_⟩
  rw [wkpNormChart_eq_finset_sum (I := I) (M := M) 1 hp_one (fun x => u x - v x)]
  have h_per_gamma : ∀ (γ : M), (hγS : γ ∈ S) →
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 p
        (chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) γ
          (fun x => u x - v x))
        (chartTargetEuclid (I := I) (M := M) γ) ≤
        ∑ α ∈ S.attach, ENNReal.ofReal (K_pair ⟨γ, hγS⟩ α) * ENNReal.ofReal ε_per := by
    intro γ hγS
    have h_u_decomp : (fun x : M => u x) =
        fun x =>
          ∑ α ∈ S.attach,
            chartPullback I (α : M)
              (chartPushed (I := I) (M := M)
                (CalabiYau.RiemannianVolume.chartAtlasPOU I M) (α : M) u) x := by
      have h_decomp := fun_eq_finset_sum_chartPullback_chartPushed
        (I := I) (M := M) u
      rw [h_decomp]
      funext x
      rw [show (∑ α ∈ S, chartPullback I α
            (chartPushed (I := I) (M := M)
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u) x) =
          (∑ α ∈ S.attach, chartPullback I (α : M)
            (chartPushed (I := I) (M := M)
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M) (α : M) u) x)
          from by rw [Finset.sum_attach S (fun α => chartPullback I α
            (chartPushed (I := I) (M := M)
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u) x)]]
    have h_uv_decomp : (fun x : M => u x - v x) =
        fun x =>
          ∑ α ∈ S.attach,
            chartPullback I (α : M)
              (fun y => chartPushed (I := I) (M := M)
                (CalabiYau.RiemannianVolume.chartAtlasPOU I M) (α : M) u y -
                χ α y) x := by
      funext x
      have h1 := congrFun h_u_decomp x
      change u x - v x = _
      rw [hv_def]
      simp only
      rw [h1]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro α _
      classical
      by_cases hxα : x ∈ (chartAt H (α : M)).source
      · rw [chartPullback_apply_of_mem (I := I) (M := M) (α : M) _ hxα]
        rw [chartPullback_apply_of_mem (I := I) (M := M) (α : M) _ hxα]
        rw [chartPullback_apply_of_mem (I := I) (M := M) (α : M) _ hxα]
      · rw [chartPullback_apply_of_notMem (I := I) (M := M) (α : M) _ hxα]
        rw [chartPullback_apply_of_notMem (I := I) (M := M) (α : M) _ hxα]
        rw [chartPullback_apply_of_notMem (I := I) (M := M) (α : M) _ hxα]
        ring
    have h_chartPushed_decomp : chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) γ
        (fun x => u x - v x) =
        fun y => ∑ α ∈ S.attach,
          chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) γ
            (chartPullback I (α : M)
              (fun z => chartPushed (I := I) (M := M)
                (CalabiYau.RiemannianVolume.chartAtlasPOU I M) (α : M) u z -
                χ α z)) y := by
      rw [h_uv_decomp]
      exact chartPushed_finset_sum
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) γ S.attach
        (fun α x => chartPullback I (α : M)
          (fun y => chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) (α : M) u y -
            χ α y) x)
    rw [h_chartPushed_decomp]
    have h_per_alpha : ∀ α ∈ S.attach,
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 p
          (chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) γ
            (chartPullback I (α : M)
              (fun y => chartPushed (I := I) (M := M)
                (CalabiYau.RiemannianVolume.chartAtlasPOU I M) (α : M) u y -
                χ α y)))
          (chartTargetEuclid (I := I) (M := M) γ) ≤
          ENNReal.ofReal (K_pair ⟨γ, hγS⟩ α) * ENNReal.ofReal ε_per := by
      intro α _hα_mem
      set f_α : EuclN → ℝ :=
        tightenedChartPushed (I := I) (M := M) (α : M) (η_M α) u with hf_α_def
      have h_chartPullback_eq : chartPullback I (α : M)
          (fun y => chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) (α : M) u y -
            χ α y) =
          chartPullback I (α : M) (fun y => f_α y - χ α y) := by
        rw [chartPullback_sub, chartPullback_sub, hf_α_def,
          chartPullback_tightenedChartPushed_eq (I := I) (M := M)
            (α : M) (hη_one_on_tsupport α) u]
      rw [h_chartPullback_eq]
      have hf_α_mem : Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 1 p f_α
          (chartTargetEuclid (I := I) (M := M) (α : M)) :=
        tightenedChartPushed_memWkp (I := I) (M := M) hp_one hu (α : M)
          (hη_smooth α) (hη_M_compact α) (hη_M_support_chart α)
      have hχ_α_mem : Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 1 p (χ α)
          (chartTargetEuclid (I := I) (M := M) (α : M)) :=
        Sobolev.Euclidean.MemWkp_of_smooth_compactSupport
          (d := Module.finrank ℝ E)
          (chartTargetEuclid_isOpen (I := I) (M := M) (α : M))
          (hχ_smooth α) (hχ_compact α) (hχ_support_target α) hp_one 1
      have h_diff_mem : Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 1 p (fun y => f_α y - χ α y)
          (chartTargetEuclid (I := I) (M := M) (α : M)) :=
        Sobolev.Euclidean.MemWkp.sub
          (d := Module.finrank ℝ E) hp_one
          (chartTargetEuclid_isOpen (I := I) (M := M) (α : M))
          hf_α_mem hχ_α_mem
      have h_diff_support : tsupport (fun y => f_α y - χ α y) ⊆
          (fun x : M => (toEuclidean (E := E)) (extChartAt I (α : M) x)) '' K_α α := by
        have h_support_sub : Function.support (fun y => f_α y - χ α y) ⊆
            Function.support f_α ∪ Function.support (χ α) := by
          intro y hy
          by_cases hyf : y ∈ Function.support f_α
          · exact Or.inl hyf
          · right
            change χ α y ≠ 0
            intro h0
            apply hy
            change f_α y - χ α y = 0
            have : f_α y = 0 := Function.notMem_support.mp hyf
            rw [this, h0, sub_self]
        have h_tsupp_sub : tsupport (fun y => f_α y - χ α y) ⊆
            tsupport f_α ∪ tsupport (χ α) := by
          unfold tsupport
          refine (closure_mono h_support_sub).trans ?_
          rw [closure_union]
        have hf_α_support : tsupport f_α ⊆
            (fun x : M => (toEuclidean (E := E)) (extChartAt I (α : M) x)) '' K_α α :=
          tsupport_tightenedChartPushed_subset (I := I) (M := M) (α : M)
            (hη_M_compact α) (hη_M_support_chart α) (hη_tsupp_K α) u
        exact h_tsupp_sub.trans (Set.union_subset hf_α_support (hχ_support α))
      have h_bd := hK_pair_bound ⟨γ, hγS⟩ α h_diff_mem h_diff_support
      have h_diff_close :
          Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 1 p
            (fun y => f_α y - χ α y)
            (chartTargetEuclid (I := I) (M := M) (α : M)) ≤
          ENNReal.ofReal ε_per := by
        rw [hf_α_def]
        rw [wkpNorm_tightenedChartPushed_sub_eq (I := I) (M := M) hp_one (α : M)
          (hη_one_on_tsupport α) u (χ α)]
        exact hχ_close α
      refine h_bd.trans ?_
      exact mul_le_mul_of_nonneg_left h_diff_close (zero_le)
    have h_summand_mem : ∀ α ∈ S.attach,
        Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 1 p
          (chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) γ
            (chartPullback I (α : M)
              (fun y => chartPushed (I := I) (M := M)
                (CalabiYau.RiemannianVolume.chartAtlasPOU I M) (α : M) u y -
                χ α y)))
          (chartTargetEuclid (I := I) (M := M) γ) := by
      intro α _hα_mem
      set f_α : EuclN → ℝ :=
        tightenedChartPushed (I := I) (M := M) (α : M) (η_M α) u with hf_α_def'
      have hf_α_mem : Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 1 p f_α
          (chartTargetEuclid (I := I) (M := M) (α : M)) :=
        tightenedChartPushed_memWkp (I := I) (M := M) hp_one hu (α : M)
          (hη_smooth α) (hη_M_compact α) (hη_M_support_chart α)
      have hχ_α_mem : Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 1 p (χ α)
          (chartTargetEuclid (I := I) (M := M) (α : M)) :=
        Sobolev.Euclidean.MemWkp_of_smooth_compactSupport
          (d := Module.finrank ℝ E)
          (chartTargetEuclid_isOpen (I := I) (M := M) (α : M))
          (hχ_smooth α) (hχ_compact α) (hχ_support_target α) hp_one 1
      have h_diff_mem : Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 1 p (fun y => f_α y - χ α y)
          (chartTargetEuclid (I := I) (M := M) (α : M)) :=
        Sobolev.Euclidean.MemWkp.sub
          (d := Module.finrank ℝ E) hp_one
          (chartTargetEuclid_isOpen (I := I) (M := M) (α : M))
          hf_α_mem hχ_α_mem
      have h_diff_support : tsupport (fun y => f_α y - χ α y) ⊆
          (fun x : M => (toEuclidean (E := E)) (extChartAt I (α : M) x)) '' K_α α := by
        have h_support_sub : Function.support (fun y => f_α y - χ α y) ⊆
            Function.support f_α ∪ Function.support (χ α) := by
          intro y hy
          by_cases hyf : y ∈ Function.support f_α
          · exact Or.inl hyf
          · right
            change χ α y ≠ 0
            intro h0
            apply hy
            change f_α y - χ α y = 0
            have : f_α y = 0 := Function.notMem_support.mp hyf
            rw [this, h0, sub_self]
        have h_tsupp_sub : tsupport (fun y => f_α y - χ α y) ⊆
            tsupport f_α ∪ tsupport (χ α) := by
          unfold tsupport
          refine (closure_mono h_support_sub).trans ?_
          rw [closure_union]
        have hf_α_support : tsupport f_α ⊆
            (fun x : M => (toEuclidean (E := E)) (extChartAt I (α : M) x)) '' K_α α :=
          tsupport_tightenedChartPushed_subset (I := I) (M := M) (α : M)
            (hη_M_compact α) (hη_M_support_chart α) (hη_tsupp_K α) u
        exact h_tsupp_sub.trans (Set.union_subset hf_α_support (hχ_support α))
      have h_mem_cross : Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 1 p
          (chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) γ
            (chartPullback I (α : M) (fun y => f_α y - χ α y)))
          (chartTargetEuclid (I := I) (M := M) γ) :=
        MemWkp_of_cross_chart_pushforward (I := I) (M := M) γ (α : M)
          (hK_compact α) (hK_chart α) hp_one hp_top h_diff_mem h_diff_support
      have h_eq : chartPullback I (α : M)
          (fun y => chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) (α : M) u y -
            χ α y) =
          chartPullback I (α : M) (fun y => f_α y - χ α y) := by
        rw [chartPullback_sub, chartPullback_sub, hf_α_def',
          chartPullback_tightenedChartPushed_eq (I := I) (M := M)
            (α : M) (hη_one_on_tsupport α) u]
      simpa [h_eq] using h_mem_cross
    set Ωγ := chartTargetEuclid (I := I) (M := M) γ with hΩγ_def
    have hΩγ_open : IsOpen Ωγ := chartTargetEuclid_isOpen (I := I) (M := M) γ
    have h_total_bound : Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 p
        (fun y => ∑ α ∈ S.attach,
          chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) γ
            (chartPullback I (α : M)
              (fun z => chartPushed (I := I) (M := M)
                (CalabiYau.RiemannianVolume.chartAtlasPOU I M) (α : M) u z -
                χ α z)) y)
        Ωγ ≤
      ∑ α ∈ S.attach, ENNReal.ofReal (K_pair ⟨γ, hγS⟩ α) * ENNReal.ofReal ε_per := by
      set F : (↥S) → EuclN → ℝ := fun (α' : S) y =>
        chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) γ
          (chartPullback I (α' : M)
            (fun z => chartPushed (I := I) (M := M)
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M) (α' : M) u z -
              χ α' z)) y with hF_def
      have hF_mem : ∀ (α' : S) (h : α' ∈ S.attach),
          Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) 1 p (F α') Ωγ := by
        intro α' hα'
        simpa [hF_def] using h_summand_mem α' hα'
      induction S.attach using Finset.induction_on with
      | empty =>
          simp [Sobolev.Euclidean.wkpNorm_zero_fun_zero
            (d := Module.finrank ℝ E) hp_one hΩγ_open]
      | insert α T hαT ih =>
          have hsum_eq : (fun y => ∑ α' ∈ insert α T, F α' y) =
              (fun y => F α y + ∑ α' ∈ T, F α' y) := by
            ext y; simp [Finset.sum_insert hαT]
          rw [hsum_eq]
          have h_mem_α : Sobolev.Euclidean.MemWkp
              (d := Module.finrank ℝ E) 1 p (F α) Ωγ :=
            hF_mem α (Finset.mem_attach _ _)
          have h_mem_sum : Sobolev.Euclidean.MemWkp
              (d := Module.finrank ℝ E) 1 p (fun y => ∑ α' ∈ T, F α' y) Ωγ := by
            refine Finset.induction_on T ?_ ?_
            · exact Sobolev.Euclidean.MemWkp_zero_fun
                (d := Module.finrank ℝ E) hp_one hΩγ_open
            · intro β T' hβT' ih_sum
              have hsum_eq' : (fun y => ∑ β' ∈ insert β T', F β' y) =
                  (fun y => F β y + ∑ β' ∈ T', F β' y) := by
                ext y; simp [Finset.sum_insert hβT']
              rw [hsum_eq']
              exact Sobolev.Euclidean.MemWkp.add
                (d := Module.finrank ℝ E) hp_one hΩγ_open
                (hF_mem β (Finset.mem_attach _ _)) ih_sum
          refine (Sobolev.Euclidean.wkpNorm_add_le
            (d := Module.finrank ℝ E) hp_one hΩγ_open h_mem_α h_mem_sum).trans ?_
          rw [Finset.sum_insert hαT]
          refine add_le_add ?_ ?_
          · exact h_per_alpha α (Finset.mem_attach _ _)
          · exact ih
    exact h_total_bound
  let f : S → ENNReal := fun (γ : S) =>
    Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) 1 p
      (chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) γ.val
        (fun x => u x - v x))
      (chartTargetEuclid (I := I) (M := M) γ.val)
  have h_f_bound : ∀ (γ : S), f γ ≤ ∑ α : S, ENNReal.ofReal (K_pair γ α) * ENNReal.ofReal
    ε_per := by
    intro γ
    dsimp [f]
    simpa [Finset.sum_attach (s := CalabiYau.RiemannianVolume.chartAtlasPOUFinset), hS_def] using
      h_per_gamma γ.val γ.property
  rw [← Finset.sum_attach (s := S)]
  calc
    (∑ γ : S, f γ) ≤ (∑ γ : S, ∑ α : S, ENNReal.ofReal (K_pair γ α) * ENNReal.ofReal ε_per) :=
      Finset.sum_le_sum (fun γ _ => h_f_bound γ)
    _ ≤ ENNReal.ofReal ε := by
      calc
        (∑ γ : S, ∑ α : S, ENNReal.ofReal (K_pair γ α) * ENNReal.ofReal ε_per)
            = (∑ γ : S, ∑ α : S, ENNReal.ofReal (K_pair γ α * ε_per)) := by
          refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun α _ => ?_
          rw [ENNReal.ofReal_mul ((hK_pair_pos γ α).le)]
        _ = ENNReal.ofReal (∑ γ : S, ∑ α : S, (K_pair γ α * ε_per)) := by
          calc
            (∑ γ : S, ∑ α : S, ENNReal.ofReal (K_pair γ α * ε_per))
                = (∑ γ : S, ENNReal.ofReal (∑ α : S, (K_pair γ α * ε_per))) := by
              refine Finset.sum_congr rfl (fun γ _ => ?_)
              rw [ENNReal.ofReal_sum_of_nonneg (fun α hα =>
                mul_nonneg ((hK_pair_pos γ α).le) hε_per_pos.le)]
            _ = ENNReal.ofReal (∑ γ : S, ∑ α : S, (K_pair γ α * ε_per)) := by
              rw [ENNReal.ofReal_sum_of_nonneg (fun γ hγ =>
                Finset.sum_nonneg (fun α hα =>
                  mul_nonneg ((hK_pair_pos γ α).le) hε_per_pos.le))]
        _ = ENNReal.ofReal ((∑ γ : S, ∑ α : S, K_pair γ α) * ε_per) := by
          simp [Finset.sum_mul]
        _ = ENNReal.ofReal ((K_total - 1) * ε_per) := by
          rw [hK_total_def]
          ring_nf
        _ ≤ ENNReal.ofReal (K_total * ε_per) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by
            have : 0 ≤ 1 := by norm_num
            linarith) hε_per_pos.le)
        _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hK_total_eps_le

end Chart
end Sobolev
