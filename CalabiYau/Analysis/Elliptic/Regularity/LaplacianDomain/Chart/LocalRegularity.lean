-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/LaplacianDomain/Chart/LocalRegularity.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.ChartBilinear.H1Compl
public import CalabiYau.Analysis.Elliptic.Regularity.ChartBilinear.H1ComplFromDom
public import CalabiYau.Analysis.Elliptic.Regularity.ChartHk.H2NonSmooth
public import CalabiYau.Analysis.Elliptic.Operator.ChartLocalLaplacian
public import CalabiYau.Mathlib.Geometry.Manifold.PartitionOfUnity.CompactSupport
public import CalabiYau.Analysis.Sobolev.Nirenberg.MasterInequality.Coercivity
public import CalabiYau.Analysis.Sobolev.Nirenberg.MasterInequality.CrossBoundsSummandContinuityIntegrability
public import CalabiYau.Analysis.Sobolev.Nirenberg.MasterInequality.CrossBoundsPointwiseProductBounds
public import CalabiYau.Analysis.Sobolev.Tools.DifferenceQuotient
public import CalabiYau.Analysis.Sobolev.Euclidean.WeakDerivative.Distribution
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Function.L2Space
public import CalabiYau.Analysis.Elliptic.Operator.VariationalLaplacian
public import CalabiYau.Analysis.Sobolev.Chart.Defs
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import CalabiYau.Analysis.Elliptic.Regularity.LaplacianDomain.Chart.VariationalData
public import CalabiYau.Analysis.Elliptic.Regularity.ChartBilinear.UniformDiffQuotBoundFromDomain.WeakPartialDerivativeBound
public import CalabiYau.Analysis.Sobolev.Approximation.Density.Smooth
public import CalabiYau.Analysis.Sobolev.Euclidean.Density

@[expose] public section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace CalabiYau
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Laplacian.MetricExtension
  hiding chartTargetEuclid
open CalabiYau.Analysis.Laplacian.ChartLocalLaplacian
open CalabiYau.Laplacian.ChartMeasureEquiv
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.ChartH2NonSmooth
open CalabiYau.Analysis.Laplacian.LaplacianDomainChartData
open CalabiYau.Analysis.Laplacian.LaplacianDomainVariationalIdentityIntegralForm
open _root_.Sobolev
open _root_.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private lemma thickening_mono_of_lt
    {α : Type*} [PseudoEMetricSpace α]
    {r r' : ℝ} (hr_lt : r < r') (K : Set α) :
    Metric.thickening r K ⊆ Metric.thickening r' K := by
  intro y hy
  refine Metric.mem_thickening_iff_infEDist_lt.mpr ?_
  have h := Metric.mem_thickening_iff_infEDist_lt.mp hy
  exact lt_of_lt_of_le h
    (ENNReal.ofReal_le_ofReal hr_lt.le)

private lemma self_subset_thickening_of_pos
    {α : Type*} [PseudoEMetricSpace α]
    {r : ℝ} (hr_pos : 0 < r) (K : Set α) :
    K ⊆ Metric.thickening r K :=
  Metric.self_subset_thickening hr_pos K

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartPushed_pou_zero_off_KApha
    [T2Space M] [SigmaCompactSpace M]
    (α : M) (u : M → ℝ) :
    ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      y ∉ chartImagePOUTsupport (I := I) (M := M) α →
        chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u y = 0 := by
  intro y hy hy_off
  exact chartPushed_eq_zero_off_chartImagePOUTsupport (I := I) (M := M) α u hy hy_off

theorem chartPushed_memWkp_two_of_laplacianDomain
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (α : M) :
    Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((h1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set u : M → ℝ := ((h1ComplToLp (I := I) (M := M) g u_h :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) with hu_def
  set D := chartBilinearH1ComplDataOfLaplacianDomain
    (I := I) (M := M) g α hu_h with hD_def
  set K_α : Set EuclN := chartImagePOUTsupport (I := I) (M := M) α with hK_α_def
  have hK_α_compact : IsCompact K_α :=
    chartImagePOUTsupport_isCompact (I := I) (M := M) α
  have hK_α_in_chart : K_α ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartImagePOUTsupport_subset_target (I := I) (M := M) α
  have h_chart_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  obtain ⟨R_α, hR_α_pos, hR_α_subset⟩ :=
    hK_α_compact.exists_cthickening_subset_open h_chart_open hK_α_in_chart
  set ε : ℝ := R_α / 16 with hε_def
  have hε_pos : 0 < ε := by positivity
  set R₀ : ℝ := ε with hR₀_def
  have hR₀_pos : 0 < R₀ := hε_pos
  set Ω'' : Set EuclN := Metric.thickening (2 * ε) K_α with hΩ''_def
  have hΩ''_open : IsOpen Ω'' := Metric.isOpen_thickening
  have h_two_ε_pos : 0 < 2 * ε := by positivity
  have hK_α_in_Ω'' : K_α ⊆ Ω'' :=
    self_subset_thickening_of_pos h_two_ε_pos K_α
  have h_closureΩ''_sub : closure Ω'' ⊆ Metric.cthickening (2 * ε) K_α := by
    refine closure_minimal (Metric.thickening_subset_cthickening _ _)
      Metric.isClosed_cthickening
  have h_cthick_two_ε_in_chart : Metric.cthickening (2 * ε) K_α ⊆
      chartTargetEuclid (I := I) (M := M) α := by
    have hle : (2 * ε) ≤ R_α := by change 2 * (R_α / 16) ≤ R_α; linarith
    have h := Metric.cthickening_mono hle K_α
    exact h.trans hR_α_subset
  have h_closureΩ''_in_chart : closure Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α :=
    h_closureΩ''_sub.trans h_cthick_two_ε_in_chart
  have hΩ''_compact_closure : IsCompact (closure Ω'') :=
    hK_α_compact.cthickening.of_isClosed_subset isClosed_closure h_closureΩ''_sub
  have h_room : Metric.cthickening R₀ (closure Ω'') ⊆
      chartTargetEuclid (I := I) (M := M) α := by
    have h1 : Metric.cthickening R₀ (closure Ω'') ⊆
        Metric.cthickening R₀ (Metric.cthickening (2 * ε) K_α) :=
      Metric.cthickening_subset_of_subset _ h_closureΩ''_sub
    have h2 : Metric.cthickening R₀ (Metric.cthickening (2 * ε) K_α) ⊆
        Metric.cthickening (R₀ + 2 * ε) K_α := by
      apply Metric.cthickening_cthickening_subset
      · positivity
      · positivity
    have h3 : Metric.cthickening (R₀ + 2 * ε) K_α ⊆
        Metric.cthickening R_α K_α := by
      have hle : R₀ + 2 * ε ≤ R_α := by
        change R_α / 16 + 2 * (R_α / 16) ≤ R_α; linarith
      exact Metric.cthickening_mono hle K_α
    exact ((h1.trans h2).trans h3).trans hR_α_subset
  set Ω' : Set EuclN := Metric.thickening (8 * ε) K_α with hΩ'_def
  have hΩ'_open : IsOpen Ω' := Metric.isOpen_thickening
  have h_eight_ε_pos : 0 < 8 * ε := by positivity
  have hK_α_in_Ω' : K_α ⊆ Ω' :=
    self_subset_thickening_of_pos h_eight_ε_pos K_α
  have h_closureΩ'_sub : closure Ω' ⊆ Metric.cthickening (8 * ε) K_α := by
    refine closure_minimal (Metric.thickening_subset_cthickening _ _)
      Metric.isClosed_cthickening
  have h_cthick_eight_ε_in_chart : Metric.cthickening (8 * ε) K_α ⊆
      chartTargetEuclid (I := I) (M := M) α := by
    have hle : (8 * ε) ≤ R_α := by change 8 * (R_α / 16) ≤ R_α; linarith
    have h := Metric.cthickening_mono hle K_α
    exact h.trans hR_α_subset
  have h_closureΩ'_in_chart : closure Ω' ⊆ chartTargetEuclid (I := I) (M := M) α :=
    h_closureΩ'_sub.trans h_cthick_eight_ε_in_chart
  have hΩ'_compact_closure : IsCompact (closure Ω') :=
    hK_α_compact.cthickening.of_isClosed_subset isClosed_closure h_closureΩ'_sub
  have h_cthick_two_ε_sub_thick_three_ε :
      Metric.cthickening (2 * ε) K_α ⊆ Metric.thickening (3 * ε) K_α :=
    Metric.cthickening_subset_thickening' (by positivity) (by linarith) K_α
  have h_thick_three_ε_sub_Ω' :
      Metric.thickening (3 * ε) K_α ⊆ Ω' := by
    rw [hΩ'_def]
    exact thickening_mono_of_lt (by linarith) K_α
  set K_η : Set EuclN := Metric.cthickening (3 * ε) K_α with hK_η_def
  have hK_η_compact : IsCompact K_η := hK_α_compact.cthickening
  set Ω_η : Set EuclN := Metric.thickening (5 * ε) K_α with hΩ_η_def
  have hΩ_η_open : IsOpen Ω_η := Metric.isOpen_thickening
  have hK_η_in_Ω_η : K_η ⊆ Ω_η := by
    refine Metric.cthickening_subset_thickening' (by positivity) (by linarith) K_α
  obtain ⟨δ_η, η, hδ_η_pos, hδ_η_sub_Ωη, hη_smooth, hη_support, hη_range,
      hη_one_on_cthick_K_η, hη_tsupp_in_Ω_η⟩ :=
    Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      (d := Module.finrank ℝ E) hK_η_compact hΩ_η_open hK_η_in_Ω_η
  obtain ⟨N, hN_pos, h_fderiv_eta⟩ :=
    Sobolev.Chart.exists_grad_bound_of_compactSupport_smooth
      hη_smooth hη_support
  have hN_nn : 0 ≤ N := hN_pos.le
  have hη_one_on_K_η : ∀ x ∈ K_η, η x = 1 := by
    intro x hx
    apply hη_one_on_cthick_K_η
    exact Metric.self_subset_cthickening _ hx
  have hΩ''_sub_K_η : Ω'' ⊆ K_η := by
    intro y hy
    have h1 : y ∈ Metric.cthickening (2 * ε) K_α :=
      Metric.thickening_subset_cthickening _ _ hy
    refine Metric.cthickening_mono (by linarith : (2 * ε) ≤ 3 * ε) K_α h1
  have hη_one_on_Ω'' : ∀ x ∈ Ω'', η x = 1 := fun x hx => hη_one_on_K_η x (hΩ''_sub_K_η hx)
  have hη_in_Ω' : tsupport η ⊆ Ω' := by
    refine hη_tsupp_in_Ω_η.trans ?_
    rw [hΩ_η_def, hΩ'_def]
    exact thickening_mono_of_lt (by linarith) K_α
  have hh_support_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω' := by
    intro h hh
    have h_tsupp_in_cthick_5ε : tsupport η ⊆ Metric.cthickening (5 * ε) K_α := by
      refine hη_tsupp_in_Ω_η.trans ?_
      rw [hΩ_η_def]
      exact Metric.thickening_subset_cthickening _ _
    by_cases h_abs : |h| ≤ 0
    · have hh_zero : |h| = 0 := le_antisymm h_abs (abs_nonneg _)
      have hcth_zero : Metric.cthickening |h| (tsupport η) = tsupport η := by
        rw [hh_zero, Metric.cthickening_zero]
        exact (isClosed_tsupport η).closure_eq
      rw [hcth_zero]
      exact hη_in_Ω'
    · have h_abs_pos : 0 < |h| := not_le.mp h_abs
      have h1 : Metric.cthickening |h| (tsupport η) ⊆
          Metric.cthickening |h| (Metric.cthickening (5 * ε) K_α) :=
        Metric.cthickening_subset_of_subset _ h_tsupp_in_cthick_5ε
      have h2 : Metric.cthickening |h| (Metric.cthickening (5 * ε) K_α) ⊆
          Metric.cthickening (|h| + 5 * ε) K_α := by
        apply Metric.cthickening_cthickening_subset
        · exact h_abs_pos.le
        · positivity
      have h_le : |h| + 5 * ε < 8 * ε := by
        calc |h| + 5 * ε ≤ R₀ + 5 * ε := by linarith
          _ = ε + 5 * ε := by rw [hR₀_def]
          _ = 6 * ε := by ring
          _ < 8 * ε := by linarith
      have h3 : Metric.cthickening (|h| + 5 * ε) K_α ⊆ Ω' := by
        rw [hΩ'_def]
        exact Metric.cthickening_subset_thickening' (by linarith) h_le K_α
      exact (h1.trans h2).trans h3
  obtain ⟨MBound, hM_nn, h_uniform_bd⟩ :=
    uniform_diffQuot_weakPartial_bound
      (I := I) (M := M) (g := g) (α := α) D
      hη_smooth hη_support hη_range hN_nn h_fderiv_eta
      hΩ'_open h_closureΩ'_in_chart hΩ'_compact_closure
      hη_in_Ω' hR₀_pos hh_support_in_Ω' hη_one_on_Ω'' hΩ''_open.measurableSet
  have h_h2 :=
    exists_weak_second_partial_of_uniform_diffQuot_bound
      (I := I) (M := M) (g := g) (α := α) D
      hΩ''_open hΩ''_compact_closure hR₀_pos h_room
      hM_nn h_uniform_bd
  set f : EuclN → ℝ := chartPushed (I := I) (M := M)
    (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u with hf_def
  set v : EuclN → ℝ := Ω''.indicator f with hv_def
  have h_chart_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    h_chart_open.measurableSet
  have hΩ''_meas : MeasurableSet Ω'' := hΩ''_open.measurableSet
  have h_v_eq_f_ae : v =ᵐ[volume.restrict (chartTargetEuclid (I := I) (M := M) α)] f := by
    refine (ae_restrict_iff' h_chart_meas).mpr ?_
    refine Filter.Eventually.of_forall fun y hy => ?_
    by_cases hyΩ : y ∈ Ω''
    · rw [hv_def]
      rw [Set.indicator_of_mem hyΩ]
    · rw [hv_def]
      rw [Set.indicator_of_notMem hyΩ]
      have hy_off_K_α : y ∉ K_α := fun hyK => hyΩ (hK_α_in_Ω'' hyK)
      exact (chartPushed_pou_zero_off_KApha (I := I) (M := M) α u y hy hy_off_K_α).symm
  have hΩ''_in_chart : Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α :=
    fun y hy => h_closureΩ''_in_chart (subset_closure hy)
  have h_support_v_sub_K_α : Function.support v ⊆ K_α := by
    intro y hy
    by_contra hy_off
    apply hy
    rw [hv_def]
    by_cases hyΩ : y ∈ Ω''
    · rw [Set.indicator_of_mem hyΩ]
      have hy_chart : y ∈ chartTargetEuclid (I := I) (M := M) α := hΩ''_in_chart hyΩ
      exact chartPushed_pou_zero_off_KApha (I := I) (M := M) α u y hy_chart hy_off
    · rw [Set.indicator_of_notMem hyΩ]
  have h_tsupp_v_sub_K_α : tsupport v ⊆ K_α := by
    refine closure_minimal h_support_v_sub_K_α ?_
    exact hK_α_compact.isClosed
  have hv_compactSupport : HasCompactSupport v :=
    hK_α_compact.of_isClosed_subset (isClosed_tsupport _) h_tsupp_v_sub_K_α
  have h_tsupp_v_sub_Ω'' : tsupport v ⊆ Ω'' := h_tsupp_v_sub_K_α.trans hK_α_in_Ω''
  have h_uChart_memLp_vol_closureΩ'' :
      MemLp D.uChart 2 (volume.restrict (closure Ω'')) :=
    memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure (I := I) (M := M)
      D.u_chart_memLp_weighted hΩ''_compact_closure
      hΩ''_compact_closure.isClosed.measurableSet h_closureΩ''_in_chart
  have h_uChart_memLp_vol_Ω'' :
      MemLp D.uChart 2 (volume.restrict Ω'') :=
    h_uChart_memLp_vol_closureΩ''.mono_measure
      (Measure.restrict_mono subset_closure le_rfl)
  have h_uChart_ae_f :
      D.uChart =ᵐ[volume.restrict (chartTargetEuclid (I := I) (M := M) α)] f := by
    have h_coeFn :=
      chartPushedLpFromLp_coeFn
      (I := I) (M := M) g α (h1ComplToLp (I := I) (M := M) g u_h)
    have h_v_abs_w :
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α) ≪
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α) := by
      intro A hA
      unfold chartPulledWeightedMeasure at hA
      rw [show ((volume : Measure EuclN).withDensity
          (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))).restrict
          (chartTargetEuclid (I := I) (M := M) α) =
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)).withDensity
            (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
        from MeasureTheory.restrict_withDensity h_chart_meas _] at hA
      rw [MeasureTheory.withDensity_apply_eq_zero'
        (μ := (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α))
        (f := fun y : EuclN => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
        (ENNReal.measurable_ofReal.comp_aemeasurable
          ((densityOnEuclid_continuousOn (I := I) g α).aemeasurable h_chart_meas))] at hA
      rw [Measure.restrict_apply' h_chart_meas]
      rw [Measure.restrict_apply' h_chart_meas] at hA
      refine MeasureTheory.measure_mono_null ?_ hA
      intro y ⟨hy_A, hy_chart⟩
      refine ⟨⟨?_, hy_A⟩, hy_chart⟩
      have h_pos : 0 < densityOnEuclid (I := I) g α y :=
        densityOnEuclid_pos (I := I) g α hy_chart
      exact (ENNReal.ofReal_pos.mpr h_pos).ne'
    have h_coeFn_vol : ((chartPushedLpFromLp (I := I) (M := M) g α
          (h1ComplToLp (I := I) (M := M) g u_h)) : EuclN → ℝ) =ᵐ[
          (volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)]
        chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α
          ((h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ) :=
      h_v_abs_w.ae_le h_coeFn
    change ((chartPushedLpFromLp (I := I) (M := M) g α
          (h1ComplToLp (I := I) (M := M) g u_h)) : EuclN → ℝ) =ᵐ[_] f
    exact h_coeFn_vol
  have h_uChart_ae_v_Ω'' : D.uChart =ᵐ[volume.restrict Ω''] v := by
    have h_sub : Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α := hΩ''_in_chart
    have h_uChart_ae_f_Ω'' : D.uChart =ᵐ[volume.restrict Ω''] f :=
      h_uChart_ae_f.filter_mono (MeasureTheory.ae_mono
        (Measure.restrict_mono h_sub le_rfl))
    refine h_uChart_ae_f_Ω''.mp ?_
    refine (ae_restrict_iff' hΩ''_meas).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy heq
    rw [hv_def, Set.indicator_of_mem hy]
    exact heq
  have hv_memLp_Ω'' : MemLp v 2 (volume.restrict Ω'') :=
    (MeasureTheory.memLp_congr_ae h_uChart_ae_v_Ω'').mp h_uChart_memLp_vol_Ω''
  have h_dwp_weak_v_Ω'' : ∀ i, Sobolev.Euclidean.HasWeakPartialDeriv
      (d := Module.finrank ℝ E) i (D.weakPartial i) v Ω'' := by
    intro i
    have h_dwp_uChart : Sobolev.Euclidean.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
        (D.weakPartial i) D.uChart (chartTargetEuclid (I := I) (M := M) α) :=
      D.weak_partial_isWeakPartial i
    have h_dwp_uChart_Ω'' : Sobolev.Euclidean.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
        (D.weakPartial i) D.uChart Ω'' :=
      Sobolev.Euclidean.HasWeakPartialDeriv.restrict hΩ''_in_chart h_dwp_uChart
    exact Sobolev.Euclidean.hasWeakPartialDeriv_congr_ae
      (d := Module.finrank ℝ E) i h_uChart_ae_v_Ω'' h_dwp_uChart_Ω''
  have h_dwp_memLp_Ω'' : ∀ i, MemLp (D.weakPartial i) 2 (volume.restrict Ω'') := by
    intro i
    have h := D.weak_partial_locally_memLp i (closure Ω'') hΩ''_compact_closure
      h_closureΩ''_in_chart
    exact h.mono_measure (Measure.restrict_mono subset_closure le_rfl)
  have hv_memW1p_Ω'' : Sobolev.Euclidean.MemW1p (d := Module.finrank ℝ E) 2 v Ω'' := by
    refine ⟨hv_memLp_Ω'', ?_⟩
    intro i
    exact ⟨D.weakPartial i, h_dwp_memLp_Ω'' i, h_dwp_weak_v_Ω'' i⟩
  have hwp_i_memW1p_Ω'' : ∀ i,
      Sobolev.Euclidean.MemW1p (d := Module.finrank ℝ E) 2 (D.weakPartial i) Ω'' := by
    intro i
    refine ⟨h_dwp_memLp_Ω'' i, ?_⟩
    intro k
    obtain ⟨g_ik, hg_ik_memLp, hg_ik_partial, _hg_ik_norm⟩ := h_h2 i k
    exact ⟨g_ik, hg_ik_memLp, hg_ik_partial⟩
  have hv_memWkp_two_Ω'' :
      Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2 v Ω'' := by
    refine ⟨hv_memW1p_Ω'', ?_⟩
    intro i
    have h_chosen_partial : Sobolev.Euclidean.HasWeakPartialDeriv
        (d := Module.finrank ℝ E) i
        (Sobolev.Euclidean.chosenWeakPartialOrZero
          2 i v Ω'') v Ω'' :=
      Sobolev.Euclidean.chosenWeakPartialOrZero_isWeakPartial_of_mem
        hv_memW1p_Ω'' i
    have h_chosen_local : MeasureTheory.LocallyIntegrable
        (Sobolev.Euclidean.chosenWeakPartialOrZero
          2 i v Ω'') (volume.restrict Ω'') :=
      (Sobolev.Euclidean.chosenWeakPartialOrZero_memLp_of_mem
        hv_memW1p_Ω'' i).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have h_dwp_local : MeasureTheory.LocallyIntegrable (D.weakPartial i)
        (volume.restrict Ω'') :=
      (h_dwp_memLp_Ω'' i).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have h_ae : Sobolev.Euclidean.chosenWeakPartialOrZero
        2 i v Ω'' =ᵐ[volume.restrict Ω''] D.weakPartial i :=
      Sobolev.Euclidean.HasWeakPartialDeriv.ae_eq hΩ''_open h_chosen_partial
        (h_dwp_weak_v_Ω'' i) h_chosen_local h_dwp_local
    rw [Sobolev.Euclidean.MemWkp.one_iff_memW1p]
    exact (Sobolev.Euclidean.MemW1p_congr_ae
      h_ae.symm).mp (hwp_i_memW1p_Ω'' i)
  have hv_memWkp_two_chart :
      Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2 v (chartTargetEuclid (I := I) (M := M) α) :=
    Sobolev.Euclidean.MemWkp.extend_zero
      (k := 2) (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      hΩ''_open h_chart_open hΩ''_in_chart hv_memWkp_two_Ω'' h_tsupp_v_sub_Ω''
      hv_compactSupport
  exact (Sobolev.Euclidean.MemWkp_congr_ae
    (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_chart_open
    h_v_eq_f_ae).mp hv_memWkp_two_chart

theorem laplacianDomain_memWkpChart_two
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    Sobolev.Chart.MemWkpChart
      (I := I) (M := M) 2 2
      ((h1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
    Sobolev.Chart.wkpNormChart
      (I := I) (M := M) 2 2
      ((h1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤ := by
  have h_mem : Sobolev.Chart.MemWkpChart
      (I := I) (M := M) 2 2
      ((h1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
    fun α => chartPushed_memWkp_two_of_laplacianDomain (I := I) (M := M) g hu_h α
  exact ⟨h_mem,
    Sobolev.Chart.wkpNormChart_lt_top_of_memWkpChart
      (I := I) (M := M) (k := 2) (p := 2) (by norm_num) h_mem⟩

end Laplacian
end Analysis
end CalabiYau
