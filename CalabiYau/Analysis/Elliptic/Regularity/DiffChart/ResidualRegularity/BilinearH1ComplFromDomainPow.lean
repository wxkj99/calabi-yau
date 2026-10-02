-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/DiffChart/ResidualRegularity/BilinearH1ComplFromDomainPow.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.DiffChart.Differentiated.BilinearH1Compl
public import CalabiYau.Analysis.Elliptic.Regularity.LaplacianDomain.Chart.VariationalData
public import CalabiYau.Analysis.Elliptic.Regularity.Iterated.Bootstrap.H2RegularitySuccessor
public import CalabiYau.Analysis.Sobolev.Chart.Defs
public import CalabiYau.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev
public import CalabiYau.Analysis.Elliptic.Regularity.LaplacianDomain.Variational.IntegralIdentity

@[expose] public section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace CalabiYau
namespace Analysis
namespace Laplacian
namespace DiffChartBilinearH1Compl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Laplacian.MetricExtension
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.ChartPushedWeakPartialOnVolume
open CalabiYau.Analysis.Laplacian.H1ComplGradientH1LipschitzBound
open CalabiYau.Analysis.Laplacian.H1ComplWeakPartialLimit
open CalabiYau.Analysis.Laplacian.LaplacianDomainChartData
open CalabiYau.Analysis.Laplacian.LaplacianDomainVariationalIdentityIntegralForm
open Sobolev.NirenbergEuclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma locallyIntegrable_of_memLp_two_compact_open_subset
    (K Ω' : Set EuclN) (_hK_compact : IsCompact K) (hΩ'_subset_K : Ω' ⊆ K)
    (hΩ'_meas : MeasurableSet Ω')
    {f : EuclN → ℝ}
    (hf_memLp_K : MemLp f 2 ((volume : Measure EuclN).restrict K)) :
    LocallyIntegrable f ((volume : Measure EuclN).restrict Ω') := by
  have h_eq : ((volume : Measure EuclN).restrict K).restrict Ω' =
      (volume : Measure EuclN).restrict Ω' := by
    rw [Measure.restrict_restrict hΩ'_meas]
    congr 1
    exact Set.inter_eq_self_of_subset_left hΩ'_subset_K
  have hf_memLp_Ω' : MemLp f 2 ((volume : Measure EuclN).restrict Ω') := by
    rw [← h_eq]; exact hf_memLp_K.restrict Ω'
  exact hf_memLp_Ω'.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)

noncomputable def fChartPiecePreimage
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) : EuclN → ℝ :=
  Sobolev.Chart.chartPushed
    (I := I) (M := M) (chartAtlasPOU I M) α
    ((laplacianDomain.preimage (I := I) (M := M) g
        ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h⟩ :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)

private noncomputable def smoothMulLpRhoPreimage
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
    (laplacianDomain.preimage (I := I) (M := M) g
      ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h⟩)

noncomputable def fHLeibnizResidualLp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  -((2 : ℝ) • gradInnerCLM (I := I) (M := M) g
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h) -
    smoothMulLp (I := I) (M := M) g
      (laplacianOfChartPOU (I := I) (M := M) g α)
      (h1ComplToLp (I := I) (M := M) g u_h)

omit [NeZero (Module.finrank ℝ E)] in
private lemma fHLeibniz_eq_piecePreimage_add_residual
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    leibnizCompensatedSource (I := I) (M := M) g α u_h
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h) =
      smoothMulLpRhoPreimage (I := I) (M := M) g α hu_h +
        fHLeibnizResidualLp (I := I) (M := M) g α u_h := by
  classical
  unfold smoothMulLpRhoPreimage fHLeibnizResidualLp
  rw [fHLeibniz_def]
  have h_diff_eq :
      h1ComplToLp (I := I) (M := M) g u_h -
        laplacianOp (I := I) (M := M) g
          ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h⟩ =
      laplacianDomain.preimage (I := I) (M := M) g
        ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h⟩ := by
    rw [laplacianOp_apply]
    abel
  rw [h_diff_eq]
  abel

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartPushedRawLpFromLp_coeFn_add
    (g : SmoothRiemannianMetric I M) (α : M)
    (F G : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ((chartPushedRawLpFromLp (I := I) (M := M) g α (F + G) :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α))) : EuclN → ℝ)
      =ᵐ[(chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)]
      (fun y => ((chartPushedRawLpFromLp (I := I) (M := M) g α F :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α))) : EuclN → ℝ) y +
        ((chartPushedRawLpFromLp (I := I) (M := M) g α G :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α))) : EuclN → ℝ) y) := by
  classical
  have h_FG_coeFn := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α (F + G)
  have h_F_coeFn := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α F
  have h_G_coeFn := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α G
  set sumFun : M → ℝ := fun x =>
    ((F : Lp ℝ 2 _) : M → ℝ) x + ((G : Lp ℝ 2 _) : M → ℝ) x with hsumFun_def
  have h_sum_coe : ((F + G : Lp ℝ 2 _) : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g] sumFun :=
    MeasureTheory.Lp.coeFn_add F G
  have h_FG_meas : Measurable ((F + G : Lp ℝ 2 _) : M → ℝ) :=
    (Lp.stronglyMeasurable (F + G)).measurable
  have hF_meas : Measurable ((F : Lp ℝ 2 _) : M → ℝ) :=
    (Lp.stronglyMeasurable F).measurable
  have hG_meas : Measurable ((G : Lp ℝ 2 _) : M → ℝ) :=
    (Lp.stronglyMeasurable G).measurable
  have hsum_meas : Measurable sumFun := hF_meas.add hG_meas
  have h_chartPushedRaw_FG :
      Sobolev.Chart.chartPushedRaw (I := I) α
        ((F + G : Lp ℝ 2 _) : M → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)]
      Sobolev.Chart.chartPushedRaw (I := I) α
        sumFun :=
    CalabiYau.Analysis.Laplacian.LaplacianDomainChartData.chartPushedRaw_aeEq_of_aeEq
      (I := I) (M := M) g α h_FG_meas hsum_meas h_sum_coe
  have h_chartPushedRaw_sum_pointwise :
      ∀ y : EuclN,
        Sobolev.Chart.chartPushedRaw (I := I) α
          sumFun y =
        Sobolev.Chart.chartPushedRaw (I := I) α
          ((F : Lp ℝ 2 _) : M → ℝ) y +
        Sobolev.Chart.chartPushedRaw (I := I) α
          ((G : Lp ℝ 2 _) : M → ℝ) y := by
    intro y
    by_cases hy : y ∈ Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α
    · rw [Sobolev.Chart.chartPushedRaw_apply_of_mem
        (I := I) (M := M) (α := α) sumFun hy,
        Sobolev.Chart.chartPushedRaw_apply_of_mem
          (I := I) (M := M) (α := α) ((F : Lp ℝ 2 _) : M → ℝ) hy,
        Sobolev.Chart.chartPushedRaw_apply_of_mem
          (I := I) (M := M) (α := α) ((G : Lp ℝ 2 _) : M → ℝ) hy]
    · rw [Sobolev.Chart.chartPushedRaw_apply_of_notMem
        (I := I) (M := M) (α := α) sumFun hy,
        Sobolev.Chart.chartPushedRaw_apply_of_notMem
          (I := I) (M := M) (α := α) ((F : Lp ℝ 2 _) : M → ℝ) hy,
        Sobolev.Chart.chartPushedRaw_apply_of_notMem
          (I := I) (M := M) (α := α) ((G : Lp ℝ 2 _) : M → ℝ) hy]
      ring
  filter_upwards [h_FG_coeFn, h_F_coeFn, h_G_coeFn, h_chartPushedRaw_FG]
    with y hy_FG hy_F hy_G hy_chart
  rw [hy_FG, hy_chart, h_chartPushedRaw_sum_pointwise y]
  rw [← hy_F, ← hy_G]

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartPushedRawLpFromLp_smoothMulLpRhoPreimage_coeFn_aeEq
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    ((chartPushedRawLpFromLp (I := I) (M := M) g α
        (smoothMulLpRhoPreimage (I := I) (M := M) g α hu_h) :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α))) : EuclN → ℝ)
      =ᵐ[(chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)]
      fChartPiecePreimage (I := I) (M := M) g α hu_h := by
  classical
  have h_coeFn := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α
    (smoothMulLpRhoPreimage (I := I) (M := M) g α hu_h)
  have h_smoothMulLp_ae : (smoothMulLpRhoPreimage (I := I) (M := M) g α hu_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x *
        ((laplacianDomain.preimage (I := I) (M := M) g
          ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h⟩ :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x) := by
    unfold smoothMulLpRhoPreimage
    exact smoothMulLp_apply_coeFn (I := I) (M := M) g _ _
  have h_smoothMul_meas :
      Measurable ((smoothMulLpRhoPreimage (I := I) (M := M) g α hu_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
    (Lp.stronglyMeasurable _).measurable
  have h_prod_meas :
      Measurable (fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x *
        ((laplacianDomain.preimage (I := I) (M := M) g
          ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h⟩ :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x) := by
    refine Measurable.mul ?_ ?_
    · exact ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff.continuous).measurable
    · exact (Lp.stronglyMeasurable _).measurable
  have h_chartPushedRaw_ae :
      Sobolev.Chart.chartPushedRaw (I := I) α
        ((smoothMulLpRhoPreimage (I := I) (M := M) g α hu_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)]
      Sobolev.Chart.chartPushedRaw (I := I) α
        (fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x *
          ((laplacianDomain.preimage (I := I) (M := M) g
            ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h⟩ :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x) :=
    CalabiYau.Analysis.Laplacian.LaplacianDomainChartData.chartPushedRaw_aeEq_of_aeEq
      (I := I) (M := M) g α h_smoothMul_meas h_prod_meas h_smoothMulLp_ae
  have h_chartTarget_meas : MeasurableSet
      (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
    (Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α).measurableSet
  have h_weighted_restrict_self :
      ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)),
      y ∈ Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α := by
    rw [ae_restrict_iff' h_chartTarget_meas]
    exact Filter.Eventually.of_forall (fun _ h => h)
  filter_upwards [h_coeFn, h_chartPushedRaw_ae, h_weighted_restrict_self]
    with y hy_coeFn hy_chart hy_in
  rw [hy_coeFn, hy_chart]
  unfold fChartPiecePreimage
  exact (Sobolev.Chart.chartPushed_eq_chartPushedRaw_pou_mul_on_target
    (I := I) (M := M) (chartAtlasPOU I M) α
    ((laplacianDomain.preimage (I := I) (M := M) g
      ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h⟩ :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) hy_in).symm

private lemma base_f_chart_ae_eq_piecePreimage_add_residual_chartPulled
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h)).fChart
      =ᵐ[(chartPulledWeightedMeasure (I := I) g α).restrict
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)]
      (fun y => fChartPiecePreimage (I := I) (M := M) g α hu_h y +
        ((chartPushedRawLpFromLp (I := I) (M := M) g α
            (fHLeibnizResidualLp (I := I) (M := M) g α u_h) :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (Sobolev.Chart.chartTargetEuclid
              (I := I) (M := M) α))) : EuclN → ℝ) y) := by
  classical
  have h_base_def := chartBilinearH1ComplData_of_laplacianDomain_f_chart_def
    (I := I) (M := M) g α
    (laplacianDomainPow_succ_subset_laplacianDomain
      (I := I) (M := M) g 1 hu_h)
  have h_fHLeibniz_decomp := fHLeibniz_eq_piecePreimage_add_residual
    (I := I) (M := M) g α hu_h
  have h_chartPushedRaw_add_ae :=
    chartPushedRawLpFromLp_coeFn_add (I := I) (M := M) g α
      (smoothMulLpRhoPreimage (I := I) (M := M) g α hu_h)
      (fHLeibnizResidualLp (I := I) (M := M) g α u_h)
  have h_piece1 := chartPushedRawLpFromLp_smoothMulLpRhoPreimage_coeFn_aeEq
    (I := I) (M := M) g α hu_h
  rw [h_base_def, h_fHLeibniz_decomp]
  filter_upwards [h_chartPushedRaw_add_ae, h_piece1] with y hy_add hy_piece1
  rw [hy_add, hy_piece1]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma vol_abs_chartPulledWeighted_on_chartTarget
    (g : SmoothRiemannianMetric I M) (α : M) :
    (volume : Measure EuclN).restrict
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) ≪
      (chartPulledWeightedMeasure (I := I) g α).restrict
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) := by
  intro A hA
  have h_chartTarget_meas : MeasurableSet
      (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
    (Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α).measurableSet
  unfold chartPulledWeightedMeasure at hA
  rw [show ((volume : Measure EuclN).withDensity
      (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))).restrict
      (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) =
      ((volume : Measure EuclN).restrict
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)).withDensity
        (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
    from MeasureTheory.restrict_withDensity h_chartTarget_meas _] at hA
  rw [MeasureTheory.withDensity_apply_eq_zero'
    (μ := (volume : Measure EuclN).restrict
      (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α))
    (f := fun y : EuclN => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
    (ENNReal.measurable_ofReal.comp_aemeasurable
      ((densityOnEuclid_continuousOn (I := I) g α).aemeasurable h_chartTarget_meas))]
    at hA
  rw [Measure.restrict_apply' h_chartTarget_meas]
  rw [Measure.restrict_apply' h_chartTarget_meas] at hA
  refine MeasureTheory.measure_mono_null ?_ hA
  intro y ⟨hy_A, hy_chart⟩
  refine ⟨⟨?_, hy_A⟩, hy_chart⟩
  have h_pos : 0 < densityOnEuclid (I := I) g α y :=
    densityOnEuclid_pos (I := I) g α hy_chart
  exact (ENNReal.ofReal_pos.mpr h_pos).ne'

lemma base_f_chart_ae_eq_piecePreimage_add_residual_chartPulled_on_vol
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h)).fChart
      =ᵐ[(volume : Measure EuclN).restrict
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)]
      (fun y => fChartPiecePreimage (I := I) (M := M) g α hu_h y +
        ((chartPushedRawLpFromLp (I := I) (M := M) g α
            (fHLeibnizResidualLp (I := I) (M := M) g α u_h) :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (Sobolev.Chart.chartTargetEuclid
              (I := I) (M := M) α))) : EuclN → ℝ) y) := by
  exact (vol_abs_chartPulledWeighted_on_chartTarget (I := I) (M := M) g α).ae_le
    (base_f_chart_ae_eq_piecePreimage_add_residual_chartPulled
      (I := I) (M := M) g α hu_h)

noncomputable def fChartResidual
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) : EuclN → ℝ :=
  ((chartPushedRawLpFromLp (I := I) (M := M) g α
      (fHLeibnizResidualLp (I := I) (M := M) g α u_h) :
    Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
      (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α))) : EuclN → ℝ)

end DiffChartBilinearH1Compl
end Laplacian
end Analysis
end CalabiYau

end
