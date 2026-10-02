module

public import CalabiYau.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplFromDomainPow

/-!
# Decomposition of the base chart forcing

`leibnizCompensatedSource = ρ_α · (u - laplacianOp u) - 2⟨∇ρ_α, ∇u⟩ - (Δρ_α) u`, and
`u - laplacianOp u` is `laplacianDomain.preimage u`. So the raw chart forcing is the
POU-pushed preimage plus the raw residual.

Port target: DifferentialGeometry at `7a48598d35109aa99d1cc678e2724c213cdf4ff3`,
`Iterated/BaseFChart/PolymorphicRegularity.lean` lines 1039–1255
(`base_f_chart_ae_eq_piecePreimage_add_residual`), stated for `laplacianDomain`.
The existing `base_f_chart_ae_eq_piecePreimage_add_residual_chartPulled_on_vol`
(`DiffChart/ResidualRegularity/BilinearH1ComplFromDomainPow.lean`) is the same identity
under `laplacianDomainPow 2`.
-/

@[expose] public section

noncomputable section
open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace CalabiYau.PoissonDomainRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
open CalabiYau.RiemannianVolume CalabiYau.Analysis.Laplacian Sobolev.Chart Sobolev.Euclidean
open CalabiYau.Laplacian.MetricExtension hiding chartTargetEuclid chartTargetEuclid_isOpen
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.LaplacianDomainChartData
open CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
variable [I.Boundaryless]

variable [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
/-- The base chart forcing is the POU-pushed resolvent preimage plus the raw residual. -/
private noncomputable def baseForcingSmoothMulLpRhoPreimage
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
    (laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_h⟩)

section

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
private lemma baseForcingLeibnizDecomp
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    leibnizCompensatedSource (I := I) (M := M) g α u_h hu_h =
      baseForcingSmoothMulLpRhoPreimage (I := I) (M := M) g α hu_h +
        fHLeibnizResidualLp (I := I) (M := M) g α u_h := by
  classical
  unfold baseForcingSmoothMulLpRhoPreimage fHLeibnizResidualLp
  rw [fHLeibniz_def]
  have h_diff_eq :
      h1ComplToLp (I := I) (M := M) g u_h -
        laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩ =
      laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_h⟩ := by
    rw [laplacianOp_apply]
    abel
  rw [h_diff_eq]
  abel

private lemma baseForcingRawAdd
    (g : SmoothRiemannianMetric I M) (α : M)
    (F G : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ((chartPushedRawLpFromLp (I := I) (M := M) g α (F + G) :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ)
      =ᵐ[(chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      (fun y => ((chartPushedRawLpFromLp (I := I) (M := M) g α F :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y +
        ((chartPushedRawLpFromLp (I := I) (M := M) g α G :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) := by
  classical
  have h_FG_coeFn := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α (F + G)
  have h_F_coeFn := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α F
  have h_G_coeFn := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α G
  set sumFun : M → ℝ := fun x => ((F : Lp ℝ 2 _) : M → ℝ) x + ((G : Lp ℝ 2 _) : M → ℝ) x
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
      chartPushedRaw (I := I) α ((F + G : Lp ℝ 2 _) : M → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      chartPushedRaw (I := I) α sumFun :=
    chartPushedRaw_aeEq_of_aeEq (I := I) (M := M) g α h_FG_meas hsum_meas h_sum_coe
  have h_chartPushedRaw_sum_pointwise : ∀ y : EuclN,
      chartPushedRaw (I := I) α sumFun y =
        chartPushedRaw (I := I) α ((F : Lp ℝ 2 _) : M → ℝ) y +
        chartPushedRaw (I := I) α ((G : Lp ℝ 2 _) : M → ℝ) y := by
    intro y
    by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
    · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) (α := α) sumFun hy,
        chartPushedRaw_apply_of_mem (I := I) (M := M) (α := α) ((F : Lp ℝ 2 _) : M → ℝ) hy,
        chartPushedRaw_apply_of_mem (I := I) (M := M) (α := α) ((G : Lp ℝ 2 _) : M → ℝ) hy]
    · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) (α := α) sumFun hy,
        chartPushedRaw_apply_of_notMem (I := I) (M := M) (α := α) ((F : Lp ℝ 2 _) : M → ℝ) hy,
        chartPushedRaw_apply_of_notMem (I := I) (M := M) (α := α) ((G : Lp ℝ 2 _) : M → ℝ) hy]
      ring
  filter_upwards [h_FG_coeFn, h_F_coeFn, h_G_coeFn, h_chartPushedRaw_FG]
    with y hy_FG hy_F hy_G hy_chart
  rw [hy_FG, hy_chart, h_chartPushedRaw_sum_pointwise y]
  rw [← hy_F, ← hy_G]

private lemma baseForcingPreimagePush
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    ((chartPushedRawLpFromLp (I := I) (M := M) g α
        (baseForcingSmoothMulLpRhoPreimage (I := I) (M := M) g α hu_h) :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ)
      =ᵐ[(chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      (fun y => chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_h⟩ :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) y) := by
  classical
  have h_coeFn := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α
    (baseForcingSmoothMulLpRhoPreimage (I := I) (M := M) g α hu_h)
  have h_mul_ae : (baseForcingSmoothMulLpRhoPreimage (I := I) (M := M) g α hu_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x *
        ((laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_h⟩ :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x) := by
    unfold baseForcingSmoothMulLpRhoPreimage
    exact smoothMulLp_apply_coeFn (I := I) (M := M) g _ _
  have h_mul_meas : Measurable ((baseForcingSmoothMulLpRhoPreimage
      (I := I) (M := M) g α hu_h : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
    (Lp.stronglyMeasurable _).measurable
  have h_prod_meas : Measurable (fun x : M =>
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x *
        ((laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_h⟩ :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x) := by
    refine Measurable.mul ?_ ?_
    · exact ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff.continuous).measurable
    · exact (Lp.stronglyMeasurable _).measurable
  have h_raw_ae : chartPushedRaw (I := I) α
        ((baseForcingSmoothMulLpRhoPreimage (I := I) (M := M) g α hu_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      chartPushedRaw (I := I) α (fun x : M =>
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x *
          ((laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_h⟩ :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x) :=
    chartPushedRaw_aeEq_of_aeEq (I := I) (M := M) g α h_mul_meas h_prod_meas h_mul_ae
  have h_target_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  have h_weighted_restrict_self : ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α)),
      y ∈ chartTargetEuclid (I := I) (M := M) α := by
    rw [ae_restrict_iff' h_target_meas]
    exact Filter.Eventually.of_forall (fun _ h => h)
  filter_upwards [h_coeFn, h_raw_ae, h_weighted_restrict_self] with y hy_coe hy_raw hy_in
  rw [hy_coe, hy_raw]
  exact (chartPushed_eq_chartPushedRaw_pou_mul_on_target (I := I) (M := M)
    (chartAtlasPOU I M) α
    ((laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_h⟩ :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) hy_in).symm

end

variable [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma baseForcingWeightedDecomp
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α hu_h).fChart
      =ᵐ[(chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      (fun y => chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_h⟩ :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) y +
        fChartResidual (I := I) (M := M) g α u_h y) := by
  classical
  have h_base_def := chartBilinearH1ComplData_of_laplacianDomain_f_chart_def
    (I := I) (M := M) g α hu_h
  have h_decomp := baseForcingLeibnizDecomp (I := I) (M := M) g α hu_h
  have h_add := baseForcingRawAdd (I := I) (M := M) g α
    (baseForcingSmoothMulLpRhoPreimage (I := I) (M := M) g α hu_h)
    (fHLeibnizResidualLp (I := I) (M := M) g α u_h)
  have h_push := baseForcingPreimagePush (I := I) (M := M) g α hu_h
  rw [h_base_def, h_decomp]
  filter_upwards [h_add, h_push] with y hy_add hy_push
  rw [hy_add, hy_push]
  rfl

private lemma baseForcingVolumeAbs
    (g : SmoothRiemannianMetric I M) (α : M) :
    (volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α) ≪
      (chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α) := by
  intro A hA
  have h_target_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  unfold chartPulledWeightedMeasure at hA
  rw [show ((volume : Measure EuclN).withDensity
      (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))).restrict
      (chartTargetEuclid (I := I) (M := M) α) =
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)).withDensity
        (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
    from MeasureTheory.restrict_withDensity h_target_meas _] at hA
  rw [MeasureTheory.withDensity_apply_eq_zero'
    (μ := (volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α))
    (f := fun y : EuclN => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
    (ENNReal.measurable_ofReal.comp_aemeasurable
      ((densityOnEuclid_continuousOn (I := I) g α).aemeasurable h_target_meas))] at hA
  rw [Measure.restrict_apply' h_target_meas]
  rw [Measure.restrict_apply' h_target_meas] at hA
  refine MeasureTheory.measure_mono_null ?_ hA
  intro y ⟨hy_A, hy_chart⟩
  refine ⟨⟨?_, hy_A⟩, hy_chart⟩
  have h_pos : 0 < densityOnEuclid (I := I) g α y := densityOnEuclid_pos (I := I) g α hy_chart
  exact (ENNReal.ofReal_pos.mpr h_pos).ne'

variable [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem baseFChart_ae_eq_preimage_add_residual
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α hu_h).fChart
      =ᵐ[(volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)]
      (fun y => chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_h⟩ :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) y +
        fChartResidual (I := I) (M := M) g α u_h y) := by
  exact (baseForcingVolumeAbs (I := I) (M := M) g α).ae_le
    (baseForcingWeightedDecomp (I := I) (M := M) g α hu_h)

end CalabiYau.PoissonDomainRegularity
