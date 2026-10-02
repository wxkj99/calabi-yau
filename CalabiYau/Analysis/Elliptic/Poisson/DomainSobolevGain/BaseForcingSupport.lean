module

public import CalabiYau.Analysis.Elliptic.Regularity.LaplacianDomain.Chart.VariationalData
public import CalabiYau.Analysis.Sobolev.Approximation.Density.Smooth

/-!
# Support of the base chart forcing

Every term of `leibnizCompensatedSource` carries `ρ_α`, `∇ρ_α` or `Δρ_α`, so its raw chart
push vanishes off the chart image of `tsupport ρ_α`.

Port target: DifferentialGeometry at `7a48598d35109aa99d1cc678e2724c213cdf4ff3`,
`Analysis/Elliptic/Regularity/DiffChart/Differentiated/CanonicalDerivedData.lean`,
`base_f_chart_ae_zero_off_chart_image_pou_tsupport` (line 441 onward; its `K_α` is
`chartImagePOUTsupport`).
-/

@[expose] public section

noncomputable section
open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace CalabiYau.PoissonDomainRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
open CalabiYau.RiemannianVolume CalabiYau.Analysis.Laplacian Sobolev.Chart Sobolev.Euclidean
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.LaplacianDomainChartData
open CalabiYau.Analysis.Laplacian.ChartBilinearH1ComplFromDom
open CalabiYau.Laplacian.MetricExtension hiding chartTargetEuclid chartTargetEuclid_isOpen
open CalabiYau.Analysis.Laplacian.LaplacianDomainVariationalIdentityIntegralForm
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
variable [T2Space M]

variable [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private abbrev K_α (α : M) : Set EuclN :=
  chartImagePOUTsupport (I := I) (M := M) α

variable [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M]  [T2Space M] [SigmaCompactSpace M] in
private lemma K_α_compact (α : M) : IsCompact (K_α (I := I) (M := M) α) :=
  chartImagePOUTsupport_isCompact (I := I) (M := M) α

variable [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M]  [T2Space M] [SigmaCompactSpace M] in
private lemma K_α_meas (α : M) : MeasurableSet (K_α (I := I) (M := M) α) :=
  (K_α_compact (I := I) (M := M) α).isClosed.measurableSet

variable [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartTarget_diff_K_α_isOpen (α : M) :
    IsOpen (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α) :=
  (chartTargetEuclid_isOpen (I := I) (M := M) α).sdiff
    (K_α_compact (I := I) (M := M) α).isClosed

variable [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] in
private lemma chartTarget_diff_K_α_subset_target (α : M) :
    chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α := fun _ hy => hy.1

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma weakPartial_ae_zero_on_open_of_ae_zero_on_open
    {Ω U : Set EuclN} (hΩ_open : IsOpen Ω) (hU_open : IsOpen U)
    (hU_sub : U ⊆ Ω)
    {f w : EuclN → ℝ}
    (i : Fin (Module.finrank ℝ E))
    (hw_isWeak : Sobolev.Euclidean.HasWeakPartialDeriv (d := Module.finrank ℝ E) i w f Ω)
    (hw_li : LocallyIntegrableOn w U (volume : Measure EuclN))
    (hf_ae_zero : ∀ᵐ y ∂((volume : Measure EuclN).restrict U), f y = 0) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict U), w y = 0 := by
  classical
  have hU_meas : MeasurableSet U := hU_open.measurableSet
  have hf_ae_zero_vol : ∀ᵐ y ∂(volume : Measure EuclN), y ∈ U → f y = 0 := by
    rw [← ae_restrict_iff' hU_meas]; exact hf_ae_zero
  have h_target : ∀ᵐ y ∂(volume : Measure EuclN), y ∈ U → w y = 0 := by
    apply hU_open.ae_eq_zero_of_integral_contDiff_smul_eq_zero hw_li
    intro ψ hψ_smooth hψ_cs hψ_support
    have hψ_support_Ω : tsupport ψ ⊆ Ω := hψ_support.trans hU_sub
    have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
    have h_weak := hw_isWeak ψ hψ_smooth hψ_cs hψ_support_Ω
    have h_f_support_ae : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
        f y * (fderiv ℝ ψ y) (EuclideanSpace.single i 1) = 0 := by
      refine (ae_restrict_iff' hΩ_meas).mpr ?_
      filter_upwards [hf_ae_zero_vol] with y hy _hyΩ
      by_cases hy_U : y ∈ U
      · rw [hy hy_U]; ring
      · have h_compl_open : IsOpen ((tsupport ψ)ᶜ) :=
          (isClosed_tsupport _).isOpen_compl
        have h_y_not_support : y ∉ tsupport ψ := fun h => hy_U (hψ_support h)
        have h_zero_neighborhood : ∀ᶠ z in 𝓝 y, ψ z = 0 := by
          filter_upwards [h_compl_open.mem_nhds h_y_not_support] with z hz
          exact image_eq_zero_of_notMem_tsupport hz
        have h_fderiv_zero : fderiv ℝ ψ y = 0 := by
          have h_ev_const : ψ =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := h_zero_neighborhood
          rw [Filter.EventuallyEq.fderiv_eq h_ev_const]; simp
        rw [h_fderiv_zero]; simp
    have h_zero_lhs :
        ∫ y in Ω, f y * (fderiv ℝ ψ y) (EuclideanSpace.single i 1)
          ∂(volume : Measure EuclN) = 0 := by
      rw [MeasureTheory.integral_congr_ae h_f_support_ae]; simp
    rw [h_zero_lhs] at h_weak
    have h_rhs_zero :
        ∫ y in Ω, w y * ψ y ∂(volume : Measure EuclN) = 0 := by linarith
    have h_vanish_off_Ω : ∀ x ∉ Ω, ψ x • w x = 0 := fun x hx => by
      have hx_support : x ∉ tsupport ψ := fun h => hx (hψ_support_Ω h)
      have hψ_x : ψ x = 0 := image_eq_zero_of_notMem_tsupport hx_support
      rw [hψ_x]; simp
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      h_vanish_off_Ω]
    refine (MeasureTheory.setIntegral_congr_fun hΩ_meas ?_).trans h_rhs_zero
    intro x _hxΩ; simp [smul_eq_mul, mul_comm]
  refine (ae_restrict_iff' hU_meas).mpr ?_
  filter_upwards [h_target] with y hy hy_U
  exact hy hy_U

variable [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] in
private lemma vol_restrict_complement_absCont_chartTarget (α : M) :
    (volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α) ≪
      (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α) :=
  MeasureTheory.Measure.absolutelyContinuous_of_le
    (MeasureTheory.Measure.restrict_mono
      (chartTarget_diff_K_α_subset_target (I := I) (M := M) α) le_rfl)

variable [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma base_u_chart_aeEq_chartPushed
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
        hu_h).uChart =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ) := by
  classical
  have h_chartTarget_meas : MeasurableSet
      (chartTargetEuclid (I := I) (M := M) α) :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
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
      from MeasureTheory.restrict_withDensity h_chartTarget_meas _] at hA
    rw [MeasureTheory.withDensity_apply_eq_zero'
      (μ := (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α))
      (f := fun y : EuclN => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
      (ENNReal.measurable_ofReal.comp_aemeasurable
        ((densityOnEuclid_continuousOn (I := I) g α).aemeasurable
          h_chartTarget_meas))] at hA
    rw [Measure.restrict_apply' h_chartTarget_meas]
    rw [Measure.restrict_apply' h_chartTarget_meas] at hA
    refine MeasureTheory.measure_mono_null ?_ hA
    intro y ⟨hy_A, hy_chart⟩
    refine ⟨⟨?_, hy_A⟩, hy_chart⟩
    have h_pos : 0 < densityOnEuclid (I := I) g α y :=
      densityOnEuclid_pos (I := I) g α hy_chart
    exact (ENNReal.ofReal_pos.mpr h_pos).ne'
  have h_coeFn := chartPushedLpFromLp_coeFn (I := I) (M := M) g α
    (h1ComplToLp (I := I) (M := M) g u_h)
  exact h_v_abs_w.ae_le h_coeFn

variable [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma base_u_chart_ae_zero_off_K_α
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
        hu_h).uChart y = 0 := by
  classical
  have h_aeEq := base_u_chart_aeEq_chartPushed (I := I) (M := M) g α hu_h
  have h_abs := vol_restrict_complement_absCont_chartTarget
    (I := I) (M := M) (α := α)
  have h_aeEq_restrict := h_abs.ae_le h_aeEq
  have h_diff_meas : MeasurableSet
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α) :=
    (chartTarget_diff_K_α_isOpen (I := I) (M := M) α).measurableSet
  refine (ae_restrict_iff' h_diff_meas).mpr ?_
  filter_upwards [(ae_restrict_iff' h_diff_meas).mp h_aeEq_restrict] with y hy hy_diff
  rw [hy hy_diff]
  exact chartPushed_eq_zero_off_chartImagePOUTsupport (I := I) (M := M) α _
    hy_diff.1 hy_diff.2

variable [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma locallyIntegrableOn_of_locally_memLp_two
    (α : M) {f : EuclN → ℝ}
    (hf : ∀ K' : Set EuclN, IsCompact K' →
      K' ⊆ chartTargetEuclid (I := I) (M := M) α →
      MemLp f 2 ((volume : Measure EuclN).restrict K')) :
    LocallyIntegrableOn f
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)
      (volume : Measure EuclN) := by
  classical
  intro x hx
  have hΩ_open := chartTarget_diff_K_α_isOpen (I := I) (M := M) α
  obtain ⟨r, hr_pos, hr_subset⟩ := Metric.isOpen_iff.mp hΩ_open x hx
  set B : Set EuclN := Metric.closedBall x (r / 2)
  have hB_compact : IsCompact B := isCompact_closedBall _ _
  have hB_subset : B ⊆ chartTargetEuclid (I := I) (M := M) α \
      K_α (I := I) (M := M) α := by
    intro y hy; apply hr_subset
    rw [Metric.mem_ball]; rw [Metric.mem_closedBall] at hy; linarith [hr_pos]
  have hB_subset_chart : B ⊆ chartTargetEuclid (I := I) (M := M) α :=
    fun y hy => (hB_subset hy).1
  have h_memLp := hf B hB_compact hB_subset_chart
  have hB_finite : (volume : Measure EuclN) B < ⊤ := hB_compact.measure_lt_top
  have : IsFiniteMeasure ((volume : Measure EuclN).restrict B) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact hB_finite
  have h_int : IntegrableOn f B (volume : Measure EuclN) :=
    h_memLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  refine ⟨B, ?_, h_int⟩
  refine Filter.mem_inf_of_left ?_
  apply Filter.mem_of_superset (Metric.ball_mem_nhds x
    (by linarith : 0 < r / 2))
  exact Metric.ball_subset_closedBall

variable [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma base_weak_partial_ae_zero_off_chart_image_pou_tsupport
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i : Fin (Module.finrank ℝ E)) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)),
      (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
        hu_h).weakPartial i y = 0 := by
  classical
  set D := chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α hu_h
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hU_open := chartTarget_diff_K_α_isOpen (I := I) (M := M) α
  have hU_sub : chartTargetEuclid (I := I) (M := M) α \
      K_α (I := I) (M := M) α ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartTarget_diff_K_α_subset_target (I := I) (M := M) α
  have h_isWeak := D.weak_partial_isWeakPartial i
  have hw_li : LocallyIntegrableOn (D.weakPartial i)
      (chartTargetEuclid (I := I) (M := M) α \ K_α (I := I) (M := M) α)
      (volume : Measure EuclN) :=
    locallyIntegrableOn_of_locally_memLp_two (α := α) (f := D.weakPartial i)
      (fun K' hK' hK'_in => D.weak_partial_locally_memLp i K' hK' hK'_in)
  have hf_ae := base_u_chart_ae_zero_off_K_α (I := I) (M := M) g α hu_h
  exact weakPartial_ae_zero_on_open_of_ae_zero_on_open
    hΩ_open hU_open hU_sub (i := i) h_isWeak hw_li hf_ae

variable [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem continuousOn_memLp_top_compact_local {α β : Type*} [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α] [NormedAddCommGroup β] {f : α → β} {s : Set α} {μ : Measure α} (hf : ContinuousOn f s) (hs : IsCompact s) (hsm : MeasurableSet s) : MemLp f ∞ (μ.restrict s) := by
  obtain ⟨C, hC⟩ := hs.bddAbove_image hf.norm
  apply memLp_top_of_bound (hf.aestronglyMeasurable_of_subset_isCompact hs hsm Subset.rfl) C
  filter_upwards [ae_restrict_mem hsm] with x hx
  exact hC (mem_image_of_mem (fun y => ‖f y‖) hx)

variable [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [I.Boundaryless] [T2Space M] in
private lemma base_f_chart_locally_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp ((chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
        hu_h).fChart) 2
      ((volume : Measure EuclN).restrict K) := by
  set D := chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α hu_h
  have h_weighted := D.f_chart_memLp_weighted
  obtain ⟨c, _hc_pos, h_le⟩ :=
    volume_restrict_compact_le_chartPulledWeightedMeasure (I := I) (M := M)
      (g := g) (α := α) hK_compact hK_compact.isClosed.measurableSet hK_in
  have hc_ne_top : (ENNReal.ofReal c) ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have h_smul : MemLp D.fChart 2
      (ENNReal.ofReal c • ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))) :=
    h_weighted.smul_measure hc_ne_top
  exact h_smul.mono_measure h_le

variable [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
/-- The base chart forcing vanishes a.e. off the chart image of the POU support. -/
theorem baseFChart_ae_zero_off_chartImagePOUTsupport
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α hu_h).fChart
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ chartImagePOUTsupport (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  set D := chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α hu_h
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α
  set U : Set EuclN := Ω \ K_α (I := I) (M := M) α
  have hU_open := chartTarget_diff_K_α_isOpen (I := I) (M := M) α
  have hU_sub := chartTarget_diff_K_α_subset_target (I := I) (M := M) α
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have hU_meas : MeasurableSet U := hU_open.measurableSet
  have hK_meas : MeasurableSet (K_α (I := I) (M := M) α) :=
    K_α_meas (I := I) (M := M) α
  have h_fc_li : LocallyIntegrableOn D.fChart U
      (volume : Measure EuclN) :=
    locallyIntegrableOn_of_locally_memLp_two (α := α) (f := D.fChart)
      (fun K' hK' hK'_in => base_f_chart_locally_memLp (I := I) (M := M) g α
        hu_h hK' hK'_in)
  have h_density_contOn : ContinuousOn (densityOnEuclid (I := I) g α) Ω :=
    densityOnEuclid_continuousOn (I := I) g α
  have h_prod_localInt : LocallyIntegrableOn
      (fun y => densityOnEuclid (I := I) g α y * D.fChart y) U
      (volume : Measure EuclN) := by
    intro x hx
    obtain ⟨r, hr_pos, hr_subset⟩ := Metric.isOpen_iff.mp hU_open x hx
    set B : Set EuclN := Metric.closedBall x (r / 2)
    have hB_compact : IsCompact B := isCompact_closedBall _ _
    have hB_subset_U : B ⊆ U := by
      intro y hy; apply hr_subset
      rw [Metric.mem_ball]; rw [Metric.mem_closedBall] at hy; linarith [hr_pos]
    have hB_subset_Ω : B ⊆ Ω := fun y hy => hU_sub (hB_subset_U hy)
    have h_fchart_K_memLp := base_f_chart_locally_memLp (I := I) (M := M) g α
      hu_h hB_compact hB_subset_Ω
    have hB_meas : MeasurableSet B := hB_compact.isClosed.measurableSet
    have h_density_memLp_top := continuousOn_memLp_top_compact_local (μ := volume) (h_density_contOn.mono hB_subset_Ω) hB_compact hB_meas
    have h_prod_memLp : MemLp (fun y => densityOnEuclid (I := I) g α y *
        D.fChart y) 2 ((volume : Measure EuclN).restrict B) :=
      MemLp.mul' (p := ∞) (q := 2) (r := 2) h_fchart_K_memLp h_density_memLp_top
    have hB_finite : (volume : Measure EuclN) B < ⊤ := hB_compact.measure_lt_top
    have : IsFiniteMeasure ((volume : Measure EuclN).restrict B) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      exact hB_finite
    have h_int : IntegrableOn (fun y => densityOnEuclid (I := I) g α y *
        D.fChart y) B (volume : Measure EuclN) :=
      h_prod_memLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    refine ⟨B, ?_, h_int⟩
    refine Filter.mem_inf_of_left ?_
    apply Filter.mem_of_superset (Metric.ball_mem_nhds x
      (by linarith : 0 < r / 2))
    exact Metric.ball_subset_closedBall
  have h_zero_for_test : ∀ ψ : EuclN → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U →
      ∫ y, ψ y • (densityOnEuclid (I := I) g α y * D.fChart y)
        ∂(volume : Measure EuclN) = 0 := by
    intro ψ hψ_smooth hψ_cs hψ_support_U
    have hψ_support_chart : tsupport ψ ⊆ Ω := hψ_support_U.trans hU_sub
    have h_var := D.variational_identity ψ hψ_smooth hψ_cs hψ_support_chart
    change (∫ y in Ω,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              D.weakPartial i y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN)) +
      (∫ y in Ω,
        densityOnEuclid (I := I) g α y * D.uChart y * ψ y
        ∂(volume : Measure EuclN)) =
      ∫ y in Ω,
        densityOnEuclid (I := I) g α y * D.fChart y * ψ y
        ∂(volume : Measure EuclN) at h_var
    have h_principal_zero :
        ∫ y in Ω,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weakPartial i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN) = 0 := by
      have h_integrand_ae_zero :
          (fun y : EuclN => ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weakPartial i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) =ᵐ[
            (volume : Measure EuclN).restrict Ω]
            (fun _ : EuclN => (0 : ℝ)) := by
        refine (ae_restrict_iff' hΩ_meas).mpr ?_
        have h_wp_each : ∀ i : Fin (Module.finrank ℝ E),
            ∀ᵐ y ∂((volume : Measure EuclN).restrict U),
              D.weakPartial i y = 0 := fun i =>
          base_weak_partial_ae_zero_off_chart_image_pou_tsupport (I := I) (M := M) g α hu_h i
        have h_wp_all_vol : ∀ᵐ y ∂(volume : Measure EuclN),
            ∀ i : Fin (Module.finrank ℝ E),
              y ∈ U → D.weakPartial i y = 0 := by
          rw [ae_all_iff]; intro i
          rw [← ae_restrict_iff' hU_meas]
          exact h_wp_each i
        filter_upwards [h_wp_all_vol] with y hy _hyΩ
        by_cases hy_U : y ∈ U
        · refine Finset.sum_eq_zero ?_; intro i _
          refine Finset.sum_eq_zero ?_; intro j _
          rw [hy i hy_U]; ring
        · have h_y_not_in_support : y ∉ tsupport ψ := fun h => hy_U (hψ_support_U h)
          have h_compl_open : IsOpen (tsupport ψ)ᶜ :=
            (isClosed_tsupport _).isOpen_compl
          have h_zero_neighborhood : ∀ᶠ z in 𝓝 y, ψ z = 0 := by
            filter_upwards [h_compl_open.mem_nhds h_y_not_in_support] with z hz
            exact image_eq_zero_of_notMem_tsupport hz
          have h_fderiv_zero : fderiv ℝ ψ y = 0 := by
            have h_ev_const : ψ =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := h_zero_neighborhood
            rw [Filter.EventuallyEq.fderiv_eq h_ev_const]; simp
          refine Finset.sum_eq_zero ?_; intro i _
          refine Finset.sum_eq_zero ?_; intro j _
          rw [h_fderiv_zero]; simp
      rw [MeasureTheory.integral_congr_ae h_integrand_ae_zero]; simp
    have h_mass_zero :
        ∫ y in Ω, densityOnEuclid (I := I) g α y * D.uChart y * ψ y
          ∂(volume : Measure EuclN) = 0 := by
      have h_integrand_ae_zero :
          (fun y : EuclN => densityOnEuclid (I := I) g α y * D.uChart y * ψ y) =ᵐ[
            (volume : Measure EuclN).restrict Ω]
            (fun _ : EuclN => (0 : ℝ)) := by
        refine (ae_restrict_iff' hΩ_meas).mpr ?_
        have h_uc_ae : ∀ᵐ y ∂((volume : Measure EuclN).restrict U),
            D.uChart y = 0 :=
          base_u_chart_ae_zero_off_K_α (I := I) (M := M) g α hu_h
        have h_uc_vol : ∀ᵐ y ∂(volume : Measure EuclN),
            y ∈ U → D.uChart y = 0 := by
          rw [← ae_restrict_iff' hU_meas]; exact h_uc_ae
        filter_upwards [h_uc_vol] with y hy _hyΩ
        by_cases hy_U : y ∈ U
        · rw [hy hy_U]; ring
        · have h_y_not_in_support : y ∉ tsupport ψ := fun h => hy_U (hψ_support_U h)
          have hψ_zero : ψ y = 0 := image_eq_zero_of_notMem_tsupport h_y_not_in_support
          rw [hψ_zero]; ring
      rw [MeasureTheory.integral_congr_ae h_integrand_ae_zero]; simp
    rw [h_principal_zero, h_mass_zero, zero_add] at h_var
    have h_vanish_off_chart : ∀ x ∉ Ω,
        ψ x • (densityOnEuclid (I := I) g α x * D.fChart x) = 0 := fun x hx => by
      have hx_not_support : x ∉ tsupport ψ := fun h => hx (hψ_support_chart h)
      have hψ_x : ψ x = 0 := image_eq_zero_of_notMem_tsupport hx_not_support
      rw [hψ_x]; simp
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      h_vanish_off_chart]
    rw [show (fun x : EuclN => ψ x • (densityOnEuclid (I := I) g α x *
        D.fChart x)) = (fun y : EuclN =>
        densityOnEuclid (I := I) g α y * D.fChart y * ψ y) by
      funext y; simp [smul_eq_mul, mul_comm]]
    exact h_var.symm
  have h_cf_ae_zero : ∀ᵐ y ∂(volume : Measure EuclN), y ∈ U →
      densityOnEuclid (I := I) g α y * D.fChart y = 0 :=
    hU_open.ae_eq_zero_of_integral_contDiff_smul_eq_zero h_prod_localInt
      h_zero_for_test
  have h_target_ae : ∀ᵐ y ∂(volume : Measure EuclN),
      y ∈ U → D.fChart y = 0 := by
    filter_upwards [h_cf_ae_zero] with y hy hy_U
    have h_cf := hy hy_U
    have h_density_pos : 0 < densityOnEuclid (I := I) g α y :=
      densityOnEuclid_pos (I := I) g α (hU_sub hy_U)
    exact (mul_eq_zero.mp h_cf).resolve_left h_density_pos.ne'
  refine (ae_restrict_iff' hU_meas).mpr ?_
  filter_upwards [h_target_ae] with y hy hy_U
  exact hy hy_U

end CalabiYau.PoissonDomainRegularity
