module
public import CalabiYau.Analysis.Elliptic.Regularity.ChartBilinear.H1Compl
public import CalabiYau.Analysis.Elliptic.Poisson.DomainSobolevGain.MixedPartialRegularity

@[expose] public section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume CalabiYau.DivergenceTheorem
open CalabiYau.Laplacian.MetricExtension

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- Upper density control is asserted only on a compact subset inside the chart. -/
lemma chartPulledWeighted_restrict_compact_le_volume
    {g : SmoothRiemannianMetric I M} (α : M)
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ c : ℝ, 0 < c ∧
      (chartPulledWeightedMeasure (I := I) g α).restrict K ≤
        ENNReal.ofReal c • ((volume : Measure EuclN).restrict K) := by
  classical
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  obtain ⟨_c_min, c_max, hc_min_pos, hc_le, h_bd⟩ :=
    densityOnEuclid_bounded_on_compact (I := I) (M := M) g α hK_compact hK_in
  refine ⟨c_max, lt_of_lt_of_le hc_min_pos hc_le, ?_⟩
  refine Measure.le_iff.2 ?_
  intro A hA
  rw [Measure.restrict_apply hA, Measure.smul_apply, Measure.restrict_apply hA]
  unfold chartPulledWeightedMeasure
  rw [withDensity_apply _ (hA.inter hK_meas)]
  have h_pointwise_bd :
      ∫⁻ y in A ∩ K,
          ENNReal.ofReal (densityOnEuclid (I := I) g α y)
            ∂(volume : Measure EuclN) ≤
      ∫⁻ _y in A ∩ K, ENNReal.ofReal c_max ∂(volume : Measure EuclN) := by
    apply MeasureTheory.setLIntegral_mono_ae'
    · exact hA.inter hK_meas
    · refine Filter.Eventually.of_forall fun y hy => ?_
      apply ENNReal.ofReal_le_ofReal
      exact (h_bd y hy.2).2
  have h_const_eval :
      ∫⁻ _y in A ∩ K, ENNReal.ofReal c_max ∂(volume : Measure EuclN) =
      ENNReal.ofReal c_max * (volume : Measure EuclN) (A ∩ K) := by
    rw [MeasureTheory.setLIntegral_const]
  rw [smul_eq_mul]
  exact h_pointwise_bd.trans (le_of_eq h_const_eval)

/-- Compact essential support converts chart volume L² to weighted L².
The support assertion stays almost everywhere, not pointwise. -/
lemma memLp_weighted_of_memLp_volume_of_ae_zero_off_compact
    {g : SmoothRiemannianMetric I M} (α : M)
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    {f : EuclN → ℝ}
    (hf : MemLp f 2 ((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α)))
    (hzero : ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α)), y ∉ K → f y = 0) :
    MemLp f 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have h_u_eq_ind : f =ᵐ[(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α)] K.indicator f := by
    filter_upwards [hzero] with y hy
    by_cases hy_K : y ∈ K
    · simp [Set.indicator_of_mem hy_K]
    · rw [Set.indicator_of_notMem hy_K, hy hy_K]
  have h_global_K : MemLp f 2 ((volume : Measure EuclN).restrict K) := by
    have h_restrict := hf.restrict K
    have h_eq : ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)).restrict K =
        (volume : Measure EuclN).restrict K := by
      rw [Measure.restrict_restrict hK_meas]
      congr 1
      exact Set.inter_eq_self_of_subset_left hK_in
    rw [h_eq] at h_restrict
    exact h_restrict
  obtain ⟨c, _hc_pos, h_le⟩ :=
    chartPulledWeighted_restrict_compact_le_volume (I := I) (M := M)
      (g := g) α hK_compact hK_in
  have h_u_weighted_K : MemLp f 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict K) :=
    h_global_K.of_measure_le_smul (c := ENNReal.ofReal c)
      ENNReal.ofReal_ne_top h_le
  have h_indicator_memLp_weighted : MemLp (K.indicator f) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    rw [memLp_indicator_iff_restrict hK_meas]
    have h_double_restrict :
        ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)).restrict K =
        (chartPulledWeightedMeasure (I := I) g α).restrict K := by
      rw [Measure.restrict_restrict hK_meas]
      congr 1
      exact Set.inter_eq_self_of_subset_left hK_in
    rw [h_double_restrict]
    exact h_u_weighted_K
  have h_absCont :
      (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α) ≪
      (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α) := by
    refine Measure.AbsolutelyContinuous.restrict ?_ _
    unfold chartPulledWeightedMeasure
    exact MeasureTheory.withDensity_absolutelyContinuous _ _
  exact (memLp_congr_ae (h_absCont.ae_eq h_u_eq_ind)).mpr h_indicator_memLp_weighted

omit [FiniteDimensional ℝ E] in
/-- A weak derivative cannot acquire essential support on an open subset
where the original function vanishes almost everywhere. -/
lemma weakPartial_ae_zero_on_open_subset
    {Ω U : Set EuclN} (hΩ_open : IsOpen Ω) (hU_open : IsOpen U)
    (hU_sub : U ⊆ Ω) {f w : EuclN → ℝ}
    (i : Fin (Module.finrank ℝ E))
    (hw_isWeak : Sobolev.Euclidean.HasWeakPartialDeriv i w f Ω)
    (hw_li : LocallyIntegrableOn w U (volume : Measure EuclN))
    (hf_ae_zero : ∀ᵐ y ∂((volume : Measure EuclN).restrict U), f y = 0) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict U), w y = 0 := by
  classical
  have hU_meas : MeasurableSet U := hU_open.measurableSet
  have hf_ae_zero_vol : ∀ᵐ y ∂(volume : Measure EuclN), y ∈ U → f y = 0 := by
    rw [← ae_restrict_iff' hU_meas]
    exact hf_ae_zero
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
      · rw [hy hy_U]
        ring
      · have h_compl_open : IsOpen ((tsupport ψ)ᶜ) :=
          (isClosed_tsupport _).isOpen_compl
        have h_y_not_support : y ∉ tsupport ψ := fun h => hy_U (hψ_support h)
        have h_zero_neighborhood : ∀ᶠ z in 𝓝 y, ψ z = 0 := by
          filter_upwards [h_compl_open.mem_nhds h_y_not_support] with z hz
          exact image_eq_zero_of_notMem_tsupport hz
        have h_fderiv_zero : fderiv ℝ ψ y = 0 := by
          have h_ev_const : ψ =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := h_zero_neighborhood
          rw [Filter.EventuallyEq.fderiv_eq h_ev_const]
          simp
        rw [h_fderiv_zero]
        simp
    have h_zero_lhs :
        ∫ y in Ω, f y * (fderiv ℝ ψ y) (EuclideanSpace.single i 1)
          ∂(volume : Measure EuclN) = 0 := by
      rw [MeasureTheory.integral_congr_ae h_f_support_ae]
      simp
    rw [h_zero_lhs] at h_weak
    have h_rhs_zero : ∫ y in Ω, w y * ψ y ∂(volume : Measure EuclN) = 0 := by
      linarith
    have h_vanish_off_Ω : ∀ x ∉ Ω, ψ x • w x = 0 := fun x hx => by
      have hx_support : x ∉ tsupport ψ := fun h => hx (hψ_support_Ω h)
      have hψ_x : ψ x = 0 := image_eq_zero_of_notMem_tsupport hx_support
      rw [hψ_x]
      simp
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero h_vanish_off_Ω]
    refine (MeasureTheory.setIntegral_congr_fun hΩ_meas ?_).trans h_rhs_zero
    intro x _hxΩ
    simp [smul_eq_mul, mul_comm]
  refine (ae_restrict_iff' hU_meas).mpr ?_
  filter_upwards [h_target] with y hy hy_U
  exact hy hy_U

end CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl

namespace CalabiYau.PoissonDomainRegularity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
open CalabiYau.RiemannianVolume CalabiYau.Analysis.Laplacian
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl Sobolev.Chart Sobolev.Euclidean
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

lemma chosenMthMixedPartialChartPushedU_ae_zero_off_chartImagePOUTsupport
    (g : SmoothRiemannianMetric I M) (α : M) (u_h : H1Compl g) :
    ∀ (m : ℕ), MemWkp (m + 1) 2
      (chartPushed (chartAtlasPOU I M) α ((h1ComplToLp g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) →
    ∀ (dirs : Fin m → Fin (Module.finrank ℝ E)),
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
        ((chartTargetEuclid (I := I) (M := M) α) \ chartImagePOUTsupport (I := I) (M := M) α)),
        chosenMthMixedPartialChartPushedU g α u_h m dirs y = 0 := by
  intro m
  induction m with
  | zero =>
    intro _h dirs
    have hU : IsOpen ((chartTargetEuclid (I := I) (M := M) α) \
        chartImagePOUTsupport (I := I) (M := M) α) :=
      (chartTargetEuclid_isOpen (I := I) (M := M) α).sdiff
        (chartImagePOUTsupport_isCompact (I := I) (M := M) α).isClosed
    refine (ae_restrict_iff' hU.measurableSet).mpr (Filter.Eventually.of_forall ?_)
    intro y hy
    exact chartPushed_eq_zero_off_chartImagePOUTsupport (I := I) (M := M) α _ hy.1 hy.2
  | succ m ih =>
    intro h_parent dirs
    have h_parent' : MemWkp (m + 1) 2
        (chartPushed (chartAtlasPOU I M) α ((h1ComplToLp g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α) :=
      MemWkp.le_of_le (by omega) h_parent
    have h_inner := chosenMthMixedPartialChartPushedU_memW1p_two g α u_h m h_parent' (Fin.init dirs)
    have hΩ : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    have hU := hΩ.sdiff (chartImagePOUTsupport_isCompact (I := I) (M := M) α).isClosed
    have h_li : LocallyIntegrableOn
        (chosenWeakPartialOrZero 2 (dirs (Fin.last m))
          (chosenMthMixedPartialChartPushedU g α u_h m (Fin.init dirs))
          (chartTargetEuclid (I := I) (M := M) α))
        ((chartTargetEuclid (I := I) (M := M) α) \ chartImagePOUTsupport (I := I) (M := M) α)
        (volume : Measure EuclN) := by
      apply LocallyIntegrableOn.mono_set _ Set.sdiff_subset
      exact locallyIntegrableOn_of_locallyIntegrable_restrict
        ((chosenWeakPartialOrZero_memLp_of_mem h_inner (dirs (Fin.last m))).locallyIntegrable (by norm_num))
    exact weakPartial_ae_zero_on_open_subset hΩ hU Set.sdiff_subset
      (dirs (Fin.last m)) (chosenWeakPartialOrZero_isWeakPartial_of_mem h_inner _)
      h_li (ih h_parent' (Fin.init dirs))

lemma chosenMthMixedPartialChartPushedU_memLp_weighted
    (g : SmoothRiemannianMetric I M) (α : M) (u_h : H1Compl g) (m : ℕ)
    (h_parent : MemWkp (m + 1) 2
      (chartPushed (chartAtlasPOU I M) α ((h1ComplToLp g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α))
    (dirs : Fin m → Fin (Module.finrank ℝ E)) :
    MemLp (chosenMthMixedPartialChartPushedU g α u_h m dirs) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  apply memLp_weighted_of_memLp_volume_of_ae_zero_off_compact α
    (chartImagePOUTsupport_isCompact (I := I) (M := M) α)
    (chartImagePOUTsupport_subset_target (I := I) (M := M) α)
    (chosenMthMixedPartialChartPushedU_memLp_two g α u_h m
      (MemWkp.le_of_le (by omega) h_parent) dirs)
  have hzero := chosenMthMixedPartialChartPushedU_ae_zero_off_chartImagePOUTsupport g α u_h m h_parent dirs
  have hΩ := (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  have hU := ((chartTargetEuclid_isOpen (I := I) (M := M) α).sdiff
    (chartImagePOUTsupport_isCompact (I := I) (M := M) α).isClosed).measurableSet
  refine (ae_restrict_iff' hΩ).mpr ?_
  filter_upwards [(ae_restrict_iff' hU).mp hzero] with y hy hyΩ hyK
  exact hy ⟨hyΩ, hyK⟩
end CalabiYau.PoissonDomainRegularity
