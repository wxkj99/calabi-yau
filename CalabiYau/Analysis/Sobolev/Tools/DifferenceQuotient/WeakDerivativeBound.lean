-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Tools/DifferenceQuotient/WeakDerivativeBound.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Tools.DifferenceQuotient
public import CalabiYau.Analysis.Sobolev.Tools.Mollification.WeakDerivative

@[expose] public section

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open scoped ENNReal NNReal Convolution Pointwise BigOperators

namespace Sobolev

variable {d : ℕ} [NeZero d]

local notation "EuclN" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private lemma lintegral_enorm_sq_diffQuot_le_lintegral_enorm_sq_partialDeriv_local
    {v : EuclN → ℝ} (hv : ContDiff ℝ 1 v) (k : Fin d) {h : ℝ} (hh : h ≠ 0)
    {Ω' Ω'' : Set EuclN}
    (hΩ' : MeasurableSet Ω') (hΩ'' : MeasurableSet Ω'')
    (h_admissible : ∀ x ∈ Ω'', ∀ s ∈ Set.Ioc (0 : ℝ) 1,
      x + (s * h) • EuclideanSpace.single k 1 ∈ Ω') :
    ∫⁻ x in Ω'',
      (‖diffQuot k h v x‖ₑ : ℝ≥0∞) ^ 2 ∂(volume : Measure EuclN) ≤
    ∫⁻ y in Ω',
      (‖(fderiv ℝ v y) (EuclideanSpace.single k 1)‖ₑ : ℝ≥0∞) ^ 2
      ∂(volume : Measure EuclN) := by
  classical
  set e : EuclN := EuclideanSpace.single k (1 : ℝ) with he
  have hfd_cont : Continuous (fun y : EuclN => fderiv ℝ v y) :=
    hv.continuous_fderiv one_ne_zero
  have h_partial_cont : Continuous (fun y : EuclN => (fderiv ℝ v y) e) :=
    hfd_cont.clm_apply continuous_const
  set FF : EuclN → ℝ≥0∞ := fun y =>
    (‖(fderiv ℝ v y) e‖ₑ : ℝ≥0∞) ^ 2 with hFF_def
  have hFF_meas : Measurable FF := by
    rw [hFF_def]
    exact h_partial_cont.measurable.enorm.pow_const 2
  have hFF_indicator_meas : Measurable (Ω'.indicator FF) :=
    hFF_meas.indicator hΩ'
  have hPoint_lint : ∀ x ∈ Ω'',
      (‖diffQuot k h v x‖ₑ : ℝ≥0∞) ^ 2 ≤
        ∫⁻ s in Set.Ioc (0 : ℝ) 1,
          Ω'.indicator FF (x + (s * h) • e) := by
    intro x hx
    have hreal :
        (diffQuot k h v x) ^ 2 ≤
          ∫ s in Set.Ioc (0 : ℝ) 1,
            ((fderiv ℝ v (x + (s * h) • e)) e) ^ 2 :=
      sq_diffQuot_le_integral_sq_partialDeriv (d := d) hv k hh x
    have hLHS_eq :
        (‖diffQuot k h v x‖ₑ : ℝ≥0∞) ^ 2 =
          ENNReal.ofReal ((diffQuot k h v x) ^ 2) := by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2,
        sq_abs]
    have hgam_cont : Continuous (fun s : ℝ => x + (s * h) • e) :=
      continuous_const.add
        ((continuous_id.mul continuous_const).smul continuous_const)
    have h_int_real :
        Integrable (fun s : ℝ =>
          ((fderiv ℝ v (x + (s * h) • e)) e) ^ 2)
          ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) := by
      have h_bd_cont : Continuous (fun s : ℝ =>
          ((fderiv ℝ v (x + (s * h) • e)) e) ^ 2) :=
        ((h_partial_cont.comp hgam_cont)).pow 2
      exact h_bd_cont.integrableOn_Ioc (a := 0) (b := 1)
    have h_real_to_lint :
        ENNReal.ofReal (∫ s in Set.Ioc (0 : ℝ) 1,
          ((fderiv ℝ v (x + (s * h) • e)) e) ^ 2) =
        ∫⁻ s in Set.Ioc (0 : ℝ) 1,
          (‖((fderiv ℝ v (x + (s * h) • e)) e)‖ₑ : ℝ≥0∞) ^ 2 := by
      rw [ofReal_integral_eq_lintegral_ofReal h_int_real
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
      refine lintegral_congr_ae ?_
      filter_upwards with s
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2,
        sq_abs]
    have h_indicator_eq :
        ∫⁻ s in Set.Ioc (0 : ℝ) 1,
          (‖((fderiv ℝ v (x + (s * h) • e)) e)‖ₑ : ℝ≥0∞) ^ 2 =
        ∫⁻ s in Set.Ioc (0 : ℝ) 1,
          Ω'.indicator FF (x + (s * h) • e) := by
      refine lintegral_congr_ae ?_
      refine (ae_restrict_iff' measurableSet_Ioc).mpr ?_
      refine Filter.Eventually.of_forall ?_
      intro s hs
      have hin : x + (s * h) • e ∈ Ω' := h_admissible x hx s hs
      simp only [Set.indicator_of_mem hin, hFF_def]
    calc (‖diffQuot k h v x‖ₑ : ℝ≥0∞) ^ 2
        = ENNReal.ofReal ((diffQuot k h v x) ^ 2) := hLHS_eq
      _ ≤ ENNReal.ofReal (∫ s in Set.Ioc (0 : ℝ) 1,
            ((fderiv ℝ v (x + (s * h) • e)) e) ^ 2) :=
            ENNReal.ofReal_le_ofReal hreal
      _ = ∫⁻ s in Set.Ioc (0 : ℝ) 1,
            (‖((fderiv ℝ v (x + (s * h) • e)) e)‖ₑ : ℝ≥0∞) ^ 2 :=
            h_real_to_lint
      _ = ∫⁻ s in Set.Ioc (0 : ℝ) 1,
            Ω'.indicator FF (x + (s * h) • e) := h_indicator_eq
  have h_step1 :
      ∫⁻ x in Ω'', (‖diffQuot k h v x‖ₑ : ℝ≥0∞) ^ 2
        ∂(volume : Measure EuclN) ≤
        ∫⁻ x in Ω'',
          (∫⁻ s in Set.Ioc (0 : ℝ) 1,
            Ω'.indicator FF (x + (s * h) • e))
          ∂(volume : Measure EuclN) := by
    refine lintegral_mono_ae ?_
    rw [ae_restrict_iff' hΩ'']
    refine Filter.Eventually.of_forall ?_
    intro x hx
    exact hPoint_lint x hx
  have h_step2 :
      ∫⁻ x in Ω'',
          (∫⁻ s in Set.Ioc (0 : ℝ) 1,
            Ω'.indicator FF (x + (s * h) • e))
          ∂(volume : Measure EuclN) ≤
        ∫⁻ x : EuclN,
          (∫⁻ s in Set.Ioc (0 : ℝ) 1,
            Ω'.indicator FF (x + (s * h) • e))
          ∂(volume : Measure EuclN) :=
    lintegral_mono' Measure.restrict_le_self (le_refl _)
  have h_pair_meas : Measurable (fun p : EuclN × ℝ =>
      Ω'.indicator FF (p.1 + (p.2 * h) • e)) := by
    have hpt : Measurable (fun p : EuclN × ℝ => p.1 + (p.2 * h) • e) := by
      have h1 : Measurable (fun p : EuclN × ℝ => p.1) := measurable_fst
      have h2 : Measurable (fun p : EuclN × ℝ => p.2) := measurable_snd
      have h3 : Measurable (fun p : EuclN × ℝ => p.2 * h) :=
        h2.mul measurable_const
      have h4 : Measurable (fun p : EuclN × ℝ => (p.2 * h) • e) :=
        h3.smul measurable_const
      exact h1.add h4
    exact hFF_indicator_meas.comp hpt
  have h_swap :
      ∫⁻ x : EuclN,
          (∫⁻ s in Set.Ioc (0 : ℝ) 1,
            Ω'.indicator FF (x + (s * h) • e))
          ∂(volume : Measure EuclN) =
        ∫⁻ s in Set.Ioc (0 : ℝ) 1,
          (∫⁻ x : EuclN, Ω'.indicator FF (x + (s * h) • e)
            ∂(volume : Measure EuclN)) := by
    change ∫⁻ x : EuclN,
          (∫⁻ s in Set.Ioc (0 : ℝ) 1,
            (Function.uncurry (fun (x : EuclN) (s : ℝ) =>
              Ω'.indicator FF (x + (s * h) • e))) (x, s)) =
          ∫⁻ s in Set.Ioc (0 : ℝ) 1,
            (∫⁻ x : EuclN,
              (Function.uncurry (fun (x : EuclN) (s : ℝ) =>
                Ω'.indicator FF (x + (s * h) • e))) (x, s))
    exact lintegral_lintegral_swap h_pair_meas.aemeasurable
  have h_trans : ∀ s : ℝ,
      ∫⁻ x : EuclN, Ω'.indicator FF (x + (s * h) • e)
          ∂(volume : Measure EuclN) =
        ∫⁻ y : EuclN, Ω'.indicator FF y ∂(volume : Measure EuclN) := by
    intro s
    have hMP : MeasurePreserving (fun x : EuclN => x + (s * h) • e)
        (volume : Measure EuclN) (volume : Measure EuclN) :=
      measurePreserving_add_right (volume : Measure EuclN) _
    exact hMP.lintegral_comp hFF_indicator_meas
  have h_inner_const : (fun s : ℝ =>
        ∫⁻ x : EuclN, Ω'.indicator FF (x + (s * h) • e)
          ∂(volume : Measure EuclN)) =
      fun _ : ℝ => ∫⁻ y : EuclN, Ω'.indicator FF y
        ∂(volume : Measure EuclN) := by
    funext s; exact h_trans s
  have h_vol_unit :
      ((volume : Measure ℝ)) (Set.Ioc (0 : ℝ) 1) = 1 := by
    simp [Real.volume_Ioc]
  have h_outer_const :
      ∫⁻ s in Set.Ioc (0 : ℝ) 1,
          ∫⁻ x : EuclN, Ω'.indicator FF (x + (s * h) • e)
            ∂(volume : Measure EuclN) =
        ∫⁻ y : EuclN, Ω'.indicator FF y ∂(volume : Measure EuclN) := by
    rw [h_inner_const, lintegral_const,
      Measure.restrict_apply MeasurableSet.univ]
    simp [h_vol_unit]
  have h_indicator_to_restrict :
      ∫⁻ y : EuclN, Ω'.indicator FF y ∂(volume : Measure EuclN) =
        ∫⁻ y in Ω', FF y ∂(volume : Measure EuclN) := by
    rw [lintegral_indicator hΩ']
  calc ∫⁻ x in Ω'', (‖diffQuot k h v x‖ₑ : ℝ≥0∞) ^ 2
          ∂(volume : Measure EuclN)
      ≤ ∫⁻ x in Ω'',
            (∫⁻ s in Set.Ioc (0 : ℝ) 1,
              Ω'.indicator FF (x + (s * h) • e))
            ∂(volume : Measure EuclN) := h_step1
    _ ≤ ∫⁻ x : EuclN,
            (∫⁻ s in Set.Ioc (0 : ℝ) 1,
              Ω'.indicator FF (x + (s * h) • e))
            ∂(volume : Measure EuclN) := h_step2
    _ = ∫⁻ s in Set.Ioc (0 : ℝ) 1,
            ∫⁻ x : EuclN, Ω'.indicator FF (x + (s * h) • e)
              ∂(volume : Measure EuclN) := h_swap
    _ = ∫⁻ y : EuclN, Ω'.indicator FF y
            ∂(volume : Measure EuclN) := h_outer_const
    _ = ∫⁻ y in Ω', FF y ∂(volume : Measure EuclN) := h_indicator_to_restrict

omit [NeZero d] in
private lemma eLpNorm_two_restrict_le_of_sup_bound
    {K : Set EuclN} (hK_meas : MeasurableSet K)
    {f : EuclN → ℝ} {C : ℝ} (hf : ∀ x ∈ K, ‖f x‖ ≤ C) :
    eLpNorm f 2 ((volume : Measure EuclN).restrict K) ≤
      ((volume : Measure EuclN) K) ^ (1 / 2 : ℝ) * ENNReal.ofReal C := by
  classical
  have hae : ∀ᵐ x ∂((volume : Measure EuclN).restrict K), ‖f x‖ ≤ C := by
    rw [ae_restrict_iff' hK_meas]
    exact Filter.Eventually.of_forall fun x hx => hf x hx
  have h_bound : eLpNorm f 2 ((volume : Measure EuclN).restrict K) ≤
      (((volume : Measure EuclN).restrict K) Set.univ) ^ (2 : ℝ≥0∞).toReal⁻¹ *
        ENNReal.ofReal C :=
    eLpNorm_le_of_ae_bound (μ := (volume : Measure EuclN).restrict K) (p := 2) hae
  have h_meas_univ : ((volume : Measure EuclN).restrict K) Set.univ =
      (volume : Measure EuclN) K := by
    rw [Measure.restrict_apply MeasurableSet.univ]
    simp
  rw [h_meas_univ] at h_bound
  have h_pow_eq : ((2 : ℝ≥0∞).toReal)⁻¹ = (1/2 : ℝ) := by
    have h2 : ((2 : ℝ≥0∞).toReal) = 2 := by
      show ENNReal.toReal 2 = 2; rfl
    rw [h2]; norm_num
  rw [h_pow_eq] at h_bound
  exact h_bound

omit [NeZero d] in
private lemma tendsto_eLpNorm_restrict_of_tendstoUniformlyOn
    {ι : Type*} {l : Filter ι}
    {K : Set EuclN} (hK_meas : MeasurableSet K)
    (hK_volume_finite : (volume : Measure EuclN) K < ∞)
    {fSeq : ι → EuclN → ℝ} {f : EuclN → ℝ}
    (h_uniform : TendstoUniformlyOn fSeq f l K) :
    Tendsto (fun i => eLpNorm (fun x => fSeq i x - f x) 2
      ((volume : Measure EuclN).restrict K)) l (𝓝 0) := by
  classical
  have hK_volume_ne_top : (volume : Measure EuclN) K ≠ ∞ := hK_volume_finite.ne
  have h_uniform_metric : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ i in l, ∀ x ∈ K, dist (f x) (fSeq i x) < ε :=
    Metric.tendstoUniformlyOn_iff.mp h_uniform
  have h_uniform_real : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ i in l, ∀ x ∈ K, ‖fSeq i x - f x‖ ≤ ε := by
    intro ε hε
    have := h_uniform_metric ε hε
    filter_upwards [this] with i hi
    intro x hx
    have h := hi x hx
    rw [dist_comm, Real.dist_eq] at h
    rw [Real.norm_eq_abs]
    exact h.le
  set V : ℝ≥0∞ := ((volume : Measure EuclN) K) ^ (1/2 : ℝ) with hV_def
  have hV_lt_top : V < ∞ := by
    rw [hV_def]
    refine ENNReal.rpow_lt_top_of_nonneg ?_ hK_volume_ne_top
    norm_num
  have hV_ne_top : V ≠ ∞ := hV_lt_top.ne
  have h_eventual_bound : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ i in l, eLpNorm (fun x => fSeq i x - f x) 2
        ((volume : Measure EuclN).restrict K) ≤ V * ENNReal.ofReal ε := by
    intro ε hε
    filter_upwards [h_uniform_real ε hε] with i hi
    exact eLpNorm_two_restrict_le_of_sup_bound hK_meas hi
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ_pos
  by_cases hδ_top : δ = ∞
  · refine Filter.Eventually.of_forall fun i => ?_
    rw [hδ_top]; exact le_top
  have hδ_real : δ.toReal > 0 := ENNReal.toReal_pos hδ_pos.ne' hδ_top
  have h_ε_exists : ∃ ε₀ : ℝ, 0 < ε₀ ∧ V * ENNReal.ofReal ε₀ ≤ δ := by
    by_cases hV_zero : V = 0
    · refine ⟨1, by norm_num, ?_⟩
      rw [hV_zero]; simp
    · have hV_pos : 0 < V := pos_iff_ne_zero.mpr hV_zero
      have hV_real_pos : 0 < V.toReal := ENNReal.toReal_pos hV_zero hV_ne_top
      set ε₀ : ℝ := δ.toReal / (V.toReal + 1) with hε₀_def
      have hε₀_pos : 0 < ε₀ := by
        rw [hε₀_def]; apply div_pos hδ_real; linarith
      refine ⟨ε₀, hε₀_pos, ?_⟩
      have hV_eq : V = ENNReal.ofReal V.toReal := (ENNReal.ofReal_toReal hV_ne_top).symm
      rw [hV_eq, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
      rw [show δ = ENNReal.ofReal δ.toReal from (ENNReal.ofReal_toReal hδ_top).symm]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [hε₀_def, mul_div_assoc']
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < V.toReal + 1)]
      nlinarith [hV_real_pos.le, hδ_real.le]
  rcases h_ε_exists with ⟨ε₀, hε₀_pos, hε₀_le⟩
  filter_upwards [h_eventual_bound ε₀ hε₀_pos] with i hi
  exact hi.trans hε₀_le

omit [NeZero d] in
private lemma tendstoUniformlyOn_mollifyEps_of_uniformContinuous
    {ι : Type*} {l : Filter ι}
    {εFn : ι → ℝ} (hε_pos : ∀ i, 0 < εFn i) (hε_tendsto : Tendsto εFn l (𝓝 0))
    {φ : EuclN → ℝ} (hφ_cont : Continuous φ) (hφ_uc : UniformContinuous φ)
    {K : Set EuclN} :
    TendstoUniformlyOn (fun i => mollifyEps (d := d) (hε_pos i) φ) φ l K := by
  classical
  rw [Metric.tendstoUniformlyOn_iff]
  intro α hα
  rw [Metric.uniformContinuous_iff] at hφ_uc
  have hα2_pos : 0 < α / 2 := by linarith
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := hφ_uc (α / 2) hα2_pos
  have h_eventual_radius : ∀ᶠ i in l, εFn i < δ := by
    rw [Metric.tendsto_nhds] at hε_tendsto
    have := hε_tendsto δ hδ_pos
    filter_upwards [this] with i hi
    rw [Real.dist_eq, sub_zero, abs_of_pos (hε_pos i)] at hi
    exact hi
  filter_upwards [h_eventual_radius] with i h_radius
  intro x _
  have h_bound :
      dist
        ((((mollifierBumpEps (d := d) (hε_pos i)).normed (volume : Measure EuclN)
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure EuclN)] φ : EuclN → ℝ) x))
        (φ x) ≤ α / 2 := by
    refine ContDiffBump.dist_normed_convolution_le hφ_cont.aestronglyMeasurable
      (fun y hy => ?_)
    have h_mem : y ∈ Metric.ball x (εFn i) := hy
    have h_dist_lt : dist y x < εFn i := h_mem
    have hd_lt_δ : dist y x < δ := lt_trans h_dist_lt h_radius
    exact (hδ_bound hd_lt_δ).le
  have h_eq :
      ((mollifierBumpEps (d := d) (hε_pos i)).normed (volume : Measure EuclN)
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure EuclN)] φ : EuclN → ℝ) x =
        mollifyEps (d := d) (hε_pos i) φ x := rfl
  rw [h_eq] at h_bound
  have h_half_lt : α / 2 < α := by linarith
  rw [dist_comm]
  exact lt_of_le_of_lt h_bound h_half_lt

omit [NeZero d] in
private lemma tendsto_eLpNorm_restrict_sub_mollifyEps_of_continuous_compactSupport
    {ι : Type*} {l : Filter ι}
    {εFn : ι → ℝ} (hε_pos : ∀ i, 0 < εFn i) (hε_tendsto : Tendsto εFn l (𝓝 0))
    {K : Set EuclN} (hK_compact : IsCompact K)
    {φ : EuclN → ℝ} (hφ_cont : Continuous φ)
    (hφ_compactSupport : HasCompactSupport φ) :
    Tendsto (fun i => eLpNorm
      (fun x => mollifyEps (d := d) (hε_pos i) φ x - φ x) 2
      ((volume : Measure EuclN).restrict K)) l (𝓝 0) := by
  classical
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have hK_volume_finite : (volume : Measure EuclN) K < ∞ :=
    hK_compact.measure_lt_top
  have hφ_uc : UniformContinuous φ := by
    refine hφ_cont.uniformContinuous_of_tendsto_cocompact (x := 0) ?_
    rw [tendsto_def]
    intro s hs
    rcases _root_.mem_nhds_iff.mp hs with ⟨t, hts, ht_open, h0_mem⟩
    refine mem_cocompact.mpr ⟨tsupport φ, hφ_compactSupport, ?_⟩
    intro x hx
    have hx_notin_tsupp : x ∉ tsupport φ := hx
    have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hx_notin_tsupp
    rw [Set.mem_preimage, hφx]
    exact hts h0_mem
  have h_uniform : TendstoUniformlyOn
      (fun i => mollifyEps (d := d) (hε_pos i) φ) φ l K :=
    tendstoUniformlyOn_mollifyEps_of_uniformContinuous hε_pos hε_tendsto
      hφ_cont hφ_uc
  exact tendsto_eLpNorm_restrict_of_tendstoUniformlyOn hK_meas hK_volume_finite h_uniform

omit [NeZero d] in
private lemma mollifyEps_sub_eq_mollifyEps_sub
    {ε : ℝ} (hε : 0 < ε) {f g : EuclN → ℝ}
    (hf_local : LocallyIntegrable f (volume : Measure EuclN))
    (hg_local : LocallyIntegrable g (volume : Measure EuclN)) :
    mollifyEps (d := d) hε f - mollifyEps (d := d) hε g =
      mollifyEps (d := d) hε (f - g) := by
  funext x
  rw [Pi.sub_apply, mollifyEps_apply hε f x, mollifyEps_apply hε g x,
    mollifyEps_apply hε (f - g) x]
  have hψ_compact : HasCompactSupport (mollifierEps (d := d) hε) :=
    mollifierEps_compactSupport hε
  have hψ_cont : Continuous (mollifierEps (d := d) hε) :=
    mollifierEps_continuous hε
  have h_int_f : Integrable (fun t : EuclN =>
    mollifierEps (d := d) hε t * f (x - t)) (volume : Measure EuclN) := by
    have h_existsAt : ConvolutionExistsAt (mollifierEps (d := d) hε) f x
        (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure EuclN) :=
      hψ_compact.convolutionExists_left
        (L := ContinuousLinearMap.lsmul ℝ ℝ) hψ_cont hf_local x
    refine h_existsAt.integrable.congr ?_
    filter_upwards with t
    simp [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have h_int_g : Integrable (fun t : EuclN =>
    mollifierEps (d := d) hε t * g (x - t)) (volume : Measure EuclN) := by
    have h_existsAt : ConvolutionExistsAt (mollifierEps (d := d) hε) g x
        (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure EuclN) :=
      hψ_compact.convolutionExists_left
        (L := ContinuousLinearMap.lsmul ℝ ℝ) hψ_cont hg_local x
    refine h_existsAt.integrable.congr ?_
    filter_upwards with t
    simp [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [← integral_sub h_int_f h_int_g]
  refine integral_congr_ae ?_
  filter_upwards with t
  simp [Pi.sub_apply]
  ring

omit [NeZero d] in
private lemma tendsto_eLpNorm_restrict_sub_mollifyEps_of_memLp
    {ι : Type*} {l : Filter ι}
    {εFn : ι → ℝ} (hε_pos : ∀ i, 0 < εFn i) (hε_tendsto : Tendsto εFn l (𝓝 0))
    {K : Set EuclN} (hK_compact : IsCompact K)
    {g : EuclN → ℝ} (hg : MemLp g 2 (volume : Measure EuclN)) :
    Tendsto (fun i => eLpNorm
      (fun x => mollifyEps (d := d) (hε_pos i) g x - g x) 2
      ((volume : Measure EuclN).restrict K)) l (𝓝 0) := by
  classical
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have hg_local : LocallyIntegrable g (volume : Measure EuclN) :=
    hg.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ_pos
  by_cases hδ_top : δ = ∞
  · refine Filter.Eventually.of_forall fun i => ?_
    rw [hδ_top]; exact le_top
  set δ3 : ℝ≥0∞ := δ / 3 with hδ3_def
  have hδ3_pos : 0 < δ3 := by
    rw [hδ3_def]; exact ENNReal.div_pos hδ_pos.ne' (by norm_num)
  have hδ3_ne_top : δ3 ≠ ∞ := by
    rw [hδ3_def]
    exact ENNReal.div_ne_top hδ_top (by norm_num)
  obtain ⟨φ, hφ_compactSupport, h_approx, hφ_cont, hφ_memLp⟩ :=
    hg.exists_hasCompactSupport_eLpNorm_sub_le (p := 2)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hδ3_pos.ne'
  set gd : EuclN → ℝ := fun x => g x - φ x with hgd_def
  have hgd_memLp : MemLp gd 2 (volume : Measure EuclN) := hg.sub hφ_memLp
  have hgd_local : LocallyIntegrable gd (volume : Measure EuclN) :=
    hgd_memLp.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hφ_local : LocallyIntegrable φ (volume : Measure EuclN) :=
    hφ_memLp.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hgd_eLp_le : eLpNorm gd 2 (volume : Measure EuclN) ≤ δ3 := by
    rw [hgd_def]
    have h_eq : (fun x => g x - φ x) = g - φ := by funext x; rfl
    rw [h_eq]
    exact h_approx
  have h_term2_tendsto : Tendsto (fun i => eLpNorm
      (fun x => mollifyEps (d := d) (hε_pos i) φ x - φ x) 2
      ((volume : Measure EuclN).restrict K)) l (𝓝 0) :=
    tendsto_eLpNorm_restrict_sub_mollifyEps_of_continuous_compactSupport
      hε_pos hε_tendsto hK_compact hφ_cont hφ_compactSupport
  rw [ENNReal.tendsto_nhds_zero] at h_term2_tendsto
  filter_upwards [h_term2_tendsto δ3 hδ3_pos] with i h2_le
  have h_moll_g_cont : Continuous (mollifyEps (d := d) (hε_pos i) g) :=
    mollifyEps_continuous (hε_pos i) hg_local
  have h_moll_φ_cont : Continuous (mollifyEps (d := d) (hε_pos i) φ) :=
    mollifyEps_continuous (hε_pos i) hφ_local
  have h_moll_gd_cont : Continuous (mollifyEps (d := d) (hε_pos i) gd) :=
    mollifyEps_continuous (hε_pos i) hgd_local
  set f1 : EuclN → ℝ := mollifyEps (d := d) (hε_pos i) gd with hf1_def
  set f2 : EuclN → ℝ := fun x => mollifyEps (d := d) (hε_pos i) φ x - φ x with hf2_def
  set f3 : EuclN → ℝ := fun x => φ x - g x with hf3_def
  have hf1_aestron : AEStronglyMeasurable f1
      ((volume : Measure EuclN).restrict K) :=
    h_moll_gd_cont.aestronglyMeasurable.restrict
  have hf2_aestron : AEStronglyMeasurable f2
      ((volume : Measure EuclN).restrict K) :=
    (h_moll_φ_cont.sub hφ_cont).aestronglyMeasurable.restrict
  have hf3_aestron : AEStronglyMeasurable f3
      ((volume : Measure EuclN).restrict K) := by
    refine (hφ_memLp.sub hg).aestronglyMeasurable.restrict
  have h_decomp : (fun x => mollifyEps (d := d) (hε_pos i) g x - g x) =
      f1 + f2 + f3 := by
    funext x
    change mollifyEps (d := d) (hε_pos i) g x - g x =
      mollifyEps (d := d) (hε_pos i) gd x +
      (mollifyEps (d := d) (hε_pos i) φ x - φ x) + (φ x - g x)
    have h_lin : mollifyEps (d := d) (hε_pos i) gd =
        mollifyEps (d := d) (hε_pos i) g - mollifyEps (d := d) (hε_pos i) φ := by
      rw [hgd_def]
      have h_diff_eq : (fun y => g y - φ y) = g - φ := by funext y; rfl
      rw [h_diff_eq]
      have := mollifyEps_sub_eq_mollifyEps_sub (hε_pos i) hg_local hφ_local
      have h_funeq : (g - φ) = (fun y => g y - φ y) := by funext y; rfl
      rw [show g - φ = (fun y => g y - φ y) from rfl]
      symm
      have := mollifyEps_sub_eq_mollifyEps_sub (hε_pos i) hg_local hφ_local
      have h_subeq : (fun y => g y - φ y) = g - φ := by funext y; rfl
      rw [h_subeq]
      exact this
    rw [h_lin, Pi.sub_apply]
    ring
  rw [h_decomp]
  have h_tri : eLpNorm (f1 + f2 + f3) 2 ((volume : Measure EuclN).restrict K) ≤
      eLpNorm f1 2 ((volume : Measure EuclN).restrict K) +
      eLpNorm f2 2 ((volume : Measure EuclN).restrict K) +
      eLpNorm f3 2 ((volume : Measure EuclN).restrict K) := by
    have h_step1 : eLpNorm (f1 + f2 + f3) 2
        ((volume : Measure EuclN).restrict K) ≤
        eLpNorm (f1 + f2) 2 ((volume : Measure EuclN).restrict K) +
        eLpNorm f3 2 ((volume : Measure EuclN).restrict K) := by
      exact eLpNorm_add_le (hf1_aestron.add hf2_aestron) hf3_aestron
        (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have h_step2 : eLpNorm (f1 + f2) 2
        ((volume : Measure EuclN).restrict K) ≤
        eLpNorm f1 2 ((volume : Measure EuclN).restrict K) +
        eLpNorm f2 2 ((volume : Measure EuclN).restrict K) :=
      eLpNorm_add_le hf1_aestron hf2_aestron (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    refine h_step1.trans ?_
    exact add_le_add h_step2 le_rfl
  refine h_tri.trans ?_
  have h_f1_le : eLpNorm f1 2 ((volume : Measure EuclN).restrict K) ≤ δ3 := by
    rw [hf1_def]
    refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
    exact (eLpNorm_mollifyEps_le (hε_pos i) hgd_memLp).trans hgd_eLp_le
  have h_f2_le : eLpNorm f2 2 ((volume : Measure EuclN).restrict K) ≤ δ3 := h2_le
  have h_f3_le : eLpNorm f3 2 ((volume : Measure EuclN).restrict K) ≤ δ3 := by
    rw [hf3_def]
    have h_eq : (fun x => φ x - g x) = -gd := by
      funext x; rw [hgd_def]; simp [neg_sub]
    rw [h_eq, eLpNorm_neg]
    refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
    exact hgd_eLp_le
  have h_sum : δ3 + δ3 + δ3 = δ := by
    rw [hδ3_def]
    rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same]
    rw [show δ + δ + δ = δ * 3 from by ring]
    rw [ENNReal.mul_div_cancel_right (by norm_num : (3 : ℝ≥0∞) ≠ 0)
      (by norm_num : (3 : ℝ≥0∞) ≠ ∞)]
  refine (add_le_add (add_le_add h_f1_le h_f2_le) h_f3_le).trans ?_
  rw [h_sum]

omit [NeZero d] in
private lemma eLpNorm_le_of_eLpNorm_sub_le
    {μ : Measure EuclN} {f g : EuclN → ℝ}
    (hf_aestron : AEStronglyMeasurable f μ)
    (hg_aestron : AEStronglyMeasurable g μ)
    {δ : ℝ≥0∞}
    (h_le : eLpNorm (fun x => f x - g x) 2 μ ≤ δ) :
    eLpNorm f 2 μ ≤ eLpNorm g 2 μ + δ := by
  have h_eq : f = (fun x => f x - g x) + g := by funext x; rw [Pi.add_apply]; ring
  rw [h_eq]
  refine (eLpNorm_add_le (hf_aestron.sub hg_aestron) hg_aestron
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans ?_
  rw [add_comm]
  exact add_le_add le_rfl h_le

omit [NeZero d] in
private lemma eLpNorm_sq_le_of_eLpNorm_sub_le
    {μ : Measure EuclN} {f g : EuclN → ℝ}
    (hf_aestron : AEStronglyMeasurable f μ)
    (hg_aestron : AEStronglyMeasurable g μ)
    {δ : ℝ≥0∞}
    (h_le : eLpNorm (fun x => f x - g x) 2 μ ≤ δ) :
    eLpNorm f 2 μ ^ 2 ≤ (eLpNorm g 2 μ + δ) ^ 2 :=
  pow_le_pow_left' (eLpNorm_le_of_eLpNorm_sub_le hf_aestron hg_aestron h_le) 2

omit [NeZero d] in
private lemma lintegral_enorm_sq_eq_eLpNorm_sq
    {μ : Measure EuclN} (f : EuclN → ℝ) :
    ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ 2 ∂μ = (eLpNorm f 2 μ) ^ 2 := by
  classical
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := μ)
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by show ENNReal.toReal 2 = 2; rfl
  rw [h2]
  have h_inner_eq : ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂μ =
      ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards with x
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
  rw [h_inner_eq]
  rw [← ENNReal.rpow_natCast _ 2]
  rw [← ENNReal.rpow_mul]
  norm_num

omit [NeZero d] in
private theorem lintegral_enorm_sq_diffQuot_le_lintegral_enorm_sq_weakPartial
    {u g_k : EuclN → ℝ}
    (hu_l2 : MemLp u 2 (volume : Measure EuclN))
    (hg_k_l2 : MemLp g_k 2 (volume : Measure EuclN))
    (k : Fin d) (hwp : DeGiorgi.HasWeakPartialDeriv (d := d) k g_k u Set.univ)
    {Ω' Ω'' : Set EuclN}
    (_hΩ'_meas : MeasurableSet Ω') (hΩ''_meas : MeasurableSet Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    {h₀ : ℝ} (_hh₀_pos : 0 < h₀)
    (h_thick : Metric.cthickening h₀ (closure Ω'') ⊆ Ω')
    {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ h₀) :
    ∫⁻ x in Ω'', (‖diffQuot k h u x‖ₑ : ℝ≥0∞) ^ 2
        ∂(volume : Measure EuclN) ≤
      ∫⁻ y in Ω', (‖g_k y‖ₑ : ℝ≥0∞) ^ 2 ∂(volume : Measure EuclN) := by
  classical
  set K : Set EuclN := Metric.cthickening h₀ (closure Ω'') with hK_def
  have hK_compact : IsCompact K := hΩ''_compact_closure.cthickening
  have hK_subset : K ⊆ Ω' := h_thick
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  set εFn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hεFn_def
  have hε_pos : ∀ n, 0 < εFn n := fun n => by
    rw [hεFn_def]; positivity
  have hε_tendsto : Tendsto εFn Filter.atTop (𝓝 0) := by
    rw [hεFn_def]; exact tendsto_one_div_add_atTop_nhds_zero_nat
  set u_n : ℕ → EuclN → ℝ := fun n => mollifyEps (d := d) (hε_pos n) u with hu_n_def
  have hu_local : LocallyIntegrable u (volume : Measure EuclN) :=
    hu_l2.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hg_k_local : LocallyIntegrable g_k (volume : Measure EuclN) :=
    hg_k_l2.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hu_n_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (u_n n) := fun n =>
    mollifyEps_contDiff (hε_pos n) hu_local
  have hu_n_C1 : ∀ n, ContDiff ℝ 1 (u_n n) := fun n =>
    (hu_n_smooth n).of_le (by norm_cast)
  have h_partial_eq : ∀ n,
      (fun y => (fderiv ℝ (u_n n) y) (EuclideanSpace.single k 1)) =
        mollifyEps (d := d) (hε_pos n) g_k := by
    intro n
    funext y
    exact mollifyEps_partial_eq_mollifyEps_weakPartial (hε_pos n) hu_local hwp y
  have h_admissible : ∀ x ∈ Ω'', ∀ s ∈ Set.Ioc (0 : ℝ) 1,
      x + (s * h) • EuclideanSpace.single k 1 ∈ K := by
    intro x hx s hs
    have h_dist : dist (x + (s * h) • EuclideanSpace.single k 1) x ≤ h₀ := by
      have h_norm_eq :
          ‖(s * h) • EuclideanSpace.single k (1 : ℝ)‖ = |s * h| := by
        rw [norm_smul]
        have hsing : ‖(EuclideanSpace.single k (1 : ℝ) : EuclN)‖ = 1 := by simp
        rw [hsing, mul_one, Real.norm_eq_abs]
      rw [show dist (x + (s * h) • EuclideanSpace.single k 1) x =
        ‖x + (s * h) • EuclideanSpace.single k 1 - x‖ from (dist_eq_norm _ _)]
      rw [add_sub_cancel_left, h_norm_eq]
      have hs_le : s ≤ 1 := hs.2
      have hs_nn : 0 ≤ s := hs.1.le
      have hh_abs_nn : 0 ≤ |h| := abs_nonneg _
      calc |s * h| = |s| * |h| := abs_mul s h
        _ = s * |h| := by rw [abs_of_nonneg hs_nn]
        _ ≤ 1 * |h| := mul_le_mul_of_nonneg_right hs_le hh_abs_nn
        _ = |h| := one_mul _
        _ ≤ h₀ := hh_le
    rw [hK_def]
    have h_in_closure : x ∈ closure Ω'' := subset_closure hx
    exact Metric.mem_cthickening_of_dist_le
      (x + (s * h) • EuclideanSpace.single k 1) x h₀ (closure Ω'')
      h_in_closure h_dist
  have h_smooth_bound : ∀ n,
      ∫⁻ x in Ω'',
        (‖diffQuot k h (u_n n) x‖ₑ : ℝ≥0∞) ^ 2 ∂(volume : Measure EuclN) ≤
      ∫⁻ y in K,
        (‖(fderiv ℝ (u_n n) y) (EuclideanSpace.single k 1)‖ₑ : ℝ≥0∞) ^ 2
        ∂(volume : Measure EuclN) := fun n =>
    lintegral_enorm_sq_diffQuot_le_lintegral_enorm_sq_partialDeriv_local
      (hu_n_C1 n) k hh hK_meas hΩ''_meas h_admissible
  have h_partial_substitute : ∀ n,
      ∫⁻ y in K,
        (‖(fderiv ℝ (u_n n) y) (EuclideanSpace.single k 1)‖ₑ : ℝ≥0∞) ^ 2
        ∂(volume : Measure EuclN) =
      ∫⁻ y in K,
        (‖mollifyEps (d := d) (hε_pos n) g_k y‖ₑ : ℝ≥0∞) ^ 2
        ∂(volume : Measure EuclN) := by
    intro n
    refine lintegral_congr_ae ?_
    refine Filter.Eventually.of_forall fun y => ?_
    have h_eq_pt : (fderiv ℝ (u_n n) y) (EuclideanSpace.single k 1) =
        mollifyEps (d := d) (hε_pos n) g_k y :=
      congr_fun (h_partial_eq n) y
    change (‖(fderiv ℝ (u_n n) y) (EuclideanSpace.single k 1)‖ₑ : ℝ≥0∞) ^ 2 =
      (‖mollifyEps (d := d) (hε_pos n) g_k y‖ₑ : ℝ≥0∞) ^ 2
    rw [h_eq_pt]
  have h_combined : ∀ n,
      ∫⁻ x in Ω'', (‖diffQuot k h (u_n n) x‖ₑ : ℝ≥0∞) ^ 2
        ∂(volume : Measure EuclN) ≤
      ∫⁻ y in K, (‖mollifyEps (d := d) (hε_pos n) g_k y‖ₑ : ℝ≥0∞) ^ 2
        ∂(volume : Measure EuclN) := fun n =>
    (h_smooth_bound n).trans (le_of_eq (h_partial_substitute n))
  have h_ae_u : ∀ᵐ x ∂(volume : Measure EuclN),
      Tendsto (fun n => u_n n x) Filter.atTop (𝓝 (u x)) :=
    ae_tendsto_mollifyEps_of_locallyIntegrable hε_pos hε_tendsto hu_local
  have h_ae_u_translate : ∀ᵐ x ∂(volume : Measure EuclN),
      Tendsto (fun n => u_n n (x + h • EuclideanSpace.single k 1))
        Filter.atTop (𝓝 (u (x + h • EuclideanSpace.single k 1))) := by
    have hMP : MeasurePreserving
        (fun x : EuclN => x + h • EuclideanSpace.single k 1)
        (volume : Measure EuclN) (volume : Measure EuclN) :=
      measurePreserving_add_right (volume : Measure EuclN) _
    have h_qmp : MeasureTheory.Measure.QuasiMeasurePreserving
        (fun x : EuclN => x + h • EuclideanSpace.single k 1)
        (volume : Measure EuclN) (volume : Measure EuclN) :=
      hMP.quasiMeasurePreserving
    exact h_qmp.ae h_ae_u
  have h_ae_diffQuot : ∀ᵐ x ∂(volume : Measure EuclN),
      Tendsto (fun n => diffQuot k h (u_n n) x) Filter.atTop
        (𝓝 (diffQuot k h u x)) := by
    filter_upwards [h_ae_u, h_ae_u_translate] with x hx hx_t
    rw [diffQuot_apply_of_ne (d := d) k hh u x]
    have h_diff_eq : ∀ n,
        diffQuot k h (u_n n) x =
          (u_n n (x + h • EuclideanSpace.single k 1) - u_n n x) / h := by
      intro n
      exact diffQuot_apply_of_ne (d := d) k hh (u_n n) x
    have h_funeq :
        (fun n => diffQuot k h (u_n n) x) =
          (fun n => (u_n n (x + h • EuclideanSpace.single k 1) - u_n n x) / h) := by
      funext n; exact h_diff_eq n
    rw [h_funeq]
    exact ((hx_t.sub hx).div_const h)
  have h_ae_sq : ∀ᵐ x ∂(volume : Measure EuclN),
      Tendsto (fun n => (‖diffQuot k h (u_n n) x‖ₑ : ℝ≥0∞) ^ 2)
        Filter.atTop (𝓝 ((‖diffQuot k h u x‖ₑ : ℝ≥0∞) ^ 2)) := by
    filter_upwards [h_ae_diffQuot] with x hx
    have h_norm_tendsto : Tendsto (fun n => ‖diffQuot k h (u_n n) x‖ₑ)
        Filter.atTop (𝓝 ‖diffQuot k h u x‖ₑ) := hx.enorm
    have h_pow_cont : ContinuousAt (fun y : ℝ≥0∞ => y ^ 2) ‖diffQuot k h u x‖ₑ :=
      (ENNReal.continuous_pow 2).continuousAt
    exact h_pow_cont.tendsto.comp h_norm_tendsto
  have h_ae_sq_restrict : ∀ᵐ x ∂((volume : Measure EuclN).restrict Ω''),
      Tendsto (fun n => (‖diffQuot k h (u_n n) x‖ₑ : ℝ≥0∞) ^ 2)
        Filter.atTop (𝓝 ((‖diffQuot k h u x‖ₑ : ℝ≥0∞) ^ 2)) :=
    ae_restrict_of_ae h_ae_sq
  have h_fatou : ∫⁻ x in Ω'',
      (‖diffQuot k h u x‖ₑ : ℝ≥0∞) ^ 2 ∂(volume : Measure EuclN) ≤
      Filter.atTop.liminf (fun n =>
        ∫⁻ x in Ω'', (‖diffQuot k h (u_n n) x‖ₑ : ℝ≥0∞) ^ 2
          ∂(volume : Measure EuclN)) := by
    have h_meas : ∀ n, AEMeasurable
        (fun x => (‖diffQuot k h (u_n n) x‖ₑ : ℝ≥0∞) ^ 2)
        ((volume : Measure EuclN).restrict Ω'') := by
      intro n
      have h_cont : Continuous (diffQuot k h (u_n n)) :=
        continuous_diffQuot_of_continuous (d := d) k h (hu_n_C1 n).continuous
      exact (h_cont.measurable.enorm.pow_const 2).aemeasurable
    have h_lim_meas := h_ae_sq_restrict
    refine (lintegral_liminf_le' h_meas).trans_eq' ?_
    refine lintegral_congr_ae ?_
    filter_upwards [h_ae_sq_restrict] with x hx
    exact hx.liminf_eq
  have h_step5 : Filter.atTop.liminf (fun n =>
        ∫⁻ x in Ω'', (‖diffQuot k h (u_n n) x‖ₑ : ℝ≥0∞) ^ 2
          ∂(volume : Measure EuclN)) ≤
      Filter.atTop.liminf (fun n =>
        ∫⁻ y in K, (‖mollifyEps (d := d) (hε_pos n) g_k y‖ₑ : ℝ≥0∞) ^ 2
          ∂(volume : Measure EuclN)) := by
    refine Filter.liminf_le_liminf ?_
    refine Filter.Eventually.of_forall fun n => ?_
    exact h_combined n
  have h_l2_tendsto : Tendsto (fun n => eLpNorm
      (fun x => mollifyEps (d := d) (hε_pos n) g_k x - g_k x) 2
      ((volume : Measure EuclN).restrict K)) Filter.atTop (𝓝 0) :=
    tendsto_eLpNorm_restrict_sub_mollifyEps_of_memLp hε_pos hε_tendsto
      hK_compact hg_k_l2
  have h_eLpNorm_g_k_K : eLpNorm g_k 2 ((volume : Measure EuclN).restrict K) < ∞ := by
    have h_le : eLpNorm g_k 2 ((volume : Measure EuclN).restrict K) ≤
        eLpNorm g_k 2 (volume : Measure EuclN) :=
      eLpNorm_mono_measure g_k Measure.restrict_le_self
    exact lt_of_le_of_lt h_le hg_k_l2.eLpNorm_lt_top
  have h_eLpNorm_g_k_K_ne_top : eLpNorm g_k 2
      ((volume : Measure EuclN).restrict K) ≠ ∞ := h_eLpNorm_g_k_K.ne
  have h_lint_eq_eLpNorm_sq : ∀ n,
      ∫⁻ y in K, (‖mollifyEps (d := d) (hε_pos n) g_k y‖ₑ : ℝ≥0∞) ^ 2
        ∂(volume : Measure EuclN) =
      (eLpNorm (mollifyEps (d := d) (hε_pos n) g_k) 2
        ((volume : Measure EuclN).restrict K)) ^ 2 := by
    intro n
    rw [← lintegral_enorm_sq_eq_eLpNorm_sq (mollifyEps (d := d) (hε_pos n) g_k)
      (μ := (volume : Measure EuclN).restrict K)]
  have h_lint_eq_eLpNorm_sq_g : ∫⁻ y in K, (‖g_k y‖ₑ : ℝ≥0∞) ^ 2
        ∂(volume : Measure EuclN) =
      (eLpNorm g_k 2 ((volume : Measure EuclN).restrict K)) ^ 2 := by
    rw [← lintegral_enorm_sq_eq_eLpNorm_sq g_k
      (μ := (volume : Measure EuclN).restrict K)]
  have h_eventual_sq_bound : ∀ δ : ℝ≥0∞, 0 < δ →
      ∀ᶠ n in Filter.atTop,
        (eLpNorm (mollifyEps (d := d) (hε_pos n) g_k) 2
          ((volume : Measure EuclN).restrict K)) ^ 2 ≤
        (eLpNorm g_k 2 ((volume : Measure EuclN).restrict K) + δ) ^ 2 := by
    intro δ hδ_pos
    rw [ENNReal.tendsto_nhds_zero] at h_l2_tendsto
    filter_upwards [h_l2_tendsto δ hδ_pos] with n hn
    have h_aestron_n : AEStronglyMeasurable (mollifyEps (d := d) (hε_pos n) g_k)
        ((volume : Measure EuclN).restrict K) :=
      (mollifyEps_continuous (hε_pos n) hg_k_local).aestronglyMeasurable.restrict
    have h_aestron_g : AEStronglyMeasurable g_k
        ((volume : Measure EuclN).restrict K) := hg_k_l2.aestronglyMeasurable.restrict
    exact eLpNorm_sq_le_of_eLpNorm_sub_le h_aestron_n h_aestron_g hn
  have h_lint_bound : ∀ δ : ℝ≥0∞, 0 < δ →
      ∀ᶠ n in Filter.atTop,
        ∫⁻ y in K, (‖mollifyEps (d := d) (hε_pos n) g_k y‖ₑ : ℝ≥0∞) ^ 2
          ∂(volume : Measure EuclN) ≤
        (eLpNorm g_k 2 ((volume : Measure EuclN).restrict K) + δ) ^ 2 := by
    intro δ hδ_pos
    filter_upwards [h_eventual_sq_bound δ hδ_pos] with n hn
    rw [h_lint_eq_eLpNorm_sq n]
    exact hn
  have h_liminf_bound : ∀ δ : ℝ≥0∞, 0 < δ →
      Filter.atTop.liminf (fun n =>
        ∫⁻ y in K, (‖mollifyEps (d := d) (hε_pos n) g_k y‖ₑ : ℝ≥0∞) ^ 2
          ∂(volume : Measure EuclN)) ≤
        (eLpNorm g_k 2 ((volume : Measure EuclN).restrict K) + δ) ^ 2 := by
    intro δ hδ_pos
    have h_event := h_lint_bound δ hδ_pos
    exact Filter.liminf_le_of_frequently_le' (h_event.frequently)
  have h_inf_at_zero : Filter.atTop.liminf (fun n =>
        ∫⁻ y in K, (‖mollifyEps (d := d) (hε_pos n) g_k y‖ₑ : ℝ≥0∞) ^ 2
          ∂(volume : Measure EuclN)) ≤
      (eLpNorm g_k 2 ((volume : Measure EuclN).restrict K)) ^ 2 := by
    set N : ℝ≥0∞ := eLpNorm g_k 2 ((volume : Measure EuclN).restrict K) with hN_def
    have hN_ne_top : N ≠ ∞ := h_eLpNorm_g_k_K.ne
    have h_seq_sub_tendsto : Tendsto (fun m : ℕ => (N + (1 : ℝ≥0∞) / (m + 1)) ^ 2)
        Filter.atTop (𝓝 (N ^ 2)) := by
      have h_one_div : Tendsto (fun m : ℕ => (1 : ℝ≥0∞) / (m + 1))
          Filter.atTop (𝓝 0) := by
        have := ENNReal.tendsto_inv_nat_nhds_zero
        have h_eq : (fun m : ℕ => (1 : ℝ≥0∞) / (m + 1)) =
            (fun m : ℕ => ((m + 1 : ℕ) : ℝ≥0∞)⁻¹) := by
          funext m
          push_cast
          rw [ENNReal.div_eq_inv_mul, mul_one]
        rw [h_eq]
        exact ENNReal.tendsto_inv_nat_nhds_zero.comp
          (Filter.tendsto_atTop_atTop.mpr fun n => ⟨n, fun m hm => by omega⟩)
      have h_add : Tendsto (fun m : ℕ => N + (1 : ℝ≥0∞) / (m + 1))
          Filter.atTop (𝓝 (N + 0)) := tendsto_const_nhds.add h_one_div
      have h_pow : Tendsto (fun m : ℕ => (N + (1 : ℝ≥0∞) / (m + 1)) ^ 2)
          Filter.atTop (𝓝 ((N + 0) ^ 2)) := by
        exact (ENNReal.continuous_pow 2).continuousAt.tendsto.comp h_add
      simpa using h_pow
    have h_liminf_bound_seq : ∀ m : ℕ,
        Filter.atTop.liminf (fun n =>
          ∫⁻ y in K, (‖mollifyEps (d := d) (hε_pos n) g_k y‖ₑ : ℝ≥0∞) ^ 2
            ∂(volume : Measure EuclN)) ≤ (N + (1 : ℝ≥0∞) / (m + 1)) ^ 2 := by
      intro m
      have h_pos : (0 : ℝ≥0∞) < (1 : ℝ≥0∞) / (m + 1) := by
        rw [ENNReal.div_pos_iff]
        refine ⟨by norm_num, ?_⟩
        exact ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _, by norm_num⟩
      have := h_liminf_bound ((1 : ℝ≥0∞) / (m + 1)) h_pos
      rw [hN_def]; exact this
    have h_le_lim : Filter.atTop.liminf (fun n =>
          ∫⁻ y in K, (‖mollifyEps (d := d) (hε_pos n) g_k y‖ₑ : ℝ≥0∞) ^ 2
            ∂(volume : Measure EuclN)) ≤ N ^ 2 := by
      refine ge_of_tendsto h_seq_sub_tendsto ?_
      exact Filter.Eventually.of_forall h_liminf_bound_seq
    rw [hN_def] at h_le_lim ⊢
    exact h_le_lim
  have h_K_to_Ω' : ∫⁻ y in K, (‖g_k y‖ₑ : ℝ≥0∞) ^ 2
        ∂(volume : Measure EuclN) ≤
      ∫⁻ y in Ω', (‖g_k y‖ₑ : ℝ≥0∞) ^ 2 ∂(volume : Measure EuclN) :=
    lintegral_mono' (Measure.restrict_mono hK_subset le_rfl) le_rfl
  calc ∫⁻ x in Ω'', (‖diffQuot k h u x‖ₑ : ℝ≥0∞) ^ 2 ∂(volume : Measure EuclN)
      ≤ Filter.atTop.liminf (fun n =>
            ∫⁻ x in Ω'', (‖diffQuot k h (u_n n) x‖ₑ : ℝ≥0∞) ^ 2
              ∂(volume : Measure EuclN)) := h_fatou
    _ ≤ Filter.atTop.liminf (fun n =>
            ∫⁻ y in K, (‖mollifyEps (d := d) (hε_pos n) g_k y‖ₑ : ℝ≥0∞) ^ 2
              ∂(volume : Measure EuclN)) := h_step5
    _ ≤ (eLpNorm g_k 2 ((volume : Measure EuclN).restrict K)) ^ 2 :=
            h_inf_at_zero
    _ = ∫⁻ y in K, (‖g_k y‖ₑ : ℝ≥0∞) ^ 2 ∂(volume : Measure EuclN) :=
            h_lint_eq_eLpNorm_sq_g.symm
    _ ≤ ∫⁻ y in Ω', (‖g_k y‖ₑ : ℝ≥0∞) ^ 2 ∂(volume : Measure EuclN) := h_K_to_Ω'

omit [NeZero d] in
theorem integral_sq_diffQuot_le_integral_sq_weakPartial_meas
    {u g_k : EuclN → ℝ}
    (hu_l2 : MemLp u 2 (volume : Measure EuclN))
    (hg_k_l2 : MemLp g_k 2 (volume : Measure EuclN))
    (k : Fin d) (hwp : DeGiorgi.HasWeakPartialDeriv (d := d) k g_k u Set.univ)
    {Ω' Ω'' : Set EuclN}
    (hΩ'_meas : MeasurableSet Ω') (hΩ''_meas : MeasurableSet Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    {h₀ : ℝ} (hh₀_pos : 0 < h₀)
    (h_thick : Metric.cthickening h₀ (closure Ω'') ⊆ Ω')
    {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ h₀) :
    ∫ x in Ω'', (diffQuot k h u x)^2 ∂(volume : Measure EuclN) ≤
      ∫ x in Ω', (g_k x)^2 ∂(volume : Measure EuclN) := by
  classical
  have h_lint :=
    lintegral_enorm_sq_diffQuot_le_lintegral_enorm_sq_weakPartial
      hu_l2 hg_k_l2 k hwp hΩ'_meas hΩ''_meas
      hΩ''_compact_closure hh₀_pos h_thick hh hh_le
  have h_RHS_lint_lt_top :
      ∫⁻ y in Ω', (‖g_k y‖ₑ : ℝ≥0∞) ^ 2 ∂(volume : Measure EuclN) < ∞ := by
    rw [lintegral_enorm_sq_eq_eLpNorm_sq g_k
      (μ := (volume : Measure EuclN).restrict Ω')]
    have h_lt_top : eLpNorm g_k 2 ((volume : Measure EuclN).restrict Ω') < ∞ :=
      lt_of_le_of_lt (eLpNorm_mono_measure g_k Measure.restrict_le_self)
        hg_k_l2.eLpNorm_lt_top
    exact ENNReal.pow_lt_top h_lt_top
  have h_LHS_lint_lt_top :
      ∫⁻ x in Ω'', (‖diffQuot k h u x‖ₑ : ℝ≥0∞) ^ 2 ∂(volume : Measure EuclN) < ∞ :=
    lt_of_le_of_lt h_lint h_RHS_lint_lt_top
  have hu_aestron : AEStronglyMeasurable u (volume : Measure EuclN) :=
    hu_l2.aestronglyMeasurable
  have hg_k_aestron : AEStronglyMeasurable g_k (volume : Measure EuclN) :=
    hg_k_l2.aestronglyMeasurable
  have hd_aestron : AEStronglyMeasurable (diffQuot k h u) (volume : Measure EuclN) :=
    aestronglyMeasurable_diffQuot (d := d) k h hu_aestron
  have h_LHS_aestron :
      AEStronglyMeasurable (fun x => (diffQuot k h u x) ^ 2)
        ((volume : Measure EuclN).restrict Ω'') := by
    refine ((hd_aestron.pow 2)).restrict
  have h_RHS_aestron :
      AEStronglyMeasurable (fun x => (g_k x) ^ 2)
        ((volume : Measure EuclN).restrict Ω') := by
    refine ((hg_k_aestron.pow 2)).restrict
  have h_LHS_eq :
      ∫ x in Ω'', (diffQuot k h u x) ^ 2 ∂(volume : Measure EuclN) =
        (∫⁻ x in Ω'', (‖diffQuot k h u x‖ₑ : ℝ≥0∞) ^ 2
          ∂(volume : Measure EuclN)).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun x => sq_nonneg _) h_LHS_aestron]
    refine congrArg ENNReal.toReal ?_
    refine lintegral_congr_ae ?_
    filter_upwards with x
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2, sq_abs]
  have h_RHS_eq :
      ∫ x in Ω', (g_k x) ^ 2 ∂(volume : Measure EuclN) =
        (∫⁻ y in Ω', (‖g_k y‖ₑ : ℝ≥0∞) ^ 2 ∂(volume : Measure EuclN)).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun x => sq_nonneg _) h_RHS_aestron]
    refine congrArg ENNReal.toReal ?_
    refine lintegral_congr_ae ?_
    filter_upwards with y
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2, sq_abs]
  rw [h_LHS_eq, h_RHS_eq]
  exact ENNReal.toReal_mono h_RHS_lint_lt_top.ne h_lint

end Sobolev
