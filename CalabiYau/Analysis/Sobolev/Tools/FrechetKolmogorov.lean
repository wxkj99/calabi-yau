-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Tools/FrechetKolmogorov.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Tools.ArzelaAscoli

@[expose] public section


noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open scoped ENNReal NNReal Convolution Pointwise

namespace Sobolev

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

lemma eLpNorm_translate_eq
    {p : ℝ≥0∞} {f : E → ℝ}
    (hf : AEStronglyMeasurable f volume) (h : E) :
    eLpNorm (fun x => f (x - h)) p volume = eLpNorm f p volume := by
  have hMP : MeasurePreserving (fun x : E => x - h) volume volume := by
    have hMP_neg : MeasurePreserving (fun x : E => x + (-h)) volume volume :=
      measurePreserving_add_right volume (-h)
    have hEq : (fun x : E => x - h) = (fun x : E => x + (-h)) := by
      funext x; rw [sub_eq_add_neg]
    rw [hEq]
    exact hMP_neg
  exact eLpNorm_comp_measurePreserving hf hMP

theorem lintegral_pow_le_pow_lintegral_prob
    {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsProbabilityMeasure ν]
    {pr : ℝ} (hpr_ge_one : 1 ≤ pr)
    {g : α → ℝ≥0∞} (hg : AEMeasurable g ν) :
    (∫⁻ s, g s ∂ν) ^ pr ≤ ∫⁻ s, (g s) ^ pr ∂ν := by
  classical
  by_cases hpr_one : pr = 1
  · simp [hpr_one]
  have hpr_pos : 0 < pr := lt_of_lt_of_le zero_lt_one hpr_ge_one
  have hpr_gt_one : 1 < pr := lt_of_le_of_ne hpr_ge_one (Ne.symm hpr_one)
  set q : ℝ := Real.conjExponent pr with hq_def
  have hHC : pr.HolderConjugate q :=
    Real.HolderConjugate.conjExponent hpr_gt_one
  have hone_meas : AEMeasurable (fun _ : α => (1 : ℝ≥0∞)) ν := aemeasurable_const
  have hHolder :
      (∫⁻ s, g s * 1 ∂ν) ≤
        (∫⁻ s, (g s) ^ pr ∂ν) ^ (1 / pr) *
          (∫⁻ s, (1 : ℝ≥0∞) ^ q ∂ν) ^ (1 / q) := by
    have := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ := ν) hHC hg hone_meas
    simpa using this
  have hone_lint : ∫⁻ s, (1 : ℝ≥0∞) ^ q ∂ν = 1 := by simp
  have hsimp_left : (∫⁻ s, g s * 1 ∂ν) = ∫⁻ s, g s ∂ν := by
    refine lintegral_congr_ae ?_
    filter_upwards with s using mul_one _
  rw [hsimp_left] at hHolder
  rw [hone_lint, ENNReal.one_rpow, mul_one] at hHolder
  have hpow :
      (∫⁻ s, g s ∂ν) ^ pr ≤ ((∫⁻ s, (g s) ^ pr ∂ν) ^ (1 / pr)) ^ pr :=
    ENNReal.rpow_le_rpow hHolder hpr_pos.le
  refine hpow.trans ?_
  rw [← ENNReal.rpow_mul, show (1 / pr) * pr = 1 by field_simp, ENNReal.rpow_one]

private lemma convolution_sub_eq_integral
    {η u : E → ℝ}
    (hη_cont : Continuous η) (hη_compact : HasCompactSupport η)
    (hη_int_eq_one : ∫ s, η s ∂(volume : Measure E) = 1)
    (hu_local : LocallyIntegrable u volume) (x : E) :
    (η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x - u x =
      ∫ s, η s • (u (x - s) - u x) ∂(volume : Measure E) := by
  have hη_int : Integrable η volume :=
    hη_cont.integrable_of_hasCompactSupport hη_compact
  have hCe : ConvolutionExistsAt η u x (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    hη_compact.convolutionExists_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ) hη_cont hu_local x
  have hint_etaUsmul :
      Integrable (fun s : E => η s • u (x - s)) volume := by
    refine hCe.congr ?_
    filter_upwards with s using by simp [ContinuousLinearMap.lsmul_apply]
  have hint_etaUx :
      Integrable (fun s : E => η s • u x) volume := hη_int.smul_const (u x)
  have h1 :
      (η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x =
        ∫ s, η s • u (x - s) ∂volume := by
    simp [MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply]
  have h2 : (∫ s, η s • u x ∂volume) = u x := by
    rw [show ∫ s, η s • u x ∂volume = (∫ s, η s ∂volume) • u x from
      integral_smul_const _ _]
    rw [hη_int_eq_one, one_smul]
  have hsub_eq :
      ∫ s, η s • (u (x - s) - u x) ∂volume =
        (∫ s, η s • u (x - s) ∂volume) - ∫ s, η s • u x ∂volume := by
    rw [← integral_sub hint_etaUsmul hint_etaUx]
    congr 1; funext s; rw [smul_sub]
  rw [h1, hsub_eq, h2]

private lemma integrable_eta_smul_translate_sub
    {η u : E → ℝ}
    (hη_cont : Continuous η) (hη_compact : HasCompactSupport η)
    (hu_local : LocallyIntegrable u volume) (x : E) :
    Integrable (fun s : E => η s • (u (x - s) - u x)) volume := by
  have hη_int : Integrable η volume :=
    hη_cont.integrable_of_hasCompactSupport hη_compact
  have hCe : ConvolutionExistsAt η u x (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    hη_compact.convolutionExists_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ) hη_cont hu_local x
  have hint_etaUsmul :
      Integrable (fun s : E => η s • u (x - s)) volume := by
    refine hCe.congr ?_
    filter_upwards with s using by simp [ContinuousLinearMap.lsmul_apply]
  have hint_etaUx :
      Integrable (fun s : E => η s • u x) volume := hη_int.smul_const (u x)
  have heq :
      (fun s : E => η s • (u (x - s) - u x)) =
        (fun s : E => η s • u (x - s)) - (fun s : E => η s • u x) := by
    funext s; rw [smul_sub]; rfl
  rw [heq]
  exact hint_etaUsmul.sub hint_etaUx

private lemma norm_eta_smul_eq_eta_mul_norm
    {η : E → ℝ} (hη_nonneg : ∀ y, 0 ≤ η y) (s : E) (r : ℝ) :
    ‖η s • r‖ = η s * ‖r‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hη_nonneg s)]

private lemma enorm_convolution_sub_le_lintegral
    {η u : E → ℝ}
    (hη_cont : Continuous η) (hη_compact : HasCompactSupport η)
    (hη_nonneg : ∀ y, 0 ≤ η y)
    (hη_int_eq_one : ∫ s, η s ∂(volume : Measure E) = 1)
    (hu_local : LocallyIntegrable u volume) (x : E) :
    (‖(η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x - u x‖ₑ : ℝ≥0∞) ≤
      ∫⁻ s, ENNReal.ofReal (η s) * (‖u (x - s) - u x‖ₑ : ℝ≥0∞) ∂volume := by
  classical
  have hf_eq :=
    convolution_sub_eq_integral hη_cont hη_compact hη_int_eq_one hu_local x
  have hint_diff_vol :
      Integrable (fun s : E => η s • (u (x - s) - u x)) volume :=
    integrable_eta_smul_translate_sub hη_cont hη_compact hu_local x
  rw [hf_eq]
  have hReal_norm_le :
      ‖∫ s, η s • (u (x - s) - u x) ∂volume‖ ≤
        ∫ s, ‖η s • (u (x - s) - u x)‖ ∂volume :=
    norm_integral_le_integral_norm _
  have hReal_to_lint :
      ENNReal.ofReal (∫ s, ‖η s • (u (x - s) - u x)‖ ∂volume) =
        ∫⁻ s, ENNReal.ofReal (η s) * (‖u (x - s) - u x‖ₑ : ℝ≥0∞) ∂volume := by
    rw [ofReal_integral_eq_lintegral_ofReal hint_diff_vol.norm
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)]
    refine lintegral_congr_ae ?_
    filter_upwards with s
    rw [norm_eta_smul_eq_eta_mul_norm hη_nonneg s,
      ENNReal.ofReal_mul (hη_nonneg s)]
    congr 1
    rw [ofReal_norm]
  have hf_norm_e :
      (‖∫ s, η s • (u (x - s) - u x) ∂volume‖ₑ : ℝ≥0∞) ≤
        ENNReal.ofReal (∫ s, ‖η s • (u (x - s) - u x)‖ ∂volume) := by
    rw [Real.enorm_eq_ofReal_abs]
    refine ENNReal.ofReal_le_ofReal ?_
    refine (?_ : |∫ s, η s • (u (x - s) - u x) ∂volume| ≤
      ‖∫ s, η s • (u (x - s) - u x) ∂volume‖).trans hReal_norm_le
    rw [Real.norm_eq_abs]
  exact hf_norm_e.trans (le_of_eq hReal_to_lint)

theorem lintegral_rpow_convolution_sub_le_translationAverage
    {pr : ℝ} (hpr_ge_one : 1 ≤ pr)
    {η : E → ℝ}
    (hη_cont : Continuous η) (hη_compact : HasCompactSupport η)
    (hη_nonneg : ∀ y, 0 ≤ η y)
    (hη_int_eq_one : ∫ s, η s ∂(volume : Measure E) = 1)
    {u : E → ℝ}
    (hu_meas : Measurable u)
    (hu_local : LocallyIntegrable u volume) :
    ∫⁻ x, (‖(η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x - u x‖ₑ : ℝ≥0∞) ^
        pr ∂volume ≤
      ∫⁻ s, ENNReal.ofReal (η s) *
        (∫⁻ x, (‖u (x - s) - u x‖ₑ : ℝ≥0∞) ^ pr ∂volume) ∂volume := by
  classical
  have hpr_pos : 0 < pr := lt_of_lt_of_le zero_lt_one hpr_ge_one
  set ρ : E → ℝ≥0∞ := fun y => ENNReal.ofReal (η y) with hρ_def
  set ν : Measure E := volume.withDensity ρ with hν_def
  have hη_int : Integrable η volume :=
    hη_cont.integrable_of_hasCompactSupport hη_compact
  have hρ_meas : Measurable ρ := hη_cont.measurable.ennreal_ofReal
  have hρ_lt_top : ∀ᵐ y ∂volume, ρ y < ∞ := by
    filter_upwards with y; simp [ρ]
  have hν_prob : IsProbabilityMeasure ν := by
    refine ⟨?_⟩
    rw [hν_def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hη_int
      (Filter.Eventually.of_forall hη_nonneg), hη_int_eq_one]
    simp
  have hPt_e : ∀ x : E,
      (‖(η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x - u x‖ₑ : ℝ≥0∞) ≤
        ∫⁻ s, ρ s * (‖u (x - s) - u x‖ₑ : ℝ≥0∞) ∂volume :=
    fun x =>
      enorm_convolution_sub_le_lintegral (d := d) hη_cont hη_compact hη_nonneg
        hη_int_eq_one hu_local x
  have hPt_e_pow : ∀ x : E,
      (‖(η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x - u x‖ₑ : ℝ≥0∞) ^ pr ≤
        (∫⁻ s, ρ s * (‖u (x - s) - u x‖ₑ : ℝ≥0∞) ∂volume) ^ pr := fun x =>
    ENNReal.rpow_le_rpow (hPt_e x) hpr_pos.le
  have hG_meas : ∀ x : E,
      AEMeasurable (fun s : E => (‖u (x - s) - u x‖ₑ : ℝ≥0∞)) ν := by
    intro x
    have h1 : Measurable (fun s : E => u (x - s) - u x) :=
      (hu_meas.comp (measurable_id.const_sub x)).sub measurable_const
    exact h1.enorm.aemeasurable
  have hPt_to_ν : ∀ x : E,
      ∫⁻ s, ρ s * (‖u (x - s) - u x‖ₑ : ℝ≥0∞) ∂volume =
        ∫⁻ s, (‖u (x - s) - u x‖ₑ : ℝ≥0∞) ∂ν := by
    intro x
    rw [hν_def]
    rw [lintegral_withDensity_eq_lintegral_mul_non_measurable volume hρ_meas hρ_lt_top]
    rfl
  have hJensen_ν : ∀ x : E,
      (∫⁻ s, (‖u (x - s) - u x‖ₑ : ℝ≥0∞) ∂ν) ^ pr ≤
        ∫⁻ s, ((‖u (x - s) - u x‖ₑ : ℝ≥0∞) ^ pr) ∂ν :=
    fun x =>
      lintegral_pow_le_pow_lintegral_prob (ν := ν) hpr_ge_one (hG_meas x)
  have hPt_ν_to_vol : ∀ x : E,
      ∫⁻ s, ((‖u (x - s) - u x‖ₑ : ℝ≥0∞) ^ pr) ∂ν =
        ∫⁻ s, ρ s * ((‖u (x - s) - u x‖ₑ : ℝ≥0∞) ^ pr) ∂volume := by
    intro x
    rw [hν_def]
    rw [lintegral_withDensity_eq_lintegral_mul_non_measurable volume hρ_meas hρ_lt_top]
    rfl
  have hOverall_pt : ∀ x : E,
      (‖(η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x - u x‖ₑ : ℝ≥0∞) ^ pr ≤
        ∫⁻ s, ρ s * ((‖u (x - s) - u x‖ₑ : ℝ≥0∞) ^ pr) ∂volume := by
    intro x
    refine (hPt_e_pow x).trans ?_
    rw [hPt_to_ν x]
    refine (hJensen_ν x).trans ?_
    rw [hPt_ν_to_vol x]
  have h_le_int : ∫⁻ x, (‖(η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x - u x‖ₑ : ℝ≥0∞) ^
        pr ∂volume ≤
      ∫⁻ x, ∫⁻ s, ρ s * ((‖u (x - s) - u x‖ₑ : ℝ≥0∞) ^ pr) ∂volume ∂volume := by
    refine lintegral_mono_ae ?_
    filter_upwards with x using hOverall_pt x
  refine h_le_int.trans ?_
  have hMeas_pair :
      Measurable (Function.uncurry fun (x : E) (s : E) =>
        ρ s * ((‖u (x - s) - u x‖ₑ : ℝ≥0∞) ^ pr)) := by
    have h_sub : Measurable (fun p : E × E => p.1 - p.2) :=
      measurable_fst.sub measurable_snd
    have h_u_sub : Measurable (fun p : E × E => u (p.1 - p.2)) :=
      hu_meas.comp h_sub
    have h_u_first : Measurable (fun p : E × E => u p.1) :=
      hu_meas.comp measurable_fst
    have h_diff : Measurable (fun p : E × E => u (p.1 - p.2) - u p.1) :=
      h_u_sub.sub h_u_first
    have h_e : Measurable (fun p : E × E => (‖u (p.1 - p.2) - u p.1‖ₑ : ℝ≥0∞)) :=
      h_diff.enorm
    have h_e_pow : Measurable
        (fun p : E × E => ((‖u (p.1 - p.2) - u p.1‖ₑ : ℝ≥0∞) ^ pr)) :=
      h_e.pow_const pr
    have h_ρ_snd : Measurable (fun p : E × E => ρ p.2) :=
      hρ_meas.comp measurable_snd
    exact h_ρ_snd.mul h_e_pow
  have hSwap :
      ∫⁻ x, ∫⁻ s, ρ s * ((‖u (x - s) - u x‖ₑ : ℝ≥0∞) ^ pr) ∂volume ∂volume =
        ∫⁻ s, ∫⁻ x, ρ s * ((‖u (x - s) - u x‖ₑ : ℝ≥0∞) ^ pr) ∂volume ∂volume :=
    lintegral_lintegral_swap hMeas_pair.aemeasurable
  rw [hSwap]
  refine lintegral_mono_ae ?_
  filter_upwards with s
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

theorem eLpNorm_convolution_sub_le_of_ae_translation_bound
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    {η : E → ℝ}
    (hη_cont : Continuous η) (hη_compact : HasCompactSupport η)
    (hη_nonneg : ∀ y, 0 ≤ η y)
    (hη_int_eq_one : ∫ s, η s ∂(volume : Measure E) = 1)
    {u : E → ℝ}
    (hu_meas : Measurable u)
    (hu_local : LocallyIntegrable u volume)
    {T : ℝ≥0∞}
    (hT_le : ∀ᵐ s ∂(volume : Measure E),
      η s ≠ 0 → eLpNorm (fun x => u (x - s) - u x) p volume ≤ T) :
    eLpNorm
      (fun x => (η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x - u x)
      p volume ≤ T := by
  classical
  have hp_ne : p ≠ 0 := by
    intro h0
    rw [h0] at hp_one
    exact absurd hp_one (by norm_num : ¬ (1 : ℝ≥0∞) ≤ 0)
  set pr : ℝ := p.toReal with hpr_def
  have hpr_pos : 0 < pr := ENNReal.toReal_pos hp_ne hp_top
  have hpr_ge_one : 1 ≤ pr := by
    have := ENNReal.toReal_mono hp_top hp_one
    simpa using this
  have hp_eq : p = ENNReal.ofReal pr := by
    rw [hpr_def]
    exact (ENNReal.ofReal_toReal hp_top).symm
  have hp0_pr : ENNReal.ofReal pr ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hpr_pos).ne'
  have hp_top_pr : ENNReal.ofReal pr ≠ ∞ := ENNReal.ofReal_ne_top
  have hpr_toReal : (ENNReal.ofReal pr).toReal = pr :=
    ENNReal.toReal_ofReal hpr_pos.le
  have hpr_inv_nn : 0 ≤ 1 / pr := by positivity
  have hLHS_eq :
      eLpNorm (fun x =>
          (η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x - u x)
        p volume =
        (∫⁻ x, (‖(η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x - u x‖ₑ : ℝ≥0∞)
            ^ pr ∂volume) ^ (1 / pr) := by
    have hmeas : AEStronglyMeasurable
        (fun x => (η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x - u x) volume :=
      ((hη_compact.continuous_convolution_left
        (L := ContinuousLinearMap.lsmul ℝ ℝ) hη_cont hu_local).measurable.sub
        hu_meas).aestronglyMeasurable
    rw [hp_eq, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0_pr hp_top_pr hmeas]
    simp [hpr_toReal]
  rw [hLHS_eq]
  have hcore := lintegral_rpow_convolution_sub_le_translationAverage hpr_ge_one
      hη_cont hη_compact hη_nonneg hη_int_eq_one hu_meas hu_local
  have hT_pow : ∀ᵐ s ∂(volume : Measure E),
      η s ≠ 0 →
        ∫⁻ x, (‖u (x - s) - u x‖ₑ : ℝ≥0∞) ^ pr ∂volume ≤ T ^ pr := by
    filter_upwards [hT_le] with s hT_s hηs_ne_zero
    have h := hT_s hηs_ne_zero
    have h_eq :
        eLpNorm (fun x => u (x - s) - u x) p volume =
          (∫⁻ x, (‖u (x - s) - u x‖ₑ : ℝ≥0∞) ^ pr ∂volume) ^ (1 / pr) := by
      have hmeas : AEStronglyMeasurable (fun x => u (x - s) - u x) volume :=
        ((hu_meas.comp (measurable_id.sub_const s)).sub hu_meas).aestronglyMeasurable
      rw [hp_eq, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0_pr hp_top_pr hmeas]
      simp [hpr_toReal]
    rw [h_eq] at h
    have hraise : ((∫⁻ x, (‖u (x - s) - u x‖ₑ : ℝ≥0∞) ^ pr ∂volume) ^ (1 / pr)) ^ pr ≤
        T ^ pr :=
      ENNReal.rpow_le_rpow h hpr_pos.le
    rw [← ENNReal.rpow_mul] at hraise
    rw [show (1 / pr) * pr = 1 by field_simp, ENNReal.rpow_one] at hraise
    exact hraise
  have hOuter :
      ∫⁻ s, ENNReal.ofReal (η s) *
        (∫⁻ x, (‖u (x - s) - u x‖ₑ : ℝ≥0∞) ^ pr ∂volume) ∂volume ≤
        T ^ pr * ∫⁻ s, ENNReal.ofReal (η s) ∂volume := by
    have h1 :
        ∫⁻ s, ENNReal.ofReal (η s) *
          (∫⁻ x, (‖u (x - s) - u x‖ₑ : ℝ≥0∞) ^ pr ∂volume) ∂volume ≤
          ∫⁻ s, ENNReal.ofReal (η s) * (T ^ pr) ∂volume := by
      refine lintegral_mono_ae ?_
      filter_upwards [hT_pow] with s hT_pow_s
      by_cases hηs : η s = 0
      · simp [hηs]
      · have h := hT_pow_s hηs
        gcongr
    have hpull :
        ∫⁻ s, ENNReal.ofReal (η s) * (T ^ pr) ∂volume =
          T ^ pr * ∫⁻ s, ENNReal.ofReal (η s) ∂volume := by
      rw [lintegral_mul_const'']
      · ring
      · exact hη_cont.measurable.ennreal_ofReal.aemeasurable
    exact h1.trans (le_of_eq hpull)
  have hη_int_lint : ∫⁻ s, ENNReal.ofReal (η s) ∂volume = 1 := by
    have hη_int : Integrable η volume :=
      hη_cont.integrable_of_hasCompactSupport hη_compact
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hη_int
      (Filter.Eventually.of_forall hη_nonneg)]
    rw [hη_int_eq_one]
    simp
  rw [hη_int_lint, mul_one] at hOuter
  have h_inner_bound :
      ∫⁻ x, (‖(η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x - u x‖ₑ : ℝ≥0∞) ^ pr
        ∂volume ≤ T ^ pr :=
    hcore.trans hOuter
  have hraise :
      (∫⁻ x, (‖(η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x - u x‖ₑ : ℝ≥0∞) ^ pr
        ∂volume) ^ (1 / pr) ≤ (T ^ pr) ^ (1 / pr) :=
    ENNReal.rpow_le_rpow h_inner_bound hpr_inv_nn
  refine hraise.trans ?_
  rw [← ENNReal.rpow_mul]
  rw [show pr * (1 / pr) = 1 by field_simp, ENNReal.rpow_one]

private lemma volume_lt_top_of_compact
    {K : Set E} (hK_compact : IsCompact K) :
    (volume : Measure E) K < ∞ :=
  hK_compact.measure_lt_top

private lemma integrable_of_memLp_compactSupport
    {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {K : Set E} (hK_compact : IsCompact K)
    {u : E → ℝ} (hu_memLp : MemLp u p volume)
    (hu_support : ∀ x, x ∉ K → u x = 0) :
    Integrable u volume := by
  classical
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have hK_vol : volume K ≠ ∞ := hK_compact.measure_lt_top.ne
  have hu_memLp_one : MemLp u 1 volume :=
    hu_memLp.mono_exponent_of_measure_support_ne_top hu_support hK_vol hp_one
  exact (memLp_one_iff_integrable.mp hu_memLp_one)

private lemma convolution_support_subset_cthickening
    {ε : ℝ} (_hε : 0 ≤ ε)
    {K : Set E} {u η : E → ℝ}
    (hu_support : ∀ x, x ∉ K → u x = 0)
    (hη_support : Function.support η ⊆ Metric.closedBall (0 : E) ε) (x : E)
    (hx : x ∉ Metric.cthickening ε K) :
    (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) x = 0 := by
  classical
  rw [convolution_def]
  have h_zero_integrand : ∀ t : E, (ContinuousLinearMap.lsmul ℝ ℝ) (u t) (η (x - t)) = 0 := by
    intro t
    by_cases hut : u t = 0
    · simp [hut]
    by_cases hη_xmt : η (x - t) = 0
    · simp [hη_xmt]
    exfalso
    have ht_K : t ∈ K := by
      by_contra h
      exact hut (hu_support t h)
    have h_xmt_support : (x - t) ∈ Function.support η := Function.mem_support.mpr hη_xmt
    have h_ht : (x - t) ∈ Metric.closedBall (0 : E) ε := hη_support h_xmt_support
    have h_dist : dist x t ≤ ε := by
      have hmem : (x - t) ∈ Metric.closedBall (0 : E) ε := h_ht
      rw [Metric.mem_closedBall, dist_zero_right] at hmem
      rwa [dist_eq_norm]
    have h_in_cthickening : x ∈ Metric.cthickening ε K :=
      Metric.mem_cthickening_of_dist_le x t ε K ht_K h_dist
    exact hx h_in_cthickening
  simp [h_zero_integrand]

private lemma cauchy_lp_of_uniformly_cauchy_on_compact_support
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    {K : Set E} (hK_compact : IsCompact K)
    {g : ℕ → E → ℝ}
    (_hg_cont : ∀ n, Continuous (g n))
    (hg_support : ∀ n, ∀ x, x ∉ K → g n x = 0)
    (hg_uCauchy : ∀ ε > 0, ∃ J : ℕ, ∀ j ≥ J, ∀ l ≥ J, ∀ x ∈ K,
      dist (g j x) (g l x) < ε) :
    ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j ≥ J, ∀ l ≥ J,
      eLpNorm (fun x => g j x - g l x) p volume ≤ ENNReal.ofReal ε := by
  classical
  have hp_ne : p ≠ 0 := by
    intro h0
    rw [h0] at hp_one
    exact absurd hp_one (by norm_num : ¬ (1 : ℝ≥0∞) ≤ 0)
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have hK_vol_lt_top : (volume : Measure E) K < ∞ := hK_compact.measure_lt_top
  set vK : ℝ≥0∞ := (volume : Measure E) K with hvK_def
  have hp_toReal_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne hp_top
  have hp_inv_nn : 0 ≤ p.toReal⁻¹ := inv_nonneg.mpr hp_toReal_pos.le
  set M : ℝ≥0∞ := vK ^ (p.toReal⁻¹) with hM_def
  have hM_lt_top : M < ∞ := ENNReal.rpow_lt_top_of_nonneg hp_inv_nn hK_vol_lt_top.ne
  have h_eLp_le : ∀ j l, ∀ η : ℝ, 0 < η →
      (∀ x, ‖g j x - g l x‖ ≤ η) →
        eLpNorm (fun x => g j x - g l x) p volume ≤ M * ENNReal.ofReal η := by
    intro j l η hη hbnd
    have h_diff_support : ∀ x, x ∉ K → g j x - g l x = 0 := by
      intro x hx
      rw [hg_support j x hx, hg_support l x hx, sub_zero]
    have h_indicator : (fun x => g j x - g l x) =
        K.indicator (fun x => g j x - g l x) := by
      funext x
      by_cases hx : x ∈ K
      · simp [hx]
      · simp [hx, h_diff_support x hx]
    rw [h_indicator, eLpNorm_indicator_eq_eLpNorm_restrict hK_meas]
    have hbnd_ae : ∀ᵐ x ∂(volume.restrict K), ‖g j x - g l x‖ ≤ η :=
      Filter.Eventually.of_forall hbnd
    have h_le := eLpNorm_le_of_ae_bound (μ := volume.restrict K) (p := p)
      ((_hg_cont j).sub (_hg_cont l)).aestronglyMeasurable hbnd_ae
    have h_univ : (volume.restrict K) Set.univ = vK := by
      rw [hvK_def, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    rw [h_univ] at h_le
    exact h_le
  intro ε hε
  by_cases hM_zero : M = 0
  · rcases hg_uCauchy 1 (by norm_num) with ⟨J, hJ⟩
    refine ⟨J, fun j hj l hl => ?_⟩
    have hbnd : ∀ x, ‖g j x - g l x‖ ≤ 1 := by
      intro x
      by_cases hx : x ∈ K
      · have hd := hJ j hj l hl x hx
        rw [Real.dist_eq] at hd
        rw [Real.norm_eq_abs]
        exact hd.le
      · rw [hg_support j x hx, hg_support l x hx, sub_zero, norm_zero]
        norm_num
    have h := h_eLp_le j l 1 (by norm_num) hbnd
    rw [hM_zero, zero_mul] at h
    exact h.trans bot_le
  · have hM_pos : 0 < M := pos_iff_ne_zero.mpr hM_zero
    have hε_e_pos : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
    set ε_e : ℝ≥0∞ := ENNReal.ofReal ε / M with hε_e_def
    have hε_e_pos' : 0 < ε_e := ENNReal.div_pos hε_e_pos.ne' hM_lt_top.ne
    have hε_e_lt_top : ε_e < ∞ :=
      ENNReal.div_lt_top ENNReal.ofReal_ne_top hM_zero
    set η_real : ℝ := ε_e.toReal with hη_real_def
    have hη_real_pos : 0 < η_real := ENNReal.toReal_pos hε_e_pos'.ne' hε_e_lt_top.ne
    have h_M_eta : M * ENNReal.ofReal η_real = ENNReal.ofReal ε := by
      rw [hη_real_def, ENNReal.ofReal_toReal hε_e_lt_top.ne]
      rw [hε_e_def, ENNReal.mul_div_cancel hM_zero hM_lt_top.ne]
    rcases hg_uCauchy η_real hη_real_pos with ⟨J, hJ⟩
    refine ⟨J, fun j hj l hl => ?_⟩
    have hbnd : ∀ x, ‖g j x - g l x‖ ≤ η_real := by
      intro x
      by_cases hx : x ∈ K
      · have hd := hJ j hj l hl x hx
        rw [Real.dist_eq] at hd
        rw [Real.norm_eq_abs]
        exact hd.le
      · rw [hg_support j x hx, hg_support l x hx, sub_zero, norm_zero]
        exact hη_real_pos.le
    have h := h_eLp_le j l η_real hη_real_pos hbnd
    rw [h_M_eta] at h
    exact h

theorem tendsto_subseq_of_uniform_translation_in_Lp
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    {K : Set E} (hK_compact : IsCompact K)
    {u : ℕ → E → ℝ}
    (hu_mem : ∀ n, MeasureTheory.MemLp (u n) p volume)
    (hu_support : ∀ n, ∀ x, x ∉ K → u n x = 0)
    {R : ℝ}
    (hu_bdd : ∀ n, eLpNorm (u n) p volume ≤ ENNReal.ofReal R)
    (hu_translation :
      ∀ ε > 0, ∃ δ > 0, ∀ n, ∀ h : E,
        ‖h‖ < δ →
        eLpNorm (fun x => u n (x - h) - u n x) p volume ≤ ENNReal.ofReal ε) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ (u_lim : E → ℝ),
        MeasureTheory.MemLp u_lim p volume ∧
        Filter.Tendsto
          (fun k => eLpNorm (fun x => u (φ k) x - u_lim x) p volume)
          Filter.atTop (𝓝 0) := by
  classical
  set K' : Set E := Metric.cthickening 1 K with hK'_def
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have hK'_compact : IsCompact K' := hK_compact.cthickening
  have hK'_meas : MeasurableSet K' := hK'_compact.isClosed.measurableSet
  have hK_vol_lt_top : (volume : Measure E) K < ∞ :=
    volume_lt_top_of_compact (d := d) hK_compact
  have hK_vol_ne_top : (volume : Measure E) K ≠ ∞ := hK_vol_lt_top.ne
  set vFn : ℕ → E → ℝ := fun n =>
    K.indicator ((hu_mem n).aestronglyMeasurable.mk (u n)) with hvFn_def
  have hv_meas : ∀ n, Measurable (vFn n) := by
    intro n
    refine Measurable.indicator ?_ hK_meas
    exact (hu_mem n).aestronglyMeasurable.measurable_mk
  have hv_support : ∀ n, ∀ x, x ∉ K → vFn n x = 0 := by
    intro n x hx
    simp [vFn, hx]
  have hv_aeEq_u : ∀ n, vFn n =ᵐ[volume] u n := by
    intro n
    have h1 : (hu_mem n).aestronglyMeasurable.mk (u n) =ᵐ[volume] u n :=
      ((hu_mem n).aestronglyMeasurable.ae_eq_mk).symm
    have h3 : (K.indicator (u n) : E → ℝ) = u n := by
      funext x
      by_cases hxK : x ∈ K
      · simp [hxK]
      · rw [Set.indicator_of_notMem hxK, hu_support n x hxK]
    have h2 : vFn n =ᵐ[volume] K.indicator (u n) := by
      simp only [vFn]
      filter_upwards [h1] with x hx
      simp only [Set.indicator]
      split_ifs with _
      · exact hx
      · rfl
    calc vFn n =ᵐ[volume] K.indicator (u n) := h2
      _ = u n := h3
  have hv_eLpNorm : ∀ n, eLpNorm (vFn n) p volume = eLpNorm (u n) p volume := fun n =>
    eLpNorm_congr_ae (hv_aeEq_u n)
  have hv_bdd : ∀ n, eLpNorm (vFn n) p volume ≤ ENNReal.ofReal R := fun n =>
    (hv_eLpNorm n).symm ▸ hu_bdd n
  have hv_memLp : ∀ n, MemLp (vFn n) p volume := fun n =>
    memLp_iff.mpr (by
      rw [hv_eLpNorm n]; exact (hu_mem n).eLpNorm_lt_top)
  have hv_translate_aeEq : ∀ n h,
      (fun x => vFn n (x - h)) =ᵐ[volume] (fun x => u n (x - h)) := by
    intro n h
    have hMP : MeasurePreserving (fun x : E => x - h) volume volume := by
      have hMP_neg : MeasurePreserving (fun x : E => x + (-h)) volume volume :=
        measurePreserving_add_right volume (-h)
      have hEq : (fun x : E => x - h) = (fun x : E => x + (-h)) := by
        funext x; rw [sub_eq_add_neg]
      rw [hEq]
      exact hMP_neg
    have := hMP.quasiMeasurePreserving.ae_eq_comp (hv_aeEq_u n)
    exact this
  have hv_translation : ∀ ε > 0, ∃ δ > 0, ∀ n, ∀ h : E,
      ‖h‖ < δ →
      eLpNorm (fun x => vFn n (x - h) - vFn n x) p volume ≤ ENNReal.ofReal ε := by
    intro ε hε
    rcases hu_translation ε hε with ⟨δ, hδ_pos, hδ_bnd⟩
    refine ⟨δ, hδ_pos, fun n h hh => ?_⟩
    have hEq : (fun x => vFn n (x - h) - vFn n x) =ᵐ[volume]
        (fun x => u n (x - h) - u n x) := by
      have h1 := hv_translate_aeEq n h
      have h2 := hv_aeEq_u n
      filter_upwards [h1, h2] with x hx1 hx2
      rw [hx1, hx2]
    rw [eLpNorm_congr_ae hEq]
    exact hδ_bnd n h hh
  have hv_int : ∀ n, Integrable (vFn n) volume := fun n =>
    integrable_of_memLp_compactSupport (d := d) hp_one hK_compact (hv_memLp n) (hv_support n)
  have hv_local : ∀ n, LocallyIntegrable (vFn n) volume := fun n =>
    (hv_int n).locallyIntegrable
  set εFn : ℕ → ℝ := fun k => (1 : ℝ) / ((k : ℝ) + 1) with hεFn_def
  have hε_pos : ∀ k, 0 < εFn k := fun k => by
    rw [hεFn_def]
    apply div_pos one_pos
    positivity
  have hε_le_one : ∀ k, εFn k ≤ 1 := fun k => by
    have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have h1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith
    have hpos : (0 : ℝ) < (k : ℝ) + 1 := by linarith
    rw [hεFn_def, div_le_one hpos]
    exact h1
  have hε_tendsto : Filter.Tendsto εFn Filter.atTop (𝓝 0) := by
    rw [hεFn_def]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  set ηFn : ℕ → E → ℝ := fun k => mollifierEps (d := d) (hε_pos k) with hηFn_def
  have hη_smooth : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (ηFn k) := fun k =>
    mollifierEps_smooth (hε_pos k)
  have hη_cont : ∀ k, Continuous (ηFn k) := fun k => (hη_smooth k).continuous
  have hη_compact : ∀ k, HasCompactSupport (ηFn k) := fun k =>
    mollifierEps_compactSupport (hε_pos k)
  have hη_nonneg : ∀ k, ∀ y, 0 ≤ (ηFn k) y := fun k y =>
    mollifierEps_nonneg (hε_pos k) y
  have hη_int_eq_one : ∀ k, ∫ s, (ηFn k) s ∂(volume : Measure E) = 1 := fun k =>
    mollifierEps_integral_eq_one (hε_pos k)
  have hη_support_subset_eps_ball : ∀ k,
      Function.support (ηFn k) ⊆ Metric.closedBall (0 : E) (εFn k) := fun k =>
    mollifierEps_support_subset_closedBall_eps (hε_pos k)
  have hη_support_subset_one_ball : ∀ k,
      Function.support (ηFn k) ⊆ Metric.closedBall (0 : E) 1 := by
    intro k
    refine (hη_support_subset_eps_ball k).trans ?_
    exact Metric.closedBall_subset_closedBall (hε_le_one k)
  set fConvergence : ℕ → ℕ → E → ℝ := fun k n =>
    ((ηFn k) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (vFn n)) with hfConvergence_def
  have hfConvergence_cont : ∀ k n, Continuous (fConvergence k n) := fun k n => by
    refine HasCompactSupport.continuous_convolution_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (hη_compact k) ?_ (hv_local n)
    exact hη_cont k
  have hfConvergence_alt : ∀ k n,
      fConvergence k n = (vFn n) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (ηFn k) := by
    intro k n
    funext x
    change (ηFn k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] vFn n) x =
      (vFn n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ηFn k) x
    rw [convolution_def, convolution_def]
    have h_translate :
        ∫ t : E, (ContinuousLinearMap.lsmul ℝ ℝ) (ηFn k t) (vFn n (x - t)) ∂volume =
        ∫ t : E, (ContinuousLinearMap.lsmul ℝ ℝ) (ηFn k (x - t)) (vFn n (x - (x - t))) ∂volume := by
      let f : E → ℝ := fun s =>
        (ContinuousLinearMap.lsmul ℝ ℝ) (ηFn k s) (vFn n (x - s))
      have h := integral_sub_left_eq_self f (volume : Measure E) x
      simpa [f] using h.symm
    rw [h_translate]
    have h_eqfn :
        (fun t : E =>
          (ContinuousLinearMap.lsmul ℝ ℝ) (ηFn k (x - t)) (vFn n (x - (x - t)))) =
        (fun t : E => (ContinuousLinearMap.lsmul ℝ ℝ) (vFn n t) (ηFn k (x - t))) := by
      funext t
      rw [sub_sub_cancel]
      simp [ContinuousLinearMap.lsmul_apply, mul_comm]
    rw [h_eqfn]
  have hfConvergence_support : ∀ k n, ∀ x, x ∉ K' → (fConvergence k n) x = 0 := by
    intro k n x hx
    rw [hfConvergence_alt k n]
    refine convolution_support_subset_cthickening (d := d) (zero_le_one) (hv_support n)
      (hη_support_subset_one_ball k) x hx
  have hConvergenceSub_bnd : ∀ ε : ℝ, 0 < ε → ∃ K0 : ℕ, ∀ k ≥ K0, ∀ n,
      eLpNorm (fun x => (fConvergence k n) x - vFn n x) p volume ≤
        ENNReal.ofReal ε := by
    intro ε hε
    rcases hv_translation ε hε with ⟨δ, hδ_pos, hδ_bnd⟩
    rw [Metric.tendsto_atTop] at hε_tendsto
    rcases hε_tendsto δ hδ_pos with ⟨K0, hK0⟩
    refine ⟨K0, fun k hk n => ?_⟩
    have hεk_lt : εFn k < δ := by
      have hd := hK0 k hk
      rw [Real.dist_eq, sub_zero] at hd
      have habs : εFn k = |εFn k| := (abs_of_pos (hε_pos k)).symm
      rw [habs]
      exact hd
    refine eLpNorm_convolution_sub_le_of_ae_translation_bound
      hp_one hp_top (hη_cont k) (hη_compact k) (hη_nonneg k) (hη_int_eq_one k)
      (hv_meas n) (hv_local n) ?_
    filter_upwards with s hs
    have hs_support : s ∈ Function.support (ηFn k) := Function.mem_support.mpr hs
    have hs_in_ball : s ∈ Metric.closedBall (0 : E) (εFn k) :=
      hη_support_subset_eps_ball k hs_support
    have hs_norm_le : ‖s‖ ≤ εFn k := by
      rw [Metric.mem_closedBall, dist_zero_right] at hs_in_ball
      exact hs_in_ball
    have hs_norm_lt : ‖s‖ < δ := lt_of_le_of_lt hs_norm_le hεk_lt
    exact hδ_bnd n s hs_norm_lt
  have h_supnorm_bound : ∀ k, ∃ M_k : ℝ, 0 ≤ M_k ∧ ∀ y, ‖ηFn k y‖ ≤ M_k :=
    fun k => exists_norm_bound_of_continuous_compactSupport (hη_cont k) (hη_compact k)
  have h_lip_bound : ∀ k, ∃ L_k : ℝ, 0 ≤ L_k ∧ ∀ x y, ‖ηFn k x - ηFn k y‖ ≤ L_k * ‖x - y‖ :=
    fun k => lipschitz_of_contDiff_compactSupport
      ((hη_smooth k).of_le (by norm_cast)) (hη_compact k)
  set vK : ℝ≥0∞ := (volume : Measure E) K with hvK_def
  have h_int_norm_bound : ∀ n,
      ∫ t, ‖vFn n t‖ ∂(volume : Measure E) ≤
        (ENNReal.ofReal R * vK ^ ((1 : ℝ) - p.toReal⁻¹)).toReal := by
    intro n
    have hp_ne : p ≠ 0 := by
      intro h0
      rw [h0] at hp_one
      exact absurd hp_one (by norm_num : ¬ (1 : ℝ≥0∞) ≤ 0)
    have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne hp_top
    have h_indicator : (fun x => ‖vFn n x‖) = K.indicator (fun x => ‖vFn n x‖) := by
      funext x
      by_cases hxK : x ∈ K
      · simp [hxK]
      · rw [Set.indicator_of_notMem hxK, hv_support n x hxK, norm_zero]
    have h_eLp1_eq :
        eLpNorm (vFn n) 1 volume = eLpNorm (vFn n) 1 (volume.restrict K) := by
      have h_ind_eq : (vFn n) = K.indicator (vFn n) := by
        funext x
        by_cases hxK : x ∈ K
        · simp [hxK]
        · rw [Set.indicator_of_notMem hxK, hv_support n x hxK]
      conv_lhs => rw [h_ind_eq]
      exact MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict (μ := volume)
        (s := K) (p := 1) (f := vFn n) hK_meas
    have h_eLpp_eq :
        eLpNorm (vFn n) p volume = eLpNorm (vFn n) p (volume.restrict K) := by
      have h_ind_eq : (vFn n) = K.indicator (vFn n) := by
        funext x
        by_cases hxK : x ∈ K
        · simp [hxK]
        · rw [Set.indicator_of_notMem hxK, hv_support n x hxK]
      conv_lhs => rw [h_ind_eq]
      exact MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict (μ := volume)
        (s := K) (p := p) (f := vFn n) hK_meas
    have : IsFiniteMeasure (volume.restrict K) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      exact hK_vol_lt_top
    have h_holder := MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (p := 1) (q := p) (μ := volume.restrict K) hp_one
      (hv_meas n).aestronglyMeasurable
    have h_restrict_univ : (volume.restrict K) Set.univ = vK := by
      rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    rw [h_restrict_univ] at h_holder
    rw [← h_eLp1_eq, ← h_eLpp_eq] at h_holder
    have h_combine : eLpNorm (vFn n) 1 volume ≤ ENNReal.ofReal R *
        vK ^ ((1 : ℝ) - p.toReal⁻¹) := by
      refine h_holder.trans ?_
      have h1 : eLpNorm (vFn n) p volume ≤ ENNReal.ofReal R := hv_bdd n
      have h2 : (1 : ℝ≥0∞).toReal = 1 := ENNReal.toReal_one
      have h3 : (1 : ℝ) / 1 = 1 := by norm_num
      have h4 : (1 : ℝ) / 1 - 1 / p.toReal = 1 - p.toReal⁻¹ := by
        rw [h3, one_div]
      rw [h2, h4]
      exact mul_le_mul' h1 le_rfl
    have h_lp1_int : eLpNorm (vFn n) 1 volume = ∫⁻ t, ‖vFn n t‖ₑ ∂volume := by
      have := eLpNorm_one_eq_lintegral_enorm (μ := volume) (f := vFn n)
        (hv_meas n).aestronglyMeasurable
      exact this
    rw [h_lp1_int] at h_combine
    have h_int_eq :
        ∫ t, ‖vFn n t‖ ∂(volume : Measure E) =
          (∫⁻ t, ‖vFn n t‖ₑ ∂(volume : Measure E)).toReal := by
      rw [MeasureTheory.integral_norm_eq_lintegral_enorm (hv_meas n).aestronglyMeasurable]
    rw [h_int_eq]
    refine ENNReal.toReal_mono ?_ h_combine
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    refine ENNReal.rpow_ne_top_of_nonneg ?_ hK_vol_ne_top
    have hpinv : p.toReal⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right
      have : (1 : ℝ) ≤ p.toReal := by
        have := ENNReal.toReal_mono hp_top hp_one
        simpa using this
      exact this
    linarith
  set Sbound : ℝ := (ENNReal.ofReal R * vK ^ ((1 : ℝ) - p.toReal⁻¹)).toReal with hSbound_def
  have hSbound_nn : 0 ≤ Sbound := ENNReal.toReal_nonneg
  have h_fConvergence_supnorm_uniform : ∀ k, ∃ C_k : ℝ, 0 < C_k ∧
      ∀ n, ∀ x, |fConvergence k n x| ≤ C_k := by
    intro k
    rcases h_supnorm_bound k with ⟨M_k, hM_k_nn, hM_k⟩
    refine ⟨M_k * Sbound + 1, by linarith [mul_nonneg hM_k_nn hSbound_nn], ?_⟩
    intro n x
    rw [show fConvergence k n = vFn n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ηFn k from
      hfConvergence_alt k n]
    have hbnd := convolution_sup_le_holder (d := d)
      (hv_int n) (hη_cont k).aestronglyMeasurable hM_k x
    have hbnd2 := hbnd.trans (mul_le_mul_of_nonneg_left (h_int_norm_bound n) hM_k_nn)
    have h_norm_eq_abs : ‖(vFn n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ηFn k) x‖ =
        |(vFn n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ηFn k) x| := Real.norm_eq_abs _
    rw [← h_norm_eq_abs]
    linarith
  have h_fConvergence_lip_uniform : ∀ k, ∃ L_k : ℝ, ∃ hL_k_nn : 0 ≤ L_k,
      ∀ n, LipschitzWith ⟨L_k, hL_k_nn⟩ (fConvergence k n) := by
    intro k
    rcases h_lip_bound k with ⟨L_eta_k, hL_eta_k_nn, hL_eta_k⟩
    refine ⟨L_eta_k * Sbound, mul_nonneg hL_eta_k_nn hSbound_nn, ?_⟩
    intro n
    have hConvergenceAlt := hfConvergence_alt k n
    rw [hConvergenceAlt]
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have h := convolution_lipschitz_with (d := d) (hv_int n) (hη_cont k)
      (hη_compact k) hL_eta_k x y
    have hbnd_int : L_eta_k * (∫ t, ‖vFn n t‖ ∂volume) ≤ L_eta_k * Sbound :=
      mul_le_mul_of_nonneg_left (h_int_norm_bound n) hL_eta_k_nn
    have hh :
        ‖(vFn n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ηFn k) x -
          (vFn n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ηFn k) y‖ ≤
        (L_eta_k * Sbound) * ‖x - y‖ := by
      refine h.trans ?_
      gcongr
    rw [dist_eq_norm, dist_eq_norm]
    exact hh
  have hExtract : ∀ (k : ℕ) (σ : ℕ → ℕ) (_hσ : StrictMono σ),
      ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∃ v_k : E → ℝ,
        Continuous v_k ∧
        TendstoUniformlyOn (fun j => fConvergence k (σ (τ j))) v_k atTop K' := by
    intro k σ _hσ
    rcases h_fConvergence_supnorm_uniform k with ⟨C_k, hC_k_pos, hC_k_bd⟩
    rcases h_fConvergence_lip_uniform k with ⟨L_k, hL_k_nn, hL_k_lip⟩
    rcases tendsto_subseq_of_uniformly_lipschitz_uniformly_bounded (d := d)
      hK'_compact (f := fun j => fConvergence k (σ j))
      (fun j => hfConvergence_cont k (σ j)) hC_k_pos
      (fun j x => hC_k_bd (σ j) x) hL_k_nn (fun j => hL_k_lip (σ j)) with
      ⟨τ, hτ_mono, v_k, hv_k_cont, hv_k_uniform⟩
    exact ⟨τ, hτ_mono, v_k, hv_k_cont, hv_k_uniform⟩
  let StateType := { σ : ℕ → ℕ // StrictMono σ }
  let stateRec : ℕ → StateType := fun k => Nat.rec
    (motive := fun _ => StateType)
    ⟨id, strictMono_id⟩
    (fun k_prev prev =>
      ⟨prev.val ∘ Classical.choose (hExtract (k_prev + 1) prev.val prev.property),
        StrictMono.comp prev.property
          (Classical.choose_spec (hExtract (k_prev + 1) prev.val prev.property)).1⟩)
    k
  let φAux : ℕ → ℕ := fun j => (stateRec j).val j
  have hφAux_mono : StrictMono φAux := by
    intro a b hab
    have hStep : ∀ k, φAux k < φAux (k + 1) := by
      intro k
      have hSt_val_eq : (stateRec (k + 1)).val =
          (stateRec k).val ∘
            Classical.choose (hExtract (k + 1) (stateRec k).val (stateRec k).property) := rfl
      have hτ_mono :=
        (Classical.choose_spec (hExtract (k + 1) (stateRec k).val (stateRec k).property)).1
      have h1 : φAux (k + 1) = (stateRec k).val
          (Classical.choose (hExtract (k + 1) (stateRec k).val (stateRec k).property) (k + 1)) := by
        change (stateRec (k + 1)).val (k + 1) = _
        rw [hSt_val_eq]; rfl
      have h2 : φAux k = (stateRec k).val k := rfl
      rw [h1, h2]
      apply (stateRec k).property
      have hge := hτ_mono.id_le
      have h_at : (id (k + 1) : ℕ) ≤
        Classical.choose (hExtract (k + 1) (stateRec k).val (stateRec k).property) (k + 1) :=
        hge (k + 1)
      simp only [id_eq] at h_at
      omega
    exact (strictMono_nat_of_lt_succ hStep) hab
  have hTail : ∀ k, ∀ m ≥ k, ∃ τ : ℕ → ℕ, StrictMono τ ∧
      (stateRec m).val = (stateRec k).val ∘ τ := by
    intro k m hkm
    induction m, hkm using Nat.le_induction with
    | base =>
      exact ⟨id, strictMono_id, by simp⟩
    | succ m hkm IH =>
      rcases IH with ⟨τ', hτ'_mono, hτ'_eq⟩
      let τStep_m := Classical.choose (hExtract (m + 1) (stateRec m).val (stateRec m).property)
      have hτStep_m_mono : StrictMono τStep_m :=
        (Classical.choose_spec (hExtract (m + 1) (stateRec m).val (stateRec m).property)).1
      have h_succ_eq : (stateRec (m + 1)).val = (stateRec m).val ∘ τStep_m := rfl
      refine ⟨τ' ∘ τStep_m, hτ'_mono.comp hτStep_m_mono, ?_⟩
      rw [h_succ_eq, hτ'_eq]
      ext n
      simp [Function.comp]
  have hLimSeq : ∀ k, ∃ wSeq_k : E → ℝ, Continuous wSeq_k ∧
      TendstoUniformlyOn (fun j => fConvergence (k + 1) ((stateRec (k + 1)).val j)) wSeq_k atTop K' := by
    intro k
    let τStep_k := Classical.choose (hExtract (k + 1) (stateRec k).val (stateRec k).property)
    have hτStep_k_spec :=
      Classical.choose_spec (hExtract (k + 1) (stateRec k).val (stateRec k).property)
    obtain ⟨_, v_k, hv_k_cont, hv_k_uniform⟩ := hτStep_k_spec
    have h_eq : (stateRec (k + 1)).val = (stateRec k).val ∘ τStep_k := rfl
    refine ⟨v_k, hv_k_cont, ?_⟩
    rw [show (fun j => fConvergence (k + 1) ((stateRec (k + 1)).val j)) =
      (fun j => fConvergence (k + 1) ((stateRec k).val (τStep_k j))) from by
        funext j; rw [h_eq]; rfl]
    exact hv_k_uniform
  have hDiagCv : ∀ k, ∃ wSeq_k : E → ℝ, Continuous wSeq_k ∧
      ∀ ε > 0, ∃ J : ℕ, ∀ j ≥ J, ∀ x ∈ K',
        dist (wSeq_k x) (fConvergence (k + 1) (φAux j) x) < ε := by
    intro k
    rcases hLimSeq k with ⟨wSeq_k, hwSeq_k_cont, hwSeq_k_uniform⟩
    refine ⟨wSeq_k, hwSeq_k_cont, ?_⟩
    intro ε hε
    rw [Metric.tendstoUniformlyOn_iff] at hwSeq_k_uniform
    have hJ_ev := hwSeq_k_uniform ε hε
    rw [Filter.eventually_atTop] at hJ_ev
    rcases hJ_ev with ⟨J0, hJ0⟩
    refine ⟨max (k + 1) J0, fun j hj x hxK' => ?_⟩
    have hjk : k + 1 ≤ j := le_of_max_le_left hj
    have hjJ0 : J0 ≤ j := le_of_max_le_right hj
    rcases hTail (k + 1) j hjk with ⟨τ, hτ_mono, hτ_eq⟩
    have hφAux_eq : φAux j = (stateRec (k + 1)).val (τ j) := by
      change (stateRec j).val j = _
      rw [hτ_eq]; rfl
    rw [hφAux_eq]
    have hτ_ge : J0 ≤ τ j := le_trans hjJ0 (hτ_mono.id_le j)
    exact hJ0 (τ j) hτ_ge x hxK'
  have hUniformCauchy : ∀ k, ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j ≥ J, ∀ l ≥ J, ∀ x ∈ K',
      dist (fConvergence (k + 1) (φAux j) x) (fConvergence (k + 1) (φAux l) x) < ε := by
    intro k ε hε
    rcases hDiagCv k with ⟨wSeq_k, _, hwSeq_k_uniform⟩
    rcases hwSeq_k_uniform (ε / 2) (by linarith) with ⟨J, hJ⟩
    refine ⟨J, fun j hj l hl x hxK' => ?_⟩
    have hjJ := hJ j hj x hxK'
    have hlJ := hJ l hl x hxK'
    have hTri := dist_triangle (fConvergence (k + 1) (φAux j) x) (wSeq_k x)
      (fConvergence (k + 1) (φAux l) x)
    have h2 : dist (fConvergence (k + 1) (φAux j) x) (wSeq_k x) < ε / 2 := by
      rw [dist_comm]
      exact hjJ
    have h3 : dist (wSeq_k x) (fConvergence (k + 1) (φAux l) x) < ε / 2 := hlJ
    linarith
  have hLp_cauchy_at_level : ∀ k, ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j ≥ J, ∀ l ≥ J,
      eLpNorm (fun x => fConvergence (k + 1) (φAux j) x - fConvergence (k + 1) (φAux l) x) p volume ≤
        ENNReal.ofReal ε := by
    intro k ε hε
    have h_helper :=
      cauchy_lp_of_uniformly_cauchy_on_compact_support (d := d) hp_one hp_top
        hK'_compact (g := fun j => fConvergence (k + 1) (φAux j))
        (fun j => hfConvergence_cont (k + 1) (φAux j))
        (fun j x hx => hfConvergence_support (k + 1) (φAux j) x hx)
        (hUniformCauchy k)
    exact h_helper ε hε
  have hVfnCauchy : ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j ≥ J, ∀ l ≥ J,
      eLpNorm (fun x => vFn (φAux j) x - vFn (φAux l) x) p volume ≤
        ENNReal.ofReal ε := by
    intro ε hε
    set ε' : ℝ := ε / 3 with hε'_def
    have hε'_pos : 0 < ε' := by rw [hε'_def]; linarith
    rcases hConvergenceSub_bnd ε' hε'_pos with ⟨K0, hK0⟩
    rcases hLp_cauchy_at_level K0 ε' hε'_pos with ⟨J, hJ⟩
    refine ⟨J, fun j hj l hl => ?_⟩
    have hT1 : eLpNorm (fun x => vFn (φAux j) x - fConvergence (K0 + 1) (φAux j) x) p volume ≤
        ENNReal.ofReal ε' := by
      rw [show (fun x => vFn (φAux j) x - fConvergence (K0 + 1) (φAux j) x) =
        -(fun x => fConvergence (K0 + 1) (φAux j) x - vFn (φAux j) x) from by
          funext x; simp [neg_sub]]
      rw [eLpNorm_neg]
      exact hK0 (K0 + 1) (Nat.le_succ K0) (φAux j)
    have hT2 : eLpNorm
        (fun x => fConvergence (K0 + 1) (φAux j) x - fConvergence (K0 + 1) (φAux l) x) p volume ≤
        ENNReal.ofReal ε' := hJ j hj l hl
    have hT3 : eLpNorm (fun x => fConvergence (K0 + 1) (φAux l) x - vFn (φAux l) x) p volume ≤
        ENNReal.ofReal ε' := hK0 (K0 + 1) (Nat.le_succ K0) (φAux l)
    have hSplit : (fun x => vFn (φAux j) x - vFn (φAux l) x) =
        (fun x => vFn (φAux j) x - fConvergence (K0 + 1) (φAux j) x) +
          ((fun x => fConvergence (K0 + 1) (φAux j) x - fConvergence (K0 + 1) (φAux l) x) +
            (fun x => fConvergence (K0 + 1) (φAux l) x - vFn (φAux l) x)) := by
      funext x
      change _ = (vFn (φAux j) x - fConvergence (K0 + 1) (φAux j) x) +
        ((fConvergence (K0 + 1) (φAux j) x - fConvergence (K0 + 1) (φAux l) x) +
          (fConvergence (K0 + 1) (φAux l) x - vFn (φAux l) x))
      ring
    rw [hSplit]
    have h_step1 := eLpNorm_add_le (μ := volume) (f := fun x => vFn (φAux j) x - fConvergence (K0 + 1) (φAux j) x)
      (g := (fun x => fConvergence (K0 + 1) (φAux j) x - fConvergence (K0 + 1) (φAux l) x) +
        (fun x => fConvergence (K0 + 1) (φAux l) x - vFn (φAux l) x)) hp_one
    have h_step2 := eLpNorm_add_le (μ := volume)
      (f := fun x => fConvergence (K0 + 1) (φAux j) x - fConvergence (K0 + 1) (φAux l) x)
      (g := fun x => fConvergence (K0 + 1) (φAux l) x - vFn (φAux l) x) hp_one
    have hε_split : ENNReal.ofReal ε = ENNReal.ofReal ε' +
      (ENNReal.ofReal ε' + ENNReal.ofReal ε') := by
      rw [hε'_def]
      rw [← ENNReal.ofReal_add hε'_pos.le hε'_pos.le, ← ENNReal.ofReal_add hε'_pos.le
        (add_nonneg hε'_pos.le hε'_pos.le)]
      congr 1
      ring
    rw [hε_split]
    refine h_step1.trans ?_
    refine add_le_add hT1 (h_step2.trans ?_)
    exact add_le_add hT2 hT3
  have hVfnCauchy_nat : ∀ N : ℕ, ∃ J : ℕ, ∀ j ≥ J, ∀ l ≥ J,
      eLpNorm (fun x => vFn (φAux j) x - vFn (φAux l) x) p volume <
        ENNReal.ofReal ((1 : ℝ) / (2 : ℝ) ^ (N + 1)) := by
    intro N
    have hN_pos : (0 : ℝ) < (1 : ℝ) / (2 : ℝ) ^ (N + 1) :=
      div_pos one_pos (by positivity)
    rcases hVfnCauchy ((1 : ℝ) / (2 : ℝ) ^ (N + 2)) (by positivity) with ⟨J, hJ⟩
    refine ⟨J, fun j hj l hl => ?_⟩
    have h := hJ j hj l hl
    refine h.trans_lt ?_
    refine ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr ?_
    have h2 : (1 : ℝ) / (2 : ℝ) ^ (N + 2) < (1 : ℝ) / (2 : ℝ) ^ (N + 1) := by
      apply div_lt_div_of_pos_left one_pos (by positivity)
      apply pow_lt_pow_right₀ one_lt_two
      omega
    exact h2
  let JFn : ℕ → ℕ := fun N => Classical.choose (hVfnCauchy_nat N)
  have hJFn_spec : ∀ N : ℕ, ∀ j ≥ JFn N, ∀ l ≥ JFn N,
      eLpNorm (fun x => vFn (φAux j) x - vFn (φAux l) x) p volume <
        ENNReal.ofReal ((1 : ℝ) / (2 : ℝ) ^ (N + 1)) := fun N =>
    Classical.choose_spec (hVfnCauchy_nat N)
  let ψ : ℕ → ℕ := fun N => Nat.rec
    (motive := fun _ => ℕ)
    (JFn 0)
    (fun N_prev ψ_prev => max (JFn (N_prev + 1)) (ψ_prev + 1))
    N
  have hψ_ge_J : ∀ N, ψ N ≥ JFn N := by
    intro N
    induction N with
    | zero => exact le_refl _
    | succ N _ =>
      change max (JFn (N + 1)) _ ≥ JFn (N + 1)
      exact le_max_left _ _
  have hψ_mono : StrictMono ψ := by
    refine strictMono_nat_of_lt_succ fun N => ?_
    change ψ N < max (JFn (N + 1)) (ψ N + 1)
    have : ψ N + 1 > ψ N := by omega
    exact lt_of_lt_of_le this (le_max_right _ _)
  let final_φ : ℕ → ℕ := φAux ∘ ψ
  have hfinal_φ_mono : StrictMono final_φ := hφAux_mono.comp hψ_mono
  have hCauchyBnd : ∀ N j m, N ≤ j → N ≤ m →
      eLpNorm (fun x => vFn (final_φ j) x - vFn (final_φ m) x) p volume <
        ENNReal.ofReal ((1 : ℝ) / (2 : ℝ) ^ (N + 1)) := by
    intro N j m hNj hNm
    have hψj : ψ j ≥ JFn N := le_trans (hψ_ge_J N) (hψ_mono.le_iff_le.mpr hNj)
    have hψm : ψ m ≥ JFn N := le_trans (hψ_ge_J N) (hψ_mono.le_iff_le.mpr hNm)
    exact hJFn_spec N (ψ j) hψj (ψ m) hψm
  have hVfn_memLp : ∀ k, MemLp (vFn (final_φ k)) p volume := fun k =>
    hv_memLp (final_φ k)
  set Bbnd : ℕ → ℝ≥0∞ := fun N => ENNReal.ofReal ((1 : ℝ) / (2 : ℝ) ^ (N + 1))
    with hBbnd_def
  have hBbnd_summable : ∑' i, Bbnd i ≠ ∞ := by
    rw [hBbnd_def]
    have h_sum_real : Summable (fun i : ℕ => (1 : ℝ) / (2 : ℝ) ^ (i + 1)) := by
      have h1 : Summable (fun i : ℕ => (1 : ℝ) * ((1 / 2 : ℝ) ^ (i + 1))) := by
        have h_geom : Summable (fun i : ℕ => ((1 / 2 : ℝ)) ^ i) :=
          summable_geometric_of_abs_lt_one (by simp; norm_num)
        have h_geom' : Summable (fun i : ℕ => ((1 / 2 : ℝ)) ^ (i + 1)) := by
          have : (fun i : ℕ => ((1 / 2 : ℝ)) ^ (i + 1)) =
              (fun i : ℕ => ((1 / 2 : ℝ)) ^ i) ∘ (· + 1) := by
            funext i; simp
          rw [this]
          exact (summable_nat_add_iff 1).mpr h_geom
        exact h_geom'.mul_left 1
      have h_eq : (fun i : ℕ => (1 : ℝ) / (2 : ℝ) ^ (i + 1)) =
          (fun i : ℕ => (1 : ℝ) * ((1 / 2 : ℝ) ^ (i + 1))) := by
        funext i
        rw [one_mul]
        rw [show ((1 / 2 : ℝ) ^ (i + 1)) = (1 : ℝ) ^ (i + 1) / (2 : ℝ) ^ (i + 1) from by
          rw [div_pow]]
        rw [one_pow]
      rw [h_eq]
      exact h1
    have h_pos : ∀ i : ℕ, 0 ≤ (1 : ℝ) / (2 : ℝ) ^ (i + 1) := fun i => by positivity
    rw [show (fun N => ENNReal.ofReal ((1 : ℝ) / (2 : ℝ) ^ (N + 1))) =
      (fun N => ENNReal.ofReal ((1 : ℝ) / (2 : ℝ) ^ (N + 1))) from rfl]
    have h_tsum_eq :
        (∑' i, ENNReal.ofReal ((1 : ℝ) / (2 : ℝ) ^ (i + 1))) =
          ENNReal.ofReal (∑' i, (1 : ℝ) / (2 : ℝ) ^ (i + 1)) := by
      rw [ENNReal.ofReal_tsum_of_nonneg h_pos h_sum_real]
    rw [h_tsum_eq]
    exact ENNReal.ofReal_ne_top
  rcases MeasureTheory.Lp.cauchy_complete_eLpNorm hp_one hVfn_memLp hBbnd_summable hCauchyBnd with
    ⟨u_lim_v, hu_lim_v_memLp, h_lim_tendsto⟩
  refine ⟨final_φ, hfinal_φ_mono, u_lim_v, hu_lim_v_memLp, ?_⟩
  have h_aeEq : ∀ n, (fun x => u (final_φ n) x - u_lim_v x) =ᵐ[volume]
      (fun x => vFn (final_φ n) x - u_lim_v x) := by
    intro n
    have h := hv_aeEq_u (final_φ n)
    filter_upwards [h] with x hx
    rw [hx]
  have h_eLpEq : ∀ n,
      eLpNorm (fun x => u (final_φ n) x - u_lim_v x) p volume =
        eLpNorm (fun x => vFn (final_φ n) x - u_lim_v x) p volume := fun n =>
    eLpNorm_congr_ae (h_aeEq n)
  rw [show (fun k => eLpNorm (fun x => u (final_φ k) x - u_lim_v x) p volume) =
    (fun k => eLpNorm (fun x => vFn (final_φ k) x - u_lim_v x) p volume) from
      funext h_eLpEq]
  exact h_lim_tendsto

end Sobolev
