-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Euclidean/Embedding/Morrey/RieszKernel.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Euclidean.W1p.Witness
public import CalabiYau.Analysis.Sobolev.Euclidean.W1p.Approximation
public import CalabiYau.Analysis.Sobolev.Euclidean.Poincare.Ball
public import CalabiYau.Analysis.Sobolev.Euclidean.Poincare.SobolevPoincare
public import CalabiYau.Analysis.Sobolev.Euclidean.Ball.Approximation
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Integral.Average

@[expose] public section

-- Private declarations used in public declarations require the compatibility option below.

noncomputable section

open MeasureTheory Set Filter Topology Metric Function
open scoped ENNReal NNReal

namespace Sobolev
namespace EuclideanMorrey
variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem riesz_kernel_integrable_of_gt_neg_dim
    {α : ℝ} (hα : -(d : ℝ) < α) {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun x : E => ‖x‖ ^ α) (Metric.ball (0 : E) R) volume := by
  let g : ℝ → ℝ := fun r => if r < R then r ^ α else 0
  have hag :
      (fun x : E => ‖x‖ ^ α) =ᵐ[volume.restrict (Metric.ball (0 : E) R)] (g ∘ (‖·‖)) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    simp only [Function.comp_apply, g, Metric.mem_ball, dist_zero_right] at hx ⊢
    rw [ite_eq_left hx]
  rw [IntegrableOn, integrable_congr hag]
  suffices h : Integrable (fun x : E => g ‖x‖) volume from h.integrableOn
  have hd_one : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hfin : Module.finrank ℝ E = d := finrank_euclideanSpace_fin
  have h1d : IntegrableOn (fun y : ℝ => y ^ (Module.finrank ℝ E - 1) • g y) (Set.Ioi 0) := by
    rw [hfin]
    set h_ind : ℝ → ℝ := (Set.Ioo (0 : ℝ) R).indicator (fun y => y ^ ((d : ℝ) - 1 + α))
    have heq : Set.EqOn (fun y : ℝ => y ^ (d - 1) • g y) h_ind (Set.Ioi 0) := by
      intro r hr
      simp only [Set.mem_Ioi] at hr
      simp only [g, smul_eq_mul, h_ind, Set.indicator, Set.mem_Ioo]
      by_cases h1 : r < R
      · have h_in : 0 < r ∧ r < R := ⟨hr, h1⟩
        simp only [ite_eq_left h1, ite_eq_left h_in]
        rw [← Real.rpow_natCast r (d - 1), ← Real.rpow_add hr,
          Nat.cast_sub hd_one]
        push_cast
        ring_nf
      · simp only [ite_eq_right h1, mul_zero]
        have h_not : ¬ (0 < r ∧ r < R) := fun ⟨_, h2⟩ => h1 h2
        simp only [ite_eq_right h_not]
    have hα_finite : -1 < (d : ℝ) - 1 + α := by linarith
    have h_ind_int : IntegrableOn h_ind (Set.Ioi 0) := by
      apply Integrable.integrableOn
      refine (integrable_indicator_iff measurableSet_Ioo).mpr ?_
      have h_int_Ioo : IntegrableOn (fun y : ℝ => y ^ ((d : ℝ) - 1 + α)) (Set.Ioo 0 R) volume :=
        (intervalIntegral.integrableOn_Ioo_rpow_iff hR).mpr hα_finite
      exact h_int_Ioo
    exact h_ind_int.congr_fun heq.symm measurableSet_Ioi
  exact (MeasureTheory.integrable_fun_norm_addHaar (μ := volume) (f := g)).mpr h1d

private theorem integral_norm_rpow_ball_of_gt_neg_dim
    {α : ℝ} (hα : -(d : ℝ) < α) {R : ℝ} (hR : 0 < R) :
    ∫ x in Metric.ball (0 : E) R, ‖x‖ ^ α ∂volume =
      (d : ℝ) * (volume (Metric.ball (0 : E) 1)).toReal *
        R ^ ((d : ℝ) + α) / ((d : ℝ) + α) := by
  let f : ℝ → ℝ := fun r => if 0 < r ∧ r < R then r ^ α else 0
  have hd_one : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hfin : Module.finrank ℝ E = d := finrank_euclideanSpace_fin
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hα_pos : (0 : ℝ) < (d : ℝ) + α := by linarith
  have hconv : ∫ x in Metric.ball (0 : E) R, ‖x‖ ^ α ∂volume = ∫ x : E, f (‖x‖) ∂volume := by
    rw [← integral_indicator measurableSet_ball]
    refine integral_congr_ae ?_
    have hmeas0 : (volume : Measure E) {(0 : E)} = 0 := measure_singleton _
    have hae : ∀ᵐ x ∂(volume : Measure E), x ≠ (0 : E) :=
      compl_mem_ae_iff.mpr hmeas0
    filter_upwards [hae] with x hx
    simp only [f, indicator, Metric.mem_ball, dist_zero_right]
    have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    simp only [and_iff_right hpos]
  have hrad : ∫ x : E, f (‖x‖) ∂volume =
      ↑(Module.finrank ℝ E) • (volume : Measure E).real (Metric.ball 0 1) •
        ∫ y in Set.Ioi (0 : ℝ), y ^ (Module.finrank ℝ E - 1) • f y :=
    MeasureTheory.integral_fun_norm_addHaar (μ := (volume : Measure E)) f
  have h1d : ∫ y in Set.Ioi (0 : ℝ), y ^ (Module.finrank ℝ E - 1) • f y =
      R ^ ((d : ℝ) + α) / ((d : ℝ) + α) := by
    rw [hfin]
    have hsupp : ∀ y ∈ Set.Ioi (0 : ℝ), y ^ (d - 1) • f y =
        Set.indicator (Set.Ioo 0 R) (fun y => y ^ ((d : ℝ) - 1 + α)) y := by
      intro y hy
      have hy_pos : 0 < y := hy
      by_cases hlt : y < R
      · have h_in : 0 < y ∧ y < R := ⟨hy_pos, hlt⟩
        have h_in_mem : y ∈ Set.Ioo 0 R := h_in
        rw [Set.indicator_of_mem h_in_mem]
        have hf_y : f y = y ^ α := by simp [f, h_in]
        rw [show (y ^ (d - 1) • f y) = y ^ (d - 1) * y ^ α from by
          rw [hf_y]; rfl]
        rw [← Real.rpow_natCast y (d - 1), Nat.cast_sub hd_one,
          ← Real.rpow_add hy_pos]
        push_cast
        ring_nf
      · have h_not_mem : y ∉ Set.Ioo 0 R := fun ⟨_, h2⟩ => hlt h2
        rw [Set.indicator_of_notMem h_not_mem]
        have hf_y : f y = 0 := by
          simp only [f]
          have h_not : ¬ (0 < y ∧ y < R) := fun ⟨_, h2⟩ => hlt h2
          rw [ite_eq_right h_not]
        rw [hf_y]
        simp
    rw [setIntegral_congr_fun measurableSet_Ioi hsupp]
    rw [setIntegral_indicator measurableSet_Ioo]
    rw [show Set.Ioi (0 : ℝ) ∩ Set.Ioo 0 R = Set.Ioo 0 R from
      Set.inter_eq_right.mpr Set.Ioo_subset_Ioi_self]
    have hexp_finite : -1 < (d : ℝ) - 1 + α := by linarith
    have hexp_plus_one : ((d : ℝ) - 1 + α) + 1 = (d : ℝ) + α := by ring
    have h_int_Ioo : ∫ y in Set.Ioo 0 R, y ^ ((d : ℝ) - 1 + α) ∂volume =
        ∫ y in (0 : ℝ)..R, y ^ ((d : ℝ) - 1 + α) := by
      rw [intervalIntegral.integral_of_le hR.le]
      exact (integral_Ioc_eq_integral_Ioo).symm
    rw [h_int_Ioo]
    rw [integral_rpow (Or.inl hexp_finite)]
    rw [hexp_plus_one]
    rw [show (0 : ℝ) ^ ((d : ℝ) + α) = 0 from
      Real.zero_rpow hα_pos.ne']
    ring
  rw [hconv, hrad, h1d, hfin]
  simp only [Measure.real, nsmul_eq_mul, smul_eq_mul]
  ring

private theorem integral_norm_sub_rpow_ball_of_gt_neg_dim
    {α : ℝ} (hα : -(d : ℝ) < α) {R : ℝ} (hR : 0 < R) (x : E) :
    ∫ y in Metric.ball x R, ‖x - y‖ ^ α ∂volume =
      (d : ℝ) * (volume (Metric.ball (0 : E) 1)).toReal *
        R ^ ((d : ℝ) + α) / ((d : ℝ) + α) := by
  have hmp := measurePreserving_add_right (volume : Measure E) x
  have hemb := (MeasurableEquiv.addRight x : E ≃ᵐ E).measurableEmbedding
  have hpre : ((· + x) ⁻¹' Metric.ball x R) = Metric.ball (0 : E) R := by
    ext z; simp [Metric.mem_ball]
  rw [← hmp.setIntegral_preimage_emb hemb, hpre]
  rw [show (fun z => ‖x - (z + x)‖ ^ α) = (fun z => ‖z‖ ^ α) from by
    funext z; congr 1
    rw [show x - (z + x) = -z from by abel]
    simp]
  exact integral_norm_rpow_ball_of_gt_neg_dim hα hR

omit [NeZero d] in
private lemma setIntegral_ball_translate {f : E → ℝ} {x₀ : E} {R : ℝ} :
    ∫ y in Metric.ball x₀ R, f y ∂volume =
      ∫ z in Metric.ball (0 : E) R, f (x₀ + z) ∂volume := by
  have hmp := measurePreserving_add_left (volume : Measure E) x₀
  have hemb := (MeasurableEquiv.addLeft x₀).measurableEmbedding
  have h_image : (x₀ + ·) '' Metric.ball (0 : E) R = Metric.ball x₀ R := by
    simp
  have key := hmp.setIntegral_image_emb hemb f (Metric.ball (0 : E) R)
  rw [h_image] at key
  rw [← key]

private lemma average_ball_translate {f : E → ℝ} {x₀ : E} {R : ℝ} :
    ⨍ y in Metric.ball x₀ R, f y ∂volume =
      ⨍ z in Metric.ball (0 : E) R, f (x₀ + z) ∂volume := by
  by_cases hR : 0 ≤ R
  · have hvol_eq : (volume : Measure E) (Metric.ball x₀ R) =
        (volume : Measure E) (Metric.ball (0 : E) R) := by
      rw [Measure.addHaar_ball (volume : Measure E) x₀ hR,
        Measure.addHaar_ball (volume : Measure E) (0 : E) hR]
    simp only [average_eq, measureReal_def]
    rw [Measure.restrict_apply_univ, Measure.restrict_apply_univ]
    rw [hvol_eq]
    congr 1
    exact setIntegral_ball_translate
  · have hR_lt : R < 0 := lt_of_not_ge hR
    have h_empty1 : Metric.ball x₀ R = ∅ :=
      Metric.ball_eq_empty.mpr hR_lt.le
    have h_empty2 : Metric.ball (0 : E) R = ∅ :=
      Metric.ball_eq_empty.mpr hR_lt.le
    rw [h_empty1, h_empty2]
    simp [average]

theorem representation_formula_smooth_translated
    {x₀ : E} {R : ℝ} (hR : 0 < R)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {x : E} (hx : x ∈ Metric.ball x₀ R) :
    ‖u x - ⨍ y in Metric.ball x₀ R, u y ∂volume‖ ≤
      (2 : ℝ) ^ d / ((d : ℝ) * (volume (Metric.ball (0 : E) 1)).toReal) *
        ∫ y in Metric.ball x₀ R, ‖fderiv ℝ u y‖ * ‖x - y‖ ^ (1 - (d : ℝ)) ∂volume := by
  set v : E → ℝ := fun z => u (x₀ + z) with hv_def
  have hv : ContDiff ℝ (⊤ : ℕ∞) v := hu.comp (contDiff_const.add contDiff_id)
  have hx_t : x - x₀ ∈ Metric.ball (0 : E) R := by
    rw [Metric.mem_ball, dist_zero_right]
    have := hx
    rw [Metric.mem_ball, dist_eq_norm] at this
    exact this
  have hkey :=
    Sobolev.Euclidean.representation_formula_smooth (d := d) hR (u := v) hv (x - x₀) hx_t
  have hv_x_t : v (x - x₀) = u x := by simp [v]
  rw [hv_x_t] at hkey
  have havg_eq : ⨍ z in Metric.ball (0 : E) R, v z ∂volume =
      ⨍ y in Metric.ball x₀ R, u y ∂volume := by
    rw [show (fun z => v z) = (fun z => u (x₀ + z)) from rfl]
    exact (average_ball_translate (f := u) (x₀ := x₀) (R := R)).symm
  rw [havg_eq] at hkey
  have hfderiv_v : ∀ z : E, fderiv ℝ v z = fderiv ℝ u (x₀ + z) := by
    intro z
    have hadd_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun w : E => x₀ + w) :=
      contDiff_const.add contDiff_id
    have hadd_diff : DifferentiableAt ℝ (fun w : E => x₀ + w) z :=
      (hadd_smooth.contDiffAt).differentiableAt (by simp)
    have hu_diff : DifferentiableAt ℝ u (x₀ + z) :=
      (hu.contDiffAt).differentiableAt (by simp)
    have hfd_add : fderiv ℝ (fun w : E => x₀ + w) z = ContinuousLinearMap.id ℝ E := by
      have h1 : fderiv ℝ (fun w : E => x₀ + w) z =
          fderiv ℝ (fun w : E => x₀) z + fderiv ℝ (fun w : E => w) z := by
        exact fderiv_add (differentiable_const _).differentiableAt
          differentiable_id.differentiableAt
      rw [h1]
      simp
    rw [hv_def]
    rw [show (fun z => u (x₀ + z)) = u ∘ (fun z => x₀ + z) from rfl]
    rw [fderiv_comp z hu_diff hadd_diff]
    rw [hfd_add]
    rfl
  have hgrad_eq :
      ∫ y in Metric.ball (0 : E) R,
        ‖fderiv ℝ v y‖ * ‖(x - x₀) - y‖ ^ (1 - (d : ℝ)) ∂volume =
      ∫ y' in Metric.ball x₀ R,
        ‖fderiv ℝ u y'‖ * ‖x - y'‖ ^ (1 - (d : ℝ)) ∂volume := by
    rw [setIntegral_ball_translate (f := fun y' => ‖fderiv ℝ u y'‖ * ‖x - y'‖ ^ (1 - (d : ℝ)))
      (x₀ := x₀) (R := R)]
    refine setIntegral_congr_fun (μ := (volume : Measure E)) measurableSet_ball ?_
    intro y _
    change ‖fderiv ℝ v y‖ * ‖x - x₀ - y‖ ^ (1 - (d : ℝ)) =
      ‖fderiv ℝ u (x₀ + y)‖ * ‖x - (x₀ + y)‖ ^ (1 - (d : ℝ))
    rw [hfderiv_v y]
    congr 2
    rw [show x - x₀ - y = x - (x₀ + y) from by abel]
  rw [hgrad_eq] at hkey
  exact hkey

theorem integral_norm_sub_rpow_ball_at_other_center
    {α : ℝ} (hα : -(d : ℝ) < α) {z x : E} {R : ℝ} (hR : 0 < R) :
    ∫ y in Metric.ball z R, ‖x - y‖ ^ α ∂volume ≤
      (d : ℝ) * (volume (Metric.ball (0 : E) 1)).toReal *
        (R + dist x z) ^ ((d : ℝ) + α) / ((d : ℝ) + α) := by
  set R' : ℝ := R + dist x z with hR'_def
  have hR'_pos : 0 < R' := by
    have := dist_nonneg (x := x) (y := z)
    linarith
  have hsub : Metric.ball z R ⊆ Metric.ball x R' := by
    intro y hy
    rw [Metric.mem_ball] at hy ⊢
    calc dist y x ≤ dist y z + dist z x := dist_triangle y z x
      _ < R + dist z x := by linarith
      _ = R + dist x z := by rw [dist_comm]
  have hd_α_pos : (0 : ℝ) < (d : ℝ) + α := by linarith
  have hint_origin :
      IntegrableOn (fun y : E => ‖x - y‖ ^ α) (Metric.ball x R') volume := by
    have hmp := measurePreserving_add_right (volume : Measure E) x
    have hemb := (MeasurableEquiv.addRight x : E ≃ᵐ E).measurableEmbedding
    have hpre : ((· + x) ⁻¹' Metric.ball x R') = Metric.ball (0 : E) R' := by
      ext z; simp [Metric.mem_ball]
    have h_eq : ∀ w : E, ‖x - (w + x)‖ ^ α = ‖w‖ ^ α := by
      intro w
      congr 1
      rw [show x - (w + x) = -w from by abel]
      rw [norm_neg]
    have hint_translated :
        IntegrableOn (fun w : E => ‖x - (w + x)‖ ^ α) (Metric.ball (0 : E) R') volume := by
      refine (riesz_kernel_integrable_of_gt_neg_dim (d := d) hα hR'_pos).congr (ae_of_all _ ?_)
      intro w
      exact (h_eq w).symm
    have hcomp_eq : (fun y => ‖x - y‖ ^ α) ∘ (· + x) =
        fun w : E => ‖x - (w + x)‖ ^ α := by funext; rfl
    have := (hmp.integrableOn_comp_preimage (β := E) (e := (· + x))
      (f := fun y : E => ‖x - y‖ ^ α) (s := Metric.ball x R') hemb).mp
    apply this
    rw [hcomp_eq, hpre]
    exact hint_translated
  have hnonneg : ∀ y : E, 0 ≤ ‖x - y‖ ^ α := fun y => Real.rpow_nonneg (norm_nonneg _) _
  calc ∫ y in Metric.ball z R, ‖x - y‖ ^ α ∂volume
      ≤ ∫ y in Metric.ball x R', ‖x - y‖ ^ α ∂volume := by
        apply setIntegral_mono_set hint_origin
        · exact ae_of_all _ hnonneg
        · exact hsub.eventuallyLE
    _ = (d : ℝ) * (volume (Metric.ball (0 : E) 1)).toReal *
          R' ^ ((d : ℝ) + α) / ((d : ℝ) + α) :=
        integral_norm_sub_rpow_ball_of_gt_neg_dim (d := d) hα hR'_pos x

lemma measurable_norm_sub_rpow (α : ℝ) (x : E) :
    AEStronglyMeasurable (fun y : E => ‖x - y‖ ^ α) (volume : Measure E) := by
  have hcont_complement : ContinuousOn (fun y : E => ‖x - y‖ ^ α) ({x} : Set E)ᶜ := by
    refine ContinuousOn.rpow_const ?_ ?_
    · exact (continuous_const.sub continuous_id').norm.continuousOn
    · intro y hy
      left
      apply norm_ne_zero_iff.mpr
      apply sub_ne_zero.mpr
      intro h
      exact hy (h ▸ rfl)
  have h_open : IsOpen (({x} : Set E)ᶜ) := isClosed_singleton.isOpen_compl
  have h_compl_meas : MeasurableSet (({x} : Set E)ᶜ) := (measurableSet_singleton x).compl
  have h_x_null : (volume : Measure E) {x} = 0 := measure_singleton _
  have h_aesm_compl : AEStronglyMeasurable (fun y : E => ‖x - y‖ ^ α)
      (volume.restrict (({x} : Set E)ᶜ)) :=
    hcont_complement.aestronglyMeasurable h_compl_meas
  rw [show (volume : Measure E) = volume.restrict (({x} : Set E)ᶜ) from by
    rw [Measure.restrict_eq_self_of_ae_mem]
    filter_upwards [(compl_mem_ae_iff.mpr h_x_null : ({x} : Set E)ᶜ ∈ ae (volume : Measure E))]
      with y hy
    exact hy]
  exact h_aesm_compl

theorem riesz_kernel_memLp
    {p : ℝ} (hp : (d : ℝ) < p) {z : E} {R : ℝ} (hR : 0 < R) (x : E) :
    MemLp (fun y : E => ‖x - y‖ ^ (1 - (d : ℝ)))
      (ENNReal.ofReal (p / (p - 1))) (volume.restrict (Metric.ball z R)) := by
  classical
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hd_one_le : (1 : ℝ) ≤ d :=
    by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))
  have hp_pos : 0 < p := lt_trans hd_pos hp
  have hp_one : 1 < p := by linarith
  have hpm1_pos : 0 < p - 1 := by linarith
  set q : ℝ := p / (p - 1) with hq_def
  have hq_pos : 0 < q := div_pos hp_pos hpm1_pos
  have hq_one : 1 ≤ q := by
    rw [hq_def]
    have hpm1_le_p : p - 1 ≤ p := by linarith
    rw [le_div_iff₀ hpm1_pos]
    linarith
  set α : ℝ := (1 - (d : ℝ)) * q with hα_def
  have hα_gt : -(d : ℝ) < α := by
    have h_lhs : -(d : ℝ) * (p - 1) < (1 - (d : ℝ)) * p := by nlinarith [hp]
    have h_rhs_eq : -(d : ℝ) = -(d : ℝ) * (p - 1) / (p - 1) :=
      (mul_div_cancel_right₀ _ hpm1_pos.ne').symm
    rw [h_rhs_eq]
    rw [show α = (1 - (d : ℝ)) * p / (p - 1) from by simp [hα_def, hq_def]; ring]
    exact (div_lt_div_iff_of_pos_right hpm1_pos).mpr h_lhs
  have h_aesm : AEStronglyMeasurable (fun y : E => ‖x - y‖ ^ (1 - (d : ℝ)))
      (volume.restrict (Metric.ball z R)) :=
    (measurable_norm_sub_rpow (1 - (d : ℝ)) x).restrict
  have hα_int : IntegrableOn (fun y : E => ‖x - y‖ ^ α) (Metric.ball z R) volume := by
    have hsub : Metric.ball z R ⊆ Metric.ball x (R + dist x z) := by
      intro y hy
      rw [Metric.mem_ball] at hy ⊢
      calc dist y x ≤ dist y z + dist z x := dist_triangle y z x
        _ < R + dist z x := by linarith
        _ = R + dist x z := by rw [dist_comm]
    have hRR_pos : 0 < R + dist x z := by have := dist_nonneg (x := x) (y := z); linarith
    have hint_origin :
        IntegrableOn (fun y : E => ‖y‖ ^ α) (Metric.ball (0 : E) (R + dist x z)) volume :=
      riesz_kernel_integrable_of_gt_neg_dim (d := d) hα_gt hRR_pos
    have hint_at_x : IntegrableOn (fun y : E => ‖x - y‖ ^ α) (Metric.ball x (R + dist x z))
      volume := by
      have hmp := measurePreserving_add_right (volume : Measure E) x
      have hemb := (MeasurableEquiv.addRight x : E ≃ᵐ E).measurableEmbedding
      have hpre : ((· + x) ⁻¹' Metric.ball x (R + dist x z)) =
          Metric.ball (0 : E) (R + dist x z) := by
        ext z; simp [Metric.mem_ball]
      have h_eq : ∀ w : E, ‖x - (w + x)‖ ^ α = ‖w‖ ^ α := by
        intro w
        congr 1
        rw [show x - (w + x) = -w from by abel]
        rw [norm_neg]
      have hint_translated :
          IntegrableOn (fun w : E => ‖x - (w + x)‖ ^ α) (Metric.ball (0 : E) (R + dist x z))
            volume := by
        refine hint_origin.congr (ae_of_all _ ?_)
        intro w
        exact (h_eq w).symm
      have := (hmp.integrableOn_comp_preimage (β := E) (e := (· + x))
        (f := fun y : E => ‖x - y‖ ^ α) (s := Metric.ball x (R + dist x z)) hemb).mp
      apply this
      have hcomp_eq : (fun y => ‖x - y‖ ^ α) ∘ (· + x) =
          fun w : E => ‖x - (w + x)‖ ^ α := by funext; rfl
      rw [hcomp_eq, hpre]
      exact hint_translated
    exact hint_at_x.mono_set hsub
  have h_lintegral_finite :
      ∫⁻ y in Metric.ball z R, ‖‖x - y‖ ^ (1 - (d : ℝ))‖ₑ ^ q ∂volume ≠ ⊤ := by
    have h_lintegral_eq :
        ∫⁻ y in Metric.ball z R, ‖‖x - y‖ ^ (1 - (d : ℝ))‖ₑ ^ q ∂volume =
        ∫⁻ y in Metric.ball z R, ENNReal.ofReal (‖x - y‖ ^ α) ∂volume := by
      refine lintegral_congr_ae ?_
      filter_upwards with y
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hq_pos.le]
      congr 1
      rw [← Real.rpow_mul (norm_nonneg _)]
    rw [h_lintegral_eq]
    rw [← ofReal_integral_eq_lintegral_ofReal hα_int (ae_of_all _ fun y =>
      Real.rpow_nonneg (norm_nonneg _) _)]
    exact ENNReal.ofReal_ne_top
  apply memLp_iff.mpr
  have hq_enn_ne_zero : ENNReal.ofReal q ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero]
    exact not_le.mpr hq_pos
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq_enn_ne_zero ENNReal.ofReal_ne_top h_aesm]
  rw [ENNReal.toReal_ofReal hq_pos.le]
  refine ENNReal.rpow_lt_top_of_nonneg ?_ ?_
  · positivity
  exact h_lintegral_finite

end EuclideanMorrey
end Sobolev
