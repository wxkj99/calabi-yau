-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Euclidean/Embedding/Morrey/SmoothHolderBound.lean
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
public import CalabiYau.Analysis.Sobolev.Euclidean.Embedding.Morrey.RieszKernel

@[expose] public section

-- Private declarations used in public declarations require the compatibility option below.

noncomputable section

open MeasureTheory Set Filter Topology Metric Function
open scoped ENNReal NNReal

namespace Sobolev
namespace EuclideanMorrey
variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

private lemma continuous_norm_fderiv {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    Continuous (fun y : E => ‖fderiv ℝ u y‖) :=
  continuous_norm.comp (hu.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0))

theorem smooth_grad_memLp_on_ball
    {p : ℝ} {x₀ : E} {R : ℝ} (hR : 0 < R)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    MemLp (fun y : E => ‖fderiv ℝ u y‖) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball x₀ R)) := by
  have hcont : Continuous (fun y : E => ‖fderiv ℝ u y‖) := continuous_norm_fderiv hu
  have hfin : (volume.restrict (Metric.ball x₀ R)) (Set.univ) < ⊤ := by
    rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top
  obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_closedBall x₀ R) hcont.continuousOn
  have hM_nonneg : 0 ≤ M := by
    have h1 : x₀ ∈ Metric.closedBall x₀ R := Metric.mem_closedBall_self hR.le
    exact le_trans (norm_nonneg _) (hM x₀ h1)
  have : IsFiniteMeasure (volume.restrict (Metric.ball x₀ R)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top
  refine MemLp.of_le_mul (g := fun _ : E => (1 : ℝ)) (c := M) ?_ ?_ ?_
  · exact memLp_const (1 : ℝ)
  · exact hcont.aestronglyMeasurable.restrict
  · refine ae_restrict_iff' measurableSet_ball |>.mpr ?_
    filter_upwards with y hy
    have hy' : y ∈ Metric.closedBall x₀ R := Metric.ball_subset_closedBall hy
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), norm_one, mul_one]
    have := hM y hy'
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at this
    exact this

variable [NeZero d] in
private theorem smooth_pointwise_holder_bound
    {p : ℝ} (hp : (d : ℝ) < p) {x₀ : E} {R : ℝ} (hR : 0 < R)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {x : E} (hx : x ∈ Metric.ball x₀ R) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖u x - ⨍ y in Metric.ball x₀ R, u y ∂volume‖ ≤
        C *
          (eLpNorm (fun y => ‖fderiv ℝ u y‖) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ R))).toReal := by
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
    rw [hq_def, le_div_iff₀ hpm1_pos]; linarith
  have hpq_holder : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp_one
  have hrep := representation_formula_smooth_translated (d := d) hR hu hx
  set C₁ : ℝ := (2 : ℝ) ^ d / ((d : ℝ) * (volume (Metric.ball (0 : E) 1)).toReal) with hC₁_def
  have hvol_pos : (0 : ℝ) < (volume (Metric.ball (0 : E) 1)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  have hC₁_pos : 0 < C₁ := by
    rw [hC₁_def]; positivity
  have hf_nonneg : ∀ y : E, 0 ≤ ‖fderiv ℝ u y‖ := fun y => norm_nonneg _
  have hK_nonneg : ∀ y : E, 0 ≤ ‖x - y‖ ^ (1 - (d : ℝ)) := fun y =>
    Real.rpow_nonneg (norm_nonneg _) _
  have hf_memLp : MemLp (fun y : E => ‖fderiv ℝ u y‖) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball x₀ R)) :=
    smooth_grad_memLp_on_ball (d := d) hR hu
  have hK_memLp : MemLp (fun y : E => ‖x - y‖ ^ (1 - (d : ℝ))) (ENNReal.ofReal q)
      (volume.restrict (Metric.ball x₀ R)) :=
    riesz_kernel_memLp (d := d) hp hR x
  set μ : Measure E := volume.restrict (Metric.ball x₀ R) with hμ_def
  have hf_aemeas : AEMeasurable (fun y : E => ENNReal.ofReal (‖fderiv ℝ u y‖)) μ :=
    hf_memLp.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hK_aemeas : AEMeasurable (fun y : E => ENNReal.ofReal (‖x - y‖ ^ (1 - (d : ℝ)))) μ :=
    hK_memLp.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ := μ) hpq_holder hf_aemeas hK_aemeas
  have hHolder_simp :
      (∫⁻ y, ENNReal.ofReal (‖fderiv ℝ u y‖ * ‖x - y‖ ^ (1 - (d : ℝ))) ∂μ) ≤
        (∫⁻ y, (ENNReal.ofReal ‖fderiv ℝ u y‖) ^ p ∂μ) ^ (1 / p) *
        (∫⁻ y, (ENNReal.ofReal (‖x - y‖ ^ (1 - (d : ℝ)))) ^ q ∂μ) ^ (1 / q) := by
    have h_LHS_eq :
        (∫⁻ y, ENNReal.ofReal (‖fderiv ℝ u y‖ * ‖x - y‖ ^ (1 - (d : ℝ))) ∂μ) =
        ∫⁻ a,
          ((fun y => ENNReal.ofReal ‖fderiv ℝ u y‖) *
            (fun y => ENNReal.ofReal (‖x - y‖ ^ (1 - (d : ℝ))))) a ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards with y
      rw [Pi.mul_apply, ENNReal.ofReal_mul (hf_nonneg y)]
    rw [h_LHS_eq]
    exact hHolder
  have hf_p_eq : ∀ y : E, (ENNReal.ofReal (‖fderiv ℝ u y‖)) ^ p =
      ENNReal.ofReal (‖fderiv ℝ u y‖ ^ p) := by
    intro y
    rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp_pos.le]
  have hK_q_eq : ∀ y : E, (ENNReal.ofReal (‖x - y‖ ^ (1 - (d : ℝ)))) ^ q =
      ENNReal.ofReal (‖x - y‖ ^ ((1 - (d : ℝ)) * q)) := by
    intro y
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hq_pos.le]
    congr 1
    rw [← Real.rpow_mul (norm_nonneg _)]
  have hHolder' :
      (∫⁻ y, ENNReal.ofReal (‖fderiv ℝ u y‖ * ‖x - y‖ ^ (1 - (d : ℝ))) ∂μ) ≤
        (∫⁻ y, ENNReal.ofReal (‖fderiv ℝ u y‖ ^ p) ∂μ) ^ (1 / p) *
          (∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ ((1 - (d : ℝ)) * q)) ∂μ) ^ (1 / q) := by
    refine hHolder_simp.trans_eq ?_
    rw [show (∫⁻ a, (ENNReal.ofReal (‖fderiv ℝ u a‖)) ^ p ∂μ) =
        ∫⁻ y, ENNReal.ofReal (‖fderiv ℝ u y‖ ^ p) ∂μ from
      lintegral_congr_ae (Eventually.of_forall hf_p_eq)]
    rw [show (∫⁻ a, (ENNReal.ofReal (‖x - a‖ ^ (1 - (d : ℝ)))) ^ q ∂μ) =
        ∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ ((1 - (d : ℝ)) * q)) ∂μ from
      lintegral_congr_ae (Eventually.of_forall hK_q_eq)]
  have hf_p_int : IntegrableOn (fun y => ‖fderiv ℝ u y‖ ^ p) (Metric.ball x₀ R) volume := by
    have h1 := hf_memLp.integrable_norm_rpow
      (by rw [Ne, ENNReal.ofReal_eq_zero]; exact not_le.mpr hp_pos) ENNReal.ofReal_ne_top
    rw [ENNReal.toReal_ofReal hp_pos.le] at h1
    refine h1.congr (ae_of_all _ fun y => ?_)
    change ‖‖fderiv ℝ u y‖‖ ^ p = ‖fderiv ℝ u y‖ ^ p
    rw [show ‖‖fderiv ℝ u y‖‖ = ‖fderiv ℝ u y‖ from
      Real.norm_of_nonneg (norm_nonneg _)]
  have hf_p_lint :
      ∫⁻ y, ENNReal.ofReal (‖fderiv ℝ u y‖ ^ p) ∂μ =
      ENNReal.ofReal (∫ y in Metric.ball x₀ R, ‖fderiv ℝ u y‖ ^ p ∂volume) := by
    rw [hμ_def]
    rw [← ofReal_integral_eq_lintegral_ofReal hf_p_int
      (ae_of_all _ fun y => Real.rpow_nonneg (norm_nonneg _) _)]
  set α : ℝ := (1 - (d : ℝ)) * q with hα_def
  have hα_gt : -(d : ℝ) < α := by
    have h_lhs : -(d : ℝ) * (p - 1) < (1 - (d : ℝ)) * p := by nlinarith [hp]
    have h_rhs_eq : -(d : ℝ) = -(d : ℝ) * (p - 1) / (p - 1) :=
      (mul_div_cancel_right₀ _ hpm1_pos.ne').symm
    rw [h_rhs_eq]
    rw [show α = (1 - (d : ℝ)) * p / (p - 1) from by simp [hα_def, hq_def]; ring]
    exact (div_lt_div_iff_of_pos_right hpm1_pos).mpr h_lhs
  have hK_alpha_int : IntegrableOn (fun y : E => ‖x - y‖ ^ α)
      (Metric.ball x₀ R) volume := by
    have hsub : Metric.ball x₀ R ⊆ Metric.ball x (R + dist x x₀) := by
      intro y hy
      rw [Metric.mem_ball] at hy ⊢
      calc dist y x ≤ dist y x₀ + dist x₀ x := dist_triangle y x₀ x
        _ < R + dist x₀ x := by linarith
        _ = R + dist x x₀ := by rw [dist_comm]
    have hRR_pos : 0 < R + dist x x₀ := by have := dist_nonneg (x := x) (y := x₀); linarith
    have hint_origin :
        IntegrableOn (fun y : E => ‖y‖ ^ α) (Metric.ball (0 : E) (R + dist x x₀)) volume :=
      riesz_kernel_integrable_of_gt_neg_dim (d := d) hα_gt hRR_pos
    have hmp := measurePreserving_add_right (volume : Measure E) x
    have hemb := (MeasurableEquiv.addRight x : E ≃ᵐ E).measurableEmbedding
    have hpre : ((· + x) ⁻¹' Metric.ball x (R + dist x x₀)) =
        Metric.ball (0 : E) (R + dist x x₀) := by
      ext z; simp [Metric.mem_ball]
    have h_eq : ∀ w : E, ‖x - (w + x)‖ ^ α = ‖w‖ ^ α := by
      intro w
      congr 1
      rw [show x - (w + x) = -w from by abel]
      rw [norm_neg]
    have hint_translated :
        IntegrableOn (fun w : E => ‖x - (w + x)‖ ^ α) (Metric.ball (0 : E) (R + dist x x₀))
          volume := by
      refine hint_origin.congr (ae_of_all _ ?_)
      intro w
      exact (h_eq w).symm
    have hint_at_x : IntegrableOn (fun y : E => ‖x - y‖ ^ α)
        (Metric.ball x (R + dist x x₀)) volume := by
      have := (hmp.integrableOn_comp_preimage (β := E) (e := (· + x))
        (f := fun y : E => ‖x - y‖ ^ α) (s := Metric.ball x (R + dist x x₀)) hemb).mp
      apply this
      have hcomp_eq : (fun y => ‖x - y‖ ^ α) ∘ (· + x) =
          fun w : E => ‖x - (w + x)‖ ^ α := by funext; rfl
      rw [hcomp_eq, hpre]
      exact hint_translated
    exact hint_at_x.mono_set hsub
  have hK_alpha_lint :
      ∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ α) ∂μ =
      ENNReal.ofReal (∫ y in Metric.ball x₀ R, ‖x - y‖ ^ α ∂volume) := by
    rw [hμ_def]
    rw [← ofReal_integral_eq_lintegral_ofReal hK_alpha_int
      (ae_of_all _ fun y => Real.rpow_nonneg (norm_nonneg _) _)]
  have hLHS_int : IntegrableOn (fun y : E => ‖fderiv ℝ u y‖ * ‖x - y‖ ^ (1 - (d : ℝ)))
      (Metric.ball x₀ R) volume := by
    have hcont_grad := continuous_norm_fderiv hu
    obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn
      (isCompact_closedBall x₀ R) hcont_grad.continuousOn
    have hM_nonneg : 0 ≤ M :=
      le_trans (norm_nonneg _) (hM x₀ (Metric.mem_closedBall_self hR.le))
    have hK_int_orig : IntegrableOn (fun y : E => ‖x - y‖ ^ (1 - (d : ℝ)))
        (Metric.ball x₀ R) volume := by
      have h_neg_d : -(d : ℝ) < 1 - (d : ℝ) := by linarith
      have hsub : Metric.ball x₀ R ⊆ Metric.ball x (R + dist x x₀) := by
        intro y hy
        rw [Metric.mem_ball] at hy ⊢
        calc dist y x ≤ dist y x₀ + dist x₀ x := dist_triangle y x₀ x
          _ < R + dist x₀ x := by linarith
          _ = R + dist x x₀ := by rw [dist_comm]
      have hRR_pos : 0 < R + dist x x₀ := by
        have := dist_nonneg (x := x) (y := x₀); linarith
      have hint_origin :
          IntegrableOn (fun y : E => ‖y‖ ^ (1 - (d : ℝ)))
            (Metric.ball (0 : E) (R + dist x x₀)) volume :=
        riesz_kernel_integrable_of_gt_neg_dim (d := d) h_neg_d hRR_pos
      have hmp := measurePreserving_add_right (volume : Measure E) x
      have hemb := (MeasurableEquiv.addRight x : E ≃ᵐ E).measurableEmbedding
      have hpre : ((· + x) ⁻¹' Metric.ball x (R + dist x x₀)) =
          Metric.ball (0 : E) (R + dist x x₀) := by
        ext z; simp [Metric.mem_ball]
      have h_eq : ∀ w : E, ‖x - (w + x)‖ ^ (1 - (d : ℝ)) = ‖w‖ ^ (1 - (d : ℝ)) := by
        intro w
        congr 1
        rw [show x - (w + x) = -w from by abel]
        rw [norm_neg]
      have hint_translated :
          IntegrableOn (fun w : E => ‖x - (w + x)‖ ^ (1 - (d : ℝ)))
            (Metric.ball (0 : E) (R + dist x x₀)) volume := by
        refine hint_origin.congr (ae_of_all _ ?_)
        intro w
        exact (h_eq w).symm
      have hint_at_x : IntegrableOn (fun y : E => ‖x - y‖ ^ (1 - (d : ℝ)))
          (Metric.ball x (R + dist x x₀)) volume := by
        have := (hmp.integrableOn_comp_preimage (β := E) (e := (· + x))
          (f := fun y : E => ‖x - y‖ ^ (1 - (d : ℝ)))
          (s := Metric.ball x (R + dist x x₀)) hemb).mp
        apply this
        have hcomp_eq : (fun y => ‖x - y‖ ^ (1 - (d : ℝ))) ∘ (· + x) =
            fun w : E => ‖x - (w + x)‖ ^ (1 - (d : ℝ)) := by funext; rfl
        rw [hcomp_eq, hpre]
        exact hint_translated
      exact hint_at_x.mono_set hsub
    refine Integrable.mono (hK_int_orig.const_mul M) ?_ ?_
    · refine AEStronglyMeasurable.restrict ?_
      have h1 : AEStronglyMeasurable (fun y : E => ‖fderiv ℝ u y‖) volume :=
        (continuous_norm_fderiv hu).aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun y : E => ‖x - y‖ ^ (1 - (d : ℝ))) volume :=
        measurable_norm_sub_rpow (1 - (d : ℝ)) x
      exact h1.mul h2
    · refine ae_restrict_iff' measurableSet_ball |>.mpr ?_
      filter_upwards with y hy
      have hy' : y ∈ Metric.closedBall x₀ R := Metric.ball_subset_closedBall hy
      have h_grad_le : ‖fderiv ℝ u y‖ ≤ M := by
        have h_at_y := hM y hy'
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h_at_y
        exact h_at_y
      have hk_nn : 0 ≤ ‖x - y‖ ^ (1 - (d : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
      have h_grad_nn : 0 ≤ ‖fderiv ℝ u y‖ := norm_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h_grad_nn hk_nn)]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hM_nonneg hk_nn)]
      exact mul_le_mul_of_nonneg_right h_grad_le hk_nn
  have hLHS_lint :
      ∫⁻ y, ENNReal.ofReal (‖fderiv ℝ u y‖ * ‖x - y‖ ^ (1 - (d : ℝ))) ∂μ =
      ENNReal.ofReal
        (∫ y in Metric.ball x₀ R, ‖fderiv ℝ u y‖ * ‖x - y‖ ^ (1 - (d : ℝ)) ∂volume) := by
    rw [hμ_def]
    rw [← ofReal_integral_eq_lintegral_ofReal hLHS_int (ae_of_all _ fun y =>
      mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))]
  set Iint : ℝ := ∫ y in Metric.ball x₀ R, ‖fderiv ℝ u y‖ ^ p ∂volume with hIint_def
  set Kint : ℝ := ∫ y in Metric.ball x₀ R, ‖x - y‖ ^ α ∂volume with hKint_def
  have hIint_nn : 0 ≤ Iint := setIntegral_nonneg measurableSet_ball
    (fun y _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hKint_nn : 0 ≤ Kint := setIntegral_nonneg measurableSet_ball
    (fun y _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hReal_bound :
      ∫ y in Metric.ball x₀ R, ‖fderiv ℝ u y‖ * ‖x - y‖ ^ (1 - (d : ℝ)) ∂volume ≤
      Iint ^ (1 / p) * Kint ^ (1 / q) := by
    have hineq := hHolder'
    rw [hLHS_lint, hf_p_lint, hK_alpha_lint] at hineq
    rw [ENNReal.ofReal_rpow_of_nonneg hIint_nn (by positivity : 0 ≤ (1 / p : ℝ))] at hineq
    rw [ENNReal.ofReal_rpow_of_nonneg hKint_nn (by positivity : 0 ≤ (1 / q : ℝ))] at hineq
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hIint_nn _)] at hineq
    rwa [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hineq
  refine ⟨C₁ * Kint ^ (1 / q), by positivity, ?_⟩
  calc ‖u x - ⨍ y in Metric.ball x₀ R, u y ∂volume‖
      ≤ C₁ * ∫ y in Metric.ball x₀ R, ‖fderiv ℝ u y‖ * ‖x - y‖ ^ (1 - (d : ℝ)) ∂volume := hrep
    _ ≤ C₁ * (Iint ^ (1 / p) * Kint ^ (1 / q)) :=
        mul_le_mul_of_nonneg_left hReal_bound hC₁_pos.le
    _ = (C₁ * Kint ^ (1 / q)) * Iint ^ (1 / p) := by ring
    _ = (C₁ * Kint ^ (1 / q)) *
          (eLpNorm (fun y => ‖fderiv ℝ u y‖) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ R))).toReal := by
        congr 1
        rw [hIint_def]
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
          (by rw [Ne, ENNReal.ofReal_eq_zero]; exact not_le.mpr hp_pos)
          ENNReal.ofReal_ne_top]
        rw [ENNReal.toReal_ofReal hp_pos.le]
        have h_eq :
            ∫⁻ y in Metric.ball x₀ R, ‖‖fderiv ℝ u y‖‖ₑ ^ p ∂volume =
            ENNReal.ofReal (∫ y in Metric.ball x₀ R, ‖fderiv ℝ u y‖ ^ p ∂volume) := by
          have h_lint_eq :
              ∫⁻ y in Metric.ball x₀ R, ‖‖fderiv ℝ u y‖‖ₑ ^ p ∂volume =
              ∫⁻ y in Metric.ball x₀ R, ENNReal.ofReal (‖fderiv ℝ u y‖ ^ p) ∂volume := by
            refine lintegral_congr_ae ?_
            filter_upwards with y
            rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (norm_nonneg _)]
            rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp_pos.le]
          rw [h_lint_eq]
          exact (ofReal_integral_eq_lintegral_ofReal hf_p_int
            (ae_of_all _ fun y => Real.rpow_nonneg (norm_nonneg _) _)).symm
        rw [h_eq]
        rw [show (ENNReal.ofReal (∫ y in Metric.ball x₀ R, ‖fderiv ℝ u y‖ ^ p) ^ (1 / p)).toReal =
            ((ENNReal.ofReal (∫ y in Metric.ball x₀ R, ‖fderiv ℝ u y‖ ^ p)).toReal) ^ (1 / p) from
            (ENNReal.toReal_rpow _ _).symm]
        rw [ENNReal.toReal_ofReal hIint_nn]

def smoothHolderConst (d : ℕ) (p : ℝ) : ℝ :=
  let q : ℝ := p / (p - 1)
  let α : ℝ := (1 - (d : ℝ)) * q
  let dα : ℝ := (d : ℝ) + α
  let C₁ : ℝ := (2 : ℝ) ^ d /
    ((d : ℝ) * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal)
  C₁ * ((d : ℝ) * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal *
    (2 : ℝ) ^ dα / dα) ^ (1 / q)

section

variable [NeZero d]

theorem smoothHolderConst_nonneg {d : ℕ} [NeZero d] {p : ℝ} (hp : (d : ℝ) < p) :
    0 ≤ smoothHolderConst d p := by
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hd_one_le : (1 : ℝ) ≤ d :=
    by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))
  have hp_pos : 0 < p := lt_trans hd_pos hp
  have hp_one : 1 < p := lt_of_le_of_lt hd_one_le hp
  have hpm1_pos : 0 < p - 1 := by linarith
  have hq_pos : 0 < p / (p - 1) := div_pos hp_pos hpm1_pos
  have hα_def : (1 - (d : ℝ)) * (p / (p - 1)) =
      (1 - (d : ℝ)) * (p / (p - 1)) := rfl
  have hdα_pos : (0 : ℝ) < (d : ℝ) + (1 - (d : ℝ)) * (p / (p - 1)) := by
    have h_lhs : -(d : ℝ) * (p - 1) < (1 - (d : ℝ)) * p := by nlinarith [hp]
    have h_rhs_eq : -(d : ℝ) = -(d : ℝ) * (p - 1) / (p - 1) :=
      (mul_div_cancel_right₀ _ hpm1_pos.ne').symm
    have heq : (1 - (d : ℝ)) * (p / (p - 1)) = (1 - (d : ℝ)) * p / (p - 1) := by ring
    rw [heq]
    have : -(d : ℝ) < (1 - (d : ℝ)) * p / (p - 1) := by
      rw [h_rhs_eq]
      exact (div_lt_div_iff_of_pos_right hpm1_pos).mpr h_lhs
    linarith
  have hvol_pos : (0 : ℝ) < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  unfold smoothHolderConst
  positivity

theorem smooth_pointwise_holder_bound_explicit
    {p : ℝ} (hp : (d : ℝ) < p) {z : E} {r : ℝ} (hr : 0 < r)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {x : E} (hx : x ∈ Metric.ball z r) :
    ‖u x - ⨍ y in Metric.ball z r, u y ∂volume‖ ≤
      smoothHolderConst d p * r ^ (1 - (d : ℝ) / p) *
        (eLpNorm (fun y => ‖fderiv ℝ u y‖) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball z r))).toReal := by
  classical
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hd_one_le : (1 : ℝ) ≤ d :=
    by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))
  have hp_pos : 0 < p := lt_trans hd_pos hp
  have hp_one : 1 < p := lt_of_le_of_lt hd_one_le hp
  have hpm1_pos : 0 < p - 1 := by linarith
  set q : ℝ := p / (p - 1) with hq_def
  have hq_pos : 0 < q := div_pos hp_pos hpm1_pos
  have hq_one : 1 ≤ q := by
    rw [hq_def, le_div_iff₀ hpm1_pos]; linarith
  have hpq_holder : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp_one
  have hrep := representation_formula_smooth_translated (d := d) hr hu hx
  set α : ℝ := (1 - (d : ℝ)) * q with hα_def
  have hα_gt : -(d : ℝ) < α := by
    have h_lhs : -(d : ℝ) * (p - 1) < (1 - (d : ℝ)) * p := by nlinarith [hp]
    have h_rhs_eq : -(d : ℝ) = -(d : ℝ) * (p - 1) / (p - 1) :=
      (mul_div_cancel_right₀ _ hpm1_pos.ne').symm
    rw [h_rhs_eq]
    rw [show α = (1 - (d : ℝ)) * p / (p - 1) from by simp [hα_def, hq_def]; ring]
    exact (div_lt_div_iff_of_pos_right hpm1_pos).mpr h_lhs
  have hdα_pos : (0 : ℝ) < (d : ℝ) + α := by linarith
  have hKint_le :
      ∫ y in Metric.ball z r, ‖x - y‖ ^ α ∂volume ≤
        (d : ℝ) * (volume (Metric.ball (0 : E) 1)).toReal *
          (2 * r) ^ ((d : ℝ) + α) / ((d : ℝ) + α) := by
    have h1 := integral_norm_sub_rpow_ball_at_other_center (d := d) hα_gt (z := z) (x := x)
      (R := r) hr
    have hxz : dist x z < r := by rw [Metric.mem_ball] at hx; exact hx
    have htwo_r : r + dist x z ≤ 2 * r := by linarith
    have htwo_r_nn : 0 ≤ 2 * r := by linarith
    have hr_dist_nn : 0 ≤ r + dist x z := by have := dist_nonneg (x := x) (y := z); linarith
    have h_rpow_le : (r + dist x z) ^ ((d : ℝ) + α) ≤ (2 * r) ^ ((d : ℝ) + α) := by
      apply Real.rpow_le_rpow hr_dist_nn htwo_r hdα_pos.le
    calc ∫ y in Metric.ball z r, ‖x - y‖ ^ α ∂volume
        ≤ (d : ℝ) * (volume (Metric.ball (0 : E) 1)).toReal *
            (r + dist x z) ^ ((d : ℝ) + α) / ((d : ℝ) + α) := h1
      _ ≤ (d : ℝ) * (volume (Metric.ball (0 : E) 1)).toReal *
            (2 * r) ^ ((d : ℝ) + α) / ((d : ℝ) + α) := by
          apply div_le_div_of_nonneg_right _ hdα_pos.le
          apply mul_le_mul_of_nonneg_left h_rpow_le
          have hvol_nn : 0 ≤ (volume (Metric.ball (0 : E) 1)).toReal := by positivity
          have hd_nn : 0 ≤ (d : ℝ) := hd_pos.le
          positivity
  obtain ⟨C, hC_nn, hbound⟩ := smooth_pointwise_holder_bound (d := d) hp hr hu hx
  set C₁ : ℝ := (2 : ℝ) ^ d / ((d : ℝ) * (volume (Metric.ball (0 : E) 1)).toReal) with hC₁_def
  have hvol_pos : (0 : ℝ) < (volume (Metric.ball (0 : E) 1)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  have hC₁_pos : 0 < C₁ := by rw [hC₁_def]; positivity
  set Iint : ℝ := ∫ y in Metric.ball z r, ‖fderiv ℝ u y‖ ^ p ∂volume with hIint_def
  set Kint : ℝ := ∫ y in Metric.ball z r, ‖x - y‖ ^ α ∂volume with hKint_def
  have hIint_nn : 0 ≤ Iint := setIntegral_nonneg measurableSet_ball
    (fun y _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hKint_nn : 0 ≤ Kint := setIntegral_nonneg measurableSet_ball
    (fun y _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hf_memLp : MemLp (fun y : E => ‖fderiv ℝ u y‖) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball z r)) :=
    smooth_grad_memLp_on_ball (d := d) hr hu
  have hK_memLp : MemLp (fun y : E => ‖x - y‖ ^ (1 - (d : ℝ))) (ENNReal.ofReal q)
      (volume.restrict (Metric.ball z r)) :=
    riesz_kernel_memLp (d := d) hp hr x
  set μ : Measure E := volume.restrict (Metric.ball z r) with hμ_def
  have hf_aemeas : AEMeasurable (fun y : E => ENNReal.ofReal (‖fderiv ℝ u y‖)) μ :=
    hf_memLp.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hK_aemeas : AEMeasurable (fun y : E => ENNReal.ofReal (‖x - y‖ ^ (1 - (d : ℝ)))) μ :=
    hK_memLp.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ := μ) hpq_holder hf_aemeas hK_aemeas
  have hf_nonneg : ∀ y : E, 0 ≤ ‖fderiv ℝ u y‖ := fun y => norm_nonneg _
  have hHolder_simp :
      (∫⁻ y, ENNReal.ofReal (‖fderiv ℝ u y‖ * ‖x - y‖ ^ (1 - (d : ℝ))) ∂μ) ≤
        (∫⁻ y, (ENNReal.ofReal ‖fderiv ℝ u y‖) ^ p ∂μ) ^ (1 / p) *
        (∫⁻ y, (ENNReal.ofReal (‖x - y‖ ^ (1 - (d : ℝ)))) ^ q ∂μ) ^ (1 / q) := by
    have h_LHS_eq :
        (∫⁻ y, ENNReal.ofReal (‖fderiv ℝ u y‖ * ‖x - y‖ ^ (1 - (d : ℝ))) ∂μ) =
        ∫⁻ a,
          ((fun y => ENNReal.ofReal ‖fderiv ℝ u y‖) *
            (fun y => ENNReal.ofReal (‖x - y‖ ^ (1 - (d : ℝ))))) a ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards with y
      rw [Pi.mul_apply, ENNReal.ofReal_mul (hf_nonneg y)]
    rw [h_LHS_eq]
    exact hHolder
  have hf_p_eq : ∀ y : E, (ENNReal.ofReal (‖fderiv ℝ u y‖)) ^ p =
      ENNReal.ofReal (‖fderiv ℝ u y‖ ^ p) := by
    intro y; rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp_pos.le]
  have hK_q_eq : ∀ y : E, (ENNReal.ofReal (‖x - y‖ ^ (1 - (d : ℝ)))) ^ q =
      ENNReal.ofReal (‖x - y‖ ^ ((1 - (d : ℝ)) * q)) := by
    intro y
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hq_pos.le]
    congr 1
    rw [← Real.rpow_mul (norm_nonneg _)]
  have hHolder' :
      (∫⁻ y, ENNReal.ofReal (‖fderiv ℝ u y‖ * ‖x - y‖ ^ (1 - (d : ℝ))) ∂μ) ≤
        (∫⁻ y, ENNReal.ofReal (‖fderiv ℝ u y‖ ^ p) ∂μ) ^ (1 / p) *
          (∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ ((1 - (d : ℝ)) * q)) ∂μ) ^ (1 / q) := by
    refine hHolder_simp.trans_eq ?_
    rw [show (∫⁻ a, (ENNReal.ofReal (‖fderiv ℝ u a‖)) ^ p ∂μ) =
        ∫⁻ y, ENNReal.ofReal (‖fderiv ℝ u y‖ ^ p) ∂μ from
      lintegral_congr_ae (Eventually.of_forall hf_p_eq)]
    rw [show (∫⁻ a, (ENNReal.ofReal (‖x - a‖ ^ (1 - (d : ℝ)))) ^ q ∂μ) =
        ∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ ((1 - (d : ℝ)) * q)) ∂μ from
      lintegral_congr_ae (Eventually.of_forall hK_q_eq)]
  have hf_p_int : IntegrableOn (fun y => ‖fderiv ℝ u y‖ ^ p) (Metric.ball z r) volume := by
    have h1 := hf_memLp.integrable_norm_rpow
      (by rw [Ne, ENNReal.ofReal_eq_zero]; exact not_le.mpr hp_pos) ENNReal.ofReal_ne_top
    rw [ENNReal.toReal_ofReal hp_pos.le] at h1
    refine h1.congr (ae_of_all _ fun y => ?_)
    change ‖‖fderiv ℝ u y‖‖ ^ p = ‖fderiv ℝ u y‖ ^ p
    rw [show ‖‖fderiv ℝ u y‖‖ = ‖fderiv ℝ u y‖ from
      Real.norm_of_nonneg (norm_nonneg _)]
  have hf_p_lint :
      ∫⁻ y, ENNReal.ofReal (‖fderiv ℝ u y‖ ^ p) ∂μ =
      ENNReal.ofReal (∫ y in Metric.ball z r, ‖fderiv ℝ u y‖ ^ p ∂volume) := by
    rw [hμ_def]
    rw [← ofReal_integral_eq_lintegral_ofReal hf_p_int
      (ae_of_all _ fun y => Real.rpow_nonneg (norm_nonneg _) _)]
  have hK_alpha_int : IntegrableOn (fun y : E => ‖x - y‖ ^ α)
      (Metric.ball z r) volume := by
    have hsub : Metric.ball z r ⊆ Metric.ball x (r + dist x z) := by
      intro y hy
      rw [Metric.mem_ball] at hy ⊢
      calc dist y x ≤ dist y z + dist z x := dist_triangle y z x
        _ < r + dist z x := by linarith
        _ = r + dist x z := by rw [dist_comm]
    have hRR_pos : 0 < r + dist x z := by have := dist_nonneg (x := x) (y := z); linarith
    have hint_origin :
        IntegrableOn (fun y : E => ‖y‖ ^ α) (Metric.ball (0 : E) (r + dist x z)) volume :=
      riesz_kernel_integrable_of_gt_neg_dim (d := d) hα_gt hRR_pos
    have hmp := measurePreserving_add_right (volume : Measure E) x
    have hemb := (MeasurableEquiv.addRight x : E ≃ᵐ E).measurableEmbedding
    have hpre : ((· + x) ⁻¹' Metric.ball x (r + dist x z)) =
        Metric.ball (0 : E) (r + dist x z) := by
      ext z; simp [Metric.mem_ball]
    have h_eq : ∀ w : E, ‖x - (w + x)‖ ^ α = ‖w‖ ^ α := by
      intro w
      congr 1
      rw [show x - (w + x) = -w from by abel, norm_neg]
    have hint_translated :
        IntegrableOn (fun w : E => ‖x - (w + x)‖ ^ α) (Metric.ball (0 : E) (r + dist x z))
          volume := by
      refine hint_origin.congr (ae_of_all _ ?_)
      intro w; exact (h_eq w).symm
    have hint_at_x : IntegrableOn (fun y : E => ‖x - y‖ ^ α)
        (Metric.ball x (r + dist x z)) volume := by
      have := (hmp.integrableOn_comp_preimage (β := E) (e := (· + x))
        (f := fun y : E => ‖x - y‖ ^ α) (s := Metric.ball x (r + dist x z)) hemb).mp
      apply this
      have hcomp_eq : (fun y => ‖x - y‖ ^ α) ∘ (· + x) =
          fun w : E => ‖x - (w + x)‖ ^ α := by funext; rfl
      rw [hcomp_eq, hpre]
      exact hint_translated
    exact hint_at_x.mono_set hsub
  have hK_alpha_lint :
      ∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ α) ∂μ =
      ENNReal.ofReal (∫ y in Metric.ball z r, ‖x - y‖ ^ α ∂volume) := by
    rw [hμ_def]
    rw [← ofReal_integral_eq_lintegral_ofReal hK_alpha_int
      (ae_of_all _ fun y => Real.rpow_nonneg (norm_nonneg _) _)]
  have hLHS_int : IntegrableOn (fun y : E => ‖fderiv ℝ u y‖ * ‖x - y‖ ^ (1 - (d : ℝ)))
      (Metric.ball z r) volume := by
    have hcont_grad := continuous_norm_fderiv hu
    obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn
      (isCompact_closedBall z r) hcont_grad.continuousOn
    have hM_nonneg : 0 ≤ M :=
      le_trans (norm_nonneg _) (hM z (Metric.mem_closedBall_self hr.le))
    have hK_int_orig : IntegrableOn (fun y : E => ‖x - y‖ ^ (1 - (d : ℝ)))
        (Metric.ball z r) volume := by
      have h_neg_d : -(d : ℝ) < 1 - (d : ℝ) := by linarith
      have hsub : Metric.ball z r ⊆ Metric.ball x (r + dist x z) := by
        intro y hy
        rw [Metric.mem_ball] at hy ⊢
        calc dist y x ≤ dist y z + dist z x := dist_triangle y z x
          _ < r + dist z x := by linarith
          _ = r + dist x z := by rw [dist_comm]
      have hRR_pos : 0 < r + dist x z := by
        have := dist_nonneg (x := x) (y := z); linarith
      have hint_origin :
          IntegrableOn (fun y : E => ‖y‖ ^ (1 - (d : ℝ)))
            (Metric.ball (0 : E) (r + dist x z)) volume :=
        riesz_kernel_integrable_of_gt_neg_dim (d := d) h_neg_d hRR_pos
      have hmp := measurePreserving_add_right (volume : Measure E) x
      have hemb := (MeasurableEquiv.addRight x : E ≃ᵐ E).measurableEmbedding
      have hpre : ((· + x) ⁻¹' Metric.ball x (r + dist x z)) =
          Metric.ball (0 : E) (r + dist x z) := by
        ext z; simp [Metric.mem_ball]
      have h_eq : ∀ w : E, ‖x - (w + x)‖ ^ (1 - (d : ℝ)) = ‖w‖ ^ (1 - (d : ℝ)) := by
        intro w
        congr 1
        rw [show x - (w + x) = -w from by abel, norm_neg]
      have hint_translated :
          IntegrableOn (fun w : E => ‖x - (w + x)‖ ^ (1 - (d : ℝ)))
            (Metric.ball (0 : E) (r + dist x z)) volume := by
        refine hint_origin.congr (ae_of_all _ ?_)
        intro w; exact (h_eq w).symm
      have hint_at_x : IntegrableOn (fun y : E => ‖x - y‖ ^ (1 - (d : ℝ)))
          (Metric.ball x (r + dist x z)) volume := by
        have := (hmp.integrableOn_comp_preimage (β := E) (e := (· + x))
          (f := fun y : E => ‖x - y‖ ^ (1 - (d : ℝ)))
          (s := Metric.ball x (r + dist x z)) hemb).mp
        apply this
        have hcomp_eq : (fun y => ‖x - y‖ ^ (1 - (d : ℝ))) ∘ (· + x) =
            fun w : E => ‖x - (w + x)‖ ^ (1 - (d : ℝ)) := by funext; rfl
        rw [hcomp_eq, hpre]
        exact hint_translated
      exact hint_at_x.mono_set hsub
    refine Integrable.mono (hK_int_orig.const_mul M) ?_ ?_
    · refine AEStronglyMeasurable.restrict ?_
      have h1 : AEStronglyMeasurable (fun y : E => ‖fderiv ℝ u y‖) volume :=
        (continuous_norm_fderiv hu).aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun y : E => ‖x - y‖ ^ (1 - (d : ℝ))) volume :=
        measurable_norm_sub_rpow (1 - (d : ℝ)) x
      exact h1.mul h2
    · refine ae_restrict_iff' measurableSet_ball |>.mpr ?_
      filter_upwards with y hy
      have hy' : y ∈ Metric.closedBall z r := Metric.ball_subset_closedBall hy
      have h_grad_le : ‖fderiv ℝ u y‖ ≤ M := by
        have h_at_y := hM y hy'
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h_at_y
        exact h_at_y
      have hk_nn : 0 ≤ ‖x - y‖ ^ (1 - (d : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
      have h_grad_nn : 0 ≤ ‖fderiv ℝ u y‖ := norm_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h_grad_nn hk_nn)]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hM_nonneg hk_nn)]
      exact mul_le_mul_of_nonneg_right h_grad_le hk_nn
  have hLHS_lint :
      ∫⁻ y, ENNReal.ofReal (‖fderiv ℝ u y‖ * ‖x - y‖ ^ (1 - (d : ℝ))) ∂μ =
      ENNReal.ofReal
        (∫ y in Metric.ball z r, ‖fderiv ℝ u y‖ * ‖x - y‖ ^ (1 - (d : ℝ)) ∂volume) := by
    rw [hμ_def]
    rw [← ofReal_integral_eq_lintegral_ofReal hLHS_int (ae_of_all _ fun y =>
      mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))]
  have hReal_bound :
      ∫ y in Metric.ball z r, ‖fderiv ℝ u y‖ * ‖x - y‖ ^ (1 - (d : ℝ)) ∂volume ≤
      Iint ^ (1 / p) * Kint ^ (1 / q) := by
    have hineq := hHolder'
    rw [hLHS_lint, hf_p_lint, hK_alpha_lint] at hineq
    rw [ENNReal.ofReal_rpow_of_nonneg hIint_nn (by positivity : 0 ≤ (1 / p : ℝ))] at hineq
    rw [ENNReal.ofReal_rpow_of_nonneg hKint_nn (by positivity : 0 ≤ (1 / q : ℝ))] at hineq
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hIint_nn _)] at hineq
    rwa [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hineq
  set Kbound : ℝ := (d : ℝ) * (volume (Metric.ball (0 : E) 1)).toReal *
        (2 * r) ^ ((d : ℝ) + α) / ((d : ℝ) + α) with hKbound_def
  have hKbound_nn : 0 ≤ Kbound := by
    have hr_nn : 0 ≤ 2 * r := by linarith
    rw [hKbound_def]; positivity
  have hKint_le_bound : Kint ≤ Kbound := hKint_le
  have hKint_pow_le : Kint ^ (1 / q) ≤ Kbound ^ (1 / q) := by
    apply Real.rpow_le_rpow hKint_nn hKint_le_bound (by positivity : (0 : ℝ) ≤ 1 / q)
  have h_dα_q : ((d : ℝ) + α) / q = 1 - (d : ℝ) / p := by
    rw [hα_def, hq_def]
    field_simp
    ring
  have h_two_r_rpow : (2 * r : ℝ) ^ ((d : ℝ) + α) =
      (2 : ℝ) ^ ((d : ℝ) + α) * r ^ ((d : ℝ) + α) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hr.le]
  set Kbase : ℝ := (d : ℝ) * (volume (Metric.ball (0 : E) 1)).toReal *
      (2 : ℝ) ^ ((d : ℝ) + α) / ((d : ℝ) + α) with hKbase_def
  have hKbase_nn : 0 ≤ Kbase := by
    rw [hKbase_def]; positivity
  have hKbound_eq : Kbound = Kbase * r ^ ((d : ℝ) + α) := by
    rw [hKbound_def, hKbase_def]
    rw [h_two_r_rpow]
    ring
  have hKbound_pow_eq : Kbound ^ (1 / q) = Kbase ^ (1 / q) * r ^ (((d : ℝ) + α) / q) := by
    rw [hKbound_eq]
    rw [Real.mul_rpow hKbase_nn (Real.rpow_nonneg hr.le _)]
    congr 1
    rw [← Real.rpow_mul hr.le]
    congr 1
    field_simp
  rw [h_dα_q] at hKbound_pow_eq
  have hsmoothC_eq : smoothHolderConst d p = C₁ * Kbase ^ (1 / q) := by
    unfold smoothHolderConst Kbase C₁ q α
    rfl
  calc ‖u x - ⨍ y in Metric.ball z r, u y ∂volume‖
      ≤ C₁ * ∫ y in Metric.ball z r, ‖fderiv ℝ u y‖ * ‖x - y‖ ^ (1 - (d : ℝ)) ∂volume :=
        hrep
    _ ≤ C₁ * (Iint ^ (1 / p) * Kint ^ (1 / q)) :=
        mul_le_mul_of_nonneg_left hReal_bound hC₁_pos.le
    _ ≤ C₁ * (Iint ^ (1 / p) * Kbound ^ (1 / q)) := by
        apply mul_le_mul_of_nonneg_left
        · apply mul_le_mul_of_nonneg_left hKint_pow_le
          exact Real.rpow_nonneg hIint_nn _
        · exact hC₁_pos.le
    _ = (C₁ * Kbase ^ (1 / q)) * r ^ (1 - (d : ℝ) / p) * Iint ^ (1 / p) := by
        rw [hKbound_pow_eq]; ring
    _ = smoothHolderConst d p * r ^ (1 - (d : ℝ) / p) * Iint ^ (1 / p) := by
        rw [hsmoothC_eq]
    _ = smoothHolderConst d p * r ^ (1 - (d : ℝ) / p) *
          (eLpNorm (fun y => ‖fderiv ℝ u y‖) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball z r))).toReal := by
        congr 1
        rw [hIint_def]
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
          (by rw [Ne, ENNReal.ofReal_eq_zero]; exact not_le.mpr hp_pos)
          ENNReal.ofReal_ne_top]
        rw [ENNReal.toReal_ofReal hp_pos.le]
        have h_eq :
            ∫⁻ y in Metric.ball z r, ‖‖fderiv ℝ u y‖‖ₑ ^ p ∂volume =
            ENNReal.ofReal (∫ y in Metric.ball z r, ‖fderiv ℝ u y‖ ^ p ∂volume) := by
          have h_lint_eq :
              ∫⁻ y in Metric.ball z r, ‖‖fderiv ℝ u y‖‖ₑ ^ p ∂volume =
              ∫⁻ y in Metric.ball z r, ENNReal.ofReal (‖fderiv ℝ u y‖ ^ p) ∂volume := by
            refine lintegral_congr_ae ?_
            filter_upwards with y
            rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (norm_nonneg _)]
            rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp_pos.le]
          rw [h_lint_eq]
          exact (ofReal_integral_eq_lintegral_ofReal hf_p_int
            (ae_of_all _ fun y => Real.rpow_nonneg (norm_nonneg _) _)).symm
        rw [h_eq]
        rw [show (ENNReal.ofReal (∫ y in Metric.ball z r, ‖fderiv ℝ u y‖ ^ p) ^ (1 / p)).toReal =
            ((ENNReal.ofReal (∫ y in Metric.ball z r, ‖fderiv ℝ u y‖ ^ p)).toReal) ^ (1 / p) from
            (ENNReal.toReal_rpow _ _).symm]
        rw [ENNReal.toReal_ofReal hIint_nn]

end

lemma norm_fderiv_eq_norm_partials_local
    {ψ : E → ℝ} (y : E) :
    ‖fderiv ℝ ψ y‖ =
      ‖(WithLp.toLp 2
        (fun i : Fin d => (fderiv ℝ ψ y) (EuclideanSpace.single i 1)) : E)‖ := by
  classical
  set v : E :=
    (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ ψ y) with hv_def
  have hv_map : (InnerProductSpace.toDual ℝ E) v = fderiv ℝ ψ y := by simp [v]
  have h_fderiv_norm_eq_v : ‖fderiv ℝ ψ y‖ = ‖v‖ := by simp [v]
  have h_v_eq_components : v =
      WithLp.toLp 2
        (fun i : Fin d => (fderiv ℝ ψ y) (EuclideanSpace.single i 1)) := by
    ext i
    calc
      v i = inner ℝ v (EuclideanSpace.single i (1 : ℝ)) := by
        simpa using
          (EuclideanSpace.inner_single_right (i := i) (a := (1 : ℝ)) v).symm
      _ = ((InnerProductSpace.toDual ℝ E) v) (EuclideanSpace.single i (1 : ℝ)) := by
        rw [InnerProductSpace.toDual_apply_apply]
      _ = (fderiv ℝ ψ y) (EuclideanSpace.single i (1 : ℝ)) := by rw [hv_map]
      _ = (WithLp.toLp 2
            (fun j : Fin d => (fderiv ℝ ψ y) (EuclideanSpace.single j 1))) i := by simp
  rw [h_fderiv_norm_eq_v, h_v_eq_components]

lemma euclidean_norm_le_sum_norms (v : E) :
    ‖v‖ ≤ ∑ i : Fin d, ‖v i‖ := by
  classical
  have h_v_sum :
      v = ∑ i : Fin d, EuclideanSpace.single i (v i) := by
    ext j
    simp [Finset.sum_apply]
  conv_lhs => rw [h_v_sum]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  simp

private theorem smooth_memLp_on_ball
    {p : ℝ} (_hp_pos : 0 < p) {x₀ : E} {R : ℝ} (_hR : 0 < R)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    MemLp u (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R)) := by
  obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_closedBall x₀ R) hu.continuous.continuousOn
  have : IsFiniteMeasure (volume.restrict (Metric.ball x₀ R)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top
  refine MemLp.of_le_mul (g := fun _ : E => (1 : ℝ)) (c := M) ?_ ?_ ?_
  · exact memLp_const (1 : ℝ)
  · exact hu.continuous.aestronglyMeasurable.restrict
  · refine ae_restrict_iff' measurableSet_ball |>.mpr ?_
    filter_upwards with y hy
    have hy' : y ∈ Metric.closedBall x₀ R := Metric.ball_subset_closedBall hy
    have h_at_y := hM y hy'
    rw [norm_one, mul_one]
    exact h_at_y

private lemma smooth_setIntegral_norm_le_eLpNorm
    {p : ℝ} (hp_one : 1 < p) {x₀ : E} {R : ℝ} (hR : 0 < R)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ∫ y in Metric.ball x₀ R, ‖u y‖ ∂volume ≤
      (eLpNorm u (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R))).toReal *
        ((volume (Metric.ball x₀ R)).toReal) ^ (1 - 1 / p) := by
  have hp_pos : 0 < p := lt_trans zero_lt_one hp_one
  have hu_memLp : MemLp u (ENNReal.ofReal p)
      (volume.restrict (Metric.ball x₀ R)) := smooth_memLp_on_ball hp_pos hR hu
  set μ : Measure E := volume.restrict (Metric.ball x₀ R) with hμ_def
  have : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    rw [hμ_def, Measure.restrict_apply_univ]
    exact measure_ball_lt_top
  have hp_ennreal_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal hp_one.le
  have h_compare := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ) (f := u)
    hp_ennreal_le hu_memLp.aestronglyMeasurable
  have hp_top : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp_pos.le
  have h_exp_eq : (1 : ℝ) / (1 : ℝ≥0∞).toReal - 1 / (ENNReal.ofReal p).toReal = 1 - 1 / p := by
    rw [hp_top]
    simp
  rw [h_exp_eq] at h_compare
  have hsub_nn' : (0 : ℝ) ≤ 1 - 1 / p := by
    rw [sub_nonneg, div_le_one hp_pos]; exact hp_one.le
  have h_lt_top : eLpNorm u (ENNReal.ofReal p) μ *
      (μ Set.univ) ^ (1 - 1 / p) ≠ ⊤ := by
    have h_finite : (μ Set.univ) ≠ ⊤ := measure_ne_top _ _
    have h_eLp_ne_top : eLpNorm u (ENNReal.ofReal p) μ ≠ ⊤ := hu_memLp.eLpNorm_ne_top
    exact ENNReal.mul_ne_top h_eLp_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hsub_nn' h_finite)
  have h_le_real := ENNReal.toReal_mono h_lt_top h_compare
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow] at h_le_real
  have hu_int : Integrable u μ := by
    rw [hμ_def]
    have h_int_compact : IntegrableOn u (Metric.closedBall x₀ R) volume :=
      hu.continuous.continuousOn.integrableOn_compact (isCompact_closedBall x₀ R)
    exact h_int_compact.mono_set ball_subset_closedBall
  have h_eLp_one_eq :
      (eLpNorm u 1 μ).toReal = ∫ y in Metric.ball x₀ R, ‖u y‖ ∂volume := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    have h_lint :
        ∫⁻ y, ‖u y‖ₑ ∂μ = ENNReal.ofReal (∫ y in Metric.ball x₀ R, ‖u y‖ ∂volume) := by
      have h_eq :
          ∫⁻ y, ‖u y‖ₑ ∂μ = ∫⁻ y, ENNReal.ofReal ‖u y‖ ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards with y
        rw [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs]
      rw [h_eq, hμ_def]
      exact (ofReal_integral_eq_lintegral_ofReal hu_int.norm
        (ae_of_all _ fun _ => norm_nonneg _)).symm
    rw [h_lint]
    rw [ENNReal.toReal_ofReal (integral_nonneg fun _ => norm_nonneg _)]
  rw [h_eLp_one_eq] at h_le_real
  rw [hμ_def, Measure.restrict_apply_univ] at h_le_real
  exact h_le_real

lemma smooth_norm_average_le
    {p : ℝ} (hp_one : 1 < p) {x₀ : E} {R : ℝ} (hR : 0 < R)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ‖⨍ y in Metric.ball x₀ R, u y ∂volume‖ ≤
      (eLpNorm u (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R))).toReal *
        ((volume (Metric.ball x₀ R)).toReal) ^ (-(1 / p)) := by
  have hp_pos : 0 < p := lt_trans zero_lt_one hp_one
  have hvol_pos : 0 < (volume (Metric.ball x₀ R)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume x₀ hR).ne' measure_ball_lt_top.ne
  have h_avg_eq :
      ⨍ y in Metric.ball x₀ R, u y ∂volume =
        ((volume (Metric.ball x₀ R)).toReal)⁻¹ • ∫ y in Metric.ball x₀ R, u y ∂volume := by
    rw [setAverage_eq, measureReal_def]
  rw [h_avg_eq, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (ENNReal.toReal_nonneg)]
  have h_int_norm :
      ‖∫ y in Metric.ball x₀ R, u y ∂volume‖ ≤
        ∫ y in Metric.ball x₀ R, ‖u y‖ ∂volume := by
    exact norm_integral_le_integral_norm _
  have h_L1_le := smooth_setIntegral_norm_le_eLpNorm (x₀ := x₀) hp_one hR hu
  have h_combined :
      ‖∫ y in Metric.ball x₀ R, u y ∂volume‖ ≤
        (eLpNorm u (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R))).toReal *
          ((volume (Metric.ball x₀ R)).toReal) ^ (1 - 1 / p) :=
    le_trans h_int_norm h_L1_le
  have h_vol_inv_nn : 0 ≤ ((volume (Metric.ball x₀ R)).toReal)⁻¹ :=
    inv_nonneg.mpr ENNReal.toReal_nonneg
  have h_eLp_nn : 0 ≤ (eLpNorm u (ENNReal.ofReal p)
      (volume.restrict (Metric.ball x₀ R))).toReal := ENNReal.toReal_nonneg
  have h_left_le :
      ((volume (Metric.ball x₀ R)).toReal)⁻¹ * ‖∫ y in Metric.ball x₀ R, u y ∂volume‖ ≤
        ((volume (Metric.ball x₀ R)).toReal)⁻¹ *
          ((eLpNorm u (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R))).toReal *
            ((volume (Metric.ball x₀ R)).toReal) ^ (1 - 1 / p)) :=
    mul_le_mul_of_nonneg_left h_combined h_vol_inv_nn
  have h_rpow_collapse :
      ((volume (Metric.ball x₀ R)).toReal)⁻¹ *
        ((volume (Metric.ball x₀ R)).toReal) ^ (1 - 1 / p) =
      ((volume (Metric.ball x₀ R)).toReal) ^ (-(1 / p)) := by
    rw [show ((volume (Metric.ball x₀ R)).toReal)⁻¹ =
      ((volume (Metric.ball x₀ R)).toReal) ^ (-1 : ℝ) from
      (Real.rpow_neg_one _).symm]
    rw [← Real.rpow_add hvol_pos]
    congr 1
    ring
  calc ((volume (Metric.ball x₀ R)).toReal)⁻¹ *
        ‖∫ y in Metric.ball x₀ R, u y ∂volume‖
      ≤ ((volume (Metric.ball x₀ R)).toReal)⁻¹ *
          ((eLpNorm u (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R))).toReal *
            ((volume (Metric.ball x₀ R)).toReal) ^ (1 - 1 / p)) := h_left_le
    _ = (eLpNorm u (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ R))).toReal *
          (((volume (Metric.ball x₀ R)).toReal)⁻¹ *
            ((volume (Metric.ball x₀ R)).toReal) ^ (1 - 1 / p)) := by ring
    _ = (eLpNorm u (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ R))).toReal *
          ((volume (Metric.ball x₀ R)).toReal) ^ (-(1 / p)) := by
        rw [h_rpow_collapse]

end EuclideanMorrey
end Sobolev
