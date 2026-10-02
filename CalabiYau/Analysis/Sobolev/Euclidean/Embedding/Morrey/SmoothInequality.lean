-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Euclidean/Embedding/Morrey/SmoothInequality.lean
-- Locally modified.
module
public import CalabiYau.Analysis.DeGiorgi.SobolevSpace.Witnesses
public import CalabiYau.Analysis.DeGiorgi.SobolevSpace.Approximation
public import CalabiYau.Analysis.DeGiorgi.Poincare
public import CalabiYau.Analysis.DeGiorgi.SobolevPoincare
public import CalabiYau.Analysis.DeGiorgi.UnitBallApproximation
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Integral.Average
public import CalabiYau.Analysis.Sobolev.Euclidean.Embedding.Morrey.SmoothHolderBound

@[expose] public section

-- Private declarations used in public declarations require the compatibility option below..

noncomputable section

open MeasureTheory Set Filter Topology Metric Function
open scoped ENNReal NNReal

namespace Sobolev
namespace EuclideanMorrey
variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem smooth_morrey_pair_bound
    {d : ℕ} [NeZero d] {p : ℝ} (hp : (d : ℝ) < p)
    {x₀ : EuclideanSpace ℝ (Fin d)} {R : ℝ} (hR : 0 < R)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {x y : EuclideanSpace ℝ (Fin d)},
        x ∈ Metric.ball x₀ (R / 2) → y ∈ Metric.ball x₀ (R / 2) →
          ‖u x - u y‖ ≤ C * (dist x y) ^ (1 - (d : ℝ) / p) *
            (eLpNorm (fun z => ‖fderiv ℝ u z‖) (ENNReal.ofReal p)
              (volume.restrict (Metric.ball x₀ R))).toReal := by
  classical
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hd_one_le : (1 : ℝ) ≤ d :=
    by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))
  have hp_pos : 0 < p := lt_trans hd_pos hp
  have hp_one : 1 < p := lt_of_le_of_lt hd_one_le hp
  have h_exp_pos : 0 < 1 - (d : ℝ) / p := by
    rw [sub_pos]
    rw [div_lt_one hp_pos]
    exact hp
  have hC₀_nn : 0 ≤ smoothHolderConst d p := smoothHolderConst_nonneg hp
  set C : ℝ := (2 : ℝ) * (2 : ℝ) ^ (1 - (d : ℝ) / p) * smoothHolderConst d p with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    have h2_pow_nn : 0 ≤ (2 : ℝ) ^ (1 - (d : ℝ) / p) :=
      Real.rpow_nonneg (by norm_num) _
    positivity
  refine ⟨C, hC_nn, ?_⟩
  intro x y hx hy
  set N : ℝ := (eLpNorm (fun z => ‖fderiv ℝ u z‖) (ENNReal.ofReal p)
    (volume.restrict (Metric.ball x₀ R))).toReal with hN_def
  have hN_nn : 0 ≤ N := ENNReal.toReal_nonneg
  by_cases h_small : dist x y < R / 2
  · by_cases h_zero : dist x y = 0
    · have hxy_eq : x = y := dist_eq_zero.mp h_zero
      rw [hxy_eq, sub_self, norm_zero]
      have h_zero_pow : (dist y y) ^ (1 - (d : ℝ) / p) = 0 := by
        rw [dist_self]
        exact Real.zero_rpow h_exp_pos.ne'
      rw [h_zero_pow, mul_zero, zero_mul]
    · have h_dist_pos : 0 < dist x y := lt_of_le_of_ne dist_nonneg (Ne.symm h_zero)
      set m : EuclideanSpace ℝ (Fin d) := (1 / 2 : ℝ) • (x + y) with hm_def
      have h_m_minus_x₀ : m - x₀ = (1 / 2 : ℝ) • (x - x₀) + (1 / 2 : ℝ) • (y - x₀) := by
        rw [hm_def]
        rw [smul_add]
        have hx₀_split : x₀ = (1 / 2 : ℝ) • x₀ + (1 / 2 : ℝ) • x₀ := by
          rw [← add_smul]
          rw [show (1 : ℝ)/2 + 1/2 = 1 from by norm_num, one_smul]
        nth_rewrite 1 [hx₀_split]
        rw [smul_sub, smul_sub]
        abel
      have h_m_dist : dist m x₀ < R / 2 := by
        have hxR2 : dist x x₀ < R / 2 := by
          rw [Metric.mem_ball] at hx
          exact hx
        have hyR2 : dist y x₀ < R / 2 := by
          rw [Metric.mem_ball] at hy
          exact hy
        have h_mid : dist m x₀ ≤
            (1 / 2 : ℝ) * dist x x₀ + (1 / 2 : ℝ) * dist y x₀ := by
          rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, h_m_minus_x₀]
          have hsum : ‖(1 / 2 : ℝ) • (x - x₀) + (1 / 2 : ℝ) • (y - x₀)‖ ≤
              ‖(1 / 2 : ℝ) • (x - x₀)‖ + ‖(1 / 2 : ℝ) • (y - x₀)‖ :=
            norm_add_le _ _
          rw [norm_smul, norm_smul] at hsum
          rw [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hsum
          exact hsum
        have h_bound : (1 / 2 : ℝ) * dist x x₀ + (1 / 2 : ℝ) * dist y x₀ < R / 2 := by
          have h_x_lt : (1 / 2 : ℝ) * dist x x₀ < (1 / 2 : ℝ) * (R / 2) :=
            mul_lt_mul_of_pos_left hxR2 (by norm_num : (0 : ℝ) < 1 / 2)
          have h_y_lt : (1 / 2 : ℝ) * dist y x₀ < (1 / 2 : ℝ) * (R / 2) :=
            mul_lt_mul_of_pos_left hyR2 (by norm_num : (0 : ℝ) < 1 / 2)
          linarith
        linarith
      have h_ball_sub : Metric.ball m (dist x y) ⊆ Metric.ball x₀ R := by
        intro z hz
        rw [Metric.mem_ball] at hz ⊢
        calc dist z x₀ ≤ dist z m + dist m x₀ := dist_triangle z m x₀
          _ < dist x y + R / 2 := add_lt_add hz h_m_dist
          _ < R / 2 + R / 2 := by linarith
          _ = R := by ring
      have h_x_minus_m : x - m = (1 / 2 : ℝ) • (x - y) := by
        rw [hm_def, smul_add]
        have hx_split : x = (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • x := by
          rw [← add_smul]
          rw [show (1 : ℝ)/2 + 1/2 = 1 from by norm_num, one_smul]
        rw [smul_sub]
        nth_rewrite 1 [hx_split]
        abel
      have h_y_minus_m : y - m = (1 / 2 : ℝ) • (y - x) := by
        rw [hm_def, smul_add]
        have hy_split : y = (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • y := by
          rw [← add_smul]
          rw [show (1 : ℝ)/2 + 1/2 = 1 from by norm_num, one_smul]
        rw [smul_sub]
        nth_rewrite 1 [hy_split]
        abel
      have h_dx_m : dist x m = dist x y / 2 := by
        rw [dist_eq_norm, h_x_minus_m, norm_smul]
        rw [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        rw [← dist_eq_norm]; ring
      have h_dy_m : dist y m = dist x y / 2 := by
        rw [dist_eq_norm, h_y_minus_m, norm_smul]
        rw [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        rw [show y - x = -(x - y) from by abel, norm_neg]
        rw [← dist_eq_norm]; ring
      have hx_in : x ∈ Metric.ball m (dist x y) := by
        rw [Metric.mem_ball, h_dx_m]; linarith
      have hy_in : y ∈ Metric.ball m (dist x y) := by
        rw [Metric.mem_ball, h_dy_m]; linarith
      have h_at_x := smooth_pointwise_holder_bound_explicit (d := d) hp h_dist_pos hu hx_in
      have h_at_y := smooth_pointwise_holder_bound_explicit (d := d) hp h_dist_pos hu hy_in
      set N_small : ℝ := (eLpNorm (fun z => ‖fderiv ℝ u z‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball m (dist x y)))).toReal with hN_small_def
      have hN_small_le : N_small ≤ N := by
        rw [hN_small_def, hN_def]
        exact smooth_grad_eLpNorm_le_of_ball_subset hR hu h_ball_sub
      set Mavg : ℝ := ⨍ z in Metric.ball m (dist x y), u z ∂volume with hMavg_def
      have h_at_x' : ‖u x - Mavg‖ ≤
          smoothHolderConst d p * dist x y ^ (1 - (d : ℝ) / p) * N_small := h_at_x
      have h_at_y' : ‖u y - Mavg‖ ≤
          smoothHolderConst d p * dist x y ^ (1 - (d : ℝ) / p) * N_small := h_at_y
      have h_triangle : ‖u x - u y‖ ≤ ‖u x - Mavg‖ + ‖u y - Mavg‖ := by
        calc ‖u x - u y‖ = ‖(u x - Mavg) - (u y - Mavg)‖ := by ring_nf
          _ ≤ ‖u x - Mavg‖ + ‖u y - Mavg‖ := norm_sub_le _ _
      have h_dxy_pow_nn : 0 ≤ dist x y ^ (1 - (d : ℝ) / p) :=
        Real.rpow_nonneg dist_nonneg _
      have h_step1 : ‖u x - u y‖ ≤
          2 * (smoothHolderConst d p * dist x y ^ (1 - (d : ℝ) / p) * N_small) := by
        linarith
      have h_step2 : 2 * (smoothHolderConst d p * dist x y ^ (1 - (d : ℝ) / p) * N_small) ≤
          2 * (smoothHolderConst d p * dist x y ^ (1 - (d : ℝ) / p) * N) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
        apply mul_le_mul_of_nonneg_left hN_small_le
        exact mul_nonneg hC₀_nn h_dxy_pow_nn
      have h_step3 : 2 * (smoothHolderConst d p * dist x y ^ (1 - (d : ℝ) / p) * N) ≤
          C * dist x y ^ (1 - (d : ℝ) / p) * N := by
        rw [hC_def]
        have h_rfl : (2 : ℝ) * (smoothHolderConst d p * dist x y ^ (1 - (d : ℝ) / p) * N) =
            2 * smoothHolderConst d p * dist x y ^ (1 - (d : ℝ) / p) * N := by ring
        rw [h_rfl]
        have h_2_le : (2 : ℝ) * smoothHolderConst d p ≤
            (2 : ℝ) * (2 : ℝ) ^ (1 - (d : ℝ) / p) * smoothHolderConst d p := by
          have h_2pow_ge_one : (1 : ℝ) ≤ (2 : ℝ) ^ (1 - (d : ℝ) / p) :=
            Real.one_le_rpow (by norm_num) h_exp_pos.le
          have : (2 : ℝ) ≤ (2 : ℝ) * (2 : ℝ) ^ (1 - (d : ℝ) / p) := by
            calc (2 : ℝ) = 2 * 1 := by ring
              _ ≤ 2 * (2 : ℝ) ^ (1 - (d : ℝ) / p) :=
                  mul_le_mul_of_nonneg_left h_2pow_ge_one (by norm_num)
          exact mul_le_mul_of_nonneg_right this hC₀_nn
        have h_factor :
            (2 : ℝ) * smoothHolderConst d p * dist x y ^ (1 - (d : ℝ) / p) * N ≤
              (2 : ℝ) * (2 : ℝ) ^ (1 - (d : ℝ) / p) * smoothHolderConst d p *
                dist x y ^ (1 - (d : ℝ) / p) * N := by
          have h_inner :
              (2 : ℝ) * smoothHolderConst d p *
                (dist x y ^ (1 - (d : ℝ) / p) * N) ≤
              (2 : ℝ) * (2 : ℝ) ^ (1 - (d : ℝ) / p) * smoothHolderConst d p *
                (dist x y ^ (1 - (d : ℝ) / p) * N) :=
            mul_le_mul_of_nonneg_right h_2_le (mul_nonneg h_dxy_pow_nn hN_nn)
          linarith
        exact h_factor
      linarith
  · have h_large : R / 2 ≤ dist x y := not_lt.mp h_small
    have hx_R : x ∈ Metric.ball x₀ R := by
      rw [Metric.mem_ball] at hx ⊢
      linarith
    have hy_R : y ∈ Metric.ball x₀ R := by
      rw [Metric.mem_ball] at hy ⊢
      linarith
    have h_at_x := smooth_pointwise_holder_bound_explicit (d := d) hp hR hu hx_R
    have h_at_y := smooth_pointwise_holder_bound_explicit (d := d) hp hR hu hy_R
    set Mavg : ℝ := ⨍ z in Metric.ball x₀ R, u z ∂volume with hMavg_def
    have h_at_x' : ‖u x - Mavg‖ ≤
        smoothHolderConst d p * R ^ (1 - (d : ℝ) / p) * N := h_at_x
    have h_at_y' : ‖u y - Mavg‖ ≤
        smoothHolderConst d p * R ^ (1 - (d : ℝ) / p) * N := h_at_y
    have h_triangle : ‖u x - u y‖ ≤ ‖u x - Mavg‖ + ‖u y - Mavg‖ := by
      calc ‖u x - u y‖ = ‖(u x - Mavg) - (u y - Mavg)‖ := by ring_nf
        _ ≤ ‖u x - Mavg‖ + ‖u y - Mavg‖ := norm_sub_le _ _
    have h_R_pow_nn : 0 ≤ R ^ (1 - (d : ℝ) / p) := Real.rpow_nonneg hR.le _
    have h_step1 : ‖u x - u y‖ ≤
        2 * (smoothHolderConst d p * R ^ (1 - (d : ℝ) / p) * N) := by linarith
    have h_R_le_2dxy : R ≤ 2 * dist x y := by linarith
    have h_R_rpow_le : R ^ (1 - (d : ℝ) / p) ≤
        (2 : ℝ) ^ (1 - (d : ℝ) / p) * dist x y ^ (1 - (d : ℝ) / p) := by
      have h2dxy_nn : 0 ≤ 2 * dist x y := by linarith
      have h_le_pow : R ^ (1 - (d : ℝ) / p) ≤ (2 * dist x y) ^ (1 - (d : ℝ) / p) :=
        Real.rpow_le_rpow hR.le h_R_le_2dxy h_exp_pos.le
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) dist_nonneg] at h_le_pow
      exact h_le_pow
    have h_step2 : 2 * (smoothHolderConst d p * R ^ (1 - (d : ℝ) / p) * N) ≤
        2 * (smoothHolderConst d p *
          ((2 : ℝ) ^ (1 - (d : ℝ) / p) * dist x y ^ (1 - (d : ℝ) / p)) * N) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left h_R_rpow_le hC₀_nn
      · exact hN_nn
    have h_simp : 2 * (smoothHolderConst d p *
        ((2 : ℝ) ^ (1 - (d : ℝ) / p) * dist x y ^ (1 - (d : ℝ) / p)) * N) =
        C * dist x y ^ (1 - (d : ℝ) / p) * N := by
      rw [hC_def]; ring
    linarith

theorem smooth_morrey_sup_bound
    {d : ℕ} [NeZero d] {p : ℝ} (hp : (d : ℝ) < p)
    {x₀ : EuclideanSpace ℝ (Fin d)} {R : ℝ} (hR : 0 < R)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Metric.ball x₀ (R / 2), ‖u x‖ ≤ C * (
        (eLpNorm u (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R))).toReal +
        (eLpNorm (fun z => ‖fderiv ℝ u z‖) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ R))).toReal) := by
  classical
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hd_one_le : (1 : ℝ) ≤ d :=
    by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))
  have hp_pos : 0 < p := lt_trans hd_pos hp
  have hp_one : 1 < p := lt_of_le_of_lt hd_one_le hp
  have h_exp_pos : 0 < 1 - (d : ℝ) / p := by
    rw [sub_pos, div_lt_one hp_pos]; exact hp
  have hC₀_nn : 0 ≤ smoothHolderConst d p := smoothHolderConst_nonneg hp
  have hvol_pos : 0 < (volume (Metric.ball x₀ R)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume x₀ hR).ne' measure_ball_lt_top.ne
  set A : ℝ := smoothHolderConst d p * R ^ (1 - (d : ℝ) / p) with hA_def
  set Bcoeff : ℝ := ((volume (Metric.ball x₀ R)).toReal) ^ (-(1 / p)) with hBcoeff_def
  have hA_nn : 0 ≤ A := by
    rw [hA_def]
    exact mul_nonneg hC₀_nn (Real.rpow_nonneg hR.le _)
  have hBcoeff_nn : 0 ≤ Bcoeff := by
    rw [hBcoeff_def]
    exact Real.rpow_nonneg ENNReal.toReal_nonneg _
  set C : ℝ := A + Bcoeff with hC_def
  have hC_nn : 0 ≤ C := by rw [hC_def]; linarith
  refine ⟨C, hC_nn, ?_⟩
  intro x hx
  set N_grad : ℝ := (eLpNorm (fun z => ‖fderiv ℝ u z‖) (ENNReal.ofReal p)
    (volume.restrict (Metric.ball x₀ R))).toReal with hN_grad_def
  set N_u : ℝ := (eLpNorm u (ENNReal.ofReal p)
    (volume.restrict (Metric.ball x₀ R))).toReal with hN_u_def
  have hN_grad_nn : 0 ≤ N_grad := ENNReal.toReal_nonneg
  have hN_u_nn : 0 ≤ N_u := ENNReal.toReal_nonneg
  have hx_R : x ∈ Metric.ball x₀ R := by
    rw [Metric.mem_ball] at hx ⊢
    linarith
  set Mavg : ℝ := ⨍ z in Metric.ball x₀ R, u z ∂volume with hMavg_def
  have h_diff_bound := smooth_pointwise_holder_bound_explicit (d := d) hp hR hu hx_R
  have h_diff_bound' : ‖u x - Mavg‖ ≤ A * N_grad := by
    change ‖u x - ⨍ z in Metric.ball x₀ R, u z ∂volume‖ ≤
        smoothHolderConst d p * R ^ (1 - (d : ℝ) / p) * N_grad
    exact h_diff_bound
  have h_avg_bound := smooth_norm_average_le (x₀ := x₀) hp_one hR hu
  have h_avg_bound' : ‖Mavg‖ ≤ Bcoeff * N_u := by
    change ‖⨍ z in Metric.ball x₀ R, u z ∂volume‖ ≤ Bcoeff * N_u
    rw [show Bcoeff * N_u = N_u * Bcoeff from by ring]
    exact h_avg_bound
  have h_split : ‖u x‖ ≤ ‖u x - Mavg‖ + ‖Mavg‖ := by
    calc ‖u x‖ = ‖(u x - Mavg) + Mavg‖ := by ring_nf
      _ ≤ ‖u x - Mavg‖ + ‖Mavg‖ := norm_add_le _ _
  have h_combined : ‖u x‖ ≤ A * N_grad + Bcoeff * N_u := by linarith
  have h_factor :
      A * N_grad + Bcoeff * N_u ≤ C * (N_u + N_grad) := by
    rw [hC_def]
    have h_expand : (A + Bcoeff) * (N_u + N_grad) =
        A * N_u + A * N_grad + Bcoeff * N_u + Bcoeff * N_grad := by ring
    rw [h_expand]
    have h_ANu_nn : 0 ≤ A * N_u := mul_nonneg hA_nn hN_u_nn
    have h_BNgrad_nn : 0 ≤ Bcoeff * N_grad := mul_nonneg hBcoeff_nn hN_grad_nn
    linarith
  linarith

theorem smooth_morrey_holder_modulus
    {d : ℕ} [NeZero d] {p : ℝ} (hp : (d : ℝ) < p)
    {x₀ : EuclideanSpace ℝ (Fin d)} {R : ℝ} (hR : 0 < R)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {x y : EuclideanSpace ℝ (Fin d)},
        x ∈ Metric.ball x₀ (R / 2) → y ∈ Metric.ball x₀ (R / 2) →
          ‖u x - u y‖ ≤ C * (dist x y) ^ (1 - (d : ℝ) / p) := by
  classical
  obtain ⟨C₀, hC₀_nn, hbound⟩ := smooth_morrey_pair_bound (d := d) hp hR hu
  set N : ℝ := (eLpNorm (fun z => ‖fderiv ℝ u z‖) (ENNReal.ofReal p)
    (volume.restrict (Metric.ball x₀ R))).toReal with hN_def
  have hN_nn : 0 ≤ N := ENNReal.toReal_nonneg
  refine ⟨C₀ * N, mul_nonneg hC₀_nn hN_nn, ?_⟩
  intro x y hx hy
  have h := hbound hx hy
  rw [show C₀ * N * dist x y ^ (1 - (d : ℝ) / p) =
      C₀ * dist x y ^ (1 - (d : ℝ) / p) * N from by ring]
  exact h

theorem smooth_morrey_pair_bound_uniform
    {d : ℕ} [NeZero d] {p : ℝ} (hp : (d : ℝ) < p)
    {x₀ : EuclideanSpace ℝ (Fin d)} {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : EuclideanSpace ℝ (Fin d) → ℝ}, ContDiff ℝ (⊤ : ℕ∞) u →
        ∀ {x y : EuclideanSpace ℝ (Fin d)},
          x ∈ Metric.ball x₀ (R / 2) → y ∈ Metric.ball x₀ (R / 2) →
            ‖u x - u y‖ ≤ C * (dist x y) ^ (1 - (d : ℝ) / p) *
              (eLpNorm (fun z => ‖fderiv ℝ u z‖) (ENNReal.ofReal p)
                (volume.restrict (Metric.ball x₀ R))).toReal := by
  classical
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hd_one_le : (1 : ℝ) ≤ d :=
    by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))
  have hp_pos : 0 < p := lt_trans hd_pos hp
  have hp_one : 1 < p := lt_of_le_of_lt hd_one_le hp
  have h_exp_pos : 0 < 1 - (d : ℝ) / p := by
    rw [sub_pos, div_lt_one hp_pos]; exact hp
  have hC₀_nn : 0 ≤ smoothHolderConst d p := smoothHolderConst_nonneg hp
  set C : ℝ := (2 : ℝ) * (2 : ℝ) ^ (1 - (d : ℝ) / p) * smoothHolderConst d p with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    have h2_pow_nn : 0 ≤ (2 : ℝ) ^ (1 - (d : ℝ) / p) :=
      Real.rpow_nonneg (by norm_num) _
    positivity
  refine ⟨C, hC_nn, ?_⟩
  intro u hu x y hx hy
  set N : ℝ := (eLpNorm (fun z => ‖fderiv ℝ u z‖) (ENNReal.ofReal p)
    (volume.restrict (Metric.ball x₀ R))).toReal with hN_def
  have hN_nn : 0 ≤ N := ENNReal.toReal_nonneg
  by_cases h_small : dist x y < R / 2
  · by_cases h_zero : dist x y = 0
    · have hxy_eq : x = y := dist_eq_zero.mp h_zero
      rw [hxy_eq, sub_self, norm_zero]
      have h_zero_pow : (dist y y) ^ (1 - (d : ℝ) / p) = 0 := by
        rw [dist_self]
        exact Real.zero_rpow h_exp_pos.ne'
      rw [h_zero_pow, mul_zero, zero_mul]
    · have h_dist_pos : 0 < dist x y := lt_of_le_of_ne dist_nonneg (Ne.symm h_zero)
      set m : EuclideanSpace ℝ (Fin d) := (1 / 2 : ℝ) • (x + y) with hm_def
      have h_m_minus_x₀ : m - x₀ = (1 / 2 : ℝ) • (x - x₀) + (1 / 2 : ℝ) • (y - x₀) := by
        rw [hm_def]
        rw [smul_add]
        have hx₀_split : x₀ = (1 / 2 : ℝ) • x₀ + (1 / 2 : ℝ) • x₀ := by
          rw [← add_smul]
          rw [show (1 : ℝ)/2 + 1/2 = 1 from by norm_num, one_smul]
        nth_rewrite 1 [hx₀_split]
        rw [smul_sub, smul_sub]
        abel
      have h_m_dist : dist m x₀ < R / 2 := by
        have hxR2 : dist x x₀ < R / 2 := by rw [Metric.mem_ball] at hx; exact hx
        have hyR2 : dist y x₀ < R / 2 := by rw [Metric.mem_ball] at hy; exact hy
        have h_mid : dist m x₀ ≤
            (1 / 2 : ℝ) * dist x x₀ + (1 / 2 : ℝ) * dist y x₀ := by
          rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, h_m_minus_x₀]
          have hsum : ‖(1 / 2 : ℝ) • (x - x₀) + (1 / 2 : ℝ) • (y - x₀)‖ ≤
              ‖(1 / 2 : ℝ) • (x - x₀)‖ + ‖(1 / 2 : ℝ) • (y - x₀)‖ := norm_add_le _ _
          rw [norm_smul, norm_smul] at hsum
          rw [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hsum
          exact hsum
        have h_bound : (1 / 2 : ℝ) * dist x x₀ + (1 / 2 : ℝ) * dist y x₀ < R / 2 := by
          have h_x_lt : (1 / 2 : ℝ) * dist x x₀ < (1 / 2 : ℝ) * (R / 2) :=
            mul_lt_mul_of_pos_left hxR2 (by norm_num : (0 : ℝ) < 1 / 2)
          have h_y_lt : (1 / 2 : ℝ) * dist y x₀ < (1 / 2 : ℝ) * (R / 2) :=
            mul_lt_mul_of_pos_left hyR2 (by norm_num : (0 : ℝ) < 1 / 2)
          linarith
        linarith
      have h_ball_sub : Metric.ball m (dist x y) ⊆ Metric.ball x₀ R := by
        intro z hz
        rw [Metric.mem_ball] at hz ⊢
        calc dist z x₀ ≤ dist z m + dist m x₀ := dist_triangle z m x₀
          _ < dist x y + R / 2 := add_lt_add hz h_m_dist
          _ < R / 2 + R / 2 := by linarith
          _ = R := by ring
      have h_x_minus_m : x - m = (1 / 2 : ℝ) • (x - y) := by
        rw [hm_def, smul_add]
        have hx_split : x = (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • x := by
          rw [← add_smul]
          rw [show (1 : ℝ)/2 + 1/2 = 1 from by norm_num, one_smul]
        rw [smul_sub]
        nth_rewrite 1 [hx_split]
        abel
      have h_y_minus_m : y - m = (1 / 2 : ℝ) • (y - x) := by
        rw [hm_def, smul_add]
        have hy_split : y = (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • y := by
          rw [← add_smul]
          rw [show (1 : ℝ)/2 + 1/2 = 1 from by norm_num, one_smul]
        rw [smul_sub]
        nth_rewrite 1 [hy_split]
        abel
      have h_dx_m : dist x m = dist x y / 2 := by
        rw [dist_eq_norm, h_x_minus_m, norm_smul]
        rw [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        rw [← dist_eq_norm]; ring
      have h_dy_m : dist y m = dist x y / 2 := by
        rw [dist_eq_norm, h_y_minus_m, norm_smul]
        rw [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        rw [show y - x = -(x - y) from by abel, norm_neg]
        rw [← dist_eq_norm]; ring
      have hx_in : x ∈ Metric.ball m (dist x y) := by
        rw [Metric.mem_ball, h_dx_m]; linarith
      have hy_in : y ∈ Metric.ball m (dist x y) := by
        rw [Metric.mem_ball, h_dy_m]; linarith
      have h_at_x := smooth_pointwise_holder_bound_explicit (d := d) hp h_dist_pos hu hx_in
      have h_at_y := smooth_pointwise_holder_bound_explicit (d := d) hp h_dist_pos hu hy_in
      set N_small : ℝ := (eLpNorm (fun z => ‖fderiv ℝ u z‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball m (dist x y)))).toReal with hN_small_def
      have hN_small_le : N_small ≤ N := by
        rw [hN_small_def, hN_def]
        exact smooth_grad_eLpNorm_le_of_ball_subset hR hu h_ball_sub
      set Mavg : ℝ := ⨍ z in Metric.ball m (dist x y), u z ∂volume with hMavg_def
      have h_at_x' : ‖u x - Mavg‖ ≤
          smoothHolderConst d p * dist x y ^ (1 - (d : ℝ) / p) * N_small := h_at_x
      have h_at_y' : ‖u y - Mavg‖ ≤
          smoothHolderConst d p * dist x y ^ (1 - (d : ℝ) / p) * N_small := h_at_y
      have h_triangle : ‖u x - u y‖ ≤ ‖u x - Mavg‖ + ‖u y - Mavg‖ := by
        calc ‖u x - u y‖ = ‖(u x - Mavg) - (u y - Mavg)‖ := by ring_nf
          _ ≤ ‖u x - Mavg‖ + ‖u y - Mavg‖ := norm_sub_le _ _
      have h_dxy_pow_nn : 0 ≤ dist x y ^ (1 - (d : ℝ) / p) :=
        Real.rpow_nonneg dist_nonneg _
      have h_step1 : ‖u x - u y‖ ≤
          2 * (smoothHolderConst d p * dist x y ^ (1 - (d : ℝ) / p) * N_small) := by
        linarith
      have h_step2 : 2 * (smoothHolderConst d p * dist x y ^ (1 - (d : ℝ) / p) * N_small) ≤
          2 * (smoothHolderConst d p * dist x y ^ (1 - (d : ℝ) / p) * N) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
        apply mul_le_mul_of_nonneg_left hN_small_le
        exact mul_nonneg hC₀_nn h_dxy_pow_nn
      have h_step3 : 2 * (smoothHolderConst d p * dist x y ^ (1 - (d : ℝ) / p) * N) ≤
          C * dist x y ^ (1 - (d : ℝ) / p) * N := by
        rw [hC_def]
        have h_rfl : (2 : ℝ) * (smoothHolderConst d p * dist x y ^ (1 - (d : ℝ) / p) * N) =
            2 * smoothHolderConst d p * dist x y ^ (1 - (d : ℝ) / p) * N := by ring
        rw [h_rfl]
        have h_2_le : (2 : ℝ) * smoothHolderConst d p ≤
            (2 : ℝ) * (2 : ℝ) ^ (1 - (d : ℝ) / p) * smoothHolderConst d p := by
          have h_2pow_ge_one : (1 : ℝ) ≤ (2 : ℝ) ^ (1 - (d : ℝ) / p) :=
            Real.one_le_rpow (by norm_num) h_exp_pos.le
          have : (2 : ℝ) ≤ (2 : ℝ) * (2 : ℝ) ^ (1 - (d : ℝ) / p) := by
            calc (2 : ℝ) = 2 * 1 := by ring
              _ ≤ 2 * (2 : ℝ) ^ (1 - (d : ℝ) / p) :=
                  mul_le_mul_of_nonneg_left h_2pow_ge_one (by norm_num)
          exact mul_le_mul_of_nonneg_right this hC₀_nn
        have h_factor :
            (2 : ℝ) * smoothHolderConst d p * dist x y ^ (1 - (d : ℝ) / p) * N ≤
              (2 : ℝ) * (2 : ℝ) ^ (1 - (d : ℝ) / p) * smoothHolderConst d p *
                dist x y ^ (1 - (d : ℝ) / p) * N := by
          have h_inner :
              (2 : ℝ) * smoothHolderConst d p *
                (dist x y ^ (1 - (d : ℝ) / p) * N) ≤
              (2 : ℝ) * (2 : ℝ) ^ (1 - (d : ℝ) / p) * smoothHolderConst d p *
                (dist x y ^ (1 - (d : ℝ) / p) * N) :=
            mul_le_mul_of_nonneg_right h_2_le (mul_nonneg h_dxy_pow_nn hN_nn)
          linarith
        exact h_factor
      linarith
  · have h_large : R / 2 ≤ dist x y := not_lt.mp h_small
    have hx_R : x ∈ Metric.ball x₀ R := by
      rw [Metric.mem_ball] at hx ⊢; linarith
    have hy_R : y ∈ Metric.ball x₀ R := by
      rw [Metric.mem_ball] at hy ⊢; linarith
    have h_at_x := smooth_pointwise_holder_bound_explicit (d := d) hp hR hu hx_R
    have h_at_y := smooth_pointwise_holder_bound_explicit (d := d) hp hR hu hy_R
    set Mavg : ℝ := ⨍ z in Metric.ball x₀ R, u z ∂volume with hMavg_def
    have h_at_x' : ‖u x - Mavg‖ ≤
        smoothHolderConst d p * R ^ (1 - (d : ℝ) / p) * N := h_at_x
    have h_at_y' : ‖u y - Mavg‖ ≤
        smoothHolderConst d p * R ^ (1 - (d : ℝ) / p) * N := h_at_y
    have h_triangle : ‖u x - u y‖ ≤ ‖u x - Mavg‖ + ‖u y - Mavg‖ := by
      calc ‖u x - u y‖ = ‖(u x - Mavg) - (u y - Mavg)‖ := by ring_nf
        _ ≤ ‖u x - Mavg‖ + ‖u y - Mavg‖ := norm_sub_le _ _
    have h_R_pow_nn : 0 ≤ R ^ (1 - (d : ℝ) / p) := Real.rpow_nonneg hR.le _
    have h_step1 : ‖u x - u y‖ ≤
        2 * (smoothHolderConst d p * R ^ (1 - (d : ℝ) / p) * N) := by linarith
    have h_R_le_2dxy : R ≤ 2 * dist x y := by linarith
    have h_R_rpow_le : R ^ (1 - (d : ℝ) / p) ≤
        (2 : ℝ) ^ (1 - (d : ℝ) / p) * dist x y ^ (1 - (d : ℝ) / p) := by
      have h2dxy_nn : 0 ≤ 2 * dist x y := by linarith
      have h_le_pow : R ^ (1 - (d : ℝ) / p) ≤ (2 * dist x y) ^ (1 - (d : ℝ) / p) :=
        Real.rpow_le_rpow hR.le h_R_le_2dxy h_exp_pos.le
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) dist_nonneg] at h_le_pow
      exact h_le_pow
    have h_step2 : 2 * (smoothHolderConst d p * R ^ (1 - (d : ℝ) / p) * N) ≤
        2 * (smoothHolderConst d p *
          ((2 : ℝ) ^ (1 - (d : ℝ) / p) * dist x y ^ (1 - (d : ℝ) / p)) * N) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left h_R_rpow_le hC₀_nn
      · exact hN_nn
    have h_simp : 2 * (smoothHolderConst d p *
        ((2 : ℝ) ^ (1 - (d : ℝ) / p) * dist x y ^ (1 - (d : ℝ) / p)) * N) =
        C * dist x y ^ (1 - (d : ℝ) / p) * N := by
      rw [hC_def]; ring
    linarith

theorem smooth_morrey_sup_bound_uniform
    {d : ℕ} [NeZero d] {p : ℝ} (hp : (d : ℝ) < p)
    {x₀ : EuclideanSpace ℝ (Fin d)} {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : EuclideanSpace ℝ (Fin d) → ℝ}, ContDiff ℝ (⊤ : ℕ∞) u →
        ∀ x ∈ Metric.ball x₀ (R / 2), ‖u x‖ ≤ C *
          ((eLpNorm u (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R))).toReal +
           (eLpNorm (fun z => ‖fderiv ℝ u z‖) (ENNReal.ofReal p)
             (volume.restrict (Metric.ball x₀ R))).toReal) := by
  classical
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hd_one_le : (1 : ℝ) ≤ d :=
    by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))
  have hp_pos : 0 < p := lt_trans hd_pos hp
  have hp_one : 1 < p := lt_of_le_of_lt hd_one_le hp
  have h_exp_pos : 0 < 1 - (d : ℝ) / p := by
    rw [sub_pos, div_lt_one hp_pos]; exact hp
  have hC₀_nn : 0 ≤ smoothHolderConst d p := smoothHolderConst_nonneg hp
  have hvol_pos : 0 < (volume (Metric.ball x₀ R)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume x₀ hR).ne' measure_ball_lt_top.ne
  set A : ℝ := smoothHolderConst d p * R ^ (1 - (d : ℝ) / p) with hA_def
  set Bcoeff : ℝ := ((volume (Metric.ball x₀ R)).toReal) ^ (-(1 / p)) with hBcoeff_def
  have hA_nn : 0 ≤ A := by
    rw [hA_def]
    exact mul_nonneg hC₀_nn (Real.rpow_nonneg hR.le _)
  have hBcoeff_nn : 0 ≤ Bcoeff := by
    rw [hBcoeff_def]
    exact Real.rpow_nonneg ENNReal.toReal_nonneg _
  set C : ℝ := A + Bcoeff with hC_def
  have hC_nn : 0 ≤ C := by rw [hC_def]; linarith
  refine ⟨C, hC_nn, ?_⟩
  intro u hu x hx
  set N_grad : ℝ := (eLpNorm (fun z => ‖fderiv ℝ u z‖) (ENNReal.ofReal p)
    (volume.restrict (Metric.ball x₀ R))).toReal with hN_grad_def
  set N_u : ℝ := (eLpNorm u (ENNReal.ofReal p)
    (volume.restrict (Metric.ball x₀ R))).toReal with hN_u_def
  have hN_grad_nn : 0 ≤ N_grad := ENNReal.toReal_nonneg
  have hN_u_nn : 0 ≤ N_u := ENNReal.toReal_nonneg
  have hx_R : x ∈ Metric.ball x₀ R := by
    rw [Metric.mem_ball] at hx ⊢; linarith
  set Mavg : ℝ := ⨍ z in Metric.ball x₀ R, u z ∂volume with hMavg_def
  have h_diff_bound := smooth_pointwise_holder_bound_explicit (d := d) hp hR hu hx_R
  have h_diff_bound' : ‖u x - Mavg‖ ≤ A * N_grad := by
    change ‖u x - ⨍ z in Metric.ball x₀ R, u z ∂volume‖ ≤
        smoothHolderConst d p * R ^ (1 - (d : ℝ) / p) * N_grad
    exact h_diff_bound
  have h_avg_bound := smooth_norm_average_le (x₀ := x₀) hp_one hR hu
  have h_avg_bound' : ‖Mavg‖ ≤ Bcoeff * N_u := by
    change ‖⨍ z in Metric.ball x₀ R, u z ∂volume‖ ≤ Bcoeff * N_u
    rw [show Bcoeff * N_u = N_u * Bcoeff from by ring]
    exact h_avg_bound
  have h_split : ‖u x‖ ≤ ‖u x - Mavg‖ + ‖Mavg‖ := by
    calc ‖u x‖ = ‖(u x - Mavg) + Mavg‖ := by ring_nf
      _ ≤ ‖u x - Mavg‖ + ‖Mavg‖ := norm_add_le _ _
  have h_combined : ‖u x‖ ≤ A * N_grad + Bcoeff * N_u := by linarith
  have h_factor :
      A * N_grad + Bcoeff * N_u ≤ C * (N_u + N_grad) := by
    rw [hC_def]
    have h_expand : (A + Bcoeff) * (N_u + N_grad) =
        A * N_u + A * N_grad + Bcoeff * N_u + Bcoeff * N_grad := by ring
    rw [h_expand]
    have h_ANu_nn : 0 ≤ A * N_u := mul_nonneg hA_nn hN_u_nn
    have h_BNgrad_nn : 0 ≤ Bcoeff * N_grad := mul_nonneg hBcoeff_nn hN_grad_nn
    linarith
  linarith

end EuclideanMorrey
end Sobolev
