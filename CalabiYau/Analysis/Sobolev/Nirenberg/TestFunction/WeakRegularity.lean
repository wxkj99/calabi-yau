-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Nirenberg/TestFunction/WeakRegularity.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Nirenberg.TestFunction.Basic
public import CalabiYau.Analysis.Sobolev.Nirenberg.TestFunction.CutoffDiffQuot

@[expose] public section

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open Sobolev
open scoped ENNReal NNReal Convolution Pointwise BigOperators

namespace Sobolev.NirenbergTestFunction

variable {d : ℕ}

local notation "EuclN" => EuclideanSpace ℝ (Fin d)

private lemma eLpNorm_const_mul
    (c : ℝ) (f : EuclN → ℝ) :
    eLpNorm (fun x => c * f x) 2 (volume : Measure EuclN) =
      ENNReal.ofReal |c| * eLpNorm f 2 (volume : Measure EuclN) := by
  have h_eq : (fun x => c * f x) = c • f := by
    funext x; rw [Pi.smul_apply, smul_eq_mul]
  rw [h_eq]
  rw [eLpNorm_const_smul c f]
  simp [Real.enorm_eq_ofReal_abs]

private lemma eLpNorm_translate_eq (k : Fin d) (h : ℝ) (F : EuclN → ℝ) :
    eLpNorm (translate k h F) 2 (volume : Measure EuclN) =
      eLpNorm F 2 (volume : Measure EuclN) := by
  set τ : EuclN ≃ₜ EuclN :=
    Homeomorph.addRight (h • EuclideanSpace.single k 1) with hτ_def
  have hMP : MeasurePreserving τ volume volume := by
    rw [show (τ : EuclN → EuclN) = fun x => x + h • EuclideanSpace.single k 1
      from rfl]
    exact measurePreserving_add_right volume _
  have hτ_emb : MeasurableEmbedding τ := τ.measurableEmbedding
  have h_eq : translate k h F = F ∘ (τ : EuclN → EuclN) := rfl
  rw [h_eq]
  rw [show eLpNorm F 2 (volume : Measure EuclN) =
      eLpNorm F 2 (Measure.map τ volume) from by rw [hMP.map_eq]]
  exact (hτ_emb.eLpNorm_map_measure (g := F) (p := 2)).symm

private lemma eLpNorm_diffQuot_neg_le
    (k : Fin d) {h : ℝ} (hh : h ≠ 0) {F : EuclN → ℝ}
    (hF_aesm : AEStronglyMeasurable F (volume : Measure EuclN)) :
    eLpNorm (diffQuot k (-h) F) 2 (volume : Measure EuclN) ≤
      (2 / ENNReal.ofReal |h|) * eLpNorm F 2 (volume : Measure EuclN) := by
  have hnh : (-h) ≠ 0 := neg_ne_zero.mpr hh
  have h_dq_eq : diffQuot k (-h) F =
      fun x => (-h)⁻¹ * (translate k (-h) F x - F x) := by
    funext x
    rw [diffQuot_apply_of_ne (d := d) k hnh F x]
    change (F (x + (-h) • EuclideanSpace.single k 1) - F x) / (-h) =
      (-h)⁻¹ * (F (x + (-h) • EuclideanSpace.single k 1) - F x)
    field_simp
  rw [h_dq_eq]
  have h_eq2 : (fun x => (-h)⁻¹ * (translate k (-h) F x - F x)) =
      fun x => (-h)⁻¹ * ((translate k (-h) F - F) x) := by
    funext x; simp [Pi.sub_apply]
  rw [h_eq2, eLpNorm_const_mul (-h)⁻¹ (translate k (-h) F - F)]
  have hτF_aesm : AEStronglyMeasurable (translate k (-h) F)
      (volume : Measure EuclN) := by
    have hMP : MeasurePreserving
        (fun x : EuclN => x + (-h) • EuclideanSpace.single k 1)
        volume volume :=
      measurePreserving_add_right volume _
    exact hF_aesm.comp_measurePreserving hMP
  have h_minkowski : eLpNorm (translate k (-h) F - F) 2
      (volume : Measure EuclN) ≤
        eLpNorm (translate k (-h) F) 2 (volume : Measure EuclN) +
          eLpNorm F 2 (volume : Measure EuclN) :=
    eLpNorm_sub_le hτF_aesm hF_aesm (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h_τF_eq : eLpNorm (translate k (-h) F) 2 (volume : Measure EuclN) =
      eLpNorm F 2 (volume : Measure EuclN) :=
    eLpNorm_translate_eq (d := d) k (-h) F
  rw [h_τF_eq] at h_minkowski
  have h_step : eLpNorm (translate k (-h) F - F) 2 (volume : Measure EuclN) ≤
      2 * eLpNorm F 2 (volume : Measure EuclN) := by
    rw [two_mul]; exact h_minkowski
  have h_inv_abs : |(-h)⁻¹| = |h|⁻¹ := by
    rw [abs_inv, abs_neg]
  have habs_h_pos : 0 < |h| := abs_pos.mpr hh
  have h_ofReal_inv :
      ENNReal.ofReal |(-h)⁻¹| = (ENNReal.ofReal |h|)⁻¹ := by
    rw [h_inv_abs]
    exact ENNReal.ofReal_inv_of_pos habs_h_pos
  rw [h_ofReal_inv]
  calc (ENNReal.ofReal |h|)⁻¹ *
        eLpNorm (translate k (-h) F - F) 2 (volume : Measure EuclN)
      ≤ (ENNReal.ofReal |h|)⁻¹ * (2 * eLpNorm F 2 (volume : Measure EuclN)) := by
        gcongr
    _ = 2 / ENNReal.ofReal |h| * eLpNorm F 2 (volume : Measure EuclN) := by
        rw [← mul_assoc]
        congr 1
        rw [ENNReal.div_eq_inv_mul]

private lemma eLpNorm_eta_sq_diffQuot_le
    (k : Fin d) (h : ℝ) {η u : EuclN → ℝ}
    {M_η : ℝ} (_hM_η_nn : 0 ≤ M_η) (hM_η : ∀ x, |η x| ≤ M_η) :
    eLpNorm (fun y => (η y)^2 * diffQuot k h u y) 2
        (volume : Measure EuclN) ≤
      ENNReal.ofReal (M_η^2) *
        eLpNorm (diffQuot k h u) 2 (volume : Measure EuclN) := by
  classical
  have h2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2_ne_top : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  have h2_toReal : ((2 : ℝ≥0∞)).toReal = 2 := by show ENNReal.toReal 2 = 2; rfl
  have h_pow_eq : ∀ a : ℝ≥0∞, a ^ (2 : ℝ) = a ^ (2 : ℕ) := by
    intro a
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
  have h_pt : ∀ y : EuclN,
      (‖(η y)^2 * diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ) ≤
        ENNReal.ofReal (M_η^4) * (‖diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ) := by
    intro y
    have h_real : ((η y)^2 * diffQuot k h u y)^2 ≤
        M_η^4 * (diffQuot k h u y)^2 := by
      have h_eta_sq_le : (η y)^2 ≤ M_η^2 := by
        have hY := hM_η y
        have h_abs_sq : (η y)^2 = |η y|^2 := by rw [sq_abs]
        rw [h_abs_sq]
        exact pow_le_pow_left₀ (abs_nonneg _) hY 2
      have h_eta_sq_sq_le : ((η y)^2)^2 ≤ (M_η^2)^2 := by
        have h_sq_nn : 0 ≤ (η y)^2 := sq_nonneg _
        exact pow_le_pow_left₀ h_sq_nn h_eta_sq_le 2
      have h_dq_sq_nn : 0 ≤ (diffQuot k h u y)^2 := sq_nonneg _
      have h_step : ((η y)^2 * diffQuot k h u y)^2 =
          ((η y)^2)^2 * (diffQuot k h u y)^2 := by ring
      have hM4 : (M_η^2)^2 = M_η^4 := by ring
      calc ((η y)^2 * diffQuot k h u y)^2
          = ((η y)^2)^2 * (diffQuot k h u y)^2 := h_step
        _ ≤ (M_η^2)^2 * (diffQuot k h u y)^2 :=
            mul_le_mul_of_nonneg_right h_eta_sq_sq_le h_dq_sq_nn
        _ = M_η^4 * (diffQuot k h u y)^2 := by rw [hM4]
    have h_lhs_eq :
        (‖(η y)^2 * diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ) =
          ENNReal.ofReal (((η y)^2 * diffQuot k h u y)^2) := by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2,
        sq_abs]
    have h_rhs_eq :
        (‖diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ) =
          ENNReal.ofReal ((diffQuot k h u y)^2) := by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2,
        sq_abs]
    rw [h_lhs_eq, h_rhs_eq]
    have hM4_nn : 0 ≤ M_η^4 := by positivity
    rw [show ENNReal.ofReal (M_η^4) *
        ENNReal.ofReal ((diffQuot k h u y)^2) =
      ENNReal.ofReal (M_η^4 * (diffQuot k h u y)^2) from
      (ENNReal.ofReal_mul hM4_nn).symm]
    exact ENNReal.ofReal_le_ofReal h_real
  have h_lint_le :
      ∫⁻ y : EuclN, (‖(η y)^2 * diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ)
          ∂(volume : Measure EuclN) ≤
        ENNReal.ofReal (M_η^4) *
          ∫⁻ y : EuclN, (‖diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ)
          ∂(volume : Measure EuclN) := by
    calc ∫⁻ y : EuclN, (‖(η y)^2 * diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ)
        ≤ ∫⁻ y : EuclN, ENNReal.ofReal (M_η^4) *
            (‖diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ) := by
          refine lintegral_mono_ae ?_
          filter_upwards with y using h_pt y
      _ = ENNReal.ofReal (M_η^4) *
            ∫⁻ y : EuclN, (‖diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ) := by
          rw [lintegral_const_mul']
          exact ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h2_ne_zero h2_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal h2_ne_zero h2_ne_top]
  rw [h2_toReal]
  have h_lhs_pow_eq :
      (∫⁻ y : EuclN, (‖(η y)^2 * diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℝ)
          ∂(volume : Measure EuclN)) =
        ∫⁻ y : EuclN, (‖(η y)^2 * diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ)
          ∂(volume : Measure EuclN) := by
    refine lintegral_congr_ae ?_
    filter_upwards with y using h_pow_eq _
  have h_rhs_pow_eq :
      (∫⁻ y : EuclN, (‖diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℝ)
          ∂(volume : Measure EuclN)) =
        ∫⁻ y : EuclN, (‖diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ)
          ∂(volume : Measure EuclN) := by
    refine lintegral_congr_ae ?_
    filter_upwards with y using h_pow_eq _
  rw [h_lhs_pow_eq, h_rhs_pow_eq]
  refine le_trans (ENNReal.rpow_le_rpow h_lint_le (by norm_num : (0 : ℝ) ≤ 1/2)) ?_
  have h_pull :
      (ENNReal.ofReal (M_η^4) *
          ∫⁻ y : EuclN, (‖diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ)) ^ ((1 : ℝ) / 2) =
        (ENNReal.ofReal (M_η^4))^((1 : ℝ) / 2) *
          (∫⁻ y : EuclN, (‖diffQuot k h u y‖ₑ : ℝ≥0∞)^(2 : ℕ))^((1 : ℝ) / 2) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1/2)]
  rw [h_pull]
  have h_sqrt_M4 :
      (ENNReal.ofReal (M_η^4))^((1 : ℝ) / 2) = ENNReal.ofReal (M_η^2) := by
    have hM2_nn : 0 ≤ M_η^2 := sq_nonneg _
    have h_M4_to_pow :
        ENNReal.ofReal (M_η^4) = (ENNReal.ofReal (M_η^2))^(2 : ℕ) := by
      rw [show M_η^4 = (M_η^2)^(2 : ℕ) from by ring,
        ENNReal.ofReal_pow hM2_nn 2]
    rw [h_M4_to_pow]
    rw [← ENNReal.rpow_natCast (ENNReal.ofReal (M_η^2)) 2,
      ← ENNReal.rpow_mul]
    have h_calc : ((2 : ℕ) : ℝ) * (1 / 2) = 1 := by norm_num
    rw [h_calc, ENNReal.rpow_one]
  rw [h_sqrt_M4]

theorem eLpNorm_nirenbergTestFunction_le
    (k : Fin d) {h : ℝ} (hh : h ≠ 0)
    {η u : EuclN → ℝ}
    (hη_cont : Continuous η)
    (hu_aesm : AEStronglyMeasurable u (volume : Measure EuclN))
    {M_η : ℝ} (hM_η_nn : 0 ≤ M_η) (hM_η : ∀ x, |η x| ≤ M_η) :
    eLpNorm (nirenbergTestFunction k h η u) 2 (volume : Measure EuclN) ≤
      (2 / ENNReal.ofReal |h|) * ENNReal.ofReal (M_η^2) *
        eLpNorm (diffQuot k h u) 2 (volume : Measure EuclN) := by
  set F : EuclN → ℝ := fun y => (η y)^2 * diffQuot k h u y with hF_def
  have hF_aesm : AEStronglyMeasurable F (volume : Measure EuclN) := by
    rw [hF_def]
    have h1 : AEStronglyMeasurable (fun y : EuclN => (η y)^2)
        (volume : Measure EuclN) :=
      (hη_cont.pow 2).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (diffQuot k h u) (volume : Measure EuclN) :=
      aestronglyMeasurable_diffQuot (d := d) k h hu_aesm
    exact h1.mul h2
  have h_step_A : eLpNorm (diffQuot k (-h) F) 2 (volume : Measure EuclN) ≤
      (2 / ENNReal.ofReal |h|) * eLpNorm F 2 (volume : Measure EuclN) :=
    eLpNorm_diffQuot_neg_le (d := d) k hh hF_aesm
  have h_step_B : eLpNorm F 2 (volume : Measure EuclN) ≤
      ENNReal.ofReal (M_η^2) *
        eLpNorm (diffQuot k h u) 2 (volume : Measure EuclN) := by
    rw [hF_def]
    exact eLpNorm_eta_sq_diffQuot_le (d := d) k h hM_η_nn hM_η
  have h_lhs_unfold : nirenbergTestFunction k h η u = diffQuot k (-h) F := rfl
  rw [h_lhs_unfold]
  calc eLpNorm (diffQuot k (-h) F) 2 (volume : Measure EuclN)
      ≤ (2 / ENNReal.ofReal |h|) * eLpNorm F 2 (volume : Measure EuclN) := h_step_A
    _ ≤ (2 / ENNReal.ofReal |h|) *
          (ENNReal.ofReal (M_η^2) *
            eLpNorm (diffQuot k h u) 2 (volume : Measure EuclN)) := by
          gcongr
    _ = (2 / ENNReal.ofReal |h|) * ENNReal.ofReal (M_η^2) *
          eLpNorm (diffQuot k h u) 2 (volume : Measure EuclN) := by
        rw [mul_assoc]

end Sobolev.NirenbergTestFunction
