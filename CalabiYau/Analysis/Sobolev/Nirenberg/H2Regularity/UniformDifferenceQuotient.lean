-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Nirenberg/H2Regularity/UniformDifferenceQuotient.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Nirenberg.MasterInequality.MasterInequalityNonSmooth
public import CalabiYau.Analysis.Sobolev.Nirenberg.TestFunction.WeakRegularity
public import CalabiYau.Analysis.Sobolev.Tools.DifferenceQuotient.WeakDerivativeBound

@[expose] public section

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open Sobolev
open Sobolev.NirenbergCrossBoundsNonSmooth
open scoped ENNReal NNReal Convolution Pointwise BigOperators InnerProductSpace

namespace Sobolev.NirenbergEuclidean

variable {d : ℕ} [NeZero d]

local notation "Eucl" => EuclideanSpace ℝ (Fin d)

private lemma sq_le_finset_sum_sq
    {n : ℕ} {α : Type*} (f : Fin n → α → ℝ) (i : Fin n) (x : α) :
    (f i x)^2 ≤ ∑ l : Fin n, (f l x)^2 :=
  Finset.single_le_sum (f := fun l => (f l x)^2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

private lemma sq_eLpNorm_two_eq_lintegral_enorm_sq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ)
    (hf : AEStronglyMeasurable f μ) :
    (eLpNorm f 2 μ) ^ 2 = ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
  classical
  have h2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2_ne_top : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := μ) h2_ne_zero h2_ne_top hf]
  have h2_toReal : ((2 : ℝ≥0∞)).toReal = 2 := by show ENNReal.toReal 2 = 2; rfl
  rw [h2_toReal]
  have h_inner_eq : ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂μ =
      ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards with x
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
  rw [h_inner_eq]
  rw [← ENNReal.rpow_natCast _ 2]
  rw [← ENNReal.rpow_mul]
  norm_num

private lemma lintegral_ofReal_eq_ofReal_integral
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : α → ℝ} (hg_int : Integrable g μ) (hg_nn : 0 ≤ᵐ[μ] g) :
    ∫⁻ x, ENNReal.ofReal (g x) ∂μ = ENNReal.ofReal (∫ x, g x ∂μ) := by
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg_int hg_nn]

private lemma sq_eLpNorm_two_le_of_integral_sum_sq_le
    {n : ℕ} {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : Fin n → α → ℝ)
    (h_sum_int : Integrable (fun x => ∑ l : Fin n, (f l x) ^ 2) μ)
    (i : Fin n) (hf : AEStronglyMeasurable (f i) μ) {S : ℝ}
    (h_sum_le : ∫ x, ∑ l : Fin n, (f l x) ^ 2 ∂μ ≤ S) :
    (eLpNorm (f i) 2 μ)^ 2 ≤ ENNReal.ofReal S := by
  classical
  have h_sum_nn : 0 ≤ᵐ[μ] (fun x => ∑ l : Fin n, (f l x)^2) := by
    refine Filter.Eventually.of_forall ?_
    intro x
    exact Finset.sum_nonneg (fun l _ => sq_nonneg _)
  have h_pt : ∀ x : α,
      (‖f i x‖ₑ : ℝ≥0∞)^ 2 ≤
        ENNReal.ofReal (∑ l : Fin n, (f l x)^2) := by
    intro x
    have h_lhs_eq :
        (‖f i x‖ₑ : ℝ≥0∞)^ 2 = ENNReal.ofReal ((f i x)^2) := by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2,
        sq_abs]
    rw [h_lhs_eq]
    exact ENNReal.ofReal_le_ofReal (sq_le_finset_sum_sq f i x)
  have h_lint_le :
      ∫⁻ x, (‖f i x‖ₑ : ℝ≥0∞)^ 2 ∂μ ≤
        ∫⁻ x, ENNReal.ofReal (∑ l : Fin n, (f l x)^2) ∂μ := by
    refine lintegral_mono_ae ?_
    filter_upwards with x using h_pt x
  have h_sum_int_eq :
      ∫⁻ x, ENNReal.ofReal (∑ l : Fin n, (f l x)^2) ∂μ =
        ENNReal.ofReal (∫ x, ∑ l : Fin n, (f l x)^2 ∂μ) :=
    lintegral_ofReal_eq_ofReal_integral h_sum_int h_sum_nn
  rw [sq_eLpNorm_two_eq_lintegral_enorm_sq μ (f i) hf]
  refine h_lint_le.trans ?_
  rw [h_sum_int_eq]
  exact ENNReal.ofReal_le_ofReal h_sum_le

private lemma le_sqrt_of_sq_le {x y : ℝ≥0∞} (h : x ^ 2 ≤ y) :
    x ≤ y ^ ((1 : ℝ) / 2) := by
  have h_xpow : x = (x^ 2) ^ ((1 : ℝ) / 2) := by
    rw [← ENNReal.rpow_natCast x 2]
    rw [← ENNReal.rpow_mul]
    norm_num
  conv_lhs => rw [h_xpow]
  exact ENNReal.rpow_le_rpow h (by norm_num)

private lemma sqrt_ofReal_eq_ofReal_sqrt {S : ℝ} (hS : 0 ≤ S) :
    (ENNReal.ofReal S) ^ ((1 : ℝ) / 2) = ENNReal.ofReal (Real.sqrt S) := by
  rw [show S = Real.sqrt S * Real.sqrt S from (Real.mul_self_sqrt hS).symm]
  rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  rw [show (ENNReal.ofReal (Real.sqrt S)) * (ENNReal.ofReal (Real.sqrt S)) =
    (ENNReal.ofReal (Real.sqrt S))^ 2 from by ring]
  rw [← ENNReal.rpow_natCast _ 2]
  rw [← ENNReal.rpow_mul]
  norm_num

private lemma eLpNorm_two_le_ofReal_sqrt
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    {S : ℝ} (hS : 0 ≤ S)
    (h_sq : (eLpNorm f 2 μ) ^ 2 ≤ ENNReal.ofReal S) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal (Real.sqrt S) := by
  have h_pow := le_sqrt_of_sq_le h_sq
  rw [sqrt_ofReal_eq_ofReal_sqrt hS] at h_pow
  exact h_pow

theorem uniform_diffQuot_bound_quantitative
    (B : SmoothEllipticBilinearForm
      d (Set.univ : Set Eucl))
    {u_g f_g : Eucl → ℝ}
    (hu_g_l2 : MemLp u_g 2 (volume : Measure Eucl))
    (hf_g_l2_local : ∀ {Ω' : Set Eucl}, IsCompact (closure Ω') →
      MemLp f_g 2 ((volume : Measure Eucl).restrict Ω'))
    {g_g : Fin d → Eucl → ℝ}
    (hg_g_l2 : ∀ i, MemLp (g_g i) 2 (volume : Measure Eucl))
    {η : Eucl → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_support : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (hN : 0 ≤ N) (h_fderiv_eta : ∀ x : Eucl, ‖fderiv ℝ η x‖ ≤ N)
    {Ω' Ω'' : Set Eucl} (hΩ' : IsOpen Ω')
    (hΩ'_compact : IsCompact (closure Ω'))
    {R₀ : ℝ}
    (hh_support_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (hη_one_on_Ω'' : ∀ x ∈ Ω'', η x = 1)
    (hΩ''_meas : MeasurableSet Ω'')
    (h_diffQuot_u_bound :
      ∀ (k : Fin d),
      ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
        ∫ x in tsupport η,
            (Sobolev.diffQuot k h u_g x)^2
          ∂(volume : Measure Eucl) ≤
          ∫ x in Ω', ∑ l : Fin d, ((g_g l) x) ^ 2
            ∂(volume : Measure Eucl))
    (h_testFunction_sq_bound :
      ∀ (k : Fin d),
      ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
        ∫ x, (Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u_g x)^2 ∂(volume : Measure Eucl) ≤
          8 * N^2 *
            ∫ x in tsupport η,
                (Sobolev.diffQuot k h u_g x)^2
              ∂(volume : Measure Eucl) +
          2 * ∫ x, (η x)^2 *
              (Sobolev.diffQuot k h (g_g k) x)^2
            ∂(volume : Measure Eucl))
    (h_coercivity :
      ∀ (k : Fin d),
      ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      B.lam * ∫ x, (η x)^2 *
          ∑ l : Fin d,
            Sobolev.diffQuot k h (g_g l) x ^ 2
        ∂(volume : Measure Eucl) ≤
        |∑ i : Fin d,
          ∑ j : Fin d, ∫ x,
              2 * Sobolev.translate k h
                (fun y : Eucl => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              Sobolev.diffQuot k h (g_g i) x *
              Sobolev.diffQuot k h u_g x
            ∂(volume : Measure Eucl)| +
        |∑ i : Fin d,
          ∑ j : Fin d, ∫ x,
              Sobolev.diffQuot k h
                (fun y : Eucl => B.a y i j) x * (η x)^2 *
              ((g_g i) x) *
              Sobolev.diffQuot k h (g_g j) x
            ∂(volume : Measure Eucl)| +
        |∑ i : Fin d,
          ∑ j : Fin d, ∫ x,
              2 * Sobolev.diffQuot k h
                (fun y : Eucl => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              ((g_g i) x) *
              Sobolev.diffQuot k h u_g x
            ∂(volume : Measure Eucl)| +
        |∫ x in (Set.univ : Set Eucl), f_g x *
            Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u_g x| +
        |∫ x in (Set.univ : Set Eucl), B.c x * u_g x *
            Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u_g x ∂(volume : Measure Eucl)|) :
    ∀ ⦃i k : Fin d⦄ ⦃h : ℝ⦄,
      0 < |h| → |h| ≤ R₀ →
        eLpNorm
          (Sobolev.diffQuot
            (d := d) k h (g_g i)) 2
          ((volume : Measure Eucl).restrict Ω'')
        ≤ ENNReal.ofReal (Real.sqrt ((2 / B.lam) *
            nirenbergMasterYoungConstant B N hΩ'_compact k *
            (∫ x in Ω', ∑ l : Fin d, ((g_g l) x) ^ 2
                ∂(volume : Measure Eucl) +
              ∫ x in Ω', (u_g x)^2 ∂(volume : Measure Eucl) +
              ∫ x in Ω', (f_g x)^2 ∂(volume : Measure Eucl)))) := by
  classical
  intro i k h hh hh_le
  have habs_pos : 0 < |h| := hh
  have hh_ne : h ≠ 0 := abs_ne_zero.mp (ne_of_gt habs_pos)
  have hk_spec :
      (B.lam / 2) * ∫ x in Ω'',
          ∑ l : Fin d,
            Sobolev.diffQuot k h (g_g l) x ^ 2
        ∂(volume : Measure Eucl) ≤
        nirenbergMasterYoungConstant B N hΩ'_compact k *
          (∫ x in Ω', ∑ l : Fin d, ((g_g l) x) ^ 2
                  ∂(volume : Measure Eucl) +
              ∫ x in Ω', (u_g x)^2 ∂(volume : Measure Eucl) +
              ∫ x in Ω', (f_g x)^2 ∂(volume : Measure Eucl)) :=
    nirenberg_diffQuot_g_localL2_bound_quantitative (d := d)
      B hu_g_l2 hf_g_l2_local hg_g_l2
      hη hη_support hη_range hN h_fderiv_eta hΩ' (Set.subset_univ _) hΩ'_compact
      hh_support_in_Ω' hη_one_on_Ω'' hΩ''_meas k
      (h_diffQuot_u_bound k)
      (h_testFunction_sq_bound k)
      (h_coercivity k) hh_ne hh_le
  set G_total : ℝ :=
    (∫ x in Ω', ∑ l : Fin d, ((g_g l) x) ^ 2
      ∂(volume : Measure Eucl) +
      ∫ x in Ω', (u_g x)^2 ∂(volume : Measure Eucl) +
      ∫ x in Ω', (f_g x)^2 ∂(volume : Measure Eucl)) with hG_total_def
  have hG_total_nn : 0 ≤ G_total := by
    rw [hG_total_def]
    refine add_nonneg (add_nonneg ?_ ?_) ?_
    · refine integral_nonneg ?_
      intro x
      exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    · refine integral_nonneg ?_
      intro x; exact sq_nonneg _
    · refine integral_nonneg ?_
      intro x; exact sq_nonneg _
  have ellipticity_pos : 0 < B.lam := B.ellipticity_pos
  have hlam_half_pos : 0 < B.lam / 2 := by linarith
  have hC_nn : 0 ≤ nirenbergMasterYoungConstant B N hΩ'_compact k :=
    nirenbergMasterYoungConstant_nonneg B hN hΩ'_compact k
  set sumInt : ℝ :=
    ∫ x in Ω'',
      ∑ l : Fin d,
        Sobolev.diffQuot k h (g_g l) x ^ 2
      ∂(volume : Measure Eucl) with hsumInt_def
  set S : ℝ :=
    (2 / B.lam) * nirenbergMasterYoungConstant B N hΩ'_compact k * G_total
    with hS_def
  have hS_nn : 0 ≤ S := by
    rw [hS_def]
    refine mul_nonneg (mul_nonneg ?_ hC_nn) hG_total_nn
    have : (0 : ℝ) ≤ 2 := by norm_num
    exact div_nonneg this ellipticity_pos.le
  have h_sumInt_le_S : sumInt ≤ S := by
    have h_factor : (2 / B.lam) > 0 := by positivity
    have h_step2 : sumInt = (2 / B.lam) * ((B.lam / 2) * sumInt) := by
      rw [← mul_assoc]
      rw [show (2 / B.lam) * (B.lam / 2) = 1 from by field_simp]
      rw [one_mul]
    rw [h_step2, hS_def]
    have h_rhs_eq :
        (2 / B.lam) * nirenbergMasterYoungConstant B N hΩ'_compact k * G_total =
          (2 / B.lam) *
            (nirenbergMasterYoungConstant B N hΩ'_compact k * G_total) := by
      ring
    rw [h_rhs_eq]
    exact mul_le_mul_of_nonneg_left hk_spec h_factor.le
  have h_per_l_int :
      ∀ l : Fin d,
        Integrable
          (fun x => (Sobolev.diffQuot
            (d := d) k h (g_g l) x)^2)
          ((volume : Measure Eucl).restrict Ω'') := by
    intro l
    have h_dq_l2_global :
        MemLp
          (Sobolev.diffQuot
            (d := d) k h (g_g l)) 2
          (volume : Measure Eucl) :=
      memLp_diffQuot_two (d := d) k h (hg_g_l2 l)
    have h_dq_l2_restrict :
        MemLp
          (Sobolev.diffQuot
            (d := d) k h (g_g l)) 2
          ((volume : Measure Eucl).restrict Ω'') :=
      h_dq_l2_global.restrict _
    exact h_dq_l2_restrict.integrable_sq
  have h_sum_int :
      Integrable
        (fun x => ∑ l : Fin d,
          (Sobolev.diffQuot
            (d := d) k h (g_g l) x)^2)
        ((volume : Measure Eucl).restrict Ω'') := by
    have h_aux := integrable_finsetSum
      (Finset.univ : Finset (Fin d))
      (fun l _ => h_per_l_int l)
    have h_eq :
        (fun x : Eucl => ∑ l : Fin d,
          (Sobolev.diffQuot
            (d := d) k h (g_g l) x)^2) =
        (fun x : Eucl => ∑ l ∈ (Finset.univ : Finset (Fin d)),
          (fun y => (Sobolev.diffQuot
            (d := d) k h (g_g l) y)^2) x) := by
      funext x; rfl
    rw [h_eq]; exact h_aux
  have h_per_i_sq :
      (eLpNorm (Sobolev.diffQuot
        (d := d) k h (g_g i)) 2
        ((volume : Measure Eucl).restrict Ω''))^ 2 ≤
        ENNReal.ofReal S := by
    refine sq_eLpNorm_two_le_of_integral_sum_sq_le
      (n := d)
      (μ := (volume : Measure Eucl).restrict Ω'')
      (fun l => Sobolev.diffQuot
        (d := d) k h (g_g l)) h_sum_int i
      ((memLp_diffQuot_two (d := d) k h (hg_g_l2 i)).restrict Ω'').aestronglyMeasurable ?_
    exact h_sumInt_le_S
  exact eLpNorm_two_le_ofReal_sqrt hS_nn h_per_i_sq

end Sobolev.NirenbergEuclidean
