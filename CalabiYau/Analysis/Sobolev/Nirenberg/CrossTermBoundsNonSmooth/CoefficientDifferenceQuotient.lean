-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Nirenberg/CrossTermBoundsNonSmooth/CoefficientDifferenceQuotient.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Nirenberg.MasterInequality.CrossBounds
public import CalabiYau.Analysis.Sobolev.Nirenberg.CrossTermBoundsNonSmooth.CrossBoundsNonSmooth
public import CalabiYau.Analysis.Sobolev.Nirenberg.TestFunction.TranslatedCutoffDiffQuot

@[expose] public section

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open Sobolev
open Sobolev.NirenbergEuclidean
open Sobolev.NirenbergCrossBounds
open scoped ENNReal NNReal Convolution Pointwise BigOperators InnerProductSpace

namespace Sobolev.NirenbergCrossBoundsNonSmooth

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem cross_2_pointwise_bound_nonsmooth
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (g : Fin d → E → ℝ)
    {η : E → ℝ} (_hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    (i j k : Fin d)
    {Ω' : Set E} {M : ℝ} (hM_nn : 0 ≤ M)
    (h_M : ∀ i j : Fin d, ∀ x ∈ closure Ω',
      |(fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single k 1)| ≤ M)
    {h : ℝ}
    (hh_support_in_Ω' : Metric.cthickening |h| (tsupport η) ⊆ Ω')
    {ε : ℝ} (hε : 0 < ε) (x : E) :
    |diffQuot k h (fun y => B.a y i j) x * (η x)^2 *
        ((g i) x) *
        diffQuot k h (g j) x| ≤
      ε * (η x)^2 *
        (diffQuot k h (g j) x)^2 +
      (M^2 / (4 * ε)) * (η x)^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        ((g i) x)^2 := by
  classical
  by_cases hx : x ∈ tsupport η
  · have h_dq_a_bound : |diffQuot k h (fun y => B.a y i j) x| ≤ M :=
      abs_diffQuot_a_le_of_bound_on_set (d := d)
        (B.contDiff_a i j |>.of_le (by norm_cast)) k h
        (h_M i j) ((singleton_cthick_subset (d := d) η hh_support_in_Ω' (le_refl _) hx).trans
          subset_closure)
    have h_η_in : η x ∈ Set.Icc (0 : ℝ) 1 := hη_range ⟨x, rfl⟩
    have h_η_nn : 0 ≤ η x := h_η_in.1
    have h_η_le : η x ≤ 1 := h_η_in.2
    have h_η_sq_nn : 0 ≤ (η x)^2 := sq_nonneg _
    set A : ℝ := η x * diffQuot k h (g j) x with hA_def
    set B' : ℝ := M * η x * (g i) x with hB'_def
    have h2ε_pos : 0 < 2 * ε := by linarith
    have h_young := Sobolev.NirenbergCrossBounds.two_abs_mul_le_eps_sq_add A B' (2 * ε) h2ε_pos
    have h_AB_abs : |A * B'| ≤ ε * A^2 + (1/(4*ε)) * B'^2 := by
      have h1 : |A * B'| = |A| * |B'| := abs_mul A B'
      have h_double : 2 * (ε * A^2 + (1/(4*ε)) * B'^2) =
          2 * ε * A^2 + (1/(2*ε)) * B'^2 := by
        field_simp
        ring
      have h_ε_ne : ε ≠ 0 := ne_of_gt hε
      linarith [h_young, h_double]
    have h_lhs_bound :
        |diffQuot k h (fun y => B.a y i j) x * (η x)^2 *
            ((g i) x) *
            diffQuot k h (g j) x| ≤
          |A * B'| := by
      have h_lhs_abs_eq : |diffQuot k h (fun y => B.a y i j) x * (η x)^2 *
            ((g i) x) *
            diffQuot k h (g j) x| =
          |diffQuot k h (fun y => B.a y i j) x| * (η x)^2 *
            |(g i) x| *
            |diffQuot k h (g j) x| := by
        rw [abs_mul, abs_mul, abs_mul]
        rw [show |(η x)^2| = (η x)^2 from abs_of_nonneg h_η_sq_nn]
      have h_AB_abs_eq : |A * B'| =
          M * (η x)^2 * |(g i) x| *
          |diffQuot k h (g j) x| := by
        change |(η x * _) * (M * η x * _)| = _
        rw [show η x * diffQuot k h (g j) x *
            (M * η x * (g i) x) =
          M * (η x)^2 * (g i) x *
            diffQuot k h (g j) x from by
              rw [sq]; ring]
        rw [abs_mul, abs_mul, abs_mul]
        rw [abs_of_nonneg hM_nn, abs_of_nonneg h_η_sq_nn]
      rw [h_lhs_abs_eq, h_AB_abs_eq]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      exact mul_le_mul_of_nonneg_right h_dq_a_bound h_η_sq_nn
    refine h_lhs_bound.trans ?_
    refine h_AB_abs.trans ?_
    have h_indicator : Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x = 1 := by
      rw [Set.indicator_of_mem hx]
    rw [h_indicator]
    have hA_sq : A^2 = (η x)^2 *
        (diffQuot k h (g j) x)^2 := by
      change (η x * _)^2 = _; ring
    have hB'_sq_le : B'^2 ≤ M^2 * (η x)^2 *
        ((g i) x)^2 := by
      change (M * η x * _)^2 ≤ _; nlinarith
    have h_4ε_pos : 0 < 4 * ε := by linarith
    have h_4ε_ne : (4 * ε) ≠ 0 := ne_of_gt h_4ε_pos
    have h_inv_4ε_nn : 0 ≤ 1 / (4 * ε) :=
      one_div_nonneg.mpr (by linarith)
    have h_step :
        (1/(4*ε)) * B'^2 ≤ (1/(4*ε)) * (M^2 * (η x)^2 *
          ((g i) x)^2) :=
      mul_le_mul_of_nonneg_left hB'_sq_le h_inv_4ε_nn
    calc ε * A^2 + (1/(4*ε)) * B'^2
        ≤ ε * A^2 + (1/(4*ε)) *
            (M^2 * (η x)^2 *
              ((g i) x)^2) := by linarith
      _ = ε * (η x)^2 *
              (diffQuot k h (g j) x)^2 +
          (M^2 / (4 * ε)) * (η x)^2 * 1 *
            ((g i) x)^2 := by
            rw [hA_sq]
            have h_div_eq : 1 / (4 * ε) * (M^2 * (η x)^2 *
                ((g i) x)^2) =
                M^2 / (4 * ε) * (η x)^2 * 1 *
                  ((g i) x)^2 := by
              field_simp
            linarith [h_div_eq]
  · have h_η_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx
    have h_indicator : Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x = 0 :=
      Set.indicator_of_notMem hx _
    rw [h_indicator]
    have h_lhs_zero : diffQuot k h (fun y => B.a y i j) x * (η x)^2 *
        ((g i) x) *
        diffQuot k h (g j) x = 0 := by
      rw [h_η_zero]; ring
    rw [h_lhs_zero, abs_zero]
    have h_t1_nn : 0 ≤ ε * (η x)^2 *
        (diffQuot k h (g j) x)^2 := by
      apply mul_nonneg
      · apply mul_nonneg hε.le (sq_nonneg _)
      · exact sq_nonneg _
    have h_t2_zero : (M^2 / (4 * ε)) * (η x)^2 * 0 *
        ((g i) x)^2 = 0 := by ring
    linarith

private lemma exists_bound_cross_2_coefficient
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (i j k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : E,
      |diffQuot k h (fun y => B.a y i j) x * (η x)^2| ≤ M := by
  classical
  have h_dq_a : Continuous (Sobolev.diffQuot k h
      (fun y : E => B.a y i j)) :=
    continuous_diffQuot_smooth (d := d) (B.contDiff_a i j) k hh
  have hη_sq_cont : Continuous (fun x : E => (η x)^2) := hη.continuous.pow 2
  have hη_sq_support : HasCompactSupport (fun y : E => η y ^ 2) := by
    have heq : (fun y : E => η y ^ 2) = (fun y : E => η y * η y) := by
      funext y; ring
    rw [heq]; exact hη_support.mul_right
  have h_prod_cont : Continuous
      (fun x : E => Sobolev.diffQuot k h
          (fun y : E => B.a y i j) x * (η x)^2) :=
    h_dq_a.mul hη_sq_cont
  have h_prod_support : HasCompactSupport
      (fun x : E => Sobolev.diffQuot k h
          (fun y : E => B.a y i j) x * (η x)^2) :=
    hη_sq_support.mul_left
  exact exists_bound_of_continuous_compactSupport h_prod_cont h_prod_support

private lemma integrable_cross_2_summand_nonsmooth
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {g : Fin d → E → ℝ}
    (hg_l2 : ∀ i, MemLp (g i) 2 (volume : Measure E))
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (i j k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    Integrable (fun x : E =>
      diffQuot k h (fun y => B.a y i j) x * (η x)^2 *
        ((g i) x) *
        diffQuot k h (g j) x) volume := by
  classical
  have h_dq_a : Continuous (Sobolev.diffQuot k h
      (fun y : E => B.a y i j)) :=
    continuous_diffQuot_smooth (d := d) (B.contDiff_a i j) k hh
  have hη_sq_cont : Continuous (fun x : E => (η x)^2) := hη.continuous.pow 2
  have hη_sq_support : HasCompactSupport (fun y : E => η y ^ 2) := by
    have heq : (fun y : E => η y ^ 2) = (fun y : E => η y * η y) := by
      funext y; ring
    rw [heq]; exact hη_support.mul_right
  set f₂ : E → ℝ := fun x =>
    Sobolev.diffQuot k h
      (fun y : E => B.a y i j) x * (η x)^2 with hf₂_def
  have hf₂_cont : Continuous f₂ := h_dq_a.mul hη_sq_cont
  have hf₂_support : HasCompactSupport f₂ := hη_sq_support.mul_left
  obtain ⟨M, hM_nn, hM⟩ :=
    exists_bound_of_continuous_compactSupport hf₂_cont hf₂_support
  have h_dq_g_l2 : MemLp (diffQuot k h (g j)) 2 (volume : Measure E) :=
    memLp_diffQuot_two k h (hg_l2 j)
  have hf₂_gi_l2 : MemLp (fun x => f₂ x * (g i) x) 2
      (volume : Measure E) :=
    memLp_bounded_mul hf₂_cont.aestronglyMeasurable hM (hg_l2 i)
  have h_target_eq :
      (fun x : E =>
        Sobolev.diffQuot k h
          (fun y : E => B.a y i j) x * (η x)^2 *
          ((g i) x) *
          Sobolev.diffQuot k h (g j) x) =
      (fun x => f₂ x * (g i) x) *
        (Sobolev.diffQuot k h (g j)) := by
    funext x
    change Sobolev.diffQuot k h
        (fun y : E => B.a y i j) x * (η x)^2 *
        ((g i) x) *
        Sobolev.diffQuot k h (g j) x =
      (f₂ x * (g i) x) *
        Sobolev.diffQuot k h (g j) x
    simp only [hf₂_def]
  rw [h_target_eq]
  exact MemLp.integrable_mul (p := 2) (q := 2) hf₂_gi_l2 h_dq_g_l2

omit [NeZero d] in
private lemma integrable_const_eta_sq_indicator_g_sq
    {g : Fin d → E → ℝ}
    (hg_l2 : ∀ i, MemLp (g i) 2 (volume : Measure E))
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (i : Fin d) (c : ℝ) :
    Integrable (fun x : E => c * (η x)^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        ((g i) x)^2)
      (volume : Measure E) := by
  classical
  have hη_sq_cont : Continuous (fun x : E => η x ^ 2) := hη.continuous.pow 2
  have hη_sq_support : HasCompactSupport (fun x : E => η x ^ 2) := by
    have heq : (fun y : E => η y ^ 2) = (fun y : E => η y * η y) := by
      funext y; ring
    rw [heq]; exact hη_support.mul_right
  obtain ⟨M, hM_nn, hM⟩ :=
    exists_bound_of_continuous_compactSupport hη_sq_cont hη_sq_support
  have h_g_sq_int : Integrable (fun x : E => ((g i) x)^2)
      (volume : Measure E) := by
    have h_g_norm_sq_int : Integrable
        (fun x : E => ‖(g i) x‖ ^ (2 : ℕ)) (volume : Measure E) := by
      have hh := (hg_l2 i).integrable_norm_rpow
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      have h_pow_eq : (2 : ℝ≥0∞).toReal = 2 := by
        show ENNReal.toReal 2 = 2; rfl
      rw [h_pow_eq] at hh
      have heq : (fun x : E => ‖(g i) x‖ ^ (2 : ℝ)) =
          (fun x : E => ‖(g i) x‖ ^ (2 : ℕ)) := by
        funext x
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_cast,
          Real.rpow_natCast]
      rw [heq] at hh
      exact hh
    have heq2 : (fun x : E => ((g i) x)^2) =
        (fun x : E => ‖(g i) x‖ ^ (2 : ℕ)) := by
      funext x
      rw [Real.norm_eq_abs, sq_abs]
    rw [heq2]
    exact h_g_norm_sq_int
  have h_tsupp_meas : MeasurableSet (tsupport η) :=
    isClosed_tsupport η |>.measurableSet
  have h_aesm : AEStronglyMeasurable
      (fun x : E => c * (η x)^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        ((g i) x)^2) (volume : Measure E) := by
    have h1 : AEStronglyMeasurable (fun x : E => c * (η x)^2)
        (volume : Measure E) :=
      (continuous_const.mul hη_sq_cont).aestronglyMeasurable
    have h_ind_aesm :
        AEStronglyMeasurable (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)))
          (volume : Measure E) := by
      refine (aestronglyMeasurable_indicator_iff h_tsupp_meas).mpr ?_
      exact aestronglyMeasurable_const
    have h_g_aesm : AEStronglyMeasurable (g i) (volume : Measure E) :=
      (hg_l2 i).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun x : E => ((g i) x)^2)
        (volume : Measure E) := h_g_aesm.pow 2
    exact (h1.mul h_ind_aesm).mul h2
  have h_const_mul_int : Integrable
      (fun x : E => |c| * M * ((g i) x)^2)
      (volume : Measure E) := h_g_sq_int.const_mul (|c| * M)
  refine h_const_mul_int.mono' h_aesm ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  have h_eta_sq_nn : 0 ≤ (η x)^2 := sq_nonneg _
  have h_g_sq_nn : 0 ≤ ((g i) x)^2 := sq_nonneg _
  have h_eta_sq_le : (η x)^2 ≤ M := by
    have hM_apply := hM x
    rw [abs_of_nonneg h_eta_sq_nn] at hM_apply
    exact hM_apply
  rw [Real.norm_eq_abs]
  by_cases hx : x ∈ tsupport η
  · rw [Set.indicator_of_mem hx, mul_one]
    have h_LHS_eq : |c * (η x)^2 * ((g i) x)^2| =
        |c| * (η x)^2 * ((g i) x)^2 := by
      rw [show c * (η x)^2 * ((g i) x)^2 =
        c * ((η x)^2 * ((g i) x)^2) from by ring]
      rw [abs_mul, abs_mul]
      rw [abs_of_nonneg h_eta_sq_nn, abs_of_nonneg h_g_sq_nn]
      ring
    rw [h_LHS_eq]
    have h_ic_nn : 0 ≤ |c| := abs_nonneg _
    have h_ic_eta_sq : |c| * (η x)^2 ≤ |c| * M :=
      mul_le_mul_of_nonneg_left h_eta_sq_le h_ic_nn
    exact mul_le_mul_of_nonneg_right h_ic_eta_sq h_g_sq_nn
  · rw [Set.indicator_of_notMem hx, mul_zero, zero_mul, abs_zero]
    refine mul_nonneg (mul_nonneg (abs_nonneg _) hM_nn) h_g_sq_nn

omit [NeZero d] in
private lemma integrable_const_eta_sq_diffQuot_g_sq_cross2
    {g : Fin d → E → ℝ}
    (hg_l2 : ∀ i, MemLp (g i) 2 (volume : Measure E))
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (j k : Fin d) (h : ℝ) (c : ℝ) :
    Integrable (fun x : E => c * (η x)^2 *
      (diffQuot k h (g j) x)^2)
      (volume : Measure E) := by
  classical
  have hη_sq_cont : Continuous (fun x : E => η x ^ 2) := hη.continuous.pow 2
  have hη_sq_support : HasCompactSupport (fun x : E => η x ^ 2) := by
    have heq : (fun y : E => η y ^ 2) = (fun y : E => η y * η y) := by
      funext y; ring
    rw [heq]; exact hη_support.mul_right
  obtain ⟨M, hM_nn, hM⟩ :=
    exists_bound_of_continuous_compactSupport hη_sq_cont hη_sq_support
  have h_dq_g_l2 : MemLp (diffQuot k h (g j)) 2 (volume : Measure E) :=
    memLp_diffQuot_two k h (hg_l2 j)
  have h_dq_g_sq_int : Integrable (fun x : E => (diffQuot k h (g j) x)^2)
      (volume : Measure E) := by
    have h_dq_norm_sq_int : Integrable
        (fun x : E => ‖diffQuot k h (g j) x‖ ^ (2 : ℕ)) (volume : Measure E) := by
      have hh := h_dq_g_l2.integrable_norm_rpow
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      have h_pow_eq : (2 : ℝ≥0∞).toReal = 2 := by
        show ENNReal.toReal 2 = 2; rfl
      rw [h_pow_eq] at hh
      have heq : (fun x : E => ‖diffQuot k h (g j) x‖ ^ (2 : ℝ)) =
          (fun x : E => ‖diffQuot k h (g j) x‖ ^ (2 : ℕ)) := by
        funext x
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_cast,
          Real.rpow_natCast]
      rw [heq] at hh
      exact hh
    have heq2 : (fun x : E => (diffQuot k h (g j) x)^2) =
        (fun x : E => ‖diffQuot k h (g j) x‖ ^ (2 : ℕ)) := by
      funext x
      rw [Real.norm_eq_abs, sq_abs]
    rw [heq2]
    exact h_dq_norm_sq_int
  have h_aesm : AEStronglyMeasurable
      (fun x : E => c * (η x)^2 * (diffQuot k h (g j) x)^2)
      (volume : Measure E) := by
    have h1 : AEStronglyMeasurable (fun x : E => c * (η x)^2)
        (volume : Measure E) :=
      (continuous_const.mul hη_sq_cont).aestronglyMeasurable
    have h_dq_aesm : AEStronglyMeasurable (diffQuot k h (g j))
        (volume : Measure E) :=
      aestronglyMeasurable_diffQuot (d := d) k h (hg_l2 j).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun x : E => (diffQuot k h (g j) x)^2)
        (volume : Measure E) := h_dq_aesm.pow 2
    exact h1.mul h2
  have h_const_mul_int : Integrable
      (fun x : E => |c| * M * (diffQuot k h (g j) x)^2)
      (volume : Measure E) := h_dq_g_sq_int.const_mul (|c| * M)
  refine h_const_mul_int.mono' h_aesm ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  have h_eta_sq_nn : 0 ≤ (η x)^2 := sq_nonneg _
  have h_dq_sq_nn : 0 ≤ (diffQuot k h (g j) x)^2 := sq_nonneg _
  have h_eta_sq_le : (η x)^2 ≤ M := by
    have hM_apply := hM x
    rw [abs_of_nonneg h_eta_sq_nn] at hM_apply
    exact hM_apply
  rw [Real.norm_eq_abs]
  have h_LHS_eq : |c * (η x)^2 * (diffQuot k h (g j) x)^2| =
      |c| * (η x)^2 * (diffQuot k h (g j) x)^2 := by
    rw [show c * (η x)^2 * (diffQuot k h (g j) x)^2 =
      c * ((η x)^2 * (diffQuot k h (g j) x)^2) from by ring]
    rw [abs_mul, abs_mul]
    rw [abs_of_nonneg h_eta_sq_nn, abs_of_nonneg h_dq_sq_nn]
    ring
  rw [h_LHS_eq]
  have h_ic_nn : 0 ≤ |c| := abs_nonneg _
  have h_ic_eta_sq : |c| * (η x)^2 ≤ |c| * M :=
    mul_le_mul_of_nonneg_left h_eta_sq_le h_ic_nn
  exact mul_le_mul_of_nonneg_right h_ic_eta_sq h_dq_sq_nn

omit [NeZero d] in
private lemma integrable_eta_sq_diffQuot_g_sq_cross2
    {g : Fin d → E → ℝ}
    (hg_l2 : ∀ i, MemLp (g i) 2 (volume : Measure E))
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (j k : Fin d) (h : ℝ) :
    Integrable (fun x : E => (η x)^2 *
      (diffQuot k h (g j) x)^2)
      (volume : Measure E) := by
  have hint := integrable_const_eta_sq_diffQuot_g_sq_cross2 (d := d)
    hg_l2 hη hη_support j k h 1
  have h_eq : (fun x : E => (η x)^2 * (diffQuot k h (g j) x)^2) =
      fun x : E => 1 * (η x)^2 * (diffQuot k h (g j) x)^2 := by
    funext x; ring
  rw [h_eq]
  exact hint

theorem coefficient_difference_quotient_mixed_term_bound_nonsmooth_quantitative
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {g : Fin d → E → ℝ}
    (hg_l2 : ∀ i, MemLp (g i) 2 (volume : Measure E))
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {Ω' : Set E} (hΩ' : IsOpen Ω')
    (hΩ'_compact : IsCompact (closure Ω'))
    {R₀ : ℝ}
    (hh_support_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (k : Fin d) (ε : ℝ) (hε : 0 < ε) :
  ∀ ⦃h : ℝ⦄, h ≠ 0 → |h| ≤ R₀ →
    |- ∑ i : Fin d, ∑ j : Fin d, ∫ x,
          (Sobolev.diffQuot k h
            (fun y : E => B.a y i j)) x *
          (η x)^2 *
          ((g i) x) *
          Sobolev.diffQuot k h (g j) x
        ∂(volume : Measure E)| ≤
      ε * ∫ x, (η x)^2 *
          ∑ j : Fin d,
            Sobolev.diffQuot k h (g j) x ^ 2
        ∂(volume : Measure E) +
      (((Classical.choose
            (SmoothEllipticBilinearForm.bounded_fderiv_a_on_compact
              (d := d) B k hΩ'_compact))^2
          / (4 * (ε / (Fintype.card (Fin d) : ℝ))))
          * (Fintype.card (Fin d) : ℝ)^2) * ∫ x in Ω',
          ∑ i : Fin d, ((g i) x) ^ 2
        ∂(volume : Measure E) := by
  classical
  set M : ℝ := Classical.choose
    (SmoothEllipticBilinearForm.bounded_fderiv_a_on_compact (d := d) B k hΩ'_compact)
    with hM_eq
  have hM_nn : 0 ≤ M :=
    (Classical.choose_spec
      (SmoothEllipticBilinearForm.bounded_fderiv_a_on_compact
        (d := d) B k hΩ'_compact)).1
  have h_M : ∀ i j : Fin d, ∀ x ∈ closure Ω',
      |(fderiv ℝ (fun x : E => B.a x i j) x) (EuclideanSpace.single k 1)| ≤ M :=
    (Classical.choose_spec
      (SmoothEllipticBilinearForm.bounded_fderiv_a_on_compact
        (d := d) B k hΩ'_compact)).2
  set d_real : ℝ := (Fintype.card (Fin d) : ℝ) with hd_real
  have hd_pos : 0 < d_real := by
    rw [hd_real]; exact_mod_cast Fintype.card_pos
  have hd_nn : 0 ≤ d_real := hd_pos.le
  have hε'_pos : 0 < ε / d_real := div_pos hε hd_pos
  set C : ℝ := (M^2 / (4 * (ε / d_real))) * d_real^2 with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    refine mul_nonneg ?_ (sq_nonneg _)
    refine mul_nonneg (sq_nonneg _) ?_
    refine inv_nonneg.mpr (by linarith [hε'_pos])
  intro h hh hh_le
  have h_thick_in_Ω' : Metric.cthickening |h| (tsupport η) ⊆ Ω' := hh_support_in_Ω' hh_le
  have h_each_pointwise := fun (i j : Fin d) (x : E) =>
    cross_2_pointwise_bound_nonsmooth (d := d) B g hη hη_range i j k hM_nn h_M
      h_thick_in_Ω' hε'_pos x
  set S : ℝ := ∑ i : Fin d, ∑ j : Fin d, ∫ x,
        diffQuot k h (fun y : E => B.a y i j) x * (η x)^2 *
        ((g i) x) *
        diffQuot k h (g j) x
      ∂(volume : Measure E) with hS_def
  rw [abs_neg]
  have h_abs_sum : |S| ≤
      ∑ i : Fin d, ∑ j : Fin d, |∫ x,
          diffQuot k h (fun y : E => B.a y i j) x * (η x)^2 *
          ((g i) x) *
          diffQuot k h (g j) x
        ∂(volume : Measure E)| :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _))
  refine h_abs_sum.trans ?_
  have h_integrand_int : ∀ i j : Fin d, Integrable (fun x : E =>
      diffQuot k h (fun y => B.a y i j) x * (η x)^2 *
        ((g i) x) *
        diffQuot k h (g j) x) volume :=
    fun i j => integrable_cross_2_summand_nonsmooth (d := d) B hg_l2 hη hη_support
      i j k hh
  have h_first_int : ∀ j : Fin d, Integrable (fun x : E =>
      (ε / d_real) * (η x)^2 *
        (diffQuot k h (g j) x)^2) volume :=
    fun j => integrable_const_eta_sq_diffQuot_g_sq_cross2 (d := d) hg_l2 hη hη_support
      j k h (ε / d_real)
  have h_second_int : ∀ i : Fin d, Integrable (fun x : E =>
      (M^2 / (4 * (ε / d_real))) * (η x)^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        ((g i) x)^2) volume :=
    fun i => integrable_const_eta_sq_indicator_g_sq (d := d) hg_l2 hη hη_support i
      (M^2 / (4 * (ε / d_real)))
  have h_pt_bound_int : ∀ i j : Fin d, Integrable (fun x : E =>
      (ε / d_real) * (η x)^2 *
        (diffQuot k h (g j) x)^2 +
      (M^2 / (4 * (ε / d_real))) * (η x)^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        ((g i) x)^2) volume :=
    fun i j => (h_first_int j).add (h_second_int i)
  have h_per_pair_bound : ∀ i j : Fin d,
      |∫ x, diffQuot k h (fun y => B.a y i j) x * (η x)^2 *
          ((g i) x) *
          diffQuot k h (g j) x ∂(volume : Measure E)| ≤
      ∫ x, ((ε / d_real) * (η x)^2 *
          (diffQuot k h (g j) x)^2 +
        (M^2 / (4 * (ε / d_real))) * (η x)^2 *
          (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
          ((g i) x)^2) ∂(volume : Measure E) := by
    intro i j
    have h_tri := abs_integral_le_integral_abs (μ := (volume : Measure E))
      (f := fun x : E => diffQuot k h (fun y => B.a y i j) x * (η x)^2 *
          ((g i) x) *
          diffQuot k h (g j) x)
    refine h_tri.trans ?_
    refine integral_mono_ae ((h_integrand_int i j).abs) (h_pt_bound_int i j) ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    exact h_each_pointwise i j x
  have h_outer_sum :
      ∑ i : Fin d, ∑ j : Fin d, |∫ x,
          diffQuot k h (fun y => B.a y i j) x * (η x)^2 *
          ((g i) x) *
          diffQuot k h (g j) x ∂(volume : Measure E)| ≤
      ∑ i : Fin d, ∑ j : Fin d,
        ∫ x, ((ε / d_real) * (η x)^2 *
            (diffQuot k h (g j) x)^2 +
          (M^2 / (4 * (ε / d_real))) * (η x)^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((g i) x)^2) ∂(volume : Measure E) :=
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum
      (fun j _ => h_per_pair_bound i j))
  refine h_outer_sum.trans ?_
  have h_total_eq :
      ∑ i : Fin d, ∑ j : Fin d,
        ∫ x, ((ε / d_real) * (η x)^2 *
            (diffQuot k h (g j) x)^2 +
          (M^2 / (4 * (ε / d_real))) * (η x)^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((g i) x)^2) ∂(volume : Measure E) =
      ε * ∫ x, (η x)^2 *
          ∑ j : Fin d, (diffQuot k h (g j) x)^2
        ∂(volume : Measure E) +
      d_real * ((M^2 / (4 * (ε / d_real))) *
        ∫ x, (η x)^2 *
            ∑ i : Fin d, (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((g i) x)^2
          ∂(volume : Measure E)) := by
    have h_per_ij : ∀ i j : Fin d,
        ∫ x, ((ε / d_real) * (η x)^2 *
            (diffQuot k h (g j) x)^2 +
          (M^2 / (4 * (ε / d_real))) * (η x)^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((g i) x)^2) ∂(volume : Measure E) =
        ∫ x, (ε / d_real) * (η x)^2 *
            (diffQuot k h (g j) x)^2 ∂(volume : Measure E) +
        ∫ x, (M^2 / (4 * (ε / d_real))) * (η x)^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((g i) x)^2 ∂(volume : Measure E) := by
      intro i j
      rw [integral_add (h_first_int j) (h_second_int i)]
    rw [show (∑ i : Fin d, ∑ j : Fin d,
          ∫ x, ((ε / d_real) * (η x)^2 *
              (diffQuot k h (g j) x)^2 +
            (M^2 / (4 * (ε / d_real))) * (η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((g i) x)^2) ∂(volume : Measure E)) =
        ∑ i : Fin d, ∑ j : Fin d,
          (∫ x, (ε / d_real) * (η x)^2 *
              (diffQuot k h (g j) x)^2 ∂(volume : Measure E) +
          ∫ x, (M^2 / (4 * (ε / d_real))) * (η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((g i) x)^2 ∂(volume : Measure E)) from
          Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
            (fun j _ => h_per_ij i j))]
    have h_inner_step : ∀ i : Fin d, ∑ j : Fin d,
          (∫ x, (ε / d_real) * (η x)^2 *
              (diffQuot k h (g j) x)^2 ∂(volume : Measure E) +
          ∫ x, (M^2 / (4 * (ε / d_real))) * (η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((g i) x)^2 ∂(volume : Measure E)) =
        (∑ j : Fin d, ∫ x, (ε / d_real) * (η x)^2 *
              (diffQuot k h (g j) x)^2 ∂(volume : Measure E)) +
        d_real * ∫ x, (M^2 / (4 * (ε / d_real))) * (η x)^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((g i) x)^2 ∂(volume : Measure E) := by
      intro i
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [show (∑ i : Fin d, ∑ j : Fin d,
            (∫ x, (ε / d_real) * (η x)^2 *
                (diffQuot k h (g j) x)^2 ∂(volume : Measure E) +
            ∫ x, (M^2 / (4 * (ε / d_real))) * (η x)^2 *
                (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
                ((g i) x)^2 ∂(volume : Measure E))) =
        ∑ i : Fin d,
          ((∑ j : Fin d, ∫ x, (ε / d_real) * (η x)^2 *
                (diffQuot k h (g j) x)^2 ∂(volume : Measure E)) +
          d_real * ∫ x, (M^2 / (4 * (ε / d_real))) * (η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((g i) x)^2 ∂(volume : Measure E)) from
        Finset.sum_congr rfl (fun i _ => h_inner_step i)]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h_first_eq : d_real * (∑ j : Fin d, ∫ x, (ε / d_real) * (η x)^2 *
              (diffQuot k h (g j) x)^2 ∂(volume : Measure E)) =
        ε * ∫ x, (η x)^2 *
            ∑ j : Fin d, (diffQuot k h (g j) x)^2
          ∂(volume : Measure E) := by
      have h_pull_const : ∀ j : Fin d,
          ∫ x, (ε / d_real) * (η x)^2 *
              (diffQuot k h (g j) x)^2 ∂(volume : Measure E) =
          (ε / d_real) * ∫ x, (η x)^2 *
              (diffQuot k h (g j) x)^2 ∂(volume : Measure E) := by
        intro j
        rw [show (fun x : E => (ε / d_real) * (η x)^2 *
              (diffQuot k h (g j) x)^2) =
            fun x : E => (ε / d_real) * ((η x)^2 *
              (diffQuot k h (g j) x)^2) from
            by funext x; ring]
        rw [integral_const_mul]
      rw [show (∑ j : Fin d, ∫ x, (ε / d_real) * (η x)^2 *
              (diffQuot k h (g j) x)^2 ∂(volume : Measure E)) =
          ∑ j : Fin d, (ε / d_real) * ∫ x, (η x)^2 *
              (diffQuot k h (g j) x)^2 ∂(volume : Measure E) from
          Finset.sum_congr rfl (fun j _ => h_pull_const j)]
      rw [← Finset.mul_sum]
      have h_eta_sq_diffQuot_int : ∀ j : Fin d, Integrable (fun x : E =>
          (η x)^2 * (diffQuot k h (g j) x)^2) volume :=
        fun j => integrable_eta_sq_diffQuot_g_sq_cross2 (d := d) hg_l2 hη hη_support j k h
      rw [show (∑ j : Fin d, ∫ x, (η x)^2 *
              (diffQuot k h (g j) x)^2 ∂(volume : Measure E)) =
          ∫ x, ∑ j : Fin d, ((η x)^2 *
              (diffQuot k h (g j) x)^2) ∂(volume : Measure E)
          from (integral_finsetSum _ (fun j _ => h_eta_sq_diffQuot_int j)).symm]
      have h_swap : (fun x : E => ∑ j : Fin d, ((η x)^2 *
              (diffQuot k h (g j) x)^2)) =
          fun x : E => (η x)^2 *
              ∑ j : Fin d, (diffQuot k h (g j) x)^2 := by
        funext x; rw [Finset.mul_sum]
      rw [h_swap, ← mul_assoc, mul_div_cancel₀ _ (ne_of_gt hd_pos)]
    rw [h_first_eq]
    have h_second_eq :
        (∑ i : Fin d, d_real * ∫ x, (M^2 / (4 * (ε / d_real))) * (η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((g i) x)^2 ∂(volume : Measure E)) =
        d_real * (∑ i : Fin d, ∫ x, (M^2 / (4 * (ε / d_real))) * (η x)^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((g i) x)^2 ∂(volume : Measure E)) :=
      (Finset.mul_sum _ _ _).symm
    rw [h_second_eq]
    have h_pull_const_2 : ∀ i : Fin d, ∫ x, (M^2 / (4 * (ε / d_real))) * (η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((g i) x)^2 ∂(volume : Measure E) =
        (M^2 / (4 * (ε / d_real))) * ∫ x, (η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((g i) x)^2 ∂(volume : Measure E) := by
      intro i
      rw [show (fun x : E => (M^2 / (4 * (ε / d_real))) * (η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((g i) x)^2) =
          fun x : E => (M^2 / (4 * (ε / d_real))) * ((η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((g i) x)^2) from by funext x; ring]
      rw [integral_const_mul]
    rw [show (∑ i : Fin d, ∫ x, (M^2 / (4 * (ε / d_real))) * (η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((g i) x)^2 ∂(volume : Measure E)) =
        ∑ i : Fin d, (M^2 / (4 * (ε / d_real))) * ∫ x, (η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((g i) x)^2 ∂(volume : Measure E) from
        Finset.sum_congr rfl (fun i _ => h_pull_const_2 i)]
    rw [← Finset.mul_sum]
    have h_inner_int : ∀ i : Fin d, Integrable (fun x : E =>
        (η x)^2 * (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        ((g i) x)^2) volume := by
      intro i
      have h := integrable_const_eta_sq_indicator_g_sq (d := d) hg_l2 hη hη_support i 1
      have h_eq : (fun x : E => (1 : ℝ) * (η x)^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((g i) x)^2) =
          (fun x : E => (η x)^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((g i) x)^2) := by
        funext x; ring
      rw [h_eq] at h; exact h
    rw [show (∑ i : Fin d, ∫ x, (η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((g i) x)^2 ∂(volume : Measure E)) =
        ∫ x, ∑ i : Fin d, ((η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((g i) x)^2) ∂(volume : Measure E) from
        (integral_finsetSum _ (fun i _ => h_inner_int i)).symm]
    have h_swap : (fun x : E => ∑ i : Fin d, ((η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((g i) x)^2)) =
        fun x : E => (η x)^2 *
            ∑ i : Fin d, ((Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((g i) x)^2) := by
      funext x; rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _; ring
    rw [h_swap]
  rw [h_total_eq]
  have h_M_factor_nn : 0 ≤ M^2 / (4 * (ε / d_real)) := by
    refine div_nonneg (sq_nonneg _) (by linarith)
  have h_d_real_ge_one : 1 ≤ d_real := by
    rw [hd_real]
    have hd_natpos : 0 < Fintype.card (Fin d) := Fintype.card_pos
    exact_mod_cast hd_natpos
  have h_ind_bound :
      ∫ x, (η x)^2 *
        ∑ i : Fin d, (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
          ((g i) x)^2 ∂(volume : Measure E) ≤
      ∫ x in Ω', ∑ i : Fin d, ((g i) x)^2
        ∂(volume : Measure E) := by
    have h_pointwise : ∀ x : E,
        (η x)^2 * ∑ i : Fin d, (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
          ((g i) x)^2 ≤
        (Set.indicator Ω' (fun y : E => ∑ i : Fin d,
          ((g i) y)^2)) x := by
      intro x
      by_cases hx : x ∈ tsupport η
      · have hx_Ω' : x ∈ Ω' :=
          h_thick_in_Ω' (self_subset_cthickening _ hx)
        rw [Set.indicator_of_mem hx_Ω']
        have h_η_in : η x ∈ Set.Icc (0 : ℝ) 1 := hη_range ⟨x, rfl⟩
        have h_η_sq_le : (η x)^2 ≤ 1 := by
          have h_η_le : η x ≤ 1 := h_η_in.2
          have h_η_nn : 0 ≤ η x := h_η_in.1
          calc (η x)^2 ≤ (1 : ℝ)^2 := by
                  refine pow_le_pow_left₀ h_η_nn h_η_le 2
            _ = 1 := one_pow _
        have h_η_sq_nn : 0 ≤ (η x)^2 := sq_nonneg _
        have h_indicator_le_one : ∀ y : E,
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) y) ≤ 1 := by
          intro y
          by_cases hy : y ∈ tsupport η
          · rw [Set.indicator_of_mem hy]
          · rw [Set.indicator_of_notMem hy]; norm_num
        have h_sum_le : ∑ i : Fin d, (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((g i) x)^2 ≤
            ∑ i : Fin d, ((g i) x)^2 := by
          refine Finset.sum_le_sum ?_
          intro i _
          have h_le := h_indicator_le_one x
          have h_sq_nn : 0 ≤ ((g i) x)^2 := sq_nonneg _
          have h_step : (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
                ((g i) x)^2 ≤
              1 * ((g i) x)^2 :=
            mul_le_mul_of_nonneg_right h_le h_sq_nn
          linarith
        have h_sum_nn : 0 ≤ ∑ i : Fin d,
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((g i) x)^2 := by
          refine Finset.sum_nonneg ?_
          intro i _
          have h_ind_nn : 0 ≤ Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x := by
            by_cases hxx : x ∈ tsupport η
            · rw [Set.indicator_of_mem hxx]; norm_num
            · rw [Set.indicator_of_notMem hxx]
          exact mul_nonneg h_ind_nn (sq_nonneg _)
        calc (η x)^2 * (∑ i : Fin d,
                (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
                  ((g i) x)^2) ≤
            1 * (∑ i : Fin d,
                (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
                  ((g i) x)^2) :=
              mul_le_mul_of_nonneg_right h_η_sq_le h_sum_nn
          _ = ∑ i : Fin d,
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
                ((g i) x)^2 := by ring
          _ ≤ ∑ i : Fin d, ((g i) x)^2 := h_sum_le
      · have h_η_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx
        rw [h_η_zero]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, ge_iff_le]
        by_cases hx_Ω' : x ∈ Ω'
        · rw [Set.indicator_of_mem hx_Ω']
          exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
        · rw [Set.indicator_of_notMem hx_Ω']
    have h_lhs_int : Integrable (fun x : E =>
        (η x)^2 * ∑ i : Fin d, (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
          ((g i) x)^2) volume := by
      have h_each_int : ∀ i : Fin d, Integrable (fun x : E =>
          (η x)^2 * ((Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((g i) x)^2)) volume := by
        intro i
        have h := integrable_const_eta_sq_indicator_g_sq (d := d) hg_l2 hη hη_support i 1
        have h_eq : (fun x : E => (1 : ℝ) * (η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((g i) x)^2) =
            (fun x : E => (η x)^2 *
              ((Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((g i) x)^2)) := by
          funext x; ring
        rw [h_eq] at h; exact h
      have h_sum_int : Integrable (fun x : E => ∑ i : Fin d, (η x)^2 *
            ((Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((g i) x)^2)) volume :=
        integrable_finsetSum (Finset.univ : Finset (Fin d)) (fun i _ => h_each_int i)
      have h_eq : (fun x : E => ∑ i : Fin d, (η x)^2 *
            ((Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((g i) x)^2)) =
          (fun x : E => (η x)^2 * ∑ i : Fin d,
            ((Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((g i) x)^2)) := by
        funext x; rw [Finset.mul_sum]
      rw [h_eq] at h_sum_int; exact h_sum_int
    have h_g_sq_int : ∀ i : Fin d, Integrable (fun x : E => ((g i) x)^2)
        (volume : Measure E) := by
      intro i
      have h_g_norm_sq_int : Integrable
          (fun x : E => ‖(g i) x‖ ^ (2 : ℕ)) (volume : Measure E) := by
        have hh' := (hg_l2 i).integrable_norm_rpow
          (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
        have h_pow_eq : (2 : ℝ≥0∞).toReal = 2 := by
          show ENNReal.toReal 2 = 2; rfl
        rw [h_pow_eq] at hh'
        have heq : (fun x : E => ‖(g i) x‖ ^ (2 : ℝ)) =
            (fun x : E => ‖(g i) x‖ ^ (2 : ℕ)) := by
          funext x
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_cast,
            Real.rpow_natCast]
        rw [heq] at hh'
        exact hh'
      have heq2 : (fun x : E => ((g i) x)^2) =
          (fun x : E => ‖(g i) x‖ ^ (2 : ℕ)) := by
        funext x
        rw [Real.norm_eq_abs, sq_abs]
      rw [heq2]
      exact h_g_norm_sq_int
    have h_sum_g_sq_int : Integrable (fun x : E =>
        ∑ i : Fin d, ((g i) x)^2) (volume : Measure E) :=
      integrable_finsetSum (Finset.univ : Finset (Fin d))
        (fun i _ => h_g_sq_int i)
    have h_sum_g_sq_intOn : IntegrableOn (fun x : E =>
        ∑ i : Fin d, ((g i) x)^2) Ω' (volume : Measure E) :=
      h_sum_g_sq_int.integrableOn
    have h_rhs_int : Integrable (fun y : E =>
        Set.indicator Ω' (fun z : E => ∑ i : Fin d,
          ((g i) z)^2) y) volume :=
      h_sum_g_sq_intOn.integrable_indicator hΩ'.measurableSet
    have h_int_le := integral_mono h_lhs_int h_rhs_int h_pointwise
    refine h_int_le.trans ?_
    rw [show (fun y : E => Set.indicator Ω' (fun z : E => ∑ i : Fin d,
            ((g i) z)^2) y) =
        Set.indicator Ω' (fun z : E => ∑ i : Fin d,
          ((g i) z)^2) from rfl]
    rw [MeasureTheory.integral_indicator hΩ'.measurableSet]
  have h_combine :
      d_real * ((M^2 / (4 * (ε / d_real))) *
        ∫ x, (η x)^2 *
            ∑ i : Fin d, (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((g i) x)^2 ∂(volume : Measure E)) ≤
      C * ∫ x in Ω',
          ∑ i : Fin d, ((g i) x) ^ 2
        ∂(volume : Measure E) := by
    have h_step1 : d_real * ((M^2 / (4 * (ε / d_real))) *
        ∫ x, (η x)^2 *
            ∑ i : Fin d, (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((g i) x)^2 ∂(volume : Measure E)) ≤
        d_real * ((M^2 / (4 * (ε / d_real))) *
          ∫ x in Ω', ∑ i : Fin d, ((g i) x)^2
            ∂(volume : Measure E)) := by
      refine mul_le_mul_of_nonneg_left ?_ hd_nn
      exact mul_le_mul_of_nonneg_left h_ind_bound h_M_factor_nn
    refine h_step1.trans ?_
    have h_J_nn : 0 ≤ ∫ x in Ω',
        ∑ i : Fin d, ((g i) x)^2
          ∂(volume : Measure E) := by
      refine integral_nonneg ?_
      intro x
      exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have h_step2 :
        d_real * ((M^2 / (4 * (ε / d_real))) *
          ∫ x in Ω', ∑ i : Fin d, ((g i) x)^2
            ∂(volume : Measure E)) ≤
        d_real^2 * ((M^2 / (4 * (ε / d_real))) *
          ∫ x in Ω', ∑ i : Fin d, ((g i) x)^2
            ∂(volume : Measure E)) := by
      have h_factor_nn :
          0 ≤ (M^2 / (4 * (ε / d_real))) *
            ∫ x in Ω', ∑ i : Fin d, ((g i) x)^2
              ∂(volume : Measure E) :=
        mul_nonneg h_M_factor_nn h_J_nn
      have h_d_le_d_sq : d_real ≤ d_real^2 := by
        have h := h_d_real_ge_one
        nlinarith
      exact mul_le_mul_of_nonneg_right h_d_le_d_sq h_factor_nn
    refine h_step2.trans ?_
    have h_C_eq : C = d_real^2 * (M^2 / (4 * (ε / d_real))) := by
      rw [hC_def]; ring
    rw [show d_real^2 * ((M^2 / (4 * (ε / d_real))) *
        ∫ x in Ω', ∑ i : Fin d, ((g i) x)^2
          ∂(volume : Measure E)) =
      (d_real^2 * (M^2 / (4 * (ε / d_real)))) *
        ∫ x in Ω', ∑ i : Fin d, ((g i) x)^2
          ∂(volume : Measure E) from by ring]
    rw [← h_C_eq]
  linarith

end Sobolev.NirenbergCrossBoundsNonSmooth
