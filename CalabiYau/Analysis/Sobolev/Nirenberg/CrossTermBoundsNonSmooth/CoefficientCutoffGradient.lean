-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Nirenberg/CrossTermBoundsNonSmooth/CoefficientCutoffGradient.lean
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

private theorem diffQuot_coeff_cutoff_gradient_pointwise_bound_nonsmooth
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (u : E → ℝ) (g : Fin d → E → ℝ)
    {η : E → ℝ} (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (h_fderiv_eta : ∀ x : E, ‖fderiv ℝ η x‖ ≤ N)
    (i j k : Fin d)
    {Ω' : Set E} {M : ℝ} (hM_nn : 0 ≤ M)
    (h_M : ∀ i j : Fin d, ∀ x ∈ closure Ω',
      |(fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single k 1)| ≤ M)
    {h : ℝ}
    (hh_support_in_Ω' : Metric.cthickening |h| (tsupport η) ⊆ Ω') (x : E) :
    |2 * diffQuot k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        ((g i) x) *
        diffQuot k h u x| ≤
      M * N *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        ((g i) x)^2 +
      M * N *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2 := by
  classical
  by_cases hx : x ∈ tsupport η
  · have h_dq_a_bound : |diffQuot k h (fun y => B.a y i j) x| ≤ M := by
      have hCD : ContDiff ℝ 1 (fun y : E => B.a y i j) :=
        (B.contDiff_a i j).of_le (by norm_cast)
      exact abs_diffQuot_a_le_of_bound_on_set (d := d) hCD k h
        (h_M i j) ((singleton_cthick_subset (d := d) η hh_support_in_Ω' (le_refl _) hx).trans
          subset_closure)
    have h_dη_bound : |(fderiv ℝ η x) (EuclideanSpace.single j 1)| ≤ N := by
      have hsing_norm :
          ‖(EuclideanSpace.single j (1 : ℝ) : E)‖ = 1 := by simp
      have h_apply :
          ‖(fderiv ℝ η x) (EuclideanSpace.single j 1)‖ ≤
            ‖fderiv ℝ η x‖ * ‖(EuclideanSpace.single j (1 : ℝ) : E)‖ :=
        (fderiv ℝ η x).le_opNorm _
      rw [hsing_norm, mul_one] at h_apply
      have h2 := h_apply.trans (h_fderiv_eta x)
      rw [Real.norm_eq_abs] at h2
      exact h2
    have h_η_in : η x ∈ Set.Icc (0 : ℝ) 1 := hη_range ⟨x, rfl⟩
    have h_η_nn : 0 ≤ η x := h_η_in.1
    have h_η_le : η x ≤ 1 := h_η_in.2
    have hN_nn : 0 ≤ N := le_trans (norm_nonneg _) (h_fderiv_eta x)
    have h_lhs_eq :
        |2 * diffQuot k h (fun y => B.a y i j) x * (η x) *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            ((g i) x) *
            diffQuot k h u x| =
          2 * |diffQuot k h (fun y => B.a y i j) x| * (η x) *
            |(fderiv ℝ η x) (EuclideanSpace.single j 1)| *
            |(g i) x| *
            |diffQuot k h u x| := by
      rw [show (2 * diffQuot k h (fun y => B.a y i j) x * (η x) *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            ((g i) x) *
            diffQuot k h u x) =
          2 * (diffQuot k h (fun y => B.a y i j) x *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            ((g i) x) *
            diffQuot k h u x * η x) from by ring]
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      rw [abs_mul, abs_mul, abs_mul, abs_mul]
      rw [abs_of_nonneg h_η_nn]
      ring
    rw [h_lhs_eq]
    have h_step1 :
        2 * |diffQuot k h (fun y => B.a y i j) x| * (η x) *
            |(fderiv ℝ η x) (EuclideanSpace.single j 1)| *
            |(g i) x| *
            |diffQuot k h u x| ≤
          2 * M * (η x) * N *
            |(g i) x| *
            |diffQuot k h u x| := by
      have h_step1a :
          2 * |diffQuot k h (fun y => B.a y i j) x| ≤ 2 * M := by
        linarith
      have h_step1b :
          2 * |diffQuot k h (fun y => B.a y i j) x| * (η x) ≤ 2 * M * (η x) :=
        mul_le_mul_of_nonneg_right h_step1a h_η_nn
      have h_step1c :
          2 * |diffQuot k h (fun y => B.a y i j) x| * (η x) *
              |(fderiv ℝ η x) (EuclideanSpace.single j 1)| ≤
            2 * M * (η x) * N := by
        have h_step1c1 : 0 ≤ 2 * M * (η x) :=
          mul_nonneg (mul_nonneg (by linarith) hM_nn) h_η_nn
        calc 2 * |diffQuot k h (fun y => B.a y i j) x| * (η x) *
              |(fderiv ℝ η x) (EuclideanSpace.single j 1)| ≤
            2 * M * (η x) *
              |(fderiv ℝ η x) (EuclideanSpace.single j 1)| := by
              exact mul_le_mul_of_nonneg_right h_step1b (abs_nonneg _)
          _ ≤ 2 * M * (η x) * N :=
              mul_le_mul_of_nonneg_left h_dη_bound h_step1c1
      have h_step1c1 : 0 ≤ 2 * M * (η x) * N :=
        mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hM_nn) h_η_nn) hN_nn
      have h_intermediate : 2 * |diffQuot k h (fun y => B.a y i j) x| * (η x) *
              |(fderiv ℝ η x) (EuclideanSpace.single j 1)| *
              |(g i) x| ≤
            2 * M * (η x) * N *
              |(g i) x| :=
        mul_le_mul_of_nonneg_right h_step1c (abs_nonneg _)
      exact mul_le_mul_of_nonneg_right h_intermediate (abs_nonneg _)
    refine h_step1.trans ?_
    have h_young2 : 2 *
        |(g i) x| *
        |diffQuot k h u x| ≤
        ((g i) x)^2 + (diffQuot k h u x)^2 := by
      have h_sq_diff : 0 ≤ (|(g i) x| - |diffQuot k h u x|)^2 := sq_nonneg _
      have h_g_sq : |(g i) x|^2 = ((g i) x)^2 := sq_abs _
      have h_dq_sq : |diffQuot k h u x|^2 = (diffQuot k h u x)^2 := sq_abs _
      nlinarith [h_sq_diff, h_g_sq, h_dq_sq]
    have h_MN_η_nn : 0 ≤ M * (η x) * N :=
      mul_nonneg (mul_nonneg hM_nn h_η_nn) hN_nn
    have h_step2 :
        2 * M * (η x) * N *
          |(g i) x| *
          |diffQuot k h u x| ≤
        M * (η x) * N *
          (((g i) x)^2 + (diffQuot k h u x)^2) := by
      have h_eq : 2 * M * (η x) * N *
          |(g i) x| *
          |diffQuot k h u x| =
          M * (η x) * N *
          (2 * |(g i) x| *
            |diffQuot k h u x|) := by ring
      rw [h_eq]
      exact mul_le_mul_of_nonneg_left h_young2 h_MN_η_nn
    refine h_step2.trans ?_
    have h_step3 :
        M * (η x) * N *
          (((g i) x)^2 + (diffQuot k h u x)^2) ≤
        M * N *
          (((g i) x)^2 + (diffQuot k h u x)^2) := by
      have h_M_η_N_le : M * (η x) * N ≤ M * 1 * N := by
        refine mul_le_mul_of_nonneg_right ?_ hN_nn
        exact mul_le_mul_of_nonneg_left h_η_le hM_nn
      have h_M_N_eq : M * 1 * N = M * N := by ring
      have h_fact_nn : 0 ≤ ((g i) x)^2 +
          (diffQuot k h u x)^2 := by
        exact add_nonneg (sq_nonneg _) (sq_nonneg _)
      calc M * (η x) * N *
              (((g i) x)^2 + (diffQuot k h u x)^2) ≤
          M * 1 * N *
            (((g i) x)^2 + (diffQuot k h u x)^2) :=
            mul_le_mul_of_nonneg_right h_M_η_N_le h_fact_nn
        _ = M * N *
            (((g i) x)^2 + (diffQuot k h u x)^2) := by
            rw [h_M_N_eq]
    refine h_step3.trans ?_
    have h_indicator : Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x = 1 := by
      rw [Set.indicator_of_mem hx]
    rw [h_indicator]
    ring_nf
    rfl
  · have h_η_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx
    have h_indicator : Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x = 0 :=
      Set.indicator_of_notMem hx _
    have h_lhs_zero : 2 * diffQuot k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        ((g i) x) *
        diffQuot k h u x = 0 := by
      rw [h_η_zero]; ring
    rw [h_lhs_zero, abs_zero, h_indicator]
    have h_t1 : M * N * 0 *
        ((g i) x)^2 = 0 := by ring
    have h_t2 : M * N * 0 * (diffQuot k h u x)^2 = 0 := by ring
    linarith

private lemma diffQuot_a_continuous
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (i j k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    Continuous (fun x : E =>
      Sobolev.diffQuot k h
        (fun y : E => B.a y i j) x) :=
  continuous_diffQuot_smooth (d := d) (B.contDiff_a i j) k hh

private lemma integrable_cross_3_summand_nonsmooth
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ} (hu_l2 : MemLp u 2 (volume : Measure E))
    {g : Fin d → E → ℝ}
    (hg_l2 : ∀ i, MemLp (g i) 2 (volume : Measure E))
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (i j k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    Integrable (fun x : E =>
      2 * diffQuot k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        ((g i) x) *
        diffQuot k h u x) volume := by
  classical
  have h_dq_a : Continuous (Sobolev.diffQuot k h
      (fun y : E => B.a y i j)) :=
    diffQuot_a_continuous (d := d) B i j k hh
  have hη_C1 : ContDiff ℝ 1 η := hη.of_le (by norm_cast)
  have h_partial_η : Continuous
      (fun x : E => (fderiv ℝ η x) (EuclideanSpace.single j 1)) :=
    ((hη_C1.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  set f₃ : E → ℝ := fun x =>
    2 * Sobolev.diffQuot k h
      (fun y : E => B.a y i j) x * (η x) *
      ((fderiv ℝ η x) (EuclideanSpace.single j 1)) with hf₃_def
  have hf₃_cont : Continuous f₃ :=
    ((continuous_const.mul h_dq_a).mul hη.continuous).mul h_partial_η
  have hf₃_support : HasCompactSupport f₃ := by
    have h_step1 : HasCompactSupport (fun x : E =>
        2 * Sobolev.diffQuot k h
          (fun y : E => B.a y i j) x * (η x)) := by
      exact hη_support.mul_left
    exact h_step1.mul_right
  obtain ⟨M, hM_nn, hM⟩ :=
    exists_bound_of_continuous_compactSupport hf₃_cont hf₃_support
  have h_dq_u_l2 : MemLp (diffQuot k h u) 2 (volume : Measure E) :=
    memLp_diffQuot_two k h hu_l2
  have hf₃_gi_l2 : MemLp (fun x => f₃ x * (g i) x) 2
      (volume : Measure E) :=
    memLp_bounded_mul hf₃_cont.aestronglyMeasurable hM (hg_l2 i)
  have h_target_eq :
      (fun x : E =>
        2 * Sobolev.diffQuot k h
          (fun y : E => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          ((g i) x) *
          Sobolev.diffQuot k h u x) =
      (fun x => f₃ x * (g i) x) *
        (Sobolev.diffQuot k h u) := by
    funext x
    change 2 * Sobolev.diffQuot k h
        (fun y : E => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        ((g i) x) *
        Sobolev.diffQuot k h u x =
      (f₃ x * (g i) x) *
        Sobolev.diffQuot k h u x
    simp only [hf₃_def]
  rw [h_target_eq]
  exact MemLp.integrable_mul (p := 2) (q := 2) hf₃_gi_l2 h_dq_u_l2

omit [NeZero d] in
private lemma integrable_const_indicator_g_sq
    {g : Fin d → E → ℝ}
    (hg_l2 : ∀ i, MemLp (g i) 2 (volume : Measure E))
    (η : E → ℝ)
    (i : Fin d) (c : ℝ) :
    Integrable (fun x : E => c *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        ((g i) x)^2)
      (volume : Measure E) := by
  classical
  have h_tsupp_meas : MeasurableSet (tsupport η) :=
    isClosed_tsupport η |>.measurableSet
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
  have h_aesm : AEStronglyMeasurable
      (fun x : E => c *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        ((g i) x)^2) (volume : Measure E) := by
    have h_ind_aesm :
        AEStronglyMeasurable (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)))
          (volume : Measure E) := by
      refine (aestronglyMeasurable_indicator_iff h_tsupp_meas).mpr ?_
      exact aestronglyMeasurable_const
    have h_g_aesm : AEStronglyMeasurable (g i) (volume : Measure E) :=
      (hg_l2 i).aestronglyMeasurable
    have h_g_sq_aesm : AEStronglyMeasurable
        (fun x : E => ((g i) x)^2) (volume : Measure E) :=
      h_g_aesm.pow 2
    exact ((aestronglyMeasurable_const.mul h_ind_aesm).mul h_g_sq_aesm)
  refine (h_g_sq_int.const_mul |c|).mono' h_aesm ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  rw [Real.norm_eq_abs]
  by_cases hx : x ∈ tsupport η
  · rw [Set.indicator_of_mem hx, mul_one]
    have h_g_sq_nn : 0 ≤ ((g i) x)^2 := sq_nonneg _
    rw [abs_mul, abs_of_nonneg h_g_sq_nn]
  · rw [Set.indicator_of_notMem hx, mul_zero, zero_mul]
    rw [abs_zero]
    have h_g_sq_nn : 0 ≤ ((g i) x)^2 := sq_nonneg _
    refine mul_nonneg (abs_nonneg _) h_g_sq_nn

omit [NeZero d] in
private lemma integral_const_indicator_g_sq_eq
    {g : Fin d → E → ℝ} (η : E → ℝ) (i : Fin d) (c : ℝ) :
    ∫ x, c * (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        ((g i) x)^2 ∂(volume : Measure E) =
      c * ∫ x in tsupport η, ((g i) x)^2 ∂(volume : Measure E) := by
  have h_eq : (fun x : E => c *
      (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
      ((g i) x)^2) =
      (fun x : E => c * ((Set.indicator (tsupport η)
        (fun _ : E => (1 : ℝ)) x) * ((g i) x)^2)) := by
    funext x; ring
  rw [h_eq, integral_const_mul]
  congr 1
  rw [show (fun x : E => (Set.indicator (tsupport η)
        (fun _ : E => (1 : ℝ)) x) * ((g i) x)^2) =
      (fun x : E => Set.indicator (tsupport η)
        (fun y : E => ((g i) y)^2) x) from by
    funext x
    by_cases hx : x ∈ tsupport η
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]; ring
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; ring]
  rw [MeasureTheory.integral_indicator (isClosed_tsupport η).measurableSet]

theorem diffQuot_coeff_cutoff_gradient_bound_nonsmooth_quantitative
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ}
    (hu_l2 : MemLp u 2 (volume : Measure E))
    {g : Fin d → E → ℝ}
    (hg_l2 : ∀ i, MemLp (g i) 2 (volume : Measure E))
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (hN : 0 ≤ N) (h_fderiv_eta : ∀ x : E, ‖fderiv ℝ η x‖ ≤ N)
    {Ω' : Set E}
    (hΩ'_compact : IsCompact (closure Ω'))
    {R₀ : ℝ}
    (hh_support_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (k : Fin d)
    (h_FK_diffQuot_u_bound : ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E) ≤
        ∫ x in Ω', ∑ i : Fin d, ((g i) x) ^ 2 ∂(volume : Measure E)) :
    ∀ ⦃h : ℝ⦄, h ≠ 0 → |h| ≤ R₀ →
      |- ∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
            (Sobolev.diffQuot k h
              (fun y : E => B.a y i j)) x *
            (η x) *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            ((g i) x) *
            Sobolev.diffQuot k h u x
          ∂(volume : Measure E)| ≤
        (2 * (Classical.choose
              (SmoothEllipticBilinearForm.bounded_fderiv_a_on_compact
                (d := d) B k hΩ'_compact))
            * N * (Fintype.card (Fin d) : ℝ)^2) * ∫ x in Ω',
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
  have hd_ge_one : 1 ≤ d_real := by
    rw [hd_real]; exact_mod_cast Fintype.card_pos
  have hd_nn : 0 ≤ d_real := hd_pos.le
  set C : ℝ := 2 * M * N * d_real^2 with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    refine mul_nonneg ?_ (sq_nonneg _)
    refine mul_nonneg ?_ hN
    exact mul_nonneg (by linarith) hM_nn
  intro h hh hh_le
  have h_thick_in_Ω' : Metric.cthickening |h| (tsupport η) ⊆ Ω' := hh_support_in_Ω' hh_le
  have h_each_pointwise := fun (i j : Fin d) (x : E) =>
    diffQuot_coeff_cutoff_gradient_pointwise_bound_nonsmooth (d := d) B u g hη_range h_fderiv_eta i
      j k hM_nn h_M
      h_thick_in_Ω' x
  set S : ℝ := ∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
        diffQuot k h (fun y : E => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        ((g i) x) *
        diffQuot k h u x
      ∂(volume : Measure E) with hS_def
  rw [abs_neg]
  have h_abs_sum : |S| ≤
      ∑ i : Fin d, ∑ j : Fin d, |∫ x, 2 *
          diffQuot k h (fun y : E => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          ((g i) x) *
          diffQuot k h u x ∂(volume : Measure E)| :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _))
  refine h_abs_sum.trans ?_
  have h_integrand_int : ∀ i j : Fin d, Integrable (fun x : E =>
      2 * diffQuot k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        ((g i) x) *
        diffQuot k h u x) volume :=
    fun i j => integrable_cross_3_summand_nonsmooth (d := d) B hu_l2 hg_l2 hη hη_support
      i j k hh
  have h_pt_bound1_int : ∀ i : Fin d, Integrable (fun x : E =>
      M * N *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        ((g i) x)^2) volume :=
    fun i => integrable_const_indicator_g_sq (d := d) hg_l2 η i (M * N)
  have h_pt_bound2_int : Integrable (fun x : E =>
      M * N *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2) volume :=
    integrable_const_indicator_diffQuot_u_sq (d := d) hu_l2 hη_support k h (M * N)
  have h_pt_bound_int : ∀ i j : Fin d, Integrable (fun x : E =>
      M * N *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        ((g i) x)^2 +
      M * N *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2) volume :=
    fun i j => (h_pt_bound1_int i).add h_pt_bound2_int
  have h_per_pair_bound : ∀ i j : Fin d,
      |∫ x, 2 * diffQuot k h (fun y => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          ((g i) x) *
          diffQuot k h u x ∂(volume : Measure E)| ≤
      ∫ x, (M * N *
          (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
          ((g i) x)^2 +
        M * N *
          (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
          (diffQuot k h u x)^2) ∂(volume : Measure E) := by
    intro i j
    have h_tri := abs_integral_le_integral_abs (μ := (volume : Measure E))
      (f := fun x : E => 2 * diffQuot k h (fun y => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          ((g i) x) *
          diffQuot k h u x)
    refine h_tri.trans ?_
    refine integral_mono_ae ((h_integrand_int i j).abs) (h_pt_bound_int i j) ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    exact h_each_pointwise i j x
  have h_outer_sum :
      ∑ i : Fin d, ∑ j : Fin d, |∫ x, 2 *
          diffQuot k h (fun y => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          ((g i) x) *
          diffQuot k h u x ∂(volume : Measure E)| ≤
      ∑ i : Fin d, ∑ j : Fin d,
        ∫ x, (M * N *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((g i) x)^2 +
          M * N *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2) ∂(volume : Measure E) :=
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => h_per_pair_bound i j))
  refine h_outer_sum.trans ?_
  have h_total_bound :
      ∑ i : Fin d, ∑ j : Fin d,
        ∫ x, (M * N *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((g i) x)^2 +
          M * N *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2) ∂(volume : Measure E) ≤
      C * ∫ x in Ω',
          ∑ i : Fin d, ((g i) x) ^ 2
        ∂(volume : Measure E) := by
    have h_split_integral : ∀ i j : Fin d,
        ∫ x, (M * N *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((g i) x)^2 +
          M * N *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2) ∂(volume : Measure E) =
        ∫ x, M * N *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((g i) x)^2 ∂(volume : Measure E) +
        ∫ x, M * N *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2 ∂(volume : Measure E) := by
      intro i j
      rw [integral_add (h_pt_bound1_int i) h_pt_bound2_int]
    have h_A_factor : ∀ i : Fin d,
        ∫ x, M * N *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((g i) x)^2 ∂(volume : Measure E) =
        M * N * ∫ x in tsupport η,
          ((g i) x)^2 ∂(volume : Measure E) := by
      intro i
      exact integral_const_indicator_g_sq_eq (d := d) η i (M * N)
    have h_B_factor :
        ∫ x, M * N *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2 ∂(volume : Measure E) =
        M * N * ∫ x in tsupport η,
          (diffQuot k h u x)^2 ∂(volume : Measure E) :=
      integral_const_indicator_eq (d := d) k h η (M * N) (u := u)
    rw [show (∑ i : Fin d, ∑ j : Fin d, ∫ x, (M * N *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((g i) x)^2 +
          M * N *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2) ∂(volume : Measure E)) =
        ∑ i : Fin d, ∑ j : Fin d,
          (∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((g i) x)^2 ∂(volume : Measure E) +
          ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E)) from
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => h_split_integral i j))]
    rw [show (∑ i : Fin d, ∑ j : Fin d,
          (∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((g i) x)^2 ∂(volume : Measure E) +
          ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E))) =
        ∑ i : Fin d, (∑ j : Fin d, ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((g i) x)^2 ∂(volume : Measure E)) +
        ∑ i : Fin d, (∑ j : Fin d, ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E)) from by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [Finset.sum_add_distrib]]
    have h_step1 : (∑ i : Fin d, (∑ _j : Fin d, ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((g i) x)^2 ∂(volume : Measure E))) =
        d_real * ∑ i : Fin d, ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((g i) x)^2 ∂(volume : Measure E) := by
      rw [show (∑ i : Fin d, (∑ _j : Fin d, ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((g i) x)^2 ∂(volume : Measure E))) =
          ∑ i : Fin d, d_real * ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((g i) x)^2 ∂(volume : Measure E) from
            Finset.sum_congr rfl (fun i _ => by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul])]
      rw [← Finset.mul_sum]
    have h_step2 : (∑ _i : Fin d, (∑ _j : Fin d, ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E))) =
        d_real^2 * ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E) := by
      have h_inner : ∀ _i : Fin d, (∑ _j : Fin d, ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E)) =
            d_real * ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E) := by
        intro _i
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [show (∑ _i : Fin d, (∑ _j : Fin d, ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E))) =
          ∑ _i : Fin d, d_real * ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E) from
            Finset.sum_congr rfl (fun i _ => h_inner i)]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, ← hd_real]
      ring
    rw [h_step1, h_step2]
    rw [show (∑ i : Fin d, ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((g i) x)^2 ∂(volume : Measure E)) =
        ∑ i : Fin d, M * N * ∫ x in tsupport η,
          ((g i) x)^2 ∂(volume : Measure E) from
        Finset.sum_congr rfl (fun i _ => h_A_factor i)]
    rw [h_B_factor]
    have h_MN_nn : 0 ≤ M * N := mul_nonneg hM_nn hN
    have h_d_le_d_sq : d_real ≤ d_real^2 := by nlinarith
    have h_J_nn : 0 ≤ ∫ x in Ω',
        ∑ i : Fin d, ((g i) x)^2
          ∂(volume : Measure E) :=
      integral_nonneg (fun x => Finset.sum_nonneg (fun i _ => sq_nonneg _))
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
    have h_int_Ω' : ∀ i : Fin d, IntegrableOn
        (fun x : E => ((g i) x)^2) Ω' (volume : Measure E) :=
      fun i => (h_g_sq_int i).integrableOn
    have h_tsupp_subset_Ω' : tsupport η ⊆ Ω' :=
      fun x hx => h_thick_in_Ω' (self_subset_cthickening _ hx)
    have h_part_bound : ∀ i : Fin d,
        ∫ x in tsupport η, ((g i) x)^2 ∂(volume : Measure E) ≤
        ∫ x in Ω', ((g i) x)^2 ∂(volume : Measure E) := by
      intro i
      refine setIntegral_mono_set (h_int_Ω' i) ?_ ?_
      · exact Filter.Eventually.of_forall (fun x => sq_nonneg _)
      · exact Filter.Eventually.of_forall h_tsupp_subset_Ω'
    have h_sum_part_bound :
        ∑ i : Fin d, ∫ x in tsupport η,
          ((g i) x)^2 ∂(volume : Measure E) ≤
        ∫ x in Ω',
          ∑ i : Fin d, ((g i) x)^2 ∂(volume : Measure E) := by
      have h_sum_eq :
          ∫ x in Ω',
              ∑ i : Fin d, ((g i) x)^2
            ∂(volume : Measure E) =
          ∑ i : Fin d, ∫ x in Ω',
              ((g i) x)^2 ∂(volume : Measure E) := by
        exact integral_finsetSum (Finset.univ : Finset (Fin d))
          (fun i _ => h_int_Ω' i)
      rw [h_sum_eq]
      exact Finset.sum_le_sum (fun i _ => h_part_bound i)
    have h_diff_bound :
        ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E) ≤
        ∫ x in Ω',
          ∑ i : Fin d, ((g i) x)^2 ∂(volume : Measure E) :=
      h_FK_diffQuot_u_bound hh hh_le
    have h_term1 :
        d_real * ∑ i : Fin d, M * N *
            ∫ x in tsupport η,
              ((g i) x)^2 ∂(volume : Measure E) ≤
        d_real^2 * (M * N * ∫ x in Ω',
              ∑ i : Fin d, ((g i) x)^2
            ∂(volume : Measure E)) := by
      rw [show (d_real * ∑ i : Fin d, M * N *
            ∫ x in tsupport η,
              ((g i) x)^2 ∂(volume : Measure E)) =
          (d_real * (M * N)) * (∑ i : Fin d, ∫ x in tsupport η,
              ((g i) x)^2 ∂(volume : Measure E)) from by
        rw [← Finset.mul_sum]; ring]
      have h_step_a : (d_real * (M * N)) * (∑ i : Fin d, ∫ x in tsupport η,
              ((g i) x)^2 ∂(volume : Measure E)) ≤
          (d_real * (M * N)) * (∫ x in Ω',
              ∑ i : Fin d, ((g i) x)^2
            ∂(volume : Measure E)) := by
        refine mul_le_mul_of_nonneg_left h_sum_part_bound ?_
        exact mul_nonneg hd_nn h_MN_nn
      refine h_step_a.trans ?_
      rw [show d_real^2 * (M * N * ∫ x in Ω',
              ∑ i : Fin d, ((g i) x)^2
            ∂(volume : Measure E)) =
          (d_real^2 * (M * N)) * (∫ x in Ω',
              ∑ i : Fin d, ((g i) x)^2
            ∂(volume : Measure E)) from by ring]
      refine mul_le_mul_of_nonneg_right ?_ h_J_nn
      exact mul_le_mul_of_nonneg_right h_d_le_d_sq h_MN_nn
    have h_term2 :
        d_real^2 * (M * N * ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E)) ≤
        d_real^2 * (M * N * ∫ x in Ω',
              ∑ i : Fin d, ((g i) x)^2
            ∂(volume : Measure E)) := by
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_left h_diff_bound h_MN_nn
    have h_sum_le : d_real * ∑ i : Fin d, M * N *
            ∫ x in tsupport η,
              ((g i) x)^2 ∂(volume : Measure E) +
        d_real^2 * (M * N * ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E)) ≤
        2 * (d_real^2 * (M * N * ∫ x in Ω',
              ∑ i : Fin d, ((g i) x)^2
            ∂(volume : Measure E))) := by linarith
    refine h_sum_le.trans ?_
    have h_C_eq : C = 2 * d_real^2 * M * N := by
      rw [hC_def]; ring
    rw [show 2 * (d_real^2 * (M * N * ∫ x in Ω',
              ∑ i : Fin d, ((g i) x)^2
            ∂(volume : Measure E))) =
        (2 * d_real^2 * M * N) *
          ∫ x in Ω',
              ∑ i : Fin d, ((g i) x)^2
            ∂(volume : Measure E) from by ring]
    rw [← h_C_eq]
  exact h_total_bound

end Sobolev.NirenbergCrossBoundsNonSmooth
