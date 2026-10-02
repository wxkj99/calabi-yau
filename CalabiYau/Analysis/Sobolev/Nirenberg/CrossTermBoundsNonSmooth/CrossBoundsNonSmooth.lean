-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Nirenberg/CrossTermBoundsNonSmooth/CrossBoundsNonSmooth.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Nirenberg.MasterInequality.Coercivity
public import CalabiYau.Analysis.Sobolev.Nirenberg.MasterInequality.CrossBoundsSummandContinuityIntegrability
public import CalabiYau.Analysis.Sobolev.Nirenberg.MasterInequality.CrossBoundsPointwiseProductBounds
public import CalabiYau.Analysis.Sobolev.Nirenberg.TestFunction.CutoffDiffQuot
public import CalabiYau.Analysis.Sobolev.Tools.DifferenceQuotient

@[expose] public section

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open Sobolev
open Sobolev.NirenbergEuclidean
open Sobolev.NirenbergCrossBounds
open scoped ENNReal NNReal Convolution Pointwise BigOperators InnerProductSpace

namespace Sobolev.NirenbergCrossBoundsNonSmooth

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

variable [NeZero d] in
private theorem cross_1_pointwise_bound_nonsmooth
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (u : E → ℝ) (g : Fin d → E → ℝ)
    {η : E → ℝ} (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (h_fderiv_eta : ∀ x : E, ‖fderiv ℝ η x‖ ≤ N)
    {Ω' : Set E} {Λ : ℝ}
    (h_Λ : ∀ i j : Fin d, ∀ x ∈ closure Ω', |B.a x i j| ≤ Λ)
    (i j k : Fin d) {h : ℝ}
    (hh_support_in_Ω' : Metric.cthickening |h| (tsupport η) ⊆ Ω')
    {ε : ℝ} (hε : 0 < ε) (x : E) :
    |2 * translate k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        diffQuot k h (g i) x *
        diffQuot k h u x| ≤
      ε * (η x)^2 *
        (diffQuot k h (g i) x)^2 +
      (1/ε) * Λ^2 * N^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2 := by
  classical
  by_cases hx : x ∈ tsupport η
  · have h_shift_in : x + h • EuclideanSpace.single k 1 ∈ closure Ω' := by
      have h_shift_in_Ω' : x + h • EuclideanSpace.single k 1 ∈ Ω' := by
        refine hh_support_in_Ω' ?_
        refine Metric.mem_cthickening_of_dist_le _ x |h| (tsupport η) hx ?_
        have hsing_norm : ‖(EuclideanSpace.single k (1 : ℝ) : E)‖ = 1 := by simp
        have hdist_eq :
            dist (x + h • EuclideanSpace.single k 1) x = |h| := by
          rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hsing_norm, mul_one,
            Real.norm_eq_abs]
        rw [hdist_eq]
      exact subset_closure h_shift_in_Ω'
    have h_τa_bound : |translate k h (fun y => B.a y i j) x| ≤ Λ := by
      unfold translate
      exact h_Λ i j _ h_shift_in
    have h_dη_bound : |(fderiv ℝ η x) (EuclideanSpace.single j 1)| ≤ N := by
      have hsing_norm :
          ‖(EuclideanSpace.single j (1 : ℝ) : E)‖ = 1 := by simp
      have h_apply :
          ‖(fderiv ℝ η x) (EuclideanSpace.single j 1)‖ ≤
            ‖fderiv ℝ η x‖ * ‖(EuclideanSpace.single j (1 : ℝ) : E)‖ :=
        (fderiv ℝ η x).le_opNorm _
      rw [hsing_norm, mul_one] at h_apply
      have h2 : ‖(fderiv ℝ η x) (EuclideanSpace.single j 1)‖ ≤ N :=
        h_apply.trans (h_fderiv_eta x)
      rw [Real.norm_eq_abs] at h2
      exact h2
    have h_η_in : η x ∈ Set.Icc (0 : ℝ) 1 := hη_range ⟨x, rfl⟩
    have h_η_nn : 0 ≤ η x := h_η_in.1
    set A : ℝ := η x * diffQuot k h (g i) x with hA_def
    set B' : ℝ := translate k h (fun y => B.a y i j) x *
      ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
      diffQuot k h u x with hB'_def
    have h_eq_lhs :
        |2 * translate k h (fun y => B.a y i j) x * (η x) *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            diffQuot k h (g i) x *
            diffQuot k h u x| =
        2 * |A| * |B'| := by
      have h_AB'_eq : 2 * A * B' =
          2 * translate k h (fun y => B.a y i j) x * (η x) *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            diffQuot k h (g i) x *
            diffQuot k h u x := by
        change 2 * (η x * diffQuot k h (g i) x) *
            (translate k h (fun y => B.a y i j) x *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              diffQuot k h u x) = _
        ring
      rw [← h_AB'_eq]
      rw [show (2 * A * B') = 2 * (A * B') by ring]
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_mul]
      ring
    rw [h_eq_lhs]
    have h_young := Sobolev.NirenbergCrossBounds.two_abs_mul_le_eps_sq_add A B' ε hε
    refine h_young.trans ?_
    have hA_sq : A^2 = (η x)^2 * (diffQuot k h (g i) x)^2 := by
      change ((η x) * diffQuot k h (g i) x)^2 = _
      ring
    have hB'_sq_le : B'^2 ≤ Λ^2 * N^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2 := by
      have h_indicator : Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x = 1 := by
        rw [Set.indicator_of_mem hx]
      rw [h_indicator]
      change (translate k h (fun y => B.a y i j) x *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          diffQuot k h u x)^2 ≤ _
      have h_τa_sq_le : (translate k h (fun y => B.a y i j) x)^2 ≤ Λ^2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h_τa_bound 2
      have h_dη_sq_le : ((fderiv ℝ η x) (EuclideanSpace.single j 1))^2 ≤ N^2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h_dη_bound 2
      have hΛ_nn : 0 ≤ Λ := by
        have h_x_in_Ω' : x ∈ Ω' :=
          hh_support_in_Ω' (self_subset_cthickening _ hx)
        have h_x_in : x ∈ closure Ω' := subset_closure h_x_in_Ω'
        exact le_trans (abs_nonneg _) (h_Λ i j x h_x_in)
      have hN_nn : 0 ≤ N := le_trans (norm_nonneg _) (h_fderiv_eta x)
      have hΛ_sq_nn : 0 ≤ Λ^2 := sq_nonneg _
      have hN_sq_nn : 0 ≤ N^2 := sq_nonneg _
      have h_dq_sq_nn : 0 ≤ (diffQuot k h u x)^2 := sq_nonneg _
      have h_τa_sq_nn : 0 ≤ (translate k h (fun y => B.a y i j) x)^2 := sq_nonneg _
      have h_dη_sq_nn : 0 ≤ ((fderiv ℝ η x) (EuclideanSpace.single j 1))^2 := sq_nonneg _
      have h_step1 : (translate k h (fun y => B.a y i j) x)^2 *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1))^2 *
            (diffQuot k h u x)^2 ≤
          Λ^2 * N^2 * (diffQuot k h u x)^2 := by
        have h_first :
            (translate k h (fun y => B.a y i j) x)^2 *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1))^2 ≤ Λ^2 * N^2 :=
          mul_le_mul h_τa_sq_le h_dη_sq_le h_dη_sq_nn hΛ_sq_nn
        exact mul_le_mul_of_nonneg_right h_first h_dq_sq_nn
      calc (translate k h (fun y => B.a y i j) x *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              diffQuot k h u x)^2
          = (translate k h (fun y => B.a y i j) x)^2 *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1))^2 *
              (diffQuot k h u x)^2 := by ring
        _ ≤ Λ^2 * N^2 * (diffQuot k h u x)^2 := h_step1
        _ = Λ^2 * N^2 * 1 * (diffQuot k h u x)^2 := by rw [mul_one]
    have hε_pos : 0 < (1 : ℝ) / ε := one_div_pos.mpr hε
    have h_step :
        (1/ε) * B'^2 ≤ (1/ε) * (Λ^2 * N^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2) :=
      mul_le_mul_of_nonneg_left hB'_sq_le hε_pos.le
    calc ε * A^2 + (1/ε) * B'^2
        ≤ ε * A^2 + (1/ε) * (Λ^2 * N^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2) := by linarith
      _ = ε * (η x)^2 * (diffQuot k h (g i) x)^2 +
          (1/ε) * Λ^2 * N^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2 := by
            rw [hA_sq]; ring
  · have h_η_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx
    have h_LHS_zero : 2 * translate k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        diffQuot k h (g i) x *
        diffQuot k h u x = 0 := by
      rw [h_η_zero]; ring
    rw [h_LHS_zero, abs_zero]
    have h_indicator : Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x = 0 :=
      Set.indicator_of_notMem hx _
    have h_t1_nn : 0 ≤ ε * (η x)^2 *
        (diffQuot k h (g i) x)^2 := by
      apply mul_nonneg
      · exact mul_nonneg hε.le (sq_nonneg _)
      · exact sq_nonneg _
    have h_t2_zero : (1/ε) * Λ^2 * N^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2 = 0 := by
      rw [h_indicator]; ring
    linarith

lemma memLp_diffQuot_two
    (k : Fin d) (h : ℝ) {v : E → ℝ}
    (hv : MemLp v 2 (volume : Measure E)) :
    MemLp (diffQuot k h v) 2 (volume : Measure E) :=
  memLp_diffQuot k h hv

lemma exists_bound_of_continuous_compactSupport
    {f : E → ℝ} (hf_cont : Continuous f) (hf_support : HasCompactSupport f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |f x| ≤ M := by
  have h_abs_cont : Continuous (fun x : E => |f x|) :=
    hf_cont.abs
  have h_abs_support : HasCompactSupport (fun x : E => |f x|) := by
    have heq : (fun x : E => |f x|) = (fun y : ℝ => |y|) ∘ f := rfl
    rw [heq]
    exact hf_support.comp_left abs_zero
  obtain ⟨M, hM⟩ := h_abs_cont.bddAbove_range_of_hasCompactSupport h_abs_support
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  have h : |f x| ≤ M := hM ⟨x, rfl⟩
  exact h.trans (le_max_left _ _)

lemma memLp_bounded_mul
    {f g : E → ℝ}
    (hf_aesm : AEStronglyMeasurable f (volume : Measure E))
    {M : ℝ} (hM : ∀ x, |f x| ≤ M)
    (hg : MemLp g 2 (volume : Measure E)) :
    MemLp (fun x => f x * g x) 2 (volume : Measure E) := by
  have h_aesm : AEStronglyMeasurable (fun x => f x * g x) (volume : Measure E) :=
    hf_aesm.mul hg.aestronglyMeasurable
  refine MemLp.of_le_mul (c := M) hg h_aesm ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hM x) (abs_nonneg _)

variable [NeZero d] in
private lemma integrable_cross_1_summand_nonsmooth
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ} (hu_l2 : MemLp u 2 (volume : Measure E))
    {g : Fin d → E → ℝ}
    (hg_l2 : ∀ i, MemLp (g i) 2 (volume : Measure E))
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (i j k : Fin d) (h : ℝ) :
    Integrable (fun x : E =>
      2 * translate k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        diffQuot k h (g i) x *
        diffQuot k h u x) volume := by
  classical
  have h_a_cont : Continuous (fun x : E => B.a x i j) := B.continuous_a i j
  have h_translate_a : Continuous
      (translate k h (fun y => B.a y i j)) := by
    unfold translate
    exact h_a_cont.comp (continuous_id.add continuous_const)
  have hη_C1 : ContDiff ℝ 1 η := hη.of_le (by norm_cast)
  have h_partial_η : Continuous
      (fun x : E => (fderiv ℝ η x) (EuclideanSpace.single j 1)) :=
    ((hη_C1.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  set f₁ : E → ℝ := fun x =>
    2 * translate k h (fun y => B.a y i j) x * (η x) *
      ((fderiv ℝ η x) (EuclideanSpace.single j 1)) with hf₁_def
  have hf₁_cont : Continuous f₁ :=
    ((continuous_const.mul h_translate_a).mul hη.continuous).mul h_partial_η
  have hf₁_support : HasCompactSupport f₁ := by
    have h_step1 : HasCompactSupport (fun x : E =>
        2 * translate k h (fun y => B.a y i j) x * (η x)) := by
      exact hη_support.mul_left
    exact h_step1.mul_right
  obtain ⟨M, hM_nn, hM⟩ :=
    exists_bound_of_continuous_compactSupport hf₁_cont hf₁_support
  have h_dq_g_l2 : MemLp (diffQuot k h (g i)) 2 (volume : Measure E) :=
    memLp_diffQuot_two k h (hg_l2 i)
  have h_dq_u_l2 : MemLp (diffQuot k h u) 2 (volume : Measure E) :=
    memLp_diffQuot_two k h hu_l2
  have hf₁_dqg_l2 : MemLp (fun x => f₁ x * diffQuot k h (g i) x) 2
      (volume : Measure E) :=
    memLp_bounded_mul hf₁_cont.aestronglyMeasurable hM h_dq_g_l2
  have h_target_eq :
      (fun x : E =>
        2 * translate k h (fun y => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          diffQuot k h (g i) x *
          diffQuot k h u x) =
      (fun x => f₁ x * diffQuot k h (g i) x) * (diffQuot k h u) := by
    funext x
    change 2 * translate k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        diffQuot k h (g i) x *
        diffQuot k h u x =
        (f₁ x * diffQuot k h (g i) x) * diffQuot k h u x
    simp only [hf₁_def]
  rw [h_target_eq]
  exact MemLp.integrable_mul (p := 2) (q := 2) hf₁_dqg_l2 h_dq_u_l2

lemma integrable_const_eta_sq_diffQuot_g_sq
    {g : Fin d → E → ℝ}
    (hg_l2 : ∀ i, MemLp (g i) 2 (volume : Measure E))
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (i k : Fin d) (h : ℝ) (c : ℝ) :
    Integrable (fun x : E => c * (η x)^2 *
      (diffQuot k h (g i) x)^2)
      (volume : Measure E) := by
  classical
  have hη_sq_cont : Continuous (fun x : E => η x ^ 2) := hη.continuous.pow 2
  have hη_sq_support : HasCompactSupport (fun x : E => η x ^ 2) := by
    have heq : (fun y : E => η y ^ 2) = (fun y : E => η y * η y) := by
      funext y; ring
    rw [heq]; exact hη_support.mul_right
  obtain ⟨M, hM_nn, hM⟩ :=
    exists_bound_of_continuous_compactSupport hη_sq_cont hη_sq_support
  have h_dq_g_l2 : MemLp (diffQuot k h (g i)) 2 (volume : Measure E) :=
    memLp_diffQuot_two k h (hg_l2 i)
  have h_dq_g_sq_int : Integrable (fun x : E => (diffQuot k h (g i) x)^2)
      (volume : Measure E) := by
    have h_dq_norm_sq_int : Integrable
        (fun x : E => ‖diffQuot k h (g i) x‖ ^ (2 : ℕ)) (volume : Measure E) := by
      have hh := h_dq_g_l2.integrable_norm_rpow
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      have h_pow_eq : (2 : ℝ≥0∞).toReal = 2 := by
        show ENNReal.toReal 2 = 2; rfl
      rw [h_pow_eq] at hh
      have heq : (fun x : E => ‖diffQuot k h (g i) x‖ ^ (2 : ℝ)) =
          (fun x : E => ‖diffQuot k h (g i) x‖ ^ (2 : ℕ)) := by
        funext x
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_cast,
          Real.rpow_natCast]
      rw [heq] at hh
      exact hh
    have heq2 : (fun x : E => (diffQuot k h (g i) x)^2) =
        (fun x : E => ‖diffQuot k h (g i) x‖ ^ (2 : ℕ)) := by
      funext x
      rw [Real.norm_eq_abs, sq_abs]
    rw [heq2]
    exact h_dq_norm_sq_int
  have h_aesm : AEStronglyMeasurable
      (fun x : E => c * (η x)^2 * (diffQuot k h (g i) x)^2)
      (volume : Measure E) := by
    have h1 : AEStronglyMeasurable (fun x : E => c * (η x)^2)
        (volume : Measure E) :=
      (continuous_const.mul hη_sq_cont).aestronglyMeasurable
    have h_dq_aesm : AEStronglyMeasurable (diffQuot k h (g i))
        (volume : Measure E) :=
      aestronglyMeasurable_diffQuot (d := d) k h (hg_l2 i).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun x : E => (diffQuot k h (g i) x)^2)
        (volume : Measure E) := h_dq_aesm.pow 2
    exact h1.mul h2
  have h_const_mul_int : Integrable
      (fun x : E => |c| * M * (diffQuot k h (g i) x)^2)
      (volume : Measure E) := h_dq_g_sq_int.const_mul (|c| * M)
  refine h_const_mul_int.mono' h_aesm ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  have h_eta_sq_nn : 0 ≤ (η x)^2 := sq_nonneg _
  have h_dq_sq_nn : 0 ≤ (diffQuot k h (g i) x)^2 := sq_nonneg _
  have h_eta_sq_le : (η x)^2 ≤ M := by
    have hM_apply := hM x
    rw [abs_of_nonneg h_eta_sq_nn] at hM_apply
    exact hM_apply
  rw [Real.norm_eq_abs]
  have h_LHS_eq : |c * (η x)^2 * (diffQuot k h (g i) x)^2| =
      |c| * (η x)^2 * (diffQuot k h (g i) x)^2 := by
    rw [show c * (η x)^2 * (diffQuot k h (g i) x)^2 =
      c * ((η x)^2 * (diffQuot k h (g i) x)^2) from by ring]
    rw [abs_mul, abs_mul]
    rw [abs_of_nonneg h_eta_sq_nn, abs_of_nonneg h_dq_sq_nn]
    ring
  rw [h_LHS_eq]
  have h_ic_nn : 0 ≤ |c| := abs_nonneg _
  have h_ic_eta_sq : |c| * (η x)^2 ≤ |c| * M :=
    mul_le_mul_of_nonneg_left h_eta_sq_le h_ic_nn
  exact mul_le_mul_of_nonneg_right h_ic_eta_sq h_dq_sq_nn

lemma integrable_const_indicator_diffQuot_u_sq
    {u : E → ℝ} (hu_l2 : MemLp u 2 (volume : Measure E))
    {η : E → ℝ} (hη_support : HasCompactSupport η)
    (k : Fin d) (h : ℝ) (c : ℝ) :
    Integrable (fun x : E => c *
      (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
      (diffQuot k h u x)^2)
      (volume : Measure E) := by
  classical
  have h_tsupp_meas : MeasurableSet (tsupport η) :=
    isClosed_tsupport η |>.measurableSet
  have h_tsupp_compact : IsCompact (tsupport η) := hη_support
  have h_dq_u_l2 : MemLp (diffQuot k h u) 2 (volume : Measure E) :=
    memLp_diffQuot_two k h hu_l2
  have h_dq_u_sq_int : Integrable (fun x : E => (diffQuot k h u x)^2)
      (volume : Measure E) := by
    have h_dq_norm_sq_int : Integrable
        (fun x : E => ‖diffQuot k h u x‖ ^ (2 : ℕ)) (volume : Measure E) := by
      have hh := h_dq_u_l2.integrable_norm_rpow
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      have h_pow_eq : (2 : ℝ≥0∞).toReal = 2 := by
        show ENNReal.toReal 2 = 2; rfl
      rw [h_pow_eq] at hh
      have heq : (fun x : E => ‖diffQuot k h u x‖ ^ (2 : ℝ)) =
          (fun x : E => ‖diffQuot k h u x‖ ^ (2 : ℕ)) := by
        funext x
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_cast,
          Real.rpow_natCast]
      rw [heq] at hh
      exact hh
    have heq2 : (fun x : E => (diffQuot k h u x)^2) =
        (fun x : E => ‖diffQuot k h u x‖ ^ (2 : ℕ)) := by
      funext x
      rw [Real.norm_eq_abs, sq_abs]
    rw [heq2]
    exact h_dq_norm_sq_int
  have h_aesm : AEStronglyMeasurable
      (fun x : E => c *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2) (volume : Measure E) := by
    have h_ind_aesm :
        AEStronglyMeasurable (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)))
          (volume : Measure E) := by
      refine (aestronglyMeasurable_indicator_iff h_tsupp_meas).mpr ?_
      exact aestronglyMeasurable_const
    have h_dq_aesm : AEStronglyMeasurable (diffQuot k h u)
        (volume : Measure E) :=
      aestronglyMeasurable_diffQuot (d := d) k h hu_l2.aestronglyMeasurable
    have h_dq_sq_aesm : AEStronglyMeasurable
        (fun x : E => (diffQuot k h u x)^2) (volume : Measure E) :=
      h_dq_aesm.pow 2
    exact ((aestronglyMeasurable_const.mul h_ind_aesm).mul h_dq_sq_aesm)
  refine (h_dq_u_sq_int.const_mul |c|).mono' h_aesm ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  rw [Real.norm_eq_abs]
  by_cases hx : x ∈ tsupport η
  · rw [Set.indicator_of_mem hx, mul_one]
    have h_dq_sq_nn : 0 ≤ (diffQuot k h u x)^2 := sq_nonneg _
    rw [abs_mul, abs_of_nonneg h_dq_sq_nn]
  · rw [Set.indicator_of_notMem hx, mul_zero, zero_mul]
    rw [abs_zero]
    have h_dq_sq_nn : 0 ≤ (diffQuot k h u x)^2 := sq_nonneg _
    refine mul_nonneg (abs_nonneg _) h_dq_sq_nn

lemma integral_const_indicator_eq
    {u : E → ℝ} (k : Fin d) (h : ℝ) (η : E → ℝ) (c : ℝ) :
    ∫ x, c * (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2 ∂(volume : Measure E) =
      c * ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E) := by
  have h_eq : (fun x : E => c *
      (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
      (diffQuot k h u x)^2) =
      (fun x : E => c * ((Set.indicator (tsupport η)
        (fun _ : E => (1 : ℝ)) x) * (diffQuot k h u x)^2)) := by
    funext x; ring
  rw [h_eq, integral_const_mul]
  congr 1
  rw [show (fun x : E => (Set.indicator (tsupport η)
        (fun _ : E => (1 : ℝ)) x) * (diffQuot k h u x)^2) =
      (fun x : E => Set.indicator (tsupport η)
        (fun y : E => (diffQuot k h u y)^2) x) from by
    funext x
    by_cases hx : x ∈ tsupport η
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]; ring
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; ring]
  rw [MeasureTheory.integral_indicator (isClosed_tsupport η).measurableSet]

private lemma integrable_eta_sq_diffQuot_g_sq
    {g : Fin d → E → ℝ}
    (hg_l2 : ∀ i, MemLp (g i) 2 (volume : Measure E))
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (i k : Fin d) (h : ℝ) :
    Integrable (fun x : E => (η x)^2 *
      (diffQuot k h (g i) x)^2)
      (volume : Measure E) := by
  have hint := integrable_const_eta_sq_diffQuot_g_sq (d := d) hg_l2 hη hη_support i k h 1
  have h_eq : (fun x : E => (η x)^2 * (diffQuot k h (g i) x)^2) =
      fun x : E => 1 * (η x)^2 * (diffQuot k h (g i) x)^2 := by
    funext x; ring
  rw [h_eq]
  exact hint

variable [NeZero d] in
theorem cross_1_bound_nonsmooth_quantitative
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ}
    (hu_l2 : MemLp u 2 (volume : Measure E))
    {g : Fin d → E → ℝ}
    (hg_l2 : ∀ i, MemLp (g i) 2 (volume : Measure E))
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (h_fderiv_eta : ∀ x : E, ‖fderiv ℝ η x‖ ≤ N)
    {Ω' : Set E}
    (hΩ'_compact : IsCompact (closure Ω'))
    {R₀ : ℝ}
    (hh_support_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (k : Fin d)
    (h_FK_diffQuot_u_bound : ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E) ≤
        ∫ x in Ω', ∑ i : Fin d, ((g i) x) ^ 2 ∂(volume : Measure E))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ ⦃h : ℝ⦄, h ≠ 0 → |h| ≤ R₀ →
      |- ∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
            (Sobolev.translate k h
              (fun y : E => B.a y i j)) x *
            (η x) *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            Sobolev.diffQuot k h (g i) x *
            Sobolev.diffQuot k h u x
          ∂(volume : Measure E)| ≤
        ε * ∫ x, (η x)^2 *
            ∑ i : Fin d,
              Sobolev.diffQuot k h (g i) x ^ 2
          ∂(volume : Measure E) +
        ((1 / (ε / (Fintype.card (Fin d) : ℝ)))
            * (Classical.choose
                (SmoothEllipticBilinearForm.bounded_a_on_compact
                  (d := d) B hΩ'_compact))^2
            * N^2 * (Fintype.card (Fin d) : ℝ)^2) * ∫ x in Ω',
            ∑ i : Fin d, ((g i) x) ^ 2
          ∂(volume : Measure E) := by
  classical
  set Λ : ℝ := Classical.choose
    (SmoothEllipticBilinearForm.bounded_a_on_compact (d := d) B hΩ'_compact)
    with hΛ_eq
  have hΛ_nn : 0 ≤ Λ :=
    (Classical.choose_spec
      (SmoothEllipticBilinearForm.bounded_a_on_compact (d := d) B hΩ'_compact)).1
  have hΛ : ∀ i j : Fin d, ∀ x ∈ closure Ω', |B.a x i j| ≤ Λ :=
    (Classical.choose_spec
      (SmoothEllipticBilinearForm.bounded_a_on_compact (d := d) B hΩ'_compact)).2
  set d_real : ℝ := (Fintype.card (Fin d) : ℝ) with hd_real
  have hd_pos : 0 < d_real := by
    rw [hd_real]; exact_mod_cast Fintype.card_pos
  have hd_nn : 0 ≤ d_real := hd_pos.le
  have hε'_pos : 0 < ε / d_real := div_pos hε hd_pos
  set C : ℝ := (1 / (ε / d_real)) * Λ^2 * N^2 * d_real^2 with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    refine mul_nonneg (mul_nonneg (mul_nonneg ?_ (sq_nonneg _)) (sq_nonneg _))
      (sq_nonneg _)
    exact (one_div_pos.mpr hε'_pos).le
  intro h hh hh_le
  have h_thick_in_Ω' : Metric.cthickening |h| (tsupport η) ⊆ Ω' := hh_support_in_Ω' hh_le
  have h_each_pointwise := fun (i j : Fin d) (x : E) =>
    cross_1_pointwise_bound_nonsmooth (d := d) B u g hη_range h_fderiv_eta
      hΛ i j k h_thick_in_Ω' hε'_pos x
  set S : ℝ := ∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
        translate k h (fun y : E => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        diffQuot k h (g i) x *
        diffQuot k h u x
      ∂(volume : Measure E) with hS_def
  rw [abs_neg]
  have h_abs_sum : |S| ≤
      ∑ i : Fin d, ∑ j : Fin d, |∫ x, 2 *
          translate k h (fun y : E => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          diffQuot k h (g i) x *
          diffQuot k h u x
        ∂(volume : Measure E)| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum ?_
    intro i _
    exact Finset.abs_sum_le_sum_abs _ _
  refine h_abs_sum.trans ?_
  have h_integrand_int : ∀ i j : Fin d, Integrable (fun x : E =>
      2 * translate k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        diffQuot k h (g i) x *
        diffQuot k h u x) volume :=
    fun i j => integrable_cross_1_summand_nonsmooth (d := d) B hu_l2 hg_l2 hη
      hη_support i j k h
  have h_first_int : ∀ i : Fin d, Integrable (fun x : E =>
      (ε / d_real) * (η x)^2 *
        (diffQuot k h (g i) x)^2) volume :=
    fun i => integrable_const_eta_sq_diffQuot_g_sq hg_l2 hη hη_support
      i k h (ε / d_real)
  have h_indicator_int : Integrable (fun x : E =>
      (1 / (ε / d_real)) * Λ^2 * N^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2) volume :=
    integrable_const_indicator_diffQuot_u_sq hu_l2 hη_support
      k h ((1 / (ε / d_real)) * Λ^2 * N^2)
  have h_pt_bound_int : ∀ i j : Fin d, Integrable (fun x : E =>
      (ε / d_real) * (η x)^2 *
        (diffQuot k h (g i) x)^2 +
      (1 / (ε / d_real)) * Λ^2 * N^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2) volume :=
    fun i _ => (h_first_int i).add h_indicator_int
  have h_per_pair_bound : ∀ i j : Fin d,
      |∫ x, 2 * translate k h (fun y => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          diffQuot k h (g i) x *
          diffQuot k h u x ∂(volume : Measure E)| ≤
      ∫ x, ((ε / d_real) * (η x)^2 *
        (diffQuot k h (g i) x)^2 +
      (1 / (ε / d_real)) * Λ^2 * N^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2) ∂(volume : Measure E) := by
    intro i j
    have h_tri := abs_integral_le_integral_abs (μ := (volume : Measure E))
      (f := fun x : E => 2 * translate k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        diffQuot k h (g i) x *
        diffQuot k h u x)
    refine h_tri.trans ?_
    refine integral_mono_ae ((h_integrand_int i j).abs) (h_pt_bound_int i j) ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    exact h_each_pointwise i j x
  have h_outer_sum :
      ∑ i : Fin d, ∑ j : Fin d, |∫ x, 2 *
          translate k h (fun y => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          diffQuot k h (g i) x *
          diffQuot k h u x ∂(volume : Measure E)| ≤
      ∑ i : Fin d, ∑ j : Fin d,
        ∫ x, ((ε / d_real) * (η x)^2 *
          (diffQuot k h (g i) x)^2 +
        (1 / (ε / d_real)) * Λ^2 * N^2 *
          (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
          (diffQuot k h u x)^2) ∂(volume : Measure E) :=
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
      h_per_pair_bound i j))
  refine h_outer_sum.trans ?_
  have h_total_eq :
      ∑ i : Fin d, ∑ j : Fin d,
        ∫ x, ((ε / d_real) * (η x)^2 *
          (diffQuot k h (g i) x)^2 +
        (1 / (ε / d_real)) * Λ^2 * N^2 *
          (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
          (diffQuot k h u x)^2) ∂(volume : Measure E) =
      ε * ∫ x, (η x)^2 *
          ∑ i : Fin d, (diffQuot k h (g i) x)^2
        ∂(volume : Measure E) +
      d_real^2 * ((1 / (ε / d_real)) * Λ^2 * N^2 *
        ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E)) := by
    have h_per_ij : ∀ i j : Fin d,
        ∫ x, ((ε / d_real) * (η x)^2 *
            (diffQuot k h (g i) x)^2 +
          (1 / (ε / d_real)) * Λ^2 * N^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2) ∂(volume : Measure E) =
        ∫ x, (ε / d_real) * (η x)^2 *
            (diffQuot k h (g i) x)^2 ∂(volume : Measure E) +
        ∫ x, (1 / (ε / d_real)) * Λ^2 * N^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2 ∂(volume : Measure E) := by
      intro i j
      rw [integral_add (h_first_int i) h_indicator_int]
    rw [show (∑ i : Fin d, ∑ j : Fin d,
        ∫ x, ((ε / d_real) * (η x)^2 *
          (diffQuot k h (g i) x)^2 +
        (1 / (ε / d_real)) * Λ^2 * N^2 *
          (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
          (diffQuot k h u x)^2) ∂(volume : Measure E)) =
        ∑ i : Fin d, ∑ j : Fin d,
          (∫ x, (ε / d_real) * (η x)^2 *
              (diffQuot k h (g i) x)^2 ∂(volume : Measure E) +
          ∫ x, (1 / (ε / d_real)) * Λ^2 * N^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E)) from
          Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
            (fun j _ => h_per_ij i j))]
    have h_step_b : ∀ i : Fin d, ∑ _j : Fin d,
          (∫ x, (ε / d_real) * (η x)^2 *
              (diffQuot k h (g i) x)^2 ∂(volume : Measure E) +
          ∫ x, (1 / (ε / d_real)) * Λ^2 * N^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E)) =
        d_real * (∫ x, (ε / d_real) * (η x)^2 *
              (diffQuot k h (g i) x)^2 ∂(volume : Measure E) +
          ∫ x, (1 / (ε / d_real)) * Λ^2 * N^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E)) := by
      intro i
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [show (∑ i : Fin d, ∑ _j : Fin d,
          (∫ x, (ε / d_real) * (η x)^2 *
              (diffQuot k h (g i) x)^2 ∂(volume : Measure E) +
          ∫ x, (1 / (ε / d_real)) * Λ^2 * N^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E))) =
        ∑ i : Fin d, d_real * (∫ x, (ε / d_real) * (η x)^2 *
              (diffQuot k h (g i) x)^2 ∂(volume : Measure E) +
          ∫ x, (1 / (ε / d_real)) * Λ^2 * N^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E)) from
        Finset.sum_congr rfl (fun i _ => h_step_b i)]
    rw [← Finset.mul_sum]
    rw [Finset.sum_add_distrib]
    rw [show (∑ _i : Fin d, ∫ x, (1 / (ε / d_real)) * Λ^2 * N^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2 ∂(volume : Measure E)) =
        d_real * ∫ x, (1 / (ε / d_real)) * Λ^2 * N^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2 ∂(volume : Measure E)
        from by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]]
    have h_indicator_eq := integral_const_indicator_eq (d := d) k h η
      ((1 / (ε / d_real)) * Λ^2 * N^2) (u := u)
    rw [h_indicator_eq]
    have h_eta_sq_diffQuot_int : ∀ i : Fin d,
        ∫ x, (ε / d_real) * (η x)^2 *
            (diffQuot k h (g i) x)^2 ∂(volume : Measure E) =
        (ε / d_real) * ∫ x, (η x)^2 *
            (diffQuot k h (g i) x)^2 ∂(volume : Measure E) := by
      intro i
      rw [show (fun x : E => (ε / d_real) * (η x)^2 *
            (diffQuot k h (g i) x)^2) =
          fun x : E => (ε / d_real) * ((η x)^2 *
            (diffQuot k h (g i) x)^2) from by funext x; ring]
      rw [integral_const_mul]
    rw [show (∑ i : Fin d, ∫ x, (ε / d_real) * (η x)^2 *
              (diffQuot k h (g i) x)^2 ∂(volume : Measure E)) =
        ∑ i : Fin d, (ε / d_real) * ∫ x, (η x)^2 *
              (diffQuot k h (g i) x)^2 ∂(volume : Measure E) from
        Finset.sum_congr rfl (fun i _ => h_eta_sq_diffQuot_int i)]
    rw [← Finset.mul_sum]
    have h_first_int_per : ∀ i : Fin d, Integrable (fun x : E =>
        (η x)^2 * (diffQuot k h (g i) x)^2) volume :=
      fun i => integrable_eta_sq_diffQuot_g_sq (d := d) hg_l2 hη hη_support i k h
    have h_swap_sum : ∑ i : Fin d, ∫ x, (η x)^2 *
            (diffQuot k h (g i) x)^2 ∂(volume : Measure E) =
        ∫ x, (η x)^2 *
            ∑ i : Fin d, (diffQuot k h (g i) x)^2 ∂(volume : Measure E) := by
      rw [← integral_finsetSum _ (fun i _ => h_first_int_per i)]
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [Finset.mul_sum]
    rw [h_swap_sum]
    rw [mul_add]
    congr 1
    · rw [← mul_assoc, mul_div_cancel₀ _ (ne_of_gt hd_pos)]
    · ring
  rw [h_total_eq]
  have h_diffQuot_sq_le := h_FK_diffQuot_u_bound hh hh_le
  have h_factor_nn : 0 ≤ (1 / (ε / d_real)) * Λ^2 * N^2 := by
    refine mul_nonneg (mul_nonneg ?_ (sq_nonneg _)) (sq_nonneg _)
    exact (one_div_pos.mpr hε'_pos).le
  have h_d_real_sq_nn : 0 ≤ d_real^2 := sq_nonneg _
  have h_C_eq : C = d_real^2 * ((1 / (ε / d_real)) * Λ^2 * N^2) := by
    rw [hC_def]; ring
  have h_combine :
      d_real^2 * ((1 / (ε / d_real)) * Λ^2 * N^2 *
          ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E)) ≤
      C * ∫ x in Ω',
          ∑ i : Fin d, ((g i) x) ^ 2
        ∂(volume : Measure E) := by
    rw [show d_real^2 * ((1 / (ε / d_real)) * Λ^2 * N^2 *
          ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E)) =
        (d_real^2 * ((1 / (ε / d_real)) * Λ^2 * N^2)) *
          ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E)
        from by ring, ← h_C_eq]
    refine mul_le_mul_of_nonneg_left h_diffQuot_sq_le ?_
    rw [h_C_eq]; exact mul_nonneg h_d_real_sq_nn h_factor_nn
  linarith

end Sobolev.NirenbergCrossBoundsNonSmooth
