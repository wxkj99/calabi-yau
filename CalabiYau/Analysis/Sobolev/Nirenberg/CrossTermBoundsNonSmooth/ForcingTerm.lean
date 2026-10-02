-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Nirenberg/CrossTermBoundsNonSmooth/ForcingTerm.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Nirenberg.MasterInequality.Coercivity
public import CalabiYau.Analysis.Sobolev.Nirenberg.MasterInequality.CrossBoundsSummandContinuityIntegrability
public import CalabiYau.Analysis.Sobolev.Nirenberg.MasterInequality.CrossBoundsPointwiseProductBounds
public import CalabiYau.Analysis.Sobolev.Nirenberg.CrossTermBoundsNonSmooth.CrossBoundsNonSmooth
public import CalabiYau.Analysis.Sobolev.Nirenberg.CrossTermBoundsNonSmooth.CoefficientDifferenceQuotient
public import CalabiYau.Analysis.Sobolev.Nirenberg.TestFunction.CutoffDiffQuot
public import CalabiYau.Analysis.Sobolev.Tools.DifferenceQuotient

@[expose] public section

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open Sobolev
open Sobolev.NirenbergEuclidean
open Sobolev.NirenbergCrossBounds
open Sobolev.NirenbergCrossBoundsNonSmooth
open scoped ENNReal NNReal Convolution Pointwise BigOperators InnerProductSpace

namespace Sobolev.NirenbergCrossBoundsNonSmooth

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

private lemma nirenbergTestFunction_tsupport_subset_of_thickening_nonsmooth_fterm
    {u : E → ℝ}
    {η : E → ℝ}
    {Ω' : Set E}
    {R₀ : ℝ}
    (hh_support_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (k : Fin d) {h : ℝ} (hh_le : |h| ≤ R₀) :
    tsupport
      (Sobolev.NirenbergTestFunction.nirenbergTestFunction
        k h η u) ⊆ Ω' :=
  (Sobolev.NirenbergTestFunction.tsupport_nirenbergTestFunction_subset
    (d := d) η u k h).trans (hh_support_in_Ω' hh_le)

private lemma hasCompactSupport_v_test_nonsmooth_fterm
    {η : E → ℝ} (hη_support : HasCompactSupport η)
    {u : E → ℝ} (k : Fin d) (h : ℝ) :
    HasCompactSupport
      (Sobolev.NirenbergTestFunction.nirenbergTestFunction
        k h η u) :=
  NirenbergTestFunction.hasCompactSupport_nirenbergTestFunction
    hη_support k h

private lemma memLp_eta_sq_diffQuot_u_fterm
    {u : E → ℝ} (hu_l2 : MemLp u 2 (volume : Measure E))
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (k : Fin d) (h : ℝ) :
    MemLp (fun x : E => (η x) ^ 2 * diffQuot k h u x) 2
      (volume : Measure E) := by
  classical
  have hη_sq_cont : Continuous (fun x : E => (η x) ^ 2) := hη.continuous.pow 2
  have hη_sq_support : HasCompactSupport (fun x : E => (η x) ^ 2) := by
    have heq : (fun y : E => η y ^ 2) = (fun y : E => η y * η y) := by
      funext y; ring
    rw [heq]; exact hη_support.mul_right
  obtain ⟨M, _, hM⟩ :=
    exists_bound_of_continuous_compactSupport hη_sq_cont hη_sq_support
  have h_dq_l2 : MemLp (diffQuot k h u) 2 (volume : Measure E) :=
    memLp_diffQuot_two k h hu_l2
  exact memLp_bounded_mul hη_sq_cont.aestronglyMeasurable hM h_dq_l2

private lemma memLp_v_test_nonsmooth_fterm
    {u : E → ℝ} (hu_l2 : MemLp u 2 (volume : Measure E))
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (k : Fin d) (h : ℝ) :
    MemLp
      (Sobolev.NirenbergTestFunction.nirenbergTestFunction
        k h η u) 2 (volume : Measure E) := by
  classical
  have h_inner : MemLp (fun x : E => (η x) ^ 2 * diffQuot k h u x) 2
      (volume : Measure E) :=
    memLp_eta_sq_diffQuot_u_fterm (d := d) hu_l2 hη hη_support k h
  have h_eq :
      Sobolev.NirenbergTestFunction.nirenbergTestFunction
        k h η u =
      diffQuot k (-h) (fun x : E => (η x) ^ 2 * diffQuot k h u x) := rfl
  rw [h_eq]
  exact memLp_diffQuot_two k (-h) h_inner

private lemma pointwise_young_f_v_test
    (f : E → ℝ) (v_test : E → ℝ) {ε : ℝ} (hε : 0 < ε) (x : E) :
    |f x * v_test x| ≤ (ε/2) * (v_test x) ^ 2 + (1/(2*ε)) * (f x) ^ 2 := by
  have h_y := Sobolev.NirenbergCrossBounds.two_abs_mul_le_eps_sq_add (v_test x) (f x) ε hε
  have h_abs_eq : |f x * v_test x| = |v_test x| * |f x| := by
    rw [show (f x * v_test x) = v_test x * f x from by ring, abs_mul]
  rw [h_abs_eq]
  have h_div_eq : (1 / ε) * (f x) ^ 2 = 2 * ((1 / (2 * ε)) * (f x) ^ 2) := by
    have hε_ne : ε ≠ 0 := ne_of_gt hε
    field_simp
  have h_ε_eq : ε * (v_test x) ^ 2 = 2 * ((ε / 2) * (v_test x) ^ 2) := by ring
  linarith [h_y, h_div_eq, h_ε_eq]

private lemma pointwise_half_sum_f_v_test
    (f v_test : E → ℝ) (x : E) :
    |f x * v_test x| ≤ (1/2) * ((f x) ^ 2 + (v_test x) ^ 2) := by
  have h_y := Sobolev.NirenbergCrossBounds.two_abs_mul_le_eps_sq_add (f x) (v_test x) 1 zero_lt_one
  simp only [one_mul, div_one] at h_y
  have h_abs : |f x * v_test x| = |f x| * |v_test x| := abs_mul _ _
  linarith

theorem forcing_term_bound_nonsmooth_quantitative
    {Ω : Set E}
    {f : E → ℝ} (hf_l2_local : ∀ {Ω' : Set E}, IsCompact (closure Ω') →
      MemLp f 2 (volume.restrict Ω'))
    {u : E → ℝ}
    (hu_l2 : MemLp u 2 (volume : Measure E))
    {g : Fin d → E → ℝ}
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    {N : ℝ}
    {Ω' : Set E} (hΩ'_closure : closure Ω' ⊆ Ω)
    (hΩ'_compact : IsCompact (closure Ω'))
    {R₀ : ℝ}
    (hh_support_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (k : Fin d)
    (h_FK_diffQuot_u_bound : ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      ∫ x in tsupport η,
          (Sobolev.diffQuot k h u x) ^ 2
        ∂(volume : Measure E) ≤
        ∫ x in Ω', ∑ i : Fin d, ((g i) x) ^ 2 ∂(volume : Measure E))
    (h_v_test_l2_bound : ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      ∫ x, (Sobolev.NirenbergTestFunction.nirenbergTestFunction
            k h η u x) ^ 2 ∂(volume : Measure E) ≤
        8 * N ^ 2 *
          ∫ x in tsupport η,
              (Sobolev.diffQuot k h u x) ^ 2
            ∂(volume : Measure E) +
        2 * ∫ x, (η x) ^ 2 *
            ∑ i : Fin d,
              (Sobolev.diffQuot k h (g i) x) ^ 2
          ∂(volume : Measure E))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ ⦃h : ℝ⦄, h ≠ 0 → |h| ≤ R₀ →
      |∫ x in Ω, f x *
          Sobolev.NirenbergTestFunction.nirenbergTestFunction
            k h η u x| ≤
        ε * ∫ x, (η x) ^ 2 *
            ∑ i : Fin d,
              Sobolev.diffQuot k h (g i) x ^ 2
          ∂(volume : Measure E) +
        (max (4 * ε * N ^ 2) (1 / (2 * ε))) * (∫ x in Ω',
              ∑ i : Fin d, ((g i) x) ^ 2
            ∂(volume : Measure E) +
          ∫ x in Ω', (f x) ^ 2 ∂(volume : Measure E)) := by
  classical
  set C : ℝ := max (4 * ε * N ^ 2) (1 / (2 * ε)) with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    refine le_max_of_le_left ?_
    refine mul_nonneg ?_ (sq_nonneg _)
    exact mul_nonneg (by linarith) hε.le
  intro h hh hh_le
  have h_thick_in_Ω' : Metric.cthickening |h| (tsupport η) ⊆ Ω' := hh_support_in_Ω' hh_le
  set v_test : E → ℝ :=
    Sobolev.NirenbergTestFunction.nirenbergTestFunction
      k h η u with hv_test_def
  have h_v_test_support : tsupport v_test ⊆ Ω' :=
    nirenbergTestFunction_tsupport_subset_of_thickening_nonsmooth_fterm (d := d) hh_support_in_Ω' k hh_le
  have h_v_test_support_cmp : HasCompactSupport v_test :=
    hasCompactSupport_v_test_nonsmooth_fterm (d := d) hη_support k h
  have h_v_test_memLp : MemLp v_test 2 (volume : Measure E) :=
    memLp_v_test_nonsmooth_fterm (d := d) hu_l2 hη hη_support k h
  have h_v_test_zero_outside : ∀ x ∉ Ω, v_test x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport
      (fun hy => hx (hΩ'_closure (subset_closure (h_v_test_support hy))))
  have h_v_test_zero_outside_Ω' : ∀ x ∉ Ω', v_test x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hy => hx (h_v_test_support hy))
  have hf_memLp : MemLp f 2 (volume.restrict Ω') := hf_l2_local hΩ'_compact
  have hf_sq_int_Ω' : IntegrableOn (fun x : E => (f x) ^ 2) Ω' volume :=
    hf_memLp.integrable_sq
  have h_int_E : ∫ x in Ω, f x * v_test x ∂(volume : Measure E) =
      ∫ x in Ω', f x * v_test x ∂(volume : Measure E) := by
    have h_eq_zero_Ω : ∀ x, x ∉ Ω → f x * v_test x = 0 := by
      intro x hx; rw [h_v_test_zero_outside x hx]; ring
    have h_eq_zero_Ω' : ∀ x, x ∉ Ω' → f x * v_test x = 0 := by
      intro x hx; rw [h_v_test_zero_outside_Ω' x hx]; ring
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero h_eq_zero_Ω,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero h_eq_zero_Ω']
  rw [h_int_E]
  have h_pointwise : ∀ x : E,
      |f x * v_test x| ≤ (ε/2) * (v_test x) ^ 2 + (1/(2*ε)) * (f x) ^ 2 :=
    pointwise_young_f_v_test (d := d) f v_test hε
  have h_v_test_sq_int_E : Integrable (fun x : E => (v_test x) ^ 2)
      (volume : Measure E) := by
    have h_norm_sq_int : Integrable
        (fun x : E => ‖v_test x‖ ^ (2 : ℕ)) (volume : Measure E) := by
      have hh' := h_v_test_memLp.integrable_norm_rpow
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      have h_pow_eq : (2 : ℝ≥0∞).toReal = 2 := by
        show ENNReal.toReal 2 = 2; rfl
      rw [h_pow_eq] at hh'
      have heq : (fun x : E => ‖v_test x‖ ^ (2 : ℝ)) =
          (fun x : E => ‖v_test x‖ ^ (2 : ℕ)) := by
        funext x
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_cast, Real.rpow_natCast]
      rw [heq] at hh'
      exact hh'
    have heq2 : (fun x : E => (v_test x) ^ 2) =
        (fun x : E => ‖v_test x‖ ^ (2 : ℕ)) := by
      funext x
      rw [Real.norm_eq_abs, sq_abs]
    rw [heq2]
    exact h_norm_sq_int
  have h_v_test_sq_int_Ω' : IntegrableOn (fun x : E => (v_test x) ^ 2) Ω' volume :=
    h_v_test_sq_int_E.integrableOn
  have h_f_v_int_Ω' : IntegrableOn (fun x : E => f x * v_test x) Ω' volume := by
    have h_pointwise_abs : ∀ x : E,
        |f x * v_test x| ≤ (1/2) * ((f x) ^ 2 + (v_test x) ^ 2) :=
      pointwise_half_sum_f_v_test (d := d) f v_test
    have h_rhs_int : IntegrableOn (fun x : E => (1/2) * ((f x) ^ 2 + (v_test x) ^ 2)) Ω' volume :=
      (hf_sq_int_Ω'.add h_v_test_sq_int_Ω').const_mul (1/2)
    have h_f_AEStrong : AEStronglyMeasurable f (volume.restrict Ω') :=
      hf_memLp.aestronglyMeasurable
    have h_v_AEStrong : AEStronglyMeasurable v_test (volume.restrict Ω') :=
      h_v_test_memLp.aestronglyMeasurable.restrict
    have h_prod_AEStrong : AEStronglyMeasurable (fun x : E => f x * v_test x)
        (volume.restrict Ω') := h_f_AEStrong.mul h_v_AEStrong
    refine ⟨h_prod_AEStrong, ?_⟩
    refine HasFiniteIntegral.mono' h_rhs_int.hasFiniteIntegral ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    rw [Real.norm_eq_abs]
    exact h_pointwise_abs x
  have h_rhs_int_Ω' : IntegrableOn (fun x : E =>
      (ε/2) * (v_test x) ^ 2 + (1/(2*ε)) * (f x) ^ 2) Ω' volume := by
    refine (h_v_test_sq_int_Ω'.const_mul (ε/2)).add (hf_sq_int_Ω'.const_mul (1/(2*ε)))
  have h_step1 : |∫ x in Ω', f x * v_test x ∂(volume : Measure E)| ≤
      ∫ x in Ω', |f x * v_test x| ∂(volume : Measure E) :=
    abs_integral_le_integral_abs (μ := (volume : Measure E).restrict Ω')
  have h_step2 : ∫ x in Ω', |f x * v_test x| ∂(volume : Measure E) ≤
      ∫ x in Ω', ((ε/2) * (v_test x) ^ 2 + (1/(2*ε)) * (f x) ^ 2) ∂(volume : Measure E) := by
    refine integral_mono_ae h_f_v_int_Ω'.abs h_rhs_int_Ω' ?_
    refine Filter.Eventually.of_forall ?_
    intro x; exact h_pointwise x
  refine (h_step1.trans h_step2).trans ?_
  rw [integral_add (h_v_test_sq_int_Ω'.const_mul (ε/2)) (hf_sq_int_Ω'.const_mul (1/(2*ε)))]
  rw [integral_const_mul, integral_const_mul]
  have h_v_test_sq_Ω'_le_E :
      ∫ x in Ω', (v_test x) ^ 2 ∂(volume : Measure E) ≤
      ∫ x, (v_test x) ^ 2 ∂(volume : Measure E) := by
    have h_v_test_sq_eq : ∫ x, (v_test x) ^ 2 ∂(volume : Measure E) =
        ∫ x in Ω', (v_test x) ^ 2 ∂(volume : Measure E) := by
      have h_eq_zero : ∀ x, x ∉ Ω' → (v_test x) ^ 2 = 0 := by
        intro x hx
        rw [h_v_test_zero_outside_Ω' x hx]; ring
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero h_eq_zero).symm
    rw [h_v_test_sq_eq]
  have h_v_test_bound := h_v_test_l2_bound hh hh_le
  have h_v_sq_le_8N_2I :
      ∫ x in Ω', (v_test x) ^ 2 ∂(volume : Measure E) ≤
        8 * N ^ 2 *
          ∫ x in tsupport η, (diffQuot k h u x) ^ 2 ∂(volume : Measure E) +
        2 * ∫ x, (η x) ^ 2 *
            ∑ i : Fin d, (diffQuot k h (g i) x) ^ 2
          ∂(volume : Measure E) :=
    h_v_test_sq_Ω'_le_E.trans h_v_test_bound
  have h_diff_bound :
      ∫ x in tsupport η, (diffQuot k h u x) ^ 2 ∂(volume : Measure E) ≤
        ∫ x in Ω', ∑ i : Fin d, ((g i) x) ^ 2
          ∂(volume : Measure E) :=
    h_FK_diffQuot_u_bound hh hh_le
  have h_gradL2_nn : 0 ≤ ∫ x in Ω',
        ∑ i : Fin d, ((g i) x) ^ 2
          ∂(volume : Measure E) :=
    integral_nonneg (fun x => Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have h_fL2_nn : 0 ≤ ∫ x in Ω', (f x) ^ 2 ∂(volume : Measure E) :=
    integral_nonneg (fun x => sq_nonneg _)
  have h_v_full_bound :
      (ε/2) * ∫ x in Ω', (v_test x) ^ 2 ∂(volume : Measure E) ≤
      4 * ε * N ^ 2 *
        ∫ x in Ω', ∑ i : Fin d, ((g i) x) ^ 2
          ∂(volume : Measure E) +
      ε * ∫ x, (η x) ^ 2 *
          ∑ i : Fin d, (diffQuot k h (g i) x) ^ 2
        ∂(volume : Measure E) := by
    have h_step_a := mul_le_mul_of_nonneg_left h_v_sq_le_8N_2I (by linarith : 0 ≤ ε/2)
    have h_step_b : (ε/2) * (8 * N ^ 2 *
            ∫ x in tsupport η, (diffQuot k h u x) ^ 2 ∂(volume : Measure E) +
          2 * ∫ x, (η x) ^ 2 *
            ∑ i : Fin d, (diffQuot k h (g i) x) ^ 2
            ∂(volume : Measure E)) ≤
        4 * ε * N ^ 2 *
            ∫ x in Ω', ∑ i : Fin d, ((g i) x) ^ 2
              ∂(volume : Measure E) +
        ε * ∫ x, (η x) ^ 2 *
            ∑ i : Fin d, (diffQuot k h (g i) x) ^ 2
            ∂(volume : Measure E) := by
      have h1 : (ε/2) * (8 * N ^ 2 *
            ∫ x in tsupport η, (diffQuot k h u x) ^ 2 ∂(volume : Measure E)) =
          4 * ε * N ^ 2 *
            ∫ x in tsupport η, (diffQuot k h u x) ^ 2 ∂(volume : Measure E) := by ring
      have h2 : (ε/2) * (2 * ∫ x, (η x) ^ 2 *
            ∑ i : Fin d, (diffQuot k h (g i) x) ^ 2
            ∂(volume : Measure E)) =
          ε * ∫ x, (η x) ^ 2 *
            ∑ i : Fin d, (diffQuot k h (g i) x) ^ 2
            ∂(volume : Measure E) := by ring
      have h_diff_pos : 0 ≤ 4 * ε * N ^ 2 := by
        refine mul_nonneg ?_ (sq_nonneg _)
        exact mul_nonneg (by linarith) hε.le
      have h_step_c : 4 * ε * N ^ 2 *
            ∫ x in tsupport η, (diffQuot k h u x) ^ 2 ∂(volume : Measure E) ≤
          4 * ε * N ^ 2 *
            ∫ x in Ω', ∑ i : Fin d, ((g i) x) ^ 2
              ∂(volume : Measure E) :=
        mul_le_mul_of_nonneg_left h_diff_bound h_diff_pos
      linarith [h1, h2]
    linarith
  have h_C_grad_le : 4 * ε * N ^ 2 ≤ C := le_max_left _ _
  have h_C_fL2_le : 1 / (2 * ε) ≤ C := le_max_right _ _
  have h_combine :
      4 * ε * N ^ 2 *
          ∫ x in Ω', ∑ i : Fin d, ((g i) x) ^ 2
            ∂(volume : Measure E) +
      (1 / (2 * ε)) * ∫ x in Ω', (f x) ^ 2 ∂(volume : Measure E) ≤
      C * (∫ x in Ω', ∑ i : Fin d, ((g i) x) ^ 2
              ∂(volume : Measure E) +
          ∫ x in Ω', (f x) ^ 2 ∂(volume : Measure E)) := by
    have h_left_le := mul_le_mul_of_nonneg_right h_C_grad_le h_gradL2_nn
    have h_right_le := mul_le_mul_of_nonneg_right h_C_fL2_le h_fL2_nn
    have h_C_dist : C * (∫ x in Ω', ∑ i : Fin d, ((g i) x) ^ 2
              ∂(volume : Measure E) +
          ∫ x in Ω', (f x) ^ 2 ∂(volume : Measure E)) =
        C * (∫ x in Ω', ∑ i : Fin d, ((g i) x) ^ 2
              ∂(volume : Measure E)) +
        C * ∫ x in Ω', (f x) ^ 2 ∂(volume : Measure E) := by ring
    linarith
  linarith

end Sobolev.NirenbergCrossBoundsNonSmooth
