-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Nirenberg/CrossTermBoundsNonSmooth/CrossBoundsNonSmoothCTerm.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Nirenberg.MasterInequality.Coercivity
public import CalabiYau.Analysis.Sobolev.Nirenberg.MasterInequality.CrossBoundsSummandContinuityIntegrability
public import CalabiYau.Analysis.Sobolev.Nirenberg.MasterInequality.CrossBoundsPointwiseProductBounds
public import CalabiYau.Analysis.Sobolev.Nirenberg.CrossTermBoundsNonSmooth.CrossBoundsNonSmooth
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

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private lemma memLp_two_v_test
    {u : E → ℝ} (hu_l2 : MemLp u 2 (volume : Measure E))
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (k : Fin d) (h : ℝ) :
    MemLp (Sobolev.NirenbergTestFunction.nirenbergTestFunction
        k h η u) 2 (volume : Measure E) := by
  classical
  set gFun : E → ℝ := fun y : E => (η y) ^ 2 *
    Sobolev.diffQuot k h u y with hgFun_def
  have hη_sq_cont : Continuous (fun x : E => (η x) ^ 2) := hη.continuous.pow 2
  have hη_sq_support : HasCompactSupport (fun x : E => (η x) ^ 2) := by
    have heq : (fun y : E => η y ^ 2) = (fun y : E => η y * η y) := by
      funext y; ring
    rw [heq]; exact hη_support.mul_right
  obtain ⟨Mη, hMη_nn, hMη⟩ :=
    exists_bound_of_continuous_compactSupport hη_sq_cont hη_sq_support
  have h_dqu_l2 : MemLp (Sobolev.diffQuot k h u) 2
      (volume : Measure E) := memLp_diffQuot_two k h hu_l2
  have h_gFun_l2 : MemLp gFun 2 (volume : Measure E) :=
    memLp_bounded_mul hη_sq_cont.aestronglyMeasurable hMη h_dqu_l2
  have h_v_eq : Sobolev.NirenbergTestFunction.nirenbergTestFunction
      k h η u =
      Sobolev.diffQuot k (-h) gFun := rfl
  rw [h_v_eq]
  exact memLp_diffQuot_two k (-h) h_gFun_l2

omit [NeZero d] in
private lemma aestronglyMeasurable_v_test
    {u : E → ℝ} (hu_l2 : MemLp u 2 (volume : Measure E))
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (k : Fin d) (h : ℝ) :
    AEStronglyMeasurable
      (Sobolev.NirenbergTestFunction.nirenbergTestFunction
        k h η u) (volume : Measure E) := by
  have hη_sq_cont : Continuous (fun x : E => (η x) ^ 2) := hη.continuous.pow 2
  have h_dqu_aesm : AEStronglyMeasurable
      (Sobolev.diffQuot k h u)
      (volume : Measure E) :=
    aestronglyMeasurable_diffQuot (d := d) k h hu_l2.aestronglyMeasurable
  have h_g_aesm : AEStronglyMeasurable
      (fun y : E => (η y) ^ 2 *
        Sobolev.diffQuot k h u y)
      (volume : Measure E) :=
    hη_sq_cont.aestronglyMeasurable.mul h_dqu_aesm
  exact aestronglyMeasurable_diffQuot (d := d) k (-h) h_g_aesm

theorem c_term_bound_nonsmooth_quantitative
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ}
    (hu_l2 : MemLp u 2 (volume : Measure E))
    {g : Fin d → E → ℝ}
    (hg_l2 : ∀ i, MemLp (g i) 2 (volume : Measure E))
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    {N : ℝ}
    {Ω' : Set E} (hΩ' : IsOpen Ω') (hΩ'_closure : closure Ω' ⊆ Ω)
    (hΩ'_compact : IsCompact (closure Ω'))
    {R₀ : ℝ}
    (hh_support_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (k : Fin d) (ε : ℝ) (hε : 0 < ε)
    (h_v_test_sq_bound : ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      ∫ x, (Sobolev.NirenbergTestFunction.nirenbergTestFunction
          k h η u x) ^ 2 ∂(volume : Measure E) ≤
        8 * N ^ 2 *
          ∫ x in tsupport η, (Sobolev.diffQuot k h u x) ^ 2
            ∂(volume : Measure E) +
        2 * ∫ x, (η x) ^ 2 *
            (Sobolev.diffQuot k h (g k) x) ^ 2
          ∂(volume : Measure E))
    (h_FK_diffQuot_u_bound : ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      ∫ x in tsupport η, (Sobolev.diffQuot k h u x) ^ 2
          ∂(volume : Measure E) ≤
        ∫ x in Ω', ∑ i : Fin d, ((g i) x) ^ 2 ∂(volume : Measure E)) :
    ∀ ⦃h : ℝ⦄, h ≠ 0 → |h| ≤ R₀ →
      |∫ x in Ω, B.c x * u x *
          Sobolev.NirenbergTestFunction.nirenbergTestFunction
            k h η u x ∂(volume : Measure E)| ≤
        ε * ∫ x, (η x) ^ 2 *
            ∑ i : Fin d, Sobolev.diffQuot k h (g i) x ^ 2
          ∂(volume : Measure E) +
        (max (4 * ε * N ^ 2)
            ((Classical.choose
                (SmoothEllipticBilinearForm.bounded_c_on_compact
                  (d := d) B hΩ'_compact)) ^ 2 / (2 * ε)))
          * (∫ x in Ω',
              ∑ i : Fin d, ((g i) x) ^ 2
            ∂(volume : Measure E) +
          ∫ x in Ω', (u x) ^ 2 ∂(volume : Measure E)) := by
  classical
  set Mc : ℝ := Classical.choose
    (SmoothEllipticBilinearForm.bounded_c_on_compact (d := d) B hΩ'_compact)
    with hMc_eq
  have hMc_nn : 0 ≤ Mc :=
    (Classical.choose_spec
      (SmoothEllipticBilinearForm.bounded_c_on_compact (d := d) B hΩ'_compact)).1
  have h_Mc : ∀ x ∈ closure Ω', |B.c x| ≤ Mc :=
    (Classical.choose_spec
      (SmoothEllipticBilinearForm.bounded_c_on_compact (d := d) B hΩ'_compact)).2
  set C : ℝ := max (4 * ε * N ^ 2) (Mc^2 / (2 * ε)) with hC_def
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
    (NirenbergTestFunction.tsupport_nirenbergTestFunction_subset
      (d := d) η u k h).trans h_thick_in_Ω'
  have h_v_test_in_Ω : tsupport v_test ⊆ Ω := fun x hx =>
    hΩ'_closure (subset_closure (h_v_test_support hx))
  have h_c_cont : Continuous B.c := B.continuous_c
  have h_v_test_aesm : AEStronglyMeasurable v_test (volume : Measure E) :=
    aestronglyMeasurable_v_test (d := d) hu_l2 hη k h
  have h_v_test_l2 : MemLp v_test 2 (volume : Measure E) :=
    memLp_two_v_test (d := d) hu_l2 hη hη_support k h
  have h_v_test_zero_outside : ∀ x ∉ Ω, v_test x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hy => hx (h_v_test_in_Ω hy))
  have h_v_test_zero_outside_Ω' : ∀ x ∉ Ω', v_test x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hy => hx (h_v_test_support hy))
  have h_uv_l1 : Integrable (fun x : E => u x * v_test x) (volume : Measure E) :=
    MemLp.integrable_mul (p := 2) (q := 2) hu_l2 h_v_test_l2
  have h_pointwise_cuv :
      ∀ x : E, |B.c x * u x * v_test x| ≤ Mc * |u x * v_test x| := by
    intro x
    by_cases hx : x ∈ Ω'
    · have hx_cl : x ∈ closure Ω' := subset_closure hx
      have h_c_le : |B.c x| ≤ Mc := h_Mc x hx_cl
      have h_uv_nn : 0 ≤ |u x * v_test x| := abs_nonneg _
      calc |B.c x * u x * v_test x|
          = |B.c x| * |u x * v_test x| := by
            rw [show B.c x * u x * v_test x = B.c x * (u x * v_test x) from by ring,
              abs_mul]
        _ ≤ Mc * |u x * v_test x| :=
              mul_le_mul_of_nonneg_right h_c_le h_uv_nn
    · have h_v_zero : v_test x = 0 := h_v_test_zero_outside_Ω' x hx
      have h_lhs_zero : B.c x * u x * v_test x = 0 := by rw [h_v_zero]; ring
      rw [h_lhs_zero, abs_zero]
      have h_rhs_nn : 0 ≤ Mc * |u x * v_test x| :=
        mul_nonneg hMc_nn (abs_nonneg _)
      exact h_rhs_nn
  have h_cuv_aesm : AEStronglyMeasurable (fun x : E => B.c x * u x * v_test x)
      (volume : Measure E) := by
    have h1 : AEStronglyMeasurable B.c (volume : Measure E) :=
      h_c_cont.aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun x : E => B.c x * u x) (volume : Measure E) :=
      h1.mul hu_l2.aestronglyMeasurable
    exact h2.mul h_v_test_aesm
  have h_cuv_int : Integrable (fun x : E => B.c x * u x * v_test x)
      (volume : Measure E) := by
    have h_uv_abs_l1 : Integrable (fun x : E => |u x * v_test x|)
        (volume : Measure E) := h_uv_l1.abs
    refine (h_uv_abs_l1.const_mul Mc).mono' h_cuv_aesm ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    rw [Real.norm_eq_abs]
    exact h_pointwise_cuv x
  have h_int_E : ∫ x in Ω, B.c x * u x * v_test x ∂(volume : Measure E) =
      ∫ x, B.c x * u x * v_test x ∂(volume : Measure E) := by
    have h_eq_zero : ∀ x, x ∉ Ω → B.c x * u x * v_test x = 0 := by
      intro x hx
      rw [h_v_test_zero_outside x hx]; ring
    exact setIntegral_eq_integral_of_forall_compl_eq_zero h_eq_zero
  rw [h_int_E]
  have h_int_Ω' : ∫ x, B.c x * u x * v_test x ∂(volume : Measure E) =
      ∫ x in Ω', B.c x * u x * v_test x ∂(volume : Measure E) := by
    have h_eq_zero : ∀ x, x ∉ Ω' → B.c x * u x * v_test x = 0 := by
      intro x hx
      rw [h_v_test_zero_outside_Ω' x hx]; ring
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero h_eq_zero).symm
  rw [h_int_Ω']
  have h_pointwise_cu_v : ∀ x : E,
      |B.c x * u x * v_test x| ≤ (ε/2) * (v_test x) ^ 2 + (1/(2*ε)) * (B.c x * u x) ^ 2 := by
    intro x
    have h_y := Sobolev.NirenbergCrossBounds.two_abs_mul_le_eps_sq_add (v_test x) (B.c x * u x) ε hε
    have h_abs_eq : |B.c x * u x * v_test x| = |v_test x| * |B.c x * u x| := by
      rw [show (B.c x * u x * v_test x) = v_test x * (B.c x * u x) from by ring,
        abs_mul]
    rw [h_abs_eq]
    have h_div_eq : (1 / ε) * (B.c x * u x) ^ 2 = 2 * ((1 / (2 * ε)) * (B.c x * u x) ^ 2) := by
      have hε_ne : ε ≠ 0 := ne_of_gt hε
      field_simp
    have h_ε_eq : ε * (v_test x) ^ 2 = 2 * ((ε / 2) * (v_test x) ^ 2) := by ring
    linarith [h_y, h_div_eq, h_ε_eq]
  have h_v_test_sq_int : Integrable (fun x : E => (v_test x) ^ 2)
      (volume : Measure E) := h_v_test_l2.integrable_sq
  have h_v_test_sq_int_Ω' : IntegrableOn (fun x : E => (v_test x) ^ 2) Ω' volume :=
    h_v_test_sq_int.integrableOn
  have h_u_sq_int_Ω' : IntegrableOn (fun x : E => (u x) ^ 2) Ω' volume := by
    have h_u_sq_int_E : Integrable (fun x : E => (u x) ^ 2) (volume : Measure E) :=
      hu_l2.integrable_sq
    exact h_u_sq_int_E.integrableOn
  have h_cu_sq_bound : ∀ x ∈ Ω', (B.c x * u x) ^ 2 ≤ Mc^2 * (u x) ^ 2 := by
    intro x hx
    have h_x_in_clΩ' : x ∈ closure Ω' := subset_closure hx
    have h_c_le : |B.c x| ≤ Mc := h_Mc x h_x_in_clΩ'
    have h_c_sq_le : (B.c x) ^ 2 ≤ Mc^2 := by
      rw [← sq_abs (B.c x)]; exact pow_le_pow_left₀ (abs_nonneg _) h_c_le 2
    have h_u_sq_nn : 0 ≤ (u x) ^ 2 := sq_nonneg _
    calc (B.c x * u x) ^ 2 = (B.c x) ^ 2 * (u x) ^ 2 := by ring
      _ ≤ Mc^2 * (u x) ^ 2 := mul_le_mul_of_nonneg_right h_c_sq_le h_u_sq_nn
  have h_cu_sq_int_Ω' : IntegrableOn (fun x : E => (B.c x * u x) ^ 2) Ω' volume := by
    have h_cu_sq_aesm : AEStronglyMeasurable
        (fun x : E => (B.c x * u x) ^ 2) ((volume : Measure E).restrict Ω') :=
      ((h_c_cont.aestronglyMeasurable.mul hu_l2.aestronglyMeasurable).pow 2).restrict
    have h_const_int : IntegrableOn (fun x : E => Mc^2 * (u x) ^ 2) Ω' volume :=
      h_u_sq_int_Ω'.const_mul (Mc^2)
    refine ⟨h_cu_sq_aesm, ?_⟩
    refine HasFiniteIntegral.mono' h_const_int.hasFiniteIntegral ?_
    refine (ae_restrict_iff' hΩ'.measurableSet).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro x hx
    rw [Real.norm_eq_abs]
    have h_cu_sq_nn : 0 ≤ (B.c x * u x) ^ 2 := sq_nonneg _
    rw [abs_of_nonneg h_cu_sq_nn]
    exact h_cu_sq_bound x hx
  have h_cu_v_int_Ω' : IntegrableOn (fun x : E => B.c x * u x * v_test x) Ω' volume :=
    h_cuv_int.integrableOn
  have h_rhs_int_Ω' : IntegrableOn (fun x : E =>
      (ε/2) * (v_test x) ^ 2 + (1/(2*ε)) * (B.c x * u x) ^ 2) Ω' volume := by
    refine (h_v_test_sq_int_Ω'.const_mul (ε/2)).add (h_cu_sq_int_Ω'.const_mul (1/(2*ε)))
  have h_step1 : |∫ x in Ω', B.c x * u x * v_test x ∂(volume : Measure E)| ≤
      ∫ x in Ω', |B.c x * u x * v_test x| ∂(volume : Measure E) :=
    abs_integral_le_integral_abs (μ := (volume : Measure E).restrict Ω')
  have h_step2 : ∫ x in Ω', |B.c x * u x * v_test x| ∂(volume : Measure E) ≤
      ∫ x in Ω',
        ((ε/2) * (v_test x) ^ 2 + (1/(2*ε)) * (B.c x * u x) ^ 2)
        ∂(volume : Measure E) := by
    refine integral_mono_ae h_cu_v_int_Ω'.abs h_rhs_int_Ω' ?_
    refine Filter.Eventually.of_forall ?_
    intro x; exact h_pointwise_cu_v x
  refine (h_step1.trans h_step2).trans ?_
  rw [integral_add (h_v_test_sq_int_Ω'.const_mul (ε/2))
      (h_cu_sq_int_Ω'.const_mul (1/(2*ε)))]
  rw [integral_const_mul, integral_const_mul]
  have h_v_test_sq_Ω'_le_E :
      ∫ x in Ω', (v_test x) ^ 2 ∂(volume : Measure E) ≤
      ∫ x, (v_test x) ^ 2 ∂(volume : Measure E) := by
    have h_eq : ∫ x, (v_test x) ^ 2 ∂(volume : Measure E) =
        ∫ x in Ω', (v_test x) ^ 2 ∂(volume : Measure E) := by
      have h_eq_zero : ∀ x, x ∉ Ω' → (v_test x) ^ 2 = 0 := by
        intro x hx; rw [h_v_test_zero_outside_Ω' x hx]; ring
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero h_eq_zero).symm
    rw [h_eq]
  have h_v_test_bound := h_v_test_sq_bound hh hh_le
  have h_cu_sq_int_Ω'_le : ∫ x in Ω', (B.c x * u x) ^ 2 ∂(volume : Measure E) ≤
      Mc^2 * ∫ x in Ω', (u x) ^ 2 ∂(volume : Measure E) := by
    have h_const_int : IntegrableOn (fun x : E => Mc^2 * (u x) ^ 2) Ω' volume :=
      h_u_sq_int_Ω'.const_mul (Mc^2)
    have h_step :
        ∫ x in Ω', (B.c x * u x) ^ 2 ∂(volume : Measure E) ≤
        ∫ x in Ω', Mc^2 * (u x) ^ 2 ∂(volume : Measure E) :=
      setIntegral_mono_on h_cu_sq_int_Ω' h_const_int hΩ'.measurableSet h_cu_sq_bound
    rw [integral_const_mul] at h_step
    exact h_step
  have h_v_sq_le_8N_2I :
      ∫ x in Ω', (v_test x) ^ 2 ∂(volume : Measure E) ≤
        8 * N ^ 2 *
          ∫ x in tsupport η, (Sobolev.diffQuot k h u x) ^ 2
            ∂(volume : Measure E) +
        2 * ∫ x, (η x) ^ 2 *
            (Sobolev.diffQuot k h (g k) x) ^ 2
          ∂(volume : Measure E) :=
    h_v_test_sq_Ω'_le_E.trans h_v_test_bound
  have h_diff_bound :
      ∫ x in tsupport η, (Sobolev.diffQuot k h u x) ^ 2
          ∂(volume : Measure E) ≤
        ∫ x in Ω', ∑ i : Fin d, ((g i) x) ^ 2 ∂(volume : Measure E) :=
    h_FK_diffQuot_u_bound hh hh_le
  have h_partial_le_sum : ∀ x : E,
      (η x) ^ 2 *
        (Sobolev.diffQuot k h (g k) x) ^ 2 ≤
      (η x) ^ 2 *
        ∑ i : Fin d,
          (Sobolev.diffQuot k h (g i) x) ^ 2 := by
    intro x
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    exact Finset.single_le_sum
      (f := fun i => (Sobolev.diffQuot k h (g i) x) ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ k)
  have h_eta_sq_partial_int : Integrable (fun x : E =>
      (η x) ^ 2 *
        (Sobolev.diffQuot k h (g k) x) ^ 2) volume := by
    have hint := integrable_const_eta_sq_diffQuot_g_sq (d := d) hg_l2 hη hη_support k k h 1
    have h_eq : (fun x : E => (η x) ^ 2 *
            (Sobolev.diffQuot k h (g k) x) ^ 2) =
        fun x : E => 1 * (η x) ^ 2 *
            (Sobolev.diffQuot k h (g k) x) ^ 2 := by
      funext x; ring
    rw [h_eq]; exact hint
  have h_eta_sq_sum_int : Integrable (fun x : E =>
      (η x) ^ 2 *
        ∑ i : Fin d,
          (Sobolev.diffQuot k h (g i) x) ^ 2) volume := by
    have h_per_i : ∀ i : Fin d, Integrable (fun x : E =>
        (η x) ^ 2 *
          (Sobolev.diffQuot k h (g i) x) ^ 2) volume := by
      intro i
      have hint := integrable_const_eta_sq_diffQuot_g_sq (d := d) hg_l2 hη hη_support i k h 1
      have h_eq : (fun x : E => (η x) ^ 2 *
              (Sobolev.diffQuot k h (g i) x) ^ 2) =
          fun x : E => 1 * (η x) ^ 2 *
              (Sobolev.diffQuot k h (g i) x) ^ 2 := by
        funext x; ring
      rw [h_eq]; exact hint
    have h_sum_int : Integrable (fun x : E =>
        ∑ i : Fin d, (η x) ^ 2 *
          (Sobolev.diffQuot k h (g i) x) ^ 2) volume :=
      integrable_finsetSum (Finset.univ : Finset (Fin d)) (fun i _ => h_per_i i)
    have h_eq : (fun x : E => ∑ i : Fin d, (η x) ^ 2 *
            (Sobolev.diffQuot k h (g i) x) ^ 2) =
        (fun x : E => (η x) ^ 2 *
            ∑ i : Fin d,
              (Sobolev.diffQuot k h (g i) x) ^ 2) := by
      funext x; rw [Finset.mul_sum]
    rw [h_eq] at h_sum_int; exact h_sum_int
  have h_partial_int_le :
      ∫ x, (η x) ^ 2 *
          (Sobolev.diffQuot k h (g k) x) ^ 2
        ∂(volume : Measure E) ≤
      ∫ x, (η x) ^ 2 *
          ∑ i : Fin d,
            (Sobolev.diffQuot k h (g i) x) ^ 2
        ∂(volume : Measure E) :=
    integral_mono h_eta_sq_partial_int h_eta_sq_sum_int h_partial_le_sum
  have h_gradL2_nn : 0 ≤ ∫ x in Ω',
        ∑ i : Fin d, ((g i) x) ^ 2 ∂(volume : Measure E) :=
    integral_nonneg (fun x => Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have h_uL2_nn : 0 ≤ ∫ x in Ω', (u x) ^ 2 ∂(volume : Measure E) :=
    integral_nonneg (fun x => sq_nonneg _)
  have h_v_full_bound :
      (ε/2) * ∫ x in Ω', (v_test x) ^ 2 ∂(volume : Measure E) ≤
      4 * ε * N ^ 2 *
        ∫ x in Ω', ∑ i : Fin d, ((g i) x) ^ 2 ∂(volume : Measure E) +
      ε * ∫ x, (η x) ^ 2 *
          ∑ i : Fin d,
            (Sobolev.diffQuot k h (g i) x) ^ 2
        ∂(volume : Measure E) := by
    have h_step_a := mul_le_mul_of_nonneg_left h_v_sq_le_8N_2I (by linarith : 0 ≤ ε/2)
    have h_step_b : (ε/2) * (8 * N ^ 2 *
            ∫ x in tsupport η, (Sobolev.diffQuot k h u x) ^ 2
              ∂(volume : Measure E) +
          2 * ∫ x, (η x) ^ 2 *
            (Sobolev.diffQuot k h (g k) x) ^ 2
            ∂(volume : Measure E)) ≤
        4 * ε * N ^ 2 *
            ∫ x in Ω', ∑ i : Fin d, ((g i) x) ^ 2 ∂(volume : Measure E) +
        ε * ∫ x, (η x) ^ 2 *
            ∑ i : Fin d,
              (Sobolev.diffQuot k h (g i) x) ^ 2
            ∂(volume : Measure E) := by
      have h1 : (ε/2) * (8 * N ^ 2 *
            ∫ x in tsupport η, (Sobolev.diffQuot k h u x) ^ 2
              ∂(volume : Measure E)) =
          4 * ε * N ^ 2 *
            ∫ x in tsupport η, (Sobolev.diffQuot k h u x) ^ 2
              ∂(volume : Measure E) := by ring
      have h2 : (ε/2) * (2 * ∫ x, (η x) ^ 2 *
            (Sobolev.diffQuot k h (g k) x) ^ 2
            ∂(volume : Measure E)) =
          ε * ∫ x, (η x) ^ 2 *
            (Sobolev.diffQuot k h (g k) x) ^ 2
            ∂(volume : Measure E) := by ring
      have h_diff_pos : 0 ≤ 4 * ε * N ^ 2 := by
        refine mul_nonneg ?_ (sq_nonneg _)
        exact mul_nonneg (by linarith) hε.le
      have h_step_c : 4 * ε * N ^ 2 *
            ∫ x in tsupport η, (Sobolev.diffQuot k h u x) ^ 2
              ∂(volume : Measure E) ≤
          4 * ε * N ^ 2 *
            ∫ x in Ω', ∑ i : Fin d, ((g i) x) ^ 2 ∂(volume : Measure E) :=
        mul_le_mul_of_nonneg_left h_diff_bound h_diff_pos
      have h_step_d : ε * ∫ x, (η x) ^ 2 *
            (Sobolev.diffQuot k h (g k) x) ^ 2
            ∂(volume : Measure E) ≤
          ε * ∫ x, (η x) ^ 2 *
            ∑ i : Fin d,
              (Sobolev.diffQuot k h (g i) x) ^ 2
            ∂(volume : Measure E) :=
        mul_le_mul_of_nonneg_left h_partial_int_le hε.le
      linarith
    linarith
  have h_cu_full_bound :
      (1/(2*ε)) * ∫ x in Ω', (B.c x * u x) ^ 2 ∂(volume : Measure E) ≤
      (Mc^2 / (2 * ε)) * ∫ x in Ω', (u x) ^ 2 ∂(volume : Measure E) := by
    have h_div_pos : 0 < 1/(2*ε) := by
      refine one_div_pos.mpr ?_; linarith
    have h_step := mul_le_mul_of_nonneg_left h_cu_sq_int_Ω'_le h_div_pos.le
    have h_eq : (1 / (2 * ε)) * (Mc ^ 2 * ∫ x in Ω', u x ^ 2 ∂(volume : Measure E)) =
        Mc^2 / (2*ε) * ∫ x in Ω', (u x) ^ 2 ∂(volume : Measure E) := by ring
    linarith [h_step, h_eq]
  have h_C_grad_le : 4 * ε * N ^ 2 ≤ C := le_max_left _ _
  have h_C_uL2_le : Mc^2 / (2*ε) ≤ C := le_max_right _ _
  have h_combine :
      4 * ε * N ^ 2 *
          ∫ x in Ω', ∑ i : Fin d, ((g i) x) ^ 2 ∂(volume : Measure E) +
      (Mc^2 / (2 * ε)) * ∫ x in Ω', (u x) ^ 2 ∂(volume : Measure E) ≤
      C * (∫ x in Ω', ∑ i : Fin d, ((g i) x) ^ 2 ∂(volume : Measure E) +
          ∫ x in Ω', (u x) ^ 2 ∂(volume : Measure E)) := by
    have h_left_le := mul_le_mul_of_nonneg_right h_C_grad_le h_gradL2_nn
    have h_right_le := mul_le_mul_of_nonneg_right h_C_uL2_le h_uL2_nn
    have h_C_dist : C * (∫ x in Ω', ∑ i : Fin d, ((g i) x) ^ 2 ∂(volume : Measure E) +
          ∫ x in Ω', (u x) ^ 2 ∂(volume : Measure E)) =
        C * (∫ x in Ω', ∑ i : Fin d, ((g i) x) ^ 2 ∂(volume : Measure E)) +
        C * ∫ x in Ω', (u x) ^ 2 ∂(volume : Measure E) := by ring
    linarith
  linarith

end Sobolev.NirenbergCrossBoundsNonSmooth
