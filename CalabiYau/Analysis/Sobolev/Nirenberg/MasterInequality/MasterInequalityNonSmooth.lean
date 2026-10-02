-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Nirenberg/MasterInequality/MasterInequalityNonSmooth.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Nirenberg.CrossTermBoundsNonSmooth.CrossBoundsNonSmooth
public import CalabiYau.Analysis.Sobolev.Nirenberg.CrossTermBoundsNonSmooth.CoefficientDifferenceQuotient
public import CalabiYau.Analysis.Sobolev.Nirenberg.CrossTermBoundsNonSmooth.CoefficientCutoffGradient
public import CalabiYau.Analysis.Sobolev.Nirenberg.CrossTermBoundsNonSmooth.CrossBoundsNonSmoothCTerm
public import CalabiYau.Analysis.Sobolev.Nirenberg.CrossTermBoundsNonSmooth.ForcingTerm

@[expose] public section

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open Sobolev
open Sobolev.NirenbergEuclidean
open Sobolev.NirenbergCrossBounds
open Sobolev.NirenbergCrossBoundsNonSmooth
open scoped ENNReal NNReal Convolution Pointwise BigOperators InnerProductSpace

namespace Sobolev.NirenbergCrossBoundsNonSmooth

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

noncomputable def nirenbergMasterYoungConstant
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (N : ℝ) {Ω' : Set E} (hΩ'_compact : IsCompact (closure Ω'))
    (k : Fin d) : ℝ :=
  max
    (((1 / ((B.lam / 8) / (Fintype.card (Fin d) : ℝ)))
          * (Classical.choose
              (SmoothEllipticBilinearForm.bounded_a_on_compact
                (d := d) B hΩ'_compact))^2
          * N^2 * (Fintype.card (Fin d) : ℝ)^2)
      + (((Classical.choose
              (SmoothEllipticBilinearForm.bounded_fderiv_a_on_compact
                (d := d) B k hΩ'_compact))^2
            / (4 * ((B.lam / 8) / (Fintype.card (Fin d) : ℝ))))
          * (Fintype.card (Fin d) : ℝ)^2)
      + (2 * (Classical.choose
              (SmoothEllipticBilinearForm.bounded_fderiv_a_on_compact
                (d := d) B k hΩ'_compact))
          * N * (Fintype.card (Fin d) : ℝ)^2)
      + max (4 * (B.lam / 8) * N^2)
          ((Classical.choose
              (SmoothEllipticBilinearForm.bounded_c_on_compact
                (d := d) B hΩ'_compact))^2 / (2 * (B.lam / 8)))
      + max (4 * (B.lam / 8) * N^2) (1 / (2 * (B.lam / 8))))
    (max
      (max (4 * (B.lam / 8) * N^2)
        ((Classical.choose
            (SmoothEllipticBilinearForm.bounded_c_on_compact
              (d := d) B hΩ'_compact))^2 / (2 * (B.lam / 8))))
      (max (4 * (B.lam / 8) * N^2) (1 / (2 * (B.lam / 8)))))

theorem nirenbergMasterYoungConstant_nonneg
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {N : ℝ} (hN : 0 ≤ N) {Ω' : Set E}
    (hΩ'_compact : IsCompact (closure Ω')) (k : Fin d) :
    0 ≤ nirenbergMasterYoungConstant (d := d) B N hΩ'_compact k := by
  classical
  have hε₀ : (0 : ℝ) < B.lam / 8 := div_pos B.ellipticity_pos (by norm_num)
  have hd_pos : (0 : ℝ) < (Fintype.card (Fin d) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hε'_pos : 0 < (B.lam / 8) / (Fintype.card (Fin d) : ℝ) := div_pos hε₀ hd_pos
  rw [nirenbergMasterYoungConstant]
  refine le_max_of_le_left ?_
  refine add_nonneg (add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_) ?_
  · refine mul_nonneg (mul_nonneg (mul_nonneg ?_ (sq_nonneg _)) (sq_nonneg _))
      (sq_nonneg _)
    exact (one_div_pos.mpr hε'_pos).le
  · refine mul_nonneg ?_ (sq_nonneg _)
    refine mul_nonneg (sq_nonneg _) ?_
    refine inv_nonneg.mpr (by linarith [hε'_pos])
  · refine mul_nonneg ?_ (sq_nonneg _)
    refine mul_nonneg ?_ hN
    refine mul_nonneg (by linarith) ?_
    exact (Classical.choose_spec
      (SmoothEllipticBilinearForm.bounded_fderiv_a_on_compact
        (d := d) B k hΩ'_compact)).1
  · refine le_max_of_le_left ?_
    refine mul_nonneg ?_ (sq_nonneg _)
    exact mul_nonneg (by linarith) hε₀.le
  · refine le_max_of_le_left ?_
    refine mul_nonneg ?_ (sq_nonneg _)
    exact mul_nonneg (by linarith) hε₀.le

theorem nirenberg_master_inequality_after_young_nonsmooth_quantitative
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u f : E → ℝ}
    (hu_l2 : MemLp u 2 (volume : Measure E))
    (hf_l2_local : ∀ {Ω' : Set E}, IsCompact (closure Ω') →
      MemLp f 2 (volume.restrict Ω'))
    {g : Fin d → E → ℝ}
    (hg_l2 : ∀ i, MemLp (g i) 2 (volume : Measure E))
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (hN : 0 ≤ N) (h_fderiv_eta : ∀ x : E, ‖fderiv ℝ η x‖ ≤ N)
    {Ω' : Set E} (hΩ' : IsOpen Ω') (hΩ'_closure : closure Ω' ⊆ Ω)
    (hΩ'_compact : IsCompact (closure Ω'))
    {R₀ : ℝ}
    (hh_support_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (k : Fin d)
    (h_FK_diffQuot_u_bound : ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      ∫ x in tsupport η,
          (Sobolev.diffQuot k h u x)^2
        ∂(volume : Measure E) ≤
        ∫ x in Ω', ∑ i : Fin d, ((g i) x) ^ 2 ∂(volume : Measure E))
    (h_v_test_sq_bound : ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      ∫ x, (Sobolev.NirenbergTestFunction.nirenbergTestFunction
            k h η u x)^2 ∂(volume : Measure E) ≤
        8 * N^2 *
          ∫ x in tsupport η,
              (Sobolev.diffQuot k h u x)^2
            ∂(volume : Measure E) +
        2 * ∫ x, (η x)^2 *
            (Sobolev.diffQuot k h (g k) x)^2
          ∂(volume : Measure E))
    (h_master_nonsmooth : ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      B.lam * ∫ x, (η x)^2 *
          ∑ i : Fin d, Sobolev.diffQuot k h (g i) x ^ 2
        ∂(volume : Measure E) ≤
        |∑ i : Fin d, ∑ j : Fin d, ∫ x,
              2 * Sobolev.translate k h
                (fun y : E => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              Sobolev.diffQuot k h (g i) x *
              Sobolev.diffQuot k h u x
            ∂(volume : Measure E)| +
        |∑ i : Fin d, ∑ j : Fin d, ∫ x,
              Sobolev.diffQuot k h
                (fun y : E => B.a y i j) x * (η x)^2 *
              ((g i) x) *
              Sobolev.diffQuot k h (g j) x
            ∂(volume : Measure E)| +
        |∑ i : Fin d, ∑ j : Fin d, ∫ x,
              2 * Sobolev.diffQuot k h
                (fun y : E => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              ((g i) x) *
              Sobolev.diffQuot k h u x
            ∂(volume : Measure E)| +
        |∫ x in Ω, f x *
            Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u x| +
        |∫ x in Ω, B.c x * u x *
            Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u x ∂(volume : Measure E)|) :
    ∀ ⦃h : ℝ⦄, h ≠ 0 → |h| ≤ R₀ →
      B.lam * ∫ x, (η x)^2 *
          ∑ i : Fin d, Sobolev.diffQuot k h (g i) x ^ 2
        ∂(volume : Measure E) ≤
        (B.lam / 2) * ∫ x, (η x)^2 *
            ∑ i : Fin d,
              Sobolev.diffQuot k h (g i) x ^ 2
          ∂(volume : Measure E) +
        nirenbergMasterYoungConstant (d := d) B N hΩ'_compact k
          * (∫ x in Ω', ∑ i : Fin d, ((g i) x) ^ 2
              ∂(volume : Measure E) +
          ∫ x in Ω', (u x)^2 ∂(volume : Measure E) +
          ∫ x in Ω', (f x)^2 ∂(volume : Measure E)) := by
  classical
  have hε_effective_pos₀ : (0 : ℝ) < B.lam / 8 := div_pos B.ellipticity_pos (by norm_num)
  have hC1 := cross_1_bound_nonsmooth_quantitative (d := d) B hu_l2 hg_l2
    hη hη_support hη_range h_fderiv_eta hΩ'_compact
    hh_support_in_Ω' k h_FK_diffQuot_u_bound (B.lam / 8) hε_effective_pos₀
  have hC2 := coefficient_difference_quotient_mixed_term_bound_nonsmooth_quantitative (d := d) B hg_l2
    hη hη_support hη_range hΩ' hΩ'_compact
    hh_support_in_Ω' k (B.lam / 8) hε_effective_pos₀
  have hC3 := diffQuot_coeff_cutoff_gradient_bound_nonsmooth_quantitative (d := d) B hu_l2 hg_l2
    hη hη_support hη_range hN h_fderiv_eta hΩ'_compact
    hh_support_in_Ω' k h_FK_diffQuot_u_bound
  have hCc := c_term_bound_nonsmooth_quantitative (d := d) B hu_l2 hg_l2
    hη hη_support hΩ' hΩ'_closure hΩ'_compact hh_support_in_Ω' k
    (B.lam / 8) hε_effective_pos₀ h_v_test_sq_bound
    h_FK_diffQuot_u_bound
  have h_v_test_sq_bound_sum : ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      ∫ x, (Sobolev.NirenbergTestFunction.nirenbergTestFunction
            k h η u x)^2 ∂(volume : Measure E) ≤
        8 * N^2 *
          ∫ x in tsupport η,
              (Sobolev.diffQuot k h u x)^2
            ∂(volume : Measure E) +
        2 * ∫ x, (η x)^2 *
            ∑ i : Fin d,
              (Sobolev.diffQuot k h (g i) x)^2
          ∂(volume : Measure E) := by
    intro h hh hh_le
    have h_single := h_v_test_sq_bound hh hh_le
    have h_pointwise : ∀ x : E,
        (η x)^2 * (Sobolev.diffQuot k h (g k) x)^2 ≤
          (η x)^2 * ∑ i : Fin d,
            (Sobolev.diffQuot k h (g i) x)^2 := by
      intro x
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      have h_kmem : k ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ k
      have h_term_le_sum :
          (Sobolev.diffQuot k h (g k) x)^2 ≤
            ∑ i : Fin d,
              (Sobolev.diffQuot k h (g i) x)^2 :=
        Finset.single_le_sum
          (f := fun i => (Sobolev.diffQuot k h (g i) x)^2)
          (fun i _ => sq_nonneg _) h_kmem
      exact h_term_le_sum
    have h_integrable_single : Integrable (fun x : E =>
        (η x)^2 * (Sobolev.diffQuot k h (g k) x)^2)
        (volume : Measure E) := by
      have hint := integrable_const_eta_sq_diffQuot_g_sq (d := d) hg_l2 hη hη_support
        k k h 1
      have h_eq : (fun x : E => (η x)^2 *
          (Sobolev.diffQuot k h (g k) x)^2) =
          (fun x : E => 1 * (η x)^2 *
          (Sobolev.diffQuot k h (g k) x)^2) := by
        funext x; ring
      rw [h_eq]
      exact hint
    have h_integrable_sum : Integrable (fun x : E =>
        (η x)^2 * ∑ i : Fin d,
          (Sobolev.diffQuot k h (g i) x)^2)
        (volume : Measure E) := by
      have h_per_i : ∀ i : Fin d, Integrable (fun x : E =>
          (η x)^2 * (Sobolev.diffQuot k h (g i) x)^2)
          (volume : Measure E) := by
        intro i
        have hint := integrable_const_eta_sq_diffQuot_g_sq (d := d) hg_l2 hη hη_support
          i k h 1
        have h_eq : (fun x : E => (η x)^2 *
            (Sobolev.diffQuot k h (g i) x)^2) =
            (fun x : E => 1 * (η x)^2 *
            (Sobolev.diffQuot k h (g i) x)^2) := by
          funext x; ring
        rw [h_eq]
        exact hint
      have h_sum_int := integrable_finsetSum (Finset.univ : Finset (Fin d))
        (fun i _ => h_per_i i)
      have h_eq : (fun x : E =>
          (η x)^2 * ∑ i : Fin d,
            (Sobolev.diffQuot k h (g i) x)^2) =
          (fun x : E => ∑ i : Fin d,
            (η x)^2 * (Sobolev.diffQuot k h (g i) x)^2) := by
        funext x
        rw [Finset.mul_sum]
      rw [h_eq]
      exact h_sum_int
    have h_int_le :
        ∫ x, (η x)^2 * (Sobolev.diffQuot k h (g k) x)^2
            ∂(volume : Measure E) ≤
          ∫ x, (η x)^2 * ∑ i : Fin d,
              (Sobolev.diffQuot k h (g i) x)^2
            ∂(volume : Measure E) :=
      integral_mono h_integrable_single h_integrable_sum h_pointwise
    have h_two_int_le :
        2 * ∫ x, (η x)^2 * (Sobolev.diffQuot k h (g k) x)^2
            ∂(volume : Measure E) ≤
          2 * ∫ x, (η x)^2 * ∑ i : Fin d,
              (Sobolev.diffQuot k h (g i) x)^2
            ∂(volume : Measure E) :=
      mul_le_mul_of_nonneg_left h_int_le (by linarith)
    linarith
  have hCf := forcing_term_bound_nonsmooth_quantitative (d := d) hf_l2_local hu_l2
    hη hη_support hΩ'_closure hΩ'_compact hh_support_in_Ω' k
    h_FK_diffQuot_u_bound h_v_test_sq_bound_sum
    (B.lam / 8) hε_effective_pos₀
  set ε_effective : ℝ := B.lam / 8 with hε_effective_def
  set Λ : ℝ := Classical.choose
    (SmoothEllipticBilinearForm.bounded_a_on_compact (d := d) B hΩ'_compact)
    with hΛ_eq
  set M : ℝ := Classical.choose
    (SmoothEllipticBilinearForm.bounded_fderiv_a_on_compact (d := d) B k hΩ'_compact)
    with hM_eq
  set Mc : ℝ := Classical.choose
    (SmoothEllipticBilinearForm.bounded_c_on_compact (d := d) B hΩ'_compact)
    with hMc_eq
  set d_real : ℝ := (Fintype.card (Fin d) : ℝ) with hd_real
  have hd_pos : 0 < d_real := by
    rw [hd_real]; exact_mod_cast Fintype.card_pos
  have hε_effective_pos : 0 < ε_effective := hε_effective_pos₀
  have hε'_pos : 0 < ε_effective / d_real := div_pos hε_effective_pos hd_pos
  set C1 : ℝ := (1 / (ε_effective / d_real)) * Λ^2 * N^2 * d_real^2 with hC1_def
  set C2 : ℝ := (M^2 / (4 * (ε_effective / d_real))) * d_real^2 with hC2_def
  set C3 : ℝ := 2 * M * N * d_real^2 with hC3_def
  set Cc : ℝ := max (4 * ε_effective * N^2) (Mc^2 / (2 * ε_effective)) with hCc_def
  set Cf : ℝ := max (4 * ε_effective * N^2) (1 / (2 * ε_effective)) with hCf_def
  have hΛ_nn : 0 ≤ Λ :=
    (Classical.choose_spec
      (SmoothEllipticBilinearForm.bounded_a_on_compact (d := d) B hΩ'_compact)).1
  have hM_nn : 0 ≤ M :=
    (Classical.choose_spec
      (SmoothEllipticBilinearForm.bounded_fderiv_a_on_compact
        (d := d) B k hΩ'_compact)).1
  have hMc_nn : 0 ≤ Mc :=
    (Classical.choose_spec
      (SmoothEllipticBilinearForm.bounded_c_on_compact (d := d) B hΩ'_compact)).1
  have hC1_nn : 0 ≤ C1 := by
    rw [hC1_def]
    refine mul_nonneg (mul_nonneg (mul_nonneg ?_ (sq_nonneg _)) (sq_nonneg _))
      (sq_nonneg _)
    exact (one_div_pos.mpr hε'_pos).le
  have hC2_nn : 0 ≤ C2 := by
    rw [hC2_def]
    refine mul_nonneg ?_ (sq_nonneg _)
    refine mul_nonneg (sq_nonneg _) ?_
    refine inv_nonneg.mpr (by linarith [hε'_pos])
  have hC3_nn : 0 ≤ C3 := by
    rw [hC3_def]
    refine mul_nonneg ?_ (sq_nonneg _)
    refine mul_nonneg ?_ hN
    exact mul_nonneg (by linarith) hM_nn
  have hCc_nn : 0 ≤ Cc := by
    rw [hCc_def]
    refine le_max_of_le_left ?_
    refine mul_nonneg ?_ (sq_nonneg _)
    exact mul_nonneg (by linarith) hε_effective_pos.le
  have hCf_nn : 0 ≤ Cf := by
    rw [hCf_def]
    refine le_max_of_le_left ?_
    refine mul_nonneg ?_ (sq_nonneg _)
    exact mul_nonneg (by linarith) hε_effective_pos.le
  set C : ℝ := max (C1 + C2 + C3 + Cc + Cf) (max Cc Cf) with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    refine le_max_of_le_left ?_
    refine add_nonneg (add_nonneg (add_nonneg (add_nonneg hC1_nn hC2_nn) hC3_nn) hCc_nn) hCf_nn
  intro h hh hh_le
  set I : ℝ := ∫ x, (η x)^2 *
      ∑ i : Fin d, Sobolev.diffQuot k h (g i) x ^ 2
    ∂(volume : Measure E) with hI_def
  set G : ℝ := ∫ x in Ω', ∑ i : Fin d, ((g i) x) ^ 2
    ∂(volume : Measure E) with hG_def
  set U : ℝ := ∫ x in Ω', (u x)^2 ∂(volume : Measure E) with hU_def
  set F : ℝ := ∫ x in Ω', (f x)^2 ∂(volume : Measure E) with hF_def
  have hI_nn : 0 ≤ I := by
    refine integral_nonneg ?_
    intro x
    refine mul_nonneg (sq_nonneg _) ?_
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hG_nn : 0 ≤ G := integral_nonneg
    (fun x => Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have hU_nn : 0 ≤ U := integral_nonneg (fun x => sq_nonneg _)
  have hF_nn : 0 ≤ F := integral_nonneg (fun x => sq_nonneg _)
  have h_master := h_master_nonsmooth hh hh_le
  have hC1_h := hC1 hh hh_le
  have hC2_h := hC2 hh hh_le
  have hC3_h := hC3 hh hh_le
  have hCc_h := hCc hh hh_le
  have hCf_h := hCf hh hh_le
  have h_4ε_eq : 4 * ε_effective = B.lam / 2 := by
    rw [hε_effective_def]; ring
  have h_combine : B.lam * I ≤
      4 * ε_effective * I + (C1 + C2 + C3 + Cc + Cf) * G + Cc * U + Cf * F := by
    have h_sum_bound :
        |∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
              Sobolev.translate k h
                (fun y : E => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              Sobolev.diffQuot k h (g i) x *
              Sobolev.diffQuot k h u x
            ∂(volume : Measure E)| +
          |∑ i : Fin d, ∑ j : Fin d, ∫ x,
              Sobolev.diffQuot k h
                (fun y : E => B.a y i j) x * (η x)^2 *
              ((g i) x) *
              Sobolev.diffQuot k h (g j) x
            ∂(volume : Measure E)| +
          |∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
              Sobolev.diffQuot k h
                (fun y : E => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              ((g i) x) *
              Sobolev.diffQuot k h u x
            ∂(volume : Measure E)| +
          |∫ x in Ω, f x *
              Sobolev.NirenbergTestFunction.nirenbergTestFunction
                k h η u x| +
          |∫ x in Ω, B.c x * u x *
              Sobolev.NirenbergTestFunction.nirenbergTestFunction
                k h η u x ∂(volume : Measure E)| ≤
        (ε_effective * I + C1 * G) + (ε_effective * I + C2 * G) + (C3 * G) +
          (ε_effective * I + Cf * (G + F)) + (ε_effective * I + Cc * (G + U)) := by
      have h1 : |- ∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
              Sobolev.translate k h
                (fun y : E => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              Sobolev.diffQuot k h (g i) x *
              Sobolev.diffQuot k h u x
            ∂(volume : Measure E)| ≤ ε_effective * I + C1 * G := hC1_h
      have h1' :
        |∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
              Sobolev.translate k h
                (fun y : E => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              Sobolev.diffQuot k h (g i) x *
              Sobolev.diffQuot k h u x
            ∂(volume : Measure E)| ≤ ε_effective * I + C1 * G := by
        rw [← abs_neg]; exact h1
      have h2 : |- ∑ i : Fin d, ∑ j : Fin d, ∫ x,
              Sobolev.diffQuot k h
                (fun y : E => B.a y i j) x * (η x)^2 *
              ((g i) x) *
              Sobolev.diffQuot k h (g j) x
            ∂(volume : Measure E)| ≤ ε_effective * I + C2 * G := hC2_h
      have h2' :
        |∑ i : Fin d, ∑ j : Fin d, ∫ x,
              Sobolev.diffQuot k h
                (fun y : E => B.a y i j) x * (η x)^2 *
              ((g i) x) *
              Sobolev.diffQuot k h (g j) x
            ∂(volume : Measure E)| ≤ ε_effective * I + C2 * G := by
        rw [← abs_neg]; exact h2
      have h3 : |- ∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
              Sobolev.diffQuot k h
                (fun y : E => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              ((g i) x) *
              Sobolev.diffQuot k h u x
            ∂(volume : Measure E)| ≤ C3 * G := hC3_h
      have h3' :
        |∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
              Sobolev.diffQuot k h
                (fun y : E => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              ((g i) x) *
              Sobolev.diffQuot k h u x
            ∂(volume : Measure E)| ≤ C3 * G := by
        rw [← abs_neg]; exact h3
      linarith
    refine h_master.trans (h_sum_bound.trans ?_)
    have hCc_distrib : Cc * (G + U) = Cc * G + Cc * U := by ring
    have hCf_distrib : Cf * (G + F) = Cf * G + Cf * F := by ring
    linarith [hCc_distrib, hCf_distrib]
  rw [show (4 * ε_effective * I) = (B.lam / 2) * I from by rw [h_4ε_eq]] at h_combine
  have hC_grad_le : C1 + C2 + C3 + Cc + Cf ≤ C := le_max_left _ _
  have hC_Cc_le : Cc ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hC_Cf_le : Cf ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  have h_step1 : (C1 + C2 + C3 + Cc + Cf) * G ≤ C * G :=
    mul_le_mul_of_nonneg_right hC_grad_le hG_nn
  have h_step2 : Cc * U ≤ C * U :=
    mul_le_mul_of_nonneg_right hC_Cc_le hU_nn
  have h_step3 : Cf * F ≤ C * F :=
    mul_le_mul_of_nonneg_right hC_Cf_le hF_nn
  have h_C_dist : C * (G + U + F) = C * G + C * U + C * F := by ring
  have h_const_eq : nirenbergMasterYoungConstant (d := d) B N hΩ'_compact k = C :=
    rfl
  rw [h_const_eq]
  linarith

theorem nirenberg_master_inequality_absorbed_nonsmooth_quantitative
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u f : E → ℝ}
    (hu_l2 : MemLp u 2 (volume : Measure E))
    (hf_l2_local : ∀ {Ω' : Set E}, IsCompact (closure Ω') →
      MemLp f 2 (volume.restrict Ω'))
    {g : Fin d → E → ℝ}
    (hg_l2 : ∀ i, MemLp (g i) 2 (volume : Measure E))
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (hN : 0 ≤ N) (h_fderiv_eta : ∀ x : E, ‖fderiv ℝ η x‖ ≤ N)
    {Ω' : Set E} (hΩ' : IsOpen Ω') (hΩ'_closure : closure Ω' ⊆ Ω)
    (hΩ'_compact : IsCompact (closure Ω'))
    {R₀ : ℝ}
    (hh_support_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (k : Fin d)
    (h_FK_diffQuot_u_bound : ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      ∫ x in tsupport η,
          (Sobolev.diffQuot k h u x)^2
        ∂(volume : Measure E) ≤
        ∫ x in Ω', ∑ i : Fin d, ((g i) x) ^ 2 ∂(volume : Measure E))
    (h_v_test_sq_bound : ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      ∫ x, (Sobolev.NirenbergTestFunction.nirenbergTestFunction
            k h η u x)^2 ∂(volume : Measure E) ≤
        8 * N^2 *
          ∫ x in tsupport η,
              (Sobolev.diffQuot k h u x)^2
            ∂(volume : Measure E) +
        2 * ∫ x, (η x)^2 *
            (Sobolev.diffQuot k h (g k) x)^2
          ∂(volume : Measure E))
    (h_master_nonsmooth : ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      B.lam * ∫ x, (η x)^2 *
          ∑ i : Fin d, Sobolev.diffQuot k h (g i) x ^ 2
        ∂(volume : Measure E) ≤
        |∑ i : Fin d, ∑ j : Fin d, ∫ x,
              2 * Sobolev.translate k h
                (fun y : E => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              Sobolev.diffQuot k h (g i) x *
              Sobolev.diffQuot k h u x
            ∂(volume : Measure E)| +
        |∑ i : Fin d, ∑ j : Fin d, ∫ x,
              Sobolev.diffQuot k h
                (fun y : E => B.a y i j) x * (η x)^2 *
              ((g i) x) *
              Sobolev.diffQuot k h (g j) x
            ∂(volume : Measure E)| +
        |∑ i : Fin d, ∑ j : Fin d, ∫ x,
              2 * Sobolev.diffQuot k h
                (fun y : E => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              ((g i) x) *
              Sobolev.diffQuot k h u x
            ∂(volume : Measure E)| +
        |∫ x in Ω, f x *
            Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u x| +
        |∫ x in Ω, B.c x * u x *
            Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u x ∂(volume : Measure E)|) :
    ∀ ⦃h : ℝ⦄, h ≠ 0 → |h| ≤ R₀ →
      (B.lam / 2) * ∫ x, (η x)^2 *
          ∑ i : Fin d, Sobolev.diffQuot k h (g i) x ^ 2
        ∂(volume : Measure E) ≤
        nirenbergMasterYoungConstant (d := d) B N hΩ'_compact k
          * (∫ x in Ω', ∑ i : Fin d, ((g i) x) ^ 2
              ∂(volume : Measure E) +
          ∫ x in Ω', (u x)^2 ∂(volume : Measure E) +
          ∫ x in Ω', (f x)^2 ∂(volume : Measure E)) := by
  classical
  have hC := nirenberg_master_inequality_after_young_nonsmooth_quantitative
    (d := d) B hu_l2 hf_l2_local hg_l2 hη hη_support hη_range hN
    h_fderiv_eta hΩ' hΩ'_closure hΩ'_compact hh_support_in_Ω' k
    h_FK_diffQuot_u_bound h_v_test_sq_bound
    h_master_nonsmooth
  intro h hh hh_le
  have h_main := hC hh hh_le
  set I : ℝ := ∫ x, (η x)^2 *
      ∑ i : Fin d, Sobolev.diffQuot k h (g i) x ^ 2
    ∂(volume : Measure E) with hI_def
  have h_lam_split : B.lam * I - (B.lam / 2) * I = (B.lam / 2) * I := by ring
  linarith [h_main]

theorem nirenberg_diffQuot_g_localL2_bound_quantitative
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u f : E → ℝ}
    (hu_l2 : MemLp u 2 (volume : Measure E))
    (hf_l2_local : ∀ {Ω' : Set E}, IsCompact (closure Ω') →
      MemLp f 2 (volume.restrict Ω'))
    {g : Fin d → E → ℝ}
    (hg_l2 : ∀ i, MemLp (g i) 2 (volume : Measure E))
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (hN : 0 ≤ N) (h_fderiv_eta : ∀ x : E, ‖fderiv ℝ η x‖ ≤ N)
    {Ω' Ω'' : Set E} (hΩ' : IsOpen Ω') (hΩ'_closure : closure Ω' ⊆ Ω)
    (hΩ'_compact : IsCompact (closure Ω'))
    {R₀ : ℝ}
    (hh_support_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (hη_one_on_Ω'' : ∀ x ∈ Ω'', η x = 1)
    (hΩ''_meas : MeasurableSet Ω'')
    (k : Fin d)
    (h_FK_diffQuot_u_bound : ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      ∫ x in tsupport η,
          (Sobolev.diffQuot k h u x)^2
        ∂(volume : Measure E) ≤
        ∫ x in Ω', ∑ i : Fin d, ((g i) x) ^ 2 ∂(volume : Measure E))
    (h_v_test_sq_bound : ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      ∫ x, (Sobolev.NirenbergTestFunction.nirenbergTestFunction
            k h η u x)^2 ∂(volume : Measure E) ≤
        8 * N^2 *
          ∫ x in tsupport η,
              (Sobolev.diffQuot k h u x)^2
            ∂(volume : Measure E) +
        2 * ∫ x, (η x)^2 *
            (Sobolev.diffQuot k h (g k) x)^2
          ∂(volume : Measure E))
    (h_master_nonsmooth : ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      B.lam * ∫ x, (η x)^2 *
          ∑ i : Fin d, Sobolev.diffQuot k h (g i) x ^ 2
        ∂(volume : Measure E) ≤
        |∑ i : Fin d, ∑ j : Fin d, ∫ x,
              2 * Sobolev.translate k h
                (fun y : E => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              Sobolev.diffQuot k h (g i) x *
              Sobolev.diffQuot k h u x
            ∂(volume : Measure E)| +
        |∑ i : Fin d, ∑ j : Fin d, ∫ x,
              Sobolev.diffQuot k h
                (fun y : E => B.a y i j) x * (η x)^2 *
              ((g i) x) *
              Sobolev.diffQuot k h (g j) x
            ∂(volume : Measure E)| +
        |∑ i : Fin d, ∑ j : Fin d, ∫ x,
              2 * Sobolev.diffQuot k h
                (fun y : E => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              ((g i) x) *
              Sobolev.diffQuot k h u x
            ∂(volume : Measure E)| +
        |∫ x in Ω, f x *
            Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u x| +
        |∫ x in Ω, B.c x * u x *
            Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u x ∂(volume : Measure E)|) :
    ∀ ⦃h : ℝ⦄, h ≠ 0 → |h| ≤ R₀ →
      (B.lam / 2) * ∫ x in Ω'',
          ∑ i : Fin d, Sobolev.diffQuot k h (g i) x ^ 2
        ∂(volume : Measure E) ≤
        nirenbergMasterYoungConstant (d := d) B N hΩ'_compact k
          * (∫ x in Ω', ∑ i : Fin d, ((g i) x) ^ 2
              ∂(volume : Measure E) +
          ∫ x in Ω', (u x)^2 ∂(volume : Measure E) +
          ∫ x in Ω', (f x)^2 ∂(volume : Measure E)) := by
  classical
  have hC := nirenberg_master_inequality_absorbed_nonsmooth_quantitative
    (d := d) B hu_l2 hf_l2_local hg_l2 hη hη_support hη_range hN
    h_fderiv_eta hΩ' hΩ'_closure hΩ'_compact hh_support_in_Ω' k
    h_FK_diffQuot_u_bound h_v_test_sq_bound
    h_master_nonsmooth
  intro h hh hh_le
  have h_main := hC hh hh_le
  set sumSq : E → ℝ := fun x : E => ∑ i : Fin d,
    Sobolev.diffQuot k h (g i) x ^ 2
    with hsumSq_def
  have h_sumSq_nn : ∀ x : E, 0 ≤ sumSq x := by
    intro x; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have h_pointwise : ∀ x : E,
      Ω''.indicator sumSq x ≤ (η x)^2 * sumSq x := by
    intro x
    by_cases hx : x ∈ Ω''
    · rw [Set.indicator_of_mem hx]
      rw [hη_one_on_Ω'' x hx, one_pow, one_mul]
    · rw [Set.indicator_of_notMem hx]
      exact mul_nonneg (sq_nonneg _) (h_sumSq_nn x)
  have h_eta_sq_sumSq_int : Integrable (fun x : E => (η x)^2 * sumSq x)
      (volume : Measure E) := by
    have h_per_i : ∀ i : Fin d, Integrable (fun x : E =>
        (η x)^2 * (Sobolev.diffQuot k h (g i) x)^2)
        (volume : Measure E) := by
      intro i
      have hint := integrable_const_eta_sq_diffQuot_g_sq (d := d) hg_l2 hη hη_support
        i k h 1
      have h_eq : (fun x : E => (η x)^2 *
          (Sobolev.diffQuot k h (g i) x)^2) =
          (fun x : E => 1 * (η x)^2 *
          (Sobolev.diffQuot k h (g i) x)^2) := by
        funext x; ring
      rw [h_eq]
      exact hint
    have h_sum_int := integrable_finsetSum (Finset.univ : Finset (Fin d))
      (fun i _ => h_per_i i)
    have h_eq : (fun x : E => (η x)^2 * sumSq x) =
        (fun x : E => ∑ i : Fin d,
          (η x)^2 * (Sobolev.diffQuot k h (g i) x)^2) := by
      funext x
      simp only [hsumSq_def, Finset.mul_sum]
    rw [h_eq]
    exact h_sum_int
  have h_indicator_int : Integrable (fun x : E => Ω''.indicator sumSq x)
      (volume : Measure E) := by
    refine h_eta_sq_sumSq_int.mono' ?_ ?_
    · refine AEStronglyMeasurable.indicator ?_ hΩ''_meas
      have h_per_i_aesm : ∀ i : Fin d, AEStronglyMeasurable
          (fun x : E => (Sobolev.diffQuot k h (g i) x)^2)
          (volume : Measure E) := by
        intro i
        exact (aestronglyMeasurable_diffQuot (d := d) k h
          (hg_l2 i).aestronglyMeasurable).pow 2
      have h_sum_aesm : AEStronglyMeasurable
          (fun x : E => ∑ i : Fin d,
            (Sobolev.diffQuot k h (g i) x)^2)
          (volume : Measure E) := by
        have h_aux := Finset.aestronglyMeasurable_sum
          (Finset.univ : Finset (Fin d)) (fun i _ => h_per_i_aesm i)
        have h_eq : (∑ i ∈ (Finset.univ : Finset (Fin d)),
              fun x : E => (Sobolev.diffQuot k h (g i) x)^2) =
            (fun x : E => ∑ i : Fin d,
              (Sobolev.diffQuot k h (g i) x)^2) := by
          funext x
          rw [Finset.sum_apply]
        rw [h_eq] at h_aux
        exact h_aux
      exact h_sum_aesm
    · refine Filter.Eventually.of_forall ?_
      intro x
      rw [Real.norm_eq_abs]
      have h_indicator_nn : 0 ≤ Ω''.indicator sumSq x :=
        Set.indicator_nonneg (fun y _ => h_sumSq_nn y) x
      rw [abs_of_nonneg h_indicator_nn]
      exact h_pointwise x
  have h_int_le : ∫ x, Ω''.indicator sumSq x ∂(volume : Measure E) ≤
      ∫ x, (η x)^2 * sumSq x ∂(volume : Measure E) :=
    integral_mono h_indicator_int h_eta_sq_sumSq_int h_pointwise
  have h_indicator_eq : ∫ x, Ω''.indicator sumSq x ∂(volume : Measure E) =
      ∫ x in Ω'', sumSq x ∂(volume : Measure E) :=
    MeasureTheory.integral_indicator hΩ''_meas
  rw [h_indicator_eq] at h_int_le
  have h_lam_half_nn : 0 ≤ B.lam / 2 := by linarith [B.ellipticity_pos]
  have h_step1 : (B.lam / 2) * ∫ x in Ω'', sumSq x ∂(volume : Measure E) ≤
      (B.lam / 2) * ∫ x, (η x)^2 * sumSq x ∂(volume : Measure E) :=
    mul_le_mul_of_nonneg_left h_int_le h_lam_half_nn
  exact h_step1.trans h_main

end Sobolev.NirenbergCrossBoundsNonSmooth
