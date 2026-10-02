-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Nirenberg/SubstitutionIdentity/SubstitutionNonSmooth.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Nirenberg.MasterInequality.MasterInequalityNonSmooth
public import CalabiYau.Analysis.Sobolev.Nirenberg.TestFunction.WeakRegularity
public import CalabiYau.Analysis.Sobolev.Solutions.WeakSolution

@[expose] public section

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open Sobolev
open Sobolev.NirenbergEuclidean
open Sobolev.NirenbergCrossBounds
open Sobolev.NirenbergCrossBoundsNonSmooth
open Sobolev.NirenbergTestFunction
open scoped ENNReal NNReal Convolution Pointwise BigOperators InnerProductSpace
  RealInnerProductSpace

namespace Sobolev.NirenbergSubstitutionNonSmooth

variable {d : ℕ} [NeZero d]

local notation "EuclN" => EuclideanSpace ℝ (Fin d)

private lemma shiftedEllipticity_pointwise
    {Ω : Set EuclN} (B : SmoothEllipticBilinearForm d Ω)
    (V : Fin d → ℝ) (k : Fin d) (h : ℝ) {x : EuclN}
    (hx_translate : x + h • EuclideanSpace.single k 1 ∈ Ω) :
    B.lam * ∑ i : Fin d, (V i)^2 ≤
      ∑ i : Fin d, ∑ j : Fin d,
        B.a (x + h • EuclideanSpace.single k 1) i j * V i * V j := by
  classical
  set y : EuclN := x + h • EuclideanSpace.single k 1 with hy_def
  set ξ : EuclN := WithLp.toLp 2 V with hξ_def
  have hξ_ofLp : ξ.ofLp = V := by
    change (WithLp.toLp 2 V : EuclN).ofLp = V
    rfl
  have hξ_norm_sq : ‖ξ‖ ^ 2 = ∑ i : Fin d, (V i)^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl ?_
    intro i _
    change ‖(WithLp.toLp 2 V : EuclN) i‖ ^ 2 = _
    have : (WithLp.toLp 2 V : EuclN) i = V i := by rfl
    rw [this, Real.norm_eq_abs, sq_abs]
  have hcoer : B.lam * ‖ξ‖ ^ 2 ≤ ⟪ξ, DeGiorgi.matMulE (B.a y) ξ⟫_ℝ :=
    B.coercive y hx_translate ξ
  have h_inner :
      ⟪ξ, DeGiorgi.matMulE (B.a y) ξ⟫_ℝ =
        ∑ i : Fin d, ∑ j : Fin d, B.a y i j * V i * V j := by
    have hmat_ofLp : (DeGiorgi.matMulE (B.a y) ξ).ofLp = (B.a y).mulVec V := by
      rw [DeGiorgi.matMulE_ofLp, hξ_ofLp]
    change (DeGiorgi.matMulE (B.a y) ξ).ofLp ⬝ᵥ star ξ.ofLp = _
    rw [hmat_ofLp, hξ_ofLp]
    have hstarV : (star V : Fin d → ℝ) = V := by funext i; simp
    rw [hstarV]
    change ∑ i : Fin d, (B.a y).mulVec V i * V i = _
    refine Finset.sum_congr rfl ?_
    intro i _
    change (∑ j : Fin d, B.a y i j * V j) * V i = _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  rw [h_inner] at hcoer
  rw [← hξ_norm_sq]
  exact hcoer

theorem principal_term_ge_lambda_norm_sq_nonsmooth
    {Ω : Set EuclN} (B : SmoothEllipticBilinearForm d Ω)
    {g : Fin d → EuclN → ℝ}
    (hg_l2 : ∀ i, MemLp (g i) 2 (volume : Measure EuclN))
    {η : EuclN → ℝ} (hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_support : HasCompactSupport η)
    {Ω' : Set EuclN}
    (hΩ'_in_Ω : closure Ω' ⊆ Ω)
    {R₀ : ℝ}
    (hh_support_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (k : Fin d) {h : ℝ} (hh_le : |h| ≤ R₀) :
    B.lam *
      ∫ x, (η x)^2 *
        ∑ i : Fin d, (Sobolev.diffQuot k h (g i) x)^2
        ∂(volume : Measure EuclN)
    ≤ ∫ x, ∑ i : Fin d, ∑ j : Fin d,
        (Sobolev.translate k h
          (fun y : EuclN => B.a y i j)) x *
        (η x)^2 *
        Sobolev.diffQuot k h (g i) x *
        Sobolev.diffQuot k h (g j) x
      ∂(volume : Measure EuclN) := by
  classical
  have h_thick_in_Ω : Metric.cthickening |h| (tsupport η) ⊆ Ω :=
    (hh_support_in_Ω' hh_le).trans (subset_closure.trans hΩ'_in_Ω)
  have h_pointwise : ∀ x : EuclN,
      B.lam * ((η x)^2 *
          ∑ i : Fin d, (Sobolev.diffQuot k h (g i) x)^2) ≤
        ∑ i : Fin d, ∑ j : Fin d,
          (Sobolev.translate k h
            (fun y : EuclN => B.a y i j)) x *
          (η x)^2 *
          Sobolev.diffQuot k h (g i) x *
          Sobolev.diffQuot k h (g j) x := by
    intro x
    by_cases hx : x ∈ tsupport η
    · have hx_translate : x + h • EuclideanSpace.single k 1 ∈ Ω := by
        apply h_thick_in_Ω
        refine Metric.mem_cthickening_of_dist_le _ x |h| (tsupport η) hx ?_
        have hsing_norm :
            ‖(EuclideanSpace.single k (1 : ℝ) : EuclN)‖ = 1 := by simp
        have hdist_eq :
            dist (x + h • EuclideanSpace.single k 1) x = |h| := by
          rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hsing_norm, mul_one,
            Real.norm_eq_abs]
        rw [hdist_eq]
      set V : Fin d → ℝ := fun i =>
        Sobolev.diffQuot k h (g i) x with hV_def
      have h_ellip := shiftedEllipticity_pointwise (d := d) B V k h hx_translate
      have h_eta_nn : 0 ≤ (η x)^2 := sq_nonneg _
      have h_mul := mul_le_mul_of_nonneg_left h_ellip h_eta_nn
      have h_translate_eq : ∀ i j : Fin d,
          Sobolev.translate k h
            (fun y : EuclN => B.a y i j) x =
          B.a (x + h • EuclideanSpace.single k 1) i j := by
        intro i j; rfl
      have h_lhs_eq :
          B.lam * ((η x)^2 * ∑ i : Fin d, (V i)^2) =
            (η x)^2 * (B.lam * ∑ i : Fin d, (V i)^2) := by ring
      rw [h_lhs_eq]
      refine h_mul.trans ?_
      apply le_of_eq
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [h_translate_eq i j]
      ring
    · have hη_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx
      have h_lhs : B.lam * ((η x)^2 *
          ∑ i : Fin d, (Sobolev.diffQuot k h (g i) x)^2) = 0 := by
        rw [hη_zero]; ring
      rw [h_lhs]
      have h_rhs_eq : ∑ i : Fin d, ∑ j : Fin d,
          (Sobolev.translate k h
            (fun y : EuclN => B.a y i j)) x *
          (η x)^2 *
          Sobolev.diffQuot k h (g i) x *
          Sobolev.diffQuot k h (g j) x = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i _
        refine Finset.sum_eq_zero ?_
        intro j _
        rw [hη_zero]; ring
      rw [h_rhs_eq]
  have h_lhs_factor :
      B.lam *
        ∫ x, (η x)^2 *
          ∑ i : Fin d, (Sobolev.diffQuot k h (g i) x)^2
        ∂(volume : Measure EuclN) =
      ∫ x, B.lam * ((η x)^2 *
          ∑ i : Fin d, (Sobolev.diffQuot k h (g i) x)^2)
        ∂(volume : Measure EuclN) := by
    rw [integral_const_mul]
  rw [h_lhs_factor]
  have hη_smooth_top : ContDiff ℝ (⊤ : ℕ∞) η := hη_smooth
  have h_lhs_int : Integrable (fun x : EuclN => B.lam * ((η x)^2 *
      ∑ i : Fin d, (Sobolev.diffQuot k h (g i) x)^2))
      (volume : Measure EuclN) := by
    have h_per_i : ∀ i : Fin d, Integrable (fun x : EuclN =>
        (η x)^2 * (Sobolev.diffQuot k h (g i) x)^2)
        (volume : Measure EuclN) := by
      intro i
      have hint := integrable_const_eta_sq_diffQuot_g_sq (d := d) hg_l2 hη_smooth_top
        hη_support i k h 1
      have h_eq : (fun x : EuclN => (η x)^2 *
          (Sobolev.diffQuot k h (g i) x)^2) =
          (fun x : EuclN => 1 * (η x)^2 *
          (Sobolev.diffQuot k h (g i) x)^2) := by
        funext x; ring
      rw [h_eq]
      exact hint
    have h_sum_int := integrable_finsetSum (Finset.univ : Finset (Fin d))
      (fun i _ => h_per_i i)
    have h_eq_outer : (fun x : EuclN => B.lam * ((η x)^2 *
        ∑ i : Fin d, (Sobolev.diffQuot k h (g i) x)^2)) =
        (fun x : EuclN => B.lam * ∑ i : Fin d,
          (η x)^2 * (Sobolev.diffQuot k h (g i) x)^2) := by
      funext x
      rw [Finset.mul_sum]
    rw [h_eq_outer]
    exact h_sum_int.const_mul B.lam
  have h_rhs_per_ij_int : ∀ i j : Fin d, Integrable (fun x : EuclN =>
      (Sobolev.translate k h
        (fun y : EuclN => B.a y i j)) x *
      (η x)^2 *
      Sobolev.diffQuot k h (g i) x *
      Sobolev.diffQuot k h (g j) x)
      (volume : Measure EuclN) := by
    intro i j
    classical
    have hη_sq_cont : Continuous (fun x : EuclN => η x ^ 2) := hη_smooth.continuous.pow 2
    have hη_sq_support : HasCompactSupport (fun x : EuclN => η x ^ 2) := by
      have heq : (fun y : EuclN => η y ^ 2) = (fun y : EuclN => η y * η y) := by
        funext y; ring
      rw [heq]; exact hη_support.mul_right
    obtain ⟨Mη2, _, hMη2⟩ :=
      exists_bound_of_continuous_compactSupport hη_sq_cont hη_sq_support
    have h_translate_a_cont : Continuous
        (Sobolev.translate k h
          (fun y : EuclN => B.a y i j)) := by
      unfold Sobolev.translate
      exact (B.continuous_a i j).comp (continuous_id.add continuous_const)
    have h_prod_cont : Continuous
        (fun x : EuclN => (η x)^2 *
          (Sobolev.translate k h
            (fun y : EuclN => B.a y i j)) x) :=
      hη_sq_cont.mul h_translate_a_cont
    have h_prod_support : HasCompactSupport
        (fun x : EuclN => (η x)^2 *
          (Sobolev.translate k h
            (fun y : EuclN => B.a y i j)) x) :=
      hη_sq_support.mul_right
    obtain ⟨Mprod, hMprod_nn, hMprod⟩ :=
      exists_bound_of_continuous_compactSupport h_prod_cont h_prod_support
    have h_dq_g_l2 : ∀ i', MemLp
        (Sobolev.diffQuot k h (g i')) 2
        (volume : Measure EuclN) :=
      fun i' => memLp_diffQuot_two k h (hg_l2 i')
    have h_dq_g_sq_int : ∀ i', Integrable (fun x : EuclN =>
        (Sobolev.diffQuot k h (g i') x)^2)
        (volume : Measure EuclN) := by
      intro i'
      have h_dq_norm_sq_int : Integrable (fun x : EuclN =>
          ‖Sobolev.diffQuot k h (g i') x‖ ^ (2 : ℕ))
          (volume : Measure EuclN) := by
        have hh := (h_dq_g_l2 i').integrable_norm_rpow
          (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
        have h_pow_eq : (2 : ℝ≥0∞).toReal = 2 := by show ENNReal.toReal 2 = 2; rfl
        rw [h_pow_eq] at hh
        have heq : (fun x : EuclN =>
            ‖Sobolev.diffQuot k h (g i') x‖ ^ (2 : ℝ)) =
            (fun x : EuclN =>
            ‖Sobolev.diffQuot k h (g i') x‖ ^ (2 : ℕ)) := by
          funext x
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_cast, Real.rpow_natCast]
        rw [heq] at hh
        exact hh
      have heq2 : (fun x : EuclN =>
          (Sobolev.diffQuot k h (g i') x)^2) =
          (fun x : EuclN =>
          ‖Sobolev.diffQuot k h (g i') x‖ ^ (2 : ℕ)) := by
        funext x
        rw [Real.norm_eq_abs, sq_abs]
      rw [heq2]
      exact h_dq_norm_sq_int
    have h_upper_int : Integrable (fun x : EuclN => (Mprod / 2) *
        ((Sobolev.diffQuot k h (g i) x)^2 +
         (Sobolev.diffQuot k h (g j) x)^2))
        (volume : Measure EuclN) :=
      ((h_dq_g_sq_int i).add (h_dq_g_sq_int j)).const_mul (Mprod / 2)
    have h_lhs_aesm : AEStronglyMeasurable
        (fun x : EuclN =>
          (Sobolev.translate k h
            (fun y : EuclN => B.a y i j)) x *
          (η x)^2 *
          Sobolev.diffQuot k h (g i) x *
          Sobolev.diffQuot k h (g j) x)
        (volume : Measure EuclN) := by
      have h_ta_aesm : AEStronglyMeasurable
          (Sobolev.translate k h
            (fun y : EuclN => B.a y i j))
          (volume : Measure EuclN) := h_translate_a_cont.aestronglyMeasurable
      have h_eta_aesm : AEStronglyMeasurable (fun x : EuclN => (η x)^2)
          (volume : Measure EuclN) := hη_sq_cont.aestronglyMeasurable
      have h_dq_aesm_i : AEStronglyMeasurable
          (Sobolev.diffQuot k h (g i))
          (volume : Measure EuclN) :=
        aestronglyMeasurable_diffQuot (d := d) k h (hg_l2 i).aestronglyMeasurable
      have h_dq_aesm_j : AEStronglyMeasurable
          (Sobolev.diffQuot k h (g j))
          (volume : Measure EuclN) :=
        aestronglyMeasurable_diffQuot (d := d) k h (hg_l2 j).aestronglyMeasurable
      exact ((h_ta_aesm.mul h_eta_aesm).mul h_dq_aesm_i).mul h_dq_aesm_j
    refine h_upper_int.mono' h_lhs_aesm ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    set X : ℝ := Sobolev.diffQuot k h (g i) x with hX_def
    set Y : ℝ := Sobolev.diffQuot k h (g j) x with hY_def
    set τaη2 : ℝ := (Sobolev.translate k h
        (fun y : EuclN => B.a y i j)) x * (η x)^2 with hτaη2_def
    have h_τaη2_eq_swap : (Sobolev.translate k h
        (fun y : EuclN => B.a y i j)) x * (η x)^2 =
        (η x)^2 * (Sobolev.translate k h
          (fun y : EuclN => B.a y i j)) x := by ring
    have h_τaη2_bound : |τaη2| ≤ Mprod := by
      rw [hτaη2_def]
      have hb := hMprod x
      have h_swap_eq :
          (Sobolev.translate k h
            (fun y : EuclN => B.a y i j)) x * (η x) ^ 2 =
          (η x) ^ 2 * (Sobolev.translate k h
            (fun y : EuclN => B.a y i j)) x := by ring
      rw [h_swap_eq]
      exact hb
    have h_lhs_eq : (Sobolev.translate k h
        (fun y : EuclN => B.a y i j)) x * (η x)^2 *
        Sobolev.diffQuot k h (g i) x *
        Sobolev.diffQuot k h (g j) x =
        τaη2 * X * Y := by
      change (Sobolev.translate k h
        (fun y : EuclN => B.a y i j)) x * (η x)^2 * X * Y =
        (Sobolev.translate k h
        (fun y : EuclN => B.a y i j)) x * (η x)^2 * X * Y
      rfl
    rw [h_lhs_eq]
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have h_iX_nn : 0 ≤ |X| := abs_nonneg _
    have h_iY_nn : 0 ≤ |Y| := abs_nonneg _
    have h_step1 : |τaη2| * |X| ≤ Mprod * |X| :=
      mul_le_mul_of_nonneg_right h_τaη2_bound h_iX_nn
    have h_step2 : |τaη2| * |X| * |Y| ≤ Mprod * |X| * |Y| :=
      mul_le_mul_of_nonneg_right h_step1 h_iY_nn
    have h_amgm : 2 * |X| * |Y| ≤ X^2 + Y^2 := by
      have h := two_mul_le_add_sq |X| |Y|
      rw [sq_abs, sq_abs] at h
      exact h
    have h_amgm_half : |X| * |Y| ≤ (1/2) * (X^2 + Y^2) := by linarith
    have h_step3 : Mprod * |X| * |Y| ≤ Mprod * ((1/2) * (X^2 + Y^2)) := by
      have h_swap : Mprod * |X| * |Y| = Mprod * (|X| * |Y|) := by ring
      rw [h_swap]
      exact mul_le_mul_of_nonneg_left h_amgm_half hMprod_nn
    have h_final : Mprod * ((1/2) * (X^2 + Y^2)) = (Mprod / 2) * (X^2 + Y^2) := by ring
    rw [← h_final]
    exact h_step2.trans h_step3
  have h_rhs_int : Integrable (fun x : EuclN => ∑ i : Fin d, ∑ j : Fin d,
      (Sobolev.translate k h
        (fun y : EuclN => B.a y i j)) x *
      (η x)^2 *
      Sobolev.diffQuot k h (g i) x *
      Sobolev.diffQuot k h (g j) x)
      (volume : Measure EuclN) := by
    have h_inner : ∀ i : Fin d, Integrable (fun x : EuclN =>
        ∑ j : Fin d,
        (Sobolev.translate k h
          (fun y : EuclN => B.a y i j)) x *
        (η x)^2 *
        Sobolev.diffQuot k h (g i) x *
        Sobolev.diffQuot k h (g j) x)
        (volume : Measure EuclN) :=
      fun i => integrable_finsetSum _ (fun j _ => h_rhs_per_ij_int i j)
    exact integrable_finsetSum _ (fun i _ => h_inner i)
  exact integral_mono h_lhs_int h_rhs_int h_pointwise

end Sobolev.NirenbergSubstitutionNonSmooth
