-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Nirenberg/MasterInequality/Coercivity.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Nirenberg.SubstitutionIdentity.Substitution

@[expose] public section

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open Sobolev
open Sobolev.NirenbergEuclidean
open Sobolev.NirenbergTestFunction
open Sobolev.NirenbergSubstitution
open scoped ENNReal NNReal Convolution Pointwise BigOperators InnerProductSpace

namespace Sobolev.NirenbergCoercivity

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

private def shiftedPrincipal
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (u : E → ℝ) (k : Fin d) (h : ℝ) (x : E) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d,
    Sobolev.translate k h
      (fun y : E => B.a y i j) x *
      Sobolev.diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
      Sobolev.diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x

private def diffQuotGradient
    (u : E → ℝ) (k : Fin d) (h : ℝ) (x : E) : E :=
  WithLp.toLp 2 (fun i : Fin d =>
    Sobolev.diffQuot k h
      (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)

omit [NeZero d] in
private lemma diffQuotGradient_norm_sq
    (u : E → ℝ) (k : Fin d) (h : ℝ) (x : E) :
    ‖diffQuotGradient u k h x‖ ^ 2 =
      ∑ i : Fin d,
        Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2 := by
  unfold diffQuotGradient
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl ?_
  intro i _
  change ‖Sobolev.diffQuot k h
      (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x‖ ^ 2 = _
  rw [Real.norm_eq_abs, sq_abs]

private theorem shiftedPrincipal_ge
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (u : E → ℝ) (k : Fin d) (h : ℝ) {x : E}
    (hx_translate : x + h • EuclideanSpace.single k 1 ∈ Ω) :
    B.lam * ‖diffQuotGradient u k h x‖ ^ 2 ≤
      shiftedPrincipal B u k h x := by
  classical
  set y : E := x + h • EuclideanSpace.single k 1 with hy_def
  set ξ : E := diffQuotGradient u k h x with hξ_def
  set V : Fin d → ℝ := fun i =>
    Sobolev.diffQuot k h
      (fun z : E => (fderiv ℝ u z) (EuclideanSpace.single i 1)) x with hV_def
  have hξofLp : ξ.ofLp = V := by simp [hξ_def, hV_def, diffQuotGradient]
  have hcoer : B.lam * ‖ξ‖ ^ 2 ≤ ⟪ξ, DeGiorgi.matMulE (B.a y) ξ⟫_ℝ :=
    B.coercive y hx_translate ξ
  have h_inner :
      ⟪ξ, DeGiorgi.matMulE (B.a y) ξ⟫_ℝ =
        ∑ i : Fin d, ∑ j : Fin d,
          B.a y i j * V i * V j := by
    have hmatofLp : (DeGiorgi.matMulE (B.a y) ξ).ofLp = (B.a y).mulVec V := by
      rw [DeGiorgi.matMulE_ofLp, hξofLp]
    change (DeGiorgi.matMulE (B.a y) ξ).ofLp ⬝ᵥ star ξ.ofLp = _
    rw [hmatofLp, hξofLp]
    have hstarV : (star V : Fin d → ℝ) = V := by
      funext i; simp
    rw [hstarV]
    change ∑ i : Fin d, (B.a y).mulVec V i * V i = _
    refine Finset.sum_congr rfl ?_
    intro i _
    change (∑ j : Fin d, B.a y i j * V j) * V i = ∑ j : Fin d, B.a y i j * V i * V j
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  have h_target :
      shiftedPrincipal B u k h x =
        ∑ i : Fin d, ∑ j : Fin d, B.a y i j * V i * V j := by
    unfold shiftedPrincipal
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    change Sobolev.translate k h
              (fun z : E => B.a z i j) x *
            Sobolev.diffQuot k h
              (fun z : E => (fderiv ℝ u z) (EuclideanSpace.single i 1)) x *
            Sobolev.diffQuot k h
              (fun z : E => (fderiv ℝ u z) (EuclideanSpace.single j 1)) x =
          B.a y i j * V i * V j
    rfl
  rw [h_target]
  rw [h_inner] at hcoer
  exact hcoer

private theorem principal_integrand_pointwise_decomposition
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (i j k : Fin d) {h : ℝ} (hh : h ≠ 0) (x : E) :
    Sobolev.diffQuot k h
        (fun y : E => B.a y i j *
          ((fderiv ℝ u y) (EuclideanSpace.single i 1))) x *
      ((fderiv ℝ
          (fun y : E => η y ^ 2 *
            Sobolev.diffQuot k h u y) x)
        (EuclideanSpace.single j 1)) =
      Sobolev.translate k h
          (fun y : E => B.a y i j) x * (η x)^2 *
        Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
        Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x +
      2 * Sobolev.translate k h
          (fun y : E => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
        Sobolev.diffQuot k h u x +
      Sobolev.diffQuot k h
          (fun y : E => B.a y i j) x * (η x)^2 *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x +
      2 * Sobolev.diffQuot k h
          (fun y : E => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        Sobolev.diffQuot k h u x := by
  have h_first : Sobolev.diffQuot k h
        (fun y : E => B.a y i j *
          ((fderiv ℝ u y) (EuclideanSpace.single i 1))) x =
      Sobolev.translate k h
          (fun y : E => B.a y i j) x *
        Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x +
      Sobolev.diffQuot k h
          (fun y : E => B.a y i j) x *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) :=
    diffQuot_coeff_apply (d := d) k h
      (fun y : E => B.a y i j)
      (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x
  have h_second :
      ((fderiv ℝ
          (fun y : E => η y ^ 2 *
            Sobolev.diffQuot k h u y) x)
        (EuclideanSpace.single j 1)) =
      2 * η x * ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        Sobolev.diffQuot k h u x +
      η x ^ 2 *
        Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x :=
    fderiv_eta_sq_times_diffQuot_apply (d := d) hη hu k j hh x
  rw [h_first, h_second]
  ring

omit [NeZero d] in
private lemma continuous_diffQuot_of_contDiff
    {v : E → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) (k : Fin d) (h : ℝ) :
    Continuous (Sobolev.diffQuot k h v) := by
  by_cases hh : h = 0
  · subst hh
    rw [Sobolev.diffQuot_zero_h]
    exact continuous_const
  · exact (contDiff_diffQuot_of_contDiff (d := d) hv k hh).continuous

omit [NeZero d] in
private lemma continuous_translate_of_continuous
    {v : E → ℝ} (hv : Continuous v) (k : Fin d) (h : ℝ) :
    Continuous (Sobolev.translate k h v) := by
  unfold Sobolev.translate
  have h_translate_map :
      Continuous (fun y : E => y + h • EuclideanSpace.single k 1) :=
    continuous_id.add continuous_const
  exact hv.comp h_translate_map

theorem nirenberg_principal_decomposition
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    ∑ i : Fin d, ∑ j : Fin d, ∫ x,
        Sobolev.diffQuot k h
            (fun y : E => B.a y i j *
              ((fderiv ℝ u y) (EuclideanSpace.single i 1))) x *
          ((fderiv ℝ
              (fun y : E => η y ^ 2 *
                Sobolev.diffQuot k h u y) x)
            (EuclideanSpace.single j 1))
        ∂(volume : Measure E) =
      (∑ i : Fin d, ∑ j : Fin d, ∫ x,
          Sobolev.translate k h
              (fun y : E => B.a y i j) x * (η x)^2 *
            Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
            Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x
          ∂(volume : Measure E)) +
      (∑ i : Fin d, ∑ j : Fin d, ∫ x,
          2 * Sobolev.translate k h
              (fun y : E => B.a y i j) x * (η x) *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
            Sobolev.diffQuot k h u x
          ∂(volume : Measure E)) +
      (∑ i : Fin d, ∑ j : Fin d, ∫ x,
          Sobolev.diffQuot k h
              (fun y : E => B.a y i j) x * (η x)^2 *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
            Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x
          ∂(volume : Measure E)) +
      (∑ i : Fin d, ∑ j : Fin d, ∫ x,
          2 * Sobolev.diffQuot k h
              (fun y : E => B.a y i j) x * (η x) *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
            Sobolev.diffQuot k h u x
          ∂(volume : Measure E)) := by
  classical
  have hu_C1 : ContDiff ℝ 1 u := hu.of_le (by norm_cast)
  have hη_C1 : ContDiff ℝ 1 η := hη.of_le (by norm_cast)
  have h_eta_sq_support : HasCompactSupport (fun y : E => η y ^ 2) := by
    have heq : (fun y : E => η y ^ 2) = (fun y : E => η y * η y) := by
      funext y; ring
    rw [heq]
    exact hη_support.mul_right
  have h_pair : ∀ i j : Fin d, ∀ x : E,
      Sobolev.diffQuot k h
            (fun y : E => B.a y i j *
              ((fderiv ℝ u y) (EuclideanSpace.single i 1))) x *
          ((fderiv ℝ
              (fun y : E => η y ^ 2 *
                Sobolev.diffQuot k h u y) x)
            (EuclideanSpace.single j 1)) =
        Sobolev.translate k h
            (fun y : E => B.a y i j) x * (η x)^2 *
          Sobolev.diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
          Sobolev.diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x +
        2 * Sobolev.translate k h
            (fun y : E => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          Sobolev.diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
          Sobolev.diffQuot k h u x +
        Sobolev.diffQuot k h
            (fun y : E => B.a y i j) x * (η x)^2 *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
          Sobolev.diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x +
        2 * Sobolev.diffQuot k h
            (fun y : E => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
          Sobolev.diffQuot k h u x := by
    intro i j x
    exact principal_integrand_pointwise_decomposition (d := d) B hu hη i j k hh x
  let T1 : Fin d → Fin d → E → ℝ := fun i j x =>
    Sobolev.translate k h
        (fun y : E => B.a y i j) x * (η x)^2 *
      Sobolev.diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
      Sobolev.diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x
  let T2 : Fin d → Fin d → E → ℝ := fun i j x =>
    2 * Sobolev.translate k h
        (fun y : E => B.a y i j) x * (η x) *
      ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
      Sobolev.diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
      Sobolev.diffQuot k h u x
  let T3 : Fin d → Fin d → E → ℝ := fun i j x =>
    Sobolev.diffQuot k h
        (fun y : E => B.a y i j) x * (η x)^2 *
      ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
      Sobolev.diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x
  let T4 : Fin d → Fin d → E → ℝ := fun i j x =>
    2 * Sobolev.diffQuot k h
        (fun y : E => B.a y i j) x * (η x) *
      ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
      ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
      Sobolev.diffQuot k h u x
  let LHSint : Fin d → Fin d → E → ℝ := fun i j x =>
    Sobolev.diffQuot k h
        (fun y : E => B.a y i j *
          ((fderiv ℝ u y) (EuclideanSpace.single i 1))) x *
      ((fderiv ℝ
          (fun y : E => η y ^ 2 *
            Sobolev.diffQuot k h u y) x)
        (EuclideanSpace.single j 1))
  have h_LHS_eq : ∀ i j : Fin d, ∀ x : E,
      LHSint i j x = T1 i j x + T2 i j x + T3 i j x + T4 i j x := h_pair
  have h_a_cont : ∀ i j : Fin d, Continuous (fun y : E => B.a y i j) :=
    fun i j => B.continuous_a i j
  have h_translate_a_cont : ∀ i j : Fin d,
      Continuous (Sobolev.translate k h
        (fun y : E => B.a y i j)) :=
    fun i j => continuous_translate_of_continuous (d := d)
      (h_a_cont i j) k h
  have h_partial_u_cont : ∀ i : Fin d,
      Continuous (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) :=
    fun i => (hu_C1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have h_partial_η_cont : ∀ j : Fin d,
      Continuous (fun y : E => (fderiv ℝ η y) (EuclideanSpace.single j 1)) :=
    fun j => (hη_C1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have h_diffQuot_partial_u_cont : ∀ i : Fin d,
      Continuous (Sobolev.diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1))) := by
    intro i
    have h_smooth :
        ContDiff ℝ (⊤ : ℕ∞)
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) := by
      have h_fderiv_smooth : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ u) :=
        hu.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
      have h_apply_smooth :
          ContDiff ℝ (⊤ : ℕ∞)
            (fun T : E →L[ℝ] ℝ => T (EuclideanSpace.single i 1)) :=
        (ContinuousLinearMap.apply ℝ ℝ
          (EuclideanSpace.single i (1 : ℝ))).contDiff
      exact h_apply_smooth.comp h_fderiv_smooth
    exact continuous_diffQuot_of_contDiff (d := d) h_smooth k h
  have h_diffQuot_a_cont : ∀ i j : Fin d,
      Continuous (Sobolev.diffQuot k h
        (fun y : E => B.a y i j)) :=
    fun i j => continuous_diffQuot_of_contDiff (d := d) (B.contDiff_a i j) k h
  have h_diffQuot_u_cont :
      Continuous (Sobolev.diffQuot k h u) :=
    continuous_diffQuot_of_contDiff (d := d) hu k h
  have hT1_cont : ∀ i j : Fin d, Continuous (T1 i j) := by
    intro i j
    refine ((((h_translate_a_cont i j).mul (hη.continuous.pow 2)).mul
      (h_diffQuot_partial_u_cont i)).mul
      (h_diffQuot_partial_u_cont j))
  have hT2_cont : ∀ i j : Fin d, Continuous (T2 i j) := by
    intro i j
    refine (((((continuous_const : Continuous (fun _ : E => (2 : ℝ))).mul
      (h_translate_a_cont i j)).mul hη.continuous).mul
      (h_partial_η_cont j)).mul (h_diffQuot_partial_u_cont i)).mul
      h_diffQuot_u_cont
  have hT3_cont : ∀ i j : Fin d, Continuous (T3 i j) := by
    intro i j
    refine ((((h_diffQuot_a_cont i j).mul (hη.continuous.pow 2)).mul
      (h_partial_u_cont i)).mul (h_diffQuot_partial_u_cont j))
  have hT4_cont : ∀ i j : Fin d, Continuous (T4 i j) := by
    intro i j
    refine (((((continuous_const : Continuous (fun _ : E => (2 : ℝ))).mul
      (h_diffQuot_a_cont i j)).mul hη.continuous).mul
      (h_partial_η_cont j)).mul (h_partial_u_cont i)).mul h_diffQuot_u_cont
  have hLHS_cont_via_eq : ∀ i j : Fin d, Continuous (LHSint i j) := by
    intro i j
    have heq_fun : LHSint i j = (fun x => T1 i j x + T2 i j x + T3 i j x + T4 i j x) := by
      funext x
      exact h_LHS_eq i j x
    rw [heq_fun]
    exact (((hT1_cont i j).add (hT2_cont i j)).add (hT3_cont i j)).add
      (hT4_cont i j)
  have hT1_support : ∀ i j : Fin d, HasCompactSupport (T1 i j) := by
    intro i j
    have h_factor_support : HasCompactSupport (fun x : E => (η x)^2) := h_eta_sq_support
    change HasCompactSupport (fun x : E =>
      Sobolev.translate k h
          (fun y : E => B.a y i j) x * (η x)^2 *
        Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
        Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)
    have h_step1 : HasCompactSupport (fun x : E =>
        Sobolev.translate k h
            (fun y : E => B.a y i j) x * (η x)^2) :=
      h_eta_sq_support.mul_left
    have h_step2 : HasCompactSupport (fun x : E =>
        Sobolev.translate k h
            (fun y : E => B.a y i j) x * (η x)^2 *
          Sobolev.diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x) :=
      h_step1.mul_right
    exact h_step2.mul_right
  have hT2_support : ∀ i j : Fin d, HasCompactSupport (T2 i j) := by
    intro i j
    change HasCompactSupport (fun x : E =>
      2 * Sobolev.translate k h
          (fun y : E => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
        Sobolev.diffQuot k h u x)
    have h_step1 : HasCompactSupport (fun x : E =>
        2 * Sobolev.translate k h
            (fun y : E => B.a y i j) x * (η x)) := hη_support.mul_left
    have h_step2 : HasCompactSupport (fun x : E =>
        2 * Sobolev.translate k h
            (fun y : E => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1))) := h_step1.mul_right
    have h_step3 : HasCompactSupport (fun x : E =>
        2 * Sobolev.translate k h
            (fun y : E => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          Sobolev.diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x) :=
      h_step2.mul_right
    exact h_step3.mul_right
  have hT3_support : ∀ i j : Fin d, HasCompactSupport (T3 i j) := by
    intro i j
    change HasCompactSupport (fun x : E =>
      Sobolev.diffQuot k h
          (fun y : E => B.a y i j) x * (η x)^2 *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)
    have h_step1 : HasCompactSupport (fun x : E =>
        Sobolev.diffQuot k h
            (fun y : E => B.a y i j) x * (η x)^2) :=
      h_eta_sq_support.mul_left
    have h_step2 : HasCompactSupport (fun x : E =>
        Sobolev.diffQuot k h
            (fun y : E => B.a y i j) x * (η x)^2 *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1))) :=
      h_step1.mul_right
    exact h_step2.mul_right
  have hT4_support : ∀ i j : Fin d, HasCompactSupport (T4 i j) := by
    intro i j
    change HasCompactSupport (fun x : E =>
      2 * Sobolev.diffQuot k h
          (fun y : E => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        Sobolev.diffQuot k h u x)
    have h_step1 : HasCompactSupport (fun x : E =>
        2 * Sobolev.diffQuot k h
            (fun y : E => B.a y i j) x * (η x)) := hη_support.mul_left
    have h_step2 : HasCompactSupport (fun x : E =>
        2 * Sobolev.diffQuot k h
            (fun y : E => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1))) := h_step1.mul_right
    have h_step3 : HasCompactSupport (fun x : E =>
        2 * Sobolev.diffQuot k h
            (fun y : E => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1))) :=
      h_step2.mul_right
    exact h_step3.mul_right
  have hLHS_support : ∀ i j : Fin d, HasCompactSupport (LHSint i j) := by
    intro i j
    have heq_fun : LHSint i j = (fun x => T1 i j x + T2 i j x + T3 i j x + T4 i j x) := by
      funext x
      exact h_LHS_eq i j x
    rw [heq_fun]
    exact (((hT1_support i j).add (hT2_support i j)).add (hT3_support i j)).add
      (hT4_support i j)
  have hT1_int : ∀ i j : Fin d, Integrable (T1 i j) volume := fun i j =>
    (hT1_cont i j).integrable_of_hasCompactSupport (hT1_support i j)
  have hT2_int : ∀ i j : Fin d, Integrable (T2 i j) volume := fun i j =>
    (hT2_cont i j).integrable_of_hasCompactSupport (hT2_support i j)
  have hT3_int : ∀ i j : Fin d, Integrable (T3 i j) volume := fun i j =>
    (hT3_cont i j).integrable_of_hasCompactSupport (hT3_support i j)
  have hT4_int : ∀ i j : Fin d, Integrable (T4 i j) volume := fun i j =>
    (hT4_cont i j).integrable_of_hasCompactSupport (hT4_support i j)
  have h_pair_int : ∀ i j : Fin d,
      ∫ x, LHSint i j x ∂(volume : Measure E) =
        ∫ x, T1 i j x ∂(volume : Measure E) +
        ∫ x, T2 i j x ∂(volume : Measure E) +
        ∫ x, T3 i j x ∂(volume : Measure E) +
        ∫ x, T4 i j x ∂(volume : Measure E) := by
    intro i j
    have heq_fun : LHSint i j = (fun x => T1 i j x + T2 i j x + T3 i j x + T4 i j x) := by
      funext x
      exact h_LHS_eq i j x
    rw [heq_fun]
    have h_step1 :
        ∫ x, T1 i j x + T2 i j x + T3 i j x + T4 i j x ∂(volume : Measure E) =
          (∫ x, T1 i j x + T2 i j x + T3 i j x ∂(volume : Measure E)) +
          ∫ x, T4 i j x ∂(volume : Measure E) :=
      integral_add ((hT1_int i j).add (hT2_int i j) |>.add (hT3_int i j))
        (hT4_int i j)
    have h_step2 :
        ∫ x, T1 i j x + T2 i j x + T3 i j x ∂(volume : Measure E) =
          (∫ x, T1 i j x + T2 i j x ∂(volume : Measure E)) +
          ∫ x, T3 i j x ∂(volume : Measure E) :=
      integral_add ((hT1_int i j).add (hT2_int i j)) (hT3_int i j)
    have h_step3 :
        ∫ x, T1 i j x + T2 i j x ∂(volume : Measure E) =
          (∫ x, T1 i j x ∂(volume : Measure E)) +
          ∫ x, T2 i j x ∂(volume : Measure E) :=
      integral_add (hT1_int i j) (hT2_int i j)
    rw [h_step1, h_step2, h_step3]
  rw [show (∑ i : Fin d, ∑ j : Fin d, ∫ x, LHSint i j x ∂(volume : Measure E)) =
      ∑ i : Fin d, ∑ j : Fin d, (∫ x, T1 i j x ∂(volume : Measure E) +
        ∫ x, T2 i j x ∂(volume : Measure E) +
        ∫ x, T3 i j x ∂(volume : Measure E) +
        ∫ x, T4 i j x ∂(volume : Measure E)) from ?_]
  · have h_split : ∀ i : Fin d,
        (∑ j : Fin d, (∫ x, T1 i j x ∂(volume : Measure E) +
            ∫ x, T2 i j x ∂(volume : Measure E) +
            ∫ x, T3 i j x ∂(volume : Measure E) +
            ∫ x, T4 i j x ∂(volume : Measure E))) =
          (∑ j : Fin d, ∫ x, T1 i j x ∂(volume : Measure E)) +
          (∑ j : Fin d, ∫ x, T2 i j x ∂(volume : Measure E)) +
          (∑ j : Fin d, ∫ x, T3 i j x ∂(volume : Measure E)) +
          (∑ j : Fin d, ∫ x, T4 i j x ∂(volume : Measure E)) := by
      intro i
      rw [show (fun j : Fin d => ∫ x, T1 i j x ∂(volume : Measure E) +
              ∫ x, T2 i j x ∂(volume : Measure E) +
              ∫ x, T3 i j x ∂(volume : Measure E) +
              ∫ x, T4 i j x ∂(volume : Measure E)) =
          (fun j : Fin d => (∫ x, T1 i j x ∂(volume : Measure E) +
              ∫ x, T2 i j x ∂(volume : Measure E) +
              ∫ x, T3 i j x ∂(volume : Measure E)) +
              ∫ x, T4 i j x ∂(volume : Measure E)) from rfl]
      rw [Finset.sum_add_distrib]
      rw [show (fun j : Fin d => ∫ x, T1 i j x ∂(volume : Measure E) +
              ∫ x, T2 i j x ∂(volume : Measure E) +
              ∫ x, T3 i j x ∂(volume : Measure E)) =
          (fun j : Fin d => (∫ x, T1 i j x ∂(volume : Measure E) +
              ∫ x, T2 i j x ∂(volume : Measure E)) +
              ∫ x, T3 i j x ∂(volume : Measure E)) from rfl]
      rw [Finset.sum_add_distrib]
      rw [Finset.sum_add_distrib]
    rw [show (fun i : Fin d => ∑ j : Fin d, (∫ x, T1 i j x ∂(volume : Measure E) +
            ∫ x, T2 i j x ∂(volume : Measure E) +
            ∫ x, T3 i j x ∂(volume : Measure E) +
            ∫ x, T4 i j x ∂(volume : Measure E))) =
        (fun i : Fin d => ((∑ j : Fin d, ∫ x, T1 i j x ∂(volume : Measure E)) +
            (∑ j : Fin d, ∫ x, T2 i j x ∂(volume : Measure E)) +
            (∑ j : Fin d, ∫ x, T3 i j x ∂(volume : Measure E)) +
            (∑ j : Fin d, ∫ x, T4 i j x ∂(volume : Measure E)))) from
        funext (fun i => h_split i)]
    rw [show (fun i : Fin d => (∑ j : Fin d, ∫ x, T1 i j x ∂(volume : Measure E)) +
            (∑ j : Fin d, ∫ x, T2 i j x ∂(volume : Measure E)) +
            (∑ j : Fin d, ∫ x, T3 i j x ∂(volume : Measure E)) +
            (∑ j : Fin d, ∫ x, T4 i j x ∂(volume : Measure E))) =
        (fun i : Fin d => ((∑ j : Fin d, ∫ x, T1 i j x ∂(volume : Measure E)) +
            (∑ j : Fin d, ∫ x, T2 i j x ∂(volume : Measure E)) +
            (∑ j : Fin d, ∫ x, T3 i j x ∂(volume : Measure E))) +
            (∑ j : Fin d, ∫ x, T4 i j x ∂(volume : Measure E))) from rfl]
    rw [Finset.sum_add_distrib]
    rw [show (fun i : Fin d => (∑ j : Fin d, ∫ x, T1 i j x ∂(volume : Measure E)) +
            (∑ j : Fin d, ∫ x, T2 i j x ∂(volume : Measure E)) +
            (∑ j : Fin d, ∫ x, T3 i j x ∂(volume : Measure E))) =
        (fun i : Fin d => ((∑ j : Fin d, ∫ x, T1 i j x ∂(volume : Measure E)) +
            (∑ j : Fin d, ∫ x, T2 i j x ∂(volume : Measure E))) +
            (∑ j : Fin d, ∫ x, T3 i j x ∂(volume : Measure E))) from rfl]
    rw [Finset.sum_add_distrib]
    rw [Finset.sum_add_distrib]
  · refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    exact h_pair_int i j

private theorem principal_pointwise_bound
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (u : E → ℝ)
    {η : E → ℝ}
    (k : Fin d) {h : ℝ}
    (hh_support : Metric.cthickening |h| (tsupport η) ⊆ Ω) (x : E) :
    B.lam * (η x)^2 *
      ∑ i : Fin d, Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2 ≤
      (η x)^2 * shiftedPrincipal B u k h x := by
  by_cases hx : x ∈ tsupport η
  · have hx_translate : x + h • EuclideanSpace.single k 1 ∈ Ω := by
      apply hh_support
      refine Metric.mem_cthickening_of_dist_le _ x |h| (tsupport η) hx ?_
      have hsing_norm :
          ‖(EuclideanSpace.single k (1 : ℝ) : E)‖ = 1 := by simp
      have hdist_eq :
          dist (x + h • EuclideanSpace.single k 1) x =
            ‖h • EuclideanSpace.single k (1 : ℝ)‖ := by
        rw [dist_eq_norm]
        have hsub :
            (x + h • EuclideanSpace.single k 1) - x =
              h • EuclideanSpace.single k (1 : ℝ) := by
          rw [add_sub_cancel_left]
        rw [hsub]
      rw [hdist_eq]
      rw [norm_smul, hsing_norm, mul_one, Real.norm_eq_abs]
    have h_bound :=
      shiftedPrincipal_ge (d := d) B u k h hx_translate
    have h_eta_nn : 0 ≤ (η x)^2 := sq_nonneg _
    have h_grad_norm_sq :
        ‖diffQuotGradient u k h x‖ ^ 2 =
          ∑ i : Fin d,
            Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2 :=
      diffQuotGradient_norm_sq (d := d) u k h x
    rw [← h_grad_norm_sq]
    have h_mul := mul_le_mul_of_nonneg_left h_bound h_eta_nn
    have h_lhs_eq :
        B.lam * (η x)^2 * ‖diffQuotGradient u k h x‖ ^ 2 =
          (η x)^2 * (B.lam * ‖diffQuotGradient u k h x‖ ^ 2) := by
      ring
    rw [h_lhs_eq]
    exact h_mul
  · have hη_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx
    rw [hη_zero]
    simp

theorem principal_term_ge_lambda_norm_sq
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (k : Fin d) {h : ℝ}
    (hh_support : Metric.cthickening |h| (tsupport η) ⊆ Ω) :
    B.lam * ∫ x, (η x)^2 * (∑ i : Fin d,
        Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2)
      ∂(volume : Measure E) ≤
    ∑ i : Fin d, ∑ j : Fin d, ∫ x,
        Sobolev.translate k h
            (fun y : E => B.a y i j) x * (η x)^2 *
          Sobolev.diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
          Sobolev.diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x
        ∂(volume : Measure E) := by
  classical
  have hu_C1 : ContDiff ℝ 1 u := hu.of_le (by norm_cast)
  have h_eta_sq_support : HasCompactSupport (fun y : E => η y ^ 2) := by
    have heq : (fun y : E => η y ^ 2) = (fun y : E => η y * η y) := by
      funext y; ring
    rw [heq]
    exact hη_support.mul_right
  have h_diffQuot_partial_u_cont : ∀ i : Fin d,
      Continuous (Sobolev.diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1))) := by
    intro i
    have h_smooth :
        ContDiff ℝ (⊤ : ℕ∞)
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) := by
      have h_fderiv_smooth : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ u) :=
        hu.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
      have h_apply_smooth :
          ContDiff ℝ (⊤ : ℕ∞)
            (fun T : E →L[ℝ] ℝ => T (EuclideanSpace.single i 1)) :=
        (ContinuousLinearMap.apply ℝ ℝ
          (EuclideanSpace.single i (1 : ℝ))).contDiff
      exact h_apply_smooth.comp h_fderiv_smooth
    exact continuous_diffQuot_of_contDiff (d := d) h_smooth k h
  have h_a_cont : ∀ i j : Fin d, Continuous (fun y : E => B.a y i j) :=
    fun i j => B.continuous_a i j
  have h_translate_a_cont : ∀ i j : Fin d,
      Continuous (Sobolev.translate k h
        (fun y : E => B.a y i j)) :=
    fun i j => continuous_translate_of_continuous (d := d)
      (h_a_cont i j) k h
  have h_LHS_cont : Continuous (fun x : E =>
      (η x)^2 * ∑ i : Fin d, Sobolev.diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2) := by
    refine (hη.continuous.pow 2).mul ?_
    exact continuous_finsetSum _ (fun i _ => (h_diffQuot_partial_u_cont i).pow 2)
  have h_LHS_support : HasCompactSupport (fun x : E =>
      (η x)^2 * ∑ i : Fin d, Sobolev.diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2) :=
    h_eta_sq_support.mul_right
  have h_LHS_int : Integrable (fun x : E =>
      (η x)^2 * ∑ i : Fin d, Sobolev.diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2)
        volume :=
    h_LHS_cont.integrable_of_hasCompactSupport h_LHS_support
  have hT1_cont : ∀ i j : Fin d, Continuous (fun x : E =>
      Sobolev.translate k h
          (fun y : E => B.a y i j) x * (η x)^2 *
        Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
        Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x) := by
    intro i j
    refine ((((h_translate_a_cont i j).mul (hη.continuous.pow 2)).mul
      (h_diffQuot_partial_u_cont i)).mul (h_diffQuot_partial_u_cont j))
  have hT1_support : ∀ i j : Fin d, HasCompactSupport (fun x : E =>
      Sobolev.translate k h
          (fun y : E => B.a y i j) x * (η x)^2 *
        Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
        Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x) := by
    intro i j
    have h_step1 : HasCompactSupport (fun x : E =>
        Sobolev.translate k h
            (fun y : E => B.a y i j) x * (η x)^2) :=
      h_eta_sq_support.mul_left
    have h_step2 : HasCompactSupport (fun x : E =>
        Sobolev.translate k h
            (fun y : E => B.a y i j) x * (η x)^2 *
          Sobolev.diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x) :=
      h_step1.mul_right
    exact h_step2.mul_right
  have hT1_int : ∀ i j : Fin d, Integrable (fun x : E =>
      Sobolev.translate k h
          (fun y : E => B.a y i j) x * (η x)^2 *
        Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
        Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)
        volume := fun i j =>
    (hT1_cont i j).integrable_of_hasCompactSupport (hT1_support i j)
  have h_shiftedPrincipal_cont :
      Continuous (fun x : E => (η x)^2 * shiftedPrincipal B u k h x) := by
    refine (hη.continuous.pow 2).mul ?_
    unfold shiftedPrincipal
    refine continuous_finsetSum _ ?_
    intro i _
    refine continuous_finsetSum _ ?_
    intro j _
    refine ((h_translate_a_cont i j).mul (h_diffQuot_partial_u_cont i)).mul
      (h_diffQuot_partial_u_cont j)
  have h_shiftedPrincipal_support :
      HasCompactSupport (fun x : E => (η x)^2 * shiftedPrincipal B u k h x) :=
    h_eta_sq_support.mul_right
  have h_shiftedPrincipal_int :
      Integrable (fun x : E => (η x)^2 * shiftedPrincipal B u k h x) volume :=
    h_shiftedPrincipal_cont.integrable_of_hasCompactSupport
      h_shiftedPrincipal_support
  have h_pointwise_ineq : ∀ x : E,
      B.lam * ((η x)^2 * (∑ i : Fin d,
        Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2)) ≤
        (η x)^2 * shiftedPrincipal B u k h x := by
    intro x
    have hpw := principal_pointwise_bound (d := d) B u (η := η) k hh_support x
    have h_lhs_eq :
        B.lam * ((η x)^2 * (∑ i : Fin d,
          Sobolev.diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2)) =
          B.lam * (η x)^2 * (∑ i : Fin d,
          Sobolev.diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2) := by
      ring
    rw [h_lhs_eq]
    exact hpw
  have h_lhs_factor :
      B.lam * ∫ x, (η x)^2 *
          (∑ i : Fin d, Sobolev.diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2)
        ∂(volume : Measure E) =
      ∫ x, B.lam * ((η x)^2 *
          (∑ i : Fin d, Sobolev.diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2))
        ∂(volume : Measure E) := by
    rw [integral_const_mul]
  rw [h_lhs_factor]
  have h_LHS_int_mul :
      Integrable (fun x : E => B.lam * ((η x)^2 *
          (∑ i : Fin d, Sobolev.diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2)))
        volume := h_LHS_int.const_mul B.lam
  have h_int_le :
      ∫ x, B.lam * ((η x)^2 *
          (∑ i : Fin d, Sobolev.diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2))
        ∂(volume : Measure E) ≤
      ∫ x, (η x)^2 * shiftedPrincipal B u k h x ∂(volume : Measure E) :=
    integral_mono h_LHS_int_mul h_shiftedPrincipal_int h_pointwise_ineq
  refine h_int_le.trans ?_
  have h_pointwise_eq : ∀ x : E,
      (η x)^2 * shiftedPrincipal B u k h x =
        ∑ i : Fin d, ∑ j : Fin d,
          Sobolev.translate k h
              (fun y : E => B.a y i j) x * (η x)^2 *
            Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
            Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x := by
    intro x
    unfold shiftedPrincipal
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  have h_eq_fun :
      (fun x : E => (η x)^2 * shiftedPrincipal B u k h x) =
        (fun x : E => ∑ i : Fin d, ∑ j : Fin d,
          Sobolev.translate k h
              (fun y : E => B.a y i j) x * (η x)^2 *
            Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
            Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x) := by
    funext x
    exact h_pointwise_eq x
  rw [h_eq_fun]
  have h_inner_int : ∀ i : Fin d,
      Integrable (fun x : E => ∑ j : Fin d,
        Sobolev.translate k h
            (fun y : E => B.a y i j) x * (η x)^2 *
          Sobolev.diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
          Sobolev.diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)
      volume :=
    fun i => integrable_finsetSum _ (fun j _ => hT1_int i j)
  rw [show (fun x : E => ∑ i : Fin d, ∑ j : Fin d,
          Sobolev.translate k h
              (fun y : E => B.a y i j) x * (η x)^2 *
            Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
            Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x) =
      (fun x : E => ∑ i : Fin d, (fun y : E => ∑ j : Fin d,
          Sobolev.translate k h
              (fun z : E => B.a z i j) y * (η y)^2 *
            Sobolev.diffQuot k h
              (fun z : E => (fderiv ℝ u z) (EuclideanSpace.single i 1)) y *
            Sobolev.diffQuot k h
              (fun z : E => (fderiv ℝ u z) (EuclideanSpace.single j 1)) y) x)
      from rfl]
  rw [integral_finsetSum _ (fun i _ => h_inner_int i)]
  refine le_of_eq ?_
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [show (fun y : E => ∑ j : Fin d,
          Sobolev.translate k h
              (fun z : E => B.a z i j) y * (η y)^2 *
            Sobolev.diffQuot k h
              (fun z : E => (fderiv ℝ u z) (EuclideanSpace.single i 1)) y *
            Sobolev.diffQuot k h
              (fun z : E => (fderiv ℝ u z) (EuclideanSpace.single j 1)) y) =
      (fun y : E => ∑ j : Fin d, (fun z : E =>
          Sobolev.translate k h
              (fun w : E => B.a w i j) z * (η z)^2 *
            Sobolev.diffQuot k h
              (fun w : E => (fderiv ℝ u w) (EuclideanSpace.single i 1)) z *
            Sobolev.diffQuot k h
              (fun w : E => (fderiv ℝ u w) (EuclideanSpace.single j 1)) z) y)
      from rfl]
  rw [integral_finsetSum _ (fun j _ => hT1_int i j)]

theorem nirenberg_master_inequality
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u f : E → ℝ}
    (h_weak : B.IsSmoothWeakSolution u f)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (k : Fin d) {h : ℝ} (hh : h ≠ 0)
    (hh_support : Metric.cthickening |h| (tsupport η) ⊆ Ω) :
    B.lam * ∫ x, (η x)^2 * (∑ i : Fin d,
        Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2)
      ∂(volume : Measure E) ≤
      |∑ i : Fin d, ∑ j : Fin d, ∫ x,
          2 * Sobolev.translate k h
              (fun y : E => B.a y i j) x * (η x) *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
            Sobolev.diffQuot k h u x
          ∂(volume : Measure E)| +
      |∑ i : Fin d, ∑ j : Fin d, ∫ x,
          Sobolev.diffQuot k h
              (fun y : E => B.a y i j) x * (η x)^2 *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
            Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x
          ∂(volume : Measure E)| +
      |∑ i : Fin d, ∑ j : Fin d, ∫ x,
          2 * Sobolev.diffQuot k h
              (fun y : E => B.a y i j) x * (η x) *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
            Sobolev.diffQuot k h u x
          ∂(volume : Measure E)| +
      |∫ x in Ω, f x * nirenbergTestFunction k h η u x| +
      |∫ x in Ω, B.c x * u x * nirenbergTestFunction k h η u x| := by
  classical
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := h_weak.1
  have h_sub :=
    nirenberg_substitution_identity (d := d) B h_weak hη hη_support k hh hh_support
  set S : ℝ := ∑ i : Fin d, ∑ j : Fin d, ∫ x,
      Sobolev.diffQuot k h
          (fun y : E => B.a y i j *
            ((fderiv ℝ u y) (EuclideanSpace.single i 1))) x *
        ((fderiv ℝ
            (fun y : E => η y ^ 2 *
              Sobolev.diffQuot k h u y) x)
          (EuclideanSpace.single j 1))
      ∂(volume : Measure E) with hS_def
  set Q : ℝ := ∫ x in Ω, B.c x * u x * nirenbergTestFunction k h η u x
    with hQ_def
  set R : ℝ := ∫ x in Ω, f x * nirenbergTestFunction k h η u x
    with hR_def
  have h_sub_S : -S + Q = R := h_sub
  set P : ℝ := ∑ i : Fin d, ∑ j : Fin d, ∫ x,
      Sobolev.translate k h
          (fun y : E => B.a y i j) x * (η x)^2 *
        Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
        Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x
    ∂(volume : Measure E) with hP_def
  set C1 : ℝ := ∑ i : Fin d, ∑ j : Fin d, ∫ x,
      2 * Sobolev.translate k h
          (fun y : E => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
        Sobolev.diffQuot k h u x
    ∂(volume : Measure E) with hC1_def
  set C2 : ℝ := ∑ i : Fin d, ∑ j : Fin d, ∫ x,
      Sobolev.diffQuot k h
          (fun y : E => B.a y i j) x * (η x)^2 *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x
    ∂(volume : Measure E) with hC2_def
  set C3 : ℝ := ∑ i : Fin d, ∑ j : Fin d, ∫ x,
      2 * Sobolev.diffQuot k h
          (fun y : E => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        Sobolev.diffQuot k h u x
    ∂(volume : Measure E) with hC3_def
  have h_decomp : S = P + C1 + C2 + C3 :=
    nirenberg_principal_decomposition (d := d) B hu hη hη_support k hh
  set L : ℝ := B.lam * ∫ x, (η x)^2 * (∑ i : Fin d,
      Sobolev.diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2)
    ∂(volume : Measure E) with hL_def
  have h_coerc : L ≤ P :=
    principal_term_ge_lambda_norm_sq (d := d) B hu hη hη_support k hh_support
  have h_S_eq : S = Q - R := by
    have := h_sub_S
    linarith
  have h_P_eq : P = S - C1 - C2 - C3 := by
    have := h_decomp
    linarith
  have h_chain : L ≤ -C1 - C2 - C3 - R + Q := by
    have hP : P = -C1 - C2 - C3 - R + Q := by
      rw [h_P_eq, h_S_eq]; ring
    rw [hP] at h_coerc
    exact h_coerc
  have h_abs : -C1 - C2 - C3 - R + Q ≤
      |C1| + |C2| + |C3| + |R| + |Q| := by
    have h1 : -C1 ≤ |C1| := by
      have h := neg_abs_le C1
      linarith [abs_nonneg C1]
    have h2 : -C2 ≤ |C2| := by
      have h := neg_abs_le C2
      linarith [abs_nonneg C2]
    have h3 : -C3 ≤ |C3| := by
      have h := neg_abs_le C3
      linarith [abs_nonneg C3]
    have h4 : -R ≤ |R| := by
      have h := neg_abs_le R
      linarith [abs_nonneg R]
    have h5 : Q ≤ |Q| := le_abs_self Q
    linarith
  exact h_chain.trans h_abs

end Sobolev.NirenbergCoercivity
