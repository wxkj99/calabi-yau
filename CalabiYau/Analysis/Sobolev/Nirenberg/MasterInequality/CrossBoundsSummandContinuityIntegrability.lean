-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Nirenberg/MasterInequality/CrossBoundsSummandContinuityIntegrability.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Nirenberg.MasterInequality.Coercivity

@[expose] public section

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open Sobolev
open Sobolev.NirenbergEuclidean
open Sobolev.NirenbergTestFunction
open Sobolev.NirenbergSubstitution
open Sobolev.NirenbergCoercivity
open scoped ENNReal NNReal Convolution Pointwise BigOperators InnerProductSpace

namespace Sobolev.NirenbergCrossBounds

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
lemma continuous_diffQuot_smooth
    {v : E → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) (k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    Continuous (diffQuot k h v) :=
  (contDiff_diffQuot_of_contDiff (d := d) hv k hh).continuous

omit [NeZero d] in
private lemma continuous_diffQuot_sq_smooth
    {v : E → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) (k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    Continuous (fun x : E => (diffQuot k h v x)^2) :=
  (continuous_diffQuot_smooth (d := d) hv k hh).pow 2

private lemma cross_1_summand_continuous
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (i j k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    Continuous (fun x : E =>
      2 * translate k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
        diffQuot k h u x) := by
  have h_a_cont : Continuous (fun x : E => B.a x i j) := B.continuous_a i j
  have h_translate_a : Continuous
      (translate k h (fun y => B.a y i j)) := by
    unfold translate
    exact h_a_cont.comp (continuous_id.add continuous_const)
  have h_diffQuot_partial_u : Continuous
      (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1))) := by
    have h_smooth : ContDiff ℝ (⊤ : ℕ∞)
        (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) := by
      have h_fderiv_smooth : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ u) :=
        hu.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
      have h_apply_smooth : ContDiff ℝ (⊤ : ℕ∞)
          (fun T : E →L[ℝ] ℝ => T (EuclideanSpace.single i 1)) :=
        (ContinuousLinearMap.apply ℝ ℝ
          (EuclideanSpace.single i (1 : ℝ))).contDiff
      exact h_apply_smooth.comp h_fderiv_smooth
    exact continuous_diffQuot_smooth (d := d) h_smooth k hh
  have h_diffQuot_u : Continuous (diffQuot k h u) :=
    continuous_diffQuot_smooth (d := d) hu k hh
  have hη_C1 : ContDiff ℝ 1 η := hη.of_le (by norm_cast)
  have h_partial_η : Continuous
      (fun x : E => (fderiv ℝ η x) (EuclideanSpace.single j 1)) :=
    ((hη_C1.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  refine (((((continuous_const.mul h_translate_a).mul hη.continuous).mul
    h_partial_η).mul h_diffQuot_partial_u).mul h_diffQuot_u)

private lemma cross_1_summand_compactSupport
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (u : E → ℝ)
    {η : E → ℝ} (hη_support : HasCompactSupport η)
    (i j k : Fin d) (h : ℝ) :
    HasCompactSupport (fun x : E =>
      2 * translate k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
        diffQuot k h u x) := by
  have h_step1 : HasCompactSupport (fun x : E =>
      2 * translate k h (fun y => B.a y i j) x * (η x)) :=
    hη_support.mul_left
  have h_step2 : HasCompactSupport (fun x : E =>
      2 * translate k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1))) := h_step1.mul_right
  have h_step3 : HasCompactSupport (fun x : E =>
      2 * translate k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x) :=
    h_step2.mul_right
  exact h_step3.mul_right

omit [NeZero d] in
private lemma continuous_diffQuot_partial_u
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (i k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    Continuous (Sobolev.diffQuot k h
      (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1))) := by
  have h_smooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) := by
    have h_fderiv_smooth : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ u) :=
      hu.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
    have h_apply_smooth : ContDiff ℝ (⊤ : ℕ∞)
        (fun T : E →L[ℝ] ℝ => T (EuclideanSpace.single i 1)) :=
      (ContinuousLinearMap.apply ℝ ℝ
        (EuclideanSpace.single i (1 : ℝ))).contDiff
    exact h_apply_smooth.comp h_fderiv_smooth
  exact continuous_diffQuot_smooth (d := d) h_smooth k hh

omit [NeZero d] in
lemma continuous_partial_u
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (i : Fin d) :
    Continuous (fun x : E => (fderiv ℝ u x) (EuclideanSpace.single i 1)) := by
  have hu_C1 : ContDiff ℝ 1 u := hu.of_le (by norm_cast)
  exact (hu_C1.continuous_fderiv (by norm_num)).clm_apply continuous_const

omit [NeZero d] in
lemma integrable_eta_sq_diffQuot_sum
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    Integrable (fun x : E => (η x)^2 *
        ∑ i : Fin d, (diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2)
      (volume : Measure E) := by
  have h_eta_sq_support : HasCompactSupport (fun y : E => η y ^ 2) := by
    have heq : (fun y : E => η y ^ 2) = (fun y : E => η y * η y) := by
      funext y; ring
    rw [heq]; exact hη_support.mul_right
  have h_diffQuot_partial_cont : ∀ i : Fin d,
      Continuous (Sobolev.diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1))) :=
    fun i => continuous_diffQuot_partial_u (d := d) hu i k hh
  have h_inner_cont : Continuous (fun x : E =>
      ∑ i : Fin d, (diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2) :=
    continuous_finsetSum _ (fun i _ => (h_diffQuot_partial_cont i).pow 2)
  have h_eta_sq_cont : Continuous (fun x : E => η x ^ 2) := hη.continuous.pow 2
  have h_prod_cont : Continuous (fun x : E => (η x)^2 *
        ∑ i : Fin d, (diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2) :=
    h_eta_sq_cont.mul h_inner_cont
  have h_prod_support : HasCompactSupport (fun x : E => (η x)^2 *
        ∑ i : Fin d, (diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2) :=
    h_eta_sq_support.mul_right
  exact h_prod_cont.integrable_of_hasCompactSupport h_prod_support

lemma integrable_cross_1_summand
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (i j k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    Integrable (fun x : E =>
      2 * translate k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
        diffQuot k h u x) volume := by
  have h_cont := cross_1_summand_continuous (d := d) B hu hη i j k hh
  have h_support := cross_1_summand_compactSupport (d := d) B u hη_support i j k h
  exact h_cont.integrable_of_hasCompactSupport h_support

omit [NeZero d] in
lemma integrable_eta_sq_diffQuot_partial_sq
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (i k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    Integrable (fun x : E => (η x)^2 *
      (diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2)
      (volume : Measure E) := by
  have h_eta_sq_support : HasCompactSupport (fun y : E => η y ^ 2) := by
    have heq : (fun y : E => η y ^ 2) = (fun y : E => η y * η y) := by
      funext y; ring
    rw [heq]; exact hη_support.mul_right
  have h_eta_sq_cont : Continuous (fun y : E => η y ^ 2) := hη.continuous.pow 2
  have h_diffQuot_cont :
      Continuous (Sobolev.diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1))) :=
    continuous_diffQuot_partial_u (d := d) hu i k hh
  have h_cont : Continuous (fun x : E => (η x)^2 *
      (diffQuot k h (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2) :=
    h_eta_sq_cont.mul (h_diffQuot_cont.pow 2)
  have h_support : HasCompactSupport (fun x : E => (η x)^2 *
      (diffQuot k h (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2) :=
    h_eta_sq_support.mul_right
  exact h_cont.integrable_of_hasCompactSupport h_support

omit [NeZero d] in
lemma integrable_const_eta_sq_diffQuot_partial_sq
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (i k : Fin d) {h : ℝ} (hh : h ≠ 0) (c : ℝ) :
    Integrable (fun x : E => c * (η x)^2 *
      (diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2)
      (volume : Measure E) := by
  have h_base := integrable_eta_sq_diffQuot_partial_sq (d := d) hu hη hη_support i k hh
  have h_eq : (fun x : E => c * (η x)^2 *
      (diffQuot k h (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2) =
      (fun x : E => c * ((η x)^2 *
        (diffQuot k h (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2)) := by
    funext x; ring
  rw [h_eq]
  exact h_base.const_mul c

omit [NeZero d] in
lemma integrable_const_indicator_diffQuot_sq
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη_support : HasCompactSupport η)
    (k : Fin d) {h : ℝ} (hh : h ≠ 0) (c : ℝ) :
    Integrable (fun x : E => c *
      (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
      (diffQuot k h u x)^2) (volume : Measure E) := by
  have h_diffQuot_u_cont : Continuous (Sobolev.diffQuot k h u) :=
    continuous_diffQuot_smooth (d := d) hu k hh
  have h_diffQuot_u_sq_cont : Continuous (fun x : E => (diffQuot k h u x)^2) :=
    h_diffQuot_u_cont.pow 2
  have h_tsupp_meas : MeasurableSet (tsupport η) :=
    isClosed_tsupport η |>.measurableSet
  have h_tsupp_compact : IsCompact (tsupport η) := hη_support
  have h_eq : (fun x : E => c *
      (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
      (diffQuot k h u x)^2) =
      (fun x : E => Set.indicator (tsupport η)
        (fun y : E => c * (diffQuot k h u y)^2) x) := by
    funext x
    by_cases hx : x ∈ tsupport η
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]; ring
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; ring
  rw [h_eq]
  have h_inner_cont : Continuous (fun y : E => c * (diffQuot k h u y)^2) :=
    continuous_const.mul h_diffQuot_u_sq_cont
  exact (ContinuousOn.integrableOn_compact h_tsupp_compact
    h_inner_cont.continuousOn).integrable_indicator
    h_tsupp_meas

private lemma cross_2_summand_continuous
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (i j k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    Continuous (fun x : E =>
      diffQuot k h (fun y => B.a y i j) x * (η x)^2 *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x) := by
  have h_dq_a : Continuous (Sobolev.diffQuot k h
      (fun y : E => B.a y i j)) :=
    continuous_diffQuot_smooth (d := d) (B.contDiff_a i j) k hh
  have h_eta_sq_cont : Continuous (fun x : E => (η x)^2) := hη.continuous.pow 2
  have h_partial_u : Continuous
      (fun x : E => (fderiv ℝ u x) (EuclideanSpace.single i 1)) :=
    continuous_partial_u (d := d) hu i
  have h_dq_partial_u : Continuous
      (Sobolev.diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1))) :=
    continuous_diffQuot_partial_u (d := d) hu j k hh
  exact (((h_dq_a.mul h_eta_sq_cont).mul h_partial_u).mul h_dq_partial_u)

private lemma cross_2_summand_compactSupport
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (u : E → ℝ) {η : E → ℝ} (hη_support : HasCompactSupport η)
    (i j k : Fin d) (h : ℝ) :
    HasCompactSupport (fun x : E =>
      diffQuot k h (fun y => B.a y i j) x * (η x)^2 *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x) := by
  have h_eta_sq_support : HasCompactSupport (fun y : E => η y ^ 2) := by
    have heq : (fun y : E => η y ^ 2) = (fun y : E => η y * η y) := by
      funext y; ring
    rw [heq]; exact hη_support.mul_right
  have h1 : HasCompactSupport (fun x : E =>
      diffQuot k h (fun y => B.a y i j) x * (η x)^2) :=
    h_eta_sq_support.mul_left
  have h2 : HasCompactSupport (fun x : E =>
      diffQuot k h (fun y => B.a y i j) x * (η x)^2 *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1))) :=
    h1.mul_right
  exact h2.mul_right

lemma integrable_cross_2_summand
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (i j k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    Integrable (fun x : E =>
      diffQuot k h (fun y => B.a y i j) x * (η x)^2 *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)
      volume :=
  (cross_2_summand_continuous (d := d) B hu hη i j k hh).integrable_of_hasCompactSupport
    (cross_2_summand_compactSupport (d := d) B u hη_support i j k h)

omit [NeZero d] in
lemma integrable_const_eta_sq_indicator_partial_sq
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (i : Fin d) (c : ℝ) :
    Integrable (fun x : E => c * (η x)^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2)
      (volume : Measure E) := by
  have h_partial_cont : Continuous
      (fun x : E => (fderiv ℝ u x) (EuclideanSpace.single i 1)) :=
    continuous_partial_u (d := d) hu i
  have h_eta_sq_cont : Continuous (fun x : E => (η x)^2) := hη.continuous.pow 2
  have h_eta_sq_support : HasCompactSupport (fun y : E => η y ^ 2) := by
    have heq : (fun y : E => η y ^ 2) = (fun y : E => η y * η y) := by
      funext y; ring
    rw [heq]; exact hη_support.mul_right
  have h_eq : (fun x : E => c * (η x)^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) =
      (fun x : E => c * (η x)^2 *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) := by
    funext x
    by_cases hx : x ∈ tsupport η
    · rw [Set.indicator_of_mem hx]; ring
    · rw [Set.indicator_of_notMem hx]
      have h_η_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [h_η_zero]; ring
  rw [h_eq]
  have h_cont : Continuous (fun x : E => c * (η x)^2 *
      ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) :=
    (continuous_const.mul h_eta_sq_cont).mul (h_partial_cont.pow 2)
  have h_step1 : HasCompactSupport (fun x : E => c * (η x)^2) :=
    h_eta_sq_support.mul_left
  have h_step2 : HasCompactSupport (fun x : E => c * (η x)^2 *
      ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) :=
    h_step1.mul_right
  exact h_cont.integrable_of_hasCompactSupport h_step2

private lemma cross_3_summand_continuous
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (i j k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    Continuous (fun x : E =>
      2 * diffQuot k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        diffQuot k h u x) := by
  have h_dq_a : Continuous (Sobolev.diffQuot k h
      (fun y : E => B.a y i j)) :=
    continuous_diffQuot_smooth (d := d) (B.contDiff_a i j) k hh
  have hη_C1 : ContDiff ℝ 1 η := hη.of_le (by norm_cast)
  have h_partial_η : Continuous
      (fun x : E => (fderiv ℝ η x) (EuclideanSpace.single j 1)) :=
    ((hη_C1.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  have h_partial_u : Continuous
      (fun x : E => (fderiv ℝ u x) (EuclideanSpace.single i 1)) :=
    continuous_partial_u (d := d) hu i
  have h_dq_u : Continuous (Sobolev.diffQuot k h u) :=
    continuous_diffQuot_smooth (d := d) hu k hh
  exact (((((continuous_const.mul h_dq_a).mul hη.continuous).mul h_partial_η).mul
    h_partial_u).mul h_dq_u)

private lemma cross_3_summand_compactSupport
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (u : E → ℝ) {η : E → ℝ} (hη_support : HasCompactSupport η)
    (i j k : Fin d) (h : ℝ) :
    HasCompactSupport (fun x : E =>
      2 * diffQuot k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        diffQuot k h u x) := by
  have h1 : HasCompactSupport (fun x : E =>
      2 * diffQuot k h (fun y => B.a y i j) x * (η x)) :=
    hη_support.mul_left
  have h2 : HasCompactSupport (fun x : E =>
      2 * diffQuot k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1))) :=
    h1.mul_right
  have h3 : HasCompactSupport (fun x : E =>
      2 * diffQuot k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1))) :=
    h2.mul_right
  exact h3.mul_right

lemma integrable_cross_3_summand
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (i j k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    Integrable (fun x : E =>
      2 * diffQuot k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        diffQuot k h u x) volume :=
  (cross_3_summand_continuous (d := d) B hu hη i j k hh).integrable_of_hasCompactSupport
    (cross_3_summand_compactSupport (d := d) B u hη_support i j k h)

omit [NeZero d] in
lemma nirenbergTestFunction_tsupport_subset_of_thickening
    {u : E → ℝ}
    {η : E → ℝ}
    {Ω' : Set E}
    {R₀ : ℝ}
    (hh_support_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (k : Fin d) {h : ℝ} (hh_le : |h| ≤ R₀) :
    tsupport (Sobolev.NirenbergTestFunction.nirenbergTestFunction
      k h η u) ⊆ Ω' :=
  (Sobolev.NirenbergTestFunction.tsupport_nirenbergTestFunction_subset
    (d := d) η u k h).trans (hh_support_in_Ω' hh_le)

omit [NeZero d] in
lemma continuous_v_test
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    Continuous (Sobolev.NirenbergTestFunction.nirenbergTestFunction
      k h η u) :=
  (Sobolev.NirenbergTestFunction.contDiff_nirenbergTestFunction
    hη hu k hh).continuous

omit [NeZero d] in
lemma hasCompactSupport_v_test
    {u : E → ℝ} {η : E → ℝ} (hη_support : HasCompactSupport η)
    (k : Fin d) (h : ℝ) :
    HasCompactSupport
      (Sobolev.NirenbergTestFunction.nirenbergTestFunction
      k h η u) :=
  hasCompactSupport_nirenbergTestFunction
    hη_support k h

end Sobolev.NirenbergCrossBounds
