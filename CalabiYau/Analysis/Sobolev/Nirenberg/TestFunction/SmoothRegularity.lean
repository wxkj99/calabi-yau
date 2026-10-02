-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Nirenberg/TestFunction/SmoothRegularity.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Nirenberg.TestFunction.Defs
public import CalabiYau.Analysis.Sobolev.Tools.DifferenceQuotient.SmoothRegularity

@[expose] public section

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open scoped ENNReal NNReal Convolution Pointwise BigOperators

namespace Sobolev.NirenbergTestFunction

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem contDiff_nirenbergTestFunction
    {η u : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (nirenbergTestFunction k h η u) := by
  unfold nirenbergTestFunction
  have hnh : (-h) ≠ 0 := neg_ne_zero.mpr hh
  have h_eta_sq : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => η y ^ 2) := hη.pow 2
  have h_diffQuot_u :
      ContDiff ℝ (⊤ : ℕ∞)
        (Sobolev.diffQuot k h u) :=
    contDiff_diffQuot_of_contDiff (d := d) hu k hh
  have h_prod :
      ContDiff ℝ (⊤ : ℕ∞)
        (fun y : E => η y ^ 2 *
          Sobolev.diffQuot k h u y) :=
    h_eta_sq.mul h_diffQuot_u
  exact contDiff_diffQuot_of_contDiff (d := d) h_prod k hnh

theorem fderiv_eta_sq_times_diffQuot_apply
    {η u : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (k j : Fin d) {h : ℝ} (hh : h ≠ 0) (x : E) :
    (fderiv ℝ
        (fun y : E => η y ^ 2 *
          Sobolev.diffQuot k h u y) x)
      (EuclideanSpace.single j 1) =
      2 * η x * ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        Sobolev.diffQuot k h u x +
      η x ^ 2 *
        Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x := by
  have hη_diff : Differentiable ℝ η := hη.differentiable (by simp)
  have hη_sq_diff : Differentiable ℝ (fun y : E => η y ^ 2) :=
    (hη.pow 2).differentiable (by simp)
  have h_diffQuot_u_smooth :
      ContDiff ℝ (⊤ : ℕ∞)
        (Sobolev.diffQuot k h u) :=
    contDiff_diffQuot_of_contDiff (d := d) hu k hh
  have h_diffQuot_u_diff :
      Differentiable ℝ
        (Sobolev.diffQuot k h u) :=
    h_diffQuot_u_smooth.differentiable (by simp)
  set ej : E := EuclideanSpace.single j 1 with hej
  have h_prod :
      fderiv ℝ
          (fun y : E => η y ^ 2 *
            Sobolev.diffQuot k h u y) x =
        η x ^ 2 •
          fderiv ℝ
            (Sobolev.diffQuot k h u) x +
          Sobolev.diffQuot k h u x •
            fderiv ℝ (fun y : E => η y ^ 2) x := by
    exact fderiv_fun_mul (hη_sq_diff x) (h_diffQuot_u_diff x)
  rw [h_prod]
  rw [add_apply,
      smul_apply,
      smul_apply]
  have hη_pow_fd :
      fderiv ℝ (fun y : E => η y ^ 2) x =
        ((2 : ℕ) • (η x) ^ ((2 : ℕ) - 1)) • fderiv ℝ η x :=
    fderiv_fun_pow 2 (hη_diff x)
  rw [hη_pow_fd]
  rw [smul_apply]
  have hpow1 : (η x) ^ ((2 : ℕ) - 1) = η x := by
    norm_num
  rw [hpow1]
  have h_fderiv_diffQuot :
      (fderiv ℝ
          (Sobolev.diffQuot k h u) x) ej =
        Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) ej) x :=
    fderiv_diffQuot_apply_eq_diffQuot_partial (d := d) hu k j hh x
  rw [h_fderiv_diffQuot]
  have h_two_smul : ((2 : ℕ) • η x) = 2 * η x := by
    rw [two_smul]
    ring
  rw [h_two_smul]
  change η x ^ 2 *
        Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) ej) x +
      Sobolev.diffQuot k h u x *
        (2 * η x * (fderiv ℝ η x) ej) =
      2 * η x * (fderiv ℝ η x) ej *
        Sobolev.diffQuot k h u x +
      η x ^ 2 *
        Sobolev.diffQuot k h
          (fun y : E => (fderiv ℝ u y) ej) x
  ring

theorem fderiv_nirenbergTestFunction_apply
    {η u : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (k j : Fin d) {h : ℝ} (hh : h ≠ 0) (x : E) :
    (fderiv ℝ (nirenbergTestFunction k h η u) x)
        (EuclideanSpace.single j 1) =
      Sobolev.diffQuot k (-h)
        (fun y : E =>
          2 * η y * ((fderiv ℝ η y) (EuclideanSpace.single j 1)) *
            Sobolev.diffQuot k h u y +
          η y ^ 2 *
            Sobolev.diffQuot k h
              (fun z : E =>
                (fderiv ℝ u z) (EuclideanSpace.single j 1)) y)
        x := by
  unfold nirenbergTestFunction
  have hnh : (-h) ≠ 0 := neg_ne_zero.mpr hh
  have hg_smooth :
      ContDiff ℝ (⊤ : ℕ∞)
        (fun y : E => η y ^ 2 *
          Sobolev.diffQuot k h u y) := by
    have h_eta_sq : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => η y ^ 2) := hη.pow 2
    have h_diffQuot_u :
        ContDiff ℝ (⊤ : ℕ∞)
          (Sobolev.diffQuot k h u) :=
      contDiff_diffQuot_of_contDiff (d := d) hu k hh
    exact h_eta_sq.mul h_diffQuot_u
  rw [fderiv_diffQuot_apply_eq_diffQuot_partial (d := d) hg_smooth k j hnh x]
  have h_pointwise :
      (fun y : E =>
          (fderiv ℝ
              (fun z : E => η z ^ 2 *
                Sobolev.diffQuot k h u z) y)
            (EuclideanSpace.single j 1)) =
        fun y : E =>
          2 * η y * ((fderiv ℝ η y) (EuclideanSpace.single j 1)) *
            Sobolev.diffQuot k h u y +
          η y ^ 2 *
            Sobolev.diffQuot k h
              (fun z : E =>
                (fderiv ℝ u z) (EuclideanSpace.single j 1)) y := by
    funext y
    exact fderiv_eta_sq_times_diffQuot_apply (d := d) hη hu k j hh y
  rw [h_pointwise]

end Sobolev.NirenbergTestFunction
