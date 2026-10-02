-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Tools/DifferenceQuotient/Support.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Tools.DifferenceQuotient

@[expose] public section

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open scoped ENNReal NNReal Convolution Pointwise BigOperators

namespace Sobolev

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
theorem hasCompactSupport_translate_of_hasCompactSupport
    {v : E → ℝ} (hv : HasCompactSupport v) (k : Fin d) (h : ℝ) :
    HasCompactSupport
      (Sobolev.translate k h v) := by
  let φ : E ≃ₜ E := Homeomorph.addRight (h • EuclideanSpace.single k 1)
  have heq :
      Sobolev.translate k h v = v ∘ φ := by
    funext x
    rfl
  rw [heq]
  exact hv.comp_homeomorph φ

omit [NeZero d] in
theorem hasCompactSupport_diffQuot_of_hasCompactSupport
    {v : E → ℝ} (hv : HasCompactSupport v) (k : Fin d) (h : ℝ) :
    HasCompactSupport
      (Sobolev.diffQuot k h v) := by
  by_cases hh : h = 0
  · subst hh
    rw [Sobolev.diffQuot_zero_h]
    exact HasCompactSupport.zero
  · have heq :
        Sobolev.diffQuot k h v =
          (h⁻¹ : ℝ) •
            (Sobolev.translate k h v - v) := by
      funext x
      rw [Sobolev.diffQuot_apply_of_ne
        (d := d) k hh v x]
      change (v (x + h • EuclideanSpace.single k 1) - v x) / h =
        h⁻¹ • (v (x + h • EuclideanSpace.single k 1) - v x)
      rw [div_eq_inv_mul, smul_eq_mul]
    rw [heq]
    have h_translate :
        HasCompactSupport
          (Sobolev.translate k h v) :=
      hasCompactSupport_translate_of_hasCompactSupport (d := d) hv k h
    have h_diff :
        HasCompactSupport
          (Sobolev.translate k h v - v) :=
      h_translate.sub hv
    exact h_diff.smul_left

end Sobolev
