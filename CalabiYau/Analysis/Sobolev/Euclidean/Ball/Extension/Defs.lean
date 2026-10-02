-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/External/DeGiorgi/BallExtension/Core.lean
-- Locally modified.
-- Modified 2026-04-28: updated internal import paths for project namespace
module
public import CalabiYau.Analysis.Sobolev.Euclidean.W1p
public import CalabiYau.Analysis.Sobolev.Euclidean.Ball.Approximation

@[expose] public section

/-!
# Ball Extension Core

Definitions and basic algebra for the explicit unit-ball extension operator.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Sobolev.Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

section

variable [NeZero d]

/-- Retraction used for the explicit unit-ball extension operator. -/
def unitBallRetraction (x : E) : E :=
  if ‖x‖ ≤ 1 then
    x
  else if ‖x‖ < 2 then
    (‖x‖ ^ (2 : ℕ))⁻¹ • x
  else
    0

/-- Radial cutoff used for the explicit unit-ball extension operator. -/
def unitBallCutoff (x : E) : ℝ :=
  min 1 (max (2 - ‖x‖) 0)

/-- Explicit unit-ball extension operator. -/
def unitBallExtension (u : E → ℝ) (x : E) : ℝ :=
  unitBallCutoff x * u (unitBallRetraction x)

end

lemma unitBallExtension_zero :
    unitBallExtension (d := d) (fun _ : E => (0 : ℝ)) = fun _ : E => (0 : ℝ) := by
  funext x
  simp [unitBallExtension]

lemma unitBallExtension_sub (u v : E → ℝ) :
    unitBallExtension (d := d) (fun x => u x - v x) =
      fun x => unitBallExtension (d := d) u x - unitBallExtension (d := d) v x := by
  funext x
  simp [unitBallExtension, sub_eq_add_neg, mul_add]

lemma unitBallRetraction_eq_self_of_norm_le_one {x : E} (hx : ‖x‖ ≤ 1) :
    unitBallRetraction (d := d) x = x := by
  simp [unitBallRetraction, hx]

lemma unitBallRetraction_eq_self_of_mem_ball {x : E} (hx : x ∈ Metric.ball (0 : E) 1) :
    unitBallRetraction (d := d) x = x := by
  apply unitBallRetraction_eq_self_of_norm_le_one (d := d)
  rw [Metric.mem_ball, dist_zero_right] at hx
  exact le_of_lt hx

lemma unitBallExtension_eq_of_mem_ball {u : E → ℝ} {x : E}
    (hx : x ∈ Metric.ball (0 : E) 1) :
    unitBallExtension (d := d) u x = u x := by
  unfold unitBallExtension unitBallCutoff
  rw [unitBallRetraction_eq_self_of_mem_ball (d := d) hx]
  rw [Metric.mem_ball, dist_zero_right] at hx
  have hgt : 1 < 2 - ‖x‖ := by linarith
  rw [max_eq_left (by positivity), min_eq_left (le_of_lt hgt), one_mul]

lemma unitBallRetraction_eq_smul_of_annulus {x : E}
    (h1 : 1 < ‖x‖) (h2 : ‖x‖ < 2) :
    unitBallRetraction (d := d) x = (‖x‖ ^ (2 : ℕ))⁻¹ • x := by
  have hx1 : ¬ ‖x‖ ≤ 1 := by linarith
  simp [unitBallRetraction, hx1, h2]

end Sobolev.Euclidean
