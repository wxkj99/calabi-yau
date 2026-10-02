-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Euclidean/Embedding/Morrey/SmoothInequality.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Euclidean.W1p.Witness
public import CalabiYau.Analysis.Sobolev.Euclidean.W1p.Approximation
public import CalabiYau.Analysis.Sobolev.Euclidean.Poincare.Ball
public import CalabiYau.Analysis.Sobolev.Euclidean.Poincare.SobolevPoincare
public import CalabiYau.Analysis.Sobolev.Euclidean.Ball.Approximation
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Integral.Average
public import CalabiYau.Analysis.Sobolev.Euclidean.Embedding.Morrey.SmoothHolderBound

@[expose] public section

-- Private declarations used in public declarations require the compatibility option below..

noncomputable section

open MeasureTheory Set Filter Topology Metric Function
open scoped ENNReal NNReal

namespace Sobolev
namespace EuclideanMorrey
variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem smooth_morrey_sup_bound_uniform
    {d : ℕ} [NeZero d] {p : ℝ} (hp : (d : ℝ) < p)
    {x₀ : EuclideanSpace ℝ (Fin d)} {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : EuclideanSpace ℝ (Fin d) → ℝ}, ContDiff ℝ (⊤ : ℕ∞) u →
        ∀ x ∈ Metric.ball x₀ (R / 2), ‖u x‖ ≤ C *
          ((eLpNorm u (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R))).toReal +
           (eLpNorm (fun z => ‖fderiv ℝ u z‖) (ENNReal.ofReal p)
             (volume.restrict (Metric.ball x₀ R))).toReal) := by
  classical
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hd_one_le : (1 : ℝ) ≤ d :=
    by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))
  have hp_pos : 0 < p := lt_trans hd_pos hp
  have hp_one : 1 < p := lt_of_le_of_lt hd_one_le hp
  have h_exp_pos : 0 < 1 - (d : ℝ) / p := by
    rw [sub_pos, div_lt_one hp_pos]; exact hp
  have hC₀_nn : 0 ≤ smoothHolderConst d p := smoothHolderConst_nonneg hp
  have hvol_pos : 0 < (volume (Metric.ball x₀ R)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume x₀ hR).ne' measure_ball_lt_top.ne
  set A : ℝ := smoothHolderConst d p * R ^ (1 - (d : ℝ) / p) with hA_def
  set Bcoeff : ℝ := ((volume (Metric.ball x₀ R)).toReal) ^ (-(1 / p)) with hBcoeff_def
  have hA_nn : 0 ≤ A := by
    rw [hA_def]
    exact mul_nonneg hC₀_nn (Real.rpow_nonneg hR.le _)
  have hBcoeff_nn : 0 ≤ Bcoeff := by
    rw [hBcoeff_def]
    exact Real.rpow_nonneg ENNReal.toReal_nonneg _
  set C : ℝ := A + Bcoeff with hC_def
  have hC_nn : 0 ≤ C := by rw [hC_def]; linarith
  refine ⟨C, hC_nn, ?_⟩
  intro u hu x hx
  set N_grad : ℝ := (eLpNorm (fun z => ‖fderiv ℝ u z‖) (ENNReal.ofReal p)
    (volume.restrict (Metric.ball x₀ R))).toReal with hN_grad_def
  set N_u : ℝ := (eLpNorm u (ENNReal.ofReal p)
    (volume.restrict (Metric.ball x₀ R))).toReal with hN_u_def
  have hN_grad_nn : 0 ≤ N_grad := ENNReal.toReal_nonneg
  have hN_u_nn : 0 ≤ N_u := ENNReal.toReal_nonneg
  have hx_R : x ∈ Metric.ball x₀ R := by
    rw [Metric.mem_ball] at hx ⊢; linarith
  set Mavg : ℝ := ⨍ z in Metric.ball x₀ R, u z ∂volume with hMavg_def
  have h_diff_bound := smooth_pointwise_holder_bound_explicit (d := d) hp hR hu hx_R
  have h_diff_bound' : ‖u x - Mavg‖ ≤ A * N_grad := by
    change ‖u x - ⨍ z in Metric.ball x₀ R, u z ∂volume‖ ≤
        smoothHolderConst d p * R ^ (1 - (d : ℝ) / p) * N_grad
    exact h_diff_bound
  have h_avg_bound := smooth_norm_average_le (x₀ := x₀) hp_one hR hu
  have h_avg_bound' : ‖Mavg‖ ≤ Bcoeff * N_u := by
    change ‖⨍ z in Metric.ball x₀ R, u z ∂volume‖ ≤ Bcoeff * N_u
    rw [show Bcoeff * N_u = N_u * Bcoeff from by ring]
    exact h_avg_bound
  have h_split : ‖u x‖ ≤ ‖u x - Mavg‖ + ‖Mavg‖ := by
    calc ‖u x‖ = ‖(u x - Mavg) + Mavg‖ := by ring_nf
      _ ≤ ‖u x - Mavg‖ + ‖Mavg‖ := norm_add_le _ _
  have h_combined : ‖u x‖ ≤ A * N_grad + Bcoeff * N_u := by linarith
  have h_factor :
      A * N_grad + Bcoeff * N_u ≤ C * (N_u + N_grad) := by
    rw [hC_def]
    have h_expand : (A + Bcoeff) * (N_u + N_grad) =
        A * N_u + A * N_grad + Bcoeff * N_u + Bcoeff * N_grad := by ring
    rw [h_expand]
    have h_ANu_nn : 0 ≤ A * N_u := mul_nonneg hA_nn hN_u_nn
    have h_BNgrad_nn : 0 ≤ Bcoeff * N_grad := mul_nonneg hBcoeff_nn hN_grad_nn
    linarith
  linarith

end EuclideanMorrey
end Sobolev
