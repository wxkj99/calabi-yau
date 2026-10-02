module

public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.ComplexSmoothBall.Basic
public import CalabiYau.Analysis.Elliptic.Schauder.VariableCoefficient.BallInterior

/-!
# Radius-gap reciprocal/power bounds and existing polynomial exponent/scale choosers.

Proof-preserving extraction from the committed SourceInterpolation module
073d0f59b03ec37cc921b9792875e063bec3fb01.
Source: Constantin, Schauder Estimates, equation (9), p. 7 and localization/
lower-jet interpolation, pp. 8–9. Only visibility and namespace are changed.
-/

@[expose] public section

open Set Matrix
open scoped NNReal ContDiff Topology

namespace CalabiYau.Schauder.SourceInterpolationProofs

theorem realBallSourceRadius_inv_bound
    {R d r t : ℝ} (hR : 0 < R) (hd : 0 < d) (hr : 0 ≤ r)
    (hrt : r < t) (htR : t ≤ R) :
    (min d ((t - r) / 4))⁻¹ ≤ (d⁻¹ * R + 4) * (t - r)⁻¹ := by
  have hgap : 0 < t - r := by linarith
  have hgapR : t - r ≤ R := by linarith
  by_cases hmin : d ≤ (t - r) / 4
  · rw [min_eq_left hmin]
    have hratio : 1 ≤ R / (t-r) := (le_div_iff₀ hgap).2 (by simpa using hgapR)
    have hmul : d⁻¹ ≤ d⁻¹ * (R / (t-r)) := by
      calc
        d⁻¹ = d⁻¹ * 1 := (mul_one _).symm
        _ ≤ d⁻¹ * (R / (t-r)) := mul_le_mul_of_nonneg_left hratio (inv_nonneg.mpr hd.le)
    calc
      d⁻¹ ≤ d⁻¹ * (R / (t-r)) := hmul
      _ = (d⁻¹ * R) * (t-r)⁻¹ := by rw [div_eq_mul_inv]; ring
      _ ≤ (d⁻¹ * R + 4) * (t-r)⁻¹ := by
        apply mul_le_mul_of_nonneg_right
        · exact le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 4)
        · exact inv_nonneg.mpr hgap.le
  · rw [min_eq_right (le_of_not_ge hmin)]
    have h4 : ((t-r)/4)⁻¹ = 4 * (t-r)⁻¹ := by
      field_simp [ne_of_gt hgap]
    rw [h4]
    calc
      4 * (t-r)⁻¹ ≤ (d⁻¹ * R + 4) * (t-r)⁻¹ := by
        apply mul_le_mul_of_nonneg_right
        · exact le_add_of_nonneg_left (by positivity : (0 : ℝ) ≤ d⁻¹ * R)
        · exact inv_nonneg.mpr hgap.le

theorem realBallExists_polynomial_small_theta_power
    {α : ℝ≥0} (hα : α < 1) :
    ∃ m : ℕ, 0 < m ∧ 3 + (α : ℝ) ≤ (m : ℝ) * (1 - (α : ℝ)) := by
  have hαR : (α : ℝ) < 1 := by exact_mod_cast hα
  have hgap : 0 < 1 - (α : ℝ) := by linarith
  obtain ⟨m, hm⟩ := exists_nat_gt ((3 + (α : ℝ)) / (1 - (α : ℝ)))
  have hmpos : 0 < m := by
    exact_mod_cast (lt_trans (by positivity : (0 : ℝ) < (3 + (α : ℝ)) / (1 - (α : ℝ))) hm)
  refine ⟨m, hmpos, ?_⟩
  exact ((div_lt_iff₀ hgap).mp hm).le

end CalabiYau.Schauder.SourceInterpolationProofs
