module

public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.SourceInterpolation.Basic

/-!
# Radius-independent positive interpolation coefficients

Source: Constantin, Schauder Estimates, small-top-norm absorption p. 8.
The coefficients are selected before the radius and equation data.
-/

@[expose] public section

open scoped NNReal

namespace CalabiYau.Schauder

private theorem positive_coefficient_witness
    (A θ α β : ℝ≥0) (hθ : 0 < θ) (hβ : 0 < β) :
    let ζ : ℝ≥0 := min 1 ((θ / 2) / (A + 1))
    let b : ℝ≥0 := ζ ^ ((β : ℝ)⁻¹)
    let a : ℝ≥0 := min (1 / 2) ((θ / 2) * b ^ (α : ℝ) / (4 * (A + 1)))
    0 < b ∧ b ≤ 1 ∧ 0 < a ∧ a ≤ 1 / 2 ∧
      A * b ^ (β : ℝ) ≤ θ / 2 ∧ 4 * A * a / b ^ (α : ℝ) ≤ θ / 2 := by
  dsimp
  let ζ : ℝ≥0 := min 1 ((θ / 2) / (A + 1))
  let b : ℝ≥0 := ζ ^ ((β : ℝ)⁻¹)
  let a : ℝ≥0 := min (1 / 2) ((θ / 2) * b ^ (α : ℝ) / (4 * (A + 1)))
  have hA1 : 0 < A + 1 := by positivity
  have hθ2 : 0 < θ / 2 := by positivity
  have hζpos : 0 < ζ := by
    dsimp [ζ]
    exact lt_min zero_lt_one (div_pos hθ2 hA1)
  have hζle1 : ζ ≤ 1 := by
    dsimp [ζ]
    exact min_le_left _ _
  have hβR : 0 < (β : ℝ) := by exact_mod_cast hβ
  have hβRne : (β : ℝ) ≠ 0 := ne_of_gt hβR
  have hbpos : 0 < b := by
    dsimp [b]
    exact NNReal.rpow_pos hζpos
  have hbβ : b ^ (β : ℝ) = ζ := by
    dsimp [b]
    simpa [one_div] using NNReal.rpow_self_rpow_inv hβRne ζ
  have hbpow : 0 < b ^ (α : ℝ) := NNReal.rpow_pos hbpos
  have hb_le_one : b ≤ 1 := by
    dsimp [b]
    exact NNReal.rpow_le_one hζle1 (by positivity)
  have hζbound : ζ * (A + 1) ≤ θ / 2 := by
    have hquot : ζ ≤ (θ / 2) / (A + 1) := by
      dsimp [ζ]
      exact min_le_right _ _
    exact (le_div_iff₀ hA1).mp hquot
  have hAb : A * b ^ (β : ℝ) ≤ θ / 2 := by
    rw [hbβ]
    calc
      A * ζ ≤ (A + 1) * ζ :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by norm_num)) (by positivity)
      _ = ζ * (A + 1) := by ring
      _ ≤ θ / 2 := hζbound
  have hden : 0 < 4 * (A + 1) := by positivity
  have ha_second : a ≤ (θ / 2) * b ^ (α : ℝ) / (4 * (A + 1)) := by
    dsimp [a]
    exact min_le_right _ _
  have ha_bound : a * (4 * (A + 1)) ≤ (θ / 2) * b ^ (α : ℝ) :=
    (le_div_iff₀ hden).mp ha_second
  have hnum : 4 * A * a ≤ (θ / 2) * b ^ (α : ℝ) := by
    calc
      4 * A * a = (4 * A) * a := by ring
      _ ≤ (4 * (A + 1)) * a :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by norm_num)) (by norm_num))
          (by positivity)
      _ = a * (4 * (A + 1)) := by ring
      _ ≤ (θ / 2) * b ^ (α : ℝ) := ha_bound
  have hquot_bound : 4 * A * a / b ^ (α : ℝ) ≤ θ / 2 :=
    (div_le_iff₀ hbpow).2 hnum
  have ha_pos : 0 < a := by
    dsimp [a]
    apply lt_min
    · norm_num
    · exact div_pos (mul_pos hθ2 hbpow) hden
  have ha_le_half : a ≤ 1 / 2 := by
    dsimp [a]
    exact min_le_left _ _
  exact ⟨hbpos, hb_le_one, ha_pos, ha_le_half, hAb, hquot_bound⟩

/-- Choose two positive coefficients with a full finite gauge budget. -/
theorem realBallSource_budget_choice
    {α A : ℝ≥0} (hα : α < 1) (θ : ℝ≥0) (hθ : 0 < θ) :
    ∃ a b : ℝ≥0, 0 < a ∧ a ≤ 1 / 2 ∧ 0 < b ∧ b ≤ 1 ∧
      A * (b ^ ((1 : ℝ≥0) - α : ℝ) + 4 * a / b ^ (α : ℝ)) ≤ θ := by
  let β : ℝ≥0 := 1 - α
  let ζ : ℝ≥0 := min 1 ((θ / 2) / (A + 1))
  let b : ℝ≥0 := ζ ^ ((β : ℝ)⁻¹)
  let a : ℝ≥0 := min (1 / 2) ((θ / 2) * b ^ (α : ℝ) / (4 * (A + 1)))
  have hβ : 0 < β := by dsimp [β]; exact tsub_pos_of_lt hα
  have h := positive_coefficient_witness A θ α β hθ hβ
  have hβcast : ((β : ℝ)) = 1 - (α : ℝ) := by
    dsimp [β]
    rw [NNReal.coe_sub hα.le]
    norm_num
  dsimp [ζ, b, a] at h
  rcases h with ⟨hbpos, hble, hap, hale, hAb, hCa⟩
  have hCa' : A * (4 * a / b ^ (α : ℝ)) ≤ θ / 2 := by
    have heq : A * (4 * a / b ^ (α : ℝ)) = (4 * A * a) / b ^ (α : ℝ) := by
      field_simp [ne_of_gt (NNReal.rpow_pos hbpos)]
    rw [heq]
    exact hCa
  refine ⟨a, b, hap, hale, hbpos, hble, ?_⟩
  calc
    A * (b ^ ((1 : ℝ≥0) - α : ℝ) + 4 * a / b ^ (α : ℝ)) =
        A * b ^ (β : ℝ) + A * (4 * a / b ^ (α : ℝ)) := by
          rw [mul_add]
          congr 1
          congr 1
          rw [hβcast]
          norm_num
    _ ≤ θ / 2 + θ / 2 := add_le_add hAb hCa'
    _ = θ := by ring

end CalabiYau.Schauder
