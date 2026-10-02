module

public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.LocalApproximation.Basic

open Filter
open scoped NNReal Topology

@[expose] public section

namespace CalabiYau.Schauder

/-- Algebraic assembly of the value and slope bounds using the same vanishing M.
J is a fixed nonnegative constant, independent of the scale index. -/
theorem covarianceCommonModulusLeaf_commonModulus
    {J K α : ℝ} (hJ : 0 ≤ J) (hK : 0 ≤ K)
    (M r V D : ℕ → ℝ) (hM_nonneg : ∀ m, 0 ≤ M m)
    (hM_zero : Tendsto M atTop (𝓝 0))
    (hr : ∀ m, 0 < r m)
    (hValue : ∀ m, |V m| ≤ 2 * K * M m * (r m) ^ α)
    (hSlope : ∀ m, D m ≤ 4 * K * J * M m / (r m) ^ (1 - α)) :
    ∃ δ : ℕ → ℝ≥0, Tendsto δ atTop (𝓝 0) ∧
      (∀ m, (δ m : ℝ) = K * (2 + 4 * J) * M m) ∧
      (∀ m, |V m| ≤ (δ m : ℝ) * (r m) ^ α) ∧
      (∀ m, D m ≤ (δ m : ℝ) / (r m) ^ (1 - α)) := by
  let C : ℝ := K * (2 + 4 * J)
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hC_value : 2 * K ≤ C := by
    dsimp [C]
    nlinarith [mul_nonneg hK (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hJ)]
  have hC_slope : 4 * K * J ≤ C := by
    dsimp [C]
    nlinarith [mul_nonneg hK (by norm_num : (0 : ℝ) ≤ 2)]
  refine ⟨fun m => ⟨C * M m, mul_nonneg hC_nonneg (hM_nonneg m)⟩, ?_, ?_, ?_, ?_⟩
  · apply NNReal.tendsto_coe.1
    change Tendsto (fun m : ℕ => C * M m) atTop (𝓝 0)
    simpa [C] using (tendsto_const_nhds.mul hM_zero)
  · intro m
    change C * M m = K * (2 + 4 * J) * M m
    rfl
  · intro m
    calc
      |V m| ≤ 2 * K * M m * (r m) ^ α := hValue m
      _ ≤ (C * M m) * (r m) ^ α := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (le_of_lt (hr m)) α)
        exact mul_le_mul_of_nonneg_right hC_value (hM_nonneg m)
      _ = (⟨C * M m, mul_nonneg hC_nonneg (hM_nonneg m)⟩ : ℝ≥0) * (r m) ^ α := rfl
  · intro m
    calc
      D m ≤ 4 * K * J * M m / (r m) ^ (1 - α) := hSlope m
      _ ≤ (C * M m) / (r m) ^ (1 - α) := by
        apply div_le_div_of_nonneg_right _ (le_of_lt (Real.rpow_pos_of_pos (hr m) _))
        exact mul_le_mul_of_nonneg_right hC_slope (hM_nonneg m)
      _ = (⟨C * M m, mul_nonneg hC_nonneg (hM_nonneg m)⟩ : ℝ≥0) /
          (r m) ^ (1 - α) := rfl

/-- The explicit coefficient gives one modulus uniformly over any set of points,
including an empty set; no spatial sample or inhabitedness is required. -/
theorem covarianceCommonModulusLeaf_commonModulus_uniform
    {X : Type*} (s : Set X) {J K α : ℝ} (hJ : 0 ≤ J) (hK : 0 ≤ K)
    (M r : ℕ → ℝ) (V D : ℕ → X → ℝ)
    (hM_nonneg : ∀ m, 0 ≤ M m) (hM_zero : Tendsto M atTop (𝓝 0))
    (hr : ∀ m, 0 < r m)
    (hValue : ∀ m x, x ∈ s → |V m x| ≤ 2 * K * M m * (r m) ^ α)
    (hSlope : ∀ m x, x ∈ s → D m x ≤ 4 * K * J * M m / (r m) ^ (1 - α)) :
    ∃ δ : ℕ → ℝ≥0, Tendsto δ atTop (𝓝 0) ∧
      (∀ m, (δ m : ℝ) = K * (2 + 4 * J) * M m) ∧
      (∀ m x, x ∈ s → |V m x| ≤ (δ m : ℝ) * (r m) ^ α) ∧
      (∀ m x, x ∈ s → D m x ≤ (δ m : ℝ) / (r m) ^ (1 - α)) := by
  obtain ⟨δ, hδ, hformula, _, _⟩ :=
    covarianceCommonModulusLeaf_commonModulus (α := α) hJ hK M r (fun _ => 0) (fun _ => 0)
      hM_nonneg hM_zero hr
      (by
        intro m
        have hMm := hM_nonneg m
        have hrm := hr m
        simp only [abs_zero]
        positivity)
      (by
        intro m
        have hMm := hM_nonneg m
        have hrm := hr m
        positivity)
  have hCv : 2 * K ≤ K * (2 + 4 * J) := by
    nlinarith [mul_nonneg hK hJ]
  have hCs : 4 * K * J ≤ K * (2 + 4 * J) := by
    nlinarith
  refine ⟨δ, hδ, hformula, ?_, ?_⟩
  · intro m x hx
    rw [hformula m]
    exact (hValue m x hx).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCv (hM_nonneg m))
        (Real.rpow_nonneg (hr m).le α))
  · intro m x hx
    rw [hformula m]
    exact (hSlope m x hx).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCs (hM_nonneg m))
        (Real.rpow_pos_of_pos (hr m) _).le)

end CalabiYau.Schauder
