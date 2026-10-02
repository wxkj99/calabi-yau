module

public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.SourceInterpolation.Basic

/-!
# Positive q-scaled interpolation radii and weighted gauge absorption

Source: Constantin, Schauder Estimates, interpolation and absorption p. 8.
The q^(3+alpha) cutoff loss is included before absorption.
-/

@[expose] public section

open scoped NNReal

namespace CalabiYau.Schauder

private theorem scale_positive_buffer
    (δ : ℝ) (hδ : 0 < δ) (k : ℕ) (a : ℝ≥0)
    (ha : 0 < a) (haHalf : a ≤ 1 / 2) :
    let q : ℝ≥0 := 1 + (Real.toNNReal δ)⁻¹
    let eps₁ : ℝ≥0 := a * q ^ (-((k : ℝ) + 4))
    0 < eps₁ ∧ eps₁ ≤ Real.toNNReal δ / 2 := by
  dsimp
  let q : ℝ≥0 := 1 + (Real.toNNReal δ)⁻¹
  let eps₁ : ℝ≥0 := a * q ^ (-((k : ℝ) + 4))
  have hδNN : 0 < Real.toNNReal δ := Real.toNNReal_pos.mpr hδ
  have hq : (1 : ℝ≥0) ≤ q := by
    dsimp [q]
    exact le_add_of_nonneg_right (by positivity)
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hqδ : q⁻¹ ≤ Real.toNNReal δ := by
    have hqdef : q = 1 + (Real.toNNReal δ)⁻¹ := rfl
    have hqinv : Real.toNNReal δ * (Real.toNNReal δ)⁻¹ = 1 :=
      mul_inv_cancel₀ (ne_of_gt hδNN)
    have hprod : 1 < Real.toNNReal δ * q := by
      rw [hqdef, mul_add, hqinv]
      simpa only [mul_one] using (lt_add_of_pos_left (1 : ℝ≥0) hδNN)
    rw [inv_eq_one_div]
    exact (div_le_iff₀ hqpos).2 (by simpa [div_eq_mul_inv] using hprod.le)
  have hpow : q ^ (-((k : ℝ) + 4)) ≤ q ^ (-1 : ℝ) := by
    apply NNReal.rpow_le_rpow_of_exponent_le hq
    have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hpowδ : q ^ (-1 : ℝ) ≤ Real.toNNReal δ := by
    rw [NNReal.rpow_neg_one]
    exact hqδ
  constructor
  · change 0 < a * q ^ (-((k : ℝ) + 4))
    exact mul_pos ha (NNReal.rpow_pos hqpos)
  · calc
      eps₁ ≤ (1 / 2 : ℝ≥0) * q ^ (-1 : ℝ) := by
        dsimp [eps₁]
        exact mul_le_mul (by exact haHalf) hpow (by positivity) (by norm_num)
      _ ≤ (1 / 2 : ℝ≥0) * Real.toNNReal δ := by gcongr
      _ = Real.toNNReal δ / 2 := by ring

private theorem scale_small_epsilon_bound
    (q b : ℝ≥0) (k : ℕ) (hq : 1 ≤ q) (hb : b ≤ 1) :
    let eps₂ : ℝ≥0 := b * q ^ (-(k : ℝ))
    eps₂ ≤ 1 := by
  dsimp
  calc
    b * q ^ (-(k : ℝ)) ≤ 1 * 1 :=
      mul_le_mul hb (by
        calc
          q ^ (-(k : ℝ)) ≤ q ^ (0 : ℝ) := by
            apply NNReal.rpow_le_rpow_of_exponent_le hq
            have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
            linarith
          _ = 1 := by simp) (by positivity) (by positivity)
    _ = 1 := by ring

/-- The fixed threshold gives positive scales, the radius buffer, and the full gauge bound. -/
theorem realBallSource_budget_scales
    {α A a b θ : ℝ≥0} (hα : α < 1) (k : ℕ)
    (hk : 3 + (α : ℝ) ≤ (k : ℝ) * (1 - (α : ℝ)))
    (ha : 0 < a) (haHalf : a ≤ 1 / 2) (hb : 0 < b) (hbOne : b ≤ 1)
    (hchoice : A * (b ^ ((1 : ℝ≥0) - α : ℝ) + 4 * a / b ^ (α : ℝ)) ≤ θ)
    {δ : ℝ} (hδ : 0 < δ) :
    let q := realBallSourceScale δ
    let eps₁ := a * q ^ (-((k : ℝ) + 4))
    let eps₂ := b * q ^ (-(k : ℝ))
    0 < eps₁ ∧ 0 < eps₂ ∧ eps₁ ≤ Real.toNNReal δ / 2 ∧ eps₂ ≤ 1 ∧
      A * q ^ (3 + (α : ℝ)) *
        (eps₁ * (1 + eps₂ ^ ((1 : ℝ≥0) - α : ℝ)) +
          eps₂ ^ ((1 : ℝ≥0) - α : ℝ) + 2 * eps₁ / eps₂ ^ (α : ℝ)) ≤ θ := by
  dsimp
  let β : ℝ := 1 - (α : ℝ)
  let q : ℝ≥0 := 1 + (Real.toNNReal δ)⁻¹
  let eps₁ : ℝ≥0 := a * q ^ (-((k : ℝ) + 4))
  let eps₂ : ℝ≥0 := b * q ^ (-(k : ℝ))
  have hαNN : α < 1 := hα
  have hβ : 0 < β := by dsimp [β]; linarith [show (α : ℝ) < 1 from hα]
  have hβNNcast : ((1 - α : ℝ≥0) : ℝ) = β := by
    dsimp [β]
    rw [NNReal.coe_sub hα.le]
    norm_num
  have hq : (1 : ℝ≥0) ≤ q := by
    dsimp [q]
    exact le_add_of_nonneg_right (by positivity)
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hδNN : 0 < Real.toNNReal δ := Real.toNNReal_pos.mpr hδ
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have heps₁pos : 0 < eps₁ := by
    dsimp [eps₁]
    exact mul_pos ha (NNReal.rpow_pos hqpos)
  have heps₂pos : 0 < eps₂ := by
    dsimp [eps₂]
    exact mul_pos hb (NNReal.rpow_pos hqpos)
  have heps₁le : eps₁ ≤ Real.toNNReal δ / 2 := by
    exact (scale_positive_buffer δ hδ k a ha haHalf).2
  have heps₂le : eps₂ ≤ 1 := by
    exact scale_small_epsilon_bound q b k hq hbOne
  have hαreal : 0 ≤ (α : ℝ) := NNReal.coe_nonneg α
  have hβcontract : ((1 : ℝ≥0) - α : ℝ) = β := by
    dsimp [β]
  have hpowβ : eps₂ ^ β = b ^ β * q ^ ((-(k : ℝ)) * β) := by
    dsimp [eps₂]
    rw [NNReal.mul_rpow, NNReal.rpow_mul]
  have hpowα : eps₂ ^ (α : ℝ) = b ^ (α : ℝ) * q ^ ((-(k : ℝ)) * (α : ℝ)) := by
    dsimp [eps₂]
    rw [NNReal.mul_rpow, NNReal.rpow_mul]
  have hratio : eps₁ / eps₂ ^ (α : ℝ) =
      (a / b ^ (α : ℝ)) *
        q ^ (-((k : ℝ) + 4) - (-(k : ℝ)) * (α : ℝ)) := by
    rw [hpowα]
    dsimp [eps₁]
    calc
      (a * q ^ (-((k : ℝ) + 4))) /
          (b ^ (α : ℝ) * q ^ ((-(k : ℝ)) * (α : ℝ))) =
          (a / b ^ (α : ℝ)) *
            (q ^ (-((k : ℝ) + 4)) / q ^ ((-(k : ℝ)) * (α : ℝ))) := by
              field_simp [ne_of_gt (NNReal.rpow_pos hb),
                ne_of_gt (NNReal.rpow_pos hqpos)]
      _ = (a / b ^ (α : ℝ)) *
          q ^ (-((k : ℝ) + 4) - (-(k : ℝ)) * (α : ℝ)) := by
            rw [← NNReal.rpow_sub hqne]
  have hterm₁ : A * q ^ (3 + (α : ℝ)) * eps₂ ^ β =
      A * b ^ β * q ^ (3 + (α : ℝ) - (k : ℝ) * β) := by
    rw [hpowβ]
    calc
      A * q ^ (3 + (α : ℝ)) * (b ^ β * q ^ ((-(k : ℝ)) * β)) =
          A * b ^ β * (q ^ (3 + (α : ℝ)) * q ^ ((-(k : ℝ)) * β)) := by ring
      _ = A * b ^ β * q ^ (3 + (α : ℝ) + (-(k : ℝ)) * β) := by
        rw [← NNReal.rpow_add hqne]
      _ = A * b ^ β * q ^ (3 + (α : ℝ) - (k : ℝ) * β) := by congr 2; ring
  have hterm₂ : A * q ^ (3 + (α : ℝ)) * (4 * eps₁ / eps₂ ^ (α : ℝ)) =
      (4 * A * a / b ^ (α : ℝ)) *
        q ^ (3 + (α : ℝ) - 4 - (k : ℝ) * β) := by
    calc
      A * q ^ (3 + (α : ℝ)) * (4 * eps₁ / eps₂ ^ (α : ℝ)) =
          A * q ^ (3 + (α : ℝ)) * (4 * (eps₁ / eps₂ ^ (α : ℝ))) := by ring
      _ = A * q ^ (3 + (α : ℝ)) *
          (4 * ((a / b ^ (α : ℝ)) *
            q ^ (-((k : ℝ) + 4) - (-(k : ℝ)) * (α : ℝ)))) := by rw [hratio]
      _ = (4 * A * a / b ^ (α : ℝ)) *
            (q ^ (3 + (α : ℝ)) *
              q ^ (-((k : ℝ) + 4) - (-(k : ℝ)) * (α : ℝ))) := by ring
      _ = (4 * A * a / b ^ (α : ℝ)) *
          q ^ (3 + (α : ℝ) + (-((k : ℝ) + 4) - (-(k : ℝ)) * (α : ℝ))) := by
            rw [← NNReal.rpow_add hqne]
      _ = (4 * A * a / b ^ (α : ℝ)) *
          q ^ (3 + (α : ℝ) - 4 - (k : ℝ) * β) := by congr 2; dsimp [β]; ring
  have hexp₁ : 3 + (α : ℝ) - (k : ℝ) * β ≤ 0 := by
    dsimp [β]
    linarith [hk]
  have hexp₂ : 3 + (α : ℝ) - 4 - (k : ℝ) * β ≤ 0 := by
    dsimp [β]
    linarith [hk]
  have hqpow₁ : q ^ (3 + (α : ℝ) - (k : ℝ) * β) ≤ 1 := by
    calc
      q ^ (3 + (α : ℝ) - (k : ℝ) * β) ≤ q ^ (0 : ℝ) :=
        NNReal.rpow_le_rpow_of_exponent_le hq hexp₁
      _ = 1 := by simp
  have hqpow₂ : q ^ (3 + (α : ℝ) - 4 - (k : ℝ) * β) ≤ 1 := by
    calc
      q ^ (3 + (α : ℝ) - 4 - (k : ℝ) * β) ≤ q ^ (0 : ℝ) :=
        NNReal.rpow_le_rpow_of_exponent_le hq hexp₂
      _ = 1 := by simp
  have hbpowpos : 0 < b ^ (α : ℝ) := NNReal.rpow_pos hb
  have hchoice' : A * b ^ β + 4 * A * a / b ^ (α : ℝ) ≤ θ := by
    have hchoiceBeta : A * (b ^ β + 4 * a / b ^ (α : ℝ)) ≤ θ := by
      simpa [hβcontract, mul_add, mul_comm, mul_left_comm, mul_assoc] using hchoice
    calc
      A * b ^ β + 4 * A * a / b ^ (α : ℝ) =
          A * (b ^ β + 4 * a / b ^ (α : ℝ)) := by
            field_simp [ne_of_gt hbpowpos]
      _ ≤ θ := hchoiceBeta
  have hbound₁ : A * b ^ β * q ^ (3 + (α : ℝ) - (k : ℝ) * β) ≤ A * b ^ β := by
    calc
      A * b ^ β * q ^ (3 + (α : ℝ) - (k : ℝ) * β) =
          (A * b ^ β) * q ^ (3 + (α : ℝ) - (k : ℝ) * β) := by ring
      _ ≤ (A * b ^ β) * 1 := mul_le_mul_of_nonneg_left hqpow₁ (by positivity)
      _ = A * b ^ β := by simp
  have hbound₂ : (4 * A * a / b ^ (α : ℝ)) *
      q ^ (3 + (α : ℝ) - 4 - (k : ℝ) * β) ≤ 4 * A * a / b ^ (α : ℝ) := by
    calc
      (4 * A * a / b ^ (α : ℝ)) *
          q ^ (3 + (α : ℝ) - 4 - (k : ℝ) * β) =
          (4 * A * a / b ^ (α : ℝ)) *
            q ^ (3 + (α : ℝ) - 4 - (k : ℝ) * β) := rfl
      _ ≤ (4 * A * a / b ^ (α : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left hqpow₂ (by positivity)
      _ = 4 * A * a / b ^ (α : ℝ) := by simp
  have hbudget :
      A * b ^ β * q ^ (3 + (α : ℝ) - (k : ℝ) * β) +
        (4 * A * a / b ^ (α : ℝ)) *
          q ^ (3 + (α : ℝ) - 4 - (k : ℝ) * β) ≤ θ := by
    calc
      _ ≤ A * b ^ β + 4 * A * a / b ^ (α : ℝ) := add_le_add hbound₁ hbound₂
      _ ≤ θ := hchoice'
  have hsmall : eps₁ * (1 + eps₂ ^ β) ≤ 2 * eps₁ := by
    calc
      eps₁ * (1 + eps₂ ^ β) ≤ eps₁ * 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc
          1 + eps₂ ^ β = eps₂ ^ β + 1 := by ring
          _ ≤ 1 + 1 := add_le_add_left
            (NNReal.rpow_le_one heps₂le (by positivity)) 1
          _ = 2 := by norm_num
      _ = 2 * eps₁ := by ring
  have hpowαle : eps₂ ^ (α : ℝ) ≤ 1 :=
    NNReal.rpow_le_one heps₂le (by positivity)
  have hpowαpos : 0 < eps₂ ^ (α : ℝ) := NNReal.rpow_pos heps₂pos
  have hratioSmall : 2 * eps₁ ≤ 2 * eps₁ / eps₂ ^ (α : ℝ) := by
    apply (le_div_iff₀ hpowαpos).2
    calc
      (2 * eps₁) * eps₂ ^ (α : ℝ) ≤ (2 * eps₁) * 1 :=
        mul_le_mul_of_nonneg_left hpowαle (by positivity)
      _ = 2 * eps₁ := by simp
  have hinside : eps₁ * (1 + eps₂ ^ β) + eps₂ ^ β +
      2 * eps₁ / eps₂ ^ (α : ℝ) ≤ eps₂ ^ β + 4 * eps₁ / eps₂ ^ (α : ℝ) := by
    calc
      _ ≤ 2 * eps₁ + eps₂ ^ β + 2 * eps₁ / eps₂ ^ (α : ℝ) := by
        exact add_le_add (add_le_add hsmall le_rfl) le_rfl
      _ = eps₂ ^ β + (2 * eps₁ + 2 * eps₁ / eps₂ ^ (α : ℝ)) := by ring
      _ ≤ eps₂ ^ β + (2 * eps₁ / eps₂ ^ (α : ℝ) + 2 * eps₁ / eps₂ ^ (α : ℝ)) := by
        gcongr
      _ = eps₂ ^ β + 4 * eps₁ / eps₂ ^ (α : ℝ) := by ring
  have hfinal : A * q ^ (3 + (α : ℝ)) *
      (eps₂ ^ β + 4 * eps₁ / eps₂ ^ (α : ℝ)) ≤ θ := by
    calc
      A * q ^ (3 + (α : ℝ)) *
          (eps₂ ^ β + 4 * eps₁ / eps₂ ^ (α : ℝ)) =
          A * b ^ β * q ^ (3 + (α : ℝ) - (k : ℝ) * β) +
            (4 * A * a / b ^ (α : ℝ)) *
              q ^ (3 + (α : ℝ) - 4 - (k : ℝ) * β) := by
                rw [mul_add, hterm₁, hterm₂]
      _ ≤ θ := hbudget
  refine ⟨heps₁pos, heps₂pos, heps₁le, heps₂le, ?_⟩
  calc
    A * q ^ (3 + (α : ℝ)) *
        (eps₁ * (1 + eps₂ ^ ((1 : ℝ≥0) - α : ℝ)) +
          eps₂ ^ ((1 : ℝ≥0) - α : ℝ) + 2 * eps₁ / eps₂ ^ (α : ℝ)) ≤
        A * q ^ (3 + (α : ℝ)) *
          (eps₂ ^ β + 4 * eps₁ / eps₂ ^ (α : ℝ)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            simpa [hβcontract] using hinside
    _ ≤ θ := hfinal

end CalabiYau.Schauder
