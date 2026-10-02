module

public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.SourceInterpolation.Basic

/-!
# Uniform data powers for the actual lower-jet budget

Source: Constantin, Schauder Estimates, localization/interpolation p. 8.
The exponent is fixed before theta, and the data coefficient before the radius.
-/

@[expose] public section

open scoped NNReal

namespace CalabiYau.Schauder

/-- Finite coefficient determined by the radius-independent choices. -/
noncomputable def realBallSourceBudgetDataConst (α A a b : ℝ≥0) : ℝ≥0 :=
  A * (2 + 2 / a + 4 / (a * b ^ (α : ℝ)) +
    2 * b ^ ((1 : ℝ≥0) - α : ℝ) / a + 2 / b ^ (α : ℝ))

noncomputable section

private theorem lower_jet_data_exponents
    (s k α β : ℝ) (hs : s = 3 + α) (hβ : β = 1 - α)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hk0 : 0 ≤ k)
    (hscale : s ≤ k * β) :
    s + k + 4 ≤ 2 * k + 8 ∧
    s + k + 4 + k * α ≤ 2 * k + 8 ∧
    s + k + 4 - k * β ≤ 2 * k + 8 ∧
    s + k * α ≤ 2 * k + 8 := by
  have hβle1 : β ≤ 1 := by rw [hβ]; linarith
  have hkb_le_k : k * β ≤ k * 1 := mul_le_mul_of_nonneg_left hβle1 hk0
  have hsk : s ≤ k := hscale.trans (by nlinarith)
  have hkα_le_k : k * α ≤ k * 1 := mul_le_mul_of_nonneg_left hα1 hk0
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

private theorem lower_jet_full_source_data_budget
    (q A a b K₀ K₁ : ℝ≥0) (s k α β : ℝ)
    (hq : 1 ≤ q) (ha : 0 < a) (hb : 0 < b)
    (hs : s = 3 + α) (hβ : β = 1 - α)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hk0 : 0 ≤ k)
    (hscale : s ≤ k * β) :
    A * q ^ s * K₁ + A * q ^ s * K₀ +
      A * (2 / a) * K₀ * q ^ (s + k + 4) +
      A * (4 / (a * b ^ α)) * K₀ * q ^ (s + k + 4 + k * α) +
      A * (2 * b ^ β / a) * K₀ * q ^ (s + k + 4 - k * β) +
      A * (2 / b ^ α) * K₀ * q ^ (s + k * α) ≤
    A * (2 + 2 / a + 4 / (a * b ^ α) + 2 * b ^ β / a + 2 / b ^ α) *
      q ^ (2 * k + 8) * (K₁ + K₀) := by
  obtain ⟨hGexp, hVexp, hW₁exp, hW₂exp⟩ :=
    lower_jet_data_exponents s k α β hs hβ hα0 hα1 hk0 hscale
  have hsP : s ≤ 2 * k + 8 := by nlinarith [hGexp, hk0]
  have hqP : 1 ≤ q ^ (2 * k + 8) := by
    have hpow := NNReal.rpow_le_rpow_of_exponent_le hq
      (by positivity : (0 : ℝ) ≤ 2 * k + 8)
    simpa using hpow
  have hqS : q ^ s ≤ q ^ (2 * k + 8) :=
    NNReal.rpow_le_rpow_of_exponent_le hq hsP
  have hraw : A * q ^ s * K₁ + A * q ^ s * K₀ ≤
      A * q ^ (2 * k + 8) * (K₁ + K₀) := by
    calc
      A * q ^ s * K₁ + A * q ^ s * K₀ ≤
          A * q ^ (2 * k + 8) * K₁ + A * q ^ (2 * k + 8) * K₀ := by
            apply add_le_add
            · calc
                A * q ^ s * K₁ = (A * K₁) * q ^ s := by ring
                _ ≤ (A * K₁) * q ^ (2 * k + 8) := mul_le_mul_of_nonneg_left hqS (by positivity)
                _ = A * q ^ (2 * k + 8) * K₁ := by ring
            · calc
                A * q ^ s * K₀ = (A * K₀) * q ^ s := by ring
                _ ≤ (A * K₀) * q ^ (2 * k + 8) := mul_le_mul_of_nonneg_left hqS (by positivity)
                _ = A * q ^ (2 * k + 8) * K₀ := by ring
      _ = A * q ^ (2 * k + 8) * (K₁ + K₀) := by ring
  have h₁ : A * (2 / a) * K₀ * q ^ (s + k + 4) ≤
      A * (2 / a) * K₀ * q ^ (2 * k + 8) :=
    mul_le_mul_of_nonneg_left (NNReal.rpow_le_rpow_of_exponent_le hq hGexp) (by positivity)
  have h₂ : A * (4 / (a * b ^ α)) * K₀ * q ^ (s + k + 4 + k * α) ≤
      A * (4 / (a * b ^ α)) * K₀ * q ^ (2 * k + 8) :=
    mul_le_mul_of_nonneg_left (NNReal.rpow_le_rpow_of_exponent_le hq hVexp) (by positivity)
  have h₃ : A * (2 * b ^ β / a) * K₀ * q ^ (s + k + 4 - k * β) ≤
      A * (2 * b ^ β / a) * K₀ * q ^ (2 * k + 8) :=
    mul_le_mul_of_nonneg_left (NNReal.rpow_le_rpow_of_exponent_le hq hW₁exp) (by positivity)
  have h₄ : A * (2 / b ^ α) * K₀ * q ^ (s + k * α) ≤
      A * (2 / b ^ α) * K₀ * q ^ (2 * k + 8) :=
    mul_le_mul_of_nonneg_left (NNReal.rpow_le_rpow_of_exponent_le hq hW₂exp) (by positivity)
  let D : ℝ≥0 := 2 / a + 4 / (a * b ^ α) + 2 * b ^ β / a + 2 / b ^ α
  have hfour :
      A * (2 / a) * K₀ * q ^ (s + k + 4) +
      A * (4 / (a * b ^ α)) * K₀ * q ^ (s + k + 4 + k * α) +
      A * (2 * b ^ β / a) * K₀ * q ^ (s + k + 4 - k * β) +
      A * (2 / b ^ α) * K₀ * q ^ (s + k * α) ≤
      A * D * q ^ (2 * k + 8) * K₀ := by
    calc
      _ ≤ A * (2 / a) * K₀ * q ^ (2 * k + 8) +
          A * (4 / (a * b ^ α)) * K₀ * q ^ (2 * k + 8) +
          A * (2 * b ^ β / a) * K₀ * q ^ (2 * k + 8) +
          A * (2 / b ^ α) * K₀ * q ^ (2 * k + 8) := by
            exact add_le_add (add_le_add (add_le_add h₁ h₂) h₃) h₄
      _ = A * D * q ^ (2 * k + 8) * K₀ := by dsimp [D]; ring
  have hK0 : A * D * q ^ (2 * k + 8) * K₀ ≤
      A * D * q ^ (2 * k + 8) * (K₁ + K₀) :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by positivity)
  calc
    _ = (A * q ^ s * K₁ + A * q ^ s * K₀) +
        (A * (2 / a) * K₀ * q ^ (s + k + 4) +
          A * (4 / (a * b ^ α)) * K₀ * q ^ (s + k + 4 + k * α) +
          A * (2 * b ^ β / a) * K₀ * q ^ (s + k + 4 - k * β) +
          A * (2 / b ^ α) * K₀ * q ^ (s + k * α)) := by ring
    _ ≤ A * q ^ (2 * k + 8) * (K₁ + K₀) +
        A * D * q ^ (2 * k + 8) * (K₁ + K₀) := add_le_add hraw (hfour.trans hK0)
    _ ≤ A * (2 + D) * q ^ (2 * k + 8) * (K₁ + K₀) := by
      calc
        _ = A * (1 + D) * q ^ (2 * k + 8) * (K₁ + K₀) := by ring
        _ ≤ A * (2 + D) * q ^ (2 * k + 8) * (K₁ + K₀) := by
          gcongr
          norm_num
    _ = _ := by dsimp [D]; ring

private theorem lower_jet_eps_scale_rpow_identities
    (q a b : ℝ≥0) (k α β : ℝ) :
    (a * q ^ (-(k + 4)))⁻¹ = a⁻¹ * q ^ (k + 4) ∧
    (b * q ^ (-k)) ^ α = b ^ α * (q ^ (k * α))⁻¹ ∧
    (b * q ^ (-k)) ^ β = b ^ β * (q ^ (k * β))⁻¹ := by
  constructor
  · rw [mul_inv, NNReal.rpow_neg, inv_inv]
  constructor
  · rw [NNReal.mul_rpow, ← NNReal.rpow_mul,
      show (-k) * α = -(k * α) by ring, NNReal.rpow_neg]
  · rw [NNReal.mul_rpow, ← NNReal.rpow_mul,
      show (-k) * β = -(k * β) by ring, NNReal.rpow_neg]

private theorem eps_postsubstitution_data_bridge
    (q a b K₀ : ℝ≥0) (s k α β : ℝ) (hq : 0 < q) :
    let eps₁ : ℝ≥0 := a * q ^ (-(k + 4))
    let eps₂ : ℝ≥0 := b * q ^ (-k)
    2 * K₀ / eps₁ * q ^ s = (2 / a) * K₀ * q ^ (s + k + 4) ∧
    4 * K₀ / (eps₁ * eps₂ ^ α) * q ^ s =
      (4 / (a * b ^ α)) * K₀ * q ^ (s + k + 4 + k * α) ∧
    2 * K₀ * eps₂ ^ β / eps₁ * q ^ s =
      (2 * b ^ β / a) * K₀ * q ^ (s + k + 4 - k * β) ∧
    2 * K₀ / eps₂ ^ α * q ^ s = (2 / b ^ α) * K₀ * q ^ (s + k * α) := by
  dsimp
  let eps₁ : ℝ≥0 := a * q ^ (-(k + 4))
  let eps₂ : ℝ≥0 := b * q ^ (-k)
  have hid := lower_jet_eps_scale_rpow_identities q a b k α β
  rcases hid with ⟨hi₁, hi₂, hi₃⟩
  have hqne : q ≠ 0 := ne_of_gt hq
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      2 * K₀ / (a * q ^ (-(k + 4))) * q ^ s =
          2 * K₀ * ((a * q ^ (-(k + 4)))⁻¹) * q ^ s := by ring
      _ = 2 * K₀ * (a⁻¹ * q ^ (k + 4)) * q ^ s := by rw [hi₁]
      _ = (2 / a) * K₀ * (q ^ (k + 4) * q ^ s) := by ring
      _ = (2 / a) * K₀ * q ^ (s + k + 4) := by
        rw [← NNReal.rpow_add hqne]
        congr 2; ring
  · calc
      4 * K₀ / ((a * q ^ (-(k + 4))) * (b * q ^ (-k)) ^ α) * q ^ s =
          4 * K₀ * ((a * q ^ (-(k + 4)))⁻¹) * ((b * q ^ (-k)) ^ α)⁻¹ * q ^ s := by ring
      _ = 4 * K₀ * (a⁻¹ * q ^ (k + 4)) *
          (b ^ α * (q ^ (k * α))⁻¹)⁻¹ * q ^ s := by rw [hi₁, hi₂]
      _ = (4 / (a * b ^ α)) * K₀ * (q ^ (k + 4) * q ^ (k * α) * q ^ s) := by
        rw [mul_inv, inv_inv]
        ring
      _ = (4 / (a * b ^ α)) * K₀ * q ^ (s + k + 4 + k * α) := by
        rw [← NNReal.rpow_add hqne, ← NNReal.rpow_add hqne]
        congr 2; ring
  · calc
      2 * K₀ * (b * q ^ (-k)) ^ β / (a * q ^ (-(k + 4))) * q ^ s =
          2 * K₀ * (b * q ^ (-k)) ^ β * (a * q ^ (-(k + 4)))⁻¹ * q ^ s := by ring
      _ = 2 * K₀ * (b ^ β * (q ^ (k * β))⁻¹) *
          (a⁻¹ * q ^ (k + 4)) * q ^ s := by rw [hi₃, hi₁]
      _ = (2 * b ^ β / a) * K₀ * (q ^ (k + 4) * (q ^ (k * β))⁻¹ * q ^ s) := by ring
      _ = (2 * b ^ β / a) * K₀ * (q ^ (k + 4) * q ^ (-(k * β)) * q ^ s) := by
        rw [← NNReal.rpow_neg]
      _ = (2 * b ^ β / a) * K₀ * q ^ (s + k + 4 - k * β) := by
        rw [← NNReal.rpow_add hqne, ← NNReal.rpow_add hqne]
        congr 2; ring
  · calc
      2 * K₀ / (b * q ^ (-k)) ^ α * q ^ s =
          2 * K₀ * ((b * q ^ (-k)) ^ α)⁻¹ * q ^ s := by ring
      _ = 2 * K₀ * (b ^ α * (q ^ (k * α))⁻¹)⁻¹ * q ^ s := by rw [hi₂]
      _ = (2 / b ^ α) * K₀ * (q ^ (k * α) * q ^ s) := by
        rw [mul_inv, inv_inv]
        ring
      _ = (2 / b ^ α) * K₀ * q ^ (s + k * α) := by
        rw [← NNReal.rpow_add hqne]
        congr 2; ring

private theorem source_GVW_combined_bound
    (q A C θ K₀ K₁ H eps₁ eps₂ : ℝ≥0) (s p α β : ℝ)
    (hdata :
      A * q ^ s * K₁ + A * q ^ s * K₀ +
        A * ((2 * K₀ / eps₁) * q ^ s) +
        A * ((4 * K₀ / (eps₁ * eps₂ ^ α)) * q ^ s) +
        A * ((2 * K₀ * eps₂ ^ β / eps₁) * q ^ s) +
        A * ((2 * K₀ / eps₂ ^ α) * q ^ s) ≤ C * q ^ p * (K₁ + K₀))
    (hgauge : A * q ^ s *
      (eps₁ * (1 + eps₂ ^ β) + eps₂ ^ β + 2 * eps₁ / eps₂ ^ α) ≤ θ) :
    let G : ℝ≥0 := 2 * K₀ / eps₁ + H * eps₁
    let V : ℝ≥0 := G * eps₂ ^ β + 2 * K₀ / eps₂ ^ α
    let W : ℝ≥0 := H * eps₂ ^ β + 2 * G / eps₂ ^ α
    A * q ^ s * (K₁ + K₀ + G + V + W) ≤ C * q ^ p * (K₁ + K₀) + θ * H := by
  dsimp
  let G : ℝ≥0 := 2 * K₀ / eps₁ + H * eps₁
  let V : ℝ≥0 := G * eps₂ ^ β + 2 * K₀ / eps₂ ^ α
  let W : ℝ≥0 := H * eps₂ ^ β + 2 * G / eps₂ ^ α
  let GaugeCoeff : ℝ≥0 := eps₁ * (1 + eps₂ ^ β) + eps₂ ^ β + 2 * eps₁ / eps₂ ^ α
  have hGaugeH : A * q ^ s * H * GaugeCoeff ≤ θ * H := by
    calc
      A * q ^ s * H * GaugeCoeff = (A * q ^ s * GaugeCoeff) * H := by ring
      _ ≤ θ * H := mul_le_mul_of_nonneg_right hgauge (by positivity)
  have hdecomp :
      A * q ^ s * (K₁ + K₀ + G + V + W) =
        (A * q ^ s * K₁ + A * q ^ s * K₀ +
          A * ((2 * K₀ / eps₁) * q ^ s) +
          A * ((4 * K₀ / (eps₁ * eps₂ ^ α)) * q ^ s) +
          A * ((2 * K₀ * eps₂ ^ β / eps₁) * q ^ s) +
          A * ((2 * K₀ / eps₂ ^ α) * q ^ s)) + A * q ^ s * H * GaugeCoeff := by
    dsimp [G, V, W, GaugeCoeff]
    ring
  calc
    _ = _ := hdecomp
    _ ≤ C * q ^ p * (K₁ + K₀) + θ * H := add_le_add hdata hGaugeH

private theorem port_actual_data
    {α A a b θ q : ℝ≥0} (hα : α < 1) (k : ℕ)
    (hk : 3 + (α : ℝ) ≤ (k : ℝ) * (1 - (α : ℝ)))
    (hq : 1 ≤ q) (ha : 0 < a) (hb : 0 < b)
    (hgauge :
      let eps₁ : ℝ≥0 := a * q ^ (-((k : ℝ) + 4))
      let eps₂ : ℝ≥0 := b * q ^ (-(k : ℝ))
      A * q ^ (3 + (α : ℝ)) *
        (eps₁ * (1 + eps₂ ^ ((1 : ℝ≥0) - α : ℝ)) +
          eps₂ ^ ((1 : ℝ≥0) - α : ℝ) + 2 * eps₁ / eps₂ ^ (α : ℝ)) ≤ θ) :
    let eps₁ : ℝ≥0 := a * q ^ (-((k : ℝ) + 4))
    let eps₂ : ℝ≥0 := b * q ^ (-(k : ℝ))
    ∀ K₀ K₁ H : ℝ≥0,
      let G := CalabiYau.Schauder.realBallLowerGradientBound K₀ H eps₁
      let V := CalabiYau.Schauder.realBallLowerValueHolderBound α K₀ G eps₂
      let W := CalabiYau.Schauder.realBallLowerGradientHolderBound α H G eps₂
      A * q ^ (3 + (α : ℝ)) * (K₁ + K₀ + G + V + W) ≤
        CalabiYau.Schauder.realBallSourceBudgetDataConst α A a b * q ^ (2 * k + 8) * (K₁ + K₀) + θ * H := by
  dsimp
  let β : ℝ := 1 - (α : ℝ)
  let s : ℝ := 3 + (α : ℝ)
  let kR : ℝ := (k : ℝ)
  let eps₁ : ℝ≥0 := a * q ^ (-((k : ℝ) + 4))
  let eps₂ : ℝ≥0 := b * q ^ (-(k : ℝ))
  have hα0 : 0 ≤ (α : ℝ) := NNReal.coe_nonneg α
  have hα1 : (α : ℝ) ≤ 1 := hα.le
  have hk0 : 0 ≤ kR := by positivity
  have hscale : s ≤ kR * β := by
    dsimp [s, kR, β]
    exact hk
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hβcontract : ((1 : ℝ≥0) - α : ℝ) = β := by
    dsimp [β]
  have hβNNcast : ((1 - α : ℝ≥0) : ℝ) = β := by
    dsimp [β]
    rw [NNReal.coe_sub hα.le]
    norm_num
  have hPcast : ((2 * k + 8 : ℕ) : ℝ) = 2 * kR + 8 := by
    dsimp [kR]
    push_cast
    ring
  have hqP : q ^ (2 * kR + 8) = q ^ (2 * k + 8 : ℕ) := by
    rw [← hPcast]
    exact NNReal.rpow_natCast q (2 * k + 8)
  let C : ℝ≥0 := CalabiYau.Schauder.realBallSourceBudgetDataConst α A a b
  have hgauge' : A * q ^ s *
      (eps₁ * (1 + eps₂ ^ β) + eps₂ ^ β + 2 * eps₁ / eps₂ ^ (α : ℝ)) ≤ θ := by
    simpa [s, eps₁, eps₂, hβcontract] using hgauge
  intro K₀ K₁ H
  have hbridge := eps_postsubstitution_data_bridge q a b K₀ s kR (α : ℝ) β hqpos
  rcases hbridge with ⟨h₁, h₂, h₃, h₄⟩
  let G : ℝ≥0 := CalabiYau.Schauder.realBallLowerGradientBound K₀ H eps₁
  let V : ℝ≥0 := CalabiYau.Schauder.realBallLowerValueHolderBound α K₀ G eps₂
  let W : ℝ≥0 := CalabiYau.Schauder.realBallLowerGradientHolderBound α H G eps₂
  let C' : ℝ≥0 := A * (2 + 2 / a + 4 / (a * b ^ (α : ℝ)) +
    2 * b ^ β / a + 2 / b ^ (α : ℝ))
  have hdata :
      A * q ^ s * K₁ + A * q ^ s * K₀ +
        A * ((2 * K₀ / eps₁) * q ^ s) +
        A * ((4 * K₀ / (eps₁ * eps₂ ^ (α : ℝ))) * q ^ s) +
        A * ((2 * K₀ * eps₂ ^ β / eps₁) * q ^ s) +
        A * ((2 * K₀ / eps₂ ^ (α : ℝ)) * q ^ s) ≤
        C' * q ^ (2 * kR + 8) * (K₁ + K₀) := by
    have hDB' := lower_jet_full_source_data_budget q A a b K₀ K₁ s kR
      (α : ℝ) β hq ha hb (by rfl) (by dsimp [β]) hα0 hα1 hk0 hscale
    calc
      _ = A * q ^ s * K₁ + A * q ^ s * K₀ +
          A * ((2 / a) * K₀ * q ^ (s + kR + 4)) +
          A * ((4 / (a * b ^ (α : ℝ))) * K₀ * q ^ (s + kR + 4 + kR * (α : ℝ))) +
          A * ((2 * b ^ β / a) * K₀ * q ^ (s + kR + 4 - kR * β)) +
          A * ((2 / b ^ (α : ℝ)) * K₀ * q ^ (s + kR * (α : ℝ))) := by
            rw [h₁, h₂, h₃, h₄]
      _ ≤ C' * q ^ (2 * kR + 8) * (K₁ + K₀) := by
            simpa [C', CalabiYau.Schauder.realBallSourceBudgetDataConst, hβNNcast, mul_assoc] using hDB'
  have hcombined := source_GVW_combined_bound q A C' θ K₀ K₁ H eps₁ eps₂
    s (2 * kR + 8) (α : ℝ) β hdata hgauge'
  calc
    A * q ^ s * (K₁ + K₀ + G + V + W) ≤
        C' * q ^ (2 * kR + 8) * (K₁ + K₀) + θ * H := hcombined
    _ = CalabiYau.Schauder.realBallSourceBudgetDataConst α A a b * q ^ (2 * k + 8 : ℕ) * (K₁ + K₀) + θ * H := by
      rw [hqP]
      rfl

private theorem exact_budget_data_contract
    {α A a b θ q : ℝ≥0} (hα : α < 1) (k : ℕ)
    (hk : 3 + (α : ℝ) ≤ (k : ℝ) * (1 - (α : ℝ)))
    (hq : 1 ≤ q) (ha : 0 < a) (hb : 0 < b)
    (hgauge :
      let eps₁ := a * q ^ (-((k : ℝ) + 4))
      let eps₂ := b * q ^ (-(k : ℝ))
      A * q ^ (3 + (α : ℝ)) *
        (eps₁ * (1 + eps₂ ^ ((1 : ℝ≥0) - α : ℝ)) +
          eps₂ ^ ((1 : ℝ≥0) - α : ℝ) + 2 * eps₁ / eps₂ ^ (α : ℝ)) ≤ θ) :
    let eps₁ := a * q ^ (-((k : ℝ) + 4))
    let eps₂ := b * q ^ (-(k : ℝ))
    ∀ K₀ K₁ H : ℝ≥0,
      let G := CalabiYau.Schauder.realBallLowerGradientBound K₀ H eps₁
      let V := CalabiYau.Schauder.realBallLowerValueHolderBound α K₀ G eps₂
      let W := CalabiYau.Schauder.realBallLowerGradientHolderBound α H G eps₂
      A * q ^ (3 + (α : ℝ)) * (K₁ + K₀ + G + V + W) ≤
        CalabiYau.Schauder.realBallSourceBudgetDataConst α A a b *
          q ^ (2 * k + 8) * (K₁ + K₀) + θ * H := by
  exact port_actual_data hα k hk hq ha hb hgauge

end

/-- Data exponents fit 2k+8, while the supplied weighted gauge budget controls H. -/
theorem realBallSource_budget_data
    {α A a b θ q : ℝ≥0} (hα : α < 1) (k : ℕ)
    (hk : 3 + (α : ℝ) ≤ (k : ℝ) * (1 - (α : ℝ)))
    (hq : 1 ≤ q) (ha : 0 < a) (hb : 0 < b)
    (hgauge :
      let eps₁ := a * q ^ (-((k : ℝ) + 4))
      let eps₂ := b * q ^ (-(k : ℝ))
      A * q ^ (3 + (α : ℝ)) *
        (eps₁ * (1 + eps₂ ^ ((1 : ℝ≥0) - α : ℝ)) +
          eps₂ ^ ((1 : ℝ≥0) - α : ℝ) + 2 * eps₁ / eps₂ ^ (α : ℝ)) ≤ θ) :
    let eps₁ := a * q ^ (-((k : ℝ) + 4))
    let eps₂ := b * q ^ (-(k : ℝ))
    ∀ K₀ K₁ H : ℝ≥0,
      let G := realBallLowerGradientBound K₀ H eps₁
      let V := realBallLowerValueHolderBound α K₀ G eps₂
      let W := realBallLowerGradientHolderBound α H G eps₂
      A * q ^ (3 + (α : ℝ)) * (K₁ + K₀ + G + V + W) ≤
        realBallSourceBudgetDataConst α A a b * q ^ (2 * k + 8) * (K₁ + K₀) + θ * H := by
  exact exact_budget_data_contract hα k hk hq ha hb hgauge

end CalabiYau.Schauder
