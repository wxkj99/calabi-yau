module

public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.SourceInterpolation.CutoffProfileBounds

/-!
# Scalar collection of the source constants

Source: Constantin, *Schauder Estimates*, equation (9), p. 7, and localization p. 8.
This result collects the source and commutator constants; the equation,
Hölder witnesses, and canonical cutoff majorants are established separately.
-/

@[expose] public section

open scoped NNReal ContDiff Topology

namespace CalabiYau.Schauder

/-- Fold the double sum and dominate its five nonnegative coefficients by one A.
The two coefficient-Hölder terms in the actual commutator constant are retained.
`hχ₂` and `hMχ₂` use different profile constants: H₂ and Cχ respectively. -/
theorem realBallCutoffSource_master_bound
    {n : ℕ} {α K M K₀ K₁ G V W q Kχv Kχ Kχ₂ Mχ Mχ₂ patch : ℝ≥0}
    (hq : 1 ≤ q)
    (hχv : Kχv ≤ realBallCutoffScalarProfileConst * q)
    (hχ : Kχ ≤ realBallCutoffLowerProfileConst * q ^ (3 : ℕ))
    (hMχ : Mχ ≤ realBallCutoffLowerProfileConst * q ^ (3 : ℕ))
    (hχ₂ : Kχ₂ ≤ realBallCutoffSecondHolderProfileConst * q ^ (3 : ℕ))
    (hMχ₂ : Mχ₂ ≤ realBallCutoffLowerProfileConst * q ^ (3 : ℕ))
    (hpatch : patch ≤ realBallCutoffPatchProfileConst α * q ^ (α : ℝ)) :
    M * ((K₁ * Kχv + K₁ +
      realBallSourceCommutatorHolderConst n K K₀ G V W Kχ Mχ Kχ₂ Mχ₂) +
      (K₁ + realBallSourcePairCount n * K * (2 * Mχ * G + Mχ₂ * K₀)) + K₀) * patch ≤
        realBallSourceMasterConst n α K M * q ^ (3 + (α : ℝ)) *
          (K₁ + K₀ + G + V + W) := by
  have hfold :
      realBallSourceCommutatorHolderConst n K K₀ G V W Kχ Mχ Kχ₂ Mχ₂ =
        realBallSourcePairCount n * K *
          (2 * Kχ * G + 2 * Mχ * G + 2 * Mχ * W +
            (Kχ₂ + Mχ₂) * K₀ + Mχ₂ * V) := by
    simp [realBallSourceCommutatorHolderConst, realBallSourcePairCount,
      Fintype.card_prod]
    ring_nf
  let S := realBallCutoffScalarProfileConst
  let C := realBallCutoffLowerProfileConst
  let H := realBallCutoffSecondHolderProfileConst
  let P := realBallCutoffPatchProfileConst α
  let N := realBallSourcePairCount n
  let q₃ := q ^ (3 : ℕ)
  let B := S + 3 + N * K * (H + 8 * C)
  have hq0 : q ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hq)
  have hq₃ge : 1 ≤ q₃ := one_le_pow₀ hq
  have hqleq₃ : q ≤ q₃ := by
    dsimp [q₃]
    calc
      q = q * 1 := by ring
      _ ≤ q * q ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hq) (by positivity)
      _ = q ^ (3 : ℕ) := by ring
  have hqpower : q ^ (3 + (α : ℝ)) = q₃ * q ^ (α : ℝ) := by
    dsimp [q₃]
    rw [NNReal.rpow_add hq0]
    rw [show (3 : ℝ) = (3 : ℕ) by norm_num, NNReal.rpow_natCast]
  have hK1 : Kχv + 2 ≤ B * q₃ := by
    have hbase : Kχv + 2 ≤ (S + 2) * q := by
      calc
        Kχv + 2 = 2 + Kχv := by ring
        _ ≤ 2 + S * q := add_le_add_right hχv 2
        _ = S * q + 2 := by ring
        _ ≤ S * q + 2 * q := add_le_add_right
          (calc 2 = 2 * 1 := by ring
                _ ≤ 2 * q := mul_le_mul_of_nonneg_left hq (by norm_num)) (S * q)
        _ = (S + 2) * q := by ring
    calc
      Kχv + 2 ≤ (S + 2) * q := hbase
      _ ≤ (S + 3) * q₃ := by
        calc
          (S + 2) * q ≤ (S + 2) * q₃ :=
            mul_le_mul_of_nonneg_left hqleq₃ (by positivity)
          _ ≤ (S + 3) * q₃ :=
            mul_le_mul_of_nonneg_right (by gcongr ; norm_num) (by positivity)
      _ ≤ B * q₃ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp [B, S, C, H, N]
        exact le_add_of_nonneg_right (by positivity)
  have hK0 : 1 + N * K * (Kχ₂ + 2 * Mχ₂) ≤ B * q₃ := by
    have hcut : Kχ₂ + 2 * Mχ₂ ≤ (H + 2 * C) * q₃ := by
      calc
        Kχ₂ + 2 * Mχ₂ ≤ H * q₃ + 2 * (C * q₃) :=
          add_le_add hχ₂ (mul_le_mul_of_nonneg_left hMχ₂ (by norm_num))
        _ = (H + 2 * C) * q₃ := by ring
    have hpair : N * K * (Kχ₂ + 2 * Mχ₂) ≤
        (N * K * (H + 2 * C)) * q₃ := by
      calc
        _ ≤ N * K * ((H + 2 * C) * q₃) :=
          mul_le_mul_of_nonneg_left hcut (by positivity)
        _ = (N * K * (H + 2 * C)) * q₃ := by ring
    calc
      1 + N * K * (Kχ₂ + 2 * Mχ₂) ≤
          (1 + N * K * (H + 2 * C)) * q₃ := by
        calc
          _ ≤ q₃ + (N * K * (H + 2 * C)) * q₃ :=
            add_le_add hq₃ge hpair
          _ = (1 + N * K * (H + 2 * C)) * q₃ := by ring
      _ ≤ B * q₃ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hn : (1 : ℝ≥0) ≤ 3 := by norm_num
        have hbase : H + 2 * C ≤ H + 8 * C := by
          calc
            H + 2 * C = 2 * C + H := by ring
            _ ≤ 8 * C + H := add_le_add_left
              (mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ≥0) ≤ 8)
                (by positivity)) H
            _ = H + 8 * C := by ring
        have hterm : N * K * (H + 2 * C) ≤ N * K * (H + 8 * C) :=
          mul_le_mul_of_nonneg_left hbase (by positivity)
        calc
          1 + N * K * (H + 2 * C) ≤ 3 + N * K * (H + 8 * C) :=
            add_le_add hn hterm
          _ ≤ S + 3 + N * K * (H + 8 * C) := by
            calc
              3 + N * K * (H + 8 * C) ≤
                  (3 + N * K * (H + 8 * C)) + S :=
                le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ S from by positivity)
              _ = S + 3 + N * K * (H + 8 * C) := by ring
  have hG : N * K * (2 * Kχ + 4 * Mχ) ≤ B * q₃ := by
    have hsix : 2 * Kχ + 4 * Mχ ≤ 6 * C * q₃ := by
      calc
        2 * Kχ + 4 * Mχ ≤ 2 * (C * q₃) + 4 * (C * q₃) :=
          add_le_add (mul_le_mul_of_nonneg_left hχ (by norm_num))
            (mul_le_mul_of_nonneg_left hMχ (by norm_num))
        _ = 6 * C * q₃ := by ring
    have h6 : 6 * C ≤ H + 8 * C := by
      calc
        6 * C ≤ 8 * C := by gcongr ; norm_num
        _ ≤ H + 8 * C := le_add_of_nonneg_left (by positivity)
    have hconst : N * K * (6 * C) ≤ B := by
      dsimp [B]
      calc
        N * K * (6 * C) ≤ N * K * (H + 8 * C) :=
          mul_le_mul_of_nonneg_left h6 (by positivity)
        _ ≤ S + 3 + N * K * (H + 8 * C) :=
          le_add_of_nonneg_left (by positivity)
    calc
      _ ≤ N * K * (6 * C * q₃) := mul_le_mul_of_nonneg_left hsix (by positivity)
      _ = (N * K * (6 * C)) * q₃ := by ring
      _ ≤ B * q₃ := mul_le_mul_of_nonneg_right hconst (by positivity)
  have hW : N * K * (2 * Mχ) ≤ B * q₃ := by
    have htwo : 2 * Mχ ≤ 2 * C * q₃ := by
      calc
        2 * Mχ ≤ 2 * (C * q₃) :=
          mul_le_mul_of_nonneg_left hMχ (by norm_num)
        _ = 2 * C * q₃ := by ring
    have h2 : 2 * C ≤ H + 8 * C := by
      calc
        2 * C ≤ 8 * C := by gcongr ; norm_num
        _ ≤ H + 8 * C := le_add_of_nonneg_left (by positivity)
    have hconst : N * K * (2 * C) ≤ B := by
      dsimp [B]
      calc
        N * K * (2 * C) ≤ N * K * (H + 8 * C) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
        _ ≤ S + 3 + N * K * (H + 8 * C) :=
          le_add_of_nonneg_left (by positivity)
    calc
      _ ≤ N * K * (2 * C * q₃) := mul_le_mul_of_nonneg_left htwo (by positivity)
      _ = (N * K * (2 * C)) * q₃ := by ring
      _ ≤ B * q₃ := mul_le_mul_of_nonneg_right hconst (by positivity)
  have hV : N * K * Mχ₂ ≤ B * q₃ := by
    have h1 : C ≤ H + 8 * C := by
      calc
        C ≤ 8 * C := by
          calc
            C = 1 * C := by ring
            _ ≤ 8 * C := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
        _ ≤ H + 8 * C := le_add_of_nonneg_left (by positivity)
    have hconst : N * K * C ≤ B := by
      dsimp [B]
      calc
        N * K * C ≤ N * K * (H + 8 * C) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ S + 3 + N * K * (H + 8 * C) :=
          le_add_of_nonneg_left (by positivity)
    calc
      _ ≤ N * K * (C * q₃) := mul_le_mul_of_nonneg_left hMχ₂ (by positivity)
      _ = (N * K * C) * q₃ := by ring
      _ ≤ B * q₃ := mul_le_mul_of_nonneg_right hconst (by positivity)
  have hpoly :
      (Kχv + 2) * K₁ + K₀ + N * K *
        (2 * Kχ * G + 4 * Mχ * G + 2 * Mχ * W +
          (Kχ₂ + 2 * Mχ₂) * K₀ + Mχ₂ * V) ≤
        B * q₃ * (K₁ + K₀ + G + V + W) := by
    calc
      _ = (Kχv + 2) * K₁ +
          (1 + N * K * (Kχ₂ + 2 * Mχ₂)) * K₀ +
          (N * K * (2 * Kχ + 4 * Mχ)) * G +
          (N * K * (2 * Mχ)) * W + (N * K * Mχ₂) * V := by ring
      _ ≤ (B * q₃) * K₁ + (B * q₃) * K₀ +
          (B * q₃) * G + (B * q₃) * W + (B * q₃) * V := by
        gcongr
      _ = B * q₃ * (K₁ + K₀ + G + V + W) := by ring
  rw [realBallSourceMasterConst]
  calc
    M * ((K₁ * Kχv + K₁ +
      realBallSourceCommutatorHolderConst n K K₀ G V W Kχ Mχ Kχ₂ Mχ₂) +
      (K₁ + realBallSourcePairCount n * K * (2 * Mχ * G + Mχ₂ * K₀)) + K₀) * patch =
      M * patch * ((Kχv + 2) * K₁ + K₀ + N * K *
        (2 * Kχ * G + 4 * Mχ * G + 2 * Mχ * W +
          (Kχ₂ + 2 * Mχ₂) * K₀ + Mχ₂ * V)) := by
        rw [hfold]
        dsimp [N]
        ring_nf
    _ ≤ M * patch * (B * q₃ * (K₁ + K₀ + G + V + W)) :=
      mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ ≤ M * (P * q ^ (α : ℝ)) *
          (B * q₃ * (K₁ + K₀ + G + V + W)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left hpatch (by positivity)
    _ = (M * P * B) * q ^ (3 + (α : ℝ)) *
          (K₁ + K₀ + G + V + W) := by
        calc
          _ = (M * P * B) * (q₃ * q ^ (α : ℝ)) *
                (K₁ + K₀ + G + V + W) := by ring
          _ = (M * P * B) * q ^ (3 + (α : ℝ)) *
                (K₁ + K₀ + G + V + W) := by rw [← hqpower]
    _ = realBallSourceMasterConst n α K M * q ^ (3 + (α : ℝ)) *
          (K₁ + K₀ + G + V + W) := by
        dsimp [realBallSourceMasterConst, B, P, S, C, H, N]

/-- Specialize the scalar master bound to the actual canonical cutoff constants.
This estimate applies the cutoff bounds, using each bound in the resulting inequality. -/
theorem realBallCutoffSource_canonical_master_bound
    {n : ℕ} {α K M K₀ K₁ G V W : ℝ≥0}
    (x : RealBallModel n) {δ : ℝ} (hδ : 0 < δ) :
    let hr : 0 ≤ δ / 2 := by positivity
    let hrR : δ / 2 < δ := by linarith
    let Kχv := ballCutoffHolderConst (δ / 2) δ
    let Kχ := ballCutoffFDerivHolderConst (δ / 2) δ
    let Kχ₂ := ballCutoffFDeriv2HolderConst x hr hrR
    let Mχ := ‖ballCutoffFDerivBoundedContinuousFunction x hr hrR‖₊
    let Mχ₂ := ‖ballCutoffFDeriv2BoundedContinuousFunction x hr hrR‖₊
    M * ((K₁ * Kχv + K₁ +
      realBallSourceCommutatorHolderConst n K K₀ G V W Kχ Mχ Kχ₂ Mχ₂) +
      (K₁ + realBallSourcePairCount n * K * (2 * Mχ * G + Mχ₂ * K₀)) + K₀) *
      realBallPatchFactor α δ ≤
        realBallSourceMasterConst n α K M * realBallSourceScale δ ^ (3 + (α : ℝ)) *
          (K₁ + K₀ + G + V + W) := by
  obtain ⟨hχv, hχ, hMχ, hχ₂, hMχ₂, hpatch⟩ := realBallCutoffProfile_bounds x α hδ
  have hq : 1 ≤ realBallSourceScale δ := by
    dsimp [realBallSourceScale]
    exact le_add_of_nonneg_right (by positivity)
  exact realBallCutoffSource_master_bound hq hχv hχ hMχ hχ₂ hMχ₂ hpatch

end CalabiYau.Schauder
