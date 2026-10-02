module

public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.SourceInterpolation.Basic

/-!
# Lower-order canonical cutoff majorants

Source: Constantin, *Schauder Estimates*, localization p. 8. The profile constants
and the far-pair factor are explicit repository refinements of that argument.
-/

@[expose] public section

open scoped NNReal ContDiff Topology

namespace CalabiYau.Schauder

/-- Numeric majorants for the exact lower-order cutoff constants and patch factor.
No upper bound for δ or α is hidden in this statement. The scalar cutoff constant
is different from the Hölder constant of its first derivative. -/
theorem realBallCutoffLowerOrder_bounds
    {n : ℕ} (x : RealBallModel n) (α : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    let hr : 0 ≤ δ / 2 := by positivity
    let hrR : δ / 2 < δ := by linarith
    let q := realBallSourceScale δ
    ballCutoffHolderConst (δ / 2) δ ≤ realBallCutoffScalarProfileConst * q ∧
    ballCutoffFDerivHolderConst (δ / 2) δ ≤
      realBallCutoffLowerProfileConst * q ^ (3 : ℕ) ∧
    ‖ballCutoffFDerivBoundedContinuousFunction x hr hrR‖₊ ≤
      realBallCutoffLowerProfileConst * q ^ (3 : ℕ) ∧
    ‖ballCutoffFDeriv2BoundedContinuousFunction x hr hrR‖₊ ≤
      realBallCutoffLowerProfileConst * q ^ (3 : ℕ) ∧
    Real.toNNReal (ballCutoffFDeriv2Bound (δ / 2) δ) ≤
      realBallCutoffSecondSupProfileConst * q ^ (3 : ℕ) ∧
    realBallPatchFactor α δ ≤ realBallCutoffPatchProfileConst α * q ^ (α : ℝ) := by
  dsimp only
  let hr : 0 ≤ δ / 2 := by positivity
  let hrR : δ / 2 < δ := by linarith
  let q : ℝ≥0 := realBallSourceScale δ
  have hq : 1 ≤ q := by
    dsimp [q, realBallSourceScale]
    exact le_add_of_nonneg_right (by positivity)
  have hδnn : (Real.toNNReal δ : ℝ≥0) > 0 := by positivity
  have hcoe : (Real.toNNReal δ : ℝ) = δ := Real.coe_toNNReal δ hδ.le
  have hF : ballCutoffFDerivBound (δ / 2) δ =
      CutoffProfile.derivBound * (8 / (3 * δ)) := by
    unfold ballCutoffFDerivBound
    have hd : δ ^ 2 - (δ / 2) ^ 2 = 3 * δ ^ 2 / 4 := by ring
    rw [hd]
    field_simp; ring
  have hF2 : ballCutoffFDeriv2Bound (δ / 2) δ =
      CutoffProfile.derivBound * (88 / (9 * δ ^ 2)) := by
    unfold ballCutoffFDeriv2Bound
    have hd : δ ^ 2 - (δ / 2) ^ 2 = 3 * δ ^ 2 / 4 := by ring
    rw [hd]
    field_simp; ring
  have hB : 0 ≤ CutoffProfile.derivBound := CutoffProfile.derivBound_nonneg
  have hFnonneg : 0 ≤ ballCutoffFDerivBound (δ / 2) δ := by rw [hF]; positivity
  have hF2nonneg : 0 ≤ ballCutoffFDeriv2Bound (δ / 2) δ := by rw [hF2]; positivity
  have hqreal : (q : ℝ) = 1 + δ⁻¹ := by
    dsimp [q, realBallSourceScale]
    rw [max_eq_left hδ.le]
  have hqinv : (δ⁻¹ : ℝ) ≤ (q : ℝ) := by rw [hqreal]; linarith
  have hq2 : (1 : ℝ≥0) ≤ q ^ (3 : ℕ) := by
    exact one_le_pow₀ hq
  have hqR1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqRinv : δ⁻¹ ≤ (q : ℝ) := by rw [hqreal]; linarith
  have hInvSq : δ⁻¹ ^ 2 ≤ (q : ℝ) ^ 3 := by
    by_cases hy : δ⁻¹ ≤ 1
    · calc
        δ⁻¹ ^ 2 ≤ 1 := by nlinarith [inv_nonneg.mpr hδ.le]
        _ ≤ (q : ℝ) ^ 3 := one_le_pow₀ hqR1
    · have hy1 : 1 < δ⁻¹ := lt_of_not_ge hy
      have hpow : δ⁻¹ ^ 2 ≤ δ⁻¹ ^ 3 := by
        have hsub : 0 ≤ δ⁻¹ - 1 := by linarith
        nlinarith [mul_nonneg (sq_nonneg (δ⁻¹)) hsub]
      exact hpow.trans (by gcongr)
  have hqleq3 : (q : ℝ) ≤ (q : ℝ) ^ 3 := by
    calc
      (q : ℝ) = (q : ℝ) * 1 := by ring
      _ ≤ (q : ℝ) * (q : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hqR1) (by positivity)
      _ = (q : ℝ) ^ 3 := by ring
  have hInv : δ⁻¹ ≤ (q : ℝ) ^ 3 := by
    by_cases hy : δ⁻¹ ≤ 1
    · exact le_trans hy (one_le_pow₀ hqR1)
    · exact le_trans hqRinv hqleq3
  have hFto : Real.toNNReal (ballCutoffFDerivBound (δ / 2) δ) ≤
      Real.toNNReal (CutoffProfile.derivBound * (8 / 3)) * q := by
    rw [hF]
    apply (Real.toNNReal_le_iff_le_coe).2
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity), hqreal]
    have hrecip : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
    have hpos : 0 < 3 * δ := by positivity
    field_simp
    nlinarith [hB]
  have hscalarCoeff : Real.toNNReal (CutoffProfile.derivBound * (8 / 3)) ≤
      realBallCutoffScalarProfileConst := by
    unfold realBallCutoffScalarProfileConst
    apply Real.toNNReal_mono
    calc
      CutoffProfile.derivBound * (8 / 3) = 8 / 3 * CutoffProfile.derivBound := by ring
      _ ≤ max 2 (8 / 3 * CutoffProfile.derivBound) := le_max_right _ _
  have hscalarTwo : (2 : ℝ≥0) ≤ realBallCutoffScalarProfileConst := by
    unfold realBallCutoffScalarProfileConst
    have h := Real.toNNReal_mono (le_max_left (2 : ℝ)
      (8 / 3 * CutoffProfile.derivBound))
    simp
  have hscalarF : Real.toNNReal (ballCutoffFDerivBound (δ / 2) δ) ≤
      realBallCutoffScalarProfileConst * q := by
    calc
      _ ≤ Real.toNNReal (CutoffProfile.derivBound * (8 / 3)) * q := hFto
      _ ≤ realBallCutoffScalarProfileConst * q :=
        mul_le_mul_of_nonneg_right hscalarCoeff (by positivity)
  have hscalar : ballCutoffHolderConst (δ / 2) δ ≤
      realBallCutoffScalarProfileConst * q := by
    rw [ballCutoffHolderConst]
    apply max_le
    · calc
        (2 : ℝ≥0) ≤ realBallCutoffScalarProfileConst := hscalarTwo
        _ = realBallCutoffScalarProfileConst * 1 := by simp
        _ ≤ realBallCutoffScalarProfileConst * q :=
          mul_le_mul_of_nonneg_left hq (by positivity)
    · exact hscalarF
  have hF2to : Real.toNNReal (ballCutoffFDeriv2Bound (δ / 2) δ) ≤
      Real.toNNReal (CutoffProfile.derivBound * (88 / 9)) * q ^ (3 : ℕ) := by
    rw [hF2]
    apply (Real.toNNReal_le_iff_le_coe).2
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity), NNReal.coe_pow, hqreal]
    have hcoeff : 0 ≤ CutoffProfile.derivBound * (88 / 9) := by positivity
    have hsq : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
    have hrecip : (1 / δ ^ 2 : ℝ) = δ⁻¹ ^ 2 := by
      rw [one_div, inv_pow]
    calc
      CutoffProfile.derivBound * (88 / (9 * δ ^ 2))
          = (CutoffProfile.derivBound * (88 / 9)) * δ⁻¹ ^ 2 := by
            field_simp [ne_of_gt hδ]
      _ ≤ (CutoffProfile.derivBound * (88 / 9)) * (q : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_left hInvSq hcoeff
      _ = (CutoffProfile.derivBound * (88 / 9)) * (1 + δ⁻¹) ^ 3 := by
        rw [← hqreal]
  have hsecondCoeff : Real.toNNReal (CutoffProfile.derivBound * (88 / 9)) ≤
      realBallCutoffSecondSupProfileConst := by
    unfold realBallCutoffSecondSupProfileConst
    apply Real.toNNReal_mono
    exact le_of_eq (by ring)
  have hsecond : Real.toNNReal (ballCutoffFDeriv2Bound (δ / 2) δ) ≤
      realBallCutoffSecondSupProfileConst * q ^ (3 : ℕ) := by
    calc
      _ ≤ Real.toNNReal (CutoffProfile.derivBound * (88 / 9)) * q ^ (3 : ℕ) := hF2to
      _ ≤ realBallCutoffSecondSupProfileConst * q ^ (3 : ℕ) :=
        mul_le_mul_of_nonneg_right hsecondCoeff (by positivity)
  have hlowerCoeff16 : Real.toNNReal (CutoffProfile.derivBound * (16 / 3)) ≤
      realBallCutoffLowerProfileConst := by
    unfold realBallCutoffLowerProfileConst
    apply Real.toNNReal_mono
    calc
      CutoffProfile.derivBound * (16 / 3) = 16 / 3 * CutoffProfile.derivBound := by ring
      _ ≤ max (16 / 3 * CutoffProfile.derivBound)
          (88 / 9 * CutoffProfile.derivBound) := le_max_left _ _
  have hlowerCoeff88 : Real.toNNReal (CutoffProfile.derivBound * (88 / 9)) ≤
      realBallCutoffLowerProfileConst := by
    unfold realBallCutoffLowerProfileConst
    apply Real.toNNReal_mono
    calc
      CutoffProfile.derivBound * (88 / 9) = 88 / 9 * CutoffProfile.derivBound := by ring
      _ ≤ max (16 / 3 * CutoffProfile.derivBound)
          (88 / 9 * CutoffProfile.derivBound) := le_max_right _ _
  have hcoeffScaled :
      2 * Real.toNNReal (CutoffProfile.derivBound * (8 / 3)) =
        Real.toNNReal (CutoffProfile.derivBound * (16 / 3)) := by
    apply NNReal.coe_inj.mp
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity),
      Real.coe_toNNReal _ (by positivity)]
    norm_num; ring_nf
  have hfirstHolder : 2 * Real.toNNReal (ballCutoffFDerivBound (δ / 2) δ) ≤
      realBallCutoffLowerProfileConst * q ^ (3 : ℕ) := by
    calc
      _ ≤ 2 * (Real.toNNReal (CutoffProfile.derivBound * (8 / 3)) * q) :=
        mul_le_mul_of_nonneg_left hFto (by positivity)
      _ = (2 * Real.toNNReal (CutoffProfile.derivBound * (8 / 3))) * q := by ring
      _ = Real.toNNReal (CutoffProfile.derivBound * (16 / 3)) * q := by rw [hcoeffScaled]
      _ ≤ Real.toNNReal (CutoffProfile.derivBound * (16 / 3)) * q ^ (3 : ℕ) :=
        mul_le_mul_of_nonneg_left hqleq3 (by positivity)
      _ ≤ realBallCutoffLowerProfileConst * q ^ (3 : ℕ) :=
        mul_le_mul_of_nonneg_right hlowerCoeff16 (by positivity)
  have hsecondHolder : Real.toNNReal (ballCutoffFDeriv2Bound (δ / 2) δ) ≤
      realBallCutoffLowerProfileConst * q ^ (3 : ℕ) := by
    calc
      _ ≤ Real.toNNReal (CutoffProfile.derivBound * (88 / 9)) * q ^ (3 : ℕ) := hF2to
      _ ≤ realBallCutoffLowerProfileConst * q ^ (3 : ℕ) :=
        mul_le_mul_of_nonneg_right hlowerCoeff88 (by positivity)
  have hholder : ballCutoffFDerivHolderConst (δ / 2) δ ≤
      realBallCutoffLowerProfileConst * q ^ (3 : ℕ) := by
    rw [ballCutoffFDerivHolderConst]
    exact max_le hfirstHolder hsecondHolder
  have hfirstNN : Real.toNNReal (ballCutoffFDerivBound (δ / 2) δ) ≤
      realBallCutoffLowerProfileConst * q ^ (3 : ℕ) := by
    calc
      _ = 1 * Real.toNNReal (ballCutoffFDerivBound (δ / 2) δ) := by simp
      _ ≤ 2 * Real.toNNReal (ballCutoffFDerivBound (δ / 2) δ) :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ ≤ realBallCutoffLowerProfileConst * q ^ (3 : ℕ) := hfirstHolder
  have hMchi :
      ‖ballCutoffFDerivBoundedContinuousFunction x hr hrR‖₊ ≤
        realBallCutoffLowerProfileConst * q ^ (3 : ℕ) := by
    apply NNReal.coe_le_coe.mp
    apply (BoundedContinuousFunction.norm_le (NNReal.coe_nonneg _)).2
    intro y
    rw [ballCutoffFDerivBoundedContinuousFunction_apply]
    calc
      ‖ballCutoffFDeriv x (δ / 2) δ y‖ ≤ ballCutoffFDerivBound (δ / 2) δ :=
        norm_ballCutoffFDeriv_le (by positivity) (by linarith) y
      _ = (Real.toNNReal (ballCutoffFDerivBound (δ / 2) δ) : ℝ) :=
        (Real.coe_toNNReal _ hFnonneg).symm
      _ ≤ (realBallCutoffLowerProfileConst * q ^ (3 : ℕ) : ℝ) := by
        exact_mod_cast hfirstNN
  have hMchi2 :
      ‖ballCutoffFDeriv2BoundedContinuousFunction x hr hrR‖₊ ≤
        realBallCutoffLowerProfileConst * q ^ (3 : ℕ) := by
    apply NNReal.coe_le_coe.mp
    apply (BoundedContinuousFunction.norm_le (NNReal.coe_nonneg _)).2
    intro y
    rw [ballCutoffFDeriv2BoundedContinuousFunction_apply]
    calc
      ‖ballCutoffFDeriv2 x (δ / 2) δ y‖ ≤ ballCutoffFDeriv2Bound (δ / 2) δ :=
        norm_ballCutoffFDeriv2_le (by positivity) (by linarith) y
      _ = (Real.toNNReal (ballCutoffFDeriv2Bound (δ / 2) δ) : ℝ) :=
        (Real.coe_toNNReal _ hF2nonneg).symm
      _ ≤ (realBallCutoffLowerProfileConst * q ^ (3 : ℕ) : ℝ) := by
        have hsecondNN := hF2to.trans
          (mul_le_mul_of_nonneg_right hlowerCoeff88 (by positivity))
        exact_mod_cast hsecondNN
  have hbase : (Real.toNNReal (δ / 4))⁻¹ ≤ 4 * q := by
    apply NNReal.coe_le_coe.mp
    rw [NNReal.coe_inv, Real.coe_toNNReal _ (by positivity), NNReal.coe_mul]
    have hinv : (δ / 4)⁻¹ = 4 * δ⁻¹ := by
      field_simp [ne_of_gt hδ]
    rw [hinv, hqreal]
    have hsum : δ⁻¹ ≤ 1 + δ⁻¹ := by
      linarith [inv_nonneg.mpr hδ.le]
    exact mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ 4 by norm_num)
  have hqAlpha : 1 ≤ q ^ (α : ℝ) := NNReal.one_le_rpow hq α.property
  have hpatchPow : (Real.toNNReal (δ / 4))⁻¹ ^ (α : ℝ) ≤
      (4 : ℝ≥0) ^ (α : ℝ) * q ^ (α : ℝ) := by
    calc
      _ ≤ (4 * q) ^ (α : ℝ) := NNReal.rpow_le_rpow hbase α.property
      _ = (4 : ℝ≥0) ^ (α : ℝ) * q ^ (α : ℝ) := by rw [NNReal.mul_rpow]
  have hpatch : realBallPatchFactor α δ ≤
      realBallCutoffPatchProfileConst α * q ^ (α : ℝ) := by
    rw [realBallPatchFactor, realBallCutoffPatchProfileConst]
    calc
      4 + 2 * (Real.toNNReal (δ / 4))⁻¹ ^ (α : ℝ) ≤
          4 * q ^ (α : ℝ) + 2 * ((4 : ℝ≥0) ^ (α : ℝ) * q ^ (α : ℝ)) := by
        apply add_le_add
        · simpa using mul_le_mul_of_nonneg_left hqAlpha
            (show (0 : ℝ≥0) ≤ (4 : ℝ≥0) by norm_num)
        · exact mul_le_mul_of_nonneg_left hpatchPow (by norm_num)
      _ = (4 + 2 * (4 : ℝ≥0) ^ (α : ℝ)) * q ^ (α : ℝ) := by ring
  exact ⟨hscalar, hholder, hMchi, hMchi2, hsecond, hpatch⟩

end CalabiYau.Schauder
