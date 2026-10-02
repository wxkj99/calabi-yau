module

public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.SourceInterpolation.Basic

/-!
# Uniform norm of the canonical third cutoff derivative

Source: Constantin, *Schauder Estimates*, p. 8, smooth-cutoff localization.
The explicit constants refine that argument using the canonical profile.
-/

@[expose] public section

open scoped NNReal ContDiff Topology

namespace CalabiYau.Schauder

private theorem canonical_arg_lt_two_dist
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {center : E} {δ : ℝ} (hδ : 0 < δ) {y : E}
    (harg : ballCutoffArgument center (δ / 2) δ y < 2) :
    dist y center ≤ δ := by
  have hden : 0 < δ ^ 2 - (δ / 2) ^ 2 := by nlinarith
  have hquot :
      (‖y - center‖ ^ 2 - (δ / 2) ^ 2) / (δ ^ 2 - (δ / 2) ^ 2) < 1 := by
    simp only [ballCutoffArgument] at harg
    linarith
  rw [div_lt_iff₀ hden] at hquot
  have hnorm : ‖y - center‖ ≤ δ := by nlinarith
  simpa [dist_eq_norm] using hnorm

private theorem canonical_thirdTensor_algebra
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (a c : ℝ) (p : E →L[ℝ] ℝ)
    (Q : E →L[ℝ] E →L[ℝ] ℝ) :
    ‖((a • p).smulRight Q) +
      (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)).precompR E (a • p) Q +
      (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)).precompL E
        (a • Q + (c • p).smulRight p) p‖ ≤
      3 * |a| * ‖p‖ * ‖Q‖ + |c| * ‖p‖ ^ 3 := by
  let : SeminormedAddCommGroup (E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toSeminormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let : SeminormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toSeminormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let : SeminormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toSeminormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace
  let B := ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)
  let LR := B.precompR E
  let LL := B.precompL E
  have hB : ‖B‖ ≤ 1 := ContinuousLinearMap.norm_smulRightL_le
  have hR : ‖LR‖ ≤ 1 :=
    (ContinuousLinearMap.norm_precompR_le E B).trans hB
  have hL : ‖LL‖ ≤ 1 :=
    (ContinuousLinearMap.norm_precompL_le E B).trans hB
  have h1 : ‖(a • p).smulRight Q‖ ≤ (|a| * ‖p‖) * ‖Q‖ := by
    rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul, Real.norm_eq_abs]
  have hp : ‖a • p‖ ≤ |a| * ‖p‖ := by
    rw [norm_smul, Real.norm_eq_abs]
  have h2 : ‖LR (a • p) Q‖ ≤ (|a| * ‖p‖) * ‖Q‖ := by
    calc
      ‖LR (a • p) Q‖ ≤ ‖LR‖ * ‖a • p‖ * ‖Q‖ := LR.le_opNorm₂ _ _
      _ ≤ 1 * (|a| * ‖p‖) * ‖Q‖ := by gcongr
      _ = (|a| * ‖p‖) * ‖Q‖ := by ring
  have hinner : ‖a • Q + (c • p).smulRight p‖ ≤
      |a| * ‖Q‖ + (|c| * ‖p‖) * ‖p‖ := by
    calc
      ‖a • Q + (c • p).smulRight p‖ ≤
          ‖a • Q‖ + ‖(c • p).smulRight p‖ := norm_add_le _ _
      _ = |a| * ‖Q‖ + (|c| * ‖p‖) * ‖p‖ := by
          rw [norm_smul, Real.norm_eq_abs,
            ContinuousLinearMap.norm_smulRight_apply, norm_smul, Real.norm_eq_abs]
  have h3 : ‖LL (a • Q + (c • p).smulRight p) p‖ ≤
      (|a| * ‖Q‖ + (|c| * ‖p‖) * ‖p‖) * ‖p‖ := by
    calc
      ‖LL (a • Q + (c • p).smulRight p) p‖ ≤
          ‖LL‖ * ‖a • Q + (c • p).smulRight p‖ * ‖p‖ := LL.le_opNorm₂ _ _
      _ ≤ 1 * (|a| * ‖Q‖ + (|c| * ‖p‖) * ‖p‖) * ‖p‖ := by gcongr
      _ = (|a| * ‖Q‖ + (|c| * ‖p‖) * ‖p‖) * ‖p‖ := by ring
  calc
    ‖(a • p).smulRight Q + LR (a • p) Q + LL (a • Q + (c • p).smulRight p) p‖ ≤
        ‖(a • p).smulRight Q‖ + ‖LR (a • p) Q‖ +
          ‖LL (a • Q + (c • p).smulRight p) p‖ := norm_add₃_le
    _ ≤ (|a| * ‖p‖) * ‖Q‖ + (|a| * ‖p‖) * ‖Q‖ +
        (|a| * ‖Q‖ + (|c| * ‖p‖) * ‖p‖) * ‖p‖ := by gcongr
    _ = 3 * |a| * ‖p‖ * ‖Q‖ + |c| * ‖p‖ ^ 3 := by ring

/-- The exact tensor formula yields a dimension-free D³χ norm majorant.
The formula premise is discharged by `realBallCutoffThirdDerivative_formula` in
the profile-bundle assemble. Annulus support, rather than a global bound for the
quadratic argument's first derivative, is essential here. -/
theorem realBallCutoffThirdDerivative_norm_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (center : E) {δ : ℝ} (hδ : 0 < δ)
    (hformula : ∀ y, ballCutoffFDeriv3BoundedContinuousFunction center
      (show 0 ≤ δ / 2 by positivity) (by linarith : δ / 2 < δ) y =
        realBallCutoffThirdTensor center δ y) :
    ‖ballCutoffFDeriv3BoundedContinuousFunction center
      (show 0 ≤ δ / 2 by positivity) (by linarith : δ / 2 < δ)‖₊ ≤
        realBallCutoffThirdProfileConst * realBallSourceScale δ ^ (3 : ℕ) := by
  apply NNReal.coe_le_coe.mp
  simp only [coe_nnnorm]
  rw [BoundedContinuousFunction.norm_le (by positivity)]
  intro y
  by_cases harg : 2 ≤ ballCutoffArgument center (δ / 2) δ y
  · have hzero : realBallCutoffThirdTensor center δ y = 0 := by
      simp [realBallCutoffThirdTensor, CutoffProfile.deriv2_zero_of_ge harg,
        CutoffProfile.deriv3_zero_of_ge harg]
    rw [hformula y, hzero]
    simpa using mul_nonneg (NNReal.coe_nonneg (realBallCutoffThirdProfileConst))
      (pow_nonneg (NNReal.coe_nonneg (realBallSourceScale δ)) 3)
  · have harglt : ballCutoffArgument center (δ / 2) δ y < 2 := lt_of_not_ge harg
    have hdist : dist y center ≤ δ := canonical_arg_lt_two_dist hδ harglt
    have hp : ‖ballCutoffArgumentFDeriv center (δ / 2) δ y‖ ≤ 8 / (3 * δ) := by
      calc
        ‖ballCutoffArgumentFDeriv center (δ / 2) δ y‖ ≤
            2 * δ / (δ ^ 2 - (δ / 2) ^ 2) :=
          norm_ballCutoffArgumentFDeriv_le (center := center) (r := δ / 2) (R := δ)
            (by positivity) (by linarith) hdist
        _ = 8 / (3 * δ) := by field_simp; ring
    have hQ : ‖ballCutoffArgumentFDeriv2 (E := E) (δ / 2) δ‖ ≤
        8 / (3 * δ ^ 2) := by
      calc
        ‖ballCutoffArgumentFDeriv2 (E := E) (δ / 2) δ‖ ≤
            2 / (δ ^ 2 - (δ / 2) ^ 2) :=
          norm_ballCutoffArgumentFDeriv2_le (E := E) (r := δ / 2) (R := δ)
            (by positivity) (by linarith)
        _ = 8 / (3 * δ ^ 2) := by field_simp; ring
    let a₂ := deriv (deriv CutoffProfile.value)
      (ballCutoffArgument center (δ / 2) δ y)
    let c₃ := deriv (deriv (deriv CutoffProfile.value))
      (ballCutoffArgument center (δ / 2) δ y)
    have ha₂ : |a₂| ≤ CutoffProfile.derivBound :=
      CutoffProfile.abs_deriv2_le_derivBound _
    have hc₃ : |c₃| ≤ CutoffProfile.deriv3Bound :=
      CutoffProfile.abs_deriv3_le_deriv3Bound _
    have hB₂ : 0 ≤ CutoffProfile.derivBound := CutoffProfile.derivBound_nonneg
    have hB₃ : 0 ≤ CutoffProfile.deriv3Bound := CutoffProfile.deriv3Bound_nonneg
    have htensor : ‖realBallCutoffThirdTensor center δ y‖ ≤
        3 * |a₂| * ‖ballCutoffArgumentFDeriv center (δ / 2) δ y‖ *
          ‖ballCutoffArgumentFDeriv2 (E := E) (δ / 2) δ‖ +
        |c₃| * ‖ballCutoffArgumentFDeriv center (δ / 2) δ y‖ ^ 3 := by
      simpa [realBallCutoffThirdTensor, a₂, c₃] using
        (canonical_thirdTensor_algebra a₂ c₃
          (ballCutoffArgumentFDeriv center (δ / 2) δ y)
          (ballCutoffArgumentFDeriv2 (E := E) (δ / 2) δ))
    have hraw : ‖realBallCutoffThirdTensor center δ y‖ ≤
        (64 / 3 * CutoffProfile.derivBound +
          512 / 27 * CutoffProfile.deriv3Bound) / δ ^ 3 := by
      calc
        ‖realBallCutoffThirdTensor center δ y‖ ≤
            3 * |a₂| * ‖ballCutoffArgumentFDeriv center (δ / 2) δ y‖ *
                ‖ballCutoffArgumentFDeriv2 (E := E) (δ / 2) δ‖ +
              |c₃| * ‖ballCutoffArgumentFDeriv center (δ / 2) δ y‖ ^ 3 := htensor
        _ ≤ 3 * CutoffProfile.derivBound * (8 / (3 * δ)) *
              (8 / (3 * δ ^ 2)) + CutoffProfile.deriv3Bound *
                (8 / (3 * δ)) ^ 3 := by
                  gcongr
        _ = (64 / 3 * CutoffProfile.derivBound +
              512 / 27 * CutoffProfile.deriv3Bound) / δ ^ 3 := by
                field_simp
                ring
    have hcoedelta : (Real.toNNReal δ : ℝ) = δ := Real.coe_toNNReal _ hδ.le
    have hscale : δ⁻¹ ≤ (realBallSourceScale δ : ℝ) := by
      rw [realBallSourceScale]
      simp only [NNReal.coe_add, NNReal.coe_one, NNReal.coe_inv]
      rw [hcoedelta]
      linarith [inv_nonneg.mpr hδ.le]
    have hscale3 : δ⁻¹ ^ 3 ≤ (realBallSourceScale δ : ℝ) ^ 3 := by
      gcongr
    have hA : 0 ≤ 64 / 3 * CutoffProfile.derivBound +
        512 / 27 * CutoffProfile.deriv3Bound := by positivity
    have hconst : (realBallCutoffThirdProfileConst : ℝ) =
        64 / 3 * CutoffProfile.derivBound +
          512 / 27 * CutoffProfile.deriv3Bound := by
      simp only [realBallCutoffThirdProfileConst]
      exact Real.coe_toNNReal _ hA
    have hmajor :
        (64 / 3 * CutoffProfile.derivBound +
          512 / 27 * CutoffProfile.deriv3Bound) / δ ^ 3 ≤
        (realBallCutoffThirdProfileConst : ℝ) *
          (realBallSourceScale δ : ℝ) ^ 3 := by
      rw [hconst]
      calc
        (64 / 3 * CutoffProfile.derivBound +
            512 / 27 * CutoffProfile.deriv3Bound) / δ ^ 3 =
            (64 / 3 * CutoffProfile.derivBound +
              512 / 27 * CutoffProfile.deriv3Bound) * δ⁻¹ ^ 3 := by
                rw [div_eq_mul_inv, ← inv_pow]
        _ ≤ (64 / 3 * CutoffProfile.derivBound +
              512 / 27 * CutoffProfile.deriv3Bound) *
                (realBallSourceScale δ : ℝ) ^ 3 :=
          mul_le_mul_of_nonneg_left hscale3 hA
    calc
      ‖(ballCutoffFDeriv3BoundedContinuousFunction center
          (show 0 ≤ δ / 2 by positivity) (by linarith : δ / 2 < δ)) y‖ =
          ‖realBallCutoffThirdTensor center δ y‖ := by rw [hformula y]
      _ ≤ (64 / 3 * CutoffProfile.derivBound +
          512 / 27 * CutoffProfile.deriv3Bound) / δ ^ 3 := hraw
      _ ≤ (realBallCutoffThirdProfileConst : ℝ) *
          (realBallSourceScale δ : ℝ) ^ 3 := hmajor

end CalabiYau.Schauder
