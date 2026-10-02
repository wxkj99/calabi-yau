module

public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.SourceInterpolation.Basic
public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.SourceInterpolationProofs.GapBudget

/-!
# Uniform conversion of cutoff-scale powers to radius-gap powers

Source: Constantin, *Schauder Estimates*, nested-ball localization p. 8.
The explicit coefficient below is elementary radius arithmetic for the canonical
choice δ=min(d,(t-r)/4), not an existential constant chosen after the radii.
-/

@[expose] public section

open scoped NNReal ContDiff Topology

namespace CalabiYau.Schauder

/-- The full q^p loss has an explicit coefficient depending only on R,d,p.
The exponent may be zero; then the conclusion is equality. Positive R,d and the
ordered nested radii are explicit rather than hidden in `toNNReal` conversions. -/
private theorem realBallSource_gap_q_bound
    {R d r t : ℝ} (hR : 0 < R) (hd : 0 < d) (hr : 0 ≤ r)
    (hrt : r < t) (htR : t ≤ R) :
    1 + (min d ((t-r)/4))⁻¹ ≤ (R + R/d + 4) * (t-r)⁻¹ := by
  have hgap : 0 < t-r := by linarith
  have hrad := SourceInterpolationProofs.realBallSourceRadius_inv_bound hR hd hr hrt htR
  have hratio : 1 ≤ R * (t-r)⁻¹ := by
    have hdiv : 1 ≤ R / (t-r) := (le_div_iff₀ hgap).2 (by linarith)
    simpa [div_eq_mul_inv] using hdiv
  calc
    1 + (min d ((t-r)/4))⁻¹ ≤ R*(t-r)⁻¹ + (d⁻¹*R+4)*(t-r)⁻¹ :=
      add_le_add hratio hrad
    _ = (R + R/d + 4)*(t-r)⁻¹ := by rw [div_eq_mul_inv]; ring

private theorem realBallSource_gap_power_conversion
    {R d : ℝ} (hR : 0 < R) (hd : 0 < d) (p : ℕ)
    {r t : ℝ} (hr : 0 ≤ r) (hrt : r < t) (htR : t ≤ R) :
    (1 + (Real.toNNReal (min d ((t-r)/4)))⁻¹) ^ p ≤
      Real.toNNReal (R + R/d + 4) ^ p * (Real.toNNReal (t-r))⁻¹ ^ p := by
  let δ : ℝ≥0 := Real.toNNReal (min d ((t-r)/4))
  let D : ℝ≥0 := Real.toNNReal (R + R/d + 4)
  have hgap : 0 < t-r := by linarith
  have hδpos : 0 < min d ((t-r)/4) := lt_min hd (by positivity)
  have hDpos : 0 < R + R/d + 4 := by positivity
  have hδcoe : (δ : ℝ) = min d ((t-r)/4) := Real.coe_toNNReal _ hδpos.le
  have hDcoe : (D : ℝ) = R + R/d + 4 := Real.coe_toNNReal _ hDpos.le
  have hgapcoe : (Real.toNNReal (t-r) : ℝ) = t-r := Real.coe_toNNReal _ hgap.le
  have hreal := realBallSource_gap_q_bound hR hd hr hrt htR
  have hlin : 1 + δ⁻¹ ≤ D * (Real.toNNReal (t-r))⁻¹ := by
    apply NNReal.coe_le_coe.mp
    rw [NNReal.coe_add, NNReal.coe_one, NNReal.coe_inv, NNReal.coe_mul,
      NNReal.coe_inv, hδcoe, hDcoe, hgapcoe]
    exact hreal
  have hgapInvCoe : (Real.toNNReal (t-r))⁻¹ = Real.toNNReal ((t-r)⁻¹) := by
    apply NNReal.eq
    rw [NNReal.coe_inv, Real.coe_toNNReal _ hgap.le,
      Real.coe_toNNReal _ (inv_nonneg.mpr hgap.le)]
  have hgeneric : (1 + δ⁻¹) ^ p ≤ D ^ p * Real.toNNReal ((t-r)⁻¹) ^ p := by
    calc
      (1 + δ⁻¹) ^ p ≤ (D * (Real.toNNReal (t-r))⁻¹) ^ p := by gcongr
      _ = D ^ p * (Real.toNNReal (t-r))⁻¹ ^ p := by rw [mul_pow]
      _ = D ^ p * Real.toNNReal ((t-r)⁻¹) ^ p := by rw [hgapInvCoe]
  have hfinal : (1 + δ⁻¹) ^ p ≤ D ^ p * (Real.toNNReal (t-r))⁻¹ ^ p := by
    simpa only [← hgapInvCoe] using hgeneric
  change (1 + δ⁻¹) ^ p ≤ D ^ p * (Real.toNNReal (t-r))⁻¹ ^ p
  exact hfinal

theorem realBallSource_gap_power_bound
    {R d : ℝ} (hR : 0 < R) (hd : 0 < d) (p : ℕ)
    {r t : ℝ} (hr : 0 ≤ r) (hrt : r < t) (htR : t ≤ R) :
    realBallSourceScale (min d ((t - r) / 4)) ^ p ≤
      Real.toNNReal (R + R/d + 4) ^ p * (Real.toNNReal (t - r))⁻¹ ^ p := by
  simpa only [realBallSourceScale] using
    realBallSource_gap_power_conversion hR hd p hr hrt htR

end CalabiYau.Schauder
