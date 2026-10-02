module

public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.ComplexSmoothBall.Basic

/-!
# Near-pair and far-pair gauge gluing

Source: Gilbarg–Trudinger, §6.1, Theorem 6.2, freezing/interpolation proof;
Constantin, Schauder Estimates, pp. 6–9. The estimates follow Constantin, *Schauder Estimates*, pp. 6–9.
-/

@[expose] public section

open Set Matrix
open scoped NNReal ContDiff Topology

namespace CalabiYau.Schauder

/-- The exact localization contract consumed by the real-ball estimate. -/
theorem realBallGauge_le_of_patch_bounds :
    ∀ {n : ℕ} {α B : ℝ≥0} {c : RealBallModel n}
  {r δ : ℝ} {u : RealBallModel n → ℝ},
  0 < α → α < 1 → 0 ≤ r → 0 < δ →
  (∀ x ∈ Metric.closedBall c r,
    eContDiffHolderGaugeOn 2 α (Metric.closedBall x (δ / 4)) u ≤ B) →
  eContDiffHolderGaugeOn 2 α (Metric.closedBall c r) u ≤
    realBallPatchFactor α δ * B := by
  intro n α B c r δ u hα₀ hα₁ hr hδ hpatch
  let S : Set (RealBallModel n) := Metric.closedBall c r
  let ε : ℝ≥0 := Real.toNNReal (δ / 4)
  have hεpos : 0 < ε := Real.toNNReal_pos.mpr (by positivity)
  have hεcoe : (ε : ℝ) = δ / 4 :=
    Real.coe_toNNReal (δ / 4) (by positivity : 0 ≤ δ / 4)
  have hpoint (x : RealBallModel n) (hx : x ∈ S) (j : ℕ) (hj : j ≤ 2) :
      ‖iteratedFDeriv ℝ j u x‖ ≤ (B : ℝ) := by
    have hloc := hpatch x hx
    exact spatialJet_norm_le hloc hj (x := x)
      (Metric.mem_closedBall_self (by positivity))
  have hholder (x y : RealBallModel n) (hx : x ∈ S) (hy : y ∈ S) :
      edist (iteratedFDeriv ℝ 2 u x) (iteratedFDeriv ℝ 2 u y) ≤
        ((B + 2 * B / ε ^ (α : ℝ) : ℝ≥0) : ENNReal) * edist x y ^ (α : ℝ) := by
    by_cases hnear : dist x y ≤ δ / 4
    · have hxpatch : x ∈ Metric.closedBall x (δ / 4) := by
        exact Metric.mem_closedBall_self (by positivity)
      have hypatch : y ∈ Metric.closedBall x (δ / 4) := by
        rw [Metric.mem_closedBall]
        simpa [dist_comm] using hnear
      have hlocal := topSpatialJet_holderWith_restrict (hpatch x hx)
      have hlocalOn : HolderOnWith B α (iteratedFDeriv ℝ 2 u)
          (Metric.closedBall x (δ / 4)) := HolderWith.restrict_iff.mp hlocal
      have hnearBound := hlocalOn x hxpatch y hypatch
      exact hnearBound.trans (mul_le_mul_of_nonneg_right
        (ENNReal.coe_le_coe.mpr (le_add_right le_rfl)) (by positivity))
    · have hgapReal : δ / 4 ≤ dist x y := le_of_not_ge hnear
      have hgap : (ε : ENNReal) ≤ edist x y := by
        rw [edist_dist, ← ENNReal.ofReal_coe_nnreal, hεcoe]
        exact ENNReal.ofReal_le_ofReal hgapReal
      have hpow : (ε : ENNReal) ^ (α : ℝ) ≤ edist x y ^ (α : ℝ) :=
        ENNReal.rpow_le_rpow hgap α.coe_nonneg
      have hscale : ((2 * B : ℝ≥0) : ENNReal) ≤
          ((2 * B / ε ^ (α : ℝ) : ℝ≥0) : ENNReal) * edist x y ^ (α : ℝ) := by
        have hεpow : 0 < ε ^ (α : ℝ) := NNReal.rpow_pos hεpos
        have hiden : 2 * B = (2 * B / ε ^ (α : ℝ)) * ε ^ (α : ℝ) := by
          field_simp [ne_of_gt hεpow]
        calc
          ((2 * B : ℝ≥0) : ENNReal) =
              ((2 * B / ε ^ (α : ℝ) * ε ^ (α : ℝ) : ℝ≥0) : ENNReal) := by
                exact congrArg (fun t : ℝ≥0 => (t : ENNReal)) hiden
          _ = ((2 * B / ε ^ (α : ℝ) : ℝ≥0) : ENNReal) *
              (ε : ENNReal) ^ (α : ℝ) := by
            rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg _ α.coe_nonneg]
          _ ≤ ((2 * B / ε ^ (α : ℝ) : ℝ≥0) : ENNReal) *
              edist x y ^ (α : ℝ) :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
      have hxnorm := hpoint x hx 2 (by omega)
      have hynorm := hpoint y hy 2 (by omega)
      have hjetdist : edist (iteratedFDeriv ℝ 2 u x) (iteratedFDeriv ℝ 2 u y) ≤
          (2 * B : ENNReal) := by
        rw [edist_dist]
        calc
          ENNReal.ofReal (dist (iteratedFDeriv ℝ 2 u x) (iteratedFDeriv ℝ 2 u y)) ≤
              ENNReal.ofReal (‖iteratedFDeriv ℝ 2 u x‖ +
                ‖iteratedFDeriv ℝ 2 u y‖) :=
            ENNReal.ofReal_le_ofReal (dist_le_norm_add_norm _ _)
          _ ≤ ENNReal.ofReal (2 * (B : ℝ)) :=
            ENNReal.ofReal_le_ofReal (by linarith)
          _ = (2 * B : ENNReal) := by
            rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
            simp
      have hfar : edist (iteratedFDeriv ℝ 2 u x) (iteratedFDeriv ℝ 2 u y) ≤
          ((2 * B / ε ^ (α : ℝ) : ℝ≥0) : ENNReal) * edist x y ^ (α : ℝ) :=
        hjetdist.trans hscale
      exact hfar.trans (mul_le_mul_of_nonneg_right
        (ENNReal.coe_le_coe.mpr (le_add_left le_rfl)) (by positivity))
  have hspatial : ∀ j ≤ 2, ∀ x ∈ S,
      ‖iteratedFDeriv ℝ j u x‖ ≤ B := by
    intro j hj x hx
    exact hpoint x hx j hj
  have hGlobalHolder : HolderWith (B + 2 * B / ε ^ (α : ℝ)) α
      (S.domRestrict (iteratedFDeriv ℝ 2 u)) := by
    intro x y
    exact hholder x.1 y.1 x.2 y.2
  have hGlobal := eContDiffHolderGaugeOn_le (fun _ : ℕ => B)
    (B + 2 * B / ε ^ (α : ℝ)) hspatial hGlobalHolder
  have hfactorNN :
      3 * B + (B + 2 * B / ε ^ (α : ℝ)) = realBallPatchFactor α δ * B := by
    rw [realBallPatchFactor]
    change 3 * B + (B + 2 * B / ε ^ (α : ℝ)) =
      (4 + 2 * ε⁻¹ ^ (α : ℝ)) * B
    have hinv : ε⁻¹ ^ (α : ℝ) = (ε ^ (α : ℝ))⁻¹ := NNReal.inv_rpow ε _
    rw [hinv]
    ring
  have hsum : ∑ j ∈ Finset.range (2 + 1), (B : ENNReal) = (3 * B : ENNReal) := by
    norm_num [Finset.sum_range_succ]
  have hfactor :
      (∑ j ∈ Finset.range (2 + 1), (B : ENNReal)) +
          ((B + 2 * B / ε ^ (α : ℝ) : ℝ≥0) : ENNReal) =
        (realBallPatchFactor α δ * B : ENNReal) := by
    rw [hsum]
    exact_mod_cast hfactorNN
  exact hGlobal.trans_eq hfactor

end CalabiYau.Schauder
