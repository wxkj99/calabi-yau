-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/External/DeGiorgi/UnitBallApproximationCore/Rescaling.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Euclidean.Ball.Approximation.Profiles

@[expose] public section


/-!
# Chapter 02: Unit-Ball Rescaling Layer

This module packages the rescaling of Sobolev witnesses to the unit ball.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Sobolev.Euclidean

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The dilation used in the star-shaped approximation argument. -/
def unitBallDilate (lam : ℝ) (u : E → ℝ) : E → ℝ :=
  fun x => u (lam⁻¹ • x)

omit [NeZero d] in
lemma smul_inv_mem_unitBall {lam : ℝ} (hlam : 1 < lam) {x : E}
    (hx : x ∈ Metric.ball (0 : E) 1) :
    lam⁻¹ • x ∈ Metric.ball (0 : E) 1 := by
  rw [Metric.mem_ball, dist_zero_right] at hx ⊢
  have hlam_pos : 0 < lam := lt_trans zero_lt_one hlam
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hlam_pos.le)]
  have hinv_lt_one : lam⁻¹ < 1 := by
    exact inv_lt_one_of_one_lt₀ hlam
  have hmul : lam⁻¹ * ‖x‖ ≤ ‖x‖ := by
    exact mul_le_of_le_one_left (norm_nonneg x) hinv_lt_one.le
  exact lt_of_le_of_lt hmul hx

omit [NeZero d] in
theorem eLpNorm_rescale_to_unitBall
    {p : ℝ≥0∞} {x₀ : E} {R : ℝ} {f : E → ℝ}
    (hR : 0 < R) (_hp : p ≠ 0) (hp' : p ≠ ⊤) :
    eLpNorm (fun z => f (x₀ + R • z)) p (volume.restrict (Metric.ball (0 : E) 1)) =
      ENNReal.ofReal (R⁻¹ ^ (d / p.toReal)) *
        eLpNorm f p (volume.restrict (Metric.ball x₀ R)) := by
  let _ := _hp
  set T := fun z : E => x₀ + R • z with hT_def
  have hR' : R ≠ 0 := hR.ne'
  have hT_emb : MeasurableEmbedding T :=
    ((MeasurableEquiv.addLeft x₀).measurableEmbedding).comp
      ((Homeomorph.smul (isUnit_iff_ne_zero.2 hR').unit).toMeasurableEquiv.measurableEmbedding)
  rw [show (fun z => f (x₀ + R • z)) = f ∘ T from rfl, ← hT_emb.eLpNorm_map_measure]
  have hpreimage : T ⁻¹' (Metric.ball x₀ R) = Metric.ball (0 : E) 1 := by
    ext z
    simp only [T, mem_preimage, Metric.mem_ball, dist_comm, dist_eq_norm]
    constructor
    · intro h
      have : x₀ - (x₀ + R • z) = -(R • z) := by abel
      rw [this, norm_neg, norm_smul, Real.norm_of_nonneg hR.le] at h
      simp only [sub_zero]
      rwa [show R * ‖z‖ < R ↔ ‖z‖ < 1 from by constructor <;> intro hh <;> nlinarith] at h
    · intro h
      simp only [sub_zero] at h
      have : x₀ - (x₀ + R • z) = -(R • z) := by abel
      rw [this, norm_neg, norm_smul, Real.norm_of_nonneg hR.le]
      nlinarith
  conv_lhs => rw [show Metric.ball (0 : E) 1 = T ⁻¹' Metric.ball x₀ R from hpreimage.symm]
  rw [← Measure.restrict_map hT_emb.measurable measurableSet_ball]
  have hmap : Measure.map T (volume : Measure E) =
      ENNReal.ofReal (|R ^ Module.finrank ℝ E|⁻¹) • volume := by
    rw [show T = (fun z => x₀ + z) ∘ (fun z => R • z) from rfl]
    rw [← Measure.map_map (measurable_const_add x₀) (measurable_const_smul R)]
    rw [Measure.map_addHaar_smul volume hR']
    rw [Measure.map_smul, (measurePreserving_add_left volume x₀).map_eq, abs_inv]
  rw [hmap, Measure.restrict_smul, eLpNorm_smul_measure_of_ne_top hp']
  simp only [smul_eq_mul]
  congr 1
  have hfin : Module.finrank ℝ E = d := by simp
  rw [hfin]
  have hRd_pos : (0 : ℝ) < R ^ d := pow_pos hR d
  rw [abs_of_pos hRd_pos]
  rw [show (R ^ d)⁻¹ = R⁻¹ ^ d from (inv_pow R d).symm]
  have hRinv_nonneg : (0 : ℝ) ≤ R⁻¹ := inv_nonneg.mpr hR.le
  rw [ENNReal.ofReal_rpow_of_nonneg (pow_nonneg hRinv_nonneg d) ENNReal.toReal_nonneg]
  congr 1
  rw [← Real.rpow_natCast (R⁻¹) d, ← Real.rpow_mul hRinv_nonneg]
  congr 1
  rw [ENNReal.toReal_div, ENNReal.toReal_one]
  ring

end Sobolev.Euclidean
