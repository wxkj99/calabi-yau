-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/External/DeGiorgi/UnitBallApproximationCore/Dilation.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Euclidean.Ball.Approximation.Rescaling

@[expose] public section


/-!
# Chapter 02: Unit-Ball Dilation Layer

This module contains the inward and outward dilation machinery around the unit
ball.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

namespace Sobolev.Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

lemma one_lt_midpoint_of_one_lt {lam : ℝ} (hlam : 1 < lam) :
    1 < (1 + lam) / 2 := by
  linarith

lemma midpoint_lt_of_one_lt {lam : ℝ} (hlam : 1 < lam) :
    (1 + lam) / 2 < lam := by
  linarith

/-- A cutoff equal to `1` on the unit ball and supported strictly inside `B(0, lam)`. -/
theorem exists_unitBallCutoff_inside {lam : ℝ} (hlam : 1 < lam) :
    ∃ η : Cutoff (0 : E) 1 ((1 + lam) / 2),
      tsupport η.toFun ⊆ Metric.ball (0 : E) lam := by
  obtain ⟨η, _⟩ := Cutoff.exists (d := d) (0 : E)
    (r := 1) (R := (1 + lam) / 2) zero_lt_one (one_lt_midpoint_of_one_lt hlam)
  refine ⟨η, ?_⟩
  exact η.support_subset.trans <| Metric.closedBall_subset_ball (midpoint_lt_of_one_lt hlam)

private lemma unitBall_rescale_cov_helper {lam : ℝ} (hlam : 0 < lam) (f : E → ℝ) :
    ∫ z in Metric.ball (0 : E) 1, f (lam • z) =
    (lam ^ Module.finrank ℝ E)⁻¹ * ∫ x in Metric.ball (0 : E) lam, f x := by
  open scoped Pointwise in
  have hscale := Measure.setIntegral_comp_smul_of_pos volume f (Metric.ball (0 : E) 1) hlam
  rw [show lam • Metric.ball (0 : E) 1 = Metric.ball (0 : E) lam from by
      rw [smul_unitBall hlam.ne']
      simp [Real.norm_of_nonneg hlam.le]] at hscale
  simpa [smul_eq_mul] using hscale

private lemma unitBallDilate_preimage_ball {lam : ℝ} (hlam : 0 < lam) :
    (fun x : E => lam⁻¹ • x) ⁻¹' Metric.ball (0 : E) 1 = Metric.ball (0 : E) lam := by
  ext x
  rw [Metric.mem_ball, dist_zero_right, mem_preimage, Metric.mem_ball, dist_zero_right,
    norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hlam.le)]
  constructor
  · intro hx
    simpa using (inv_mul_lt_iff₀ hlam).1 hx
  · intro hx
    have hx' : ‖x‖ < lam * 1 := by simpa using hx
    exact (inv_mul_lt_iff₀ hlam).2 hx'

private lemma unitBallDilate_map_measure {lam : ℝ} (hlam : 0 < lam) :
    Measure.map (fun x : E => lam⁻¹ • x) (volume.restrict (Metric.ball (0 : E) lam)) =
      ENNReal.ofReal (|lam⁻¹ ^ Module.finrank ℝ E|⁻¹) •
        (volume.restrict (Metric.ball (0 : E) 1)) := by
  have hmeas : Measurable (fun x : E => lam⁻¹ • x) := measurable_const_smul (lam⁻¹)
  have hrestrict :
      Measure.map (fun x : E => lam⁻¹ • x) (volume.restrict (Metric.ball (0 : E) lam)) =
        (Measure.map (fun x : E => lam⁻¹ • x) volume).restrict (Metric.ball (0 : E) 1) := by
    simpa [unitBallDilate_preimage_ball (d := d) hlam] using
      (Measure.restrict_map (μ := volume) (f := fun x : E => lam⁻¹ • x) hmeas
        (s := Metric.ball (0 : E) 1) measurableSet_ball).symm
  calc
    Measure.map (fun x : E => lam⁻¹ • x) (volume.restrict (Metric.ball (0 : E) lam))
        = (Measure.map (fun x : E => lam⁻¹ • x) volume).restrict (Metric.ball (0 : E) 1) :=
          hrestrict
    _ = (ENNReal.ofReal (|lam⁻¹ ^ Module.finrank ℝ E|⁻¹) • (volume : Measure E)).restrict
          (Metric.ball (0 : E) 1) := by
            have hpow_pos : 0 < lam⁻¹ ^ Module.finrank ℝ E := by
              exact pow_pos (inv_pos.mpr hlam) _
            rw [Measure.map_addHaar_smul volume (inv_ne_zero hlam.ne'),
              abs_of_pos (inv_pos.mpr hpow_pos), abs_of_pos hpow_pos]
    _ = ENNReal.ofReal (|lam⁻¹ ^ Module.finrank ℝ E|⁻¹) •
          (volume.restrict (Metric.ball (0 : E) 1)) := by
            rw [Measure.restrict_smul]

private lemma weakPartialDeriv_unitBallDilate_to_ball
    {i : Fin d} {lam : ℝ} {u g : E → ℝ}
    (hlam : 0 < lam)
    (hg_weak : HasWeakPartialDeriv i g u (Metric.ball (0 : E) 1)) :
    HasWeakPartialDeriv i
      (fun x => lam⁻¹ * g (lam⁻¹ • x))
      (fun x => u (lam⁻¹ • x))
      (Metric.ball (0 : E) lam) := by
  intro φ hφ_smooth hφ_supp hφ_sub
  set ψ : E → ℝ := fun z => φ (lam • z)
  have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    have hψ : ψ = φ ∘ fun z ↦ lam • z := by
      funext z
      rfl
    rw [hψ]
    exact hφ_smooth.comp (contDiff_const_smul lam)
  have hψ_supp : HasCompactSupport ψ := by
    set h : E ≃ₜ E := Homeomorph.smulOfNeZero lam hlam.ne'
    exact (show ψ = φ ∘ h from by
      ext z
      simp [ψ, h, Homeomorph.smulOfNeZero]) ▸ hφ_supp.comp_homeomorph h
  have hψ_tsub : tsupport ψ ⊆ Metric.ball (0 : E) 1 := by
    intro z hz
    have hcont : Continuous (fun z : E => lam • z) := continuous_const_smul lam
    have hz' := hφ_sub ((tsupport_comp_subset_preimage _ hcont) hz)
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg hlam.le] at hz'
    rw [Metric.mem_ball, dist_zero_right]
    nlinarith
  have key := hg_weak ψ hψ_smooth hψ_supp hψ_tsub
  set ei := EuclideanSpace.single i (1 : ℝ)
  have hfderiv_rel :
      ∀ z : E, (fderiv ℝ ψ z) ei = lam * (fderiv ℝ φ (lam • z)) ei := by
    intro z
    set S : E → E := fun y => lam • y
    have hS_fd : HasFDerivAt S (lam • ContinuousLinearMap.id ℝ E) z := by
      exact ((hasFDerivAt_id (𝕜 := ℝ) z).const_smul lam).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ ↦ rfl)
    have hφ_at : HasFDerivAt φ (fderiv ℝ φ (lam • z)) (lam • z) :=
      ((hφ_smooth.differentiable (by simp)).differentiableAt (x := lam • z)).hasFDerivAt
    have hcomp := hφ_at.comp z hS_fd
    rw [show ψ = φ ∘ S from rfl, hcomp.fderiv]
    simp [ei, smul_apply, smul_eq_mul]
  set A : ℝ := ∫ x in Metric.ball (0 : E) lam,
      u (lam⁻¹ • x) * (fderiv ℝ φ x) ei
  set B : ℝ := ∫ x in Metric.ball (0 : E) lam,
      g (lam⁻¹ • x) * φ x
  have lhs_eq :
      ∫ z in Metric.ball (0 : E) 1, u z * (fderiv ℝ ψ z) ei =
        lam * ((lam ^ Module.finrank ℝ E)⁻¹ * A) := by
    simp_rw [hfderiv_rel]
    have hmul :
        (fun z : E => u z * (lam * (fderiv ℝ φ (lam • z)) ei)) =
        (fun z : E => lam * (u z * (fderiv ℝ φ (lam • z)) ei)) := by
      funext z
      ring
    rw [hmul, integral_const_mul]
    congr 1
    simpa [A, mul_assoc, smul_smul, inv_mul_cancel₀ hlam.ne'] using
      unitBall_rescale_cov_helper (d := d) hlam
        (fun x => u (lam⁻¹ • x) * (fderiv ℝ φ x) ei)
  have rhs_eq :
      -∫ z in Metric.ball (0 : E) 1, g z * ψ z =
        -((lam ^ Module.finrank ℝ E)⁻¹ * B) := by
    congr 1
    simpa [ψ, B, smul_smul, inv_mul_cancel₀ hlam.ne'] using
      unitBall_rescale_cov_helper (d := d) hlam (fun x => g (lam⁻¹ • x) * φ x)
  rw [lhs_eq, rhs_eq] at key
  have hpow_ne : (lam ^ Module.finrank ℝ E) ≠ 0 := by
    exact pow_ne_zero _ hlam.ne'
  have hpowinv_ne : ((lam ^ Module.finrank ℝ E)⁻¹ : ℝ) ≠ 0 := inv_ne_zero hpow_ne
  have key' : (lam ^ Module.finrank ℝ E)⁻¹ * (lam * A) =
      (lam ^ Module.finrank ℝ E)⁻¹ * (-B) := by
    calc
      (lam ^ Module.finrank ℝ E)⁻¹ * (lam * A)
          = lam * ((lam ^ Module.finrank ℝ E)⁻¹ * A) := by ring
      _ = -((lam ^ Module.finrank ℝ E)⁻¹ * B) := key
      _ = (lam ^ Module.finrank ℝ E)⁻¹ * (-B) := by ring
  have key'' : lam * A = -B := by
    exact mul_left_cancel₀ hpowinv_ne key'
  have hmain : A = -(lam⁻¹ * B) := by
    calc
      A = lam⁻¹ * (lam * A) := by
            field_simp [hlam.ne']
      _ = lam⁻¹ * (-B) := by rw [key'']
      _ = -(lam⁻¹ * B) := by ring
  have hconst : ∫ x in Metric.ball (0 : E) lam, lam⁻¹ * g (lam⁻¹ • x) * φ x =
      lam⁻¹ * B := by
    simp [B, integral_const_mul, mul_assoc]
  calc
    ∫ x in Metric.ball (0 : E) lam, u (lam⁻¹ • x) * (fderiv ℝ φ x) ei = A := by rfl
    _ = -(lam⁻¹ * B) := hmain
    _ = -∫ x in Metric.ball (0 : E) lam, lam⁻¹ * g (lam⁻¹ • x) * φ x := by rw [hconst]

/-- Outward dilation from the unit ball to the larger ball `B(0, lam)`. -/
noncomputable def MemW1pWitness.unitBallDilateLargeBall
    {p : ℝ} (_hp : 1 ≤ p)
    {u : E → ℝ} {lam : ℝ}
    (hlam : 1 < lam)
    (hw : MemW1pWitness (ENNReal.ofReal p) u (Metric.ball (0 : E) 1)) :
    MemW1pWitness (ENNReal.ofReal p) (Sobolev.Euclidean.unitBallDilate (d := d) lam u)
      (Metric.ball (0 : E) lam) where
  memLp := by
    let _ := _hp
    let S : E → E := fun x => lam⁻¹ • x
    have hS_emb : MeasurableEmbedding S :=
      (Homeomorph.smulOfNeZero lam⁻¹
        (inv_ne_zero (show lam ≠ 0 from ne_of_gt
        (lt_trans zero_lt_one hlam)))).toMeasurableEquiv.measurableEmbedding
    have hmap := unitBallDilate_map_measure (d := d) (show 0 < lam from lt_trans zero_lt_one hlam)
    have hu_map :
        MemLp u (ENNReal.ofReal p)
          (Measure.map S (volume.restrict (Metric.ball (0 : E) lam))) := by
      rw [hmap]
      exact hw.memLp.smul_measure ENNReal.ofReal_ne_top
    unfold Sobolev.Euclidean.unitBallDilate
    exact MemLp.ae_eq (Filter.Eventually.of_forall fun _ ↦ rfl)
      ((hS_emb.memLp_map_measure_iff).1 hu_map)
  weakGrad := fun x => lam⁻¹ • hw.weakGrad (lam⁻¹ • x)
  weakGrad_component_memLp := by
    intro i
    let S : E → E := fun x => lam⁻¹ • x
    have hS_emb : MeasurableEmbedding S :=
      (Homeomorph.smulOfNeZero lam⁻¹
        (inv_ne_zero (show lam ≠ 0 from ne_of_gt
        (lt_trans zero_lt_one hlam)))).toMeasurableEquiv.measurableEmbedding
    have hmap := unitBallDilate_map_measure (d := d) (show 0 < lam from lt_trans zero_lt_one hlam)
    have hgi_map :
        MemLp (fun x => lam⁻¹ * hw.weakGrad x i) (ENNReal.ofReal p)
          (Measure.map S (volume.restrict (Metric.ball (0 : E) lam))) := by
      rw [hmap]
      exact ((hw.weakGrad_component_memLp i).const_mul lam⁻¹).smul_measure ENNReal.ofReal_ne_top
    exact MemLp.ae_eq (Filter.Eventually.of_forall fun _ ↦ rfl)
      ((hS_emb.memLp_map_measure_iff).1 hgi_map)
  isWeakGrad := by
    intro i
    unfold Sobolev.Euclidean.unitBallDilate
    change HasWeakPartialDeriv i
      (fun x ↦ lam⁻¹ * hw.weakGrad (lam⁻¹ • x) i)
      (fun x ↦ u (lam⁻¹ • x)) (Metric.ball (0 : E) lam)
    exact weakPartialDeriv_unitBallDilate_to_ball (d := d)
      (i := i) (lam := lam) (u := u) (g := fun x ↦ hw.weakGrad x i)
      (show 0 < lam from lt_trans zero_lt_one hlam) (hw.isWeakGrad i)

end Sobolev.Euclidean
