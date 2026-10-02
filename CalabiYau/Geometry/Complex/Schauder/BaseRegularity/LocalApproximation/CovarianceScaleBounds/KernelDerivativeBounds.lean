module

public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.LocalApproximation.Basic

open Set Filter Matrix MeasureTheory Classical
open scoped ContDiff NNReal Topology Convolution

@[expose] public section

namespace CalabiYau.Schauder

private theorem a2_leaf_integrable_fderiv_apply {n : ℕ} {η : ℝ}
    (hη : 0 < η) (m : ℕ) (v : EuclideanSpace ℝ (Fin n × Fin 2)) :
    Integrable (fun w : EuclideanSpace ℝ (Fin n × Fin 2) =>
      (fderiv ℝ (localFixedKernel hη m) w) v)
      (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) := by
  let κ : EuclideanSpace ℝ (Fin n × Fin 2) → ℝ := localFixedKernel hη m
  let F : EuclideanSpace ℝ (Fin n × Fin 2) → ℝ := fun w => (fderiv ℝ κ w) v
  have hκ : ContDiff ℝ ∞ κ := by
    dsimp [κ, localFixedKernel]
    exact (localKernelBump hη m).contDiff_normed
  have hκs : HasCompactSupport κ := by
    dsimp [κ, localFixedKernel]
    exact (localKernelBump hη m).hasCompactSupport_normed
  have hFs : HasCompactSupport F := by
    dsimp [F]
    exact hκs.fderiv_apply (𝕜 := ℝ) v
  have hFc : Continuous F := by
    dsimp [F]
    exact (hκ.continuous_fderiv (by simp)).clm_apply continuous_const
  exact hFc.integrable_of_hasCompactSupport hFs

/-- The actual real kernel derivative has zero integral by parity. -/
theorem integral_fderiv_localFixedKernel_apply_eq_zero {n : ℕ} {η : ℝ}
    (hη : 0 < η) (m : ℕ) (v : EuclideanSpace ℝ (Fin n × Fin 2)) :
    (∫ w : EuclideanSpace ℝ (Fin n × Fin 2),
      (fderiv ℝ (localFixedKernel hη m) w) v) = 0 := by
  let E := EuclideanSpace ℝ (Fin n × Fin 2)
  let μ : Measure E := volume
  let κ : E → ℝ := localFixedKernel hη m
  let F : E → ℝ := fun w => (fderiv ℝ κ w) v
  have hFint : Integrable F μ := by
    simpa [F, κ, μ] using a2_leaf_integrable_fderiv_apply hη m v
  have hEq : (fun y : E => κ ((-1 : ℝ) • y)) = κ := by
    funext y
    simpa [κ] using localFixedKernel_neg hη m y
  have hodd : ∀ x : E, F (-x) = -F x := by
    intro x
    have hd := congrArg (fun q : E → ℝ => fderiv ℝ q x) hEq
    rw [fderiv_comp_smul] at hd
    have hv := congrArg (fun L : E →L[ℝ] ℝ => L v) hd
    have hval : -F (-x) = F x := by
      simpa [F, neg_smul, smul_eq_mul] using hv
    linarith
  have hMP : MeasurePreserving (fun x : E => -x) μ μ :=
    Measure.measurePreserving_neg μ
  have hchange : (∫ w, F (-w) ∂μ) = ∫ w, F w ∂μ :=
    hMP.integral_comp (Homeomorph.neg E).measurableEmbedding F
  have hI : (∫ w, F w ∂μ) = -(∫ w, F w ∂μ) := by
    calc
      (∫ w, F w ∂μ) = ∫ w, F (-w) ∂μ := hchange.symm
      _ = ∫ w, -F w ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with w
        exact hodd w
      _ = -(∫ w, F w ∂μ) := by rw [integral_neg]
  have hzero : (∫ w, F w ∂μ) = 0 := by linarith
  simpa [E, μ, F, κ] using hzero

theorem integrable_complex_fderiv_localFixedKernel_apply {n : ℕ} {η : ℝ}
    (hη : 0 < η) (m : ℕ) (v : EuclideanSpace ℝ (Fin n × Fin 2)) :
    Integrable (fun w : EuclideanSpace ℝ (Fin n × Fin 2) =>
      ((fderiv ℝ (localFixedKernel hη m) w) v : ℂ))
      (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) := by
  have hReal := a2_leaf_integrable_fderiv_apply hη m v
  simpa only [Complex.ofRealCLM_apply] using (Complex.ofRealCLM).integrable_comp hReal

theorem integral_complex_fderiv_localFixedKernel_apply_eq_zero {n : ℕ} {η : ℝ}
    (hη : 0 < η) (m : ℕ) (v : EuclideanSpace ℝ (Fin n × Fin 2)) :
    (∫ w : EuclideanSpace ℝ (Fin n × Fin 2),
      ((fderiv ℝ (localFixedKernel hη m) w) v : ℂ)) = 0 := by
  rw [integral_complex_ofReal, integral_fderiv_localFixedKernel_apply_eq_zero hη m v]
  norm_num

private theorem a2_leaf_bump_apply_scale {n : ℕ} {η : ℝ} (hη : 0 < η) (m : ℕ)
    (w : EuclideanSpace ℝ (Fin n × Fin 2)) :
    localKernelBump hη m w =
      localKernelBump (show (0 : ℝ) < 4 by norm_num) 0
        ((localKernelRadius η m)⁻¹ • w) := by
  rw [ContDiffBump.apply, ContDiffBump.apply]
  simp only [localKernelBump, localKernelRadius]
  congr 1
  · field_simp [ne_of_gt (localKernelRadius_pos hη m)]
  · simp only [sub_zero]
    rw [smul_smul]
    congr 1
    (field_simp [ne_of_gt (localKernelRadius_pos hη m)]; ring)

private theorem a2_leaf_fixedKernel_homothety {n : ℕ} {η : ℝ} (hη : 0 < η) (m : ℕ)
    (w : EuclideanSpace ℝ (Fin n × Fin 2)) :
    localFixedKernel hη m w =
      (localKernelRadius η m)⁻¹ ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin n × Fin 2)) *
        localFixedKernel (show (0 : ℝ) < 4 by norm_num) 0
          ((localKernelRadius η m)⁻¹ • w) := by
  let E := EuclideanSpace ℝ (Fin n × Fin 2)
  let κ : E → ℝ := localKernelBump (show (0 : ℝ) < 4 by norm_num) 0
  have hr : 0 < localKernelRadius η m := localKernelRadius_pos hη m
  have hI : 0 < ∫ x, κ x ∂(volume : Measure E) := by
    dsimp [κ]
    exact (localKernelBump (show (0 : ℝ) < 4 by norm_num) 0).integral_pos
  have hInt :
      (∫ x, localKernelBump hη m x ∂(volume : Measure E)) =
        (localKernelRadius η m ^ Module.finrank ℝ E) *
          ∫ x, κ x ∂(volume : Measure E) := by
    calc
      _ = ∫ x, κ ((localKernelRadius η m)⁻¹ • x) ∂(volume : Measure E) := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact a2_leaf_bump_apply_scale hη m x
      _ = _ := by
        simpa [κ, smul_eq_mul] using
          (Measure.integral_comp_inv_smul_of_nonneg
            (μ := (volume : Measure E)) (f := κ) hr.le)
  have hI' :
      (∫ x, localKernelBump (show (0 : ℝ) < 4 by norm_num) 0 x
        ∂(volume : Measure E)) = ∫ x, κ x ∂(volume : Measure E) := rfl
  change (localKernelBump hη m).normed (volume : Measure E) w =
    (localKernelRadius η m)⁻¹ ^ Module.finrank ℝ E *
      (localKernelBump (show (0 : ℝ) < 4 by norm_num) 0).normed
        (volume : Measure E) ((localKernelRadius η m)⁻¹ • w)
  rw [ContDiffBump.normed_def, ContDiffBump.normed_def,
    a2_leaf_bump_apply_scale hη m w, hInt, hI']
  field_simp [ne_of_gt hI, ne_of_gt (pow_pos hr _)]
  have hcoef :
      localKernelRadius η m ^ Module.finrank ℝ E *
          (1 / localKernelRadius η m) ^ Module.finrank ℝ E = 1 := by
    rw [← mul_pow]
    simp [hr.ne']
  rw [mul_assoc, hcoef, mul_one]

private theorem a2_leaf_fderiv_homothety {n : ℕ} {η : ℝ} (hη : 0 < η) (m : ℕ)
    (w : EuclideanSpace ℝ (Fin n × Fin 2)) :
    fderiv ℝ (localFixedKernel hη m) w =
      ((localKernelRadius η m)⁻¹ ^
        Module.finrank ℝ (EuclideanSpace ℝ (Fin n × Fin 2)) *
          (localKernelRadius η m)⁻¹) •
        fderiv ℝ (localFixedKernel (show (0 : ℝ) < 4 by norm_num) 0)
          ((localKernelRadius η m)⁻¹ • w) := by
  let E := EuclideanSpace ℝ (Fin n × Fin 2)
  let r := localKernelRadius η m
  let κ : E → ℝ := localFixedKernel (show (0 : ℝ) < 4 by norm_num) 0
  have hκ : ContDiff ℝ ∞ κ := by
    dsimp [κ, localFixedKernel]
    exact (localKernelBump (show (0 : ℝ) < 4 by norm_num) 0).contDiff_normed
  have hr : 0 < r := localKernelRadius_pos hη m
  have hfunc : localFixedKernel hη m =
      fun x => r⁻¹ ^ Module.finrank ℝ E * κ (r⁻¹ • x) := by
    funext x
    exact a2_leaf_fixedKernel_homothety hη m x
  have hscale : DifferentiableAt ℝ (fun x : E => r⁻¹ • x) w := by
    change DifferentiableAt ℝ (r⁻¹ • id) w
    exact differentiableAt_id.const_smul _
  have hcomp : DifferentiableAt ℝ (fun x : E => κ (r⁻¹ • x)) w :=
    ((hκ.differentiable (by simp)).differentiableAt).comp w hscale
  rw [hfunc]
  change fderiv ℝ (fun x : E => r⁻¹ ^ Module.finrank ℝ E • κ (r⁻¹ • x)) w =
    (r⁻¹ ^ Module.finrank ℝ E * r⁻¹) • fderiv ℝ κ (r⁻¹ • w)
  rw [fderiv_fun_const_smul hcomp (r⁻¹ ^ Module.finrank ℝ E), fderiv_comp_smul]
  simp only [smul_smul]

/-- The true derivative-kernel L1 constant scales as exactly one inverse radius. -/
theorem covarianceA2_derivativeKernelL1_scale {n : ℕ} {η : ℝ}
    (hη : 0 < η) (m : ℕ) :
    (∫ x : EuclideanSpace ℝ (Fin n × Fin 2),
      ‖fderiv ℝ (localFixedKernel hη m) x‖) =
      (localKernelRadius η m)⁻¹ *
        (∫ x : EuclideanSpace ℝ (Fin n × Fin 2),
          ‖fderiv ℝ (localFixedKernel (show (0 : ℝ) < 4 by norm_num) 0) x‖) := by
  let E := EuclideanSpace ℝ (Fin n × Fin 2)
  let r := localKernelRadius η m
  let κ : E → ℝ := localFixedKernel (show (0 : ℝ) < 4 by norm_num) 0
  let d := Module.finrank ℝ E
  have hr : 0 < r := localKernelRadius_pos hη m
  have hcpos : 0 < r⁻¹ ^ d * r⁻¹ :=
    mul_pos (pow_pos (inv_pos.mpr hr) _) (inv_pos.mpr hr)
  have hchange :
      (∫ x, ‖fderiv ℝ κ (r⁻¹ • x)‖ ∂(volume : Measure E)) =
        r ^ d * ∫ x, ‖fderiv ℝ κ x‖ ∂(volume : Measure E) := by
    simpa [d, smul_eq_mul] using
      (Measure.integral_comp_inv_smul_of_nonneg
        (μ := (volume : Measure E)) (f := fun x => ‖fderiv ℝ κ x‖) hr.le)
  have hcoef : (r⁻¹ ^ d * r⁻¹) * r ^ d = r⁻¹ := by
    have hpow : r⁻¹ ^ d * r ^ d = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hr.ne', one_pow]
    calc
      (r⁻¹ ^ d * r⁻¹) * r ^ d = r⁻¹ * (r⁻¹ ^ d * r ^ d) := by ring
      _ = r⁻¹ := by rw [hpow, mul_one]
  calc
    (∫ x : EuclideanSpace ℝ (Fin n × Fin 2),
        ‖fderiv ℝ (localFixedKernel hη m) x‖ ∂(volume : Measure E)) =
        ∫ x, (r⁻¹ ^ d * r⁻¹) * ‖fderiv ℝ κ (r⁻¹ • x)‖ ∂(volume : Measure E) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [a2_leaf_fderiv_homothety hη m x, norm_smul, Real.norm_eq_abs,
        abs_of_pos hcpos]
    _ = (r⁻¹ ^ d * r⁻¹) *
        ∫ x, ‖fderiv ℝ κ (r⁻¹ • x)‖ ∂(volume : Measure E) := by
      rw [integral_const_mul]
    _ = r⁻¹ * ∫ x, ‖fderiv ℝ κ x‖ ∂(volume : Measure E) := by
      rw [hchange]
      calc
        (r⁻¹ ^ d * r⁻¹) * (r ^ d * ∫ x, ‖fderiv ℝ κ x‖ ∂(volume : Measure E)) =
            ((r⁻¹ ^ d * r⁻¹) * r ^ d) *
              ∫ x, ‖fderiv ℝ κ x‖ ∂(volume : Measure E) := by ring
        _ = r⁻¹ * ∫ x, ‖fderiv ℝ κ x‖ ∂(volume : Measure E) := by rw [hcoef]
    _ = _ := rfl

private theorem a2_leaf_integrable_unitDerivative {n : ℕ} :
    Integrable
      (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
        ‖fderiv ℝ (localFixedKernel (show (0 : ℝ) < 4 by norm_num) 0) x‖)
      (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) := by
  let κ : EuclideanSpace ℝ (Fin n × Fin 2) → ℝ :=
    localFixedKernel (show (0 : ℝ) < 4 by norm_num) 0
  have hκ : ContDiff ℝ ∞ κ := by
    dsimp [κ, localFixedKernel]
    exact (localKernelBump (show (0 : ℝ) < 4 by norm_num) 0).contDiff_normed
  have hcompact : HasCompactSupport κ := by
    dsimp [κ, localFixedKernel]
    exact (localKernelBump (show (0 : ℝ) < 4 by norm_num) 0).hasCompactSupport_normed
  have hderiv : HasCompactSupport (fun x => ‖fderiv ℝ κ x‖) :=
    (hcompact.fderiv (𝕜 := ℝ)).norm
  exact (hκ.continuous_fderiv (by simp)).norm.integrable_of_hasCompactSupport hderiv

/-- The fixed unit-scale derivative L1 constant; it need not be at most one. -/
noncomputable def covarianceA2_J (n : ℕ) : ℝ :=
  ∫ x : EuclideanSpace ℝ (Fin n × Fin 2),
    ‖fderiv ℝ (localFixedKernel (show (0 : ℝ) < 4 by norm_num) 0) x‖

theorem covarianceA2_J_nonneg (n : ℕ) : 0 ≤ covarianceA2_J n := by
  rw [covarianceA2_J]
  exact integral_nonneg (fun x => norm_nonneg _)

private theorem a2_leaf_integrable_kernelDerivative {n : ℕ} {η : ℝ}
    (hη : 0 < η) (m : ℕ) :
    Integrable
      (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
        ‖fderiv ℝ (localFixedKernel hη m) x‖)
      (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) := by
  let κ : EuclideanSpace ℝ (Fin n × Fin 2) → ℝ := localFixedKernel hη m
  have hκ : ContDiff ℝ ∞ κ := by
    dsimp [κ, localFixedKernel]
    exact (localKernelBump hη m).contDiff_normed
  have hcompact : HasCompactSupport κ := by
    dsimp [κ, localFixedKernel]
    exact (localKernelBump hη m).hasCompactSupport_normed
  have hderiv : HasCompactSupport (fun x => ‖fderiv ℝ κ x‖) :=
    (hcompact.fderiv (𝕜 := ℝ)).norm
  exact (hκ.continuous_fderiv (by simp)).norm.integrable_of_hasCompactSupport hderiv

private theorem a2_leaf_integrable_kernelDerivative_apply {n : ℕ} {η : ℝ}
    (hη : 0 < η) (m : ℕ) (v : EuclideanSpace ℝ (Fin n × Fin 2)) :
    Integrable
      (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
        ‖fderiv ℝ (localFixedKernel hη m) x v‖)
      (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) := by
  let κ : EuclideanSpace ℝ (Fin n × Fin 2) → ℝ := localFixedKernel hη m
  have hκ : ContDiff ℝ ∞ κ := by
    dsimp [κ, localFixedKernel]
    exact (localKernelBump hη m).contDiff_normed
  have hcompact : HasCompactSupport κ := by
    dsimp [κ, localFixedKernel]
    exact (localKernelBump hη m).hasCompactSupport_normed
  have hderiv : HasCompactSupport (fun x => ‖fderiv ℝ κ x v‖) :=
    (hcompact.fderiv_apply (𝕜 := ℝ) v).norm
  have hcont : Continuous (fun x => ‖fderiv ℝ κ x v‖) :=
    ((hκ.continuous_fderiv (by simp)).clm_apply continuous_const).norm
  exact hcont.integrable_of_hasCompactSupport hderiv

theorem covarianceA2_directionalDerivativeL1_le {n : ℕ} {η : ℝ}
    (hη : 0 < η) (m : ℕ) (v : EuclideanSpace ℝ (Fin n × Fin 2)) :
    (∫ x : EuclideanSpace ℝ (Fin n × Fin 2),
      ‖fderiv ℝ (localFixedKernel hη m) x v‖) ≤
      (localKernelRadius η m)⁻¹ * covarianceA2_J n * ‖v‖ := by
  have hpoint (x : EuclideanSpace ℝ (Fin n × Fin 2)) :
      ‖fderiv ℝ (localFixedKernel hη m) x v‖ ≤
        ‖fderiv ℝ (localFixedKernel hη m) x‖ * ‖v‖ :=
    ContinuousLinearMap.le_opNorm _ _
  calc
    _ ≤ ∫ x : EuclideanSpace ℝ (Fin n × Fin 2),
        ‖v‖ * ‖fderiv ℝ (localFixedKernel hη m) x‖ := by
      apply integral_mono
        (a2_leaf_integrable_kernelDerivative_apply hη m v)
        ((a2_leaf_integrable_kernelDerivative hη m).const_mul ‖v‖)
      intro x
      simpa [mul_comm] using hpoint x
    _ = ‖v‖ * ∫ x : EuclideanSpace ℝ (Fin n × Fin 2),
        ‖fderiv ℝ (localFixedKernel hη m) x‖ := by rw [integral_const_mul]
    _ = (localKernelRadius η m)⁻¹ * covarianceA2_J n * ‖v‖ := by
      rw [covarianceA2_derivativeKernelL1_scale]
      simp [covarianceA2_J]
      ring

theorem integral_norm_complex_fderiv_localFixedKernel_apply_le {n : ℕ} {η : ℝ}
    (hη : 0 < η) (m : ℕ) (v : EuclideanSpace ℝ (Fin n × Fin 2)) :
    (∫ x : EuclideanSpace ℝ (Fin n × Fin 2),
      ‖((fderiv ℝ (localFixedKernel hη m) x) v : ℂ)‖) ≤
      (localKernelRadius η m)⁻¹ * covarianceA2_J n * ‖v‖ := by
  calc
    _ = ∫ x : EuclideanSpace ℝ (Fin n × Fin 2),
        ‖fderiv ℝ (localFixedKernel hη m) x v‖ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp
    _ ≤ (localKernelRadius η m)⁻¹ * covarianceA2_J n * ‖v‖ :=
      covarianceA2_directionalDerivativeL1_le hη m v

/-- Complex coordinate directions obey the same scaled derivative L1 bound. -/
theorem covarianceA2_complexDirectionDerivativeL1_le {n : ℕ} {η : ℝ}
    (hη : 0 < η) (m : ℕ) (v : EuclideanSpace ℂ (Fin n)) :
    (∫ x : EuclideanSpace ℝ (Fin n × Fin 2),
      ‖((fderiv ℝ (localFixedKernel hη m) x)
        (complexToRealCoordinateEquiv v) : ℂ)‖) ≤
      (localKernelRadius η m)⁻¹ * covarianceA2_J n * ‖v‖ := by
  calc
    _ ≤ (localKernelRadius η m)⁻¹ * covarianceA2_J n *
        ‖complexToRealCoordinateEquiv v‖ :=
      integral_norm_complex_fderiv_localFixedKernel_apply_le hη m
        (complexToRealCoordinateEquiv v)
    _ = (localKernelRadius η m)⁻¹ * covarianceA2_J n * ‖v‖ := by
      rw [complexToRealCoordinateEquiv.norm_map]

private theorem a2_leaf_fderiv_eq_zero_outside_closedBall {n : ℕ} {η : ℝ}
    (hη : 0 < η) (m : ℕ) (w : EuclideanSpace ℝ (Fin n × Fin 2))
    (hw : w ∉ Metric.closedBall 0 (localKernelRadius η m)) :
    fderiv ℝ (localFixedKernel hη m) w = 0 := by
  apply fderiv_of_notMem_tsupport
  intro hts
  change w ∈ tsupport ((localKernelBump hη m).normed
    (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))) at hts
  rw [(localKernelBump hη m).tsupport_normed_eq] at hts
  apply hw
  have hnorm : ‖w‖ ≤ localKernelRadius η m := by
    simpa [localKernelBump, localKernelRadius] using hts
  simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm

theorem covarianceA2_fderiv_apply_norm_le_radius_of_ne_zero {n : ℕ} {η : ℝ}
    (hη : 0 < η) (m : ℕ) (v w : EuclideanSpace ℝ (Fin n × Fin 2))
    (hq : fderiv ℝ (localFixedKernel hη m) w v ≠ 0) :
    ‖w‖ ≤ localKernelRadius η m := by
  by_contra hn
  have hw : w ∉ Metric.closedBall 0 (localKernelRadius η m) := by
    intro hb
    apply hn
    simpa [Metric.mem_closedBall, dist_eq_norm] using hb
  have hz := a2_leaf_fderiv_eq_zero_outside_closedBall hη m w hw
  rw [hz] at hq
  exact hq rfl

/-- Integrability, zero mass, and radius support for the complex-coordinate direction. -/
theorem covarianceA2_complexDirection_q_bundle {n : ℕ} {η : ℝ}
    (hη : 0 < η) (m : ℕ) (v : EuclideanSpace ℂ (Fin n)) :
    Integrable (fun w : EuclideanSpace ℝ (Fin n × Fin 2) =>
      ((fderiv ℝ (localFixedKernel hη m) w) (complexToRealCoordinateEquiv v) : ℂ))
        (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) ∧
    (∫ w : EuclideanSpace ℝ (Fin n × Fin 2),
      ((fderiv ℝ (localFixedKernel hη m) w) (complexToRealCoordinateEquiv v) : ℂ)) = 0 ∧
    (∀ w : EuclideanSpace ℝ (Fin n × Fin 2),
      ((fderiv ℝ (localFixedKernel hη m) w) (complexToRealCoordinateEquiv v) : ℂ) ≠ 0 →
        ‖w‖ ≤ localKernelRadius η m) := by
  refine ⟨integrable_complex_fderiv_localFixedKernel_apply hη m
      (complexToRealCoordinateEquiv v),
    integral_complex_fderiv_localFixedKernel_apply_eq_zero hη m
      (complexToRealCoordinateEquiv v), ?_⟩
  intro w hq
  apply covarianceA2_fderiv_apply_norm_le_radius_of_ne_zero hη m
    (complexToRealCoordinateEquiv v) w ?_
  exact_mod_cast hq

end CalabiYau.Schauder
