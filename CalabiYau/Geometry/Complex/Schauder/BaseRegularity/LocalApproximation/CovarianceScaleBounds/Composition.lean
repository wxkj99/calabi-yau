module

public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.LocalApproximation.Basic
public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.LocalApproximation.CovarianceScaleBounds.CommutationCore
public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.LocalApproximation.CovarianceScaleBounds.CompactIntegrability
public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.LocalApproximation.CovarianceScaleBounds.CompactBridge

@[expose] public section

open Set Filter MeasureTheory Classical
open scoped ContDiff NNReal Topology Convolution

namespace CalabiYau.Schauder

private theorem compactLocal_collar_sum {n : ℕ} (c : EuclideanSpace ℂ (Fin n))
    {S η : ℝ} (hη : 0 < η) :
    let K : Set (EuclideanSpace ℂ (Fin n)) :=
      (Metric.closedBall c S ×ˢ Metric.closedBall 0 (η / 2)).image
        (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) => p.1 + p.2)
    IsCompact K ∧ K ⊆ Metric.thickening η (Metric.closedBall c S) := by
  dsimp
  let C := EuclideanSpace ℂ (Fin n)
  have h1 : IsCompact (Metric.closedBall c S : Set C) := isCompact_closedBall c S
  have h2 : IsCompact (Metric.closedBall (0 : C) (η / 2)) := isCompact_closedBall 0 (η / 2)
  have hsum : IsCompact
      ((Metric.closedBall c S ×ˢ Metric.closedBall (0 : C) (η / 2)).image
        (fun p : C × C => p.1 + p.2)) := by
    apply (h1.prod h2).image
    fun_prop
  refine ⟨hsum, ?_⟩
  rintro y ⟨⟨x, v⟩, ⟨hx, hv⟩, rfl⟩
  rw [Metric.mem_thickening_iff]
  refine ⟨x, hx, ?_⟩
  calc
    dist (x + v) x = dist v 0 := by rw [dist_eq_norm, dist_eq_norm]; simp
    _ ≤ η / 2 := hv
    _ < η := by linarith

private theorem compactLocal_radius_le_four {η : ℝ} (hη : 0 < η) (m : ℕ) :
    localKernelRadius η m ≤ η / 4 := by
  unfold localKernelRadius
  have hm : 0 ≤ (m : ℝ) := by positivity
  have hden : (4 : ℝ) ≤ 4 * ((m : ℝ) + 1) := by nlinarith
  exact div_le_div_of_nonneg_left hη.le (by norm_num : (0 : ℝ) < 4) hden

private theorem compactLocal_mollify_eq_cutoff_convolution_near {n : ℕ}
    (U : Set (EuclideanSpace ℂ (Fin n))) {c : EuclideanSpace ℂ (Fin n)} {S η : ℝ}
    (hη : 0 < η) (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (f : EuclideanSpace ℂ (Fin n) → ℂ) (m : ℕ)
    (x z : EuclideanSpace ℂ (Fin n)) (hx : x ∈ Metric.ball c S)
    (hnear : dist x z < η / 8) :
    let K : Set (EuclideanSpace ℂ (Fin n)) :=
      (Metric.closedBall c S ×ˢ Metric.closedBall 0 (η / 2)).image
        (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) => p.1 + p.2)
    let Kr : Set (EuclideanSpace ℝ (Fin n × Fin 2)) := complexToRealCoordinateEquiv '' K
    localFixedMollify U hη m f z =
      ∫ w : EuclideanSpace ℝ (Fin n × Fin 2),
        localFixedKernel hη m w • Kr.indicator
          (fun y => f (complexToRealCoordinateEquiv.symm y))
          (complexToRealCoordinateEquiv z - w) := by
  dsimp
  let K : Set (EuclideanSpace ℂ (Fin n)) :=
    (Metric.closedBall c S ×ˢ Metric.closedBall 0 (η / 2)).image
      (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) => p.1 + p.2)
  let Kr : Set (EuclideanSpace ℝ (Fin n × Fin 2)) := complexToRealCoordinateEquiv '' K
  have hKU : K ⊆ U := (compactLocal_collar_sum c hη).2.trans hCollar
  have hradius := compactLocal_radius_le_four hη m
  have hsampleK (w : EuclideanSpace ℝ (Fin n × Fin 2))
      (hw : localFixedKernel hη m w ≠ 0) :
      complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w) ∈ K := by
    have htsupport : w ∈ tsupport (localFixedKernel hη m) :=
      subset_closure (Function.mem_support.mpr hw)
    change w ∈ tsupport ((localKernelBump hη m).normed
      (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))) at htsupport
    rw [(localKernelBump hη m).tsupport_normed_eq] at htsupport
    have hw' : ‖w‖ ≤ localKernelRadius η m := by
      simpa [localKernelBump, localKernelRadius, dist_eq_norm] using htsupport
    let rw := complexToRealCoordinateEquiv.symm w
    let v := z - x - rw
    have hv : dist v 0 ≤ η / 2 := by
      simp only [dist_eq_norm, sub_zero]
      dsimp [v]
      calc
        ‖z - x - rw‖ ≤ ‖z - x‖ + ‖rw‖ := norm_sub_le _ _
        _ = ‖z - x‖ + ‖w‖ := by
          rw [show ‖rw‖ = ‖w‖ by dsimp [rw]; exact complexToRealCoordinateEquiv.symm.norm_map w]
        _ = dist x z + ‖w‖ := by rw [dist_eq_norm, norm_sub_rev]
        _ ≤ η / 8 + η / 4 := add_le_add hnear.le (hw'.trans hradius)
        _ ≤ η / 2 := by linarith
    refine ⟨(x, v), ⟨Metric.ball_subset_closedBall hx, hv⟩, ?_⟩
    apply complexToRealCoordinateEquiv.injective
    rw [complexToRealCoordinateEquiv.apply_symm_apply]
    change complexToRealCoordinateEquiv
      (x + (z - x - complexToRealCoordinateEquiv.symm w)) =
        complexToRealCoordinateEquiv z - w
    simp only [map_add, map_sub, complexToRealCoordinateEquiv.apply_symm_apply]
    abel
  have hsampleU (w : EuclideanSpace ℝ (Fin n × Fin 2))
      (hw : localFixedKernel hη m w ≠ 0) :
      complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w) ∈ U :=
    hKU (hsampleK w hw)
  have hsampleKr (w : EuclideanSpace ℝ (Fin n × Fin 2))
      (hw : localFixedKernel hη m w ≠ 0) : complexToRealCoordinateEquiv z - w ∈ Kr := by
    refine ⟨complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w),
      hsampleK w hw, ?_⟩
    simp
  rw [localFixedMollify]
  apply integral_congr_ae
  filter_upwards [] with w
  by_cases hw : localFixedKernel hη m w = 0
  · simp [hw]
  · rw [if_pos (hsampleU w hw), Set.indicator_of_mem (hsampleKr w hw)]
    exact Complex.real_smul

/-- For the compactly supported kernel, the convolution derivative theorem applies. The
collar, support, and integrability hypotheses are verified here; only the generic convolution
derivative theorem is assumed. -/
private theorem compactLocal_actual_hasFDerivAt_of_convolution {n : ℕ}
    (U : Set (EuclideanSpace ℂ (Fin n))) {c : EuclideanSpace ℂ (Fin n)} {S η : ℝ}
    (hη : 0 < η) (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (f : EuclideanSpace ℂ (Fin n) → ℂ) (hf : ContinuousOn f U) (m : ℕ)
    (x : EuclideanSpace ℂ (Fin n)) (hx : x ∈ Metric.ball c S)
    (hConv :
      let K : Set (EuclideanSpace ℂ (Fin n)) :=
        (Metric.closedBall c S ×ˢ Metric.closedBall 0 (η / 2)).image
          (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) => p.1 + p.2)
      let Kr : Set (EuclideanSpace ℝ (Fin n × Fin 2)) := complexToRealCoordinateEquiv '' K
      let H : EuclideanSpace ℝ (Fin n × Fin 2) → ℂ :=
        Kr.indicator (fun y => f (complexToRealCoordinateEquiv.symm y))
      HasFDerivAt
        (fun y : EuclideanSpace ℝ (Fin n × Fin 2) =>
          ∫ w : EuclideanSpace ℝ (Fin n × Fin 2),
            localFixedKernel hη m w • H (y - w))
        (((fderiv ℝ (localFixedKernel hη m)) ⋆[
          (ContinuousLinearMap.lsmul ℝ ℝ).precompL
            (EuclideanSpace ℝ (Fin n × Fin 2)),
          (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))] H)
          (complexToRealCoordinateEquiv x)) (complexToRealCoordinateEquiv x)) :
    let K : Set (EuclideanSpace ℂ (Fin n)) :=
      (Metric.closedBall c S ×ˢ Metric.closedBall 0 (η / 2)).image
        (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) => p.1 + p.2)
    let Kr : Set (EuclideanSpace ℝ (Fin n × Fin 2)) := complexToRealCoordinateEquiv '' K
    HasFDerivAt
      (fun y => localFixedMollify U hη m f (complexToRealCoordinateEquiv.symm y))
      ((fderiv ℝ (localFixedKernel hη m) ⋆[
        (ContinuousLinearMap.lsmul ℝ ℝ).precompL
          (EuclideanSpace ℝ (Fin n × Fin 2)),
        (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))]
        (Kr.indicator (fun y => f (complexToRealCoordinateEquiv.symm y))))
        (complexToRealCoordinateEquiv x)) (complexToRealCoordinateEquiv x) := by
  dsimp
  let K : Set (EuclideanSpace ℂ (Fin n)) :=
    (Metric.closedBall c S ×ˢ Metric.closedBall 0 (η / 2)).image
      (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) => p.1 + p.2)
  let Kr : Set (EuclideanSpace ℝ (Fin n × Fin 2)) := complexToRealCoordinateEquiv '' K
  let H : EuclideanSpace ℝ (Fin n × Fin 2) → ℂ :=
    Kr.indicator (fun y => f (complexToRealCoordinateEquiv.symm y))
  have hH : Integrable H (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) :=
    compactIntegrability_compact_indicator_scalar U hη hCollar f hf
  have hEq : (fun y : EuclideanSpace ℝ (Fin n × Fin 2) =>
      localFixedMollify U hη m f (complexToRealCoordinateEquiv.symm y)) =ᶠ[
        𝓝 (complexToRealCoordinateEquiv x)]
      (fun y => ∫ w : EuclideanSpace ℝ (Fin n × Fin 2), localFixedKernel hη m w • H (y - w)) := by
    filter_upwards [Metric.ball_mem_nhds _ (by positivity : (0 : ℝ) < η / 8)] with y hy
    have hy' : dist x (complexToRealCoordinateEquiv.symm y) < η / 8 := by
      calc
        dist x (complexToRealCoordinateEquiv.symm y) =
            dist (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x))
              (complexToRealCoordinateEquiv.symm y) := by
                rw [complexToRealCoordinateEquiv.symm_apply_apply]
        _ = dist (complexToRealCoordinateEquiv x) y :=
          complexToRealCoordinateEquiv.symm.isometry.dist_eq _ _
        _ < η / 8 := by simpa [Metric.mem_ball, dist_comm] using hy
    have hlocal := compactLocal_mollify_eq_cutoff_convolution_near
      U hη hCollar f m x (complexToRealCoordinateEquiv.symm y) hx hy'
    simpa [H, Kr, K, complexToRealCoordinateEquiv.apply_symm_apply] using hlocal
  exact hConv.congr_of_eventuallyEq hEq

/-- The complex-coordinate derivative of the cutoff convolution. -/
public theorem compactComposition_actual_factor_derivative {n : ℕ}
    (U : Set (EuclideanSpace ℂ (Fin n))) {c : EuclideanSpace ℂ (Fin n)} {S η : ℝ}
    (hη : 0 < η) (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (f : EuclideanSpace ℂ (Fin n) → ℂ) (hf : ContinuousOn f U) (m : ℕ)
    (x : EuclideanSpace ℂ (Fin n)) (hx : x ∈ Metric.ball c S) :
    ∃ df : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ,
      HasFDerivAt (localFixedMollify U hη m f) df x ∧
      ∀ v : EuclideanSpace ℂ (Fin n),
        df v = ∫ w : EuclideanSpace ℝ (Fin n × Fin 2),
          (fderiv ℝ (localFixedKernel hη m) w (complexToRealCoordinateEquiv v) : ℂ) *
            (if complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w) ∈ U then
              f (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w)) else 0) := by
  let E := EuclideanSpace ℝ (Fin n × Fin 2)
  let K : Set (EuclideanSpace ℂ (Fin n)) :=
    (Metric.closedBall c S ×ˢ Metric.closedBall 0 (η / 2)).image
      (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) => p.1 + p.2)
  let Kr : Set E := complexToRealCoordinateEquiv '' K
  let H : E → ℂ := Kr.indicator (fun y => f (complexToRealCoordinateEquiv.symm y))
  have hH : Integrable H (volume : Measure E) := by
    simpa [H, Kr, K] using
      compactIntegrability_compact_indicator_scalar U hη hCollar f hf
  have hConv := compactCore_kernel_convolution_hasFDerivAt hη m H hH.locallyIntegrable
    (complexToRealCoordinateEquiv x)
  have hD := compactLocal_actual_hasFDerivAt_of_convolution U hη hCollar f hf m x hx
    (by simpa [H, Kr, K] using hConv)
  have hCLM := compactIntegrability_compact_indicator_CLM U hη hCollar f hf m x hx
  let D := ((fderiv ℝ (localFixedKernel hη m) ⋆[
    (ContinuousLinearMap.lsmul ℝ ℝ).precompL E, (volume : Measure E)] H)
      (complexToRealCoordinateEquiv x))
  have hComp := hD.comp x complexToRealCoordinateEquiv.hasFDerivAt
  have heq : (fun z : EuclideanSpace ℂ (Fin n) =>
      localFixedMollify U hη m f
        (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z))) =
      localFixedMollify U hη m f := by
    funext z
    simp
  change HasFDerivAt (fun z : EuclideanSpace ℂ (Fin n) =>
    localFixedMollify U hη m f
      (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z)))
    (D.comp complexToRealCoordinateEquiv.toContinuousLinearMap) x at hComp
  rw [heq] at hComp
  refine ⟨D.comp complexToRealCoordinateEquiv.toContinuousLinearMap, hComp, ?_⟩
  intro v
  change ((fderiv ℝ (localFixedKernel hη m) ⋆[
      (ContinuousLinearMap.lsmul ℝ ℝ).precompL E, (volume : Measure E)] H)
      (complexToRealCoordinateEquiv x)) (complexToRealCoordinateEquiv v) = _
  rw [← hD.fderiv]
  exact compactBridge_actual_cutoff_of_compact U hη hCollar m f x hx
    (complexToRealCoordinateEquiv v) hD hCLM

/-- The actual complex-coordinate derivative data for both factors and their product, discharged
by the one-factor derivative theorem. -/
public theorem compactComposition_actual_factor_derivative_data {n : ℕ}
    (U : Set (EuclideanSpace ℂ (Fin n))) {c : EuclideanSpace ℂ (Fin n)} {S η : ℝ}
    (hη : 0 < η) (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (f g : EuclideanSpace ℂ (Fin n) → ℂ) (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (m : ℕ) (x : EuclideanSpace ℂ (Fin n)) (hx : x ∈ Metric.ball c S) :
    (∃ df : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ,
      HasFDerivAt (localFixedMollify U hη m f) df x ∧
      ∀ v, df v = ∫ w : EuclideanSpace ℝ (Fin n × Fin 2),
        (fderiv ℝ (localFixedKernel hη m) w (complexToRealCoordinateEquiv v) : ℂ) *
          (if complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w) ∈ U then
            f (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w)) else 0)) ∧
    (∃ dg : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ,
      HasFDerivAt (localFixedMollify U hη m g) dg x ∧
      ∀ v, dg v = ∫ w : EuclideanSpace ℝ (Fin n × Fin 2),
        (fderiv ℝ (localFixedKernel hη m) w (complexToRealCoordinateEquiv v) : ℂ) *
          (if complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w) ∈ U then
            g (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w)) else 0)) ∧
    (∃ dfg : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ,
      HasFDerivAt (localFixedMollify U hη m (fun y => f y * g y)) dfg x ∧
      ∀ v, dfg v = ∫ w : EuclideanSpace ℝ (Fin n × Fin 2),
        (fderiv ℝ (localFixedKernel hη m) w (complexToRealCoordinateEquiv v) : ℂ) *
          (if complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w) ∈ U then
            f (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w)) *
              g (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w)) else 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact compactComposition_actual_factor_derivative U hη hCollar f hf m x hx
  · exact compactComposition_actual_factor_derivative U hη hCollar g hg m x hx
  · exact compactComposition_actual_factor_derivative U hη hCollar (fun y => f y * g y)
      (hf.mul hg) m x hx

end CalabiYau.Schauder
