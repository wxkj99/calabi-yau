module

public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.LocalApproximation.Basic

@[expose] public section

open Set Filter MeasureTheory Classical
open scoped ContDiff NNReal Topology Convolution

namespace CalabiYau.Schauder

/-- Small integrability-to-scalarization leaf for the actual cutoff derivative.  The analytic
compact-indicator certificate and the collar scalar equality are explicit premises, keeping this
module independently checkable against Basic. -/
public theorem compactBridge_apply_of_derivative_and_cutoff {n : ℕ}
    (U : Set (EuclideanSpace ℂ (Fin n))) {η : ℝ}
    (hη : 0 < η) (m : ℕ) (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (x : EuclideanSpace ℂ (Fin n))
    (v : EuclideanSpace ℝ (Fin n × Fin 2))
    (H : EuclideanSpace ℝ (Fin n × Fin 2) → ℂ)
    (hD : HasFDerivAt
      (fun y => localFixedMollify U hη m f (complexToRealCoordinateEquiv.symm y))
      ((fderiv ℝ (localFixedKernel hη m) ⋆[
        (ContinuousLinearMap.lsmul ℝ ℝ).precompL
          (EuclideanSpace ℝ (Fin n × Fin 2)),
        (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))] H)
        (complexToRealCoordinateEquiv x)) (complexToRealCoordinateEquiv x))
    (hCLM : Integrable
      (fun w : EuclideanSpace ℝ (Fin n × Fin 2) =>
        ((ContinuousLinearMap.lsmul ℝ ℝ).precompL
          (EuclideanSpace ℝ (Fin n × Fin 2)))
          (fderiv ℝ (localFixedKernel hη m) w)
          (H (complexToRealCoordinateEquiv x - w)))
      (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))))
    (hScalar : ∀ v : EuclideanSpace ℝ (Fin n × Fin 2),
      (∫ w : EuclideanSpace ℝ (Fin n × Fin 2),
        (fderiv ℝ (localFixedKernel hη m) w v : ℂ) *
          H (complexToRealCoordinateEquiv x - w)) =
      ∫ w : EuclideanSpace ℝ (Fin n × Fin 2),
        (fderiv ℝ (localFixedKernel hη m) w v : ℂ) *
          (if complexToRealCoordinateEquiv.symm
              (complexToRealCoordinateEquiv x - w) ∈ U then
            f (complexToRealCoordinateEquiv.symm
              (complexToRealCoordinateEquiv x - w)) else 0)) :
    (fderiv ℝ (fun y => localFixedMollify U hη m f
      (complexToRealCoordinateEquiv.symm y))
      (complexToRealCoordinateEquiv x)) v =
      ∫ w : EuclideanSpace ℝ (Fin n × Fin 2),
        (fderiv ℝ (localFixedKernel hη m) w v : ℂ) *
          (if complexToRealCoordinateEquiv.symm
              (complexToRealCoordinateEquiv x - w) ∈ U then
            f (complexToRealCoordinateEquiv.symm
              (complexToRealCoordinateEquiv x - w)) else 0) := by
  classical
  rw [hD.fderiv]
  have hstar :
      ((fderiv ℝ (localFixedKernel hη m) ⋆[
        (ContinuousLinearMap.lsmul ℝ ℝ).precompL
          (EuclideanSpace ℝ (Fin n × Fin 2)),
        (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))] H)
        (complexToRealCoordinateEquiv x)) =
        ∫ w : EuclideanSpace ℝ (Fin n × Fin 2),
          ((ContinuousLinearMap.lsmul ℝ ℝ).precompL
            (EuclideanSpace ℝ (Fin n × Fin 2)))
            (fderiv ℝ (localFixedKernel hη m) w)
            (H (complexToRealCoordinateEquiv x - w)) := by
    rw [← MeasureTheory.convolution_flip]
    rw [MeasureTheory.convolution_eq_swap]
    simp
  rw [hstar, ContinuousLinearMap.integral_apply hCLM]
  exact hScalar v

open Classical in
/-- The derivative kernel is supported within the actual collar, so compact-indicator and
actual U-cutoff scalar integrals agree. -/
public theorem compactBridge_scalar_cutoff_eq {n : ℕ}
    (U : Set (EuclideanSpace ℂ (Fin n))) {c : EuclideanSpace ℂ (Fin n)} {S η : ℝ}
    (hη : 0 < η) (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (f : EuclideanSpace ℂ (Fin n) → ℂ) (m : ℕ)
    (x : EuclideanSpace ℂ (Fin n)) (hx : x ∈ Metric.ball c S)
    (v : EuclideanSpace ℝ (Fin n × Fin 2)) :
    let K : Set (EuclideanSpace ℂ (Fin n)) :=
      (Metric.closedBall c S ×ˢ Metric.closedBall 0 (η / 2)).image
        (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) => p.1 + p.2)
    let Kr : Set (EuclideanSpace ℝ (Fin n × Fin 2)) := complexToRealCoordinateEquiv '' K
    (∫ w : EuclideanSpace ℝ (Fin n × Fin 2),
      (fderiv ℝ (localFixedKernel hη m) w v : ℂ) *
        Kr.indicator (fun y => f (complexToRealCoordinateEquiv.symm y))
          (complexToRealCoordinateEquiv x - w)) =
      ∫ w : EuclideanSpace ℝ (Fin n × Fin 2),
        (fderiv ℝ (localFixedKernel hη m) w v : ℂ) *
          (if complexToRealCoordinateEquiv.symm
              (complexToRealCoordinateEquiv x - w) ∈ U then
            f (complexToRealCoordinateEquiv.symm
              (complexToRealCoordinateEquiv x - w)) else 0) := by
  dsimp
  let K : Set (EuclideanSpace ℂ (Fin n)) :=
    (Metric.closedBall c S ×ˢ Metric.closedBall 0 (η / 2)).image
      (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) => p.1 + p.2)
  let Kr : Set (EuclideanSpace ℝ (Fin n × Fin 2)) := complexToRealCoordinateEquiv '' K
  let sample : EuclideanSpace ℝ (Fin n × Fin 2) → EuclideanSpace ℂ (Fin n) :=
    fun w => complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w)
  apply integral_congr_ae
  filter_upwards [] with w
  by_cases hderiv : fderiv ℝ (localFixedKernel hη m) w v = 0
  · simp [hderiv]
  · have hderivCLM : fderiv ℝ (localFixedKernel hη m) w ≠ 0 := by
      intro hzero
      exact hderiv (congrArg (fun D : EuclideanSpace ℝ (Fin n × Fin 2) →L[ℝ] ℝ => D v) hzero)
    have hts : w ∈ tsupport (fderiv ℝ (localFixedKernel hη m)) :=
      subset_closure (Function.mem_support.mpr hderivCLM)
    have htsκ : w ∈ tsupport (localFixedKernel hη m) :=
      (tsupport_fderiv_subset ℝ hts)
    change w ∈ tsupport ((localKernelBump hη m).normed
      (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))) at htsκ
    rw [(localKernelBump hη m).tsupport_normed_eq] at htsκ
    have hw : ‖w‖ ≤ localKernelRadius η m := by
      simpa [localKernelBump, localKernelRadius] using htsκ
    have hr : localKernelRadius η m ≤ η / 4 := by
      unfold localKernelRadius
      have hm : 0 ≤ (m : ℝ) := by positivity
      have hden : (4 : ℝ) ≤ 4 * ((m : ℝ) + 1) := by nlinarith
      exact div_le_div_of_nonneg_left hη.le (by norm_num) hden
    have hxs : x = complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x) :=
      (complexToRealCoordinateEquiv.symm_apply_apply x).symm
    have hxsample : dist (sample w) x = ‖w‖ := by
      calc
        dist (sample w) x =
            dist (sample w) (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x)) :=
          congrArg (fun q => dist (sample w) q) hxs
        _ = dist (complexToRealCoordinateEquiv x - w) (complexToRealCoordinateEquiv x) := by
          dsimp [sample]
          exact complexToRealCoordinateEquiv.symm.isometry.dist_eq _ _
        _ = ‖w‖ := by
          rw [dist_eq_norm]
          have hs : (complexToRealCoordinateEquiv x - w) - complexToRealCoordinateEquiv x = -w := by abel
          rw [hs, norm_neg]
    have hthick : sample w ∈ Metric.thickening η (Metric.closedBall c S) := by
      rw [Metric.mem_thickening_iff]
      refine ⟨x, Metric.ball_subset_closedBall hx, ?_⟩
      calc
        dist (sample w) x = ‖w‖ := hxsample
        _ ≤ localKernelRadius η m := hw
        _ ≤ η / 4 := hr
        _ < η := by linarith [hη]
    have hU : sample w ∈ U := hCollar hthick
    have hKr : complexToRealCoordinateEquiv x - w ∈ Kr := by
      refine ⟨sample w, ?_, ?_⟩
      · let offset := sample w - x
        have hoff : ‖offset‖ ≤ η / 2 := by
          dsimp [offset]
          calc
            ‖sample w - x‖ = dist (sample w) x := by rw [dist_eq_norm]
            _ = ‖w‖ := hxsample
            _ ≤ localKernelRadius η m := hw
            _ ≤ η / 4 := hr
            _ ≤ η / 2 := by linarith
        refine ⟨(x, offset), ⟨Metric.ball_subset_closedBall hx, ?_⟩, ?_⟩
        · simpa [dist_eq_norm] using hoff
        · apply complexToRealCoordinateEquiv.injective
          change complexToRealCoordinateEquiv (x + offset) =
            complexToRealCoordinateEquiv (sample w)
          dsimp [offset]
          rw [map_add]
          dsimp [sample]
          simp only [map_sub, complexToRealCoordinateEquiv.apply_symm_apply]
          abel
      · dsimp [sample]
        simp
    have hKr' : complexToRealCoordinateEquiv x - w ∈
        complexToRealCoordinateEquiv ''
          ((Metric.closedBall c S ×ˢ Metric.closedBall 0 (η / 2)).image
            (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) => p.1 + p.2)) := hKr
    have hsample_eq : sample w = x - complexToRealCoordinateEquiv.symm w := by
      dsimp [sample]
      rw [map_sub, complexToRealCoordinateEquiv.symm_apply_apply]
    have hsampleU : x - complexToRealCoordinateEquiv.symm w ∈ U := by
      rw [← hsample_eq]
      exact hU
    rw [Set.indicator_of_mem hKr']
    simp [hsampleU]

open Classical in
/-- Compact-indicator derivative and integrable CLM data combine with the collar lemma to give
an actual U-cutoff directional derivative formula. -/
public theorem compactBridge_actual_cutoff_of_compact {n : ℕ}
    (U : Set (EuclideanSpace ℂ (Fin n))) {c : EuclideanSpace ℂ (Fin n)} {S η : ℝ}
    (hη : 0 < η) (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (m : ℕ) (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (x : EuclideanSpace ℂ (Fin n)) (hx : x ∈ Metric.ball c S)
    (v : EuclideanSpace ℝ (Fin n × Fin 2))
    (hD : HasFDerivAt
      (fun y => localFixedMollify U hη m f (complexToRealCoordinateEquiv.symm y))
      ((fderiv ℝ (localFixedKernel hη m) ⋆[
        (ContinuousLinearMap.lsmul ℝ ℝ).precompL
          (EuclideanSpace ℝ (Fin n × Fin 2)),
        (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))]
        (let K : Set (EuclideanSpace ℂ (Fin n)) :=
          (Metric.closedBall c S ×ˢ Metric.closedBall 0 (η / 2)).image
            (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) => p.1 + p.2)
         let Kr : Set (EuclideanSpace ℝ (Fin n × Fin 2)) := complexToRealCoordinateEquiv '' K
         Kr.indicator (fun y => f (complexToRealCoordinateEquiv.symm y))))
        (complexToRealCoordinateEquiv x)) (complexToRealCoordinateEquiv x))
    (hCLM : Integrable
      (fun w : EuclideanSpace ℝ (Fin n × Fin 2) =>
        ((ContinuousLinearMap.lsmul ℝ ℝ).precompL
          (EuclideanSpace ℝ (Fin n × Fin 2)))
          (fderiv ℝ (localFixedKernel hη m) w)
          ((let K : Set (EuclideanSpace ℂ (Fin n)) :=
            (Metric.closedBall c S ×ˢ Metric.closedBall 0 (η / 2)).image
              (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) => p.1 + p.2)
           let Kr : Set (EuclideanSpace ℝ (Fin n × Fin 2)) := complexToRealCoordinateEquiv '' K
           Kr.indicator (fun y => f (complexToRealCoordinateEquiv.symm y)))
            (complexToRealCoordinateEquiv x - w)))
      (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))) :
    (fderiv ℝ (fun y => localFixedMollify U hη m f
      (complexToRealCoordinateEquiv.symm y))
      (complexToRealCoordinateEquiv x)) v =
      ∫ w : EuclideanSpace ℝ (Fin n × Fin 2),
        (fderiv ℝ (localFixedKernel hη m) w v : ℂ) *
          (if complexToRealCoordinateEquiv.symm
              (complexToRealCoordinateEquiv x - w) ∈ U then
            f (complexToRealCoordinateEquiv.symm
              (complexToRealCoordinateEquiv x - w)) else 0) := by
  let K : Set (EuclideanSpace ℂ (Fin n)) :=
    (Metric.closedBall c S ×ˢ Metric.closedBall 0 (η / 2)).image
      (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) => p.1 + p.2)
  let Kr : Set (EuclideanSpace ℝ (Fin n × Fin 2)) := complexToRealCoordinateEquiv '' K
  let H : EuclideanSpace ℝ (Fin n × Fin 2) → ℂ :=
    Kr.indicator (fun y => f (complexToRealCoordinateEquiv.symm y))
  have hScalar : ∀ u : EuclideanSpace ℝ (Fin n × Fin 2),
      (∫ w : EuclideanSpace ℝ (Fin n × Fin 2),
        (fderiv ℝ (localFixedKernel hη m) w u : ℂ) * H (complexToRealCoordinateEquiv x - w)) =
      ∫ w : EuclideanSpace ℝ (Fin n × Fin 2),
        (fderiv ℝ (localFixedKernel hη m) w u : ℂ) *
          (if complexToRealCoordinateEquiv.symm
              (complexToRealCoordinateEquiv x - w) ∈ U then
            f (complexToRealCoordinateEquiv.symm
              (complexToRealCoordinateEquiv x - w)) else 0) := by
    intro u
    simpa [H, Kr, K] using
      compactBridge_scalar_cutoff_eq U hη hCollar f m x hx u
  exact compactBridge_apply_of_derivative_and_cutoff U hη m f x v H hD hCLM hScalar

end CalabiYau.Schauder
