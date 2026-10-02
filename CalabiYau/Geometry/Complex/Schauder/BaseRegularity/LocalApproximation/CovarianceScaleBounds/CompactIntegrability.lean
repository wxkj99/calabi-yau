module

public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.LocalApproximation.Basic

@[expose] public section

open Set Filter MeasureTheory Classical
open scoped ContDiff NNReal Topology Convolution

namespace CalabiYau.Schauder

/-- Actual cutoff CLM integrability from the collar hypothesis. This is the actual-cutoff
counterpart used to prove compact-indicator CLM integrability. -/
public theorem compactIntegrability_actual_cutoff_CLM {n : ℕ}
    {U : Set (EuclideanSpace ℂ (Fin n))} {c : EuclideanSpace ℂ (Fin n)} {S η : ℝ}
    (hη : 0 < η) (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (f : EuclideanSpace ℂ (Fin n) → ℂ) (hf : ContinuousOn f U) (m : ℕ)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ Metric.ball c S) :
    Integrable
      (fun w : EuclideanSpace ℝ (Fin n × Fin 2) =>
        ((ContinuousLinearMap.lsmul ℝ ℝ).precompL
          (EuclideanSpace ℝ (Fin n × Fin 2)))
          (fderiv ℝ (localFixedKernel hη m) w)
          (if complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w) ∈ U then
            f (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w)) else 0))
      (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) := by
  let E := EuclideanSpace ℝ (Fin n × Fin 2)
  let K : Set E := Metric.closedBall 0 (localKernelRadius η m)
  let sample : E → EuclideanSpace ℂ (Fin n) :=
    fun w => complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w)
  let κ : E → ℝ := localFixedKernel hη m
  let L : (E →L[ℝ] ℝ) →L[ℝ] ℂ →L[ℝ] (E →L[ℝ] ℂ) :=
    (ContinuousLinearMap.lsmul ℝ ℝ).precompL E
  let T : E → E →L[ℝ] ℂ := fun w =>
    L (fderiv ℝ κ w) (if sample w ∈ U then f (sample w) else 0)
  have hK : IsCompact K := by
    simpa [K] using isCompact_closedBall (0 : E) (localKernelRadius η m)
  have hκ : ContDiff ℝ 1 κ := by
    dsimp [κ, localFixedKernel]
    exact (localKernelBump hη m).contDiff_normed
  have hD : Continuous (fun w : E => fderiv ℝ κ w) :=
    hκ.continuous_fderiv (by simp)
  have hsample : ContinuousOn sample K := by
    apply Continuous.continuousOn
    dsimp [sample]
    fun_prop
  have hIn : ∀ w ∈ K, sample w ∈ U := by
    intro w hw
    have hw_norm : ‖w‖ ≤ localKernelRadius η m := by simpa [K, dist_eq_norm] using hw
    have hr : localKernelRadius η m < η := by
      unfold localKernelRadius
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * ((m : ℝ) + 1))]
      nlinarith [hη]
    have hzs : z = complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z) :=
      (complexToRealCoordinateEquiv.symm_apply_apply z).symm
    have hdist : dist (sample w) z = ‖w‖ := by
      calc
        dist (sample w) z =
            dist (sample w) (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z)) :=
          congrArg (fun q => dist (sample w) q) hzs
        _ = dist (complexToRealCoordinateEquiv z - w) (complexToRealCoordinateEquiv z) := by
          dsimp [sample]
          exact complexToRealCoordinateEquiv.symm.isometry.dist_eq _ _
        _ = ‖w‖ := by
          rw [dist_eq_norm]
          have hsub : (complexToRealCoordinateEquiv z - w) - complexToRealCoordinateEquiv z = -w := by abel
          rw [hsub, norm_neg]
    have hthick : sample w ∈ Metric.thickening η (Metric.closedBall c S) := by
      rw [Metric.mem_thickening_iff]
      refine ⟨z, Metric.ball_subset_closedBall hz, ?_⟩
      calc
        dist (sample w) z = ‖w‖ := hdist
        _ ≤ localKernelRadius η m := hw_norm
        _ < η := hr
    exact hCollar hthick
  have hcut : ContinuousOn (fun w => if sample w ∈ U then f (sample w) else 0) K := by
    have hComp : ContinuousOn (fun w => f (sample w)) K := hf.comp hsample hIn
    apply hComp.congr
    intro w hw
    simp [hIn w hw]
  have hT : ContinuousOn T K := by
    dsimp [T]
    fun_prop
  have hzero : ∀ w, w ∉ K → T w = 0 := by
    intro w hw
    have hDzero : fderiv ℝ κ w = 0 := by
      by_contra hne
      have hts : w ∈ tsupport (fderiv ℝ κ) :=
        subset_closure (Function.mem_support.mpr hne)
      have htsk : w ∈ tsupport κ := (tsupport_fderiv_subset ℝ) hts
      change w ∈ tsupport ((localKernelBump hη m).normed (volume : Measure E)) at htsk
      rw [(localKernelBump hη m).tsupport_normed_eq] at htsk
      have hw_norm : ‖w‖ ≤ localKernelRadius η m := by
        simpa [localKernelBump, localKernelRadius] using htsk
      exact hw (by simpa [K, dist_eq_norm] using hw_norm)
    simp [T, hDzero]
  have hOn : IntegrableOn T K (volume : Measure E) := hT.integrableOn_compact hK
  have hInt : Integrable T (volume : Measure E) :=
    hOn.integrable_of_forall_notMem_eq_zero hzero
  simpa [T, L, κ, sample, E] using hInt

/-- Scalar compact-indicator integrability for continuous data on the collar. This is the
shared closure used by LocalAgreement and Composition. -/
public theorem compactIntegrability_compact_indicator_scalar {n : ℕ}
    (U : Set (EuclideanSpace ℂ (Fin n))) {c : EuclideanSpace ℂ (Fin n)} {S η : ℝ}
    (hη : 0 < η) (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (f : EuclideanSpace ℂ (Fin n) → ℂ) (hf : ContinuousOn f U) :
    let K : Set (EuclideanSpace ℂ (Fin n)) :=
      (Metric.closedBall c S ×ˢ Metric.closedBall 0 (η / 2)).image
        (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) => p.1 + p.2)
    let Kr : Set (EuclideanSpace ℝ (Fin n × Fin 2)) := complexToRealCoordinateEquiv '' K
    Integrable (Kr.indicator (fun y => f (complexToRealCoordinateEquiv.symm y)))
      (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) := by
  dsimp
  let K : Set (EuclideanSpace ℂ (Fin n)) :=
    (Metric.closedBall c S ×ˢ Metric.closedBall 0 (η / 2)).image
      (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) => p.1 + p.2)
  have hKcompact : IsCompact K := by
    apply (isCompact_closedBall c S).prod (isCompact_closedBall (0 : EuclideanSpace ℂ (Fin n)) (η / 2)) |>.image
    fun_prop
  have hKU : K ⊆ U := by
    rintro y ⟨⟨z, v⟩, ⟨hz, hv⟩, rfl⟩
    apply hCollar
    rw [Metric.mem_thickening_iff]
    refine ⟨z, hz, ?_⟩
    calc
      dist (z + v) z = dist v 0 := by rw [dist_eq_norm, dist_eq_norm]; simp
      _ ≤ η / 2 := hv
      _ < η := by linarith
  let Kr : Set (EuclideanSpace ℝ (Fin n × Fin 2)) := complexToRealCoordinateEquiv '' K
  have hKr : IsCompact Kr := hKcompact.image complexToRealCoordinateEquiv.continuous
  have hmaps : ∀ y ∈ Kr, complexToRealCoordinateEquiv.symm y ∈ U := by
    rintro y ⟨z, hz, rfl⟩
    simpa using hKU hz
  have hcont : ContinuousOn (fun y => f (complexToRealCoordinateEquiv.symm y)) Kr :=
    hf.comp complexToRealCoordinateEquiv.symm.continuous.continuousOn hmaps
  have hOn : IntegrableOn
      (fun y => f (complexToRealCoordinateEquiv.symm y)) Kr
      (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) :=
    hcont.integrableOn_compact hKr
  exact hOn.integrable_indicator hKr.measurableSet

/-- Full collar/support congruence: actual-cutoff CLM integrability transfers to the
compact-indicator CLM integrand required by `integral_apply`. -/
public theorem compactIntegrability_compact_indicator_CLM {n : ℕ}
    (U : Set (EuclideanSpace ℂ (Fin n))) {c : EuclideanSpace ℂ (Fin n)} {S η : ℝ}
    (hη : 0 < η) (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (f : EuclideanSpace ℂ (Fin n) → ℂ) (hf : ContinuousOn f U) (m : ℕ)
    (x : EuclideanSpace ℂ (Fin n)) (hx : x ∈ Metric.ball c S) :
    let E := EuclideanSpace ℝ (Fin n × Fin 2)
    let K : Set (EuclideanSpace ℂ (Fin n)) :=
      (Metric.closedBall c S ×ˢ Metric.closedBall 0 (η / 2)).image
        (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) => p.1 + p.2)
    let Kr : Set E := complexToRealCoordinateEquiv '' K
    Integrable
      (fun w : E => ((ContinuousLinearMap.lsmul ℝ ℝ).precompL E)
        (fderiv ℝ (localFixedKernel hη m) w)
        (Kr.indicator (fun y => f (complexToRealCoordinateEquiv.symm y))
          (complexToRealCoordinateEquiv x - w)))
      (volume : Measure E) := by
  dsimp
  let E := EuclideanSpace ℝ (Fin n × Fin 2)
  let K : Set (EuclideanSpace ℂ (Fin n)) :=
    (Metric.closedBall c S ×ˢ Metric.closedBall 0 (η / 2)).image
      (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) => p.1 + p.2)
  let Kr : Set E := complexToRealCoordinateEquiv '' K
  let H : E → ℂ := Kr.indicator (fun y => f (complexToRealCoordinateEquiv.symm y))
  let L : (E →L[ℝ] ℝ) →L[ℝ] ℂ →L[ℝ] (E →L[ℝ] ℂ) :=
    (ContinuousLinearMap.lsmul ℝ ℝ).precompL E
  let sample : E → EuclideanSpace ℂ (Fin n) :=
    fun w => complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w)
  have hAct := compactIntegrability_actual_cutoff_CLM hη hCollar f hf m x hx
  apply hAct.congr
  filter_upwards [] with w
  by_cases hD : fderiv ℝ (localFixedKernel hη m) w = 0
  · simp [hD]
  · have hts : w ∈ tsupport (fderiv ℝ (localFixedKernel hη m)) :=
      subset_closure (Function.mem_support.mpr hD)
    have htsκ : w ∈ tsupport (localFixedKernel hη m) :=
      (tsupport_fderiv_subset ℝ) hts
    change w ∈ tsupport ((localKernelBump hη m).normed (volume : Measure E)) at htsκ
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
    have hdist : dist (sample w) x = ‖w‖ := by
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
        dist (sample w) x = ‖w‖ := hdist
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
            _ = ‖w‖ := hdist
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
    have hsampleEq : sample w = x - complexToRealCoordinateEquiv.symm w := by
      dsimp [sample]
      rw [map_sub, complexToRealCoordinateEquiv.symm_apply_apply]
    have hEqU : complexToRealCoordinateEquiv.symm
        (complexToRealCoordinateEquiv x - w) = sample w := by rfl
    have hEqH : H (complexToRealCoordinateEquiv x - w) = f (sample w) := by
      change Kr.indicator (fun y => f (complexToRealCoordinateEquiv.symm y))
        (complexToRealCoordinateEquiv x - w) = f (sample w)
      rw [Set.indicator_of_mem hKr, hEqU]
    have hActualU : x - complexToRealCoordinateEquiv.symm w ∈ U := by
      rw [← hsampleEq]
      exact hU
    ext q
    rw [Set.indicator_of_mem hKr]
    rw [hEqU]
    simp [hU, Complex.real_smul]

end CalabiYau.Schauder
