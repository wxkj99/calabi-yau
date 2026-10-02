module

public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.LocalApproximation.Basic
import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.LocalApproximation.CovarianceScaleBounds.Centering
public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.LocalApproximation.CovarianceScaleBounds.KernelDerivativeBounds
import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.LocalApproximation.CovarianceScaleBounds.HolderMollification
import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.LocalApproximation.CovarianceScaleBounds.CompactIntegrability
import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.LocalApproximation.CovarianceScaleBounds.RealCovarianceDerivative

open MeasureTheory
open scoped NNReal

namespace CalabiYau.Schauder

private theorem covarianceActualSlope_factorFour
    {Ω : Type*} [MeasureSpace Ω] {μ : Measure Ω}
    {w A H : Ω → ℂ} {a h : ℂ}
    {K J M r V : ℝ} {α : ℝ}
    (hw : Integrable w μ)
    (hwA : Integrable (fun x => w x * A x) μ)
    (hwH : Integrable (fun x => w x * H x) μ)
    (hwAH : Integrable (fun x => w x * A x * H x) μ)
    (hwmass : ∫ x, w x ∂μ = 0)
    (hK : 0 ≤ K) (_hJ : 0 ≤ J) (hM : 0 ≤ M) (hr : 0 < r)
    (hA : ∀ᵐ x ∂μ, w x ≠ 0 → ‖A x - a‖ ≤ 2 * K * r ^ α)
    (hH : ∀ᵐ x ∂μ, w x ≠ 0 → ‖H x - h‖ ≤ 2 * M)
    (hL1 : ∫ x, ‖w x‖ ∂μ ≤ J * r⁻¹ * V) :
    ‖h * (∫ x, w x * A x ∂μ) + a * (∫ x, w x * H x ∂μ) -
        ∫ x, w x * A x * H x ∂μ‖ ≤ 4 * K * J * M * r ^ (α - 1) * V := by
  have hcentered :
      (∫ x, w x * A x * H x ∂μ) - h * (∫ x, w x * A x ∂μ) -
          a * (∫ x, w x * H x ∂μ) =
        ∫ x, w x * (A x - a) * (H x - h) ∂μ :=
    covarianceCentering hw hwA hwH hwAH hwmass
  have hcross :
      h * (∫ x, w x * A x ∂μ) + a * (∫ x, w x * H x ∂μ) -
          ∫ x, w x * A x * H x ∂μ =
        -(∫ x, w x * (A x - a) * (H x - h) ∂μ) := by
    rw [← hcentered]
    ring
  have hcenterInt := covarianceCentered_integrable a h hw hwA hwH hwAH
  have hbound := covarianceCentered_norm hw hcenterInt
    (by positivity : 0 ≤ 2 * K * r ^ α) (by positivity : 0 ≤ 2 * M) hA hH
  have hquot : r ^ α * r⁻¹ = r ^ (α - 1) := by
    calc
      r ^ α * r⁻¹ = r ^ α / r := by rw [div_eq_mul_inv]
      _ = r ^ (α - 1) := (Real.rpow_sub_one hr.ne' α).symm
  calc
    _ = ‖∫ x, w x * (A x - a) * (H x - h) ∂μ‖ := by rw [hcross, norm_neg]
    _ ≤ (2 * K * r ^ α) * (2 * M) * ∫ x, ‖w x‖ ∂μ := hbound
    _ ≤ (2 * K * r ^ α) * (2 * M) * (J * r⁻¹ * V) := by
      apply mul_le_mul_of_nonneg_left hL1
      positivity
    _ = 4 * K * J * M * r ^ (α - 1) * V := by
      rw [← hquot]
      ring

public theorem incrementCancellation_real_directional_bound {n : ℕ}
    {U : Set (EuclideanSpace ℂ (Fin n))} {c : EuclideanSpace ℂ (Fin n)}
    {S η M : ℝ} {α K : ℝ≥0} {f g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hη : 0 < η)
    (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (hHolder : HolderBoundOn 0 α K U f) (hM : 0 ≤ M)
    (m : ℕ) (x : EuclideanSpace ℂ (Fin n)) (hx : x ∈ Metric.ball c S)
    (hIncrement : ∀ h : EuclideanSpace ℂ (Fin n),
      ‖h‖ ≤ 2 * localKernelRadius η m → ‖g (x + h) - g x‖ ≤ M) :
    ∀ v : EuclideanSpace ℂ (Fin n),
      ‖fderiv ℝ (fun z => (localMollificationCovariance U hη m f g z).re) x v‖ ≤
        (4 * (K : ℝ) * covarianceA2_J n * M /
          localKernelRadius η m ^ (1 - (α : ℝ))) * ‖v‖ := by
  classical
  intro u
  let E := EuclideanSpace ℝ (Fin n × Fin 2)
  let sample : E → EuclideanSpace ℂ (Fin n) := fun w =>
    complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w)
  let A : E → ℂ := fun w => if sample w ∈ U then f (sample w) else 0
  let H : E → ℂ := fun w => if sample w ∈ U then g (sample w) else 0
  let q : E → ℂ := fun w =>
    (fderiv ℝ (localFixedKernel hη m) w (complexToRealCoordinateEquiv u) : ℂ)
  have hDeriv := realCovarianceDerivative_actual U hη hCollar f g hf hg m x hx
  rcases hDeriv with ⟨df, dg, dfg, hD, hEval, _⟩
  have hEvalU := hEval u
  have hDerivBound :
      ‖(Complex.reCLM.comp
        (localFixedMollify U hη m f x • dg +
          localFixedMollify U hη m g x • df - dfg)) u‖ ≤
        4 * (K : ℝ) * covarianceA2_J n * M /
          localKernelRadius η m ^ (1 - (α : ℝ)) * ‖u‖ := by
    have hq : Integrable q (volume : Measure E) := by
      simpa [q] using integrable_complex_fderiv_localFixedKernel_apply hη m
        (complexToRealCoordinateEquiv u)
    have hqA0 := compactIntegrability_actual_cutoff_CLM hη hCollar f hf m x hx
    have hqH0 := compactIntegrability_actual_cutoff_CLM hη hCollar g hg m x hx
    have hqAH0 := compactIntegrability_actual_cutoff_CLM hη hCollar
      (fun y => f y * g y) (hf.mul hg) m x hx
    have hqA0' := hqA0.apply_continuousLinearMap (complexToRealCoordinateEquiv u)
    have hqH0' := hqH0.apply_continuousLinearMap (complexToRealCoordinateEquiv u)
    have hqAH0' := hqAH0.apply_continuousLinearMap (complexToRealCoordinateEquiv u)
    have hqA : Integrable (fun w : E => q w * A w) (volume : Measure E) := by
      simpa [q, A, sample, mul_comm] using hqA0'
    have hqH : Integrable (fun w : E => q w * H w) (volume : Measure E) := by
      simpa [q, H, sample, mul_comm] using hqH0'
    have hqAHbase : Integrable (fun w : E => q w *
        (if sample w ∈ U then f (sample w) * g (sample w) else 0))
        (volume : Measure E) := by
      simpa [q, sample, mul_comm] using hqAH0'
    have hqAH : Integrable (fun w : E => q w * A w * H w)
        (volume : Measure E) := by
      apply hqAHbase.congr
      filter_upwards [] with w
      by_cases hw : sample w ∈ U <;> simp [A, H, hw, mul_assoc]
    have hqmass : (∫ w : E, q w ∂(volume : Measure E)) = 0 := by
      simpa [q] using integral_complex_fderiv_localFixedKernel_apply_eq_zero hη m
        (complexToRealCoordinateEquiv u)
    have hKernel := covarianceA2_complexDirectionDerivativeL1_le hη m u
    have hL1raw : (∫ w : E, ‖q w‖ ∂(volume : Measure E)) ≤
        (localKernelRadius η m)⁻¹ * covarianceA2_J n * ‖u‖ := by
      simpa [q, E] using hKernel
    have hL1 : (∫ w : E, ‖q w‖ ∂(volume : Measure E)) ≤
        covarianceA2_J n * (localKernelRadius η m)⁻¹ * ‖u‖ := by
      calc
        _ ≤ ((localKernelRadius η m)⁻¹ * covarianceA2_J n) * ‖u‖ := hL1raw
        _ = _ := by ring
    let meanA := localFixedMollify U hη m f x
    let meanH := localFixedMollify U hη m g x
    let δ := (K : ℝ) * localKernelRadius η m ^ (α : ℝ)
    have hδ : 0 ≤ δ := by
      dsimp [δ]
      exact mul_nonneg (NNReal.coe_nonneg K)
        (Real.rpow_nonneg (localKernelRadius_pos hη m).le _)
    have hmeanA : ‖meanA - f x‖ ≤ δ := by
      simpa [meanA, δ] using
        holderLeaf_localFixedMollify_mean_deviation_of_holder hη hCollar hf hHolder m x hx
    have hmeanH : ‖meanH - g x‖ ≤ M :=
      holderLeaf_localFixedMollify_mean_deviation_of_center_increment
        hη hCollar hg hM m x hx (by
          intro h hh
          exact hIncrement h (hh.trans (by
            have hr := localKernelRadius_pos hη m
            linarith)))
    have hAosc : ∀ᵐ w : E ∂(volume : Measure E),
        q w ≠ 0 → ‖A w - meanA‖ ≤ 2 * δ := by
      filter_upwards [] with w
      intro hw
      have hqr : fderiv ℝ (localFixedKernel hη m) w
          (complexToRealCoordinateEquiv u) ≠ 0 := by
        intro hz
        apply hw
        simp [q, hz]
      have hpoint := holderLeaf_deriv_kernel_holder_deviation hη hCollar hHolder m x hx
        (complexToRealCoordinateEquiv u) w hqr
      have hpoint' : ‖A w - f x‖ ≤ δ := by
        simpa [A, sample, δ] using hpoint
      have htri : ‖A w - meanA‖ ≤ ‖A w - f x‖ + ‖f x - meanA‖ := by
        calc
          ‖A w - meanA‖ = ‖(A w - f x) + (f x - meanA)‖ := by congr 1 ; abel
          _ ≤ ‖A w - f x‖ + ‖f x - meanA‖ := norm_add_le _ _
      have hrev : ‖f x - meanA‖ = ‖meanA - f x‖ := norm_sub_rev (f x) meanA
      rw [hrev] at htri
      calc
        ‖A w - meanA‖ ≤ ‖A w - f x‖ + ‖meanA - f x‖ := htri
        _ ≤ δ + δ := add_le_add hpoint' hmeanA
        _ = 2 * δ := by ring
    have hHosc : ∀ᵐ w : E ∂(volume : Measure E),
        q w ≠ 0 → ‖H w - meanH‖ ≤ 2 * M := by
      filter_upwards [] with w
      intro hw
      have hqr : fderiv ℝ (localFixedKernel hη m) w
          (complexToRealCoordinateEquiv u) ≠ 0 := by
        intro hz
        apply hw
        simp [q, hz]
      have hsample := holderLeaf_deriv_kernel_sample_deviation hη hCollar m x hx
        (complexToRealCoordinateEquiv u) (by
          intro h hh
          exact hIncrement h (hh.trans (by
            have hr := localKernelRadius_pos hη m
            linarith))) w hqr
      have hsample' : ‖H w - g x‖ ≤ M := by
        simpa [H, sample] using hsample
      have htriangle : ‖H w - meanH‖ =
          ‖(H w - g x) + (g x - meanH)‖ := by congr 1 ; abel
      rw [htriangle]
      calc
        ‖(H w - g x) + (g x - meanH)‖ ≤
            ‖H w - g x‖ + ‖g x - meanH‖ := norm_add_le _ _
        _ = ‖H w - g x‖ + ‖meanH - g x‖ := by
          congr 1
          exact norm_sub_rev (g x) meanH
        _ ≤ M + M := add_le_add hsample' hmeanH
        _ = 2 * M := by ring
    have hAosc' : ∀ᵐ w : E ∂(volume : Measure E),
        q w ≠ 0 → ‖A w - meanA‖ ≤ 2 * (K : ℝ) *
          (localKernelRadius η m) ^ (α : ℝ) := by
      filter_upwards [hAosc] with w hw
      intro hwq
      calc
        ‖A w - meanA‖ ≤ 2 * δ := hw hwq
        _ = 2 * (K : ℝ) * (localKernelRadius η m) ^ (α : ℝ) := by
          dsimp [δ]
          ring
    have hfactor := covarianceActualSlope_factorFour hq hqA hqH hqAH hqmass
      (by positivity : 0 ≤ (K : ℝ)) (covarianceA2_J_nonneg n) hM
      (localKernelRadius_pos hη m) hAosc' hHosc hL1
    have hfactor' :
        ‖meanH * (∫ w : E, q w * A w ∂(volume : Measure E)) +
          meanA * (∫ w : E, q w * H w ∂(volume : Measure E)) -
          ∫ w : E, q w * A w * H w ∂(volume : Measure E)‖ ≤
        4 * (K : ℝ) * covarianceA2_J n * M *
          (localKernelRadius η m) ^ ((α : ℝ) - 1) * ‖u‖ := by
      simpa only [meanA, meanH] using hfactor
    have hPower : (localKernelRadius η m) ^ ((α : ℝ) - 1) =
        1 / (localKernelRadius η m) ^ (1 - (α : ℝ)) := by
      rw [show (α : ℝ) - 1 = -(1 - (α : ℝ)) by ring,
        Real.rpow_neg (le_of_lt (localKernelRadius_pos hη m))]
      simp [one_div]
    have hcross :
        ‖localFixedMollify U hη m f x * (∫ w : E, q w * H w ∂(volume : Measure E)) +
          localFixedMollify U hη m g x * (∫ w : E, q w * A w ∂(volume : Measure E)) -
          ∫ w : E, q w * A w * H w ∂(volume : Measure E)‖ ≤
        4 * (K : ℝ) * covarianceA2_J n * M /
          localKernelRadius η m ^ (1 - (α : ℝ)) * ‖u‖ := by
      calc
        _ = ‖meanH * (∫ w : E, q w * A w ∂(volume : Measure E)) +
            meanA * (∫ w : E, q w * H w ∂(volume : Measure E)) -
            ∫ w : E, q w * A w * H w ∂(volume : Measure E)‖ := by
          simp only [meanA, meanH]
          congr 1 ; ring
        _ ≤ 4 * (K : ℝ) * covarianceA2_J n * M *
            (localKernelRadius η m) ^ ((α : ℝ) - 1) * ‖u‖ := hfactor'
        _ = 4 * (K : ℝ) * covarianceA2_J n * M /
            (localKernelRadius η m) ^ (1 - (α : ℝ)) * ‖u‖ := by
          rw [hPower]
          ring
    rw [hEvalU]
    have hRe :
        ‖(localFixedMollify U hη m f x * (∫ w : E, q w * H w ∂(volume : Measure E)) +
          localFixedMollify U hη m g x * (∫ w : E, q w * A w ∂(volume : Measure E)) -
          ∫ w : E, q w * A w * H w ∂(volume : Measure E)).re‖ ≤
        ‖localFixedMollify U hη m f x * (∫ w : E, q w * H w ∂(volume : Measure E)) +
          localFixedMollify U hη m g x * (∫ w : E, q w * A w ∂(volume : Measure E)) -
          ∫ w : E, q w * A w * H w ∂(volume : Measure E)‖ := by
      simpa using Complex.abs_re_le_norm
        (localFixedMollify U hη m f x * (∫ w : E, q w * H w ∂(volume : Measure E)) +
          localFixedMollify U hη m g x * (∫ w : E, q w * A w ∂(volume : Measure E)) -
          ∫ w : E, q w * A w * H w ∂(volume : Measure E))
    exact hRe.trans hcross
  rw [hD.fderiv]
  exact hDerivBound

end CalabiYau.Schauder
