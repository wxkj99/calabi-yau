module

public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.LocalApproximation.Basic

@[expose] public section

open Set Filter MeasureTheory Classical
open scoped ContDiff NNReal Topology Convolution

namespace CalabiYau.Schauder

/-- Basic-only core certificate for differentiating a local fixed-kernel convolution against
locally integrable data. -/
public theorem compactCore_kernel_convolution_hasFDerivAt {n : ℕ}
    {η : ℝ} (hη : 0 < η) (m : ℕ) {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (H : EuclideanSpace ℝ (Fin n × Fin 2) → F)
    (hH : LocallyIntegrable H (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))))
    (x : EuclideanSpace ℝ (Fin n × Fin 2)) :
    HasFDerivAt
      (fun z => ∫ w : EuclideanSpace ℝ (Fin n × Fin 2),
        localFixedKernel hη m w • H (z - w))
      ((fderiv ℝ (localFixedKernel hη m) ⋆[
        (ContinuousLinearMap.lsmul ℝ ℝ).precompL
          (EuclideanSpace ℝ (Fin n × Fin 2)),
        (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))] H) x) x := by
  let κ : EuclideanSpace ℝ (Fin n × Fin 2) → ℝ := localFixedKernel hη m
  let L : ℝ →L[ℝ] F →L[ℝ] F := ContinuousLinearMap.lsmul ℝ ℝ
  have hκ : ContDiff ℝ 1 κ := by
    dsimp [κ, localFixedKernel]
    exact (localKernelBump hη m).contDiff_normed
  have hcompact : HasCompactSupport κ := by
    dsimp [κ, localFixedKernel]
    exact (localKernelBump hη m).hasCompactSupport_normed
  have hderiv := hcompact.hasFDerivAt_convolution_left L hκ hH x
  have hconv :
      (fun z => ∫ w : EuclideanSpace ℝ (Fin n × Fin 2), κ w • H (z - w)) =
        κ ⋆[L, (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))] H := by
    funext z
    rw [← MeasureTheory.convolution_flip]
    rw [MeasureTheory.convolution_eq_swap]
    simp [L]
  rw [hconv]
  simpa [κ, L, ContinuousLinearMap.lsmul_apply] using hderiv

end CalabiYau.Schauder
