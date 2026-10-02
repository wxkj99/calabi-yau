module

public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.LocalApproximation.Basic
public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.LocalApproximation.CovarianceScaleBounds.Composition

open MeasureTheory
open scoped ContDiff Convolution

namespace CalabiYau.Schauder

open Classical

/-- Real covariance derivative and its crossed three-integral evaluation, using the
compact-truncation factor bundle from `Composition`. -/
public theorem realCovarianceDerivative_actual {n : ℕ}
    (U : Set (EuclideanSpace ℂ (Fin n))) {c : EuclideanSpace ℂ (Fin n)} {S η : ℝ}
    (hη : 0 < η) (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (f g : EuclideanSpace ℂ (Fin n) → ℂ)
    (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (m : ℕ) (x : EuclideanSpace ℂ (Fin n)) (hx : x ∈ Metric.ball c S) :
    ∃ df dg dfg : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ,
      HasFDerivAt
        (fun z => (localMollificationCovariance U hη m f g z).re)
        (Complex.reCLM.comp
          ((localFixedMollify U hη m f x) • dg +
            (localFixedMollify U hη m g x) • df - dfg)) x ∧
      (∀ v : EuclideanSpace ℂ (Fin n),
        (Complex.reCLM.comp
          ((localFixedMollify U hη m f x) • dg +
            (localFixedMollify U hη m g x) • df - dfg)) v =
        ((localFixedMollify U hη m f x) *
            (∫ w : EuclideanSpace ℝ (Fin n × Fin 2),
              (fderiv ℝ (localFixedKernel hη m) w (complexToRealCoordinateEquiv v) : ℂ) *
                (if complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w) ∈ U then
                  g (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w)) else 0)) +
          (localFixedMollify U hη m g x) *
            (∫ w : EuclideanSpace ℝ (Fin n × Fin 2),
              (fderiv ℝ (localFixedKernel hη m) w (complexToRealCoordinateEquiv v) : ℂ) *
                (if complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w) ∈ U then
                  f (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w)) else 0)) -
          ∫ w : EuclideanSpace ℝ (Fin n × Fin 2),
            (fderiv ℝ (localFixedKernel hη m) w (complexToRealCoordinateEquiv v) : ℂ) *
              (if complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w) ∈ U then
                f (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w)) else 0) *
              (if complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w) ∈ U then
                g (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w)) else 0)).re) ∧
      ∀ v : EuclideanSpace ℂ (Fin n),
        ((localFixedMollify U hη m f x) • dg +
          (localFixedMollify U hη m g x) • df - dfg) v =
          (localFixedMollify U hη m f x) *
            (∫ w : EuclideanSpace ℝ (Fin n × Fin 2),
              (fderiv ℝ (localFixedKernel hη m) w (complexToRealCoordinateEquiv v) : ℂ) *
                (if complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w) ∈ U then
                  g (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w)) else 0)) +
          (localFixedMollify U hη m g x) *
            (∫ w : EuclideanSpace ℝ (Fin n × Fin 2),
              (fderiv ℝ (localFixedKernel hη m) w (complexToRealCoordinateEquiv v) : ℂ) *
                (if complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w) ∈ U then
                  f (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w)) else 0)) -
          ∫ w : EuclideanSpace ℝ (Fin n × Fin 2),
            (fderiv ℝ (localFixedKernel hη m) w (complexToRealCoordinateEquiv v) : ℂ) *
              (if complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w) ∈ U then
                f (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w)) else 0) *
              (if complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w) ∈ U then
                g (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w)) else 0) := by
  have hData := compactComposition_actual_factor_derivative_data
    U hη hCollar f g hf hg m x hx
  rcases hData with ⟨⟨df, hfD, hdf⟩, ⟨dg, hgD, hdg⟩, ⟨dfg, hfgD, hdfg⟩⟩
  have hprod := (hfD.mul hgD).sub hfgD
  change HasFDerivAt
    (fun z => localFixedMollify U hη m f z * localFixedMollify U hη m g z -
      localFixedMollify U hη m (fun y => f y * g y) z)
    ((localFixedMollify U hη m f x) • dg +
      (localFixedMollify U hη m g x) • df - dfg) x at hprod
  have hcov := Complex.reCLM.hasFDerivAt.comp x hprod
  have hcov' : HasFDerivAt
      (fun z => (localMollificationCovariance U hη m f g z).re)
      (Complex.reCLM.comp
        ((localFixedMollify U hη m f x) • dg +
          (localFixedMollify U hη m g x) • df - dfg)) x := by
    simpa [localMollificationCovariance, Function.comp_def, Complex.reCLM] using hcov
  refine ⟨df, dg, dfg, hcov', ?_, ?_⟩
  intro v
  have hsample (w : EuclideanSpace ℝ (Fin n × Fin 2)) :
      complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w) =
        x - complexToRealCoordinateEquiv.symm w := by
    rw [map_sub, complexToRealCoordinateEquiv.symm_apply_apply]
  have hcut :
      (∫ w : EuclideanSpace ℝ (Fin n × Fin 2),
        (fderiv ℝ (localFixedKernel hη m) w (complexToRealCoordinateEquiv v) : ℂ) *
          (if complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w) ∈ U then
            f (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w)) *
              g (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w)) else 0)) =
      ∫ w : EuclideanSpace ℝ (Fin n × Fin 2),
        (fderiv ℝ (localFixedKernel hη m) w (complexToRealCoordinateEquiv v) : ℂ) *
          (if complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w) ∈ U then
            f (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w)) else 0) *
          (if complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w) ∈ U then
            g (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w)) else 0) := by
    apply integral_congr_ae
    filter_upwards [] with w
    by_cases hmem : complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w) ∈ U
    · have hmem' : x - complexToRealCoordinateEquiv.symm w ∈ U := by
        rw [← hsample w]
        exact hmem
      simp [hmem', mul_assoc]
    · have hmem' : x - complexToRealCoordinateEquiv.symm w ∉ U := by
        intro h
        apply hmem
        rw [hsample w]
        exact h
      simp [hmem']
  have hbase :
      (Complex.reCLM.comp
        ((localFixedMollify U hη m f x) • dg +
          (localFixedMollify U hη m g x) • df - dfg)) v =
        ((localFixedMollify U hη m f x) *
            (∫ w : EuclideanSpace ℝ (Fin n × Fin 2),
              (fderiv ℝ (localFixedKernel hη m) w (complexToRealCoordinateEquiv v) : ℂ) *
                (if complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w) ∈ U then
                  g (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w)) else 0)) +
          (localFixedMollify U hη m g x) *
            (∫ w : EuclideanSpace ℝ (Fin n × Fin 2),
              (fderiv ℝ (localFixedKernel hη m) w (complexToRealCoordinateEquiv v) : ℂ) *
                (if complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w) ∈ U then
                  f (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w)) else 0)) -
          ∫ w : EuclideanSpace ℝ (Fin n × Fin 2),
            (fderiv ℝ (localFixedKernel hη m) w (complexToRealCoordinateEquiv v) : ℂ) *
              (if complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w) ∈ U then
                f (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w)) *
                  g (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w)) else 0)).re := by
    simp [Complex.reCLM, hdf v, hdg v, hdfg v]
  calc
    _ = _ := hbase
    _ = _ := by rw [hcut]
  · intro v
    have hsample (w : EuclideanSpace ℝ (Fin n × Fin 2)) :
        complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w) =
          x - complexToRealCoordinateEquiv.symm w := by
      rw [map_sub, complexToRealCoordinateEquiv.symm_apply_apply]
    have hcut :
        (∫ w : EuclideanSpace ℝ (Fin n × Fin 2),
          (fderiv ℝ (localFixedKernel hη m) w (complexToRealCoordinateEquiv v) : ℂ) *
            (if complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w) ∈ U then
              f (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w)) *
                g (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w)) else 0)) =
        ∫ w : EuclideanSpace ℝ (Fin n × Fin 2),
          (fderiv ℝ (localFixedKernel hη m) w (complexToRealCoordinateEquiv v) : ℂ) *
            (if complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w) ∈ U then
              f (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w)) else 0) *
            (if complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w) ∈ U then
              g (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w)) else 0) := by
      apply integral_congr_ae
      filter_upwards [] with w
      by_cases hmem : complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w) ∈ U
      · have hmem' : x - complexToRealCoordinateEquiv.symm w ∈ U := by
          rw [← hsample w]
          exact hmem
        simp [hmem', mul_assoc]
      · have hmem' : x - complexToRealCoordinateEquiv.symm w ∉ U := by
          intro h
          apply hmem
          rw [hsample w]
          exact h
        simp [hmem']
    simp only [add_apply, sub_apply, smul_apply, hdf v, hdg v, hdfg v]
    rw [hcut]
    ring

end CalabiYau.Schauder
