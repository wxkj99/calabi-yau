module

public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.ComplexSmoothBall.Basic
public import CalabiYau.Analysis.Elliptic.Schauder.VariableCoefficient.BallInterior
public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.SourceInterpolationProofs.LowerJet

/-!
# Canonical second derivative product formula, matrix contraction and source agreement.

Proof-preserving extraction from the committed SourceInterpolation module
073d0f59b03ec37cc921b9792875e063bec3fb01.
Source: Constantin, Schauder Estimates, equation (9), p. 7 and localization/
lower-jet interpolation, pp. 8–9. Only visibility and namespace are changed.
-/

@[expose] public section

open Set Matrix
open scoped NNReal ContDiff Topology

namespace CalabiYau.Schauder.SourceInterpolationProofs

theorem realBallCutoffJet_second_eq_raw_cutoff_formula
    {n : ℕ} {α : ℝ≥0} {x : RealBallModel n} {δ : ℝ}
    {u : RealBallModel n → ℝ} (hδ : 0 < δ)
    (jet : RealBallCutoffJet α x δ u)
    (hsmooth : ∀ z ∈ Metric.ball x (2 * δ), ContDiffAt ℝ 2 u z) :
    ∀ y ∈ Metric.ball x δ,
      jet.second y =
        (ballCutoffBoundedContinuousFunction x (show 0 ≤ δ / 2 by positivity)
            (by linarith : δ / 2 < δ) y) • fderiv ℝ (fderiv ℝ u) y +
        (ballCutoffFDerivBoundedContinuousFunction x
            (show 0 ≤ δ / 2 by positivity) (by linarith : δ / 2 < δ) y).smulRight
          (fderiv ℝ u y) +
        (ContinuousLinearMap.smulRightL ℝ (RealBallModel n) ℝ).precompR
          (RealBallModel n)
          (ballCutoffFDerivBoundedContinuousFunction x
            (show 0 ≤ δ / 2 by positivity) (by linarith : δ / 2 < δ) y)
          (fderiv ℝ u y) +
        (ContinuousLinearMap.smulRightL ℝ (RealBallModel n) ℝ).precompL
          (RealBallModel n)
          (ballCutoffFDeriv2BoundedContinuousFunction x
            (show 0 ≤ δ / 2 by positivity) (by linarith : δ / 2 < δ) y)
          (u y) := by
  let chi := ballCutoffBoundedContinuousFunction x (show 0 ≤ δ / 2 by positivity)
    (by linarith : δ / 2 < δ)
  let dchi := ballCutoffFDerivBoundedContinuousFunction x (show 0 ≤ δ / 2 by positivity)
    (by linarith : δ / 2 < δ)
  let d2chi := ballCutoffFDeriv2BoundedContinuousFunction x (show 0 ≤ δ / 2 by positivity)
    (by linarith : δ / 2 < δ)
  let du := fderiv ℝ u
  let d2u := fderiv ℝ (fderiv ℝ u)
  let w1 : RealBallModel n → RealBallModel n →L[ℝ] ℝ :=
    fun z => chi z • du z + (dchi z).smulRight (u z)
  let w2 : RealBallModel n → RealBallModel n →L[ℝ] RealBallModel n →L[ℝ] ℝ :=
    fun z => chi z • d2u z + (dchi z).smulRight (du z) +
      (ContinuousLinearMap.smulRightL ℝ (RealBallModel n) ℝ).precompR
        (RealBallModel n) (dchi z) (du z) +
      (ContinuousLinearMap.smulRightL ℝ (RealBallModel n) ℝ).precompL
        (RealBallModel n) (d2chi z) (u z)
  intro y hy
  have hyU : y ∈ Metric.ball x (2 * δ) := by
    rw [Metric.mem_ball] at hy ⊢
    have hdist := Metric.mem_ball.mp hy
    calc
      dist y x < δ := hdist
      _ ≤ 2 * δ := by linarith
  have hchi : ∀ z, HasFDerivAt (chi : RealBallModel n → ℝ) (dchi z) z :=
    hasFDerivAt_ballCutoff x (δ / 2) δ
  have hdchi : ∀ z,
      HasFDerivAt (dchi : RealBallModel n → RealBallModel n →L[ℝ] ℝ) (d2chi z) z :=
    hasFDerivAt_ballCutoffFDeriv x (δ / 2) δ
  have hu : ∀ z ∈ Metric.ball x (2 * δ), HasFDerivAt u (du z) z := by
    intro z hz
    exact (hsmooth z hz).differentiableAt (by norm_num) |>.hasFDerivAt
  have hdu : ∀ z ∈ Metric.ball x (2 * δ),
      HasFDerivAt du (d2u z) z := by
    intro z hz
    have hcont : ContDiffAt ℝ 1 (fderiv ℝ u) z := (hsmooth z hz).fderiv_right (by norm_num)
    exact (hcont.differentiableAt (by norm_num)).hasFDerivAt
  have hfirstEq : ∀ z ∈ Metric.ball x (2 * δ), jet.first z = w1 z := by
    intro z hz
    have hprod := (hchi z).smul (hu z hz)
    have heq : (fun q => chi q * u q) = fun q => (jet.value : RealBallModel n → ℝ) q := by
      funext q
      rw [jet.value_eq q]
      rfl
    have hprod' := hprod.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq heq.symm)
    exact (jet.derivative z).unique hprod'
  have hleft := (hchi y).smul (hdu y hyU)
  have hright := (ContinuousLinearMap.smulRightL ℝ (RealBallModel n) ℝ).hasFDerivAt_of_bilinear
    (hdchi y) (hu y hyU)
  have hsum := hleft.add hright
  have hfun :
      ((chi : RealBallModel n → ℝ) • du +
        fun z => (ContinuousLinearMap.smulRightL ℝ (RealBallModel n) ℝ) (dchi z) (u z)) = w1 := by
    funext z
    rfl
  rw [hfun] at hsum
  have hfirstNear :
      (w1 : RealBallModel n → RealBallModel n →L[ℝ] ℝ) =ᶠ[𝓝 y] jet.first := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hyU] with z hz
    exact (hfirstEq z hz).symm
  have hjet := (jet.second_derivative y).congr_of_eventuallyEq hfirstNear
  have hsum' : HasFDerivAt w1 (w2 y) y := by
    simpa only [w1, w2, add_assoc] using hsum
  have heq2 := hjet.unique hsum'
  simpa only [w1, w2, chi, dchi, d2chi, du, d2u] using heq2

theorem realBallCutoffJet_variableMatrixLap_formula_on_ball
    {n : ℕ} {α : ℝ≥0}
    {a : RealBallModel n → Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ}
    {u : RealBallModel n → ℝ} {x : RealBallModel n} {δ : ℝ}
    (hδ : 0 < δ)
    (coeff : RealBallCoefficientExtension a x δ)
    (jet : RealBallCutoffJet α x δ u)
    (hsmooth : ∀ z ∈ Metric.ball x (2 * δ), ContDiffAt ℝ 2 u z) :
    ∀ y ∈ Metric.ball x δ,
      variableMatrixLap coeff.coefficient jet.second y =
        ballCutoff x (δ / 2) δ y * realBallSource a u y +
        ∑ i, ∑ j,
          ((a y i j * ballCutoffFDeriv x (δ / 2) δ y
              (EuclideanSpace.basisFun (Fin n × Fin 2) ℝ i)) *
              fderiv ℝ u y (EuclideanSpace.basisFun (Fin n × Fin 2) ℝ j) +
            (a y i j * ballCutoffFDeriv x (δ / 2) δ y
              (EuclideanSpace.basisFun (Fin n × Fin 2) ℝ j)) *
              fderiv ℝ u y (EuclideanSpace.basisFun (Fin n × Fin 2) ℝ i) +
            (a y i j * ballCutoffFDeriv2 x (δ / 2) δ y
              (EuclideanSpace.basisFun (Fin n × Fin 2) ℝ i)
              (EuclideanSpace.basisFun (Fin n × Fin 2) ℝ j)) * u y) := by
  have hsecond := realBallCutoffJet_second_eq_raw_cutoff_formula hδ jet hsmooth
  intro y hy
  have hcoeff : (fun i j => coeff.coefficient i j y) = fun i j => a y i j := by
    funext i j
    exact coeff.agrees i j y hy
  unfold realBallSource
  rw [variableMatrixLap_apply, hcoeff, hsecond y hy]
  simp [HeatEquation.matrixLap, Finset.sum_add_distrib, Finset.mul_sum,
    smul_eq_mul, mul_add, mul_left_comm, mul_comm] ; abel

theorem realBallCutoffJet_global_holder_of_cutoff_formula
    {n : ℕ} {α Ksrc Kcomm : ℝ≥0} {x : RealBallModel n} {δ : ℝ}
    {a : RealBallModel n → Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ}
    {u : RealBallModel n → ℝ}
    (hδ : 0 < δ)
    (coeff : RealBallCoefficientExtension a x δ)
    (jet : RealBallCutoffJet α x δ u)
    (source comm : RealBallModel n → ℝ)
    (hsource : HolderWith Ksrc α
      (fun y => ballCutoff x (δ / 2) δ y * source y))
    (hcomm : HolderWith Kcomm α comm)
    (hformula : ∀ y ∈ Metric.ball x δ,
      variableMatrixLap coeff.coefficient jet.second y =
        ballCutoff x (δ / 2) δ y * source y + comm y)
    (hcommZero : ∀ y, y ∉ Metric.ball x δ → comm y = 0) :
    HolderWith (Ksrc + Kcomm) α
      (variableMatrixLap coeff.coefficient jet.second : RealBallModel n → ℝ) := by
  have hsum : HolderWith (Ksrc + Kcomm) α
      (fun y => ballCutoff x (δ / 2) δ y * source y + comm y) := hsource.add hcomm
  apply holderWith_congr hsum
  intro y
  by_cases hy : y ∈ Metric.ball x δ
  · exact (hformula y hy).symm
  · have hjet : jet.second y = 0 := jet.second_support y hy
    have hcomm' := hcommZero y hy
    have hcut : ballCutoff x (δ / 2) δ y = 0 :=
      ballCutoff_eq_zero_of_not_mem_ball (by positivity) (by linarith) hy
    have hhalf : δ / 2 < δ := by linarith
    rw [variableMatrixLap_apply, hjet]
    simp [HeatEquation.matrixLap, hcomm', hcut]

theorem realBallCutoffJet_source_agrees_on_inner
    {n : ℕ} {α lam K K₀ K₁ : ℝ≥0} {U : Set (RealBallModel n)}
    {a : RealBallModel n → Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ}
    {u : RealBallModel n → ℝ} {x : RealBallModel n} {δ : ℝ}
    (hδ : 0 < δ) (hU : IsOpen U) (hball : Metric.closedBall x δ ⊆ U)
    (hdata : RealSmoothBallData α lam K K₀ K₁ U a u)
    (coeff : RealBallCoefficientExtension a x δ)
    (jet : RealBallCutoffJet α x δ u) :
    ∀ y ∈ Metric.ball x (δ / 2),
      variableMatrixLap coeff.coefficient jet.second y = realBallSource a u y := by
  have hhalf : δ / 2 < δ := by linarith
  have hinner : Metric.ball x (δ / 2) ⊆ Metric.ball x δ :=
    Metric.ball_subset_ball hhalf.le
  have hUinner : Metric.ball x (δ / 2) ⊆ U :=
    hinner.trans (Metric.ball_subset_closedBall.trans hball)
  have hu2 : ∀ y ∈ Metric.ball x (δ / 2), ContDiffAt ℝ 2 u y := by
    intro y hy
    exact (hdata.potential_smooth.contDiffAt (hU.mem_nhds (hUinner hy))).of_le (by
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr
        (show (2 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top))
  have hsecond := realBallCutoffJet_second_eq_fderiv_fderiv_on_inner hδ jet hu2
  intro y hy
  have hcoeff : (fun i j => coeff.coefficient i j y) = fun i j => a y i j := by
    funext i j
    exact coeff.agrees i j y (hinner hy)
  unfold realBallSource
  rw [variableMatrixLap_apply, hcoeff, hsecond y hy]

end CalabiYau.Schauder.SourceInterpolationProofs
