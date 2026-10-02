module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.Basic
public import CalabiYau.Geometry.Complex.Forms.Positive
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.ContractionBound.MetricFrame
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.ContractionBound.ResidualCovariance
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.ContractionBound.FrameBounds
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.ContractionBound.DiagonalAction
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.ContractionBound.ChartEnergy
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.ContractionBound.ScalarTransport

/-!
# UniformEstimate for the differentiated Ricci contraction

Székelyhidi, An Introduction to Extremal Kähler Metrics, §3.3, proof of
Lemma 3.9, printed pp. 44–45: two-sided metric comparison and the
linear-plus-quadratic connection correction.

The estimate assumes actual potentials, two finite relative trace bounds, and explicit reference and forcing jets in each reference-orthonormal frame. It vanishes for `Fin 0` and flat zero jets. In dimension one the weight and raising factors give `1/d^2`; complex-linear frame changes preserve the scalar. The nonzero torus case requires `C > 0`.
-/

public section

open scoped Manifold ContDiff BigOperators ComplexOrder MatrixOrder
open ContinuousAlternatingMap
open Matrix

namespace KahlerForm

private theorem c3_residual_covariant_frame_change {n : ℕ}
    (P B : Matrix (Fin n) (Fin n) ℂ)
    (T Y : Fin n → Fin n → Fin n → ℂ)
    (S : Fin n → Fin n → ℂ)
    (hPB : P * B = 1) (k j i : Fin n) :
    c3ThreeCovariantFrame P
      (fun a b c ↦ Y a b c - ∑ r, T r a b * S r c) k j i =
      c3ThreeCovariantFrame P Y k j i -
        ∑ r, c3MixedFrameChange P B T r k j * c3TwoCovariantFrame P S r i := by
  classical
  rw [c3_frame_residual_tensor_identity P B T Y S hPB k j i]
  unfold c3ThreeCovariantFrame
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  calc
    (∑ a, ∑ b, ∑ c, ∑ r,
        P a k * P b j * star (P c i) * (T r a b * S r c)) =
        ∑ r, ∑ a, ∑ b, ∑ c,
          P a k * P b j * star (P c i) * (T r a b * S r c) := by
      conv_lhs =>
        enter [2]; intro a
        enter [2]; intro b
        rw [Finset.sum_comm]
      conv_lhs =>
        enter [2]; intro a
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      ring

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

set_option maxHeartbeats 600000 in
theorem c3_exists_uniform_ricci_derivative_error_bound (ω₀ : KahlerForm n M)
    (S : Set ((M → ℝ) × (M → ℝ))) (hS : ∀ p ∈ S, ω₀.IsPotential p.2)
    (hMetric : ∃ B : ℝ, 0 < B ∧ ∀ p ∈ S, ∀ x,
      relTrace (ω₀ x) (ω₀ x + mddbar n p.2 x) ≤ B ∧
      relTrace (ω₀ x + mddbar n p.2 x) (ω₀ x) ≤ B)
    (R H : ℝ) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hRicci : ∀ x P, referenceOrthonormalFrameMatrix ω₀ x P →
      c3ReferenceRicciFrameBound ω₀ x
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) P R)
    (hForcing : ∀ p ∈ S, ∀ x P, referenceOrthonormalFrameMatrix ω₀ x P →
      c3ForcingFrameBound ω₀ p.1 x
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) P H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ S, ∀ x,
      |c3RicciDerivativeError ω₀ p.1 p.2 x| ≤
        C * (calabiEnergy ω₀ p.2 x + Real.sqrt (calabiEnergy ω₀ p.2 x)) := by
  obtain ⟨B, hB, hMetricBounds⟩ := hMetric
  let C := B ^ 3 * (n : ℝ) ^ 3 * (B * (R + H) * ((n : ℝ) + 1)) * (1 + B ^ 3)
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    positivity
  · intro p hp x
    have hφ : ω₀.IsPotential p.2 := hS p hp
    let z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x
    let g := ω₀.metricInChart x z
    let a := c3PerturbedMetricInChart ω₀ p.2 x z
    have hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target :=
      mem_extChartAt_target x
    have hG : g.PosDef := by
      change (ω₀.metricInChart x z).PosDef
      exact ω₀.posDef_metricInChart x hz
    have hA : a.PosDef := by
      change (ω₀.metricInChart x z +
        complexHessian (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z).PosDef
      rw [← ω₀.metricInChart_perturb hφ x hz]
      exact (ω₀.perturb p.2 hφ).posDef_metricInChart x hz
    have hbaseCoeff : (ω₀ x).coeffMatrix = g := by
      change (ω₀ x).coeffMatrix = ω₀.metricInChart x z
      exact (ω₀.metricInChart_self x).symm
    have hpertCoeff : ((ω₀.perturb p.2 hφ) x).coeffMatrix = a := by
      rw [← (ω₀.perturb p.2 hφ).metricInChart_self x,
        ω₀.metricInChart_perturb hφ x hz]
      rfl
    have hforward : relTrace (ω₀ x) (ω₀ x + mddbar n p.2 x) ≤ B :=
      (hMetricBounds p hp x).1
    have hreverse : relTrace (ω₀ x + mddbar n p.2 x) (ω₀ x) ≤ B :=
      (hMetricBounds p hp x).2
    have hMatrixForward : (g⁻¹ * a).trace.re ≤ B := by
      have hh := hforward
      rw [← ω₀.perturb_apply hφ x, ContinuousAlternatingMap.relTrace,
        hbaseCoeff, hpertCoeff] at hh
      simpa [g, a, z, c3PerturbedMetricInChart] using hh
    have hMatrixReverse : (a⁻¹ * g).trace.re ≤ B := by
      have hh := hreverse
      rw [← ω₀.perturb_apply hφ x, ContinuousAlternatingMap.relTrace,
        hpertCoeff, hbaseCoeff] at hh
      simpa [g, a, z, c3PerturbedMetricInChart] using hh
    obtain ⟨P, d, hPG, hPA, hdb⟩ :=
      c3_exists_trace_controlled_diagonal_frame g a B hG hA hB
        hMatrixForward hMatrixReverse
    have hd : ∀ i, 0 < d i := by
      intro i
      exact lt_of_lt_of_le (inv_pos.mpr hB) (hdb i).1
    let Astar := P.map star
    have hLA : (P.transpose * g) * Astar = 1 := by
      simpa [Astar, Matrix.mul_assoc] using hPG
    have hdet : Astar.det * (P.transpose * g).det = 1 := by
      have h := congrArg Matrix.det hLA
      rw [Matrix.det_mul, Matrix.det_one] at h
      calc
        Astar.det * (P.transpose * g).det = (P.transpose * g).det * Astar.det := mul_comm _ _
        _ = 1 := h
    have hAunit : IsUnit Astar.det := IsUnit.of_mul_eq_one _ hdet
    have hright : Astar * Astar⁻¹ = 1 := Matrix.mul_nonsing_inv Astar hAunit
    have hleft : Astar⁻¹ * Astar = 1 := Matrix.nonsing_inv_mul Astar hAunit
    let Q := Astar⁻¹.map star
    have hPQ : P * Q = 1 := by
      ext i j
      have h := congrArg star (congrFun (congrFun hright i) j)
      simpa [Astar, Q, Matrix.mul_apply, Matrix.one_apply, star_sum, star_mul,
        mul_comm] using h
    have hQP : Q * P = 1 := by
      ext i j
      have h := congrArg star (congrFun (congrFun hleft i) j)
      simpa [Astar, Q, Matrix.mul_apply, Matrix.one_apply, star_sum, star_mul,
        mul_comm] using h
    have hframe : referenceOrthonormalFrameMatrix ω₀ x P := by
      change P.transpose * g * P.map star = 1
      exact hPG
    have hdiagReal : P.transpose * c3PerturbedMetricInChart ω₀ p.2 x z * P.map star =
        Matrix.diagonal (RCLike.ofReal ∘ d) := by
      simpa [a, z, c3PerturbedMetricInChart] using hPA
    have hdiag : P.transpose * c3PerturbedMetricInChart ω₀ p.2 x z * P.map star =
        Matrix.diagonal (fun i ↦ (d i : ℂ)) := by
      rw [hdiagReal]
      congr 1
    let R0 := c3RicciInChart (ω₀.metricInChart x)
    let H0 : EuclideanSpace ℂ (Fin n) → Fin n → Fin n → ℂ :=
      fun w a b ↦ c3ForcingHessianInChart (n := n) p.1 x w a b
    let X : Fin n → Fin n → Fin n → ℂ := fun k j l ↦
      c3ReferenceCovariantTwoTensorZ ω₀ x R0 z k j l
    let Y : Fin n → Fin n → Fin n → ℂ := fun k j l ↦
      c3ReferenceCovariantTwoTensorZ ω₀ x (fun w a b ↦ H0 w a b) z k j l
    let D2 : Fin n → Fin n → ℂ := fun j l ↦ R0 z j l - H0 z j l
    let D3 : Fin n → Fin n → Fin n → ℂ := fun k j l ↦ X k j l - Y k j l
    let T0 : Fin n → Fin n → Fin n → ℂ :=
      c3ConnectionDifferenceInChart ω₀ p.2 x z
    let T := c3MixedFrameChange P Q T0
    let Q2 := c3TwoCovariantFrame P D2
    let Y3 := c3ThreeCovariantFrame P D3
    have hRic := hRicci x P hframe
    have hForce := hForcing p hp x P hframe
    have hdiff := c3_frame_difference_bounds P (R0 z) (H0 z) X Y R H
      hRic.1 hForce.1 hRic.2 hForce.2
    have hQ : ∀ j l, ‖Q2 j l‖ ≤ R + H := by
      simpa [Q2, D2, R0, H0] using hdiff.1
    have hY : ∀ k j l, ‖Y3 k j l‖ ≤ R + H := by
      simpa [Y3, D3] using hdiff.2
    have hE : 0 ≤ calabiEnergy ω₀ p.2 x := calabiEnergy_nonneg ω₀ hφ x
    have henergy : ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (d i / (d j * d k)) * ‖T i j k‖ ^ 2 ≤ calabiEnergy ω₀ p.2 x := by
      have heq := c3_calabiEnergyInChart_eq_frame_weighted_sum ω₀ p.2 x P Q d
        hPQ hQP hdiag hd
      simpa [calabiEnergy, T, T0, z] using le_of_eq heq.symm
    have hResidual (k j i : Fin n) :
        c3ThreeCovariantFrame P
          (fun a b c ↦ X a b c - Y a b c -
            ∑ r, T0 r a b * D2 r c) k j i =
          Y3 k j i - ∑ r, T r k j * Q2 r i := by
      exact c3_residual_covariant_frame_change P Q T0 D3 D2 hPQ k j i
    have htransport : c3RicciDerivativeError ω₀ p.1 p.2 x =
        RCLike.re (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          (d i / (d j * d k) : ℂ) * star (T i j k) *
            ((d i : ℂ)⁻¹ * c3ThreeCovariantFrame P
              (fun a b c ↦ X a b c - Y a b c -
                ∑ r, T0 r a b * D2 r c) k j i)) := by
      exact c3_error_eq_general_frame_action ω₀ p.1 p.2 x P Q d
        hd hPQ hQP hdiag
    have hAction :
        |c3RicciDerivativeError ω₀ p.1 p.2 x| ≤
          B ^ 3 * (n : ℝ) ^ 3 * (B * (R + H) * ((n : ℝ) + 1)) *
            (Real.sqrt (B ^ 3 * calabiEnergy ω₀ p.2 x) +
              B ^ 3 * calabiEnergy ω₀ p.2 x) := by
      rw [htransport]
      simp_rw [hResidual]
      exact c3_weighted_diagonal_error_growth d T Y3 Q2 B
        (calabiEnergy ω₀ p.2 x) (R + H) hB hE (add_nonneg hR hH) hd hdb
        henergy hQ hY
    calc
      |c3RicciDerivativeError ω₀ p.1 p.2 x| ≤
          B ^ 3 * (n : ℝ) ^ 3 * (B * (R + H) * ((n : ℝ) + 1)) *
            (Real.sqrt (B ^ 3 * calabiEnergy ω₀ p.2 x) +
              B ^ 3 * calabiEnergy ω₀ p.2 x) := hAction
      _ ≤ C * (calabiEnergy ω₀ p.2 x + Real.sqrt (calabiEnergy ω₀ p.2 x)) := by
        dsimp [C]
        have hsqrtCoeff : Real.sqrt (B ^ 3) ≤ 1 + B ^ 3 := by
          have hroot : 0 ≤ Real.sqrt (B ^ 3) := Real.sqrt_nonneg _
          have hsquare := Real.sq_sqrt (pow_nonneg (le_of_lt hB) 3)
          nlinarith
        have hsqrtMul : Real.sqrt (B ^ 3 * calabiEnergy ω₀ p.2 x) =
            Real.sqrt (B ^ 3) * Real.sqrt (calabiEnergy ω₀ p.2 x) := by
          rw [Real.sqrt_mul (pow_nonneg (le_of_lt hB) 3)]
        rw [hsqrtMul]
        have hcoef : 0 ≤ B ^ 3 * (n : ℝ) ^ 3 *
            (B * (R + H) * ((n : ℝ) + 1)) := by positivity
        have hEroot : 0 ≤ Real.sqrt (calabiEnergy ω₀ p.2 x) := Real.sqrt_nonneg _
        have hcube : B ^ 3 ≤ 1 + B ^ 3 := by nlinarith [pow_nonneg (le_of_lt hB) 3]
        calc
          _ ≤ (B ^ 3 * (n : ℝ) ^ 3 *
              (B * (R + H) * ((n : ℝ) + 1))) *
                ((1 + B ^ 3) * Real.sqrt (calabiEnergy ω₀ p.2 x) +
                  (1 + B ^ 3) * calabiEnergy ω₀ p.2 x) := by
            apply mul_le_mul_of_nonneg_left _ hcoef
            exact add_le_add
              (mul_le_mul_of_nonneg_right hsqrtCoeff hEroot)
              (mul_le_mul_of_nonneg_right hcube hE)
          _ = _ := by ring

end KahlerForm
