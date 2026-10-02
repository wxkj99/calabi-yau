module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.Basic
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.ContractionBound.MetricFrame
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.ContractionBound.MixedFrame
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.ContractionBound.PairingCovariance
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.ContractionBound.DiagonalPairing

/-!
# ChartEnergy for the differentiated Ricci contraction

Székelyhidi, An Introduction to Extremal Kähler Metrics, §3.3, proof of
Lemma 3.9, printed pp. 44–45: two-sided metric comparison and the
linear-plus-quadratic connection correction.

The chart energy estimate follows from scalar pairing covariance and the explicit perturbed metric. For equal flat metrics it is the sum of squared connection coefficients; in dimension one the weight is `1/d`.
-/

public section

open scoped Manifold ContDiff BigOperators ComplexOrder MatrixOrder
open ContinuousAlternatingMap
open Matrix

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

theorem c3_calabi_energy_eq_connection_pair {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₀ : KahlerForm n M) (φ : M → ℝ) (x : M)
    (z : EuclideanSpace ℂ (Fin n)) :
    calabiEnergyInChart ω₀ φ x z =
      (c3Pair (c3PerturbedMetricInChart ω₀ φ x) z
        (fun i j k ↦ c3ConnectionDifferenceInChart ω₀ φ x z i j k)
        (fun i j k ↦ c3ConnectionDifferenceInChart ω₀ φ x z i j k)).re := by
  classical
  unfold calabiEnergyInChart c3Pair
  rfl

omit [T2Space M] [CompactSpace M] in
theorem c3_calabiEnergyInChart_eq_frame_weighted_sum
    (ω₀ : KahlerForm n M) (φ : M → ℝ) (x : M)
    (P Q : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ)
    (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hdiag : P.transpose *
      c3PerturbedMetricInChart ω₀ φ x
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) * P.map star =
          Matrix.diagonal (fun i ↦ (d i : ℂ)))
    (hd : ∀ i, 0 < d i) :
    calabiEnergyInChart ω₀ φ x
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) =
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (d i / (d j * d k)) *
          ‖c3MixedFrameChange P Q
            (fun i j k ↦ c3ConnectionDifferenceInChart ω₀ φ x
              (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) i j k)
            i j k‖ ^ 2 := by
  classical
  let z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x
  let T : Fin n → Fin n → Fin n → ℂ :=
    fun i j k ↦ c3ConnectionDifferenceInChart ω₀ φ x z i j k
  let g := c3PerturbedMetricInChart ω₀ φ x
  let gd : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun _ ↦ Matrix.diagonal (fun i ↦ (d i : ℂ))
  have hmetric := c3_frame_metric_sum_identities (g z)
    (Matrix.diagonal (fun i ↦ (d i : ℂ))) P Q (fun i ↦ (d i : ℂ))
    hPQ hQP rfl (by simpa [g, z] using hdiag)
  have hpair : c3Pair gd (0 : EuclideanSpace ℂ (Fin n))
      (c3MixedFrameChange P Q T) (c3MixedFrameChange P Q T) =
      c3Pair g z T T := by
    have hcov := c3Pair_frame_change
      (Matrix.diagonal (fun i ↦ (d i : ℂ)))
      ((Matrix.diagonal (fun i ↦ (d i : ℂ)))⁻¹)
      (g z) ((g z)⁻¹) P Q T T hmetric.1 hmetric.2
    simpa only [c3Pair, gd, g, z, Function.comp_apply] using hcov
  have hpairre :
      (c3Pair gd (0 : EuclideanSpace ℂ (Fin n))
        (c3MixedFrameChange P Q T) (c3MixedFrameChange P Q T)).re =
      (c3Pair g z T T).re := congrArg RCLike.re hpair
  have hweighted := c3_pair_diagonal_metric_eq_weighted_sum d
    (c3MixedFrameChange P Q T) hd
  rw [c3_calabi_energy_eq_connection_pair]
  change (c3Pair g z T T).re = _
  rw [← hpairre, hweighted]

end KahlerForm
