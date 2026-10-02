module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.Basic
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.ContractionBound.MetricFrame
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.ContractionBound.MixedFrame
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.ContractionBound.PairingCovariance
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.ContractionBound.RaisedCovariance
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.ContractionBound.DiagonalPairing

/-!
# ScalarTransport for the differentiated Ricci contraction

Székelyhidi, An Introduction to Extremal Kähler Metrics, §3.3, proof of
Lemma 3.9, printed pp. 44–45: two-sided metric comparison and the
linear-plus-quadratic connection correction.

The diagonal error identity and general-frame scalar transport pair the raised action with `conj(T)`. For `P = 1` and `d = 1` this is the defining error; in dimension one scalar changes cancel, while in dimension zero both scalars vanish.
-/

public section

open scoped Manifold ContDiff BigOperators ComplexOrder MatrixOrder
open ContinuousAlternatingMap
open Matrix

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

theorem c3_general_frame_scalar_transport {n : ℕ}
    (P B G : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ)
    (z : EuclideanSpace ℂ (Fin n))
    (S T : Fin n → Fin n → Fin n → ℂ)
    (hd : ∀ i, 0 < d i) (hPB : P * B = 1) (hBP : B * P = 1)
    (hdiag : P.transpose * G * P.map star =
      Matrix.diagonal (fun i ↦ (d i : ℂ))) :
    (c3Pair (fun _ : EuclideanSpace ℂ (Fin n) ↦ G) z
      (fun i j k ↦ ∑ l, G⁻¹ l i * S k j l) T).re =
      RCLike.re (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (d i / (d j * d k) : ℂ) * star (c3MixedFrameChange P B T i j k) *
          (((d i : ℂ)⁻¹) * c3ThreeCovariantFrame P S k j i)) := by
  let D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun i ↦ (d i : ℂ))
  let gd : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ := fun _ ↦ D
  let U : Fin n → Fin n → Fin n → ℂ := fun i j k ↦ ∑ l, G⁻¹ l i * S k j l
  have hmetrics := c3_frame_metric_sum_identities G D P B (fun i ↦ (d i : ℂ))
    hPB hBP rfl (by simpa [D] using hdiag)
  have hpair :
      c3Pair (fun _ : EuclideanSpace ℂ (Fin n) ↦ G) z U T =
        c3Pair gd (0 : EuclideanSpace ℂ (Fin n))
          (c3MixedFrameChange P B U) (c3MixedFrameChange P B T) := by
    have hcov := c3Pair_frame_change D D⁻¹ G G⁻¹ P B U T hmetrics.1 hmetrics.2
    simpa only [c3Pair, gd, D, Function.comp_apply] using hcov.symm
  have hRaised (i j k : Fin n) :
      c3MixedFrameChange P B U i j k =
        ((d i : ℂ)⁻¹) * c3ThreeCovariantFrame P S k j i := by
    have hcov := c3_raised_three_tensor_covariance P B G d hPB hBP hd hdiag
      (fun a b c ↦ S a b c) i j k
    have hcov' :
        (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
          B i a * P b j * P c k * (∑ l : Fin n, G⁻¹ l a * S c b l)) =
          ((d i)⁻¹ : ℂ) * ∑ b : Fin n, ∑ c : Fin n,
            P c k * P b j * (∑ l : Fin n, star (P l i) * S c b l) := by
      simpa using hcov
    have hleft : c3MixedFrameChange P B U i j k =
        ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
          B i a * P b j * P c k * (∑ l : Fin n, G⁻¹ l a * S c b l) := by
      simp [c3MixedFrameChange, C3Pair, Fintype.sum_prod_type, U]
    rw [hleft, hcov']
    congr 1
    unfold c3ThreeCovariantFrame
    simp_rw [Finset.mul_sum]
    calc
      ∑ b : Fin n, ∑ c : Fin n, ∑ l : Fin n,
          P c k * P b j * (star (P l i) * S c b l) =
        ∑ c : Fin n, ∑ b : Fin n, ∑ l : Fin n,
          P c k * P b j * (star (P l i) * S c b l) := Finset.sum_comm
      _ = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
          P a k * P b j * star (P c i) * S a b c := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        apply Finset.sum_congr rfl
        intro c hc
        ring
  rw [hpair]
  rw [c3_pair_diagonal_metric_eq_weighted_pairing d _ _ hd]
  change RCLike.re (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      (d i / (d j * d k) : ℂ) *
        c3MixedFrameChange P B U i j k * star (c3MixedFrameChange P B T i j k)) = _
  simp_rw [hRaised]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

omit [T2Space M] [CompactSpace M] in
theorem c3_error_eq_general_frame_action
    (ω₀ : KahlerForm n M) (G φ : M → ℝ) (x : M)
    (P B : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ)
    (hd : ∀ i, 0 < d i) (hPB : P * B = 1) (hBP : B * P = 1)
    (hdiag : P.transpose * c3PerturbedMetricInChart ω₀ φ x
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) * P.map star =
      Matrix.diagonal (fun i ↦ (d i : ℂ))) :
    c3RicciDerivativeError ω₀ G φ x =
      let z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x
      let T := connectionDifferenceInChart ω₀ φ x
      let R := c3RicciInChart (ω₀.metricInChart x)
      let H := c3ForcingHessianInChart G x
      let S : Fin n → Fin n → Fin n → ℂ := fun a b c ↦
        c3ReferenceCovariantTwoTensorZ ω₀ x R z a b c -
          c3ReferenceCovariantTwoTensorZ ω₀ x H z a b c -
          ∑ r, T z r a b * (R z r c - H z r c)
      RCLike.re (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (d i / (d j * d k) : ℂ) * star (c3MixedFrameChange P B (T z) i j k) *
          (((d i : ℂ)⁻¹) * c3ThreeCovariantFrame P S k j i)) := by
  classical
  let z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x
  let g := c3PerturbedMetricInChart ω₀ φ x
  let T := connectionDifferenceInChart ω₀ φ x
  let R := c3RicciInChart (ω₀.metricInChart x)
  let H := c3ForcingHessianInChart (n := n) G x
  let S : Fin n → Fin n → Fin n → ℂ := fun a b c ↦
    c3ReferenceCovariantTwoTensorZ ω₀ x R z a b c -
      c3ReferenceCovariantTwoTensorZ ω₀ x H z a b c -
      ∑ r, T z r a b * (R z r c - H z r c)
  have hbasic : c3RicciDerivativeError ω₀ G φ x =
      (c3Pair (fun _ : EuclideanSpace ℂ (Fin n) ↦ g z) z
        (fun i j k ↦ ∑ l, (g z)⁻¹ l i * S k j l) (T z)).re := by
    unfold c3RicciDerivativeError
    dsimp [z, g, T, R, H, S]
    rfl
  rw [hbasic]
  exact c3_general_frame_scalar_transport P B (g z) d z S (T z)
    hd hPB hBP (by simpa [g, z] using hdiag)

end KahlerForm
