module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.BochnerTensors
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ConnectionCurvatureIdentity
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ConnectionLaplacian.MetricDerivatives
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ConnectionLaplacian.RaisedCurvature
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ConnectionLaplacian.RicciContraction
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ConnectionLaplacian.DifferentialBianchi
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ConnectionLaplacian.CovariantReduction

/-!
# Bianchi reduction of the contracted connection-difference derivative

Székelyhidi, §3.3, proof of Lemma 3.9, printed p. 45, the displayed calculation
following (3.15): `∇p∂̄p T = -∇k Ricⁱⱼ + ∇₀p R₀ⁱⱼk p̄ + (∇φ-∇₀)R₀ⁱⱼk p̄`.
The reference term is expanded concretely in `c3ReferenceTensorDrift`.
This identity is geometric and does not require a Monge–Ampère equation.
-/

@[expose] public section

open scoped Manifold ContDiff BigOperators ComplexOrder MatrixOrder

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

omit [T2Space M] [CompactSpace M] in
/-- The scalar contraction of the Bianchi identity that the Bochner proof uses.
The minus sign belongs to the varying Ricci derivative, not the reference term.
Use the already proved `c3ConnectionDifference_bar_derivative`; do not duplicate it. -/
theorem c3BochnerConnectionTerm_eq_reference_sub_ricci (ω₀ : KahlerForm n M)
    {φ : M → ℝ} (hφ : ω₀.IsPotential φ) (x : M) :
    c3BochnerConnectionTerm ω₀ φ x =
      c3BochnerReferenceTerm ω₀ φ x - c3BochnerRicciDerivativeTerm ω₀ φ x := by
  have hPartial
      (ω₀ : KahlerForm n M) {φ : M → ℝ} (hφ : ω₀.IsPotential φ)
      (x : M) (y : EuclideanSpace ℂ (Fin n))
      (hy : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
      (p i j k q : Fin n) :
      wirtingerDerivInChart
          (fun w ↦ c3PartialBar
            (fun v ↦ connectionDifferenceInChart ω₀ φ x v i j k) w q) y p =
        wirtingerDerivInChart
          (fun w ↦ -(∑ l, (c3PerturbedMetricInChart ω₀ φ x w)⁻¹ l i *
              chartCurvature (c3PerturbedMetricInChart ω₀ φ x) w j q k l) +
            ∑ l, (ω₀.metricInChart x w)⁻¹ l i *
              chartCurvature (ω₀.metricInChart x) w j q k l) y p := by
    let U : Set (EuclideanSpace ℂ (Fin n)) :=
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target
    let g₀ : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
      fun w ↦ ω₀.metricInChart x w
    let gφ : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
      fun w ↦ c3PerturbedMetricInChart ω₀ φ x w
    have hU : IsOpen U := isOpen_extChartAt_target x
    have hbar := c3ConnectionDifference_bar_derivative ω₀
    have hEq :
        (fun w ↦ c3PartialBar
            (fun v ↦ connectionDifferenceInChart ω₀ φ x v i j k) w q) =ᶠ[nhds y]
          (fun w ↦ -(∑ l, (gφ w)⁻¹ l i * chartCurvature gφ w j q k l) +
            ∑ l, (g₀ w)⁻¹ l i * chartCurvature g₀ w j q k l) := by
      filter_upwards [hU.mem_nhds hy] with w hw
      exact hbar φ hφ x w hw i j k q
    have hfd := hEq.fderiv_eq (𝕜 := ℝ)
    simpa [wirtingerDerivInChart, gφ, g₀] using congrArg
      (fun D : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦
        (D (EuclideanSpace.single p 1) -
          Complex.I * D (Complex.I • EuclideanSpace.single p 1)) / 2) hfd
  let c3ConnectionLapRaisedCurvature
      (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
      (z : EuclideanSpace ℂ (Fin n)) (i j k q : Fin n) : ℂ :=
    ∑ l, (g z)⁻¹ l i * chartCurvature g z j q k l
  have hCovariant
      (ω₀ : KahlerForm n M) {φ : M → ℝ} (hφ : ω₀.IsPotential φ)
      (x : M) (y : EuclideanSpace ℂ (Fin n))
      (hy : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
      (p i j k q : Fin n) :
      c3TensorCovariantZ (c3PerturbedMetricInChart ω₀ φ x)
        (fun w a b c =>
          c3PartialBar (fun v => connectionDifferenceInChart ω₀ φ x v a b c) w q)
        y p i j k =
      c3TensorCovariantZ (c3PerturbedMetricInChart ω₀ φ x)
        (fun w a b c =>
          -(∑ l, (c3PerturbedMetricInChart ω₀ φ x w)⁻¹ l a *
              chartCurvature (c3PerturbedMetricInChart ω₀ φ x) w b q c l) +
            ∑ l, (ω₀.metricInChart x w)⁻¹ l a *
              chartCurvature (ω₀.metricInChart x) w b q c l)
        y p i j k := by
    have hbar := c3ConnectionDifference_bar_derivative ω₀
    have hbarAt (a b c : Fin n) :
        c3PartialBar (fun v => connectionDifferenceInChart ω₀ φ x v a b c) y q =
          -(∑ l, (ω₀.metricInChart x y +
              complexHessian (φ ∘ ↑(chartAt (EuclideanSpace ℂ (Fin n)) x).symm) y)⁻¹ l a *
              chartCurvature (fun w ↦ ω₀.metricInChart x w +
                complexHessian (φ ∘ ↑(chartAt (EuclideanSpace ℂ (Fin n)) x).symm) w) y b q c l) +
            ∑ l, (ω₀.metricInChart x y)⁻¹ l a *
              chartCurvature (fun w ↦ ω₀.metricInChart x w) y b q c l := by
      exact hbar φ hφ x y hy a b c q
    have hmetric : c3PerturbedMetricInChart ω₀ φ x =
        (fun w ↦ ω₀.metricInChart x w +
          complexHessian (φ ∘ ↑(chartAt (EuclideanSpace ℂ (Fin n)) x).symm) w) := by
      funext w
      rfl
    have hmetricAt := congrFun hmetric y
    unfold c3TensorCovariantZ
    rw [hPartial ω₀ hφ x y hy p i j k q]
    simp_rw [hbarAt]
    rw [← hmetric, ← hmetricAt]
  have c3ConnectionLap_contracted_covariantZ_bar_curvature_difference
      (ω₀ : KahlerForm n M) {φ : M → ℝ} (hφ : ω₀.IsPotential φ)
      (x : M) (y : EuclideanSpace ℂ (Fin n))
      (hy : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
      (i j k : Fin n) :
      c3ConnectionTensorLaplacian ω₀ φ x y i j k =
        ∑ p, ∑ q, (c3PerturbedMetricInChart ω₀ φ x y)⁻¹ q p *
          c3TensorCovariantZ (c3PerturbedMetricInChart ω₀ φ x)
            (fun w a b c =>
              -c3ConnectionLapRaisedCurvature (c3PerturbedMetricInChart ω₀ φ x) w a b c q +
                c3ConnectionLapRaisedCurvature (ω₀.metricInChart x) w a b c q)
            y p i j k := by
    unfold c3ConnectionTensorLaplacian
    simp_rw [hCovariant ω₀ hφ x y hy,
      c3ConnectionLapRaisedCurvature]
  let z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x
  let gφ := c3PerturbedMetricInChart ω₀ φ x
  let g₀ := ω₀.metricInChart x
  have hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target :=
    mem_extChartAt_target x
  have hdata := c3PerturbedMetric_chart_data ω₀ hφ x
  dsimp only at hdata
  rcases hdata with ⟨hU, hgOn, hunitOn, hK⟩
  have hg : ∀ a b, ContDiffAt ℝ ∞ (fun w => gφ w a b) z := by
    intro a b
    exact (hgOn a b).contDiffAt (hU.mem_nhds hz)
  have hunit : IsUnit (gφ z) := hunitOn z hz
  have hg₀ : ∀ a b, ContDiffAt ℝ ∞ (fun w => g₀ w a b) z := by
    intro a b
    exact (ω₀.contDiffOn_metricInChart x a b).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz)
  have hunit₀ : IsUnit (g₀ z) := (ω₀.posDef_metricInChart x hz).isUnit
  have hPertLift := fun p i j q k => c3RaisedCurvature_covariantZ gφ z hg hunit p i j q k
  have hRefLift := fun p i j q k => c3ReferenceCurvature_covariantZ ω₀ x z hz p i j q k
  have hPertDiff := fun a b c q => c3RaisedCurvature_differentiableAt gφ z hg hunit a b c q
  have hRefDiff : ∀ a b c q, DifferentiableAt ℝ
      (fun w => c3RaisedReferenceCurvature ω₀ x w a b c q) z := by
    intro a b c q
    simpa only [c3RaisedReferenceCurvature, c3RaisedCurvatureInChart, g₀] using
      c3RaisedCurvature_differentiableAt g₀ z hg₀ hunit₀ a b c q
  have hRicci (i j k : Fin n) :
      (∑ p, ∑ q, ∑ l, (gφ z)⁻¹ q p * (gφ z)⁻¹ l i *
        c3CurvatureCovariantZ gφ z p j q k l) = c3RaisedRicciDerivative gφ z i j k := by
    exact c3CovariantCurvature_contract_eq_raisedRicci_of_permute gφ z hg hunit i j k
      (fun p q l => c3PerturbedCurvatureCovariantZ_permute ω₀ hφ x z hz p j q k l)
  have hComponent : ∀ i j k,
      c3ConnectionTensorLaplacian ω₀ φ x z i j k =
        c3ReferenceTensorDrift ω₀ φ x z i j k - c3RaisedRicciDerivative gφ z i j k := by
    intro i j k
    rw [c3ConnectionLap_contracted_covariantZ_bar_curvature_difference ω₀ hφ x z hz i j k]
    change (∑ p, ∑ q, (gφ z)⁻¹ q p * c3TensorCovariantZ gφ
      (fun w a b c => -c3RaisedCurvatureInChart gφ w a b c q +
        c3RaisedReferenceCurvature ω₀ x w a b c q) z p i j k) = _
    rw [c3Curvature_split_from_lifts ω₀ φ x z i j k hPertLift
      (by simpa only [c3TensorCovariantZ] using hRefLift) hPertDiff hRefDiff]
    rw [hRicci i j k]
  let T := connectionDifferenceInChart ω₀ φ x z
  have hPair :
      c3Pair gφ z (c3ConnectionTensorLaplacian ω₀ φ x z) T =
        c3Pair gφ z (c3ReferenceTensorDrift ω₀ φ x z) T -
          c3Pair gφ z (c3RaisedRicciDerivative gφ z) T := by
    unfold c3Pair
    simp_rw [hComponent]
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
  unfold c3BochnerConnectionTerm c3BochnerReferenceTerm c3BochnerRicciDerivativeTerm
  dsimp [z, gφ, T]
  exact congrArg Complex.re hPair

end KahlerForm
