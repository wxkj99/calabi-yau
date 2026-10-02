module

public import CalabiYau.MongeAmpere.Estimates.C3.CalabiEnergy.Basic
import CalabiYau.MongeAmpere.Estimates.C3.CalabiEnergy.ChartInvariance.MetricJet
import CalabiYau.MongeAmpere.Estimates.C3.CalabiEnergy.ChartInvariance.Contraction

@[expose] public section

open scoped BigOperators Manifold ContDiff ComplexOrder

namespace KahlerForm.ChartInvariance

/-- The nonlinear single-metric holomorphic Christoffel transition law. The
conjugate metric column contracts with inverse `[l,i]`, and the correction
`B ∂A` has a plus sign. The metric entries need only be real-smooth. -/
theorem calabiEnergy_chartChristoffel_transition {n : ℕ}
    (F : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (g g' : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (U V : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U) (hV : IsOpen V)
    (hF : ContDiffOn ℂ 2 F U)
    (hg : ∀ a b, ContDiffOn ℝ 1 (fun w => g w a b) V)
    (hFV : Set.MapsTo F U V)
    (hmetric : ∀ w ∈ U, g' w =
      (EuclideanSpace.clmMatrix (fderiv ℂ F w)).transpose * g (F w) *
        (EuclideanSpace.clmMatrix (fderiv ℂ F w)).map star)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U)
    (B : Matrix (Fin n) (Fin n) ℂ)
    (hAB : EuclideanSpace.clmMatrix (fderiv ℂ F z) * B = 1)
    (hBA : B * EuclideanSpace.clmMatrix (fderiv ℂ F z) = 1)
    (hdet : IsUnit (g (F z)).det) (i j k : Fin n) :
    let A := fun w => EuclideanSpace.clmMatrix (fderiv ℂ F w)
    (∑ l, (g' z)⁻¹ l i * wirtingerDerivInChart (fun w => g' w k l) z j) =
      (∑ p, ∑ q, ∑ r, B i p * A z q j * A z r k *
        (∑ s, (g (F z))⁻¹ s p * wirtingerDerivInChart (fun w => g w r s) (F z) q)) +
      ∑ p, B i p * wirtingerDerivInChart (fun w => A w p k) z j := by
  dsimp only
  simp_rw [calabiEnergy_c3PartialZ_metric_pullback F g g' U V hU hV hF hg hFV
    hmetric z hz]
  rw [hmetric z hz]
  exact calabiEnergy_chartChristoffel_pullback_contraction
    (EuclideanSpace.clmMatrix (fderiv ℂ F z)) B (g (F z))
    (fun q r s => wirtingerDerivInChart (fun w => g w r s) (F z) q)
    (fun j p k => wirtingerDerivInChart
      (fun w => EuclideanSpace.clmMatrix (fderiv ℂ F w) p k) z j)
    hAB hBA hdet i j k

/-- The common nonlinear correction cancels for two connections. Thus their
difference has the homogeneous `(1,2)` tensor law, with inverse Jacobian in
the output slot and forward Jacobian in each input slot. -/
theorem calabiEnergy_connectionDifference_transition_generic {n : ℕ}
    (F : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (g h g' h' : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (U V : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U) (hV : IsOpen V)
    (hF : ContDiffOn ℂ 2 F U)
    (hg : ∀ a b, ContDiffOn ℝ 1 (fun w => g w a b) V)
    (hh : ∀ a b, ContDiffOn ℝ 1 (fun w => h w a b) V)
    (hFV : Set.MapsTo F U V)
    (hgmetric : ∀ w ∈ U, g' w =
      (EuclideanSpace.clmMatrix (fderiv ℂ F w)).transpose * g (F w) *
        (EuclideanSpace.clmMatrix (fderiv ℂ F w)).map star)
    (hhmetric : ∀ w ∈ U, h' w =
      (EuclideanSpace.clmMatrix (fderiv ℂ F w)).transpose * h (F w) *
        (EuclideanSpace.clmMatrix (fderiv ℂ F w)).map star)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U)
    (B : Matrix (Fin n) (Fin n) ℂ)
    (hAB : EuclideanSpace.clmMatrix (fderiv ℂ F z) * B = 1)
    (hBA : B * EuclideanSpace.clmMatrix (fderiv ℂ F z) = 1)
    (hgdet : IsUnit (g (F z)).det) (hhdet : IsUnit (h (F z)).det)
    (i j k : Fin n) :
    let A := EuclideanSpace.clmMatrix (fderiv ℂ F z)
    (∑ l, (g' z)⁻¹ l i * wirtingerDerivInChart (fun w => g' w k l) z j) -
        (∑ l, (h' z)⁻¹ l i * wirtingerDerivInChart (fun w => h' w k l) z j) =
      ∑ p, ∑ q, ∑ r, B i p * A q j * A r k *
        ((∑ s, (g (F z))⁻¹ s p * wirtingerDerivInChart (fun w => g w r s) (F z) q) -
          ∑ s, (h (F z))⁻¹ s p * wirtingerDerivInChart (fun w => h w r s) (F z) q) := by
  dsimp only
  rw [calabiEnergy_chartChristoffel_transition F g g' U V hU hV hF hg hFV hgmetric z hz
    B hAB hBA hgdet i j k,
    calabiEnergy_chartChristoffel_transition F h h' U V hU hV hF hh hFV hhmetric z hz
    B hAB hBA hhdet i j k]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  ring

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

omit [T2Space M] [CompactSpace M] in
theorem calabiEnergy_c3Christoffel_perturb
    (ω₀ : KahlerForm n M) {φ : M → ℝ} (hφ : ω₀.IsPotential φ)
    (x : M) (z : EuclideanSpace ℂ (Fin n))
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (i j k : Fin n) :
    christoffelInChart
      (fun w ↦ ω₀.metricInChart x w +
        complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) w)
      z i j k =
    christoffelInChart (fun w ↦ (ω₀.perturb φ hφ).metricInChart x w) z i j k := by
  let g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w ↦ ω₀.metricInChart x w +
      complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) w
  let gφ : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w ↦ (ω₀.perturb φ hφ).metricInChart x w
  have hnear : g =ᶠ[nhds z] gφ := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds hz] with w hw
    exact (KahlerForm.metricInChart_perturb hφ x hw).symm
  have hvalue : g z = gφ z :=
    (KahlerForm.metricInChart_perturb hφ x hz).symm
  have hjet (a b p : Fin n) :
      wirtingerDerivInChart (fun w ↦ g w a b) z p = wirtingerDerivInChart (fun w ↦ gφ w a b) z p := by
    have hentry : (fun w ↦ g w a b) =ᶠ[nhds z] (fun w ↦ gφ w a b) :=
      hnear.mono fun w hw ↦ congrArg (fun G : Matrix (Fin n) (Fin n) ℂ ↦ G a b) hw
    have hderiv : fderiv ℝ (fun w ↦ g w a b) z =
        fderiv ℝ (fun w ↦ gφ w a b) z := hentry.fderiv_eq
    simp only [wirtingerDerivInChart, hderiv]
  unfold christoffelInChart
  dsimp only [g, gφ] at hvalue hjet ⊢
  rw [hvalue]
  apply Finset.sum_congr rfl
  intro l hl
  rw [hjet k l j]

end KahlerForm.ChartInvariance
