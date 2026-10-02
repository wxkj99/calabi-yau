module

public import CalabiYau.Geometry.Kahler.Connection.MetricJet
public import CalabiYau.Geometry.Kahler.Connection.Contraction

/-!
# Nonlinear holomorphic coordinate change for the metric connection

The single-metric law is `Γ' = B Γ A A + B ∂A`, where `A` is the
forward complex Jacobian and `B` its inverse. The inhomogeneous term is
independent of the metric, so it cancels in the difference of two connections.

Both the first-jet calculation and its finite inverse-metric contraction are
explicit dependencies. All regularity and metric equalities are local to open
coordinate sets; no extension to a globally smooth metric is assumed.

Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §1.4,
pp. 10–11, and §3.3, equation (3.13), p. 44.
-/

public section

open scoped BigOperators ContDiff

namespace KahlerForm

/-- The nonlinear single-metric holomorphic Christoffel transition law. The
conjugate metric column contracts with inverse `[l,i]`, and the correction
`B ∂A` has a plus sign. The metric entries need only be real-smooth. -/
theorem chartChristoffel_transition {n : ℕ}
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
    (∑ l, (g' z)⁻¹ l i * chartPartialZComplex (fun w => g' w k l) z j) =
      (∑ p, ∑ q, ∑ r, B i p * A z q j * A z r k *
        (∑ s, (g (F z))⁻¹ s p * chartPartialZComplex (fun w => g w r s) (F z) q)) +
      ∑ p, B i p * chartPartialZComplex (fun w => A w p k) z j := by
  dsimp only
  simp_rw [chartPartialZComplex_metric_pullback F g g' U V hU hV hF hg hFV
    hmetric z hz]
  rw [hmetric z hz]
  exact chartChristoffel_pullback_contraction
    (EuclideanSpace.clmMatrix (fderiv ℂ F z)) B (g (F z))
    (fun q r s => chartPartialZComplex (fun w => g w r s) (F z) q)
    (fun j p k => chartPartialZComplex
      (fun w => EuclideanSpace.clmMatrix (fderiv ℂ F w) p k) z j)
    hAB hBA hdet i j k

end KahlerForm
