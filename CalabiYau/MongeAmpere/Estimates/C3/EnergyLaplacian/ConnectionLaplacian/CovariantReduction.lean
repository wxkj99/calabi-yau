module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ConnectionLaplacian.Basic

/-!
# Conditional covariant reduction of the curvature difference

Székelyhidi, §3.3, proof of Lemma 3.9, the Bianchi calculation following
(3.15), printed p. 45. This conditional identity expresses the covariant
derivative of the curvature difference in terms of its component derivatives.

The varying curvature has a minus sign. Reference curvature is raised with
`g₀⁻¹`, while the outer contraction uses `gφ⁻¹`. The identity assumes the
connection-difference relation on an open neighborhood and the stated lift and
differentiability hypotheses.
-/

public section

open scoped Manifold ContDiff BigOperators ComplexOrder MatrixOrder

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- Split the contracted covariant derivative of the raised curvature difference,
assuming the actual/reference lifts and differentiability of both raised tensors.
No potential or chart-target hypothesis substitutes for any of these premises. -/
theorem c3Curvature_split_from_lifts
    (ω₀ : KahlerForm n M) (φ : M → ℝ) (x : M)
    (z : EuclideanSpace ℂ (Fin n)) (i j k : Fin n)
    (hPertLift : ∀ p i j q k,
      c3TensorCovariantZ (c3PerturbedMetricInChart ω₀ φ x)
          (fun w a b c => c3RaisedCurvatureInChart (c3PerturbedMetricInChart ω₀ φ x)
            w a b c q) z p i j k =
        ∑ l, (c3PerturbedMetricInChart ω₀ φ x z)⁻¹ l i *
          c3CurvatureCovariantZ (c3PerturbedMetricInChart ω₀ φ x) z p j q k l)
    (hRefLift : ∀ p i j q k,
      wirtingerDerivInChart (fun w => c3RaisedReferenceCurvature ω₀ x w i j k q) z p +
          ∑ r, christoffelInChart (fun w => ω₀.metricInChart x w) z i p r *
            c3RaisedReferenceCurvature ω₀ x z r j k q -
          ∑ r, christoffelInChart (fun w => ω₀.metricInChart x w) z r p j *
            c3RaisedReferenceCurvature ω₀ x z i r k q -
          ∑ r, christoffelInChart (fun w => ω₀.metricInChart x w) z r p k *
            c3RaisedReferenceCurvature ω₀ x z i j r q =
        ∑ l, (ω₀.metricInChart x z)⁻¹ l i *
          c3ReferenceCurvatureCovariantDerivativeInChart ω₀ x z p j q k l)
    (hPertDiff : ∀ a b c q, DifferentiableAt ℝ
      (fun w => c3RaisedCurvatureInChart (c3PerturbedMetricInChart ω₀ φ x) w a b c q) z)
    (hRefDiff : ∀ a b c q, DifferentiableAt ℝ
      (fun w => c3RaisedReferenceCurvature ω₀ x w a b c q) z) :
    ∑ p, ∑ q, (c3PerturbedMetricInChart ω₀ φ x z)⁻¹ q p *
        c3TensorCovariantZ (c3PerturbedMetricInChart ω₀ φ x)
          (fun w a b c =>
            -c3RaisedCurvatureInChart (c3PerturbedMetricInChart ω₀ φ x) w a b c q +
              c3RaisedReferenceCurvature ω₀ x w a b c q) z p i j k =
      c3ReferenceTensorDrift ω₀ φ x z i j k -
        ∑ p, ∑ q, ∑ l,
          (c3PerturbedMetricInChart ω₀ φ x z)⁻¹ q p *
            (c3PerturbedMetricInChart ω₀ φ x z)⁻¹ l i *
              c3CurvatureCovariantZ (c3PerturbedMetricInChart ω₀ φ x) z p j q k l := by
  let g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    c3PerturbedMetricInChart ω₀ φ x
  let g₀ : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w => ω₀.metricInChart x w
  let T : Fin n → Fin n → Fin n → ℂ :=
    connectionDifferenceInChart ω₀ φ x z
  have hGamma (a b c : Fin n) :
      christoffelInChart g z a b c =
        christoffelInChart g₀ z a b c + T a b c := by
    change christoffelInChart
        (fun w => ω₀.metricInChart x w +
          complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) w) z a b c =
      christoffelInChart (fun w => ω₀.metricInChart x w) z a b c +
        (christoffelInChart
            (fun w => ω₀.metricInChart x w +
              complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) w)
            z a b c -
          christoffelInChart (fun w => ω₀.metricInChart x w) z a b c)
    ring
  have hPartial (p q : Fin n) :
      wirtingerDerivInChart (fun w => -c3RaisedCurvatureInChart g w i j k q +
        c3RaisedReferenceCurvature ω₀ x w i j k q) z p =
      -wirtingerDerivInChart (fun w => c3RaisedCurvatureInChart g w i j k q) z p +
        wirtingerDerivInChart (fun w => c3RaisedReferenceCurvature ω₀ x w i j k q) z p := by
    have hpd : DifferentiableAt ℝ
        (fun w => c3RaisedCurvatureInChart g w i j k q) z := by
      simpa [g] using hPertDiff i j k q
    have hrd : DifferentiableAt ℝ
        (fun w => c3RaisedReferenceCurvature ω₀ x w i j k q) z :=
      hRefDiff i j k q
    have hfd : fderiv ℝ
        (fun w => -c3RaisedCurvatureInChart g w i j k q +
          c3RaisedReferenceCurvature ω₀ x w i j k q) z =
        -fderiv ℝ (fun w => c3RaisedCurvatureInChart g w i j k q) z +
          fderiv ℝ (fun w => c3RaisedReferenceCurvature ω₀ x w i j k q) z := by
      calc
        _ = fderiv ℝ
            ((fun w => -c3RaisedCurvatureInChart g w i j k q) +
              (fun w => c3RaisedReferenceCurvature ω₀ x w i j k q)) z := by
                congr 1
        _ = fderiv ℝ (fun w => -c3RaisedCurvatureInChart g w i j k q) z +
              fderiv ℝ (fun w => c3RaisedReferenceCurvature ω₀ x w i j k q) z :=
                fderiv_add hpd.neg hrd
        _ = _ := by rw [fderiv_fun_neg]
    unfold wirtingerDerivInChart
    rw [hfd]
    simp only [add_apply, neg_apply]
    ring
  have hlin (p q : Fin n) :
      c3TensorCovariantZ g
          (fun w a b c => -c3RaisedCurvatureInChart g w a b c q +
            c3RaisedReferenceCurvature ω₀ x w a b c q) z p i j k =
        -c3TensorCovariantZ g
          (fun w a b c => c3RaisedCurvatureInChart g w a b c q) z p i j k +
        c3TensorCovariantZ g
          (fun w a b c => c3RaisedReferenceCurvature ω₀ x w a b c q) z p i j k := by
    unfold c3TensorCovariantZ
    rw [hPartial]
    simp only [mul_add, mul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    ring
  have hPL (p q : Fin n) :
      c3TensorCovariantZ g
          (fun w a b c => c3RaisedCurvatureInChart g w a b c q) z p i j k =
        ∑ l, (g z)⁻¹ l i * c3CurvatureCovariantZ g z p j q k l := by
    simpa [g] using hPertLift p i j q k
  have hRefCov (p q : Fin n) :
      c3TensorCovariantZ g
          (fun w a b c => c3RaisedReferenceCurvature ω₀ x w a b c q) z p i j k =
        (∑ l, (g₀ z)⁻¹ l i *
          c3ReferenceCurvatureCovariantDerivativeInChart ω₀ x z p j q k l) +
        (∑ r, T i p r * c3RaisedReferenceCurvature ω₀ x z r j k q) -
        (∑ r, T r p j * c3RaisedReferenceCurvature ω₀ x z i r k q) -
        (∑ r, T r p k * c3RaisedReferenceCurvature ω₀ x z i j r q) := by
    unfold c3TensorCovariantZ
    simp_rw [hGamma]
    dsimp [g₀]
    simp only [add_mul, Finset.sum_add_distrib]
    linear_combination hRefLift p i j q k
  change ∑ p, ∑ q, (g z)⁻¹ q p *
      c3TensorCovariantZ g
        (fun w a b c => -c3RaisedCurvatureInChart g w a b c q +
          c3RaisedReferenceCurvature ω₀ x w a b c q) z p i j k =
    c3ReferenceTensorDrift ω₀ φ x z i j k -
      ∑ p, ∑ q, ∑ l, (g z)⁻¹ q p * (g z)⁻¹ l i *
        c3CurvatureCovariantZ g z p j q k l
  simp_rw [hlin, hPL, hRefCov]
  unfold c3ReferenceTensorDrift
  dsimp [T]
  simp only [g, g₀, mul_add, mul_sub, mul_neg, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.mul_sum]
  simp only [Finset.sum_neg_distrib]
  ring_nf

end KahlerForm
