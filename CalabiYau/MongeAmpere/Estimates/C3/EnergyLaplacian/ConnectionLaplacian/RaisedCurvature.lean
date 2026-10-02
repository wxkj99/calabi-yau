module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ConnectionLaplacian.Basic
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ConnectionLaplacian.MetricDerivatives
import CalabiYau.Geometry.Kahler.Curvature.Chart.DerivativeRules
import CalabiYau.Geometry.Kahler.Curvature.Chart.MixedDerivatives

/-!
# Covariant raising of chart curvature

Székelyhidi, §3.3, proof of Lemma 3.9, the Bianchi calculation following
(3.15), printed p. 45. The fixed antiholomorphic index is `q`; lift arguments
are `(p,i,j,q,k)`.
Reference curvature is raised with the reference metric, never the perturbed one.
Generic entrywise smoothness and invertibility are explicit hypotheses.
-/

public section

open scoped Manifold ContDiff BigOperators ComplexOrder MatrixOrder

namespace KahlerForm

variable {n : ℕ}

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

private noncomputable def liftRaisedCurvature
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (i j k q : Fin n) : ℂ :=
  c3RaisedCurvatureInChart g z i j k q

private theorem raisedCurvature_rfl
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (i j k q : Fin n) :
    c3RaisedCurvatureInChart g z i j k q = liftRaisedCurvature g z i j k q := rfl

private noncomputable def actualD
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (p j q k l : Fin n) : ℂ :=
  c3CurvatureCovariantZ g z p j q k l

private theorem curvatureCovariantZ_rfl
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (p j q k l : Fin n) :
    c3CurvatureCovariantZ g z p j q k l = actualD g z p j q k l := rfl

private theorem lift_weighted_swap
    (A B : Fin n → ℂ) (C : Fin n → Fin n → ℂ) :
    (∑ r, B r * (∑ l, A l * C l r)) =
      ∑ l, A l * (∑ r, B r * C l r) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro r _
  ring

private theorem lift_neg_weighted_swap
    (A B : Fin n → ℂ) (C : Fin n → Fin n → ℂ) :
    (∑ l, (-(∑ r, B r * C l r)) * A l) =
      -(∑ r, B r * (∑ l, C l r * A l)) := by
  simp only [neg_mul, Finset.sum_mul, Finset.mul_sum, Finset.sum_neg_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro l _
  ring

private theorem lift_partial_raised
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hg : ∀ a b, ContDiffAt ℝ ∞ (fun w => g w a b) z)
    (hunit : IsUnit (g z)) (p i j q k : Fin n) :
    c3PartialZ (fun w => liftRaisedCurvature g w i j k q) z p =
      ∑ l, (c3PartialZ (fun w => (g w)⁻¹ l i) z p *
          chartCurvature g z j q k l +
        (g z)⁻¹ l i * c3PartialZ (fun w => chartCurvature g w j q k l) z p) := by
  have hInv (a b : Fin n) : DifferentiableAt ℝ (fun w => (g w)⁻¹ a b) z :=
    chartInv_differentiableAt (fun a b => (hg a b).of_le (by norm_num)) hunit a b
  have hR (l : Fin n) := c3Curvature_differentiableAt g z hg hunit j q k l
  have hProd (l : Fin n) : DifferentiableAt ℝ
      (fun w => (g w)⁻¹ l i * chartCurvature g w j q k l) z :=
    (hInv l i).mul (hR l)
  change chartPartialZComplex
    (fun w => ∑ l, (g w)⁻¹ l i * chartCurvature g w j q k l) z p = _
  rw [chartPartialZComplex_sum (fun l w => (g w)⁻¹ l i * chartCurvature g w j q k l)
    z p hProd]
  apply Finset.sum_congr rfl
  intro l _
  exact chartPartialZComplex_mul (hInv l i) (hR l) p

private theorem actual_raised_covariant_lift
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hg : ∀ a b, ContDiffAt ℝ ∞ (fun w => g w a b) z)
    (hunit : IsUnit (g z)) (p i j q k : Fin n) :
    c3TensorCovariantZ g
      (fun w a b c => liftRaisedCurvature g w a b c q) z p i j k =
      ∑ l, (g z)⁻¹ l i * actualD g z p j q k l := by
  have hd (a b : Fin n) : DifferentiableAt ℝ (fun w => g w a b) z :=
    (hg a b).differentiableAt (by norm_num)
  have hUpper := lift_neg_weighted_swap
    (fun l => chartCurvature g z j q k l)
    (fun r => c3ChristoffelInChart g z i p r)
    (fun l r => (g z)⁻¹ l r)
  have hLowerJ := lift_weighted_swap
    (fun l => (g z)⁻¹ l i)
    (fun r => c3ChristoffelInChart g z r p j)
    (fun l r => chartCurvature g z r q k l)
  have hLowerK := lift_weighted_swap
    (fun l => (g z)⁻¹ l i)
    (fun r => c3ChristoffelInChart g z r p k)
    (fun l r => chartCurvature g z j q r l)
  unfold c3TensorCovariantZ
  rw [lift_partial_raised g z hg hunit p i j q k]
  simp_rw [c3PartialZ_inverse_eq_christoffel g z hd hunit]
  unfold liftRaisedCurvature c3RaisedCurvatureInChart
  rw [Finset.sum_add_distrib, hUpper, hLowerJ, hLowerK]
  simp only [actualD, c3CurvatureCovariantZ, mul_sub, Finset.sum_sub_distrib]
  ring

theorem c3RaisedCurvature_covariantZ
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hg : ∀ a b, ContDiffAt ℝ ∞ (fun w => g w a b) z)
    (hunit : IsUnit (g z)) (p i j q k : Fin n) :
    c3TensorCovariantZ g
      (fun w a b c => c3RaisedCurvatureInChart g w a b c q) z p i j k =
      ∑ l, (g z)⁻¹ l i * c3CurvatureCovariantZ g z p j q k l := by
  change c3TensorCovariantZ g
      (fun w a b c => liftRaisedCurvature g w a b c q) z p i j k =
    ∑ l, (g z)⁻¹ l i * actualD g z p j q k l
  exact actual_raised_covariant_lift g z hg hunit p i j q k

theorem c3RaisedCurvature_differentiableAt
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hg : ∀ a b, ContDiffAt ℝ ∞ (fun w => g w a b) z)
    (hunit : IsUnit (g z)) (i j k q : Fin n) :
    DifferentiableAt ℝ (fun w => c3RaisedCurvatureInChart g w i j k q) z := by
  have hInv (a b : Fin n) : DifferentiableAt ℝ (fun w => (g w)⁻¹ a b) z :=
    chartInv_differentiableAt (fun a b => (hg a b).of_le (by norm_num)) hunit a b
  have hR (l : Fin n) : DifferentiableAt ℝ (fun w => chartCurvature g w j q k l) z :=
    c3Curvature_differentiableAt g z hg hunit j q k l
  change DifferentiableAt ℝ
    (fun w => ∑ l, (g w)⁻¹ l i * chartCurvature g w j q k l) z
  apply DifferentiableAt.fun_sum
  intro l _
  exact (hInv l i).mul (hR l)

omit [T2Space M] [CompactSpace M] in
theorem c3ReferenceCurvature_covariantZ
    (ω₀ : KahlerForm n M) (x : M) (z : EuclideanSpace ℂ (Fin n))
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (p i j q k : Fin n) :
    c3TensorCovariantZ (fun w => ω₀.metricInChart x w)
      (fun w a b c => c3RaisedReferenceCurvature ω₀ x w a b c q) z p i j k =
      ∑ l, (ω₀.metricInChart x z)⁻¹ l i *
        c3ReferenceCurvatureCovariantDerivativeInChart ω₀ x z p j q k l := by
  have hg (a b : Fin n) :
      ContDiffAt ℝ ∞ (fun w => ω₀.metricInChart x w a b) z :=
    (ω₀.contDiffOn_metricInChart x a b).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz)
  simpa only [c3RaisedReferenceCurvature, c3ReferenceCurvatureCovariantDerivativeInChart,
    liftRaisedCurvature, actualD, c3RaisedCurvatureInChart, c3CurvatureCovariantZ] using
    (actual_raised_covariant_lift (fun w => ω₀.metricInChart x w) z hg
      (ω₀.posDef_metricInChart x hz).isUnit p i j q k)

end KahlerForm
