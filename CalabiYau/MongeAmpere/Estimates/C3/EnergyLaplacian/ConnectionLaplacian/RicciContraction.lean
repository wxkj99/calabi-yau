module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ConnectionLaplacian.Basic
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ConnectionLaplacian.MetricDerivatives
import CalabiYau.Geometry.Kahler.Curvature.Chart.DerivativeRules

/-!
# Ricci trace and the weighted differential Bianchi contraction

Székelyhidi, §3.3, proof of Lemma 3.9, the Bianchi calculation following
(3.15), printed p. 45. The Ricci trace uses inverse entries `(l,i)` and `(q,p)`
and `D[k,p,q,j,l]`.
The weighted bridge keeps the needed actual D permutation as an explicit hypothesis.
No symmetry of inverse matrix entries is used in the finite sum reordering.
-/

public section

open scoped Manifold ContDiff BigOperators ComplexOrder MatrixOrder

namespace KahlerForm

variable {n : ℕ}

private theorem ricci_covariant_trace_component
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hg : ∀ a b, ContDiffAt ℝ ∞ (fun w => g w a b) z)
    (hunit : IsUnit (g z)) (j k l : Fin n) :
    wirtingerDerivInChart (fun w => c3RicciInChart g w j l) z k -
        ∑ r, christoffelInChart g z r k j * c3RicciInChart g z r l =
      ∑ p, ∑ q, (g z)⁻¹ q p * c3CurvatureCovariantZ g z k p q j l := by
  let hInv (a b : Fin n) : DifferentiableAt ℝ (fun w => (g w)⁻¹ a b) z :=
    chartInv_differentiableAt (fun a b => (hg a b).of_le (by norm_num)) hunit a b
  have hCurv (p q a b : Fin n) :
      DifferentiableAt ℝ (fun w => chartCurvature g w p q a b) z :=
    c3Curvature_differentiableAt g z hg hunit p q a b
  have hTerm (p q : Fin n) : DifferentiableAt ℝ
      (fun w => (g w)⁻¹ q p * chartCurvature g w p q j l) z :=
    (hInv q p).mul (hCurv p q j l)
  have hInner (p : Fin n) : DifferentiableAt ℝ
      (fun w => ∑ q, (g w)⁻¹ q p * chartCurvature g w p q j l) z :=
    DifferentiableAt.fun_sum (u := Finset.univ) (fun q _ => hTerm p q)
  have hRicciDeriv :
      wirtingerDerivInChart (fun w => ∑ p, ∑ q,
        (g w)⁻¹ q p * chartCurvature g w p q j l) z k =
      ∑ p, ∑ q,
        (wirtingerDerivInChart (fun w => (g w)⁻¹ q p) z k * chartCurvature g z p q j l +
          (g z)⁻¹ q p * wirtingerDerivInChart (fun w => chartCurvature g w p q j l) z k) := by
    change chartPartialZComplex (fun w => ∑ p, ∑ q,
      (g w)⁻¹ q p * chartCurvature g w p q j l) z k = _
    rw [chartPartialZComplex_sum (fun p w =>
      ∑ q, (g w)⁻¹ q p * chartCurvature g w p q j l) z k hInner]
    apply Finset.sum_congr rfl
    intro p hp
    rw [chartPartialZComplex_sum (fun q w =>
      (g w)⁻¹ q p * chartCurvature g w p q j l) z k (hTerm p)]
    apply Finset.sum_congr rfl
    intro q hq
    exact chartPartialZComplex_mul (hInv q p) (hCurv p q j l) k
  have hInvGamma (q p : Fin n) :
      wirtingerDerivInChart (fun w => (g w)⁻¹ q p) z k =
        -∑ r, christoffelInChart g z p k r * (g z)⁻¹ q r := by
    simpa only [wirtingerDerivInChart] using wirtingerDerivInChart_inverse_eq_christoffel g z
      (fun a b => (hg a b).differentiableAt (by norm_num)) hunit q p k
  have hsum3 (F : Fin n → Fin n → Fin n → ℂ) :
      (∑ r, ∑ q, ∑ p, F r q p) = ∑ p, ∑ q, ∑ r, F r q p := by
    rw [Finset.sum_comm]
    conv_lhs => arg 2; intro q; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  have hsum3' (F : Fin n → Fin n → Fin n → ℂ) :
      (∑ r, ∑ p, ∑ q, F r p q) = ∑ p, ∑ q, ∑ r, F r p q := by
    conv_lhs => arg 2; intro r; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; intro q; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  have htraceInv :
      (∑ p, ∑ q, wirtingerDerivInChart (fun w => (g w)⁻¹ q p) z k *
        chartCurvature g z p q j l) =
        -(∑ p, ∑ q, ∑ r, (g z)⁻¹ q p *
          christoffelInChart g z r k p * chartCurvature g z r q j l) := by
    simp_rw [hInvGamma]
    simp only [Finset.sum_mul, neg_mul, Finset.sum_neg_distrib]
    rw [← hsum3 (fun r q p => (g z)⁻¹ q p *
      christoffelInChart g z r k p * chartCurvature g z r q j l)]
    congr 1
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
      Finset.sum_congr rfl fun r _ => ?_
    ring
  have htraceMetric :
      (∑ r, christoffelInChart g z r k j *
        ∑ p, ∑ q, (g z)⁻¹ q p * chartCurvature g z p q r l) =
      ∑ p, ∑ q, (g z)⁻¹ q p *
        ∑ r, christoffelInChart g z r k j * chartCurvature g z p q r l := by
    simp only [Finset.mul_sum]
    rw [hsum3' (fun r p q => christoffelInChart g z r k j *
      ((g z)⁻¹ q p * chartCurvature g z p q r l))]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro r hr
    ring
  simp only [c3RicciInChart, c3CurvatureCovariantZ]
  rw [hRicciDeriv]
  simp only [Finset.sum_add_distrib]
  rw [htraceInv, htraceMetric]
  simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  ring_nf

theorem c3RaisedRicciDerivative_eq_contracted_covariantCurvature
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hg : ∀ a b, ContDiffAt ℝ ∞ (fun w => g w a b) z)
    (hunit : IsUnit (g z)) (i j k : Fin n) :
    c3RaisedRicciDerivative g z i j k =
      ∑ l, ∑ p, ∑ q, (g z)⁻¹ l i * (g z)⁻¹ q p *
        c3CurvatureCovariantZ g z k p q j l := by
  simp only [c3RaisedRicciDerivative]
  apply Finset.sum_congr rfl
  intro l hl
  rw [ricci_covariant_trace_component g z hg hunit j k l]
  simp only [Finset.mul_sum]
  ring_nf

theorem c3CovariantCurvature_contract_eq_raisedRicci_of_permute
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hg : ∀ a b, ContDiffAt ℝ ∞ (fun w => g w a b) z)
    (hunit : IsUnit (g z)) (i j k : Fin n)
    (hSymm : ∀ p q l,
      c3CurvatureCovariantZ g z p j q k l = c3CurvatureCovariantZ g z k p q j l) :
    (∑ p, ∑ q, ∑ l, (g z)⁻¹ q p * (g z)⁻¹ l i *
      c3CurvatureCovariantZ g z p j q k l) = c3RaisedRicciDerivative g z i j k := by
  calc
    (∑ p, ∑ q, ∑ l, (g z)⁻¹ q p * (g z)⁻¹ l i *
        c3CurvatureCovariantZ g z p j q k l) =
      ∑ p, ∑ q, ∑ l, (g z)⁻¹ q p * (g z)⁻¹ l i *
        c3CurvatureCovariantZ g z k p q j l := by
          simp_rw [hSymm]
    _ = ∑ l, (g z)⁻¹ l i *
        ∑ p, ∑ q, (g z)⁻¹ q p * c3CurvatureCovariantZ g z k p q j l := by
          calc
            _ = ∑ p, ∑ q, ∑ l, (g z)⁻¹ l i *
                ((g z)⁻¹ q p * c3CurvatureCovariantZ g z k p q j l) := by
                  apply Finset.sum_congr rfl
                  intro p hp
                  apply Finset.sum_congr rfl
                  intro q hq
                  apply Finset.sum_congr rfl
                  intro l hl
                  ring
            _ = ∑ l, ∑ p, ∑ q, (g z)⁻¹ l i *
                ((g z)⁻¹ q p * c3CurvatureCovariantZ g z k p q j l) := by
                  have hsum (F : Fin n → Fin n → Fin n → ℂ) :
                      (∑ p, ∑ q, ∑ l, F p q l) = ∑ l, ∑ p, ∑ q, F p q l := by
                    conv_lhs => arg 2; intro p; rw [Finset.sum_comm]
                    rw [Finset.sum_comm]
                  exact hsum _
            _ = ∑ l, (g z)⁻¹ l i *
                ∑ p, ∑ q, (g z)⁻¹ q p * c3CurvatureCovariantZ g z k p q j l := by
                  simp only [Finset.mul_sum]
    _ = c3RaisedRicciDerivative g z i j k := by
      rw [c3RaisedRicciDerivative_eq_contracted_covariantCurvature g z hg hunit i j k]
      simp only [Finset.mul_sum]
      ring_nf

end KahlerForm
