module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ConnectionLaplacian.FiniteJets
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ConnectionLaplacian.MetricDerivatives
import CalabiYau.Geometry.Kahler.Curvature.Chart.DerivativeRules
import CalabiYau.Geometry.Kahler.Curvature.Chart.MixedDerivatives

/-!
# Coordinate curvature derivative as a finite jet expression

Székelyhidi, §3.3, proof of Lemma 3.9, Bianchi calculation following
(3.15), printed p. 45.

The first identity requires a smooth invertible metric on an open neighborhood.
The second is conditional only on that identity. Neither assumes Hermitian or
Kähler symmetry. The holomorphic covariant derivative has exactly two lower-slot
Christoffel corrections; its finite decomposition is `-W + PureZZ + Mixed - Quartic`.
-/

public section

open scoped Manifold ContDiff BigOperators ComplexOrder MatrixOrder

namespace KahlerForm

variable {n : ℕ}

theorem c3Curvature_partialZ_eq_jet
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (hg : ∀ a b, ContDiffOn ℝ ∞ (fun w => g w a b) U)
    (hunit : ∀ w ∈ U, IsUnit (g w))
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U)
    (p j q k l : Fin n) :
    chartPartialZComplex (fun w => chartCurvature g w j q k l) z p =
      c3JetCurvatureDerivative (g z)⁻¹ (c3MetricJetZ g z) (c3MetricJetBar g z)
        (c3MetricJetZBar g z) (c3MetricJetZZ g z) (c3MetricJetZZBar g z) p j q k l := by
  have hAdd (F G : EuclideanSpace ℂ (Fin n) → ℂ)
      (x : EuclideanSpace ℂ (Fin n)) (r : Fin n)
      (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
      chartPartialZComplex (fun w => F w + G w) x r =
        chartPartialZComplex F x r + chartPartialZComplex G x r := by
    unfold chartPartialZComplex
    rw [fderiv_fun_add hF hG]
    simp only [_root_.add_apply]
    ring
  have hGAt (a b : Fin n) : ContDiffAt ℝ ∞ (fun w => g w a b) z :=
    (hg a b z hz).contDiffAt (hU.mem_nhds hz)
  have hInv (a b : Fin n) : DifferentiableAt ℝ (fun w => (g w)⁻¹ a b) z :=
    chartInv_differentiableAt (fun a b => (hGAt a b).of_le (by norm_num))
      (hunit z hz) a b
  have hZAt (a b : Fin n) (r : Fin n) :
      ContDiffAt ℝ ∞ (fun w => chartPartialZComplex (fun v => g v a b) w r) z :=
    chartPartialZComplex_contDiffAt _ _ (hGAt a b) r
  have hBarAt (a b : Fin n) (r : Fin n) :
      ContDiffAt ℝ ∞ (fun w => chartPartialBarComplex (fun v => g v a b) w r) z :=
    c3ChartPartialBar_contDiffAt _ _ (hGAt a b) r
  have hZdiff (a b r : Fin n) :
      DifferentiableAt ℝ (fun w => chartPartialZComplex (fun v => g v a b) w r) z :=
    (hZAt a b r).differentiableAt (by norm_num)
  have hBardiff (a b r : Fin n) :
      DifferentiableAt ℝ (fun w => chartPartialBarComplex (fun v => g v a b) w r) z :=
    (hBarAt a b r).differentiableAt (by norm_num)
  let A : EuclideanSpace ℂ (Fin n) → ℂ := fun w =>
    chartPartialZComplex (fun v => chartPartialBarComplex (fun u => g u k l) v q) w j
  let T : Fin n → Fin n → EuclideanSpace ℂ (Fin n) → ℂ := fun a b w =>
    ((g w)⁻¹ b a * chartPartialZComplex (fun v => g v k b) w j) *
      chartPartialBarComplex (fun v => g v a l) w q
  have hAAt : ContDiffAt ℝ ∞ A z := by
    dsimp [A]
    exact chartPartialZComplex_contDiffAt _ _ (hBarAt k l q) j
  have hAdiff : DifferentiableAt ℝ A z := hAAt.differentiableAt (by norm_num)
  have hTermDiff (a b : Fin n) : DifferentiableAt ℝ (T a b) z := by
    dsimp [T]
    exact ((hInv b a).mul (hZdiff k b j)).mul (hBardiff a l q)
  have hSumBDiff (a : Fin n) : DifferentiableAt ℝ (fun w => ∑ b, T a b w) z :=
    DifferentiableAt.fun_sum (fun b _ => hTermDiff a b)
  have hSumADiff : DifferentiableAt ℝ (fun w => ∑ a, ∑ b, T a b w) z :=
    DifferentiableAt.fun_sum (fun a _ => hSumBDiff a)
  have hSumDerivative :
      chartPartialZComplex (fun w => ∑ a, ∑ b, T a b w) z p =
        ∑ a, ∑ b, chartPartialZComplex (T a b) z p := by
    rw [chartPartialZComplex_sum (fun a w => ∑ b, T a b w) z p
      (fun a => hSumBDiff a)]
    apply Finset.sum_congr rfl
    intro a ha
    exact chartPartialZComplex_sum (fun b w => T a b w) z p (fun b => hTermDiff a b)
  have hTermDerivative (a b : Fin n) :
      chartPartialZComplex (T a b) z p =
        (chartPartialZComplex (fun w => (g w)⁻¹ b a) z p *
            chartPartialZComplex (fun w => g w k b) z j +
          (g z)⁻¹ b a *
            chartPartialZComplex (fun w => chartPartialZComplex (fun v => g v k b) w j) z p) *
          chartPartialBarComplex (fun v => g v a l) z q +
        ((g z)⁻¹ b a * chartPartialZComplex (fun w => g w k b) z j) *
          chartPartialZComplex (fun w => chartPartialBarComplex (fun v => g v a l) w q) z p := by
    dsimp [T]
    calc
      chartPartialZComplex
          (fun w => ((g w)⁻¹ b a * chartPartialZComplex (fun v => g v k b) w j) *
            chartPartialBarComplex (fun v => g v a l) w q) z p =
          chartPartialZComplex
              (fun w => (g w)⁻¹ b a * chartPartialZComplex (fun v => g v k b) w j) z p *
            chartPartialBarComplex (fun v => g v a l) z q +
          ((g z)⁻¹ b a * chartPartialZComplex (fun v => g v k b) z j) *
            chartPartialZComplex (fun w => chartPartialBarComplex (fun v => g v a l) w q) z p := by
          exact chartPartialZComplex_mul
            ((hInv b a).mul (hZdiff k b j)) (hBardiff a l q) p
      _ = _ := by
          rw [chartPartialZComplex_mul (hInv b a) (hZdiff k b j) p]
  have hNegDerivative :
      chartPartialZComplex (fun w => -A w) z p = -chartPartialZComplex A z p := by
    have hfun : (fun w => -A w) = fun w => (-1 : ℂ) * A w := by
      funext w
      ring
    rw [hfun, chartPartialZComplex_const_mul (-1) A z p hAdiff]
    ring
  have hInverseDerivative (a b : Fin n) :
      chartPartialZComplex (fun w => (g w)⁻¹ b a) z p =
        -∑ c, ∑ d, (g z)⁻¹ b c * chartPartialZComplex (fun w => g w c d) z p *
          (g z)⁻¹ d a := by
    exact c3ChartPartialZ_inverse_entry_on g U hU hg hunit z hz b a p
  have hCurvatureFun :
      (fun w => chartCurvature g w j q k l) =
        fun w => -A w + ∑ a, ∑ b, T a b w := by
    rfl
  rw [hCurvatureFun]
  rw [hAdd (fun w => -A w) (fun w => ∑ a, ∑ b, T a b w)
    z p (by simpa [A] using hAdiff) hSumADiff, hNegDerivative, hSumDerivative]
  simp_rw [hTermDerivative, hInverseDerivative]
  dsimp only [A, c3JetCurvatureDerivative, c3MetricJetZ, c3MetricJetBar,
    c3MetricJetZBar, c3MetricJetZZ, c3MetricJetZZBar]
  rw [add_left_cancel_iff]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem c3CurvatureCovariantZ_eq_jet_of_expansion
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hExpand : ∀ p j q k l,
      chartPartialZComplex (fun w => chartCurvature g w j q k l) z p =
        c3JetCurvatureDerivative (g z)⁻¹ (c3MetricJetZ g z) (c3MetricJetBar g z)
          (c3MetricJetZBar g z) (c3MetricJetZZ g z) (c3MetricJetZZBar g z) p j q k l)
    (p j q k l : Fin n) :
    c3CurvatureCovariantZ g z p j q k l =
      c3JetCovariantCurvature (g z)⁻¹ (c3MetricJetZ g z) (c3MetricJetBar g z)
        (c3MetricJetZBar g z) (c3MetricJetZZ g z) (c3MetricJetZZBar g z) p j q k l := by
  change
    (wirtingerDerivInChart (fun w => chartCurvature g w j q k l) z p -
      ∑ r, christoffelInChart g z r p j * chartCurvature g z r q k l -
      ∑ r, christoffelInChart g z r p k * chartCurvature g z j q r l) =
    (c3JetCurvatureDerivative (g z)⁻¹ (c3MetricJetZ g z) (c3MetricJetBar g z)
      (c3MetricJetZBar g z) (c3MetricJetZZ g z) (c3MetricJetZZBar g z) p j q k l -
      ∑ r, c3JetChristoffel (g z)⁻¹ (c3MetricJetZ g z) r p j *
        c3JetCurvature (g z)⁻¹ (c3MetricJetZ g z) (c3MetricJetBar g z)
          (c3MetricJetZBar g z) r q k l -
      ∑ r, c3JetChristoffel (g z)⁻¹ (c3MetricJetZ g z) r p k *
        c3JetCurvature (g z)⁻¹ (c3MetricJetZ g z) (c3MetricJetBar g z)
          (c3MetricJetZBar g z) j q r l)
  rw [show wirtingerDerivInChart (fun w => chartCurvature g w j q k l) z p =
    chartPartialZComplex (fun w => chartCurvature g w j q k l) z p from rfl,
    hExpand p j q k l]
  rfl

end KahlerForm
