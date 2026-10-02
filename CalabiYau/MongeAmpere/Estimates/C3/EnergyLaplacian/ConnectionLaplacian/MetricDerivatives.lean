module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ConnectionLaplacian.Basic
import CalabiYau.Mathlib.Analysis.Matrix.EntrywiseSmoothness
import CalabiYau.Geometry.Kahler.Curvature.Chart.MixedDerivatives

/-!
# Shared inverse compatibility and chart metric regularity

Székelyhidi, §3.3, proof of Lemma 3.9, the Bianchi calculation following
(3.15), printed p. 45. The inverse derivative is `-g⁻¹ (Dg) g⁻¹`, without
transpose or conjugation. Chart data is transported on the open target, rather
than inferred from equality at a single point.
-/

public section

open scoped Manifold ContDiff BigOperators ComplexOrder MatrixOrder

namespace KahlerForm

variable {n : ℕ}

theorem wirtingerDerivInChart_inverse_eq_christoffel
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hd : ∀ a b, DifferentiableAt ℝ (fun w => g w a b) z)
    (hunit : IsUnit (g z)) (l i p : Fin n) :
    wirtingerDerivInChart (fun w => (g w)⁻¹ l i) z p =
      -∑ r, christoffelInChart g z i p r * (g z)⁻¹ l r := by
  classical
  let U := (g z)⁻¹
  let V : Matrix (Fin n) (Fin n) ℂ := fun a b =>
    fderiv ℝ (fun w => g w a b) z (EuclideanSpace.single p 1)
  let W : Matrix (Fin n) (Fin n) ℂ := fun a b =>
    fderiv ℝ (fun w => g w a b) z (Complex.I • EuclideanSpace.single p 1)
  have halgebra (U V W : Matrix (Fin n) (Fin n) ℂ) (l i : Fin n) :
      (∑ a, ∑ b, U l a * V a b * U b i) * (-1 / 2) +
          (Complex.I * (∑ a, ∑ b, U l a * W a b * U b i)) * (1 / 2) =
        -∑ a, (∑ b, U b i * ((V a b - Complex.I * W a b) / 2)) * U l a := by
    conv_lhs => rhs; rw [mul_assoc]
    simp only [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    simp_rw [← Finset.sum_add_distrib]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hreal := Matrix.fderiv_inverse_entry_apply hd hunit l i
      (EuclideanSpace.single p 1)
  have himag := Matrix.fderiv_inverse_entry_apply hd hunit l i
      (Complex.I • EuclideanSpace.single p 1)
  unfold wirtingerDerivInChart christoffelInChart
  rw [hreal, himag]
  convert halgebra U V W l i using 1
  all_goals
    simp only [U, V, W, wirtingerDerivInChart]
    try ring_nf

theorem c3ChartPartialBar_contDiffAt
    (F : EuclideanSpace ℂ (Fin n) → ℂ) (z : EuclideanSpace ℂ (Fin n))
    (hF : ContDiffAt ℝ ∞ F z) (q : Fin n) :
    ContDiffAt ℝ ∞ (fun w => chartPartialBarComplex F w q) z := by
  have hfd : ContDiffAt ℝ ∞ (fderiv ℝ F) z := hF.fderiv_right (by simp)
  unfold chartPartialBarComplex
  fun_prop

theorem c3Curvature_differentiableAt
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hg : ∀ a b, ContDiffAt ℝ ∞ (fun w => g w a b) z)
    (hunit : IsUnit (g z)) (p q j l : Fin n) :
    DifferentiableAt ℝ (fun w => chartCurvature g w p q j l) z := by
  have hInv (a b : Fin n) : DifferentiableAt ℝ (fun w => (g w)⁻¹ a b) z :=
    chartInv_differentiableAt (fun i k => (hg i k).of_le (by norm_num)) hunit a b
  change DifferentiableAt ℝ (fun w =>
    -chartPartialZComplex (fun v => chartPartialBarComplex (fun u => g u j l) v q) w p +
      ∑ a, ∑ b, (g w)⁻¹ b a * chartPartialZComplex (fun v => g v j b) w p *
        chartPartialBarComplex (fun v => g v a l) w q) z
  apply DifferentiableAt.add
  · exact ((chartPartialZComplex_contDiffAt _ z
      (c3ChartPartialBar_contDiffAt _ z (hg j l) q) p).differentiableAt
        (by norm_num)).neg
  · apply DifferentiableAt.fun_sum
    intro a _
    apply DifferentiableAt.fun_sum
    intro b _
    exact ((hInv b a).mul ((chartPartialZComplex_contDiffAt _ z (hg j b) p).differentiableAt
      (by norm_num))).mul ((c3ChartPartialBar_contDiffAt _ z (hg a l) q).differentiableAt
        (by norm_num))

theorem c3ChartPartialZ_inverse_entry_on
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (hg : ∀ a b, ContDiffOn ℝ ∞ (fun w => g w a b) U)
    (hunit : ∀ w ∈ U, IsUnit (g w))
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U)
    (i j p : Fin n) :
    chartPartialZComplex (fun w => (g w)⁻¹ i j) z p =
      -∑ a, ∑ b, (g z)⁻¹ i a *
        chartPartialZComplex (fun w => g w a b) z p * (g z)⁻¹ b j := by
  classical
  let Uinv := (g z)⁻¹
  let V : Matrix (Fin n) (Fin n) ℂ := fun a b =>
    fderiv ℝ (fun w => g w a b) z (EuclideanSpace.single p 1)
  let W : Matrix (Fin n) (Fin n) ℂ := fun a b =>
    fderiv ℝ (fun w => g w a b) z (Complex.I • EuclideanSpace.single p 1)
  have halgebra (U V W : Matrix (Fin n) (Fin n) ℂ) (l i : Fin n) :
      (∑ a, ∑ b, U l a * V a b * U b i) * (-1 / 2) +
          (Complex.I * (∑ a, ∑ b, U l a * W a b * U b i)) * (1 / 2) =
        -∑ a, (∑ b, U b i * ((V a b - Complex.I * W a b) / 2)) * U l a := by
    conv_lhs => rhs; rw [mul_assoc]
    simp only [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    simp_rw [← Finset.sum_add_distrib]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hd (a b : Fin n) : DifferentiableAt ℝ (fun w => g w a b) z :=
    ((hg a b).contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)
  have hreal := Matrix.fderiv_inverse_entry_apply hd (hunit z hz) i j
      (EuclideanSpace.single p 1)
  have himag := Matrix.fderiv_inverse_entry_apply hd (hunit z hz) i j
      (Complex.I • EuclideanSpace.single p 1)
  unfold chartPartialZComplex
  rw [hreal, himag]
  convert halgebra Uinv V W i j using 1
  all_goals
    simp only [Uinv, V, W]
    try ring_nf
  simp_rw [Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem c3PerturbedMetric_chart_data
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₀ : KahlerForm n M) {φ : M → ℝ} (hφ : ω₀.IsPotential φ) (x : M) :
    let U : Set (EuclideanSpace ℂ (Fin n)) :=
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target
    let g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
      c3PerturbedMetricInChart ω₀ φ x
    IsOpen U ∧
      (∀ a b, ContDiffOn ℝ ∞ (fun w => g w a b) U) ∧
      (∀ w ∈ U, IsUnit (g w)) ∧
      (∀ w ∈ U, ∀ a b c,
        chartPartialZComplex (fun v => g v b c) w a =
          chartPartialZComplex (fun v => g v a c) w b) := by
  dsimp
  let U : Set (EuclideanSpace ℂ (Fin n)) :=
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target
  let g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    c3PerturbedMetricInChart ω₀ φ x
  let ωφ := ω₀.perturb φ hφ
  have hU : IsOpen U := isOpen_extChartAt_target x
  have heq : Set.EqOn g (fun w => ωφ.metricInChart x w) U := by
    intro w hw
    simpa only [g, c3PerturbedMetricInChart, ωφ] using
      (ω₀.metricInChart_perturb hφ x hw).symm
  refine ⟨hU, ?_, ?_, ?_⟩
  · intro a b
    exact (ωφ.contDiffOn_metricInChart x a b).congr
      (fun w hw => congrArg (fun G : Matrix (Fin n) (Fin n) ℂ => G a b) (heq hw))
  · intro w hw
    change IsUnit (g w)
    rw [heq hw]
    exact (ωφ.posDef_metricInChart x hw).isUnit
  · intro w hw a b c
    have hnhds : U ∈ nhds w := hU.mem_nhds hw
    have hentry (s t : Fin n) :
        (fun v => g v s t) =ᶠ[nhds w] (fun v => ωφ.metricInChart x v s t) := by
      filter_upwards [hnhds] with v hv
      exact congrArg (fun G : Matrix (Fin n) (Fin n) ℂ => G s t) (heq hv)
    have hleft := (hentry b c).fderiv_eq (𝕜 := ℝ)
    have hright := (hentry a c).fderiv_eq (𝕜 := ℝ)
    unfold chartPartialZComplex
    rw [hleft, hright]
    exact ωφ.kahler_chart_metric_symmetry x hw a b c

end KahlerForm
