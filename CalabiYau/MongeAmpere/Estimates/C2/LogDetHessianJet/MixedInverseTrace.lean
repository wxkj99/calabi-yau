module

public import CalabiYau.Geometry.Kahler.Curvature.Chart
import CalabiYau.LinearAlgebra.Hermitian.LogDetDeriv

/-!
# Differentiating the varying inverse-trace expression

The inverse differentiation and matrix product rule in Székelyhidi, *An Introduction to Extremal
Kähler Metrics*, §1.4, p. 12, preceding Lemma 1.22 and in its proof. This leaf takes the first
trace identity as an explicit neighborhood germ and differentiates it in the ordered direction
`∂ₚ(∂̄ₚ f)`. It does not identify the result with curvature or commute the two derivatives.

The inverse varies with the field: its contribution is the negative quadratic matrix product.
The coordinate direction `p` is independent of both coefficient indices. Only center
invertibility, entrywise C¹, and differentiability of the barred entry fields are needed.
-/

public section

open scoped ContDiff
open Filter Topology

namespace KahlerForm

private theorem chartPartialZComplex_sum_at {n : ℕ} {ι : Type*} [Fintype ι]
    (F : ι → EuclideanSpace ℂ (Fin n) → ℂ) (z : EuclideanSpace ℂ (Fin n)) (p : Fin n)
    (hF : ∀ i, DifferentiableAt ℝ (F i) z) :
    chartPartialZComplex (fun w ↦ ∑ i, F i w) z p = ∑ i, chartPartialZComplex (F i) z p := by
  unfold chartPartialZComplex
  have hfd : fderiv ℝ (fun w ↦ ∑ i, F i w) z = ∑ i, fderiv ℝ (F i) z := by
    simpa using fderiv_fun_sum (u := Finset.univ) (fun i hi ↦ hF i)
  rw [hfd]
  simp only [sum_apply, div_eq_mul_inv]
  conv_rhs => rw [← Finset.sum_mul]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]

/-- Differentiate a barred inverse-trace germ in an independent coordinate direction. -/
theorem log_det_mixed_inverse_trace_jet {n : ℕ}
    {G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    {f : EuclideanSpace ℂ (Fin n) → ℂ} {z : EuclideanSpace ℂ (Fin n)}
    (p : Fin n)
    (hG : ∀ j k, ContDiffAt ℝ 1 (fun w ↦ G w j k) z)
    (hunit : IsUnit (G z))
    (hB : ∀ j k, DifferentiableAt ℝ
      (fun w ↦ chartPartialBarComplex (fun v ↦ G v j k) w p) z)
    (hfirst : ∀ᶠ w in 𝓝 z,
      chartPartialBarComplex f w p = Matrix.trace ((G w)⁻¹ * Matrix.of (fun j k ↦
        chartPartialBarComplex (fun v ↦ G v j k) w p))) :
    chartPartialZComplex (fun w ↦ chartPartialBarComplex f w p) z p =
      Matrix.trace ((G z)⁻¹ * Matrix.of (fun j k ↦
        chartPartialZComplex
          (fun w ↦ chartPartialBarComplex (fun v ↦ G v j k) w p) z p)) -
      Matrix.trace ((G z)⁻¹ * Matrix.of (fun j k ↦
        chartPartialZComplex (fun w ↦ G w j k) z p) * (G z)⁻¹ *
        Matrix.of (fun j k ↦ chartPartialBarComplex (fun w ↦ G w j k) z p)) := by
  classical
  let B : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ := fun w =>
    Matrix.of (fun j k ↦ chartPartialBarComplex (fun v ↦ G v j k) w p)
  let T : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun j k ↦
    chartPartialZComplex (fun w ↦ G w j k) z p)
  let H : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun j k ↦
    chartPartialZComplex (fun w ↦ chartPartialBarComplex (fun v ↦ G v j k) w p) z p)
  let D : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun j k ↦
    chartPartialZComplex (fun w ↦ (G w)⁻¹ j k) z p)
  have hInv (j k : Fin n) : DifferentiableAt ℝ (fun w ↦ (G w)⁻¹ j k) z :=
    chartInv_differentiableAt hG hunit j k
  have hdet : IsUnit (G z).det := (Matrix.isUnit_iff_isUnit_det (A := G z)).mp hunit
  have hdetCont : ContinuousAt (fun w ↦ (G w).det) z := by
    have hcont : ContDiffAt ℝ 1 (fun w ↦ (G w).det) z := by
      simp_rw [Matrix.det_apply]
      fun_prop (disch := assumption)
    exact hcont.continuousAt
  have hdetEvent : ∀ᶠ w in 𝓝 z, (G w).det ≠ 0 :=
    hdetCont.eventually_ne hdet.ne_zero
  have hunitEvent : ∀ᶠ w in 𝓝 z, IsUnit (G w) := by
    filter_upwards [hdetEvent] with w hw
    exact (Matrix.isUnit_iff_isUnit_det (A := G w)).mpr (isUnit_iff_ne_zero.mpr hw)
  have hinvprod (a b : Fin n) :
      (fun w ↦ ∑ l : Fin n, G w a l * (G w)⁻¹ l b) =ᶠ[𝓝 z]
        fun _ ↦ (1 : Matrix (Fin n) (Fin n) ℂ) a b := by
    filter_upwards [hunitEvent] with w hw
    simpa only [Matrix.mul_apply] using congrArg (fun M : Matrix (Fin n) (Fin n) ℂ ↦ M a b)
      (Matrix.mul_nonsing_inv (G w) ((Matrix.isUnit_iff_isUnit_det (A := G w)).mp hw))
  have hentryprod (a b l : Fin n) : DifferentiableAt ℝ
      (fun w ↦ G w a l * (G w)⁻¹ l b) z := by
    exact (hG a l).differentiableAt (by norm_num) |>.mul (hInv l b)
  have hInvDeriv (a b : Fin n) : chartPartialZComplex
      (fun w ↦ ∑ l : Fin n, G w a l * (G w)⁻¹ l b) z p = 0 := by
    have hfd := (hinvprod a b).fderiv_eq (𝕜 := ℝ) (x := z)
    unfold chartPartialZComplex
    rw [hfd]
    simp
  have hInvDerivSum (a b : Fin n) :
      ∑ l : Fin n,
        (chartPartialZComplex (fun w ↦ G w a l) z p * (G z)⁻¹ l b +
          G z a l * chartPartialZComplex (fun w ↦ (G w)⁻¹ l b) z p) = 0 := by
    have h := hInvDeriv a b
    rw [chartPartialZComplex_sum_at (fun l w ↦ G w a l * (G w)⁻¹ l b) z p
      (fun l ↦ hentryprod a b l)] at h
    simp_rw [chartPartialZComplex_mul ((hG a _).differentiableAt (by norm_num))
      (hInv _ _) p] at h
    exact h
  have hGD : G z * D = -(T * (G z)⁻¹) := by
    ext a b
    simp only [D, T, Matrix.mul_apply, Matrix.of_apply, Matrix.neg_apply]
    have h := hInvDerivSum a b
    simp only [Finset.sum_add_distrib] at h
    linear_combination h
  have hleft : (G z)⁻¹ * G z = 1 :=
    Matrix.nonsing_inv_mul (G z) hdet
  have hD : D = -((G z)⁻¹ * T * (G z)⁻¹) := by
    calc
      D = 1 * D := by simp
      _ = ((G z)⁻¹ * G z) * D := by rw [hleft]
      _ = (G z)⁻¹ * (G z * D) := by rw [Matrix.mul_assoc]
      _ = (G z)⁻¹ * (-(T * (G z)⁻¹)) := by rw [hGD]
      _ = -((G z)⁻¹ * T * (G z)⁻¹) := by simp [Matrix.mul_assoc]
  have htracefun : (fun w ↦ Matrix.trace ((G w)⁻¹ * B w)) =
      fun w ↦ ∑ j : Fin n, ∑ k : Fin n, (G w)⁻¹ j k * B w k j := by
    funext w
    simp [B, Matrix.trace, Matrix.mul_apply]
  have hprod (j k : Fin n) : DifferentiableAt ℝ
      (fun w ↦ (G w)⁻¹ j k * B w k j) z := by
    exact (hInv j k).mul (hB k j)
  have hinner (j : Fin n) : DifferentiableAt ℝ
      (fun w ↦ ∑ k : Fin n, (G w)⁻¹ j k * B w k j) z := by
    exact DifferentiableAt.fun_sum (fun k hk ↦ hprod j k)
  have hderivTrace : chartPartialZComplex (fun w ↦ Matrix.trace ((G w)⁻¹ * B w)) z p =
      Matrix.trace (D * B z) + Matrix.trace ((G z)⁻¹ * H) := by
    calc
      _ = chartPartialZComplex
          (fun w ↦ ∑ j : Fin n, ∑ k : Fin n, (G w)⁻¹ j k * B w k j) z p := by
            rw [htracefun]
      _ = ∑ j : Fin n, chartPartialZComplex
          (fun w ↦ ∑ k : Fin n, (G w)⁻¹ j k * B w k j) z p :=
            chartPartialZComplex_sum_at _ z p (fun j ↦ DifferentiableAt.fun_sum
              (fun k hk ↦ hprod j k))
      _ = ∑ j : Fin n, ∑ k : Fin n,
          chartPartialZComplex (fun w ↦ (G w)⁻¹ j k * B w k j) z p := by
            apply Finset.sum_congr rfl
            intro j hj
            exact chartPartialZComplex_sum_at _ z p (fun k ↦ hprod j k)
      _ = ∑ j : Fin n, ∑ k : Fin n,
          (chartPartialZComplex (fun w ↦ (G w)⁻¹ j k) z p * B z k j +
            (G z)⁻¹ j k * chartPartialZComplex (fun w ↦ B w k j) z p) := by
            apply Finset.sum_congr rfl
            intro j hj
            apply Finset.sum_congr rfl
            intro k hk
            exact chartPartialZComplex_mul (hInv j k) (hB k j) p
      _ = Matrix.trace (D * B z) + Matrix.trace ((G z)⁻¹ * H) := by
            simp [D, H, B, Matrix.trace, Matrix.mul_apply, Matrix.of_apply,
              Finset.sum_add_distrib]
  have htraceGerm : (fun w ↦ chartPartialBarComplex f w p) =ᶠ[𝓝 z]
      fun w ↦ Matrix.trace ((G w)⁻¹ * B w) := by
    filter_upwards [hfirst] with w hw
    simpa [B] using hw
  have hfirstZ := htraceGerm.fderiv_eq (𝕜 := ℝ) (x := z)
  have hZeq : chartPartialZComplex (fun w ↦ chartPartialBarComplex f w p) z p =
      chartPartialZComplex (fun w ↦ Matrix.trace ((G w)⁻¹ * B w)) z p := by
    unfold chartPartialZComplex
    rw [hfirstZ]
  rw [hZeq, hderivTrace]
  have hquad : Matrix.trace (D * B z) =
      -Matrix.trace ((G z)⁻¹ * T * (G z)⁻¹ * B z) := by
    rw [hD]
    simp [Matrix.mul_assoc]
  rw [hquad]
  simp only [B, H, T, Matrix.mul_assoc]
  ring

end KahlerForm
