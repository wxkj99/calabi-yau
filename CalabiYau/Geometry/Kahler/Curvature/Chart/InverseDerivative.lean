module

public import CalabiYau.Geometry.Kahler.Curvature.Chart.DerivativeRules

/-!
# Antiholomorphic derivative of inverse metric entries

Differentiate the local identity `g⁻¹g = 1` and multiply by the inverse on
the right. Invertibility is required only at the evaluation point.
Székelyhidi, §3.3, proof of Lemma 3.9, PDF p.48 (book p.45).
-/

public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder

namespace KahlerForm

variable {n : ℕ}

theorem chartPartialBarComplex_inverse_entry_at
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hg : ∀ a b, ContDiffAt ℝ ∞ (fun w => g w a b) z)
    (hdet : IsUnit (g z).det) (i j q : Fin n) :
    chartPartialBarComplex (fun w => (g w)⁻¹ i j) z q =
      -(∑ a, ∑ b, (g z)⁻¹ i a * chartPartialBarComplex (fun w => g w a b) z q *
        (g z)⁻¹ b j) := by
  classical
  have he (a b : Fin n) : DifferentiableAt ℝ (fun w => g w a b) z :=
    (hg a b).differentiableAt (by norm_num)
  have hi (a b : Fin n) : DifferentiableAt ℝ (fun w => (g w)⁻¹ a b) z :=
    chartInv_differentiableAt (fun a b => (hg a b).of_le (by norm_num))
      ((Matrix.isUnit_iff_isUnit_det _).2 hdet) a b
  have hd : ContinuousAt (fun w => (g w).det) z := by
    have hdc : ContDiffAt ℝ ∞ (fun w => (g w).det) z := by
      simp_rw [Matrix.det_apply]
      fun_prop (disch := assumption)
    exact hdc.continuousAt
  have hne : ∀ᶠ w in nhds z, (g w).det ≠ 0 := hd.eventually_ne hdet.ne_zero
  have hu : ∀ᶠ w in nhds z, IsUnit (g w).det := by
    filter_upwards [hne] with w hw
    exact isUnit_iff_ne_zero.mpr hw
  have hprod (a b : Fin n) :
      (fun w => ∑ t : Fin n, (g w)⁻¹ a t * g w t b) =ᶠ[nhds z]
        (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) a b) := by
    filter_upwards [hu] with w hw
    simpa only [Matrix.mul_apply] using congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M a b)
      (Matrix.nonsing_inv_mul (g w) hw)
  have hzero (a b : Fin n) :
      chartPartialBarComplex (fun w => ∑ t : Fin n, (g w)⁻¹ a t * g w t b) z q = 0 := by
    unfold chartPartialBarComplex
    rw [hprod a b |>.fderiv_eq]
    simp
  have hrel (a b : Fin n) :
      (∑ t : Fin n, chartPartialBarComplex (fun w => (g w)⁻¹ a t) z q * g z t b) +
      (∑ t : Fin n, (g z)⁻¹ a t * chartPartialBarComplex (fun w => g w t b) z q) = 0 := by
    have hh := hzero a b
    rw [chartPartialBarComplex_sum
      (fun t w => (g w)⁻¹ a t * g w t b) z q (fun t => (hi a t).mul (he t b))] at hh
    simp_rw [chartPartialBarComplex_mul _ _ z q (hi a _) (he _ b)] at hh
    rwa [Finset.sum_add_distrib] at hh
  let D : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun a b =>
    chartPartialBarComplex (fun w => (g w)⁻¹ a b) z q)
  let H : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun a b =>
    chartPartialBarComplex (fun w => g w a b) z q)
  have hmat : D * g z = -((g z)⁻¹ * H) := by
    ext a b
    simp only [D, H, Matrix.mul_apply, Matrix.of_apply, Matrix.neg_apply]
    exact (eq_neg_iff_add_eq_zero).2 (hrel a b)
  have hresult : D = -((g z)⁻¹ * H * (g z)⁻¹) := by
    calc
      D = D * 1 := by simp
      _ = D * (g z * (g z)⁻¹) := by rw [Matrix.mul_nonsing_inv (g z) hdet]
      _ = (D * g z) * (g z)⁻¹ := by rw [Matrix.mul_assoc]
      _ = -((g z)⁻¹ * H * (g z)⁻¹) := by rw [hmat]; simp [Matrix.mul_assoc]
  have hentry := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) hresult
  simp only [D, H, Matrix.of_apply, Matrix.neg_apply, Matrix.mul_apply, Finset.sum_mul] at hentry
  rw [Finset.sum_comm]
  exact hentry

end KahlerForm
