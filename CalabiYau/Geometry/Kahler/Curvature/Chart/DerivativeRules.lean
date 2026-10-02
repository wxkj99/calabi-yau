module

public import CalabiYau.Geometry.Kahler.Curvature.Chart.Basic

/-!
# Pointwise coordinate derivative rules

Finite sums, constant multiples and the antiholomorphic product rule.
These are the first-order calculus steps in the local Chern identity in
Székelyhidi, §3.3, proof of Lemma 3.9, PDF p.48 (book p.45).
-/

public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder

namespace KahlerForm

variable {n : ℕ}

theorem chartPartialZComplex_const_mul
    (c : ℂ) (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n)
    (hF : DifferentiableAt ℝ F z) :
    chartPartialZComplex (fun w ↦ c * F w) z j =
      c * chartPartialZComplex F z j := by
  unfold chartPartialZComplex
  rw [fderiv_const_mul hF c]
  simp only [smul_apply, div_eq_mul_inv]
  ring

theorem chartPartialZComplex_sum
    {ι : Type*} [Fintype ι]
    (F : ι → EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n)
    (hF : ∀ i, DifferentiableAt ℝ (F i) z) :
    chartPartialZComplex (fun w ↦ ∑ i, F i w) z j =
      ∑ i, chartPartialZComplex (F i) z j := by
  unfold chartPartialZComplex
  have hfd : fderiv ℝ (fun w ↦ ∑ i, F i w) z = ∑ i, fderiv ℝ (F i) z := by
    simpa using fderiv_fun_sum (u := Finset.univ) (fun i hi ↦ hF i)
  rw [hfd]
  simp only [sum_apply]
  have hsum :
      (∑ i, fderiv ℝ (F i) z (EuclideanSpace.single j 1)) -
        Complex.I * ∑ i, fderiv ℝ (F i) z (Complex.I • EuclideanSpace.single j 1) =
      ∑ i, (fderiv ℝ (F i) z (EuclideanSpace.single j 1) -
        Complex.I * fderiv ℝ (F i) z (Complex.I • EuclideanSpace.single j 1)) := by
    rw [Finset.mul_sum, Finset.sum_sub_distrib]
  rw [hsum]
  simp only [div_eq_mul_inv, Finset.sum_mul]

theorem chartPartialBarComplex_sum
    {ι : Type*} [Fintype ι]
    (F : ι → EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n)
    (hF : ∀ i, DifferentiableAt ℝ (F i) z) :
    chartPartialBarComplex (fun w ↦ ∑ i, F i w) z j =
      ∑ i, chartPartialBarComplex (F i) z j := by
  unfold chartPartialBarComplex
  have hfd : fderiv ℝ (fun w ↦ ∑ i, F i w) z = ∑ i, fderiv ℝ (F i) z := by
    simpa using fderiv_fun_sum (u := Finset.univ) (fun i hi ↦ hF i)
  rw [hfd]
  simp only [sum_apply]
  have hsum :
      (∑ i, fderiv ℝ (F i) z (EuclideanSpace.single j 1)) +
        Complex.I * ∑ i, fderiv ℝ (F i) z (Complex.I • EuclideanSpace.single j 1) =
      ∑ i, (fderiv ℝ (F i) z (EuclideanSpace.single j 1) +
        Complex.I * fderiv ℝ (F i) z (Complex.I • EuclideanSpace.single j 1)) := by
    rw [Finset.mul_sum, Finset.sum_add_distrib]
  rw [hsum]
  simp only [div_eq_mul_inv, Finset.sum_mul]

theorem chartPartialBarComplex_mul
    (F G : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (q : Fin n)
    (hF : DifferentiableAt ℝ F z) (hG : DifferentiableAt ℝ G z) :
    chartPartialBarComplex (fun w => F w * G w) z q =
      chartPartialBarComplex F z q * G z + F z * chartPartialBarComplex G z q := by
  unfold chartPartialBarComplex
  rw [fderiv_fun_mul hF hG]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

end KahlerForm
