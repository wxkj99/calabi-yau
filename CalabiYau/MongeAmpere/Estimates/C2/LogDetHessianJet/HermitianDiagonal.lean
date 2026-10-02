module

public import CalabiYau.Geometry.Kahler.Curvature.Chart

/-!
# Hermitian first jets and positive-diagonal trace contractions

The finite contractions of the logarithmic determinant calculation in Székelyhidi,
*An Introduction to Extremal Kähler Metrics*, §1.4, p. 12, preceding Lemma 1.22 and in its proof.
The barred entry jet is the conjugate transpose of the unbarred jet. At a positive real diagonal
center this turns the quadratic inverse-trace term into the full coefficient-index norm square.

The unbarred first jet is not assumed Hermitian. Its coefficient indices must be transposed in
the barred partner. The two algebraic identities apply also to empty matrices and to arbitrary
complex matrices `H` and `T`; only the diagonal weights are assumed positive.
-/

public section

open scoped ContDiff
open Filter Topology

namespace KahlerForm

private theorem log_det_chartPartialBarComplex_eventuallyEq {n : ℕ}
    (F G : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (p : Fin n)
    (h : F =ᶠ[𝓝 z] G) :
    chartPartialBarComplex F z p = chartPartialBarComplex G z p := by
  have hfd : fderiv ℝ F z = fderiv ℝ G z := (h.fderiv (𝕜 := ℝ)).eq_of_nhds
  unfold chartPartialBarComplex
  rw [hfd]

private theorem log_det_chartPartialBarComplex_star {n : ℕ}
    (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (q : Fin n)
    (hF : DifferentiableAt ℝ F z) :
    chartPartialBarComplex (fun w ↦ star (F w)) z q =
      star (chartPartialZComplex F z q) := by
  have hfd := fderiv_comp (𝕜 := ℝ) (f := F) (g := (Complex.conjCLE : ℂ → ℂ))
    (x := z) Complex.conjCLE.differentiableAt hF
  have hfun : (fun w ↦ star (F w)) = Complex.conjCLE ∘ F := by
    funext w
    simp
  have hstar : fderiv ℝ (fun w ↦ star (F w)) z =
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ F z) := by
    rw [hfun]
    simpa only [Complex.conjCLE.fderiv] using hfd
  unfold chartPartialBarComplex chartPartialZComplex
  rw [hstar]
  simp only [ContinuousLinearMap.comp_apply]
  change (star ((fderiv ℝ F z) (EuclideanSpace.single q 1)) +
    Complex.I * star ((fderiv ℝ F z) (Complex.I • EuclideanSpace.single q 1))) / 2 = _
  simp [Complex.conj_I]

private theorem log_det_positive_diagonal_inverse {n : ℕ}
    (lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) :
    (Matrix.diagonal (fun j ↦ (lam j : ℂ)))⁻¹ =
      Matrix.diagonal (fun j ↦ ((lam j)⁻¹ : ℂ)) := by
  have hunit : IsUnit (fun k ↦ (lam k : ℂ)) := by
    rw [Pi.isUnit_iff]
    intro k
    exact isUnit_iff_ne_zero.mpr (by exact_mod_cast ne_of_gt (hlam k))
  have hinv : Ring.inverse (fun k ↦ (lam k : ℂ)) =
      (fun k ↦ ((lam k)⁻¹ : ℂ)) := by
    funext j
    rw [Ring.inverse_of_isUnit hunit]
    simp [IsUnit.val_inv_apply hunit j]
  rw [Matrix.inv_diagonal]
  ext i j
  simp [Matrix.diagonal_apply, hinv]

/-- A Hermitian neighborhood germ conjugates and transposes its two first Wirtinger jets. -/
theorem log_det_hermitian_bar_jet {n : ℕ}
    {G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    {z : EuclideanSpace ℂ (Fin n)}
    (hG : ∀ j k, ContDiffAt ℝ 1 (fun w ↦ G w j k) z)
    (hHerm : ∀ᶠ w in 𝓝 z, (G w).IsHermitian) (p j k : Fin n) :
    chartPartialBarComplex (fun w ↦ G w j k) z p =
      star (chartPartialZComplex (fun w ↦ G w k j) z p) := by
  have hEq : (fun w ↦ G w j k) =ᶠ[𝓝 z] (fun w ↦ star (G w k j)) := by
    filter_upwards [hHerm] with w hw
    exact (hw.apply j k).symm
  calc
    chartPartialBarComplex (fun w ↦ G w j k) z p =
        chartPartialBarComplex (fun w ↦ star (G w k j)) z p :=
      log_det_chartPartialBarComplex_eventuallyEq _ _ z p hEq
    _ = star (chartPartialZComplex (fun w ↦ G w k j) z p) :=
      log_det_chartPartialBarComplex_star (fun w ↦ G w k j) z p
        ((hG k j).differentiableAt (by norm_num))

/-- The real part of the linear inverse-trace contraction at a positive diagonal matrix. -/
theorem log_det_diagonal_inverse_trace_real {n : ℕ}
    (lam : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℂ)
    (hlam : ∀ j, 0 < lam j) :
    (Matrix.trace ((Matrix.diagonal (fun j ↦ (lam j : ℂ)))⁻¹ * H)).re =
      ∑ j, (H j j).re / lam j := by
  rw [log_det_positive_diagonal_inverse lam hlam]
  simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [div_eq_mul_inv]
  ring

/-- The real quadratic inverse-trace contraction is the weighted full coefficient norm square. -/
theorem log_det_diagonal_inverse_quadratic_trace_real {n : ℕ}
    (lam : Fin n → ℝ) (T : Matrix (Fin n) (Fin n) ℂ)
    (hlam : ∀ j, 0 < lam j) :
    (Matrix.trace ((Matrix.diagonal (fun j ↦ (lam j : ℂ)))⁻¹ * T *
      (Matrix.diagonal (fun j ↦ (lam j : ℂ)))⁻¹ * T.conjTranspose)).re =
      ∑ j, ∑ k, ‖T j k‖ ^ 2 / (lam j * lam k) := by
  rw [log_det_positive_diagonal_inverse lam hlam]
  simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  have hnorm : ‖T j k‖ ^ 2 = (T j k).re ^ 2 + (T j k).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq]
    ring
  rw [hnorm]
  field_simp [ne_of_gt (hlam j), ne_of_gt (hlam k)]

end KahlerForm
