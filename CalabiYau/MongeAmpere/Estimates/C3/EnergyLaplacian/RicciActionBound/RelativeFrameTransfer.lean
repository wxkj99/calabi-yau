module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.Basic

/-!
# Transfer of a covariant coefficient bound between normalized frames

This is finite-dimensional Cauchy–Schwarz, the metric-comparison step in the
general-MA adaptation of Székelyhidi §3.3, after (3.14), printed p. 45.
The reverse relative-trace estimate supplies `g₀ ≤ B*g` in the consuming
module; it is not assumed to bound raw coordinate columns of `P`.
-/

@[expose] public section

open scoped ComplexOrder

namespace KahlerForm

/-- Entry bounds in a reference-unitary frame transfer to a perturbed-unitary
frame at cost `n*B*D`. No Hermitian condition on the covariant tensor is needed. -/
private theorem relativeFrameTransfer_frame_inverse {n : ℕ} (g U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U.transpose * g * U.map star = 1) :
    U.transpose⁻¹ = g * U.map star := by
  apply Matrix.inv_eq_left_inv
  have hRight : U.transpose * (g * U.map star) = 1 := by
    simpa only [Matrix.mul_assoc] using hU
  have hLeft : (g * U.map star) * U.transpose = 1 := mul_eq_one_comm.mp hRight
  simpa only [Matrix.mul_assoc] using hLeft

private theorem relativeFrameTransfer_frame_A {n : ℕ} (g U P : Matrix (Fin n) (Fin n) ℂ)
    (hU : U.transpose * g * U.map star = 1) :
    (P.transpose * U.transpose⁻¹) * U.transpose = P.transpose := by
  rw [relativeFrameTransfer_frame_inverse g U hU]
  calc
    P.transpose * (g * U.map star) * U.transpose =
        P.transpose * ((g * U.map star) * U.transpose) := by rw [Matrix.mul_assoc]
    _ = P.transpose := by
      have h : (g * U.map star) * U.transpose = 1 := by
        exact mul_eq_one_comm.mp (by simpa only [Matrix.mul_assoc] using hU)
      rw [h, Matrix.mul_one]

private theorem relativeFrameTransfer_frame_bar_transpose {n : ℕ} (A U P : Matrix (Fin n) (Fin n) ℂ)
    (h : P.transpose = A * U.transpose) :
    P.map star = U.map star * A.transpose.map star := by
  rw [← Matrix.transpose_transpose P, h]
  ext i j
  simp [Matrix.mul_apply, Matrix.transpose_apply]

private theorem relativeFrameTransfer_frame_coefficients {n : ℕ} (U P A : Matrix (Fin n) (Fin n) ℂ)
    (Q : Fin n → Fin n → ℂ)
    (hPU : P.transpose = A * U.transpose)
    (hPbar : P.map star = U.map star * A.transpose.map star) :
    Matrix.of (fun j l ↦ c3TwoCovariantFrame P Q j l) =
      A * Matrix.of (fun j l ↦ c3TwoCovariantFrame U Q j l) * A.transpose.map star := by
  have hFrame (V : Matrix (Fin n) (Fin n) ℂ) :
      Matrix.of (fun j l ↦ c3TwoCovariantFrame V Q j l) =
        V.transpose * Matrix.of Q * V.map star := by
    ext j l
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.of_apply, c3TwoCovariantFrame]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    ring
  rw [hFrame P, hPU, hPbar, hFrame U]
  simp only [Matrix.mul_assoc]

private theorem relativeFrameTransfer_row_sq_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (B : ℝ)
    (hA : ((B : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
      A * A.transpose.map star).PosSemidef) (j : Fin n) :
    ∑ a, ‖A j a‖ ^ 2 ≤ B := by
  have hq := hA.dotProduct_mulVec_nonneg (Pi.single j (1 : ℂ))
  have hqr := (RCLike.nonneg_iff.mp hq).1
  simp [dotProduct, Matrix.mulVec, Matrix.mul_apply, Pi.single_apply] at hqr
  simpa [← sq, Complex.sq_norm, Complex.normSq_apply] using hqr

private theorem relativeFrameTransfer_row_l1_bound_sqrt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (B : ℝ) (j : Fin n)
    (hrow : ∑ a, ‖A j a‖ ^ 2 ≤ B) :
    ∑ a, ‖A j a‖ ≤ √((n : ℝ) * B) := by
  calc
    ∑ a, ‖A j a‖ ≤ √(n : ℝ) * √(∑ a, ‖A j a‖ ^ 2) := by
      simpa using (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
        (fun _ : Fin n ↦ (1 : ℝ)) (fun a ↦ ‖A j a‖))
    _ ≤ √(n : ℝ) * √B := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrow)
      (Real.sqrt_nonneg _)
    _ = √((n : ℝ) * B) := by rw [← Real.sqrt_mul (Nat.cast_nonneg n)]

private theorem relativeFrameTransfer_product_l1_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (B : ℝ) (hB : 0 ≤ B) (j l : Fin n)
    (hj : ∑ a, ‖A j a‖ ^ 2 ≤ B) (hl : ∑ a, ‖A l a‖ ^ 2 ≤ B) :
    (∑ a, ‖A j a‖) * (∑ a, ‖A l a‖) ≤ (n : ℝ) * B := by
  have hsquare : 0 ≤ (n : ℝ) * B := mul_nonneg (Nat.cast_nonneg n) hB
  calc
    (∑ a, ‖A j a‖) * (∑ a, ‖A l a‖) ≤
        √((n : ℝ) * B) * √((n : ℝ) * B) :=
      mul_le_mul (relativeFrameTransfer_row_l1_bound_sqrt A B j hj)
        (relativeFrameTransfer_row_l1_bound_sqrt A B l hl)
        (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
        (Real.sqrt_nonneg _)
    _ = (n : ℝ) * B := by rw [← sq, Real.sq_sqrt hsquare]

private theorem relativeFrameTransfer_comparison {n : ℕ} (g₀ g U P : Matrix (Fin n) (Fin n) ℂ)
    (B : ℝ) (hU : U.transpose * g₀ * U.map star = 1)
    (hP : P.transpose * g * P.map star = 1)
    (hComp : ((B : ℂ) • g - g₀).PosSemidef) :
    let A := P.transpose * U.transpose⁻¹
    ((B : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - A * A.transpose.map star).PosSemidef := by
  dsimp
  let A := P.transpose * U.transpose⁻¹
  have hPU : P.transpose = A * U.transpose := by
    exact (relativeFrameTransfer_frame_A g₀ U P hU).symm
  have hPbar : P.map star = U.map star * A.transpose.map star :=
    relativeFrameTransfer_frame_bar_transpose A U P hPU
  have hAcomp := hComp.conjTranspose_mul_mul_same (P.map star)
  have hconj : (P.map star).conjTranspose = P.transpose := by
    ext i j
    simp [Matrix.conjTranspose, Matrix.transpose_apply, Matrix.map_apply]
  rw [hconj] at hAcomp
  have hPmetric : P.transpose * g * P.map star = 1 := hP
  have hPbase : P.transpose * g₀ * P.map star = A * A.transpose.map star := by
    rw [hPU, hPbar]
    calc
      A * U.transpose * g₀ * (U.map star * A.transpose.map star) =
          A * (U.transpose * g₀ * U.map star) * A.transpose.map star := by
            simp only [Matrix.mul_assoc]
      _ = A * 1 * A.transpose.map star := by rw [hU]
      _ = A * A.transpose.map star := by simp
  change (P.transpose * ((B : ℂ) • g - g₀) * P.map star).PosSemidef at hAcomp
  have hPcomp : P.transpose * ((B : ℂ) • g - g₀) * P.map star =
      (B : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - A * A.transpose.map star := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    calc
      P.transpose * ((B : ℂ) • g) * P.map star -
          P.transpose * g₀ * P.map star =
          (B : ℂ) • (P.transpose * g * P.map star) -
            P.transpose * g₀ * P.map star := by
              congr 1
              simp only [Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul]
      _ = (B : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - A * A.transpose.map star := by
        rw [hPmetric, hPbase]
  rw [hPcomp] at hAcomp
  exact hAcomp

theorem c3TwoCovariantFrame_bound_of_relative_matrix_comparison {n : ℕ}
    (g₀ g U P : Matrix (Fin n) (Fin n) ℂ)
    (Q : Fin n → Fin n → ℂ) (B D : ℝ)
    (hU : U.transpose * g₀ * U.map star = 1)
    (hP : P.transpose * g * P.map star = 1)
    (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hComparison : ((B : ℂ) • g - g₀).PosSemidef)
    (hQ : ∀ j l, ‖c3TwoCovariantFrame U Q j l‖ ≤ D) :
    ∀ j l, ‖c3TwoCovariantFrame P Q j l‖ ≤ (n : ℝ) * B * D := by
  let A : Matrix (Fin n) (Fin n) ℂ := P.transpose * U.transpose⁻¹
  have hPU : P.transpose = A * U.transpose := by
    exact (relativeFrameTransfer_frame_A g₀ U P hU).symm
  have hPbar : P.map star = U.map star * A.transpose.map star :=
    relativeFrameTransfer_frame_bar_transpose A U P hPU
  have hApsd : ((B : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
      A * A.transpose.map star).PosSemidef := by
    simpa [A] using relativeFrameTransfer_comparison g₀ g U P B hU hP hComparison
  have hrow : ∀ j, ∑ a, ‖A j a‖ ^ 2 ≤ B := by
    intro j
    exact relativeFrameTransfer_row_sq_bound A B hApsd j
  have hframe := relativeFrameTransfer_frame_coefficients U P A Q hPU hPbar
  intro j l
  have hentry : c3TwoCovariantFrame P Q j l =
      ∑ a, ∑ b, A j a * star (A l b) * c3TwoCovariantFrame U Q a b := by
    have hm := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ ↦ M j l) hframe
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.of_apply] at hm
    rw [hm]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    ring
  rw [hentry]
  calc
    ‖∑ a, ∑ b, A j a * star (A l b) * c3TwoCovariantFrame U Q a b‖ ≤
        ∑ a, ‖∑ b, A j a * star (A l b) * c3TwoCovariantFrame U Q a b‖ := norm_sum_le _ _
    _ ≤ ∑ a, ∑ b, ‖A j a * star (A l b) * c3TwoCovariantFrame U Q a b‖ := by
      apply Finset.sum_le_sum
      intro a ha
      exact norm_sum_le _ _
    _ ≤ ∑ a, ∑ b, (‖A j a‖ * ‖A l b‖ * D) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      rw [norm_mul, norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_left (hQ a b) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = (∑ a, ∑ b, ‖A j a‖ * ‖A l b‖) * D := by
      have hinner (a : Fin n) :
          (∑ b, ‖A j a‖ * ‖A l b‖ * D) =
            (∑ b, ‖A j a‖ * ‖A l b‖) * D := by
        simpa using (Finset.sum_mul Finset.univ
          (fun b : Fin n ↦ ‖A j a‖ * ‖A l b‖) D).symm
      calc
        (∑ a, ∑ b, ‖A j a‖ * ‖A l b‖ * D) =
            ∑ a, (∑ b, ‖A j a‖ * ‖A l b‖) * D := by
          apply Finset.sum_congr rfl
          intro a ha
          exact hinner a
        _ = (∑ a, ∑ b, ‖A j a‖ * ‖A l b‖) * D := by
          simpa using (Finset.sum_mul Finset.univ
            (fun a : Fin n ↦ ∑ b, ‖A j a‖ * ‖A l b‖) D).symm
    _ = (∑ a, ‖A j a‖) * (∑ b, ‖A l b‖) * D := by
      rw [Finset.sum_mul_sum]
    _ ≤ (n : ℝ) * B * D := by
      exact mul_le_mul_of_nonneg_right
        (relativeFrameTransfer_product_l1_bound A B hB j l (hrow j) (hrow l)) hD

end KahlerForm
