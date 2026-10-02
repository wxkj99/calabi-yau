module

public import CalabiYau.MongeAmpere.Estimates.C3.CalabiEnergy
import CalabiYau.Geometry.Complex.Forms.Positive
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.BochnerIdentity
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ConnectionLaplacian
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.DerivativeSquares
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciActionBound
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivativeBound
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceContractionBound

/-!
# Calabi's energy Laplacian inequality

Székelyhidi, §3.3, Lemma 3.9, equations (3.11)–(3.15), p. 45, gives a lower bound for the
Laplacian of the squared difference of the two Kähler connections. For the CY equation,
`Ric(ωφ) = Ric(ω₀) - i∂∂̄G`; the uniform `C³` bound on `G` controls the derivatives of Ricci
appearing there. The metric comparison controls all remaining contractions.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

/-- A five-covariant tensor contraction is controlled by the column norms of its frame matrix.
This is the abstract norm-transfer step used after controlling the tensor in an intrinsic metric
norm; it does not normalize chart-coordinate entries to be at most one. -/
private theorem c3_tensor5_frame_sum_bound
    (P : Matrix (Fin n) (Fin n) ℂ)
    (T : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ)
    (L D : ℝ) (hL : 0 ≤ L)
    (hcol : ∀ j, ∑ i : Fin n, ‖P i j‖ ^ 2 ≤ L ^ 2)
    (hT : ∀ a b c d e, ‖T a b c d e‖ ≤ D)
    (s p q j k : Fin n) :
    ‖∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, ∑ e : Fin n,
      P a s * P b p * star (P c q) * P d j * star (P e k) * T a b c d e‖ ≤
        (n : ℝ) ^ 5 * L ^ 5 * D := by
  have hentry (i j : Fin n) : ‖P i j‖ ≤ L := by
    have hsq : ‖P i j‖ ^ 2 ≤ L ^ 2 := by
      calc
        ‖P i j‖ ^ 2 ≤ ∑ a : Fin n, ‖P a j‖ ^ 2 :=
          Finset.single_le_sum (fun a ha => sq_nonneg ‖P a j‖) (Finset.mem_univ i)
        _ ≤ L ^ 2 := hcol j
    nlinarith [sq_nonneg (‖P i j‖ - L)]
  have hterm (a b c d e : Fin n) :
      ‖P a s * P b p * star (P c q) * P d j * star (P e k) * T a b c d e‖ ≤
        L ^ 5 * D := by
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_star, norm_star]
    have hprod : ‖P a s‖ * ‖P b p‖ * ‖P c q‖ * ‖P d j‖ * ‖P e k‖ ≤ L ^ 5 := by
      calc
        ‖P a s‖ * ‖P b p‖ * ‖P c q‖ * ‖P d j‖ * ‖P e k‖ ≤
            L * L * L * L * L := by
          gcongr <;> exact hentry _ _
        _ = L ^ 5 := by ring
    calc
      (‖P a s‖ * ‖P b p‖ * ‖P c q‖ * ‖P d j‖ * ‖P e k‖) * ‖T a b c d e‖ ≤
          L ^ 5 * ‖T a b c d e‖ := mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
      _ ≤ L ^ 5 * D := mul_le_mul_of_nonneg_left (hT a b c d e) (by positivity)
  calc
    ‖∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, ∑ e : Fin n,
        P a s * P b p * star (P c q) * P d j * star (P e k) * T a b c d e‖ ≤
      ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, ∑ e : Fin n,
        ‖P a s * P b p * star (P c q) * P d j * star (P e k) * T a b c d e‖ := by
      apply le_trans (norm_sum_le _ _)
      apply Finset.sum_le_sum
      intro a ha
      apply le_trans (norm_sum_le _ _)
      apply Finset.sum_le_sum
      intro b hb
      apply le_trans (norm_sum_le _ _)
      apply Finset.sum_le_sum
      intro c hc
      apply le_trans (norm_sum_le _ _)
      apply Finset.sum_le_sum
      intro d hd
      exact norm_sum_le _ _
    _ ≤ ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, ∑ e : Fin n,
        L ^ 5 * D := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      apply Finset.sum_le_sum
      intro c hc
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      exact hterm a b c d e
    _ = (n : ℝ) ^ 5 * L ^ 5 * D := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring

private theorem c3_frame_entry_bound_of_inverse_diagonal
    {n : ℕ} (A P : Matrix (Fin n) (Fin n) ℂ) (Q : ℝ) (hQ : 0 ≤ Q)
    (hAinv : A⁻¹ = P.map star * P.transpose)
    (hdiag : ∀ i, RCLike.re (A⁻¹ i i) ≤ Q) :
    ∀ i j, ‖P i j‖ ≤ Real.sqrt Q := by
  intro i j
  have hz (z : ℂ) : ‖z‖ ^ 2 = RCLike.re (star z * z) := by
    calc
      ‖z‖ ^ 2 = Complex.normSq z := (Complex.normSq_eq_norm_sq z).symm
      _ = RCLike.re (star z * z) := by
        have hc : (Complex.normSq z : ℂ) = star z * z := by
          simpa using Complex.normSq_eq_conj_mul_self (z := z)
        rw [← hc]
        simp
  have hsum : ∑ b : Fin n, ‖P i b‖ ^ 2 = RCLike.re ((P.map star * P.transpose) i i) := by
    calc
      ∑ b : Fin n, ‖P i b‖ ^ 2 =
          ∑ b : Fin n, RCLike.re (star (P i b) * P i b) := by
        apply Finset.sum_congr rfl
        intro b hb
        exact hz (P i b)
      _ = RCLike.re (∑ b : Fin n, star (P i b) * P i b) := by simp
      _ = RCLike.re ((P.map star * P.transpose) i i) := by
        simp [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply]
  have hrow : ∑ b : Fin n, ‖P i b‖ ^ 2 ≤ Q := by
    rw [hsum, ← hAinv]
    exact hdiag i
  have hentry : ‖P i j‖ ^ 2 ≤ Q := by
    exact (Finset.single_le_sum (fun b hb => sq_nonneg ‖P i b‖)
      (Finset.mem_univ j)).trans hrow
  have hsqrt : 0 ≤ Real.sqrt Q := Real.sqrt_nonneg _
  have hnorm : 0 ≤ ‖P i j‖ := norm_nonneg _
  nlinarith [Real.sq_sqrt hQ]

private theorem c3_inverse_frame_metric {n : ℕ}
    (A Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q.transpose * A * Q.map star = 1)
    (hQR : Q * Q⁻¹ = 1) :
    Q⁻¹.transpose * (Q⁻¹).map star = A := by
  have hTranspose : Q⁻¹.transpose * Q.transpose = 1 := by
    rw [← Matrix.transpose_mul, hQR]
    simp
  have hMap : Q.map star * (Q⁻¹).map star = 1 := by
    have hm : (Q * Q⁻¹).map star = Q.map star * (Q⁻¹).map star := by
      ext i j
      simp [Matrix.map, Matrix.mul_apply]
    rw [← hm, hQR]
    ext i j
    simp [Matrix.map, Matrix.one_apply]
  calc
    Q⁻¹.transpose * (Q⁻¹).map star = Q⁻¹.transpose * 1 * (Q⁻¹).map star := by simp
    _ = Q⁻¹.transpose * (Q.transpose * A * Q.map star) * (Q⁻¹).map star := by rw [hQ]
    _ = Q⁻¹.transpose * Q.transpose * A * (Q.map star * (Q⁻¹).map star) := by
      simp [Matrix.mul_assoc]
    _ = 1 * A * 1 := by rw [hTranspose, hMap]
    _ = A := by simp

private theorem c3_chart_frame_entry_bound_of_inverse_diagonal
    {n : ℕ} (A P : Matrix (Fin n) (Fin n) ℂ) (Q : ℝ) (hQ : 0 ≤ Q)
    (hP : P.transpose * A * P.map star = 1)
    (hdiag : ∀ i, RCLike.re (A⁻¹ i i) ≤ Q) :
    ∀ i j, ‖P i j‖ ≤ Real.sqrt Q := by
  have hdet := congrArg Matrix.det hP
  have hdet' : P.det * (A.det * (P.map star).det) = 1 := by
    simpa [Matrix.det_mul, Matrix.det_transpose, Matrix.mul_assoc] using hdet
  have hPdet : IsUnit P.det := IsUnit.of_mul_eq_one _ hdet'
  have hQR : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPdet
  have hRP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPdet
  have hA : P⁻¹.transpose * (P⁻¹).map star = A :=
    c3_inverse_frame_metric A P hP hQR
  have hTranspose : P.transpose * P⁻¹.transpose = 1 := by
    rw [← Matrix.transpose_mul, hRP]
    simp
  have hMap : P.map star * (P⁻¹).map star = 1 := by
    have hm : (P * P⁻¹).map star = P.map star * (P⁻¹).map star := by
      ext i j
      simp [Matrix.map, Matrix.mul_apply]
    rw [← hm, hQR]
    ext i j
    simp [Matrix.map, Matrix.one_apply]
  have hAleft : (P.map star * P.transpose) * A = 1 := by
    rw [← hA]
    calc
      (P.map star * P.transpose) * (P⁻¹.transpose * (P⁻¹).map star) =
          P.map star * (P.transpose * P⁻¹.transpose) * (P⁻¹).map star := by
            simp [Matrix.mul_assoc]
      _ = P.map star * 1 * (P⁻¹).map star := by rw [hTranspose]
      _ = P.map star * (P⁻¹).map star := by simp
      _ = 1 := hMap
  have hAinv : A⁻¹ = P.map star * P.transpose := by
    apply Matrix.inv_eq_left_inv
    exact hAleft
  exact c3_frame_entry_bound_of_inverse_diagonal A P Q hQ hAinv hdiag

private theorem c3_norm_sum_mul_le {ι : Type*} [Fintype ι] (f g : ι → ℂ)
    (C : ℝ) (hg : ∀ i, ‖g i‖ ≤ C) :
    ‖∑ i, f i * g i‖ ≤ C * ∑ i, ‖f i‖ := by
  calc
    ‖∑ i, f i * g i‖ ≤ ∑ i, ‖f i * g i‖ := norm_sum_le _ _
    _ ≤ ∑ i, C * ‖f i‖ := Finset.sum_le_sum fun i hi => by
      rw [norm_mul, mul_comm (‖f i‖) (‖g i‖)]
      exact mul_le_mul_of_nonneg_right (hg i) (norm_nonneg (f i))
    _ = C * ∑ i, ‖f i‖ := by rw [Finset.mul_sum]

private theorem c3_norm_sum_component_product_le {ι : Type*} [Fintype ι]
    (f g : ι → ℂ) (C D : ℝ) (hC : 0 ≤ C)
    (hf : ∀ i, ‖f i‖ ≤ C) (hg : ∀ i, ‖g i‖ ≤ D) :
    ‖∑ i, f i * g i‖ ≤ (Fintype.card ι : ℝ) * (C * D) := by
  calc
    ‖∑ i, f i * g i‖ ≤ ∑ i, ‖f i * g i‖ := norm_sum_le _ _
    _ ≤ ∑ i, C * D := Finset.sum_le_sum fun i hi => by
      rw [norm_mul]
      exact mul_le_mul (hf i) (hg i) (norm_nonneg (g i)) hC
    _ = (Fintype.card ι : ℝ) * (C * D) := by simp

private theorem c3_triple_contraction_bound_of_chart_frame_entry_bound {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℂ) (T : Fin n → Fin n → Fin n → ℂ)
    (Pbound B : ℝ) (hPbound : 0 ≤ Pbound)
    (hP : ∀ a b, ‖P a b‖ ≤ Pbound)
    (hT : ∀ a b c, ‖T a b c‖ ≤ B) (i j k : Fin n) :
    ‖∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
      P a i * P b j * star (P c k) * T a b c‖ ≤
        (n : ℝ)^3 * Pbound^3 * B := by
  have hterm (a b c : Fin n) :
      ‖P a i * P b j * star (P c k) * T a b c‖ ≤ Pbound^3 * B := by
    rw [norm_mul, norm_mul, norm_mul, norm_star]
    have h1 : ‖P a i‖ * ‖P b j‖ ≤ Pbound * Pbound :=
      mul_le_mul (hP a i) (hP b j) (norm_nonneg _) hPbound
    have h2 : (‖P a i‖ * ‖P b j‖) * ‖P c k‖ ≤ Pbound * Pbound * Pbound :=
      mul_le_mul h1 (hP c k) (norm_nonneg _) (mul_nonneg hPbound hPbound)
    have h3 : ‖P a i‖ * ‖P b j‖ * ‖P c k‖ ≤ Pbound^3 := by
      nlinarith [h2]
    calc
      (‖P a i‖ * ‖P b j‖ * ‖P c k‖) * ‖T a b c‖ ≤
          Pbound^3 * ‖T a b c‖ :=
        mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
      _ ≤ Pbound^3 * B :=
        mul_le_mul_of_nonneg_left (hT a b c) (by positivity)
  calc
    ‖∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
        P a i * P b j * star (P c k) * T a b c‖ ≤
      ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
        ‖P a i * P b j * star (P c k) * T a b c‖ := by
      apply le_trans (norm_sum_le _ _)
      apply Finset.sum_le_sum
      intro a ha
      apply le_trans (norm_sum_le _ _)
      apply Finset.sum_le_sum
      intro b hb
      exact norm_sum_le _ _
    _ ≤ ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, Pbound^3 * B := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      apply Finset.sum_le_sum
      intro c hc
      exact hterm a b c
    _ = (n : ℝ)^3 * Pbound^3 * B := by simp [Finset.sum_const, nsmul_eq_mul]; ring

private theorem c3_quintuple_contraction_bound_of_chart_frame_entry_bound {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℂ)
    (T : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ)
    (Pbound B : ℝ) (hPbound : 0 ≤ Pbound)
    (hP : ∀ a b, ‖P a b‖ ≤ Pbound)
    (hT : ∀ a b c d e, ‖T a b c d e‖ ≤ B)
    (s p q j k : Fin n) :
    ‖∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, ∑ e : Fin n,
      P a s * P b p * star (P c q) * P d j * star (P e k) * T a b c d e‖ ≤
        (n : ℝ)^5 * Pbound^5 * B := by
  have hterm (a b c d e : Fin n) :
      ‖P a s * P b p * star (P c q) * P d j * star (P e k) * T a b c d e‖ ≤
        Pbound^5 * B := by
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_star, norm_star]
    have h1 : ‖P a s‖ * ‖P b p‖ ≤ Pbound * Pbound :=
      mul_le_mul (hP a s) (hP b p) (norm_nonneg _) hPbound
    have h2 : (‖P a s‖ * ‖P b p‖) * ‖P c q‖ ≤ Pbound^3 := by
      have h := mul_le_mul h1 (hP c q) (norm_nonneg _) (mul_nonneg hPbound hPbound)
      nlinarith [h]
    have h3 : ((‖P a s‖ * ‖P b p‖) * ‖P c q‖) * ‖P d j‖ ≤ Pbound^4 := by
      have h := mul_le_mul h2 (hP d j) (norm_nonneg _) (by positivity : 0 ≤ Pbound^3)
      nlinarith [h]
    have h4 : (((‖P a s‖ * ‖P b p‖) * ‖P c q‖) * ‖P d j‖) * ‖P e k‖ ≤
        Pbound^5 := by
      have h := mul_le_mul h3 (hP e k) (norm_nonneg _) (by positivity : 0 ≤ Pbound^4)
      nlinarith [h]
    calc
      (((‖P a s‖ * ‖P b p‖) * ‖P c q‖) * ‖P d j‖) * ‖P e k‖ *
          ‖T a b c d e‖ ≤ Pbound^5 * ‖T a b c d e‖ :=
        mul_le_mul_of_nonneg_right h4 (norm_nonneg _)
      _ ≤ Pbound^5 * B :=
        mul_le_mul_of_nonneg_left (hT a b c d e) (by positivity)
  calc
    ‖∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, ∑ e : Fin n,
        P a s * P b p * star (P c q) * P d j * star (P e k) * T a b c d e‖ ≤
      ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, ∑ e : Fin n,
        ‖P a s * P b p * star (P c q) * P d j * star (P e k) * T a b c d e‖ := by
      apply le_trans (norm_sum_le _ _)
      apply Finset.sum_le_sum
      intro a ha
      apply le_trans (norm_sum_le _ _)
      apply Finset.sum_le_sum
      intro b hb
      apply le_trans (norm_sum_le _ _)
      apply Finset.sum_le_sum
      intro c hc
      apply le_trans (norm_sum_le _ _)
      apply Finset.sum_le_sum
      intro d hd
      exact norm_sum_le _ _
    _ ≤ ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, ∑ e : Fin n,
        Pbound^5 * B := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      apply Finset.sum_le_sum
      intro c hc
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      exact hterm a b c d e
    _ = (n : ℝ)^5 * Pbound^5 * B := by simp [Finset.sum_const, nsmul_eq_mul]; ring

private theorem c3_chart_orthonormal_quintuple_contraction_bound {n : ℕ}
    (A P : Matrix (Fin n) (Fin n) ℂ)
    (T : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ)
    (Pbound B : ℝ) (hPbound : 0 ≤ Pbound)
    (hP : P.transpose * A * P.map star = 1)
    (hInvDiag : ∀ i, RCLike.re (A⁻¹ i i) ≤ Pbound)
    (hT : ∀ a b c d e, ‖T a b c d e‖ ≤ B)
    (s p q j k : Fin n) :
    ‖∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, ∑ e : Fin n,
      P a s * P b p * star (P c q) * P d j * star (P e k) * T a b c d e‖ ≤
        (n : ℝ)^5 * (Real.sqrt Pbound)^5 * B := by
  have hPentry : ∀ a b, ‖P a b‖ ≤ Real.sqrt Pbound :=
    c3_chart_frame_entry_bound_of_inverse_diagonal A P Pbound hPbound hP hInvDiag
  exact c3_quintuple_contraction_bound_of_chart_frame_entry_bound P T
    (Real.sqrt Pbound) B (Real.sqrt_nonneg Pbound) hPentry hT s p q j k

private theorem c3_frame_connection_curvature_action_bound {n : ℕ}
    (T : Fin n → Fin n → Fin n → ℂ)
    (R : Fin n → Fin n → Fin n → Fin n → ℂ)
    (E Tbound K : ℝ) (hTnonneg : 0 ≤ Tbound)
    (hT : ∀ i j k, ‖T i j k‖ ≤ Tbound * Real.sqrt E)
    (hR : ∀ i j k l, ‖R i j k l‖ ≤ K)
    (j k l : Fin n) :
    ‖∑ i : Fin n, T i j k * R i k l j‖ ≤
      (n : ℝ) * Tbound * K * Real.sqrt E := by
  have hC : 0 ≤ Tbound * Real.sqrt E :=
    mul_nonneg hTnonneg (Real.sqrt_nonneg E)
  have h := c3_norm_sum_component_product_le
    (fun i : Fin n ↦ T i j k) (fun i : Fin n ↦ R i k l j)
    (Tbound * Real.sqrt E) K hC
    (fun i ↦ hT i j k) (fun i ↦ hR i k l j)
  calc
    ‖∑ i : Fin n, T i j k * R i k l j‖ ≤
        (Fintype.card (Fin n) : ℝ) * ((Tbound * Real.sqrt E) * K) := h
    _ = (n : ℝ) * Tbound * K * Real.sqrt E := by
      simp only [Fintype.card_fin]
      ring

private theorem c3_frame_ricci_derivative_action_bound {n : ℕ}
    (T V : Fin n → ℂ) (E Tbound D : ℝ) (hE : 0 ≤ E)
    (hTnonneg : 0 ≤ Tbound)
    (hT : ∀ i, ‖T i‖ ≤ Tbound * Real.sqrt E)
    (hV : ∀ i, ‖V i‖ ≤ D * (1 + Real.sqrt E)) :
    ‖∑ i : Fin n, T i * V i‖ ≤
      (n : ℝ) * Tbound * D * (Real.sqrt E + E) := by
  have hC : 0 ≤ Tbound * Real.sqrt E :=
    mul_nonneg hTnonneg (Real.sqrt_nonneg E)
  have h := c3_norm_sum_component_product_le T V
    (Tbound * Real.sqrt E) (D * (1 + Real.sqrt E)) hC hT hV
  calc
    ‖∑ i : Fin n, T i * V i‖ ≤
        (Fintype.card (Fin n) : ℝ) *
          ((Tbound * Real.sqrt E) * (D * (1 + Real.sqrt E))) := h
    _ = (n : ℝ) * Tbound * D * (Real.sqrt E + E) := by
      rw [Fintype.card_fin]
      have hs : Real.sqrt E * Real.sqrt E = E := by
        calc
          Real.sqrt E * Real.sqrt E = (Real.sqrt E) ^ 2 := by ring
          _ = E := Real.sq_sqrt hE
      calc
        (n : ℝ) * (Tbound * Real.sqrt E * (D * (1 + Real.sqrt E))) =
            (n : ℝ) * Tbound * D * (Real.sqrt E + Real.sqrt E * Real.sqrt E) := by ring
        _ = (n : ℝ) * Tbound * D * (Real.sqrt E + E) := by rw [hs]

/-- Full three-slot Ricci-derivative action bound. The factor `n^3` counts
all tensor components; the preceding one-slot estimate only counts one sum. -/
private theorem c3_frame_ricci_derivative_action_bound_three_slot
    {n : ℕ} (T V : Fin n → Fin n → Fin n → ℂ)
    (E L D : ℝ) (hE : 0 ≤ E) (hL : 0 ≤ L)
    (hT : ∀ i j k, ‖T i j k‖ ≤ L * Real.sqrt E)
    (hV : ∀ i j k, ‖V i j k‖ ≤ D * (1 + Real.sqrt E)) :
    ‖∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, T i j k * V i j k‖ ≤
      (n : ℝ)^3 * L * D * (Real.sqrt E + E) := by
  have hs : Real.sqrt E * Real.sqrt E = E := by
    calc
      Real.sqrt E * Real.sqrt E = (Real.sqrt E) ^ 2 := by ring
      _ = E := Real.sq_sqrt hE
  have hterm (i j k : Fin n) :
      ‖T i j k * V i j k‖ ≤ L * D * (Real.sqrt E + E) := by
    rw [norm_mul]
    calc
      ‖T i j k‖ * ‖V i j k‖ ≤
          (L * Real.sqrt E) * (D * (1 + Real.sqrt E)) :=
        mul_le_mul (hT i j k) (hV i j k) (norm_nonneg _) (mul_nonneg hL (Real.sqrt_nonneg E))
      _ = L * D * (Real.sqrt E + Real.sqrt E * Real.sqrt E) := by ring
      _ = L * D * (Real.sqrt E + E) := by rw [hs]
  have hsum :
      ‖∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, T i j k * V i j k‖ ≤
        ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ‖T i j k * V i j k‖ := by
    calc
      ‖∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, T i j k * V i j k‖ ≤
          ∑ i : Fin n, ‖∑ j : Fin n, ∑ k : Fin n, T i j k * V i j k‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, ‖∑ k : Fin n, T i j k * V i j k‖ := by
        apply Finset.sum_le_sum
        intro i hi
        exact norm_sum_le _ _
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ‖T i j k * V i j k‖ := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact norm_sum_le _ _
  calc
    ‖∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, T i j k * V i j k‖ ≤
        ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ‖T i j k * V i j k‖ := hsum
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, L * D * (Real.sqrt E + E) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro k hk
      exact hterm i j k
    _ = (n : ℝ)^3 * L * D * (Real.sqrt E + E) := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring

/-- In a unitary frame, a nonnegative tensor energy controls each component. -/
private theorem c3_frame_tensor_component_bound_of_energy_sum
    {n : ℕ} (T : Fin n → Fin n → Fin n → ℂ) (E : ℝ) (hE : 0 ≤ E)
    (henergy : ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ‖T i j k‖ ^ 2 ≤ E) :
    ∀ i j k, ‖T i j k‖ ≤ Real.sqrt E := by
  intro i j k
  have hk : ‖T i j k‖ ^ 2 ≤ ∑ l : Fin n, ‖T i j l‖ ^ 2 :=
    Finset.single_le_sum (fun l hl => sq_nonneg ‖T i j l‖) (Finset.mem_univ k)
  have hj : ∑ l : Fin n, ‖T i j l‖ ^ 2 ≤
      ∑ b : Fin n, ∑ l : Fin n, ‖T i b l‖ ^ 2 := by
    calc
      ∑ l : Fin n, ‖T i j l‖ ^ 2 =
          (fun b : Fin n => ∑ l : Fin n, ‖T i b l‖ ^ 2) j := rfl
      _ ≤ ∑ b : Fin n, (fun b : Fin n => ∑ l : Fin n, ‖T i b l‖ ^ 2) b :=
        Finset.single_le_sum
          (fun b hb => Finset.sum_nonneg fun l hl => sq_nonneg ‖T i b l‖)
          (Finset.mem_univ j)
      _ = ∑ b : Fin n, ∑ l : Fin n, ‖T i b l‖ ^ 2 := by rfl
  have hi : ∑ b : Fin n, ∑ l : Fin n, ‖T i b l‖ ^ 2 ≤
      ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ‖T a b l‖ ^ 2 := by
    calc
      ∑ b : Fin n, ∑ l : Fin n, ‖T i b l‖ ^ 2 =
          (fun a : Fin n => ∑ b : Fin n, ∑ l : Fin n, ‖T a b l‖ ^ 2) i := rfl
      _ ≤ ∑ a : Fin n, (fun a : Fin n => ∑ b : Fin n, ∑ l : Fin n, ‖T a b l‖ ^ 2) a :=
        Finset.single_le_sum
          (fun a ha => Finset.sum_nonneg fun b hb =>
            Finset.sum_nonneg fun l hl => sq_nonneg ‖T a b l‖)
          (Finset.mem_univ i)
      _ = ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ‖T a b l‖ ^ 2 := by rfl
  have hsq : ‖T i j k‖ ^ 2 ≤ E := hk.trans (hj.trans (hi.trans henergy))
  have hsqrt : 0 ≤ Real.sqrt E := Real.sqrt_nonneg E
  have hnorm : 0 ≤ ‖T i j k‖ := norm_nonneg _
  nlinarith [Real.sq_sqrt hE]

/-- The full three-slot Ricci action is controlled by its component energy
and the pointwise growth bound for the contracted Ricci derivative. -/
private theorem c3_frame_ricci_derivative_action_bound_of_energy_sum
    {n : ℕ} (T V : Fin n → Fin n → Fin n → ℂ)
    (E D : ℝ) (hE : 0 ≤ E)
    (henergy : ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ‖T i j k‖ ^ 2 ≤ E)
    (hV : ∀ i j k, ‖V i j k‖ ≤ D * (1 + Real.sqrt E)) :
    ‖∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, T i j k * V i j k‖ ≤
      (n : ℝ)^3 * D * (Real.sqrt E + E) := by
  have hs : Real.sqrt E * Real.sqrt E = E := by
    calc
      Real.sqrt E * Real.sqrt E = (Real.sqrt E) ^ 2 := by ring
      _ = E := Real.sq_sqrt hE
  have hT := c3_frame_tensor_component_bound_of_energy_sum T E hE henergy
  have hterm (i j k : Fin n) :
      ‖T i j k * V i j k‖ ≤ D * (Real.sqrt E + E) := by
    rw [norm_mul]
    calc
      ‖T i j k‖ * ‖V i j k‖ ≤ Real.sqrt E * (D * (1 + Real.sqrt E)) :=
        mul_le_mul (hT i j k) (hV i j k) (norm_nonneg _) (Real.sqrt_nonneg E)
      _ = D * (Real.sqrt E + Real.sqrt E * Real.sqrt E) := by ring
      _ = D * (Real.sqrt E + E) := by rw [hs]
  have hsum :
      ‖∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, T i j k * V i j k‖ ≤
        ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ‖T i j k * V i j k‖ := by
    calc
      ‖∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, T i j k * V i j k‖ ≤
          ∑ i : Fin n, ‖∑ j : Fin n, ∑ k : Fin n, T i j k * V i j k‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, ‖∑ k : Fin n, T i j k * V i j k‖ := by
        apply Finset.sum_le_sum
        intro i hi
        exact norm_sum_le _ _
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ‖T i j k * V i j k‖ := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact norm_sum_le _ _
  calc
    ‖∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, T i j k * V i j k‖ ≤
        ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ‖T i j k * V i j k‖ := hsum
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, D * (Real.sqrt E + E) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro k hk
      exact hterm i j k
    _ = (n : ℝ)^3 * D * (Real.sqrt E + E) := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Absorb the square-root energy error by the energy and a uniform constant.
This is the scalar Young inequality used after the Ricci-derivative action is
bounded by `C * (sqrt E + E)`. -/
private theorem c3_linear_sqrt_energy_absorbed
    (E K : ℝ) (hE : 0 ≤ E) :
    K * Real.sqrt E ≤ E + K ^ 2 / 4 := by
  have hsq : 0 ≤ (Real.sqrt E - K / 2) ^ 2 := sq_nonneg _
  have hroot : (Real.sqrt E) ^ 2 = E := Real.sq_sqrt hE
  nlinarith

private theorem c3PartialBar_mul {n : ℕ}
    {u v : EuclideanSpace ℂ (Fin n) → ℂ} {z : EuclideanSpace ℂ (Fin n)}
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) (j : Fin n) :
    c3PartialBar (fun w ↦ u w * v w) z j =
      c3PartialBar u z j * v z + u z * c3PartialBar v z j := by
  unfold c3PartialBar
  rw [fderiv_fun_mul hu hv]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

private theorem c3PartialZ_mul {n : ℕ}
    {u v : EuclideanSpace ℂ (Fin n) → ℂ} {z : EuclideanSpace ℂ (Fin n)}
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) (j : Fin n) :
    c3PartialZ (fun w ↦ u w * v w) z j =
      c3PartialZ u z j * v z + u z * c3PartialZ v z j := by
  unfold c3PartialZ
  rw [fderiv_fun_mul hu hv]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

private theorem c3PartialZ_add {n : ℕ}
    {u v : EuclideanSpace ℂ (Fin n) → ℂ} {z : EuclideanSpace ℂ (Fin n)}
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) (j : Fin n) :
    c3PartialZ (fun w ↦ u w + v w) z j = c3PartialZ u z j + c3PartialZ v z j := by
  unfold c3PartialZ
  rw [fderiv_fun_add hu hv]
  simp only [_root_.add_apply]
  ring

private theorem c3PartialBar_add {n : ℕ}
    {u v : EuclideanSpace ℂ (Fin n) → ℂ} {z : EuclideanSpace ℂ (Fin n)}
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) (j : Fin n) :
    c3PartialBar (fun w ↦ u w + v w) z j = c3PartialBar u z j + c3PartialBar v z j := by
  unfold c3PartialBar
  rw [fderiv_fun_add hu hv]
  simp only [_root_.add_apply]
  ring

private theorem c3PartialBar_differentiable_at {n : ℕ}
    (f : EuclideanSpace ℂ (Fin n) → ℂ) (hf : ContDiff ℝ 2 f)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
    DifferentiableAt ℝ (fun w ↦ c3PartialBar f w j) z := by
  have hdf : ContDiffAt ℝ 1 (fderiv ℝ f) z :=
    (hf.contDiffAt (x := z)).fderiv_right (m := 1) (by norm_num)
  have hDx : DifferentiableAt ℝ
      (fun w ↦ fderiv ℝ f w (EuclideanSpace.single j 1)) z := by
    exact (ContDiffAt.clm_apply hdf contDiffAt_const).differentiableAt (by norm_num)
  have hDy : DifferentiableAt ℝ
      (fun w ↦ fderiv ℝ f w (Complex.I • EuclideanSpace.single j 1)) z := by
    exact (ContDiffAt.clm_apply hdf contDiffAt_const).differentiableAt (by norm_num)
  change DifferentiableAt ℝ
    (fun w ↦ (fderiv ℝ f w (EuclideanSpace.single j 1) +
      Complex.I * fderiv ℝ f w (Complex.I • EuclideanSpace.single j 1)) / 2) z
  fun_prop

private theorem c3PartialZ_differentiable_at {n : ℕ}
    (f : EuclideanSpace ℂ (Fin n) → ℂ) (hf : ContDiff ℝ 2 f)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
    DifferentiableAt ℝ (fun w ↦ c3PartialZ f w j) z := by
  have hdf : ContDiffAt ℝ 1 (fderiv ℝ f) z :=
    (hf.contDiffAt (x := z)).fderiv_right (m := 1) (by norm_num)
  have hDx : DifferentiableAt ℝ
      (fun w ↦ fderiv ℝ f w (EuclideanSpace.single j 1)) z := by
    exact (ContDiffAt.clm_apply hdf contDiffAt_const).differentiableAt (by norm_num)
  have hDy : DifferentiableAt ℝ
      (fun w ↦ fderiv ℝ f w (Complex.I • EuclideanSpace.single j 1)) z := by
    exact (ContDiffAt.clm_apply hdf contDiffAt_const).differentiableAt (by norm_num)
  change DifferentiableAt ℝ
    (fun w ↦ (fderiv ℝ f w (EuclideanSpace.single j 1) -
      Complex.I * fderiv ℝ f w (Complex.I • EuclideanSpace.single j 1)) / 2) z
  fun_prop

/-- The mixed Wirtinger derivative, taken as `∂z` after `∂bar`. -/
private noncomputable def c3MixedZBar (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n) : ℂ :=
  c3PartialZ (fun w ↦ c3PartialBar f w j) z j

private theorem c3_partialBar_star_of_fderiv_star
    {n : ℕ} (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n)
    (hstar : fderiv ℝ (fun w ↦ star (f w)) z =
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ f z)) :
    c3PartialBar (fun w ↦ star (f w)) z j = star (c3PartialZ f z j) := by
  unfold c3PartialBar c3PartialZ
  rw [hstar]
  simp [ContinuousLinearEquiv.coe_coe]

private theorem c3_partialZ_star_of_fderiv_star
    {n : ℕ} (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n)
    (hstar : fderiv ℝ (fun w ↦ star (f w)) z =
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ f z)) :
    c3PartialZ (fun w ↦ star (f w)) z j = star (c3PartialBar f z j) := by
  unfold c3PartialBar c3PartialZ
  rw [hstar]
  simp [ContinuousLinearEquiv.coe_coe]
  ring

/-- The two real directional derivatives in the Hessian of a real-C² function commute. -/
private theorem c3_real_second_derivative_commute {n : ℕ}
    (f : EuclideanSpace ℂ (Fin n) → ℂ) (hf : ContDiff ℝ 2 f)
    (x u v : EuclideanSpace ℂ (Fin n)) :
    fderiv ℝ (fderiv ℝ f) x u v = fderiv ℝ (fderiv ℝ f) x v u := by
  have hs := ContDiffAt.isSymmSndFDerivAt (hf.contDiffAt (x := x)) (by norm_num)
  exact hs u v

private theorem c3_second_directional_fderiv {n : ℕ}
    (f : EuclideanSpace ℂ (Fin n) → ℂ) (hf : ContDiff ℝ 2 f)
    (x u v : EuclideanSpace ℂ (Fin n)) :
    fderiv ℝ (fun y ↦ fderiv ℝ f y v) x u =
      fderiv ℝ (fderiv ℝ f) x u v := by
  have hD : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.contDiffAt (x := x)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hc := fderiv_clm_apply hD (differentiableAt_const v)
  rw [hc]
  simp [ContinuousLinearMap.flip_apply]

private theorem c3_partialBar_deriv_apply {n : ℕ}
    (f : EuclideanSpace ℂ (Fin n) → ℂ) (hf : ContDiff ℝ 2 f)
    (z u : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
    fderiv ℝ (fun y ↦ c3PartialBar f y j) z u =
      (fderiv ℝ (fderiv ℝ f) z u (EuclideanSpace.single j 1) +
        Complex.I * fderiv ℝ (fderiv ℝ f) z u (Complex.I • EuclideanSpace.single j 1)) / 2 := by
  have he : DifferentiableAt ℝ (fun y ↦ fderiv ℝ f y (EuclideanSpace.single j 1)) z :=
    (ContDiffAt.clm_apply ((hf.contDiffAt (x := z)).fderiv_right (m := 1) (by norm_num))
      contDiffAt_const).differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hie : DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ f y (Complex.I • EuclideanSpace.single j 1)) z :=
    (ContDiffAt.clm_apply ((hf.contDiffAt (x := z)).fderiv_right (m := 1) (by norm_num))
      contDiffAt_const).differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hs : DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ f y (EuclideanSpace.single j 1) +
        Complex.I * fderiv ℝ f y (Complex.I • EuclideanSpace.single j 1)) z :=
    he.add (hie.const_mul Complex.I)
  unfold c3PartialBar
  rw [show (fun y ↦ (fderiv ℝ f y (EuclideanSpace.single j 1) +
        Complex.I * fderiv ℝ f y (Complex.I • EuclideanSpace.single j 1)) / 2) =
      (fun y ↦ (fderiv ℝ f y (EuclideanSpace.single j 1) +
        Complex.I * fderiv ℝ f y (Complex.I • EuclideanSpace.single j 1)) * (2 : ℂ)⁻¹) by
        funext y; rw [div_eq_mul_inv]]
  rw [fderiv_mul_const hs (2 : ℂ)⁻¹]
  rw [fderiv_fun_add he (hie.const_mul Complex.I)]
  rw [fderiv_const_mul hie Complex.I]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [c3_second_directional_fderiv f hf z u (EuclideanSpace.single j 1),
    c3_second_directional_fderiv f hf z u (Complex.I • EuclideanSpace.single j 1)]
  ring

private theorem c3_partialZ_deriv_apply {n : ℕ}
    (f : EuclideanSpace ℂ (Fin n) → ℂ) (hf : ContDiff ℝ 2 f)
    (z u : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
    fderiv ℝ (fun y ↦ c3PartialZ f y j) z u =
      (fderiv ℝ (fderiv ℝ f) z u (EuclideanSpace.single j 1) -
        Complex.I * fderiv ℝ (fderiv ℝ f) z u (Complex.I • EuclideanSpace.single j 1)) / 2 := by
  have he : DifferentiableAt ℝ (fun y ↦ fderiv ℝ f y (EuclideanSpace.single j 1)) z :=
    (ContDiffAt.clm_apply ((hf.contDiffAt (x := z)).fderiv_right (m := 1) (by norm_num))
      contDiffAt_const).differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hie : DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ f y (Complex.I • EuclideanSpace.single j 1)) z :=
    (ContDiffAt.clm_apply ((hf.contDiffAt (x := z)).fderiv_right (m := 1) (by norm_num))
      contDiffAt_const).differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hs : DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ f y (EuclideanSpace.single j 1) -
        Complex.I * fderiv ℝ f y (Complex.I • EuclideanSpace.single j 1)) z :=
    he.sub (hie.const_mul Complex.I)
  unfold c3PartialZ
  rw [show (fun y ↦ (fderiv ℝ f y (EuclideanSpace.single j 1) -
        Complex.I * fderiv ℝ f y (Complex.I • EuclideanSpace.single j 1)) / 2) =
      (fun y ↦ (fderiv ℝ f y (EuclideanSpace.single j 1) -
        Complex.I * fderiv ℝ f y (Complex.I • EuclideanSpace.single j 1)) * (2 : ℂ)⁻¹) by
        funext y; rw [div_eq_mul_inv]]
  rw [fderiv_mul_const hs (2 : ℂ)⁻¹]
  rw [fderiv_fun_sub he (hie.const_mul Complex.I)]
  rw [fderiv_const_mul hie Complex.I]
  simp only [_root_.sub_apply, _root_.smul_apply, smul_eq_mul]
  rw [c3_second_directional_fderiv f hf z u (EuclideanSpace.single j 1),
    c3_second_directional_fderiv f hf z u (Complex.I • EuclideanSpace.single j 1)]
  ring

private theorem c3_mixedWirtinger_commute {n : ℕ}
    (f : EuclideanSpace ℂ (Fin n) → ℂ) (hf : ContDiff ℝ 2 f)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
    c3PartialZ (fun w ↦ c3PartialBar f w j) z j =
      c3PartialBar (fun w ↦ c3PartialZ f w j) z j := by
  change (fderiv ℝ (fun w ↦ c3PartialBar f w j) z (EuclideanSpace.single j 1) -
      Complex.I * fderiv ℝ (fun w ↦ c3PartialBar f w j) z
        (Complex.I • EuclideanSpace.single j 1)) / 2 =
    (fderiv ℝ (fun w ↦ c3PartialZ f w j) z (EuclideanSpace.single j 1) +
      Complex.I * fderiv ℝ (fun w ↦ c3PartialZ f w j) z
        (Complex.I • EuclideanSpace.single j 1)) / 2
  rw [c3_partialBar_deriv_apply f hf z (EuclideanSpace.single j 1) j,
    c3_partialBar_deriv_apply f hf z (Complex.I • EuclideanSpace.single j 1) j,
    c3_partialZ_deriv_apply f hf z (EuclideanSpace.single j 1) j,
    c3_partialZ_deriv_apply f hf z (Complex.I • EuclideanSpace.single j 1) j]
  have hcomm := c3_real_second_derivative_commute f hf z
    (EuclideanSpace.single j 1) (Complex.I • EuclideanSpace.single j 1)
  rw [hcomm]
  ring

/-- The two cross terms in the mixed derivative of a complex squared norm combine
into twice their real Hermitian pairing. -/
private theorem c3_real_star_cross (u v : ℂ) :
    RCLike.re (star u * v + star v * u) = 2 * RCLike.re (star u * v) := by
  change (star u * v + star v * u).re = 2 * (star u * v).re
  simp only [Complex.add_re, Complex.mul_re, Complex.star_def, Complex.conj_re,
    Complex.conj_im]
  ring

/-- The algebraic product rule for a complex-valued mixed two-jet of a norm square:
its two first-jet contributions are the squared norms of the holomorphic and
antiholomorphic first derivatives. -/
private theorem c3_mixed_normSq_jet_algebra (f z b h : ℂ) :
    RCLike.re (h * star f + z * star z + b * star b + f * star h) =
      2 * RCLike.re (star f * h) + ‖z‖ ^ 2 + ‖b‖ ^ 2 := by
  have hcross := c3_real_star_cross f h
  have hnorm (w : ℂ) : RCLike.re (w * star w) = ‖w‖ ^ 2 := by
    have hw : (Complex.normSq w : ℂ) = w * star w := by
      simpa [mul_comm] using Complex.normSq_eq_conj_mul_self (z := w)
    calc
      RCLike.re (w * star w) = RCLike.re (Complex.normSq w : ℂ) := by rw [← hw]
      _ = Complex.normSq w := by simp
      _ = ‖w‖ ^ 2 := Complex.normSq_eq_norm_sq _
  change (h * star f + z * star z + b * star b + f * star h).re = _
  simp only [Complex.add_re]
  change RCLike.re (h * star f) + RCLike.re (z * star z) +
      RCLike.re (b * star b) + RCLike.re (f * star h) = _
  have hc : RCLike.re (h * star f + f * star h) =
      2 * RCLike.re (star f * h) := by
    convert hcross using 1
    simp [mul_comm]
  have hadd : RCLike.re (h * star f + f * star h) =
      RCLike.re (h * star f) + RCLike.re (f * star h) := by
    change (h * star f + f * star h).re = _
    exact Complex.add_re _ _
  rw [hnorm z, hnorm b, ← hc, hadd]
  abel_nf

private theorem c3_mixed_normSq_hessian_of_star_bridge
    (f : EuclideanSpace ℂ (Fin n) → ℂ) (hf : ContDiff ℝ 2 f)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n)
    (hstar : ∀ (g : EuclideanSpace ℂ (Fin n) → ℂ) (x : EuclideanSpace ℂ (Fin n)),
      DifferentiableAt ℝ g x →
        HasFDerivAt (fun w ↦ star (g w))
          ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ g x)) x) :
    RCLike.re (c3MixedZBar (fun w ↦ f w * star (f w)) z j) =
      ‖c3PartialZ f z j‖ ^ 2 + ‖c3PartialBar f z j‖ ^ 2 +
        2 * RCLike.re (star (f z) * c3MixedZBar f z j) := by
  let a : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ c3PartialZ f x j
  let b : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ c3PartialBar f x j
  let u : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ b x * star (f x)
  let v : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ f x * star (a x)
  have hfdiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ f x :=
    (hf.contDiffAt (x := x)).differentiableAt (by norm_num)
  have hstarF (x : EuclideanSpace ℂ (Fin n)) :
      HasFDerivAt (fun w ↦ star (f w))
        ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ f x)) x :=
    hstar f x (hfdiff x)
  have haDiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ a x :=
    c3PartialZ_differentiable_at f hf x j
  have hbDiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ b x :=
    c3PartialBar_differentiable_at f hf x j
  have hstarA (x : EuclideanSpace ℂ (Fin n)) :
      HasFDerivAt (fun w ↦ star (a w))
        ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ a x)) x :=
    hstar a x (haDiff x)
  have hbar : (fun x ↦ c3PartialBar (fun w ↦ f w * star (f w)) x j) =
      (fun x ↦ u x + v x) := by
    funext x
    rw [c3PartialBar_mul (hfdiff x) (hstarF x).differentiableAt j]
    rw [c3_partialBar_star_of_fderiv_star f x j (hstarF x).fderiv]
  have hmix : c3MixedZBar (fun w ↦ f w * star (f w)) z j =
      c3PartialZ (fun x ↦ u x + v x) z j := by
    unfold c3MixedZBar
    rw [hbar]
  rw [hmix, c3PartialZ_add (u := u) (v := v)
    ((hbDiff z).mul (hstarF z).differentiableAt)
    ((hfdiff z).mul (hstarA z).differentiableAt) j]
  change RCLike.re (c3PartialZ (fun x ↦ b x * star (f x)) z j +
      c3PartialZ (fun x ↦ f x * star (a x)) z j) = _
  rw [c3PartialZ_mul (u := b) (v := fun x ↦ star (f x))
      (hbDiff z) (hstarF z).differentiableAt j,
    c3PartialZ_mul (u := f) (v := fun x ↦ star (a x))
      (hfdiff z) (hstarA z).differentiableAt j]
  rw [c3_partialZ_star_of_fderiv_star f z j (hstarF z).fderiv,
    c3_partialZ_star_of_fderiv_star a z j (hstarA z).fderiv,
    c3_mixedWirtinger_commute f hf z j]
  have hlast : c3PartialBar a z j = c3MixedZBar f z j :=
    (c3_mixedWirtinger_commute f hf z j).symm
  rw [hlast]
  have halpha : c3MixedZBar f z j = c3PartialZ b z j := rfl
  rw [halpha]
  have hjet := c3_mixed_normSq_jet_algebra
    (f z) (a z) (b z) (c3PartialZ b z j)
  simpa [a, b, add_assoc, add_left_comm, add_comm] using hjet

/-- For an arbitrary real-C² complex-valued function, the diagonal mixed derivative
of its squared norm has two first-derivative squares and the mixed-jet remainder. -/
private theorem c3_mixed_normSq_hessian
    (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (hf : ContDiff ℝ 2 f) (z : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
    RCLike.re (c3MixedZBar (fun w ↦ f w * star (f w)) z j) =
      ‖c3PartialZ f z j‖ ^ 2 + ‖c3PartialBar f z j‖ ^ 2 +
        2 * RCLike.re (star (f z) * c3MixedZBar f z j) := by
  apply c3_mixed_normSq_hessian_of_star_bridge f hf z j
  intro g x hg
  have hconj : HasFDerivAt (fun w : ℂ ↦ star w)
      (Complex.conjCLE : ℂ →L[ℝ] ℂ) (g x) :=
    Complex.conjCLE.hasFDerivAt (x := g x)
  exact hconj.comp x hg.hasFDerivAt

/-- Jet-level Leibniz expansion for a varying Hermitian weight times a complex
squared norm. The first-jet terms of the weight are retained explicitly; its mixed
second jet is not discarded at a normal frame. -/
private theorem c3_weighted_normSq_mixed_jet_algebra
    (w wz wb wzb f z b h : ℂ) :
    RCLike.re (wzb * f * star f + wz * (b * star f + f * star z) +
      wb * (z * star f + f * star b) +
      w * (h * star f + b * star b + z * star z + f * star h)) =
      RCLike.re (wzb * f * star f + wz * b * star f + wz * f * star z +
        wb * z * star f + wb * f * star b + w * h * star f +
        w * b * star b + w * z * star z + w * f * star h) := by
  congr 1
  ring

/-- Actual mixed-jet Leibniz formula for a varying complex weight multiplying the
squared norm of a real-C² function. No first or second weight derivatives are
suppressed; this is the scalar contraction needed before summing a tensor norm. -/
private theorem c3_weighted_normSq_mixed_hessian_of_star_bridge
    (w f : EuclideanSpace ℂ (Fin n) → ℂ)
    (hw : ContDiff ℝ 2 w) (hf : ContDiff ℝ 2 f)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n)
    (hstar : ∀ (g : EuclideanSpace ℂ (Fin n) → ℂ) (x : EuclideanSpace ℂ (Fin n)),
      DifferentiableAt ℝ g x →
        HasFDerivAt (fun y ↦ star (g y))
          ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ g x)) x) :
    RCLike.re (c3MixedZBar (fun x ↦ w x * (f x * star (f x))) z j) =
      RCLike.re
        (c3MixedZBar w z j * (f z * star (f z)) +
          c3PartialBar w z j *
            (c3PartialZ f z j * star (f z) + f z * star (c3PartialBar f z j)) +
          c3PartialZ w z j *
            (c3PartialBar f z j * star (f z) + f z * star (c3PartialZ f z j)) +
          w z * c3MixedZBar (fun x ↦ f x * star (f x)) z j) := by
  let q : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ f x * star (f x)
  let a : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ c3PartialZ f x j
  let b : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ c3PartialBar f x j
  let wz : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ c3PartialZ w x j
  let wb : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ c3PartialBar w x j
  let u : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ wb x * q x
  let v : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ w x * c3PartialBar q x j
  have hwdiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ w x :=
    (hw.contDiffAt (x := x)).differentiableAt (by norm_num)
  have hfdiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ f x :=
    (hf.contDiffAt (x := x)).differentiableAt (by norm_num)
  have hstarW (x : EuclideanSpace ℂ (Fin n)) :
      HasFDerivAt (fun y ↦ star (w y))
        ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ w x)) x :=
    hstar w x (hwdiff x)
  have hstarF (x : EuclideanSpace ℂ (Fin n)) :
      HasFDerivAt (fun y ↦ star (f y))
        ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ f x)) x :=
    hstar f x (hfdiff x)
  have haDiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ a x :=
    c3PartialZ_differentiable_at f hf x j
  have hbDiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ b x :=
    c3PartialBar_differentiable_at f hf x j
  have hwzDiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ wz x :=
    c3PartialZ_differentiable_at w hw x j
  have hwbDiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ wb x :=
    c3PartialBar_differentiable_at w hw x j
  have hstarA (x : EuclideanSpace ℂ (Fin n)) :
      HasFDerivAt (fun y ↦ star (a y))
        ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ a x)) x :=
    hstar a x (haDiff x)
  have hqDiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ q x :=
    (hfdiff x).mul (hstarF x).differentiableAt
  have hbarQ : (fun x ↦ c3PartialBar q x j) =
      (fun x ↦ b x * star (f x) + f x * star (a x)) := by
    funext x
    rw [c3PartialBar_mul (hfdiff x) (hstarF x).differentiableAt j]
    rw [c3_partialBar_star_of_fderiv_star f x j (hstarF x).fderiv]
  have hZQ : (fun x ↦ c3PartialZ q x j) =
      (fun x ↦ a x * star (f x) + f x * star (b x)) := by
    funext x
    rw [c3PartialZ_mul (u := f) (v := fun y ↦ star (f y))
      (hfdiff x) (hstarF x).differentiableAt j]
    rw [c3_partialZ_star_of_fderiv_star f x j (hstarF x).fderiv]
  have hbarQDiff (x : EuclideanSpace ℂ (Fin n)) :
      DifferentiableAt ℝ (fun y ↦ c3PartialBar q y j) x := by
    rw [hbarQ]
    apply DifferentiableAt.add
    · exact (hbDiff x).mul (hstarF x).differentiableAt
    · exact (hfdiff x).mul (hstarA x).differentiableAt
  have hmixWQ : c3MixedZBar (fun x ↦ w x * q x) z j =
      c3PartialZ (fun x ↦ u x + v x) z j := by
    unfold c3MixedZBar
    change c3PartialZ (fun x ↦ c3PartialBar (fun y ↦ w y * q y) x j) z j = _
    rw [show (fun x ↦ c3PartialBar (fun y ↦ w y * q y) x j) =
        (fun x ↦ u x + v x) by
      funext x
      rw [c3PartialBar_mul (hwdiff x) (hqDiff x) j]]
  rw [hmixWQ, c3PartialZ_add (u := u) (v := v)
    ((hwbDiff z).mul (hqDiff z)) ((hwdiff z).mul (hbarQDiff z)) j]
  change RCLike.re
      (c3PartialZ (fun x ↦ wb x * q x) z j +
        c3PartialZ (fun x ↦ w x * c3PartialBar q x j) z j) = _
  rw [c3PartialZ_mul (u := wb) (v := q) (hwbDiff z) (hqDiff z) j,
    c3PartialZ_mul (u := w) (v := fun x ↦ c3PartialBar q x j)
      (hwdiff z) (hbarQDiff z) j]
  have hbarQz := congrFun hbarQ z
  have hZQz := congrFun hZQ z
  rw [show c3PartialZ wb z j = c3MixedZBar w z j by rfl,
    show c3PartialZ (fun x ↦ c3PartialBar q x j) z j = c3MixedZBar q z j by rfl,
    hbarQz, hZQz]
  congr 1
  ring

/-- Bilinear mixed-jet Leibniz formula for a varying scalar weight and two
independent component fields. This preserves off-diagonal tensor-norm terms
`w * F * star U`, including both first jets and the mixed second jet of `w`. -/
private theorem c3_weighted_pair_mixed_hessian_of_star_bridge
    (w f u : EuclideanSpace ℂ (Fin n) → ℂ)
    (hw : ContDiff ℝ 2 w) (hf : ContDiff ℝ 2 f) (hu : ContDiff ℝ 2 u)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n)
    (hstar : ∀ (g : EuclideanSpace ℂ (Fin n) → ℂ) (x : EuclideanSpace ℂ (Fin n)),
      DifferentiableAt ℝ g x →
        HasFDerivAt (fun y ↦ star (g y))
          ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ g x)) x) :
    RCLike.re (c3MixedZBar (fun x ↦ w x * (f x * star (u x))) z j) =
      RCLike.re
        (c3MixedZBar w z j * (f z * star (u z)) +
          c3PartialBar w z j *
            (c3PartialZ f z j * star (u z) + f z * star (c3PartialBar u z j)) +
          c3PartialZ w z j *
            (c3PartialBar f z j * star (u z) + f z * star (c3PartialZ u z j)) +
          w z *
            (c3MixedZBar f z j * star (u z) +
              c3PartialBar f z j * star (c3PartialBar u z j) +
              c3PartialZ f z j * star (c3PartialZ u z j) +
              f z * star (c3MixedZBar u z j))) := by
  let p : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ f x * star (u x)
  let a : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ c3PartialZ f x j
  let b : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ c3PartialBar f x j
  let c : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ c3PartialZ u x j
  let d : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ c3PartialBar u x j
  let wz : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ c3PartialZ w x j
  let wb : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ c3PartialBar w x j
  let v : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ w x * c3PartialBar p x j
  let r : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ wb x * p x
  let s : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ b x * star (u x)
  let t : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ f x * star (c x)
  have hwdiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ w x :=
    (hw.contDiffAt (x := x)).differentiableAt (by norm_num)
  have hfdiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ f x :=
    (hf.contDiffAt (x := x)).differentiableAt (by norm_num)
  have hudiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ u x :=
    (hu.contDiffAt (x := x)).differentiableAt (by norm_num)
  have hstarW (x : EuclideanSpace ℂ (Fin n)) :
      HasFDerivAt (fun y ↦ star (w y))
        ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ w x)) x :=
    hstar w x (hwdiff x)
  have hstarU (x : EuclideanSpace ℂ (Fin n)) :
      HasFDerivAt (fun y ↦ star (u y))
        ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ u x)) x :=
    hstar u x (hudiff x)
  have haDiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ a x :=
    c3PartialZ_differentiable_at f hf x j
  have hbDiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ b x :=
    c3PartialBar_differentiable_at f hf x j
  have hcDiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ c x :=
    c3PartialZ_differentiable_at u hu x j
  have hdDiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ d x :=
    c3PartialBar_differentiable_at u hu x j
  have hwbDiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ wb x :=
    c3PartialBar_differentiable_at w hw x j
  have hstarC (x : EuclideanSpace ℂ (Fin n)) :
      HasFDerivAt (fun y ↦ star (c y))
        ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ c x)) x :=
    hstar c x (hcDiff x)
  have hpDiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ p x :=
    (hfdiff x).mul (hstarU x).differentiableAt
  have hbarP : (fun x ↦ c3PartialBar p x j) =
      (fun x ↦ s x + t x) := by
    funext x
    rw [c3PartialBar_mul (hfdiff x) (hstarU x).differentiableAt j]
    rw [c3_partialBar_star_of_fderiv_star u x j (hstarU x).fderiv]
  have hZP : (fun x ↦ c3PartialZ p x j) =
      (fun x ↦ a x * star (u x) + f x * star (d x)) := by
    funext x
    rw [c3PartialZ_mul (u := f) (v := fun y ↦ star (u y))
      (hfdiff x) (hstarU x).differentiableAt j]
    rw [c3_partialZ_star_of_fderiv_star u x j (hstarU x).fderiv]
  have hsDiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ s x :=
    (hbDiff x).mul (hstarU x).differentiableAt
  have htDiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ t x :=
    (hfdiff x).mul (hstarC x).differentiableAt
  have hbarPDiff (x : EuclideanSpace ℂ (Fin n)) :
      DifferentiableAt ℝ (fun y ↦ c3PartialBar p y j) x := by
    rw [hbarP]
    exact (hsDiff x).add (htDiff x)
  have hbarWP : (fun x ↦ c3PartialBar (fun y ↦ w y * p y) x j) =
      (fun x ↦ wb x * p x + w x * c3PartialBar p x j) := by
    funext x
    exact c3PartialBar_mul (hwdiff x) (hpDiff x) j
  have hmixedWP : c3MixedZBar (fun x ↦ w x * p x) z j =
      c3PartialZ (fun x ↦ r x + v x) z j := by
    unfold c3MixedZBar
    change c3PartialZ (fun x ↦ c3PartialBar (fun y ↦ w y * p y) x j) z j = _
    rw [hbarWP]
  rw [hmixedWP, c3PartialZ_add (u := r) (v := v)
    ((hwbDiff z).mul (hpDiff z)) ((hwdiff z).mul (hbarPDiff z)) j]
  change RCLike.re
      (c3PartialZ (fun x ↦ wb x * p x) z j +
        c3PartialZ (fun x ↦ w x * c3PartialBar p x j) z j) = _
  rw [c3PartialZ_mul (u := w) (v := fun x ↦ c3PartialBar p x j)
      (hwdiff z) (hbarPDiff z) j,
    c3PartialZ_mul (u := wb) (v := p) (hwbDiff z) (hpDiff z) j]
  have hbarPz := congrFun hbarP z
  have hZPz := congrFun hZP z
  rw [show c3PartialZ wb z j = c3MixedZBar w z j by rfl,
    hbarPz, hZPz]
  have hbarPderiv : c3PartialZ (fun x ↦ c3PartialBar p x j) z j =
      c3PartialZ (fun x ↦ s x + t x) z j := by
    have hfun : (fun x ↦ c3PartialBar p x j) = (fun x ↦ s x + t x) := hbarP
    rw [hfun]
  rw [hbarPderiv, c3PartialZ_add (u := s) (v := t) (hsDiff z) (htDiff z) j]
  rw [c3PartialZ_mul (u := b) (v := fun x ↦ star (u x))
      (hbDiff z) (hstarU z).differentiableAt j,
    c3PartialZ_mul (u := f) (v := fun x ↦ star (c x))
      (hfdiff z) (hstarC z).differentiableAt j]
  rw [show c3PartialZ b z j = c3MixedZBar f z j by rfl,
    c3_partialZ_star_of_fderiv_star u z j (hstarU z).fderiv,
    c3_partialZ_star_of_fderiv_star c z j (hstarC z).fderiv,
    show c3PartialBar c z j = c3MixedZBar u z j by
      exact (c3_mixedWirtinger_commute u hu z j).symm]
  congr 1; ring

omit [T2Space M] in
private theorem c3_finite_cover_glue_five_slot_bound
    (ω₀ : KahlerForm n M)
    (T : M → Fin n → Fin n → Fin n → Fin n → Fin n → ℂ)
    (hlocal : ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ U, ∀ (P : Matrix (Fin n) (Fin n) ℂ),
        Matrix.transpose P *
            ω₀.metricInChart y (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y) * P.map star = 1 →
          ∀ s p q j k : Fin n,
            ‖∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
              ∑ d : Fin n, ∑ e : Fin n,
                P a s * P b p * star (P c q) * P d j * star (P e k) *
                  T y a b c d e‖ ≤ C) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (x : M) (P : Matrix (Fin n) (Fin n) ℂ),
      Matrix.transpose P *
          ω₀.metricInChart x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) * P.map star = 1 →
        ∀ s p q j k : Fin n,
          ‖∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
            ∑ d : Fin n, ∑ e : Fin n,
              P a s * P b p * star (P c q) * P d j * star (P e k) *
                T x a b c d e‖ ≤ A := by
  classical
  choose U hUopen hx hbound using hlocal
  choose C hCnonneg hCbound using hbound
  have hcover : (Set.univ : Set M) ⊆ ⋃ x : M, U x := by
    intro x hxuniv
    exact Set.mem_iUnion.mpr ⟨x, hx x⟩
  obtain ⟨t, ht⟩ := (isCompact_univ : IsCompact (Set.univ : Set M)).elim_finite_subcover
    U hUopen hcover
  let A : ℝ := ∑ x ∈ t, C x
  refine ⟨A, ?_, ?_⟩
  · exact Finset.sum_nonneg fun x hx => hCnonneg x
  · intro x P hP s p q j k
    rcases Set.mem_iUnion₂.mp (ht (Set.mem_univ x)) with ⟨y, hyt, hxy⟩
    have hsingle : C y ≤ ∑ z ∈ t, C z :=
      Finset.single_le_sum (fun z hz => hCnonneg z) hyt
    exact (hCbound y x hxy P hP s p q j k).trans (by simpa [A] using hsingle)

/-- Uniform CY form of Calabi's pointwise inequality `Δ_{ωφ} E ≥ -C E - C`.
Here `E = |Γ(gφ)-Γ(g₀)|²_{gφ}` uses the normalization in `CalabiEnergy`. -/
theorem exists_uniform_calabi_energy_laplacian_lower (ω₀ : KahlerForm n M)
    (S : Set ((M → ℝ) × (M → ℝ)))
    (hS : ∀ p ∈ S, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ p.1 ∧
      ω₀.SolvesMongeAmpere p.1 p.2)
    (hG : HolderBoundedInCharts (EuclideanSpace ℂ (Fin n)) 3 0 (Prod.fst '' S))
    (hMetric : ∃ B : ℝ, 0 < B ∧ ∀ p ∈ S, ∀ x,
      relTrace (ω₀ x) (ω₀ x + mddbar n p.2 x) ≤ B ∧
      relTrace (ω₀ x + mddbar n p.2 x) (ω₀ x) ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : (M → ℝ) × (M → ℝ)) (hp : p ∈ S) x,
      -(C * calabiEnergy ω₀ p.2 x + C) ≤
        (ω₀.perturb p.2 (hS p hp).2.1).laplacian (calabiEnergy ω₀ p.2) x := by
  obtain ⟨a, ha, haction⟩ := exists_uniform_c3BochnerRicciAction_bound ω₀ S hS hG hMetric
  obtain ⟨j, hj, hricci⟩ := exists_uniform_c3BochnerRicciDerivative_bound ω₀ S hS hG hMetric
  obtain ⟨K, hK, hcurv⟩ := ω₀.exists_uniform_reference_curvature_component_bound
  obtain ⟨A, hA, hderiv⟩ := ω₀.exists_uniform_c3ReferenceCurvatureCovariantDerivative_bound
  obtain ⟨r, hr, href⟩ := exists_uniform_c3BochnerReference_bound ω₀ S
    (fun p hp ↦ (hS p hp).2.1) hMetric K hK hcurv A hA hderiv
  refine ⟨a + 4 * (r + j) + 1, by positivity, ?_⟩
  intro p hp x
  have hpot := (hS p hp).2.1
  have hE := calabiEnergy_nonneg ω₀ hpot x
  have hbochner := calabiEnergy_laplacian_eq_bochner ω₀ hpot x
  have hconnection := c3BochnerConnectionTerm_eq_reference_sub_ricci ω₀ hpot x
  have hpositive := c3ConnectionDifference_derivativeSquares_nonneg ω₀ hpot x
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) (mem_extChartAt_target x)
  have hD : 0 ≤ c3BochnerDerivativeSquares ω₀ p.2 x := by
    dsimp only [c3BochnerDerivativeSquares, c3TensorCovariantZ, c3PerturbedMetricInChart]
    exact hpositive
  have hAlo := neg_le_of_abs_le (haction p hp x)
  have hRlo := neg_le_of_abs_le (href p hp x)
  have hJhi := le_of_abs_le (hricci p hp x)
  have hroot : Real.sqrt (calabiEnergy ω₀ p.2 x) ≤ calabiEnergy ω₀ p.2 x + 1 := by
    nlinarith [sq_nonneg (Real.sqrt (calabiEnergy ω₀ p.2 x) - 1), Real.sq_sqrt hE]
  have hscaled := mul_le_mul_of_nonneg_left hroot
    (show 0 ≤ 2 * (r + j) by positivity)
  have hC : 2 * (r + j) ≤ a + 4 * (r + j) + 1 := by linarith
  have hprod : a * calabiEnergy ω₀ p.2 x +
      2 * (r + j) * (calabiEnergy ω₀ p.2 x + Real.sqrt (calabiEnergy ω₀ p.2 x)) ≤
      (a + 4 * (r + j) + 1) * calabiEnergy ω₀ p.2 x + (a + 4 * (r + j) + 1) := by
    nlinarith
  rw [hbochner, hconnection]
  nlinarith

end KahlerForm
