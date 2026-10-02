module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.BochnerTensors

/-!
# Ricci action on a Hermitian tensor of type `(1,2)`

The three slots are the commutator following (3.14) in Székelyhidi, §3.3,
printed p. 45. The estimate here is its elementary finite-dimensional
Cauchy–Schwarz bound, without the book's Einstein specialization.

A unitary frame is expressed by `P.transpose * g z * P.map star = 1`.
Its Ricci endomorphism is `P⁻¹ * c3RicciEndomorphism g z * P`.
The lower action slots use `E r j` and `E r k`, and the pairing conjugates
its second argument. No regularity of `g` is needed for this algebraic
statement: the endomorphism defined from `g` is treated as a fixed matrix.
-/

@[expose] public section

open scoped ComplexOrder

namespace KahlerForm

/-- An entrywise raised Ricci bound in a unitary frame controls the quadratic
three-slot action by `3 * n * R` times the actual Hermitian tensor energy. -/
private theorem c3_unitary_frame_matrix_isUnit {n : ℕ}
    (P g : Matrix (Fin n) (Fin n) ℂ)
    (hP : P.transpose * g * P.map star = 1) : IsUnit P := by
  have hleft : (P.transpose * g) * P.map star = 1 := hP
  have hdetStar : (P.map star).det ≠ 0 := Matrix.det_ne_zero_of_left_inverse hleft
  have hmap : star P.det = (P.map star).det := by
    simpa using (starRingEnd ℂ).map_det P
  have hdetStar' : star P.det ≠ 0 := by rw [hmap]; exact hdetStar
  have hdetP : P.det ≠ 0 := by simpa using hdetStar'
  exact (P.isUnit_iff_isUnit_det).2 (isUnit_iff_ne_zero.mpr hdetP)

private theorem c3_normalized_frame_upper {n : ℕ}
    (g B P : Matrix (Fin n) (Fin n) ℂ)
    (_hBP : B * P = 1) (hPB : P * B = 1)
    (hNorm : P.transpose * g * P.map star = 1) :
    ∀ i a, g i a = ∑ r, B r i * star (B r a) := by
  have hTranspose : B.transpose * P.transpose = 1 := by
    rw [← Matrix.transpose_mul, hPB, Matrix.transpose_one]
  have hConj : P.map star * B.map star = 1 := by
    have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ ↦ A.map star) hPB
    simpa [Matrix.map_mul] using h
  have hG : g = B.transpose * B.map star := by
    calc
      g = 1 * g * 1 := by simp
      _ = (B.transpose * P.transpose) * g * (P.map star * B.map star) := by
        rw [hTranspose, hConj]
      _ = B.transpose * (P.transpose * g * P.map star) * B.map star := by
        noncomm_ring
      _ = B.transpose * 1 * B.map star := by rw [hNorm]
      _ = B.transpose * B.map star := by simp
  intro i a
  rw [hG, Matrix.mul_apply]
  simp [Matrix.transpose_apply, Matrix.map_apply]

private theorem c3_normalized_frame_lower {n : ℕ}
    (g B P : Matrix (Fin n) (Fin n) ℂ)
    (hBP : B * P = 1) (hPB : P * B = 1)
    (hNorm : P.transpose * g * P.map star = 1) :
    ∀ b j, g⁻¹ b j = ∑ r, P j r * star (P b r) := by
  have hUpper := c3_normalized_frame_upper g B P hBP hPB hNorm
  have hG : g = B.transpose * B.map star := by
    ext i a
    exact hUpper i a
  have hTranspose : P.transpose * B.transpose = 1 := by
    rw [← Matrix.transpose_mul, hBP, Matrix.transpose_one]
  have hConj : P.map star * B.map star = 1 := by
    have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ ↦ A.map star) hPB
    simpa [Matrix.map_mul] using h
  have hInv : g⁻¹ = P.map star * P.transpose := by
    apply Matrix.inv_eq_left_inv
    rw [hG]
    calc
      P.map star * P.transpose * (B.transpose * B.map star) =
          P.map star * (P.transpose * B.transpose) * B.map star := by noncomm_ring
      _ = P.map star * 1 * B.map star := by rw [hTranspose]
      _ = P.map star * B.map star := by simp
      _ = 1 := hConj
  intro b j
  rw [hInv, Matrix.mul_apply]
  simp only [Matrix.map_apply, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro r hr
  ring

private noncomputable def c3TensorFrameTransform {n : ℕ}
    (B P : Matrix (Fin n) (Fin n) ℂ) (T : Fin n → Fin n → Fin n → ℂ) :
    Fin n → Fin n → Fin n → ℂ := fun i j k ↦
      ∑ a, ∑ b, ∑ c, B i a * P b j * P c k * T a b c

set_option maxHeartbeats 1000000 in
private theorem c3Pair_eq_frame_components {n : ℕ}
    (g : Matrix (Fin n) (Fin n) ℂ) (z : EuclideanSpace ℂ (Fin n))
    (B P : Matrix (Fin n) (Fin n) ℂ)
    (T U : Fin n → Fin n → Fin n → ℂ)
    (hUpper : ∀ i a, g i a = ∑ r, B r i * star (B r a))
    (hLower : ∀ b j, g⁻¹ b j = ∑ r, P j r * star (P b r)) :
    c3Pair (fun _ : EuclideanSpace ℂ (Fin n) ↦ g) z T U =
      ∑ i, ∑ j, ∑ k,
        c3TensorFrameTransform B P T i j k *
          star (c3TensorFrameTransform B P U i j k) := by
  classical
  unfold c3Pair c3TensorFrameTransform
  simp_rw [hUpper, hLower]
  simp_rw [Finset.mul_sum, Finset.sum_mul, star_sum]
  let ι := Fin n × (Fin n × (Fin n × (Fin n × (Fin n × (Fin n × (Fin n × (Fin n × Fin n)))))) )
  let e : ι ≃ ι := {
    toFun := fun p ↦
      (p.2.2.2.2.2.2.2.2,
        (p.2.2.2.2.2.2.2.1,
          (p.2.2.2.2.2.2.1,
            (p.1, (p.2.1, (p.2.2.1,
              (p.2.2.2.1, (p.2.2.2.2.1, p.2.2.2.2.2.1))))))))
    invFun := fun p ↦
      (p.2.2.2.1,
        (p.2.2.2.2.1,
          (p.2.2.2.2.2.1,
            (p.2.2.2.2.2.2.1,
              (p.2.2.2.2.2.2.2.1,
                (p.2.2.2.2.2.2.2.2,
                  (p.2.2.1, (p.2.1, p.1))))))))
    left_inv := by intro p; simp [ι]
    right_inv := by intro p; simp [ι] }
  let f : ι → ℂ := fun p ↦
    B p.2.2.2.2.2.2.2.2 p.1 * star (B p.2.2.2.2.2.2.2.2 p.2.2.2.1) *
      (P p.2.1 p.2.2.2.2.2.2.2.1 * star (P p.2.2.2.2.1 p.2.2.2.2.2.2.2.1)) *
      (P p.2.2.1 p.2.2.2.2.2.2.1 * star (P p.2.2.2.2.2.1 p.2.2.2.2.2.2.1)) *
      T p.1 p.2.1 p.2.2.1 * star (U p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1)
  let g : ι → ℂ := fun p ↦
    B p.1 p.2.2.2.1 * P p.2.2.2.2.1 p.2.1 * P p.2.2.2.2.2.1 p.2.2.1 *
      T p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 *
        star (B p.1 p.2.2.2.2.2.2.1 * P p.2.2.2.2.2.2.2.1 p.2.1 *
          P p.2.2.2.2.2.2.2.2 p.2.2.1 *
          U p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2)
  have hsum : (∑ p : ι, f p) = ∑ p : ι, g p :=
    Fintype.sum_equiv e f g (by
      intro p
      change f p = g (p.2.2.2.2.2.2.2.2,
        (p.2.2.2.2.2.2.2.1, (p.2.2.2.2.2.2.1,
          (p.1, (p.2.1, (p.2.2.1,
            (p.2.2.2.1, (p.2.2.2.2.1, p.2.2.2.2.2.1))))))))
      simp only [f, g, ι, star_mul]
      ac_rfl)
  simpa only [ι, f, g, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul,
    Finset.mul_sum, Finset.sum_mul, star_sum] using hsum

private def tensorCycleEquiv {n : ℕ} :
    (Fin n × (Fin n × Fin n)) ≃ (Fin n × (Fin n × Fin n)) where
  toFun p := (p.2.2, p.1, p.2.1)
  invFun p := (p.2.1, p.2.2, p.1)
  left_inv := by intro p; simp
  right_inv := by intro p; simp

private theorem tensor_energy_perm {n : ℕ} (T : Fin n → Fin n → Fin n → ℂ) :
    (∑ i, ∑ j, ∑ k, ‖T k i j‖ ^ 2) =
      ∑ i, ∑ j, ∑ k, ‖T i j k‖ ^ 2 := by
  let f : Fin n × (Fin n × Fin n) → ℝ := fun p ↦ ‖T p.2.2 p.1 p.2.1‖ ^ 2
  let g : Fin n × (Fin n × Fin n) → ℝ := fun p ↦ ‖T p.1 p.2.1 p.2.2‖ ^ 2
  have h := Fintype.sum_equiv tensorCycleEquiv f g (by intro p; rfl)
  simpa only [Fintype.sum_prod_type, f, g] using h

private theorem tensor_sum_const {n : ℕ} (r : ℝ) :
    (∑ _ : Fin n, r) = (n : ℝ) * r := by
  calc
    _ = ∑ i ∈ (Finset.univ : Finset (Fin n)), r := by simp
    _ = _ := by rw [Finset.sum_const]; simp [nsmul_eq_mul]

private theorem tensor_cross_sum_le {n : ℕ} (T : Fin n → Fin n → Fin n → ℂ) :
    (∑ i, ∑ j, ∑ k, ∑ r, ‖T r j k‖ * ‖T i j k‖) ≤
      (n : ℝ) * (∑ i, ∑ j, ∑ k, ‖T i j k‖ ^ 2) := by
  let ι := Fin n × (Fin n × (Fin n × Fin n))
  let f : ι → ℝ := fun p ↦ ‖T p.2.2.2 p.2.1 p.2.2.1‖
  let g : ι → ℝ := fun p ↦ ‖T p.1 p.2.1 p.2.2.1‖
  let E : ℝ := ∑ i, ∑ j, ∑ k, ‖T i j k‖ ^ 2
  have hcs : (∑ p : ι, f p * g p) ^ 2 ≤
      (∑ p : ι, f p ^ 2) * ∑ p : ι, g p ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  have hsum : ∑ p : ι, f p * g p =
      ∑ i, ∑ j, ∑ k, ∑ r, ‖T r j k‖ * ‖T i j k‖ := by
    simp only [ι, f, g, Fintype.sum_prod_type]
  have hf : ∑ p : ι, f p ^ 2 = (n : ℝ) * E := by
    simp only [ι, f, Fintype.sum_prod_type]
    calc
      _ = ∑ i : Fin n, ∑ j, ∑ k, ∑ r, ‖T r j k‖ ^ 2 := rfl
      _ = ∑ i : Fin n, E := by
        apply Fintype.sum_congr
        intro i
        simpa [E] using tensor_energy_perm T
      _ = ∑ i : Fin n, E := rfl
      _ = (n : ℝ) * E := tensor_sum_const E
  have hg : ∑ p : ι, g p ^ 2 = (n : ℝ) * E := by
    simp only [ι, g, Fintype.sum_prod_type]
    calc
      _ = ∑ i : Fin n, ∑ j, ∑ k, ∑ r, ‖T i j k‖ ^ 2 := rfl
      _ = ∑ i : Fin n, ∑ j, ∑ k, (n : ℝ) * ‖T i j k‖ ^ 2 := by
        apply Fintype.sum_congr
        intro i
        apply Fintype.sum_congr
        intro j
        apply Fintype.sum_congr
        intro k
        exact tensor_sum_const (‖T i j k‖ ^ 2)
      _ = (n : ℝ) * E := by simp [E, ← Finset.mul_sum]
  rw [hsum, hf, hg] at hcs
  have hnonneg : 0 ≤ ∑ i, ∑ j, ∑ k, ∑ r, ‖T r j k‖ * ‖T i j k‖ :=
    Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ Finset.sum_nonneg fun k _ ↦
      Finset.sum_nonneg fun r _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hcs' : (∑ i, ∑ j, ∑ k, ∑ r, ‖T r j k‖ * ‖T i j k‖) ^ 2 ≤
      ((n : ℝ) * E) ^ 2 := by
    nlinarith [hcs]
  exact (sq_le_sq₀ hnonneg (mul_nonneg hn hE)).mp hcs'

private def tensorSwap12Equiv {n : ℕ} :
    (Fin n × (Fin n × Fin n)) ≃ (Fin n × (Fin n × Fin n)) where
  toFun p := (p.2.1, p.1, p.2.2)
  invFun p := (p.2.1, p.1, p.2.2)
  left_inv := by intro p; simp
  right_inv := by intro p; simp

private theorem tensor_energy_swap12 {n : ℕ} (T : Fin n → Fin n → Fin n → ℂ) :
    (∑ i, ∑ j, ∑ k, ‖T j i k‖ ^ 2) =
      ∑ i, ∑ j, ∑ k, ‖T i j k‖ ^ 2 := by
  let f : Fin n × (Fin n × Fin n) → ℝ := fun p ↦ ‖T p.2.1 p.1 p.2.2‖ ^ 2
  let g : Fin n × (Fin n × Fin n) → ℝ := fun p ↦ ‖T p.1 p.2.1 p.2.2‖ ^ 2
  have h := Fintype.sum_equiv tensorSwap12Equiv f g (by intro p; rfl)
  simpa only [Fintype.sum_prod_type, f, g] using h

private theorem tensor_cross_sum_le_second {n : ℕ}
    (T : Fin n → Fin n → Fin n → ℂ) :
    (∑ i, ∑ j, ∑ k, ∑ r, ‖T i r k‖ * ‖T i j k‖) ≤
      (n : ℝ) * (∑ i, ∑ j, ∑ k, ‖T i j k‖ ^ 2) := by
  let ι := Fin n × (Fin n × (Fin n × Fin n))
  let e : ι ≃ ι := {
    toFun := fun p ↦ (p.2.1, p.1, p.2.2.1, p.2.2.2)
    invFun := fun p ↦ (p.2.1, p.1, p.2.2.1, p.2.2.2)
    left_inv := by intro p; simp
    right_inv := by intro p; simp }
  let U : Fin n → Fin n → Fin n → ℂ := fun i j k ↦ T j i k
  let f : ι → ℝ := fun p ↦ ‖T p.2.1 p.2.2.2 p.2.2.1‖ * ‖T p.2.1 p.1 p.2.2.1‖
  let g : ι → ℝ := fun p ↦ ‖T p.1 p.2.2.2 p.2.2.1‖ * ‖T p.1 p.2.1 p.2.2.1‖
  have hsum : (∑ p : ι, f p) = ∑ p : ι, g p :=
    Fintype.sum_equiv e f g (by intro p; rfl)
  have h := tensor_cross_sum_le U
  have henergy : (∑ i, ∑ j, ∑ k, ‖U i j k‖ ^ 2) =
      ∑ i, ∑ j, ∑ k, ‖T i j k‖ ^ 2 := by
    simpa [U] using tensor_energy_swap12 T
  rw [henergy] at h
  have hf : (∑ p : ι, f p) =
      ∑ i, ∑ j, ∑ k, ∑ r, ‖U r j k‖ * ‖U i j k‖ := by
    simp only [ι, f, U, Fintype.sum_prod_type]
  have hg : (∑ p : ι, g p) =
      ∑ i, ∑ j, ∑ k, ∑ r, ‖T i r k‖ * ‖T i j k‖ := by
    simp only [ι, g, Fintype.sum_prod_type]
  rw [← hf, hsum, hg] at h
  exact h

private theorem tensor_cross_sum_le_third {n : ℕ}
    (T : Fin n → Fin n → Fin n → ℂ) :
    (∑ i, ∑ j, ∑ k, ∑ r, ‖T i j r‖ * ‖T i j k‖) ≤
      (n : ℝ) * (∑ i, ∑ j, ∑ k, ‖T i j k‖ ^ 2) := by
  let ι := Fin n × (Fin n × (Fin n × Fin n))
  let e : ι ≃ ι := {
    toFun := fun p ↦ (p.2.1, p.2.2.1, p.1, p.2.2.2)
    invFun := fun p ↦ (p.2.2.1, p.1, p.2.1, p.2.2.2)
    left_inv := by intro p; simp
    right_inv := by intro p; simp }
  let U : Fin n → Fin n → Fin n → ℂ := fun i j k ↦ T j k i
  let f : ι → ℝ := fun p ↦ ‖T p.2.1 p.2.2.1 p.2.2.2‖ * ‖T p.2.1 p.2.2.1 p.1‖
  let g : ι → ℝ := fun p ↦ ‖T p.1 p.2.1 p.2.2.2‖ * ‖T p.1 p.2.1 p.2.2.1‖
  have hsum : (∑ p : ι, f p) = ∑ p : ι, g p :=
    Fintype.sum_equiv e f g (by intro p; rfl)
  have h := tensor_cross_sum_le U
  have henergy : (∑ i, ∑ j, ∑ k, ‖U i j k‖ ^ 2) =
      ∑ i, ∑ j, ∑ k, ‖T i j k‖ ^ 2 := by
    simpa [U] using (tensor_energy_perm (fun i j k ↦ T j k i)).symm
  rw [henergy] at h
  have hf : (∑ p : ι, f p) =
      ∑ i, ∑ j, ∑ k, ∑ r, ‖U r j k‖ * ‖U i j k‖ := by
    simp only [ι, f, U, Fintype.sum_prod_type]
  have hg : (∑ p : ι, g p) =
      ∑ i, ∑ j, ∑ k, ∑ r, ‖T i j r‖ * ‖T i j k‖ := by
    simp only [ι, g, Fintype.sum_prod_type]
  rw [← hf, hsum, hg] at h
  exact h

private def algebraicRicciAction {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (T : Fin n → Fin n → Fin n → ℂ) (i j k : Fin n) : ℂ :=
  -(∑ r, A i r * T r j k) +
    ∑ r, A r j * T i r k +
    ∑ r, A r k * T i j r

private theorem algebraicRicciAction_norm_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (T : Fin n → Fin n → Fin n → ℂ)
    (K : ℝ) (hA : ∀ i j, ‖A i j‖ ≤ K) (i j k : Fin n) :
    ‖algebraicRicciAction A T i j k‖ ≤
      K * (∑ r, ‖T r j k‖) + K * (∑ r, ‖T i r k‖) + K * (∑ r, ‖T i j r‖) := by
  unfold algebraicRicciAction
  calc
    ‖-(∑ r, A i r * T r j k) + ∑ r, A r j * T i r k +
        ∑ r, A r k * T i j r‖ ≤
      ‖∑ r, A i r * T r j k‖ + ‖∑ r, A r j * T i r k‖ +
        ‖∑ r, A r k * T i j r‖ := by
      calc
        _ ≤ ‖-(∑ r, A i r * T r j k) + ∑ r, A r j * T i r k‖ +
            ‖∑ r, A r k * T i j r‖ := norm_add_le _ _
        _ ≤ _ := by
          simpa [norm_neg] using norm_add_le
            (-(∑ r, A i r * T r j k)) (∑ r, A r j * T i r k)
    _ ≤ (∑ r, ‖A i r‖ * ‖T r j k‖) +
        (∑ r, ‖A r j‖ * ‖T i r k‖) +
        (∑ r, ‖A r k‖ * ‖T i j r‖) := by
      gcongr
      · calc
          ‖∑ r, A i r * T r j k‖ ≤ ∑ r, ‖A i r * T r j k‖ := norm_sum_le _ _
          _ = _ := by simp_rw [norm_mul]
      · calc
          ‖∑ r, A r j * T i r k‖ ≤ ∑ r, ‖A r j * T i r k‖ := norm_sum_le _ _
          _ = _ := by simp_rw [norm_mul]
      · calc
          ‖∑ r, A r k * T i j r‖ ≤ ∑ r, ‖A r k * T i j r‖ := norm_sum_le _ _
          _ = _ := by simp_rw [norm_mul]
    _ ≤ K * (∑ r, ‖T r j k‖) + K * (∑ r, ‖T i r k‖) +
        K * (∑ r, ‖T i j r‖) := by
      calc
        _ ≤ (∑ r, K * ‖T r j k‖) + (∑ r, K * ‖T i r k‖) +
            (∑ r, K * ‖T i j r‖) := by
          apply add_le_add
          · apply add_le_add
            · exact Finset.sum_le_sum fun r _ ↦ mul_le_mul_of_nonneg_right (hA i r) (norm_nonneg _)
            · exact Finset.sum_le_sum fun r _ ↦ mul_le_mul_of_nonneg_right (hA r j) (norm_nonneg _)
          · exact Finset.sum_le_sum fun r _ ↦ mul_le_mul_of_nonneg_right (hA r k) (norm_nonneg _)
        _ = _ := by simp_rw [← Finset.mul_sum]

private theorem algebraicRicciAction_pair_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (T : Fin n → Fin n → Fin n → ℂ)
    (K : ℝ) (hK : 0 ≤ K) (hA : ∀ i j, ‖A i j‖ ≤ K) :
    |(∑ i, ∑ j, ∑ k, algebraicRicciAction A T i j k * star (T i j k)).re| ≤
      (3 * (n : ℝ) * K) * (∑ i, ∑ j, ∑ k, ‖T i j k‖ ^ 2) := by
  let E : ℝ := ∑ i, ∑ j, ∑ k, ‖T i j k‖ ^ 2
  have hcross1 := tensor_cross_sum_le T
  have hcross2 := tensor_cross_sum_le_second T
  have hcross3 := tensor_cross_sum_le_third T
  have hsum_norm :
      |(∑ i, ∑ j, ∑ k, algebraicRicciAction A T i j k * star (T i j k)).re| ≤
        ∑ i, ∑ j, ∑ k, ‖algebraicRicciAction A T i j k‖ * ‖T i j k‖ := by
    calc
      _ ≤ ‖∑ i, ∑ j, ∑ k,
          algebraicRicciAction A T i j k * star (T i j k)‖ := Complex.abs_re_le_norm _
      _ ≤ ∑ i, ∑ j, ∑ k,
          ‖algebraicRicciAction A T i j k * star (T i j k)‖ := by
        let ι := Fin n × (Fin n × Fin n)
        let f : ι → ℂ := fun p ↦
          algebraicRicciAction A T p.1 p.2.1 p.2.2 * star (T p.1 p.2.1 p.2.2)
        have h := norm_sum_le (Finset.univ : Finset ι) f
        simpa only [ι, f, Fintype.sum_prod_type] using h
      _ = _ := by simp_rw [norm_mul, norm_star]
  have hpoint i j k :
      ‖algebraicRicciAction A T i j k‖ * ‖T i j k‖ ≤
        K * (∑ r, ‖T r j k‖ * ‖T i j k‖) +
        K * (∑ r, ‖T i r k‖ * ‖T i j k‖) +
        K * (∑ r, ‖T i j r‖ * ‖T i j k‖) := by
    calc
      _ ≤ (K * (∑ r, ‖T r j k‖) + K * (∑ r, ‖T i r k‖) +
          K * (∑ r, ‖T i j r‖)) * ‖T i j k‖ :=
        mul_le_mul_of_nonneg_right (algebraicRicciAction_norm_le A T K hA i j k)
          (norm_nonneg _)
      _ = _ := by
        calc
          _ = K * ((∑ r, ‖T r j k‖) * ‖T i j k‖) +
              K * ((∑ r, ‖T i r k‖) * ‖T i j k‖) +
              K * ((∑ r, ‖T i j r‖) * ‖T i j k‖) := by ring
          _ = _ := by rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  let ι := Fin n × (Fin n × Fin n)
  have htotalFlat :
      (∑ p : ι, ‖algebraicRicciAction A T p.1 p.2.1 p.2.2‖ * ‖T p.1 p.2.1 p.2.2‖) ≤
        (3 * (n : ℝ) * K) * E := by
    calc
      _ ≤ (∑ p : ι, (K * (∑ r : Fin n, ‖T r p.2.1 p.2.2‖ * ‖T p.1 p.2.1 p.2.2‖) + K * (∑ r : Fin n, ‖T p.1 r p.2.2‖ * ‖T p.1 p.2.1 p.2.2‖) + K * (∑ r : Fin n, ‖T p.1 p.2.1 r‖ * ‖T p.1 p.2.1 p.2.2‖))) := by
        apply Finset.sum_le_sum
        intro p hp
        exact hpoint p.1 p.2.1 p.2.2
      _ = K * (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ r : Fin n, ‖T r j k‖ * ‖T i j k‖) +
          K * (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ r : Fin n, ‖T i r k‖ * ‖T i j k‖) +
          K * (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ r : Fin n, ‖T i j r‖ * ‖T i j k‖) := by
        simp only [ι, Fintype.sum_prod_type]
        simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ K * ((n : ℝ) * E) + K * ((n : ℝ) * E) + K * ((n : ℝ) * E) := by
        gcongr
      _ = (3 * (n : ℝ) * K) * E := by ring
  have htotal :
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        ‖algebraicRicciAction A T i j k‖ * ‖T i j k‖) ≤
        (3 * (n : ℝ) * K) * E := by
    simpa only [ι, Fintype.sum_prod_type] using htotalFlat
  exact hsum_norm.trans (by simpa [E] using htotal)

private theorem flatRicciAction_pair_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (T : Fin n → Fin n → Fin n → ℂ)
    (K : ℝ) (hK : 0 ≤ K) (hA : ∀ i j, ‖A i j‖ ≤ K)
    (z : EuclideanSpace ℂ (Fin n)) :
    |(c3Pair (fun _ : EuclideanSpace ℂ (Fin n) ↦ 1) z
      (fun i j k ↦ algebraicRicciAction A T i j k) T).re| ≤
      (3 * (n : ℝ) * K) *
        (c3Pair (fun _ : EuclideanSpace ℂ (Fin n) ↦ 1) z T T).re := by
  have h := algebraicRicciAction_pair_le A T K hK hA
  have hAction :
      (c3Pair (fun _ : EuclideanSpace ℂ (Fin n) ↦ 1) z
        (fun i j k ↦ algebraicRicciAction A T i j k) T).re =
        (∑ i, ∑ j, ∑ k, algebraicRicciAction A T i j k * star (T i j k)).re := by
    simp [c3Pair, Matrix.one_apply]
  have hEnergy :
      (c3Pair (fun _ : EuclideanSpace ℂ (Fin n) ↦ 1) z T T).re =
        ∑ i, ∑ j, ∑ k, ‖T i j k‖ ^ 2 := by
    simp [c3Pair, Matrix.one_apply, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  rw [hAction, hEnergy]
  exact h

private theorem c3_interchange_four {n : ℕ}
    (f : Fin n → ℂ) (p q : Fin n → ℂ) (C : Fin n → Fin n → ℂ)
    (T : Fin n → Fin n → Fin n → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ r, f a * p b * q c * C a r * T r b c) =
      ∑ a, ∑ r, ∑ b, ∑ c, f a * C a r * p b * q c * T r b c := by
  let ι := Fin n × (Fin n × (Fin n × Fin n))
  let e : ι ≃ ι := {
    toFun := fun x ↦ (x.1, (x.2.2.2, (x.2.1, x.2.2.1)))
    invFun := fun x ↦ (x.1, (x.2.2.1, (x.2.2.2, x.2.1)))
    left_inv := by intro x; simp [ι]
    right_inv := by intro x; simp [ι] }
  let F : ι → ℂ := fun x ↦ f x.1 * p x.2.1 * q x.2.2.1 *
    C x.1 x.2.2.2 * T x.2.2.2 x.2.1 x.2.2.1
  let G : ι → ℂ := fun x ↦ f x.1 * C x.1 x.2.1 *
    p x.2.2.1 * q x.2.2.2 * T x.2.1 x.2.2.1 x.2.2.2
  have hsum : (∑ x : ι, F x) = ∑ x : ι, G x :=
    Fintype.sum_equiv e F G (by
      intro x
      dsimp [F, G, e]
      ring)
  simpa only [ι, F, G, Fintype.sum_prod_type] using hsum

private def c3FrameChange {n : ℕ} (B Q S : Matrix (Fin n) (Fin n) ℂ)
    (T : Fin n → Fin n → Fin n → ℂ) : Fin n → Fin n → Fin n → ℂ :=
  fun i j k ↦ ∑ a, ∑ b, ∑ c, B i a * Q b j * S c k * T a b c

private theorem c3_upper_covariance {n : ℕ}
    (B D Q S C : Matrix (Fin n) (Fin n) ℂ)
    (T : Fin n → Fin n → Fin n → ℂ)
    (hDB : D * B = 1) :
    ∀ i j k,
      (∑ a, ∑ b, ∑ c, B i a * Q b j * S c k *
        (∑ r, C a r * T r b c)) =
        ∑ r, (B * C * D) i r * c3FrameChange B Q S T r j k := by
  intro i j k
  let V : Fin n → ℂ := fun r ↦ ∑ b, ∑ c, Q b j * S c k * T r b c
  have hperm :
      (∑ a, ∑ b, ∑ c, B i a * Q b j * S c k * (∑ r, C a r * T r b c)) =
        ∑ a, ∑ r, ∑ b, ∑ c, B i a * C a r * Q b j * S c k * T r b c := by
    calc
      _ = ∑ a, ∑ b, ∑ c, ∑ r,
          B i a * Q b j * S c k * C a r * T r b c := by
        simp_rw [Finset.mul_sum, mul_assoc]
      _ = _ := c3_interchange_four (fun a ↦ B i a) (fun b ↦ Q b j)
        (fun c ↦ S c k) C T
  have hleft :
      (∑ a, ∑ r, ∑ b, ∑ c, B i a * C a r * Q b j * S c k * T r b c) =
        Matrix.mulVec B (Matrix.mulVec C V) i := by
    simp only [Matrix.mulVec_apply_eq_sum]
    simp_rw [V, Finset.mul_sum, mul_assoc]
  have hDB' : (B * C * D) * B = B * C := by
    calc
      (B * C * D) * B = B * C * (D * B) := by simp only [Matrix.mul_assoc]
      _ = B * C := by rw [hDB, Matrix.mul_one]
  have hmat : Matrix.mulVec B (Matrix.mulVec C V) i =
      Matrix.mulVec (B * C * D) (Matrix.mulVec B V) i := by
    calc
      Matrix.mulVec B (Matrix.mulVec C V) i = Matrix.mulVec (B * C) V i := by
        rw [Matrix.mulVec_mulVec]
      _ = Matrix.mulVec ((B * C * D) * B) V i := by rw [hDB']
      _ = Matrix.mulVec (B * C * D) (Matrix.mulVec B V) i := by
        rw [Matrix.mulVec_mulVec]
  have hright :
      Matrix.mulVec (B * C * D) (Matrix.mulVec B V) i =
        ∑ r, (B * C * D) i r * c3FrameChange B Q S T r j k := by
    simp [Matrix.mulVec_apply_eq_sum, c3FrameChange, V, Finset.mul_sum,
      mul_assoc, mul_left_comm, mul_comm]
  calc
    _ = Matrix.mulVec B (Matrix.mulVec C V) i := hperm.trans hleft
    _ = _ := hmat.trans hright

private theorem c3_swap12_sum {n : ℕ} (F : Fin n → Fin n → Fin n → ℂ) :
    (∑ a, ∑ b, ∑ c, F a b c) = ∑ a, ∑ b, ∑ c, F b a c := by
  let ι := Fin n × (Fin n × Fin n)
  let e : ι ≃ ι := {
    toFun := fun x ↦ (x.2.1, x.1, x.2.2)
    invFun := fun x ↦ (x.2.1, x.1, x.2.2)
    left_inv := by intro x; simp [ι]
    right_inv := by intro x; simp [ι] }
  let f : ι → ℂ := fun x ↦ F x.1 x.2.1 x.2.2
  let g : ι → ℂ := fun x ↦ F x.2.1 x.1 x.2.2
  have h := Fintype.sum_equiv e f g (by intro x; rfl)
  simpa only [ι, f, g, Fintype.sum_prod_type] using h

private theorem c3_second_covariance {n : ℕ}
    (B P C : Matrix (Fin n) (Fin n) ℂ)
    (T : Fin n → Fin n → Fin n → ℂ)
    (hPB : P * B = 1) :
    ∀ i j k,
      (∑ a, ∑ b, ∑ c, B i a * P b j * P c k *
        (∑ r, C r b * T a r c)) =
        ∑ s, (B * C * P) s j * c3FrameChange B P P T i s k := by
  intro i j k
  have hDB : B.transpose * P.transpose = 1 := by
    rw [← Matrix.transpose_mul, hPB, Matrix.transpose_one]
  have h := c3_upper_covariance P.transpose B.transpose B.transpose P C.transpose
    (fun a b c ↦ T b a c) hDB j i k
  have hLeft :
      (∑ a, ∑ b, ∑ c, B i a * P b j * P c k * (∑ r, C r b * T a r c)) =
        ∑ a, ∑ b, ∑ c, P a j * B i b * P c k * (∑ r, C r a * T b r c) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (c3_swap12_sum (fun a b c ↦
        B i a * P b j * P c k * (∑ r, C r b * T a r c)))
  have hFrame (s : Fin n) :
      c3FrameChange P.transpose B.transpose P (fun a b c ↦ T b a c) s i k =
        c3FrameChange B P P T i s k := by
    simp only [c3FrameChange, Matrix.transpose_apply]
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (c3_swap12_sum (fun a b c ↦ P a s * B i b * P c k * T b a c))
  have hMat : ∀ s, (P.transpose * C.transpose * B.transpose) j s =
      (B * C * P) s j := by
    have htranspose : (B * C * P).transpose =
        P.transpose * C.transpose * B.transpose := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul]
      noncomm_ring
    intro s
    rw [← htranspose, Matrix.transpose_apply]
  calc
    _ = ∑ a, ∑ b, ∑ c, P a j * B i b * P c k *
        (∑ r, C r a * T b r c) := hLeft
    _ = ∑ s, (P.transpose * C.transpose * B.transpose) j s *
        c3FrameChange P.transpose B.transpose P (fun a b c ↦ T b a c) s i k := h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [hMat s, hFrame s]

private theorem c3_swap13_sum {n : ℕ} (F : Fin n → Fin n → Fin n → ℂ) :
    (∑ a, ∑ b, ∑ c, F a b c) = ∑ a, ∑ b, ∑ c, F c b a := by
  let ι := Fin n × (Fin n × Fin n)
  let e : ι ≃ ι := {
    toFun := fun x ↦ (x.2.2, x.2.1, x.1)
    invFun := fun x ↦ (x.2.2, x.2.1, x.1)
    left_inv := by intro x; simp [ι]
    right_inv := by intro x; simp [ι] }
  let f : ι → ℂ := fun x ↦ F x.1 x.2.1 x.2.2
  let g : ι → ℂ := fun x ↦ F x.2.2 x.2.1 x.1
  have h := Fintype.sum_equiv e f g (by intro x; rfl)
  simpa only [ι, f, g, Fintype.sum_prod_type] using h

private theorem c3_third_covariance {n : ℕ}
    (B P C : Matrix (Fin n) (Fin n) ℂ)
    (T : Fin n → Fin n → Fin n → ℂ)
    (hPB : P * B = 1) :
    ∀ i j k,
      (∑ a, ∑ b, ∑ c, B i a * P b j * P c k *
        (∑ r, C r c * T a b r)) =
        ∑ s, (B * C * P) s k * c3FrameChange B P P T i j s := by
  intro i j k
  have hDB : B.transpose * P.transpose = 1 := by
    rw [← Matrix.transpose_mul, hPB, Matrix.transpose_one]
  have h := c3_upper_covariance P.transpose B.transpose P B.transpose C.transpose
    (fun a b c ↦ T c b a) hDB k j i
  have hLeft :
      (∑ a, ∑ b, ∑ c, B i a * P b j * P c k *
        (∑ r, C r c * T a b r)) =
        ∑ a, ∑ b, ∑ c, P a k * P b j * B i c * (∑ r, C r a * T c b r) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (c3_swap13_sum (fun a b c ↦
        B i a * P b j * P c k * (∑ r, C r c * T a b r)))
  have hFrame (s : Fin n) :
      c3FrameChange P.transpose P B.transpose (fun a b c ↦ T c b a) s j i =
        c3FrameChange B P P T i j s := by
    simp only [c3FrameChange, Matrix.transpose_apply]
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (c3_swap13_sum (fun a b c ↦ P a s * P b j * B i c * T c b a))
  have hMat : ∀ s, (P.transpose * C.transpose * B.transpose) k s =
      (B * C * P) s k := by
    have htranspose : (B * C * P).transpose =
        P.transpose * C.transpose * B.transpose := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul]
      noncomm_ring
    intro s
    rw [← htranspose, Matrix.transpose_apply]
  calc
    _ = ∑ a, ∑ b, ∑ c, P a k * P b j * B i c *
        (∑ r, C r a * T c b r) := hLeft
    _ = ∑ s, (P.transpose * C.transpose * B.transpose) k s *
        c3FrameChange P.transpose P B.transpose (fun a b c ↦ T c b a) s j i := h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [hMat s, hFrame s]

private def c3ActionChange {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ)
    (T : Fin n → Fin n → Fin n → ℂ) (i j k : Fin n) : ℂ :=
  -(∑ r, C i r * T r j k) + ∑ r, C r j * T i r k + ∑ r, C r k * T i j r

private theorem c3_full_covariance {n : ℕ}
    (B P C : Matrix (Fin n) (Fin n) ℂ)
    (T : Fin n → Fin n → Fin n → ℂ)
    (hPB : P * B = 1) :
    ∀ i j k,
      c3FrameChange B P P (fun a b c ↦ c3ActionChange C T a b c) i j k =
        algebraicRicciAction (B * C * P) (c3FrameChange B P P T) i j k := by
  intro i j k
  have hu := c3_upper_covariance B P P P C T hPB i j k
  have h2 := c3_second_covariance B P C T hPB i j k
  have h3 := c3_third_covariance B P C T hPB i j k
  simp only [c3FrameChange, c3ActionChange, algebraicRicciAction]
  calc
    _ = -(∑ a, ∑ b, ∑ c, B i a * P b j * P c k *
          (∑ r, C a r * T r b c)) +
        (∑ a, ∑ b, ∑ c, B i a * P b j * P c k *
          (∑ r, C r b * T a r c)) +
        (∑ a, ∑ b, ∑ c, B i a * P b j * P c k *
          (∑ r, C r c * T a b r)) := by
      simp [Finset.sum_add_distrib, Finset.sum_neg_distrib, mul_add, mul_neg]
    _ = -(∑ r, (B * C * P) i r * c3FrameChange B P P T r j k) +
        (∑ s, (B * C * P) s j * c3FrameChange B P P T i s k) +
        (∑ s, (B * C * P) s k * c3FrameChange B P P T i j s) := by
      rw [hu, h2, h3]
    _ = _ := rfl

theorem c3RicciTensorAction_pair_bound_of_unitary_frame
    {n : ℕ}
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (T : Fin n → Fin n → Fin n → ℂ)
    (P : Matrix (Fin n) (Fin n) ℂ)
    (R : ℝ)
    (hP : P.transpose * g z * P.map star = 1)
    (hR : 0 ≤ R)
    (hA : ∀ i j,
      ‖(P⁻¹ * Matrix.of (c3RicciEndomorphism g z) * P) i j‖ ≤ R) :
    |(c3Pair g z (c3RicciTensorAction g T z) T).re| ≤
      (3 * (n : ℝ) * R) * (c3Pair g z T T).re := by
  let B : Matrix (Fin n) (Fin n) ℂ := P⁻¹
  let C : Matrix (Fin n) (Fin n) ℂ := Matrix.of (c3RicciEndomorphism g z)
  let A : Matrix (Fin n) (Fin n) ℂ := B * C * P
  let Tf : Fin n → Fin n → Fin n → ℂ := c3TensorFrameTransform B P T
  have hPunit : IsUnit P := c3_unitary_frame_matrix_isUnit P (g z) hP
  obtain ⟨u, hu⟩ := hPunit
  have hPinv : P⁻¹ = ↑(u⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [← hu]
    simp
  have hBP : B * P = 1 := by
    dsimp [B]
    rw [hPinv, ← hu]
    simp
  have hPB : P * B = 1 := by
    dsimp [B]
    rw [hPinv, ← hu]
    simp
  have hUpper := c3_normalized_frame_upper (g z) B P hBP hPB hP
  have hLower := c3_normalized_frame_lower (g z) B P hBP hPB hP
  have hCov := c3_full_covariance B P C T hPB
  have hPairAction := c3Pair_eq_frame_components (g z) z B P
    (c3RicciTensorAction g T z) T hUpper hLower
  have hPairEnergy := c3Pair_eq_frame_components (g z) z B P T T hUpper hLower
  have hFlatAction :
      c3Pair (fun _ : EuclideanSpace ℂ (Fin n) ↦ 1) z
        (fun i j k ↦ algebraicRicciAction A Tf i j k) Tf =
        ∑ i, ∑ j, ∑ k, algebraicRicciAction A Tf i j k * star (Tf i j k) := by
    simp [c3Pair, Matrix.one_apply]
  have hFlatEnergy :
      c3Pair (fun _ : EuclideanSpace ℂ (Fin n) ↦ 1) z Tf Tf =
        ∑ i, ∑ j, ∑ k, ‖Tf i j k‖ ^ 2 := by
    simp [c3Pair, Matrix.one_apply, Complex.mul_conj,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have hCov' i j k :
      c3FrameChange B P P (fun a b c ↦ c3RicciTensorAction g T z a b c) i j k =
        algebraicRicciAction (B * C * P) (c3FrameChange B P P T) i j k := by
    simpa [C, c3RicciTensorAction, c3ActionChange] using hCov i j k
  have hCov'' i j k :
      c3TensorFrameTransform B P (c3RicciTensorAction g T z) i j k =
        algebraicRicciAction A Tf i j k := by
    change c3FrameChange B P P
      (fun a b c ↦ c3RicciTensorAction g T z a b c) i j k =
        algebraicRicciAction (B * C * P) (c3FrameChange B P P T) i j k
    exact hCov' i j k
  have hActionPair :
      (c3Pair g z (c3RicciTensorAction g T z) T).re =
        (c3Pair (fun _ : EuclideanSpace ℂ (Fin n) ↦ 1) z
          (fun i j k ↦ algebraicRicciAction A Tf i j k) Tf).re := by
    change (c3Pair (fun _ ↦ g z) z (c3RicciTensorAction g T z) T).re = _
    rw [hPairAction, hFlatAction]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    rw [hCov'' i j k]
  have hFrameEnergy :
      (∑ i, ∑ j, ∑ k, c3TensorFrameTransform B P T i j k *
        star (c3TensorFrameTransform B P T i j k)) =
        ↑(∑ i, ∑ j, ∑ k, ‖Tf i j k‖ ^ 2) := by
    simpa [c3Pair, Matrix.one_apply] using hFlatEnergy
  have hEnergyPair :
      (c3Pair g z T T).re =
        (c3Pair (fun _ : EuclideanSpace ℂ (Fin n) ↦ 1) z Tf Tf).re := by
    change (c3Pair (fun _ ↦ g z) z T T).re = _
    rw [hPairEnergy, hFrameEnergy, hFlatEnergy]
  have hflat := flatRicciAction_pair_le A Tf R hR hA z
  calc
    |(c3Pair g z (c3RicciTensorAction g T z) T).re| =
        |(c3Pair (fun _ : EuclideanSpace ℂ (Fin n) ↦ 1) z
          (fun i j k ↦ algebraicRicciAction A Tf i j k) Tf).re| := by rw [hActionPair]
    _ ≤ (3 * (n : ℝ) * R) *
        (c3Pair (fun _ : EuclideanSpace ℂ (Fin n) ↦ 1) z Tf Tf).re := hflat
    _ = (3 * (n : ℝ) * R) * (c3Pair g z T T).re := by rw [← hEnergyPair]

end KahlerForm
