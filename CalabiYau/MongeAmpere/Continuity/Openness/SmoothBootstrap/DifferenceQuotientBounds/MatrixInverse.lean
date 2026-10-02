module

public import CalabiYau.Analysis.Elliptic.Schauder

/-!
# Hölder estimates for inverses of finite Hermitian matrices

This is the finite-dimensional resolvent step in the difference-quotient bootstrap. Uniform
ellipticity controls the inverse and the identity `A⁻¹ - B⁻¹ = A⁻¹ (B - A) B⁻¹`
transfers the entrywise Hölder modulus to the inverse.
-/

@[expose] public section

open scoped NNReal Topology ComplexOrder MatrixOrder
open Matrix Set

private theorem uniformlyEllipticOn_posDef {n : ℕ} (lam : ℝ≥0)
    (hlam : 0 < lam) (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : B.IsHermitian ∧ ∀ v : Fin n → ℂ,
      (lam : ℝ) * ∑ i, ‖v i‖ ^ 2 ≤ RCLike.re (star v ⬝ᵥ (B *ᵥ v))) : B.PosDef := by
  classical
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hB.1
  intro v hv
  have hvne : ∃ i, v i ≠ 0 := by
    by_contra h
    apply hv
    funext i
    exact not_not.mp (not_exists.mp h i)
  rcases hvne with ⟨i, hi⟩
  have hsum : 0 < ∑ i, ‖v i‖ ^ 2 := by
    apply Finset.sum_pos'
    · intro i hi
      positivity
    · exact ⟨i, Finset.mem_univ i, by positivity [norm_pos_iff.mpr hi]⟩
  have hre : 0 < RCLike.re (star v ⬝ᵥ (B *ᵥ v)) :=
    lt_of_lt_of_le (mul_pos (NNReal.coe_pos.mpr hlam) hsum) (hB.2 v)
  exact RCLike.lt_iff_re_im.mpr ⟨hre, (hB.1.im_star_dotProduct_mulVec_self v).symm⟩

private theorem uniformlyEllipticOn_matrix_inverse_bound {n : ℕ} (lam : ℝ≥0)
    (hlam : 0 < lam) (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : B.IsHermitian ∧ ∀ v : Fin n → ℂ,
      (lam : ℝ) * ∑ i, ‖v i‖ ^ 2 ≤ RCLike.re (star v ⬝ᵥ (B *ᵥ v))) :
    IsUnit B ∧ ∀ i j, ‖B⁻¹ i j‖ ≤ (lam⁻¹ : ℝ≥0) := by
  classical
  have hPos := uniformlyEllipticOn_posDef lam hlam B hB
  refine ⟨hPos.isUnit, ?_⟩
  intro i j
  let e : Fin n → ℂ := Pi.single j 1
  let v : Fin n → ℂ := B⁻¹ *ᵥ e
  let vE : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 v
  have hdet : IsUnit B.det := Matrix.isUnit_iff_isUnit_det B |>.mp hPos.isUnit
  have hsol : B *ᵥ (B⁻¹ *ᵥ e) = e := by
    calc
      B *ᵥ (B⁻¹ *ᵥ e) = (B * B⁻¹) *ᵥ e := by rw [Matrix.mulVec_mulVec]
      _ = 1 *ᵥ e := by rw [Matrix.mul_nonsing_inv _ hdet]
      _ = e := Matrix.one_mulVec _
  have hsol' : B *ᵥ v = e := by simpa [v] using hsol
  have hquad : (lam : ℝ) * ∑ k, ‖v k‖ ^ 2 ≤ RCLike.re (star v ⬝ᵥ e) := by
    rw [← hsol']
    exact hB.2 v
  have hdot : star v ⬝ᵥ e = star (v j) := by
    simp [e]
  have hnormSq : ‖vE‖ ^ 2 = ∑ k, ‖v k‖ ^ 2 := by
    simpa [vE] using (EuclideanSpace.norm_sq_eq (x := vE))
  have hnormBound : (lam : ℝ) * ‖vE‖ ≤ 1 := by
    by_cases hv : ‖vE‖ = 0
    · simp [hv]
    · have hvpos : 0 < ‖vE‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
      have hq : (lam : ℝ) * ‖vE‖ ^ 2 ≤ ‖vE‖ := by
        calc
          (lam : ℝ) * ‖vE‖ ^ 2 = (lam : ℝ) * ∑ k, ‖v k‖ ^ 2 := by rw [hnormSq]
          _ ≤ RCLike.re (star v ⬝ᵥ e) := hquad
          _ = RCLike.re (v j) := by rw [hdot]; simp
          _ ≤ ‖v j‖ := RCLike.re_le_norm _
          _ ≤ ‖vE‖ := PiLp.norm_apply_le vE j
      have hmul : (lam : ℝ) * ‖vE‖ ≤ 1 := by
        by_contra hnot
        have hgt : 1 < (lam : ℝ) * ‖vE‖ := lt_of_not_ge hnot
        have hprod : 0 < ‖vE‖ * ((lam : ℝ) * ‖vE‖ - 1) :=
          mul_pos hvpos (by linarith)
        nlinarith [hq, hprod]
      exact hmul
  have hnorm : ‖vE‖ ≤ ((lam : ℝ)⁻¹) := by
    calc
      ‖vE‖ = ((lam : ℝ)⁻¹) * ((lam : ℝ) * ‖vE‖) := by field_simp [ne_of_gt (NNReal.coe_pos.mpr hlam)]
      _ ≤ ((lam : ℝ)⁻¹) * 1 := by
        exact mul_le_mul_of_nonneg_left hnormBound (inv_nonneg.mpr (NNReal.coe_nonneg lam))
      _ = ((lam : ℝ)⁻¹) := by ring
  have hentry : ‖v i‖ ≤ ‖vE‖ := PiLp.norm_apply_le vE i
  calc
    ‖B⁻¹ i j‖ = ‖v i‖ := by simp [v, e]
    _ ≤ ‖vE‖ := hentry
    _ ≤ ((lam : ℝ)⁻¹) := hnorm
    _ = (lam⁻¹ : ℝ≥0) := by simp

private theorem holderOnWith_matrix_inv_entry_of_norm_bound {E : Type*}
    [PseudoMetricSpace E] {n : ℕ} {α C B : ℝ≥0} {U : Set E}
    (A : E → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, HolderOnWith C α (fun z ↦ A z i j) U)
    (hUnit : ∀ z ∈ U, IsUnit (A z))
    (hInv : ∀ z ∈ U, ∀ i j, ‖(A z)⁻¹ i j‖ ≤ B) (i j : Fin n) :
    HolderOnWith ((n : ℝ≥0) ^ 2 * B ^ 2 * C) α
      (fun z ↦ (A z)⁻¹ i j) U := by
  intro x hx y hy
  have hiden : (A x)⁻¹ - (A y)⁻¹ = (A x)⁻¹ * (A y - A x) * (A y)⁻¹ := by
    have hxdet : IsUnit (Matrix.det (A x)) :=
      (Matrix.isUnit_iff_isUnit_det (A x)).mp (hUnit x hx)
    have hydet : IsUnit (Matrix.det (A y)) :=
      (Matrix.isUnit_iff_isUnit_det (A y)).mp (hUnit y hy)
    calc
      (A x)⁻¹ - (A y)⁻¹ = (A x)⁻¹ * 1 - 1 * (A y)⁻¹ := by simp
      _ = (A x)⁻¹ * (A y * (A y)⁻¹) -
          ((A x)⁻¹ * (A x)) * (A y)⁻¹ := by
        rw [Matrix.mul_nonsing_inv _ hydet, Matrix.nonsing_inv_mul _ hxdet]
      _ = (A x)⁻¹ * (A y - A x) * (A y)⁻¹ := by
        rw [Matrix.mul_sub, Matrix.sub_mul]
        simp only [Matrix.mul_assoc]
  have hentry (k l : Fin n) :
      ‖A y k l - A x k l‖ ≤ (C : ℝ) * dist x y ^ (α : ℝ) := by
    have h := (hA k l).edist_le hx hy
    rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) α.coe_nonneg,
      ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)] at h
    have h' : dist (A x k l) (A y k l) ≤
        (C : ℝ) * dist x y ^ (α : ℝ) :=
      (ENNReal.ofReal_le_ofReal_iff
        (p := dist (A x k l) (A y k l))
        (q := (C : ℝ) * dist x y ^ (α : ℝ)) (by positivity)).mp h
    rw [dist_eq_norm] at h'
    simpa [norm_sub_rev] using h'
  have hnorm : ‖((A x)⁻¹) i j - ((A y)⁻¹) i j‖ ≤
      ((n : ℝ) ^ 2) * (B : ℝ) ^ 2 * (C : ℝ) * dist x y ^ (α : ℝ) := by
    rw [show ((A x)⁻¹) i j - ((A y)⁻¹) i j =
        ∑ k : Fin n, ∑ l : Fin n,
          (A x)⁻¹ i k * (A y k l - A x k l) * (A y)⁻¹ l j by
      rw [← Matrix.sub_apply, hiden]
      simp only [Matrix.mul_apply, Matrix.sub_apply, Finset.sum_mul]
      rw [Finset.sum_comm]]
    calc
      ‖∑ k : Fin n, ∑ l : Fin n,
          (A x)⁻¹ i k * (A y k l - A x k l) * (A y)⁻¹ l j‖ ≤
          ∑ k : Fin n, ∑ l : Fin n,
            ‖(A x)⁻¹ i k * (A y k l - A x k l) * (A y)⁻¹ l j‖ := by
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk ↦ norm_sum_le _ _)
      _ ≤ ∑ k : Fin n, ∑ l : Fin n,
          (B : ℝ) * ((C : ℝ) * dist x y ^ (α : ℝ)) * (B : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        apply Finset.sum_le_sum
        intro l hl
        calc
          ‖(A x)⁻¹ i k * (A y k l - A x k l) * (A y)⁻¹ l j‖ ≤
              ‖(A x)⁻¹ i k‖ * ‖A y k l - A x k l‖ * ‖(A y)⁻¹ l j‖ := by
            exact (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
          _ ≤ (B : ℝ) * ((C : ℝ) * dist x y ^ (α : ℝ)) * (B : ℝ) := by
            gcongr
            · exact hInv x hx i k
            · exact hentry k l
            · exact hInv y hy l j
      _ = ((n : ℝ) ^ 2) * (B : ℝ) ^ 2 * (C : ℝ) * dist x y ^ (α : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
  change edist (((A x)⁻¹) i j) (((A y)⁻¹) i j) ≤
    (((n : ℝ≥0) ^ 2 * B ^ 2 * C : ℝ≥0) : ENNReal) * edist x y ^ (α : ℝ)
  rw [edist_dist]
  calc
    ENNReal.ofReal (dist (((A x)⁻¹) i j) (((A y)⁻¹) i j)) =
        ENNReal.ofReal ‖((A x)⁻¹) i j - ((A y)⁻¹) i j‖ := by rw [dist_eq_norm]
    _ ≤ ENNReal.ofReal (((n : ℝ) ^ 2) * (B : ℝ) ^ 2 * (C : ℝ) *
        dist x y ^ (α : ℝ)) := ENNReal.ofReal_le_ofReal hnorm
    _ = (((n : ℝ≥0) ^ 2 * B ^ 2 * C : ℝ≥0) : ENNReal) * edist x y ^ (α : ℝ) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      rw [← ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) α.coe_nonneg, ← edist_dist]
      rw [ENNReal.ofReal_eq_coe_nnreal (by positivity)]
      norm_cast

private theorem holderBoundOn_zero_matrix_inv_entry_of_bound {n : ℕ} {α C B : ℝ≥0}
    {U : Set (EuclideanSpace ℂ (Fin n))}
    (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, HolderBoundOn 0 α C U (fun z ↦ A z i j))
    (hUnit : ∀ z ∈ U, IsUnit (A z))
    (hInv : ∀ z ∈ U, ∀ i j, ‖(A z)⁻¹ i j‖ ≤ B) (i j : Fin n) :
    HolderBoundOn 0 α (max B ((n : ℝ≥0) ^ 2 * B ^ 2 * C)) U
      (fun z ↦ (A z)⁻¹ i j) := by
  let L := continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℂ (Fin n)) ℂ
  have hAholder (k l : Fin n) : HolderOnWith C α (fun z ↦ A z k l) U := by
    intro z hz w hw
    have h := (hA k l).2 z hz w hw
    rw [iteratedFDeriv_zero_eq_comp] at h
    change edist (L.symm (A z k l)) (L.symm (A w k l)) ≤ _ at h
    rw [L.symm.edist_map] at h
    exact h
  have hValueHolder := holderOnWith_matrix_inv_entry_of_norm_bound A hAholder hUnit hInv i j
  have hValueHolder' : HolderOnWith ((n : ℝ≥0) ^ 2 * B ^ 2 * C) α
      (fun z ↦ (A z)⁻¹ i j) U := hValueHolder
  refine ⟨?_, ?_⟩
  · intro k hk z hz
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    change ‖iteratedFDeriv ℝ 0 (fun z ↦ (A z)⁻¹ i j) z‖ ≤ _
    rw [norm_iteratedFDeriv_zero]
    exact (hInv z hz i j).trans (le_max_left _ _)
  · intro z hz w hw
    have h := hValueHolder'.mono_const (le_max_right B ((n : ℝ≥0) ^ 2 * B ^ 2 * C)) z hz w hw
    rw [iteratedFDeriv_zero_eq_comp]
    change edist (L.symm ((A z)⁻¹ i j)) (L.symm ((A w)⁻¹ i j)) ≤ _
    rw [L.symm.edist_map]
    exact h

/-- Uniform entrywise `C^{0,α}` control of the inverse of a family of uniformly elliptic
Hermitian matrices. All constants are uniform in the auxiliary parameter. -/
theorem exists_uniform_holderBoundOn_matrix_inverse
    {n : ℕ}
    (α lam K : ℝ≥0) (hlam : 0 < lam)
    (U : Set (EuclideanSpace ℂ (Fin n))) (P : Set ℝ)
    (A : ℝ → ℝ → EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (hEll : ∀ h ∈ P, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      IsUniformlyEllipticOn (A h s) lam U)
    (hHolder : ∀ h ∈ P, ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ j l,
      HolderBoundOn 0 α K U (fun z ↦ A h s z j l)) :
    ∃ Kinv : ℝ≥0, ∀ h ∈ P, ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ j l,
      HolderBoundOn 0 α Kinv U (fun z ↦ (A h s z)⁻¹ j l) := by
  let B : ℝ≥0 := lam⁻¹
  let Kinv : ℝ≥0 := max B ((n : ℝ≥0) ^ 2 * B ^ 2 * K)
  refine ⟨Kinv, ?_⟩
  intro h hh s hs j l
  have hUnit : ∀ z ∈ U, IsUnit (A h s z) := by
    intro z hz
    exact (uniformlyEllipticOn_matrix_inverse_bound lam hlam (A h s z)
      (hEll h hh s hs z hz)).1
  have hInv : ∀ z ∈ U, ∀ i j, ‖(A h s z)⁻¹ i j‖ ≤ B := by
    intro z hz i j
    simpa [B] using (uniformlyEllipticOn_matrix_inverse_bound lam hlam (A h s z)
      (hEll h hh s hs z hz)).2 i j
  have hEntry : ∀ i j, HolderBoundOn 0 α K U (fun z ↦ A h s z i j) := hHolder h hh s hs
  have hResult := holderBoundOn_zero_matrix_inv_entry_of_bound (A h s) hEntry hUnit hInv j l
  simpa [Kinv, B] using hResult
