module

public import CalabiYau.Mathlib.Analysis.Matrix.Order

/-!
# Uniform inverse-entry bounds from determinant and coefficient bounds

The Monge–Ampère determinant identity supplies a positive lower bound for the determinant of the
perturbed metric. Combined with the upper coefficient bound, the adjugate formula bounds the
entries of its inverse uniformly across the solution family.
-/

@[expose] public section

open scoped NNReal

namespace UniformInverseEntryBound

private theorem norm_det_le_of_entries {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    {M : ℝ} (_hM : 0 ≤ M)
    (hA : ∀ i j, ‖A i j‖ ≤ M) :
    ‖A.det‖ ≤ (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * M ^ n := by
  classical
  rw [Matrix.det_apply']
  calc
    ‖∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ k : Fin n, A (σ k) k‖ ≤
        ∑ σ : Equiv.Perm (Fin n), ‖((Equiv.Perm.sign σ : ℤ) : ℂ) *
          ∏ k : Fin n, A (σ k) k‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), M ^ n := by
      apply Finset.sum_le_sum
      intro σ hσ
      rw [norm_mul]
      have hsign : ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast Equiv.Perm.sign_abs σ
      have hprod : ‖∏ k : Fin n, A (σ k) k‖ ≤ M ^ n := by
        rw [norm_prod]
        calc
          ∏ k : Fin n, ‖A (σ k) k‖ ≤ ∏ _k : Fin n, M :=
            Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun k _ => hA (σ k) k)
          _ = M ^ n := by simp [Finset.prod_const]
      rw [hsign]
      simpa using hprod
    _ = (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * M ^ n := by
      simp [Finset.sum_const, nsmul_eq_mul]

/-- A finite matrix with bounded entries and determinant bounded away from zero has bounded
inverse entries, uniformly in the matrix. -/
theorem exists_uniform_matrix_inverse_entry_bound
    {n : ℕ} {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ) :
    ∃ B : ℝ≥0, ∀ A : Matrix (Fin n) (Fin n) ℂ,
      (∀ i : Fin n, ∀ j : Fin n, ‖A i j‖ ≤ (C : ℝ)) →
      δ ≤ ‖A.det‖ →
      ∀ i j, ‖A⁻¹ i j‖ ≤ B := by
  classical
  let M : ℝ := max C 1
  have hMC : C ≤ M := le_max_left C 1
  have hM1 : 1 ≤ M := le_max_right C 1
  have hM0 : 0 ≤ M := le_trans hC hMC
  let Bval : ℝ := (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * M ^ n / δ
  have hBval : 0 ≤ Bval := by
    dsimp [Bval]
    positivity
  refine ⟨⟨Bval, hBval⟩, ?_⟩
  intro A hA hdet i j
  have hA' : ∀ k l, ‖A k l‖ ≤ M := fun k l => (hA k l).trans hMC
  have hAdj : ‖A.adjugate i j‖ ≤
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * M ^ n := by
    rw [Matrix.adjugate_apply]
    apply norm_det_le_of_entries _ hM0
    intro k l
    rw [Matrix.updateRow_apply]
    split_ifs with h
    · simp only [Pi.single_apply]
      split_ifs
      · simpa only [norm_one] using hM1
      · simpa only [norm_zero] using hM0
    · exact hA' k l
  have hdet_pos : 0 < ‖A.det‖ := lt_of_lt_of_le hδ hdet
  have hinvdet : ‖A.det‖⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ hdet
  have hinvdet' : ‖A.det⁻¹‖ ≤ δ⁻¹ := by simpa only [norm_inv] using hinvdet
  have hinv_entry : ‖A⁻¹ i j‖ ≤ δ⁻¹ *
      ((Fintype.card (Equiv.Perm (Fin n)) : ℝ) * M ^ n) := by
    rw [Matrix.inv_def, Matrix.smul_apply, norm_smul, Ring.inverse_eq_inv]
    calc
      ‖A.det⁻¹‖ * ‖A.adjugate i j‖ ≤ δ⁻¹ * ‖A.adjugate i j‖ :=
        mul_le_mul_of_nonneg_right hinvdet' (norm_nonneg _)
      _ ≤ δ⁻¹ * ((Fintype.card (Equiv.Perm (Fin n)) : ℝ) * M ^ n) :=
        mul_le_mul_of_nonneg_left hAdj (by positivity)
  have hfinal : δ⁻¹ *
      ((Fintype.card (Equiv.Perm (Fin n)) : ℝ) * M ^ n) ≤ Bval := by
    simp [Bval, div_eq_mul_inv, mul_comm]
  exact (hinv_entry.trans hfinal)

end UniformInverseEntryBound

end
