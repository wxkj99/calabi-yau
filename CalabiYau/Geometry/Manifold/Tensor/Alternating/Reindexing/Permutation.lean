-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Tensor/Alternating/Reindexing/Permutation.lean
-- Locally modified.
/-
Authors: Yury Kudryashov
Coauthors: Jack McCarthy
-/
module
public import CalabiYau.Mathlib.Logic.Equiv.FinReindexing
public import Mathlib.LinearAlgebra.Alternating.DomCoprod

@[expose] public section

namespace Equiv.Perm

open Fin

variable {m n p k : ℕ}

@[simps!]
def addAssocPerm : Equiv.Perm ((Fin m ⊕ Fin n) ⊕ Fin p) ≃ Equiv.Perm (Fin m ⊕ Fin n ⊕ Fin p) :=
    Equiv.permCongr (Equiv.sumAssoc (Fin m) (Fin n) (Fin p))

@[simp]
lemma sign_addAssocPerm (σ₁ : Equiv.Perm ((Fin m ⊕ Fin n) ⊕ Fin p)) :
    Equiv.Perm.sign (addAssocPerm σ₁) = Equiv.Perm.sign σ₁ := by
  simp only [addAssocPerm, Equiv.Perm.sign_permCongr]

def sumCongrPerm : Equiv.Perm (Fin m ⊕ Fin n) ≃ Equiv.Perm (Fin n ⊕ Fin m) :=
  Equiv.permCongr finSumCongr

@[simp]
lemma sumCongrPerm_sumCongrPerm (σ₁ : Equiv.Perm (Fin m ⊕ Fin n)) :
    sumCongrPerm (sumCongrPerm σ₁) = σ₁ := by
  ext i
  simp [sumCongrPerm, finSumCongr]

open Equiv.Perm in
lemma sumCongrPerm_spec (a b : Equiv.Perm (Fin m ⊕ Fin n))
    (h : (QuotientGroup.leftRel (Equiv.Perm.sumCongrHom (Fin m) (Fin n)).range) a b) :
    (Quot.mk (QuotientGroup.leftRel (sumCongrHom (Fin n) (Fin m)).range) ∘ sumCongrPerm) a =
      (Quot.mk (QuotientGroup.leftRel (sumCongrHom (Fin n) (Fin m)).range) ∘ sumCongrPerm) b := by
  apply Quot.sound
  rw [@QuotientGroup.leftRel_apply] at h ⊢
  simp only [sumCongrPerm, Equiv.permCongr_def]
  rw [inv_def, Equiv.Perm.mul_def]
  simp only [MonoidHom.mem_range, sumCongrHom_apply, Prod.exists] at h
  rcases h with ⟨ σ, τ, h ⟩
  simp only [MonoidHom.mem_range, sumCongrHom_apply, Prod.exists]
  use τ , σ
  ext (x | y)
  · simp only [Equiv.sumCongr_apply, Sum.map_inl, Equiv.trans_apply, Equiv.symm_trans_apply,
      Equiv.symm_apply_apply, Equiv.symm_symm]
    apply_fun (fun f => f (Sum.inr x)) at h
    simp only [Equiv.sumCongr_apply, Sum.map_inr, inv_def, coe_mul, Function.comp_apply] at h
    rw [← Equiv.symm_apply_eq, finSumCongr_symm_inl_inr, finSumCongr_symm_inl_inr, h]
  · simp only [Equiv.sumCongr_apply, Sum.map_inr, Equiv.trans_apply, Equiv.symm_trans_apply,
      Equiv.symm_apply_apply, Equiv.symm_symm]
    apply_fun (fun f => f (Sum.inl y)) at h
    simp only [Equiv.sumCongr_apply, Sum.map_inl, inv_def, coe_mul, Function.comp_apply] at h
    rw [← Equiv.symm_apply_eq, finSumCongr_symm_inr_inl, finSumCongr_symm_inr_inl, h]

@[simp]
lemma sign_sumCongrPerm (σ₁ : Equiv.Perm (Fin m ⊕ Fin n)) :
    Equiv.Perm.sign (sumCongrPerm σ₁) = Equiv.Perm.sign σ₁ := by
  simp only [sumCongrPerm, Equiv.Perm.sign_permCongr]

open Equiv.Perm in
@[simps!]
def finAddCongrEquiv : ModSumCongr (Fin m) (Fin n) ≃ ModSumCongr (Fin n) (Fin m) where
  toFun := Quot.lift (Quot.mk _ ∘ Perm.sumCongrPerm) Perm.sumCongrPerm_spec
  invFun := Quot.lift (Quot.mk _ ∘ Perm.sumCongrPerm) Perm.sumCongrPerm_spec
  left_inv := by
    intro x
    rcases x with ⟨σ₁⟩
    change Quot.mk _ (Perm.sumCongrPerm (Perm.sumCongrPerm σ₁)) = Quot.mk _ σ₁
    rw [Perm.sumCongrPerm_sumCongrPerm]
  right_inv := by
    intro x
    rcases x with ⟨σ₁⟩
    change Quot.mk _ (Perm.sumCongrPerm (Perm.sumCongrPerm σ₁)) = Quot.mk _ σ₁
    rw [Perm.sumCongrPerm_sumCongrPerm]

@[simps!]
def sumCommPerm : Equiv.Perm (Fin m ⊕ Fin n) ≃ Equiv.Perm (Fin n ⊕ Fin m) :=
  Equiv.permCongr (Equiv.sumComm (Fin m) (Fin n))

@[simp]
lemma sumCommPerm_sumCommPerm (σ₁ : Equiv.Perm (Fin m ⊕ Fin n)) :
    sumCommPerm (sumCommPerm σ₁) = σ₁ := by
  ext i
  simp

open Equiv.Perm in
lemma sumCommPerm_spec (a b : Equiv.Perm (Fin m ⊕ Fin n))
    (h : (QuotientGroup.leftRel (Equiv.Perm.sumCongrHom (Fin m) (Fin n)).range) a b) :
    (Quot.mk (QuotientGroup.leftRel (sumCongrHom (Fin n) (Fin m)).range) ∘ sumCommPerm) a =
      (Quot.mk (QuotientGroup.leftRel (sumCongrHom (Fin n) (Fin m)).range) ∘ sumCommPerm) b := by
  apply Quot.sound
  rw [@QuotientGroup.leftRel_apply] at h ⊢
  simp only [sumCommPerm, Equiv.permCongr_def]
  rw [inv_def, Equiv.Perm.mul_def]
  simp only [MonoidHom.mem_range, sumCongrHom_apply, Prod.exists] at h
  rcases h with ⟨ σ, τ, h ⟩
  simp only [Equiv.sumComm_symm, MonoidHom.mem_range, sumCongrHom_apply, Prod.exists]
  use τ , σ
  ext (x | y)
  · simp only [Equiv.sumCongr_apply, Sum.map_inl, Equiv.trans_apply, Equiv.sumComm_apply,
    Sum.swap_inl, Equiv.symm_trans_apply, Equiv.sumComm_symm, Sum.swap_swap]
    apply_fun (fun f => f (Sum.inr x)) at h
    simp only [Equiv.sumCongr_apply, Sum.map_inr, inv_def, coe_mul, Function.comp_apply] at h
    rw[← h]
    rfl
  · simp only [Equiv.sumCongr_apply, Sum.map_inr, Equiv.trans_apply, Equiv.sumComm_apply,
    Sum.swap_inr, Equiv.symm_trans_apply, Equiv.sumComm_symm, Sum.swap_swap]
    apply_fun (fun f => f (Sum.inl y)) at h
    simp only [Equiv.sumCongr_apply, Sum.map_inl, inv_def, coe_mul, Function.comp_apply] at  h
    rw[← h]
    rfl

@[simp]
lemma sign_sumCommPerm (σ₁ : Equiv.Perm (Fin m ⊕ Fin n)) :
    Equiv.Perm.sign (sumCommPerm σ₁) = Equiv.Perm.sign σ₁ := by
  simp only [sumCommPerm, Equiv.Perm.sign_permCongr]

@[simps!]
def finAddFlipEquiv : ModSumCongr (Fin m) (Fin n) ≃ ModSumCongr (Fin n) (Fin m) where
  toFun := Quot.lift (Quot.mk _ ∘ sumCommPerm) sumCommPerm_spec
  invFun := Quot.lift (Quot.mk _ ∘ sumCommPerm) sumCommPerm_spec
  left_inv := by
    intro x
    rcases x with ⟨σ₁⟩
    change Quot.mk _ (sumCommPerm (sumCommPerm σ₁)) = Quot.mk _ σ₁
    rw [sumCommPerm_sumCommPerm]
  right_inv := by
    intro x
    rcases x with ⟨σ₁⟩
    change Quot.mk _ (sumCommPerm (sumCommPerm σ₁)) = Quot.mk _ σ₁
    rw [sumCommPerm_sumCommPerm]

@[simps!]
def sumCommPermEqFin : Equiv.Perm (Fin m ⊕ Fin m) ≃ Equiv.Perm (Fin m ⊕ Fin m) :=
  MulAut.conj (Equiv.sumComm (Fin m) (Fin m))

@[simp]
lemma sumComm_inv : (Equiv.sumComm (Fin m) (Fin m))⁻¹ = (Equiv.sumComm (Fin m) (Fin m)) := by
  ext i
  simp [Equiv.Perm.inv_def]

@[simp]
lemma sumCommPerm_eqFin_sumCommPerm_eqFin (σ₁ : Equiv.Perm (Fin m ⊕ Fin m)) :
    sumCommPermEqFin (sumCommPermEqFin σ₁) = σ₁ := by
  ext i
  simp

lemma sumCommPerm_eqFin_spec (a b : Equiv.Perm (Fin m ⊕ Fin m))
    (h : (QuotientGroup.leftRel (Equiv.Perm.sumCongrHom (Fin m) (Fin m)).range) a b) :
      (Quot.mk (QuotientGroup.leftRel (sumCongrHom (Fin m) (Fin m)).range) ∘ sumCommPermEqFin) a =
      (Quot.mk (QuotientGroup.leftRel (sumCongrHom (Fin m) (Fin m)).range) ∘ sumCommPermEqFin) b
    := by
  apply Quot.sound
  rw [@QuotientGroup.leftRel_apply] at h ⊢
  simp only [sumCommPermEqFin, EquivLike.coe_coe, MulAut.conj_apply, sumComm_inv,
    mul_assoc, mul_inv_rev]
  have this (c) : Equiv.sumComm (Fin m) (Fin m) * (Equiv.sumComm (Fin m) (Fin m) * c) = c := by
    ext
    simp [mul_def]
  rw[this]
  simp only [MonoidHom.mem_range, sumCongrHom_apply, Prod.exists] at h
  rcases h with ⟨σ, τ, h⟩
  rw[← mul_assoc _ b, ← h]
  simp only [MonoidHom.mem_range, sumCongrHom_apply, Prod.exists]
  use τ, σ
  ext (x|y) <;> simp

@[simp]
lemma sign_sumCommPerm_eqFin (σ₁ : Equiv.Perm (Fin m ⊕ Fin m)) :
    Equiv.Perm.sign (sumCommPermEqFin σ₁) = Equiv.Perm.sign σ₁ := by
  simp only [sumCommPermEqFin, EquivLike.coe_coe, MulAut.conj_apply, sumComm_inv,
    Equiv.Perm.sign_mul]
  rw[mul_comm, ← mul_assoc]
  simp

open Equiv.Perm in
@[simps]
def finAddFlipEquivEqFin : ModSumCongr (Fin m) (Fin m) ≃ ModSumCongr (Fin m) (Fin m) where
  toFun := Quot.lift (Quot.mk _ ∘ sumCommPermEqFin) sumCommPerm_eqFin_spec
  invFun := Quot.lift (Quot.mk _ ∘ sumCommPermEqFin) sumCommPerm_eqFin_spec
  left_inv := by
    intro x
    rcases x with ⟨σ₁⟩
    change Quot.mk _ (sumCommPermEqFin (sumCommPermEqFin σ₁)) = Quot.mk _ σ₁
    rw [sumCommPerm_eqFin_sumCommPerm_eqFin]
  right_inv := by
    intro x
    rcases x with ⟨σ₁⟩
    change Quot.mk _ (sumCommPermEqFin (sumCommPermEqFin σ₁)) = Quot.mk _ σ₁
    rw [sumCommPerm_eqFin_sumCommPerm_eqFin]

noncomputable instance instFintypeOrderEmbeddingFinDifferentialGeometry :
    Fintype (Fin k ↪o Fin n) :=
  Fintype.ofEquiv _
    (Set.powersetCard.ofFinEmbEquiv
      (I := Fin n) (n := k)).symm

theorem orderEmb_eq_of_range_eq
    {I J : Fin k ↪o Fin n}
    (h : Set.range (⇑I) = Set.range (⇑J)) : I = J :=
  DFunLike.ext'
    ((I.strictMono.range_inj J.strictMono).mp h)

theorem orderEmb_ne_comp_perm
    {I J : Fin k ↪o Fin n} (hIJ : I ≠ J)
    (σ : Equiv.Perm (Fin k)) :
    (⇑I : Fin k → Fin n) ≠ ⇑J ∘ ⇑σ := by
  intro heq; apply hIJ; apply orderEmb_eq_of_range_eq
  rw [heq, Set.range_comp,
    Equiv.range_eq_univ, Set.image_univ]

def addCasesSwapPerm (m n : ℕ) : Equiv.Perm (Fin (m + n)) where
  toFun i := if h : i.val < n then ⟨m + i.val, by omega⟩
    else ⟨i.val - n, by omega⟩
  invFun i := if h : i.val < m then ⟨n + i.val, by omega⟩
    else ⟨i.val - m, by omega⟩
  left_inv := fun ⟨i, hi⟩ => by
    ext
    by_cases h1 : i < n
    · simp only [h1, dite_true]
      have h2 : ¬(m + i < m) := by omega
      simp only [h2, dite_false]
      omega
    · simp only [h1, dite_false]
      have h2 : i - n < m := by omega
      simp only [h2, dite_true]
      omega
  right_inv := fun ⟨i, hi⟩ => by
    ext
    by_cases h1 : i < m
    · simp only [h1, dite_true]
      have h2 : ¬(n + i < n) := by omega
      simp only [h2, dite_false]
      omega
    · simp only [h1, dite_false]
      have h2 : i - m < n := by omega
      simp only [h2, dite_true]
      omega

lemma finRotate_pow_apply {s : ℕ} (hs : s ≠ 0) (k' : ℕ) (j : Fin s) :
    ((finRotate s ^ k') j : ℕ) = (j.val + k') % s := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs
  induction k' generalizing j with
  | zero =>
    simp only [pow_zero, Nat.add_zero]
    exact (Nat.mod_eq_of_lt j.isLt).symm
  | succ k' ih =>
    rw [pow_succ, Equiv.Perm.mul_apply]
    have h_rot : ∀ x : Fin (k + 1), (finRotate (k + 1) x : ℕ) = (x.val + 1) % (k + 1) := by
      intro x
      by_cases hx : x.val < k
      · have hx' : x ≠ Fin.last k := by
          intro contra
          have hc : (Fin.last k).val = k := rfl
          rw [contra, hc] at hx
          omega
        rw [coe_finRotate_of_ne_last hx']
        exact (Nat.mod_eq_of_lt (show x.val + 1 < k + 1 by omega)).symm
      · have hx' : x = Fin.last k := by apply Fin.ext; have hc : (Fin.last k).val = k := rfl; omega
        rw [hx', coe_finRotate, if_pos rfl]
        have eq1 : (Fin.last k).val = k := rfl
        rw [eq1]
        have eq2 : k + 1 = 0 + (k + 1) := by omega
        rw [eq2, Nat.mod_self]
    have ih' := ih (finRotate (k + 1) j)
    rw [ih', h_rot j]
    have eq_mod : ((j.val + 1) % (k + 1) + k') % (k + 1) = (j.val + 1 + k') % (k + 1) := by
      apply Nat.ModEq.symm
      calc j.val + 1 + k'
        _ ≡ (j.val + 1) + k' [MOD k + 1] := Nat.ModEq.refl _
        _ ≡ (j.val + 1) % (k + 1) + k' [MOD k + 1] :=
          Nat.ModEq.add_right k' (Nat.mod_modEq (j.val + 1) (k + 1)).symm
    rw [eq_mod]
    congr 1
    omega

lemma addCasesSwapPerm_eq_finRotate (hm : m + n ≠ 0) :
    addCasesSwapPerm m n = (finRotate (m + n)) ^ m := by
  ext ⟨i, hi⟩
  simp only [addCasesSwapPerm, Equiv.coe_fn_mk]
  have h_pow := finRotate_pow_apply hm m ⟨i, hi⟩
  by_cases h_lt : i < n
  · simp only [h_lt, dite_true]
    have eq1 : ((finRotate (m + n) ^ m) ⟨i, hi⟩ : ℕ) = (i + m) % (m + n) := h_pow
    have eq2 : (i + m) % (m + n) = i + m := by
      apply Nat.mod_eq_of_lt
      omega
    rw [eq1, eq2, add_comm]
  · simp only [h_lt, dite_false]
    have eq1 : ((finRotate (m + n) ^ m) ⟨i, hi⟩ : ℕ) = (i + m) % (m + n) := h_pow
    have eq2 : (i + m) % (m + n) = i - n := by
      calc (i + m) % (m + n)
        _ = (i + m - (m + n)) % (m + n) := Nat.mod_eq_sub_mod (by omega)
        _ = i + m - (m + n) := Nat.mod_eq_of_lt (by omega)
        _ = i - n := by omega
    rw [eq1, eq2]

theorem addCasesSwapPerm_sign (m n : ℕ) :
    Equiv.Perm.sign (addCasesSwapPerm m n) = (-1) ^ (m * n) := by
  by_cases hm : m + n = 0
  · have h1 : m = 0 := by omega
    have h2 : n = 0 := by omega
    subst h1
    subst h2
    rfl
  · have hm_ne : m + n ≠ 0 := hm
    rw [addCasesSwapPerm_eq_finRotate hm_ne]
    rw [map_pow]
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm_ne
    have h_sign : Equiv.Perm.sign (finRotate (m + n)) = (-1) ^ (m + n - 1) := by
      rw [hk]
      exact sign_finRotate k.succ
    rw [h_sign, ← pow_mul]
    have e1 : (-1 : ℤˣ) ^ ((m + n - 1) * m) = (-1 : ℤˣ) ^ (((m + n - 1) * m) % 2) :=
      Int.units_pow_eq_pow_mod_two (-1 : ℤˣ) ((m + n - 1) * m)
    have e2 : (-1 : ℤˣ) ^ (m * n) = (-1 : ℤˣ) ^ ((m * n) % 2) :=
      Int.units_pow_eq_pow_mod_two (-1 : ℤˣ) (m * n)
    rw [e1, e2]
    congr 1
    have h1 : m % 2 = 0 ∨ m % 2 = 1 := by omega
    rcases h1 with h_m | h_m
    · obtain ⟨c, hc⟩ : ∃ c, m = 2 * c := ⟨m / 2, by omega⟩
      subst hc
      have e3 : (2 * c + n - 1) * (2 * c) = 2 * ((2 * c + n - 1) * c) := by ring
      have e4 : 2 * c * n = 2 * (c * n) := by ring
      rw [e3, e4]
      simp
    · obtain ⟨c, hc⟩ : ∃ c, m = 2 * c + 1 := ⟨m / 2, by omega⟩
      subst hc
      have e3 : (2 * c + 1 + n - 1) * (2 * c + 1) = (2 * c + n) * (2 * c + 1) := by
        congr 1
        omega
      have e4 : (2 * c + n) * (2 * c + 1) = 2 * ((2 * c + n) * c + c) + n := by ring
      rw [e3, e4]
      have e5 : (2 * c + 1) * n = 2 * (c * n) + n := by ring
      rw [e5]
      rw [Nat.add_mod, show 2 * ((2 * c + n) * c + c) % 2 = 0 by simp]
      simp [Nat.add_mod]

variable {𝕜 : Type*} [Field 𝕜]

end Perm
end Equiv
