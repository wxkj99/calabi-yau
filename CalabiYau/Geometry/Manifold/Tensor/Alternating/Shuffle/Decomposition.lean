-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Tensor/Alternating/Shuffle/Decomposition.lean
-- Locally modified.
/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module
public import CalabiYau.Geometry.Manifold.Tensor.Alternating.Shuffle.Split
public import Mathlib.GroupTheory.Perm.Finite
public import Mathlib.GroupTheory.Perm.Option
public import Mathlib.LinearAlgebra.Alternating.DomCoprod
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.Group

@[expose] public section

open CalabiYau

namespace ContinuousAlternatingMap

variable {m n : ℕ}

theorem shuffle_side_well_defined
    {σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1))}
    (τ : (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin (n + 1))).range) :
    (∃ k, σ⁻¹ (Sum.inl 0) = Sum.inl k) ↔
    (∃ k, ((σ * ↑τ)⁻¹ (Sum.inl 0)) = Sum.inl k) := by
  obtain ⟨⟨τ_l, τ_r⟩, hτ⟩ := τ.prop
  constructor <;> intro ⟨k, hk⟩
  · refine ⟨τ_l⁻¹ k, ?_⟩
    have : (↑τ : Equiv.Perm _) = Equiv.Perm.sumCongrHom _ _ (τ_l, τ_r) := hτ.symm
    simp only [mul_inv_rev, Equiv.Perm.coe_mul, Function.comp_apply,
      this, Equiv.Perm.sumCongrHom_apply, Equiv.Perm.sumCongr_inv,
      Equiv.sumCongr_apply, hk, Sum.map_inl]
  · rcases h : σ⁻¹ (Sum.inl (0 : Fin (m + 1))) with j | j
    · exact ⟨j, rfl⟩
    · exfalso
      have : (σ * ↑τ)⁻¹ (Sum.inl 0) = Sum.inr (τ_r⁻¹ j) := by
        simp only [mul_inv_rev, Equiv.Perm.coe_mul, Function.comp_apply, h,
          show (↑τ : Equiv.Perm _) = Equiv.Perm.sumCongrHom _ _ (τ_l, τ_r)
            from hτ.symm,
          Equiv.Perm.sumCongrHom_apply, Equiv.Perm.sumCongr_inv,
          Equiv.sumCongr_apply, Sum.map_inr]
      rw [hk] at this; simp at this

theorem shuffle_side_well_defined_right
    {σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1))}
    (τ : (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin (n + 1))).range) :
    (∃ k, σ⁻¹ (Sum.inl 0) = Sum.inr k) ↔
    (∃ k, ((σ * ↑τ)⁻¹ (Sum.inl 0)) = Sum.inr k) := by
  constructor <;> intro ⟨k, hk⟩
  · rcases h : (σ * ↑τ)⁻¹ (Sum.inl 0) with j | j
    · have := (shuffle_side_well_defined (σ := σ) τ).mpr ⟨j, h⟩
      obtain ⟨j', hj'⟩ := this; rw [hk] at hj'; exact absurd hj' (by simp)
    · exact ⟨j, h.symm ▸ rfl⟩
  · rcases h : σ⁻¹ (Sum.inl 0) with j | j
    · have := (shuffle_side_well_defined (σ := σ) τ).mp ⟨j, h⟩
      obtain ⟨j', hj'⟩ := this; rw [hk] at hj'; exact absurd hj' (by simp)
    · exact ⟨j, h.symm ▸ rfl⟩

noncomputable def finSuccSumOptionEquiv {m n : ℕ} :
    Fin (m + 1) ⊕ Fin (n + 1) ≃ Option (Fin m ⊕ Fin (n + 1)) :=
  (Equiv.sumCongr (finSuccEquiv' 0) (Equiv.refl _)).trans ShuffleSplit.optionSumEquiv

@[simp] theorem finSuccSumOptionEquiv_inl_zero {m n : ℕ} :
    (finSuccSumOptionEquiv : Fin (m + 1) ⊕ Fin (n + 1) ≃ _)
      (Sum.inl (0 : Fin (m + 1))) = none := by
  simp [finSuccSumOptionEquiv]

@[simp] theorem finSuccSumOptionEquiv_symm_none {m n : ℕ} :
    (finSuccSumOptionEquiv : Fin (m + 1) ⊕ Fin (n + 1) ≃ _).symm none =
      Sum.inl 0 := by
  simp [finSuccSumOptionEquiv]

def normalizeLeft (σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (k : Fin (m + 1)) :
    Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)) :=
  σ * Equiv.Perm.sumCongr (Equiv.swap 0 k) 1

theorem normalizeLeft_fixes (σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (k : Fin (m + 1)) (hk : σ⁻¹ (Sum.inl 0) = Sum.inl k) :
    normalizeLeft σ k (Sum.inl 0) = Sum.inl 0 := by
  simp only [normalizeLeft, Equiv.Perm.coe_mul, Function.comp_apply,
    Equiv.sumCongr_apply, Sum.map_inl, Equiv.swap_apply_left]
  rw [← hk]; simp

theorem normalizeLeft_coset (σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (k : Fin (m + 1)) :
    Quotient.mk'' (normalizeLeft σ k) =
      (Quotient.mk'' σ : Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin (n + 1))) := by
  symm; apply Quotient.sound'
  rw [QuotientGroup.leftRel_apply]
  refine ⟨⟨(Equiv.swap 0 k)⁻¹, 1⟩, ?_⟩
  simp [normalizeLeft, Equiv.Perm.sumCongrHom_apply]

noncomputable def restrictComplement
    (σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1))) :
    Equiv.Perm (Fin m ⊕ Fin (n + 1)) :=
  Equiv.removeNone (Equiv.permCongr finSuccSumOptionEquiv σ)

theorem restrictComplement_sign
    (σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (hfix : σ (Sum.inl 0) = Sum.inl 0) :
    Equiv.Perm.sign (restrictComplement σ) = Equiv.Perm.sign σ := by
  unfold restrictComplement
  rw [ShuffleSplit.removeNone_sign, Equiv.Perm.sign_permCongr]
  change finSuccSumOptionEquiv (σ (finSuccSumOptionEquiv.symm none)) = none
  rw [finSuccSumOptionEquiv_symm_none, hfix, finSuccSumOptionEquiv_inl_zero]

theorem restrictComplement_sumCongr_mem
    (τ_l : Equiv.Perm (Fin (m + 1))) (τ_r : Equiv.Perm (Fin (n + 1)))
    (hτ_fix : τ_l 0 = 0) :
    restrictComplement (Equiv.Perm.sumCongr τ_l τ_r) ∈
      (Equiv.Perm.sumCongrHom (Fin m) (Fin (n + 1))).range := by
  apply Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl
  intro x ⟨a, ha⟩; subst ha
  set σ_opt := Equiv.permCongr finSuccSumOptionEquiv (Equiv.Perm.sumCongr τ_l τ_r)
  have h_fix : σ_opt none = none := by simp [σ_opt, Equiv.permCongr_apply, hτ_fix]
  have h_oc := ShuffleSplit.optionCongr_removeNone_of_fix_none σ_opt h_fix
  suffices h : ∃ a', σ_opt (some (Sum.inl a)) = some (Sum.inl a') by
    obtain ⟨a', ha'⟩ := h
    have h_eq := congr_fun (congr_arg DFunLike.coe h_oc) (some (Sum.inl a))
    simp only [Equiv.optionCongr_apply, Option.map_some] at h_eq
    change restrictComplement _ (Sum.inl a) ∈ _
    unfold restrictComplement
    rw [show Equiv.removeNone (Equiv.permCongr finSuccSumOptionEquiv
      (Equiv.Perm.sumCongr τ_l τ_r)) = Equiv.removeNone σ_opt from rfl]
    rw [ha'] at h_eq
    exact ⟨a', ((Option.some_injective _) h_eq.symm)⟩
  have h_ne : τ_l (Fin.succAbove 0 a) ≠ 0 := by
    intro h_eq
    exact Fin.succAbove_ne 0 a (τ_l.injective (h_eq.trans hτ_fix.symm))
  obtain ⟨a', ha'⟩ : ∃ a', finSuccEquiv' (0 : Fin (m + 1))
      (τ_l (Fin.succAbove 0 a)) = some a' := by
    rcases h : finSuccEquiv' (0 : Fin (m + 1)) (τ_l (Fin.succAbove 0 a)) with _ | a'
    · exact absurd ((finSuccEquiv' 0).injective
        (h.trans (finSuccEquiv'_at 0).symm)) h_ne
    · exact ⟨a', rfl⟩
  refine ⟨a', ?_⟩
  change (finSuccSumOptionEquiv (Equiv.Perm.sumCongr τ_l τ_r
    (finSuccSumOptionEquiv.symm (some (Sum.inl a))))) = some (Sum.inl a')
  change ShuffleSplit.optionSumEquiv
    (Sum.map (finSuccEquiv' 0) id
      (Sum.map τ_l τ_r
        (Sum.map (finSuccEquiv' 0).symm id
          (Sum.inl (some a))))) = some (Sum.inl a')
  simp only [Sum.map_inl]
  rw [show (finSuccEquiv' (0 : Fin (m + 1))).symm (some a) = Fin.succAbove 0 a from
    (finSuccEquiv'_succAbove 0 a ▸ (finSuccEquiv' 0).symm_apply_apply _).symm,
    ha']; rfl

noncomputable def shuffleLeftRestrictRepresentative
    (σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (hσ : ∃ k, σ⁻¹ (Sum.inl 0) = Sum.inl k) :
    Equiv.Perm (Fin m ⊕ Fin (n + 1)) :=
  let k := hσ.choose
  restrictComplement (normalizeLeft σ k)

theorem shuffleLeftRestrictRepresentative_respects_leftRel
    (σ₁ σ₂ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (hσ₁ : ∃ k, σ₁⁻¹ (Sum.inl 0) = Sum.inl k)
    (hσ₂ : ∃ k, σ₂⁻¹ (Sum.inl 0) = Sum.inl k)
    (h_rel : QuotientGroup.leftRel
        (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin (n + 1))).range σ₁ σ₂) :
    QuotientGroup.leftRel
        (Equiv.Perm.sumCongrHom (Fin m) (Fin (n + 1))).range
        (shuffleLeftRestrictRepresentative σ₁ hσ₁) (shuffleLeftRestrictRepresentative σ₂ hσ₂) := by
  set k₁ := hσ₁.choose; set hk₁ := hσ₁.choose_spec
  set k₂ := hσ₂.choose; set hk₂ := hσ₂.choose_spec
  set n1 := normalizeLeft σ₁ k₁
  set n2 := normalizeLeft σ₂ k₂
  have hn1 := normalizeLeft_fixes σ₁ k₁ hk₁
  have hn2 := normalizeLeft_fixes σ₂ k₂ hk₂
  have h_n_rel : QuotientGroup.leftRel
      (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin (n + 1))).range n1 n2 := by
    rw [QuotientGroup.leftRel_apply]
    rw [QuotientGroup.leftRel_apply] at h_rel
    obtain ⟨⟨τ_l, τ_r⟩, hτ⟩ := h_rel
    refine ⟨⟨(Equiv.swap 0 k₁)⁻¹ * τ_l * Equiv.swap 0 k₂, τ_r⟩, ?_⟩
    simp only [Equiv.Perm.sumCongrHom_apply]
    change Equiv.Perm.sumCongr ((Equiv.swap 0 k₁)⁻¹ * τ_l * Equiv.swap 0 k₂)
      τ_r = n1⁻¹ * n2
    have hτ_eq : Equiv.Perm.sumCongr τ_l τ_r = σ₁⁻¹ * σ₂ := by
      change (Equiv.Perm.sumCongrHom _ _ (τ_l, τ_r) : Equiv.Perm _) = _; exact hτ
    symm
    calc n1⁻¹ * n2
        = (Equiv.Perm.sumCongr (Equiv.swap 0 k₁) 1)⁻¹ * σ₁⁻¹ *
            (σ₂ * Equiv.Perm.sumCongr (Equiv.swap 0 k₂) 1) := by
          simp [n1, n2, normalizeLeft]
      _ = Equiv.Perm.sumCongr (Equiv.swap 0 k₁)⁻¹ 1 *
            Equiv.Perm.sumCongr τ_l τ_r *
            Equiv.Perm.sumCongr (Equiv.swap 0 k₂) 1 := by
          rw [Equiv.Perm.sumCongr_inv, inv_one, hτ_eq]; group
      _ = Equiv.Perm.sumCongr ((Equiv.swap 0 k₁)⁻¹ * τ_l * Equiv.swap 0 k₂) τ_r := by
          rw [Equiv.Perm.sumCongr_mul, Equiv.Perm.sumCongr_mul]; simp
  rw [QuotientGroup.leftRel_apply] at h_n_rel ⊢
  obtain ⟨⟨τ_l, τ_r⟩, hτ⟩ := h_n_rel
  have hτ_eq : (Equiv.Perm.sumCongr τ_l τ_r : Equiv.Perm _) = n1⁻¹ * n2 := by
    change (Equiv.Perm.sumCongrHom _ _ (τ_l, τ_r) : Equiv.Perm _) = _; exact hτ
  have hn12 : (n1⁻¹ * n2) (Sum.inl 0) = Sum.inl 0 := by
    change n1.symm (n2 (Sum.inl 0)) = _
    rw [hn2]; exact n1.symm_apply_eq.mpr hn1.symm
  have hτ_fix : τ_l 0 = 0 := by
    have : Equiv.Perm.sumCongr τ_l τ_r (Sum.inl 0) = Sum.inl 0 := hτ_eq ▸ hn12
    simpa using this
  have h_n1_none : Equiv.permCongr finSuccSumOptionEquiv n1 none = none := by
    change finSuccSumOptionEquiv (n1 (finSuccSumOptionEquiv.symm none)) = none
    rw [finSuccSumOptionEquiv_symm_none, hn1, finSuccSumOptionEquiv_inl_zero]
  have h_n2_none : Equiv.permCongr finSuccSumOptionEquiv n2 none = none := by
    change finSuccSumOptionEquiv (n2 (finSuccSumOptionEquiv.symm none)) = none
    rw [finSuccSumOptionEquiv_symm_none, hn2, finSuccSumOptionEquiv_inl_zero]
  have h_rc_mul : (restrictComplement n1)⁻¹ * restrictComplement n2 =
      restrictComplement (n1⁻¹ * n2) := by
    unfold restrictComplement
    rw [ShuffleSplit.permCongr_inv_mul (finSuccSumOptionEquiv) n1 n2,
      ShuffleSplit.removeNone_inv_mul _ _ h_n1_none h_n2_none]
  change (restrictComplement n1)⁻¹ * restrictComplement n2 ∈ _
  rw [h_rc_mul]
  have : restrictComplement (n1⁻¹ * n2) =
      restrictComplement (Equiv.Perm.sumCongr τ_l τ_r) := by
    congr 1; exact hτ_eq.symm
  rw [this]
  exact restrictComplement_sumCongr_mem τ_l τ_r hτ_fix

noncomputable def shuffleLeftExtendRepresentative
    (σ' : Equiv.Perm (Fin m ⊕ Fin (n + 1))) :
    Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)) :=
  Equiv.permCongr finSuccSumOptionEquiv.symm σ'.optionCongr

theorem shuffleLeftExtendRepresentative_fixes (σ' : Equiv.Perm (Fin m ⊕ Fin (n + 1))) :
    shuffleLeftExtendRepresentative σ' (Sum.inl 0) = Sum.inl 0 := by
  unfold shuffleLeftExtendRepresentative
  simp [Equiv.permCongr_apply, finSuccSumOptionEquiv, ShuffleSplit.optionSumEquiv,
    Equiv.optionCongr_apply]

theorem shuffleLeftExtendRepresentative_isLeft (σ' : Equiv.Perm (Fin m ⊕ Fin (n + 1))) :
    ∃ k, (shuffleLeftExtendRepresentative σ')⁻¹ (Sum.inl 0) = Sum.inl k :=
  ⟨0, by rw [← shuffleLeftExtendRepresentative_fixes σ']; exact (shuffleLeftExtendRepresentative σ').symm_apply_apply _⟩

theorem restrictComplement_shuffleLeftExtendRepresentative
    (σ' : Equiv.Perm (Fin m ⊕ Fin (n + 1))) :
    restrictComplement (shuffleLeftExtendRepresentative σ') = σ' := by
  simp only [restrictComplement, shuffleLeftExtendRepresentative]
  have : Equiv.permCongr finSuccSumOptionEquiv
      (Equiv.permCongr finSuccSumOptionEquiv.symm σ'.optionCongr) =
      σ'.optionCongr := by
    ext x; simp [Equiv.permCongr_apply]
  rw [this]
  exact Equiv.removeNone_optionCongr σ'

theorem shuffleLeftExtendRepresentative_restrictComplement
    (σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (hfix : σ (Sum.inl 0) = Sum.inl 0) :
    shuffleLeftExtendRepresentative (restrictComplement σ) = σ := by
  have h_fixes_none :
      (Equiv.permCongr finSuccSumOptionEquiv σ) none = none := by
    simp [Equiv.permCongr_apply, hfix]
  simp only [shuffleLeftExtendRepresentative, restrictComplement]
  have h_round : (Equiv.removeNone
      (Equiv.permCongr finSuccSumOptionEquiv σ)).optionCongr =
      Equiv.permCongr finSuccSumOptionEquiv σ := by
    rw [map_equiv_removeNone, h_fixes_none]
    rw [Equiv.swap_self, ← Equiv.Perm.one_def, one_mul]
  ext x; simp [Equiv.permCongr_apply, h_round]

noncomputable def liftPermSucc (τ : Equiv.Perm (Fin m)) :
    Equiv.Perm (Fin (m + 1)) :=
  Equiv.permCongr (finSuccEquiv' 0).symm τ.optionCongr

theorem shuffleLeftExtendRepresentative_respects_leftRel
    (s1 s2 : Equiv.Perm (Fin m ⊕ Fin (n + 1)))
    (h_rel : QuotientGroup.leftRel
        (Equiv.Perm.sumCongrHom (Fin m) (Fin (n + 1))).range s1 s2) :
    QuotientGroup.leftRel
        (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin (n + 1))).range
        (shuffleLeftExtendRepresentative s1) (shuffleLeftExtendRepresentative s2) := by
  rw [QuotientGroup.leftRel_apply] at h_rel ⊢
  obtain ⟨⟨tl, tr⟩, htau⟩ := h_rel
  suffices h_mem : shuffleLeftExtendRepresentative (Equiv.Perm.sumCongr tl tr) ∈
      (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin (n + 1))).range by
    convert h_mem using 1
    have h_sc : (Equiv.Perm.sumCongrHom _ _ (tl, tr) : Equiv.Perm _) = s1⁻¹ * s2 := htau
    rw [show Equiv.Perm.sumCongr tl tr = s1⁻¹ * s2 from h_sc]
    ext x
    unfold shuffleLeftExtendRepresentative
    apply finSuccSumOptionEquiv.injective
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.permCongr_apply,
      Equiv.apply_symm_apply, Equiv.optionCongr_apply]
    change finSuccSumOptionEquiv
      ((Equiv.permCongr finSuccSumOptionEquiv.symm s1.optionCongr)⁻¹
        (finSuccSumOptionEquiv.symm (Option.map s2 (finSuccSumOptionEquiv x)))) =
      Option.map (fun x => s1⁻¹ (s2 x)) (finSuccSumOptionEquiv x)
    have h_inv_apply : forall z,
        ((Equiv.permCongr finSuccSumOptionEquiv.symm
          s1.optionCongr) : Equiv.Perm _)⁻¹ z =
        (Equiv.permCongr finSuccSumOptionEquiv.symm
          s1⁻¹.optionCongr) z := by
      intro z
      have : ((Equiv.permCongr finSuccSumOptionEquiv.symm
          s1.optionCongr) : Equiv.Perm _)⁻¹ =
        Equiv.permCongr finSuccSumOptionEquiv.symm s1⁻¹.optionCongr := by
        ext w
        simp only [Equiv.Perm.inv_def, Equiv.permCongr_apply]
        rw [Equiv.optionCongr_symm]; rfl
      rw [this]
    rw [h_inv_apply]
    simp only [Equiv.permCongr_apply, Equiv.apply_symm_apply,
      Equiv.optionCongr_apply, Equiv.symm_symm,
      Option.map_map, Function.comp_def]
  refine ⟨(liftPermSucc tl, tr), ?_⟩
  simp only [Equiv.Perm.sumCongrHom_apply]
  ext (a | b)
  · simp only [shuffleLeftExtendRepresentative, Equiv.permCongr_apply, Equiv.sumCongr_apply, Sum.map_inl,
      Equiv.optionCongr_apply, liftPermSucc]
    simp only [finSuccSumOptionEquiv, ShuffleSplit.optionSumEquiv,
      Equiv.symm_trans_apply]
    rcases h : (finSuccEquiv' (0 : Fin (m + 1))) a with _ | a' <;> simp [h]
  · simp [shuffleLeftExtendRepresentative, Equiv.permCongr_apply, Equiv.sumCongr_apply,
      Equiv.optionCongr_apply, finSuccSumOptionEquiv, ShuffleSplit.optionSumEquiv]

theorem shuffleLeftRestrictRepresentative_extendRepresentative
    (σ' : Equiv.Perm (Fin m ⊕ Fin (n + 1))) :
    shuffleLeftRestrictRepresentative (shuffleLeftExtendRepresentative σ') (shuffleLeftExtendRepresentative_isLeft σ') = σ' := by
  set hσ := shuffleLeftExtendRepresentative_isLeft σ'
  have h_inv_zero : (shuffleLeftExtendRepresentative σ')⁻¹ (Sum.inl 0) = Sum.inl 0 := by
    rw [← shuffleLeftExtendRepresentative_fixes σ']
    exact (shuffleLeftExtendRepresentative σ').symm_apply_apply _
  have hk_eq : hσ.choose = (0 : Fin (m + 1)) :=
    Sum.inl.inj (hσ.choose_spec.symm.trans h_inv_zero)
  change restrictComplement
    (normalizeLeft (shuffleLeftExtendRepresentative σ') hσ.choose) = σ'
  have : normalizeLeft (shuffleLeftExtendRepresentative σ') hσ.choose =
      shuffleLeftExtendRepresentative σ' := by
    unfold normalizeLeft; rw [hk_eq]; ext (a | b) <;> simp
  simp only [this]
  exact restrictComplement_shuffleLeftExtendRepresentative σ'

theorem shuffleLeftExtendRepresentative_restrictRepresentative_rel
    (σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (hσ : ∃ k, σ⁻¹ (Sum.inl 0) = Sum.inl k) :
    QuotientGroup.leftRel
        (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin (n + 1))).range
        (shuffleLeftExtendRepresentative (shuffleLeftRestrictRepresentative σ hσ)) σ := by
  set k := hσ.choose
  set hk := hσ.choose_spec
  rw [show shuffleLeftRestrictRepresentative σ hσ =
    restrictComplement (normalizeLeft σ k) from rfl]
  rw [shuffleLeftExtendRepresentative_restrictComplement _ (normalizeLeft_fixes σ k hk)]
  rw [QuotientGroup.leftRel_apply]
  refine ⟨⟨(Equiv.swap 0 k)⁻¹, 1⟩, ?_⟩
  simp [normalizeLeft, Equiv.Perm.sumCongrHom_apply]

noncomputable def shuffleLeftRestrict :
    {σ : Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin (n + 1)) //
      ∀ τ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)),
        Quotient.mk'' τ = σ → ∃ k, τ⁻¹ (Sum.inl 0) = Sum.inl k} ≃
    Equiv.Perm.ModSumCongr (Fin m) (Fin (n + 1)) where
  toFun := fun ⟨q, hq⟩ =>
    Quotient.mk'' (shuffleLeftRestrictRepresentative q.out (hq _ (Quotient.out_eq q)))
  invFun := fun q =>
    ⟨Quotient.mk'' (shuffleLeftExtendRepresentative q.out), fun τ hτ => by
      have h_rel := QuotientGroup.leftRel_apply.mp (Quotient.exact' hτ)
      have h_inv : (shuffleLeftExtendRepresentative q.out)⁻¹ * τ ∈
          (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin (n + 1))).range := by
        rw [show (shuffleLeftExtendRepresentative q.out)⁻¹ * τ = (τ⁻¹ * shuffleLeftExtendRepresentative q.out)⁻¹
          from by group]
        exact Subgroup.inv_mem _ h_rel
      rw [show τ = shuffleLeftExtendRepresentative q.out * ((shuffleLeftExtendRepresentative q.out)⁻¹ * τ)
        from by group]
      exact (shuffle_side_well_defined
        (σ := shuffleLeftExtendRepresentative q.out) ⟨_, h_inv⟩).mp
        (shuffleLeftExtendRepresentative_isLeft q.out)⟩
  left_inv := fun ⟨q, hq⟩ => by
    ext
    have h1 : (Quotient.mk'' (shuffleLeftRestrictRepresentative q.out
        (hq _ (Quotient.out_eq q))) :
        Equiv.Perm.ModSumCongr (Fin m) (Fin (n + 1))) =
      Quotient.mk'' (Quotient.mk'' (shuffleLeftRestrictRepresentative q.out
        (hq _ (Quotient.out_eq q)))).out :=
      (Quotient.out_eq _).symm
    calc Quotient.mk'' (shuffleLeftExtendRepresentative (Quotient.mk''
            (shuffleLeftRestrictRepresentative q.out (hq _ (Quotient.out_eq q)))).out)
        = Quotient.mk'' (shuffleLeftExtendRepresentative
            (shuffleLeftRestrictRepresentative q.out (hq _ (Quotient.out_eq q)))) :=
          Quotient.sound' (shuffleLeftExtendRepresentative_respects_leftRel _ _
            (Quotient.exact' h1.symm))
      _ = Quotient.mk'' q.out :=
          Quotient.sound' (shuffleLeftExtendRepresentative_restrictRepresentative_rel q.out _)
      _ = q := Quotient.out_eq q
  right_inv := fun q => by
    have h1 : (Quotient.mk'' (shuffleLeftExtendRepresentative q.out) :
        Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin (n + 1))) =
      Quotient.mk'' (Quotient.mk'' (shuffleLeftExtendRepresentative q.out)).out :=
      (Quotient.out_eq _).symm
    calc Quotient.mk'' (shuffleLeftRestrictRepresentative
            (Quotient.mk'' (shuffleLeftExtendRepresentative q.out)).out _)
        = Quotient.mk'' (shuffleLeftRestrictRepresentative (shuffleLeftExtendRepresentative q.out)
            (shuffleLeftExtendRepresentative_isLeft q.out)) :=
          Quotient.sound' (shuffleLeftRestrictRepresentative_respects_leftRel _ _ _ _
            (Quotient.exact' h1.symm))
      _ = Quotient.mk'' q.out := by rw [shuffleLeftRestrictRepresentative_extendRepresentative]
      _ = q := Quotient.out_eq q

theorem shuffleLeftRestrict_subtype_of_inv
    (σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (hσ : ∃ k, σ⁻¹ (Sum.inl 0) = Sum.inl k)
    (τ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (hτ : (Quotient.mk'' τ : Equiv.Perm.ModSumCongr _ _) = Quotient.mk'' σ) :
    ∃ k, τ⁻¹ (Sum.inl 0) = Sum.inl k := by
  have h_rel := QuotientGroup.leftRel_apply.mp (Quotient.exact' hτ)
  rcases h_rel with ⟨⟨tl, tr⟩, htl_tr⟩
  have h_eq : σ = τ * (Equiv.Perm.sumCongrHom _ _ (tl, tr)) := by
    rw [htl_tr]; group
  rw [h_eq] at hσ
  exact (shuffle_side_well_defined (σ := τ) ⟨_, ⟨(tl, tr), rfl⟩⟩).mpr hσ

@[simp] theorem finSuccSumOptionEquiv_symm_some
    (z : Fin m ⊕ Fin (n + 1)) :
    (finSuccSumOptionEquiv : Fin (m + 1) ⊕ Fin (n + 1) ≃ _).symm (some z) =
      Sum.map Fin.succ id z := by
  rcases z with a | b
  · simp [finSuccSumOptionEquiv, ShuffleSplit.optionSumEquiv]
  · simp [finSuccSumOptionEquiv, ShuffleSplit.optionSumEquiv]

theorem restrictComplement_lift
    (ν : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (hν : ν (Sum.inl 0) = Sum.inl 0)
    (y : Fin m ⊕ Fin (n + 1)) :
    Sum.map Fin.succ id (restrictComplement ν y) =
      ν (Sum.map Fin.succ id y) := by
  unfold restrictComplement
  set σ := Equiv.permCongr finSuccSumOptionEquiv ν with hσ_def
  have h_fix : σ none = none := by
    change finSuccSumOptionEquiv (ν (finSuccSumOptionEquiv.symm none)) = none
    rw [finSuccSumOptionEquiv_symm_none, hν, finSuccSumOptionEquiv_inl_zero]
  have h_some_y : ∃ x, σ (some y) = some x := by
    rcases h : σ (some y) with _ | x
    · exact absurd (σ.injective (h.trans h_fix.symm)) (Option.some_ne_none _)
    · exact ⟨x, rfl⟩
  have h_some : some ((Equiv.removeNone σ) y) = σ (some y) :=
    Equiv.removeNone_some _ h_some_y
  have h_unfold : σ (some y) =
      finSuccSumOptionEquiv (ν (finSuccSumOptionEquiv.symm (some y))) := rfl
  rw [h_unfold, finSuccSumOptionEquiv_symm_some] at h_some
  have h_inv := congr_arg finSuccSumOptionEquiv.symm h_some
  rw [Equiv.symm_apply_apply, finSuccSumOptionEquiv_symm_some] at h_inv
  exact h_inv

noncomputable def finSumSuccOptionEquiv {m n : ℕ} :
    Fin (m + 1) ⊕ Fin (n + 1) ≃ Option (Fin (m + 1) ⊕ Fin n) :=
  (Equiv.sumComm _ _).trans <|
    (finSuccSumOptionEquiv (m := n) (n := m)).trans <|
      Equiv.optionCongr (Equiv.sumComm _ _)

@[simp] theorem finSumSuccOptionEquiv_inr_zero {m n : ℕ} :
    (finSumSuccOptionEquiv : Fin (m + 1) ⊕ Fin (n + 1) ≃ _)
      (Sum.inr (0 : Fin (n + 1))) = none := by
  simp [finSumSuccOptionEquiv, Equiv.sumComm]

@[simp] theorem finSumSuccOptionEquiv_symm_none {m n : ℕ} :
    (finSumSuccOptionEquiv : Fin (m + 1) ⊕ Fin (n + 1) ≃ _).symm none =
      Sum.inr 0 := by
  apply (finSumSuccOptionEquiv (m := m) (n := n)).injective; simp

@[simp] theorem finSumSuccOptionEquiv_inl {m n : ℕ} (a : Fin (m + 1)) :
    (finSumSuccOptionEquiv : Fin (m + 1) ⊕ Fin (n + 1) ≃ _) (Sum.inl a) =
      some (Sum.inl a) := by
  simp [finSumSuccOptionEquiv, Equiv.sumComm, finSuccSumOptionEquiv,
    ShuffleSplit.optionSumEquiv]

@[simp] theorem finSumSuccOptionEquiv_inr_succ {m n : ℕ}
    (b : Fin n) :
    (finSumSuccOptionEquiv : Fin (m + 1) ⊕ Fin (n + 1) ≃ _)
      (Sum.inr b.succ) = some (Sum.inr b) := by
  have h : (finSuccEquiv' (0 : Fin (n + 1))) b.succ = some b :=
    finSuccEquiv'_above (Fin.zero_le _)
  simp [finSumSuccOptionEquiv, Equiv.sumComm, finSuccSumOptionEquiv,
    ShuffleSplit.optionSumEquiv, h]

@[simp] theorem finSumSuccOptionEquiv_symm_some_inl {m n : ℕ}
    (a : Fin (m + 1)) :
    (finSumSuccOptionEquiv : Fin (m + 1) ⊕ Fin (n + 1) ≃ _).symm
      (some (Sum.inl a)) = Sum.inl a := by
  apply (finSumSuccOptionEquiv (m := m) (n := n)).injective
  rw [Equiv.apply_symm_apply]; exact (finSumSuccOptionEquiv_inl a).symm

@[simp] theorem finSumSuccOptionEquiv_symm_some_inr {m n : ℕ}
    (b : Fin n) :
    (finSumSuccOptionEquiv : Fin (m + 1) ⊕ Fin (n + 1) ≃ _).symm
      (some (Sum.inr b)) = Sum.inr b.succ := by
  apply (finSumSuccOptionEquiv (m := m) (n := n)).injective
  rw [Equiv.apply_symm_apply]; exact (finSumSuccOptionEquiv_inr_succ b).symm

def normalizeRight (σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (k : Fin (n + 1)) :
    Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)) :=
  Equiv.swap (Sum.inl 0) (Sum.inr 0) *
    σ * Equiv.Perm.sumCongr 1 (Equiv.swap 0 k)

theorem normalizeRight_fixes (σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (k : Fin (n + 1)) (hk : σ⁻¹ (Sum.inl 0) = Sum.inr k) :
    normalizeRight σ k (Sum.inr 0) = Sum.inr 0 := by
  simp only [normalizeRight, Equiv.Perm.coe_mul, Function.comp_apply,
    Equiv.sumCongr_apply, Sum.map_inr, Equiv.swap_apply_left]
  rw [← hk]; simp

noncomputable def restrictComplementRight
    (σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1))) :
    Equiv.Perm (Fin (m + 1) ⊕ Fin n) :=
  Equiv.removeNone (Equiv.permCongr finSumSuccOptionEquiv σ)

theorem restrictComplementRight_sign
    (σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (hfix : σ (Sum.inr 0) = Sum.inr 0) :
    Equiv.Perm.sign (restrictComplementRight σ) = Equiv.Perm.sign σ := by
  unfold restrictComplementRight
  rw [ShuffleSplit.removeNone_sign, Equiv.Perm.sign_permCongr]
  change finSumSuccOptionEquiv (σ (finSumSuccOptionEquiv.symm none)) = none
  rw [finSumSuccOptionEquiv_symm_none, hfix, finSumSuccOptionEquiv_inr_zero]

theorem restrictComplementRight_lift
    (ν : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (hν : ν (Sum.inr 0) = Sum.inr 0)
    (y : Fin (m + 1) ⊕ Fin n) :
    Sum.map id Fin.succ (restrictComplementRight ν y) =
      ν (Sum.map id Fin.succ y) := by
  unfold restrictComplementRight
  set σ := Equiv.permCongr finSumSuccOptionEquiv ν with hσ_def
  have h_fix : σ none = none := by
    change finSumSuccOptionEquiv (ν (finSumSuccOptionEquiv.symm none)) = none
    rw [finSumSuccOptionEquiv_symm_none, hν, finSumSuccOptionEquiv_inr_zero]
  have h_some_y : ∃ x, σ (some y) = some x := by
    rcases h : σ (some y) with _ | x
    · exact absurd (σ.injective (h.trans h_fix.symm)) (Option.some_ne_none _)
    · exact ⟨x, rfl⟩
  have h_some : some ((Equiv.removeNone σ) y) = σ (some y) :=
    Equiv.removeNone_some _ h_some_y
  have h_lift : (finSumSuccOptionEquiv : Fin (m + 1) ⊕ Fin (n + 1) ≃ _).symm (some y) =
      Sum.map id Fin.succ y := by
    rcases y with a | b
    · exact finSumSuccOptionEquiv_symm_some_inl a
    · exact finSumSuccOptionEquiv_symm_some_inr b
  have h_unfold : σ (some y) =
      finSumSuccOptionEquiv (ν (finSumSuccOptionEquiv.symm (some y))) := rfl
  rw [h_lift] at h_unfold
  rw [h_unfold] at h_some
  have h_inv := congr_arg finSumSuccOptionEquiv.symm h_some
  rw [Equiv.symm_apply_apply] at h_inv
  have h_lift_rn : (finSumSuccOptionEquiv : Fin (m + 1) ⊕ Fin (n + 1) ≃ _).symm
      (some (Equiv.removeNone σ y)) = Sum.map id Fin.succ (Equiv.removeNone σ y) := by
    rcases h : (Equiv.removeNone σ y) with a | b
    · exact finSumSuccOptionEquiv_symm_some_inl a
    · exact finSumSuccOptionEquiv_symm_some_inr b
  rw [h_lift_rn] at h_inv
  exact h_inv

noncomputable def shuffleRightRestrictRepresentative
    (σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (hσ : ∃ k, σ⁻¹ (Sum.inl 0) = Sum.inr k) :
    Equiv.Perm (Fin (m + 1) ⊕ Fin n) :=
  let k := hσ.choose
  restrictComplementRight (normalizeRight σ k)

noncomputable def shuffleRightExtendRepresentative
    (σ' : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) :
    Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)) :=
  Equiv.swap (Sum.inl 0) (Sum.inr 0) *
    Equiv.permCongr finSumSuccOptionEquiv.symm σ'.optionCongr

theorem shuffleRightExtendRepresentative_isRight (σ' : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) :
    ∃ k, (shuffleRightExtendRepresentative σ')⁻¹ (Sum.inl 0) = Sum.inr k := by
  refine ⟨0, ?_⟩
  unfold shuffleRightExtendRepresentative
  rw [mul_inv_rev]
  change (Equiv.permCongr finSumSuccOptionEquiv.symm σ'.optionCongr)⁻¹
      ((Equiv.swap (Sum.inl 0) (Sum.inr 0))⁻¹ (Sum.inl 0)) = Sum.inr 0
  rw [Equiv.swap_inv, Equiv.swap_apply_left]
  change (Equiv.permCongr finSumSuccOptionEquiv.symm σ'.optionCongr).symm
    (Sum.inr 0) = Sum.inr 0
  change finSumSuccOptionEquiv.symm (σ'.optionCongr.symm
    (finSumSuccOptionEquiv (Sum.inr 0))) = Sum.inr 0
  rw [finSumSuccOptionEquiv_inr_zero]
  rw [show σ'.optionCongr.symm none = (none : Option (Fin (m + 1) ⊕ Fin n)) from by
    rw [← Equiv.optionCongr_symm]; rfl]
  exact finSumSuccOptionEquiv_symm_none

theorem restrictComplementRight_sumCongr_mem
    (τ_l : Equiv.Perm (Fin (m + 1))) (τ_r : Equiv.Perm (Fin (n + 1)))
    (hτ_fix : τ_r 0 = 0) :
    restrictComplementRight (Equiv.Perm.sumCongr τ_l τ_r) ∈
      (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin n)).range := by
  apply Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl
  intro x ⟨a, ha⟩; subst ha
  set σ_opt := Equiv.permCongr finSumSuccOptionEquiv
    (Equiv.Perm.sumCongr τ_l τ_r)
  have h_fix : σ_opt none = none := by
    simp [σ_opt, Equiv.permCongr_apply, hτ_fix]
  have h_oc := ShuffleSplit.optionCongr_removeNone_of_fix_none σ_opt h_fix
  suffices h : ∃ a', σ_opt (some (Sum.inl a)) = some (Sum.inl a') by
    obtain ⟨a', ha'⟩ := h
    have h_eq := congr_fun (congr_arg DFunLike.coe h_oc) (some (Sum.inl a))
    simp only [Equiv.optionCongr_apply, Option.map_some] at h_eq
    change restrictComplementRight _ (Sum.inl a) ∈ _
    unfold restrictComplementRight
    rw [show Equiv.removeNone (Equiv.permCongr finSumSuccOptionEquiv
      (Equiv.Perm.sumCongr τ_l τ_r)) = Equiv.removeNone σ_opt from rfl]
    rw [ha'] at h_eq
    exact ⟨a', ((Option.some_injective _) h_eq.symm)⟩
  refine ⟨τ_l a, ?_⟩
  have h_fwd : (finSumSuccOptionEquiv : Fin (m + 1) ⊕ Fin (n + 1) ≃ _)
      (Sum.inl a) = some (Sum.inl a) := by
    simp [finSumSuccOptionEquiv, Equiv.sumComm, finSuccSumOptionEquiv,
      ShuffleSplit.optionSumEquiv, Equiv.optionCongr_apply]
  have h_bwd : (finSumSuccOptionEquiv : Fin (m + 1) ⊕ Fin (n + 1) ≃ _).symm
      (some (Sum.inl a)) = Sum.inl a :=
    (finSumSuccOptionEquiv).injective (by rw [h_fwd]; exact (h_fwd).symm.symm)
  have h_fwd_τ : (finSumSuccOptionEquiv : Fin (m + 1) ⊕ Fin (n + 1) ≃ _)
      (Sum.inl (τ_l a)) = some (Sum.inl (τ_l a)) := by
    simp [finSumSuccOptionEquiv, Equiv.sumComm, finSuccSumOptionEquiv,
      ShuffleSplit.optionSumEquiv, Equiv.optionCongr_apply]
  change (Equiv.permCongr finSumSuccOptionEquiv (Equiv.Perm.sumCongr τ_l τ_r))
    (some (Sum.inl a)) = some (Sum.inl (τ_l a))
  rw [Equiv.permCongr_apply, h_bwd]
  simp only [Equiv.sumCongr_apply, Sum.map_inl]
  exact h_fwd_τ

theorem shuffleRightRestrictRepresentative_respects_leftRel
    (σ₁ σ₂ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (hσ₁ : ∃ k, σ₁⁻¹ (Sum.inl 0) = Sum.inr k)
    (hσ₂ : ∃ k, σ₂⁻¹ (Sum.inl 0) = Sum.inr k)
    (h_rel : QuotientGroup.leftRel
        (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin (n + 1))).range σ₁ σ₂) :
    QuotientGroup.leftRel
        (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin n)).range
        (shuffleRightRestrictRepresentative σ₁ hσ₁) (shuffleRightRestrictRepresentative σ₂ hσ₂) := by
  set k₁ := hσ₁.choose; set hk₁ := hσ₁.choose_spec
  set k₂ := hσ₂.choose; set hk₂ := hσ₂.choose_spec
  set n1 := normalizeRight σ₁ k₁
  set n2 := normalizeRight σ₂ k₂
  have hn1 := normalizeRight_fixes σ₁ k₁ hk₁
  have hn2 := normalizeRight_fixes σ₂ k₂ hk₂
  have h_n_rel : QuotientGroup.leftRel
      (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin (n + 1))).range n1 n2 := by
    rw [QuotientGroup.leftRel_apply]
    rw [QuotientGroup.leftRel_apply] at h_rel
    obtain ⟨⟨τ_l, τ_r⟩, hτ⟩ := h_rel
    refine ⟨⟨τ_l, (Equiv.swap 0 k₁)⁻¹ * τ_r * Equiv.swap 0 k₂⟩, ?_⟩
    simp only [Equiv.Perm.sumCongrHom_apply]
    change Equiv.Perm.sumCongr τ_l
      ((Equiv.swap 0 k₁)⁻¹ * τ_r * Equiv.swap 0 k₂) = n1⁻¹ * n2
    have hτ_eq : Equiv.Perm.sumCongr τ_l τ_r = σ₁⁻¹ * σ₂ := by
      change (Equiv.Perm.sumCongrHom _ _ (τ_l, τ_r) : Equiv.Perm _) = _; exact hτ
    symm
    calc n1⁻¹ * n2
        = (Equiv.swap (Sum.inl (0 : Fin (m + 1)))
              (Sum.inr (0 : Fin (n + 1))) *
            σ₁ * Equiv.Perm.sumCongr 1 (Equiv.swap 0 k₁))⁻¹ *
          (Equiv.swap (Sum.inl 0) (Sum.inr 0) *
            σ₂ * Equiv.Perm.sumCongr 1 (Equiv.swap 0 k₂)) := by
          simp [n1, n2, normalizeRight]
      _ = (Equiv.Perm.sumCongr 1 (Equiv.swap 0 k₁))⁻¹ * σ₁⁻¹ *
            (σ₂ * Equiv.Perm.sumCongr 1 (Equiv.swap 0 k₂)) := by
          group
      _ = Equiv.Perm.sumCongr 1 (Equiv.swap 0 k₁)⁻¹ *
            Equiv.Perm.sumCongr τ_l τ_r *
            Equiv.Perm.sumCongr 1 (Equiv.swap 0 k₂) := by
          rw [Equiv.Perm.sumCongr_inv, inv_one, hτ_eq]; group
      _ = Equiv.Perm.sumCongr τ_l ((Equiv.swap 0 k₁)⁻¹ * τ_r * Equiv.swap 0 k₂) := by
          rw [Equiv.Perm.sumCongr_mul, Equiv.Perm.sumCongr_mul]; simp
  rw [QuotientGroup.leftRel_apply] at h_n_rel ⊢
  obtain ⟨⟨τ_l, τ_r⟩, hτ⟩ := h_n_rel
  have hτ_eq : (Equiv.Perm.sumCongr τ_l τ_r : Equiv.Perm _) = n1⁻¹ * n2 := by
    change (Equiv.Perm.sumCongrHom _ _ (τ_l, τ_r) : Equiv.Perm _) = _; exact hτ
  have hn12 : (n1⁻¹ * n2) (Sum.inr 0) = Sum.inr 0 := by
    change n1.symm (n2 (Sum.inr 0)) = _
    rw [hn2]; exact n1.symm_apply_eq.mpr hn1.symm
  have hτ_fix : τ_r 0 = 0 := by
    have : Equiv.Perm.sumCongr τ_l τ_r (Sum.inr 0) = Sum.inr 0 := hτ_eq ▸ hn12
    simpa using this
  have h_n1_none : Equiv.permCongr finSumSuccOptionEquiv n1 none = none := by
    change finSumSuccOptionEquiv (n1 (finSumSuccOptionEquiv.symm none)) = none
    rw [finSumSuccOptionEquiv_symm_none, hn1, finSumSuccOptionEquiv_inr_zero]
  have h_n2_none : Equiv.permCongr finSumSuccOptionEquiv n2 none = none := by
    change finSumSuccOptionEquiv (n2 (finSumSuccOptionEquiv.symm none)) = none
    rw [finSumSuccOptionEquiv_symm_none, hn2, finSumSuccOptionEquiv_inr_zero]
  have h_rc_mul : (restrictComplementRight n1)⁻¹ *
      restrictComplementRight n2 =
      restrictComplementRight (n1⁻¹ * n2) := by
    unfold restrictComplementRight
    rw [ShuffleSplit.permCongr_inv_mul (finSumSuccOptionEquiv) n1 n2,
      ShuffleSplit.removeNone_inv_mul _ _ h_n1_none h_n2_none]
  change (restrictComplementRight n1)⁻¹ *
    restrictComplementRight n2 ∈ _
  rw [h_rc_mul]
  have : restrictComplementRight (n1⁻¹ * n2) =
      restrictComplementRight (Equiv.Perm.sumCongr τ_l τ_r) := by
    congr 1; exact hτ_eq.symm
  rw [this]
  exact restrictComplementRight_sumCongr_mem τ_l τ_r hτ_fix

noncomputable def liftPermSuccR (τ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + 1)) :=
  Equiv.permCongr (finSuccEquiv' 0).symm τ.optionCongr

theorem shuffleRightExtendRepresentative_respects_leftRel
    (σ₁' σ₂' : Equiv.Perm (Fin (m + 1) ⊕ Fin n))
    (h_rel : QuotientGroup.leftRel
        (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin n)).range σ₁' σ₂') :
    QuotientGroup.leftRel
        (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin (n + 1))).range
        (shuffleRightExtendRepresentative σ₁') (shuffleRightExtendRepresentative σ₂') := by
  rw [QuotientGroup.leftRel_apply] at h_rel ⊢
  obtain ⟨⟨tl, tr⟩, htau⟩ := h_rel
  have h_swap_cancel : (shuffleRightExtendRepresentative σ₁')⁻¹ * shuffleRightExtendRepresentative σ₂' =
      (Equiv.permCongr finSumSuccOptionEquiv.symm σ₁'.optionCongr)⁻¹ *
      (Equiv.permCongr finSumSuccOptionEquiv.symm σ₂'.optionCongr) := by
    unfold shuffleRightExtendRepresentative
    group
  rw [h_swap_cancel]
  suffices h_mem : (Equiv.permCongr finSumSuccOptionEquiv.symm
      (Equiv.Perm.sumCongr tl tr).optionCongr) ∈
      (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin (n + 1))).range by
    convert h_mem using 1
    have h_sc : (Equiv.Perm.sumCongrHom _ _ (tl, tr) : Equiv.Perm _) = σ₁'⁻¹ * σ₂' := htau
    rw [show Equiv.Perm.sumCongr tl tr = σ₁'⁻¹ * σ₂' from h_sc]
    ext x
    apply finSumSuccOptionEquiv.injective
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.permCongr_apply,
      Equiv.apply_symm_apply, Equiv.optionCongr_apply]
    change finSumSuccOptionEquiv
      ((Equiv.permCongr finSumSuccOptionEquiv.symm σ₁'.optionCongr)⁻¹
        (finSumSuccOptionEquiv.symm (Option.map σ₂' (finSumSuccOptionEquiv x)))) =
      Option.map (fun x => σ₁'⁻¹ (σ₂' x)) (finSumSuccOptionEquiv x)
    have h_inv_apply : forall z,
        ((Equiv.permCongr finSumSuccOptionEquiv.symm
          σ₁'.optionCongr) : Equiv.Perm _)⁻¹ z =
        (Equiv.permCongr finSumSuccOptionEquiv.symm
          σ₁'⁻¹.optionCongr) z := by
      intro z
      have : ((Equiv.permCongr finSumSuccOptionEquiv.symm
          σ₁'.optionCongr) : Equiv.Perm _)⁻¹ =
        Equiv.permCongr finSumSuccOptionEquiv.symm σ₁'⁻¹.optionCongr := by
        ext w
        simp only [Equiv.Perm.inv_def, Equiv.permCongr_apply]
        rw [Equiv.optionCongr_symm]; rfl
      rw [this]
    rw [h_inv_apply]
    simp only [Equiv.permCongr_apply, Equiv.apply_symm_apply,
      Equiv.optionCongr_apply, Equiv.symm_symm,
      Option.map_map, Function.comp_def]
  refine ⟨(tl, liftPermSuccR tr), ?_⟩
  simp only [Equiv.Perm.sumCongrHom_apply]
  ext x
  rw [Equiv.permCongr_apply]
  cases x with
  | inl a =>
    simp only [Equiv.sumCongr_apply, Sum.map_inl, Equiv.symm_symm,
      finSumSuccOptionEquiv_inl, Equiv.optionCongr_apply, Option.map_some,
      finSumSuccOptionEquiv_symm_some_inl]
  | inr b =>
    rcases h : (finSuccEquiv' (0 : Fin (n + 1))) b with _ | b'
    · have hb : b = 0 := (finSuccEquiv' (0 : Fin (n + 1))).injective
        (h.trans (finSuccEquiv'_at 0).symm)
      subst hb
      simp only [Equiv.sumCongr_apply, Sum.map_inr, Equiv.symm_symm,
        finSumSuccOptionEquiv_inr_zero, Equiv.optionCongr_apply, Option.map_none,
        finSumSuccOptionEquiv_symm_none, liftPermSuccR,
        Equiv.permCongr_apply]
      simp
    · have hb : b = b'.succ := by
        have h1 : (finSuccEquiv' (0 : Fin (n + 1))) b'.succ = some b' :=
          finSuccEquiv'_above (Fin.zero_le _)
        exact (finSuccEquiv' (0 : Fin (n + 1))).injective (h.trans h1.symm)
      subst hb
      simp only [Equiv.sumCongr_apply, Sum.map_inr, Equiv.symm_symm,
        finSumSuccOptionEquiv_inr_succ, Equiv.optionCongr_apply, Option.map_some,
        finSumSuccOptionEquiv_symm_some_inr, liftPermSuccR,
        Equiv.permCongr_apply]
      have h1 : (finSuccEquiv' (0 : Fin (n + 1))) b'.succ = some b' :=
        finSuccEquiv'_above (Fin.zero_le _)
      rw [h1]
      simp

theorem restrictComplementRight_shuffleRightExtendRepresentative
    (σ' : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) :
    restrictComplementRight
      (Equiv.permCongr finSumSuccOptionEquiv.symm σ'.optionCongr) = σ' := by
  simp only [restrictComplementRight]
  have : Equiv.permCongr finSumSuccOptionEquiv
      (Equiv.permCongr finSumSuccOptionEquiv.symm σ'.optionCongr) =
      σ'.optionCongr := by ext x; simp [Equiv.permCongr_apply]
  rw [this]; exact Equiv.removeNone_optionCongr σ'

theorem shuffleRightRestrictRepresentative_extendRepresentative
    (σ' : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) :
    shuffleRightRestrictRepresentative (shuffleRightExtendRepresentative σ') (shuffleRightExtendRepresentative_isRight σ') = σ' := by
  set hσ := shuffleRightExtendRepresentative_isRight σ'
  have h_inv_zero : (shuffleRightExtendRepresentative σ')⁻¹ (Sum.inl 0) = Sum.inr 0 := by
    unfold shuffleRightExtendRepresentative
    rw [mul_inv_rev]
    change (Equiv.permCongr finSumSuccOptionEquiv.symm σ'.optionCongr)⁻¹
        ((Equiv.swap (Sum.inl 0) (Sum.inr 0))⁻¹ (Sum.inl 0)) = Sum.inr 0
    rw [Equiv.swap_inv, Equiv.swap_apply_left]
    change (Equiv.permCongr finSumSuccOptionEquiv.symm σ'.optionCongr).symm
      (Sum.inr 0) = Sum.inr 0
    change finSumSuccOptionEquiv.symm (σ'.optionCongr.symm
      (finSumSuccOptionEquiv (Sum.inr 0))) = Sum.inr 0
    rw [finSumSuccOptionEquiv_inr_zero]
    rw [show σ'.optionCongr.symm none = (none : Option (Fin (m + 1) ⊕ Fin n)) from by
      rw [← Equiv.optionCongr_symm]; rfl]
    exact finSumSuccOptionEquiv_symm_none
  have hk_eq : hσ.choose = (0 : Fin (n + 1)) :=
    Sum.inr.inj (hσ.choose_spec.symm.trans h_inv_zero)
  change restrictComplementRight
    (normalizeRight (shuffleRightExtendRepresentative σ') hσ.choose) = σ'
  have h_norm : normalizeRight (shuffleRightExtendRepresentative σ') hσ.choose =
      Equiv.permCongr finSumSuccOptionEquiv.symm σ'.optionCongr := by
    unfold normalizeRight
    rw [hk_eq]
    unfold shuffleRightExtendRepresentative
    have h_swap_zero : Equiv.swap (0 : Fin (n + 1)) 0 = 1 := Equiv.swap_self 0
    rw [h_swap_zero]
    simp only [Equiv.Perm.sumCongr_one, mul_one]
    rw [← mul_assoc,
      show Equiv.swap (Sum.inl (0 : Fin (m + 1))) (Sum.inr (0 : Fin (n + 1))) *
        Equiv.swap (Sum.inl 0) (Sum.inr 0) = 1 from Equiv.swap_mul_self _ _,
      one_mul]
  simp only [h_norm]
  exact restrictComplementRight_shuffleRightExtendRepresentative σ'

theorem shuffleRightExtendRepresentative_restrictComplementRight
    (σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (hfix : σ (Sum.inr 0) = Sum.inr 0) :
    shuffleRightExtendRepresentative (restrictComplementRight σ) =
      Equiv.swap (Sum.inl 0) (Sum.inr 0) * σ := by
  unfold shuffleRightExtendRepresentative restrictComplementRight
  have h_fixes_none :
      (Equiv.permCongr finSumSuccOptionEquiv σ) none = none := by
    simp [Equiv.permCongr_apply, hfix]
  have h_round : (Equiv.removeNone
      (Equiv.permCongr finSumSuccOptionEquiv σ)).optionCongr =
      Equiv.permCongr finSumSuccOptionEquiv σ := by
    rw [map_equiv_removeNone, h_fixes_none]
    rw [Equiv.swap_self, ← Equiv.Perm.one_def, one_mul]
  rw [h_round]
  have h_cancel : Equiv.permCongr finSumSuccOptionEquiv.symm
      (Equiv.permCongr finSumSuccOptionEquiv σ) = σ := by
    ext x; simp [Equiv.permCongr_apply]
  rw [h_cancel]

theorem shuffleRightExtendRepresentative_restrictRepresentative_rel
    (σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (hσ : ∃ k, σ⁻¹ (Sum.inl 0) = Sum.inr k) :
    QuotientGroup.leftRel
        (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin (n + 1))).range
        (shuffleRightExtendRepresentative (shuffleRightRestrictRepresentative σ hσ)) σ := by
  set k := hσ.choose
  set hk := hσ.choose_spec
  rw [show shuffleRightRestrictRepresentative σ hσ =
    restrictComplementRight (normalizeRight σ k) from rfl]
  rw [shuffleRightExtendRepresentative_restrictComplementRight _ (normalizeRight_fixes σ k hk)]
  rw [QuotientGroup.leftRel_apply]
  refine ⟨⟨1, (Equiv.swap 0 k)⁻¹⟩, ?_⟩
  simp only [Equiv.Perm.sumCongrHom_apply]
  unfold normalizeRight
  have h_swap_inv : (Equiv.swap (Sum.inl (0 : Fin (m + 1)))
      (Sum.inr (0 : Fin (n + 1))))⁻¹ =
      Equiv.swap (Sum.inl 0) (Sum.inr 0) := Equiv.swap_inv _ _
  simp only [mul_inv_rev, h_swap_inv, Equiv.Perm.sumCongr_inv, inv_one]
  conv_rhs => rw [show ∀ (A B : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1))),
    A * (σ⁻¹ * Equiv.swap (Sum.inl 0) (Sum.inr 0)) *
      Equiv.swap (Sum.inl 0) (Sum.inr 0) * B =
    A * σ⁻¹ *
      (Equiv.swap (Sum.inl 0) (Sum.inr 0) *
        Equiv.swap (Sum.inl 0) (Sum.inr 0)) * B from by intros; group]
  rw [show Equiv.swap (Sum.inl (0 : Fin (m + 1)))
      (Sum.inr (0 : Fin (n + 1))) *
      Equiv.swap (Sum.inl 0) (Sum.inr 0) = 1 from Equiv.swap_mul_self _ _]
  group

noncomputable def shuffleRightRestrict :
    {σ : Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin (n + 1)) //
      ∀ τ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)),
        Quotient.mk'' τ = σ → ∃ k, τ⁻¹ (Sum.inl 0) = Sum.inr k} ≃
    Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n) where
  toFun := fun ⟨q, hq⟩ =>
    Quotient.mk'' (shuffleRightRestrictRepresentative q.out (hq _ (Quotient.out_eq q)))
  invFun := fun q =>
    ⟨Quotient.mk'' (shuffleRightExtendRepresentative q.out), fun τ hτ => by
      have h_rel := QuotientGroup.leftRel_apply.mp (Quotient.exact' hτ)
      have h_inv : (shuffleRightExtendRepresentative q.out)⁻¹ * τ ∈
          (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin (n + 1))).range := by
        rw [show (shuffleRightExtendRepresentative q.out)⁻¹ * τ =
          (τ⁻¹ * shuffleRightExtendRepresentative q.out)⁻¹ from by group]
        exact Subgroup.inv_mem _ h_rel
      rw [show τ = shuffleRightExtendRepresentative q.out *
        ((shuffleRightExtendRepresentative q.out)⁻¹ * τ) from by group]
      exact (shuffle_side_well_defined_right
        (σ := shuffleRightExtendRepresentative q.out) ⟨_, h_inv⟩).mp
        (shuffleRightExtendRepresentative_isRight q.out)⟩
  left_inv := fun ⟨q, hq⟩ => by
    ext
    have h1 := (Quotient.out_eq (Quotient.mk'' (shuffleRightRestrictRepresentative q.out
        (hq _ (Quotient.out_eq q))) :
        Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n))).symm
    calc Quotient.mk'' (shuffleRightExtendRepresentative (Quotient.mk''
            (shuffleRightRestrictRepresentative q.out (hq _ (Quotient.out_eq q)))).out)
        = Quotient.mk'' (shuffleRightExtendRepresentative
            (shuffleRightRestrictRepresentative q.out (hq _ (Quotient.out_eq q)))) :=
          Quotient.sound' (shuffleRightExtendRepresentative_respects_leftRel _ _ (Quotient.exact' h1.symm))
      _ = Quotient.mk'' q.out :=
          Quotient.sound' (shuffleRightExtendRepresentative_restrictRepresentative_rel q.out _)
      _ = q := Quotient.out_eq q
  right_inv := fun q => by
    have h1 := (Quotient.out_eq (Quotient.mk'' (shuffleRightExtendRepresentative q.out) :
        Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin (n + 1)))).symm
    calc Quotient.mk'' (shuffleRightRestrictRepresentative
            (Quotient.mk'' (shuffleRightExtendRepresentative q.out)).out _)
        = Quotient.mk'' (shuffleRightRestrictRepresentative (shuffleRightExtendRepresentative q.out)
            (shuffleRightExtendRepresentative_isRight q.out)) :=
          Quotient.sound' (shuffleRightRestrictRepresentative_respects_leftRel _ _ _ _
            (Quotient.exact' h1.symm))
      _ = Quotient.mk'' q.out := by rw [shuffleRightRestrictRepresentative_extendRepresentative]
      _ = q := Quotient.out_eq q

theorem shuffleRightRestrict_subtype_of_inv
    (σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (hσ : ∃ k, σ⁻¹ (Sum.inl 0) = Sum.inr k)
    (τ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (hτ : (Quotient.mk'' τ : Equiv.Perm.ModSumCongr _ _) = Quotient.mk'' σ) :
    ∃ k, τ⁻¹ (Sum.inl 0) = Sum.inr k := by
  have h_rel := QuotientGroup.leftRel_apply.mp (Quotient.exact' hτ)
  rcases h_rel with ⟨⟨tl, tr⟩, htl_tr⟩
  have h_eq : σ = τ * (Equiv.Perm.sumCongrHom _ _ (tl, tr)) := by
    rw [htl_tr]; group
  rw [h_eq] at hσ
  exact (shuffle_side_well_defined_right (σ := τ) ⟨_, ⟨(tl, tr), rfl⟩⟩).mpr hσ

end ContinuousAlternatingMap
