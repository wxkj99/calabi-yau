-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Tensor/Alternating/Shuffle/Decomposition.lean
-- Locally modified.
/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module
public import CalabiYau.Mathlib.LinearAlgebra.Alternating.ShuffleSplit
public import Mathlib.GroupTheory.Perm.Finite
public import Mathlib.GroupTheory.Perm.Option
public import Mathlib.LinearAlgebra.Alternating.DomCoprod
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.Group

@[expose] public section

open CalabiYau

namespace ContinuousAlternatingMap

variable {m n : ℕ}

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

@[simp] theorem finSuccSumOptionEquiv_symm_some
    (z : Fin m ⊕ Fin (n + 1)) :
    (finSuccSumOptionEquiv : Fin (m + 1) ⊕ Fin (n + 1) ≃ _).symm (some z) =
      Sum.map Fin.succ id z := by
  rcases z with a | b
  · simp [finSuccSumOptionEquiv, ShuffleSplit.optionSumEquiv]
  · simp [finSuccSumOptionEquiv, ShuffleSplit.optionSumEquiv]

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

end ContinuousAlternatingMap
