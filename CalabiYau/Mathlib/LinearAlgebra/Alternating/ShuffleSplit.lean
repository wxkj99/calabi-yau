-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Tensor/Alternating/Shuffle/Split.lean
-- Locally modified.
/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module
public import Mathlib.GroupTheory.Perm.Option
public import Mathlib.LinearAlgebra.Alternating.DomCoprod

@[expose] public section

namespace CalabiYau.ShuffleSplit

attribute [local instance] Fintype.ofFinite Classical.propDecidable

variable {α₀ : Type*} {β : Type*}

def optionSumEquiv : Option α₀ ⊕ β ≃ Option (α₀ ⊕ β) where
  toFun := fun x => match x with
    | Sum.inl none => none
    | Sum.inl (some a) => some (Sum.inl a)
    | Sum.inr b => some (Sum.inr b)
  invFun := fun x => match x with
    | none => Sum.inl none
    | some (Sum.inl a) => Sum.inl (some a)
    | some (Sum.inr b) => Sum.inr b
  left_inv := by intro x; rcases x with ((_ | a) | b) <;> rfl
  right_inv := by intro x; rcases x with (_ | (a | b)) <;> rfl

@[simp] theorem optionSumEquiv_inl_none :
    optionSumEquiv (Sum.inl (none : Option α₀) : Option α₀ ⊕ β) = none := rfl

@[simp] theorem optionSumEquiv_inl_some (a : α₀) :
    optionSumEquiv (Sum.inl (some a) : Option α₀ ⊕ β) = some (Sum.inl a) := rfl

@[simp] theorem optionSumEquiv_inr (b : β) :
    optionSumEquiv (Sum.inr b : Option α₀ ⊕ β) = some (Sum.inr b) := rfl

@[simp] theorem optionSumEquiv_symm_none :
    optionSumEquiv.symm (none : Option (α₀ ⊕ β)) = Sum.inl none := rfl

@[simp] theorem optionSumEquiv_symm_some_inl (a : α₀) :
    optionSumEquiv.symm (some (Sum.inl a) : Option (α₀ ⊕ β)) =
      Sum.inl (some a) := rfl

@[simp] theorem optionSumEquiv_symm_some_inr (b : β) :
    optionSumEquiv.symm (some (Sum.inr b) : Option (α₀ ⊕ β)) = Sum.inr b := rfl

theorem permCongr_inv_mul {α β : Type*}
    (e : α ≃ β) (σ₁ σ₂ : Equiv.Perm α) :
    Equiv.permCongr e (σ₁⁻¹ * σ₂) =
      (Equiv.permCongr e σ₁)⁻¹ * Equiv.permCongr e σ₂ := by
  have h_inv : (Equiv.permCongr e σ₁ : Equiv.Perm _)⁻¹ =
      Equiv.permCongr e σ₁⁻¹ := by
    ext y
    change (Equiv.permCongr e σ₁).symm y = e (σ₁⁻¹ (e.symm y))
    simp [Equiv.permCongr_def, Equiv.Perm.inv_def]
  ext x
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.permCongr_apply,
    h_inv, Equiv.symm_apply_apply]

end CalabiYau.ShuffleSplit
