-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Tensor/Alternating/Reindexing/FiniteEquivalence.lean
-- Locally modified.
/-
Authors: Yury Kudryashov
Coauthors: Jack McCarthy
-/
module
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Order.Hom.PowersetCard
public import Mathlib.Order.WellFounded

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Fin

variable {m n o : ℕ}

def finAssoc {m n p : ℕ} : Fin (m + n + p) ≃ Fin (m + (n + p)) :=
  finCongr <| Nat.add_assoc m n p

def finAddFlipAssoc {m n p : ℕ} : Fin (m + p + n) ≃ Fin (m + (n + p)) := by
  refine finCongr ?eq
  rw [Nat.add_right_comm]
  exact Nat.add_assoc m n p

theorem finAddFlip_finSumFinEquiv {m n : ℕ} (a : Fin m ⊕ Fin n) :
    finAddFlip (finSumFinEquiv a) = finSumFinEquiv (Equiv.sumComm _ _ a)  := by
  refine Eq.symm (DFunLike.congr_arg finSumFinEquiv ?h₂)
  rw [Equiv.congr_arg rfl]
  refine (Equiv.apply_eq_iff_eq (Equiv.sumComm (Fin m) (Fin n))).mpr ?h₂.a
  rw [Equiv.symm_apply_apply]

def finAddCongr : Fin (m + n) ≃ Fin (n + m) := finCongr (add_comm m n)

@[simp]
lemma finAddCongr_finAddCongr (i : Fin (m + n)) :
    finAddCongr (finAddCongr i) = i :=
  rfl

@[simp]
lemma finAddCongr_symm_finAddCongr_symm (i : Fin (m + n)) :
    finAddCongr.symm (finAddCongr.symm i) = i :=
  rfl

def finSumCongr : Fin m ⊕ Fin n ≃ Fin n ⊕ Fin m where
  toFun x := x.swap
  invFun x := x.swap
  left_inv := Sum.swap_swap
  right_inv := Sum.swap_swap

@[simp]
lemma finSumCongr_symm_inl_inr (x : Fin m) :
    finSumCongr.symm (Sum.inl x) = (Sum.inr x : Fin n ⊕ Fin m)
  := rfl

@[simp]
lemma finSumCongr_symm_inr_inl (x : Fin n) :
    finSumCongr.symm (Sum.inr x) = (Sum.inl x : Fin n ⊕ Fin m)
  := rfl

private theorem addCases_succAbove_castAdd_assoc {α : Type*} {m' n' : ℕ}
    (f : Fin (m' + 1) → α) (g : Fin (n' + 1) → α) (i : Fin (m' + 1))
    (k : Fin (m' + (n' + 1))) :
    (Fin.addCases f g : Fin ((m' + 1) + (n' + 1)) → α)
      ((Fin.castAdd (n' + 1) i).succAbove
        (Fin.cast (show m' + (n' + 1) = m' + 1 + n' from by omega) k)) =
    (Fin.addCases (fun a => f (i.succAbove a)) g : Fin (m' + (n' + 1)) → α) k := by
  have hleft : forall a : Fin m',
      (Fin.addCases f g : Fin ((m' + 1) + (n' + 1)) → α)
        ((Fin.castAdd (n' + 1) i).succAbove
          (Fin.cast (show m' + (n' + 1) = m' + 1 + n' from by omega)
            (Fin.castAdd (n' + 1) a))) =
      (Fin.addCases (fun a => f (i.succAbove a)) g : Fin (m' + (n' + 1)) → α)
        (Fin.castAdd (n' + 1) a) := by
    intro a
    by_cases h : a.castSucc < i
    case pos =>
      have hlt : (Fin.cast (show m' + (n' + 1) = m' + 1 + n' from by omega)
          (Fin.castAdd (n' + 1) a)).castSucc < Fin.castAdd (n' + 1) i := by
        apply Fin.lt_def.mpr
        simpa [Fin.val_castAdd, Fin.val_cast, Fin.val_castSucc] using! h
      rw [Fin.succAbove_of_castSucc_lt _ _ hlt]
      rw [show (Fin.cast (show m' + (n' + 1) = m' + 1 + n' from by omega)
          (Fin.castAdd (n' + 1) a)).castSucc = Fin.castAdd (n' + 1) a.castSucc by
        ext
        simp]
      simp [Fin.addCases_left, Fin.succAbove_of_castSucc_lt _ _ h]
    case neg =>
      have hle : Fin.castAdd (n' + 1) i <=
          (Fin.cast (show m' + (n' + 1) = m' + 1 + n' from by omega)
            (Fin.castAdd (n' + 1) a)).castSucc := by
        apply Fin.le_def.mpr
        have ha : i.val <= a.val := Fin.le_def.mp (Fin.not_lt.mp h)
        simp [Fin.val_castAdd, Fin.val_cast, Fin.val_castSucc]
        omega
      rw [Fin.succAbove_of_le_castSucc _ _ hle]
      rw [show (Fin.cast (show m' + (n' + 1) = m' + 1 + n' from by omega)
          (Fin.castAdd (n' + 1) a)).succ = Fin.castAdd (n' + 1) a.succ by
        ext
        simp]
      simp [Fin.addCases_left, Fin.succAbove_of_le_castSucc _ _ (Fin.not_lt.mp h)]
  have hright : forall b : Fin (n' + 1),
      (Fin.addCases f g : Fin ((m' + 1) + (n' + 1)) → α)
        ((Fin.castAdd (n' + 1) i).succAbove
          (Fin.cast (show m' + (n' + 1) = m' + 1 + n' from by omega)
            (Fin.natAdd m' b))) =
      (Fin.addCases (fun a => f (i.succAbove a)) g : Fin (m' + (n' + 1)) → α)
        (Fin.natAdd m' b) := by
    intro b
    have hle : Fin.castAdd (n' + 1) i <=
        (Fin.cast (show m' + (n' + 1) = m' + 1 + n' from by omega)
          (Fin.natAdd m' b)).castSucc := by
      apply Fin.le_def.mpr
      simp [Fin.val_castAdd, Fin.val_cast, Fin.val_natAdd, Fin.val_castSucc]
      omega
    rw [Fin.succAbove_of_le_castSucc _ _ hle]
    rw [show (Fin.cast (show m' + (n' + 1) = m' + 1 + n' from by omega)
        (Fin.natAdd m' b)).succ = Fin.natAdd (m' + 1) b by
      ext
      simp [Fin.val_natAdd]
      omega]
    simp [Fin.addCases_right]
  exact Fin.addCases (motive := fun k =>
      (Fin.addCases f g : Fin ((m' + 1) + (n' + 1)) → α)
        ((Fin.castAdd (n' + 1) i).succAbove
          (Fin.cast (show m' + (n' + 1) = m' + 1 + n' from by omega) k)) =
      (Fin.addCases (fun a => f (i.succAbove a)) g : Fin (m' + (n' + 1)) → α) k)
    hleft hright k

theorem addCases_succAbove_castAdd {α : Type*} {m' n' : ℕ}
    (f : Fin (m' + 1) → α) (g : Fin (n' + 1) → α) (i : Fin (m' + 1))
    (k : Fin (m' + n' + 1)) :
    (Fin.addCases f g : Fin ((m' + 1) + (n' + 1)) → α)
      ((Fin.castAdd (n' + 1) i).succAbove
        (Fin.cast (show m' + n' + 1 = m' + 1 + n' from by omega) k)) =
    (Fin.addCases (f ∘ i.succAbove) g : Fin (m' + (n' + 1)) → α) k := by
  simpa using! addCases_succAbove_castAdd_assoc (m' := m') (n' := n') f g i k

theorem addCases_succAbove_natAdd {α : Type*} {m' n' : ℕ}
    (f : Fin (m' + 1) → α) (g : Fin (n' + 1) → α) (j : Fin (n' + 1))
    (k : Fin (m' + 1 + n')) :
    (Fin.addCases f g : Fin ((m' + 1) + (n' + 1)) → α)
      ((Fin.natAdd (m' + 1) j).succAbove k) =
    (Fin.addCases f (g ∘ j.succAbove) : Fin ((m' + 1) + n') → α) k := by
  have hleft : forall a : Fin (m' + 1),
      (Fin.addCases f g : Fin ((m' + 1) + (n' + 1)) → α)
        ((Fin.natAdd (m' + 1) j).succAbove (Fin.castAdd n' a)) =
      (Fin.addCases f (fun a => g (j.succAbove a)) : Fin ((m' + 1) + n') → α)
        (Fin.castAdd n' a) := by
    intro a
    have hlt : (Fin.castAdd n' a).castSucc < Fin.natAdd (m' + 1) j := by
      apply Fin.lt_def.mpr
      simp [Fin.val_natAdd]
      omega
    rw [Fin.succAbove_of_castSucc_lt _ _ hlt]
    rw [show (Fin.castAdd n' a).castSucc = Fin.castAdd (n' + 1) a by
      ext
      simp]
    simp [Fin.addCases_left]
  have hright : forall b : Fin n',
      (Fin.addCases f g : Fin ((m' + 1) + (n' + 1)) → α)
        ((Fin.natAdd (m' + 1) j).succAbove (Fin.natAdd (m' + 1) b)) =
      (Fin.addCases f (fun a => g (j.succAbove a)) : Fin ((m' + 1) + n') → α)
        (Fin.natAdd (m' + 1) b) := by
    intro b
    simp only [Fin.addCases_right]
    by_cases h : b.castSucc < j
    case pos =>
      rw [Fin.succAbove_of_castSucc_lt]
      case h =>
        apply Fin.lt_def.mpr
        simpa [Fin.val_natAdd, Fin.val_castSucc] using! h
      rw [show (Fin.natAdd (m' + 1) b).castSucc =
          Fin.natAdd (m' + 1) b.castSucc by
        ext
        simp]
      rw [Fin.addCases_right]
      rw [Fin.succAbove_of_castSucc_lt _ _ h]
    case neg =>
      rw [Fin.succAbove_of_le_castSucc]
      case h =>
        apply Fin.le_def.mpr
        have hb : j.val <= b.val := Fin.le_def.mp (Fin.not_lt.mp h)
        simp [Fin.val_natAdd, Fin.val_castSucc]
        omega
      rw [show (Fin.natAdd (m' + 1) b).succ = Fin.natAdd (m' + 1) b.succ by
        ext
        simp
        omega]
      rw [Fin.addCases_right]
      rw [Fin.succAbove_of_le_castSucc _ _ (Fin.not_lt.mp h)]
  exact Fin.addCases (motive := fun k =>
      (Fin.addCases f g : Fin ((m' + 1) + (n' + 1)) → α)
        ((Fin.natAdd (m' + 1) j).succAbove k) =
      (Fin.addCases f (fun a => g (j.succAbove a)) : Fin ((m' + 1) + n') → α) k)
    hleft hright k

lemma det_subst_eq {R : Type*} [CommRing R] {a b : ℕ} (h : a = b)
    (f : Fin a → Fin a → R) (g : Fin b → Fin b → R)
    (hfg : ∀ i j, f (Fin.cast h.symm i) (Fin.cast h.symm j) = g i j) :
    Matrix.det f = Matrix.det g := by
  subst h; exact congr_arg _ (funext fun i => funext fun j => hfg i j)

end Fin
