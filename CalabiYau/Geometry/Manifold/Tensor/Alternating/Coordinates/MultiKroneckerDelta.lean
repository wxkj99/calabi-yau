-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Tensor/Alternating/Coordinates/MultiKroneckerDelta.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Manifold.Tensor.Alternating.Reindexing.Permutation
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

open Equiv.Perm

namespace Fin

noncomputable def multiKroneckerDelta {R : Type*} [CommRing R] {k n : ℕ}
    (I J : Fin k → Fin n) : R :=
  Matrix.det (fun i j : Fin k => if I i = J j then 1 else 0)

variable {R : Type*} [CommRing R] {k n : ℕ}

theorem multiKroneckerDelta_comp_perm
    {J : Fin k → Fin n} (hJ : Function.Injective J)
    (σ : Equiv.Perm (Fin k)) :
    multiKroneckerDelta (R := R) (J ∘ ⇑σ) J = (Equiv.Perm.sign σ : R) := by
  unfold multiKroneckerDelta
  simp only [Function.comp, hJ.eq_iff]
  rw [show (fun i j : Fin k => if σ i = j then (1 : R) else 0) =
    (1 : Matrix (Fin k) (Fin k) R).submatrix (⇑σ) id from by
    ext i j; simp [Matrix.submatrix_apply, Matrix.one_apply]]
  rw [Matrix.det_permute, Matrix.det_one, mul_one]

theorem multiKroneckerDelta_eq_zero_of_not_injective_left
    {I J : Fin k → Fin n} (hI : ¬Function.Injective I) :
    multiKroneckerDelta (R := R) I J = 0 := by
  unfold multiKroneckerDelta
  obtain ⟨i₁, i₂, heq, hne⟩ := Function.not_injective_iff.mp hI
  exact Matrix.det_zero_of_row_eq hne (funext fun j => by rw [heq])

theorem multiKroneckerDelta_eq_zero_of_not_injective_right
    {I J : Fin k → Fin n} (hJ : ¬Function.Injective J) :
    multiKroneckerDelta (R := R) I J = 0 := by
  unfold multiKroneckerDelta
  obtain ⟨j₁, j₂, heq, hne⟩ := Function.not_injective_iff.mp hJ
  exact Matrix.det_zero_of_column_eq hne (fun r => by rw [heq])

theorem multiKroneckerDelta_eq_zero
    {I J : Fin k → Fin n}
    (h : ∀ σ : Equiv.Perm (Fin k), I ≠ J ∘ ⇑σ) :
    multiKroneckerDelta (R := R) I J = 0 := by
  by_cases hI : Function.Injective I
  · by_cases hJ : Function.Injective J
    · have ⟨i, hi⟩ : ∃ i, ∀ j, I i ≠ J j := by
        by_contra hall
        push Not at hall
        choose f hf using hall
        have hf_inj : Function.Injective f :=
          fun a b hab => hI (by rw [hf a, hf b, hab])
        exact h (Equiv.ofBijective f
          ((Fintype.bijective_iff_injective_and_card f).mpr
            ⟨hf_inj, rfl⟩)) (funext hf)
      unfold multiKroneckerDelta
      exact Matrix.det_eq_zero_of_row_eq_zero i (fun j => if_neg (hi j))
    · exact multiKroneckerDelta_eq_zero_of_not_injective_right hJ
  · exact multiKroneckerDelta_eq_zero_of_not_injective_left hI

theorem multiKroneckerDelta_symm (I J : Fin k → Fin n) :
    multiKroneckerDelta (R := R) I J = multiKroneckerDelta J I := by
  unfold multiKroneckerDelta
  conv_lhs => erw [← Matrix.det_transpose]
  congr 1; ext i j
  change (if I j = J i then (1 : R) else 0) =
    (if J i = I j then 1 else 0)
  by_cases h : I j = J i
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (mt Eq.symm h)]

variable {𝕜 : Type*} [Field 𝕜]

end Fin
