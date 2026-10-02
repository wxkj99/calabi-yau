module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ConnectionLaplacian.FiniteJets

/-!
# Finite mixed and quartic curvature-jet permutations

These are the two finite-algebra cancellations used in the differential Bianchi
calculation. The only assumptions are the displayed symmetries of the finite jets;
no symmetry or invertibility of `H`, and no relation between `P` and `Q`, is required.
The indices `(p,j,q,k,l)` rotate to `(k,p,q,j,l)` with the barred slots fixed.

The identities below give the finite-algebra cancellations under the stated jet symmetries.
-/

public section

open scoped BigOperators

namespace KahlerForm

variable {n : ℕ}

private theorem c3JetNested4_swap13 {n : ℕ}
    (f : Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
      ∑ c, ∑ b, ∑ a, ∑ d, f a b c d := by
  classical
  calc
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
        ∑ b, ∑ a, ∑ c, ∑ d, f a b c d := Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ a, ∑ d, f a b c d := by
      apply Finset.sum_congr rfl
      intro b hb
      exact Finset.sum_comm
    _ = ∑ c, ∑ b, ∑ a, ∑ d, f a b c d := Finset.sum_comm

/-- The mixed first-jet/second-jet terms are invariant under the holomorphic
three-slot rotation, assuming exactly the first-jet and mixed-jet symmetries. -/
theorem c3JetMixed_permute
    (H : Matrix (Fin n) (Fin n) ℂ)
    (P : Fin n → Fin n → Fin n → ℂ)
    (S : Fin n → Fin n → Fin n → Fin n → ℂ)
    (hP : ∀ p k b, P p k b = P k p b)
    (hS : ∀ p q k l, S p q k l = S k q p l)
    (p j q k l : Fin n) :
    c3JetMixed H P S p j q k l = c3JetMixed H P S k p q j l := by
  classical
  have hFirst :
      (∑ a, ∑ b, H b a * P j k b * S p q a l) =
        ∑ r, ∑ m, H m r * P k j m * S p q r l := by
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro m hm
    rw [hP j k m]
  have hSecond :
      (∑ r, ∑ m, H m r * P p j m * S r q k l) =
        ∑ r, ∑ m, H m r * P p j m * S k q r l := by
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro m hm
    rw [hS r q k l]
  have hThird :
      (∑ r, ∑ m, H m r * P p k m * S j q r l) =
        ∑ r, ∑ m, H m r * P k p m * S r q j l := by
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro m hm
    rw [hP p k m, hS j q r l]
  unfold c3JetMixed c3JetChristoffel
  simp only [Finset.sum_mul]
  rw [hFirst, hSecond, hThird]
  ac_rfl

/-- The inverse-derivative and two connection-correction terms are invariant
under the same rotation, using only the first-jet symmetry. -/
theorem c3JetQuartic_permute
    (H : Matrix (Fin n) (Fin n) ℂ)
    (P Q : Fin n → Fin n → Fin n → ℂ)
    (hP : ∀ p k b, P p k b = P k p b)
    (s j q k l : Fin n) :
    c3JetQuartic H P Q s j q k l = c3JetQuartic H P Q k s q j l := by
  classical
  have hFirst :
      (∑ a, ∑ b, ∑ c, ∑ d,
        H b c * P s c d * H d a * P j k b * Q q a l) =
      ∑ r, ∑ m, ∑ a, ∑ b,
        H m r * P k j m * H b a * P s r b * Q q a l := by
    calc
      (∑ a, ∑ b, ∑ c, ∑ d,
          H b c * P s c d * H d a * P j k b * Q q a l) =
          ∑ c, ∑ b, ∑ a, ∑ d,
            H b c * P s c d * H d a * P j k b * Q q a l := by
        exact c3JetNested4_swap13 _
      _ = ∑ r, ∑ m, ∑ a, ∑ b,
            H m r * P k j m * H b a * P s r b * Q q a l := by
        apply Finset.sum_congr rfl
        intro r hr
        apply Finset.sum_congr rfl
        intro m hm
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        rw [hP j k m]
        ring
  have hSecond :
      (∑ r, ∑ m, ∑ a, ∑ b,
        (H m r * P s j m) * (H b a * P r k b * Q q a l)) =
      ∑ a, ∑ b, ∑ c, ∑ d,
        H b c * P k c d * H d a * P s j b * Q q a l := by
    calc
      (∑ r, ∑ m, ∑ a, ∑ b,
          (H m r * P s j m) * (H b a * P r k b * Q q a l)) =
          ∑ a, ∑ m, ∑ r, ∑ b,
            (H m r * P s j m) * (H b a * P r k b * Q q a l) := by
        exact c3JetNested4_swap13 _
      _ = ∑ a, ∑ m, ∑ r, ∑ b,
            (H m r * P s j m) * (H b a * P k r b * Q q a l) := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro m hm
        apply Finset.sum_congr rfl
        intro r hr
        apply Finset.sum_congr rfl
        intro b hb
        rw [hP r k b]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro m hm
        apply Finset.sum_congr rfl
        intro r hr
        apply Finset.sum_congr rfl
        intro b hb
        ring
  have hThird :
      (∑ r, ∑ m, ∑ a, ∑ b,
        (H m r * P s k m) * (H b a * P j r b * Q q a l)) =
      ∑ r, ∑ m, ∑ a, ∑ b,
        (H m r * P k s m) * (H b a * P r j b * Q q a l) := by
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    rw [hP s k m, hP j r b]
  unfold c3JetQuartic c3JetChristoffel
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [hFirst, hSecond, hThird]
  ac_rfl

end KahlerForm
