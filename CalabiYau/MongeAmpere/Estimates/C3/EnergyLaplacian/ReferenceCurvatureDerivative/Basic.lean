module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.BigOperators.Field

/-!
# Finite-array bridges for the covariant curvature derivative

These operators are independent of charts and metrics. They organize the two
holomorphic connection corrections and the three holomorphic/two conjugate
slots used in Székelyhidi, §3.3, proof of Lemma 3.9, printed pp. 44–45.
No geometric covariance or uniform bound is asserted by these definitions.
-/

@[expose] public section

open scoped BigOperators

namespace KahlerForm

variable {n : ℕ}

/-- Four covariant curvature slots, in holomorphic/antiholomorphic order. -/
noncomputable def c3FourSlotPullback (A : Matrix (Fin n) (Fin n) ℂ)
    (R : Fin n → Fin n → Fin n → Fin n → ℂ) (p q j k : Fin n) : ℂ :=
  ∑ a, ∑ b, ∑ c, ∑ d,
    A a p * star (A b q) * A c j * star (A d k) * R a b c d

/-- A fifth covariant slot is holomorphic: the factor order is `s,p,q̄,j,k̄`. -/
noncomputable def c3FiveSlotFrameContraction (A : Matrix (Fin n) (Fin n) ℂ)
    (T : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ)
    (s p q j k : Fin n) : ℂ :=
  ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
    A a s * A b p * star (A c q) * A d j * star (A e k) * T a b c d e

/-- The first jet of a four-slot pullback when conjugate Jacobian derivatives
vanish. This is an algebraic expression, not a claim of holomorphicity. -/
noncomputable def c3FourSlotPullbackZJet (A : Matrix (Fin n) (Fin n) ℂ)
    (dA : Fin n → Fin n → Fin n → ℂ)
    (R : Fin n → Fin n → Fin n → Fin n → ℂ)
    (dR : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ)
    (s p q j k : Fin n) : ℂ :=
  (∑ a, ∑ b, ∑ c, ∑ d,
    (dA s a p * star (A b q) * A c j * star (A d k) +
      A a p * star (A b q) * dA s c j * star (A d k)) * R a b c d) +
  ∑ t, ∑ a, ∑ b, ∑ c, ∑ d,
    A t s * A a p * star (A b q) * A c j * star (A d k) * dR t a b c d

/-- Subtract the connection on the two holomorphic slots `p,j` of curvature.
The derivative direction `s` is not another curvature slot to correct. -/
noncomputable def c3CovariantFourTensorZJet
    (Γ : Fin n → Fin n → Fin n → ℂ)
    (R : Fin n → Fin n → Fin n → Fin n → ℂ)
    (dR : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ)
    (s p q j k : Fin n) : ℂ :=
  dR s p q j k - ∑ a, Γ a s p * R a q j k - ∑ a, Γ a s j * R p q a k

end KahlerForm
