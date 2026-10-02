module

public import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.NormalCoordinates.BilinearJet
public import CalabiYau.Geometry.Complex.Forms.OneOne
import CalabiYau.LinearAlgebra.Hermitian.NormalJet

/-!
# Finite quadratic-jet cancellation

The Kähler symmetry of the reference metric's first coordinate derivatives makes the transformed
first-jet array symmetric in the derivative direction and the first metric index. Once the linear
frame has normalized the reference matrix, the remaining quadratic coordinate jet is chosen by
solving the finite normal-jet equation. `Matrix.exists_symmetric_normal_jet` supplies a symmetric
correction, and the normalization identity supplies the inverse needed to solve the contraction.

This is the algebraic cancellation step in Székelyhidi, §1.3, Proposition 1.16. The equation below
is written in exactly the coefficient order consumed by the quadratic pullback derivative child:
`Q(eₚ,eⱼ)ᵀ G J̄` cancels `Jᵀ(∂G·Jeₚ)J̄`. The assumed symmetry is the Kähler identity, not a property
of an arbitrary derivative array. For `n=0`, the equation is vacuous and `Q=0` works; for a flat
metric all derivative data vanish and the zero jet is admissible; for `n=1` the equation determines
the single quadratic coefficient. The convention is `J.transpose * G * J.map star`.
-/

@[expose] public section

open scoped MatrixOrder

namespace KahlerForm

/-- A symmetric quadratic coordinate jet cancels the first derivative of the normalized reference
metric after the linear frame `J`. -/
@[deprecated "unused hypothesis `hG`; will be removed" (since := "2026-10-02")]
theorem exists_quadratic_pullback_jet_cancellation {n : ℕ}
    (G J : Matrix (Fin n) (Fin n) ℂ) (D : Fin n → Fin n → Fin n → ℂ)
    (hG : G.IsHermitian)
    (hNorm : J.transpose * G * J.map star = 1)
    (hD : ∀ p a b, D p a b = D a p b) :
    ∃ Q : EuclideanSpace ℂ (Fin n) →L[ℂ]
        EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n),
      (∀ u v, Q u v = Q v u) ∧
      ∀ p j k,
        (∑ a, ∑ b,
          Q (EuclideanSpace.single p 1) (EuclideanSpace.single j 1) a *
            G a b * star (J b k)) +
          ∑ a, ∑ b, ∑ c,
            J a j * star (J b k) * J c p * D c a b = 0 := by
  classical
  let B := G * J.map star
  have hBJ : B.transpose * J = 1 := by
    have h : J.transpose * B = 1 := by simpa [B, Matrix.mul_assoc] using hNorm
    have ht := congrArg Matrix.transpose h
    simpa [Matrix.transpose_mul] using ht
  let T : Fin n → Fin n → Fin n → ℂ := fun p j k ↦
    ∑ c, ∑ a, ∑ b, J c p * J a j * star (J b k) * D c a b
  have hTsym (p j k : Fin n) : T p j k = T j p k := by
    dsimp [T]
    calc
      (∑ c, ∑ a, ∑ b, J c p * J a j * star (J b k) * D c a b) =
          ∑ a, ∑ c, ∑ b, J c p * J a j * star (J b k) * D c a b :=
        Finset.sum_comm
      _ = ∑ c, ∑ a, ∑ b, J c j * J a p * star (J b k) * D c a b := by
        apply Finset.sum_congr rfl
        intro c hc
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        rw [hD]
        ring
  obtain ⟨C, hC, hsolve⟩ := Matrix.exists_symmetric_normal_jet B J hBJ T hTsym
  obtain ⟨Q, hQ, hQcoeff⟩ := exists_continuous_symmetric_bilinear_jet C hC
  refine ⟨Q, hQ, ?_⟩
  intro p j k
  have hTval : T p j k =
      ∑ a, ∑ b, ∑ c, J a j * star (J b k) * J c p * D c a b := by
    dsimp [T]
    calc
      (∑ c, ∑ a, ∑ b, J c p * J a j * star (J b k) * D c a b) =
          ∑ a, ∑ c, ∑ b, J c p * J a j * star (J b k) * D c a b :=
        Finset.sum_comm
      _ = ∑ a, ∑ b, ∑ c, J c p * J a j * star (J b k) * D c a b := by
        apply Finset.sum_congr rfl
        intro a ha
        exact Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        apply Finset.sum_congr rfl
        intro c hc
        simp only [Complex.star_def]
        ring
  have hBval : (∑ a, B a k * C a p j) =
      ∑ a, ∑ b, Q (EuclideanSpace.single p 1)
        (EuclideanSpace.single j 1) a * G a b * star (J b k) := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [hQcoeff]
    change (G * J.map star) a k * C a p j = _
    simp only [Matrix.mul_apply, Matrix.map_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b hb
    simp only [Complex.star_def]
    ring
  have hs := hsolve p j k
  rw [hTval, hBval] at hs
  exact (add_comm _ _).trans hs

end KahlerForm
