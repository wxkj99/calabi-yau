module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.Basic
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.ContractionBound.MixedFrame

/-!
# PairingCovariance for the differentiated Ricci contraction

Székelyhidi, An Introduction to Extremal Kähler Metrics, §3.3, proof of
Lemma 3.9, printed pp. 44–45: two-sided metric comparison and the
linear-plus-quadratic connection correction.

The six-slot pairing identity follows from the stated output and inverse-metric contraction identities. The sums vanish for `Fin 0`; in dimension one scalar changes cancel the two metric inverses against the tensor factors.
-/

public section

open scoped Manifold ContDiff BigOperators ComplexOrder MatrixOrder
open ContinuousAlternatingMap
open Matrix

namespace KahlerForm

theorem c3Pair_frame_change {n : ℕ}
    (g₀ h₀ g₁ h₁ A B : Matrix (Fin n) (Fin n) ℂ)
    (D T : Fin n → Fin n → Fin n → ℂ)
    (hOut : ∀ p s, ∑ x : Fin n × Fin n,
      g₀ x.1 x.2 * B x.1 p * star (B x.2 s) = g₁ p s)
    (hIn : ∀ q t, ∑ x : Fin n × Fin n,
      h₀ x.1 x.2 * A q x.2 * star (A t x.1) = h₁ t q) :
    (∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
      g₀ i a * h₀ b j * h₀ c k *
        c3MixedFrameChange A B D i j k *
          star (c3MixedFrameChange A B T a b c)) =
    ∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
      g₁ i a * h₁ b j * h₁ c k * D i j k * star (T a b c) := by
  classical
  unfold c3MixedFrameChange
  simp only [star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => enter [2]; intro y; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  let f₀ : C3Pair n → C3Pair n → (Fin n × Fin n) → ℂ :=
    fun y x z ↦ g₀ z.1 z.2 * B z.1 y.1 * star (B z.2 x.1)
  let f₁ : C3Pair n → C3Pair n → (Fin n × Fin n) → ℂ :=
    fun y x z ↦ h₀ z.1 z.2 * A y.2.1 z.2 * star (A x.2.1 z.1)
  let f₂ : C3Pair n → C3Pair n → (Fin n × Fin n) → ℂ :=
    fun y x z ↦ h₀ z.1 z.2 * A y.2.2 z.2 * star (A x.2.2 z.1)
  have hfac (y x : C3Pair n) :
      (∑ z : C3PairTriple n,
        g₀ z.1.1 z.1.2 * h₀ z.2.1.1 z.2.1.2 * h₀ z.2.2.1 z.2.2.2 *
          (B z.1.1 y.1 * A y.2.1 z.2.1.2 * A y.2.2 z.2.2.2 *
            D y.1 y.2.1 y.2.2) *
          (star (T x.1 x.2.1 x.2.2) *
            (star (A x.2.2 z.2.2.1) *
              (star (A x.2.1 z.2.1.1) * star (B z.1.2 x.1))))) =
        (∑ z, f₀ y x z) * (∑ z, f₁ y x z) * (∑ z, f₂ y x z) *
          (D y.1 y.2.1 y.2.2 * star (T x.1 x.2.1 x.2.2)) := by
    calc
      _ = ∑ z : C3PairTriple n,
          f₀ y x z.1 * f₁ y x z.2.1 * f₂ y x z.2.2 *
            (D y.1 y.2.1 y.2.2 * star (T x.1 x.2.1 x.2.2)) := by
        apply Finset.sum_congr rfl
        intro z hz
        simp only [f₀, f₁, f₂]
        ring_nf
      _ = _ :=
        c3SumPairTripleFactor (f₀ y x) (f₁ y x) (f₂ y x)
          (D y.1 y.2.1 y.2.2 * star (T x.1 x.2.1 x.2.2))
  have hfacNested (y x : C3Pair n) :
      (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
        ∑ e : Fin n, ∑ f : Fin n,
          g₀ a b * h₀ c d * h₀ e f *
            (B a y.1 * A y.2.1 d * A y.2.2 f * D y.1 y.2.1 y.2.2) *
            (star (T x.1 x.2.1 x.2.2) *
              (star (A x.2.2 e) * (star (A x.2.1 c) * star (B b x.1))))) =
        (∑ z, f₀ y x z) * (∑ z, f₁ y x z) * (∑ z, f₂ y x z) *
          (D y.1 y.2.1 y.2.2 * star (T x.1 x.2.1 x.2.2)) := by
    simpa only [Fintype.sum_prod_type] using hfac y x
  conv_lhs =>
    enter [2]; intro y
    enter [2]; intro x
    enter [2]; intro x₁
    enter [2]; intro x₂
    enter [2]; intro x₃
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro y
    enter [2]; intro x
    enter [2]; intro x₁
    enter [2]; intro x₂
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro y
    enter [2]; intro x
    enter [2]; intro x₁
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro y
    enter [2]; intro x
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro y
    rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro x₅
    enter [2]; intro y
    enter [2]; intro x
    enter [2]; intro x₁
    enter [2]; intro x₂
    enter [2]; intro x₃
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro x₅
    enter [2]; intro y
    enter [2]; intro x
    enter [2]; intro x₁
    enter [2]; intro x₂
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro x₅
    enter [2]; intro y
    enter [2]; intro x
    enter [2]; intro x₁
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro x₅
    enter [2]; intro y
    enter [2]; intro x
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro x₅
    enter [2]; intro y
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro x₅
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro x₅
    enter [2]; intro y
    enter [2]; intro x
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro x₅
    enter [2]; intro y
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro x₅
    enter [2]; intro y
    enter [2]; intro a
    enter [2]; intro b
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro x₅
    enter [2]; intro y
    enter [2]; intro a
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro x₅
    enter [2]; intro y
    enter [2]; intro a
    enter [2]; intro b
    enter [2]; intro c
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro x₅
    enter [2]; intro y
    enter [2]; intro a
    enter [2]; intro b
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro x₅
    enter [2]; intro y
    enter [2]; intro a
    enter [2]; intro b
    enter [2]; intro c
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro x₅
    enter [2]; intro y
    enter [2]; intro a
    enter [2]; intro b
    enter [2]; intro c
    enter [2]; intro d
    rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs =>
    enter [2]; intro y
    enter [2]; intro x
    rw [hfacNested y x]
  simp_rw [f₀, f₁, f₂, hOut, hIn]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  ring

end KahlerForm
