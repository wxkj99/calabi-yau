module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceContractionBound.Basic

/-!
# ActionContractions for the reference-curvature contraction

Székelyhidi, An Introduction to Extremal Kähler Metrics, §3.3, proof of Lemma 3.9, terms following (3.15), printed p. 45; finite tensor contraction algebra implementing that proof.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal BigOperators ComplexOrder MatrixOrder
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

lemma referenceAction_pullback_cancel_left {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℂ)
    (hPQ : P * Q = 1) (a b : Fin n) :
    ∑ r, P a r * Q r b = if a = b then 1 else 0 := by
  have h := congrFun (congrFun hPQ a) b
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

theorem referenceAction_sum_three_cycle {n : ℕ}
    (F : Fin n → Fin n → Fin n → ℂ) :
    (∑ a, ∑ b, ∑ c, F a b c) = ∑ b, ∑ c, ∑ a, F a b c := by
  calc
    (∑ a, ∑ b, ∑ c, F a b c) = ∑ b, ∑ a, ∑ c, F a b c :=
      Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ a, F a b c := by
      apply Finset.sum_congr rfl
      intro b hb
      exact Finset.sum_comm

lemma referenceAction_pullback_tensor_contract {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℂ)
    (hPQ : P * Q = 1) (F G : Fin n → ℂ) :
    ∑ r, (∑ a, F a * P a r) * (∑ b, Q r b * G b) =
      ∑ a, F a * G a := by
  classical
  calc
    _ = ∑ r, ∑ a, ∑ b, (F a * P a r) * (Q r b * G b) := by
      apply Finset.sum_congr rfl
      intro r hr
      simp only [Fintype.sum_mul_sum]
    _ = ∑ a, ∑ b, ∑ r, (F a * P a r) * (Q r b * G b) := by
      rw [referenceAction_sum_three_cycle]
    _ = ∑ a, ∑ b, (F a * G b) * (∑ r, P a r * Q r b) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      calc
        ∑ r, (F a * P a r) * (Q r b * G b) =
            ∑ r, (F a * G b) * (P a r * Q r b) := by
          apply Finset.sum_congr rfl
          intro r hr
          ring
        _ = (F a * G b) * (∑ r, P a r * Q r b) := by
          rw [Finset.mul_sum]
    _ = ∑ a, ∑ b, (F a * G b) * (if a = b then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [referenceAction_pullback_cancel_left P Q hPQ a b]
    _ = ∑ a, F a * G a := by simp

lemma referenceAction_pullback_tensor_contract_upper_lower {n : ℕ}
    (P Q : Matrix (Fin n) (Fin n) ℂ) (hPQ : P * Q = 1)
    (F G : Fin n → ℂ) :
    ∑ r, (∑ a, Q r a * F a) * (∑ b, P b r * G b) =
      ∑ a, F a * G a := by
  calc
    (∑ r, (∑ a, Q r a * F a) * (∑ b, P b r * G b)) =
        ∑ r, (∑ b, G b * P b r) * (∑ a, Q r a * F a) := by
      apply Finset.sum_congr rfl
      intro r hr
      have hcomm : (∑ b, P b r * G b) = ∑ b, G b * P b r := by
        apply Finset.sum_congr rfl
        intro b hb
        ring
      rw [hcomm]
      ring
    _ = ∑ b, G b * F b :=
      referenceAction_pullback_tensor_contract P Q hPQ G F
    _ = ∑ a, F a * G a := by
      apply Finset.sum_congr rfl
      intro a ha
      ring

theorem referenceAction_sum_four_reorder {n : ℕ}
    (F : Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) =
      ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := by
  calc
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) = ∑ b, ∑ a, ∑ c, ∑ d, F a b c d :=
      Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ a, ∑ d, F a b c d := by
      apply Finset.sum_congr rfl
      intro b hb
      exact Finset.sum_comm
    _ = ∑ c, ∑ b, ∑ a, ∑ d, F a b c d := Finset.sum_comm
    _ = ∑ c, ∑ b, ∑ d, ∑ a, F a b c d := by
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro b hb
      exact Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ b, ∑ a, F a b c d := by
      apply Finset.sum_congr rfl
      intro c hc
      exact Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := by
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro d hd
      exact Finset.sum_comm

lemma referenceAction_metric_contract_two_actions {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℂ) (g g' : Matrix (Fin n) (Fin n) ℂ)
    (hmetric : ∀ s u, ∑ p, ∑ q, g' q p * P s p * star (P u q) = g u s)
    (F G : Fin n → ℂ) :
    ∑ p, ∑ q, g' q p * (∑ s, P s p * F s) *
      (∑ u, star (P u q) * G u) =
      ∑ s, ∑ u, g u s * F s * G u := by
  classical
  have hExpand (p q : Fin n) :
      g' q p * (∑ s, P s p * F s) * (∑ u, star (P u q) * G u) =
        ∑ s, ∑ u, (g' q p * P s p * star (P u q)) * (F s * G u) := by
    calc
      _ = ∑ u, (g' q p * (∑ s, P s p * F s)) *
          (star (P u q) * G u) := by
        rw [Finset.mul_sum]
      _ = ∑ u, ∑ s, (g' q p * (P s p * F s)) *
          (star (P u q) * G u) := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [Finset.mul_sum, Finset.sum_mul]
      _ = ∑ s, ∑ u, (g' q p * P s p * star (P u q)) *
          (F s * G u) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro s hs
        apply Finset.sum_congr rfl
        intro u hu
        ring_nf
  calc
    _ = ∑ p, ∑ q, ∑ s, ∑ u,
        (g' q p * P s p * star (P u q)) * (F s * G u) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      exact hExpand p q
    _ = ∑ s, ∑ u, F s * G u *
        (∑ p, ∑ q, g' q p * P s p * star (P u q)) := by
      rw [referenceAction_sum_four_reorder]
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro u hu
      calc
        ∑ p, ∑ q, (g' q p * P s p * star (P u q)) * (F s * G u) =
            ∑ p, (∑ q, g' q p * P s p * star (P u q)) * (F s * G u) := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [← Finset.sum_mul]
        _ = (∑ p, ∑ q, g' q p * P s p * star (P u q)) * (F s * G u) := by
          rw [← Finset.sum_mul]
        _ = F s * G u * (∑ p, ∑ q, g' q p * P s p * star (P u q)) := by ring
    _ = ∑ s, ∑ u, F s * G u * g u s := by
      simp_rw [hmetric]
    _ = ∑ s, ∑ u, g u s * F s * G u := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro u hu
      ring

lemma referenceAction_pullback_upper_action3 {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℂ)
    (Y : Fin n → Fin n → Fin n → ℂ) (r : Fin n) :
    ∑ a, ∑ b, ∑ c, Q r a * Y a b c =
      ∑ a, Q r a * (∑ b, ∑ c, Y a b c) := by
  classical
  apply Finset.sum_congr rfl
  intro a ha
  simp only [Finset.mul_sum]

lemma referenceAction_pullback_lower_action_middle {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℂ)
    (Y : Fin n → Fin n → Fin n → Fin n → ℂ) (r : Fin n) :
    ∑ a, ∑ b, ∑ c, ∑ e, Y a c e b * P b r =
      ∑ b, P b r * ∑ a, ∑ c, ∑ e, Y a c e b := by
  classical
  calc
    (∑ a, ∑ b, ∑ c, ∑ e, Y a c e b * P b r) =
        ∑ b, ∑ a, ∑ c, ∑ e, Y a c e b * P b r := by
      rw [Finset.sum_comm]
    _ = ∑ b, P b r * ∑ a, ∑ c, ∑ e, Y a c e b := by
      apply Finset.sum_congr rfl
      intro b hb
      calc
        (∑ a, ∑ c, ∑ e, Y a c e b * P b r) =
            ∑ a, ∑ c, (∑ e, Y a c e b) * P b r := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro c hc
          rw [Finset.sum_mul]
        _ = ∑ a, (∑ c, ∑ e, Y a c e b) * P b r := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.sum_mul]
        _ = (∑ a, ∑ c, ∑ e, Y a c e b) * P b r := by
          rw [Finset.sum_mul]
        _ = P b r * (∑ a, ∑ c, ∑ e, Y a c e b) := by ring
    _ = ∑ b, P b r * ∑ a, ∑ c, ∑ e, Y a c e b := rfl

lemma referenceAction_pullback_lower_action {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ)
    (X : Fin n → Fin n → ℂ) (T : Fin n → Fin n → Fin n → ℂ) (r : Fin n) :
    ∑ a, ∑ b, ∑ c, X a b * P c r * T a b c =
      ∑ c, (∑ a, ∑ b, X a b * T a b c) * P c r := by
  classical
  calc
    (∑ a, ∑ b, ∑ c, X a b * P c r * T a b c) =
        ∑ a, ∑ b, ∑ c, (X a b * T a b c) * P c r := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      ring
    _ = ∑ c, ∑ a, ∑ b, (X a b * T a b c) * P c r := by
      rw [referenceAction_sum_three_cycle, referenceAction_sum_three_cycle]
    _ = ∑ c, (∑ a, ∑ b, X a b * T a b c) * P c r := by
      apply Finset.sum_congr rfl
      intro c hc
      calc
        ∑ a, ∑ b, (X a b * T a b c) * P c r =
            ∑ a, (∑ b, X a b * T a b c) * P c r := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [← Finset.sum_mul]
        _ = (∑ a, ∑ b, X a b * T a b c) * P c r := by
          rw [← Finset.sum_mul]

lemma referenceAction_sum_triple_block_swap {n : ℕ}
    (F : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, F a b c d e f) =
      ∑ d, ∑ e, ∑ f, ∑ a, ∑ b, ∑ c, F a b c d e f := by
  classical
  simpa only [Fintype.sum_prod_type] using
    (Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun (x : Fin n × Fin n × Fin n) (y : Fin n × Fin n × Fin n) =>
        F x.1 x.2.1 x.2.2 y.1 y.2.1 y.2.2))

lemma referenceAction_sum_six_rotate {n : ℕ}
    (F : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, F a b c d e f) =
      ∑ f, ∑ d, ∑ e, ∑ a, ∑ b, ∑ c, F a b c d e f := by
  classical
  calc
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, F a b c d e f) =
        ∑ a, ∑ b, ∑ c, ∑ f, ∑ d, ∑ e, F a b c d e f := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      rw [referenceAction_sum_three_cycle, referenceAction_sum_three_cycle]
    _ = ∑ f, ∑ d, ∑ e, ∑ a, ∑ b, ∑ c, F a b c d e f :=
      referenceAction_sum_triple_block_swap (fun a b c f d e => F a b c d e f)

lemma referenceAction_pullback_upper_action {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℂ)
    (Y : Fin n → Fin n → Fin n → Fin n → ℂ) (r : Fin n) :
    ∑ a, ∑ b, ∑ c, ∑ e, Q r a * Y a b c e =
      ∑ a, Q r a * (∑ b, ∑ c, ∑ e, Y a b c e) := by
  classical
  apply Finset.sum_congr rfl
  intro a ha
  calc
    (∑ b, ∑ c, ∑ e, Q r a * Y a b c e) =
        ∑ b, ∑ c, (Q r a * ∑ e, Y a b c e) := by
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.mul_sum]
    _ = ∑ b, Q r a * (∑ c, ∑ e, Y a b c e) := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.mul_sum]
    _ = Q r a * (∑ b, ∑ c, ∑ e, Y a b c e) := by
      rw [Finset.mul_sum]

end KahlerForm
