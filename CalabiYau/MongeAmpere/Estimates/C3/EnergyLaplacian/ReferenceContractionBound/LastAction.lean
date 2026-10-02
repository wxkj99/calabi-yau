module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceContractionBound.ActionContractions

/-!
# LastAction for the reference-curvature contraction

Székelyhidi, An Introduction to Extremal Kähler Metrics, §3.3, proof of Lemma 3.9, terms following (3.15), printed p. 45; finite tensor contraction algebra implementing that proof.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal BigOperators ComplexOrder MatrixOrder
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

theorem referenceAction_minus_k_action_covariance {n : ℕ}
    (P Q g g' : Matrix (Fin n) (Fin n) ℂ)
    (T : Fin n → Fin n → Fin n → ℂ)
    (U : Fin n → Fin n → Fin n → Fin n → ℂ)
    (hPQ : P * Q = 1)
    (hmetric : ∀ s u, ∑ p, ∑ q, g' q p * P s p * star (P u q) = g u s) :
    ∀ i j k, referenceAction_tauT P Q (referenceAction_minusKPart g T U) i j k =
      referenceAction_minusKPart g' (referenceAction_tauT P Q T) (referenceAction_tauU P Q U) i j k := by
  classical
  intro i j k
  simp only [referenceAction_tauT, referenceAction_tauU, referenceAction_minusKPart]
  let X : Fin n → Fin n → ℂ := fun p a =>
    ∑ b, ∑ c, P b p * P c k * T a b c
  let Y : Fin n → Fin n → ℂ := fun q a =>
    ∑ b, ∑ c, ∑ e, Q i b * P c j * star (P e q) * U b c a e
  let A : Fin n → Fin n → ℂ := fun b r => ∑ c, P c k * T r b c
  let B : Fin n → Fin n → ℂ := fun e r =>
    ∑ b, ∑ c, Q i b * P c j * U b c r e
  have hT (r p : Fin n) :
      (∑ a, ∑ b, ∑ c, Q r a * P b p * P c k * T a b c) =
        ∑ a, Q r a * X p a := by
    dsimp [X]
    simpa only [mul_assoc] using
      (referenceAction_pullback_upper_action3 Q (fun a b c => P b p * P c k * T a b c) r)
  have hU (r q : Fin n) :
      (∑ a, ∑ b, ∑ c, ∑ e,
        Q i a * P b j * P c r * star (P e q) * U a b c e) =
        ∑ c, P c r * Y q c := by
    calc
      (∑ a, ∑ b, ∑ c, ∑ e,
        Q i a * P b j * P c r * star (P e q) * U a b c e) =
        ∑ a, ∑ b, ∑ c, ∑ e,
          Q i a * P c j * star (P e q) * U a c b e * P b r := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro b hb
        apply Finset.sum_congr rfl
        intro c hc
        apply Finset.sum_congr rfl
        intro e he
        ring
      _ = ∑ b, P b r * ∑ a, ∑ c, ∑ e,
          Q i a * P c j * star (P e q) * U a c b e := by
        exact referenceAction_pullback_lower_action_middle P
          (fun a b e c => Q i a * P b j * star (P e q) * U a b c e) r
      _ = ∑ b, P b r * Y q b := by rfl
  have hInner (p q : Fin n) :
      (∑ r,
        (∑ a, ∑ b, ∑ c, Q r a * P b p * P c k * T a b c) *
        (∑ a, ∑ b, ∑ c, ∑ e,
          Q i a * P b j * P c r * star (P e q) * U a b c e)) =
        ∑ a, X p a * Y q a := by
    calc
      _ = ∑ r, (∑ a, Q r a * X p a) * (∑ c, P c r * Y q c) := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [hT r p, hU r q]
      _ = ∑ a, X p a * Y q a :=
        referenceAction_pullback_tensor_contract_upper_lower P Q hPQ (fun a => X p a) (fun a => Y q a)
  have hRight :
      (∑ p, ∑ q, g' q p * ∑ r,
        (∑ a, ∑ b, ∑ c, Q r a * P b p * P c k * T a b c) *
        (∑ a, ∑ b, ∑ c, ∑ e,
          Q i a * P b j * P c r * star (P e q) * U a b c e)) =
        ∑ p, ∑ q, g' q p * ∑ a, X p a * Y q a := by
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    rw [hInner p q]
  have hX (p r : Fin n) :
      X p r = ∑ b, P b p * (∑ c, P c k * T r b c) := by
    dsimp [X]
    apply Finset.sum_congr rfl
    intro b hb
    calc
      (∑ c, P b p * P c k * T r b c) =
          ∑ c, P b p * (P c k * T r b c) := by
        apply Finset.sum_congr rfl
        intro c hc
        ring
      _ = P b p * (∑ c, P c k * T r b c) := by rw [← Finset.mul_sum]
  have hY (q r : Fin n) :
      Y q r = ∑ e, star (P e q) * (∑ b, ∑ c, Q i b * P c j * U b c r e) := by
    dsimp [Y]
    calc
      (∑ b, ∑ c, ∑ e, Q i b * P c j * star (P e q) * U b c r e) =
        ∑ b, ∑ c, ∑ e, star (P e q) * (Q i b * P c j * U b c r e) := by
        apply Finset.sum_congr rfl
        intro b hb
        apply Finset.sum_congr rfl
        intro c hc
        apply Finset.sum_congr rfl
        intro e he
        ring
      _ = ∑ e, ∑ b, ∑ c, star (P e q) * (Q i b * P c j * U b c r e) := by
        rw [referenceAction_sum_three_cycle, referenceAction_sum_three_cycle]
      _ = ∑ e, star (P e q) * (∑ b, ∑ c, Q i b * P c j * U b c r e) := by
        apply Finset.sum_congr rfl
        intro e he
        calc
          (∑ b, ∑ c, star (P e q) * (Q i b * P c j * U b c r e)) =
              ∑ b, star (P e q) * (∑ c, Q i b * P c j * U b c r e) := by
            apply Finset.sum_congr rfl
            intro b hb
            rw [← Finset.mul_sum]
          _ = star (P e q) * (∑ b, ∑ c, Q i b * P c j * U b c r e) := by
            rw [← Finset.mul_sum]
  have hMetricAt (r : Fin n) :
      ∑ p, ∑ q, g' q p * X p r * Y q r =
        ∑ b, ∑ e, g e b * A b r * B e r := by
    calc
      (∑ p, ∑ q, g' q p * X p r * Y q r) =
          ∑ p, ∑ q, g' q p * (∑ b, P b p * (∑ c, P c k * T r b c)) *
            (∑ e, star (P e q) * (∑ b, ∑ c, Q i b * P c j * U b c r e)) := by
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro q hq
        rw [hX p r, hY q r]
      _ = ∑ b, ∑ e, g e b * A b r * B e r := by
        simpa [A, B] using referenceAction_metric_contract_two_actions P g g' hmetric
          (fun b => ∑ c, P c k * T r b c)
          (fun e => ∑ b, ∑ c, Q i b * P c j * U b c r e)
  have hscalar : ∀ (C : ℂ) (F : Fin n → ℂ),
      (∑ a, C * F a) = C * (∑ a, F a) := by
    intro C F
    symm
    apply Finset.mul_sum
  have hscalar2 : ∀ (C : ℂ) (F : Fin n → Fin n → ℂ),
      (∑ a, ∑ b, C * F a b) = C * (∑ a, ∑ b, F a b) := by
    intro C F
    calc
      (∑ a, ∑ b, C * F a b) = ∑ a, C * (∑ b, F a b) := by
        apply Finset.sum_congr rfl
        intro a ha
        exact hscalar C (F a)
      _ = C * (∑ a, ∑ b, F a b) := hscalar C (fun a => ∑ b, F a b)
  have hFactor (p q r : Fin n) :
      ∑ c, ∑ a, ∑ b,
        Q i a * P b j * P c k * (g q p * (T r p c * U a b r q)) =
        g q p * (∑ c, P c k * T r p c) *
          (∑ a, ∑ b, Q i a * P b j * U a b r q) := by
    calc
      (∑ c, ∑ a, ∑ b,
        Q i a * P b j * P c k * (g q p * (T r p c * U a b r q))) =
        ∑ c, ∑ a, ∑ b,
          (g q p * (P c k * T r p c)) * (Q i a * P b j * U a b r q) := by
        apply Finset.sum_congr rfl
        intro c hc
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        ring
      _ = g q p * (∑ c, P c k * T r p c) *
          (∑ a, ∑ b, Q i a * P b j * U a b r q) := by
        calc
          (∑ c, ∑ a, ∑ b,
            (g q p * (P c k * T r p c)) * (Q i a * P b j * U a b r q)) =
            ∑ c, (g q p * (P c k * T r p c)) *
              (∑ a, ∑ b, Q i a * P b j * U a b r q) := by
              apply Finset.sum_congr rfl
              intro c hc
              exact hscalar2 (g q p * (P c k * T r p c))
                (fun a b => Q i a * P b j * U a b r q)
          _ = (∑ c, g q p * (P c k * T r p c)) *
              (∑ a, ∑ b, Q i a * P b j * U a b r q) := by
              rw [Finset.sum_mul]
          _ = g q p * (∑ c, P c k * T r p c) *
              (∑ a, ∑ b, Q i a * P b j * U a b r q) := by
              apply congrArg (fun z : ℂ => z * (∑ a, ∑ b, Q i a * P b j * U a b r q))
              rw [← Finset.mul_sum]
  have hSource :
      (∑ a, ∑ b, ∑ c, Q i a * P b j * P c k *
        ∑ p, ∑ q, g q p * ∑ r, T r p c * U a b r q) =
      ∑ r, ∑ p, ∑ q, g q p * (∑ c, P c k * T r p c) *
        (∑ a, ∑ b, Q i a * P b j * U a b r q) := by
    calc
      (∑ a, ∑ b, ∑ c, Q i a * P b j * P c k *
        ∑ p, ∑ q, g q p * ∑ r, T r p c * U a b r q) =
        ∑ a, ∑ b, ∑ c, ∑ p, ∑ q, ∑ r,
          Q i a * P b j * P c k * (g q p * (T r p c * U a b r q)) := by
        simp only [Finset.mul_sum]
      _ = ∑ r, ∑ p, ∑ q, ∑ c, ∑ a, ∑ b,
          Q i a * P b j * P c k * (g q p * (T r p c * U a b r q)) := by
        calc
          (∑ a, ∑ b, ∑ c, ∑ p, ∑ q, ∑ r,
            Q i a * P b j * P c k * (g q p * (T r p c * U a b r q))) =
            ∑ r, ∑ p, ∑ q, ∑ a, ∑ b, ∑ c,
              Q i a * P b j * P c k * (g q p * (T r p c * U a b r q)) := by
                rw [referenceAction_sum_six_rotate]
          _ = ∑ r, ∑ p, ∑ q, ∑ c, ∑ a, ∑ b,
              Q i a * P b j * P c k * (g q p * (T r p c * U a b r q)) := by
            apply Finset.sum_congr rfl
            intro r hr
            apply Finset.sum_congr rfl
            intro p hp
            apply Finset.sum_congr rfl
            intro q hq
            rw [referenceAction_sum_three_cycle, referenceAction_sum_three_cycle]
      _ = ∑ r, ∑ p, ∑ q, g q p * (∑ c, P c k * T r p c) *
          (∑ a, ∑ b, Q i a * P b j * U a b r q) := by
        apply Finset.sum_congr rfl
        intro r hr
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro q hq
        simpa using hFactor p q r
  have hReorder :
      (∑ p, ∑ q, g' q p * ∑ a, X p a * Y q a) =
        ∑ a, ∑ p, ∑ q, g' q p * X p a * Y q a := by
    calc
      (∑ p, ∑ q, g' q p * ∑ a, X p a * Y q a) =
          ∑ p, ∑ q, ∑ a, g' q p * (X p a * Y q a) := by
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro q hq
        rw [Finset.mul_sum]
      _ = ∑ a, ∑ p, ∑ q, g' q p * (X p a * Y q a) := by
        rw [referenceAction_sum_three_cycle, referenceAction_sum_three_cycle]
      _ = ∑ a, ∑ p, ∑ q, g' q p * X p a * Y q a := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro q hq
        ring
  rw [hRight, hReorder]
  calc
    (∑ a, ∑ b, ∑ c, Q i a * P b j * P c k *
      ∑ p, ∑ q, g q p * ∑ r, T r p c * U a b r q) =
      ∑ r, ∑ p, ∑ q, g q p * (∑ c, P c k * T r p c) *
        (∑ a, ∑ b, Q i a * P b j * U a b r q) := hSource
    _ = ∑ r, ∑ p, ∑ q, g' q p * X p r * Y q r := by
      apply Finset.sum_congr rfl
      intro r hr
      exact (hMetricAt r).symm

end KahlerForm
