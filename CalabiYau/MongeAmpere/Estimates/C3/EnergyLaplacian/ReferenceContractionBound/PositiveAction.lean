module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceContractionBound.ActionContractions

/-!
# PositiveAction for the reference-curvature contraction

Székelyhidi, An Introduction to Extremal Kähler Metrics, §3.3, proof of Lemma 3.9, terms following (3.15), printed p. 45; finite tensor contraction algebra implementing that proof.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal BigOperators ComplexOrder MatrixOrder
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

theorem referenceAction_plus_action_covariance {n : ℕ}
    (P Q g g' : Matrix (Fin n) (Fin n) ℂ)
    (T : Fin n → Fin n → Fin n → ℂ)
    (U : Fin n → Fin n → Fin n → Fin n → ℂ)
    (hPQ : P * Q = 1)
    (hmetric : ∀ s u, ∑ p, ∑ q, g' q p * P s p * star (P u q) = g u s) :
    ∀ i j k, referenceAction_tauT P Q (referenceAction_plusPart g T U) i j k =
      referenceAction_plusPart g' (referenceAction_tauT P Q T) (referenceAction_tauU P Q U) i j k := by
  classical
  intro i j k
  simp only [referenceAction_tauT, referenceAction_tauU, referenceAction_plusPart]
  let X : Fin n → Fin n → ℂ := fun p c =>
    ∑ a, ∑ b, Q i a * P b p * T a b c
  let Y : Fin n → Fin n → ℂ := fun q r =>
    ∑ b, ∑ c, ∑ e, P b j * P c k * star (P e q) * U r b c e
  have hT (p r : Fin n) :
      ∑ a, ∑ b, ∑ c, Q i a * P b p * P c r * T a b c =
        ∑ c, X p c * P c r := by
    calc
      (∑ a, ∑ b, ∑ c, Q i a * P b p * P c r * T a b c) =
          ∑ a, ∑ b, ∑ c, (Q i a * P b p) * P c r * T a b c := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        apply Finset.sum_congr rfl
        intro c hc
        ring
      _ = ∑ c, (∑ a, ∑ b, (Q i a * P b p) * T a b c) * P c r :=
        referenceAction_pullback_lower_action P (fun a b => Q i a * P b p) T r
      _ = ∑ c, X p c * P c r := by rfl
  have hU (r q : Fin n) :
      ∑ a, ∑ b, ∑ c, ∑ e,
        Q r a * P b j * P c k * star (P e q) * U a b c e =
        ∑ a, Q r a * Y q a := by
    calc
      (∑ a, ∑ b, ∑ c, ∑ e,
          Q r a * P b j * P c k * star (P e q) * U a b c e) =
          ∑ a, ∑ b, ∑ c, ∑ e,
            Q r a * (P b j * P c k * star (P e q) * U a b c e) := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        apply Finset.sum_congr rfl
        intro c hc
        apply Finset.sum_congr rfl
        intro e he
        ring
      _ = ∑ a, Q r a * (∑ b, ∑ c, ∑ e,
            P b j * P c k * star (P e q) * U a b c e) :=
        referenceAction_pullback_upper_action Q
          (fun a b c e => P b j * P c k * star (P e q) * U a b c e) r
      _ = ∑ a, Q r a * Y q a := by rfl
  have hInner (p q : Fin n) :
      ∑ r,
        (∑ a, ∑ b, ∑ c, Q i a * P b p * P c r * T a b c) *
          (∑ a, ∑ b, ∑ c, ∑ e,
            Q r a * P b j * P c k * star (P e q) * U a b c e) =
        ∑ c, X p c * Y q c := by
    calc
      (∑ r,
        (∑ a, ∑ b, ∑ c, Q i a * P b p * P c r * T a b c) *
          (∑ a, ∑ b, ∑ c, ∑ e,
            Q r a * P b j * P c k * star (P e q) * U a b c e)) =
        ∑ r, (∑ c, X p c * P c r) * (∑ a, Q r a * Y q a) := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [hT p r, hU r q]
      _ = ∑ c, X p c * Y q c := by
        exact referenceAction_pullback_tensor_contract P Q hPQ (fun c => X p c) (fun c => Y q c)
  have hRight :
      (∑ p, ∑ q, g' q p *
        ∑ r,
          (∑ a, ∑ b, ∑ c, Q i a * P b p * P c r * T a b c) *
            (∑ a, ∑ b, ∑ c, ∑ e,
              Q r a * P b j * P c k * star (P e q) * U a b c e)) =
      ∑ p, ∑ q, g' q p * ∑ c, X p c * Y q c := by
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    rw [hInner p q]
  let A : Fin n → Fin n → ℂ := fun b r =>
    ∑ a, Q i a * T a b r
  let B : Fin n → Fin n → ℂ := fun d r =>
    ∑ e, ∑ f, P e j * P f k * U r e f d
  have hX (p r : Fin n) : X p r = ∑ b, P b p * A b r := by
    dsimp [X, A]
    calc
      (∑ a, ∑ b, Q i a * P b p * T a b r) =
          ∑ b, ∑ a, Q i a * P b p * T a b r := Finset.sum_comm
      _ = ∑ b, P b p * (∑ a, Q i a * T a b r) := by
        apply Finset.sum_congr rfl
        intro b hb
        calc
          (∑ a, Q i a * P b p * T a b r) =
              ∑ a, P b p * (Q i a * T a b r) := by
            apply Finset.sum_congr rfl
            intro a ha
            ring
          _ = P b p * (∑ a, Q i a * T a b r) := by rw [← Finset.mul_sum]
  have hY (q r : Fin n) : Y q r = ∑ d, star (P d q) * B d r := by
    dsimp [Y, B]
    calc
      (∑ b, ∑ c, ∑ d, P b j * P c k * star (P d q) * U r b c d) =
          ∑ b, ∑ c, ∑ d, star (P d q) * (P b j * P c k * U r b c d) := by
        apply Finset.sum_congr rfl
        intro b hb
        apply Finset.sum_congr rfl
        intro c hc
        apply Finset.sum_congr rfl
        intro d hd
        ring
      _ = ∑ d, ∑ b, ∑ c, star (P d q) * (P b j * P c k * U r b c d) := by
        rw [referenceAction_sum_three_cycle, referenceAction_sum_three_cycle]
      _ = ∑ d, star (P d q) * (∑ b, ∑ c, P b j * P c k * U r b c d) := by
        apply Finset.sum_congr rfl
        intro d hd
        calc
          (∑ b, ∑ c, star (P d q) * (P b j * P c k * U r b c d)) =
              ∑ b, star (P d q) * (∑ c, P b j * P c k * U r b c d) := by
            apply Finset.sum_congr rfl
            intro b hb
            rw [← Finset.mul_sum]
          _ = star (P d q) * (∑ b, ∑ c, P b j * P c k * U r b c d) := by
            rw [← Finset.mul_sum]
  have hMetricAt (r : Fin n) :
      ∑ p, ∑ q, g' q p * X p r * Y q r =
        ∑ b, ∑ d, g d b * A b r * B d r := by
    calc
      (∑ p, ∑ q, g' q p * X p r * Y q r) =
          ∑ p, ∑ q, g' q p * (∑ b, P b p * A b r) *
            (∑ d, star (P d q) * B d r) := by
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro q hq
        rw [hX p r, hY q r]
      _ = ∑ b, ∑ d, g d b * A b r * B d r := by
        exact referenceAction_metric_contract_two_actions P g g' hmetric
          (fun b => A b r) (fun d => B d r)
  have hReorder :
      (∑ p, ∑ q, g' q p * ∑ c, X p c * Y q c) =
        ∑ c, ∑ p, ∑ q, g' q p * X p c * Y q c := by
    calc
      (∑ p, ∑ q, g' q p * ∑ c, X p c * Y q c) =
          ∑ p, ∑ q, ∑ c, g' q p * (X p c * Y q c) := by
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro q hq
        rw [Finset.mul_sum]
      _ = ∑ c, ∑ p, ∑ q, g' q p * (X p c * Y q c) := by
        rw [referenceAction_sum_three_cycle, referenceAction_sum_three_cycle]
      _ = ∑ c, ∑ p, ∑ q, g' q p * X p c * Y q c := by
        apply Finset.sum_congr rfl
        intro c hc
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro q hq
        ring
  have hFactor (p q r : Fin n) :
      ∑ b, ∑ c, ∑ a,
        Q i a * P b j * P c k * (g q p * (T a p r * U r b c q)) =
        g q p * (∑ a, Q i a * T a p r) *
          (∑ b, ∑ c, P b j * P c k * U r b c q) := by
    calc
      (∑ b, ∑ c, ∑ a,
        Q i a * P b j * P c k * (g q p * (T a p r * U r b c q))) =
        ∑ a, ∑ b, ∑ c,
          Q i a * P b j * P c k * (g q p * (T a p r * U r b c q)) := by
            rw [referenceAction_sum_three_cycle, referenceAction_sum_three_cycle]
      _ = g q p * (∑ a, Q i a * T a p r) *
            (∑ b, ∑ c, P b j * P c k * U r b c q) := by
        calc
          (∑ a, ∑ b, ∑ c,
            Q i a * P b j * P c k * (g q p * (T a p r * U r b c q))) =
              ∑ a, (Q i a * T a p r) *
                (g q p * ∑ b, ∑ c, P b j * P c k * U r b c q) := by
            apply Finset.sum_congr rfl
            intro a ha
            calc
              (∑ b, ∑ c,
                Q i a * P b j * P c k * (g q p * (T a p r * U r b c q))) =
                  ∑ b, ∑ c, (Q i a * T a p r * g q p) *
                    (P b j * P c k * U r b c q) := by
                apply Finset.sum_congr rfl
                intro b hb
                apply Finset.sum_congr rfl
                intro c hc
                ring
              _ = (Q i a * T a p r * g q p) *
                    (∑ b, ∑ c, P b j * P c k * U r b c q) := by
                calc
                  (∑ b, ∑ c, (Q i a * T a p r * g q p) *
                    (P b j * P c k * U r b c q)) =
                    ∑ b, (Q i a * T a p r * g q p) *
                      (∑ c, P b j * P c k * U r b c q) := by
                    apply Finset.sum_congr rfl
                    intro b hb
                    rw [← Finset.mul_sum]
                  _ = (Q i a * T a p r * g q p) *
                      (∑ b, ∑ c, P b j * P c k * U r b c q) := by
                    rw [← Finset.mul_sum]
              _ = (Q i a * T a p r) *
                    (g q p * ∑ b, ∑ c, P b j * P c k * U r b c q) := by
                ring
          _ = (∑ a, Q i a * T a p r) *
                (g q p * ∑ b, ∑ c, P b j * P c k * U r b c q) := by
            rw [Finset.sum_mul]
          _ = g q p * (∑ a, Q i a * T a p r) *
                (∑ b, ∑ c, P b j * P c k * U r b c q) := by
            ring
  have hSource :
      (∑ a, ∑ b, ∑ c, Q i a * P b j * P c k *
        ∑ p, ∑ q, g q p * ∑ r, T a p r * U r b c q) =
        ∑ r, ∑ p, ∑ q, g q p * A p r * B q r := by
    calc
      (∑ a, ∑ b, ∑ c, Q i a * P b j * P c k *
        ∑ p, ∑ q, g q p * ∑ r, T a p r * U r b c q) =
        ∑ a, ∑ b, ∑ c, ∑ p, ∑ q, ∑ r,
          Q i a * P b j * P c k * (g q p * (T a p r * U r b c q)) := by
        simp only [Finset.mul_sum]
      _ = ∑ r, ∑ p, ∑ q, ∑ b, ∑ c, ∑ a,
          Q i a * P b j * P c k * (g q p * (T a p r * U r b c q)) := by
        calc
          (∑ a, ∑ b, ∑ c, ∑ p, ∑ q, ∑ r,
            Q i a * P b j * P c k * (g q p * (T a p r * U r b c q))) =
              ∑ r, ∑ p, ∑ q, ∑ a, ∑ b, ∑ c,
                Q i a * P b j * P c k * (g q p * (T a p r * U r b c q)) := by
                  rw [referenceAction_sum_six_rotate]
          _ = ∑ r, ∑ p, ∑ q, ∑ b, ∑ c, ∑ a,
                Q i a * P b j * P c k * (g q p * (T a p r * U r b c q)) := by
            apply Finset.sum_congr rfl
            intro r hr
            apply Finset.sum_congr rfl
            intro p hp
            apply Finset.sum_congr rfl
            intro q hq
            rw [referenceAction_sum_three_cycle]
      _ = ∑ r, ∑ p, ∑ q, g q p * A p r * B q r := by
        apply Finset.sum_congr rfl
        intro r hr
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro q hq
        simpa [A, B] using hFactor p q r
  rw [hRight, hReorder]
  calc
    (∑ a, ∑ b, ∑ c, Q i a * P b j * P c k *
      ∑ p, ∑ q, g q p * ∑ r, T a p r * U r b c q) =
        ∑ r, ∑ p, ∑ q, g q p * A p r * B q r := hSource
    _ = ∑ r, ∑ p, ∑ q, g' q p * X p r * Y q r := by
      apply Finset.sum_congr rfl
      intro r hr
      exact (hMetricAt r).symm

end KahlerForm
