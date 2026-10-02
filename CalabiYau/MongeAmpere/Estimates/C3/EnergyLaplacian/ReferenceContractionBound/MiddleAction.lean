module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceContractionBound.ActionContractions

/-!
# MiddleAction for the reference-curvature contraction

Székelyhidi, An Introduction to Extremal Kähler Metrics, §3.3, proof of Lemma 3.9, terms following (3.15), printed p. 45; finite tensor contraction algebra implementing that proof.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal BigOperators ComplexOrder MatrixOrder
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

theorem referenceAction_minus_j_action_covariance {n : ℕ}
    (P Q g g' : Matrix (Fin n) (Fin n) ℂ)
    (T : Fin n → Fin n → Fin n → ℂ)
    (U : Fin n → Fin n → Fin n → Fin n → ℂ)
    (hPQ : P * Q = 1)
    (hmetric : ∀ s u, ∑ p, ∑ q, g' q p * P s p * star (P u q) = g u s) :
    ∀ i j k, referenceAction_tauT P Q (referenceAction_minusJPart g T U) i j k =
      referenceAction_minusJPart g' (referenceAction_tauT P Q T) (referenceAction_tauU P Q U) i j k := by
  classical
  intro i j k
  simp only [referenceAction_tauT, referenceAction_tauU, referenceAction_minusJPart]
  let X : Fin n → Fin n → ℂ := fun p a =>
    ∑ b, ∑ c, P b p * P c j * T a b c
  let Y : Fin n → Fin n → ℂ := fun q a =>
    ∑ c, ∑ d, ∑ e, Q i c * P d k * star (P e q) * U c a d e
  let A : Fin n → Fin n → ℂ := fun b r =>
    ∑ c, P c j * T r b c
  let B : Fin n → Fin n → ℂ := fun e r =>
    ∑ c, ∑ d, Q i c * P d k * U c r d e
  have hT (r p : Fin n) :
      (∑ a, ∑ b, ∑ c, Q r a * P b p * P c j * T a b c) =
        ∑ a, Q r a * X p a := by
    dsimp [X]
    simpa only [mul_assoc] using
      (referenceAction_pullback_upper_action3 Q (fun a b c => P b p * P c j * T a b c) r)
  have hU (r q : Fin n) :
      (∑ a, ∑ b, ∑ c, ∑ e,
        Q i a * P b r * P c k * star (P e q) * U a b c e) =
        ∑ b, P b r * Y q b := by
    calc
      (∑ a, ∑ b, ∑ c, ∑ e,
        Q i a * P b r * P c k * star (P e q) * U a b c e) =
        ∑ a, ∑ b, ∑ c, ∑ e,
          (Q i a * P c k * star (P e q) * U a b c e) * P b r := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        apply Finset.sum_congr rfl
        intro c hc
        apply Finset.sum_congr rfl
        intro e he
        ring
      _ = ∑ b, P b r * ∑ a, ∑ c, ∑ e,
          Q i a * P c k * star (P e q) * U a b c e := by
        apply referenceAction_pullback_lower_action_middle P
          (fun a c e b => Q i a * P c k * star (P e q) * U a b c e) r
      _ = ∑ b, P b r * Y q b := by rfl
  have hInner (p q : Fin n) :
      (∑ r,
        (∑ a, ∑ b, ∑ c, Q r a * P b p * P c j * T a b c) *
        (∑ a, ∑ b, ∑ c, ∑ e,
          Q i a * P b r * P c k * star (P e q) * U a b c e)) =
        ∑ a, X p a * Y q a := by
    calc
      _ = ∑ r, (∑ a, Q r a * X p a) * (∑ b, P b r * Y q b) := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [hT r p, hU r q]
      _ = ∑ a, X p a * Y q a :=
        referenceAction_pullback_tensor_contract_upper_lower P Q hPQ (fun a => X p a) (fun a => Y q a)
  have hRight :
      (∑ p, ∑ q, g' q p * ∑ r,
        (∑ a, ∑ b, ∑ c, Q r a * P b p * P c j * T a b c) *
        (∑ a, ∑ b, ∑ c, ∑ e,
          Q i a * P b r * P c k * star (P e q) * U a b c e)) =
        ∑ p, ∑ q, g' q p * ∑ a, X p a * Y q a := by
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    rw [hInner p q]
  have hX (p r : Fin n) : X p r = ∑ b, P b p * (∑ c, P c j * T r b c) := by
    dsimp [X]
    apply Finset.sum_congr rfl
    intro b hb
    calc
      (∑ c, P b p * P c j * T r b c) =
          ∑ c, P b p * (P c j * T r b c) := by
        apply Finset.sum_congr rfl
        intro c hc
        ring
      _ = P b p * (∑ c, P c j * T r b c) := by rw [← Finset.mul_sum]
  have hY (q r : Fin n) : Y q r =
      ∑ e, star (P e q) * (∑ c, ∑ d, Q i c * P d k * U c r d e) := by
    dsimp [Y]
    calc
      (∑ c, ∑ d, ∑ e, Q i c * P d k * star (P e q) * U c r d e) =
        ∑ c, ∑ d, ∑ e, star (P e q) * (Q i c * P d k * U c r d e) := by
        apply Finset.sum_congr rfl
        intro c hc
        apply Finset.sum_congr rfl
        intro d hd
        apply Finset.sum_congr rfl
        intro e he
        ring
      _ = ∑ e, ∑ c, ∑ d, star (P e q) * (Q i c * P d k * U c r d e) := by
        rw [referenceAction_sum_three_cycle, referenceAction_sum_three_cycle]
      _ = ∑ e, star (P e q) * (∑ c, ∑ d, Q i c * P d k * U c r d e) := by
        apply Finset.sum_congr rfl
        intro e he
        calc
          (∑ c, ∑ d, star (P e q) * (Q i c * P d k * U c r d e)) =
              ∑ c, star (P e q) * (∑ d, Q i c * P d k * U c r d e) := by
            apply Finset.sum_congr rfl
            intro c hc
            rw [← Finset.mul_sum]
          _ = star (P e q) * (∑ c, ∑ d, Q i c * P d k * U c r d e) := by
            rw [← Finset.mul_sum]
  have hMetricAt (r : Fin n) :
      ∑ p, ∑ q, g' q p * X p r * Y q r =
        ∑ b, ∑ e, g e b * A b r * B e r := by
    calc
      (∑ p, ∑ q, g' q p * X p r * Y q r) =
          ∑ p, ∑ q, g' q p * (∑ b, P b p * (∑ c, P c j * T r b c)) *
            (∑ e, star (P e q) * (∑ c, ∑ d, Q i c * P d k * U c r d e)) := by
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro q hq
        rw [hX p r, hY q r]
      _ = ∑ b, ∑ e, g e b * A b r * B e r := by
        simpa [A, B] using referenceAction_metric_contract_two_actions P g g' hmetric
          (fun b => ∑ c, P c j * T r b c)
          (fun e => ∑ c, ∑ d, Q i c * P d k * U c r d e)
  have hscalar : ∀ (C : ℂ) (F : Fin n → ℂ),
      (∑ a, C * F a) = C * (∑ a, F a) := by
    intro C F
    symm
    apply Finset.mul_sum
  have hFactor (p q r : Fin n) :
      ∑ b, ∑ c, ∑ a,
        Q i a * P b j * P c k * (g q p * (T r p b * U a r c q)) =
        g q p * (∑ b, P b j * T r p b) *
          (∑ a, ∑ c, Q i a * P c k * U a r c q) := by
    calc
      (∑ b, ∑ c, ∑ a,
        Q i a * P b j * P c k * (g q p * (T r p b * U a r c q))) =
        ∑ a, ∑ b, ∑ c,
          Q i a * P b j * P c k * (g q p * (T r p b * U a r c q)) := by
            rw [referenceAction_sum_three_cycle, referenceAction_sum_three_cycle]
      _ = g q p * (∑ b, P b j * T r p b) *
          (∑ a, ∑ c, Q i a * P c k * U a r c q) := by
        calc
          (∑ a, ∑ b, ∑ c,
            Q i a * P b j * P c k * (g q p * (T r p b * U a r c q))) =
            ∑ a, ∑ b, ∑ c,
              (g q p * (P b j * T r p b)) *
                (Q i a * P c k * U a r c q) := by
              apply Finset.sum_congr rfl
              intro a ha
              apply Finset.sum_congr rfl
              intro b hb
              apply Finset.sum_congr rfl
              intro c hc
              ring
          _ = ∑ a, (g q p * (∑ b, P b j * T r p b)) *
                (∑ c, Q i a * P c k * U a r c q) := by
              apply Finset.sum_congr rfl
              intro a ha
              calc
                (∑ b, ∑ c,
                  (g q p * (P b j * T r p b)) *
                    (Q i a * P c k * U a r c q)) =
                  ∑ b, (g q p * (P b j * T r p b)) *
                    (∑ c, Q i a * P c k * U a r c q) := by
                    apply Finset.sum_congr rfl
                    intro b hb
                    rw [← Finset.mul_sum]
                _ = (∑ b, g q p * (P b j * T r p b)) *
                    (∑ c, Q i a * P c k * U a r c q) := by
                    rw [Finset.sum_mul]
                _ = (g q p * (∑ b, P b j * T r p b)) *
                      (∑ c, Q i a * P c k * U a r c q) := by
                  let C : ℂ := ∑ c, Q i a * P c k * U a r c q
                  change (∑ b, g q p * (P b j * T r p b)) * C =
                    (g q p * (∑ b, P b j * T r p b)) * C
                  exact congrArg (fun z : ℂ => z * C) (by rw [← Finset.mul_sum])
          _ = g q p * (∑ b, P b j * T r p b) *
              (∑ a, ∑ c, Q i a * P c k * U a r c q) := by
            exact hscalar (g q p * ∑ b, P b j * T r p b)
              (fun a => ∑ c, Q i a * P c k * U a r c q)
  have hSource :
      (∑ a, ∑ b, ∑ c, Q i a * P b j * P c k *
        ∑ p, ∑ q, g q p * ∑ r, T r p b * U a r c q) =
        ∑ r, ∑ p, ∑ q, g q p *
          (∑ b, P b j * T r p b) *
          (∑ a, ∑ c, Q i a * P c k * U a r c q) := by
    calc
      (∑ a, ∑ b, ∑ c, Q i a * P b j * P c k *
        ∑ p, ∑ q, g q p * ∑ r, T r p b * U a r c q) =
        ∑ a, ∑ b, ∑ c, ∑ p, ∑ q, ∑ r,
          Q i a * P b j * P c k * (g q p * (T r p b * U a r c q)) := by
        simp only [Finset.mul_sum]
      _ = ∑ r, ∑ p, ∑ q, ∑ b, ∑ c, ∑ a,
          Q i a * P b j * P c k * (g q p * (T r p b * U a r c q)) := by
        calc
          (∑ a, ∑ b, ∑ c, ∑ p, ∑ q, ∑ r,
            Q i a * P b j * P c k * (g q p * (T r p b * U a r c q))) =
            ∑ r, ∑ p, ∑ q, ∑ a, ∑ b, ∑ c,
              Q i a * P b j * P c k * (g q p * (T r p b * U a r c q)) := by
                rw [referenceAction_sum_six_rotate]
          _ = ∑ r, ∑ p, ∑ q, ∑ b, ∑ c, ∑ a,
              Q i a * P b j * P c k * (g q p * (T r p b * U a r c q)) := by
            apply Finset.sum_congr rfl
            intro r hr
            apply Finset.sum_congr rfl
            intro p hp
            apply Finset.sum_congr rfl
            intro q hq
            rw [referenceAction_sum_three_cycle]
      _ = ∑ r, ∑ p, ∑ q, g q p *
          (∑ b, P b j * T r p b) *
          (∑ a, ∑ c, Q i a * P c k * U a r c q) := by
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
      ∑ p, ∑ q, g q p * ∑ r, T r p b * U a r c q) =
      ∑ r, ∑ p, ∑ q, g q p *
        (∑ b, P b j * T r p b) *
        (∑ a, ∑ c, Q i a * P c k * U a r c q) := hSource
    _ = ∑ r, ∑ p, ∑ q, g' q p * X p r * Y q r := by
      apply Finset.sum_congr rfl
      intro r hr
      exact (hMetricAt r).symm

end KahlerForm
