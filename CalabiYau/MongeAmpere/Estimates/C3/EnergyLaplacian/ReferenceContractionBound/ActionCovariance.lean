module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceContractionBound.PositiveAction
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceContractionBound.MiddleAction
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceContractionBound.LastAction

/-!
# ActionCovariance for the reference-curvature contraction

Székelyhidi, An Introduction to Extremal Kähler Metrics, §3.3, proof of Lemma 3.9, terms following (3.15), printed p. 45; finite tensor contraction algebra implementing that proof.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal BigOperators ComplexOrder MatrixOrder
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

@[deprecated "unused hypothesis `hQP`; will be removed" (since := "2026-10-02")]
theorem referenceAction_action_covariance {n : ℕ}
    (P Q g g' : Matrix (Fin n) (Fin n) ℂ)
    (T : Fin n → Fin n → Fin n → ℂ)
    (U : Fin n → Fin n → Fin n → Fin n → ℂ)
    (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hmetric : ∀ s u, ∑ p, ∑ q, g' q p * P s p * star (P u q) = g u s) :
    ∀ i j k, referenceAction_tauT P Q (referenceAction_contract g T U) i j k =
      referenceAction_contract g' (referenceAction_tauT P Q T) (referenceAction_tauU P Q U) i j k := by
  classical
  intro i j k
  have hparts (g0 : Matrix (Fin n) (Fin n) ℂ)
      (T0 : Fin n → Fin n → Fin n → ℂ)
      (U0 : Fin n → Fin n → Fin n → Fin n → ℂ) :
      referenceAction_contract g0 T0 U0 =
        (referenceAction_plusPart g0 T0 U0 - referenceAction_minusJPart g0 T0 U0) - referenceAction_minusKPart g0 T0 U0 := by
    funext a b c
    change
      (∑ p, ∑ q, g0 q p *
        ((∑ r, T0 a p r * U0 r b c q) -
         (∑ r, T0 r p b * U0 a r c q) -
         (∑ r, T0 r p c * U0 a b r q))) =
      ((∑ p, ∑ q, g0 q p * ∑ r, T0 a p r * U0 r b c q) -
       (∑ p, ∑ q, g0 q p * ∑ r, T0 r p b * U0 a r c q)) -
       ∑ p, ∑ q, g0 q p * ∑ r, T0 r p c * U0 a b r q
    calc
      _ = ∑ p, ∑ q,
          ((g0 q p * ∑ r, T0 a p r * U0 r b c q) -
           (g0 q p * ∑ r, T0 r p b * U0 a r c q) -
           (g0 q p * ∑ r, T0 r p c * U0 a b r q)) := by
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro q hq
        ring
      _ = _ := by simp only [Finset.sum_sub_distrib]
  have hlinear (F G H : Fin n → Fin n → Fin n → ℂ) :
      referenceAction_tauT P Q (fun a b c => F a b c - G a b c - H a b c) =
        (referenceAction_tauT P Q F - referenceAction_tauT P Q G) - referenceAction_tauT P Q H := by
    funext a b c
    change
      (∑ x, ∑ y, ∑ z, Q a x * P y b * P z c *
        (F x y z - G x y z - H x y z)) =
      ((∑ x, ∑ y, ∑ z, Q a x * P y b * P z c * F x y z) -
       (∑ x, ∑ y, ∑ z, Q a x * P y b * P z c * G x y z)) -
       ∑ x, ∑ y, ∑ z, Q a x * P y b * P z c * H x y z
    simp only [Finset.sum_sub_distrib, mul_sub]
  have hplus := referenceAction_plus_action_covariance P Q g g' T U hPQ hmetric i j k
  have hj := referenceAction_minus_j_action_covariance P Q g g' T U hPQ hmetric i j k
  have hk := referenceAction_minus_k_action_covariance P Q g g' T U hPQ hmetric i j k
  rw [hparts g T U]
  change referenceAction_tauT P Q
    (fun a b c => referenceAction_plusPart g T U a b c - referenceAction_minusJPart g T U a b c -
      referenceAction_minusKPart g T U a b c) i j k = _
  rw [hlinear (referenceAction_plusPart g T U) (referenceAction_minusJPart g T U) (referenceAction_minusKPart g T U)]
  change
    (referenceAction_tauT P Q (referenceAction_plusPart g T U) i j k -
      referenceAction_tauT P Q (referenceAction_minusJPart g T U) i j k) -
      referenceAction_tauT P Q (referenceAction_minusKPart g T U) i j k = _
  rw [hplus, hj, hk]
  rw [hparts g' (referenceAction_tauT P Q T) (referenceAction_tauU P Q U)]
  rfl

end KahlerForm
