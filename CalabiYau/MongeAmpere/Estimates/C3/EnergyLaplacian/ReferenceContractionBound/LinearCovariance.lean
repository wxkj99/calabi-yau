module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceContractionBound.DerivativeContraction
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceContractionBound.LaplacianContraction

/-!
# LinearCovariance for the reference-curvature contraction

Székelyhidi, An Introduction to Extremal Kähler Metrics, §3.3, proof of Lemma 3.9, terms following (3.15), printed p. 45; finite tensor contraction algebra implementing that proof.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal BigOperators ComplexOrder MatrixOrder
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

set_option maxHeartbeats 1000000 in
lemma linear_contract_both_five {n : ℕ}
    (P Q G₀ G : Matrix (Fin n) (Fin n) ℂ)
    (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (D : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ)
    (i j k : Fin n) :
    ∑ p, ∑ q, ∑ l,
      (linearPullbackMetric P G)⁻¹ q p *
        (linearPullbackMetric P G₀)⁻¹ l i *
        linearPullbackFiveTensor P D p j q k l =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ t,
        Q i t * G⁻¹ c a * P b j * P d k * G₀⁻¹ e t * D a b c d e := by
  calc
    ∑ p, ∑ q, ∑ l,
      (linearPullbackMetric P G)⁻¹ q p *
        (linearPullbackMetric P G₀)⁻¹ l i *
        linearPullbackFiveTensor P D p j q k l =
      ∑ l, (linearPullbackMetric P G₀)⁻¹ l i *
        (∑ p, ∑ q, (linearPullbackMetric P G)⁻¹ q p *
          linearPullbackFiveTensor P D p j q k l) := by
            calc
              _ = ∑ p, ∑ q, ∑ l,
                    ((linearPullbackMetric P G)⁻¹ q p *
                      linearPullbackFiveTensor P D p j q k l) *
                      (linearPullbackMetric P G₀)⁻¹ l i := by
                    apply Finset.sum_congr rfl
                    intro p hp
                    apply Finset.sum_congr rfl
                    intro q hq
                    apply Finset.sum_congr rfl
                    intro l hl
                    ring
              _ = ∑ l, ∑ p, ∑ q,
                    ((linearPullbackMetric P G)⁻¹ q p *
                      linearPullbackFiveTensor P D p j q k l) *
                      (linearPullbackMetric P G₀)⁻¹ l i :=
                    sum_three_reorder_test (fun p q l =>
                      ((linearPullbackMetric P G)⁻¹ q p *
                        linearPullbackFiveTensor P D p j q k l) *
                        (linearPullbackMetric P G₀)⁻¹ l i)
              _ = ∑ l, (linearPullbackMetric P G₀)⁻¹ l i *
                    (∑ p, ∑ q, (linearPullbackMetric P G)⁻¹ q p *
                      linearPullbackFiveTensor P D p j q k l) := by
                    apply Finset.sum_congr rfl
                    intro l hl
                    calc
                      _ = (∑ p, ∑ q, (linearPullbackMetric P G)⁻¹ q p *
                            linearPullbackFiveTensor P D p j q k l) *
                            (linearPullbackMetric P G₀)⁻¹ l i := by
                              rw [Finset.sum_mul]
                              apply Finset.sum_congr rfl
                              intro p hp
                              rw [Finset.sum_mul]
                      _ = _ := by rw [mul_comm]
    _ = ∑ l, (linearPullbackMetric P G₀)⁻¹ l i *
          (∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
            G⁻¹ c a * P b j * P d k * star (P e l) * D a b c d e) := by
            apply Finset.sum_congr rfl
            intro l hl
            rw [linear_contract_first_five P Q G hPQ hQP D j k l]
    _ = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ t,
          Q i t * G⁻¹ c a * P b j * P d k * G₀⁻¹ e t * D a b c d e :=
            linear_contract_reference_five P Q G₀ G hPQ hQP D i j k

lemma sum_transform_drift_order {n : ℕ}
    (F : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ p, ∑ q, ∑ l, F a b c p q l) =
      ∑ p, ∑ b, ∑ q, ∑ c, ∑ l, ∑ a, F a b c p q l := by
  calc
    (∑ a, ∑ b, ∑ c, ∑ p, ∑ q, ∑ l, F a b c p q l) =
        ∑ b, ∑ c, ∑ p, ∑ q, ∑ l, ∑ a, F a b c p q l :=
          sum_one_move_over_five (fun a b c p q l => F a b c p q l)
    _ = ∑ p, ∑ b, ∑ c, ∑ q, ∑ l, ∑ a, F a b c p q l :=
          sum_three_reorder_test (fun b c p => ∑ q, ∑ l, ∑ a, F a b c p q l)
    _ = ∑ p, ∑ b, ∑ q, ∑ c, ∑ l, ∑ a, F a b c p q l := by
          apply Finset.sum_congr rfl
          intro p hp
          apply Finset.sum_congr rfl
          intro b hb
          exact Finset.sum_comm

lemma linear_transform_drift_expand {n : ℕ}
    (P Q G₀ G : Matrix (Fin n) (Fin n) ℂ)
    (D : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ)
    (i j k : Fin n) :
    linearPullbackThreeTensor P Q (linearReferenceDrift G₀ G D) i j k =
      ∑ p, ∑ b, ∑ q, ∑ c, ∑ l, ∑ a,
        Q i a * P b j * P c k * G⁻¹ q p * G₀⁻¹ l a * D p b q c l := by
  unfold linearPullbackThreeTensor linearReferenceDrift
  calc
    (∑ a, ∑ b, ∑ c, Q i a * P b j * P c k *
        (∑ p, ∑ q, ∑ l, G⁻¹ q p * G₀⁻¹ l a * D p b q c l)) =
      ∑ a, ∑ b, ∑ c, ∑ p, ∑ q, ∑ l,
        Q i a * P b j * P c k * G⁻¹ q p * G₀⁻¹ l a * D p b q c l := by
          simp_rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          apply Finset.sum_congr rfl
          intro c hc
          apply Finset.sum_congr rfl
          intro p hp
          apply Finset.sum_congr rfl
          intro q hq
          apply Finset.sum_congr rfl
          intro l hl
          ring
    _ = ∑ p, ∑ b, ∑ q, ∑ c, ∑ l, ∑ a,
        Q i a * P b j * P c k * G⁻¹ q p * G₀⁻¹ l a * D p b q c l :=
          sum_transform_drift_order
            (fun a b c p q l =>
              Q i a * P b j * P c k * G⁻¹ q p * G₀⁻¹ l a * D p b q c l)

/-- The linear reference-covariant-curvature derivative contraction is natural under
arbitrary coordinate changes: both inverse-metric contractions cancel the transformed slots. -/
theorem linearReferenceDrift_pullback_covariant {n : ℕ}
    (P Q G₀ G : Matrix (Fin n) (Fin n) ℂ)
    (D : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ)
    (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (i j k : Fin n) :
    linearPullbackThreeTensor P Q (linearReferenceDrift G₀ G D) i j k =
      linearReferenceDrift (linearPullbackMetric P G₀) (linearPullbackMetric P G)
        (linearPullbackFiveTensor P D) i j k := by
  classical
  rw [linear_transform_drift_expand P Q G₀ G D i j k]
  change (∑ p, ∑ b, ∑ q, ∑ c, ∑ l, ∑ a,
      Q i a * P b j * P c k * G⁻¹ q p * G₀⁻¹ l a * D p b q c l) =
    ∑ p, ∑ q, ∑ l,
      (linearPullbackMetric P G)⁻¹ q p *
        (linearPullbackMetric P G₀)⁻¹ l i *
        linearPullbackFiveTensor P D p j q k l
  rw [linear_contract_both_five P Q G₀ G hPQ hQP D i j k]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  ring

end KahlerForm
