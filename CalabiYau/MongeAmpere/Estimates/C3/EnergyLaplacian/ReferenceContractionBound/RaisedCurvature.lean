module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceContractionBound.InverseContractions

/-!
# RaisedCurvature for the reference-curvature contraction

Székelyhidi, An Introduction to Extremal Kähler Metrics, §3.3, proof of Lemma 3.9, terms following (3.15), printed p. 45; finite tensor contraction algebra implementing that proof.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal BigOperators ComplexOrder MatrixOrder
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

theorem referenceContraction_raised_frame {n : ℕ}
    (P Q G₀ : Matrix (Fin n) (Fin n) ℂ)
    (R : Fin n → Fin n → Fin n → Fin n → ℂ)
    (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hframe : linearPullbackMetric P G₀ = 1) (i j k q : Fin n) :
    referenceAction_tauU P Q (fun a b c e => ∑ l, G₀⁻¹ l a * R b e c l) i j k q =
      referenceContractionFourSlotTransform P R j q k i := by
  classical
  have hraise (l : Fin n) :
      ∑ a, Q i a * G₀⁻¹ l a = star (P l i) := by
    have h := linear_pullback_reference_contraction P Q G₀ hPQ hQP i l
    rw [hframe] at h
    simpa [Matrix.one_apply] using h.symm
  unfold referenceAction_tauU referenceContractionFourSlotTransform
  calc
    (∑ a, ∑ b, ∑ c, ∑ e,
        Q i a * P b j * P c k * star (P e q) *
          (∑ l, G₀⁻¹ l a * R b e c l)) =
      ∑ a, ∑ b, ∑ c, ∑ e, ∑ l,
        Q i a * P b j * P c k * star (P e q) * G₀⁻¹ l a * R b e c l := by
          simp_rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          apply Finset.sum_congr rfl
          intro c hc
          apply Finset.sum_congr rfl
          intro e he
          apply Finset.sum_congr rfl
          intro l hl
          ring
    _ = ∑ b, ∑ c, ∑ e, ∑ l, ∑ a,
        Q i a * P b j * P c k * star (P e q) * G₀⁻¹ l a * R b e c l := by
          calc
            _ = ∑ b, ∑ a, ∑ c, ∑ e, ∑ l,
                Q i a * P b j * P c k * star (P e q) * G₀⁻¹ l a * R b e c l := by
                  rw [Finset.sum_comm]
            _ = ∑ b, ∑ c, ∑ a, ∑ e, ∑ l,
                Q i a * P b j * P c k * star (P e q) * G₀⁻¹ l a * R b e c l := by
                  apply Finset.sum_congr rfl
                  intro b hb
                  rw [Finset.sum_comm]
            _ = ∑ b, ∑ c, ∑ e, ∑ a, ∑ l,
                Q i a * P b j * P c k * star (P e q) * G₀⁻¹ l a * R b e c l := by
                  apply Finset.sum_congr rfl
                  intro b hb
                  apply Finset.sum_congr rfl
                  intro c hc
                  rw [Finset.sum_comm]
            _ = ∑ b, ∑ c, ∑ e, ∑ l, ∑ a,
                Q i a * P b j * P c k * star (P e q) * G₀⁻¹ l a * R b e c l := by
                  apply Finset.sum_congr rfl
                  intro b hb
                  apply Finset.sum_congr rfl
                  intro c hc
                  apply Finset.sum_congr rfl
                  intro e he
                  rw [Finset.sum_comm]
    _ = ∑ b, ∑ c, ∑ e, ∑ l,
        (∑ a, Q i a * G₀⁻¹ l a) * P b j * P c k * star (P e q) * R b e c l := by
          apply Finset.sum_congr rfl
          intro b hb
          apply Finset.sum_congr rfl
          intro c hc
          apply Finset.sum_congr rfl
          intro e he
          apply Finset.sum_congr rfl
          intro l hl
          calc
            (∑ a, Q i a * P b j * P c k * star (P e q) * G₀⁻¹ l a * R b e c l) =
                ∑ a, (Q i a * G₀⁻¹ l a) * (P b j * P c k * star (P e q) * R b e c l) := by
                  apply Finset.sum_congr rfl
                  intro a ha
                  ring
            _ = (∑ a, Q i a * G₀⁻¹ l a) *
                (P b j * P c k * star (P e q) * R b e c l) := by
                  rw [Finset.sum_mul]
            _ = (∑ a, Q i a * G₀⁻¹ l a) * P b j * P c k *
                star (P e q) * R b e c l := by ring
    _ = ∑ b, ∑ e, ∑ c, ∑ l,
        star (P l i) * P b j * P c k * star (P e q) * R b e c l := by
          simp_rw [hraise]
          apply Finset.sum_congr rfl
          intro b hb
          rw [Finset.sum_comm]
    _ = ∑ b, ∑ e, ∑ c, ∑ l,
        P b j * star (P e q) * P c k * star (P l i) * R b e c l := by
          apply Finset.sum_congr rfl
          intro b hb
          apply Finset.sum_congr rfl
          intro e he
          apply Finset.sum_congr rfl
          intro c hc
          apply Finset.sum_congr rfl
          intro l hl
          ring

end KahlerForm
