module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceContractionBound.InverseContractions
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceContractionBound.FiniteSums

/-!
# DerivativeContraction for the reference-curvature contraction

Székelyhidi, An Introduction to Extremal Kähler Metrics, §3.3, proof of Lemma 3.9, terms following (3.15), printed p. 45; finite tensor contraction algebra implementing that proof.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal BigOperators ComplexOrder MatrixOrder
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

lemma linear_contract_reference_five {n : ℕ}
    (P Q G₀ G : Matrix (Fin n) (Fin n) ℂ)
    (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (D : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ)
    (i j k : Fin n) :
    ∑ l, (linearPullbackMetric P G₀)⁻¹ l i *
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
        G⁻¹ c a * P b j * P d k * star (P e l) * D a b c d e) =
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ t,
      Q i t * G⁻¹ c a * P b j * P d k * G₀⁻¹ e t * D a b c d e := by
  let H := linearPullbackMetric P G₀
  have hterm (a b c d e : Fin n) :
      ∑ l, H⁻¹ l i * (G⁻¹ c a * P b j * P d k * star (P e l) * D a b c d e) =
        ∑ t, Q i t * G⁻¹ c a * P b j * P d k * G₀⁻¹ e t * D a b c d e := by
    calc
      ∑ l, H⁻¹ l i * (G⁻¹ c a * P b j * P d k * star (P e l) * D a b c d e) =
          (∑ l, H⁻¹ l i * star (P e l)) *
            (G⁻¹ c a * P b j * P d k * D a b c d e) := by
              calc
                _ = ∑ l, (H⁻¹ l i * star (P e l)) *
                      (G⁻¹ c a * P b j * P d k * D a b c d e) := by
                        apply Finset.sum_congr rfl
                        intro l hl
                        ring
                _ = _ := by rw [← Finset.sum_mul]
      _ = ∑ t, Q i t * G⁻¹ c a * P b j * P d k * G₀⁻¹ e t * D a b c d e := by
            rw [linear_pullback_reference_contraction P Q G₀ hPQ hQP i e]
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro t ht
            ring
  calc
    ∑ l, H⁻¹ l i *
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
        G⁻¹ c a * P b j * P d k * star (P e l) * D a b c d e) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ l,
        H⁻¹ l i * G⁻¹ c a * P b j * P d k * star (P e l) * D a b c d e := by
          calc
            _ = ∑ l, ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
                H⁻¹ l i * G⁻¹ c a * P b j * P d k * star (P e l) * D a b c d e := by
                  apply Finset.sum_congr rfl
                  intro l hl
                  simp_rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro a ha
                  apply Finset.sum_congr rfl
                  intro b hb
                  apply Finset.sum_congr rfl
                  intro c hc
                  apply Finset.sum_congr rfl
                  intro d hd
                  apply Finset.sum_congr rfl
                  intro e he
                  ring
            _ = _ := sum_one_move_over_five
              (fun l a b c d e => H⁻¹ l i * G⁻¹ c a * P b j * P d k * star (P e l) *
                D a b c d e)
    _ = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ t,
          Q i t * G⁻¹ c a * P b j * P d k * G₀⁻¹ e t * D a b c d e := by
            apply Finset.sum_congr rfl
            intro a ha
            apply Finset.sum_congr rfl
            intro b hb
            apply Finset.sum_congr rfl
            intro c hc
            apply Finset.sum_congr rfl
            intro d hd
            apply Finset.sum_congr rfl
            intro e he
            simpa only [mul_assoc] using hterm a b c d e

end KahlerForm
