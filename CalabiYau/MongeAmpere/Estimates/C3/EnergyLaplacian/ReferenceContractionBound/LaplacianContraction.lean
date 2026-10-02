module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceContractionBound.InverseContractions
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceContractionBound.FiniteSums

/-!
# LaplacianContraction for the reference-curvature contraction

Székelyhidi, An Introduction to Extremal Kähler Metrics, §3.3, proof of Lemma 3.9, terms following (3.15), printed p. 45; finite tensor contraction algebra implementing that proof.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal BigOperators ComplexOrder MatrixOrder
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

lemma linear_contract_first_five {n : ℕ}
    (P Q G : Matrix (Fin n) (Fin n) ℂ)
    (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (D : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ)
    (j k l : Fin n) :
    ∑ p, ∑ q, (linearPullbackMetric P G)⁻¹ q p *
      linearPullbackFiveTensor P D p j q k l =
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
      G⁻¹ c a * P b j * P d k * star (P e l) * D a b c d e := by
  let H := linearPullbackMetric P G
  have hExpand (p q : Fin n) :
      H⁻¹ q p * linearPullbackFiveTensor P D p j q k l =
        ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
          H⁻¹ q p * P a p * P b j * star (P c q) * P d k * star (P e l) *
            D a b c d e := by
    rw [linearPullbackFiveTensor]
    simp_rw [Finset.mul_sum, mul_assoc]
  have hterm (a b c d e : Fin n) :
      ∑ p, ∑ q, H⁻¹ q p * P a p * P b j * star (P c q) *
          P d k * star (P e l) * D a b c d e =
        G⁻¹ c a * P b j * P d k * star (P e l) * D a b c d e := by
    calc
      ∑ p, ∑ q, H⁻¹ q p * P a p * P b j * star (P c q) *
          P d k * star (P e l) * D a b c d e =
        ∑ p, ∑ q, (H⁻¹ q p * P a p * star (P c q)) *
          (P b j * P d k * star (P e l) * D a b c d e) := by
            apply Finset.sum_congr rfl
            intro p hp
            apply Finset.sum_congr rfl
            intro q hq
            ring
      _ = (∑ p, ∑ q, H⁻¹ q p * P a p * star (P c q)) *
          (P b j * P d k * star (P e l) * D a b c d e) := by
            calc
              _ = ∑ p, (∑ q, H⁻¹ q p * P a p * star (P c q)) *
                    (P b j * P d k * star (P e l) * D a b c d e) := by
                      apply Finset.sum_congr rfl
                      intro p hp
                      rw [← Finset.sum_mul]
              _ = _ := by rw [← Finset.sum_mul]
      _ = G⁻¹ c a * P b j * P d k * star (P e l) * D a b c d e := by
            rw [linear_pullback_first_contraction P Q G hPQ hQP a c]
            ring
  calc
    ∑ p, ∑ q, H⁻¹ q p * linearPullbackFiveTensor P D p j q k l =
        ∑ p, ∑ q, ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
          H⁻¹ q p * P a p * P b j * star (P c q) * P d k * star (P e l) *
            D a b c d e := by
              apply Finset.sum_congr rfl
              intro p hp
              apply Finset.sum_congr rfl
              intro q hq
              exact hExpand p q
    _ = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ p, ∑ q,
          H⁻¹ q p * P a p * P b j * star (P c q) * P d k * star (P e l) *
            D a b c d e := by
              exact sum_two_move_over_five
                (fun p q a b c d e =>
                  H⁻¹ q p * P a p * P b j * star (P c q) * P d k * star (P e l) *
                    D a b c d e)
    _ = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
          G⁻¹ c a * P b j * P d k * star (P e l) * D a b c d e := by
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
