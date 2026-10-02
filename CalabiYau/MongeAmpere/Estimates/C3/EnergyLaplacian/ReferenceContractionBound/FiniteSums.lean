module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceContractionBound.Basic

/-!
# FiniteSums for the reference-curvature contraction

Székelyhidi, An Introduction to Extremal Kähler Metrics, §3.3, proof of Lemma 3.9, terms following (3.15), printed p. 45; finite tensor contraction algebra implementing that proof.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal BigOperators ComplexOrder MatrixOrder
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

lemma sum_three_reorder_test {n : ℕ}
    (T : Fin n → Fin n → Fin n → ℂ) :
    (∑ p, ∑ q, ∑ a, T p q a) = ∑ a, ∑ p, ∑ q, T p q a := by
  calc
    (∑ p, ∑ q, ∑ a, T p q a) =
        ∑ p, ∑ z : Fin n × Fin n, T p z.1 z.2 := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [← Fintype.sum_prod_type']
    _ = ∑ z : Fin n × Fin n, ∑ p, T p z.1 z.2 := Finset.sum_comm
    _ = ∑ q, ∑ a, ∑ p, T p q a := by
          rw [Fintype.sum_prod_type]
    _ = ∑ a, ∑ p, ∑ q, T p q a := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a ha
          exact Finset.sum_comm

lemma sum_two_move_over_five {n : ℕ}
    (T : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ p, ∑ q, ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, T p q a b c d e) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ p, ∑ q, T p q a b c d e := by
  calc
    (∑ p, ∑ q, ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, T p q a b c d e) =
        ∑ a, ∑ p, ∑ q, ∑ b, ∑ c, ∑ d, ∑ e, T p q a b c d e :=
          sum_three_reorder_test (fun p q a => ∑ b, ∑ c, ∑ d, ∑ e, T p q a b c d e)
    _ = ∑ a, ∑ b, ∑ p, ∑ q, ∑ c, ∑ d, ∑ e, T p q a b c d e := by
          apply Finset.sum_congr rfl
          intro a ha
          exact sum_three_reorder_test (fun p q b => ∑ c, ∑ d, ∑ e, T p q a b c d e)
    _ = ∑ a, ∑ b, ∑ c, ∑ p, ∑ q, ∑ d, ∑ e, T p q a b c d e := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          exact sum_three_reorder_test (fun p q c => ∑ d, ∑ e, T p q a b c d e)
    _ = ∑ a, ∑ b, ∑ c, ∑ d, ∑ p, ∑ q, ∑ e, T p q a b c d e := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          apply Finset.sum_congr rfl
          intro c hc
          exact sum_three_reorder_test (fun p q d => ∑ e, T p q a b c d e)
    _ = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ p, ∑ q, T p q a b c d e := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          apply Finset.sum_congr rfl
          intro c hc
          apply Finset.sum_congr rfl
          intro d hd
          exact sum_three_reorder_test (fun p q e => T p q a b c d e)

lemma sum_one_move_over_five {n : ℕ}
    (T : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ l, ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, T l a b c d e) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ l, T l a b c d e := by
  calc
    (∑ l, ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, T l a b c d e) =
        ∑ a, ∑ l, ∑ b, ∑ c, ∑ d, ∑ e, T l a b c d e := Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ l, ∑ c, ∑ d, ∑ e, T l a b c d e := by
          apply Finset.sum_congr rfl
          intro a ha
          exact Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ c, ∑ l, ∑ d, ∑ e, T l a b c d e := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          exact Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ c, ∑ d, ∑ l, ∑ e, T l a b c d e := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          apply Finset.sum_congr rfl
          intro c hc
          exact Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ l, T l a b c d e := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          apply Finset.sum_congr rfl
          intro c hc
          apply Finset.sum_congr rfl
          intro d hd
          exact Finset.sum_comm

end KahlerForm
