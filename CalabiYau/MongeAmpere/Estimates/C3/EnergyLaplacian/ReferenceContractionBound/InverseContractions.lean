module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceContractionBound.Basic

/-!
# InverseContractions for the reference-curvature contraction

Székelyhidi, An Introduction to Extremal Kähler Metrics, §3.3, proof of Lemma 3.9, terms following (3.15), printed p. 45; finite tensor contraction algebra implementing that proof.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal BigOperators ComplexOrder MatrixOrder
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

theorem linear_pullback_metric_inverse {n : ℕ}
    (A B G : Matrix (Fin n) (Fin n) ℂ)
    (hAB : A * B = 1) (hBA : B * A = 1) :
    (A.transpose * G * A.map star)⁻¹ = B.map star * G⁻¹ * B.transpose := by
  have hinvA : A⁻¹ = B := by
    calc
      A⁻¹ = 1 * A⁻¹ := by simp
      _ = (B * A) * A⁻¹ := by rw [hBA]
      _ = B * (A * A⁻¹) := by rw [Matrix.mul_assoc]
      _ = B := by
        rw [Matrix.mul_nonsing_inv A (Matrix.isUnit_det_of_left_inverse hBA), mul_one]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  rw [← Matrix.transpose_nonsing_inv, hinvA]
  have hABstar : A.map star * B.map star = 1 := by
    ext a b
    have hij := congrArg star (congrFun (congrFun hAB a) b)
    simpa [Matrix.mul_apply, Matrix.one_apply, star_sum, star_mul, mul_comm] using hij
  have hBAstar : B.map star * A.map star = 1 := by
    ext a b
    have hij := congrArg star (congrFun (congrFun hBA a) b)
    simpa [Matrix.mul_apply, Matrix.one_apply, star_sum, star_mul, mul_comm] using hij
  have hs : IsUnit (A.map star).det := Matrix.isUnit_det_of_right_inverse hABstar
  have hinvstar : (A.map star)⁻¹ = B.map star := by
    calc
      (A.map star)⁻¹ = 1 * (A.map star)⁻¹ := by simp
      _ = (B.map star * A.map star) * (A.map star)⁻¹ := by rw [hBAstar]
      _ = B.map star * (A.map star * (A.map star)⁻¹) := by rw [Matrix.mul_assoc]
      _ = B.map star := by rw [Matrix.mul_nonsing_inv _ hs, mul_one]
  rw [hinvstar]
  rw [← Matrix.mul_assoc]

lemma linear_pullback_star_cancel {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) (hAB : A * B = 1) (s u : Fin n) :
    ∑ l, star (A s l) * star (B l u) = if s = u then 1 else 0 := by
  have hij := congrArg star (congrFun (congrFun hAB s) u)
  simpa [Matrix.mul_apply, Matrix.one_apply, star_sum, star_mul, mul_comm] using hij

lemma linear_sum_four_reorder {n : ℕ}
    (T : Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, T a b c d) = ∑ c, ∑ d, ∑ b, ∑ a, T a b c d := by
  calc
    (∑ a, ∑ b, ∑ c, ∑ d, T a b c d) = ∑ b, ∑ a, ∑ c, ∑ d, T a b c d := Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ a, ∑ d, T a b c d := by
      apply Finset.sum_congr rfl
      intro b hb
      exact Finset.sum_comm
    _ = ∑ c, ∑ b, ∑ a, ∑ d, T a b c d := Finset.sum_comm
    _ = ∑ c, ∑ b, ∑ d, ∑ a, T a b c d := by
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro b hb
      exact Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ b, ∑ a, T a b c d := by
      apply Finset.sum_congr rfl
      intro c hc
      exact Finset.sum_comm

lemma linear_pullback_contract_vector {n : ℕ}
    (A B G : Matrix (Fin n) (Fin n) ℂ)
    (hAB : A * B = 1) (i : Fin n) (X : Fin n → ℂ) :
    ∑ l, (∑ a, ∑ b, star (B l a) * G a b * B i b) *
      (∑ s, X s * star (A s l)) =
    ∑ s, ∑ b, G s b * B i b * X s := by
  calc
    _ = ∑ l, ∑ a, ∑ s, ∑ b,
          star (B l a) * G a b * B i b * (X s * star (A s l)) := by
      simp_rw [Fintype.sum_mul_sum, Finset.sum_mul]
    _ = ∑ s, ∑ b, ∑ a, ∑ l,
          star (B l a) * G a b * B i b * (X s * star (A s l)) := by
      exact linear_sum_four_reorder _
    _ = ∑ s, ∑ b, G s b * B i b * X s := by
      have hlocal (s b a : Fin n) :
          ∑ l, star (B l a) * G a b * B i b * (X s * star (A s l)) =
            (G a b * B i b * X s) * (if s = a then 1 else 0) := by
        calc
          _ = ∑ l, (G a b * B i b * X s) * (star (A s l) * star (B l a)) := by
            apply Finset.sum_congr rfl
            intro l hl
            ring
          _ = (G a b * B i b * X s) *
              (∑ l, star (A s l) * star (B l a)) := by rw [Finset.mul_sum]
          _ = _ := by rw [linear_pullback_star_cancel A B hAB s a]
      rw [show (∑ s, ∑ b, ∑ a, ∑ l,
          star (B l a) * G a b * B i b * (X s * star (A s l))) =
        ∑ s, ∑ b, ∑ a, (G a b * B i b * X s) * (if s = a then 1 else 0) by
          apply Finset.sum_congr rfl
          intro s hs
          apply Finset.sum_congr rfl
          intro b hb
          apply Finset.sum_congr rfl
          intro a ha
          exact hlocal s b a]
      simp

theorem linear_pullback_inverse_entry {n : ℕ}
    (P Q G : Matrix (Fin n) (Fin n) ℂ)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (q p : Fin n) :
    (linearPullbackMetric P G)⁻¹ q p =
      ∑ a, ∑ b, star (Q q a) * G⁻¹ a b * Q p b := by
  rw [linearPullbackMetric, linear_pullback_metric_inverse P Q G hPQ hQP]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]

lemma linear_plain_cancel {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℂ)
    (hPQ : P * Q = 1) (a b : Fin n) :
    ∑ r, P a r * Q r b = if a = b then 1 else 0 := by
  have h := congrFun (congrFun hPQ a) b
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

lemma linear_pullback_first_contraction {n : ℕ}
    (P Q G : Matrix (Fin n) (Fin n) ℂ)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (s u : Fin n) :
    ∑ p, ∑ q, (linearPullbackMetric P G)⁻¹ q p * P s p * star (P u q) =
      G⁻¹ u s := by
  have hselector (q : Fin n) :
      ∑ x, (if x = u then (1 : ℂ) else 0) * star (P x q) = star (P u q) := by
    simp
  have hcontract (p : Fin n) :
      ∑ q, (linearPullbackMetric P G)⁻¹ q p * star (P u q) =
        ∑ b, G⁻¹ u b * Q p b := by
    simp_rw [linear_pullback_inverse_entry P Q G hPQ hQP]
    calc
      ∑ q, (∑ a, ∑ b, star (Q q a) * G⁻¹ a b * Q p b) * star (P u q) =
          ∑ q, (∑ a, ∑ b, star (Q q a) * G⁻¹ a b * Q p b) *
            (∑ x, (if x = u then (1 : ℂ) else 0) * star (P x q)) := by
              apply Finset.sum_congr rfl
              intro q hq
              rw [← hselector q]
      _ = ∑ b, G⁻¹ u b * Q p b := by
            simpa using (linear_pullback_contract_vector P Q G⁻¹ hPQ p
              (fun x => if x = u then 1 else 0))
  calc
    ∑ p, ∑ q, (linearPullbackMetric P G)⁻¹ q p * P s p * star (P u q) =
        ∑ p, P s p * (∑ q, (linearPullbackMetric P G)⁻¹ q p * star (P u q)) := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q hq
          ring
    _ = ∑ p, P s p * (∑ b, G⁻¹ u b * Q p b) := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [hcontract p]
    _ = ∑ b, G⁻¹ u b * (∑ p, P s p * Q p b) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro b hb
          ac_rfl
    _ = G⁻¹ u s := by
          simp_rw [linear_plain_cancel P Q hPQ]
          simp

lemma linear_pullback_reference_contraction {n : ℕ}
    (P Q G : Matrix (Fin n) (Fin n) ℂ)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (i e : Fin n) :
    ∑ l, (linearPullbackMetric P G)⁻¹ l i * star (P e l) =
      ∑ a, Q i a * G⁻¹ e a := by
  have hselector (l : Fin n) :
      ∑ x, (if x = e then (1 : ℂ) else 0) * star (P x l) = star (P e l) := by
    simp
  simp_rw [linear_pullback_inverse_entry P Q G hPQ hQP]
  calc
    ∑ l, (∑ a, ∑ b, star (Q l a) * G⁻¹ a b * Q i b) * star (P e l) =
        ∑ l, (∑ a, ∑ b, star (Q l a) * G⁻¹ a b * Q i b) *
          (∑ x, (if x = e then (1 : ℂ) else 0) * star (P x l)) := by
            apply Finset.sum_congr rfl
            intro l hl
            rw [← hselector l]
    _ = ∑ a, Q i a * G⁻¹ e a := by
          simpa [mul_comm] using (linear_pullback_contract_vector P Q G⁻¹ hPQ i
            (fun x => if x = e then 1 else 0))

end KahlerForm
