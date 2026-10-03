module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Basic.Complex.Basic
public import CalabiYau.Mathlib.LinearAlgebra.Matrix.PullbackInverse

/-!
# The inverse-metric contraction of a holomorphic pullback first jet

This is the finite-matrix step in the Christoffel coordinate-change calculation.
The metric has holomorphic rows and antiholomorphic columns, hence the pullback
is `A.transpose * G * A.map star` and the inverse entry contracting its column
is `[l,i]`. The derivative of the Jacobian contributes with a plus sign.

Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §1.4,
coordinate product rule (p. 10) and Lemma 1.19 (p. 11).
-/

public section

open scoped BigOperators

namespace KahlerForm

private lemma pullback_star_cancel {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) (hAB : A * B = 1) (s u : Fin n) :
    ∑ l, star (A s l) * star (B l u) = if s = u then 1 else 0 := by
  have hij := congrArg star (congrFun (congrFun hAB s) u)
  simpa [Matrix.mul_apply, Matrix.one_apply, star_sum, star_mul, mul_comm] using hij

private lemma metric_inverse_entry {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (hG : IsUnit G.det) (r u : Fin n) :
    ∑ s, G r s * G⁻¹ s u = if r = u then 1 else 0 := by
  have hij := congrFun (congrFun (Matrix.mul_nonsing_inv G hG) r) u
  simpa [Matrix.mul_apply, Matrix.one_apply] using hij

private lemma sum_four_reorder {n : ℕ}
    (T : Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, T a b c d) = ∑ c, ∑ d, ∑ b, ∑ a, T a b c d := by
  calc
    (∑ a, ∑ b, ∑ c, ∑ d, T a b c d) = ∑ b, ∑ a, ∑ c, ∑ d, T a b c d :=
      Finset.sum_comm
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

private lemma pullback_contract_vector {n : ℕ}
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
      exact sum_four_reorder _
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
          _ = _ := by rw [pullback_star_cancel A B hAB s a]
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

private lemma sum_three_cycle {n : ℕ} (T : Fin n → Fin n → Fin n → ℂ) :
    (∑ p, ∑ r, ∑ s, T p r s) = ∑ s, ∑ p, ∑ r, T p r s := by
  calc
    (∑ p, ∑ r, ∑ s, T p r s) = ∑ r, ∑ p, ∑ s, T p r s := Finset.sum_comm
    _ = ∑ r, ∑ s, ∑ p, T p r s := by
      apply Finset.sum_congr rfl
      intro r hr
      exact Finset.sum_comm
    _ = ∑ s, ∑ r, ∑ p, T p r s := Finset.sum_comm
    _ = ∑ s, ∑ p, ∑ r, T p r s := by
      apply Finset.sum_congr rfl
      intro s hs
      exact Finset.sum_comm

private lemma pullback_jet_as_vectors {n : ℕ}
    (A G : Matrix (Fin n) (Fin n) ℂ)
    (C K : Fin n → Fin n → Fin n → ℂ) (j k l : Fin n) :
    (∑ r, ∑ s, K j r k * G r s * star (A s l)) +
      ∑ p, ∑ r, ∑ s, A p j * A r k * C p r s * star (A s l) =
    (∑ s, (∑ r, K j r k * G r s) * star (A s l)) +
      ∑ s, (∑ p, ∑ r, A p j * A r k * C p r s) * star (A s l) := by
  have hK :
      ∑ r, ∑ s, K j r k * G r s * star (A s l) =
        ∑ s, (∑ r, K j r k * G r s) * star (A s l) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s hs
    rw [← Finset.sum_mul]
  have hC :
      ∑ p, ∑ r, ∑ s, A p j * A r k * C p r s * star (A s l) =
        ∑ s, (∑ p, ∑ r, A p j * A r k * C p r s) * star (A s l) := by
    rw [sum_three_cycle]
    apply Finset.sum_congr rfl
    intro s hs
    calc
      ∑ p, ∑ r, A p j * A r k * C p r s * star (A s l) =
          ∑ p, (∑ r, A p j * A r k * C p r s) * star (A s l) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [← Finset.sum_mul]
      _ = (∑ p, ∑ r, A p j * A r k * C p r s) * star (A s l) := by
        rw [← Finset.sum_mul]
  rw [hK, hC]

private lemma sum_four_cycle {n : ℕ} (T : Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, T a b c d) = ∑ b, ∑ c, ∑ d, ∑ a, T a b c d := by
  calc
    (∑ a, ∑ b, ∑ c, ∑ d, T a b c d) = ∑ b, ∑ a, ∑ c, ∑ d, T a b c d :=
      Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ a, ∑ d, T a b c d := by
      apply Finset.sum_congr rfl
      intro b hb
      exact Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ d, ∑ a, T a b c d := by
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      exact Finset.sum_comm

private lemma metric_vector_contract {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ)
    (hG : IsUnit G.det) (B : Matrix (Fin n) (Fin n) ℂ) (i : Fin n)
    (K : Fin n → ℂ) :
    ∑ s, ∑ b, G⁻¹ s b * B i b * (∑ r, K r * G r s) =
      ∑ p, B i p * K p := by
  calc
    _ = ∑ s, ∑ b, ∑ r, (G⁻¹ s b * B i b) * (K r * G r s) := by
      simp_rw [Finset.mul_sum]
    _ = ∑ r, ∑ b, ∑ s, (G⁻¹ s b * B i b) * (K r * G r s) := by
      calc
        _ = ∑ b, ∑ s, ∑ r, (G⁻¹ s b * B i b) * (K r * G r s) := Finset.sum_comm
        _ = ∑ b, ∑ r, ∑ s, (G⁻¹ s b * B i b) * (K r * G r s) := by
          apply Finset.sum_congr rfl
          intro b hb
          exact Finset.sum_comm
        _ = ∑ r, ∑ b, ∑ s, (G⁻¹ s b * B i b) * (K r * G r s) := Finset.sum_comm
    _ = ∑ r, ∑ b, (K r * B i b) * (if r = b then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro b hb
      calc
        ∑ s, (G⁻¹ s b * B i b) * (K r * G r s) =
            ∑ s, (K r * B i b) * (G r s * G⁻¹ s b) := by
          apply Finset.sum_congr rfl
          intro s hs
          ring
        _ = (K r * B i b) * (∑ s, G r s * G⁻¹ s b) := by rw [Finset.mul_sum]
        _ = _ := by rw [metric_inverse_entry G hG r b]
    _ = ∑ p, B i p * K p := by simp [mul_comm]

private lemma hessian_vector_contract {n : ℕ}
    (A B G : Matrix (Fin n) (Fin n) ℂ) (i j k : Fin n)
    (C : Fin n → Fin n → Fin n → ℂ) :
    ∑ s, ∑ b, G s b * B i b * (∑ q, ∑ r, A q j * A r k * C q r s) =
    ∑ p, ∑ q, ∑ r, B i p * A q j * A r k * (∑ s, G s p * C q r s) := by
  calc
    _ = ∑ s, ∑ b, ∑ q, ∑ r,
        (G s b * B i b) * (A q j * A r k * C q r s) := by
      simp_rw [Finset.mul_sum]
    _ = ∑ b, ∑ q, ∑ r, ∑ s,
        (G s b * B i b) * (A q j * A r k * C q r s) := by
      exact sum_four_cycle _
    _ = ∑ b, ∑ q, ∑ r, B i b * A q j * A r k *
        (∑ s, G s b * C q r s) := by
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro r hr
      calc
        _ = ∑ s, (B i b * A q j * A r k) * (G s b * C q r s) := by
          apply Finset.sum_congr rfl
          intro s hs
          ring
        _ = _ := by rw [Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro r hr
      ring

/-- Contract the first jet of a pulled-back metric. Here `C q r s` is the
source metric derivative, and `K j r k` is the Jacobian derivative. No symmetry
of these derivative arrays is required by this algebraic identity. -/
theorem chartChristoffel_pullback_contraction {n : ℕ}
    (A B G : Matrix (Fin n) (Fin n) ℂ)
    (C K : Fin n → Fin n → Fin n → ℂ)
    (hAB : A * B = 1) (hBA : B * A = 1) (hG : IsUnit G.det)
    (i j k : Fin n) :
    let H := A.transpose * G * A.map star
    let D := fun k l =>
      (∑ r, ∑ s, K j r k * G r s * star (A s l)) +
      ∑ p, ∑ r, ∑ s, A p j * A r k * C p r s * star (A s l)
    (∑ l, H⁻¹ l i * D k l) =
      (∑ p, ∑ q, ∑ r,
        B i p * A q j * A r k * (∑ s, G⁻¹ s p * C q r s)) +
      ∑ p, B i p * K j p k := by
  dsimp only
  rw [Matrix.inv_transpose_mul_mul_map_star A B G hBA, Matrix.mul_assoc]
  have hcoef (l : Fin n) :
      (B.map star * (G⁻¹ * B.transpose)) l i =
        ∑ a, ∑ b, star (B l a) * G⁻¹ a b * B i b := by
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    ring
  simp_rw [hcoef]
  simp_rw [pullback_jet_as_vectors A G C K j k]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  rw [pullback_contract_vector A B G⁻¹ hAB i (fun s => ∑ r, K j r k * G r s)]
  rw [pullback_contract_vector A B G⁻¹ hAB i
    (fun s => ∑ q, ∑ r, A q j * A r k * C q r s)]
  rw [metric_vector_contract G hG B i (fun r => K j r k)]
  rw [hessian_vector_contract A B G⁻¹ i j k C]
  ring

end KahlerForm
