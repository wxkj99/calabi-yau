module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceCurvatureDerivative.Basic

/-!
# Five-slot contraction under column-frame transport

The homogeneous `(3,2)` tensor law and a frame with column matrix `P`
compose to the transported frame `A * P`. This is finite-sum algebra, not
an assertion that the geometric curvature derivative satisfies that law.
Source: Székelyhidi, §3.3, proof of Lemma 3.9, printed pp. 44–45.
-/

public section

namespace KahlerForm

private theorem sum_contract_one {n : Type} [Fintype n] [DecidableEq n]
    (f : n → ℂ) (g : n → n → ℂ) (h : n → ℂ) :
    (∑ i, ∑ a, f i * g a i * h a) =
      ∑ a, (∑ i, f i * g a i) * h a := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_mul]

private theorem sum_contract_nested {n : Type} [Fintype n] [DecidableEq n]
    (f : n → ℂ) (g : n → n → ℂ) (h : n → ℂ) :
    (∑ i, f i * ∑ a, g a i * h a) =
      ∑ a, (∑ i, f i * g a i) * h a := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  calc
    (∑ i, f i * (g a i * h a)) = ∑ i, (f i * g a i) * h a := by
      apply Finset.sum_congr rfl
      intro i _
      ring_nf
    _ = (∑ i, f i * g a i) * h a := by rw [← Finset.sum_mul]

private theorem separated_core {n : Type} [Fintype n] [DecidableEq n]
    (f g : n → ℂ) (u v : n → n → ℂ) (T : n → n → ℂ) :
    (∑ i, ∑ j, f i * g j * (∑ a, ∑ b, u a i * v b j * T a b)) =
      ∑ a, ∑ b, (∑ i, f i * u a i) * (∑ j, g j * v b j) * T a b := by
  calc
    (∑ i, ∑ j, f i * g j * (∑ a, ∑ b, u a i * v b j * T a b)) =
        ∑ i, ∑ j, ∑ a, ∑ b, f i * g j * (u a i * v b j * T a b) := by
      simp_rw [Finset.mul_sum]
    _ = ∑ i, ∑ a, ∑ j, ∑ b,
          f i * g j * (u a i * v b j * T a b) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ a, (f i * u a i) *
          (∑ j, ∑ b, g j * v b j * T a b) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro a _
      calc
        (∑ j, ∑ b, f i * g j * (u a i * v b j * T a b)) =
            ∑ j, ∑ b, (f i * u a i) * (g j * v b j * T a b) := by
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro b _
          ring_nf
        _ = ∑ j, (f i * u a i) * (∑ b, g j * v b j * T a b) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
        _ = (f i * u a i) * (∑ j, ∑ b, g j * v b j * T a b) := by
          rw [Finset.mul_sum]
    _ = ∑ a, (∑ i, f i * u a i) *
          (∑ j, ∑ b, g j * v b j * T a b) := by
      rw [sum_contract_one]
    _ = ∑ a, ∑ b, (∑ i, f i * u a i) *
          (∑ j, g j * v b j) * T a b := by
      apply Finset.sum_congr rfl
      intro a _
      calc
        (∑ i, f i * u a i) *
            (∑ j, ∑ b, g j * v b j * T a b) =
          (∑ i, f i * u a i) *
            (∑ b, (∑ j, g j * v b j) * T a b) := by
          congr 1
          exact sum_contract_one g v (fun b => T a b)
        _ = ∑ b, (∑ i, f i * u a i) *
            (∑ j, g j * v b j) * T a b := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          ring_nf

private theorem three_slot_separated_normal_normal_star
    {n : Type} [Fintype n] [DecidableEq n]
    (P Q R A B C : Matrix n n ℂ) (T : n → n → n → ℂ)
    (s p q : n) :
    (∑ i, ∑ j, P i s * Q j p *
      (∑ a, ∑ b, A a i * B b j *
        (∑ k, star (R k q) * ∑ c, star (C c k) * T a b c))) =
      ∑ a, ∑ b, (A * P) a s * (B * Q) b p *
        ∑ c, star ((C * R) c q) * T a b c := by
  calc
    (∑ i, ∑ j, P i s * Q j p *
      (∑ a, ∑ b, A a i * B b j *
        (∑ k, star (R k q) * ∑ c, star (C c k) * T a b c))) =
      ∑ a, ∑ b, (∑ i, P i s * A a i) * (∑ j, Q j p * B b j) *
        (∑ k, star (R k q) * ∑ c, star (C c k) * T a b c) := by
      exact separated_core (fun i => P i s) (fun j => Q j p) A B
        (fun a b => ∑ k, star (R k q) * ∑ c, star (C c k) * T a b c)
    _ = ∑ a, ∑ b, (A * P) a s * (B * Q) b p *
        ∑ c, star ((C * R) c q) * T a b c := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [show (∑ i, P i s * A a i) = (A * P) a s by
        simp [Matrix.mul_apply, mul_comm]]
      rw [show (∑ j, Q j p * B b j) = (B * Q) b p by
        simp [Matrix.mul_apply, mul_comm]]
      rw [sum_contract_nested (fun k => star (R k q))
        (fun c k => star (C c k)) (fun c => T a b c)]
      simp [Matrix.mul_apply, mul_comm]
private theorem two_slot_comp_normal_star {n : Type} [Fintype n] [DecidableEq n]
    (P Q A B : Matrix n n ℂ) (T : n → n → ℂ) (s p : n) :
    (∑ i, P i s * ∑ a, A a i *
      (∑ j, star (Q j p) * ∑ b, star (B b j) * T a b)) =
      ∑ a, (A * P) a s * ∑ b, star ((B * Q) b p) * T a b := by
  calc
    (∑ i, P i s * ∑ a, A a i *
      (∑ j, star (Q j p) * ∑ b, star (B b j) * T a b)) =
        ∑ a, (∑ i, P i s * A a i) *
          (∑ j, star (Q j p) * ∑ b, star (B b j) * T a b) := by
      exact sum_contract_nested (fun i => P i s) A
        (fun a => ∑ j, star (Q j p) * ∑ b, star (B b j) * T a b)
    _ = ∑ a, (A * P) a s * ∑ b, star ((B * Q) b p) * T a b := by
      apply Finset.sum_congr rfl
      intro a _
      rw [show (∑ i, P i s * A a i) = (A * P) a s by
        simp [Matrix.mul_apply, mul_comm]]
      congr 1
      rw [sum_contract_nested (fun j => star (Q j p))
        (fun b j => star (B b j)) (fun b => T a b)]
      simp [Matrix.mul_apply, mul_comm]

private theorem three_slot_comp_star_normal_star {n : Type} [Fintype n] [DecidableEq n]
    (P Q R A B C : Matrix n n ℂ) (T : n → n → n → ℂ) (s p q : n) :
    (∑ i, star (P i s) * ∑ a, star (A a i) *
      (∑ j, Q j p * ∑ b, B b j *
        (∑ k, star (R k q) * ∑ c, star (C c k) * T a b c))) =
      ∑ a, star ((A * P) a s) * ∑ b, (B * Q) b p *
        ∑ c, star ((C * R) c q) * T a b c := by
  calc
    (∑ i, star (P i s) * ∑ a, star (A a i) *
      (∑ j, Q j p * ∑ b, B b j *
        (∑ k, star (R k q) * ∑ c, star (C c k) * T a b c))) =
        ∑ a, (∑ i, star (P i s) * star (A a i)) *
          (∑ j, Q j p * ∑ b, B b j *
            (∑ k, star (R k q) * ∑ c, star (C c k) * T a b c)) := by
      exact sum_contract_nested (fun i => star (P i s))
        (fun a i => star (A a i))
        (fun a => ∑ j, Q j p * ∑ b, B b j *
          (∑ k, star (R k q) * ∑ c, star (C c k) * T a b c))
    _ = ∑ a, star ((A * P) a s) * ∑ b, (B * Q) b p *
        ∑ c, star ((C * R) c q) * T a b c := by
      apply Finset.sum_congr rfl
      intro a _
      rw [show (∑ i, star (P i s) * star (A a i)) =
        star ((A * P) a s) by simp [Matrix.mul_apply, mul_comm]]
      congr 1
      exact two_slot_comp_normal_star Q R B C
        (fun b c => T a b c) p q

private theorem five_slot_grouped_comp
    {n : Type} [Fintype n] [DecidableEq n]
    (P Q R S U A B C D E : Matrix n n ℂ)
    (T : n → n → n → n → n → ℂ) (s p q r t : n) :
    (∑ i, ∑ j, P i s * Q j p *
      (∑ a, ∑ b, A a i * B b j *
        (∑ k, star (R k q) * ∑ c, star (C c k) *
          (∑ l, S l r * ∑ d, D d l *
            (∑ m, star (U m t) * ∑ e, star (E e m) * T a b c d e))))) =
      ∑ a, ∑ b, (A * P) a s * (B * Q) b p *
        (∑ c, star ((C * R) c q) * ∑ d, (D * S) d r *
          ∑ e, star ((E * U) e t) * T a b c d e) := by
  calc
    (∑ i, ∑ j, P i s * Q j p *
      (∑ a, ∑ b, A a i * B b j *
        (∑ k, star (R k q) * ∑ c, star (C c k) *
          (∑ l, S l r * ∑ d, D d l *
            (∑ m, star (U m t) * ∑ e, star (E e m) * T a b c d e))))) =
        ∑ a, ∑ b, (∑ i, P i s * A a i) * (∑ j, Q j p * B b j) *
          (∑ k, star (R k q) * ∑ c, star (C c k) *
            (∑ l, S l r * ∑ d, D d l *
              (∑ m, star (U m t) * ∑ e, star (E e m) * T a b c d e))) := by
      exact separated_core (fun i => P i s) (fun j => Q j p) A B
        (fun a b => ∑ k, star (R k q) * ∑ c, star (C c k) *
          (∑ l, S l r * ∑ d, D d l *
            (∑ m, star (U m t) * ∑ e, star (E e m) * T a b c d e)))
    _ = ∑ a, ∑ b, (A * P) a s * (B * Q) b p *
        (∑ c, star ((C * R) c q) * ∑ d, (D * S) d r *
          ∑ e, star ((E * U) e t) * T a b c d e) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [show (∑ i, P i s * A a i) = (A * P) a s by
        simp [Matrix.mul_apply, mul_comm]]
      rw [show (∑ j, Q j p * B b j) = (B * Q) b p by
        simp [Matrix.mul_apply, mul_comm]]
      congr 1
      exact three_slot_comp_star_normal_star R S U C D E
        (fun c d e => T a b c d e) q r t

private abbrev Tuple10 (n : Type) := n × (n × (n × (n × (n × (n × (n × (n × (n × n))))))))

private def tupleShuffle {n : Type} (x : Tuple10 n) : Tuple10 n :=
  match x with
  | (a, b, c, d, e, f, g, h, i, j) => (a, b, f, g, c, h, d, i, e, j)

private def tupleUnshuffle {n : Type} (x : Tuple10 n) : Tuple10 n :=
  match x with
  | (a, b, c, d, e, f, g, h, i, j) => (a, b, e, g, i, c, d, f, h, j)

private theorem tupleShuffle_left {n : Type} (x : Tuple10 n) :
    tupleUnshuffle (tupleShuffle x) = x := by
  cases x with
  | mk a xs => cases xs with
    | mk b xs => cases xs with
      | mk c xs => cases xs with
        | mk d xs => cases xs with
          | mk e xs => cases xs with
            | mk f xs => cases xs with
              | mk g xs => cases xs with
                | mk h xs => cases xs with
                  | mk i j => rfl

private theorem tupleShuffle_right {n : Type} (x : Tuple10 n) :
    tupleShuffle (tupleUnshuffle x) = x := by
  cases x with
  | mk a xs => cases xs with
    | mk b xs => cases xs with
      | mk c xs => cases xs with
        | mk d xs => cases xs with
          | mk e xs => cases xs with
            | mk f xs => cases xs with
              | mk g xs => cases xs with
                | mk h xs => cases xs with
                  | mk i j => rfl

private theorem sum_shuffle_target {n : Type} [Fintype n] [DecidableEq n]
    (f : n → n → n → n → n → n → n → n → n → n → ℂ) :
    (∑ i, ∑ j, ∑ k, ∑ l, ∑ m, ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
      f i j k l m a b c d e) =
    (∑ i, ∑ j, ∑ a, ∑ b, ∑ k, ∑ c, ∑ l, ∑ d, ∑ m, ∑ e,
      f i j k l m a b c d e) := by
  let E : Tuple10 n ≃ Tuple10 n := {
    toFun := tupleShuffle
    invFun := tupleUnshuffle
    left_inv := tupleShuffle_left
    right_inv := tupleShuffle_right }
  let g : Tuple10 n → ℂ := fun x =>
    f x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1
      x.2.2.2.2.2.1 x.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.1
      x.2.2.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2
  have h : (∑ x : Tuple10 n, g x) = ∑ x : Tuple10 n, g (tupleUnshuffle x) := by
    exact Fintype.sum_equiv E g (fun x => g (tupleUnshuffle x))
      (by intro x; simp [E, tupleShuffle_left])
  simpa [Fintype.sum_prod_type, g, tupleUnshuffle] using h

/-- Compose a five-slot pullback with a column-frame contraction. No metric
normalization or matrix invertibility is required for this identity. -/
theorem c3_five_slot_frame_pullback {n : ℕ}
    (A P : Matrix (Fin n) (Fin n) ℂ)
    (Ty Tx : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ)
    (hT : Ty = c3FiveSlotFrameContraction A Tx) :
    c3FiveSlotFrameContraction P Ty = c3FiveSlotFrameContraction (A * P) Tx := by
  subst Ty
  ext s p q j k
  conv_lhs => simp only [c3FiveSlotFrameContraction]
  simp_rw [Finset.mul_sum]
  rw [sum_shuffle_target (fun u v w x y aa bb cc dd ee =>
    P u s * P v p * star (P w q) * P x j * star (P y k) *
      (A aa u * A bb v * star (A cc w) * A dd x * star (A ee y) *
        Tx aa bb cc dd ee))]
  have hgrp := five_slot_grouped_comp P P P P P A A A A A Tx s p q j k
  simp_rw [Finset.mul_sum, Matrix.mul_apply] at hgrp
  convert hgrp using 1
  · repeat' (apply Finset.sum_congr rfl; intro _ _)
    ring_nf
  · try simp_rw [Matrix.mul_apply, Finset.mul_sum]
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    simp only [Matrix.mul_apply]
    ring_nf

end KahlerForm
