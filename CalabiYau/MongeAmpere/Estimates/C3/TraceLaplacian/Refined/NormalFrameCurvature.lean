module

public import CalabiYau.MongeAmpere.Estimates.C3.TraceLaplacian.Refined.NormalCoordinateFrame
public import CalabiYau.MongeAmpere.Estimates.C3.TraceLaplacian.Refined.ReferenceCurvatureError
public import CalabiYau.Mathlib.LinearAlgebra.Matrix.PullbackInverse

/-!
# Reference-curvature contraction in a holomorphic normal frame

The signed reference-curvature contraction is intrinsic: transport all four
covariant curvature indices under the actual local holomorphic coordinate
change, and transport both Hermitian metric contractions contravariantly.
At a reference-normal frame diagonalizing the perturbed metric, the resulting
scalar is the source's explicit sum `∑(λⱼ/λₚ−1) R_{p p̄ j j̄}`.

Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §3.3,
Lemma 3.10, pp. 45–46; Yau (1978), §3.
-/

@[expose] public section

open scoped BigOperators Manifold ContDiff NNReal ComplexOrder MatrixOrder
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

private theorem c3RefinedTrace_diagonalSignedContraction
    {n : ℕ} (lam : Fin n → ℝ) (hlam : ∀ i, lam i ≠ 0)
    (R : Fin n → Fin n → Fin n → Fin n → ℂ) :
    RCLike.re (∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      (((Matrix.diagonal (fun i ↦ (lam i : ℂ)))⁻¹ q p *
        Matrix.diagonal (fun i ↦ (lam i : ℂ)) k j -
        (1 : Matrix (Fin n) (Fin n) ℂ) q p * (1 : Matrix (Fin n) (Fin n) ℂ) k j) *
        R p q j k)) =
      ∑ p : Fin n, ∑ j : Fin n,
        (lam j / lam p - 1) * RCLike.re (R p p j j) := by
  classical
  have hlamC (i : Fin n) : (lam i : ℂ) ≠ 0 := by exact_mod_cast hlam i
  have hfun : IsUnit (fun i : Fin n ↦ (lam i : ℂ)) := by
    rw [Pi.isUnit_iff]
    intro i
    exact isUnit_iff_ne_zero.mpr (hlamC i)
  have hinvfun (i : Fin n) :
      Ring.inverse (fun k : Fin n ↦ (lam k : ℂ)) i = (lam i : ℂ)⁻¹ := by
    rw [Ring.inverse_of_isUnit hfun]
    simp [IsUnit.val_inv_apply]
  have hinv (q p : Fin n) :
      (Matrix.diagonal (fun i ↦ (lam i : ℂ)))⁻¹ q p =
        if q = p then (lam p : ℂ)⁻¹ else 0 := by
    rw [Matrix.inv_diagonal]
    simp only [Matrix.diagonal_apply]
    split_ifs with h
    · subst q
      exact hinvfun p
    · rfl
  have hcoeff (p q j k : Fin n) :
      ((Matrix.diagonal (fun i ↦ (lam i : ℂ)))⁻¹ q p *
        Matrix.diagonal (fun i ↦ (lam i : ℂ)) k j -
        (1 : Matrix (Fin n) (Fin n) ℂ) q p *
          (1 : Matrix (Fin n) (Fin n) ℂ) k j) =
        if q = p then if k = j then ((lam j / lam p - 1 : ℝ) : ℂ) else 0 else 0 := by
    by_cases hp : q = p <;> by_cases hk : k = j
    · subst q
      subst k
      simp [hinv]
      field_simp
    · simp [hinv, hp, hk]
    · simp [hinv, hp, hk]
    · simp [hinv, hp, hk]
  have hsum :
      (∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (((Matrix.diagonal (fun i ↦ (lam i : ℂ)))⁻¹ q p *
          Matrix.diagonal (fun i ↦ (lam i : ℂ)) k j -
          (1 : Matrix (Fin n) (Fin n) ℂ) q p *
            (1 : Matrix (Fin n) (Fin n) ℂ) k j) * R p q j k)) =
        ∑ p : Fin n, ∑ j : Fin n,
          ((lam j / lam p - 1 : ℝ) : ℂ) * R p p j j := by
    simp_rw [hcoeff]
    simp [Finset.sum_ite_eq']
  rw [hsum]
  simp []

private theorem c3RefinedTrace_referenceCurvature_eq_chartCurvature
    {n : ℕ} (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hg : ∀ a b, ContDiffAt ℝ ∞ (fun w ↦ g w a b) z)
    (hdet : IsUnit (g z).det) (p q j k : Fin n) :
    c3RefinedTraceReferenceCurvatureInChart g z p q j k =
      chartCurvature g z p q j k := by
  have hc (a : Fin n) :
      c3RefinedTracePartialBar (fun w ↦ christoffelInChart g w a p j) z q =
        -(∑ l, (g z)⁻¹ l a * chartCurvature g z p q j l) := by
    change chartPartialBarComplex
      (fun w ↦ ∑ l, (g w)⁻¹ l a * chartPartialZComplex (fun v ↦ g v j l) w p) z q = _
    exact chartChristoffel_bar_eq_curvature_at g z hg hdet a p j q
  have hmul := Matrix.nonsing_inv_mul (g z) hdet
  have hcontract (l : Fin n) :
      ∑ a : Fin n, (g z)⁻¹ l a * g z a k = if l = k then 1 else 0 := by
    have h := congrFun (congrFun hmul l) k
    simpa only [Matrix.mul_apply, Matrix.one_apply] using h
  change -∑ a : Fin n, g z a k *
      c3RefinedTracePartialBar (fun w ↦ christoffelInChart g w a p j) z q = _
  have hsum :
      ∑ a : Fin n, g z a k *
          c3RefinedTracePartialBar (fun w ↦ christoffelInChart g w a p j) z q =
        ∑ a : Fin n, g z a k *
          (-(∑ l : Fin n, (g z)⁻¹ l a * chartCurvature g z p q j l)) := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [hc a]
  rw [hsum]
  simp only [mul_neg, Finset.sum_neg_distrib, neg_neg]
  change _ = chartCurvature g z p q j k
  calc
    ∑ a : Fin n, g z a k * ∑ l : Fin n, (g z)⁻¹ l a * chartCurvature g z p q j l =
        ∑ l : Fin n, (∑ a : Fin n, (g z)⁻¹ l a * g z a k) *
          chartCurvature g z p q j l := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l hl
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = chartCurvature g z p q j k := by
      simp [hcontract]

private lemma c3RefinedTrace_pullback_double_inverse {n : ℕ}
    (A B G H : Matrix (Fin n) (Fin n) ℂ)
    (hAB : A * B = 1) (hBA : B * A = 1) :
    (A.transpose * G * A.map star)⁻¹ * (A.transpose * H * A.map star) *
        (A.transpose * G * A.map star)⁻¹ =
      B.map star * (G⁻¹ * H * G⁻¹) * B.transpose := by
  rw [Matrix.inv_transpose_mul_mul_map_star A B G hBA]
  have htranspose : B.transpose * A.transpose = 1 := by
    rw [← Matrix.transpose_mul, hAB]
    simp
  have hstar : A.map star * B.map star = 1 := by
    ext a b
    have hij := congrArg star (congrFun (congrFun hAB a) b)
    simpa [Matrix.mul_apply, Matrix.one_apply, star_sum, star_mul, mul_comm] using hij
  calc
    _ = B.map star * (G⁻¹ * (B.transpose * A.transpose) * H *
          (A.map star * B.map star) * G⁻¹) * B.transpose := by
        simp only [Matrix.mul_assoc]
    _ = B.map star * (G⁻¹ * H * G⁻¹) * B.transpose := by
        rw [htranspose, hstar]
        simp only [Matrix.mul_one, Matrix.mul_assoc]

private lemma c3RefinedTrace_pullback_contract_pair {n : ℕ}
    (A B X : Matrix (Fin n) (Fin n) ℂ) (hAB : A * B = 1)
    (T : Matrix (Fin n) (Fin n) ℂ) :
    ∑ q : Fin n, ∑ p : Fin n,
      (B.map star * X * B.transpose) q p *
        (∑ a : Fin n, ∑ b : Fin n, A a p * star (A b q) * T a b) =
      ∑ a : Fin n, ∑ b : Fin n, X b a * T a b := by
  classical
  have hABstar : A.map star * B.map star = 1 := by
    ext a b
    have h := congrArg star (congrFun (congrFun hAB a) b)
    simpa [Matrix.mul_apply, Matrix.one_apply, star_sum, star_mul, mul_comm] using h
  have htranspose : B.transpose * A.transpose = 1 := by
    rw [← Matrix.transpose_mul, hAB]
    simp
  have hTP (p q : Fin n) :
      (A.transpose * T * A.map star) p q =
        ∑ a : Fin n, ∑ b : Fin n, A a p * star (A b q) * T a b := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    calc
      ∑ b : Fin n, (∑ a : Fin n, A a p * T a b) * star (A b q) =
          ∑ b : Fin n, ∑ a : Fin n, A a p * T a b * star (A b q) := by
        apply Finset.sum_congr rfl
        intro b hb
        exact Finset.sum_mul Finset.univ
          (fun a : Fin n ↦ A a p * T a b) (star (A b q))
      _ = ∑ a : Fin n, ∑ b : Fin n, A a p * T a b * star (A b q) :=
        Finset.sum_comm
      _ = ∑ a : Fin n, ∑ b : Fin n, A a p * star (A b q) * T a b := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        ring
  have htrace :
      ((B.map star * X * B.transpose) * (A.transpose * T * A.map star)).trace =
        ∑ q : Fin n, ∑ p : Fin n,
          (B.map star * X * B.transpose) q p * (A.transpose * T * A.map star) p q := by
    simp [Matrix.trace, Matrix.mul_apply]
  calc
    ∑ q : Fin n, ∑ p : Fin n,
        (B.map star * X * B.transpose) q p *
          (∑ a : Fin n, ∑ b : Fin n, A a p * star (A b q) * T a b) =
        ((B.map star * X * B.transpose) * (A.transpose * T * A.map star)).trace := by
      rw [htrace]
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro p hp
      rw [← hTP p q]
    _ = ((B.map star * X) * (B.transpose * A.transpose) * T * A.map star).trace := by
      congr 1
      simp only [Matrix.mul_assoc]
    _ = ((B.map star * X) * T * A.map star).trace := by
      rw [htranspose]
      simp
    _ = (B.map star * ((X * T) * A.map star)).trace := by
      congr 1
      simp only [Matrix.mul_assoc]
    _ = (((X * T) * A.map star) * B.map star).trace :=
      Matrix.trace_mul_comm _ _
    _ = ((X * T) * (A.map star * B.map star)).trace := by
      congr 1
      simp only [Matrix.mul_assoc]
    _ = (X * T).trace := by rw [hABstar]; simp
    _ = ∑ a : Fin n, ∑ b : Fin n, X b a * T a b := by
      simp only [Matrix.trace]
      rw [Finset.sum_comm]
      rfl

private lemma c3RefinedTrace_sum_four_reorder {n : ℕ}
    (F : Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n, F p q j k) =
      ∑ j : Fin n, ∑ k : Fin n, ∑ q : Fin n, ∑ p : Fin n, F p q j k := by
  calc
    (∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n, F p q j k) =
        ∑ q : Fin n, ∑ p : Fin n, ∑ j : Fin n, ∑ k : Fin n, F p q j k :=
      Finset.sum_comm
    _ = ∑ q : Fin n, ∑ j : Fin n, ∑ p : Fin n, ∑ k : Fin n, F p q j k := by
      apply Finset.sum_congr rfl
      intro q hq
      exact Finset.sum_comm
    _ = ∑ j : Fin n, ∑ q : Fin n, ∑ p : Fin n, ∑ k : Fin n, F p q j k :=
      Finset.sum_comm
    _ = ∑ j : Fin n, ∑ q : Fin n, ∑ k : Fin n, ∑ p : Fin n, F p q j k := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro q hq
      exact Finset.sum_comm
    _ = ∑ j : Fin n, ∑ k : Fin n, ∑ q : Fin n, ∑ p : Fin n, F p q j k := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Finset.sum_comm

private lemma c3RefinedTrace_pullback_curvature_split {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (R : Fin n → Fin n → Fin n → Fin n → ℂ)
    (p q j k : Fin n) :
    ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
      A a p * star (A b q) * A c j * star (A d k) * R a b c d =
    ∑ a : Fin n, ∑ b : Fin n, A a p * star (A b q) *
      (∑ c : Fin n, ∑ d : Fin n, A c j * star (A d k) * R a b c d) := by
  classical
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  calc
    ∑ c : Fin n, ∑ d : Fin n,
        A a p * star (A b q) * A c j * star (A d k) * R a b c d =
      ∑ c : Fin n, ∑ d : Fin n,
        (A a p * star (A b q)) * (A c j * star (A d k) * R a b c d) := by
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = ∑ c : Fin n, (A a p * star (A b q)) *
          ∑ d : Fin n, A c j * star (A d k) * R a b c d := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [← Finset.mul_sum]
    _ = (A a p * star (A b q)) *
          ∑ c : Fin n, ∑ d : Fin n, A c j * star (A d k) * R a b c d := by
      rw [← Finset.mul_sum]

private lemma c3RefinedTrace_sum_four_block_swap {n : ℕ}
    (F : Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ j : Fin n, ∑ k : Fin n, ∑ a : Fin n, ∑ b : Fin n, F a b j k) =
      ∑ a : Fin n, ∑ b : Fin n, ∑ j : Fin n, ∑ k : Fin n, F a b j k := by
  calc
    (∑ j : Fin n, ∑ k : Fin n, ∑ a : Fin n, ∑ b : Fin n, F a b j k) =
        ∑ k : Fin n, ∑ j : Fin n, ∑ a : Fin n, ∑ b : Fin n, F a b j k :=
      Finset.sum_comm
    _ = ∑ k : Fin n, ∑ a : Fin n, ∑ j : Fin n, ∑ b : Fin n, F a b j k := by
      apply Finset.sum_congr rfl
      intro k hk
      exact Finset.sum_comm
    _ = ∑ a : Fin n, ∑ k : Fin n, ∑ j : Fin n, ∑ b : Fin n, F a b j k :=
      Finset.sum_comm
    _ = ∑ a : Fin n, ∑ k : Fin n, ∑ b : Fin n, ∑ j : Fin n, F a b j k := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro k hk
      exact Finset.sum_comm
    _ = ∑ a : Fin n, ∑ b : Fin n, ∑ k : Fin n, ∑ j : Fin n, F a b j k := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = ∑ a : Fin n, ∑ b : Fin n, ∑ j : Fin n, ∑ k : Fin n, F a b j k := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact Finset.sum_comm

private lemma c3RefinedTrace_pullback_contract_four {n : ℕ}
    (A B X Y : Matrix (Fin n) (Fin n) ℂ) (hAB : A * B = 1)
    (R : Fin n → Fin n → Fin n → Fin n → ℂ) :
    ∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      (B.map star * X * B.transpose) q p * (B.map star * Y * B.transpose) k j *
        (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
          A a p * star (A b q) * A c j * star (A d k) * R a b c d) =
      ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
        X b a * Y d c * R a b c d := by
  classical
  let XF := B.map star * X * B.transpose
  let YF := B.map star * Y * B.transpose
  let Tjk : Fin n → Fin n → Fin n → Fin n → ℂ := fun j k a b =>
    ∑ c : Fin n, ∑ d : Fin n, A c j * star (A d k) * R a b c d
  have hsplit (p q j k : Fin n) :
      (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
        A a p * star (A b q) * A c j * star (A d k) * R a b c d) =
      ∑ a : Fin n, ∑ b : Fin n, A a p * star (A b q) * Tjk j k a b := by
    simpa [Tjk] using c3RefinedTrace_pullback_curvature_split A R p q j k
  have hpair1 (j k : Fin n) :
      ∑ q : Fin n, ∑ p : Fin n,
        XF q p * (∑ a : Fin n, ∑ b : Fin n,
          A a p * star (A b q) * Tjk j k a b) =
      ∑ a : Fin n, ∑ b : Fin n, X b a * Tjk j k a b := by
    let W : Matrix (Fin n) (Fin n) ℂ := fun a b => Tjk j k a b
    simpa [XF, W] using c3RefinedTrace_pullback_contract_pair A B X hAB W
  have hpair2 (a b : Fin n) :
      ∑ j : Fin n, ∑ k : Fin n, YF k j * Tjk j k a b =
      ∑ c : Fin n, ∑ d : Fin n, Y d c * R a b c d := by
    let W : Matrix (Fin n) (Fin n) ℂ := fun c d => R a b c d
    rw [Finset.sum_comm]
    simpa [YF, Tjk, W] using c3RefinedTrace_pullback_contract_pair A B Y hAB W
  calc
    _ = ∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        XF q p * YF k j * (∑ a : Fin n, ∑ b : Fin n,
          A a p * star (A b q) * Tjk j k a b) := by
      simp_rw [XF, YF, hsplit]
    _ = ∑ j : Fin n, ∑ k : Fin n, YF k j *
        (∑ q : Fin n, ∑ p : Fin n,
          XF q p * (∑ a : Fin n, ∑ b : Fin n,
            A a p * star (A b q) * Tjk j k a b)) := by
      rw [c3RefinedTrace_sum_four_reorder]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      calc
        ∑ q : Fin n, ∑ p : Fin n,
            XF q p * YF k j * (∑ a : Fin n, ∑ b : Fin n,
              A a p * star (A b q) * Tjk j k a b) =
          ∑ q : Fin n, ∑ p : Fin n,
            YF k j * (XF q p * (∑ a : Fin n, ∑ b : Fin n,
              A a p * star (A b q) * Tjk j k a b)) := by
          apply Finset.sum_congr rfl
          intro q hq
          apply Finset.sum_congr rfl
          intro p hp
          ring
        _ = ∑ q : Fin n, YF k j *
              (∑ p : Fin n, XF q p * (∑ a : Fin n, ∑ b : Fin n,
                A a p * star (A b q) * Tjk j k a b)) := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [← Finset.mul_sum]
        _ = YF k j *
              (∑ q : Fin n, ∑ p : Fin n,
                XF q p * (∑ a : Fin n, ∑ b : Fin n,
                  A a p * star (A b q) * Tjk j k a b)) := by
          rw [← Finset.mul_sum]
    _ = ∑ j : Fin n, ∑ k : Fin n, YF k j *
          (∑ a : Fin n, ∑ b : Fin n, X b a * Tjk j k a b) := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      rw [hpair1 j k]
    _ = ∑ j : Fin n, ∑ k : Fin n, ∑ a : Fin n, ∑ b : Fin n,
          X b a * YF k j * Tjk j k a b := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      calc
        YF k j * (∑ a : Fin n, ∑ b : Fin n, X b a * Tjk j k a b) =
            ∑ a : Fin n, ∑ b : Fin n, YF k j * (X b a * Tjk j k a b) := by
          calc
            _ = ∑ a : Fin n, YF k j * (∑ b : Fin n, X b a * Tjk j k a b) :=
              Finset.mul_sum Finset.univ _ _
            _ = ∑ a : Fin n, ∑ b : Fin n,
                  YF k j * (X b a * Tjk j k a b) := by
              apply Finset.sum_congr rfl
              intro a ha
              exact Finset.mul_sum Finset.univ _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          ring
    _ = ∑ a : Fin n, ∑ b : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          X b a * YF k j * Tjk j k a b := by
      exact c3RefinedTrace_sum_four_block_swap
        (fun a b j k => X b a * YF k j * Tjk j k a b)
    _ = ∑ a : Fin n, ∑ b : Fin n, X b a *
          (∑ j : Fin n, ∑ k : Fin n, YF k j * Tjk j k a b) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      calc
        ∑ j : Fin n, ∑ k : Fin n, X b a * YF k j * Tjk j k a b =
            ∑ j : Fin n, ∑ k : Fin n, X b a * (YF k j * Tjk j k a b) := by
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro k hk
          ring
        _ = ∑ j : Fin n, X b a * (∑ k : Fin n, YF k j * Tjk j k a b) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact (Finset.mul_sum Finset.univ _ _).symm
        _ = X b a * (∑ j : Fin n, ∑ k : Fin n, YF k j * Tjk j k a b) :=
          (Finset.mul_sum Finset.univ _ _).symm
    _ = ∑ a : Fin n, ∑ b : Fin n, X b a *
          (∑ c : Fin n, ∑ d : Fin n, Y d c * R a b c d) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [hpair2 a b]
    _ = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
          X b a * Y d c * R a b c d := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro d hd
      ring

private theorem c3RefinedTrace_chartCurvature_pullback_of_frame
    (ω₀ : KahlerForm n M) (φ : M → ℝ) (x : M)
    (frame : C3RefinedTraceNormalCoordinateFrame ω₀ φ x)
    (p q j k : Fin n) :
    chartCurvature (c3RefinedTracePulledReferenceMetric ω₀ x frame.coord)
        frame.center p q j k =
      ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
        (EuclideanSpace.clmMatrix (fderiv ℂ frame.coord frame.center)) a p *
          star ((EuclideanSpace.clmMatrix (fderiv ℂ frame.coord frame.center)) b q) *
          (EuclideanSpace.clmMatrix (fderiv ℂ frame.coord frame.center)) c j *
          star ((EuclideanSpace.clmMatrix (fderiv ℂ frame.coord frame.center)) d k) *
          chartCurvature (fun z ↦ ω₀.metricInChart x z)
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) a b c d := by
  let U := frame.domain
  let F := frame.coord
  let g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun z ↦ ω₀.metricInChart x z
  let gF := c3RefinedTracePulledReferenceMetric ω₀ x F
  have hFreal : ContDiffOn ℝ ∞ F U := frame.holomorphic.restrict_scalars ℝ
  have hFhol : DifferentiableOn ℂ F U :=
    frame.holomorphic.differentiableOn (by norm_num)
  have hg' : ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ g z i j) (F '' U) := by
    intro i j
    exact (ω₀.contDiffOn_metricInChart x i j).mono frame.in_chart
  have hmetric : ∀ w ∈ U,
      gF w = Matrix.transpose (EuclideanSpace.clmMatrix (fderiv ℂ F w)) *
        g (F w) * (EuclideanSpace.clmMatrix (fderiv ℂ F w)).map star := by
    intro w hw
    rfl
  have hkahler : ∀ w ∈ F '' U, ∀ i j k,
      chartPartialZComplex (fun z ↦ g z j k) w i =
        chartPartialZComplex (fun z ↦ g z i k) w j := by
    rintro w ⟨u, hu, rfl⟩ i j k
    exact ω₀.kahler_chart_metric_symmetry x (frame.in_chart ⟨u, hu, rfl⟩) i j k
  have hjac : IsUnit
      (EuclideanSpace.clmMatrix (fderiv ℂ F frame.center)).det :=
    frame.jacobian_unit frame.center frame.center_mem
  have htarget : F frame.center ∈
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target :=
    frame.in_chart ⟨frame.center, frame.center_mem, rfl⟩
  have hgdet : IsUnit (g (F frame.center)).det :=
    (Matrix.isUnit_iff_isUnit_det (A := g (F frame.center))).mp
      (ω₀.posDef_metricInChart x htarget).isUnit
  have hcurv := chartCurvature_pullback U frame.open_domain F hFreal hFhol gF g
    hg' hmetric frame.center frame.center_mem hjac hgdet p q j k
  simpa [U, F, g, gF, frame.center_eq] using hcurv

private theorem c3RefinedTrace_pulledReferenceMetric_smooth
    (ω₀ : KahlerForm n M) (φ : M → ℝ) (x : M)
    (frame : C3RefinedTraceNormalCoordinateFrame ω₀ φ x) :
    ∀ i j, ContDiffAt ℝ ∞
      (fun w ↦ c3RefinedTracePulledReferenceMetric ω₀ x frame.coord w i j) frame.center := by
  let U := frame.domain
  let F := frame.coord
  let g := fun w : EuclideanSpace ℂ (Fin n) ↦ ω₀.metricInChart x w
  let A := fun w ↦ EuclideanSpace.clmMatrix (fderiv ℂ F w)
  have hFreal : ContDiffOn ℝ ∞ F U := frame.holomorphic.restrict_scalars ℝ
  have hFhol : DifferentiableOn ℂ F U := by
    intro w hw
    exact (frame.holomorphic w hw).differentiableWithinAt (by norm_num)
  have hJ (a b : Fin n) : ContDiffOn ℝ ∞ (fun w ↦ A w a b) U := by
    intro w hw
    exact (chart_pullback_jacobian_entry_contDiffAt U frame.open_domain F hFreal hFhol
      w hw a b).contDiffWithinAt
  have hg' : ∀ a b, ContDiffOn ℝ ∞ (fun w ↦ g w a b) (F '' U) := by
    intro a b
    exact (ω₀.contDiffOn_metricInChart x a b).mono frame.in_chart
  have hGcomp (a b : Fin n) : ContDiffOn ℝ ∞ (fun w ↦ g (F w) a b) U := by
    exact (hg' a b).comp hFreal
      (by intro w hw; exact ⟨w, hw, rfl⟩)
  intro i j
  have hentry : ContDiffOn ℝ ∞
      (fun w ↦ c3RefinedTracePulledReferenceMetric ω₀ x F w i j) U := by
    change ContDiffOn ℝ ∞
      (fun w ↦ ((A w).transpose * g (F w) * (A w).map star) i j) U
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    apply ContDiffOn.sum
    intro b hb
    have hinner : ContDiffOn ℝ ∞
        (fun w ↦ ∑ a : Fin n, A w a i * g (F w) a b) U := by
      apply ContDiffOn.sum
      intro a ha
      exact (hJ a i).mul (hGcomp a b)
    have hstar : ContDiffOn ℝ ∞ (fun w ↦ star (A w b j)) U := by
      have hc := Complex.conjCLE.contDiff.contDiffOn.comp (hJ b j) (Set.mapsTo_univ _ _)
      simpa [Function.comp_def, Complex.star_def, Complex.conjCLE_apply] using hc
    exact hinner.mul hstar
  exact (hentry.contDiffAt (frame.open_domain.mem_nhds frame.center_mem))

/-- The ordered inverse-metric contractions and the K four-index curvature
law give the same signed error in the old chart and the holomorphic normal
frame. At `g=1`, `h=diag λ`, the coefficient is `λⱼ/λₚ−1`, not its negative. -/
theorem c3RefinedTrace_normalFrame_referenceCurvature
    (ω₀ : KahlerForm n M) (φ : M → ℝ) (x : M)
    (frame : C3RefinedTraceNormalCoordinateFrame ω₀ φ x) :
    let g := c3RefinedTracePulledReferenceMetric ω₀ x frame.coord
    c3RefinedTraceReferenceCurvatureSignedError ω₀ φ x =
      ∑ p : Fin n, ∑ j : Fin n,
        (frame.eigenvalue j / frame.eigenvalue p - 1) *
          RCLike.re (c3RefinedTraceReferenceCurvatureInChart g frame.center p p j j) := by
  let chart := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let z := chart x
  let g₀ : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w ↦ ω₀.metricInChart x w
  let h₀ : Matrix (Fin n) (Fin n) ℂ :=
    g₀ z + complexHessian (φ ∘ chart.symm) z
  let gF := c3RefinedTracePulledReferenceMetric ω₀ x frame.coord
  let hF := c3RefinedTracePulledPerturbedMetric ω₀ φ x frame.coord
  let A := EuclideanSpace.clmMatrix (fderiv ℂ frame.coord frame.center)
  let B := A⁻¹
  have hz : z ∈ chart.target := mem_extChartAt_target x
  have hzChart : chartAt (EuclideanSpace ℂ (Fin n)) x x = z := by
    simp [z, chart]
  have hframePos : IsUnit A.det := frame.jacobian_unit frame.center frame.center_mem
  have hAB : A * B = 1 := Matrix.mul_nonsing_inv A hframePos
  have hBA : B * A = 1 := Matrix.nonsing_inv_mul A hframePos
  have hgNormal : gF frame.center = 1 := frame.reference_normal
  have hhDiagonal : hF frame.center =
      Matrix.diagonal (fun i ↦ (frame.eigenvalue i : ℂ)) := frame.perturbed_diagonal
  have hGpull : gF frame.center = A.transpose * g₀ z * A.map star := by
    change A.transpose * ω₀.metricInChart x (frame.coord frame.center) * A.map star =
      A.transpose * ω₀.metricInChart x (chart x) * A.map star
    rw [frame.center_eq]
  have hHpull : hF frame.center = A.transpose * h₀ * A.map star := by
    change A.transpose * (ω₀.metricInChart x (frame.coord frame.center) +
        complexHessian (φ ∘ chart.symm) (frame.coord frame.center)) * A.map star =
      A.transpose * (ω₀.metricInChart x (chart x) +
        complexHessian (φ ∘ chart.symm) (chart x)) * A.map star
    rw [frame.center_eq]
  have hGinvPull : (gF frame.center)⁻¹ = B.map star * (g₀ z)⁻¹ * B.transpose := by
    rw [hGpull]
    exact Matrix.inv_transpose_mul_mul_map_star A B (g₀ z) hBA
  have hHinvPull : (hF frame.center)⁻¹ = B.map star * h₀⁻¹ * B.transpose := by
    rw [hHpull]
    exact Matrix.inv_transpose_mul_mul_map_star A B h₀ hBA
  have hDoublePull :
      (gF frame.center)⁻¹ * hF frame.center * (gF frame.center)⁻¹ =
        B.map star * ((g₀ z)⁻¹ * h₀ * (g₀ z)⁻¹) * B.transpose := by
    rw [hGpull, hHpull]
    exact c3RefinedTrace_pullback_double_inverse A B (g₀ z) h₀ hAB hBA
  have hg0At (i j : Fin n) : ContDiffAt ℝ ∞ (fun w ↦ g₀ w i j) z := by
    exact (ω₀.contDiffOn_metricInChart x i j).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz)
  have hdetg₀ : IsUnit (g₀ z).det :=
    (Matrix.isUnit_iff_isUnit_det (A := g₀ z)).mp
      (ω₀.posDef_metricInChart x hz).isUnit
  have hdetgF : IsUnit (gF frame.center).det := by
    rw [hgNormal]
    simp
  have hframeSmooth := c3RefinedTrace_pulledReferenceMetric_smooth ω₀ φ x frame
  have hcurvFrame (p q j k : Fin n) :=
    c3RefinedTrace_chartCurvature_pullback_of_frame ω₀ φ x frame p q j k
  have hcurvBase (p q j k : Fin n) :=
    c3RefinedTrace_referenceCurvature_eq_chartCurvature g₀ z hg0At hdetg₀ p q j k
  have hcurvBaseChart (p q j k : Fin n) :
      c3RefinedTraceReferenceCurvatureInChart
        (fun w ↦ ω₀.metricInChart x w) (chartAt (EuclideanSpace ℂ (Fin n)) x x) p q j k =
        chartCurvature (fun w ↦ ω₀.metricInChart x w)
          (chartAt (EuclideanSpace ℂ (Fin n)) x x) p q j k := by
    rw [hzChart]
    exact hcurvBase p q j k
  have hcurvPulled (p q j k : Fin n) :
      c3RefinedTraceReferenceCurvatureInChart gF frame.center p q j k =
        chartCurvature gF frame.center p q j k := by
    exact c3RefinedTrace_referenceCurvature_eq_chartCurvature gF frame.center
      (fun i j ↦ hframeSmooth i j) hdetgF p q j k
  let R₀ : Fin n → Fin n → Fin n → Fin n → ℂ :=
    fun p q j k ↦ chartCurvature g₀ z p q j k
  let RF : Fin n → Fin n → Fin n → Fin n → ℂ :=
    fun p q j k ↦ chartCurvature gF frame.center p q j k
  have hRpull (p q j k : Fin n) : RF p q j k =
      ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
        A a p * star (A b q) * A c j * star (A d k) * R₀ a b c d := by
    simpa [RF, R₀, g₀, z, chart] using hcurvFrame p q j k
  let oldFirst : ℂ := ∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n,
    h₀⁻¹ q p * ((g₀ z)⁻¹ * h₀ * (g₀ z)⁻¹) k j * R₀ p q j k
  let oldSecond : ℂ := ∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n,
    (g₀ z)⁻¹ q p * (g₀ z)⁻¹ k j * R₀ p q j k
  have hErrorBase : c3RefinedTraceReferenceCurvatureSignedError ω₀ φ x =
      RCLike.re (oldFirst - oldSecond) := by
    unfold c3RefinedTraceReferenceCurvatureSignedError
    dsimp [chart, z, g₀, h₀, oldFirst, oldSecond]
    simp_rw [hcurvBaseChart, hzChart, sub_mul, Finset.sum_sub_distrib]
    rfl
  have hC1 :
      ∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (hF frame.center)⁻¹ q p *
          ((gF frame.center)⁻¹ * hF frame.center * (gF frame.center)⁻¹) k j * RF p q j k =
      ∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        h₀⁻¹ q p * ((g₀ z)⁻¹ * h₀ * (g₀ z)⁻¹) k j * R₀ p q j k := by
    rw [hHinvPull, hDoublePull]
    simp_rw [hRpull]
    exact c3RefinedTrace_pullback_contract_four A B h₀⁻¹
      ((g₀ z)⁻¹ * h₀ * (g₀ z)⁻¹) hAB R₀
  have hC2 :
      ∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (gF frame.center)⁻¹ q p * (gF frame.center)⁻¹ k j * RF p q j k =
      ∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (g₀ z)⁻¹ q p * (g₀ z)⁻¹ k j * R₀ p q j k := by
    rw [hGinvPull]
    simp_rw [hRpull]
    exact c3RefinedTrace_pullback_contract_four A B (g₀ z)⁻¹ (g₀ z)⁻¹ hAB R₀
  let frameFirst : ℂ := ∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n,
    (hF frame.center)⁻¹ q p *
      ((gF frame.center)⁻¹ * hF frame.center * (gF frame.center)⁻¹) k j * RF p q j k
  let frameSecond : ℂ := ∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n,
    (gF frame.center)⁻¹ q p * (gF frame.center)⁻¹ k j * RF p q j k
  have hErrorFrame : c3RefinedTraceReferenceCurvatureSignedError ω₀ φ x =
      RCLike.re (frameFirst - frameSecond) := by
    rw [hErrorBase]
    congr 1
    dsimp [frameFirst, frameSecond, oldFirst, oldSecond]
    rw [← hC1, ← hC2]
  have hGinvOne : (gF frame.center)⁻¹ = 1 := by
    rw [hgNormal]
    simp
  have hDoubleOne :
      (gF frame.center)⁻¹ * hF frame.center * (gF frame.center)⁻¹ =
        Matrix.diagonal (fun i ↦ (frame.eigenvalue i : ℂ)) := by
    rw [hGinvOne, hhDiagonal]
    simp
  have hlam (i : Fin n) : frame.eigenvalue i ≠ 0 :=
    ne_of_gt (frame.eigenvalue_pos i)
  have hFrameDiff : frameFirst - frameSecond =
      ∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (((Matrix.diagonal (fun i ↦ (frame.eigenvalue i : ℂ)))⁻¹ q p *
          Matrix.diagonal (fun i ↦ (frame.eigenvalue i : ℂ)) k j -
          (1 : Matrix (Fin n) (Fin n) ℂ) q p *
            (1 : Matrix (Fin n) (Fin n) ℂ) k j) * RF p q j k) := by
    dsimp [frameFirst, frameSecond]
    rw [hDoubleOne, hhDiagonal, hGinvOne]
    simp_rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hFrameSigned : RCLike.re (frameFirst - frameSecond) =
      ∑ p : Fin n, ∑ j : Fin n,
        (frame.eigenvalue j / frame.eigenvalue p - 1) * RCLike.re (RF p p j j) := by
    rw [hFrameDiff]
    exact c3RefinedTrace_diagonalSignedContraction frame.eigenvalue hlam RF
  calc
    c3RefinedTraceReferenceCurvatureSignedError ω₀ φ x =
        ∑ p : Fin n, ∑ j : Fin n,
          (frame.eigenvalue j / frame.eigenvalue p - 1) *
            RCLike.re (c3RefinedTraceReferenceCurvatureInChart gF frame.center p p j j) := by
      rw [hErrorFrame, hFrameSigned]
      dsimp [RF]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro j hj
      rw [← hcurvPulled p p j j]

end KahlerForm
