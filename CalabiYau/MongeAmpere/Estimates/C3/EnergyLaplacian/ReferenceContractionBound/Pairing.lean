module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceContractionBound.Basic

/-!
# Pairing for the reference-curvature contraction

Székelyhidi, An Introduction to Extremal Kähler Metrics, §3.3, proof of Lemma 3.9, terms following (3.15), printed p. 45; finite tensor contraction algebra implementing that proof.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal BigOperators ComplexOrder MatrixOrder
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

theorem referenceContraction_star_sum {ι : Type*} [Fintype ι] (f : ι → ℂ) :
    star (∑ i, f i) = ∑ i, star (f i) := by
  change starRingEnd ℂ (∑ i, f i) = _
  exact map_sum (starRingEnd ℂ) f Finset.univ

theorem referenceContraction_fintype_mul_sum {ι : Type*} [Fintype ι]
    (a : ℂ) (f : ι → ℂ) : a * (∑ i, f i) = ∑ i, a * f i := by
  exact map_sum (AddMonoidHom.mulLeft a) f Finset.univ

theorem referenceContraction_fintype_sum_mul {ι : Type*} [Fintype ι]
    (f : ι → ℂ) (a : ℂ) : (∑ i, f i) * a = ∑ i, f i * a := by
  exact map_sum (AddMonoidHom.mulRight a) f Finset.univ

set_option maxHeartbeats 1000000 in
theorem referenceContraction_pair_eq_frame_components {n : ℕ}
    (g : Matrix (Fin n) (Fin n) ℂ) (z : EuclideanSpace ℂ (Fin n))
    (B P : Matrix (Fin n) (Fin n) ℂ)
    (T U : Fin n → Fin n → Fin n → ℂ)
    (hUpper : ∀ i a, g i a = ∑ r, B r i * star (B r a))
    (hLower : ∀ b j, g⁻¹ b j = ∑ r, P j r * star (P b r)) :
    c3Pair (fun _ : EuclideanSpace ℂ (Fin n) ↦ g) z T U =
      ∑ i, ∑ j, ∑ k,
        referenceContraction_tensorFrameTransform B P T i j k *
          star (referenceContraction_tensorFrameTransform B P U i j k) := by
  classical
  unfold c3Pair referenceContraction_tensorFrameTransform
  simp_rw [hUpper, hLower]
  simp_rw [referenceContraction_fintype_mul_sum, referenceContraction_fintype_sum_mul,
    referenceContraction_star_sum]
  let ι := Fin n × (Fin n × (Fin n × (Fin n × (Fin n × (Fin n × (Fin n × (Fin n × Fin n)))))))
  let e : ι ≃ ι := {
    toFun := fun p ↦
      (p.2.2.2.2.2.2.2.2,
        (p.2.2.2.2.2.2.2.1,
          (p.2.2.2.2.2.2.1,
            (p.1, (p.2.1, (p.2.2.1,
              (p.2.2.2.1, (p.2.2.2.2.1, p.2.2.2.2.2.1))))))))
    invFun := fun p ↦
      (p.2.2.2.1,
        (p.2.2.2.2.1,
          (p.2.2.2.2.2.1,
            (p.2.2.2.2.2.2.1,
              (p.2.2.2.2.2.2.2.1,
                (p.2.2.2.2.2.2.2.2,
                  (p.2.2.1, (p.2.1, p.1))))))))
    left_inv := by intro p; simp [ι]
    right_inv := by intro p; simp [ι] }
  let f : ι → ℂ := fun p ↦
    B p.2.2.2.2.2.2.2.2 p.1 * star (B p.2.2.2.2.2.2.2.2 p.2.2.2.1) *
      (P p.2.1 p.2.2.2.2.2.2.2.1 * star (P p.2.2.2.2.1 p.2.2.2.2.2.2.2.1)) *
      (P p.2.2.1 p.2.2.2.2.2.2.1 * star (P p.2.2.2.2.2.1 p.2.2.2.2.2.2.1)) *
      T p.1 p.2.1 p.2.2.1 * star (U p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1)
  let h : ι → ℂ := fun p ↦
    B p.1 p.2.2.2.1 * P p.2.2.2.2.1 p.2.1 * P p.2.2.2.2.2.1 p.2.2.1 *
      T p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 *
        star (B p.1 p.2.2.2.2.2.2.1 * P p.2.2.2.2.2.2.2.1 p.2.1 *
          P p.2.2.2.2.2.2.2.2 p.2.2.1 *
          U p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2)
  have hsum : (∑ p : ι, f p) = ∑ p : ι, h p :=
    Fintype.sum_equiv e f h (by
      intro p
      change f p = h (p.2.2.2.2.2.2.2.2,
        (p.2.2.2.2.2.2.2.1, (p.2.2.2.2.2.2.1,
          (p.1, (p.2.1, (p.2.2.1,
            (p.2.2.2.1, (p.2.2.2.2.1, p.2.2.2.2.2.1))))))))
      simp only [f, h, ι, star_mul]
      ac_rfl)
  simpa only [ι, f, h, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul,
    referenceContraction_fintype_mul_sum, referenceContraction_fintype_sum_mul,
    referenceContraction_star_sum] using hsum

theorem c3_star_sum {ι : Type*} [Fintype ι] (f : ι → ℂ) :
    star (∑ i, f i) = ∑ i, star (f i) := by
  change starRingEnd ℂ (∑ i, f i) = _
  exact map_sum (starRingEnd ℂ) f Finset.univ

theorem c3_fintype_mul_sum {ι : Type*} [Fintype ι] (a : ℂ) (f : ι → ℂ) :
    a * (∑ i, f i) = ∑ i, a * f i := by
  exact map_sum (AddMonoidHom.mulLeft a) f Finset.univ

theorem c3_fintype_sum_mul {ι : Type*} [Fintype ι] (f : ι → ℂ) (a : ℂ) :
    (∑ i, f i) * a = ∑ i, f i * a := by
  exact map_sum (AddMonoidHom.mulRight a) f Finset.univ

set_option maxHeartbeats 1000000 in
theorem c3Pair_eq_frame_components_local {n : ℕ}
    (g : Matrix (Fin n) (Fin n) ℂ) (z : EuclideanSpace ℂ (Fin n))
    (B P : Matrix (Fin n) (Fin n) ℂ)
    (T U : Fin n → Fin n → Fin n → ℂ)
    (hUpper : ∀ i a, g i a = ∑ r, B r i * star (B r a))
    (hLower : ∀ b j, g⁻¹ b j = ∑ r, P j r * star (P b r)) :
    c3Pair (fun _ : EuclideanSpace ℂ (Fin n) ↦ g) z T U =
      ∑ i, ∑ j, ∑ k,
        referenceContraction_tensorFrameTransform B P T i j k *
          star (referenceContraction_tensorFrameTransform B P U i j k) := by
  have hPair :
      c3Pair (fun _ : EuclideanSpace ℂ (Fin n) ↦ g) z T U =
        ∑ i, ∑ j, ∑ k,
          referenceContraction_tensorFrameTransform B P T i j k *
            star (referenceContraction_tensorFrameTransform B P U i j k) := by
    classical
    unfold c3Pair referenceContraction_tensorFrameTransform
    simp_rw [hUpper, hLower]
    simp_rw [c3_fintype_mul_sum, c3_fintype_sum_mul, c3_star_sum]
    let ι := Fin n × (Fin n × (Fin n × (Fin n × (Fin n × (Fin n × (Fin n × (Fin n × Fin n)))))) )
    let e : ι ≃ ι := {
      toFun := fun p ↦
        (p.2.2.2.2.2.2.2.2,
          (p.2.2.2.2.2.2.2.1,
            (p.2.2.2.2.2.2.1,
              (p.1, (p.2.1, (p.2.2.1,
                (p.2.2.2.1, (p.2.2.2.2.1, p.2.2.2.2.2.1))))))))
      invFun := fun p ↦
        (p.2.2.2.1,
          (p.2.2.2.2.1,
            (p.2.2.2.2.2.1,
              (p.2.2.2.2.2.2.1,
                (p.2.2.2.2.2.2.2.1,
                  (p.2.2.2.2.2.2.2.2,
                    (p.2.2.1, (p.2.1, p.1))))))))
      left_inv := by intro p; simp [ι]
      right_inv := by intro p; simp [ι] }
    let f : ι → ℂ := fun p ↦
      B p.2.2.2.2.2.2.2.2 p.1 * star (B p.2.2.2.2.2.2.2.2 p.2.2.2.1) *
        (P p.2.1 p.2.2.2.2.2.2.2.1 * star (P p.2.2.2.2.1 p.2.2.2.2.2.2.2.1)) *
        (P p.2.2.1 p.2.2.2.2.2.2.1 * star (P p.2.2.2.2.2.1 p.2.2.2.2.2.2.1)) *
        T p.1 p.2.1 p.2.2.1 * star (U p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1)
    let g : ι → ℂ := fun p ↦
      B p.1 p.2.2.2.1 * P p.2.2.2.2.1 p.2.1 * P p.2.2.2.2.2.1 p.2.2.1 *
        T p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 *
          star (B p.1 p.2.2.2.2.2.2.1 * P p.2.2.2.2.2.2.2.1 p.2.1 *
            P p.2.2.2.2.2.2.2.2 p.2.2.1 *
            U p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2)
    have hsum : (∑ p : ι, f p) = ∑ p : ι, g p :=
      Fintype.sum_equiv e f g (by
        intro p
        change f p = g (p.2.2.2.2.2.2.2.2,
          (p.2.2.2.2.2.2.2.1, (p.2.2.2.2.2.2.1,
            (p.1, (p.2.1, (p.2.2.1,
              (p.2.2.2.1, (p.2.2.2.2.1, p.2.2.2.2.2.1))))))))
        simp only [f, g, ι, star_mul]
        ac_rfl)
    simpa only [ι, f, g, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul,
      c3_fintype_mul_sum, c3_fintype_sum_mul, c3_star_sum] using hsum
  exact hPair

set_option maxHeartbeats 1000000 in
theorem c3_pair_arbitrary_frame_weighted {n : ℕ}
    (d : Fin n → ℝ) (hd : ∀ i, 0 < d i)
    (G : Matrix (Fin n) (Fin n) ℂ) (z : EuclideanSpace ℂ (Fin n))
    (P Q : Matrix (Fin n) (Fin n) ℂ) (T : Fin n → Fin n → Fin n → ℂ)
    (hUpper : ∀ i a, G i a = ∑ r,
      ((Real.sqrt (d r) : ℝ) : ℂ) * Q r i * star (((Real.sqrt (d r) : ℝ) : ℂ) * Q r a))
    (hLower : ∀ b j, G⁻¹ b j = ∑ r,
      (((Real.sqrt (d r))⁻¹ : ℝ) : ℂ) * P j r *
        star ((((Real.sqrt (d r))⁻¹ : ℝ) : ℂ) * P b r)) :
    c3Pair (fun _ : EuclideanSpace ℂ (Fin n) ↦ G) z T T =
      ∑ i, ∑ j, ∑ k,
        ((d i / (d j * d k) : ℝ) : ℂ) *
          referenceContraction_tensorFrameTransform Q P T i j k * star (referenceContraction_tensorFrameTransform Q P T i j k) := by
  let B : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i ↦ (Real.sqrt (d i) : ℂ)) * Q
  let C : Matrix (Fin n) (Fin n) ℂ :=
    P * Matrix.diagonal (fun i ↦ ((Real.sqrt (d i))⁻¹ : ℂ))
  have hU : ∀ i a, G i a = ∑ r, B r i * star (B r a) := by
    intro i a
    simpa [B, Matrix.mul_apply, Matrix.diagonal_apply] using hUpper i a
  have hCentry (b j : Fin n) : C b j =
      P b j * (((Real.sqrt (d j))⁻¹ : ℝ) : ℂ) := by
    simp [C, Matrix.mul_apply, Matrix.diagonal_apply]
  have hBentry (i a : Fin n) : B i a =
      ((Real.sqrt (d i) : ℝ) : ℂ) * Q i a := by
    simp [B, Matrix.mul_apply, Matrix.diagonal_apply]
  have hL : ∀ b j, G⁻¹ b j = ∑ r, C j r * star (C b r) := by
    intro b j
    rw [hLower b j]
    apply Finset.sum_congr rfl
    intro r hr
    rw [hCentry, hCentry]
    simp only [star_mul]
    simp
    ring
  have hframe := c3Pair_eq_frame_components_local G z B C T T hU hL
  let s : Fin n → Fin n → Fin n → ℝ :=
    fun i j k ↦ Real.sqrt (d i) / (Real.sqrt (d j) * Real.sqrt (d k))
  have hsquare (i j k : Fin n) : s i j k ^ 2 = d i / (d j * d k) := by
    have hi := Real.sq_sqrt (le_of_lt (hd i))
    have hj := Real.sq_sqrt (le_of_lt (hd j))
    have hk := Real.sq_sqrt (le_of_lt (hd k))
    have hden : Real.sqrt (d j) * Real.sqrt (d k) ≠ 0 :=
      ne_of_gt (mul_pos (Real.sqrt_pos.2 (hd j)) (Real.sqrt_pos.2 (hd k)))
    dsimp [s]
    rw [div_pow, hi, mul_pow, hj, hk]
  have htransform (i j k : Fin n) :
      referenceContraction_tensorFrameTransform B C T i j k =
        ((s i j k : ℝ) : ℂ) * referenceContraction_tensorFrameTransform Q P T i j k := by
    have hscale :
        ((Real.sqrt (d i) : ℝ) : ℂ) *
            (((Real.sqrt (d j))⁻¹ : ℝ) : ℂ) *
            (((Real.sqrt (d k))⁻¹ : ℝ) : ℂ) = ((s i j k : ℝ) : ℂ) := by
      have hreal : Real.sqrt (d i) * (Real.sqrt (d j))⁻¹ *
          (Real.sqrt (d k))⁻¹ = s i j k := by
        dsimp [s]
        field_simp [ne_of_gt (Real.sqrt_pos.2 (hd j)),
          ne_of_gt (Real.sqrt_pos.2 (hd k))]
      exact_mod_cast hreal
    simp only [referenceContraction_tensorFrameTransform]
    simp_rw [hBentry, hCentry]
    have hterm (a b c : Fin n) :
        (((Real.sqrt (d i) : ℝ) : ℂ) * Q i a) *
            (P b j * (((Real.sqrt (d j))⁻¹ : ℝ) : ℂ)) *
            (P c k * (((Real.sqrt (d k))⁻¹ : ℝ) : ℂ)) * T a b c =
          (((Real.sqrt (d i) : ℝ) : ℂ) *
            (((Real.sqrt (d j))⁻¹ : ℝ) : ℂ) *
            (((Real.sqrt (d k))⁻¹ : ℝ) : ℂ)) *
            (Q i a * P b j * P c k * T a b c) := by ring
    calc
      _ = ∑ a, ∑ b, ∑ c,
          (((Real.sqrt (d i) : ℝ) : ℂ) *
            (((Real.sqrt (d j))⁻¹ : ℝ) : ℂ) *
            (((Real.sqrt (d k))⁻¹ : ℝ) : ℂ)) *
            (Q i a * P b j * P c k * T a b c) := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        apply Finset.sum_congr rfl
        intro c hc
        exact hterm a b c
      _ = (((Real.sqrt (d i) : ℝ) : ℂ) *
          (((Real.sqrt (d j))⁻¹ : ℝ) : ℂ) *
          (((Real.sqrt (d k))⁻¹ : ℝ) : ℂ)) *
          referenceContraction_tensorFrameTransform Q P T i j k := by
        simp_rw [← Finset.mul_sum]
        rfl
      _ = ((s i j k : ℝ) : ℂ) *
          referenceContraction_tensorFrameTransform Q P T i j k := by rw [hscale]
  calc
    c3Pair (fun _ : EuclideanSpace ℂ (Fin n) ↦ G) z T T =
        ∑ i, ∑ j, ∑ k,
          referenceContraction_tensorFrameTransform B C T i j k * star (referenceContraction_tensorFrameTransform B C T i j k) := hframe
    _ = ∑ i, ∑ j, ∑ k,
          ((d i / (d j * d k) : ℝ) : ℂ) *
            referenceContraction_tensorFrameTransform Q P T i j k * star (referenceContraction_tensorFrameTransform Q P T i j k) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      rw [htransform]
      have hsstar : star ((s i j k : ℝ) : ℂ) = ((s i j k : ℝ) : ℂ) := by simp
      rw [star_mul, hsstar]
      have hcast : (((s i j k : ℝ) : ℂ) ^ 2) =
          ((d i / (d j * d k) : ℝ) : ℂ) := by
        exact_mod_cast hsquare i j k
      rw [show (((s i j k : ℝ) : ℂ) *
          referenceContraction_tensorFrameTransform Q P T i j k) *
          (star (referenceContraction_tensorFrameTransform Q P T i j k) * ((s i j k : ℝ) : ℂ)) =
          ((s i j k : ℝ) : ℂ) ^ 2 *
            referenceContraction_tensorFrameTransform Q P T i j k * star (referenceContraction_tensorFrameTransform Q P T i j k) by ring]
      rw [hcast]

end KahlerForm
