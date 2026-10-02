module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.Basic
public import CalabiYau.Mathlib.Analysis.Matrix.Hermitian.SimultaneousDiagonalization
public import CalabiYau.Mathlib.LinearAlgebra.Matrix.PullbackInverse

/-!
# MetricFrame for the differentiated Ricci contraction

Székelyhidi, An Introduction to Extremal Kähler Metrics, §3.3, proof of
Lemma 3.9, printed pp. 44–45: two-sided metric comparison and the
linear-plus-quadratic connection correction.

Simultaneous reference frame, inverse pullback and trace/eigenvalue comparison; transpose-star convention P^t G conjugate(P)=1, not P* G P. Empty index case and positive one-dimensional scaling satisfy the identities.
-/

public section

open scoped Manifold ContDiff BigOperators ComplexOrder MatrixOrder
open ContinuousAlternatingMap
open Matrix

namespace KahlerForm

/-- Simultaneous diagonalization in the reference-frame convention used by the
coordinate Ricci-derivative estimates, together with the two relative trace sums. -/
theorem c3_exists_simultaneous_reference_frame {n : ℕ}
    (G A : Matrix (Fin n) (Fin n) ℂ) (hG : G.PosDef) (hA : A.PosDef) :
    ∃ P : Matrix (Fin n) (Fin n) ℂ, ∃ d : Fin n → ℝ,
      P.transpose * G * P.map star = 1 ∧
      (∀ i, 0 < d i) ∧
      P.transpose * A * P.map star = Matrix.diagonal (RCLike.ofReal ∘ d) ∧
      (∑ i, d i) = (G⁻¹ * A).trace.re ∧
      (∑ i, (d i)⁻¹) = (A⁻¹ * G).trace.re := by
  classical
  obtain ⟨Q, d, hQG, hQA⟩ :=
    Matrix.PosDef.exists_simultaneous_diagonalization hG hA.isHermitian
  have hd : ∀ i, 0 < d i :=
    (Matrix.posDef_iff_forall_pos_of_conjTranspose_mul_mul_eq hQG hQA).1 hA
  have htrans : (Q.map star).transpose = Q.conjTranspose := by
    ext i j
    simp
  have hmap : (Q.map star).map star = Q := by
    ext i j
    simp
  refine ⟨Q.map star, d, ?_, hd, ?_, ?_, ?_⟩
  · rw [htrans, hmap]
    exact hQG
  · rw [htrans, hmap]
    exact hQA
  · exact (Matrix.re_trace_inv_mul_eq_sum_of_conjTranspose_mul_mul_eq hQG hQA).symm
  · exact (Matrix.re_trace_inv_mul_eq_sum_inv_of_conjTranspose_mul_mul_eq hQG hQA
      (fun i ↦ (hd i).ne')).symm

theorem sum_inv_metric_mul_eq_pullback {n : ℕ}
    (A G : Matrix (Fin n) (Fin n) ℂ) (q t : Fin n) :
    (∑ x : Fin n × Fin n,
      G⁻¹ x.1 x.2 * A q x.2 * star (A t x.1)) =
      (A.map star * G⁻¹ * A.transpose) t q := by
  classical
  have hentry :
      (A.map star * G⁻¹ * A.transpose) t q =
        ∑ x : Fin n, ∑ y : Fin n,
          star (A t x) * G⁻¹ x y * A q y := by
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply]
    calc
      ∑ y : Fin n, (∑ x : Fin n, star (A t x) * G⁻¹ x y) * A q y =
          ∑ y : Fin n, ∑ x : Fin n,
            star (A t x) * G⁻¹ x y * A q y := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [← Finset.sum_mul]
      _ = ∑ x : Fin n, ∑ y : Fin n,
            star (A t x) * G⁻¹ x y * A q y := Finset.sum_comm
  calc
    _ = ∑ x : Fin n, ∑ y : Fin n,
          star (A t x) * G⁻¹ x y * A q y := by
      simp only [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      ring
    _ = _ := hentry.symm

theorem c3_reconstruct_metric_from_diagonal_frame {n : ℕ}
    (A D P Q : Matrix (Fin n) (Fin n) ℂ)
    (hPQ : P * Q = 1) (_hQP : Q * P = 1)
    (hdiag : P.transpose * A * P.map star = D) :
    Q.transpose * D * Q.map star = A := by
  have hqtpt : Q.transpose * P.transpose = 1 := by
    rw [← Matrix.transpose_mul, hPQ]
    simp
  have hpstqst : P.map star * Q.map star = 1 := by
    ext i j
    have h := congrArg star (congrFun (congrFun hPQ i) j)
    simpa [Matrix.mul_apply, Matrix.one_apply, star_sum, star_mul, mul_comm] using h
  calc
    Q.transpose * D * Q.map star =
        Q.transpose * (P.transpose * A * P.map star) * Q.map star := by rw [hdiag]
    _ = (Q.transpose * P.transpose) * A * (P.map star * Q.map star) := by
      simp only [Matrix.mul_assoc]
    _ = A := by rw [hqtpt, hpstqst]; simp

theorem c3_frame_metric_sum_identities {n : ℕ}
    (A D P Q : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ)
    (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hD : D = Matrix.diagonal d)
    (hdiag : P.transpose * A * P.map star = D) :
    (∀ p s, ∑ y : Fin n × Fin n,
      D y.1 y.2 * Q y.1 p * star (Q y.2 s) = A p s) ∧
    (∀ q t, ∑ y : Fin n × Fin n,
      D⁻¹ y.1 y.2 * P q y.2 * star (P t y.1) = A⁻¹ t q) := by
  have hA : Q.transpose * D * Q.map star = A :=
    c3_reconstruct_metric_from_diagonal_frame A D P Q hPQ hQP hdiag
  constructor
  · intro p s
    have hs : ∑ y : Fin n × Fin n,
        D y.1 y.2 * Q y.1 p * star (Q y.2 s) =
          (Q.transpose * D * Q.map star) p s := by
      rw [hD]
      simp [Fintype.sum_prod_type, Matrix.diagonal_apply, Matrix.mul_apply,
        Matrix.transpose_apply, Matrix.map_apply, Finset.sum_ite_eq',
        mul_comm, mul_assoc]
    rw [hs, hA]
  · intro q t
    calc
      _ = (P.map star * D⁻¹ * P.transpose) t q :=
        sum_inv_metric_mul_eq_pullback P D q t
      _ = (Q.transpose * D * Q.map star)⁻¹ t q := by
        rw [Matrix.inv_transpose_mul_mul_map_star Q P D hPQ]
      _ = A⁻¹ t q := by rw [hA]

/-- Two trace sums bound each positive simultaneous eigenvalue in both directions. -/
theorem c3_eigenvalue_bounds_of_trace_sums {n : ℕ}
    (d : Fin n → ℝ) (B : ℝ) (hB : 0 < B)
    (hd : ∀ i, 0 < d i)
    (hupper : ∑ i : Fin n, d i ≤ B)
    (hlower : ∑ i : Fin n, (d i)⁻¹ ≤ B) :
    ∀ i, B⁻¹ ≤ d i ∧ d i ≤ B := by
  intro i
  have hsum_upper : d i ≤ ∑ j : Fin n, d j :=
    Finset.single_le_sum (fun j hj => le_of_lt (hd j)) (Finset.mem_univ i)
  have hsum_lower : (d i)⁻¹ ≤ ∑ j : Fin n, (d j)⁻¹ :=
    Finset.single_le_sum (fun j hj => inv_nonneg.mpr (le_of_lt (hd j)))
      (Finset.mem_univ i)
  constructor
  · have hrecip : (d i)⁻¹ ≤ B := hsum_lower.trans hlower
    have hmul : 1 ≤ d i * B := by
      calc
        1 = (d i)⁻¹ * d i := by field_simp [(hd i).ne']
        _ ≤ B * d i := mul_le_mul_of_nonneg_right hrecip (le_of_lt (hd i))
        _ = d i * B := mul_comm _ _
    simpa [one_div] using (div_le_iff₀ hB).2 hmul
  · exact hsum_upper.trans hupper

/-- Two relative trace bounds provide a simultaneous reference-orthonormal frame whose
positive perturbed-metric eigenvalues are individually bounded above and below. -/
theorem c3_exists_trace_controlled_diagonal_frame {n : ℕ}
    (G A : Matrix (Fin n) (Fin n) ℂ) (B : ℝ)
    (hG : G.PosDef) (hA : A.PosDef) (hB : 0 < B)
    (hupper : (G⁻¹ * A).trace.re ≤ B)
    (hlower : (A⁻¹ * G).trace.re ≤ B) :
    ∃ P : Matrix (Fin n) (Fin n) ℂ, ∃ d : Fin n → ℝ,
      P.transpose * G * P.map star = 1 ∧
      P.transpose * A * P.map star = Matrix.diagonal (RCLike.ofReal ∘ d) ∧
      (∀ i, B⁻¹ ≤ d i ∧ d i ≤ B) := by
  obtain ⟨P, d, hPG, hd, hPA, hsumA, hsumG⟩ :=
    c3_exists_simultaneous_reference_frame G A hG hA
  have hdb := c3_eigenvalue_bounds_of_trace_sums d B hB hd
    (hsumA ▸ hupper) (hsumG ▸ hlower)
  exact ⟨P, d, hPG, hPA, hdb⟩

end KahlerForm
