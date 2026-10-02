module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.Basic

/-!
# DiagonalWeights for the differentiated Ricci contraction

Székelyhidi, An Introduction to Extremal Kähler Metrics, §3.3, proof of
Lemma 3.9, printed pp. 44–45: two-sided metric comparison and the
linear-plus-quadratic connection correction.

Two-sided positive eigenvalue bounds control d_i/(d_j*d_k) between B^(-3) and B^3. For d=1 and B>=1 these bracket one; n=0 statements are empty. No division by n or by energy.
-/

public section

open scoped Manifold ContDiff BigOperators ComplexOrder MatrixOrder
open ContinuousAlternatingMap
open Matrix

namespace KahlerForm

/-- Each perturbed contraction weight is bounded below using only the two trace bounds. -/
theorem c3_diagonal_weight_lower_bound {n : ℕ}
    (d : Fin n → ℝ) (B : ℝ) (hB : 0 < B)
    (hd : ∀ i, 0 < d i)
    (hdb : ∀ i, B⁻¹ ≤ d i ∧ d i ≤ B) :
    ∀ i j k, B⁻¹ ^ 3 ≤ d i / (d j * d k) := by
  intro i j k
  have hden : 0 < d j * d k := mul_pos (hd j) (hd k)
  have hden_le : d j * d k ≤ B * B := by
    calc
      d j * d k ≤ B * d k := mul_le_mul_of_nonneg_right (hdb j).2 (le_of_lt (hd k))
      _ ≤ B * B := mul_le_mul_of_nonneg_left (hdb k).2 (le_of_lt hB)
  have hcoeff : B⁻¹ ^ 3 * (d j * d k) ≤ d i := by
    calc
      B⁻¹ ^ 3 * (d j * d k) ≤ B⁻¹ ^ 3 * (B * B) :=
        mul_le_mul_of_nonneg_left hden_le
          (pow_nonneg (inv_nonneg.mpr (le_of_lt hB)) 3)
      _ = B⁻¹ := by field_simp [hB.ne']
      _ ≤ d i := (hdb i).1
  exact (le_div_iff₀ hden).2 hcoeff

/-- The reverse comparison controls each diagonal metric coefficient above. -/
theorem c3_diagonal_weight_upper_bound {n : ℕ}
    (d : Fin n → ℝ) (B : ℝ) (hB : 0 < B)
    (hd : ∀ i, 0 < d i)
    (hdb : ∀ i, B⁻¹ ≤ d i ∧ d i ≤ B) :
    ∀ i j k, d i / (d j * d k) ≤ B ^ 3 := by
  intro i j k
  have hden : 0 < d j * d k := mul_pos (hd j) (hd k)
  have hBj : 1 ≤ B * d j := by
    calc
      1 = B * B⁻¹ := by field_simp [hB.ne']
      _ ≤ B * d j := mul_le_mul_of_nonneg_left (hdb j).1 (le_of_lt hB)
  have hBk : 1 ≤ B * d k := by
    calc
      1 = B * B⁻¹ := by field_simp [hB.ne']
      _ ≤ B * d k := mul_le_mul_of_nonneg_left (hdb k).1 (le_of_lt hB)
  have hprod : 1 ≤ (B * d j) * (B * d k) := by nlinarith
  apply (div_le_iff₀ hden).2
  calc
    d i ≤ B := (hdb i).2
    _ = B * 1 := by ring
    _ ≤ B * ((B * d j) * (B * d k)) := mul_le_mul_of_nonneg_left hprod (le_of_lt hB)
    _ = B ^ 3 * (d j * d k) := by ring

/-- A diagonal Calabi-energy bound controls the unweighted frame sum. -/
theorem c3_unweighted_energy_bound_of_diagonal_energy {n : ℕ}
    (T : Fin n → Fin n → Fin n → ℂ) (d : Fin n → ℝ) (B E : ℝ)
    (hB : 0 < B) (hd : ∀ i, 0 < d i)
    (hdb : ∀ i, B⁻¹ ≤ d i ∧ d i ≤ B)
    (henergy : ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      (d i / (d j * d k)) * ‖T i j k‖ ^ 2 ≤ E) :
    ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ‖T i j k‖ ^ 2 ≤ B ^ 3 * E := by
  have hweight := c3_diagonal_weight_lower_bound d B hB hd hdb
  have hfactor (i j k : Fin n) :
      1 ≤ B ^ 3 * (d i / (d j * d k)) := by
    calc
      1 = B ^ 3 * (B⁻¹ ^ 3) := by field_simp [hB.ne']
      _ ≤ B ^ 3 * (d i / (d j * d k)) :=
        mul_le_mul_of_nonneg_left (hweight i j k) (pow_nonneg (le_of_lt hB) 3)
  have hterm (i j k : Fin n) :
      ‖T i j k‖ ^ 2 ≤ B ^ 3 * ((d i / (d j * d k)) * ‖T i j k‖ ^ 2) := by
    calc
      ‖T i j k‖ ^ 2 = 1 * ‖T i j k‖ ^ 2 := by ring
      _ ≤ (B ^ 3 * (d i / (d j * d k))) * ‖T i j k‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (hfactor i j k) (sq_nonneg _)
      _ = B ^ 3 * ((d i / (d j * d k)) * ‖T i j k‖ ^ 2) := by ring
  calc
    ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ‖T i j k‖ ^ 2 ≤
        ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          B ^ 3 * ((d i / (d j * d k)) * ‖T i j k‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro k hk
      exact hterm i j k
    _ = B ^ 3 * (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          (d i / (d j * d k)) * ‖T i j k‖ ^ 2) := by simp_rw [Finset.mul_sum]
    _ ≤ B ^ 3 * E := mul_le_mul_of_nonneg_left henergy (pow_nonneg (le_of_lt hB) 3)

end KahlerForm
