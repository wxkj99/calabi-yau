module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.Basic
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.ContractionBound.FrameBounds
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.ContractionBound.DiagonalWeights

/-!
# DiagonalAction for the differentiated Ricci contraction

Székelyhidi, An Introduction to Extremal Kähler Metrics, §3.3, proof of
Lemma 3.9, printed pp. 44–45: two-sided metric comparison and the
linear-plus-quadratic connection correction.

The diagonal weighted action bound has linear and quadratic terms under `B > 0`, `E ≥ 0`, `K ≥ 0`, and positive eigenvalues. The action vanishes for `Fin 0`; in dimension one the weight and raising factors give the pairing coefficient `1/d^2`.
-/

public section

open scoped Manifold ContDiff BigOperators ComplexOrder MatrixOrder
open ContinuousAlternatingMap
open Matrix

namespace KahlerForm

theorem c3_frame_action_bound_of_diagonal_energy
    {n : ℕ} (T V : Fin n → Fin n → Fin n → ℂ) (d : Fin n → ℝ)
    (B E D : ℝ) (hB : 0 < B) (hE : 0 ≤ E) (hD : 0 ≤ D)
    (hd : ∀ i, 0 < d i) (hdb : ∀ i, B⁻¹ ≤ d i ∧ d i ≤ B)
    (henergy : ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      (d i / (d j * d k)) * ‖T i j k‖ ^ 2 ≤ E)
    (hV : ∀ i j k, ‖V i j k‖ ≤ D * (1 + Real.sqrt (B ^ 3 * E))) :
    ‖∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      (d i / (d j * d k)) * T i j k * V i j k‖ ≤
        B ^ 3 * (n : ℝ) ^ 3 * D *
          (Real.sqrt (B ^ 3 * E) + B ^ 3 * E) := by
  have hE0 : 0 ≤ B ^ 3 * E := mul_nonneg (pow_nonneg (le_of_lt hB) 3) hE
  have hunweighted := c3_unweighted_energy_bound_of_diagonal_energy T d B E hB hd hdb henergy
  have hcomp := c3_frame_tensor_component_bound_of_energy_sum T (B ^ 3 * E) hE0 hunweighted
  have hterm (i j k : Fin n) :
      ‖(d i / (d j * d k)) * T i j k * V i j k‖ ≤
        B ^ 3 * D * (Real.sqrt (B ^ 3 * E) + B ^ 3 * E) := by
    have hwt : 0 ≤ d i / (d j * d k) :=
      div_nonneg (le_of_lt (hd i)) (le_of_lt (mul_pos (hd j) (hd k)))
    have hcast : ((d i / (d j * d k) : ℝ) : ℂ) =
        (d i : ℂ) / ((d j : ℂ) * (d k : ℂ)) := by push_cast; rfl
    have hnormw : ‖((d i / (d j * d k) : ℝ) : ℂ)‖ = d i / (d j * d k) := by
      exact (RCLike.norm_ofReal (K := ℂ) _).trans (abs_of_nonneg hwt)
    rw [← hcast, norm_mul, norm_mul, hnormw]
    calc
      (d i / (d j * d k) * ‖T i j k‖) * ‖V i j k‖ ≤
          (d i / (d j * d k) * Real.sqrt (B ^ 3 * E)) *
            (D * (1 + Real.sqrt (B ^ 3 * E))) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hcomp i j k) hwt) (hV i j k)
          (by positivity) (by positivity)
      _ ≤ (B ^ 3 * Real.sqrt (B ^ 3 * E)) *
            (D * (1 + Real.sqrt (B ^ 3 * E))) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (c3_diagonal_weight_upper_bound d B hB hd hdb i j k)
            (Real.sqrt_nonneg _)) (mul_nonneg hD (by positivity))
      _ = B ^ 3 * D * (Real.sqrt (B ^ 3 * E) + B ^ 3 * E) := by
        ring_nf
        rw [Real.sq_sqrt hE0]
        ring
  have hsum :
      ‖∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (d i / (d j * d k)) * T i j k * V i j k‖ ≤
        ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          ‖(d i / (d j * d k)) * T i j k * V i j k‖ := by
    calc
      _ ≤ ∑ i : Fin n, ‖∑ j : Fin n, ∑ k : Fin n,
          (d i / (d j * d k)) * T i j k * V i j k‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, ‖∑ k : Fin n,
          (d i / (d j * d k)) * T i j k * V i j k‖ := by
        apply Finset.sum_le_sum
        intro i hi
        exact norm_sum_le _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact norm_sum_le _ _
  calc
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        ‖(d i / (d j * d k)) * T i j k * V i j k‖ := hsum
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        B ^ 3 * D * (Real.sqrt (B ^ 3 * E) + B ^ 3 * E) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro k hk
      exact hterm i j k
    _ = (n : ℝ) ^ 3 * (B ^ 3 * D * (Real.sqrt (B ^ 3 * E) + B ^ 3 * E)) := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring
    _ = B ^ 3 * (n : ℝ) ^ 3 * D *
        (Real.sqrt (B ^ 3 * E) + B ^ 3 * E) := by ring
/-- A raised connection correction with bounded frame coefficients grows at
most linearly in the square root of the diagonal-frame energy. -/
theorem c3_diagonal_raised_action_growth {n : ℕ}
    (d : Fin n → ℝ) (T Y : Fin n → Fin n → Fin n → ℂ)
    (Q : Matrix (Fin n) (Fin n) ℂ) (B0 E K : ℝ)
    (hB0 : 0 < B0) (hE : 0 ≤ E) (hK : 0 ≤ K)
    (hd : ∀ i, 0 < d i)
    (hdb : ∀ i, B0⁻¹ ≤ d i ∧ d i ≤ B0)
    (henergy : ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      (d i / (d j * d k)) * ‖T i j k‖ ^ 2 ≤ E)
    (hQ : ∀ j l, ‖Q j l‖ ≤ K)
    (hY : ∀ k j l, ‖Y k j l‖ ≤ K) :
    ∀ i j k,
      ‖(d i : ℂ)⁻¹ * (Y k j i - ∑ r, T r k j * Q r i)‖ ≤
        (B0 * K * ((n : ℝ) + 1)) * (1 + Real.sqrt (B0 ^ 3 * E)) := by
  have hweighted := c3_unweighted_energy_bound_of_diagonal_energy T d B0 E hB0 hd hdb henergy
  have hnonneg : 0 ≤ B0 ^ 3 * E := mul_nonneg (pow_nonneg (le_of_lt hB0) 3) hE
  have ht := c3_frame_tensor_component_bound_of_energy_sum T (B0 ^ 3 * E) hnonneg hweighted
  have hinv (i : Fin n) : (d i)⁻¹ ≤ B0 := by
    have hmul : 1 ≤ B0 * d i := by
      calc
        1 = B0⁻¹ * B0 := by field_simp [hB0.ne']
        _ ≤ d i * B0 := mul_le_mul_of_nonneg_right (hdb i).1 (le_of_lt hB0)
        _ = B0 * d i := mul_comm _ _
    simpa [one_div] using (div_le_iff₀ (hd i)).2 hmul
  have hterm (i j k : Fin n) :
      ‖(d i : ℂ)⁻¹ * (Y k j i - ∑ r, T r k j * Q r i)‖ ≤
        (B0 * K * ((n : ℝ) + 1)) * (1 + Real.sqrt (B0 ^ 3 * E)) := by
    have hnormReal : ‖(d i : ℂ)‖ = d i := by
      exact (RCLike.norm_ofReal (K := ℂ) _).trans (abs_of_nonneg (le_of_lt (hd i)))
    have hnormInv : ‖(d i : ℂ)⁻¹‖ = (d i)⁻¹ := by
      rw [norm_inv, hnormReal]
    have hsum : ‖Y k j i - ∑ r, T r k j * Q r i‖ ≤
        K + (n : ℝ) * Real.sqrt (B0 ^ 3 * E) * K := by
      calc
        ‖Y k j i - ∑ r, T r k j * Q r i‖ ≤
            ‖Y k j i‖ + ‖∑ r, T r k j * Q r i‖ := norm_sub_le _ _
        _ ≤ K + ∑ r, ‖T r k j * Q r i‖ := by
          exact add_le_add (hY k j i) (norm_sum_le _ _)
        _ ≤ K + ∑ r, (Real.sqrt (B0 ^ 3 * E) * K) := by
          apply add_le_add le_rfl
          apply Finset.sum_le_sum
          intro r hr
          rw [norm_mul]
          exact mul_le_mul (ht r k j) (hQ r i) (norm_nonneg _) (Real.sqrt_nonneg _)
        _ = K + (n : ℝ) * Real.sqrt (B0 ^ 3 * E) * K := by
          simp [Finset.sum_const, nsmul_eq_mul]
          ring
    have hroot : 0 ≤ Real.sqrt (B0 ^ 3 * E) := Real.sqrt_nonneg _
    calc
      ‖(d i : ℂ)⁻¹ * (Y k j i - ∑ r, T r k j * Q r i)‖ =
          (d i)⁻¹ * ‖Y k j i - ∑ r, T r k j * Q r i‖ := by
        rw [norm_mul, hnormInv]
      _ ≤ B0 * (K + (n : ℝ) * Real.sqrt (B0 ^ 3 * E) * K) :=
          mul_le_mul (hinv i) hsum (norm_nonneg _) (by positivity)
      _ ≤ (B0 * K * ((n : ℝ) + 1)) * (1 + Real.sqrt (B0 ^ 3 * E)) := by
          have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
          have hfactor : 1 + (n : ℝ) * Real.sqrt (B0 ^ 3 * E) ≤
              ((n : ℝ) + 1) * (1 + Real.sqrt (B0 ^ 3 * E)) := by
            nlinarith [mul_nonneg hn hroot]
          have hcoef : 0 ≤ B0 * K := mul_nonneg (le_of_lt hB0) hK
          calc
            B0 * (K + (n : ℝ) * Real.sqrt (B0 ^ 3 * E) * K) =
                (B0 * K) * (1 + (n : ℝ) * Real.sqrt (B0 ^ 3 * E)) := by ring
            _ ≤ (B0 * K) * (((n : ℝ) + 1) * (1 + Real.sqrt (B0 ^ 3 * E))) :=
              mul_le_mul_of_nonneg_left hfactor hcoef
            _ = (B0 * K * ((n : ℝ) + 1)) * (1 + Real.sqrt (B0 ^ 3 * E)) := by ring
  intro i j k
  exact hterm i j k

theorem c3_weighted_diagonal_error_growth {n : ℕ}
    (d : Fin n → ℝ) (T Y : Fin n → Fin n → Fin n → ℂ)
    (Q : Matrix (Fin n) (Fin n) ℂ) (B E K : ℝ)
    (hB : 0 < B) (hE : 0 ≤ E) (hK : 0 ≤ K)
    (hd : ∀ i, 0 < d i)
    (hdb : ∀ i, B⁻¹ ≤ d i ∧ d i ≤ B)
    (henergy : ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      (d i / (d j * d k)) * ‖T i j k‖ ^ 2 ≤ E)
    (hQ : ∀ j l, ‖Q j l‖ ≤ K)
    (hY : ∀ k j l, ‖Y k j l‖ ≤ K) :
    |RCLike.re (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      (d i / (d j * d k) : ℂ) * star (T i j k) *
        ((d i : ℂ)⁻¹ * (Y k j i - ∑ r, T r k j * Q r i)))| ≤
      B ^ 3 * (n : ℝ) ^ 3 * (B * K * ((n : ℝ) + 1)) *
        (Real.sqrt (B ^ 3 * E) + B ^ 3 * E) := by
  let V : Fin n → Fin n → Fin n → ℂ := fun i j k ↦
    (d i : ℂ)⁻¹ * (Y k j i - ∑ r, T r k j * Q r i)
  have henergyStar : ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      (d i / (d j * d k)) * ‖star (T i j k)‖ ^ 2 ≤ E := by
    simpa only [norm_star] using henergy
  have hV : ∀ i j k, ‖V i j k‖ ≤
      (B * K * ((n : ℝ) + 1)) * (1 + Real.sqrt (B ^ 3 * E)) := by
    intro i j k
    exact c3_diagonal_raised_action_growth d T Y Q B E K hB hE hK hd hdb
      henergy hQ hY i j k
  have hD : 0 ≤ B * K * ((n : ℝ) + 1) := by positivity
  have hbound := c3_frame_action_bound_of_diagonal_energy
    (fun i j k ↦ star (T i j k)) V d B E (B * K * ((n : ℝ) + 1))
    hB hE hD hd hdb henergyStar hV
  calc
    |RCLike.re (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (d i / (d j * d k) : ℂ) * star (T i j k) * V i j k)| ≤
        ‖∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          (d i / (d j * d k) : ℂ) * star (T i j k) * V i j k‖ :=
      RCLike.abs_re_le_norm _
    _ ≤ B ^ 3 * (n : ℝ) ^ 3 * (B * K * ((n : ℝ) + 1)) *
        (Real.sqrt (B ^ 3 * E) + B ^ 3 * E) := hbound

end KahlerForm
