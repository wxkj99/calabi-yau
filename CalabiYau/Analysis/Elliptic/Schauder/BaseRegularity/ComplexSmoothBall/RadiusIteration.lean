module

public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.ComplexSmoothBall.Basic

/-!
# Dyadic radial absorption

Source: Gilbarg–Trudinger, §6.1, Theorem 6.2, freezing/interpolation proof;
Constantin, Schauder Estimates, pp. 6–9. The estimates follow Constantin, *Schauder Estimates*, pp. 6–9.
-/

open Set Matrix
open scoped NNReal ContDiff Topology

namespace CalabiYau.Schauder

open Filter

@[expose] public section

/-- Iterate through `r_j = R - (R - ρ) * 2^(-j)`. The forcing series has ratio one half,
while the remainder tends to zero because the radial profile is bounded by its terminal value.
No PDE assertion is hidden here; this numerical lemma removes the outer derivative gauge
from the cutoff-source recurrence. The strict gap excludes division by a zero radius. -/
theorem realBall_radius_iteration :
    ∀ {ρ R : ℝ} {p : ℕ} {D : ℝ≥0} {H : ℝ → ℝ≥0},
  0 ≤ ρ → ρ < R → 0 < p →
  (∀ r, ρ ≤ r → r ≤ R → H r ≤ H R) →
  (∀ r t, ρ ≤ r → r < t → t ≤ R →
    H r ≤ D * (Real.toNNReal (t-r))⁻¹ ^ p + (2 ^ (p+1) : ℝ≥0)⁻¹ * H t) →
  H ρ ≤ (2 * (2 * (Real.toNNReal (R-ρ))⁻¹) ^ p) * D := by
  intro ρ R p D H hρ hρR hp hbounded hstep
  let dyadicRadius (ρ R : ℝ) (n : ℕ) : ℝ := R - (R - ρ) / (2 : ℝ) ^ n
  have dyadicRadius_zero (ρ R : ℝ) : dyadicRadius ρ R 0 = ρ := by simp [dyadicRadius]
  have two_pow_ge_one (n : ℕ) : (1 : ℝ) ≤ (2 : ℝ) ^ n := by
    induction n with
    | zero => norm_num
    | succ n ih =>
        rw [pow_succ]
        nlinarith [mul_nonneg (show 0 ≤ (2 : ℝ) by norm_num) (sub_nonneg.mpr ih)]
  have dyadicRadius_mem_Icc {ρ R : ℝ} (hρR : ρ < R)
      (n : ℕ) : dyadicRadius ρ R n ∈ Set.Icc ρ R := by
    constructor
    · dsimp [dyadicRadius]
      have hgap : 0 ≤ R - ρ := by linarith
      have hpow : 1 ≤ (2 : ℝ) ^ n := two_pow_ge_one n
      have hdiv : (R - ρ) / (2 : ℝ) ^ n ≤ R - ρ := div_le_self hgap hpow
      linarith
    · dsimp [dyadicRadius]
      have hgap : 0 ≤ (R - ρ) / (2 : ℝ) ^ n := div_nonneg (by linarith) (by positivity)
      linarith
  have dyadicRadius_gap (ρ R : ℝ) (n : ℕ) :
      dyadicRadius ρ R (n + 1) - dyadicRadius ρ R n =
        (R - ρ) / (2 : ℝ) ^ (n + 1) := by
    dsimp [dyadicRadius]
    rw [pow_succ]
    have hpow : (2 : ℝ) ^ n ≠ 0 := by positivity
    field_simp [hpow]
    ring
  have dyadicRadius_gap_nnreal {ρ R : ℝ} (hρR : ρ < R) (n : ℕ) :
      Real.toNNReal (dyadicRadius ρ R (n + 1) - dyadicRadius ρ R n) =
        Real.toNNReal (R - ρ) * (1 / 2 : ℝ≥0) ^ (n + 1) := by
    rw [dyadicRadius_gap]
    rw [Real.toNNReal_div (by linarith : 0 ≤ R - ρ)]
    rw [div_eq_mul_inv]
    rw [Real.toNNReal_of_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ (n + 1))]
    ext
    simp
  have radius_iteration_iterate
      {X gap : ℕ → ℝ≥0} {A θ : ℝ≥0} (hθ : 0 ≤ θ)
      (hrec : ∀ n, X n ≤ A * gap n + θ * X (n + 1)) :
      ∀ m N, X m ≤ A * (∑ i ∈ Finset.range N, θ ^ i * gap (m + i)) +
        θ ^ N * X (m + N) := by
    intro m N
    induction N with
    | zero => simp
    | succ N ih =>
        have hmul := mul_le_mul_of_nonneg_left (hrec (m + N)) (pow_nonneg hθ N)
        calc
          X m ≤ A * (∑ i ∈ Finset.range N, θ ^ i * gap (m + i)) +
              θ ^ N * X (m + N) := ih
          _ ≤ A * (∑ i ∈ Finset.range N, θ ^ i * gap (m + i)) +
              θ ^ N * (A * gap (m + N) + θ * X (m + N + 1)) :=
            add_le_add_right hmul _
          _ = A * (∑ i ∈ Finset.range (N + 1), θ ^ i * gap (m + i)) +
              θ ^ (N + 1) * X (m + (N + 1)) := by
            rw [Finset.sum_range_succ]
            ring_nf
            simp [Nat.add_comm, Nat.add_left_comm]
  have dyadic_geometric_sum_le_two (N : ℕ) :
      (∑ i ∈ Finset.range N, (1 / 2 : ℝ≥0) ^ i) ≤ 2 := by
    have hsumR : (∑ i ∈ Finset.range N, (1 / 2 : ℝ) ^ i) ≤ 2 := by
      calc
        (∑ i ∈ Finset.range N, (1 / 2 : ℝ) ^ i) ≤ ∑' i : ℕ, (1 / 2 : ℝ) ^ i :=
          (summable_geometric_of_lt_one (by norm_num) (by norm_num)).sum_le_tsum
            (Finset.range N) (fun i hi => pow_nonneg (by norm_num) i)
        _ = 2 := by rw [tsum_geometric_of_lt_one] <;> norm_num
    apply (NNReal.coe_le_coe).mp
    convert hsumR using 1 <;> norm_num [NNReal.coe_pow]
  let θ : ℝ≥0 := (2 ^ (p + 1) : ℝ≥0)⁻¹
  let half : ℝ≥0 := 1 / 2
  let radius : ℕ → ℝ := dyadicRadius ρ R
  let gap : ℕ → ℝ≥0 := fun n =>
    (Real.toNNReal (radius (n + 1) - radius n))⁻¹ ^ p
  let X : ℕ → ℝ≥0 := fun n => H (radius n)
  let C : ℝ≥0 := (2 * (Real.toNNReal (R - ρ))⁻¹) ^ p
  have hθpos : 0 < θ := by dsimp [θ]; positivity
  have hpone : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr (by omega)
  have hpow2 : 2 ≤ (2 : ℝ≥0) ^ (p + 1) := by
    calc
      2 = (2 : ℝ≥0) ^ 1 := by norm_num
      _ ≤ (2 : ℝ≥0) ^ (p + 1) := by gcongr <;> norm_num
  have hθlt : θ < 1 := by
    dsimp [θ]
    exact inv_lt_one_of_one_lt₀ (by
      exact lt_of_lt_of_le (by norm_num : (1 : ℝ≥0) < 2) hpow2)
  have hθhalf : θ * (2 : ℝ≥0) ^ p = half := by
    dsimp [θ, half]
    rw [pow_succ]
    field_simp
  have hrec (n : ℕ) : X n ≤ D * gap n + θ * X (n + 1) := by
    have hmem := dyadicRadius_mem_Icc hρR n
    have hnext := dyadicRadius_mem_Icc hρR (n + 1)
    have hgapPos : 0 < radius (n + 1) - radius n := by
      rw [show radius (n + 1) - radius n = (R - ρ) / (2 : ℝ) ^ (n + 1) by
        exact dyadicRadius_gap ρ R n]
      exact div_pos (by linarith) (by positivity)
    have hinc : radius n < radius (n + 1) := by linarith
    simpa [X, gap, θ, radius] using
      hstep (radius n) (radius (n + 1)) hmem.1 hinc hnext.2
  have hiter := radius_iteration_iterate (le_of_lt hθpos) hrec 0
  have hterm (n : ℕ) : θ ^ n * gap n = C * half ^ n := by
    have hL : 0 < Real.toNNReal (R - ρ) := Real.toNNReal_pos.mpr (by linarith)
    have hdist := dyadicRadius_gap_nnreal hρR n
    rw [show gap n =
      (Real.toNNReal (R - ρ) * (1 / 2 : ℝ≥0) ^ (n + 1))⁻¹ ^ p by
        dsimp [gap, radius]
        rw [hdist]]
    dsimp [θ, half, C]
    field_simp [ne_of_gt hL]
    ring_nf
    have hcancel : (1 / 2 : ℝ≥0) ^ (p * n) * 2 ^ (p * n) = 1 := by
      rw [← mul_pow]
      norm_num
    calc
      _ = ((1 / 2 : ℝ≥0) ^ (p * n) * 2 ^ (p * n)) *
          (R - ρ).toNNReal⁻¹ ^ p * (1 / 2 : ℝ≥0) ^ n * 2 ^ p := by ring
      _ = (R - ρ).toNNReal⁻¹ ^ p * (1 / 2 : ℝ≥0) ^ n * 2 ^ p := by
        rw [hcancel, one_mul]
  have hsumEq (N : ℕ) :
      (∑ i ∈ Finset.range N, θ ^ i * gap i) =
        C * (∑ i ∈ Finset.range N, half ^ i) := by
    calc
      (∑ i ∈ Finset.range N, θ ^ i * gap i) =
          ∑ i ∈ Finset.range N, C * half ^ i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hterm i
      _ = C * (∑ i ∈ Finset.range N, half ^ i) := by rw [Finset.mul_sum]
  have hCnonneg : 0 ≤ C := by positivity
  have hforce (N : ℕ) :
      D * (∑ i ∈ Finset.range N, θ ^ i * gap i) ≤ D * C * 2 := by
    rw [hsumEq]
    calc
      D * (C * (∑ i ∈ Finset.range N, half ^ i)) =
          (D * C) * (∑ i ∈ Finset.range N, half ^ i) := by ring
      _ ≤ (D * C) * 2 :=
        mul_le_mul_of_nonneg_left (dyadic_geometric_sum_le_two N)
          (mul_nonneg (show 0 ≤ D by positivity) hCnonneg)
      _ = D * C * 2 := by ring
  have htail (N : ℕ) : θ ^ N * X N ≤ θ ^ N * H R := by
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (le_of_lt hθpos) N)
    exact hbounded (radius N) (dyadicRadius_mem_Icc hρR N).1
      (dyadicRadius_mem_Icc hρR N).2
  have hboundN (N : ℕ) : H ρ ≤ D * C * 2 + θ ^ N * H R := by
    have hiterate : X 0 ≤ D * (∑ i ∈ Finset.range N, θ ^ i * gap i) + θ ^ N * X N := by
      simpa only [Nat.zero_add] using hiter N
    have hstart : X 0 = H ρ := by simp [X, radius, dyadicRadius_zero]
    calc
      H ρ = X 0 := hstart.symm
      _ ≤ D * (∑ i ∈ Finset.range N, θ ^ i * gap i) + θ ^ N * X N := hiterate
      _ ≤ D * C * 2 + θ ^ N * H R := add_le_add (hforce N) (htail N)
  have hlimit : Tendsto (fun N : ℕ => D * C * 2 + θ ^ N * H R)
      atTop (𝓝 (D * C * 2)) := by
    have hpow := NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hθlt
    simpa using (tendsto_const_nhds.add (hpow.mul_const (H R)))
  have hmain : H ρ ≤ D * C * 2 :=
    ge_of_tendsto hlimit (Eventually.of_forall hboundN)
  simpa [C, mul_comm, mul_left_comm, mul_assoc] using hmain

end

end CalabiYau.Schauder
