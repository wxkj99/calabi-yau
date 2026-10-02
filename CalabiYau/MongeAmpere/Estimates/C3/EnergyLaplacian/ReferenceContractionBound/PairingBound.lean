module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceContractionBound.Diagonal

/-!
# PairingBound for the reference-curvature contraction

Székelyhidi, An Introduction to Extremal Kähler Metrics, §3.3, proof of Lemma 3.9, terms following (3.15), printed p. 45; finite tensor contraction algebra implementing that proof.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal BigOperators ComplexOrder MatrixOrder
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

theorem referenceContraction_diagonal_pairing_weighted_bound {n : ℕ}
    (d : Fin n → ℝ) (X : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ)
    (R : Fin n → Fin n → Fin n → Fin n → ℂ) (T : Fin n → Fin n → Fin n → ℂ)
    (B A K E : ℝ) (hB : 1 ≤ B) (hE : 0 ≤ E) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hd : ∀ i, 0 < d i) (hdb : ∀ i, B⁻¹ ≤ d i ∧ d i ≤ B)
    (henergy : ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      (d i / (d j * d k)) * ‖T i j k‖ ^ 2 ≤ E)
    (hX : ∀ p j k i, ‖X p j p k i‖ ≤ A)
    (hR : ∀ i j k l, ‖R i j k l‖ ≤ K) :
    |(∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      ((d i / (d j * d k) : ℝ) : ℂ) *
        referenceContractionDiagonalDrift d X R T i j k * star (T i j k)).re| ≤
      (n : ℝ) ^ 4 * B ^ 6 * A * Real.sqrt E +
        3 * (n : ℝ) ^ 5 * B ^ 8 * K * E := by
  have hpositiveB : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hweighted := referenceContraction_unweighted_energy_bound T d B E hpositiveB hd hdb henergy
  have hnonneg : 0 ≤ B ^ 3 * E := mul_nonneg (pow_nonneg (le_of_lt hpositiveB) 3) hE
  have hT := referenceContraction_component_bound_of_energy T (B ^ 3 * E) hnonneg hweighted
  have hDrift := referenceContractionDiagonalDrift_component_bound d X R T B A K E
    hpositiveB hE hd hdb henergy hX hR
  have hweight (i j k : Fin n) : d i / (d j * d k) ≤ B ^ 3 := by
    have hden : 0 < d j * d k := mul_pos (hd j) (hd k)
    have hBj : 1 ≤ B * d j := by
      calc
        1 = B * B⁻¹ := by field_simp [hpositiveB.ne']
        _ ≤ B * d j := mul_le_mul_of_nonneg_left (hdb j).1 (le_of_lt hpositiveB)
    have hBk : 1 ≤ B * d k := by
      calc
        1 = B * B⁻¹ := by field_simp [hpositiveB.ne']
        _ ≤ B * d k := mul_le_mul_of_nonneg_left (hdb k).1 (le_of_lt hpositiveB)
    have hprod : 1 ≤ (B * d j) * (B * d k) := by nlinarith
    apply (div_le_iff₀ hden).2
    calc
      d i ≤ B := (hdb i).2
      _ = B * 1 := by ring
      _ ≤ B * ((B * d j) * (B * d k)) := mul_le_mul_of_nonneg_left hprod (le_of_lt hpositiveB)
      _ = B ^ 3 * (d j * d k) := by ring
  let W : ℝ := B ^ 3 * E
  let D : ℝ := (n : ℝ) * B * (A + 3 * (n : ℝ) * K * Real.sqrt W)
  have hW : W = B ^ 3 * E := rfl
  have hWnonneg : 0 ≤ W := by dsimp [W]; exact hnonneg
  have hDnonneg : 0 ≤ D := by
    dsimp [D]
    positivity
  have hterm (i j k : Fin n) :
      ‖((d i / (d j * d k) : ℝ) : ℂ) *
        referenceContractionDiagonalDrift d X R T i j k * star (T i j k)‖ ≤
      B ^ 3 * D * Real.sqrt W := by
    have hwi : 0 ≤ d i / (d j * d k) :=
      div_nonneg (le_of_lt (hd i)) (le_of_lt (mul_pos (hd j) (hd k)))
    have hnormw : ‖((d i / (d j * d k) : ℝ) : ℂ)‖ = d i / (d j * d k) := by
      exact (RCLike.norm_ofReal (K := ℂ) _).trans (abs_of_nonneg hwi)
    rw [norm_mul, norm_mul, norm_star, hnormw]
    calc
      (d i / (d j * d k) * ‖referenceContractionDiagonalDrift d X R T i j k‖) *
          ‖T i j k‖ ≤ (B ^ 3 * D) * Real.sqrt W := by
        exact mul_le_mul (mul_le_mul (hweight i j k) (hDrift i j k)
          (norm_nonneg _) (pow_nonneg (le_of_lt hpositiveB) 3))
          (hT i j k) (by positivity) (mul_nonneg
            (pow_nonneg (le_of_lt hpositiveB) 3) hDnonneg)
      _ = B ^ 3 * D * Real.sqrt W := by ring
  have hnormsum :
      ‖∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        ((d i / (d j * d k) : ℝ) : ℂ) *
          referenceContractionDiagonalDrift d X R T i j k * star (T i j k)‖ ≤
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        ‖((d i / (d j * d k) : ℝ) : ℂ) *
          referenceContractionDiagonalDrift d X R T i j k * star (T i j k)‖ := by
    calc
      _ ≤ ∑ i : Fin n, ‖∑ j : Fin n, ∑ k : Fin n,
          ((d i / (d j * d k) : ℝ) : ℂ) *
            referenceContractionDiagonalDrift d X R T i j k * star (T i j k)‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, ‖∑ k : Fin n,
          ((d i / (d j * d k) : ℝ) : ℂ) *
            referenceContractionDiagonalDrift d X R T i j k * star (T i j k)‖ := by
        apply Finset.sum_le_sum
        intro i hi
        exact norm_sum_le _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact norm_sum_le _ _
  have hsumBound :
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        ‖((d i / (d j * d k) : ℝ) : ℂ) *
          referenceContractionDiagonalDrift d X R T i j k * star (T i j k)‖ ≤
        (n : ℝ) ^ 3 * (B ^ 3 * D * Real.sqrt W) := by
    calc
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, B ^ 3 * D * Real.sqrt W := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro k hk
        exact hterm i j k
      _ = (n : ℝ) ^ 3 * (B ^ 3 * D * Real.sqrt W) := by
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
  have hsquare : (Real.sqrt W) ^ 2 = W := Real.sq_sqrt hWnonneg
  have hrough :
      |(∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        ((d i / (d j * d k) : ℝ) : ℂ) *
          referenceContractionDiagonalDrift d X R T i j k * star (T i j k)).re| ≤
        (n : ℝ) ^ 4 * B ^ 4 * A * Real.sqrt W +
          3 * (n : ℝ) ^ 5 * B ^ 4 * K * W := by
    calc
      _ ≤ ‖∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          ((d i / (d j * d k) : ℝ) : ℂ) *
            referenceContractionDiagonalDrift d X R T i j k * star (T i j k)‖ :=
        RCLike.abs_re_le_norm _
      _ ≤ (n : ℝ) ^ 3 * (B ^ 3 * D * Real.sqrt W) := hnormsum.trans hsumBound
      _ = (n : ℝ) ^ 4 * B ^ 4 * A * Real.sqrt W +
          3 * (n : ℝ) ^ 5 * B ^ 4 * K * W := by
        dsimp [D]
        ring_nf
        rw [hsquare]
  have hBpow : B ^ 3 ≤ B ^ 4 := by
    calc
      B ^ 3 = B ^ 3 * 1 := by ring
      _ ≤ B ^ 3 * B := mul_le_mul_of_nonneg_left hB (by positivity)
      _ = B ^ 4 := by ring
  have hsqrt : Real.sqrt W ≤ B ^ 2 * Real.sqrt E := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · calc
        W = B ^ 3 * E := hW
        _ ≤ B ^ 4 * E := mul_le_mul_of_nonneg_right hBpow hE
        _ = (B ^ 2 * Real.sqrt E) ^ 2 := by
          ring_nf
          rw [Real.sq_sqrt hE]
  have hfirst : (n : ℝ) ^ 4 * B ^ 4 * A * Real.sqrt W ≤
      (n : ℝ) ^ 4 * B ^ 6 * A * Real.sqrt E := by
    calc
      (n : ℝ) ^ 4 * B ^ 4 * A * Real.sqrt W ≤
          (n : ℝ) ^ 4 * B ^ 4 * A * (B ^ 2 * Real.sqrt E) :=
        mul_le_mul_of_nonneg_left hsqrt (by positivity)
      _ = (n : ℝ) ^ 4 * B ^ 6 * A * Real.sqrt E := by ring
  have hsecond : 3 * (n : ℝ) ^ 5 * B ^ 4 * K * W ≤
      3 * (n : ℝ) ^ 5 * B ^ 8 * K * E := by
    rw [hW]
    have hmul : B ^ 7 ≤ B ^ 8 := by
      calc
        B ^ 7 = B ^ 7 * 1 := by ring
        _ ≤ B ^ 7 * B := mul_le_mul_of_nonneg_left hB (by positivity)
        _ = B ^ 8 := by ring
    have hcoeff : 0 ≤ 3 * (n : ℝ) ^ 5 * K := by positivity
    calc
      3 * (n : ℝ) ^ 5 * B ^ 4 * K * (B ^ 3 * E) =
          (3 * (n : ℝ) ^ 5 * K) * (B ^ 7 * E) := by ring
      _ ≤ (3 * (n : ℝ) ^ 5 * K) * (B ^ 8 * E) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmul hE) hcoeff
      _ = 3 * (n : ℝ) ^ 5 * B ^ 8 * K * E := by ring
  exact (hrough.trans (add_le_add hfirst hsecond))

theorem referenceContraction_le_const_mul_add_sqrt {n : ℕ}
    (B A K E : ℝ) (hB : 1 ≤ B) (hA : 0 ≤ A) (hK : 0 ≤ K) (hE : 0 ≤ E) :
    let C := (n : ℝ) ^ 4 * B ^ 6 * A + 3 * (n : ℝ) ^ 5 * B ^ 8 * K
    0 ≤ C ∧
      (n : ℝ) ^ 4 * B ^ 6 * A * Real.sqrt E +
        3 * (n : ℝ) ^ 5 * B ^ 8 * K * E ≤ C * (E + Real.sqrt E) := by
  dsimp
  constructor
  · positivity
  · have hAterm : 0 ≤ (n : ℝ) ^ 4 * B ^ 6 * A * E := by positivity
    have hKterm : 0 ≤ 3 * (n : ℝ) ^ 5 * B ^ 8 * K * Real.sqrt E := by
      positivity
    nlinarith

end KahlerForm
