module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceContractionBound.Basic

/-!
# Diagonal for the reference-curvature contraction

Székelyhidi, An Introduction to Extremal Kähler Metrics, §3.3, proof of Lemma 3.9, terms following (3.15), printed p. 45; finite tensor contraction algebra implementing that proof.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal BigOperators ComplexOrder MatrixOrder
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

theorem referenceContraction_diagonal_weight_lower_bound {n : ℕ}
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

theorem referenceContraction_unweighted_energy_bound {n : ℕ}
    (T : Fin n → Fin n → Fin n → ℂ) (d : Fin n → ℝ) (B E : ℝ)
    (hB : 0 < B) (hd : ∀ i, 0 < d i)
    (hdb : ∀ i, B⁻¹ ≤ d i ∧ d i ≤ B)
    (henergy : ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      (d i / (d j * d k)) * ‖T i j k‖ ^ 2 ≤ E) :
    ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ‖T i j k‖ ^ 2 ≤ B ^ 3 * E := by
  have hweight := referenceContraction_diagonal_weight_lower_bound d B hB hd hdb
  have hfactor (i j k : Fin n) : 1 ≤ B ^ 3 * (d i / (d j * d k)) := by
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

theorem referenceContraction_component_bound_of_energy
    {n : ℕ} (T : Fin n → Fin n → Fin n → ℂ) (E : ℝ) (hE : 0 ≤ E)
    (henergy : ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ‖T i j k‖ ^ 2 ≤ E) :
    ∀ i j k, ‖T i j k‖ ≤ Real.sqrt E := by
  intro i j k
  have hk : ‖T i j k‖ ^ 2 ≤ ∑ l : Fin n, ‖T i j l‖ ^ 2 :=
    Finset.single_le_sum (fun l hl => sq_nonneg ‖T i j l‖) (Finset.mem_univ k)
  have hj : ∑ l : Fin n, ‖T i j l‖ ^ 2 ≤
      ∑ b : Fin n, ∑ l : Fin n, ‖T i b l‖ ^ 2 := by
    calc
      ∑ l : Fin n, ‖T i j l‖ ^ 2 =
          (fun b : Fin n => ∑ l : Fin n, ‖T i b l‖ ^ 2) j := rfl
      _ ≤ ∑ b : Fin n, (fun b : Fin n => ∑ l : Fin n, ‖T i b l‖ ^ 2) b :=
        Finset.single_le_sum
          (fun b hb => Finset.sum_nonneg fun l hl => sq_nonneg ‖T i b l‖)
          (Finset.mem_univ j)
      _ = ∑ b : Fin n, ∑ l : Fin n, ‖T i b l‖ ^ 2 := by rfl
  have hi : ∑ b : Fin n, ∑ l : Fin n, ‖T i b l‖ ^ 2 ≤
      ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ‖T a b l‖ ^ 2 := by
    calc
      ∑ b : Fin n, ∑ l : Fin n, ‖T i b l‖ ^ 2 =
          (fun a : Fin n => ∑ b : Fin n, ∑ l : Fin n, ‖T a b l‖ ^ 2) i := rfl
      _ ≤ ∑ a : Fin n, (fun a : Fin n => ∑ b : Fin n, ∑ l : Fin n, ‖T a b l‖ ^ 2) a :=
        Finset.single_le_sum
          (fun a ha => Finset.sum_nonneg fun b hb =>
            Finset.sum_nonneg fun l hl => sq_nonneg ‖T a b l‖)
          (Finset.mem_univ i)
      _ = ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ‖T a b l‖ ^ 2 := by rfl
  have hsq : ‖T i j k‖ ^ 2 ≤ E := hk.trans (hj.trans (hi.trans henergy))
  have hsqrt : 0 ≤ Real.sqrt E := Real.sqrt_nonneg E
  have hnorm : 0 ≤ ‖T i j k‖ := norm_nonneg _
  nlinarith [Real.sq_sqrt hE]

theorem referenceContraction_diagonal_drift_component_bound {n : ℕ}
    (d : Fin n → ℝ) (X : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ)
    (R : Fin n → Fin n → Fin n → Fin n → ℂ) (T : Fin n → Fin n → Fin n → ℂ)
    (B A K E : ℝ) (hB : 0 < B) (hE : 0 ≤ E)
    (hd : ∀ i, 0 < d i) (hdb : ∀ i, B⁻¹ ≤ d i ∧ d i ≤ B)
    (henergy : ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      (d i / (d j * d k)) * ‖T i j k‖ ^ 2 ≤ E)
    (hX : ∀ p j k i, ‖X p j p k i‖ ≤ A)
    (hR : ∀ i j k l, ‖R i j k l‖ ≤ K) :
    ∀ i j k, ‖referenceContraction_diagonal_drift d X R T i j k‖ ≤
      (n : ℝ) * B * (A + 3 * (n : ℝ) * K * Real.sqrt (B ^ 3 * E)) := by
  have hweighted := referenceContraction_unweighted_energy_bound T d B E hB hd hdb henergy
  have hnonneg : 0 ≤ B ^ 3 * E := mul_nonneg (pow_nonneg (le_of_lt hB) 3) hE
  have hT := referenceContraction_component_bound_of_energy T (B ^ 3 * E) hnonneg hweighted
  have hinv (p : Fin n) : (d p)⁻¹ ≤ B := by
    have hmul : 1 ≤ B * d p := by
      calc
        1 = B * B⁻¹ := by field_simp [hB.ne']
        _ ≤ B * d p := mul_le_mul_of_nonneg_left (hdb p).1 (le_of_lt hB)
    simpa [one_div] using (div_le_iff₀ (hd p)).2 hmul
  have hInvNorm (p : Fin n) : ‖((d p)⁻¹ : ℂ)‖ ≤ B := by
    have hnorm : ‖(d p : ℂ)‖ = d p :=
      (RCLike.norm_ofReal (K := ℂ) _).trans (abs_of_nonneg (le_of_lt (hd p)))
    rw [norm_inv, hnorm]
    exact hinv p
  intro i j k
  simp only [referenceContraction_diagonal_drift]
  calc
    ‖∑ p, ((d p)⁻¹ : ℂ) *
        (X p j p k i + ∑ r, T i p r * R j p k r -
          ∑ r, T r p j * R r p k i - ∑ r, T r p k * R j p r i)‖ ≤
      ∑ p, ‖((d p)⁻¹ : ℂ) *
        (X p j p k i + ∑ r, T i p r * R j p k r -
          ∑ r, T r p j * R r p k i - ∑ r, T r p k * R j p r i)‖ := norm_sum_le _ _
    _ ≤ ∑ p, B * (A + 3 * (n : ℝ) * K * Real.sqrt (B ^ 3 * E)) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_mul]
      apply mul_le_mul (hInvNorm p) _ (norm_nonneg _) (by positivity)
      calc
        ‖X p j p k i + ∑ r, T i p r * R j p k r -
            ∑ r, T r p j * R r p k i - ∑ r, T r p k * R j p r i‖ ≤
            ‖X p j p k i‖ + ‖∑ r, T i p r * R j p k r‖ +
              ‖∑ r, T r p j * R r p k i‖ + ‖∑ r, T r p k * R j p r i‖ := by
          calc
            _ ≤ ‖X p j p k i + ∑ r, T i p r * R j p k r -
                ∑ r, T r p j * R r p k i‖ + ‖∑ r, T r p k * R j p r i‖ := norm_sub_le _ _
            _ ≤ ‖X p j p k i‖ + ‖∑ r, T i p r * R j p k r‖ +
                ‖∑ r, T r p j * R r p k i‖ + ‖∑ r, T r p k * R j p r i‖ := by
              calc
                _ ≤ (‖X p j p k i + ∑ r, T i p r * R j p k r‖ +
                    ‖∑ r, T r p j * R r p k i‖) + ‖∑ r, T r p k * R j p r i‖ := by
                  gcongr
                  exact norm_sub_le _ _
                _ ≤ _ := by
                  gcongr
                  exact norm_add_le _ _
        _ ≤ A + 3 * (n : ℝ) * K * Real.sqrt (B ^ 3 * E) := by
          have hsumBound (f : Fin n → ℂ) : ‖∑ r, f r‖ ≤ ∑ r, ‖f r‖ := norm_sum_le _ _
          have hOne (f : Fin n → ℂ) (hf : ∀ r, ‖f r‖ ≤
              Real.sqrt (B ^ 3 * E) * K) :
              ‖∑ r, f r‖ ≤ (n : ℝ) * Real.sqrt (B ^ 3 * E) * K := by
            calc
              ‖∑ r, f r‖ ≤ ∑ r, ‖f r‖ := hsumBound f
              _ ≤ ∑ r, Real.sqrt (B ^ 3 * E) * K := by
                apply Finset.sum_le_sum
                intro r hr
                exact hf r
              _ = (n : ℝ) * Real.sqrt (B ^ 3 * E) * K := by
                simp [Finset.sum_const, nsmul_eq_mul]
                ring
          have h1 : ‖∑ r, T i p r * R j p k r‖ ≤
              (n : ℝ) * Real.sqrt (B ^ 3 * E) * K := hOne _ (by
                intro r
                rw [norm_mul]
                exact mul_le_mul (hT i p r) (hR j p k r)
                  (norm_nonneg _) (Real.sqrt_nonneg _))
          have h2 : ‖∑ r, T r p j * R r p k i‖ ≤
              (n : ℝ) * Real.sqrt (B ^ 3 * E) * K := hOne _ (by
                intro r
                rw [norm_mul]
                exact mul_le_mul (hT r p j) (hR r p k i)
                  (norm_nonneg _) (Real.sqrt_nonneg _))
          have h3 : ‖∑ r, T r p k * R j p r i‖ ≤
              (n : ℝ) * Real.sqrt (B ^ 3 * E) * K := hOne _ (by
                intro r
                rw [norm_mul]
                exact mul_le_mul (hT r p k) (hR j p r i)
                  (norm_nonneg _) (Real.sqrt_nonneg _))
          nlinarith [hX p j k i]
    _ = (n : ℝ) * B * (A + 3 * (n : ℝ) * K * Real.sqrt (B ^ 3 * E)) := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring

end KahlerForm
