module

public import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.Positivity.Finset

/-!
# Elementary inequalities between sums, products and reciprocals of positive reals

This file supplements `Mathlib.Analysis.MeanInequalities` with the finite inequalities that
control the eigenvalues `λᵢ > 0` of one positive definite Hermitian matrix relative to another
in terms of `∑ λᵢ` and `∏ λᵢ`. They are the scalar kernels of the matrix inequalities in
`CalabiYau.LinearAlgebra.Hermitian.TraceInequality` and
`CalabiYau.LinearAlgebra.Hermitian.EigenvalueBound`, which are reduced to them by simultaneous
diagonalization.

The unweighted AM–GM inequality is `Real.geom_mean_le_arith_mean` with weights `1`; we record the
form with `rpow` of the cardinality that the matrix statements use.

## Main statements

* `Real.prod_rpow_inv_card_le_sum_div_card`: `(∏ xᵢ)^{1/n} ≤ (∑ xᵢ)/n`.
* `Real.card_sq_le_sum_mul_sum_inv`: `n² ≤ (∑ xᵢ) (∑ xᵢ⁻¹)`.
* `Real.sum_inv_le_sum_pow_div_prod`: `∑ xᵢ⁻¹ ≤ (∑ xᵢ)^{n-1} / ∏ xᵢ`.
* `Real.prod_div_sum_pow_le`: `(∏ xⱼ) / (∑ xⱼ)^{n-1} ≤ xᵢ` for every index `i`.

## References

* S.-T. Yau, *On the Ricci curvature of a compact Kähler manifold and the complex Monge–Ampère
  equation I*, Comm. Pure Appl. Math. 31 (1978), §2.
* G. Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §3.3 (the C² estimate).
-/

public section

open Finset

namespace Real

variable {ι : Type*} (s : Finset ι) {x : ι → ℝ}

/-- **AM–GM inequality**, unweighted form: the geometric mean of nonnegative reals is at most their
arithmetic mean. -/
theorem prod_rpow_inv_card_le_sum_div_card (hs : s.Nonempty) (hx : ∀ i ∈ s, 0 ≤ x i) :
    (∏ i ∈ s, x i) ^ (#s : ℝ)⁻¹ ≤ (∑ i ∈ s, x i) / #s := by
  have h := geom_mean_le_arith_mean s (fun _ ↦ 1) x (fun _ _ ↦ zero_le_one)
    (by simpa using hs.card_pos) hx
  simpa using h

/-- The harmonic-arithmetic mean inequality in product form: `n² ≤ (∑ xᵢ) (∑ xᵢ⁻¹)`. -/
theorem card_sq_le_sum_mul_sum_inv (hx : ∀ i ∈ s, 0 < x i) :
    (#s : ℝ) ^ 2 ≤ (∑ i ∈ s, x i) * ∑ i ∈ s, (x i)⁻¹ := by
  have h := sum_sq_le_sum_mul_sum_of_sq_le_mul s (r := fun _ ↦ (1 : ℝ))
    (fun i hi ↦ (hx i hi).le) (fun i hi ↦ inv_nonneg.2 (hx i hi).le)
    (fun i hi ↦ by rw [one_pow, mul_inv_cancel₀ (hx i hi).ne'])
  simpa using h

/-- For positive reals, `∑ xᵢ⁻¹ ≤ (∑ xᵢ)^{n-1} / ∏ xᵢ`; equivalently the elementary symmetric
function `e_{n-1}` is bounded by `e₁^{n-1}`. This is the scalar form of
`tr(B⁻¹A) ≤ tr(A⁻¹B)^{n-1} / det(A⁻¹B)`. -/
theorem sum_inv_le_sum_pow_div_prod (hx : ∀ i ∈ s, 0 < x i) :
    ∑ i ∈ s, (x i)⁻¹ ≤ (∑ i ∈ s, x i) ^ (#s - 1) / ∏ i ∈ s, x i := by
  classical
  have hprod : 0 < ∏ i ∈ s, x i := prod_pos fun i hi ↦ hx i hi
  have hsum : 0 ≤ ∑ i ∈ s, x i := sum_nonneg fun i hi ↦ (hx i hi).le
  have hkey : (∏ i ∈ s, x i) * (∑ i ∈ s, (x i)⁻¹) =
      ∑ i ∈ s, ∏ j ∈ s.erase i, x j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.mul_prod_erase s x hi]
    calc
      x i * (∏ j ∈ s.erase i, x j) * (x i)⁻¹ =
          (∏ j ∈ s.erase i, x j) * (x i * (x i)⁻¹) := by ring
      _ = ∏ j ∈ s.erase i, x j := by rw [mul_inv_cancel₀ (ne_of_gt (hx i hi)), mul_one]
  have hsymmetric : (∑ i ∈ s, ∏ j ∈ s.erase i, x j) ≤
      (∑ i ∈ s, x i) ^ (#s - 1) := by
    have hbound : ∀ t : Finset ι, (∀ i ∈ t, 0 ≤ x i) →
        (∑ i ∈ t, ∏ j ∈ t.erase i, x j) ≤ (∑ i ∈ t, x i) ^ (#t - 1) := by
      intro t
      induction t using Finset.induction with
      | empty => intro _; simp
      | @insert a t ha ih =>
        intro ht
        have hrec : (∑ i ∈ insert a t, ∏ j ∈ (insert a t).erase i, x j) =
            (∏ j ∈ t, x j) + x a * (∑ i ∈ t, ∏ j ∈ t.erase i, x j) := by
          rw [Finset.sum_insert ha, Finset.erase_insert ha]
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.erase_insert_of_ne (by intro h; subst i; exact ha hi), Finset.prod_insert]
          simp [Finset.mem_erase, ha]
        by_cases htempty : t = ∅
        · subst t
          simp
        · have htn : 0 < #t := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr htempty)
          have htS : 0 ≤ ∑ i ∈ t, x i := Finset.sum_nonneg fun i hi => ht i (Finset.mem_insert_of_mem hi)
          have hP : (∏ j ∈ t, x j) ≤ (∑ i ∈ t, x i) ^ #t := by
            calc
              (∏ j ∈ t, x j) ≤ ∏ _j ∈ t, ∑ k ∈ t, x k :=
                Finset.prod_le_prod₀ (fun j hj => ht j (Finset.mem_insert_of_mem hj))
                  (fun j hj => Finset.single_le_sum
                    (fun k hk => ht k (Finset.mem_insert_of_mem hk)) hj)
              _ = (∑ i ∈ t, x i) ^ #t := by rw [Finset.prod_const, Finset.card_eq_sum_ones]
          have hE := ih (fun i hi => ht i (Finset.mem_insert_of_mem hi))
          have hxa : 0 ≤ x a := ht a (Finset.mem_insert_self _ _)
          have hmone : 1 ≤ #t := by omega
          have hpow : (∑ i ∈ t, x i) ^ #t + x a * (∑ i ∈ t, x i) ^ (#t - 1) ≤
              (x a + ∑ i ∈ t, x i) ^ #t := by
            have hpowS : (∑ i ∈ t, x i) ^ #t =
                (∑ i ∈ t, x i) ^ (#t - 1) * (∑ i ∈ t, x i) := by
              calc
                _ = (∑ i ∈ t, x i) ^ ((#t - 1) + 1) := by congr 1; omega
                _ = _ := by rw [pow_succ]
            have hpowA : (x a + ∑ i ∈ t, x i) ^ #t =
                (x a + ∑ i ∈ t, x i) ^ (#t - 1) * (x a + ∑ i ∈ t, x i) := by
              calc
                _ = (x a + ∑ i ∈ t, x i) ^ ((#t - 1) + 1) := by congr 1; omega
                _ = _ := by rw [pow_succ]
            have hbase : (∑ i ∈ t, x i) ^ (#t - 1) ≤
                (x a + ∑ i ∈ t, x i) ^ (#t - 1) := by
              gcongr
              exact le_add_of_nonneg_left hxa
            calc
              _ = (∑ i ∈ t, x i + x a) * (∑ i ∈ t, x i) ^ (#t - 1) := by
                rw [hpowS]
                ring
              _ ≤ (∑ i ∈ t, x i + x a) * (x a + ∑ i ∈ t, x i) ^ (#t - 1) :=
                mul_le_mul_of_nonneg_left hbase (add_nonneg htS hxa)
              _ = (x a + ∑ i ∈ t, x i) ^ #t := by
                rw [hpowA]
                ring
          have hstep : (∏ j ∈ t, x j) + x a * (∑ i ∈ t, ∏ j ∈ t.erase i, x j) ≤
              (x a + ∑ i ∈ t, x i) ^ #t := by
            calc
              (∏ j ∈ t, x j) + x a * (∑ i ∈ t, ∏ j ∈ t.erase i, x j) ≤
                  (∑ i ∈ t, x i) ^ #t + x a * (∑ i ∈ t, x i) ^ (#t - 1) :=
                add_le_add hP (mul_le_mul_of_nonneg_left hE hxa)
              _ ≤ (x a + ∑ i ∈ t, x i) ^ #t := hpow
          rw [hrec]
          simpa [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, add_comm] using hstep
    simpa using hbound s (fun i hi => (hx i hi).le)
  apply (le_div_iff₀ hprod).2
  rw [mul_comm]
  rw [hkey]
  exact hsymmetric

/-- Each of finitely many positive reals is at least their product divided by the `(n-1)`-st power
of their sum. -/
theorem prod_div_sum_pow_le (hx : ∀ i ∈ s, 0 < x i) {i : ι} (hi : i ∈ s) :
    (∏ j ∈ s, x j) / (∑ j ∈ s, x j) ^ (#s - 1) ≤ x i := by
  classical
  have hS : 0 < ∑ j ∈ s, x j := sum_pos hx ⟨i, hi⟩
  have h1 : ∏ j ∈ s.erase i, x j ≤ (∑ j ∈ s, x j) ^ (#s - 1) := by
    calc ∏ j ∈ s.erase i, x j ≤ ∏ _j ∈ s.erase i, ∑ k ∈ s, x k :=
          prod_le_prod₀ (fun j hj ↦ (hx j (mem_of_mem_erase hj)).le)
            (fun j hj ↦ single_le_sum (fun k hk ↦ (hx k hk).le) (mem_of_mem_erase hj))
      _ = (∑ j ∈ s, x j) ^ (#s - 1) := by rw [prod_const, card_erase_of_mem hi]
  rw [← mul_prod_erase s x hi, div_le_iff₀ (pow_pos hS _)]
  exact mul_le_mul_of_nonneg_left h1 (hx i hi).le

end Real
