-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Euclidean/Completeness/IteratedSobolevBanach.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Euclidean.Completeness.IteratedSobolevCauchy
public import CalabiYau.Analysis.Sobolev.Euclidean.WeakDerivative.Closedness

@[expose] public section

-- Private declarations used in public declarations require the compatibility option below.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Sobolev
namespace Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem exists_subseq_geom_bound
    {k : ℕ} {p : ℝ≥0∞} {Ω : Set E} {u : ℕ → E → ℝ}
    (hu_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      iteratedWeakSobolevNorm (d := d) k p (fun x => u m x - u n x) Ω ≤ ENNReal.ofReal ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i, iteratedWeakSobolevNorm (d := d) k p (fun x => u (φ (i + 1)) x - u (φ i) x) Ω ≤
        ENNReal.ofReal ((1 : ℝ) / 2 ^ (i + 1)) := by
  classical
  have h_choose : ∀ i : ℕ, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      iteratedWeakSobolevNorm (d := d) k p (fun x => u m x - u n x) Ω ≤
        ENNReal.ofReal ((1 : ℝ) / 2 ^ (i + 1)) := by
    intro i
    have hpos : (0 : ℝ) < (1 : ℝ) / 2 ^ (i + 1) := by positivity
    exact hu_cauchy ((1 : ℝ) / 2 ^ (i + 1)) hpos
  let N_seq : ℕ → ℕ := fun i => (h_choose i).choose
  have hN_spec : ∀ i m n, N_seq i ≤ m → N_seq i ≤ n →
      iteratedWeakSobolevNorm (d := d) k p (fun x => u m x - u n x) Ω ≤
        ENNReal.ofReal ((1 : ℝ) / 2 ^ (i + 1)) :=
    fun i => (h_choose i).choose_spec
  let φ : ℕ → ℕ := fun i => Nat.rec (N_seq 0)
    (fun i φi => max (N_seq (i + 1)) (φi + 1)) i
  have hφ_zero : φ 0 = N_seq 0 := rfl
  have hφ_succ : ∀ i, φ (i + 1) = max (N_seq (i + 1)) (φ i + 1) := fun _ => rfl
  have hφ_strict : StrictMono φ := by
    apply strictMono_nat_of_lt_succ
    intro i
    rw [hφ_succ]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  have hφ_ge_N : ∀ i, N_seq i ≤ φ i := by
    intro i
    cases i with
    | zero => exact le_of_eq hφ_zero.symm
    | succ i => rw [hφ_succ]; exact le_max_left _ _
  refine ⟨φ, hφ_strict, ?_⟩
  intro i
  have h_φi : N_seq i ≤ φ i := hφ_ge_N i
  have h_φi1 : N_seq i ≤ φ (i + 1) := by
    rw [hφ_succ]
    exact le_trans h_φi (le_trans (Nat.le_succ _) (le_max_right _ _))
  exact hN_spec i (φ (i + 1)) (φ i) h_φi1 h_φi

private lemma summable_geom_pow_two : Summable (fun i : ℕ => (1 : ℝ) / 2 ^ i) := by
  have hgeom : Summable (fun i : ℕ => ((1 : ℝ) / 2) ^ i) := by
    have h2 : ‖((1 : ℝ) / 2)‖ < 1 := by
      rw [Real.norm_eq_abs]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
      norm_num
    exact summable_geometric_of_norm_lt_one h2
  have heq : (fun i : ℕ => ((1 : ℝ) / 2) ^ i) = (fun i : ℕ => (1 : ℝ) / 2 ^ i) := by
    funext i; rw [div_pow, one_pow]
  rwa [heq] at hgeom

private lemma summable_2_div_pow : Summable (fun N : ℕ => 2 * (1 : ℝ) / 2 ^ N) := by
  have h := summable_geom_pow_two.const_smul (2 : ℝ)
  exact h.congr fun N => by simp only [smul_eq_mul, div_eq_mul_inv]; ring

private lemma tsum_ofReal_2_div_pow_ne_top :
    ∑' i : ℕ, ENNReal.ofReal (2 * (1 : ℝ) / 2 ^ i) ≠ ∞ := by
  have h_nn : ∀ i : ℕ, 0 ≤ 2 * (1 : ℝ) / 2 ^ i := fun _ => by positivity
  have h_eq : ∑' i, ENNReal.ofReal (2 * (1 : ℝ) / 2 ^ i) =
      ENNReal.ofReal (∑' i, 2 * (1 : ℝ) / 2 ^ i) :=
    (ENNReal.ofReal_tsum_of_nonneg h_nn summable_2_div_pow).symm
  rw [h_eq]
  exact ENNReal.ofReal_ne_top

private theorem wkpNorm_telescope_sum
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set E} (hΩ : IsOpen Ω)
    {v : ℕ → E → ℝ}
    (hv_mem : ∀ n, MemWkp (d := d) k p (v n) Ω)
    (n ℓ : ℕ) :
    iteratedWeakSobolevNorm (d := d) k p (fun x => v (n + ℓ) x - v n x) Ω ≤
      ∑ i ∈ Finset.range ℓ,
        iteratedWeakSobolevNorm (d := d) k p (fun x => v (n + i + 1) x - v (n + i) x) Ω := by
  induction ℓ with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, add_zero]
      have h_zero_fun : (fun x : E => v n x - v n x) =
          (fun _ : E => (0 : ℝ)) := by
        funext x; ring
      rw [h_zero_fun]
      rw [wkpNorm_zero_fun_zero (d := d) hp hΩ]
  | succ ℓ ih =>
      set L : E → ℝ := fun x => v (n + (ℓ + 1)) x - v n x with hL_def
      set A : E → ℝ := fun x => v (n + ℓ) x - v n x with hA_def
      set C : E → ℝ := fun x => v (n + ℓ + 1) x - v (n + ℓ) x with hC_def
      have hL_eq : L = (fun x => A x + C x) := by
        funext x
        have heq : n + (ℓ + 1) = n + ℓ + 1 := by ring
        simp only [hL_def, hA_def, hC_def]
        rw [heq]; ring
      have hA_mem : MemWkp (d := d) k p A Ω :=
        MemWkp.sub (d := d) hp hΩ (hv_mem (n + ℓ)) (hv_mem n)
      have hC_mem : MemWkp (d := d) k p C Ω :=
        MemWkp.sub (d := d) hp hΩ (hv_mem (n + ℓ + 1)) (hv_mem (n + ℓ))
      have h_le_triangle :
          iteratedWeakSobolevNorm (d := d) k p (fun x => A x + C x) Ω ≤
            iteratedWeakSobolevNorm (d := d) k p A Ω + iteratedWeakSobolevNorm (d := d) k p C Ω :=
        wkpNorm_add_le (d := d) hp hΩ hA_mem hC_mem
      have hL_norm_eq :
          iteratedWeakSobolevNorm (d := d) k p L Ω = iteratedWeakSobolevNorm (d := d) k p
            (fun x => A x + C x) Ω := by
        rw [hL_eq]
      have hL_le :
          iteratedWeakSobolevNorm (d := d) k p L Ω ≤
            iteratedWeakSobolevNorm (d := d) k p A Ω + iteratedWeakSobolevNorm (d := d) k p C
              Ω := by
        rw [hL_norm_eq]
        exact h_le_triangle
      have h_ih_le_sum :
          iteratedWeakSobolevNorm (d := d) k p A Ω ≤
            ∑ i ∈ Finset.range ℓ,
              iteratedWeakSobolevNorm (d := d) k p (fun x => v (n + i + 1) x - v (n + i) x) Ω := ih
      have h_step :
          iteratedWeakSobolevNorm (d := d) k p A Ω + iteratedWeakSobolevNorm (d := d) k p C Ω ≤
            (∑ i ∈ Finset.range ℓ,
              iteratedWeakSobolevNorm (d := d) k p
                (fun x => v (n + i + 1) x - v (n + i) x) Ω) +
              iteratedWeakSobolevNorm (d := d) k p C Ω := by
        exact add_le_add h_ih_le_sum (le_refl _)
      have h_succ_eq :
          (∑ i ∈ Finset.range ℓ,
            iteratedWeakSobolevNorm (d := d) k p (fun x => v (n + i + 1) x - v (n + i) x) Ω) +
            iteratedWeakSobolevNorm (d := d) k p C Ω =
          ∑ i ∈ Finset.range (ℓ + 1),
            iteratedWeakSobolevNorm (d := d) k p (fun x => v (n + i + 1) x - v (n + i) x) Ω := by
        rw [Finset.sum_range_succ]
      calc
        iteratedWeakSobolevNorm (d := d) k p (fun x => v (n + (ℓ + 1)) x - v n x) Ω
            = iteratedWeakSobolevNorm (d := d) k p L Ω := rfl
        _ ≤ iteratedWeakSobolevNorm (d := d) k p A Ω + iteratedWeakSobolevNorm (d := d) k p C Ω :=
          hL_le
        _ ≤ (∑ i ∈ Finset.range ℓ,
              iteratedWeakSobolevNorm (d := d) k p
                (fun x => v (n + i + 1) x - v (n + i) x) Ω) +
              iteratedWeakSobolevNorm (d := d) k p C Ω := h_step
        _ = ∑ i ∈ Finset.range (ℓ + 1),
              iteratedWeakSobolevNorm (d := d) k p
                (fun x => v (n + i + 1) x - v (n + i) x) Ω := h_succ_eq

private theorem wkpNorm_sub_comm
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set E} (hΩ : IsOpen Ω)
    {a b : E → ℝ}
    (ha : MemWkp (d := d) k p a Ω) (hb : MemWkp (d := d) k p b Ω) :
    iteratedWeakSobolevNorm (d := d) k p (fun x => a x - b x) Ω =
      iteratedWeakSobolevNorm (d := d) k p (fun x => b x - a x) Ω := by
  have h_eq : (fun x : E => a x - b x) =
      (fun x => (-1 : ℝ) * (b x - a x)) := by
    funext x; ring
  have h_ba : MemWkp (d := d) k p (fun x => b x - a x) Ω :=
    MemWkp.sub (d := d) hp hΩ hb ha
  rw [h_eq]
  rw [wkpNorm_const_smul (d := d) hp hΩ h_ba (-1)]
  have h_norm_neg_one : ‖(-1 : ℝ)‖ₑ = 1 := by
    simp
  rw [h_norm_neg_one, one_mul]

private lemma partial_geom_sum_eq (ℓ : ℕ) :
    ∑ i ∈ Finset.range ℓ, ((1 : ℝ) / 2) ^ i = 2 - 2 * ((1 : ℝ) / 2) ^ ℓ := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
      rw [Finset.sum_range_succ, ih]
      have hpow : ((1 : ℝ) / 2) ^ (ℓ + 1) = (1 / 2) ^ ℓ / 2 := by
        rw [pow_succ]
        ring
      rw [hpow]
      ring

private lemma partial_geom_sum_lt_two (ℓ : ℕ) :
    ∑ i ∈ Finset.range ℓ, ((1 : ℝ) / 2) ^ i < 2 := by
  rw [partial_geom_sum_eq]
  have hpow_pos : (0 : ℝ) < ((1 : ℝ) / 2) ^ ℓ := by positivity
  linarith

private lemma scaled_partial_geom_sum_lt
    (n ℓ : ℕ) :
    ∑ i ∈ Finset.range ℓ, (1 : ℝ) / 2 ^ (n + i + 1) < (1 : ℝ) / 2 ^ n := by
  have h_factor : ∀ i : ℕ, (1 : ℝ) / 2 ^ (n + i + 1) =
      (1 / 2 ^ (n + 1)) * ((1 / 2) ^ i) := by
    intro i
    have h_index : n + i + 1 = (n + 1) + i := by ring
    rw [h_index]
    rw [pow_add]
    rw [div_pow, one_pow]
    field_simp
  have h_sum_eq : ∑ i ∈ Finset.range ℓ, (1 : ℝ) / 2 ^ (n + i + 1) =
      (1 / 2 ^ (n + 1)) * ∑ i ∈ Finset.range ℓ, ((1 : ℝ) / 2) ^ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact h_factor i
  rw [h_sum_eq]
  have h_sum_lt : ∑ i ∈ Finset.range ℓ, ((1 : ℝ) / 2) ^ i < 2 := partial_geom_sum_lt_two ℓ
  have h_pos : (0 : ℝ) < 1 / 2 ^ (n + 1) := by positivity
  calc
    (1 / 2 ^ (n + 1)) * ∑ i ∈ Finset.range ℓ, ((1 : ℝ) / 2) ^ i
        < (1 / 2 ^ (n + 1)) * 2 := by
          exact (mul_lt_mul_of_pos_left h_sum_lt h_pos)
    _ = 1 / 2 ^ n := by
          rw [pow_succ]
          field_simp

private theorem wkpNorm_subseq_lt
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set E} (hΩ : IsOpen Ω)
    {u : ℕ → E → ℝ}
    (hu_mem : ∀ n, MemWkp (d := d) k p (u n) Ω)
    {φ : ℕ → ℕ} (_hφ : StrictMono φ)
    (h_geom : ∀ i, iteratedWeakSobolevNorm (d := d) k p (fun x => u (φ (i + 1)) x - u (φ i) x) Ω ≤
      ENNReal.ofReal ((1 : ℝ) / 2 ^ (i + 1))) :
    ∀ N n m : ℕ, N ≤ n → N ≤ m →
      iteratedWeakSobolevNorm (d := d) k p (fun x => u (φ n) x - u (φ m) x) Ω <
        ENNReal.ofReal (2 * (1 : ℝ) / 2 ^ N) := by
  have h_aux : ∀ a b : ℕ, a ≤ b →
      iteratedWeakSobolevNorm (d := d) k p (fun x => u (φ b) x - u (φ a) x) Ω ≤
      ENNReal.ofReal ((1 : ℝ) / 2 ^ a) := by
    intro a b hab
    obtain ⟨ℓ, rfl⟩ := Nat.le.dest hab
    have h_telescope := wkpNorm_telescope_sum (d := d) hp hΩ
      (v := fun n => u (φ n)) (fun n => hu_mem (φ n)) a ℓ
    have h_each : ∀ i,
        iteratedWeakSobolevNorm (d := d) k p
          (fun x => u (φ (a + i + 1)) x - u (φ (a + i)) x) Ω ≤
        ENNReal.ofReal ((1 : ℝ) / 2 ^ (a + i + 1)) := fun i => h_geom (a + i)
    have h_sum_bound :
        (∑ i ∈ Finset.range ℓ,
          iteratedWeakSobolevNorm (d := d) k p
            (fun x => u (φ (a + i + 1)) x - u (φ (a + i)) x) Ω) ≤
        ∑ i ∈ Finset.range ℓ, ENNReal.ofReal ((1 : ℝ) / 2 ^ (a + i + 1)) :=
      Finset.sum_le_sum (fun i _ => h_each i)
    have h_geom_sum :
        ∑ i ∈ Finset.range ℓ, ENNReal.ofReal ((1 : ℝ) / 2 ^ (a + i + 1)) ≤
          ENNReal.ofReal ((1 : ℝ) / 2 ^ a) := by
      classical
      have h_nn : ∀ i ∈ Finset.range ℓ, (0 : ℝ) ≤ (1 : ℝ) / 2 ^ (a + i + 1) :=
        fun _ _ => by positivity
      rw [← ENNReal.ofReal_sum_of_nonneg h_nn]
      apply ENNReal.ofReal_le_ofReal
      exact (scaled_partial_geom_sum_lt a ℓ).le
    exact le_trans h_telescope (le_trans h_sum_bound h_geom_sum)
  intro N n m hn hm
  have h_strict_real : ∀ a : ℕ, N ≤ a → (1 : ℝ) / 2 ^ a < 2 * (1 : ℝ) / 2 ^ N := by
    intro a hNa
    have h_pow : (2 : ℝ) ^ N ≤ 2 ^ a :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hNa
    have h2 : 0 < (2 : ℝ) ^ a := by positivity
    have h3 : 0 < (2 : ℝ) ^ N := by positivity
    have h_div_le : (1 : ℝ) / 2 ^ a ≤ 1 / 2 ^ N := one_div_le_one_div_of_le h3 h_pow
    have h_pos : (0 : ℝ) < 1 / 2 ^ N := by positivity
    have h_lt : (1 : ℝ) / 2 ^ N < 2 * (1 / 2 ^ N) := by
      have : (1 : ℝ) < 2 := by norm_num
      nlinarith
    have h_eq : (2 : ℝ) * ((1 : ℝ) / 2 ^ N) = 2 * (1 : ℝ) / 2 ^ N := by ring
    rw [h_eq] at h_lt
    linarith
  by_cases hnm : n ≤ m
  · have h_le := h_aux n m hnm
    have h_strict :
        ENNReal.ofReal ((1 : ℝ) / 2 ^ n) < ENNReal.ofReal (2 * (1 : ℝ) / 2 ^ N) := by
      rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
      exact h_strict_real n hn
    rw [wkpNorm_sub_comm (d := d) hp hΩ (hu_mem (φ n)) (hu_mem (φ m))]
    exact lt_of_le_of_lt h_le h_strict
  · have hm_le_n : m ≤ n := Nat.le_of_lt (Nat.lt_of_not_le hnm)
    have h_le := h_aux m n hm_le_n
    have h_strict :
        ENNReal.ofReal ((1 : ℝ) / 2 ^ m) < ENNReal.ofReal (2 * (1 : ℝ) / 2 ^ N) := by
      rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
      exact h_strict_real m hm
    exact lt_of_le_of_lt h_le h_strict

private theorem exists_iter_limits_subseq
    {k : ℕ} {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {Ω : Set E} (hΩ : IsOpen Ω)
    {u : ℕ → E → ℝ}
    (hu_mem : ∀ n, MemWkp (d := d) k p (u n) Ω)
    {φ : ℕ → ℕ} (hφ_strict : StrictMono φ)
    (h_geom : ∀ i, iteratedWeakSobolevNorm (d := d) k p
        (fun x => u (φ (i + 1)) x - u (φ i) x) Ω ≤
      ENNReal.ofReal ((1 : ℝ) / 2 ^ (i + 1))) :
    ∃ v : ∀ j : ℕ, (Fin j → Fin d) → E → ℝ,
      (∀ (j : ℕ) (β : Fin j → Fin d), j ≤ k →
        MemLp (v j β) p (volume.restrict Ω)) ∧
      (∀ (j : ℕ) (β : Fin j → Fin d), j ≤ k →
        Tendsto
          (fun i => eLpNorm
            (fun x => iterWeakPartial (d := d) p j β (u (φ i)) Ω x - v j β x)
            p (volume.restrict Ω))
          atTop (𝓝 0)) := by
  classical
  let B : ℕ → ℝ≥0∞ := fun N => ENNReal.ofReal (2 * (1 : ℝ) / 2 ^ N)
  have hB_summable : ∑' i, B i ≠ ∞ := tsum_ofReal_2_div_pow_ne_top
  have h_cau : ∀ N n m : ℕ, N ≤ n → N ≤ m →
      iteratedWeakSobolevNorm (d := d) k p
        (fun x => u (φ n) x - u (φ m) x) Ω < B N :=
    wkpNorm_subseq_lt (d := d) hp_one hΩ hu_mem hφ_strict h_geom
  have hu_φ : ∀ i, MemWkp (d := d) k p (u (φ i)) Ω := fun i => hu_mem (φ i)
  have h_each : ∀ (j : ℕ) (β : Fin j → Fin d), j ≤ k → ∃ v_jβ : E → ℝ,
      MemLp v_jβ p (volume.restrict Ω) ∧
      atTop.Tendsto
        (fun n => eLpNorm
          (fun x => iterWeakPartial (d := d) p j β (u (φ n)) Ω x - v_jβ x)
          p (volume.restrict Ω))
        (𝓝 0) := by
    intro j β hj
    exact @exists_eLpNorm_limit_iterWeakPartial d k p hp_one Ω hΩ
      (fun i => u (φ i)) hu_φ B hB_summable h_cau j hj β
  refine ⟨fun j β => if hj : j ≤ k then (h_each j β hj).choose else (fun _ : E => (0 : ℝ)),
    ?_, ?_⟩
  · intro j β hj
    change MemLp (if hj' : j ≤ k then (h_each j β hj').choose else (fun _ : E => (0 : ℝ)))
      p (volume.restrict Ω)
    rw [dif_pos hj]
    exact (h_each j β hj).choose_spec.1
  · intro j β hj
    change Tendsto (fun n => eLpNorm
        (fun x => iterWeakPartial (d := d) p j β (u (φ n)) Ω x -
          (if hj' : j ≤ k then (h_each j β hj').choose else (fun _ : E => (0 : ℝ))) x)
        p (volume.restrict Ω))
      atTop (𝓝 0)
    rw [dif_pos hj]
    exact (h_each j β hj).choose_spec.2

private theorem subseq_limit_memWkp_and_wkpNorm_tendsto
    {k : ℕ} {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {Ω : Set E} (hΩ : IsOpen Ω)
    {u : ℕ → E → ℝ}
    (hu_mem : ∀ n, MemWkp (d := d) k p (u n) Ω)
    {φ : ℕ → ℕ} (hφ_strict : StrictMono φ)
    (h_geom : ∀ i, iteratedWeakSobolevNorm (d := d) k p
        (fun x => u (φ (i + 1)) x - u (φ i) x) Ω ≤
      ENNReal.ofReal ((1 : ℝ) / 2 ^ (i + 1))) :
    ∃ u_lim : E → ℝ, MemWkp (d := d) k p u_lim Ω ∧
      Tendsto
        (fun i => iteratedWeakSobolevNorm (d := d) k p (fun x => u (φ i) x - u_lim x) Ω)
        atTop (𝓝 0) := by
  classical
  obtain ⟨v, hv_lp, h_v_tendsto⟩ :=
    exists_iter_limits_subseq (d := d) hp_one hΩ hu_mem hφ_strict h_geom
  obtain ⟨h_lim_mem, h_lim_iter_ae⟩ :=
    MemWkp_of_iter_tendsto_eLpNorm (d := d) hp_one hΩ k
      (u_n := fun i => u (φ i)) (fun i => hu_mem (φ i)) v hv_lp h_v_tendsto
  refine ⟨v 0 ![], h_lim_mem, ?_⟩
  unfold iteratedWeakSobolevNorm
  have h_per_pair : ∀ (j : ℕ) (_hj : j ∈ Finset.range (k + 1)) (β : Fin j → Fin d),
      Tendsto
        (fun i => eLpNorm
          (iterWeakPartial (d := d) p j β
            (fun x => u (φ i) x - v 0 ![] x) Ω) p (volume.restrict Ω))
        atTop (𝓝 0) := by
    intro j hj β
    have hj_le : j ≤ k := by rw [Finset.mem_range] at hj; omega
    have h_lim_v : MemWkp (d := d) j p (v 0 ![]) Ω := MemWkp.le_of_le hj_le h_lim_mem
    have h_seq_v : ∀ i, MemWkp (d := d) j p (u (φ i)) Ω :=
      fun i => MemWkp.le_of_le hj_le (hu_mem (φ i))
    have h_iter_sub : ∀ i,
        iterWeakPartial (d := d) p j β (fun x => u (φ i) x - v 0 ![] x) Ω
          =ᵐ[volume.restrict Ω]
        (fun x => iterWeakPartial (d := d) p j β (u (φ i)) Ω x -
          iterWeakPartial (d := d) p j β (v 0 ![]) Ω x) := by
      intro i
      have h_eq : (fun x => u (φ i) x - v 0 ![] x) =
          (fun x => u (φ i) x + (-1) * v 0 ![] x) := by
        funext x; ring
      rw [h_eq]
      have h_neg_v : MemWkp (d := d) j p (fun x => (-1 : ℝ) * v 0 ![] x) Ω :=
        MemWkp.const_smul (d := d) hp_one hΩ h_lim_v (-1)
      have h_iter_add :
          iterWeakPartial (d := d) p j β (fun x => u (φ i) x + (-1) * v 0 ![] x) Ω
            =ᵐ[volume.restrict Ω]
          fun x => iterWeakPartial (d := d) p j β (u (φ i)) Ω x +
            iterWeakPartial (d := d) p j β (fun x => (-1 : ℝ) * v 0 ![] x) Ω x :=
        iterWeakPartial_add_ae (d := d) hp_one hΩ β (h_seq_v i) h_neg_v
      have h_iter_smul :
          iterWeakPartial (d := d) p j β (fun x => (-1 : ℝ) * v 0 ![] x) Ω
            =ᵐ[volume.restrict Ω]
          fun x => (-1 : ℝ) * iterWeakPartial (d := d) p j β (v 0 ![]) Ω x :=
        iterWeakPartial_const_smul_ae (d := d) hp_one hΩ β h_lim_v (-1)
      filter_upwards [h_iter_add, h_iter_smul] with x hx_add hx_smul
      rw [hx_add]
      rw [hx_smul]
      ring
    have h_iter_v_ae :
        iterWeakPartial (d := d) p j β (v 0 ![]) Ω =ᵐ[volume.restrict Ω] v j β :=
      h_lim_iter_ae j β hj_le
    have h_combined : ∀ i,
        iterWeakPartial (d := d) p j β (fun x => u (φ i) x - v 0 ![] x) Ω
          =ᵐ[volume.restrict Ω]
        (fun x => iterWeakPartial (d := d) p j β (u (φ i)) Ω x - v j β x) := by
      intro i
      filter_upwards [h_iter_sub i, h_iter_v_ae] with x hx hxv
      rw [hx]
      rw [hxv]
    have h_norm_eq : ∀ i,
        eLpNorm
          (iterWeakPartial (d := d) p j β
            (fun x => u (φ i) x - v 0 ![] x) Ω) p (volume.restrict Ω) =
        eLpNorm
          (fun x => iterWeakPartial (d := d) p j β (u (φ i)) Ω x - v j β x)
          p (volume.restrict Ω) := fun i => eLpNorm_congr_ae (h_combined i)
    have h_targ := h_v_tendsto j β hj_le
    have h_eq_fun : (fun i => eLpNorm
        (iterWeakPartial (d := d) p j β
          (fun x => u (φ i) x - v 0 ![] x) Ω) p (volume.restrict Ω)) =
        (fun i => eLpNorm
          (fun x => iterWeakPartial (d := d) p j β (u (φ i)) Ω x - v j β x)
          p (volume.restrict Ω)) := by
      funext i; exact h_norm_eq i
    rw [h_eq_fun]
    exact h_targ
  have h_inner_tendsto : ∀ j ∈ Finset.range (k + 1),
      Tendsto
        (fun n => ∑ β : Fin j → Fin d,
          eLpNorm (iterWeakPartial (d := d) p j β
            (fun x => u (φ n) x - v 0 ![] x) Ω) p (volume.restrict Ω))
        atTop (𝓝 0) := by
    intro j hj
    have h_β_tendsto : ∀ β : Fin j → Fin d, Tendsto
        (fun n => eLpNorm
          (iterWeakPartial (d := d) p j β
            (fun x => u (φ n) x - v 0 ![] x) Ω)
          p (volume.restrict Ω))
        atTop (𝓝 0) := fun β => h_per_pair j hj β
    have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin j → Fin d))
      (fun β _ => h_β_tendsto β)
    simpa using hsum
  have hfinal := tendsto_finsetSum (Finset.range (k + 1)) h_inner_tendsto
  simpa using hfinal

private theorem wkpNorm_tendsto_of_cauchy_of_subseq
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set E} (hΩ : IsOpen Ω)
    {u : ℕ → E → ℝ} {u_lim : E → ℝ}
    (hu_mem : ∀ n, MemWkp (d := d) k p (u n) Ω)
    (hu_lim_mem : MemWkp (d := d) k p u_lim Ω)
    (hu_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      iteratedWeakSobolevNorm (d := d) k p (fun x => u m x - u n x) Ω ≤ ENNReal.ofReal ε)
    {φ : ℕ → ℕ} (hφ_strict : StrictMono φ)
    (h_subseq_tendsto : Tendsto
      (fun i => iteratedWeakSobolevNorm (d := d) k p (fun x => u (φ i) x - u_lim x) Ω)
      atTop (𝓝 0)) :
    Tendsto
      (fun n => iteratedWeakSobolevNorm (d := d) k p (fun x => u n x - u_lim x) Ω)
      atTop (𝓝 0) := by
  classical
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε_pos
  by_cases h_top : ε = ⊤
  · refine ⟨0, ?_⟩
    intro n _
    rw [h_top]; exact le_top
  have hε_ne : ε ≠ ⊤ := h_top
  have hε_real_pos : 0 < ε.toReal := ENNReal.toReal_pos hε_pos.ne' hε_ne
  set δ : ℝ := ε.toReal / 2 with hδ_def
  have hδ_pos : 0 < δ := half_pos hε_real_pos
  obtain ⟨N₁, hN₁⟩ := hu_cauchy δ hδ_pos
  have hδ_ofReal_pos : 0 < ENNReal.ofReal δ := by
    rw [ENNReal.ofReal_pos]; exact hδ_pos
  rw [ENNReal.tendsto_atTop_zero] at h_subseq_tendsto
  obtain ⟨N₂, hN₂⟩ := h_subseq_tendsto (ENNReal.ofReal δ) hδ_ofReal_pos
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  have hn_N₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn_N₂ : N₂ ≤ n := le_trans (le_max_right _ _) hn
  have h_φn_ge_n : n ≤ φ n := hφ_strict.id_le n
  have h_φn_ge_N₁ : N₁ ≤ φ n := le_trans hn_N₁ h_φn_ge_n
  have h_cauchy_bound : iteratedWeakSobolevNorm (d := d) k p (fun x => u n x - u (φ n) x) Ω ≤
      ENNReal.ofReal δ :=
    hN₁ n (φ n) hn_N₁ h_φn_ge_N₁
  have h_subseq_bound : iteratedWeakSobolevNorm (d := d) k p (fun x => u (φ n) x - u_lim x) Ω ≤
      ENNReal.ofReal δ := hN₂ n hn_N₂
  have h_triangle :
      iteratedWeakSobolevNorm (d := d) k p (fun x => u n x - u_lim x) Ω ≤
        iteratedWeakSobolevNorm (d := d) k p (fun x => u n x - u (φ n) x) Ω +
          iteratedWeakSobolevNorm (d := d) k p (fun x => u (φ n) x - u_lim x) Ω := by
    have h_split : (fun x : E => u n x - u_lim x) =
        (fun x => (u n x - u (φ n) x) + (u (φ n) x - u_lim x)) := by
      funext x; ring
    rw [h_split]
    apply wkpNorm_add_le (d := d) hp hΩ
    · exact MemWkp.sub (d := d) hp hΩ (hu_mem n) (hu_mem (φ n))
    · exact MemWkp.sub (d := d) hp hΩ (hu_mem (φ n)) hu_lim_mem
  calc
    iteratedWeakSobolevNorm (d := d) k p (fun x => u n x - u_lim x) Ω
        ≤ iteratedWeakSobolevNorm (d := d) k p (fun x => u n x - u (φ n) x) Ω +
            iteratedWeakSobolevNorm (d := d) k p (fun x => u (φ n) x - u_lim x) Ω := h_triangle
    _ ≤ ENNReal.ofReal δ + ENNReal.ofReal δ := by
        exact add_le_add h_cauchy_bound h_subseq_bound
    _ = ENNReal.ofReal (δ + δ) := (ENNReal.ofReal_add hδ_pos.le hδ_pos.le).symm
    _ = ENNReal.ofReal ε.toReal := by
        congr 1
        show δ + δ = ε.toReal
        rw [hδ_def]
        ring
    _ = ε := ENNReal.ofReal_toReal hε_ne

theorem MemWkp.exists_limit_of_wkpNorm_cauchy
    {Ω : Set E} (hΩ_open : IsOpen Ω)
    (k : ℕ) (p : ℝ≥0∞) (hp_one : 1 ≤ p)
    {u : ℕ → E → ℝ}
    (hu_mem : ∀ n, MemWkp (d := d) k p (u n) Ω)
    (hu_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      iteratedWeakSobolevNorm (d := d) k p (fun x => u m x - u n x) Ω ≤ ENNReal.ofReal ε) :
    ∃ u_lim : E → ℝ,
      MemWkp (d := d) k p u_lim Ω ∧
      Filter.Tendsto
        (fun n => iteratedWeakSobolevNorm (d := d) k p (fun x => u n x - u_lim x) Ω)
        Filter.atTop (𝓝 0) := by
  classical
  obtain ⟨φ, hφ_strict, h_geom⟩ :=
    exists_subseq_geom_bound (d := d) (k := k) (p := p) (Ω := Ω) (u := u) hu_cauchy
  obtain ⟨u_lim, hu_lim_mem, h_subseq_tendsto⟩ :=
    subseq_limit_memWkp_and_wkpNorm_tendsto (d := d) hp_one hΩ_open
      hu_mem hφ_strict h_geom
  refine ⟨u_lim, hu_lim_mem, ?_⟩
  exact wkpNorm_tendsto_of_cauchy_of_subseq (d := d) hp_one hΩ_open
    hu_mem hu_lim_mem hu_cauchy hφ_strict h_subseq_tendsto

end Euclidean
end Sobolev
