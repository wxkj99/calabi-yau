-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Euclidean/WeakDerivative/Closedness.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

@[expose] public section


noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Sobolev
namespace Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)
section

variable [NeZero d]


private def conj (p : ℝ≥0∞) : ℝ≥0∞ := (1 - p⁻¹)⁻¹

private lemma conj_inv_add_inv_eq_one {p : ℝ≥0∞} (hp : 1 ≤ p) :
    p⁻¹ + (conj p)⁻¹ = 1 := by
  unfold conj
  have h_inv_le_one : p⁻¹ ≤ 1 := ENNReal.inv_le_one.mpr hp
  rw [inv_inv]
  exact (add_tsub_cancel_of_le h_inv_le_one)

private theorem holderConjugate_conj (p : ℝ≥0∞) (hp : 1 ≤ p) :
    ENNReal.HolderConjugate p (conj p) where
  inv_add_inv_eq_inv := by
    simp only [inv_one]
    exact conj_inv_add_inv_eq_one hp

end

private lemma memLp_of_contDiff_hasCompactSupport
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_support : HasCompactSupport φ)
    (Ω : Set E) (q : ℝ≥0∞) :
    MemLp φ q (volume.restrict Ω) :=
  (hφ.continuous.memLp_of_hasCompactSupport hφ_support).restrict _

private lemma fderiv_apply_memLp
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_support : HasCompactSupport φ)
    (v : E) (Ω : Set E) (q : ℝ≥0∞) :
    MemLp (fun x => (fderiv ℝ φ x) v) q (volume.restrict Ω) := by
  have hcont : Continuous (fun x => (fderiv ℝ φ x) v) :=
    (hφ.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
      continuous_const
  have hcpt : HasCompactSupport (fun x => (fderiv ℝ φ x) v) :=
    hφ_support.fderiv_apply (𝕜 := ℝ) v
  exact (hcont.memLp_of_hasCompactSupport hcpt).restrict _

private lemma abs_integral_mul_le_eLpNorm_mul_eLpNorm
    {μ : Measure E} {f g : E → ℝ} {p q : ℝ≥0∞}
    [ENNReal.HolderConjugate p q]
    (hf : MemLp f p μ) (hg : MemLp g q μ) :
    ENNReal.ofReal |∫ x, f x * g x ∂μ| ≤ eLpNorm f p μ * eLpNorm g q μ := by
  have h_abs_le_lintegral :
      ENNReal.ofReal |∫ x, f x * g x ∂μ| ≤ ∫⁻ x, ‖f x * g x‖ₑ ∂μ := by
    rw [← Real.norm_eq_abs]
    have hint : ‖∫ x, f x * g x ∂μ‖ₑ ≤ ∫⁻ x, ‖f x * g x‖ₑ ∂μ :=
      enorm_integral_le_lintegral_enorm _
    have hofreal : ENNReal.ofReal ‖∫ x, f x * g x ∂μ‖ = ‖∫ x, f x * g x ∂μ‖ₑ :=
      ofReal_norm _
    rw [hofreal]
    exact hint
  have h_lintegral_eq :
      ∫⁻ x, ‖f x * g x‖ₑ ∂μ = eLpNorm (fun x => g x * f x) 1 μ := by
    rw [eLpNorm_one_eq_lintegral_enorm (f := fun x => g x * f x) (hg.aestronglyMeasurable.mul hf.aestronglyMeasurable)]
    refine lintegral_congr (fun x => ?_)
    simp [enorm_mul, mul_comm]
  have h_smul_bound :
      eLpNorm (fun x => g x * f x) 1 μ ≤ eLpNorm g q μ * eLpNorm f p μ := by
    have h_mul_eq :
        (fun x => g x * f x) = (g : E → ℝ) • (f : E → ℝ) := by
      funext x
      simp [smul_eq_mul]
    rw [h_mul_eq]
    have : ENNReal.HolderTriple q p 1 := ENNReal.HolderTriple.symm
    exact eLpNorm_smul_le_mul_eLpNorm hg.aestronglyMeasurable hf.aestronglyMeasurable
  calc
    ENNReal.ofReal |∫ x, f x * g x ∂μ|
        ≤ ∫⁻ x, ‖f x * g x‖ₑ ∂μ := h_abs_le_lintegral
    _ = eLpNorm (fun x => g x * f x) 1 μ := h_lintegral_eq
    _ ≤ eLpNorm g q μ * eLpNorm f p μ := h_smul_bound
    _ = eLpNorm f p μ * eLpNorm g q μ := mul_comm _ _

private lemma tendsto_integral_mul_of_eLpNorm_tendsto_zero
    {μ : Measure E} {p q : ℝ≥0∞}
    [ENNReal.HolderConjugate p q]
    {f : E → ℝ} {g : ℕ → E → ℝ}
    (hf : MemLp f q μ)
    (hg : ∀ n, MemLp (g n) p μ)
    (hlim : Tendsto (fun n => eLpNorm (g n) p μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f x * g n x ∂μ) atTop (𝓝 0) := by
  have h_bound_pointwise : ∀ n,
      ENNReal.ofReal |∫ x, f x * g n x ∂μ| ≤ eLpNorm f q μ * eLpNorm (g n) p μ := by
    intro n
    have : ENNReal.HolderConjugate q p := ENNReal.HolderConjugate.symm
    have h := abs_integral_mul_le_eLpNorm_mul_eLpNorm (μ := μ) (f := f) (g := g n)
      (p := q) (q := p) hf (hg n)
    exact h
  have h_eLpNorm_f_lt_top : eLpNorm f q μ < ∞ := hf.eLpNorm_lt_top
  have h_rhs_tendsto :
      Tendsto (fun n => eLpNorm f q μ * eLpNorm (g n) p μ) atTop (𝓝 0) := by
    have htm := ENNReal.Tendsto.const_mul (a := eLpNorm f q μ) hlim
      (Or.inr h_eLpNorm_f_lt_top.ne)
    simpa using htm
  have h_abs_tendsto :
      Tendsto (fun n => |∫ x, f x * g n x ∂μ|) atTop (𝓝 0) := by
    have h_le_real : ∀ n,
        |∫ x, f x * g n x ∂μ| ≤ (eLpNorm f q μ * eLpNorm (g n) p μ).toReal := by
      intro n
      have h_finite : eLpNorm f q μ * eLpNorm (g n) p μ ≠ ∞ :=
        ENNReal.mul_ne_top h_eLpNorm_f_lt_top.ne (hg n).eLpNorm_lt_top.ne
      have h_ofreal := h_bound_pointwise n
      have h_toReal : (ENNReal.ofReal |∫ x, f x * g n x ∂μ|).toReal ≤
          (eLpNorm f q μ * eLpNorm (g n) p μ).toReal :=
        ENNReal.toReal_mono h_finite h_ofreal
      have hnn : 0 ≤ |∫ x, f x * g n x ∂μ| := abs_nonneg _
      simpa [ENNReal.toReal_ofReal hnn] using h_toReal
    have h_ge : ∀ n, 0 ≤ |∫ x, f x * g n x ∂μ| := fun _ => abs_nonneg _
    have h_rhs_real_tendsto :
        Tendsto (fun n => (eLpNorm f q μ * eLpNorm (g n) p μ).toReal) atTop (𝓝 0) := by
      have hcomp := (ENNReal.tendsto_toReal_zero_iff (f := fun n =>
        eLpNorm f q μ * eLpNorm (g n) p μ)
        (fun n => ENNReal.mul_ne_top h_eLpNorm_f_lt_top.ne (hg n).eLpNorm_lt_top.ne)).mpr
        h_rhs_tendsto
      exact hcomp
    exact squeeze_zero h_ge h_le_real h_rhs_real_tendsto
  exact (tendsto_zero_iff_abs_tendsto_zero _).2 h_abs_tendsto

theorem hasWeakPartialDeriv_of_tendsto_eLpNorm
    {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {Ω : Set E}
    (i : Fin d)
    {u_n g_n : ℕ → E → ℝ}
    {u g : E → ℝ}
    (hu_n_lp : ∀ n, MemLp (u_n n) p (volume.restrict Ω))
    (hg_n_lp : ∀ n, MemLp (g_n n) p (volume.restrict Ω))
    (hu_lp : MemLp u p (volume.restrict Ω))
    (hg_lp : MemLp g p (volume.restrict Ω))
    (h_weak : ∀ n, Sobolev.Euclidean.HasWeakPartialDeriv i (g_n n) (u_n n) Ω)
    (h_u_tendsto : Tendsto
      (fun n => eLpNorm (fun x => u_n n x - u x) p (volume.restrict Ω))
      atTop (𝓝 0))
    (h_g_tendsto : Tendsto
      (fun n => eLpNorm (fun x => g_n n x - g x) p (volume.restrict Ω))
      atTop (𝓝 0)) :
    Sobolev.Euclidean.HasWeakPartialDeriv i g u Ω := by
  intro φ hφ hφ_support hφ_sub
  let μ : Measure E := volume.restrict Ω
  let dφ : E → ℝ := fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1)
  let q : ℝ≥0∞ := conj p
  have hpq : ENNReal.HolderConjugate p q := holderConjugate_conj p hp_one
  have hpq_symm : ENNReal.HolderConjugate q p := ENNReal.HolderConjugate.symm
  have hpq1 : ENNReal.HolderTriple p q 1 := hpq
  have hpq1_symm : ENNReal.HolderTriple q p 1 := hpq_symm
  have hdφ_memLp : MemLp dφ q μ :=
    fderiv_apply_memLp hφ hφ_support (EuclideanSpace.single i 1) Ω q
  have hφ_memLp : MemLp φ q μ :=
    memLp_of_contDiff_hasCompactSupport hφ hφ_support Ω q
  have h_u_diff_memLp : ∀ n, MemLp (fun x => u_n n x - u x) p μ := fun n =>
    (hu_n_lp n).sub hu_lp
  have h_g_diff_memLp : ∀ n, MemLp (fun x => g_n n x - g x) p μ := fun n =>
    (hg_n_lp n).sub hg_lp
  have h_u_int_tendsto :
      Tendsto (fun n => ∫ x, dφ x * (u_n n x - u x) ∂μ) atTop (𝓝 0) :=
    tendsto_integral_mul_of_eLpNorm_tendsto_zero hdφ_memLp h_u_diff_memLp h_u_tendsto
  have h_g_int_tendsto :
      Tendsto (fun n => ∫ x, φ x * (g_n n x - g x) ∂μ) atTop (𝓝 0) :=
    tendsto_integral_mul_of_eLpNorm_tendsto_zero hφ_memLp h_g_diff_memLp h_g_tendsto
  have h_lhs_tendsto :
      Tendsto (fun n => ∫ x in Ω, u_n n x * dφ x)
        atTop (𝓝 (∫ x in Ω, u x * dφ x)) := by
    have h_eq : ∀ n,
        ∫ x, u_n n x * dφ x ∂μ =
          (∫ x, u x * dφ x ∂μ) + ∫ x, dφ x * (u_n n x - u x) ∂μ := by
      intro n
      have hfi : Integrable (fun x => u x * dφ x) μ := by
        exact (MemLp.integrable_mul hdφ_memLp hu_lp).congr <|
          Filter.Eventually.of_forall fun x ↦ by simp only [Pi.mul_apply, mul_comm]
      have hdi : Integrable (fun x => dφ x * (u_n n x - u x)) μ :=
        MemLp.integrable_mul hdφ_memLp (h_u_diff_memLp n)
      calc
        ∫ x, u_n n x * dφ x ∂μ
            = ∫ x, (u x * dφ x) + dφ x * (u_n n x - u x) ∂μ := by
                congr with x
                ring
        _ = (∫ x, u x * dφ x ∂μ) + ∫ x, dφ x * (u_n n x - u x) ∂μ :=
              integral_add hfi hdi
    have h_aux :
        Tendsto
          (fun n => (∫ x, u x * dφ x ∂μ) + ∫ x, dφ x * (u_n n x - u x) ∂μ)
          atTop (𝓝 ((∫ x, u x * dφ x ∂μ) + 0)) :=
      Tendsto.const_add _ h_u_int_tendsto
    have h_aux' : Tendsto
          (fun n => ∫ x, u_n n x * dφ x ∂μ) atTop
          (𝓝 ((∫ x, u x * dφ x ∂μ) + 0)) := by
      simpa [h_eq] using h_aux
    simpa [μ, add_zero] using h_aux'
  have h_rhs_tendsto :
      Tendsto (fun n => -∫ x in Ω, g_n n x * φ x)
        atTop (𝓝 (-∫ x in Ω, g x * φ x)) := by
    have h_eq : ∀ n,
        ∫ x, g_n n x * φ x ∂μ =
          (∫ x, g x * φ x ∂μ) + ∫ x, φ x * (g_n n x - g x) ∂μ := by
      intro n
      have hgi : Integrable (fun x => g x * φ x) μ := by
        exact (MemLp.integrable_mul hφ_memLp hg_lp).congr <|
          Filter.Eventually.of_forall fun x ↦ by simp only [Pi.mul_apply, mul_comm]
      have hdi : Integrable (fun x => φ x * (g_n n x - g x)) μ :=
        MemLp.integrable_mul hφ_memLp (h_g_diff_memLp n)
      calc
        ∫ x, g_n n x * φ x ∂μ
            = ∫ x, (g x * φ x) + φ x * (g_n n x - g x) ∂μ := by
                congr with x
                ring
        _ = (∫ x, g x * φ x ∂μ) + ∫ x, φ x * (g_n n x - g x) ∂μ :=
              integral_add hgi hdi
    have h_neg :
        Tendsto
          (fun n => -((∫ x, g x * φ x ∂μ) + ∫ x, φ x * (g_n n x - g x) ∂μ))
          atTop (𝓝 (-((∫ x, g x * φ x ∂μ) + 0))) :=
      Tendsto.neg (Tendsto.const_add _ h_g_int_tendsto)
    have h_neg' : Tendsto
        (fun n => -∫ x, g_n n x * φ x ∂μ) atTop
        (𝓝 (-((∫ x, g x * φ x ∂μ) + 0))) := by
      simpa [h_eq] using h_neg
    simpa [μ, add_zero] using h_neg'
  have h_eq_n :
      ∀ n, ∫ x in Ω, u_n n x * dφ x = -∫ x in Ω, g_n n x * φ x := by
    intro n
    exact h_weak n φ hφ hφ_support hφ_sub
  have h_eq_tendsto :
      Tendsto (fun n => ∫ x in Ω, u_n n x * dφ x)
        atTop (𝓝 (-∫ x in Ω, g x * φ x)) := by
    simpa [h_eq_n] using h_rhs_tendsto
  have h_unique := tendsto_nhds_unique h_lhs_tendsto h_eq_tendsto
  change ∫ x in Ω, u x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) =
    -∫ x in Ω, g x * φ x
  simpa [dφ] using h_unique

private theorem memW1p_and_chosenWeakPartial_ae_of_tendsto
    {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {Ω : Set E} (hΩ : IsOpen Ω)
    {u_n : ℕ → E → ℝ} {u : E → ℝ}
    {g : Fin d → E → ℝ}
    (hu_n_w1p : ∀ n, Sobolev.Euclidean.MemW1p p (u_n n) Ω)
    (hu_lp : MemLp u p (volume.restrict Ω))
    (hg_lp : ∀ i, MemLp (g i) p (volume.restrict Ω))
    (h_u_tendsto : Tendsto
      (fun n => eLpNorm (fun x => u_n n x - u x) p (volume.restrict Ω))
      atTop (𝓝 0))
    (h_partial_tendsto : ∀ i, Tendsto
      (fun n => eLpNorm
        (fun x => chosenWeakPartialOrZero p i (u_n n) Ω x - g i x)
        p (volume.restrict Ω))
      atTop (𝓝 0)) :
    Sobolev.Euclidean.MemW1p p u Ω ∧
      ∀ i, chosenWeakPartialOrZero p i u Ω =ᵐ[volume.restrict Ω] g i := by
  classical
  have h_chosen_lp : ∀ n i,
      MemLp (chosenWeakPartialOrZero p i (u_n n) Ω) p (volume.restrict Ω) :=
    fun n i => chosenWeakPartialOrZero_memLp_of_mem (hu_n_w1p n) i
  have hu_n_lp : ∀ n, MemLp (u_n n) p (volume.restrict Ω) :=
    fun n => (hu_n_w1p n).1
  have h_weak_g : ∀ i, Sobolev.Euclidean.HasWeakPartialDeriv i (g i) u Ω := by
    intro i
    refine hasWeakPartialDeriv_of_tendsto_eLpNorm hp_one i
      hu_n_lp (fun n => h_chosen_lp n i) hu_lp (hg_lp i) ?_ h_u_tendsto (h_partial_tendsto i)
    intro n
    exact chosenWeakPartialOrZero_isWeakPartial_of_mem (hu_n_w1p n) i
  have hu_w1p : Sobolev.Euclidean.MemW1p p u Ω := by
    refine ⟨hu_lp, ?_⟩
    intro i
    exact ⟨g i, hg_lp i, h_weak_g i⟩
  refine ⟨hu_w1p, ?_⟩
  intro i
  have h_chosen_weak : Sobolev.Euclidean.HasWeakPartialDeriv i
      (chosenWeakPartialOrZero p i u Ω) u Ω :=
    chosenWeakPartialOrZero_isWeakPartial_of_mem hu_w1p i
  have h_chosen_local : LocallyIntegrable (chosenWeakPartialOrZero p i u Ω)
      (volume.restrict Ω) :=
    (chosenWeakPartialOrZero_memLp_of_mem hu_w1p i).locallyIntegrable hp_one
  have hg_local : LocallyIntegrable (g i) (volume.restrict Ω) :=
    (hg_lp i).locallyIntegrable hp_one
  exact Sobolev.Euclidean.HasWeakPartialDeriv.ae_eq hΩ h_chosen_weak (h_weak_g i) h_chosen_local hg_local

theorem MemWkp_of_iter_tendsto_eLpNorm
    {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {Ω : Set E} (hΩ : IsOpen Ω)
    (k : ℕ)
    {u_n : ℕ → E → ℝ}
    (hu_n_mem : ∀ n, MemWkp (d := d) k p (u_n n) Ω)
    (v : ∀ j : ℕ, (Fin j → Fin d) → E → ℝ)
    (hv_lp : ∀ (j : ℕ) (β : Fin j → Fin d), j ≤ k →
      MemLp (v j β) p (volume.restrict Ω))
    (h_iter_tendsto : ∀ (j : ℕ) (β : Fin j → Fin d), j ≤ k →
      Tendsto
        (fun n => eLpNorm
          (fun x => iterWeakPartial (d := d) p j β (u_n n) Ω x - v j β x)
          p (volume.restrict Ω))
        atTop (𝓝 0)) :
    MemWkp (d := d) k p (v 0 ![]) Ω ∧
      ∀ (j : ℕ) (β : Fin j → Fin d), j ≤ k →
        iterWeakPartial (d := d) p j β (v 0 ![]) Ω =ᵐ[volume.restrict Ω] v j β := by
  classical
  induction k generalizing u_n v with
  | zero =>
      refine ⟨?_, ?_⟩
      · rw [MemWkp_zero]
        have hj0 : (0 : ℕ) ≤ 0 := le_refl _
        exact hv_lp 0 ![] hj0
      · intro j β hj
        interval_cases j
        simp only [iterWeakPartial_zero]
        have hβ : β = ![] := by
          funext i; exact i.elim0
        subst hβ
        rfl
  | succ k ih =>
      have hu_n_w1p : ∀ n, Sobolev.Euclidean.MemW1p p (u_n n) Ω := fun n =>
        (hu_n_mem n).memW1p
      have hu_lp : MemLp (v 0 ![]) p (volume.restrict Ω) :=
        hv_lp 0 ![] (Nat.zero_le _)
      have h_u_tendsto : Tendsto
          (fun n => eLpNorm (fun x => u_n n x - v 0 ![] x) p (volume.restrict Ω))
          atTop (𝓝 0) := by
        have h := h_iter_tendsto 0 ![] (Nat.zero_le _)
        simpa [iterWeakPartial_zero] using h
      let g : Fin d → E → ℝ := fun i => v 1 ![i]
      have hg_lp : ∀ i, MemLp (g i) p (volume.restrict Ω) := by
        intro i
        exact hv_lp 1 ![i] (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero _))
      have h_partial_tendsto : ∀ i, Tendsto
          (fun n => eLpNorm
            (fun x => chosenWeakPartialOrZero p i (u_n n) Ω x - g i x)
            p (volume.restrict Ω))
          atTop (𝓝 0) := by
        intro i
        have h := h_iter_tendsto 1 ![i]
          (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero _))
        have h_iter_eq : ∀ n,
            iterWeakPartial (d := d) p 1 ![i] (u_n n) Ω =
              chosenWeakPartialOrZero p i (u_n n) Ω := by
          intro n
          rw [iterWeakPartial_succ]
          have h0 : (![i] : Fin 1 → Fin d) 0 = i := by simp
          rw [h0]
          simp [iterWeakPartial_zero]
        have h_simp :
            (fun n => eLpNorm
              (fun x => iterWeakPartial (d := d) p 1 ![i] (u_n n) Ω x - g i x) p
              (volume.restrict Ω)) =
            (fun n => eLpNorm
              (fun x => chosenWeakPartialOrZero p i (u_n n) Ω x - g i x) p
              (volume.restrict Ω)) := by
          funext n
          rw [h_iter_eq]
        rw [← h_simp]
        exact h
      obtain ⟨hu_w1p, h_chosen_ae⟩ :=
        memW1p_and_chosenWeakPartial_ae_of_tendsto hp_one hΩ
          hu_n_w1p hu_lp hg_lp h_u_tendsto h_partial_tendsto
      have h_chosen_mem_k :
          ∀ i, MemWkp (d := d) k p (g i) Ω := by
        intro i
        let v_i : ∀ j : ℕ, (Fin j → Fin d) → E → ℝ := fun j β =>
          v (j + 1) (Fin.cons i β)
        have hv_i_lp : ∀ (j : ℕ) (β : Fin j → Fin d), j ≤ k →
            MemLp (v_i j β) p (volume.restrict Ω) := by
          intro j β hj
          exact hv_lp (j + 1) (Fin.cons i β) (Nat.succ_le_succ hj)
        have h_iter_i : ∀ n, MemWkp (d := d) k p
            (chosenWeakPartialOrZero p i (u_n n) Ω) Ω :=
          fun n => (hu_n_mem n).chosenWeakPartial_mem i
        have h_iter_i_tendsto : ∀ (j : ℕ) (β : Fin j → Fin d), j ≤ k →
            Tendsto
              (fun n => eLpNorm
                (fun x => iterWeakPartial (d := d) p j β
                  (chosenWeakPartialOrZero p i (u_n n) Ω) Ω x - v_i j β x)
                p (volume.restrict Ω))
              atTop (𝓝 0) := by
          intro j β hj
          have h_iter_eq : ∀ n,
              iterWeakPartial (d := d) p j β
                  (chosenWeakPartialOrZero p i (u_n n) Ω) Ω =
                iterWeakPartial (d := d) p (j + 1) (Fin.cons i β) (u_n n) Ω := by
            intro n
            rw [iterWeakPartial_succ]
            have h0 : (Fin.cons i β : Fin (j + 1) → Fin d) 0 = i := by
              simp [Fin.cons_zero]
            have htail : (fun j' : Fin j => (Fin.cons i β : Fin (j+1) → Fin d) j'.succ) = β := by
              funext j'
              simp [Fin.cons_succ]
            rw [h0, htail]
          have h := h_iter_tendsto (j + 1) (Fin.cons i β) (Nat.succ_le_succ hj)
          have h_simp :
              (fun n => eLpNorm
                (fun x => iterWeakPartial (d := d) p (j + 1) (Fin.cons i β) (u_n n) Ω x - v_i j β x)
                p (volume.restrict Ω)) =
              (fun n => eLpNorm
                (fun x => iterWeakPartial (d := d) p j β
                    (chosenWeakPartialOrZero p i (u_n n) Ω) Ω x - v_i j β x)
                p (volume.restrict Ω)) := by
            funext n
            rw [h_iter_eq n]
          rw [h_simp] at h
          have h_v_eq : v (j + 1) (Fin.cons i β) = v_i j β := rfl
          simpa [h_v_eq] using h
        obtain ⟨h_g_mem, _⟩ :=
          ih h_iter_i v_i hv_i_lp h_iter_i_tendsto
        have h_cons_eq : Fin.cons i (![] : Fin 0 → Fin d) = ![i] := by
          funext j'
          induction j' using Fin.cases with
          | zero => simp
          | succ i'' => exact i''.elim0
        have h_eq : v_i 0 ![] = v 1 ![i] := by
          change v 1 (Fin.cons i ![]) = v 1 ![i]
          rw [h_cons_eq]
        rw [h_eq] at h_g_mem
        exact h_g_mem
      have hu_memWkp : MemWkp (d := d) (k + 1) p (v 0 ![]) Ω := by
        rw [MemWkp_succ]
        refine ⟨hu_w1p, ?_⟩
        intro i
        have h_ae : chosenWeakPartialOrZero p i (v 0 ![]) Ω =ᵐ[volume.restrict Ω] g i :=
          h_chosen_ae i
        exact (MemWkp_congr_ae (d := d) hp_one hΩ h_ae).mpr (h_chosen_mem_k i)
      refine ⟨hu_memWkp, ?_⟩
      intro j β hj
      cases j with
      | zero =>
          have hβ : β = ![] := by funext i; exact i.elim0
          subst hβ
          simp only [iterWeakPartial_zero]
          rfl
      | succ j =>
          rw [iterWeakPartial_succ]
          have hj' : j ≤ k := Nat.le_of_succ_le_succ hj
          have h_chosen_β_ae :
              chosenWeakPartialOrZero p (β 0) (v 0 ![]) Ω =ᵐ[volume.restrict Ω] g (β 0) :=
            h_chosen_ae (β 0)
          have h_iter_congr :
              iterWeakPartial (d := d) p j (fun i : Fin j => β i.succ)
                  (chosenWeakPartialOrZero p (β 0) (v 0 ![]) Ω) Ω
                =ᵐ[volume.restrict Ω]
              iterWeakPartial (d := d) p j (fun i : Fin j => β i.succ) (g (β 0)) Ω :=
            iterWeakPartial_ae_congr (d := d) hp_one hΩ j _ h_chosen_β_ae
          let v_i : ∀ j' : ℕ, (Fin j' → Fin d) → E → ℝ := fun j' β' =>
            v (j' + 1) (Fin.cons (β 0) β')
          have hv_i_lp : ∀ (j' : ℕ) (β' : Fin j' → Fin d), j' ≤ k →
              MemLp (v_i j' β') p (volume.restrict Ω) := by
            intro j' β' hj'
            exact hv_lp (j' + 1) (Fin.cons (β 0) β') (Nat.succ_le_succ hj')
          have h_iter_i : ∀ n, MemWkp (d := d) k p
              (chosenWeakPartialOrZero p (β 0) (u_n n) Ω) Ω :=
            fun n => (hu_n_mem n).chosenWeakPartial_mem (β 0)
          have h_iter_i_tendsto : ∀ (j' : ℕ) (β' : Fin j' → Fin d), j' ≤ k →
              Tendsto
                (fun n => eLpNorm
                  (fun x => iterWeakPartial (d := d) p j' β'
                    (chosenWeakPartialOrZero p (β 0) (u_n n) Ω) Ω x - v_i j' β' x)
                  p (volume.restrict Ω))
                atTop (𝓝 0) := by
            intro j' β' hj'
            have h_iter_eq : ∀ n,
                iterWeakPartial (d := d) p j' β'
                    (chosenWeakPartialOrZero p (β 0) (u_n n) Ω) Ω =
                  iterWeakPartial (d := d) p (j' + 1)
                    (Fin.cons (β 0) β') (u_n n) Ω := by
              intro n
              rw [iterWeakPartial_succ]
              have h0 : (Fin.cons (β 0) β' : Fin (j' + 1) → Fin d) 0 = β 0 := by
                simp [Fin.cons_zero]
              have htail : (fun j'' : Fin j' =>
                  (Fin.cons (β 0) β' : Fin (j'+1) → Fin d) j''.succ) = β' := by
                funext j''
                simp [Fin.cons_succ]
              rw [h0, htail]
            have h := h_iter_tendsto (j' + 1) (Fin.cons (β 0) β')
              (Nat.succ_le_succ hj')
            have h_simp :
                (fun n => eLpNorm
                  (fun x => iterWeakPartial (d := d) p (j' + 1) (Fin.cons (β 0) β') (u_n n) Ω x
                    - v_i j' β' x)
                  p (volume.restrict Ω)) =
                (fun n => eLpNorm
                  (fun x => iterWeakPartial (d := d) p j' β'
                      (chosenWeakPartialOrZero p (β 0) (u_n n) Ω) Ω x - v_i j' β' x)
                  p (volume.restrict Ω)) := by
              funext n
              rw [h_iter_eq n]
            rw [h_simp] at h
            have h_v_eq : v (j' + 1) (Fin.cons (β 0) β') = v_i j' β' := rfl
            simpa [h_v_eq] using h
          obtain ⟨_, h_iter_ae⟩ :=
            ih h_iter_i v_i hv_i_lp h_iter_i_tendsto
          have h_cons_zero_eq :
              Fin.cons (β 0) (![] : Fin 0 → Fin d) = ![β 0] := by
            funext j''
            induction j'' using Fin.cases with
            | zero => simp
            | succ i'' => exact i''.elim0
          have h_v_i_zero : v_i 0 ![] = g (β 0) := by
            change v 1 (Fin.cons (β 0) ![]) = v 1 ![β 0]
            rw [h_cons_zero_eq]
          have h_iter_i_specialized :=
            h_iter_ae j (fun i' : Fin j => β i'.succ) hj'
          rw [h_v_i_zero] at h_iter_i_specialized
          have h_cons_full_eq :
              Fin.cons (β 0) (fun i' : Fin j => β i'.succ) = β := by
            funext i'
            induction i' using Fin.cases with
            | zero => simp
            | succ i'' => simp
          have h_v_eq2 : v_i j (fun i' : Fin j => β i'.succ) = v (j + 1) β := by
            change v (j + 1) (Fin.cons (β 0) (fun i' : Fin j => β i'.succ)) = v (j + 1) β
            rw [h_cons_full_eq]
          rw [h_v_eq2] at h_iter_i_specialized
          exact h_iter_congr.trans h_iter_i_specialized

end Euclidean
end Sobolev
