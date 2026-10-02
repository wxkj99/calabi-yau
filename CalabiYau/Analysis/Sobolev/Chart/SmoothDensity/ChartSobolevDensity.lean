-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Chart/SmoothDensity/ChartSobolevDensity.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Chart.ChartTransition.Transition
public import CalabiYau.Analysis.Sobolev.Chart.ChartTransition.ChartPullbackSmooth
public import CalabiYau.Analysis.Sobolev.Chart.ChartTransition.TransitionDiffeo
public import CalabiYau.Analysis.Sobolev.Chart.SmoothDensity.Defs
public import CalabiYau.Analysis.Sobolev.Chart.BanachCompleteness.CompletenessLp
public import CalabiYau.Analysis.Sobolev.Euclidean.Density
public import CalabiYau.Analysis.Sobolev.Euclidean.Multiplication.Multiply
public import CalabiYau.Analysis.Sobolev.Euclidean.ChainRule.CompChainRuleK

@[expose] public section

-- Private declarations used in public declarations require the compatibility option below.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace Sobolev

namespace Euclidean

variable {d : ℕ}

local notation "EucD" => EuclideanSpace ℝ (Fin d)

variable [NeZero d]

theorem SmoothDiffeoBoundedAtOrder.wkpNorm_comp_le
    {kmax : ℕ}
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {Ω Ω' : Set EucD} (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω')
    (Φ : SmoothDiffeoBoundedAtOrder d Ω Ω' kmax)
    (k : ℕ) (hk : k ≤ kmax)
    {u : EucD → ℝ} (hu : MemWkp (d := d) k p u Ω')
    (hu_compactSupport : HasCompactSupport u)
    (hu_support : tsupport u ⊆ Ω') :
    iteratedWeakSobolevNorm (d := d) k p (fun x => u (Φ.toFun x)) Ω ≤
      ENNReal.ofReal (Φ.wkpCompositionConstant k p) *
        iteratedWeakSobolevNorm (d := d) k p u Ω' := by
  classical
  set K_const : ℝ := Φ.wkpCompositionConstant k p with hK_def
  have hK_pos : 0 < K_const := by
    have hp_zero : p ≠ 0 := by
      intro hpz; rw [hpz] at hp_one
      exact absurd hp_one (by norm_num)
    have hq_pos : 0 < p.toReal := ENNReal.toReal_pos hp_zero hp_top
    have hjLB_pos : 0 < Φ.jacobianLowerBound := Φ.jacobian_lower_bound_pos
    have hjLB_inv_pos : 0 < 1 / Φ.jacobianLowerBound := by positivity
    have hKchg_pos : 0 < (1 / Φ.jacobianLowerBound) ^ (1 / p.toReal) :=
      Real.rpow_pos_of_pos hjLB_inv_pos _
    rw [hK_def]
    unfold Sobolev.Euclidean.SmoothDiffeoBoundedAtOrder.wkpCompositionConstant
    have h_zero_in : (0 : ℕ) ∈ Finset.range (k + 1) :=
      Finset.mem_range.mpr (Nat.zero_lt_succ _)
    have h_at_zero : (Fintype.card (Fin 0 → Fin d) : ℝ) = 1 := by
      have h_card : Fintype.card (Fin 0 → Fin d) = 1 := by
        rw [Fintype.card_fun]; simp
      exact_mod_cast h_card
    have h_card_pos : 0 < (Finset.range (k + 1)).sum
        (fun j => (Fintype.card (Fin j → Fin d) : ℝ)) := by
      have h_le := Finset.single_le_sum (s := Finset.range (k + 1))
        (f := fun j => (Fintype.card (Fin j → Fin d) : ℝ))
        (fun j _ => by positivity) h_zero_in
      rw [h_at_zero] at h_le
      linarith
    have h_kfact_D_pos : 0 < (k.factorial : ℝ) * Φ.derivBoundMaxOne ^ k := by
      refine mul_pos ?_ ?_
      · exact_mod_cast Nat.factorial_pos k
      · exact pow_pos Φ.derivBoundMaxOne_pos k
    have h_k1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.zero_lt_succ k
    positivity
  have hK_nonneg : 0 ≤ K_const := hK_pos.le
  have h_approx : ∀ n : ℕ, ∃ ψ : EucD → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ Ω' ∧
      iteratedWeakSobolevNorm (d := d) k p (fun x => u x - ψ x) Ω' ≤
        ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)) := by
    intro n
    have h_pos : 0 < (1 : ℝ) / (n + 1 : ℝ) := by positivity
    exact MemWkp.exists_smooth_compactSupport_approx
      (d := d) hΩ' k p hp_one hp_top hu hu_compactSupport hu_support _ h_pos
  let ψ : ℕ → EucD → ℝ := fun n => (h_approx n).choose
  have hψ_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (ψ n) := fun n =>
    (h_approx n).choose_spec.1
  have hψ_compact : ∀ n, HasCompactSupport (ψ n) := fun n =>
    (h_approx n).choose_spec.2.1
  have hψ_support : ∀ n, tsupport (ψ n) ⊆ Ω' := fun n =>
    (h_approx n).choose_spec.2.2.1
  have hψ_close : ∀ n,
      iteratedWeakSobolevNorm (d := d) k p (fun x => u x - ψ n x) Ω' ≤
        ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)) := fun n =>
    (h_approx n).choose_spec.2.2.2
  have hψ_mem : ∀ n, MemWkp (d := d) k p (ψ n) Ω' := fun n =>
    MemWkp_of_smooth_compactSupport (d := d) hΩ' (hψ_smooth n) (hψ_compact n)
      (hψ_support n) hp_one k
  have hψ_comp_mem : ∀ n, MemWkp (d := d) k p (fun x => ψ n (Φ.toFun x)) Ω :=
    fun n => MemWkp.comp_smoothDiffeoBoundedAtOrder
      (d := d) k hk hp_one hp_top hΩ hΩ' Φ (hψ_mem n) (hψ_compact n) (hψ_support n)
  have h_cauchy : ∀ ε > 0, ∃ N : ℕ, ∀ m n, N ≤ m → N ≤ n →
      iteratedWeakSobolevNorm (d := d) k p
        (fun x => (ψ m (Φ.toFun x)) - (ψ n (Φ.toFun x))) Ω ≤
        ENNReal.ofReal ε := by
    intro ε hε
    have hε_K_pos : 0 < ε / (2 * K_const) := by positivity
    obtain ⟨N0, hN0_real⟩ := exists_nat_gt (1 / (ε / (2 * K_const)) - 1)
    have hN1_pos : (0 : ℝ) < (N0 : ℝ) + 1 := by
      have : 0 < 1 / (ε / (2 * K_const)) := by positivity
      linarith
    have hN0_inv : (1 : ℝ) / (N0 + 1 : ℝ) ≤ ε / (2 * K_const) := by
      rw [div_le_iff₀ hN1_pos]
      have h1 : (1 : ℝ) = (ε / (2 * K_const)) * (1 / (ε / (2 * K_const))) := by
        rw [mul_one_div, div_self hε_K_pos.ne']
      rw [h1]
      apply mul_le_mul_of_nonneg_left _ hε_K_pos.le
      linarith
    refine ⟨N0, ?_⟩
    intro m n hm hn
    let δ : EucD → ℝ := fun x => ψ m x - ψ n x
    have hδ_smooth : ContDiff ℝ (⊤ : ℕ∞) δ := (hψ_smooth m).sub (hψ_smooth n)
    have hδ_compact : HasCompactSupport δ := (hψ_compact m).sub (hψ_compact n)
    have hδ_support : tsupport δ ⊆ Ω' := by
      have h_support_sub : Function.support δ ⊆
          Function.support (ψ m) ∪ Function.support (ψ n) := by
        intro x hx
        by_cases hxm : x ∈ Function.support (ψ m)
        · exact Or.inl hxm
        · right
          change ψ n x ≠ 0
          intro hxn
          apply hx
          change ψ m x - ψ n x = 0
          rw [Function.notMem_support.mp hxm, hxn, sub_zero]
      have h_tsupp_sub : tsupport δ ⊆ tsupport (ψ m) ∪ tsupport (ψ n) := by
        unfold tsupport
        refine (closure_mono h_support_sub).trans ?_
        rw [closure_union]
      exact h_tsupp_sub.trans (Set.union_subset (hψ_support m) (hψ_support n))
    have hS1 := Φ.wkpNorm_comp_smooth_le hp_one hp_top hΩ hΩ'
      k hk hδ_smooth hδ_compact hδ_support
    have h_uψn_mem : MemWkp (d := d) k p (fun x => u x - ψ n x) Ω' :=
      MemWkp.sub (d := d) hp_one hΩ' hu (hψ_mem n)
    have h_uψm_mem : MemWkp (d := d) k p (fun x => u x - ψ m x) Ω' :=
      MemWkp.sub (d := d) hp_one hΩ' hu (hψ_mem m)
    have h_δ_alg : δ = (fun x => (u x - ψ n x) - (u x - ψ m x)) := by
      funext x
      change ψ m x - ψ n x = u x - ψ n x - (u x - ψ m x)
      ring
    have h_δ_wkp_le :
        iteratedWeakSobolevNorm (d := d) k p δ Ω' ≤
          iteratedWeakSobolevNorm (d := d) k p (fun x => u x - ψ n x) Ω' +
            iteratedWeakSobolevNorm (d := d) k p (fun x => u x - ψ m x) Ω' := by
      rw [h_δ_alg]
      have hneg : MemWkp (d := d) k p (fun x => -(u x - ψ m x)) Ω' :=
        MemWkp.neg (d := d) hp_one hΩ' h_uψm_mem
      have h_eq :
          (fun x => u x - ψ n x - (u x - ψ m x)) =
            (fun x => (u x - ψ n x) + (-(u x - ψ m x))) := by
        funext x; ring
      rw [h_eq]
      have h_add := wkpNorm_add_le (d := d) hp_one hΩ' h_uψn_mem hneg
      refine h_add.trans ?_
      have h_neg_eq :
          iteratedWeakSobolevNorm (d := d) k p (fun x => -(u x - ψ m x)) Ω' =
            iteratedWeakSobolevNorm (d := d) k p (fun x => u x - ψ m x) Ω' := by
        have h_eq_smul : (fun x => -(u x - ψ m x)) =
            (fun x => (-1 : ℝ) * (u x - ψ m x)) := by funext x; ring
        rw [h_eq_smul, wkpNorm_const_smul (d := d) hp_one hΩ' h_uψm_mem (-1)]
        simp
      rw [h_neg_eq]
    have hψm_close := hψ_close m
    have hψn_close := hψ_close n
    have h_n_le : ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)) ≤
        ENNReal.ofReal ((1 : ℝ) / (N0 + 1 : ℝ)) := by
      refine ENNReal.ofReal_le_ofReal ?_
      apply div_le_div_of_nonneg_left zero_le_one hN1_pos
      have hN0n : (N0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have h_m_le : ENNReal.ofReal ((1 : ℝ) / (m + 1 : ℝ)) ≤
        ENNReal.ofReal ((1 : ℝ) / (N0 + 1 : ℝ)) := by
      refine ENNReal.ofReal_le_ofReal ?_
      apply div_le_div_of_nonneg_left zero_le_one hN1_pos
      have hN0m : (N0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    have h_δ_le_2N0 :
        iteratedWeakSobolevNorm (d := d) k p δ Ω' ≤
          ENNReal.ofReal (2 * ((1 : ℝ) / (N0 + 1 : ℝ))) := by
      refine h_δ_wkp_le.trans ?_
      refine (add_le_add hψn_close hψm_close).trans ?_
      refine (add_le_add h_n_le h_m_le).trans ?_
      have h2 : (2 * ((1 : ℝ) / (N0 + 1 : ℝ))) =
          ((1 : ℝ) / (N0 + 1 : ℝ)) + ((1 : ℝ) / (N0 + 1 : ℝ)) := by ring
      rw [h2]
      have h_pos : 0 ≤ (1 : ℝ) / (N0 + 1 : ℝ) := by positivity
      rw [ENNReal.ofReal_add h_pos h_pos]
    have h_δcomp_eq : (fun x => δ (Φ.toFun x)) =
        (fun x => ψ m (Φ.toFun x) - ψ n (Φ.toFun x)) := by
      funext x; rfl
    rw [h_δcomp_eq] at hS1
    refine hS1.trans ?_
    refine (mul_le_mul_of_nonneg_left h_δ_le_2N0 (zero_le)).trans ?_
    rw [← ENNReal.ofReal_mul hK_nonneg]
    refine ENNReal.ofReal_le_ofReal ?_
    calc K_const * (2 * ((1 : ℝ) / (N0 + 1 : ℝ)))
        = (2 * K_const) * ((1 : ℝ) / (N0 + 1 : ℝ)) := by ring
      _ ≤ (2 * K_const) * (ε / (2 * K_const)) := by
            apply mul_le_mul_of_nonneg_left hN0_inv
            positivity
      _ = ε := by
            have h_pos : 0 < 2 * K_const := by positivity
            field_simp
  obtain ⟨vΦ, hvΦ_mem, hvΦ_tendsto⟩ :=
    MemWkp.exists_limit_of_wkpNorm_cauchy (d := d) hΩ k p hp_one
      hψ_comp_mem h_cauchy
  have h_Lp_close : ∀ n,
      eLpNorm (fun x => u (Φ.toFun x) - ψ n (Φ.toFun x)) p
        (volume.restrict Ω) ≤
        ENNReal.ofReal
            ((1 / Φ.jacobianLowerBound) ^ (1 / p.toReal)) *
          ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)) := by
    intro n
    have h_chg := Φ.eLpNorm_comp_toFun_le_const hp_one hp_top hΩ
      (fun x => u x - ψ n x)
    have h_uψn_mem : MemWkp (d := d) k p (fun x => u x - ψ n x) Ω' :=
      MemWkp.sub (d := d) hp_one hΩ' hu (hψ_mem n)
    have h_eLp_le_wkp :
        eLpNorm (fun x => u x - ψ n x) p (volume.restrict Ω') ≤
          iteratedWeakSobolevNorm (d := d) k p (fun x => u x - ψ n x) Ω' := by
      have h_zero_le :
          eLpNorm (fun x => u x - ψ n x) p (volume.restrict Ω') =
            iteratedWeakSobolevNorm (d := d) 0 p (fun x => u x - ψ n x) Ω' := by
        rw [wkpNorm_zero]
      rw [h_zero_le]
      unfold iteratedWeakSobolevNorm
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro j hj
        rw [Finset.mem_range] at hj ⊢; omega
      · intros _ _ _; exact zero_le
    have h_arg_eq : (fun x => u (Φ.toFun x) - ψ n (Φ.toFun x)) =
        (fun x => (fun y => u y - ψ n y) (Φ.toFun x)) := by funext x; rfl
    rw [h_arg_eq]
    refine h_chg.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (zero_le)
    exact h_eLp_le_wkp.trans (hψ_close n)
  have h_uΦ_aestrong :
      AEStronglyMeasurable (fun x => u (Φ.toFun x)) (volume.restrict Ω) := by
    have hu_aestrong : AEStronglyMeasurable u (volume.restrict Ω') :=
      hu.memLp.aestronglyMeasurable
    exact hu_aestrong.comp_quasiMeasurePreserving Φ.toFun_quasiMeasurePreserving
  have h_vΦ_eq_uΦ : vΦ =ᵐ[volume.restrict Ω] (fun x => u (Φ.toFun x)) := by
    have h_v_aestrong : AEStronglyMeasurable vΦ (volume.restrict Ω) :=
      hvΦ_mem.memLp.aestronglyMeasurable
    have hp_zero_ne : p ≠ 0 := by
      intro hpz; rw [hpz] at hp_one
      exact absurd hp_one (by norm_num)
    have h_zero :
        eLpNorm (fun x => vΦ x - u (Φ.toFun x)) p (volume.restrict Ω) = 0 := by
      have h_bound : ∀ n,
          eLpNorm (fun x => vΦ x - u (Φ.toFun x)) p (volume.restrict Ω) ≤
            iteratedWeakSobolevNorm (d := d) k p (fun x => vΦ x - ψ n (Φ.toFun x)) Ω +
            ENNReal.ofReal
                ((1 / Φ.jacobianLowerBound) ^ (1 / p.toReal)) *
              ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)) := by
        intro n
        have h_ψn_comp_aestrong : AEStronglyMeasurable
            (fun x => ψ n (Φ.toFun x)) (volume.restrict Ω) :=
          (hψ_smooth n).continuous.aestronglyMeasurable.comp_quasiMeasurePreserving
            Φ.toFun_quasiMeasurePreserving
        have h_decomp :
            (fun x => vΦ x - u (Φ.toFun x)) = (fun x =>
              (vΦ x - ψ n (Φ.toFun x)) + (ψ n (Φ.toFun x) - u (Φ.toFun x))) := by
          funext x; ring
        rw [h_decomp]
        have h_tri := eLpNorm_add_le (μ := volume.restrict Ω)
          (h_v_aestrong.sub h_ψn_comp_aestrong)
          (h_ψn_comp_aestrong.sub h_uΦ_aestrong) hp_one
        refine h_tri.trans ?_
        have h_first :
            eLpNorm (fun x => vΦ x - ψ n (Φ.toFun x)) p (volume.restrict Ω) ≤
              iteratedWeakSobolevNorm (d := d) k p (fun x => vΦ x - ψ n (Φ.toFun x)) Ω := by
          rw [show eLpNorm (fun x => vΦ x - ψ n (Φ.toFun x)) p (volume.restrict Ω) =
            iteratedWeakSobolevNorm (d := d) 0 p (fun x => vΦ x - ψ n (Φ.toFun x)) Ω from
            (wkpNorm_zero p _ _).symm]
          unfold iteratedWeakSobolevNorm
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro j hj; rw [Finset.mem_range] at hj ⊢; omega
          · intros _ _ _; exact zero_le
        have h_second :
            eLpNorm (fun x => ψ n (Φ.toFun x) - u (Φ.toFun x)) p
                (volume.restrict Ω) ≤
              ENNReal.ofReal
                  ((1 / Φ.jacobianLowerBound) ^ (1 / p.toReal)) *
                ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)) := by
          have h_eq :
              (fun x => ψ n (Φ.toFun x) - u (Φ.toFun x)) =
                (fun x => -(u (Φ.toFun x) - ψ n (Φ.toFun x))) := by
            funext x; ring
          rw [h_eq]
          have h_neg :
              eLpNorm (fun x => -(u (Φ.toFun x) - ψ n (Φ.toFun x))) p
                  (volume.restrict Ω) =
                eLpNorm (fun x => u (Φ.toFun x) - ψ n (Φ.toFun x)) p
                  (volume.restrict Ω) := by
            rw [show (fun x => -(u (Φ.toFun x) - ψ n (Φ.toFun x))) =
                fun x => -1 * (u (Φ.toFun x) - ψ n (Φ.toFun x)) from by
              funext x; ring]
            rw [show (fun x => -1 * (u (Φ.toFun x) - ψ n (Φ.toFun x))) =
                ((-1 : ℝ) • fun x => u (Φ.toFun x) - ψ n (Φ.toFun x)) from by
              funext x; simp [Pi.smul_apply, smul_eq_mul]]
            rw [eLpNorm_const_smul]
            simp
          rw [h_neg]
          exact h_Lp_close n
        exact add_le_add h_first h_second
      apply le_antisymm _ (zero_le)
      have h_tendsto_first :
          Filter.Tendsto
            (fun n => iteratedWeakSobolevNorm (d := d) k p (fun x => vΦ x - ψ n (Φ.toFun x)) Ω)
            atTop (𝓝 0) := by
        have h_eq : ∀ n, (fun x => vΦ x - ψ n (Φ.toFun x)) =
            (fun x => -(ψ n (Φ.toFun x) - vΦ x)) := by
          intro n; funext x; ring
        have h_norm_eq : ∀ n,
            iteratedWeakSobolevNorm (d := d) k p (fun x => vΦ x - ψ n (Φ.toFun x)) Ω =
              iteratedWeakSobolevNorm (d := d) k p (fun x => ψ n (Φ.toFun x) - vΦ x) Ω := by
          intro n
          rw [h_eq n]
          have hf_mem : MemWkp (d := d) k p
              (fun x => ψ n (Φ.toFun x) - vΦ x) Ω :=
            MemWkp.sub (d := d) hp_one hΩ (hψ_comp_mem n) hvΦ_mem
          rw [show (fun x => -(ψ n (Φ.toFun x) - vΦ x)) =
              (fun x => (-1 : ℝ) * (ψ n (Φ.toFun x) - vΦ x)) from by
            funext x; ring]
          rw [wkpNorm_const_smul (d := d) hp_one hΩ hf_mem (-1)]
          simp
        rw [show (fun n => iteratedWeakSobolevNorm (d := d) k p
              (fun x => vΦ x - ψ n (Φ.toFun x)) Ω) =
            (fun n => iteratedWeakSobolevNorm (d := d) k p
              (fun x => ψ n (Φ.toFun x) - vΦ x) Ω) from funext h_norm_eq]
        exact hvΦ_tendsto
      have h_tendsto_second :
          Filter.Tendsto
            (fun n : ℕ => ENNReal.ofReal
                ((1 / Φ.jacobianLowerBound) ^ (1 / p.toReal)) *
              ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)))
            atTop (𝓝 0) := by
        have h_inner_tendsto :
            Filter.Tendsto
              (fun n : ℕ => ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)))
              atTop (𝓝 0) := by
          have h_real : Filter.Tendsto
              (fun n : ℕ => (1 : ℝ) / (n + 1 : ℝ)) atTop (𝓝 0) :=
            tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
          have h_ofReal := (ENNReal.continuous_ofReal.tendsto 0).comp h_real
          rw [ENNReal.ofReal_zero] at h_ofReal
          exact h_ofReal
        set C : ℝ≥0∞ := ENNReal.ofReal
            ((1 / Φ.jacobianLowerBound) ^ (1 / p.toReal)) with hC_def
        have hC_ne_top : C ≠ ⊤ := by rw [hC_def]; exact ENNReal.ofReal_ne_top
        have h_const_mul := ENNReal.Tendsto.const_mul (a := C) (b := 0)
          h_inner_tendsto (Or.inr hC_ne_top)
        simpa using h_const_mul
      have h_tendsto_sum :
          Filter.Tendsto
            (fun n => iteratedWeakSobolevNorm (d := d) k p (fun x => vΦ x - ψ n (Φ.toFun x)) Ω +
              ENNReal.ofReal
                  ((1 / Φ.jacobianLowerBound) ^ (1 / p.toReal)) *
                ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)))
            atTop (𝓝 0) := by
        have := h_tendsto_first.add h_tendsto_second
        simpa using this
      exact ge_of_tendsto h_tendsto_sum (Filter.Eventually.of_forall h_bound)
    have h_diff_zero : (fun x => vΦ x - u (Φ.toFun x)) =ᵐ[volume.restrict Ω]
        0 := by
      have h_aestrong := h_v_aestrong.sub h_uΦ_aestrong
      exact (eLpNorm_eq_zero_iff h_aestrong hp_zero_ne).mp h_zero
    filter_upwards [h_diff_zero] with x hx
    have : vΦ x - u (Φ.toFun x) = 0 := hx
    linarith
  have h_uΦ_eq_vΦ : (fun x => u (Φ.toFun x)) =ᵐ[volume.restrict Ω] vΦ :=
    h_vΦ_eq_uΦ.symm
  have h_norm_eq :
      iteratedWeakSobolevNorm (d := d) k p (fun x => u (Φ.toFun x)) Ω =
        iteratedWeakSobolevNorm (d := d) k p vΦ Ω :=
    wkpNorm_congr_ae (d := d) hp_one hΩ h_uΦ_eq_vΦ
  rw [h_norm_eq]
  set RHS : ℝ≥0∞ := ENNReal.ofReal K_const * iteratedWeakSobolevNorm (d := d) k p u Ω' with hRHS_def
  have h_bound2 : ∀ n,
      iteratedWeakSobolevNorm (d := d) k p vΦ Ω ≤
        iteratedWeakSobolevNorm (d := d) k p (fun x => vΦ x - ψ n (Φ.toFun x)) Ω +
        ENNReal.ofReal K_const * ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)) +
        RHS := by
    intro n
    have h_decomp : (fun x => vΦ x) =
        (fun x => (vΦ x - ψ n (Φ.toFun x)) + ψ n (Φ.toFun x)) := by
      funext x; ring
    have h_ψcomp_mem : MemWkp (d := d) k p (fun x => ψ n (Φ.toFun x)) Ω :=
      hψ_comp_mem n
    have h_diff_mem : MemWkp (d := d) k p (fun x => vΦ x - ψ n (Φ.toFun x)) Ω :=
      MemWkp.sub (d := d) hp_one hΩ hvΦ_mem h_ψcomp_mem
    have h_fun_eq : vΦ = fun x => (vΦ x - ψ n (Φ.toFun x)) + ψ n (Φ.toFun x) := by
      funext x; ring
    conv_lhs => rw [h_fun_eq]
    have h_tri := wkpNorm_add_le (d := d) hp_one hΩ h_diff_mem h_ψcomp_mem
    refine h_tri.trans ?_
    have h_smooth_bound := Φ.wkpNorm_comp_smooth_le hp_one hp_top hΩ hΩ' k hk
      (hψ_smooth n) (hψ_compact n) (hψ_support n)
    have h_ψn_le_u : iteratedWeakSobolevNorm (d := d) k p (ψ n) Ω' ≤
        iteratedWeakSobolevNorm (d := d) k p u Ω' + ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)) := by
      have h_neg_uψn_mem : MemWkp (d := d) k p (fun x => ψ n x - u x) Ω' := by
        have h_uψn_mem : MemWkp (d := d) k p (fun x => u x - ψ n x) Ω' :=
          MemWkp.sub (d := d) hp_one hΩ' hu (hψ_mem n)
        have h_neg : MemWkp (d := d) k p (fun x => -(u x - ψ n x)) Ω' :=
          MemWkp.neg (d := d) hp_one hΩ' h_uψn_mem
        have h_eq : (fun x => -(u x - ψ n x)) = (fun x => ψ n x - u x) := by
          funext x; ring
        rw [h_eq] at h_neg; exact h_neg
      have h_eq_norm' : iteratedWeakSobolevNorm (d := d) k p (ψ n) Ω' =
          iteratedWeakSobolevNorm (d := d) k p (fun x => u x + (ψ n x - u x)) Ω' := by
        congr 1
        funext x; ring
      rw [h_eq_norm']
      have h_tri' := wkpNorm_add_le (d := d) hp_one hΩ' hu h_neg_uψn_mem
      refine h_tri'.trans ?_
      have h_diff_norm_eq :
          iteratedWeakSobolevNorm (d := d) k p (fun x => ψ n x - u x) Ω' =
            iteratedWeakSobolevNorm (d := d) k p (fun x => u x - ψ n x) Ω' := by
        have h_uψn_mem : MemWkp (d := d) k p (fun x => u x - ψ n x) Ω' :=
          MemWkp.sub (d := d) hp_one hΩ' hu (hψ_mem n)
        have h_eq : (fun x => ψ n x - u x) =
            (fun x => (-1 : ℝ) * (u x - ψ n x)) := by funext x; ring
        rw [h_eq, wkpNorm_const_smul (d := d) hp_one hΩ' h_uψn_mem (-1)]
        simp
      rw [h_diff_norm_eq]
      exact add_le_add (le_refl _) (hψ_close n)
    have h_bound_ψn :
        iteratedWeakSobolevNorm (d := d) k p (fun x => ψ n (Φ.toFun x)) Ω ≤
          ENNReal.ofReal K_const *
            (iteratedWeakSobolevNorm (d := d) k p u Ω' + ENNReal.ofReal
              ((1 : ℝ) / (n + 1 : ℝ))) := by
      refine h_smooth_bound.trans ?_
      exact mul_le_mul_of_nonneg_left h_ψn_le_u (zero_le)
    refine le_trans (add_le_add (le_refl _) h_bound_ψn) ?_
    rw [mul_add]
    have h_eq_RHS : ENNReal.ofReal K_const * iteratedWeakSobolevNorm (d := d) k p u Ω' = RHS := rfl
    rw [h_eq_RHS]
    have h_rearr :
        iteratedWeakSobolevNorm (d := d) k p (fun x => vΦ x - ψ n (Φ.toFun x)) Ω +
            (RHS + ENNReal.ofReal K_const * ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ))) =
          iteratedWeakSobolevNorm (d := d) k p (fun x => vΦ x - ψ n (Φ.toFun x)) Ω +
            ENNReal.ofReal K_const * ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)) +
            RHS := by ring
    rw [h_rearr]
  have h_tendsto_first :
      Filter.Tendsto
        (fun n => iteratedWeakSobolevNorm (d := d) k p (fun x => vΦ x - ψ n (Φ.toFun x)) Ω)
        atTop (𝓝 0) := by
    have h_eq : ∀ n, (fun x => vΦ x - ψ n (Φ.toFun x)) =
        (fun x => -(ψ n (Φ.toFun x) - vΦ x)) := by
      intro n; funext x; ring
    have h_norm_eq2 : ∀ n,
        iteratedWeakSobolevNorm (d := d) k p (fun x => vΦ x - ψ n (Φ.toFun x)) Ω =
          iteratedWeakSobolevNorm (d := d) k p (fun x => ψ n (Φ.toFun x) - vΦ x) Ω := by
      intro n
      rw [h_eq n]
      have hf_mem : MemWkp (d := d) k p
          (fun x => ψ n (Φ.toFun x) - vΦ x) Ω :=
        MemWkp.sub (d := d) hp_one hΩ (hψ_comp_mem n) hvΦ_mem
      rw [show (fun x => -(ψ n (Φ.toFun x) - vΦ x)) =
          (fun x => (-1 : ℝ) * (ψ n (Φ.toFun x) - vΦ x)) from by
        funext x; ring]
      rw [wkpNorm_const_smul (d := d) hp_one hΩ hf_mem (-1)]
      simp
    rw [show (fun n => iteratedWeakSobolevNorm (d := d) k p
          (fun x => vΦ x - ψ n (Φ.toFun x)) Ω) =
        (fun n => iteratedWeakSobolevNorm (d := d) k p
          (fun x => ψ n (Φ.toFun x) - vΦ x) Ω) from funext h_norm_eq2]
    exact hvΦ_tendsto
  have h_tendsto_second :
      Filter.Tendsto
        (fun n : ℕ => ENNReal.ofReal K_const *
          ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)))
        atTop (𝓝 0) := by
    have h_inner_tendsto :
        Filter.Tendsto
          (fun n : ℕ => ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)))
          atTop (𝓝 0) := by
      have h_real : Filter.Tendsto
          (fun n : ℕ => (1 : ℝ) / (n + 1 : ℝ)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      have h_ofReal := (ENNReal.continuous_ofReal.tendsto 0).comp h_real
      rw [ENNReal.ofReal_zero] at h_ofReal
      exact h_ofReal
    set C : ℝ≥0∞ := ENNReal.ofReal K_const with hC_def
    have hC_ne_top : C ≠ ⊤ := by rw [hC_def]; exact ENNReal.ofReal_ne_top
    have h_const_mul := ENNReal.Tendsto.const_mul (a := C) (b := 0)
      h_inner_tendsto (Or.inr hC_ne_top)
    simpa using h_const_mul
  have h_tendsto_zero :
      Filter.Tendsto
        (fun n =>
          iteratedWeakSobolevNorm (d := d) k p (fun x => vΦ x - ψ n (Φ.toFun x)) Ω +
          ENNReal.ofReal K_const * ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ)))
        atTop (𝓝 0) := by
    have := h_tendsto_first.add h_tendsto_second
    simpa using this
  have h_tendsto_rhs :
      Filter.Tendsto
        (fun n =>
          (iteratedWeakSobolevNorm (d := d) k p (fun x => vΦ x - ψ n (Φ.toFun x)) Ω +
           ENNReal.ofReal K_const * ENNReal.ofReal ((1 : ℝ) / (n + 1 : ℝ))) +
          RHS)
        atTop (𝓝 (0 + RHS)) :=
    h_tendsto_zero.add tendsto_const_nhds
  rw [zero_add] at h_tendsto_rhs
  exact ge_of_tendsto h_tendsto_rhs (Filter.Eventually.of_forall h_bound2)

end Euclidean

namespace Chart

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [IsManifold I ∞ M] in
private lemma chartPushed_chartPullback_apply_of_mem
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M)
    (ψ : EuclN → ℝ) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushed (I := I) (M := M) ρ α (chartPullback I α ψ) y =
      (ρ α : C^∞⟮I, M; ℝ⟯) ((extChartAt I α).symm (toEuclidean.symm y)) * ψ y := by
  classical
  unfold chartPushed
  set z : M := (extChartAt I α).symm (toEuclidean.symm y) with hz_def
  have hsymm_target : toEuclidean.symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have hz_source : z ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hsymm_target
  have hz_chartAt_source : z ∈ (chartAt H α).source := by
    rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
      (I := I) (M := M)] at hz_source
    exact hz_source
  rw [chartPullback_apply_of_mem (I := I) (M := M) α ψ hz_chartAt_source]
  have hz_inv : (extChartAt I α) z = toEuclidean.symm y :=
    (extChartAt I α).right_inv hsymm_target
  rw [hz_inv, toEuclidean.apply_symm_apply]

private lemma chartPushed_chartPullback_self
    [T2Space M] [SigmaCompactSpace M]
    (α : M) (χ : EuclN → ℝ) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α
        (chartPullback I α χ) y =
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) ((extChartAt I α).symm (toEuclidean.symm y)) *
      χ y :=
  chartPushed_chartPullback_apply_of_mem (I := I) (M := M)
    (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α χ hy

end Chart
end Sobolev
