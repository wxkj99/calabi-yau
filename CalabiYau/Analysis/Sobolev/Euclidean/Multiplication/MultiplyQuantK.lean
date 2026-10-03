-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Euclidean/Multiplication/MultiplyQuantK.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuant

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Sobolev
namespace Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

private lemma sum_fin_succ_to_iterWeakPartial_succ
    (j : ℕ) (q : ℝ≥0∞) (u : E → ℝ) (Ω : Set E) :
    ∑ α : Fin (j + 1) → Fin d,
        eLpNorm (iterWeakPartial (d := d) q (j + 1) α u Ω) q (volume.restrict Ω) =
      ∑ i : Fin d, ∑ α' : Fin j → Fin d,
        eLpNorm
          (iterWeakPartial (d := d) q j α'
            (chosenWeakPartialOrZero (d := d) q i u Ω) Ω) q (volume.restrict Ω) := by
  classical
  rw [← Fintype.sum_equiv
        (Fin.consEquiv (fun _ : Fin (j + 1) => Fin d))
        (fun (pr : Fin d × (Fin j → Fin d)) =>
          eLpNorm (iterWeakPartial (d := d) q (j + 1)
            (Fin.cons pr.1 pr.2 : Fin (j + 1) → Fin d) u Ω) q (volume.restrict Ω))
        (fun α : Fin (j + 1) → Fin d =>
          eLpNorm (iterWeakPartial (d := d) q (j + 1) α u Ω) q (volume.restrict Ω))
        (fun pr => by simp [Fin.consEquiv])]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun α' _ => ?_))
  rw [iterWeakPartial_succ]
  have h_first : (Fin.cons i α' : Fin (j + 1) → Fin d) 0 = i := Fin.cons_zero _ _
  have h_tail :
      (fun (k : Fin j) => (Fin.cons i α' : Fin (j + 1) → Fin d) k.succ) = α' := by
    funext k
    exact Fin.cons_succ _ _ _
  rw [h_first, h_tail]

theorem wkpNorm_succ_eq_eLpNorm_add_sum_partial
    (k : ℕ) (p : ℝ≥0∞) (Ω : Set E) (u : E → ℝ) :
    iteratedWeakSobolevNorm (d := d) (k + 1) p u Ω =
      eLpNorm u p (volume.restrict Ω) +
      ∑ i : Fin d,
        iteratedWeakSobolevNorm (d := d) k p (chosenWeakPartialOrZero (d := d) p i u Ω) Ω := by
  classical
  unfold iteratedWeakSobolevNorm
  have h_split :
      ∑ j ∈ Finset.range (k + 2),
        ∑ α : Fin j → Fin d,
          eLpNorm (iterWeakPartial (d := d) p j α u Ω) p (volume.restrict Ω) =
      (∑ α : Fin 0 → Fin d,
          eLpNorm (iterWeakPartial (d := d) p 0 α u Ω) p (volume.restrict Ω)) +
      ∑ j' ∈ Finset.range (k + 1),
        ∑ α : Fin (j' + 1) → Fin d,
          eLpNorm (iterWeakPartial (d := d) p (j' + 1) α u Ω) p
            (volume.restrict Ω) := by
    have h_image : Finset.range (k + 2) =
        insert 0 ((Finset.range (k + 1)).image (· + 1)) := by
      ext j; rcases Nat.eq_zero_or_pos j with hj | hj
      · rw [hj]; simp
      · rw [Finset.mem_insert, Finset.mem_range, Finset.mem_image]
        constructor
        · intro h_in
          right
          refine ⟨j - 1, ?_, ?_⟩
          · rw [Finset.mem_range]; omega
          · omega
        · rintro (h0 | ⟨j', hj'_mem, hj'_eq⟩)
          · omega
          · rw [Finset.mem_range] at hj'_mem; omega
    have h_zero_not_in : 0 ∉ (Finset.range (k + 1)).image (· + 1) := by
      simp [Finset.mem_image, Finset.mem_range]
    rw [h_image]
    rw [Finset.sum_insert h_zero_not_in]
    rw [Finset.sum_image (fun j _ j' _ h => by omega)]
  rw [h_split]
  have h_zero_term :
      (∑ α : Fin 0 → Fin d,
        eLpNorm (iterWeakPartial (d := d) p 0 α u Ω) p (volume.restrict Ω)) =
        eLpNorm u p (volume.restrict Ω) := by
    have hUniq : ∀ α : Fin 0 → Fin d, α = (fun i : Fin 0 => i.elim0) := fun α => by
      funext i; exact i.elim0
    have : Unique (Fin 0 → Fin d) :=
      { default := fun i : Fin 0 => i.elim0
        uniq := fun α => (hUniq α).symm ▸ rfl }
    rw [Fintype.sum_unique
          (f := fun α : Fin 0 → Fin d =>
            eLpNorm (iterWeakPartial (d := d) p 0 α u Ω) p (volume.restrict Ω))]
    simp [iterWeakPartial_zero]
  rw [h_zero_term]
  have h_inner_swap :
      ∑ j' ∈ Finset.range (k + 1),
        ∑ α : Fin (j' + 1) → Fin d,
          eLpNorm (iterWeakPartial (d := d) p (j' + 1) α u Ω) p
            (volume.restrict Ω) =
      ∑ i : Fin d,
        ∑ j' ∈ Finset.range (k + 1),
          ∑ α' : Fin j' → Fin d,
            eLpNorm
              (iterWeakPartial (d := d) p j' α'
                (chosenWeakPartialOrZero (d := d) p i u Ω) Ω) p
              (volume.restrict Ω) := by
    have h_rewrite : ∀ j' ∈ Finset.range (k + 1),
        (∑ α : Fin (j' + 1) → Fin d,
          eLpNorm (iterWeakPartial (d := d) p (j' + 1) α u Ω) p
            (volume.restrict Ω)) =
        (∑ i : Fin d, ∑ α' : Fin j' → Fin d,
          eLpNorm
            (iterWeakPartial (d := d) p j' α'
              (chosenWeakPartialOrZero (d := d) p i u Ω) Ω) p
            (volume.restrict Ω)) :=
      fun j' _ => sum_fin_succ_to_iterWeakPartial_succ (d := d) j' p u Ω
    rw [Finset.sum_congr rfl h_rewrite]
    rw [Finset.sum_comm]
  rw [h_inner_swap]

lemma wkpNorm_chosenWeakPartial_le_wkpNorm_succ
    (k : ℕ) {p : ℝ≥0∞} {Ω : Set E} (u : E → ℝ) (i : Fin d) :
    iteratedWeakSobolevNorm (d := d) k p (chosenWeakPartialOrZero (d := d) p i u Ω) Ω ≤
      iteratedWeakSobolevNorm (d := d) (k + 1) p u Ω := by
  classical
  rw [wkpNorm_succ_eq_eLpNorm_add_sum_partial (d := d) k p Ω u]
  have h_one_term :
      iteratedWeakSobolevNorm (d := d) k p (chosenWeakPartialOrZero (d := d) p i u Ω) Ω ≤
        ∑ i' : Fin d,
          iteratedWeakSobolevNorm (d := d) k p (chosenWeakPartialOrZero (d := d) p i' u Ω) Ω := by
    refine Finset.single_le_sum (f := fun i' : Fin d =>
        iteratedWeakSobolevNorm (d := d) k p (chosenWeakPartialOrZero (d := d) p i' u Ω) Ω)
      (fun _ _ => bot_le) (Finset.mem_univ i)
  have h_left_le : (∑ i' : Fin d,
      iteratedWeakSobolevNorm (d := d) k p (chosenWeakPartialOrZero (d := d) p i' u Ω) Ω) ≤
      eLpNorm u p (volume.restrict Ω) +
      ∑ i' : Fin d,
        iteratedWeakSobolevNorm (d := d) k p (chosenWeakPartialOrZero (d := d) p i' u Ω) Ω := by
    exact le_add_self
  exact h_one_term.trans h_left_le

section LeibnizQuant

variable [NeZero d]

theorem wkpNorm_smul_smooth_bounded_le
    (k : ℕ) {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {Ω : Set E} (hΩ_open : IsOpen Ω)
    {η : E → ℝ}
    (hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η)
    {C : ℝ} (hC_nonneg : 0 ≤ C)
    (hη_bound : ∀ j ≤ k, ∀ x ∈ Ω, ‖iteratedFDeriv ℝ j η x‖ ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ {u : E → ℝ}, MemWkp (d := d) k p u Ω →
      iteratedWeakSobolevNorm (d := d) k p (fun x => η x * u x) Ω ≤
        ENNReal.ofReal K * iteratedWeakSobolevNorm (d := d) k p u Ω := by
  classical
  induction k generalizing η with
  | zero =>
      exact wkpNorm_smul_smooth_bounded_le_one (k := 0) (Nat.zero_le _)
        hp_one hΩ_open hη_smooth hC_nonneg hη_bound
  | succ k ih =>
      have hη_bound_k : ∀ j ≤ k, ∀ x ∈ Ω, ‖iteratedFDeriv ℝ j η x‖ ≤ C :=
        fun j hj x hx => hη_bound j (hj.trans (Nat.le_succ _)) x hx
      obtain ⟨K_eta, hK_eta_pos, hK_eta_bound⟩ :=
        ih hη_smooth hη_bound_k
      have h_partial_eta_smooth : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞)
          (fun x : E => (fderiv ℝ η x) (EuclideanSpace.single i 1)) := fun i =>
        contDiff_partial_eta (d := d) hη_smooth i
      have h_partial_eta_bound : ∀ i : Fin d, ∀ j ≤ k, ∀ x ∈ Ω,
          ‖iteratedFDeriv ℝ j
            (fun x : E => (fderiv ℝ η x) (EuclideanSpace.single i 1)) x‖ ≤ C := by
        intro i j hj x hx
        calc
          ‖iteratedFDeriv ℝ j
              (fun x : E => (fderiv ℝ η x) (EuclideanSpace.single i 1)) x‖
              ≤ ‖iteratedFDeriv ℝ (j + 1) η x‖ :=
                norm_iteratedFDeriv_partial_le (d := d) hη_smooth i j x
          _ ≤ C := hη_bound (j + 1) (Nat.succ_le_succ hj) x hx
      have h_partial_eta_ih : ∀ i : Fin d, ∃ K' : ℝ, 0 < K' ∧
          ∀ {u : E → ℝ}, MemWkp (d := d) k p u Ω →
            iteratedWeakSobolevNorm (d := d) k p
              (fun x => (fderiv ℝ η x) (EuclideanSpace.single i 1) * u x) Ω ≤
              ENNReal.ofReal K' * iteratedWeakSobolevNorm (d := d) k p u Ω := fun i =>
        ih (h_partial_eta_smooth i) (h_partial_eta_bound i)
      let K_pi : Fin d → ℝ := fun i => (h_partial_eta_ih i).choose
      have hK_pi_pos : ∀ i : Fin d, 0 < K_pi i := fun i =>
        (h_partial_eta_ih i).choose_spec.1
      have hK_pi_bound : ∀ i : Fin d, ∀ {u : E → ℝ}, MemWkp (d := d) k p u Ω →
          iteratedWeakSobolevNorm (d := d) k p
            (fun x => (fderiv ℝ η x) (EuclideanSpace.single i 1) * u x) Ω ≤
            ENNReal.ofReal (K_pi i) * iteratedWeakSobolevNorm (d := d) k p u Ω := fun i =>
        (h_partial_eta_ih i).choose_spec.2
      set K_partial_sum : ℝ := ∑ i : Fin d, K_pi i with hKPS_def
      have hK_partial_sum_pos : 0 < K_partial_sum := by
        rw [hKPS_def]
        have hNeZero : (Finset.univ : Finset (Fin d)).Nonempty := by
          have h_card : 0 < (Finset.univ : Finset (Fin d)).card := by
            rw [Finset.card_univ, Fintype.card_fin]
            exact Nat.pos_of_ne_zero (NeZero.ne d)
          exact Finset.card_pos.mp h_card
        refine Finset.sum_pos (fun i _ => hK_pi_pos i) hNeZero
      set K_total : ℝ := max (C + 1) (K_eta + K_partial_sum) with hKt_def
      have hC_le_K_total : C ≤ K_total := by
        rw [hKt_def]; calc C ≤ C + 1 := by linarith
          _ ≤ max (C + 1) (K_eta + K_partial_sum) := le_max_left _ _
      have hC_plus_one_le_K_total : C + 1 ≤ K_total := le_max_left _ _
      have hK_eta_le_K_total : K_eta ≤ K_total := by
        rw [hKt_def]
        calc K_eta ≤ K_eta + K_partial_sum := by linarith [hK_partial_sum_pos]
          _ ≤ max (C + 1) (K_eta + K_partial_sum) := le_max_right _ _
      have hK_pi_le_K_total : ∀ i : Fin d, K_pi i ≤ K_total := by
        intro i
        rw [hKt_def]
        have h_le : K_pi i ≤ K_partial_sum := by
          rw [hKPS_def]
          refine Finset.single_le_sum (f := K_pi) ?_ (Finset.mem_univ i)
          intro j _; exact (hK_pi_pos j).le
        calc K_pi i ≤ K_partial_sum := h_le
          _ ≤ K_eta + K_partial_sum := by linarith
          _ ≤ max (C + 1) (K_eta + K_partial_sum) := le_max_right _ _
      have hK_total_pos : 0 < K_total := lt_of_lt_of_le (by linarith) hC_plus_one_le_K_total
      set K_final : ℝ := C + K_eta + K_partial_sum + 1 with hKf_def
      have hK_final_pos : 0 < K_final := by
        rw [hKf_def]
        linarith [hK_eta_pos, hK_partial_sum_pos]
      refine ⟨K_final, hK_final_pos, ?_⟩
      intro u hu
      have hηu_W : MemWkp (d := d) (k + 1) p (fun x => η x * u x) Ω :=
        MemWkp.smul_smooth_bounded (d := d) (k + 1) hp_one hΩ_open hη_smooth hη_bound hu
      rw [wkpNorm_succ_eq_eLpNorm_add_sum_partial (d := d) k p Ω (fun x => η x * u x)]
      rw [wkpNorm_succ_eq_eLpNorm_add_sum_partial (d := d) k p Ω u]
      have h0 : ∀ x ∈ Ω, ‖η x‖ ≤ C := by
        intro x hx
        have h := hη_bound 0 (Nat.zero_le _) x hx
        rwa [norm_iteratedFDeriv_zero] at h
      have h_eta_u_eLp_le : eLpNorm (fun x => η x * u x) p (volume.restrict Ω) ≤
          ENNReal.ofReal C * eLpNorm u p (volume.restrict Ω) :=
        eLpNorm_eta_mul_le (d := d) hΩ_open hη_smooth.continuous.aestronglyMeasurable h0 u
      have h_partial_bound : ∀ i : Fin d,
          iteratedWeakSobolevNorm (d := d) k p
            (chosenWeakPartialOrZero (d := d) p i (fun x => η x * u x) Ω) Ω ≤
          ENNReal.ofReal K_eta *
            iteratedWeakSobolevNorm (d := d) k p (chosenWeakPartialOrZero (d := d) p i u Ω) Ω +
          ENNReal.ofReal (K_pi i) * iteratedWeakSobolevNorm (d := d) k p u Ω := by
        intro i
        have h0' : ∀ x ∈ Ω, ‖η x‖ ≤ C := h0
        have h1' : ∀ x ∈ Ω, ‖fderiv ℝ η x‖ ≤ C := by
          intro x hx
          have h := hη_bound 1 (Nat.succ_le_succ (Nat.zero_le _)) x hx
          rwa [norm_iteratedFDeriv_one] at h
        have hu_W1p : Sobolev.Euclidean.MemW1p (d := d) p u Ω := hu.memW1p
        have hae := chosenWeakPartialOrZero_smul_smooth_bounded_ae (d := d) hp_one hΩ_open
          hη_smooth h0' h1' hu_W1p i
        rw [wkpNorm_congr_ae (d := d) hp_one hΩ_open hae]
        have h_du_mem : MemWkp (d := d) k p (chosenWeakPartialOrZero (d := d) p i u Ω) Ω :=
          hu.chosenWeakPartial_mem i
        have h_eta_du_mem : MemWkp (d := d) k p
            (fun x => η x * chosenWeakPartialOrZero (d := d) p i u Ω x) Ω :=
          MemWkp.smul_smooth_bounded (d := d) k hp_one hΩ_open hη_smooth hη_bound_k h_du_mem
        have hu_at_k : MemWkp (d := d) k p u Ω := hu.le_succ
        have h_dei_u_mem : MemWkp (d := d) k p
            (fun x => (fderiv ℝ η x) (EuclideanSpace.single i 1) * u x) Ω :=
          MemWkp.smul_smooth_bounded (d := d) k hp_one hΩ_open
            (h_partial_eta_smooth i) (h_partial_eta_bound i) hu_at_k
        have h_triangle := wkpNorm_add_le (d := d) hp_one hΩ_open h_eta_du_mem h_dei_u_mem
        refine h_triangle.trans ?_
        refine add_le_add ?_ ?_
        · exact hK_eta_bound h_du_mem
        · exact hK_pi_bound i hu_at_k
      have h_sum_bound :
          (∑ i : Fin d,
            iteratedWeakSobolevNorm (d := d) k p
              (chosenWeakPartialOrZero (d := d) p i (fun x => η x * u x) Ω) Ω) ≤
          ENNReal.ofReal K_eta *
            (∑ i : Fin d,
              iteratedWeakSobolevNorm (d := d) k p (chosenWeakPartialOrZero (d := d) p i u Ω) Ω) +
          ENNReal.ofReal K_partial_sum * iteratedWeakSobolevNorm (d := d) k p u Ω := by
        calc
          (∑ i : Fin d,
            iteratedWeakSobolevNorm (d := d) k p
              (chosenWeakPartialOrZero (d := d) p i (fun x => η x * u x) Ω) Ω)
              ≤ ∑ i : Fin d,
                (ENNReal.ofReal K_eta *
                  iteratedWeakSobolevNorm (d := d) k p (chosenWeakPartialOrZero (d := d) p i u Ω) Ω +
                ENNReal.ofReal (K_pi i) * iteratedWeakSobolevNorm (d := d) k p u Ω) :=
              Finset.sum_le_sum (fun i _ => h_partial_bound i)
          _ = (∑ i : Fin d, ENNReal.ofReal K_eta *
                iteratedWeakSobolevNorm (d := d) k p (chosenWeakPartialOrZero (d := d) p i u Ω) Ω) +
              ∑ i : Fin d, ENNReal.ofReal (K_pi i) * iteratedWeakSobolevNorm (d := d) k p u Ω := by
              rw [Finset.sum_add_distrib]
          _ = ENNReal.ofReal K_eta *
                (∑ i : Fin d,
                  iteratedWeakSobolevNorm (d := d) k p (chosenWeakPartialOrZero (d := d) p i u Ω) Ω) +
              (∑ i : Fin d, ENNReal.ofReal (K_pi i)) *
                iteratedWeakSobolevNorm (d := d) k p u Ω := by
              rw [Finset.mul_sum, ← Finset.sum_mul]
          _ = ENNReal.ofReal K_eta *
                (∑ i : Fin d,
                  iteratedWeakSobolevNorm (d := d) k p (chosenWeakPartialOrZero (d := d) p i u Ω) Ω) +
              ENNReal.ofReal K_partial_sum * iteratedWeakSobolevNorm (d := d) k p u Ω := by
              congr 1
              rw [hKPS_def]
              rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => (hK_pi_pos i).le)]
      have h_lhs_bound :
          eLpNorm (fun x => η x * u x) p (volume.restrict Ω) +
          ∑ i : Fin d,
            iteratedWeakSobolevNorm (d := d) k p
              (chosenWeakPartialOrZero (d := d) p i (fun x => η x * u x) Ω) Ω ≤
          ENNReal.ofReal C * eLpNorm u p (volume.restrict Ω) +
          (ENNReal.ofReal K_eta *
            (∑ i : Fin d,
              iteratedWeakSobolevNorm (d := d) k p (chosenWeakPartialOrZero (d := d) p i u Ω) Ω) +
          ENNReal.ofReal K_partial_sum * iteratedWeakSobolevNorm (d := d) k p u Ω) :=
        add_le_add h_eta_u_eLp_le h_sum_bound
      refine h_lhs_bound.trans ?_
      set S_lp : ℝ≥0∞ := eLpNorm u p (volume.restrict Ω) with hSlp_def
      set S_part : ℝ≥0∞ := ∑ i : Fin d,
        iteratedWeakSobolevNorm (d := d) k p (chosenWeakPartialOrZero (d := d) p i u Ω) Ω with hSpart_def
      have hu_at_k_norm_le_succ :
          iteratedWeakSobolevNorm (d := d) k p u Ω ≤ S_lp + S_part := by
        rw [hSlp_def, hSpart_def]
        rw [show S_lp + S_part = eLpNorm u p (volume.restrict Ω) +
            ∑ i : Fin d, iteratedWeakSobolevNorm (d := d) k p
              (chosenWeakPartialOrZero (d := d) p i u Ω) Ω from rfl]
        rw [← wkpNorm_succ_eq_eLpNorm_add_sum_partial (d := d) k p Ω u]
        unfold iteratedWeakSobolevNorm
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro j hj
          rw [Finset.mem_range] at hj ⊢; omega
        · intros _ _ _; exact bot_le
      have hC_plus_KPS_le_K_final : ENNReal.ofReal C + ENNReal.ofReal K_partial_sum ≤
          ENNReal.ofReal K_final := by
        rw [← ENNReal.ofReal_add hC_nonneg hK_partial_sum_pos.le]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hKf_def]
        linarith [hK_eta_pos]
      have hK_eta_plus_KPS_le_K_final : ENNReal.ofReal K_eta + ENNReal.ofReal K_partial_sum ≤
          ENNReal.ofReal K_final := by
        rw [← ENNReal.ofReal_add hK_eta_pos.le hK_partial_sum_pos.le]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hKf_def]
        linarith [hC_nonneg]
      have h_main_calc :
          ENNReal.ofReal C * S_lp +
          (ENNReal.ofReal K_eta * S_part +
          ENNReal.ofReal K_partial_sum * iteratedWeakSobolevNorm (d := d) k p u Ω) ≤
          ENNReal.ofReal K_final * (S_lp + S_part) := by
        have h_KPS_u_le :
            ENNReal.ofReal K_partial_sum * iteratedWeakSobolevNorm (d := d) k p u Ω ≤
            ENNReal.ofReal K_partial_sum * (S_lp + S_part) :=
          mul_le_mul_of_nonneg_left hu_at_k_norm_le_succ bot_le
        have h_combine_S_lp :
            ENNReal.ofReal C * S_lp + ENNReal.ofReal K_partial_sum * S_lp =
            (ENNReal.ofReal C + ENNReal.ofReal K_partial_sum) * S_lp := by
          rw [add_mul]
        have h_combine_S_part :
            ENNReal.ofReal K_eta * S_part + ENNReal.ofReal K_partial_sum * S_part =
            (ENNReal.ofReal K_eta + ENNReal.ofReal K_partial_sum) * S_part := by
          rw [add_mul]
        calc
          ENNReal.ofReal C * S_lp +
            (ENNReal.ofReal K_eta * S_part +
            ENNReal.ofReal K_partial_sum * iteratedWeakSobolevNorm (d := d) k p u Ω)
              ≤ ENNReal.ofReal C * S_lp +
                (ENNReal.ofReal K_eta * S_part +
                ENNReal.ofReal K_partial_sum * (S_lp + S_part)) := by
              gcongr
          _ = ENNReal.ofReal C * S_lp +
                (ENNReal.ofReal K_eta * S_part +
                (ENNReal.ofReal K_partial_sum * S_lp +
                  ENNReal.ofReal K_partial_sum * S_part)) := by
              rw [mul_add]
          _ = (ENNReal.ofReal C * S_lp + ENNReal.ofReal K_partial_sum * S_lp) +
              (ENNReal.ofReal K_eta * S_part + ENNReal.ofReal K_partial_sum * S_part) := by
              ring
          _ = (ENNReal.ofReal C + ENNReal.ofReal K_partial_sum) * S_lp +
              (ENNReal.ofReal K_eta + ENNReal.ofReal K_partial_sum) * S_part := by
              rw [h_combine_S_lp, h_combine_S_part]
          _ ≤ ENNReal.ofReal K_final * S_lp + ENNReal.ofReal K_final * S_part := by
              exact add_le_add
                (mul_le_mul_of_nonneg_right hC_plus_KPS_le_K_final bot_le)
                (mul_le_mul_of_nonneg_right hK_eta_plus_KPS_le_K_final bot_le)
          _ = ENNReal.ofReal K_final * (S_lp + S_part) := by rw [mul_add]
      exact h_main_calc

end LeibnizQuant

theorem exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_compact : HasCompactSupport η)
    (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, ∀ j ≤ m, ‖iteratedFDeriv ℝ j η x‖ ≤ C := by
  classical
  have h_per_j : ∀ j, ∃ Cj : ℝ, 0 ≤ Cj ∧
      ∀ x : E, ‖iteratedFDeriv ℝ j η x‖ ≤ Cj := by
    intro j
    have h_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun x => iteratedFDeriv ℝ j η x) := by
      have h := hη.iteratedFDeriv_right' (m := (⊤ : ℕ∞)) (i := j)
      simpa using h
    have h_support : HasCompactSupport (fun x => iteratedFDeriv ℝ j η x) :=
      hη_compact.iteratedFDeriv (𝕜 := ℝ) j
    obtain ⟨M, hM⟩ := h_support.exists_bound_of_continuous h_smooth.continuous
    refine ⟨max 0 M, le_max_left _ _, ?_⟩
    intro x
    exact (hM x).trans (le_max_right _ _)
  let Cj : ℕ → ℝ := fun j => Classical.choose (h_per_j j)
  have hCj_nn : ∀ j, 0 ≤ Cj j := fun j => (Classical.choose_spec (h_per_j j)).1
  have hCj_bound : ∀ j, ∀ x : E, ‖iteratedFDeriv ℝ j η x‖ ≤ Cj j := fun j =>
    (Classical.choose_spec (h_per_j j)).2
  have h_nonempty : (Finset.range (m + 1)).Nonempty :=
    ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩
  let C : ℝ := (Finset.range (m + 1)).sup' h_nonempty Cj
  have hC_ge : ∀ j ∈ Finset.range (m + 1), Cj j ≤ C := fun j hj =>
    Finset.le_sup' Cj hj
  have hC_nn : 0 ≤ C :=
    le_trans (hCj_nn 0) (hC_ge 0 (Finset.mem_range.mpr (Nat.zero_lt_succ _)))
  refine ⟨C, hC_nn, ?_⟩
  intro x j hj
  have hj_mem : j ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  exact le_trans (hCj_bound j x) (hC_ge j hj_mem)

end Euclidean
end Sobolev
