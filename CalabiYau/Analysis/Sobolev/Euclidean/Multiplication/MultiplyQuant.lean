-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Euclidean/Multiplication/MultiplyQuant.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Euclidean.Multiplication.Multiply

@[expose] public section

-- Private declarations used in public declarations require the compatibility option below..

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Sobolev
namespace Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

lemma norm_partial_eta_le_fderiv
    {η : E → ℝ} (i : Fin d) (x : E) :
    ‖(fderiv ℝ η x) (EuclideanSpace.single i (1 : ℝ))‖ ≤ ‖fderiv ℝ η x‖ := by
  have h := ContinuousLinearMap.le_opNorm (fderiv ℝ η x)
    (EuclideanSpace.single i (1 : ℝ))
  have h_one : ‖(EuclideanSpace.single i (1 : ℝ))‖ = 1 := by simp
  rw [h_one, mul_one] at h
  exact h

lemma eLpNorm_eta_mul_le
    {p : ℝ≥0∞} {Ω : Set E} (hΩ : IsOpen Ω)
    {η : E → ℝ}
    {C : ℝ}
    (hη_bound : ∀ x ∈ Ω, ‖η x‖ ≤ C)
    (v : E → ℝ) :
    eLpNorm (fun x => η x * v x) p (volume.restrict Ω) ≤
      ENNReal.ofReal C * eLpNorm v p (volume.restrict Ω) := by
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (g := v) (c := C) ?_ p
  refine (ae_restrict_iff' hΩ.measurableSet).mpr ?_
  refine Filter.Eventually.of_forall (fun x hx => ?_)
  calc
    ‖η x * v x‖ = ‖η x‖ * ‖v x‖ := norm_mul _ _
    _ ≤ C * ‖v x‖ := by
          gcongr
          exact hη_bound x hx

lemma eLpNorm_partial_eta_mul_le
    {p : ℝ≥0∞} {Ω : Set E} (hΩ : IsOpen Ω)
    {η : E → ℝ}
    {C : ℝ}
    (hη_grad_bound : ∀ x ∈ Ω, ‖fderiv ℝ η x‖ ≤ C)
    (i : Fin d) (v : E → ℝ) :
    eLpNorm (fun x => (fderiv ℝ η x) (EuclideanSpace.single i (1 : ℝ)) * v x)
        p (volume.restrict Ω) ≤
      ENNReal.ofReal C * eLpNorm v p (volume.restrict Ω) := by
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (g := v) (c := C) ?_ p
  refine (ae_restrict_iff' hΩ.measurableSet).mpr ?_
  refine Filter.Eventually.of_forall (fun x hx => ?_)
  calc
    ‖(fderiv ℝ η x) (EuclideanSpace.single i (1 : ℝ)) * v x‖
        = ‖(fderiv ℝ η x) (EuclideanSpace.single i (1 : ℝ))‖ * ‖v x‖ := norm_mul _ _
    _ ≤ ‖fderiv ℝ η x‖ * ‖v x‖ := by
          gcongr
          exact norm_partial_eta_le_fderiv i x
    _ ≤ C * ‖v x‖ := by
          gcongr
          exact hη_grad_bound x hx

lemma eLpNorm_chosenWeakPartialOrZero_smul_smooth_bounded_le
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω)
    {η : E → ℝ}
    (hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η)
    {C : ℝ}
    (hη_bound : ∀ x ∈ Ω, ‖η x‖ ≤ C)
    (hη_grad_bound : ∀ x ∈ Ω, ‖fderiv ℝ η x‖ ≤ C)
    {u : E → ℝ} (hu : DeGiorgi.MemW1p (d := d) p u Ω) (i : Fin d) :
    eLpNorm (chosenWeakPartialOrZero (d := d) p i (fun x => η x * u x) Ω) p
        (volume.restrict Ω) ≤
      ENNReal.ofReal C *
        eLpNorm (chosenWeakPartialOrZero (d := d) p i u Ω) p (volume.restrict Ω) +
      ENNReal.ofReal C * eLpNorm u p (volume.restrict Ω) := by
  classical
  have hae := chosenWeakPartialOrZero_smul_smooth_bounded_ae (d := d) hp_one hΩ
    hη_smooth hη_bound hη_grad_bound hu i
  have hηcwp_meas : AEStronglyMeasurable
      (fun x => η x * chosenWeakPartialOrZero (d := d) p i u Ω x)
      (volume.restrict Ω) :=
    hη_smooth.continuous.aestronglyMeasurable.mul
      (chosenWeakPartialOrZero_memLp_of_mem hu i).aestronglyMeasurable
  have hderiv_cont : Continuous
      (fun x : E => (fderiv ℝ η x) (EuclideanSpace.single i (1 : ℝ))) :=
    (hη_smooth.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
      continuous_const
  have hdηu_meas : AEStronglyMeasurable
      (fun x => (fderiv ℝ η x) (EuclideanSpace.single i (1 : ℝ)) * u x)
      (volume.restrict Ω) :=
    hderiv_cont.aestronglyMeasurable.mul hu.1.aestronglyMeasurable
  rw [eLpNorm_congr_ae hae]
  have hSumEq :
      (fun x => η x * chosenWeakPartialOrZero (d := d) p i u Ω x +
        (fderiv ℝ η x) (EuclideanSpace.single i (1 : ℝ)) * u x) =
      (fun x => η x * chosenWeakPartialOrZero (d := d) p i u Ω x) +
      (fun x => (fderiv ℝ η x) (EuclideanSpace.single i (1 : ℝ)) * u x) := by
    funext x
    simp [Pi.add_apply]
  rw [hSumEq]
  have htriangle :
      eLpNorm
          ((fun x => η x * chosenWeakPartialOrZero (d := d) p i u Ω x) +
            fun x => (fderiv ℝ η x) (EuclideanSpace.single i (1 : ℝ)) * u x)
          p (volume.restrict Ω)
        ≤ eLpNorm (fun x => η x * chosenWeakPartialOrZero (d := d) p i u Ω x)
            p (volume.restrict Ω) +
          eLpNorm
            (fun x => (fderiv ℝ η x) (EuclideanSpace.single i (1 : ℝ)) * u x)
            p (volume.restrict Ω) :=
    eLpNorm_add_le hηcwp_meas hdηu_meas hp_one
  refine htriangle.trans ?_
  have hbnd1 :
      eLpNorm (fun x => η x * chosenWeakPartialOrZero (d := d) p i u Ω x)
          p (volume.restrict Ω)
        ≤ ENNReal.ofReal C *
          eLpNorm (chosenWeakPartialOrZero (d := d) p i u Ω) p (volume.restrict Ω) :=
    eLpNorm_eta_mul_le (d := d) hΩ hη_bound (chosenWeakPartialOrZero p i u Ω)
  have hbnd2 :
      eLpNorm (fun x => (fderiv ℝ η x) (EuclideanSpace.single i (1 : ℝ)) * u x)
          p (volume.restrict Ω)
        ≤ ENNReal.ofReal C * eLpNorm u p (volume.restrict Ω) :=
    eLpNorm_partial_eta_mul_le (d := d) hΩ hη_grad_bound i u
  exact add_le_add hbnd1 hbnd2

lemma ofReal_eq_ofReal_max_zero (C : ℝ) :
    ENNReal.ofReal C = ENNReal.ofReal (max C 0) := by
  rcases lt_or_ge C 0 with hC | hC
  · have hmax : max C 0 = 0 := max_eq_right hC.le
    rw [hmax, ENNReal.ofReal_of_nonpos hC.le]
    simp
  · have hmax : max C 0 = C := max_eq_left hC
    rw [hmax]

lemma natCast_one_add_d_eq_ofReal (d : ℕ) :
    ((1 + d : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((1 + d : ℕ) : ℝ) := by
  rw [ENNReal.ofReal_natCast]

lemma natCast_one_add_d_mul_ofReal (d : ℕ) (C : ℝ) :
    (((1 + d : ℕ) : ℝ≥0∞) * ENNReal.ofReal C) =
      ENNReal.ofReal (((1 + d : ℕ) : ℝ) * max C 0) := by
  have hnn : (0 : ℝ) ≤ ((1 + d : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [natCast_one_add_d_eq_ofReal d, ofReal_eq_ofReal_max_zero C,
      ← ENNReal.ofReal_mul hnn]

theorem wkpNorm_smul_smooth_bounded_le_one
    (k : ℕ) (hk : k ≤ 1) {d : ℕ}
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ_open : IsOpen Ω)
    {η : EuclideanSpace ℝ (Fin d) → ℝ}
    (hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η)
    {C : ℝ} (hC_nonneg : 0 ≤ C)
    (hη_bound : ∀ j ≤ k, ∀ x ∈ Ω, ‖iteratedFDeriv ℝ j η x‖ ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ {u : EuclideanSpace ℝ (Fin d) → ℝ} (_hu : MemWkp k p u Ω),
      iteratedWeakSobolevNorm k p (fun x => η x * u x) Ω ≤ ENNReal.ofReal K *
        iteratedWeakSobolevNorm k p u Ω := by
  match k, hk with
  | 0, _ =>
    have h0 : ∀ x ∈ Ω, ‖η x‖ ≤ C := by
      intro x hx
      have h := hη_bound 0 (Nat.zero_le _) x hx
      rwa [norm_iteratedFDeriv_zero] at h
    refine ⟨C + 1, by linarith, ?_⟩
    intro u hu
    rw [wkpNorm_zero (d := d) (p := p), wkpNorm_zero (d := d) (p := p)]
    have hb : eLpNorm (fun x => η x * u x) p (volume.restrict Ω) ≤
        ENNReal.ofReal C * eLpNorm u p (volume.restrict Ω) := by
      refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (g := u) (c := C) ?_ p
      refine (ae_restrict_iff' hΩ_open.measurableSet).mpr ?_
      refine Filter.Eventually.of_forall (fun x hx => ?_)
      calc
        ‖η x * u x‖ = ‖η x‖ * ‖u x‖ := norm_mul _ _
        _ ≤ C * ‖u x‖ := by gcongr; exact h0 x hx
    have hC : ENNReal.ofReal C ≤ ENNReal.ofReal (C + 1) :=
      ENNReal.ofReal_le_ofReal (by linarith)
    exact hb.trans (mul_le_mul' hC (le_refl _))
  | 1, _ =>
    have h_eta0 : ∀ x ∈ Ω, ‖η x‖ ≤ C := by
      intro x hx
      have h := hη_bound 0 (by omega) x hx
      rwa [norm_iteratedFDeriv_zero] at h
    have h_eta1 : ∀ x ∈ Ω, ‖fderiv ℝ η x‖ ≤ C := by
      intro x hx
      have h := hη_bound 1 (by omega) x hx
      rwa [norm_iteratedFDeriv_one] at h
    classical
    let _ := hp_top
    set K : ℝ := ((1 + d : ℕ) : ℝ) * (max C 0 + 1) with hK_def
    have h_natpos : (0 : ℝ) < ((1 + d : ℕ) : ℝ) := by
      have h : (0 : ℕ) < 1 + d := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_add_right _ _)
      exact_mod_cast h
    have hK_pos : 0 < K := by
      have hMaxNonneg : (0 : ℝ) ≤ max C 0 := le_max_right _ _
      have h1 : (0 : ℝ) < max C 0 + 1 := by linarith
      exact mul_pos h_natpos h1
    refine ⟨K, hK_pos, ?_⟩
    intro v hv
    have hv_W1p : DeGiorgi.MemW1p (d := d) p v Ω := hv.memW1p
    set Au : ℝ≥0∞ := eLpNorm v p (volume.restrict Ω) with hAu_def
    set Bu : Fin d → ℝ≥0∞ :=
      fun i => eLpNorm (chosenWeakPartialOrZero p i v Ω) p (volume.restrict Ω)
      with hBu_def
    set OC : ℝ≥0∞ := ENNReal.ofReal C with hOC_def
    set OK : ℝ≥0∞ := ENNReal.ofReal K with hOK_def
    have h_eta_v_bnd :
        eLpNorm (fun x => η x * v x) p (volume.restrict Ω) ≤ OC * Au :=
      eLpNorm_eta_mul_le (d := d) hΩ_open h_eta0 v
    have h_chosen_bnd : ∀ i : Fin d,
        eLpNorm (chosenWeakPartialOrZero p i (fun x => η x * v x) Ω) p
            (volume.restrict Ω)
          ≤ OC * Bu i + OC * Au := fun i =>
      eLpNorm_chosenWeakPartialOrZero_smul_smooth_bounded_le (d := d) hp_one hΩ_open
        hη_smooth h_eta0 h_eta1 hv_W1p i
    have hLHS_unfold : iteratedWeakSobolevNorm (d := d) 1 p (fun x => η x * v x) Ω =
        eLpNorm (fun x => η x * v x) p (volume.restrict Ω) +
        ∑ α : Fin 1 → Fin d,
          eLpNorm (iterWeakPartial (d := d) p 1 α (fun x => η x * v x) Ω) p
            (volume.restrict Ω) := by
      unfold iteratedWeakSobolevNorm
      rw [show (1 : ℕ) + 1 = 1 + 1 from rfl]
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      have h0_unique : ∀ α : Fin 0 → Fin d, α = (fun i : Fin 0 => i.elim0) :=
        fun α => by funext i; exact i.elim0
      have : Unique (Fin 0 → Fin d) :=
        { default := fun i : Fin 0 => i.elim0
          uniq := fun α => (h0_unique α).symm ▸ rfl }
      rw [Fintype.sum_unique
            (f := fun α : Fin 0 → Fin d =>
              eLpNorm (iterWeakPartial (d := d) p 0 α (fun x => η x * v x) Ω) p
                (volume.restrict Ω))]
      simp [iterWeakPartial_zero]
    have hRHS_unfold : iteratedWeakSobolevNorm (d := d) 1 p v Ω =
        Au +
        ∑ α : Fin 1 → Fin d,
          eLpNorm (iterWeakPartial (d := d) p 1 α v Ω) p (volume.restrict Ω) := by
      unfold iteratedWeakSobolevNorm
      rw [show (1 : ℕ) + 1 = 1 + 1 from rfl]
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      have h0_unique : ∀ α : Fin 0 → Fin d, α = (fun i : Fin 0 => i.elim0) :=
        fun α => by funext i; exact i.elim0
      have : Unique (Fin 0 → Fin d) :=
        { default := fun i : Fin 0 => i.elim0
          uniq := fun α => (h0_unique α).symm ▸ rfl }
      rw [Fintype.sum_unique
            (f := fun α : Fin 0 → Fin d =>
              eLpNorm (iterWeakPartial (d := d) p 0 α v Ω) p (volume.restrict Ω))]
      simp [iterWeakPartial_zero, hAu_def]
    have hIter1_eta_v : ∀ α : Fin 1 → Fin d,
        iterWeakPartial (d := d) p 1 α (fun x => η x * v x) Ω =
          chosenWeakPartialOrZero (d := d) p (α 0) (fun x => η x * v x) Ω := by
      intro α; rw [iterWeakPartial_succ]; rfl
    have hIter1_v : ∀ α : Fin 1 → Fin d,
        iterWeakPartial (d := d) p 1 α v Ω =
          chosenWeakPartialOrZero (d := d) p (α 0) v Ω := by
      intro α; rw [iterWeakPartial_succ]; rfl
    have hLHS_unfold' : iteratedWeakSobolevNorm (d := d) 1 p (fun x => η x * v x) Ω =
        eLpNorm (fun x => η x * v x) p (volume.restrict Ω) +
        ∑ α : Fin 1 → Fin d,
          eLpNorm (chosenWeakPartialOrZero (d := d) p (α 0) (fun x => η x * v x) Ω) p
            (volume.restrict Ω) := by
      rw [hLHS_unfold]
      refine congrArg (eLpNorm (fun x => η x * v x) p (volume.restrict Ω) + ·) ?_
      refine Finset.sum_congr rfl (fun α _ => ?_)
      rw [hIter1_eta_v α]
    have hRHS_unfold' : iteratedWeakSobolevNorm (d := d) 1 p v Ω =
        Au +
        ∑ α : Fin 1 → Fin d,
          eLpNorm (chosenWeakPartialOrZero (d := d) p (α 0) v Ω) p (volume.restrict Ω) := by
      rw [hRHS_unfold]
      refine congrArg (Au + ·) ?_
      refine Finset.sum_congr rfl (fun α _ => ?_)
      rw [hIter1_v α]
    have hSumBu :
        ∑ α : Fin 1 → Fin d,
            eLpNorm (chosenWeakPartialOrZero (d := d) p (α 0) v Ω) p
              (volume.restrict Ω) =
          ∑ α : Fin 1 → Fin d, Bu (α 0) := by
      refine Finset.sum_congr rfl (fun α _ => ?_)
      rw [hBu_def]
    rw [hLHS_unfold', hRHS_unfold', hSumBu]
    have hSum_chosen_bnd :
        ∑ α : Fin 1 → Fin d,
            eLpNorm (chosenWeakPartialOrZero (d := d) p (α 0) (fun x => η x * v x) Ω) p
              (volume.restrict Ω)
          ≤ ∑ α : Fin 1 → Fin d, (OC * Bu (α 0) + OC * Au) :=
      Finset.sum_le_sum (fun α _ => h_chosen_bnd (α 0))
    refine (add_le_add h_eta_v_bnd hSum_chosen_bnd).trans ?_
    have hSum_split :
        ∑ α : Fin 1 → Fin d, (OC * Bu (α 0) + OC * Au) =
          (∑ α : Fin 1 → Fin d, OC * Bu (α 0)) +
          ∑ _α : Fin 1 → Fin d, OC * Au := Finset.sum_add_distrib
    rw [hSum_split]
    have hCard : (Finset.univ : Finset (Fin 1 → Fin d)).card = d := by
      rw [Finset.card_univ]; simp
    have hSum_const :
        ∑ _α : Fin 1 → Fin d, OC * Au = (d : ℝ≥0∞) * (OC * Au) := by
      rw [Finset.sum_const, hCard, nsmul_eq_mul]
    rw [hSum_const]
    have hSum_factor :
        ∑ α : Fin 1 → Fin d, OC * Bu (α 0) = OC * ∑ α : Fin 1 → Fin d, Bu (α 0) := by
      rw [Finset.mul_sum]
    rw [hSum_factor]
    set SBu : ℝ≥0∞ := ∑ α : Fin 1 → Fin d, Bu (α 0) with hSBu_def
    have h_one_plus_d_OC_le_OK : ((1 + d : ℕ) : ℝ≥0∞) * OC ≤ OK := by
      rw [hOC_def, hOK_def, natCast_one_add_d_mul_ofReal]
      apply ENNReal.ofReal_le_ofReal
      have hMaxNonneg : (0 : ℝ) ≤ max C 0 := le_max_right _ _
      have : max C 0 ≤ max C 0 + 1 := by linarith
      have hMul := mul_le_mul_of_nonneg_left this h_natpos.le
      exact hMul
    have h_OC_le_OK : OC ≤ OK := by
      rw [hOC_def, hOK_def, ofReal_eq_ofReal_max_zero]
      apply ENNReal.ofReal_le_ofReal
      have hMaxNonneg : (0 : ℝ) ≤ max C 0 := le_max_right _ _
      have h1 : max C 0 ≤ max C 0 + 1 := by linarith
      have h3 : (1 : ℝ) ≤ ((1 + d : ℕ) : ℝ) := by
        have h : (1 : ℕ) ≤ 1 + d := Nat.le_add_right _ _
        exact_mod_cast h
      have h4 : max C 0 + 1 ≤ ((1 + d : ℕ) : ℝ) * (max C 0 + 1) := by
        have hPos : 0 ≤ max C 0 + 1 := by linarith
        have := mul_le_mul_of_nonneg_right h3 hPos
        simpa [one_mul] using this
      linarith
    change OC * Au + (OC * SBu + (d : ℝ≥0∞) * (OC * Au)) ≤ OK * (Au + SBu)
    have h_factor_one_plus_d :
        OC + (d : ℝ≥0∞) * OC = ((1 + d : ℕ) : ℝ≥0∞) * OC := by
      rw [show ((1 + d : ℕ) : ℝ≥0∞) = 1 + (d : ℝ≥0∞) by push_cast; ring]
      rw [add_mul, one_mul]
    have h_lhs_factor :
        OC * Au + (OC * SBu + (d : ℝ≥0∞) * (OC * Au)) =
          ((1 + d : ℕ) : ℝ≥0∞) * OC * Au + OC * SBu := by
      rw [← h_factor_one_plus_d, add_mul]
      ring
    rw [h_lhs_factor]
    have hbnd_Au : ((1 + d : ℕ) : ℝ≥0∞) * OC * Au ≤ OK * Au :=
      mul_le_mul_left h_one_plus_d_OC_le_OK Au
    have hbnd_SBu : OC * SBu ≤ OK * SBu :=
      mul_le_mul_left h_OC_le_OK SBu
    calc
      ((1 + d : ℕ) : ℝ≥0∞) * OC * Au + OC * SBu
          ≤ OK * Au + OK * SBu := add_le_add hbnd_Au hbnd_SBu
      _ = OK * (Au + SBu) := by rw [mul_add]

end Euclidean
end Sobolev
