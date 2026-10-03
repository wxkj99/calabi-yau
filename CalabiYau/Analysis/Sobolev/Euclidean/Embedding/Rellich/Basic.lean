-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Euclidean/Embedding/Rellich/Basic.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Tools.FrechetKolmogorov

@[expose] public section

-- Private declarations used in public declarations require the compatibility option below.

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open scoped ENNReal NNReal Convolution Pointwise

namespace Sobolev

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

lemma euclidean_component_norm_le (v : E) (i : Fin d) : ‖v i‖ ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq]
  have : ‖v i‖ ^ 2 ≤ ∑ j, ‖v j‖ ^ 2 := by
    refine Finset.single_le_sum (f := fun j => ‖v j‖ ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hsum_nn : 0 ≤ ∑ j, ‖v j‖ ^ 2 := by
    refine Finset.sum_nonneg ?_
    intros
    exact sq_nonneg _
  have hnorm_nn : 0 ≤ ‖v i‖ := norm_nonneg _
  calc
    ‖v i‖ = Real.sqrt (‖v i‖ ^ 2) := (Real.sqrt_sq hnorm_nn).symm
    _ ≤ Real.sqrt (∑ j, ‖v j‖ ^ 2) := Real.sqrt_le_sqrt this

lemma fderiv_norm_le_sum_components
    {φ : E → ℝ} (x : E) :
    ‖fderiv ℝ φ x‖ ≤ ∑ i : Fin d, |(fderiv ℝ φ x) (EuclideanSpace.single i 1)| := by
  classical
  set L : E →L[ℝ] ℝ := fderiv ℝ φ x
  have h_apply : ∀ v : E, L v = ∑ i : Fin d, v i * L (EuclideanSpace.single i 1) := by
    intro v
    have hv : v = ∑ i : Fin d, v i • EuclideanSpace.single i (1 : ℝ) := by
      ext j
      simp [EuclideanSpace.single, Pi.single_apply, smul_eq_mul]
    conv_lhs => rw [hv]
    rw [map_sum]
    simp [smul_eq_mul]
  refine ContinuousLinearMap.opNorm_le_bound L ?_ ?_
  · exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
  · intro v
    rw [h_apply v]
    calc
      ‖∑ i : Fin d, v i * L (EuclideanSpace.single i 1)‖
          ≤ ∑ i : Fin d, ‖v i * L (EuclideanSpace.single i 1)‖ :=
            norm_sum_le _ _
      _ = ∑ i : Fin d, ‖v i‖ * ‖L (EuclideanSpace.single i 1)‖ := by
            simp [norm_mul]
      _ ≤ ∑ i : Fin d, ‖v‖ * ‖L (EuclideanSpace.single i 1)‖ := by
            refine Finset.sum_le_sum ?_
            intro i _
            have hvi : ‖v i‖ ≤ ‖v‖ := euclidean_component_norm_le v i
            exact mul_le_mul_of_nonneg_right hvi (norm_nonneg _)
      _ = ‖v‖ * ∑ i : Fin d, ‖L (EuclideanSpace.single i 1)‖ := by
            rw [← Finset.mul_sum]
      _ = ‖v‖ * ∑ i : Fin d, |L (EuclideanSpace.single i 1)| := by
            have hcongr :
                (∑ i : Fin d, ‖L (EuclideanSpace.single i 1)‖) =
                  ∑ i : Fin d, |L (EuclideanSpace.single i 1)| := by
              apply Finset.sum_congr rfl
              intros i _
              exact Real.norm_eq_abs _
            rw [hcongr]
      _ = (∑ i : Fin d, |L (EuclideanSpace.single i 1)|) * ‖v‖ := by ring

lemma eLpNorm_fderiv_le_sum_components
    {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    eLpNorm (fun x => ‖fderiv ℝ φ x‖) p volume ≤
      ∑ i : Fin d,
        eLpNorm (fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1)) p volume := by
  classical
  have hcomp_aem :
      ∀ i : Fin d,
        AEStronglyMeasurable
          (fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1)) volume := by
    intro i
    have hcont : Continuous
        (fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1)) :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    exact hcont.aestronglyMeasurable
  have hbound : ∀ x, ‖fderiv ℝ φ x‖ ≤
      ∑ i : Fin d, |(fderiv ℝ φ x) (EuclideanSpace.single i 1)| := by
    intro x
    exact fderiv_norm_le_sum_components (d := d) x
  have hmono :
      eLpNorm (fun x => ‖fderiv ℝ φ x‖) p volume ≤
        eLpNorm
          (fun x => ∑ i : Fin d, |(fderiv ℝ φ x) (EuclideanSpace.single i 1)|) p volume := by
    refine eLpNorm_mono_ae_real
      (hφ.continuous_fderiv (by simp)).aestronglyMeasurable.norm ?_
    filter_upwards with x
    have hnn : 0 ≤ ‖fderiv ℝ φ x‖ := norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hbound x
  have h_step_general :
      ∀ (T : Finset (Fin d)),
        eLpNorm
            (fun x => ∑ i ∈ T, |(fderiv ℝ φ x) (EuclideanSpace.single i 1)|) p volume ≤
          ∑ i ∈ T,
            eLpNorm
              (fun x => |(fderiv ℝ φ x) (EuclideanSpace.single i 1)|) p volume := by
    intro T
    classical
    refine Finset.induction_on T ?_ ?_
    · simp
    · intros a s hi IH
      have hsum_eq_LHS :
          (fun x => ∑ i ∈ insert a s,
              |(fderiv ℝ φ x) (EuclideanSpace.single i 1)|) =
            fun x =>
              |(fderiv ℝ φ x) (EuclideanSpace.single a 1)| +
                ∑ i ∈ s, |(fderiv ℝ φ x) (EuclideanSpace.single i 1)| := by
        funext x
        exact Finset.sum_insert hi
      rw [hsum_eq_LHS]
      have hsum_eq_RHS :
          ∑ i ∈ insert a s,
              eLpNorm
                (fun x => |(fderiv ℝ φ x) (EuclideanSpace.single i 1)|) p volume =
            eLpNorm
                (fun x => |(fderiv ℝ φ x) (EuclideanSpace.single a 1)|) p volume +
              ∑ i ∈ s,
                eLpNorm
                  (fun x => |(fderiv ℝ φ x) (EuclideanSpace.single i 1)|) p volume :=
        Finset.sum_insert hi
      rw [hsum_eq_RHS]
      have hadd_le :=
        eLpNorm_add_le (μ := volume) (p := p)
          (f := fun x => |(fderiv ℝ φ x) (EuclideanSpace.single a 1)|)
          (g := fun x => ∑ i ∈ s, |(fderiv ℝ φ x) (EuclideanSpace.single i 1)|)
          hp_one
      refine hadd_le.trans ?_
      gcongr
  have h_step := h_step_general (Finset.univ : Finset (Fin d))
  refine hmono.trans (h_step.trans ?_)
  refine Finset.sum_le_sum ?_
  intro i _
  refine le_of_eq ?_
  have hcongr :
      (fun x => |(fderiv ℝ φ x) (EuclideanSpace.single i 1)|) =
        (fun x => ‖(fderiv ℝ φ x) (EuclideanSpace.single i 1)‖) := by
    funext x
    exact (Real.norm_eq_abs _).symm
  rw [hcongr, eLpNorm_norm _ (hcomp_aem i)]

lemma eLpNorm_translate_sub_le_sum_components
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (h : E) :
    eLpNorm (fun x => φ (x - h) - φ x) p volume ≤
      ENNReal.ofReal ‖h‖ *
        ∑ i : Fin d,
          eLpNorm (fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1)) p volume := by
  classical
  have hStepA :
      eLpNorm (fun x => φ x - φ (x - h)) p volume ≤
        ENNReal.ofReal ‖h‖ * eLpNorm (fun x => ‖fderiv ℝ φ x‖) p volume :=
    eLpNorm_translate_sub_le_smul_eLpNorm_fderiv (d := d) hp_one hp_top hφ h
  have hSym :
      eLpNorm (fun x => φ (x - h) - φ x) p volume =
        eLpNorm (fun x => φ x - φ (x - h)) p volume := by
    have hEq1 : (fun x => φ (x - h) - φ x) =
        ((fun x => φ (x - h)) - (fun x => φ x)) := by
      funext x; rfl
    have hEq2 : (fun x => φ x - φ (x - h)) =
        ((fun x => φ x) - (fun x => φ (x - h))) := by
      funext x; rfl
    rw [hEq1, hEq2]
    exact eLpNorm_sub_comm (μ := volume) (p := p)
      (f := fun x => φ (x - h)) (g := fun x => φ x)
  rw [hSym]
  refine hStepA.trans ?_
  have hgrad_bound :
      eLpNorm (fun x => ‖fderiv ℝ φ x‖) p volume ≤
        ∑ i : Fin d,
          eLpNorm (fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1)) p volume :=
    eLpNorm_fderiv_le_sum_components (d := d) hp_one hφ
  gcongr

variable [NeZero d] in
private lemma eLpNorm_grad_eq_restrict
    {Ω : Set E} (hΩ_meas : MeasurableSet Ω)
    {φ : E → ℝ}
    (hφ_sub : tsupport φ ⊆ Ω)
    {p : ℝ≥0∞} (i : Fin d) :
    eLpNorm (fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1)) p volume =
      eLpNorm (fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1)) p
        (volume.restrict Ω) := by
  have hgrad_eq_indicator :
      (fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1)) =
        Ω.indicator (fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1)) := by
    funext x
    by_cases hx : x ∈ Ω
    · simp [hx]
    · have hzero :=
        Sobolev.Euclidean.fderiv_apply_zero_outside_of_tsupport_subset
          (Ω := Ω) (hsub := hφ_sub) hx i
      simp [hx, hzero]
  conv_lhs => rw [hgrad_eq_indicator]
  exact MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict
    (μ := volume) (s := Ω) (p := p)
    (f := fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1)) hΩ_meas

private lemma eLpNorm_phi_sub_indicator_eq
    {Ω : Set E} (hΩ_meas : MeasurableSet Ω)
    {φ u : E → ℝ}
    (hφ_sub : tsupport φ ⊆ Ω)
    {p : ℝ≥0∞} :
    eLpNorm (fun x => φ x - Ω.indicator u x) p volume =
      eLpNorm (fun x => φ x - u x) p (volume.restrict Ω) := by
  have hEq :
      (fun x => φ x - Ω.indicator u x) =
        Ω.indicator (fun x => φ x - u x) := by
    funext x
    by_cases hx : x ∈ Ω
    · simp [hx]
    · have hφx : φ x = 0 :=
        Sobolev.Euclidean.zero_outside_of_tsupport_subset (Ω := Ω) hφ_sub hx
      simp [hx, hφx]
  conv_lhs => rw [hEq]
  exact MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict
    (μ := volume) (s := Ω) (p := p) (f := fun x => φ x - u x) hΩ_meas

variable [NeZero d] in
theorem eLpNorm_translate_sub_le_of_memW01p
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    {Ω : Set E} (hΩ_open : IsOpen Ω)
    {u : E → ℝ}
    (hu : Sobolev.Euclidean.MemW01p p u Ω)
    (h : E) :
    eLpNorm (fun x => Ω.indicator u (x - h) - Ω.indicator u x) p volume ≤
      ENNReal.ofReal ‖h‖ *
        ∑ i : Fin d,
          eLpNorm (fun x => (Classical.choose hu.2).weakGrad x i)
            p (volume.restrict Ω) := by
  classical
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  set hw : Sobolev.Euclidean.MemW1pWitness p u Ω := Classical.choose hu.2 with hw_def
  have hSpec := Classical.choose_spec hu.2
  set φ : ℕ → E → ℝ := Classical.choose hSpec with hφ_def
  have hSpec' := Classical.choose_spec hSpec
  have hφ_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n) := hSpec'.1
  have hφ_compact : ∀ n, HasCompactSupport (φ n) := hSpec'.2.1
  have hφ_sub : ∀ n, tsupport (φ n) ⊆ Ω := hSpec'.2.2.1
  have hφ_fun :
      Tendsto (fun n => eLpNorm (fun x => φ n x - u x) p (volume.restrict Ω))
        atTop (nhds 0) := hSpec'.2.2.2.1
  have hφ_grad : ∀ i : Fin d,
      Tendsto
        (fun n => eLpNorm
          (fun x =>
            (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
          p (volume.restrict Ω))
        atTop (nhds 0) := hSpec'.2.2.2.2
  have hu_aesm_restrict :
      AEStronglyMeasurable u (volume.restrict Ω) := hw.memLp.aestronglyMeasurable
  have hu_ind_aesm :
      AEStronglyMeasurable (Ω.indicator u) volume :=
    (aestronglyMeasurable_indicator_iff (μ := volume) hΩ_meas).mpr hu_aesm_restrict
  have hφ_smooth_aesm : ∀ n, AEStronglyMeasurable (φ n) volume :=
    fun n => (hφ_smooth n).continuous.aestronglyMeasurable
  have hφ_to_uExt :
      Tendsto (fun n => eLpNorm (fun x => φ n x - Ω.indicator u x) p volume)
        atTop (nhds 0) := by
    have hEq :
        (fun n => eLpNorm (fun x => φ n x - Ω.indicator u x) p volume) =
          (fun n => eLpNorm (fun x => φ n x - u x) p (volume.restrict Ω)) := by
      funext n
      exact eLpNorm_phi_sub_indicator_eq (d := d) hΩ_meas (hφ_sub n) (φ := φ n) (u := u)
    rw [hEq]
    exact hφ_fun
  set LHS : ℝ≥0∞ :=
    eLpNorm (fun x => Ω.indicator u (x - h) - Ω.indicator u x) p volume with hLHS_def
  set S : ℝ≥0∞ :=
    ∑ i : Fin d,
      eLpNorm (fun x => hw.weakGrad x i) p (volume.restrict Ω) with hS_def
  set Dseq : ℕ → ℝ≥0∞ := fun n =>
    ∑ i : Fin d,
      eLpNorm
        (fun x =>
          (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
        p (volume.restrict Ω) with hDseq_def
  change LHS ≤ ENNReal.ofReal ‖h‖ * S
  have hTri : ∀ n : ℕ,
      LHS ≤
        eLpNorm (fun x => Ω.indicator u (x - h) - φ n (x - h)) p volume +
          eLpNorm (fun x => φ n (x - h) - φ n x) p volume +
          eLpNorm (fun x => φ n x - Ω.indicator u x) p volume := by
    intro n
    have hDecomp :
        (fun x => Ω.indicator u (x - h) - Ω.indicator u x) =
          (fun x => Ω.indicator u (x - h) - φ n (x - h)) +
            ((fun x => φ n (x - h) - φ n x) +
              (fun x => φ n x - Ω.indicator u x)) := by
      funext x
      change _ = (Ω.indicator u (x - h) - φ n (x - h)) +
        ((φ n (x - h) - φ n x) + (φ n x - Ω.indicator u x))
      ring
    have hLHS_eq :
        LHS = eLpNorm
            ((fun x => Ω.indicator u (x - h) - φ n (x - h)) +
                ((fun x => φ n (x - h) - φ n x) +
                  (fun x => φ n x - Ω.indicator u x))) p volume := by
      rw [hLHS_def, hDecomp]
    rw [hLHS_eq]
    calc
      eLpNorm
          ((fun x => Ω.indicator u (x - h) - φ n (x - h)) +
            ((fun x => φ n (x - h) - φ n x) +
              (fun x => φ n x - Ω.indicator u x))) p volume
          ≤
        eLpNorm (fun x => Ω.indicator u (x - h) - φ n (x - h)) p volume +
          eLpNorm
            ((fun x => φ n (x - h) - φ n x) +
              (fun x => φ n x - Ω.indicator u x)) p volume :=
        eLpNorm_add_le hp_one
      _ ≤ eLpNorm (fun x => Ω.indicator u (x - h) - φ n (x - h)) p volume +
            (eLpNorm (fun x => φ n (x - h) - φ n x) p volume +
              eLpNorm (fun x => φ n x - Ω.indicator u x) p volume) := by
              gcongr
              exact eLpNorm_add_le hp_one
      _ = _ := by ring
  have hA_to_zero :
      Tendsto
        (fun n => eLpNorm (fun x => Ω.indicator u (x - h) - φ n (x - h)) p volume)
        atTop (nhds 0) := by
    have hEq_each :
        ∀ n,
          eLpNorm (fun x => Ω.indicator u (x - h) - φ n (x - h)) p volume =
            eLpNorm (fun x => φ n x - Ω.indicator u x) p volume := by
      intro n
      have hSM : AEStronglyMeasurable (fun x : E => Ω.indicator u x - φ n x) volume :=
        hu_ind_aesm.sub (hφ_smooth_aesm n)
      have hTrEq :
          eLpNorm (fun x => Ω.indicator u (x - h) - φ n (x - h)) p volume =
            eLpNorm (fun x => Ω.indicator u x - φ n x) p volume :=
        eLpNorm_translate_eq (p := p) hSM h
      have hSign :
          eLpNorm (fun x => Ω.indicator u x - φ n x) p volume =
            eLpNorm (fun x => φ n x - Ω.indicator u x) p volume :=
        eLpNorm_sub_comm (μ := volume) (p := p) (f := Ω.indicator u) (g := φ n)
      rw [hTrEq, hSign]
    rw [show
        (fun n => eLpNorm (fun x => Ω.indicator u (x - h) - φ n (x - h)) p volume) =
        (fun n => eLpNorm (fun x => φ n x - Ω.indicator u x) p volume)
      from funext hEq_each]
    exact hφ_to_uExt
  have hStepA : ∀ n,
      eLpNorm (fun x => φ n (x - h) - φ n x) p volume ≤
        ENNReal.ofReal ‖h‖ *
          ∑ i : Fin d,
            eLpNorm (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1))
              p volume :=
    fun n =>
      eLpNorm_translate_sub_le_sum_components hp_one hp_top (hφ_smooth n) h
  have hgrad_eLp_eq :
      ∀ n i,
        eLpNorm (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1)) p volume =
          eLpNorm (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1)) p
            (volume.restrict Ω) := by
    intro n i
    exact eLpNorm_grad_eq_restrict (d := d) hΩ_meas (hφ_sub n) i
  have hgrad_triangle : ∀ n i,
      eLpNorm (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1)) p
          (volume.restrict Ω) ≤
        eLpNorm
            (fun x =>
              (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
            p (volume.restrict Ω) +
          eLpNorm (fun x => hw.weakGrad x i) p (volume.restrict Ω) := by
    intro n i
    have hEq :
        (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1)) =
          (fun x =>
              ((fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i) +
                hw.weakGrad x i) := by
      funext x; ring
    rw [hEq]
    exact eLpNorm_add_le hp_one
  have hB_bound : ∀ n,
      eLpNorm (fun x => φ n (x - h) - φ n x) p volume ≤
        ENNReal.ofReal ‖h‖ * (Dseq n + S) := by
    intro n
    refine (hStepA n).trans ?_
    have hEq_sum :
        ∑ i : Fin d,
            eLpNorm (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1))
              p volume =
          ∑ i : Fin d,
            eLpNorm (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1))
              p (volume.restrict Ω) := by
      apply Finset.sum_congr rfl
      intros i _
      exact hgrad_eLp_eq n i
    rw [hEq_sum]
    have hsum_le :
        ∑ i : Fin d,
            eLpNorm (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1))
              p (volume.restrict Ω) ≤
          Dseq n + S := by
      rw [hDseq_def, hS_def]
      rw [show (∑ i : Fin d,
                eLpNorm (fun x =>
                    (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
                  p (volume.restrict Ω)) +
              ∑ i : Fin d,
                eLpNorm (fun x => hw.weakGrad x i) p (volume.restrict Ω) =
            ∑ i : Fin d,
              (eLpNorm (fun x =>
                (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
                p (volume.restrict Ω) +
                eLpNorm (fun x => hw.weakGrad x i) p (volume.restrict Ω)) from
              (Finset.sum_add_distrib).symm]
      refine Finset.sum_le_sum ?_
      intros i _
      exact hgrad_triangle n i
    gcongr
  have hLHS_le : ∀ n,
      LHS ≤
        eLpNorm (fun x => Ω.indicator u (x - h) - φ n (x - h)) p volume +
          ENNReal.ofReal ‖h‖ * (Dseq n + S) +
          eLpNorm (fun x => φ n x - Ω.indicator u x) p volume := by
    intro n
    refine (hTri n).trans ?_
    gcongr
    exact hB_bound n
  have hC_to_zero :
      Tendsto (fun n => eLpNorm (fun x => φ n x - Ω.indicator u x) p volume)
        atTop (nhds 0) := hφ_to_uExt
  have hD_to_zero : Tendsto Dseq atTop (nhds 0) := by
    have hsum_zero :
        Tendsto Dseq atTop (nhds (∑ _i : Fin d, (0 : ℝ≥0∞))) := by
      rw [hDseq_def]
      exact tendsto_finsetSum (Finset.univ : Finset (Fin d)) (fun i _ => hφ_grad i)
    simpa using hsum_zero
  have h_mul_tendsto :
      Tendsto (fun n => ENNReal.ofReal ‖h‖ * (Dseq n + S))
        atTop (nhds (ENNReal.ofReal ‖h‖ * S)) := by
    have hadd : Tendsto (fun n => Dseq n + S) atTop (nhds (0 + S)) :=
      hD_to_zero.add tendsto_const_nhds
    have h_zero_add : (0 : ℝ≥0∞) + S = S := by simp
    rw [show (ENNReal.ofReal ‖h‖ * S) = ENNReal.ofReal ‖h‖ * (0 + S) by rw [h_zero_add]]
    exact ENNReal.Tendsto.const_mul hadd (Or.inr ENNReal.ofReal_ne_top)
  have h_sum_tendsto :
      Tendsto
        (fun n =>
          eLpNorm (fun x => Ω.indicator u (x - h) - φ n (x - h)) p volume +
            ENNReal.ofReal ‖h‖ * (Dseq n + S) +
            eLpNorm (fun x => φ n x - Ω.indicator u x) p volume)
        atTop (nhds (ENNReal.ofReal ‖h‖ * S)) := by
    have h1 :
        Tendsto
          (fun n =>
            eLpNorm (fun x => Ω.indicator u (x - h) - φ n (x - h)) p volume +
              ENNReal.ofReal ‖h‖ * (Dseq n + S))
          atTop (nhds (0 + ENNReal.ofReal ‖h‖ * S)) :=
      hA_to_zero.add h_mul_tendsto
    have h2 :
        Tendsto
          (fun n =>
            eLpNorm (fun x => Ω.indicator u (x - h) - φ n (x - h)) p volume +
              ENNReal.ofReal ‖h‖ * (Dseq n + S) +
              eLpNorm (fun x => φ n x - Ω.indicator u x) p volume)
          atTop (nhds (0 + ENNReal.ofReal ‖h‖ * S + 0)) :=
      h1.add hC_to_zero
    simpa using h2
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds h_sum_tendsto hLHS_le

private lemma isCompact_closure_of_bounded
    {Ω : Set E} (hΩ_bdd : Bornology.IsBounded Ω) :
    IsCompact (closure Ω) :=
  hΩ_bdd.isCompact_closure

private lemma indicator_support_subset_closure
    {Ω : Set E} {u : E → ℝ} (x : E) (hx : x ∉ closure Ω) :
    Ω.indicator u x = 0 := by
  rw [Set.indicator_of_notMem]
  intro hxΩ
  exact hx (subset_closure hxΩ)

variable [NeZero d] in
theorem rellich_kondrachov_W01p_seq
    {Ω : Set E}
    (hΩ_open : IsOpen Ω) (hΩ_bdd : Bornology.IsBounded Ω)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    {u : ℕ → E → ℝ}
    (hu_mem : ∀ n, Sobolev.Euclidean.MemW01p p (u n) Ω)
    {R : ℝ}
    (hu_bdd_fun : ∀ n, eLpNorm (u n) p (volume.restrict Ω) ≤ ENNReal.ofReal R)
    (hu_bdd_grad : ∀ n,
      ∑ i : Fin d,
        eLpNorm (fun x => (Classical.choose (hu_mem n).2).weakGrad x i)
          p (volume.restrict Ω) ≤ ENNReal.ofReal R) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ u_lim : E → ℝ,
        MeasureTheory.MemLp u_lim p (volume.restrict Ω) ∧
        Filter.Tendsto
          (fun k => eLpNorm (fun x => u (φ k) x - u_lim x) p (volume.restrict Ω))
          Filter.atTop (𝓝 0) := by
  classical
  set K : Set E := closure Ω with hK_def
  have hK_compact : IsCompact K := isCompact_closure_of_bounded (d := d) hΩ_bdd
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  set u_ext : ℕ → E → ℝ := fun n => Ω.indicator (u n) with hu_ext_def
  have hu_ext_support : ∀ n, ∀ x, x ∉ K → u_ext n x = 0 := by
    intro n x hx
    rw [hu_ext_def]
    exact indicator_support_subset_closure (d := d) x hx
  have hu_ext_memLp : ∀ n, MemLp (u_ext n) p volume := by
    intro n
    have h_iff := MeasureTheory.memLp_indicator_iff_restrict (μ := volume) (s := Ω)
      (f := u n) (p := p) hΩ_meas
    rw [hu_ext_def]
    exact h_iff.mpr ((hu_mem n).1).1
  have hu_ext_eLp : ∀ n,
      eLpNorm (u_ext n) p volume = eLpNorm (u n) p (volume.restrict Ω) := by
    intro n
    rw [hu_ext_def]
    exact MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict (μ := volume) (s := Ω)
      (f := u n) (p := p) hΩ_meas
  have hu_ext_bdd : ∀ n, eLpNorm (u_ext n) p volume ≤ ENNReal.ofReal R := by
    intro n
    rw [hu_ext_eLp n]
    exact hu_bdd_fun n
  have hu_ext_translation :
      ∀ ε > 0, ∃ δ > 0, ∀ n, ∀ h : E, ‖h‖ < δ →
        eLpNorm (fun x => u_ext n (x - h) - u_ext n x) p volume ≤
          ENNReal.ofReal ε := by
    intro ε hε
    refine ⟨ε / (max R 0 + 1), ?_, ?_⟩
    · positivity
    intro n h hh
    have hPhB := eLpNorm_translate_sub_le_of_memW01p (d := d) hp_one hp_top
      hΩ_open (hu_mem n) h
    have hgrad := hu_bdd_grad n
    have hPhB' : eLpNorm (fun x => u_ext n (x - h) - u_ext n x) p volume ≤
        ENNReal.ofReal ‖h‖ * ENNReal.ofReal R := by
      refine hPhB.trans ?_
      exact mul_le_mul' le_rfl hgrad
    have hR_le_max : (R : ℝ) ≤ max R 0 := le_max_left R 0
    have h2 : ENNReal.ofReal ‖h‖ * ENNReal.ofReal R ≤
        ENNReal.ofReal ‖h‖ * ENNReal.ofReal (max R 0) :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hR_le_max)
    have hmaxR_nn : 0 ≤ max R 0 := le_max_right R 0
    have hdelta_pos : 0 < (max R 0 + 1) := by linarith
    have hh_le : ‖h‖ ≤ ε / (max R 0 + 1) := hh.le
    have hh_nn : 0 ≤ ‖h‖ := norm_nonneg _
    have h3 : ‖h‖ * max R 0 ≤ ε := by
      have h3a : ‖h‖ * max R 0 ≤ ‖h‖ * (max R 0 + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hh_nn
      have h3b : ‖h‖ * (max R 0 + 1) ≤ ε := by
        rw [show (ε : ℝ) = ε / (max R 0 + 1) * (max R 0 + 1) from
          (div_mul_cancel₀ ε hdelta_pos.ne').symm]
        exact mul_le_mul_of_nonneg_right hh_le (by linarith)
      linarith
    have h4 : ENNReal.ofReal ‖h‖ * ENNReal.ofReal (max R 0) ≤ ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_mul hh_nn]
      exact ENNReal.ofReal_le_ofReal h3
    exact hPhB'.trans (h2.trans h4)
  rcases tendsto_subseq_of_uniform_translation_in_Lp (d := d)
    hp_one hp_top hK_compact hu_ext_memLp hu_ext_support hu_ext_bdd hu_ext_translation with
    ⟨φ, hφ_mono, u_lim_v, hu_lim_v_memLp, h_tendsto_v⟩
  refine ⟨φ, hφ_mono, u_lim_v, hu_lim_v_memLp.restrict Ω, ?_⟩
  have hSqueeze : ∀ k,
      eLpNorm (fun x => u (φ k) x - u_lim_v x) p (volume.restrict Ω) ≤
        eLpNorm (fun x => u_ext (φ k) x - u_lim_v x) p volume := by
    intro k
    have h_cong : ∀ᵐ x ∂(volume.restrict Ω),
        u (φ k) x - u_lim_v x = u_ext (φ k) x - u_lim_v x := by
      filter_upwards [self_mem_ae_restrict hΩ_meas] with x hx
      simp [hu_ext_def, Set.indicator_of_mem hx]
    have h_eq : eLpNorm (fun x => u (φ k) x - u_lim_v x) p (volume.restrict Ω) =
        eLpNorm (fun x => u_ext (φ k) x - u_lim_v x) p (volume.restrict Ω) :=
      eLpNorm_congr_ae h_cong
    rw [h_eq]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  refine ENNReal.tendsto_atTop_zero.mpr ?_
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero] at h_tendsto_v
  rcases h_tendsto_v ε hε with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  exact (hSqueeze n).trans (hN n hn)

end Sobolev
