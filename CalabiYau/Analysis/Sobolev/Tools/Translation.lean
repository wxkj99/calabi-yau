-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Tools/Translation.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Euclidean.W1p.Approximation

@[expose] public section


noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open scoped ENNReal NNReal Convolution Pointwise

namespace Sobolev

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem sub_translate_eq_integral_fderiv
    {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ) (x h : E) :
    φ x - φ (x - h) =
      ∫ s in Set.Ioc (0 : ℝ) 1, (fderiv ℝ φ (x - h + s • h)) h := by
  have hφ_diff : Differentiable ℝ φ := hφ.differentiable_one
  set γ : ℝ → E := fun t => x - h + t • h with hγ_def
  have hγ_deriv : ∀ t, HasDerivAt γ h t := by
    intro t
    have hsmul : HasDerivAt (fun s : ℝ => s • h) h t := by
      simpa using (hasDerivAt_id t).smul_const h
    have hadd : HasDerivAt (fun s : ℝ => (x - h) + s • h) h t :=
      hsmul.const_add (x - h)
    simpa [γ, add_comm] using hadd
  have hcomp : ∀ t, HasDerivAt (φ ∘ γ) ((fderiv ℝ φ (γ t)) h) t := by
    intro t
    have hφ_at : HasFDerivAt φ (fderiv ℝ φ (γ t)) (γ t) :=
      (hφ_diff (γ t)).hasFDerivAt
    exact hφ_at.comp_hasDerivAt t (hγ_deriv t)
  have hderiv_cont :
      Continuous (fun s : ℝ => (fderiv ℝ φ (γ s)) h) := by
    have hγ_cont : Continuous γ :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hfderiv_cont : Continuous (fun s : ℝ => fderiv ℝ φ (γ s)) :=
      (hφ.continuous_fderiv one_ne_zero).comp hγ_cont
    exact hfderiv_cont.clm_apply continuous_const
  have hftc :
      ∫ s in (0 : ℝ)..1, (fderiv ℝ φ (γ s)) h =
        (φ ∘ γ) 1 - (φ ∘ γ) 0 := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := φ ∘ γ) (f' := fun t => (fderiv ℝ φ (γ t)) h)
      (a := 0) (b := 1) (fun t _ => hcomp t) ?_
    exact hderiv_cont.intervalIntegrable _ _
  have hγ0 : γ 0 = x - h := by simp [γ]
  have hγ1 : γ 1 = x := by simp [γ]
  have hint :
      ∫ s in (0 : ℝ)..1, (fderiv ℝ φ (γ s)) h =
        ∫ s in Set.Ioc (0 : ℝ) 1, (fderiv ℝ φ (γ s)) h := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  calc
    φ x - φ (x - h)
        = (φ ∘ γ) 1 - (φ ∘ γ) 0 := by simp [Function.comp, hγ0, hγ1]
    _ = ∫ s in (0 : ℝ)..1, (fderiv ℝ φ (γ s)) h := hftc.symm
    _ = ∫ s in Set.Ioc (0 : ℝ) 1, (fderiv ℝ φ (γ s)) h := hint

private theorem rpow_abs_sub_translate_le
    {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ)
    {p : ℝ} (hp_one : 1 ≤ p) (x h : E) :
    |φ x - φ (x - h)| ^ p ≤
      ‖h‖ ^ p *
        ∫ s in Set.Ioc (0 : ℝ) 1, ‖fderiv ℝ φ (x - h + s • h)‖ ^ p := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp_one
  have hrep := sub_translate_eq_integral_fderiv (d := d) hφ x h
  set γ : ℝ → E := fun t => x - h + t • h with hγ_def
  have hγ_cont : Continuous γ :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hfderiv_cont : Continuous (fun s : ℝ => fderiv ℝ φ (γ s)) :=
    (hφ.continuous_fderiv one_ne_zero).comp hγ_cont
  have hnorm_cont :
      Continuous (fun s : ℝ => ‖fderiv ℝ φ (γ s)‖) :=
    hfderiv_cont.norm
  have h_int_norm :
      ‖∫ s in Set.Ioc (0 : ℝ) 1, (fderiv ℝ φ (γ s)) h‖ ≤
        ∫ s in Set.Ioc (0 : ℝ) 1, ‖(fderiv ℝ φ (γ s)) h‖ := by
    simpa using
      (norm_integral_le_integral_norm
        (μ := (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1))
        (f := fun s => (fderiv ℝ φ (γ s)) h))
  have h_op_le :
      ∀ s, ‖(fderiv ℝ φ (γ s)) h‖ ≤ ‖fderiv ℝ φ (γ s)‖ * ‖h‖ :=
    fun s => (fderiv ℝ φ (γ s)).le_opNorm h
  have hmul_cont :
      Continuous (fun s : ℝ => ‖fderiv ℝ φ (γ s)‖ * ‖h‖) :=
    hnorm_cont.mul continuous_const
  have hmul_int_on :
      IntegrableOn (fun s : ℝ => ‖fderiv ℝ φ (γ s)‖ * ‖h‖)
        (Set.Ioc (0 : ℝ) 1) volume :=
    hmul_cont.integrableOn_Ioc (a := 0) (b := 1)
  have hopcont :
      Continuous (fun s : ℝ => ‖(fderiv ℝ φ (γ s)) h‖) :=
    (hfderiv_cont.clm_apply continuous_const).norm
  have hop_int_on :
      IntegrableOn (fun s : ℝ => ‖(fderiv ℝ φ (γ s)) h‖)
        (Set.Ioc (0 : ℝ) 1) volume :=
    hopcont.integrableOn_Ioc (a := 0) (b := 1)
  have h_int_op :
      ∫ s in Set.Ioc (0 : ℝ) 1, ‖(fderiv ℝ φ (γ s)) h‖ ≤
        ∫ s in Set.Ioc (0 : ℝ) 1, ‖fderiv ℝ φ (γ s)‖ * ‖h‖ := by
    refine integral_mono_ae ?_ ?_ ?_
    · exact hop_int_on
    · exact hmul_int_on
    · filter_upwards with s using h_op_le s
  have h_pull :
      ∫ s in Set.Ioc (0 : ℝ) 1, ‖fderiv ℝ φ (γ s)‖ * ‖h‖ =
        (∫ s in Set.Ioc (0 : ℝ) 1, ‖fderiv ℝ φ (γ s)‖) * ‖h‖ := by
    simp [integral_mul_const]
  have hbound :
      |φ x - φ (x - h)| ≤
        ‖h‖ * ∫ s in Set.Ioc (0 : ℝ) 1, ‖fderiv ℝ φ (γ s)‖ := by
    calc
      |φ x - φ (x - h)|
          = ‖φ x - φ (x - h)‖ := (Real.norm_eq_abs _).symm
      _ = ‖∫ s in Set.Ioc (0 : ℝ) 1, (fderiv ℝ φ (γ s)) h‖ := by rw [hrep]
      _ ≤ ∫ s in Set.Ioc (0 : ℝ) 1, ‖(fderiv ℝ φ (γ s)) h‖ := h_int_norm
      _ ≤ ∫ s in Set.Ioc (0 : ℝ) 1, ‖fderiv ℝ φ (γ s)‖ * ‖h‖ := h_int_op
      _ = (∫ s in Set.Ioc (0 : ℝ) 1, ‖fderiv ℝ φ (γ s)‖) * ‖h‖ := h_pull
      _ = ‖h‖ * ∫ s in Set.Ioc (0 : ℝ) 1, ‖fderiv ℝ φ (γ s)‖ := by ring
  have hfn_nonneg :
      0 ≤
        ∫ s in Set.Ioc (0 : ℝ) 1, ‖fderiv ℝ φ (γ s)‖ := by
    refine integral_nonneg ?_
    intro s
    exact norm_nonneg _
  have habs_nn : 0 ≤ |φ x - φ (x - h)| := abs_nonneg _
  have hb_pow :
      |φ x - φ (x - h)| ^ p ≤
        (‖h‖ * ∫ s in Set.Ioc (0 : ℝ) 1, ‖fderiv ℝ φ (γ s)‖) ^ p :=
    Real.rpow_le_rpow habs_nn hbound hp_pos.le
  have hJensen :
      (∫ s in Set.Ioc (0 : ℝ) 1, ‖fderiv ℝ φ (γ s)‖) ^ p ≤
        ∫ s in Set.Ioc (0 : ℝ) 1, ‖fderiv ℝ φ (γ s)‖ ^ p := by
    have hμprob :
        IsProbabilityMeasure
          ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp [Real.volume_Ioc]
    have hconv : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun t : ℝ => t ^ p) :=
      convexOn_rpow hp_one
    have hcont_on :
        ContinuousOn (fun t : ℝ => t ^ p) (Set.Ici (0 : ℝ)) :=
      continuousOn_id.rpow_const (by intro t _; exact Or.inr hp_pos.le)
    have hf_int :
        Integrable (fun s : ℝ => ‖fderiv ℝ φ (γ s)‖)
          ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) :=
      hnorm_cont.integrableOn_Ioc (a := 0) (b := 1)
    have hgf_int :
        Integrable
          (fun s : ℝ => ‖fderiv ℝ φ (γ s)‖ ^ p)
          ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) := by
      have hcont :
          Continuous
            (fun s : ℝ => ‖fderiv ℝ φ (γ s)‖ ^ p) :=
        hnorm_cont.rpow_const (fun _ => Or.inr hp_pos.le)
      exact hcont.integrableOn_Ioc (a := 0) (b := 1)
    have hfs :
        ∀ᵐ s : ℝ ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)),
          ‖fderiv ℝ φ (γ s)‖ ∈ Set.Ici (0 : ℝ) := by
      filter_upwards with s
      exact norm_nonneg _
    exact hconv.map_integral_le hcont_on isClosed_Ici hfs hf_int hgf_int
  calc
    |φ x - φ (x - h)| ^ p
        ≤ (‖h‖ * ∫ s in Set.Ioc (0 : ℝ) 1, ‖fderiv ℝ φ (γ s)‖) ^ p := hb_pow
    _ = ‖h‖ ^ p *
          (∫ s in Set.Ioc (0 : ℝ) 1, ‖fderiv ℝ φ (γ s)‖) ^ p := by
          rw [Real.mul_rpow (norm_nonneg _) hfn_nonneg]
    _ ≤ ‖h‖ ^ p *
          ∫ s in Set.Ioc (0 : ℝ) 1, ‖fderiv ℝ φ (γ s)‖ ^ p := by
          have hh_pow_nn : 0 ≤ ‖h‖ ^ p :=
            Real.rpow_nonneg (norm_nonneg _) p
          exact mul_le_mul_of_nonneg_left hJensen hh_pow_nn

private theorem lintegral_rpow_translate_sub_le
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    {pr : ℝ} (hpr_ge_one : 1 ≤ pr) (h : E) :
    ∫⁻ x : E, (‖φ x - φ (x - h)‖ₑ : ℝ≥0∞) ^ pr ≤
      ENNReal.ofReal ‖h‖ ^ pr *
        ∫⁻ x : E, (‖fderiv ℝ φ x‖ₑ : ℝ≥0∞) ^ pr := by
  classical
  have hpr_pos : 0 < pr := lt_of_lt_of_le zero_lt_one hpr_ge_one
  have hφ_C1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_cast)
  have hφ_diff : Differentiable ℝ φ := hφ_C1.differentiable_one
  have hφ_cont : Continuous φ := hφ_diff.continuous
  have hφ_fderiv_cont : Continuous (fun x => fderiv ℝ φ x) :=
    hφ_C1.continuous_fderiv one_ne_zero
  have hφ_fderiv_norm_cont : Continuous (fun x => ‖fderiv ℝ φ x‖) :=
    hφ_fderiv_cont.norm
  have hfderiv_norm_meas : Measurable (fun x : E => ‖fderiv ℝ φ x‖) :=
    hφ_fderiv_norm_cont.measurable
  have hPointwise :
      ∀ x : E,
        |φ x - φ (x - h)| ^ pr ≤
          ‖h‖ ^ pr *
            ∫ s in Set.Ioc (0 : ℝ) 1, ‖fderiv ℝ φ (x - h + s • h)‖ ^ pr :=
    fun x => rpow_abs_sub_translate_le (d := d) hφ_C1 hpr_ge_one x h
  have hPtENN :
      ∀ x : E,
        (‖φ x - φ (x - h)‖ₑ : ℝ≥0∞) ^ pr ≤
          ENNReal.ofReal ‖h‖ ^ pr *
            ∫⁻ s in Set.Ioc (0 : ℝ) 1,
              (‖fderiv ℝ φ (x - h + s • h)‖ₑ : ℝ≥0∞) ^ pr := by
    intro x
    have hreal := hPointwise x
    have h_lhs :
        (‖φ x - φ (x - h)‖ₑ : ℝ≥0∞) ^ pr =
          ENNReal.ofReal (|φ x - φ (x - h)| ^ pr) := by
      rw [Real.enorm_eq_ofReal_abs,
        ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hpr_pos.le]
    have hrhs_real_nn :
        0 ≤ ‖h‖ ^ pr *
          ∫ s in Set.Ioc (0 : ℝ) 1, ‖fderiv ℝ φ (x - h + s • h)‖ ^ pr := by
      refine mul_nonneg (Real.rpow_nonneg (norm_nonneg _) pr) ?_
      refine integral_nonneg ?_
      intro s
      exact Real.rpow_nonneg (norm_nonneg _) pr
    have htrans :
        ENNReal.ofReal (|φ x - φ (x - h)| ^ pr) ≤
          ENNReal.ofReal (‖h‖ ^ pr *
            ∫ s in Set.Ioc (0 : ℝ) 1, ‖fderiv ℝ φ (x - h + s • h)‖ ^ pr) :=
      ENNReal.ofReal_le_ofReal hreal
    have hrhs_expand :
        ENNReal.ofReal (‖h‖ ^ pr *
            ∫ s in Set.Ioc (0 : ℝ) 1, ‖fderiv ℝ φ (x - h + s • h)‖ ^ pr) =
          ENNReal.ofReal ‖h‖ ^ pr *
            ENNReal.ofReal
              (∫ s in Set.Ioc (0 : ℝ) 1,
                ‖fderiv ℝ φ (x - h + s • h)‖ ^ pr) := by
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) pr)]
      congr 1
      rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hpr_pos.le]
    have hint :
        Integrable (fun s : ℝ => ‖fderiv ℝ φ (x - h + s • h)‖ ^ pr)
          ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) := by
      have hγ_cont : Continuous (fun s : ℝ => x - h + s • h) :=
        continuous_const.add (continuous_id.smul continuous_const)
      have hcont :
          Continuous (fun s : ℝ => ‖fderiv ℝ φ (x - h + s • h)‖ ^ pr) :=
        ((hφ_fderiv_cont.comp hγ_cont).norm).rpow_const
          (fun _ => Or.inr hpr_pos.le)
      exact hcont.integrableOn_Ioc (a := 0) (b := 1)
    have heq_pt :
        ∀ s : ℝ,
          (‖fderiv ℝ φ (x - h + s • h)‖ₑ : ℝ≥0∞) ^ pr =
            ENNReal.ofReal (‖fderiv ℝ φ (x - h + s • h)‖ ^ pr) := by
      intro s
      rw [← ofReal_norm,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hpr_pos.le]
    have hint_eq :
        ENNReal.ofReal
            (∫ s in Set.Ioc (0 : ℝ) 1,
              ‖fderiv ℝ φ (x - h + s • h)‖ ^ pr) =
          ∫⁻ s in Set.Ioc (0 : ℝ) 1,
            (‖fderiv ℝ φ (x - h + s • h)‖ₑ : ℝ≥0∞) ^ pr := by
      rw [ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun s =>
          Real.rpow_nonneg (norm_nonneg _) pr)]
      refine lintegral_congr_ae ?_
      filter_upwards with s
      exact (heq_pt s).symm
    calc
      (‖φ x - φ (x - h)‖ₑ : ℝ≥0∞) ^ pr
          = ENNReal.ofReal (|φ x - φ (x - h)| ^ pr) := h_lhs
      _ ≤ ENNReal.ofReal (‖h‖ ^ pr *
            ∫ s in Set.Ioc (0 : ℝ) 1,
              ‖fderiv ℝ φ (x - h + s • h)‖ ^ pr) := htrans
      _ = ENNReal.ofReal ‖h‖ ^ pr *
            ENNReal.ofReal
              (∫ s in Set.Ioc (0 : ℝ) 1,
                ‖fderiv ℝ φ (x - h + s • h)‖ ^ pr) := hrhs_expand
      _ = ENNReal.ofReal ‖h‖ ^ pr *
            ∫⁻ s in Set.Ioc (0 : ℝ) 1,
              (‖fderiv ℝ φ (x - h + s • h)‖ₑ : ℝ≥0∞) ^ pr := by
            rw [hint_eq]
  have hMeas_pair :
      Measurable
        (Function.uncurry
          fun (x : E) (s : ℝ) =>
            (‖fderiv ℝ φ (x - h + s • h)‖ₑ : ℝ≥0∞) ^ pr) := by
    have hp1 : Measurable (fun p : E × ℝ => p.1) := measurable_fst
    have hp2 : Measurable (fun p : E × ℝ => p.2) := measurable_snd
    have hp1' : Measurable (fun p : E × ℝ => p.1 - h) := hp1.sub_const _
    have hp2' : Measurable (fun p : E × ℝ => p.2 • h) :=
      hp2.smul measurable_const
    have hpos : Measurable (fun p : E × ℝ => p.1 - h + p.2 • h) :=
      hp1'.add hp2'
    have hfd_meas : Measurable (fun x : E => fderiv ℝ φ x) :=
      hφ_fderiv_cont.measurable
    have hcomp_meas :
        Measurable (fun p : E × ℝ => fderiv ℝ φ (p.1 - h + p.2 • h)) :=
      hfd_meas.comp hpos
    have henorm :
        Measurable (fun p : E × ℝ =>
          (‖fderiv ℝ φ (p.1 - h + p.2 • h)‖ₑ : ℝ≥0∞)) :=
      hcomp_meas.enorm
    exact henorm.pow_const pr
  have h_lhs_bound :
      ∫⁻ x : E, (‖φ x - φ (x - h)‖ₑ : ℝ≥0∞) ^ pr ≤
        ∫⁻ x : E,
          ENNReal.ofReal ‖h‖ ^ pr *
            ∫⁻ s in Set.Ioc (0 : ℝ) 1,
              (‖fderiv ℝ φ (x - h + s • h)‖ₑ : ℝ≥0∞) ^ pr := by
    refine lintegral_mono_ae ?_
    filter_upwards with x
    exact hPtENN x
  have h_lhs_step :
      ∫⁻ x : E,
        ENNReal.ofReal ‖h‖ ^ pr *
          ∫⁻ s in Set.Ioc (0 : ℝ) 1,
            (‖fderiv ℝ φ (x - h + s • h)‖ₑ : ℝ≥0∞) ^ pr =
      ENNReal.ofReal ‖h‖ ^ pr *
        ∫⁻ x : E,
          ∫⁻ s in Set.Ioc (0 : ℝ) 1,
            (‖fderiv ℝ φ (x - h + s • h)‖ₑ : ℝ≥0∞) ^ pr := by
    rw [lintegral_const_mul']
    exact ENNReal.rpow_ne_top_of_nonneg hpr_pos.le ENNReal.ofReal_ne_top
  have hTonelli :
      ∫⁻ x : E,
          ∫⁻ s in Set.Ioc (0 : ℝ) 1,
            (‖fderiv ℝ φ (x - h + s • h)‖ₑ : ℝ≥0∞) ^ pr =
        ∫⁻ s in Set.Ioc (0 : ℝ) 1,
          ∫⁻ x : E,
            (‖fderiv ℝ φ (x - h + s • h)‖ₑ : ℝ≥0∞) ^ pr := by
    exact lintegral_lintegral_swap hMeas_pair.aemeasurable
  have hTransLint :
      ∀ s : ℝ,
        ∫⁻ x : E, (‖fderiv ℝ φ (x - h + s • h)‖ₑ : ℝ≥0∞) ^ pr =
          ∫⁻ x : E, (‖fderiv ℝ φ x‖ₑ : ℝ≥0∞) ^ pr := by
    intro s
    set y : E := -h + s • h with hy_def
    have hMP_y : MeasurePreserving (fun x : E => x + y) volume volume :=
      measurePreserving_add_right volume y
    have heq :
        ∀ x : E,
          (‖fderiv ℝ φ (x - h + s • h)‖ₑ : ℝ≥0∞) ^ pr =
            (‖fderiv ℝ φ (x + y)‖ₑ : ℝ≥0∞) ^ pr := by
      intro x
      congr 2
      simp [y, sub_eq_add_neg, add_comm, add_left_comm]
    have hcongr :
        (fun x : E => (‖fderiv ℝ φ (x - h + s • h)‖ₑ : ℝ≥0∞) ^ pr) =
          (fun x : E => (‖fderiv ℝ φ (x + y)‖ₑ : ℝ≥0∞) ^ pr) := by
      funext x
      exact heq x
    rw [hcongr]
    have hf_meas : Measurable (fun x : E => (‖fderiv ℝ φ x‖ₑ : ℝ≥0∞) ^ pr) :=
      hφ_fderiv_cont.measurable.enorm.pow_const pr
    exact hMP_y.lintegral_comp hf_meas
  have hVol_unit :
      (volume : Measure ℝ) (Set.Ioc (0 : ℝ) 1) = 1 := by
    simp [Real.volume_Ioc]
  have hPostSwap :
      ∫⁻ s in Set.Ioc (0 : ℝ) 1,
        ∫⁻ x : E, (‖fderiv ℝ φ (x - h + s • h)‖ₑ : ℝ≥0∞) ^ pr =
      ∫⁻ x : E, (‖fderiv ℝ φ x‖ₑ : ℝ≥0∞) ^ pr := by
    have hcongr :
        (fun s : ℝ =>
          ∫⁻ x : E, (‖fderiv ℝ φ (x - h + s • h)‖ₑ : ℝ≥0∞) ^ pr) =
        (fun _ => ∫⁻ x : E, (‖fderiv ℝ φ x‖ₑ : ℝ≥0∞) ^ pr) := by
      funext s
      exact hTransLint s
    rw [hcongr]
    rw [lintegral_const]
    rw [Measure.restrict_apply MeasurableSet.univ]
    simp [hVol_unit]
  calc
    ∫⁻ x : E, (‖φ x - φ (x - h)‖ₑ : ℝ≥0∞) ^ pr
        ≤
      ∫⁻ x : E,
        ENNReal.ofReal ‖h‖ ^ pr *
          ∫⁻ s in Set.Ioc (0 : ℝ) 1,
            (‖fderiv ℝ φ (x - h + s • h)‖ₑ : ℝ≥0∞) ^ pr := h_lhs_bound
    _ = ENNReal.ofReal ‖h‖ ^ pr *
          ∫⁻ x : E,
            ∫⁻ s in Set.Ioc (0 : ℝ) 1,
              (‖fderiv ℝ φ (x - h + s • h)‖ₑ : ℝ≥0∞) ^ pr := h_lhs_step
    _ = ENNReal.ofReal ‖h‖ ^ pr *
          ∫⁻ s in Set.Ioc (0 : ℝ) 1,
            ∫⁻ x : E,
              (‖fderiv ℝ φ (x - h + s • h)‖ₑ : ℝ≥0∞) ^ pr := by
          rw [hTonelli]
    _ = ENNReal.ofReal ‖h‖ ^ pr *
          ∫⁻ x : E, (‖fderiv ℝ φ x‖ₑ : ℝ≥0∞) ^ pr := by
          rw [hPostSwap]

theorem eLpNorm_translate_sub_le_smul_eLpNorm_fderiv
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (h : E) :
    eLpNorm (fun x => φ x - φ (x - h)) p volume ≤
      ENNReal.ofReal ‖h‖ *
        eLpNorm (fun x => ‖fderiv ℝ φ x‖) p volume := by
  classical
  have hp_ne : p ≠ 0 := by
    intro h0
    rw [h0] at hp_one
    exact absurd hp_one (by norm_num : ¬ (1 : ℝ≥0∞) ≤ 0)
  set pr : ℝ := p.toReal with hpr_def
  have hpr_pos : 0 < pr := ENNReal.toReal_pos hp_ne hp_top
  have hpr_ge_one : 1 ≤ pr := by
    have := ENNReal.toReal_mono hp_top hp_one
    simpa using this
  have hp_eq : p = ENNReal.ofReal pr := by
    rw [hpr_def]
    exact (ENNReal.ofReal_toReal hp_top).symm
  have hp0_pr : ENNReal.ofReal pr ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hpr_pos).ne'
  have hp_top_pr : ENNReal.ofReal pr ≠ ∞ := ENNReal.ofReal_ne_top
  have hpr_toReal : (ENNReal.ofReal pr).toReal = pr :=
    ENNReal.toReal_ofReal hpr_pos.le
  have hsub_meas : AEStronglyMeasurable (fun x => φ x - φ (x - h)) volume :=
    (hφ.continuous.sub (hφ.continuous.comp (continuous_id.sub continuous_const))).aestronglyMeasurable
  have hderiv_meas : AEStronglyMeasurable (fun x => ‖fderiv ℝ φ x‖) volume :=
    (hφ.continuous_fderiv (by simp)).norm.aestronglyMeasurable
  have hLHS :
      eLpNorm (fun x => φ x - φ (x - h)) p volume =
        (∫⁻ x : E, (‖φ x - φ (x - h)‖ₑ : ℝ≥0∞) ^ pr) ^ (1 / pr) := by
    rw [hp_eq, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0_pr hp_top_pr hsub_meas]
    simp [hpr_toReal]
  have hRHS :
      eLpNorm (fun x => ‖fderiv ℝ φ x‖) p volume =
        (∫⁻ x : E, (‖fderiv ℝ φ x‖ₑ : ℝ≥0∞) ^ pr) ^ (1 / pr) := by
    rw [hp_eq, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0_pr hp_top_pr hderiv_meas]
    have hcongr :
        ∀ x : E, (‖‖fderiv ℝ φ x‖‖ₑ : ℝ≥0∞) = (‖fderiv ℝ φ x‖ₑ : ℝ≥0∞) := by
      intro x
      rw [Real.enorm_eq_ofReal (norm_nonneg _), ofReal_norm]
    rw [hpr_toReal]
    have hcongr_lint :
        (∫⁻ x : E, (‖‖fderiv ℝ φ x‖‖ₑ : ℝ≥0∞) ^ pr) =
          ∫⁻ x : E, (‖fderiv ℝ φ x‖ₑ : ℝ≥0∞) ^ pr := by
      refine lintegral_congr_ae ?_
      filter_upwards with x
      rw [hcongr x]
    rw [hcongr_lint]
  rw [hLHS, hRHS]
  have hLR := lintegral_rpow_translate_sub_le (d := d) hφ hpr_ge_one h
  have hpr_inv_nn : 0 ≤ 1 / pr := by positivity
  have hPow :
      (∫⁻ x : E, (‖φ x - φ (x - h)‖ₑ : ℝ≥0∞) ^ pr) ^ (1 / pr) ≤
        (ENNReal.ofReal ‖h‖ ^ pr *
          ∫⁻ x : E, (‖fderiv ℝ φ x‖ₑ : ℝ≥0∞) ^ pr) ^ (1 / pr) :=
    ENNReal.rpow_le_rpow hLR hpr_inv_nn
  have hMul_rpow :
      (ENNReal.ofReal ‖h‖ ^ pr *
          ∫⁻ x : E, (‖fderiv ℝ φ x‖ₑ : ℝ≥0∞) ^ pr) ^ (1 / pr) =
        ENNReal.ofReal ‖h‖ *
          (∫⁻ x : E, (‖fderiv ℝ φ x‖ₑ : ℝ≥0∞) ^ pr) ^ (1 / pr) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hpr_inv_nn,
      ← ENNReal.rpow_mul]
    have hcancel : pr * (1 / pr) = 1 := by
      field_simp
    rw [hcancel, ENNReal.rpow_one]
  exact hPow.trans hMul_rpow.le

end Sobolev
