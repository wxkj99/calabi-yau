-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Tools/Mollification/Lp.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Tools.Mollification.Basic

@[expose] public section

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open scoped ENNReal NNReal Convolution Pointwise BigOperators

namespace Sobolev

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
theorem eLpNorm_mollifyEps_le
    {ε : ℝ} (hε : 0 < ε) {u : E → ℝ}
    (hu : MemLp u 2 (volume : Measure E)) :
    eLpNorm (mollifyEps (d := d) hε u) 2 (volume : Measure E) ≤
      eLpNorm u 2 (volume : Measure E) := by
  classical
  have hmem_p : MemLp u (ENNReal.ofReal 2) (volume : Measure E) := by
    have h_eq : (ENNReal.ofReal 2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_cast]
      rw [show (2 : ℝ≥0∞) = ((2 : ℕ) : ℝ≥0∞) from by norm_cast]
      exact ENNReal.ofReal_natCast 2
    rw [h_eq]; exact hu
  set ψ : E → ℝ := mollifierEps (d := d) hε with hψ_def
  have hψ_int : ∫ y, ψ y ∂(volume : Measure E) = 1 := mollifierEps_integral_eq_one hε
  have hψ_nn : ∀ y, 0 ≤ ψ y := mollifierEps_nonneg hε
  have hψ_integrable : Integrable ψ (volume : Measure E) := mollifierEps_integrable hε
  have hψ_cont : Continuous ψ := mollifierEps_continuous hε
  have hψ_compact : HasCompactSupport ψ := mollifierEps_compactSupport hε
  set C : ℝ≥0∞ := eLpNorm u 2 (volume : Measure E) with hC_def
  have hu_aestrong : AEStronglyMeasurable u (volume : Measure E) := hu.aestronglyMeasurable
  have h_pt_jensen : ∀ x : E,
      ‖(ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x‖ ^ (2 : ℝ) ≤
      ((fun y => ‖u y‖ ^ (2 : ℝ))
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] ψ) x := by
    intro x
    set h_norm_sq : E → ℝ := fun y => ‖u y‖ ^ (2 : ℝ) with hh_norm_sq_def
    set ρ : E → ℝ≥0∞ := fun y => ENNReal.ofReal (ψ y) with hρ_def
    set ν : Measure E := (volume : Measure E).withDensity ρ with hν_def
    have hρ_meas : Measurable ρ := hψ_cont.measurable.ennreal_ofReal
    have hρ_lt_top : ∀ᵐ y ∂(volume : Measure E), ρ y < ∞ := by
      filter_upwards with y
      simp [ρ]
    have hν_prob : IsProbabilityMeasure ν := by
      refine ⟨?_⟩
      rw [hν_def, withDensity_apply _ MeasurableSet.univ]
      rw [Measure.restrict_univ]
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hψ_integrable
        (Filter.Eventually.of_forall hψ_nn)]
      rw [hψ_int]
      simp
    have hu_local : LocallyIntegrable u (volume : Measure E) :=
      hu.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hce_u : ConvolutionExistsAt ψ u x
        (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure E) :=
      hψ_compact.convolutionExists_left
        (L := ContinuousLinearMap.lsmul ℝ ℝ) hψ_cont hu_local x
    have hconv_ν :
        ((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x) =
          ∫ y, u (x - y) ∂ν := by
      rw [hν_def]
      rw [integral_withDensity_eq_integral_toReal_smul hρ_meas hρ_lt_top]
      rw [MeasureTheory.convolution_def]
      refine integral_congr_ae ?_
      filter_upwards with y
      simp [ρ, ψ, ContinuousLinearMap.lsmul_apply, smul_eq_mul, hψ_nn y]
    have h_norm_sq_int_vol : Integrable (fun y => (ρ y).toReal * ‖u (x - y)‖)
      (volume : Measure E) := by
      refine hce_u.integrable.norm.congr ?_
      filter_upwards with y
      simp [ρ, ψ, ContinuousLinearMap.lsmul_apply, smul_eq_mul, hψ_nn y]
    have h_norm_int : Integrable (fun y => ‖u (x - y)‖) ν := by
      exact (MeasureTheory.integrable_withDensity_iff_integrable_smul' hρ_meas hρ_lt_top).2 <| by
        simpa [ρ, ψ, hψ_nn] using h_norm_sq_int_vol
    have hu_sq_local : LocallyIntegrable (fun y => ‖u y‖ ^ (2 : ℝ)) (volume : Measure E) := by
      have hh_int : Integrable (fun y => ‖u y‖ ^ (2 : ℝ)) (volume : Measure E) := by
        have := hu.integrable_norm_rpow (p := 2) (by norm_num : (2 : ℝ≥0∞) ≠ 0)
          (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
        simpa using this
      exact hh_int.locallyIntegrable
    have hce_h : ConvolutionExistsAt ψ h_norm_sq x
        (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure E) :=
      hψ_compact.convolutionExists_left
        (L := ContinuousLinearMap.lsmul ℝ ℝ) hψ_cont hu_sq_local x
    have h_rpow_int_vol :
        Integrable (fun y => (ρ y).toReal * ‖u (x - y)‖ ^ (2 : ℝ)) (volume : Measure E) := by
      refine hce_h.integrable.congr ?_
      filter_upwards with y
      simp [ρ, ψ, h_norm_sq, ContinuousLinearMap.lsmul_apply, smul_eq_mul,
        hψ_nn y]
    have h_rpow_int : Integrable (fun y => ‖u (x - y)‖ ^ (2 : ℝ)) ν := by
      exact (MeasureTheory.integrable_withDensity_iff_integrable_smul' hρ_meas hρ_lt_top).2 <| by
        simpa [ρ, ψ, hψ_nn] using h_rpow_int_vol
    have hnorm_le_int : ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x)‖ ≤
        ∫ y, ‖u (x - y)‖ ∂ν := by
      rw [hconv_ν]
      exact MeasureTheory.norm_integral_le_integral_norm _
    have hJensen_ν : (∫ y, ‖u (x - y)‖ ∂ν) ^ (2 : ℝ) ≤ ∫ y, ‖u (x - y)‖ ^ (2 : ℝ) ∂ν := by
      have hconv : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun t : ℝ => t ^ (2 : ℝ)) :=
        convexOn_rpow (by norm_num : (1 : ℝ) ≤ 2)
      have hcont : ContinuousOn (fun t : ℝ => t ^ (2 : ℝ)) (Set.Ici (0 : ℝ)) :=
        continuousOn_id.rpow_const (fun t _ => Or.inr (by norm_num : (0 : ℝ) ≤ 2))
      have hmem : ∀ᵐ y ∂ν, ‖u (x - y)‖ ∈ Set.Ici (0 : ℝ) := by
        filter_upwards with y
        exact norm_nonneg _
      exact hconv.map_integral_le hcont isClosed_Ici hmem h_norm_int h_rpow_int
    calc
      ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x)‖ ^ (2 : ℝ)
          ≤ (∫ y, ‖u (x - y)‖ ∂ν) ^ (2 : ℝ) :=
            Real.rpow_le_rpow (norm_nonneg _) hnorm_le_int (by norm_num : (0 : ℝ) ≤ 2)
      _ ≤ ∫ y, ‖u (x - y)‖ ^ (2 : ℝ) ∂ν := hJensen_ν
      _ = ∫ y, ψ y * ‖u (x - y)‖ ^ (2 : ℝ) ∂(volume : Measure E) := by
            rw [hν_def]
            rw [integral_withDensity_eq_integral_toReal_smul hρ_meas hρ_lt_top]
            refine integral_congr_ae ?_
            filter_upwards with y
            simp [ρ, ψ, hψ_nn y]
      _ = ((fun y => ‖u y‖ ^ (2 : ℝ))
            ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] ψ) x := by
            have hMP : MeasurePreserving (fun y : E => x - y) (volume : Measure E)
                (volume : Measure E) := by
              have h_neg : MeasurePreserving (fun t : E => -t) (volume : Measure E)
                  (volume : Measure E) :=
                Measure.measurePreserving_neg (volume : Measure E)
              have h_addL : MeasurePreserving (fun t : E => x + t) (volume : Measure E)
                  (volume : Measure E) :=
                measurePreserving_add_left (volume : Measure E) x
              have heq : (fun y : E => x - y) = (fun y : E => x + (-y)) := by
                funext y; rw [sub_eq_add_neg]
              rw [heq]; exact h_addL.comp h_neg
            have h_subst : ∫ y, ψ y * ‖u (x - y)‖ ^ (2 : ℝ) ∂(volume : Measure E) =
                ∫ t, ψ (x - t) * ‖u (x - (x - t))‖ ^ (2 : ℝ) ∂(volume : Measure E) :=
              (hMP.integral_comp (Homeomorph.subLeft x).measurableEmbedding
                (fun y : E => ψ y * ‖u (x - y)‖ ^ (2 : ℝ))).symm
            rw [h_subst]
            have h_rearr : ∀ t : E,
                ψ (x - t) * ‖u (x - (x - t))‖ ^ (2 : ℝ) =
                ‖u t‖ ^ (2 : ℝ) * ψ (x - t) := by
              intro t
              have h_simp : x - (x - t) = t := by abel
              rw [h_simp]
              ring
            rw [convolution_def]
            refine integral_congr_ae ?_
            filter_upwards with t
            rw [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
            exact h_rearr t
  have hu_local : LocallyIntegrable u (volume : Measure E) :=
    hu.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hu_sq_int : Integrable (fun y => ‖u y‖ ^ (2 : ℝ)) (volume : Measure E) := by
    have := hu.integrable_norm_rpow (p := 2) (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    simpa using this
  have hconv_cont : Continuous
      (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u :
        E → ℝ) :=
    hψ_compact.continuous_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
      hψ_cont hu_local
  have hh_convergence_int : Integrable
      ((fun y => ‖u y‖ ^ (2 : ℝ))
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] ψ)
      (volume : Measure E) :=
    hu_sq_int.integrable_convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) hψ_integrable
  have hpow_int : Integrable
      (fun x => ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x)‖
        ^ (2 : ℝ)) (volume : Measure E) := by
    refine Integrable.mono' hh_convergence_int ?_ ?_
    · exact (hconv_cont.norm.rpow_const
        (fun _ => Or.inr (by norm_num : (0 : ℝ) ≤ 2))).aestronglyMeasurable
    · filter_upwards with x
      have h_nn :
          0 ≤ ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x)‖
            ^ (2 : ℝ) :=
        Real.rpow_nonneg (norm_nonneg _) _
      rw [Real.norm_eq_abs, abs_of_nonneg h_nn]
      exact h_pt_jensen x
  have h_int_le :
      ∫ x, ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x)‖ ^ (2 : ℝ)
        ∂(volume : Measure E) ≤
      ∫ x, ((fun y => ‖u y‖ ^ (2 : ℝ))
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] ψ) x
        ∂(volume : Measure E) := by
    refine integral_mono_ae hpow_int hh_convergence_int ?_
    filter_upwards with x
    exact h_pt_jensen x
  have h_convergence_eq :
      ∫ x, ((fun y => ‖u y‖ ^ (2 : ℝ))
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] ψ) x
        ∂(volume : Measure E) =
      ∫ x, ‖u x‖ ^ (2 : ℝ) ∂(volume : Measure E) := by
    have h := MeasureTheory.integral_convolution
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := (volume : Measure E))
      (ν := (volume : Measure E)) hu_sq_int hψ_integrable
    rw [h]
    simp [ContinuousLinearMap.lsmul_apply, smul_eq_mul, hψ_int]
  have hconv_memLp : MemLp (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u : E → ℝ)
      2 (volume : Measure E) := by
    refine ⟨hconv_cont.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := (volume : Measure E))
      (f := (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u : E → ℝ))
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
    have h_2_toReal : ((2 : ℝ≥0∞).toReal) = (2 : ℝ) := by norm_num
    rw [h_2_toReal]
    have h_lint_finite : ∫⁻ x, ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x)‖ₑ
        ^ (2 : ℝ) ∂(volume : Measure E) < ∞ := by
      have h_pt_lint : ∀ x : E,
          ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x)‖ₑ
            ^ (2 : ℝ) =
          ENNReal.ofReal (‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x)‖
            ^ (2 : ℝ)) := by
        intro x
        rw [← ofReal_norm,
          ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
      have h_lint_pt :
          (fun x => ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x)‖ₑ
            ^ (2 : ℝ)) =
          (fun x => ENNReal.ofReal
            (‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x)‖
            ^ (2 : ℝ))) := by
        funext x
        exact h_pt_lint x
      rw [h_lint_pt]
      rw [← ofReal_integral_eq_lintegral_ofReal hpow_int
        (Filter.Eventually.of_forall (fun x => Real.rpow_nonneg (norm_nonneg _) _))]
      exact ENNReal.ofReal_lt_top
    refine ENNReal.rpow_lt_top_of_nonneg ?_ h_lint_finite.ne
    norm_num
  have h_2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h_2_ne_top : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  have h_eLp_lhs :
      eLpNorm (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u : E → ℝ)
        2 (volume : Measure E) =
      ENNReal.ofReal ((∫ x,
        ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x)‖ ^ (2 : ℝ)
          ∂(volume : Measure E)) ^ ((2 : ℝ)⁻¹)) := by
    have h := hconv_memLp.eLpNorm_eq_integral_rpow_norm h_2_ne_zero h_2_ne_top
    have h_2_toReal : ((2 : ℝ≥0∞).toReal) = (2 : ℝ) := by norm_num
    rw [h_2_toReal] at h
    exact h
  have h_eLp_rhs :
      eLpNorm u 2 (volume : Measure E) =
      ENNReal.ofReal ((∫ x, ‖u x‖ ^ (2 : ℝ) ∂(volume : Measure E)) ^ ((2 : ℝ)⁻¹)) := by
    have h := hu.eLpNorm_eq_integral_rpow_norm h_2_ne_zero h_2_ne_top
    have h_2_toReal : ((2 : ℝ≥0∞).toReal) = (2 : ℝ) := by norm_num
    rw [h_2_toReal] at h
    exact h
  have hcomm : mollifyEps (d := d) hε u =
      (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)]
        mollifierEps (d := d) hε) := by
    funext y
    exact mollifyEps_eq_convolution_swap hε u y
  rw [hcomm]
  have hcomm_convergence : ∀ y : E,
      (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)]
        mollifierEps (d := d) hε) y =
      (mollifierEps (d := d) hε
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) y := by
    intro y
    rw [convolution_lsmul, convolution_lsmul_swap]
    refine integral_congr_ae ?_
    filter_upwards with t
    rw [smul_eq_mul, smul_eq_mul, mul_comm]
  have hfun_eq :
      (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)]
        mollifierEps (d := d) hε) =
      (mollifierEps (d := d) hε
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) := by
    funext y; exact hcomm_convergence y
  rw [hfun_eq]
  change eLpNorm (mollifierEps (d := d) hε
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) 2
      (volume : Measure E) ≤ eLpNorm u 2 (volume : Measure E)
  rw [h_eLp_lhs, h_eLp_rhs]
  refine ENNReal.ofReal_le_ofReal ?_
  have h_int_combined :
      ∫ x, ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x)‖ ^ (2 : ℝ)
        ∂(volume : Measure E) ≤
      ∫ x, ‖u x‖ ^ (2 : ℝ) ∂(volume : Measure E) :=
    h_int_le.trans (le_of_eq h_convergence_eq)
  refine Real.rpow_le_rpow ?_ h_int_combined ?_
  · exact integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
  · exact inv_nonneg.mpr (by norm_num : (0 : ℝ) ≤ 2)

end Sobolev
