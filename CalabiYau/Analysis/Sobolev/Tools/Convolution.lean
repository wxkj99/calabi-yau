-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Tools/Convolution.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Tools.Mollification.Kernel

@[expose] public section


noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open scoped ENNReal NNReal Convolution Pointwise

namespace Sobolev

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

lemma exists_norm_bound_of_continuous_compactSupport
    {η : E → ℝ} (hη_cont : Continuous η) (hη_compact : HasCompactSupport η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖η y‖ ≤ C := by
  rcases hη_cont.bounded_above_of_compact_support hη_compact with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, fun y => ?_⟩
  exact (hC y).trans (le_max_left _ _)

lemma lipschitz_of_contDiff_compactSupport
    {η : E → ℝ} (hη_C1 : ContDiff ℝ 1 η) (hη_compact : HasCompactSupport η) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y, ‖η x - η y‖ ≤ L * ‖x - y‖ := by
  have hfderiv_cont : Continuous (fderiv ℝ η) := hη_C1.continuous_fderiv (by simp)
  have hfderiv_compact : HasCompactSupport (fderiv ℝ η) := hη_compact.fderiv ℝ
  rcases hfderiv_cont.bounded_above_of_compact_support hfderiv_compact with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, fun x y => ?_⟩
  have hbnd : ∀ z, ‖fderiv ℝ η z‖ ≤ max C 0 := fun z =>
    (hC z).trans (le_max_left _ _)
  have hbnd_nn : ∀ z, ‖fderiv ℝ η z‖₊ ≤
      NNReal.mk (max C 0) (le_max_right _ _) := by
    intro z
    change ‖fderiv ℝ η z‖ ≤ max C 0
    exact hbnd z
  have hLip : LipschitzWith (NNReal.mk (max C 0) (le_max_right _ _)) η :=
    lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
      (hη_C1.differentiable (by norm_cast)) hbnd_nn
  have hdist : dist (η x) (η y) ≤ max C 0 * dist x y := by
    have := hLip.dist_le_mul x y
    change dist (η x) (η y) ≤ max C 0 * dist x y at this
    exact this
  rw [show ‖η x - η y‖ = dist (η x) (η y) from (Real.dist_eq _ _).symm,
    show ‖x - y‖ = dist x y from (dist_eq_norm _ _).symm]
  exact hdist

private lemma measurePreserving_constSub (z : E) :
    MeasurePreserving (fun t : E => z - t) volume volume := by
  have h_neg : MeasurePreserving (fun t : E => -t) volume volume :=
    Measure.measurePreserving_neg volume
  have h_addL : MeasurePreserving (fun t : E => z + t) volume volume :=
    measurePreserving_add_left volume z
  have heq : (fun t : E => z - t) = (fun t : E => z + (-t)) := by
    funext t; rw [sub_eq_add_neg]
  rw [heq]
  exact h_addL.comp h_neg

theorem convolution_sup_le_holder
    {f η : E → ℝ}
    (hf_int : Integrable f volume)
    (hη_meas : AEStronglyMeasurable η volume)
    {M : ℝ} (hη_bnd : ∀ y, ‖η y‖ ≤ M) (x : E) :
    ‖(f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) x‖ ≤
      M * ∫ t, ‖f t‖ ∂volume := by
  classical
  have hη_meas_sub :
      AEStronglyMeasurable (fun t : E => η (x - t)) volume :=
    hη_meas.comp_measurePreserving (measurePreserving_constSub (d := d) x)
  have hpt : ∀ t : E, ‖f t • η (x - t)‖ ≤ M * ‖f t‖ := by
    intro t
    rw [norm_smul, mul_comm M ‖f t‖]
    exact mul_le_mul_of_nonneg_left (hη_bnd _) (norm_nonneg _)
  have hint_smul :
      Integrable (fun t : E => f t • η (x - t)) volume := by
    refine Integrable.mono' (g := fun t => M * ‖f t‖) ?_ ?_ ?_
    · exact hf_int.norm.const_mul M
    · exact hf_int.aestronglyMeasurable.smul hη_meas_sub
    · filter_upwards with t
      exact hpt t
  have hconv_eq :
      (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) x =
        ∫ t, f t • η (x - t) ∂volume := by
    simp [MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply]
  rw [hconv_eq]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hint_pt :
      ∫ t, ‖f t • η (x - t)‖ ∂volume ≤
        ∫ t, M * ‖f t‖ ∂volume := by
    refine integral_mono_ae hint_smul.norm
      (hf_int.norm.const_mul M) ?_
    filter_upwards with t using hpt t
  refine hint_pt.trans ?_
  rw [integral_const_mul]

theorem convolution_lipschitz_with
    {f η : E → ℝ}
    (hf_int : Integrable f volume)
    (hη_cont : Continuous η) (hη_compact : HasCompactSupport η)
    {L : ℝ}
    (hη_lip : ∀ x y, ‖η x - η y‖ ≤ L * ‖x - y‖) (x y : E) :
    ‖(f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) x -
      (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) y‖ ≤
      L * (∫ t, ‖f t‖ ∂volume) * ‖x - y‖ := by
  classical
  rcases exists_norm_bound_of_continuous_compactSupport (d := d)
      hη_cont hη_compact with ⟨M, hM_nn, hη_bnd⟩
  have hη_meas : AEStronglyMeasurable η volume := hη_cont.aestronglyMeasurable
  have hη_meas_sub : ∀ z : E,
      AEStronglyMeasurable (fun t : E => η (z - t)) volume := fun z =>
    hη_meas.comp_measurePreserving (measurePreserving_constSub (d := d) z)
  have hint_smul : ∀ z : E,
      Integrable (fun t : E => f t • η (z - t)) volume := by
    intro z
    refine Integrable.mono' (g := fun t => M * ‖f t‖) ?_ ?_ ?_
    · exact hf_int.norm.const_mul M
    · exact hf_int.aestronglyMeasurable.smul (hη_meas_sub z)
    · filter_upwards with t
      have : ‖f t • η (z - t)‖ ≤ M * ‖f t‖ := by
        rw [norm_smul, mul_comm M ‖f t‖]
        exact mul_le_mul_of_nonneg_left (hη_bnd _) (norm_nonneg _)
      exact this
  have hconv_eq : ∀ z : E,
      (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) z =
        ∫ t, f t • η (z - t) ∂volume := by
    intro z
    simp [MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply]
  rw [hconv_eq x, hconv_eq y, ← integral_sub (hint_smul x) (hint_smul y)]
  have hpt : ∀ t : E,
      ‖f t • η (x - t) - f t • η (y - t)‖ ≤ L * ‖x - y‖ * ‖f t‖ := by
    intro t
    rw [show f t • η (x - t) - f t • η (y - t) =
      f t • (η (x - t) - η (y - t)) from by rw [smul_sub]]
    rw [norm_smul]
    have h1 : ‖η (x - t) - η (y - t)‖ ≤ L * ‖(x - t) - (y - t)‖ :=
      hη_lip (x - t) (y - t)
    have hxy : (x - t) - (y - t) = x - y := by abel
    rw [hxy] at h1
    calc
      ‖f t‖ * ‖η (x - t) - η (y - t)‖ ≤ ‖f t‖ * (L * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = L * ‖x - y‖ * ‖f t‖ := by ring
  have hint_diff :
      Integrable (fun t : E =>
        f t • η (x - t) - f t • η (y - t)) volume :=
    (hint_smul x).sub (hint_smul y)
  refine (norm_integral_le_integral_norm _).trans ?_
  have hint_pt :
      ∫ t, ‖f t • η (x - t) - f t • η (y - t)‖ ∂volume ≤
        ∫ t, L * ‖x - y‖ * ‖f t‖ ∂volume := by
    refine integral_mono_ae hint_diff.norm
      (hf_int.norm.const_mul (L * ‖x - y‖)) ?_
    filter_upwards with t using hpt t
  refine hint_pt.trans ?_
  rw [integral_const_mul]
  rw [mul_assoc L ‖x - y‖ _, mul_comm ‖x - y‖ _, ← mul_assoc]

end Sobolev
