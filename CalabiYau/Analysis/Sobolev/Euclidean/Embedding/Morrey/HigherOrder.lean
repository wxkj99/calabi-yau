-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Euclidean/Embedding/Morrey/HigherOrder.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Euclidean.W1p.Witness
public import CalabiYau.Analysis.Sobolev.Euclidean.W1p.Approximation
public import CalabiYau.Analysis.Sobolev.Euclidean.Poincare.Ball
public import CalabiYau.Analysis.Sobolev.Euclidean.Poincare.SobolevPoincare
public import CalabiYau.Analysis.Sobolev.Euclidean.Ball.Approximation
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Integral.Average
public import CalabiYau.Analysis.Sobolev.Euclidean.Embedding.Morrey.RieszKernel
public import CalabiYau.Analysis.Sobolev.Euclidean.Embedding.Morrey.SmoothHolderBound
public import CalabiYau.Analysis.Sobolev.Euclidean.Embedding.Morrey.SmoothInequality
public import CalabiYau.Analysis.Sobolev.Euclidean.ChainRule.CompChainRuleK

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric Function
open scoped ENNReal NNReal

namespace CalabiYau
namespace Analysis
namespace Sobolev

open Sobolev.Euclidean Sobolev.EuclideanMorrey

namespace EuclideanMorrey

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

private lemma euclideanSpace_coord_abs_le_norm (v : E) (i : Fin d) :
    |v i| ≤ ‖v‖ := by
  classical
  have h_sq : (v i) ^ 2 ≤ ∑ j : Fin d, (v j) ^ 2 := by
    have h_nn : ∀ j : Fin d, 0 ≤ (v j) ^ 2 := fun j => sq_nonneg _
    have h_single : (v i) ^ 2 = ∑ j ∈ ({i} : Finset (Fin d)), (v j) ^ 2 := by simp
    rw [h_single]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ => h_nn j)
  have h_sqrt_le : Real.sqrt ((v i) ^ 2) ≤ Real.sqrt (∑ j : Fin d, (v j) ^ 2) :=
    Real.sqrt_le_sqrt h_sq
  have h_sqrt_sq : Real.sqrt ((v i) ^ 2) = |v i| := Real.sqrt_sq_eq_abs _
  have h_norm_eq : ‖v‖ = Real.sqrt (∑ j : Fin d, (v j) ^ 2) := by
    rw [EuclideanSpace.norm_eq v]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Real.norm_eq_abs, sq_abs]
  rw [h_norm_eq, ← h_sqrt_sq]
  exact h_sqrt_le

variable [NeZero d] in
private def basisTuple {m : ℕ} (α : Fin m → Fin d) : Fin m → E :=
  fun i => EuclideanSpace.single (α i) 1

private lemma basisTuple_norm_one {m : ℕ} (α : Fin m → Fin d) (i : Fin m) :
    ‖basisTuple α i‖ = 1 := by
  simp [basisTuple]

private lemma basisTuple_prod_norms {m : ℕ} (α : Fin m → Fin d) :
    (∏ i : Fin m, ‖basisTuple α i‖) = 1 := by
  apply Finset.prod_eq_one
  intros i _; exact basisTuple_norm_one α i

private lemma euclideanSpace_basis_expansion (v : E) :
    v = ∑ j : Fin d, v j • EuclideanSpace.single j (1 : ℝ) := by
  classical
  have h_pi_decomp : (fun i : Fin d => v i) =
      ∑ j : Fin d, (v j) • ((Pi.single j (1 : ℝ)) : Fin d → ℝ) := by
    funext i
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single i]
    · simp [smul_eq_mul]
    · intro j _ hj
      rw [Pi.smul_apply, Pi.single_apply, ite_eq_right hj.symm, smul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have h_v_toLp : v = WithLp.toLp 2 (fun i : Fin d => v i) := by rfl
  have h_rhs :
      (∑ j : Fin d, v j • EuclideanSpace.single j (1 : ℝ) : E) =
        ∑ j : Fin d, v j • WithLp.toLp 2 ((Pi.single j (1 : ℝ)) : Fin d → ℝ) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rfl
  rw [h_rhs]
  conv_lhs => rw [h_v_toLp, h_pi_decomp]
  rw [show (WithLp.toLp 2 : (Fin d → ℝ) → E) =
      (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).symm from rfl]
  rw [_root_.map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [LinearEquiv.map_smul]

private theorem opNorm_le_sum_basis
    {m : ℕ} (f : ContinuousMultilinearMap ℝ (fun _ : Fin m => E) ℝ) :
    ‖f‖ ≤ ∑ α : Fin m → Fin d, |f (basisTuple α)| := by
  classical
  set S : ℝ := ∑ α : Fin m → Fin d, |f (basisTuple α)| with hS_def
  have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun α _ => abs_nonneg _)
  refine ContinuousMultilinearMap.opNorm_le_bound hS_nn (fun v => ?_)
  have h_v_eq : v = fun i : Fin m => ∑ j : Fin d, (v i j) • EuclideanSpace.single j (1 : ℝ) := by
    funext i; exact euclideanSpace_basis_expansion (v i)
  conv_lhs => rw [h_v_eq]
  have h_sum_expand :
      f (fun i : Fin m => ∑ j : Fin d, (v i j) • EuclideanSpace.single j (1 : ℝ)) =
        ∑ α : Fin m → Fin d, f (fun i => (v i (α i)) • EuclideanSpace.single (α i) (1 : ℝ)) := by
    change f.toMultilinearMap (fun i : Fin m => ∑ j : Fin d,
        (v i j) • EuclideanSpace.single j (1 : ℝ)) =
      ∑ α : Fin m → Fin d,
        f.toMultilinearMap (fun i => (v i (α i)) • EuclideanSpace.single (α i) (1 : ℝ))
    exact f.toMultilinearMap.map_sum
      (g := fun (i : Fin m) (j : Fin d) => (v i j) • EuclideanSpace.single j (1 : ℝ))
  rw [h_sum_expand]
  refine (norm_sum_le _ _).trans ?_
  have h_norm_eq : ∀ α : Fin m → Fin d,
      ‖f (fun i => (v i (α i)) • EuclideanSpace.single (α i) (1 : ℝ))‖ =
        |f (fun i => (v i (α i)) • EuclideanSpace.single (α i) (1 : ℝ))| := by
    intro α; rfl
  rw [Finset.sum_congr rfl (fun α _ => h_norm_eq α)]
  have h_map_smul : ∀ (α : Fin m → Fin d),
      f (fun i => (v i (α i)) • EuclideanSpace.single (α i) (1 : ℝ)) =
        (∏ i : Fin m, v i (α i)) • f (basisTuple α) := by
    intro α
    classical
    have h := f.toMultilinearMap.map_smul_univ
      (fun i : Fin m => v i (α i))
      (fun i : Fin m => EuclideanSpace.single (α i) (1 : ℝ))
    have hb : (fun i : Fin m => EuclideanSpace.single (α i) (1 : ℝ)) = basisTuple α := rfl
    rw [hb] at h
    change f.toMultilinearMap (fun i => (v i (α i)) • EuclideanSpace.single (α i) (1 : ℝ)) =
      (∏ i : Fin m, v i (α i)) • f.toMultilinearMap (basisTuple α)
    exact h
  have h_each : ∀ α : Fin m → Fin d,
      |f (fun i => (v i (α i)) • EuclideanSpace.single (α i) (1 : ℝ))| ≤
        |f (basisTuple α)| * ∏ i : Fin m, ‖v i‖ := by
    intro α
    rw [h_map_smul α, smul_eq_mul, abs_mul, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [Finset.abs_prod]
    apply Finset.prod_le_prod₀
    · intros; exact abs_nonneg _
    · intros i _
      exact euclideanSpace_coord_abs_le_norm (v i) (α i)
  refine le_trans (Finset.sum_le_sum (fun α _ => h_each α)) ?_
  rw [← Finset.sum_mul]

private lemma abs_apply_basisTuple_le_opNorm
    {m : ℕ} (f : ContinuousMultilinearMap ℝ (fun _ : Fin m => E) ℝ)
    (α : Fin m → Fin d) :
    |f (basisTuple α)| ≤ ‖f‖ := by
  have h := f.le_opNorm (basisTuple α)
  rw [basisTuple_prod_norms α, mul_one] at h
  exact h

private theorem contDiff_iteratedFDeriv_apply_basisTuple
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) {m : ℕ} (α : Fin m → Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : E => (iteratedFDeriv ℝ m u y) (basisTuple α)) := by
  classical
  have h_iterFD : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => iteratedFDeriv ℝ m u y) := by
    have h := hu.iteratedFDeriv_right' (m := (⊤ : ℕ∞)) (i := m)
    simpa using h
  let app : ContinuousMultilinearMap ℝ (fun _ : Fin m => E) ℝ →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => E) ℝ (basisTuple α)
  exact app.contDiff.comp h_iterFD

private lemma abs_iteratedFDeriv_apply_basisTuple_le
    (u : E → ℝ) {m : ℕ} (α : Fin m → Fin d) (y : E) :
    |(iteratedFDeriv ℝ m u y) (basisTuple α)| ≤ ‖iteratedFDeriv ℝ m u y‖ :=
  abs_apply_basisTuple_le_opNorm _ α

private theorem norm_fderiv_iteratedFDeriv_apply_basisTuple_le
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) {m : ℕ} (α : Fin m → Fin d) (y : E) :
    ‖fderiv ℝ (fun z : E => (iteratedFDeriv ℝ m u z) (basisTuple α)) y‖ ≤
      ‖iteratedFDeriv ℝ (m + 1) u y‖ := by
  classical
  have h_iterFD_smooth :
      ContDiff ℝ (⊤ : ℕ∞) (fun y : E => iteratedFDeriv ℝ m u y) := by
    have h := hu.iteratedFDeriv_right' (m := (⊤ : ℕ∞)) (i := m)
    simpa using h
  have h_diff_at : DifferentiableAt ℝ
      (fun y : E => iteratedFDeriv ℝ m u y) y :=
    (h_iterFD_smooth.differentiable (by simp)).differentiableAt
  set app : ContinuousMultilinearMap ℝ (fun _ : Fin m => E) ℝ →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => E) ℝ (basisTuple α)
  have h_funext :
      (fun z : E => (iteratedFDeriv ℝ m u z) (basisTuple α)) =
        fun z => app (iteratedFDeriv ℝ m u z) := by
    funext z; rfl
  rw [h_funext]
  have h_app_hasFDerivAt : HasFDerivAt app app (iteratedFDeriv ℝ m u y) :=
    app.hasFDerivAt
  have h_inner_hasFDerivAt :
      HasFDerivAt (fun z : E => iteratedFDeriv ℝ m u z)
        (fderiv ℝ (fun z : E => iteratedFDeriv ℝ m u z) y) y :=
    h_diff_at.hasFDerivAt
  have h_chain : HasFDerivAt (fun z : E => app (iteratedFDeriv ℝ m u z))
      (app.comp (fderiv ℝ (fun z : E => iteratedFDeriv ℝ m u z) y)) y :=
    h_app_hasFDerivAt.comp y h_inner_hasFDerivAt
  rw [h_chain.fderiv]
  refine (app.opNorm_comp_le _).trans ?_
  have h_app_norm_le : ‖app‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun c => ?_)
    have h_eval : app c = c (basisTuple α) := rfl
    rw [h_eval]
    have h := c.le_opNorm (basisTuple α)
    rw [basisTuple_prod_norms α, mul_one] at h
    rw [one_mul]
    exact h
  have h_iter_norm :
      ‖fderiv ℝ (fun z : E => iteratedFDeriv ℝ m u z) y‖ =
        ‖iteratedFDeriv ℝ (m + 1) u y‖ := norm_fderiv_iteratedFDeriv
  rw [h_iter_norm]
  calc ‖app‖ * ‖iteratedFDeriv ℝ (m + 1) u y‖
      ≤ 1 * ‖iteratedFDeriv ℝ (m + 1) u y‖ :=
        mul_le_mul_of_nonneg_right h_app_norm_le (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ (m + 1) u y‖ := one_mul _

private lemma eLpNorm_apply_basisTuple_le_eLpNorm_iteratedFDeriv
    (u : E → ℝ) (m : ℕ) {p_e : ℝ≥0∞} {μ : Measure E} (α : Fin m → Fin d)
    (hf : AEStronglyMeasurable
      (fun y : E => (iteratedFDeriv ℝ m u y) (basisTuple α)) μ) :
    eLpNorm (fun y : E => (iteratedFDeriv ℝ m u y) (basisTuple α)) p_e μ ≤
      eLpNorm (fun y : E => ‖iteratedFDeriv ℝ m u y‖) p_e μ := by
  apply eLpNorm_mono hf
  intro y
  rw [Real.norm_eq_abs]
  rw [show ‖‖iteratedFDeriv ℝ m u y‖‖ = ‖iteratedFDeriv ℝ m u y‖ from
    Real.norm_of_nonneg (norm_nonneg _)]
  exact abs_iteratedFDeriv_apply_basisTuple_le _ _ _

private lemma eLpNorm_fderiv_apply_basisTuple_le_eLpNorm_iteratedFDeriv_succ
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (m : ℕ) {p_e : ℝ≥0∞} {μ : Measure E}
    (α : Fin m → Fin d) :
    eLpNorm
      (fun y : E => ‖fderiv ℝ (fun z => (iteratedFDeriv ℝ m u z) (basisTuple α)) y‖)
      p_e μ ≤
      eLpNorm (fun y : E => ‖iteratedFDeriv ℝ (m + 1) u y‖) p_e μ := by
  have hg := contDiff_iteratedFDeriv_apply_basisTuple hu α
  apply eLpNorm_mono (hg.continuous_fderiv (by simp)).norm.aestronglyMeasurable
  intro y
  rw [show ‖‖fderiv ℝ (fun z => (iteratedFDeriv ℝ m u z) (basisTuple α)) y‖‖ =
    ‖fderiv ℝ (fun z => (iteratedFDeriv ℝ m u z) (basisTuple α)) y‖ from
    Real.norm_of_nonneg (norm_nonneg _)]
  rw [show ‖‖iteratedFDeriv ℝ (m + 1) u y‖‖ = ‖iteratedFDeriv ℝ (m + 1) u y‖ from
    Real.norm_of_nonneg (norm_nonneg _)]
  exact norm_fderiv_iteratedFDeriv_apply_basisTuple_le hu α y

private lemma smooth_iteratedFDeriv_norm_memLp_on_ball
    {p : ℝ} (_hp_pos : 0 < p) {x₀ : E} {R : ℝ} (_hR : 0 < R) (j : ℕ)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    MemLp (fun y : E => ‖iteratedFDeriv ℝ j u y‖) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball x₀ R)) := by
  have h_iter_cont : Continuous (fun y : E => iteratedFDeriv ℝ j u y) := by
    have h := hu.iteratedFDeriv_right' (m := (⊤ : ℕ∞)) (i := j)
    simpa using h.continuous
  have hcont : Continuous (fun y : E => ‖iteratedFDeriv ℝ j u y‖) :=
    continuous_norm.comp h_iter_cont
  obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_closedBall x₀ R) hcont.continuousOn
  have : IsFiniteMeasure (volume.restrict (Metric.ball x₀ R)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top
  refine MemLp.of_le_mul (g := fun _ : E => (1 : ℝ)) (c := M) ?_ ?_ ?_
  · exact memLp_const (1 : ℝ)
  · exact hcont.aestronglyMeasurable.restrict
  · refine ae_restrict_iff' measurableSet_ball |>.mpr ?_
    filter_upwards with y hy
    have hy' : y ∈ Metric.closedBall x₀ R := Metric.ball_subset_closedBall hy
    rw [norm_one, mul_one]
    exact hM y hy'

private lemma smooth_iteratedFDeriv_norm_eLpNorm_ne_top
    {p : ℝ} (hp_pos : 0 < p) {x₀ : E} {R : ℝ} (hR : 0 < R) (j : ℕ)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    eLpNorm (fun y : E => ‖iteratedFDeriv ℝ j u y‖) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball x₀ R)) ≠ ⊤ :=
  (smooth_iteratedFDeriv_norm_memLp_on_ball hp_pos hR j hu).eLpNorm_ne_top

variable [NeZero d] in
theorem smooth_morrey_iteratedFDeriv_bound_uniform
    {p : ℝ} (hp : (d : ℝ) < p)
    {x₀ : E} {R : ℝ} (hR : 0 < R)
    (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : E → ℝ}, ContDiff ℝ (⊤ : ℕ∞) u →
        ∀ x ∈ Metric.ball x₀ (R / 2),
          ‖iteratedFDeriv ℝ m u x‖ ≤ C *
            ((Finset.range (m + 2)).sum fun j =>
              (eLpNorm (fun z => ‖iteratedFDeriv ℝ j u z‖) (ENNReal.ofReal p)
                (volume.restrict (Metric.ball x₀ R))).toReal) := by
  classical
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hp_pos : 0 < p := lt_trans hd_pos hp
  obtain ⟨C₀, hC₀_nn, hC₀_bound⟩ :=
    smooth_morrey_sup_bound_uniform (d := d) hp (x₀ := x₀) (R := R) hR
  set N : ℕ := Fintype.card (Fin m → Fin d) with hN_def
  refine ⟨(N : ℝ) * C₀, mul_nonneg (Nat.cast_nonneg _) hC₀_nn, ?_⟩
  intro u hu x hx
  set g : (Fin m → Fin d) → (E → ℝ) :=
    fun α y => (iteratedFDeriv ℝ m u y) (basisTuple α) with hg_def
  have h_gα_smooth : ∀ α, ContDiff ℝ (⊤ : ℕ∞) (g α) := fun α =>
    contDiff_iteratedFDeriv_apply_basisTuple hu α
  have h_per_α : ∀ α : Fin m → Fin d,
      ‖g α x‖ ≤ C₀ * (
        (eLpNorm (g α) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ R))).toReal +
        (eLpNorm (fun z => ‖fderiv ℝ (g α) z‖) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ R))).toReal) := fun α =>
    hC₀_bound (h_gα_smooth α) x hx
  set Nm : ℝ := (eLpNorm (fun z => ‖iteratedFDeriv ℝ m u z‖) (ENNReal.ofReal p)
    (volume.restrict (Metric.ball x₀ R))).toReal with hNm_def
  set Nm1 : ℝ := (eLpNorm (fun z => ‖iteratedFDeriv ℝ (m + 1) u z‖) (ENNReal.ofReal p)
    (volume.restrict (Metric.ball x₀ R))).toReal with hNm1_def
  have hNm_nn : 0 ≤ Nm := ENNReal.toReal_nonneg
  have hNm1_nn : 0 ≤ Nm1 := ENNReal.toReal_nonneg
  have hNm_finite : eLpNorm (fun z => ‖iteratedFDeriv ℝ m u z‖) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball x₀ R)) ≠ ⊤ :=
    smooth_iteratedFDeriv_norm_eLpNorm_ne_top hp_pos hR m hu
  have hNm1_finite : eLpNorm (fun z => ‖iteratedFDeriv ℝ (m + 1) u z‖) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball x₀ R)) ≠ ⊤ :=
    smooth_iteratedFDeriv_norm_eLpNorm_ne_top hp_pos hR (m + 1) hu
  have h_each_α_simplified : ∀ α : Fin m → Fin d, ‖g α x‖ ≤ C₀ * (Nm + Nm1) := by
    intro α
    refine (h_per_α α).trans ?_
    apply mul_le_mul_of_nonneg_left _ hC₀_nn
    have h1 :
        (eLpNorm (g α) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ R))).toReal ≤ Nm := by
      apply ENNReal.toReal_mono hNm_finite
      exact eLpNorm_apply_basisTuple_le_eLpNorm_iteratedFDeriv u m α
        (h_gα_smooth α).continuous.aestronglyMeasurable
    have h2 :
        (eLpNorm (fun z => ‖fderiv ℝ (g α) z‖) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ R))).toReal ≤ Nm1 := by
      apply ENNReal.toReal_mono hNm1_finite
      exact eLpNorm_fderiv_apply_basisTuple_le_eLpNorm_iteratedFDeriv_succ hu m α
    linarith
  have h_pointwise : ‖iteratedFDeriv ℝ m u x‖ ≤ ∑ α : Fin m → Fin d, |g α x| :=
    opNorm_le_sum_basis (iteratedFDeriv ℝ m u x)
  have h_sum_each :
      ∑ α : Fin m → Fin d, ‖g α x‖ ≤ (N : ℝ) * (C₀ * (Nm + Nm1)) := by
    have h_each_le : ∀ α : Fin m → Fin d, ‖g α x‖ ≤ C₀ * (Nm + Nm1) :=
      h_each_α_simplified
    have h_sum_le : ∑ α : Fin m → Fin d, ‖g α x‖ ≤
        ∑ _α : Fin m → Fin d, C₀ * (Nm + Nm1) :=
      Finset.sum_le_sum (fun α _ => h_each_le α)
    have h_const_sum : ∑ _α : Fin m → Fin d, C₀ * (Nm + Nm1) =
        (N : ℝ) * (C₀ * (Nm + Nm1)) := by
      rw [Finset.sum_const, hN_def, Finset.card_univ]
      ring
    rw [h_const_sum] at h_sum_le
    exact h_sum_le
  have h_sum_eq : ∑ α : Fin m → Fin d, |g α x| = ∑ α : Fin m → Fin d, ‖g α x‖ := by
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rfl
  rw [← h_sum_eq] at h_sum_each
  have h_step1 : ‖iteratedFDeriv ℝ m u x‖ ≤ (N : ℝ) * (C₀ * (Nm + Nm1)) :=
    le_trans h_pointwise h_sum_each
  set total : ℝ :=
    (Finset.range (m + 2)).sum fun j =>
      (eLpNorm (fun z => ‖iteratedFDeriv ℝ j u z‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball x₀ R))).toReal with htotal_def
  have h_total_nn : 0 ≤ total :=
    Finset.sum_nonneg (fun j _ => ENNReal.toReal_nonneg)
  have h_Nm_plus_Nm1_le_total : Nm + Nm1 ≤ total := by
    have h_pair_eq :
        Nm + Nm1 =
          ((eLpNorm (fun z => ‖iteratedFDeriv ℝ m u z‖) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ R))).toReal +
           (eLpNorm (fun z => ‖iteratedFDeriv ℝ (m + 1) u z‖) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ R))).toReal) := by
      rw [hNm_def, hNm1_def]
    rw [h_pair_eq]
    set f : ℕ → ℝ := fun j => (eLpNorm (fun z => ‖iteratedFDeriv ℝ j u z‖)
      (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R))).toReal with hf_def
    have h_split : (Finset.range (m + 2)).sum f =
        f m + f (m + 1) +
          (((Finset.range (m + 2)).erase m).erase (m + 1)).sum f := by
      have hm_mem : m ∈ Finset.range (m + 2) := by
        rw [Finset.mem_range]; omega
      have hm1_mem : m + 1 ∈ Finset.range (m + 2) := by
        rw [Finset.mem_range]; omega
      have hm1_mem_erase : m + 1 ∈ ((Finset.range (m + 2)).erase m) := by
        rw [Finset.mem_erase]; exact ⟨by omega, hm1_mem⟩
      rw [← Finset.sum_erase_add _ _ hm_mem]
      rw [← Finset.sum_erase_add _ _ hm1_mem_erase]
      ring
    rw [htotal_def]
    have h_total_unfold :
        (Finset.range (m + 2)).sum (fun j =>
          (eLpNorm (fun z => ‖iteratedFDeriv ℝ j u z‖) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ R))).toReal) = (Finset.range (m + 2)).sum f := rfl
    rw [h_total_unfold, h_split]
    have h_remainder_nn : 0 ≤
        (((Finset.range (m + 2)).erase m).erase (m + 1)).sum f :=
      Finset.sum_nonneg (fun j _ => ENNReal.toReal_nonneg)
    have hf_m : f m = Nm := rfl
    have hf_m1 : f (m + 1) = Nm1 := rfl
    linarith [h_remainder_nn]
  have hN_C₀_nn : 0 ≤ (N : ℝ) * C₀ := mul_nonneg (Nat.cast_nonneg _) hC₀_nn
  have h_step2 :
      (N : ℝ) * (C₀ * (Nm + Nm1)) ≤ ((N : ℝ) * C₀) * total := by
    have h_rewrite : (N : ℝ) * (C₀ * (Nm + Nm1)) = ((N : ℝ) * C₀) * (Nm + Nm1) := by ring
    rw [h_rewrite]
    exact mul_le_mul_of_nonneg_left h_Nm_plus_Nm1_le_total hN_C₀_nn
  exact le_trans h_step1 h_step2

private theorem exists_smooth_cutoff_outer
    {x₀ : E} {R : ℝ} (hR : 0 < R) :
    ∃ η : E → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) η ∧
      HasCompactSupport η ∧
      Set.range η ⊆ Set.Icc (0 : ℝ) 1 ∧
      (∀ x ∈ Metric.closedBall x₀ (3 * R / 4), η x = 1) ∧
      tsupport η ⊆ Metric.closedBall x₀ (7 * R / 8) := by
  classical
  have hδ_pos : (0 : ℝ) < R / 16 := by linarith
  have hclosed_R34 : IsClosed (Metric.closedBall x₀ (3 * R / 4)) :=
    Metric.isClosed_closedBall
  have hopen_R78 : IsOpen (Metric.thickening (R / 16) (Metric.closedBall x₀ (3 * R / 4))) :=
    isOpen_thickening
  have hRsub : Metric.closedBall x₀ (3 * R / 4) ⊆
      Metric.thickening (R / 16) (Metric.closedBall x₀ (3 * R / 4)) :=
    Metric.self_subset_thickening hδ_pos _
  rcases exists_contMDiff_support_eq_eq_one_iff
      (I := modelWithCornersSelf ℝ E)
      (s := Metric.thickening (R / 16) (Metric.closedBall x₀ (3 * R / 4)))
      (t := Metric.closedBall x₀ (3 * R / 4))
      hopen_R78 hclosed_R34 hRsub with
    ⟨η, hη_smooth, hη_range, hη_support, hη_one_iff⟩
  have h_support_in_closedBall :
      tsupport η ⊆ Metric.closedBall x₀ (7 * R / 8) := by
    have hRR_le : 3 * R / 4 + R / 16 ≤ 7 * R / 8 := by linarith
    have h_closed : IsClosed (Metric.closedBall x₀ (7 * R / 8)) :=
      Metric.isClosed_closedBall
    rw [tsupport, hη_support]
    refine closure_minimal ?_ h_closed
    intro y hy
    rw [Metric.mem_thickening_iff] at hy
    rcases hy with ⟨z, hz_mem, hyz⟩
    rw [Metric.mem_closedBall] at hz_mem ⊢
    calc dist y x₀ ≤ dist y z + dist z x₀ := dist_triangle _ _ _
      _ ≤ R / 16 + 3 * R / 4 := by
          have hyz_le : dist y z ≤ R / 16 := le_of_lt hyz
          linarith
      _ ≤ 7 * R / 8 := by linarith
  refine ⟨η, contMDiff_iff_contDiff.mp hη_smooth, ?_, hη_range, ?_, h_support_in_closedBall⟩
  · refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (x := x₀) (7 * R / 8)) ?_
    exact (subset_tsupport _).trans h_support_in_closedBall
  · intro x hx
    exact (hη_one_iff x).1 hx

private theorem exists_smooth_cutoff_smaller
    {x₀ : E} {R : ℝ} (hR : 0 < R) :
    ∃ ψ : E → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ψ ∧
      HasCompactSupport ψ ∧
      Set.range ψ ⊆ Set.Icc (0 : ℝ) 1 ∧
      (∀ x ∈ Metric.closedBall x₀ (R / 4), ψ x = 1) ∧
      tsupport ψ ⊆ Metric.closedBall x₀ (R / 3) := by
  classical
  have hδ_pos : (0 : ℝ) < R / 24 := by linarith
  have hclosed : IsClosed (Metric.closedBall x₀ (R / 4)) := Metric.isClosed_closedBall
  have hopen_thick : IsOpen (Metric.thickening (R / 24) (Metric.closedBall x₀ (R / 4))) :=
    isOpen_thickening
  have hsub : Metric.closedBall x₀ (R / 4) ⊆
      Metric.thickening (R / 24) (Metric.closedBall x₀ (R / 4)) :=
    Metric.self_subset_thickening hδ_pos _
  rcases exists_contMDiff_support_eq_eq_one_iff
      (I := modelWithCornersSelf ℝ E)
      (s := Metric.thickening (R / 24) (Metric.closedBall x₀ (R / 4)))
      (t := Metric.closedBall x₀ (R / 4))
      hopen_thick hclosed hsub with
    ⟨ψ, hψ_smooth, hψ_range, hψ_support, hψ_one_iff⟩
  have h_support_in_closedBall :
      tsupport ψ ⊆ Metric.closedBall x₀ (R / 3) := by
    have h_closed_R3 : IsClosed (Metric.closedBall x₀ (R / 3)) := Metric.isClosed_closedBall
    rw [tsupport, hψ_support]
    refine closure_minimal ?_ h_closed_R3
    intro y hy
    rw [Metric.mem_thickening_iff] at hy
    rcases hy with ⟨z, hz_mem, hyz⟩
    rw [Metric.mem_closedBall] at hz_mem ⊢
    calc dist y x₀ ≤ dist y z + dist z x₀ := dist_triangle _ _ _
      _ ≤ R / 24 + R / 4 := by
          have hyz_le : dist y z ≤ R / 24 := le_of_lt hyz
          linarith
      _ ≤ R / 3 := by linarith
  refine ⟨ψ, contMDiff_iff_contDiff.mp hψ_smooth, ?_, hψ_range, ?_, h_support_in_closedBall⟩
  · refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (x := x₀) (R / 3)) ?_
    exact (subset_tsupport _).trans h_support_in_closedBall
  · intro x hx
    exact (hψ_one_iff x).1 hx

private lemma exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
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
section

variable [NeZero d]


private theorem smooth_compactSupport_pair_iteratedFDeriv_bound
    {p : ℝ} (hp : (d : ℝ) < p)
    {x₀ : E} {R : ℝ} (hR : 0 < R) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {f g : E → ℝ}, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
        tsupport f ⊆ Metric.ball x₀ R →
        ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
        tsupport g ⊆ Metric.ball x₀ R →
        ∀ x ∈ Metric.ball x₀ (R / 2),
          ∀ j ≤ m,
          ‖iteratedFDeriv ℝ j (fun y => f y - g y) x‖ ≤ C *
            (iteratedWeakSobolevNorm (d := d) (m + 1) (ENNReal.ofReal p) (fun y => f y - g y)
              (Metric.ball x₀ R)).toReal := by
  classical
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hp_pos : 0 < p := lt_trans hd_pos hp
  have hp_one : 1 ≤ p := by
    have hd_one_le : (1 : ℝ) ≤ d :=
      by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))
    linarith
  have hpp_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal hp_one
  have hΩ_open : IsOpen (Metric.ball x₀ R) := Metric.isOpen_ball
  have h_per_j : ∀ j, ∃ Cj : ℝ, 0 ≤ Cj ∧
      ∀ {h : E → ℝ}, ContDiff ℝ (⊤ : ℕ∞) h →
        ∀ x ∈ Metric.ball x₀ (R / 2),
          ‖iteratedFDeriv ℝ j h x‖ ≤ Cj *
            ((Finset.range (j + 2)).sum fun i =>
              (eLpNorm (fun z => ‖iteratedFDeriv ℝ i h z‖) (ENNReal.ofReal p)
                (volume.restrict (Metric.ball x₀ R))).toReal) := fun j =>
    smooth_morrey_iteratedFDeriv_bound_uniform (d := d) hp (x₀ := x₀) hR j
  let CjFun : ℕ → ℝ := fun j => Classical.choose (h_per_j j)
  have hCjFun_nn : ∀ j, 0 ≤ CjFun j := fun j => (Classical.choose_spec (h_per_j j)).1
  have hCjFun_bound : ∀ j {h : E → ℝ}, ContDiff ℝ (⊤ : ℕ∞) h →
      ∀ x ∈ Metric.ball x₀ (R / 2),
        ‖iteratedFDeriv ℝ j h x‖ ≤ CjFun j *
          ((Finset.range (j + 2)).sum fun i =>
            (eLpNorm (fun z => ‖iteratedFDeriv ℝ i h z‖) (ENNReal.ofReal p)
              (volume.restrict (Metric.ball x₀ R))).toReal) := fun j _ hh =>
    (Classical.choose_spec (h_per_j j)).2 hh
  have h_nonempty : (Finset.range (m + 1)).Nonempty :=
    ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩
  let C : ℝ := (Finset.range (m + 1)).sup' h_nonempty CjFun
  have hC_ge : ∀ j ∈ Finset.range (m + 1), CjFun j ≤ C := fun j hj =>
    Finset.le_sup' CjFun hj
  have hC_nn : 0 ≤ C :=
    le_trans (hCjFun_nn 0) (hC_ge 0 (Finset.mem_range.mpr (Nat.zero_lt_succ _)))
  refine ⟨C, hC_nn, ?_⟩
  intro f g hf_smooth hf_compact hf_support hg_smooth hg_compact hg_support x hx j hj
  set h : E → ℝ := fun y => f y - g y with hh_def
  have hh_smooth : ContDiff ℝ (⊤ : ℕ∞) h := hf_smooth.sub hg_smooth
  have hh_compact : HasCompactSupport h := hf_compact.sub hg_compact
  have hh_support : tsupport h ⊆ Metric.ball x₀ R := by
    have h_support_le : tsupport h ⊆ tsupport f ∪ tsupport g := by
      refine closure_minimal ?_ (isClosed_tsupport _ |>.union (isClosed_tsupport _))
      intro y hy
      simp only [Function.mem_support, ne_eq] at hy
      by_contra hyne
      rw [Set.mem_union] at hyne
      push Not at hyne
      obtain ⟨hyf', hyg'⟩ := hyne
      have hf_zero : f y = 0 := image_eq_zero_of_notMem_tsupport hyf'
      have hg_zero : g y = 0 := image_eq_zero_of_notMem_tsupport hyg'
      apply hy
      change f y - g y = 0
      rw [hf_zero, hg_zero]; ring
    exact h_support_le.trans (Set.union_subset hf_support hg_support)
  have hj_mem : j ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  have h_morrey := hCjFun_bound j hh_smooth x hx
  set S : ℝ := (Finset.range (j + 2)).sum fun i =>
    (eLpNorm (fun z => ‖iteratedFDeriv ℝ i h z‖) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball x₀ R))).toReal with hS_def
  have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  have hh_W : MemWkp (d := d) (m + 1) (ENNReal.ofReal p) h (Metric.ball x₀ R) :=
    MemWkp_of_smooth_compactSupport (d := d) hΩ_open hh_smooth hh_compact
      hh_support hpp_one (m + 1)
  have hh_wkp_finite : iteratedWeakSobolevNorm (d := d) (m + 1) (ENNReal.ofReal p) h
      (Metric.ball x₀ R) < ⊤ := wkpNorm_lt_top_of_memWkp hh_W
  set N : ℝ := (iteratedWeakSobolevNorm (d := d) (m + 1) (ENNReal.ofReal p) h
    (Metric.ball x₀ R)).toReal with hN_def
  have hN_nn : 0 ≤ N := ENNReal.toReal_nonneg
  have h_bridge :=
    eLpNorm_iteratedFDeriv_le_wkpNorm (d := d) hΩ_open hpp_one (m + 1)
      hh_smooth hh_compact hh_support
  have hj_le_succ : j + 2 ≤ m + 2 := by omega
  have hS_le_total :
      S ≤ ((Finset.range (m + 2)).sum fun i =>
        (eLpNorm (fun z => ‖iteratedFDeriv ℝ i h z‖) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ R))).toReal) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro k hk
      rw [Finset.mem_range] at hk ⊢
      omega
    · intros; exact ENNReal.toReal_nonneg
  have h_eLp_finite : ∀ i ∈ Finset.range (m + 2),
      eLpNorm (fun z => ‖iteratedFDeriv ℝ i h z‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball x₀ R)) ≠ ⊤ := fun i _ =>
    smooth_iteratedFDeriv_norm_eLpNorm_ne_top hp_pos hR i hh_smooth
  have h_sum_toReal_eq :
      ((Finset.range (m + 2)).sum fun i =>
        (eLpNorm (fun z => ‖iteratedFDeriv ℝ i h z‖) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ R))).toReal) =
      ((Finset.range (m + 2)).sum fun i =>
        eLpNorm (fun z => ‖iteratedFDeriv ℝ i h z‖) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ R))).toReal := by
    rw [← ENNReal.toReal_sum h_eLp_finite]
  have h_sum_le_N :
      ((Finset.range (m + 2)).sum fun i =>
        (eLpNorm (fun z => ‖iteratedFDeriv ℝ i h z‖) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x₀ R))).toReal) ≤ N := by
    rw [h_sum_toReal_eq]
    exact ENNReal.toReal_mono hh_wkp_finite.ne h_bridge
  have hCjFun_j_nn : 0 ≤ CjFun j := hCjFun_nn j
  have h_step1 : ‖iteratedFDeriv ℝ j h x‖ ≤ CjFun j * S := h_morrey
  have h_step2 : CjFun j * S ≤ C * N := by
    calc CjFun j * S
        ≤ CjFun j * ((Finset.range (m + 2)).sum fun i =>
          (eLpNorm (fun z => ‖iteratedFDeriv ℝ i h z‖) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball x₀ R))).toReal) := by
          exact mul_le_mul_of_nonneg_left hS_le_total hCjFun_j_nn
      _ ≤ CjFun j * N := mul_le_mul_of_nonneg_left h_sum_le_N hCjFun_j_nn
      _ ≤ C * N := mul_le_mul_of_nonneg_right (hC_ge j hj_mem) hN_nn
  exact le_trans h_step1 h_step2

private theorem exists_smooth_approx_seq_of_memWkp
    {p : ℝ} (hp : (d : ℝ) < p)
    {x₀ : E} {R : ℝ} (hR : 0 < R) (m : ℕ)
    {u : E → ℝ}
    (hu : MemWkp (d := d) (m + 1) (ENNReal.ofReal p) u (Metric.ball x₀ R)) :
    ∃ (χ : E → ℝ) (φ : ℕ → E → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) χ ∧
      HasCompactSupport χ ∧
      Set.range χ ⊆ Set.Icc (0 : ℝ) 1 ∧
      (∀ x ∈ Metric.closedBall x₀ (3 * R / 4), χ x = 1) ∧
      tsupport χ ⊆ Metric.closedBall x₀ (7 * R / 8) ∧
      MemWkp (d := d) (m + 1) (ENNReal.ofReal p) (fun x => χ x * u x)
        (Metric.ball x₀ R) ∧
      tsupport (fun x => χ x * u x) ⊆ Metric.closedBall x₀ (7 * R / 8) ∧
      HasCompactSupport (fun x => χ x * u x) ∧
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n)) ∧
      (∀ n, HasCompactSupport (φ n)) ∧
      (∀ n, tsupport (φ n) ⊆ Metric.ball x₀ R) ∧
      (∀ n, iteratedWeakSobolevNorm (d := d) (m + 1) (ENNReal.ofReal p)
        (fun x => χ x * u x - φ n x) (Metric.ball x₀ R) ≤
          ENNReal.ofReal (1 / (n + 1 : ℝ))) := by
  classical
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hp_pos : 0 < p := lt_trans hd_pos hp
  have hp_one : 1 ≤ p := by
    have hd_one_le : (1 : ℝ) ≤ d :=
      by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))
    linarith
  have hpp_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal hp_one
  have hp_top : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hΩ_open : IsOpen (Metric.ball x₀ R) := Metric.isOpen_ball
  obtain ⟨χ, hχ_smooth, hχ_compact, hχ_range, hχ_one, hχ_support⟩ :=
    exists_smooth_cutoff_outer (x₀ := x₀) hR
  obtain ⟨Cχ, hCχ_nn, hCχ_bound⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport hχ_smooth hχ_compact (m + 1)
  have hv_W : MemWkp (d := d) (m + 1) (ENNReal.ofReal p) (fun x => χ x * u x)
      (Metric.ball x₀ R) :=
    MemWkp.smul_smooth_bounded (d := d) (m + 1) hpp_one hΩ_open hχ_smooth
      (C := Cχ) (fun j hj x _ => hCχ_bound x j hj) hu
  have hv_support : tsupport (fun x => χ x * u x) ⊆ Metric.closedBall x₀ (7 * R / 8) := by
    have h_support_sub_χ : tsupport (fun x => χ x * u x) ⊆ tsupport χ := by
      refine closure_mono ?_
      intro y hy
      simp only [Function.mem_support, ne_eq] at hy ⊢
      intro hyne
      apply hy
      rw [hyne, zero_mul]
    exact h_support_sub_χ.trans hχ_support
  have h_closed_subset_open : Metric.closedBall x₀ (7 * R / 8) ⊆ Metric.ball x₀ R := by
    intro z hz; rw [Metric.mem_closedBall] at hz; rw [Metric.mem_ball]; linarith
  have hv_support_open : tsupport (fun x => χ x * u x) ⊆ Metric.ball x₀ R :=
    hv_support.trans h_closed_subset_open
  have hv_compact : HasCompactSupport (fun x => χ x * u x) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (x := x₀) (7 * R / 8)) ?_
    exact (subset_tsupport _).trans hv_support
  have h_pick : ∀ n : ℕ, ∃ φₙ : E → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φₙ ∧
      HasCompactSupport φₙ ∧
      tsupport φₙ ⊆ Metric.ball x₀ R ∧
      iteratedWeakSobolevNorm (d := d) (m + 1) (ENNReal.ofReal p)
        (fun x => χ x * u x - φₙ x) (Metric.ball x₀ R) ≤
          ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
    intro n
    have hε_pos : 0 < (1 / (n + 1 : ℝ)) := by
      apply div_pos
      · norm_num
      · exact_mod_cast Nat.zero_lt_succ n
    obtain ⟨φn, hφn_smooth, hφn_compact, hφn_support, hφn_close⟩ :=
      MemWkp.exists_smooth_compactSupport_approx (d := d) hΩ_open (m + 1) (ENNReal.ofReal p)
        hpp_one hp_top hv_W hv_compact hv_support_open _ hε_pos
    exact ⟨φn, hφn_smooth, hφn_compact, hφn_support, hφn_close⟩
  let φ : ℕ → E → ℝ := fun n => Classical.choose (h_pick n)
  have hφ_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n) := fun n =>
    (Classical.choose_spec (h_pick n)).1
  have hφ_compact : ∀ n, HasCompactSupport (φ n) := fun n =>
    (Classical.choose_spec (h_pick n)).2.1
  have hφ_support : ∀ n, tsupport (φ n) ⊆ Metric.ball x₀ R := fun n =>
    (Classical.choose_spec (h_pick n)).2.2.1
  have hφ_close : ∀ n, iteratedWeakSobolevNorm (d := d) (m + 1) (ENNReal.ofReal p)
      (fun x => χ x * u x - φ n x) (Metric.ball x₀ R) ≤
        ENNReal.ofReal (1 / (n + 1 : ℝ)) := fun n =>
    (Classical.choose_spec (h_pick n)).2.2.2
  exact ⟨χ, φ, hχ_smooth, hχ_compact, hχ_range, hχ_one, hχ_support,
    hv_W, hv_support, hv_compact,
    hφ_smooth, hφ_compact, hφ_support, hφ_close⟩

end

private lemma norm_iteratedFDeriv_mul_left_bound
    {ψ : E → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_compact : HasCompactSupport ψ)
    (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {f : E → ℝ}, ContDiff ℝ (⊤ : ℕ∞) f →
        ∀ x : E, ∀ j ≤ m,
          ‖iteratedFDeriv ℝ j (fun y => ψ y * f y) x‖ ≤
            C * ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ i f x‖ := by
  classical
  obtain ⟨Cψ, hCψ_nn, hCψ_bound⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport hψ_smooth hψ_compact m
  have h_simple_bound : ∀ n i : ℕ, ((n.choose i : ℕ) : ℝ) ≤ 2 ^ n := by
    intro n i
    exact_mod_cast Nat.choose_le_two_pow n i
  refine ⟨Cψ * 2 ^ m, mul_nonneg hCψ_nn (by positivity), ?_⟩
  intro f hf x j hj
  have hψ_top : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ := by simpa using hψ_smooth
  have hf_top : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f := by simpa using hf
  have hj_le' : (j : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    have h : (j : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
    exact_mod_cast h
  have h_leibniz : ‖iteratedFDeriv ℝ j (fun y => ψ y * f y) x‖ ≤
      ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψ x‖ * ‖iteratedFDeriv ℝ (j - i) f x‖ :=
    norm_iteratedFDeriv_mul_le (𝕜 := ℝ)
      (n := j) (f := ψ) (g := f) (x := x) (N := ((⊤ : ℕ∞) : WithTop ℕ∞))
      hψ_top hf_top hj_le'
  refine h_leibniz.trans ?_
  have h_each : ∀ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψ x‖ * ‖iteratedFDeriv ℝ (j - i) f x‖ ≤
      (2 ^ m * Cψ) * ‖iteratedFDeriv ℝ (j - i) f x‖ := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hi_le_j : i ≤ j := Nat.lt_succ_iff.mp hi
    have hψ_bd : ‖iteratedFDeriv ℝ i ψ x‖ ≤ Cψ :=
      hCψ_bound x i (le_trans hi_le_j hj)
    have h_choose : ((j.choose i : ℕ) : ℝ) ≤ 2 ^ m := by
      have h1 : ((j.choose i : ℕ) : ℝ) ≤ 2 ^ j := h_simple_bound j i
      have h2 : (2 : ℝ) ^ j ≤ 2 ^ m :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj
      exact le_trans h1 h2
    have h_lhs : ((j.choose i : ℕ) : ℝ) * ‖iteratedFDeriv ℝ i ψ x‖ ≤ 2 ^ m * Cψ := by
      have h1 : ((j.choose i : ℕ) : ℝ) * ‖iteratedFDeriv ℝ i ψ x‖ ≤
          ((j.choose i : ℕ) : ℝ) * Cψ :=
        mul_le_mul_of_nonneg_left hψ_bd (by positivity)
      have h2 : ((j.choose i : ℕ) : ℝ) * Cψ ≤ 2 ^ m * Cψ :=
        mul_le_mul_of_nonneg_right h_choose hCψ_nn
      exact le_trans h1 h2
    exact mul_le_mul_of_nonneg_right h_lhs (norm_nonneg _)
  have h_reindex : ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ (j - i) f x‖ =
      ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ i f x‖ := by
    refine Finset.sum_nbij' (fun i : ℕ => j - i) (fun i : ℕ => j - i)
      (fun i hi => by simp only [Finset.mem_range] at hi ⊢; omega)
      (fun i hi => by simp only [Finset.mem_range] at hi ⊢; omega)
      (fun i hi => by simp only [Finset.mem_range] at hi; omega)
      (fun i hi => by simp only [Finset.mem_range] at hi; omega)
      (fun _ _ => rfl)
  have h2pow_Cψ_nn : 0 ≤ (2 : ℝ) ^ m * Cψ := by positivity
  calc ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψ x‖ * ‖iteratedFDeriv ℝ (j - i) f x‖
      ≤ ∑ i ∈ Finset.range (j + 1),
          (2 ^ m * Cψ) * ‖iteratedFDeriv ℝ (j - i) f x‖ := Finset.sum_le_sum h_each
    _ = (2 ^ m * Cψ) *
          ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ (j - i) f x‖ := by
        rw [Finset.mul_sum]
    _ = (2 ^ m * Cψ) *
          ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ i f x‖ := by
        rw [h_reindex]
    _ = (Cψ * 2 ^ m) *
          ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ i f x‖ := by ring
section

variable [NeZero d]


private theorem smooth_compactSupport_pair_iteratedFDeriv_mul_bound
    {p : ℝ} (hp : (d : ℝ) < p)
    {x₀ : E} {R : ℝ} (hR : 0 < R) (m : ℕ)
    {ψ : E → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_compact : HasCompactSupport ψ)
    (hψ_support_ball : tsupport ψ ⊆ Metric.ball x₀ (R / 2)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {f g : E → ℝ}, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
        tsupport f ⊆ Metric.ball x₀ R →
        ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
        tsupport g ⊆ Metric.ball x₀ R →
        ∀ x : E, ∀ j ≤ m,
          ‖iteratedFDeriv ℝ j (fun y => ψ y * (f y - g y)) x‖ ≤ C *
            (iteratedWeakSobolevNorm (d := d) (m + 1) (ENNReal.ofReal p) (fun y => f y - g y)
              (Metric.ball x₀ R)).toReal := by
  classical
  obtain ⟨C_inner, hC_inner_nn, hC_inner_bound⟩ :=
    smooth_compactSupport_pair_iteratedFDeriv_bound (d := d) hp hR m
  obtain ⟨C_leibniz, hC_leibniz_nn, hC_leibniz_bound⟩ :=
    norm_iteratedFDeriv_mul_left_bound (d := d) hψ_smooth hψ_compact m
  refine ⟨C_leibniz * (m + 1 : ℕ) * C_inner,
    by positivity, ?_⟩
  intro f g hf_smooth hf_compact hf_support hg_smooth hg_compact hg_support x j hj
  by_cases hx_support : x ∈ tsupport ψ
  · have hx_in_ball : x ∈ Metric.ball x₀ (R / 2) := hψ_support_ball hx_support
    have hfg_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun y => f y - g y) := hf_smooth.sub hg_smooth
    have h_leibniz := hC_leibniz_bound hfg_smooth x j hj
    refine h_leibniz.trans ?_
    have h_each : ∀ i ∈ Finset.range (j + 1),
        ‖iteratedFDeriv ℝ i (fun y => f y - g y) x‖ ≤ C_inner *
          (iteratedWeakSobolevNorm (d := d) (m + 1) (ENNReal.ofReal p) (fun y => f y - g y)
            (Metric.ball x₀ R)).toReal := by
      intro i hi
      rw [Finset.mem_range] at hi
      have hi_le : i ≤ m := Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le hi (Nat.succ_le_succ hj))
      exact hC_inner_bound hf_smooth hf_compact hf_support hg_smooth hg_compact hg_support x hx_in_ball i hi_le
    set NormDiff : ℝ :=
      (iteratedWeakSobolevNorm (d := d) (m + 1) (ENNReal.ofReal p) (fun y => f y - g y)
        (Metric.ball x₀ R)).toReal with hNormDiff_def
    have hNormDiff_nn : 0 ≤ NormDiff := ENNReal.toReal_nonneg
    have h_sum_le : ∑ i ∈ Finset.range (j + 1),
        ‖iteratedFDeriv ℝ i (fun y => f y - g y) x‖ ≤
        ∑ _i ∈ Finset.range (j + 1), C_inner * NormDiff :=
      Finset.sum_le_sum h_each
    have h_const_sum : ∑ _i ∈ Finset.range (j + 1), C_inner * NormDiff =
        ((j + 1 : ℕ) : ℝ) * (C_inner * NormDiff) := by
      rw [Finset.sum_const, Finset.card_range]
      push_cast
      ring
    calc C_leibniz * ∑ i ∈ Finset.range (j + 1),
            ‖iteratedFDeriv ℝ i (fun y => f y - g y) x‖
        ≤ C_leibniz * (∑ _i ∈ Finset.range (j + 1), C_inner * NormDiff) :=
          mul_le_mul_of_nonneg_left h_sum_le hC_leibniz_nn
      _ = C_leibniz * (((j + 1 : ℕ) : ℝ) * (C_inner * NormDiff)) := by rw [h_const_sum]
      _ = (C_leibniz * ((j + 1 : ℕ) : ℝ)) * (C_inner * NormDiff) := by ring
      _ ≤ (C_leibniz * ((m + 1 : ℕ) : ℝ)) * (C_inner * NormDiff) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg hC_inner_nn hNormDiff_nn)
          exact mul_le_mul_of_nonneg_left
            (by exact_mod_cast Nat.succ_le_succ hj) hC_leibniz_nn
      _ = (C_leibniz * ((m + 1 : ℕ) : ℝ) * C_inner) * NormDiff := by ring
  · have h_zero_neighborhood : ∀ᶠ y in 𝓝 x, ψ y = 0 := by
      have h_open : IsOpen (tsupport ψ)ᶜ := isClosed_tsupport ψ |>.isOpen_compl
      have h_eq : ∀ y ∈ (tsupport ψ)ᶜ, ψ y = 0 := fun y hy =>
        image_eq_zero_of_notMem_tsupport hy
      exact Filter.eventually_of_mem (h_open.mem_nhds hx_support) h_eq
    have h_prod_zero_neighborhood : ∀ᶠ y in 𝓝 x, ψ y * (f y - g y) = 0 := by
      filter_upwards [h_zero_neighborhood] with y hy
      rw [hy, zero_mul]
    have h_iter_zero : iteratedFDeriv ℝ j (fun y => ψ y * (f y - g y)) x = 0 := by
      have h_eq : (fun y => ψ y * (f y - g y)) =ᶠ[𝓝 x] (fun _ : E => (0 : ℝ)) :=
        h_prod_zero_neighborhood
      have h_iter_eq := Filter.EventuallyEq.iteratedFDeriv ℝ h_eq j
      have h_at_x := h_iter_eq.self_of_nhds
      rw [h_at_x, iteratedFDeriv_fun_zero, Pi.zero_apply]
    rw [h_iter_zero, norm_zero]
    have hN_nn : 0 ≤ (iteratedWeakSobolevNorm (d := d) (m + 1) (ENNReal.ofReal p)
      (fun y => f y - g y)
      (Metric.ball x₀ R)).toReal := ENNReal.toReal_nonneg
    have hC_nn : 0 ≤ C_leibniz * ↑(m + 1) * C_inner := by positivity
    exact mul_nonneg hC_nn hN_nn

private noncomputable def cauchyIteratedLimit
    (j : ℕ) (g : ℕ → E → ℝ)
    (h_cauchy : ∀ x : E, CauchySeq (fun n => iteratedFDeriv ℝ j (g n) x)) :
    E → ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℝ :=
  fun x => Classical.choose (cauchySeq_tendsto_of_complete (h_cauchy x))

end

private lemma cauchyIteratedLimit_tendsto
    {j : ℕ} {g : ℕ → E → ℝ}
    (h_cauchy : ∀ x : E, CauchySeq (fun n => iteratedFDeriv ℝ j (g n) x))
    (x : E) :
    Filter.Tendsto (fun n => iteratedFDeriv ℝ j (g n) x) Filter.atTop
      (𝓝 (cauchyIteratedLimit j g h_cauchy x)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete (h_cauchy x))

private lemma cauchy_at_of_uniformCauchy
    {j : ℕ} {g : ℕ → E → ℝ}
    (h_uniform_cauchy : ∀ ε > 0, ∃ N : ℕ, ∀ n n', N ≤ n → N ≤ n' → ∀ x : E,
      ‖iteratedFDeriv ℝ j (g n) x - iteratedFDeriv ℝ j (g n') x‖ ≤ ε)
    (x : E) :
    CauchySeq (fun n => iteratedFDeriv ℝ j (g n) x) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := h_uniform_cauchy (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn n' hn' => ?_⟩
  rw [dist_eq_norm]
  exact lt_of_le_of_lt (hN n n' hn hn' x) (by linarith)

private lemma cauchyIteratedLimit_tendstoUniformly
    {j : ℕ} {g : ℕ → E → ℝ}
    (h_uniform_cauchy : ∀ ε > 0, ∃ N : ℕ, ∀ n n', N ≤ n → N ≤ n' → ∀ x : E,
      ‖iteratedFDeriv ℝ j (g n) x - iteratedFDeriv ℝ j (g n') x‖ ≤ ε) :
    TendstoUniformly (fun n x => iteratedFDeriv ℝ j (g n) x)
      (cauchyIteratedLimit j g (cauchy_at_of_uniformCauchy h_uniform_cauchy)) Filter.atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := h_uniform_cauchy (ε / 2) (half_pos hε)
  refine Filter.eventually_atTop.mpr ⟨N, fun n hn x => ?_⟩
  set Lx := cauchyIteratedLimit j g (cauchy_at_of_uniformCauchy h_uniform_cauchy) x with hLx_def
  have h_limit_norm :
      Filter.Tendsto
        (fun n' => ‖iteratedFDeriv ℝ j (g n) x - iteratedFDeriv ℝ j (g n') x‖)
        Filter.atTop
        (𝓝 ‖iteratedFDeriv ℝ j (g n) x - Lx‖) :=
    (continuous_norm.tendsto _).comp
      (tendsto_const_nhds.sub
        (cauchyIteratedLimit_tendsto (cauchy_at_of_uniformCauchy h_uniform_cauchy) x))
  have h_eventually : ∀ᶠ n' in Filter.atTop,
      ‖iteratedFDeriv ℝ j (g n) x - iteratedFDeriv ℝ j (g n') x‖ ≤ ε / 2 :=
    Filter.eventually_atTop.mpr ⟨N, fun n' hn' => hN n n' hn hn' x⟩
  have h_norm_le : ‖iteratedFDeriv ℝ j (g n) x - Lx‖ ≤ ε / 2 :=
    le_of_tendsto h_limit_norm h_eventually
  rw [dist_eq_norm]
  have h_norm_neg : ‖Lx - iteratedFDeriv ℝ j (g n) x‖ =
      ‖iteratedFDeriv ℝ j (g n) x - Lx‖ := by
    rw [norm_sub_rev]
  rw [h_norm_neg]
  linarith

noncomputable def cauchyLimitFun
    (g : ℕ → E → ℝ)
    (h_uniform_cauchy : ∀ ε > 0, ∃ N : ℕ, ∀ n n', N ≤ n → N ≤ n' → ∀ x : E,
      ‖g n x - g n' x‖ ≤ ε) : E → ℝ :=
  fun x => Classical.choose
    (cauchySeq_tendsto_of_complete (u := fun n => g n x) (by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := h_uniform_cauchy (ε / 2) (half_pos hε)
      refine ⟨N, fun n hn n' hn' => ?_⟩
      rw [dist_eq_norm]
      exact lt_of_le_of_lt (hN n n' hn hn' x) (by linarith)))

lemma cauchyLimitFun_tendsto
    {g : ℕ → E → ℝ}
    (h_uniform_cauchy : ∀ ε > 0, ∃ N : ℕ, ∀ n n', N ≤ n → N ≤ n' → ∀ x : E,
      ‖g n x - g n' x‖ ≤ ε)
    (x : E) :
    Filter.Tendsto (fun n => g n x) Filter.atTop
      (𝓝 (cauchyLimitFun g h_uniform_cauchy x)) := by
  have h_cauchy : CauchySeq (fun n => g n x) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := h_uniform_cauchy (ε / 2) (half_pos hε)
    refine ⟨N, fun n hn n' hn' => ?_⟩
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (hN n n' hn hn' x) (by linarith)
  have h_spec := Classical.choose_spec (cauchySeq_tendsto_of_complete h_cauchy)
  unfold cauchyLimitFun
  exact h_spec

theorem iteratedFDeriv_cauchyLimitFun_eq
    (m : ℕ) {g : ℕ → E → ℝ} (hg_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (g n))
    (h_uniform_cauchy_C0 : ∀ ε > 0, ∃ N : ℕ, ∀ n n', N ≤ n → N ≤ n' → ∀ x : E,
      ‖g n x - g n' x‖ ≤ ε)
    (h_uniform_cauchy : ∀ j ≤ m, ∀ ε > 0, ∃ N : ℕ, ∀ n n', N ≤ n → N ≤ n' → ∀ x : E,
      ‖iteratedFDeriv ℝ j (g n) x - iteratedFDeriv ℝ j (g n') x‖ ≤ ε) :
    ContDiff ℝ m (cauchyLimitFun g h_uniform_cauchy_C0) ∧
    ∀ j, j ≤ m → ∀ x : E,
      Filter.Tendsto (fun n => iteratedFDeriv ℝ j (g n) x) Filter.atTop
        (𝓝 (iteratedFDeriv ℝ j (cauchyLimitFun g h_uniform_cauchy_C0) x)) := by
  classical
  set u_smooth := cauchyLimitFun g h_uniform_cauchy_C0 with hu_smooth_def
  have hu_tendsto : ∀ x, Filter.Tendsto (fun n => g n x) Filter.atTop (𝓝 (u_smooth x)) :=
    cauchyLimitFun_tendsto h_uniform_cauchy_C0
  have h_cauchy_at : ∀ j ≤ m, ∀ x : E,
      CauchySeq (fun n => iteratedFDeriv ℝ j (g n) x) := fun j hj =>
    cauchy_at_of_uniformCauchy (h_uniform_cauchy j hj)
  let D : ∀ (j : ℕ), j ≤ m → E → ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℝ :=
    fun j hj => cauchyIteratedLimit j g (h_cauchy_at j hj)
  have hD_tendsto : ∀ j (hj : j ≤ m), ∀ x : E,
      Filter.Tendsto (fun n => iteratedFDeriv ℝ j (g n) x) Filter.atTop (𝓝 (D j hj x)) :=
    fun j hj x => cauchyIteratedLimit_tendsto (h_cauchy_at j hj) x
  have h_uniform_D : ∀ j (hj : j ≤ m),
      TendstoUniformly (fun n x => iteratedFDeriv ℝ j (g n) x) (D j hj) Filter.atTop :=
    fun j hj => cauchyIteratedLimit_tendstoUniformly (h_uniform_cauchy j hj)
  have hD_continuous : ∀ j (hj : j ≤ m), Continuous (D j hj) := by
    intro j hj
    have h_each_cont : ∀ n, Continuous (fun x => iteratedFDeriv ℝ j (g n) x) := fun n => by
      have h_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun x => iteratedFDeriv ℝ j (g n) x) := by
        have h := (hg_smooth n).iteratedFDeriv_right' (m := (⊤ : ℕ∞)) (i := j)
        simpa using h
      exact h_smooth.continuous
    exact (h_uniform_D j hj).continuous
      ((Filter.Eventually.of_forall h_each_cont).frequently)
  have h_diff_D_at : ∀ j (hj_succ : j + 1 ≤ m), ∀ x : E,
      HasFDerivAt (D j (le_of_lt hj_succ))
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) ℝ)
          (D (j + 1) hj_succ x)) x := by
    intro j hj_succ x
    set LC := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) ℝ with hLC_def
    have hg_diff_at : ∀ n y, DifferentiableAt ℝ
        (fun z => iteratedFDeriv ℝ j (g n) z) y := fun n y => by
      have h_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun z => iteratedFDeriv ℝ j (g n) z) := by
        have h := (hg_smooth n).iteratedFDeriv_right' (m := (⊤ : ℕ∞)) (i := j)
        simpa using h
      exact h_smooth.differentiable (by simp) |>.differentiableAt
    have h_fderiv_eq : ∀ n y, fderiv ℝ (iteratedFDeriv ℝ j (g n)) y =
        LC (iteratedFDeriv ℝ (j + 1) (g n) y) := fun n y => rfl
    have h_tendsto_LC :
        TendstoUniformly (fun n y => LC (iteratedFDeriv ℝ (j + 1) (g n) y))
          (fun y => LC (D (j + 1) hj_succ y)) Filter.atTop := by
      have h_isom : Isometry LC := LC.isometry
      have h_uniform := h_uniform_D (j + 1) hj_succ
      rw [Metric.tendstoUniformly_iff] at h_uniform ⊢
      intro ε hε
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h_uniform ε hε)
      refine Filter.eventually_atTop.mpr ⟨N, fun n hn y => ?_⟩
      have h_dist := hN n hn y
      rw [dist_eq_norm] at h_dist ⊢
      rw [← LC.map_sub, h_isom.norm_map_of_map_zero (map_zero _)]
      exact h_dist
    have h_tendsto_fderiv :
        TendstoUniformly (fun n y => fderiv ℝ (iteratedFDeriv ℝ j (g n)) y)
          (fun y => LC (D (j + 1) hj_succ y)) Filter.atTop := by
      rw [Metric.tendstoUniformly_iff] at h_tendsto_LC ⊢
      intro ε hε
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h_tendsto_LC ε hε)
      refine Filter.eventually_atTop.mpr ⟨N, fun n hn y => ?_⟩
      rw [h_fderiv_eq n y]
      exact hN n hn y
    refine hasFDerivAt_of_tendstoUniformly (f := fun n y => iteratedFDeriv ℝ j (g n) y)
      h_tendsto_fderiv ?_ ?_ x
    · intro n y'
      exact (hg_diff_at n y').hasFDerivAt
    · intro y'
      exact hD_tendsto j (le_of_lt hj_succ) y'
  have h_iter_eq_D : ∀ j (hj : j ≤ m), ∀ x : E,
      iteratedFDeriv ℝ j u_smooth x = D j hj x := by
    intro j hj
    induction j with
    | zero =>
        intro x
        apply ContinuousMultilinearMap.ext
        intro m_tup
        rw [iteratedFDeriv_zero_apply]
        have h_tendsto_eval : Filter.Tendsto
            (fun n => iteratedFDeriv ℝ 0 (g n) x m_tup) Filter.atTop (𝓝 (D 0 hj x m_tup)) := by
          let eval0 : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ →L[ℝ] ℝ :=
            ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => E) ℝ m_tup
          exact (eval0.continuous.tendsto _).comp (hD_tendsto 0 hj x)
        have h_eq_g : ∀ n, iteratedFDeriv ℝ 0 (g n) x m_tup = g n x := fun n =>
          iteratedFDeriv_zero_apply m_tup
        simp_rw [h_eq_g] at h_tendsto_eval
        exact tendsto_nhds_unique (hu_tendsto x) h_tendsto_eval
    | succ k ih =>
        intro x
        have hk_lt : k + 1 ≤ m := hj
        have hk_le : k ≤ m := le_of_lt (Nat.lt_of_succ_le hk_lt)
        have ih' : ∀ y, iteratedFDeriv ℝ k u_smooth y = D k hk_le y := ih hk_le
        set LC := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) ℝ
        have h_D_diff := h_diff_D_at k hk_lt x
        have h_fn_eq : (fun y => iteratedFDeriv ℝ k u_smooth y) = D k hk_le :=
          funext ih'
        have h_iter_diff : HasFDerivAt (fun y => iteratedFDeriv ℝ k u_smooth y)
            (LC (D (k + 1) hk_lt x)) x := by
          rw [h_fn_eq]; exact h_D_diff
        have h_fderiv : fderiv ℝ (fun y => iteratedFDeriv ℝ k u_smooth y) x =
            LC (D (k + 1) hk_lt x) := h_iter_diff.fderiv
        have h_fderiv_iter :
            fderiv ℝ (fun y => iteratedFDeriv ℝ k u_smooth y) x =
              LC (iteratedFDeriv ℝ (k + 1) u_smooth x) := rfl
        have h_LC_eq : LC (iteratedFDeriv ℝ (k + 1) u_smooth x) = LC (D (k + 1) hk_lt x) := by
          rw [← h_fderiv_iter]; exact h_fderiv
        exact LC.injective h_LC_eq
  refine ⟨?_, ?_⟩
  · rw [contDiff_nat_iff_continuous_differentiable]
    refine ⟨?_, ?_⟩
    · intro j hj
      have h_fn_eq : (fun x => iteratedFDeriv ℝ j u_smooth x) = D j hj :=
        funext (h_iter_eq_D j hj)
      rw [h_fn_eq]
      exact hD_continuous j hj
    · intro j hj_lt y
      have hj_succ : j + 1 ≤ m := hj_lt
      have h_fn_eq : (fun z => iteratedFDeriv ℝ j u_smooth z) = D j (le_of_lt hj_lt) :=
        funext (h_iter_eq_D j (le_of_lt hj_lt))
      rw [h_fn_eq]
      exact (h_diff_D_at j hj_succ y).differentiableAt
  · intro j hj x
    rw [h_iter_eq_D j hj]
    exact hD_tendsto j hj x

variable [NeZero d] in
theorem morrey_iteratedFDeriv_representative
    {p : ℝ} (hp : (d : ℝ) < p)
    {x₀ : E} {R : ℝ} (hR : 0 < R) (m : ℕ)
    {u : E → ℝ}
    (hu : MemWkp (d := d) (m + 1) (ENNReal.ofReal p) u (Metric.ball x₀ R)) :
    ∃ u_smooth : E → ℝ,
      ContDiff ℝ m u_smooth ∧
      u =ᵐ[volume.restrict (Metric.ball x₀ (R / 4))] u_smooth := by
  classical
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hp_pos : 0 < p := lt_trans hd_pos hp
  have hp_one : 1 ≤ p := by
    have hd_one_le : (1 : ℝ) ≤ d :=
      by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))
    linarith
  have hpp_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal hp_one
  have hΩ_open : IsOpen (Metric.ball x₀ R) := Metric.isOpen_ball
  obtain ⟨χ, φ, hχ_smooth, hχ_compact, hχ_range, hχ_one, hχ_support,
    hv_W, _hv_support_closed, _hv_compact,
    hφ_smooth, hφ_compact, hφ_support, hφ_close⟩ :=
    exists_smooth_approx_seq_of_memWkp (d := d) hp hR m hu
  obtain ⟨ψ, hψ_smooth, hψ_compact, _hψ_range, hψ_one, hψ_support⟩ :=
    exists_smooth_cutoff_smaller (x₀ := x₀) hR
  have hψ_support_ball : tsupport ψ ⊆ Metric.ball x₀ (R / 2) := by
    refine hψ_support.trans ?_
    intro z hz; rw [Metric.mem_closedBall] at hz; rw [Metric.mem_ball]; linarith
  obtain ⟨Cpair, hCpair_nn, hCpair_bound⟩ :=
    smooth_compactSupport_pair_iteratedFDeriv_mul_bound (d := d) hp hR m
      hψ_smooth hψ_compact hψ_support_ball
  let g : ℕ → E → ℝ := fun n y => ψ y * φ n y
  have hg_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (g n) := fun n =>
    hψ_smooth.mul (hφ_smooth n)
  have hφ_W : ∀ n, MemWkp (d := d) (m + 1) (ENNReal.ofReal p) (φ n)
      (Metric.ball x₀ R) := fun n =>
    MemWkp_of_smooth_compactSupport (d := d) hΩ_open (hφ_smooth n) (hφ_compact n)
      (hφ_support n) hpp_one (m + 1)
  have hφ_cauchy_wkp : ∀ ε > 0, ∃ N : ℕ, ∀ n n', N ≤ n → N ≤ n' →
      iteratedWeakSobolevNorm (d := d) (m + 1) (ENNReal.ofReal p)
        (fun y => φ n y - φ n' y) (Metric.ball x₀ R) ≤ ENNReal.ofReal ε := by
    intro ε hε
    have hε_half_pos : 0 < ε / 2 := half_pos hε
    obtain ⟨N₀, hN₀⟩ := exists_nat_one_div_lt hε_half_pos
    refine ⟨N₀, fun n n' hn hn' => ?_⟩
    have h_decomp : (fun y => φ n y - φ n' y) =
        fun y => -(χ y * u y - φ n y) + (χ y * u y - φ n' y) := by
      funext y; ring
    rw [h_decomp]
    have h_mem_minus : MemWkp (d := d) (m + 1) (ENNReal.ofReal p)
        (fun y => -(χ y * u y - φ n y)) (Metric.ball x₀ R) :=
      MemWkp.neg (d := d) hpp_one hΩ_open
        (MemWkp.sub (d := d) hpp_one hΩ_open hv_W (hφ_W n))
    have h_mem_plus : MemWkp (d := d) (m + 1) (ENNReal.ofReal p)
        (fun y => χ y * u y - φ n' y) (Metric.ball x₀ R) :=
      MemWkp.sub (d := d) hpp_one hΩ_open hv_W (hφ_W n')
    have h_triangle :=
      wkpNorm_add_le (d := d) hpp_one hΩ_open h_mem_minus h_mem_plus
    have h_norm_neg : iteratedWeakSobolevNorm (d := d) (m + 1) (ENNReal.ofReal p)
        (fun y => -(χ y * u y - φ n y)) (Metric.ball x₀ R) =
        iteratedWeakSobolevNorm (d := d) (m + 1) (ENNReal.ofReal p)
          (fun y => χ y * u y - φ n y) (Metric.ball x₀ R) := by
      have h_smul_eq : (fun y => -(χ y * u y - φ n y)) =
          fun y => (-1 : ℝ) * (χ y * u y - φ n y) := by
        funext y; ring
      rw [h_smul_eq, wkpNorm_const_smul (d := d) hpp_one hΩ_open
        (MemWkp.sub (d := d) hpp_one hΩ_open hv_W (hφ_W n)) (-1)]
      simp
    rw [h_norm_neg] at h_triangle
    refine le_trans h_triangle ?_
    have h_n_le : (1 / (n + 1 : ℝ)) ≤ ε / 2 := by
      have h_pos_N : 0 < (N₀ + 1 : ℝ) := by positivity
      have h_pos_n : 0 < (n + 1 : ℝ) := by positivity
      have h_n_inc : ((N₀ : ℝ) + 1) ≤ (n + 1 : ℝ) := by
        have : N₀ + 1 ≤ n + 1 := Nat.succ_le_succ hn
        exact_mod_cast this
      have h_inv_inc : (1 / (n + 1 : ℝ)) ≤ 1 / ((N₀ : ℝ) + 1) :=
        one_div_le_one_div_of_le h_pos_N h_n_inc
      exact le_trans h_inv_inc (le_of_lt hN₀)
    have h_n'_le : (1 / (n' + 1 : ℝ)) ≤ ε / 2 := by
      have h_pos_N : 0 < (N₀ + 1 : ℝ) := by positivity
      have h_pos_n' : 0 < (n' + 1 : ℝ) := by positivity
      have h_n_inc : ((N₀ : ℝ) + 1) ≤ (n' + 1 : ℝ) := by
        have : N₀ + 1 ≤ n' + 1 := Nat.succ_le_succ hn'
        exact_mod_cast this
      have h_inv_inc : (1 / (n' + 1 : ℝ)) ≤ 1 / ((N₀ : ℝ) + 1) :=
        one_div_le_one_div_of_le h_pos_N h_n_inc
      exact le_trans h_inv_inc (le_of_lt hN₀)
    have h_n_ennreal : ENNReal.ofReal (1 / (n + 1 : ℝ)) ≤ ENNReal.ofReal (ε / 2) :=
      ENNReal.ofReal_le_ofReal h_n_le
    have h_n'_ennreal : ENNReal.ofReal (1 / (n' + 1 : ℝ)) ≤ ENNReal.ofReal (ε / 2) :=
      ENNReal.ofReal_le_ofReal h_n'_le
    have h_combined :
        iteratedWeakSobolevNorm (d := d) (m + 1) (ENNReal.ofReal p) (fun y => χ y * u y - φ n y)
          (Metric.ball x₀ R) +
        iteratedWeakSobolevNorm (d := d) (m + 1) (ENNReal.ofReal p) (fun y => χ y * u y - φ n' y)
          (Metric.ball x₀ R) ≤
        ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
      add_le_add (le_trans (hφ_close n) h_n_ennreal) (le_trans (hφ_close n') h_n'_ennreal)
    refine le_trans h_combined ?_
    rw [← ENNReal.ofReal_add (le_of_lt hε_half_pos) (le_of_lt hε_half_pos)]
    rw [show ε / 2 + ε / 2 = ε from by ring]
  have hg_uniform_cauchy : ∀ j ≤ m, ∀ ε > 0, ∃ N : ℕ, ∀ n n', N ≤ n → N ≤ n' → ∀ x : E,
      ‖iteratedFDeriv ℝ j (g n) x - iteratedFDeriv ℝ j (g n') x‖ ≤ ε := by
    intro j hj ε hε
    by_cases hCpair_zero : Cpair = 0
    · refine ⟨0, fun n n' _ _ x => ?_⟩
      have h_iter_sub :
          iteratedFDeriv ℝ j (g n) x - iteratedFDeriv ℝ j (g n') x =
            iteratedFDeriv ℝ j (fun y => g n y - g n' y) x := by
        have h_fn_eq : (fun y => g n y - g n' y) = g n - g n' := rfl
        rw [h_fn_eq, iteratedFDeriv_sub_apply
          ((hg_smooth n).of_le (by exact_mod_cast le_top : (j : WithTop ℕ∞) ≤
                                     ((⊤ : ℕ∞) : WithTop ℕ∞))).contDiffAt
          ((hg_smooth n').of_le (by exact_mod_cast le_top : (j : WithTop ℕ∞) ≤
                                      ((⊤ : ℕ∞) : WithTop ℕ∞))).contDiffAt]
      have h_diff_eq : (fun y => g n y - g n' y) = fun y => ψ y * (φ n y - φ n' y) := by
        funext y; simp [g]; ring
      rw [h_iter_sub, h_diff_eq]
      have h_pair := hCpair_bound (hφ_smooth n) (hφ_compact n) (hφ_support n)
        (hφ_smooth n') (hφ_compact n') (hφ_support n') x j hj
      rw [hCpair_zero, zero_mul] at h_pair
      exact le_trans h_pair (le_of_lt hε)
    · push Not at hCpair_zero
      have hCpair_pos : 0 < Cpair := lt_of_le_of_ne hCpair_nn (Ne.symm hCpair_zero)
      have hε_div : 0 < ε / Cpair := div_pos hε hCpair_pos
      obtain ⟨N, hN⟩ := hφ_cauchy_wkp (ε / Cpair) hε_div
      refine ⟨N, fun n n' hn hn' x => ?_⟩
      have h_iter_sub :
          iteratedFDeriv ℝ j (g n) x - iteratedFDeriv ℝ j (g n') x =
            iteratedFDeriv ℝ j (fun y => g n y - g n' y) x := by
        have h_fn_eq : (fun y => g n y - g n' y) = g n - g n' := rfl
        rw [h_fn_eq, iteratedFDeriv_sub_apply
          ((hg_smooth n).of_le (by exact_mod_cast le_top : (j : WithTop ℕ∞) ≤
                                     ((⊤ : ℕ∞) : WithTop ℕ∞))).contDiffAt
          ((hg_smooth n').of_le (by exact_mod_cast le_top : (j : WithTop ℕ∞) ≤
                                      ((⊤ : ℕ∞) : WithTop ℕ∞))).contDiffAt]
      have h_diff_eq : (fun y => g n y - g n' y) = fun y => ψ y * (φ n y - φ n' y) := by
        funext y; simp [g]; ring
      rw [h_iter_sub, h_diff_eq]
      have h_pair := hCpair_bound (hφ_smooth n) (hφ_compact n) (hφ_support n)
        (hφ_smooth n') (hφ_compact n') (hφ_support n') x j hj
      have h_wkp_le := hN n n' hn hn'
      have h_wkp_to_real :
          (iteratedWeakSobolevNorm (d := d) (m + 1) (ENNReal.ofReal p) (fun y => φ n y - φ n' y)
            (Metric.ball x₀ R)).toReal ≤ ε / Cpair := by
        have h_toReal_le := ENNReal.toReal_mono ENNReal.ofReal_ne_top h_wkp_le
        rw [ENNReal.toReal_ofReal hε_div.le] at h_toReal_le
        exact h_toReal_le
      calc ‖iteratedFDeriv ℝ j (fun y => ψ y * (φ n y - φ n' y)) x‖
          ≤ Cpair * (iteratedWeakSobolevNorm (d := d) (m + 1) (ENNReal.ofReal p)
              (fun y => φ n y - φ n' y) (Metric.ball x₀ R)).toReal := h_pair
        _ ≤ Cpair * (ε / Cpair) :=
            mul_le_mul_of_nonneg_left h_wkp_to_real hCpair_nn
        _ = ε := by field_simp
  have hg_uniform_cauchy_C0 : ∀ ε > 0, ∃ N : ℕ, ∀ n n', N ≤ n → N ≤ n' → ∀ x : E,
      ‖g n x - g n' x‖ ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hg_uniform_cauchy 0 (Nat.zero_le _) ε hε
    refine ⟨N, fun n n' hn hn' x => ?_⟩
    have := hN n n' hn hn' x
    have h_sub : iteratedFDeriv ℝ 0 (g n) x - iteratedFDeriv ℝ 0 (g n') x =
        iteratedFDeriv ℝ 0 (fun y => g n y - g n' y) x := by
      have h_fn_eq : (fun y => g n y - g n' y) = g n - g n' := rfl
      rw [h_fn_eq, iteratedFDeriv_sub_apply
        ((hg_smooth n).of_le (by exact_mod_cast le_top : (0 : WithTop ℕ∞) ≤
                                   ((⊤ : ℕ∞) : WithTop ℕ∞))).contDiffAt
        ((hg_smooth n').of_le (by exact_mod_cast le_top : (0 : WithTop ℕ∞) ≤
                                    ((⊤ : ℕ∞) : WithTop ℕ∞))).contDiffAt]
    rw [h_sub, norm_iteratedFDeriv_zero] at this
    exact this
  set u_smooth := cauchyLimitFun g hg_uniform_cauchy_C0 with hu_smooth_def
  have hu_tendsto : ∀ x, Filter.Tendsto (fun n => g n x) Filter.atTop (𝓝 (u_smooth x)) :=
    cauchyLimitFun_tendsto hg_uniform_cauchy_C0
  obtain ⟨hu_contDiff, hu_iter_tendsto⟩ :=
    iteratedFDeriv_cauchyLimitFun_eq m hg_smooth hg_uniform_cauchy_C0 hg_uniform_cauchy
  refine ⟨u_smooth, hu_contDiff, ?_⟩
  have hχu_ae_meas : AEStronglyMeasurable (fun y => χ y * u y)
      (volume.restrict (Metric.ball x₀ R)) := hv_W.memLp.aestronglyMeasurable
  have hφ_ae_meas : ∀ n, AEStronglyMeasurable (φ n)
      (volume.restrict (Metric.ball x₀ R)) := fun n =>
    (hφ_smooth n).continuous.aestronglyMeasurable
  have h_eLp_le_wkp : ∀ n,
      eLpNorm (fun y => χ y * u y - φ n y)
        (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R)) ≤
      iteratedWeakSobolevNorm (d := d) (m + 1) (ENNReal.ofReal p)
        (fun y => χ y * u y - φ n y) (Metric.ball x₀ R) := fun n => by
    unfold iteratedWeakSobolevNorm
    have h_term_eq :
        ∑ α : Fin 0 → Fin d,
          eLpNorm (iterWeakPartial (d := d) (ENNReal.ofReal p) 0 α
            (fun y => χ y * u y - φ n y) (Metric.ball x₀ R))
            (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R)) =
        eLpNorm (fun y => χ y * u y - φ n y)
          (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R)) := by
      have h_uniq : ∀ α : Fin 0 → Fin d, α = (fun i => i.elim0) := fun α => by
        funext i; exact i.elim0
      have : Unique (Fin 0 → Fin d) :=
        { default := fun i : Fin 0 => i.elim0
          uniq := fun α => (h_uniq α).symm ▸ rfl }
      rw [Fintype.sum_unique
        (f := fun α : Fin 0 → Fin d =>
          eLpNorm (iterWeakPartial (d := d) (ENNReal.ofReal p) 0 α
            (fun y => χ y * u y - φ n y) (Metric.ball x₀ R))
            (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R)))]
      simp [iterWeakPartial_zero]
    have h_zero_mem : 0 ∈ Finset.range (m + 1 + 1) := by
      rw [Finset.mem_range]; omega
    rw [← h_term_eq, ← Finset.sum_erase_add _ _ h_zero_mem]
    exact le_add_of_nonneg_left (Finset.sum_nonneg (fun _ _ => zero_le))
  have h_eLp_tendsto : Filter.Tendsto
      (fun n => eLpNorm (fun y => χ y * u y - φ n y)
        (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R))) Filter.atTop (𝓝 0) := by
    have h_close_tendsto : Filter.Tendsto
        (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) Filter.atTop (𝓝 0) := by
      rw [ENNReal.tendsto_atTop_zero]
      intro ε hε
      by_cases hε_top : ε = ⊤
      · exact ⟨0, fun n _ => by rw [hε_top]; exact le_top⟩
      have hε_pos_toReal : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hε_top
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε_pos_toReal
      refine ⟨N, fun n hn => ?_⟩
      have h_n_real : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le (n := n)
      have h_pos : 0 < ((n : ℝ) + 1) := by linarith
      have h_N_real : 0 ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le (n := N)
      have h_pos_N : 0 < ((N : ℝ) + 1) := by linarith
      have h_N_le_n : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have h_inc : ((N : ℝ) + 1) ≤ ((n : ℝ) + 1) := by linarith
      have h_inv_le : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
        one_div_le_one_div_of_le h_pos_N h_inc
      have h_toReal_lt : (1 / ((n : ℝ) + 1)) < ε.toReal := lt_of_le_of_lt h_inv_le hN
      have h_ofReal_le : ENNReal.ofReal (1 / ((n : ℝ) + 1)) ≤ ENNReal.ofReal ε.toReal :=
        ENNReal.ofReal_le_ofReal h_toReal_lt.le
      rw [ENNReal.ofReal_toReal hε_top] at h_ofReal_le
      exact h_ofReal_le
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (a := (0 : ℝ≥0∞))
      (f := fun n : ℕ => eLpNorm (fun y => χ y * u y - φ n y)
        (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R)))
      (g := fun _ : ℕ => (0 : ℝ≥0∞))
      (h := fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1)))
      tendsto_const_nhds h_close_tendsto
      (fun _ => zero_le) (fun n => le_trans (h_eLp_le_wkp n) (hφ_close n))
  have h_eLp_tendsto' : Filter.Tendsto
      (fun n => eLpNorm (φ n - fun y => χ y * u y)
        (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R))) Filter.atTop (𝓝 0) := by
    have h_eq : ∀ n, eLpNorm (φ n - fun y => χ y * u y)
        (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R)) =
        eLpNorm (fun y => χ y * u y - φ n y)
          (ENNReal.ofReal p) (volume.restrict (Metric.ball x₀ R)) := fun n => by
      rw [← eLpNorm_neg]
      apply eLpNorm_congr_ae
      filter_upwards with y
      change -(φ n y - (χ y * u y)) = χ y * u y - φ n y
      ring
    simp_rw [h_eq]
    exact h_eLp_tendsto
  have h_in_measure : MeasureTheory.TendstoInMeasure
      (volume.restrict (Metric.ball x₀ R)) φ Filter.atTop
      (fun y => χ y * u y) :=
    MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm
      (p := ENNReal.ofReal p) (l := Filter.atTop)
      (by simp [ENNReal.ofReal_eq_zero, not_le.mpr hp_pos])
      h_eLp_tendsto'
  obtain ⟨ns, _hns_strict, hns_ae⟩ := h_in_measure.exists_seq_tendsto_ae
  have h_psi_one_R4 : ∀ x ∈ Metric.ball x₀ (R / 4), ψ x = 1 := fun x hx =>
    hψ_one x (Metric.ball_subset_closedBall hx)
  have h_chi_one_R4 : ∀ x ∈ Metric.ball x₀ (R / 4), χ x = 1 := fun x hx => by
    apply hχ_one
    rw [Metric.mem_ball] at hx; rw [Metric.mem_closedBall]; linarith
  have h_ball_R4_sub_R : Metric.ball x₀ (R / 4) ⊆ Metric.ball x₀ R := by
    intro z hz; rw [Metric.mem_ball] at hz ⊢; linarith
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_ball]
  rw [ae_restrict_iff' measurableSet_ball] at hns_ae
  filter_upwards [hns_ae] with y h_ae_y h_y_in_R4
  have h_y_in_R : y ∈ Metric.ball x₀ R := h_ball_R4_sub_R h_y_in_R4
  have h_φ_ns_tendsto := h_ae_y h_y_in_R
  have h_g_tendsto := hu_tendsto y
  have h_g_eq_φ : ∀ n, g n y = φ n y := fun n => by
    simp [g, h_psi_one_R4 y h_y_in_R4]
  have h_g_ns_tendsto : Filter.Tendsto (fun k => g (ns k) y) Filter.atTop (𝓝 (u_smooth y)) :=
    h_g_tendsto.comp (Filter.tendsto_atTop_atTop_of_monotone
      (fun a b hab => _hns_strict.le_iff_le.mpr hab) (fun n => ⟨n, _hns_strict.id_le n⟩))
  simp_rw [h_g_eq_φ] at h_g_ns_tendsto
  have h_chi_y : χ y * u y = u y := by rw [h_chi_one_R4 y h_y_in_R4, one_mul]
  rw [h_chi_y] at h_φ_ns_tendsto
  exact tendsto_nhds_unique h_φ_ns_tendsto h_g_ns_tendsto

end EuclideanMorrey
end Sobolev
end Analysis
end CalabiYau
