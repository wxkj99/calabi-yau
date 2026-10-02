-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Euclidean/Multiplication/SmoothCoefWeakPartialIBP.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Euclidean.Density
public import CalabiYau.Analysis.Calculus.ContDiff.Support
public import CalabiYau.Analysis.DeGiorgi.SobolevSpace.WeakDerivatives

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace CalabiYau
namespace Analysis
namespace Sobolev
namespace Euclidean

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
theorem integral_smul_weak_partial_eq
    {Ω : Set E} (hΩ_open : IsOpen Ω)
    {φ : E → ℝ}
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    {v : E → ℝ}
    {w : Fin d → E → ℝ}
    (hv_localMemLp : ∀ K : Set E, IsCompact K → K ⊆ Ω →
      MeasureTheory.MemLp v 2
        ((MeasureTheory.volume : MeasureTheory.Measure E).restrict K))
    (hw_localMemLp : ∀ (j : Fin d) (K : Set E), IsCompact K → K ⊆ Ω →
      MeasureTheory.MemLp (w j) 2
        ((MeasureTheory.volume : MeasureTheory.Measure E).restrict K))
    (hw_isWeakPartial : ∀ j : Fin d,
      DeGiorgi.HasWeakPartialDeriv (d := d) j (w j) v Ω)
    (j : Fin d)
    {ψ : E → ℝ}
    (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ Ω) :
    (∫ y in Ω, φ y * v y *
      (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
      ∂(MeasureTheory.volume : MeasureTheory.Measure E))
    = -((∫ y in Ω, (fderiv ℝ φ y) (EuclideanSpace.single j 1) * v y * ψ y
        ∂(MeasureTheory.volume : MeasureTheory.Measure E))
      + (∫ y in Ω, φ y * w j y * ψ y
        ∂(MeasureTheory.volume : MeasureTheory.Measure E))) := by
  classical
  let _ := hΩ_open
  set K : Set E := tsupport ψ with hK_def
  have hK_compact : IsCompact K := hψ_cs
  have hK_meas : MeasurableSet K := (isClosed_tsupport ψ).measurableSet
  have hK_sub : K ⊆ Ω := hψ_support
  set ξ : E → ℝ := fun y => φ y * ψ y with hξ_def
  have hξ_smooth : ContDiff ℝ (⊤ : ℕ∞) ξ := hφ_smooth.mul hψ_smooth
  have hξ_cs : HasCompactSupport ξ := hψ_cs.mul_left
  have hξ_tsupport : tsupport ξ ⊆ K := by
    have h_sub_support : Function.support ξ ⊆ Function.support ψ := by
      intro y hy
      have : φ y * ψ y ≠ 0 := hy
      have : ψ y ≠ 0 := fun hψy => this (by simp [hψy])
      exact this
    have h_sub_tsupport : tsupport ξ ⊆ tsupport ψ :=
      closure_mono h_sub_support
    exact h_sub_tsupport
  have hξ_support : tsupport ξ ⊆ Ω := hξ_tsupport.trans hK_sub
  have hφ_diff : Differentiable ℝ φ := hφ_smooth.differentiable (by simp)
  have hψ_diff : Differentiable ℝ ψ := hψ_smooth.differentiable (by simp)
  let ej : E := EuclideanSpace.single j (1 : ℝ)
  have hφ_cont : Continuous φ := hφ_smooth.continuous
  have hψ_cont : Continuous ψ := hψ_smooth.continuous
  have hφ_deriv_cont : Continuous (fun y : E => (fderiv ℝ φ y) ej) :=
    (hφ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψ_deriv_cont : Continuous (fun y : E => (fderiv ℝ ψ y) ej) :=
    (hψ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have fderiv_prod : ∀ y : E, (fderiv ℝ ξ y) ej =
      (fderiv ℝ φ y) ej * ψ y + φ y * (fderiv ℝ ψ y) ej := by
    intro y
    have hfd :
        fderiv ℝ (fun z => φ z * ψ z) y =
          φ y • fderiv ℝ ψ y + ψ y • fderiv ℝ φ y :=
      fderiv_fun_mul hφ_diff.differentiableAt hψ_diff.differentiableAt
    have hξ_eq : (fderiv ℝ ξ y) ej = (fderiv ℝ (fun z => φ z * ψ z) y) ej := rfl
    rw [hξ_eq, hfd]
    simp [add_apply, smul_apply,
      smul_eq_mul]
    ring
  have key :
      ∫ y in Ω, v y * (fderiv ℝ ξ y) ej
        ∂(MeasureTheory.volume : MeasureTheory.Measure E) =
      -∫ y in Ω, w j y * ξ y
        ∂(MeasureTheory.volume : MeasureTheory.Measure E) := by
    simpa [ej] using hw_isWeakPartial j ξ hξ_smooth hξ_cs hξ_support
  have hvK_memLp : MemLp v 2 ((volume : Measure E).restrict K) :=
    hv_localMemLp K hK_compact hK_sub
  have hwK_memLp : MemLp (w j) 2 ((volume : Measure E).restrict K) :=
    hw_localMemLp j K hK_compact hK_sub
  have hvolK_finite : (volume : Measure E) K < ∞ := hK_compact.measure_lt_top
  have hvolK_finite' : (volume.restrict K : Measure E) Set.univ < ∞ := by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact hvolK_finite
  have : IsFiniteMeasure ((volume : Measure E).restrict K) := ⟨hvolK_finite'⟩
  have hv_int_K : IntegrableOn v K (volume : Measure E) :=
    hvK_memLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hw_int_K : IntegrableOn (w j) K (volume : Measure E) :=
    hwK_memLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have integrable_mul_compact :
      ∀ {h : E → ℝ}, Continuous h → tsupport h ⊆ K →
        Integrable (fun y => v y * h y) (volume.restrict Ω) := by
    intro h hh_cont hh_support
    have hh_contOn : ContinuousOn h K := hh_cont.continuousOn
    have step_K : IntegrableOn (fun y => v y * h y) K (volume : Measure E) :=
      hv_int_K.mul_continuousOn hh_contOn hK_compact
    have h_vanish : ∀ y, y ∉ K → v y * h y = 0 := by
      intro y hy
      have : h y = 0 := image_eq_zero_of_notMem_tsupport
        (fun hy_support => hy (hh_support hy_support))
      simp [this]
    have h_eq_ind :
        (fun y => v y * h y) = K.indicator (fun y => v y * h y) := by
      funext y
      by_cases hy : y ∈ K
      · simp [Set.indicator_of_mem hy]
      · simp [Set.indicator_of_notMem hy, h_vanish y hy]
    have ind_int : Integrable (K.indicator (fun y => v y * h y))
        (volume : Measure E) :=
      (integrable_indicator_iff hK_meas).mpr step_K
    have full_int : Integrable (fun y => v y * h y) (volume : Measure E) := by
      rw [h_eq_ind]; exact ind_int
    exact full_int.restrict
  have integrable_mul_compact_w :
      ∀ {h : E → ℝ}, Continuous h → tsupport h ⊆ K →
        Integrable (fun y => w j y * h y) (volume.restrict Ω) := by
    intro h hh_cont hh_support
    have hh_contOn : ContinuousOn h K := hh_cont.continuousOn
    have step_K : IntegrableOn (fun y => w j y * h y) K (volume : Measure E) :=
      hw_int_K.mul_continuousOn hh_contOn hK_compact
    have h_vanish : ∀ y, y ∉ K → w j y * h y = 0 := by
      intro y hy
      have : h y = 0 := image_eq_zero_of_notMem_tsupport
        (fun hy_support => hy (hh_support hy_support))
      simp [this]
    have h_eq_ind :
        (fun y => w j y * h y) = K.indicator (fun y => w j y * h y) := by
      funext y
      by_cases hy : y ∈ K
      · simp [Set.indicator_of_mem hy]
      · simp [Set.indicator_of_notMem hy, h_vanish y hy]
    have ind_int : Integrable (K.indicator (fun y => w j y * h y))
        (volume : Measure E) :=
      (integrable_indicator_iff hK_meas).mpr step_K
    have full_int : Integrable (fun y => w j y * h y) (volume : Measure E) := by
      rw [h_eq_ind]; exact ind_int
    exact full_int.restrict
  have h_dφ_ψ_cont : Continuous (fun y : E => (fderiv ℝ φ y) ej * ψ y) :=
    hφ_deriv_cont.mul hψ_cont
  have h_dφ_ψ_support : tsupport (fun y : E => (fderiv ℝ φ y) ej * ψ y) ⊆ K := by
    have h_sub : Function.support (fun y : E => (fderiv ℝ φ y) ej * ψ y) ⊆
        Function.support ψ := by
      intro y hy
      have : (fderiv ℝ φ y) ej * ψ y ≠ 0 := hy
      have : ψ y ≠ 0 := fun hψy => this (by simp [hψy])
      exact this
    exact closure_mono h_sub
  have h_φ_dψ_cont : Continuous (fun y : E => φ y * (fderiv ℝ ψ y) ej) :=
    hφ_cont.mul hψ_deriv_cont
  have h_φ_dψ_support : tsupport (fun y : E => φ y * (fderiv ℝ ψ y) ej) ⊆ K := by
    have h1 : Function.support (fun y : E => (fderiv ℝ ψ y) ej) ⊆
        tsupport ψ := by
      intro y hy
      by_contra hy'
      have hψeq : ψ =ᶠ[𝓝 y] 0 :=
        (isClosed_tsupport (f := ψ)).isOpen_compl.eventually_mem hy' |>.mono
          (fun z hz => image_eq_zero_of_notMem_tsupport hz)
      have hfderiv_eq : fderiv ℝ ψ y = fderiv ℝ (fun _ : E => (0 : ℝ)) y :=
        Filter.EventuallyEq.fderiv_eq hψeq
      have hψfderiv_zero : fderiv ℝ ψ y = 0 := by
        rw [hfderiv_eq]
        exact fderiv_const_apply (0 : ℝ)
      have : (fderiv ℝ ψ y) ej = 0 := by simp [hψfderiv_zero]
      exact hy this
    have h2 : Function.support (fun y : E => φ y * (fderiv ℝ ψ y) ej) ⊆
        Function.support (fun y : E => (fderiv ℝ ψ y) ej) := by
      intro y hy
      have : φ y * (fderiv ℝ ψ y) ej ≠ 0 := hy
      have : (fderiv ℝ ψ y) ej ≠ 0 := fun h0 => this (by simp [h0])
      exact this
    have : tsupport (fun y : E => φ y * (fderiv ℝ ψ y) ej) ⊆
        tsupport (fun y : E => (fderiv ℝ ψ y) ej) := closure_mono h2
    have : tsupport (fun y : E => φ y * (fderiv ℝ ψ y) ej) ⊆ tsupport ψ :=
      this.trans (by
        exact (closure_mono h1).trans (by
          rw [closure_eq_iff_isClosed.mpr (isClosed_tsupport ψ)]))
    exact this
  have h_ψ_cont : Continuous ψ := hψ_cont
  have h_ψ_support : tsupport ψ ⊆ K := by rw [hK_def]
  have int_v_dφ_ψ :
      Integrable (fun y => v y * ((fderiv ℝ φ y) ej * ψ y))
        (volume.restrict Ω) :=
    integrable_mul_compact h_dφ_ψ_cont h_dφ_ψ_support
  have int_v_φ_dψ :
      Integrable (fun y => v y * (φ y * (fderiv ℝ ψ y) ej))
        (volume.restrict Ω) :=
    integrable_mul_compact h_φ_dψ_cont h_φ_dψ_support
  have int_w_ξ :
      Integrable (fun y => w j y * ξ y) (volume.restrict Ω) := by
    have h_ξ_cont : Continuous ξ := hφ_cont.mul hψ_cont
    exact integrable_mul_compact_w h_ξ_cont hξ_tsupport
  have key' :
      ∫ y in Ω, v y * ((fderiv ℝ φ y) ej * ψ y) +
        v y * (φ y * (fderiv ℝ ψ y) ej)
        ∂(volume : Measure E) =
      -∫ y in Ω, w j y * ξ y ∂(volume : Measure E) := by
    have eq1 :
        ∫ y in Ω, v y * (fderiv ℝ ξ y) ej ∂(volume : Measure E) =
        ∫ y in Ω, v y * ((fderiv ℝ φ y) ej * ψ y) +
          v y * (φ y * (fderiv ℝ ψ y) ej) ∂(volume : Measure E) := by
      refine integral_congr_ae ?_
      refine Filter.Eventually.of_forall (fun y => ?_)
      have := fderiv_prod y
      calc
        v y * (fderiv ℝ ξ y) ej
            = v y * ((fderiv ℝ φ y) ej * ψ y + φ y * (fderiv ℝ ψ y) ej) := by
              rw [this]
        _ = v y * ((fderiv ℝ φ y) ej * ψ y) + v y * (φ y * (fderiv ℝ ψ y) ej) := by
              ring
    rw [eq1] at key
    exact key
  rw [integral_add int_v_dφ_ψ int_v_φ_dψ] at key'
  have congr_lhs :
      (fun y => φ y * v y * (fderiv ℝ ψ y) ej) =
      (fun y => v y * (φ y * (fderiv ℝ ψ y) ej)) := by
    funext y; ring
  have congr_dφ_v_ψ :
      (fun y => (fderiv ℝ φ y) ej * v y * ψ y) =
      (fun y => v y * ((fderiv ℝ φ y) ej * ψ y)) := by
    funext y; ring
  have congr_φ_w_ψ :
      (fun y => φ y * w j y * ψ y) = (fun y => w j y * ξ y) := by
    funext y; simp [ξ]; ring
  change ∫ y in Ω, φ y * v y * (fderiv ℝ ψ y) ej ∂(volume : Measure E) =
    -((∫ y in Ω, (fderiv ℝ φ y) ej * v y * ψ y ∂(volume : Measure E))
      + (∫ y in Ω, φ y * w j y * ψ y ∂(volume : Measure E)))
  rw [show
      (fun y => φ y * v y * (fderiv ℝ ψ y) ej) =
      (fun y => v y * (φ y * (fderiv ℝ ψ y) ej)) from congr_lhs,
    show
      (fun y => (fderiv ℝ φ y) ej * v y * ψ y) =
      (fun y => v y * ((fderiv ℝ φ y) ej * ψ y)) from congr_dφ_v_ψ,
    show (fun y => φ y * w j y * ψ y) = (fun y => w j y * ξ y) from
      congr_φ_w_ψ]
  have h_extract :
      ∫ y in Ω, v y * (φ y * (fderiv ℝ ψ y) ej) ∂(volume : Measure E) =
      -(∫ y in Ω, w j y * ξ y ∂(volume : Measure E)) -
        ∫ y in Ω, v y * ((fderiv ℝ φ y) ej * ψ y) ∂(volume : Measure E) := by
    linarith
  rw [h_extract]
  ring

end Euclidean
end Sobolev
end Analysis
end CalabiYau

namespace DeGiorgi

open Metric

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

end DeGiorgi
