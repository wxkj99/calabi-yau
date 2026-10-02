-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Euclidean/ChainRule/Defs.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev
public import CalabiYau.Analysis.Sobolev.Euclidean.Multiplication.Multiply
public import Mathlib.MeasureTheory.Function.Jacobian

@[expose] public section

-- Private declarations used in public declarations require the compatibility option below..

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Sobolev
namespace Euclidean

structure SmoothDiffeoBounded (d : ℕ) (Ω Ω' : Set (EuclideanSpace ℝ (Fin d))) where
  toFun : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)
  invFun : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)
  toFun_smooth : ContDiff ℝ (⊤ : ℕ∞) toFun
  invFun_smooth : ContDiff ℝ (⊤ : ℕ∞) invFun
  bijOn : Set.BijOn toFun Ω Ω'
  invFun_bijOn : Set.BijOn invFun Ω' Ω
  left_inv : Set.LeftInvOn invFun toFun Ω
  right_inv : Set.RightInvOn invFun toFun Ω'
  derivBound : ℝ
  deriv_bound_pos : 0 < derivBound
  iter_deriv_bounded : ∀ k : ℕ, ∀ x, ‖iteratedFDeriv ℝ k toFun x‖ ≤ derivBound
  iter_deriv_invFun_bounded : ∀ k : ℕ, ∀ x, ‖iteratedFDeriv ℝ k invFun x‖ ≤ derivBound
  jacobianLowerBound : ℝ
  jacobian_lower_bound_pos : 0 < jacobianLowerBound
  jacobian_lower : ∀ x ∈ Ω, jacobianLowerBound ≤ |(fderiv ℝ toFun x).det|

namespace SmoothDiffeoBounded

variable {d : ℕ} {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    (Φ : SmoothDiffeoBounded d Ω Ω')

lemma mapsTo_toFun {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ Ω) :
    Φ.toFun x ∈ Ω' := Φ.bijOn.mapsTo hx

lemma mapsTo_invFun {y : EuclideanSpace ℝ (Fin d)} (hy : y ∈ Ω') :
    Φ.invFun y ∈ Ω := Φ.invFun_bijOn.mapsTo hy

lemma continuous_toFun : Continuous Φ.toFun := Φ.toFun_smooth.continuous

lemma continuous_invFun : Continuous Φ.invFun := Φ.invFun_smooth.continuous

lemma differentiable_toFun : Differentiable ℝ Φ.toFun :=
  Φ.toFun_smooth.differentiable (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)

lemma differentiable_invFun : Differentiable ℝ Φ.invFun :=
  Φ.invFun_smooth.differentiable (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)

lemma toFun_preimage_inter_eq_invFun_image
    (s : Set (EuclideanSpace ℝ (Fin d))) :
    Φ.toFun ⁻¹' s ∩ Ω = Φ.invFun '' (s ∩ Ω') := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_image]
  constructor
  · rintro ⟨hxs, hxΩ⟩
    refine ⟨Φ.toFun x, ⟨hxs, Φ.mapsTo_toFun hxΩ⟩, Φ.left_inv hxΩ⟩
  · rintro ⟨y, ⟨hys, hyΩ'⟩, hxy⟩
    refine ⟨?_, ?_⟩
    · rw [← hxy, Φ.right_inv hyΩ']; exact hys
    · rw [← hxy]; exact Φ.mapsTo_invFun hyΩ'

lemma toFun_preimage_null
    {s : Set (EuclideanSpace ℝ (Fin d))} (hs : volume (s ∩ Ω') = 0) :
    volume (Φ.toFun ⁻¹' s ∩ Ω) = 0 := by
  rw [Φ.toFun_preimage_inter_eq_invFun_image]
  exact MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    (volume) Φ.differentiable_invFun.differentiableOn hs

lemma toFun_quasiMeasurePreserving :
    MeasureTheory.Measure.QuasiMeasurePreserving Φ.toFun
      (volume.restrict Ω) (volume.restrict Ω') := by
  refine ⟨Φ.continuous_toFun.measurable, ?_⟩
  refine MeasureTheory.Measure.AbsolutelyContinuous.mk ?_
  intro s hs_meas hs_zero
  rw [MeasureTheory.Measure.restrict_apply hs_meas] at hs_zero
  have hpre_meas : MeasurableSet (Φ.toFun ⁻¹' s) :=
    Φ.continuous_toFun.measurable hs_meas
  have h_step1 : ((volume.restrict Ω).map Φ.toFun) s = volume (Φ.toFun ⁻¹' s ∩ Ω) := by
    rw [MeasureTheory.Measure.map_apply Φ.continuous_toFun.measurable hs_meas,
        MeasureTheory.Measure.restrict_apply hpre_meas]
  rw [h_step1]
  exact Φ.toFun_preimage_null hs_zero

end SmoothDiffeoBounded

lemma SmoothDiffeoBounded.lintegral_image_eq
    {d : ℕ} {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsOpen Ω) (Φ : SmoothDiffeoBounded d Ω Ω')
    (g : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) :
    ∫⁻ y in Ω', g y ∂(volume) =
      ∫⁻ x in Ω, ENNReal.ofReal |(fderiv ℝ Φ.toFun x).det| * g (Φ.toFun x) ∂(volume) := by
  have hΦ_image : Φ.toFun '' Ω = Ω' := Φ.bijOn.image_eq
  have hΩ_meas : MeasurableSet Ω := hΩ.measurableSet
  have h_inj : Set.InjOn Φ.toFun Ω := Φ.bijOn.injOn
  have hΦ_diff : ∀ x, HasFDerivAt Φ.toFun (fderiv ℝ Φ.toFun x) x := fun x =>
    (Φ.differentiable_toFun x).hasFDerivAt
  have hΦ_deriv_within : ∀ x ∈ Ω, HasFDerivWithinAt Φ.toFun (fderiv ℝ Φ.toFun x) Ω x :=
    fun x _hx => (hΦ_diff x).hasFDerivWithinAt
  have h_chg :=
    MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul (μ := volume)
      (s := Ω) (f := Φ.toFun) (f' := fun x => fderiv ℝ Φ.toFun x)
      hΩ_meas hΦ_deriv_within h_inj g
  rw [hΦ_image] at h_chg
  exact h_chg

end Euclidean
end Sobolev
