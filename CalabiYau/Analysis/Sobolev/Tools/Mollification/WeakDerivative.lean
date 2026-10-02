-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Tools/Mollification/WeakDerivative.lean
-- Locally modified.
module
public import CalabiYau.Analysis.DeGiorgi.SobolevSpace.WeakDerivatives
public import CalabiYau.Analysis.Sobolev.Tools.Mollification.Lp

@[expose] public section

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open scoped ENNReal NNReal Convolution Pointwise BigOperators

namespace Sobolev

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
theorem convolution_fderiv_eq_convolution_weakPartial_univ
    {u g : E → ℝ} {i : Fin d}
    (hweak : DeGiorgi.HasWeakPartialDeriv i g u Set.univ)
    {φ : E → ℝ} (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (x : E) :
    ((fun y => (fderiv ℝ φ y) (EuclideanSpace.single i 1))
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x =
      (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x := by
  classical
  let T : Homeomorph E E := (Homeomorph.neg E).trans (Homeomorph.addLeft x)
  let ψ : E → ℝ := φ ∘ T
  have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    let h : ContDiff ℝ (⊤ : ℕ∞) ψ :=
      hφ_smooth.comp (contDiff_const.add contDiff_id.neg)
    exact h
  have hψ_compact : HasCompactSupport ψ := by
    simpa [ψ, T, Function.comp] using hφ_compact.comp_homeomorph T
  have key := hweak ψ hψ_smooth hψ_compact (by simp)
  have hderiv :
      ∀ t,
        (fderiv ℝ ψ t) (EuclideanSpace.single i 1) =
          - (fderiv ℝ φ (x + -t)) (EuclideanSpace.single i 1) := by
    intro t
    have hraw :=
      (hφ_smooth.differentiable
        (show (((⊤ : ℕ∞) : WithTop ℕ∞)) ≠ 0 by simp) (x + -t)).hasFDerivAt.comp t
          ((hasFDerivAt_const x t).add (hasFDerivAt_id t).neg)
    have heq : ψ = φ ∘ ((fun _ : E => x) + -id) := by
      funext y
      simp [ψ, T]
    rw [← heq] at hraw
    rw [hraw.fderiv]
    simp
  have hkey :
      ∫ t, g t * ψ t ∂volume =
        ∫ t, u t * (fderiv ℝ φ (x + -t)) (EuclideanSpace.single i 1) ∂volume := by
    have hkey' :
        ∫ t, u t * (fderiv ℝ ψ t) (EuclideanSpace.single i 1) ∂volume =
          -∫ t, g t * ψ t ∂volume := by
      simpa [Measure.restrict_univ] using key
    have hderiv_int :
        ∫ t, u t * (fderiv ℝ ψ t) (EuclideanSpace.single i 1) ∂volume =
          -∫ t, u t * (fderiv ℝ φ (x + -t)) (EuclideanSpace.single i 1) ∂volume := by
      calc
        ∫ t, u t * (fderiv ℝ ψ t) (EuclideanSpace.single i 1) ∂volume
          = ∫ t, -(u t * (fderiv ℝ φ (x + -t)) (EuclideanSpace.single i 1)) ∂volume := by
              refine integral_congr_ae ?_
              filter_upwards with t
              rw [hderiv t]
              ring
        _ = -∫ t, u t * (fderiv ℝ φ (x + -t)) (EuclideanSpace.single i 1) ∂volume := by
              rw [integral_neg]
    linarith
  calc
      ((fun y => (fderiv ℝ φ y) (EuclideanSpace.single i 1))
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x
      = ∫ t, u t * (fderiv ℝ φ (x - t)) (EuclideanSpace.single i 1) ∂volume := by
          simpa [smul_eq_mul, mul_comm] using
            (MeasureTheory.convolution_lsmul_swap
              (f := fun y => (fderiv ℝ φ y) (EuclideanSpace.single i 1)) (g := u) (x := x)
              (μ := volume))
    _ = ∫ t, g t * ψ t ∂volume := hkey.symm
    _ = (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x := by
          simpa [ψ, T, Function.comp, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
            smul_eq_mul, mul_comm] using
            (MeasureTheory.convolution_lsmul_swap (f := φ) (g := g) (x := x) (μ := volume)).symm

omit [NeZero d] in
theorem mollifyEps_partial_eq_mollifyEps_weakPartial
    {ε : ℝ} (hε : 0 < ε)
    {u g : E → ℝ} {j : Fin d}
    (hu_local : LocallyIntegrable u (volume : Measure E))
    (hweak : DeGiorgi.HasWeakPartialDeriv (d := d) j g u Set.univ) (x : E) :
    (fderiv ℝ (mollifyEps (d := d) hε u) x)
        (EuclideanSpace.single j 1) =
      mollifyEps (d := d) hε g x := by
  classical
  have hη_smooth : ContDiff ℝ (⊤ : ℕ∞) (mollifierEps (d := d) hε) :=
    mollifierEps_smooth hε
  have hη_C1 : ContDiff ℝ 1 (mollifierEps (d := d) hε) :=
    hη_smooth.of_le (by norm_cast)
  have hη_compact : HasCompactSupport (mollifierEps (d := d) hε) :=
    mollifierEps_compactSupport hε
  have hderiv : HasFDerivAt
      (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)]
        mollifierEps (d := d) hε)
      ((u ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompR E,
        (volume : Measure E)] fderiv ℝ (mollifierEps (d := d) hε)) x) x :=
    hη_compact.hasFDerivAt_convolution_right
      (L := ContinuousLinearMap.lsmul ℝ ℝ) hu_local hη_C1 x
  have hpartial_uη :
      (fderiv ℝ (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)]
        mollifierEps (d := d) hε) x) (EuclideanSpace.single j 1) =
      (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)]
        (fun y => (fderiv ℝ (mollifierEps (d := d) hε) y)
          (EuclideanSpace.single j 1))) x := by
    rw [hderiv.fderiv]
    exact convolution_precompR_apply (𝕜 := ℝ)
      (L := ContinuousLinearMap.lsmul ℝ ℝ)
      hu_local (hη_compact.fderiv ℝ)
      (hη_smooth.continuous_fderiv (by simp)) x
        (EuclideanSpace.single j 1)
  have hcomm : mollifyEps (d := d) hε u =
      (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)]
        mollifierEps (d := d) hε) := by
    funext y
    exact mollifyEps_eq_convolution_swap hε u y
  rw [hcomm]
  rw [hpartial_uη]
  have h_swap_convergence : ∀ y : E,
      (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)]
        (fun z => (fderiv ℝ (mollifierEps (d := d) hε) z)
          (EuclideanSpace.single j 1))) y =
      ((fun z => (fderiv ℝ (mollifierEps (d := d) hε) z)
          (EuclideanSpace.single j 1))
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) y := by
    intro y
    rw [convolution_lsmul, convolution_lsmul_swap]
    refine integral_congr_ae ?_
    filter_upwards with t
    rw [smul_eq_mul, smul_eq_mul, mul_comm]
  rw [h_swap_convergence x]
  have hη_smooth' : ContDiff ℝ (⊤ : ℕ∞) (mollifierEps (d := d) hε) :=
    mollifierEps_smooth hε
  have h_ibp :=
    convolution_fderiv_eq_convolution_weakPartial_univ
      (d := d) (i := j) (g := g) (u := u) hweak hη_smooth' hη_compact x
  rw [h_ibp]
  rfl

omit [NeZero d] in
theorem eLpNorm_partial_mollifyEps_le_of_weakPartial_univ
    {ε : ℝ} (hε : 0 < ε)
    {u g : E → ℝ} {j : Fin d}
    (hu_local : LocallyIntegrable u (volume : Measure E))
    (hg : MemLp g 2 (volume : Measure E))
    (hweak : DeGiorgi.HasWeakPartialDeriv (d := d) j g u Set.univ) :
    eLpNorm
      (fun x => (fderiv ℝ (mollifyEps (d := d) hε u) x)
        (EuclideanSpace.single j 1)) 2 (volume : Measure E) ≤
      eLpNorm g 2 (volume : Measure E) := by
  have h_pointwise : (fun x : E =>
      (fderiv ℝ (mollifyEps (d := d) hε u) x)
        (EuclideanSpace.single j 1)) =
      (fun x : E => mollifyEps (d := d) hε g x) := by
    funext x
    exact mollifyEps_partial_eq_mollifyEps_weakPartial hε hu_local hweak x
  rw [h_pointwise]
  exact eLpNorm_mollifyEps_le hε hg

end Sobolev
