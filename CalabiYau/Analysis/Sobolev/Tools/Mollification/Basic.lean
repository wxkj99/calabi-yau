-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Tools/Mollification/Basic.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Tools.Mollification.Kernel
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

@[expose] public section

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open scoped ENNReal NNReal Convolution Pointwise BigOperators InnerProductSpace
  RealInnerProductSpace

namespace Sobolev

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

def mollifyEps {ε : ℝ} (hε : 0 < ε) (u : E → ℝ) : E → ℝ :=
  Sobolev.mollifierEps (d := d) hε ⋆[
    ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u

omit [NeZero d] in
theorem mollifyEps_contDiff {ε : ℝ} (hε : 0 < ε) {u : E → ℝ}
    (hu_local : LocallyIntegrable u (volume : Measure E)) :
    ContDiff ℝ (⊤ : ℕ∞) (mollifyEps (d := d) hε u) := by
  unfold mollifyEps
  exact HasCompactSupport.contDiff_convolution_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (Sobolev.mollifierEps_compactSupport hε)
    (Sobolev.mollifierEps_smooth hε)
    hu_local

omit [NeZero d] in
theorem mollifyEps_continuous {ε : ℝ} (hε : 0 < ε) {u : E → ℝ}
    (hu_local : LocallyIntegrable u (volume : Measure E)) :
    Continuous (mollifyEps (d := d) hε u) :=
  (mollifyEps_contDiff (d := d) hε hu_local).continuous

omit [NeZero d] in
lemma mollifyEps_apply {ε : ℝ} (hε : 0 < ε) (u : E → ℝ) (x : E) :
    mollifyEps (d := d) hε u x =
      ∫ t,
        Sobolev.mollifierEps (d := d) hε t * u (x - t)
        ∂(volume : Measure E) := by
  simp [mollifyEps, MeasureTheory.convolution_def,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul]

omit [NeZero d] in
theorem mollifyEps_eq_convolution_swap
    {ε : ℝ} (hε : 0 < ε) (u : E → ℝ) (x : E) :
    mollifyEps (d := d) hε u x =
      (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)]
        mollifierEps (d := d) hε) x := by
  classical
  unfold mollifyEps
  rw [convolution_lsmul, convolution_lsmul_swap]
  refine integral_congr_ae ?_
  filter_upwards with t
  rw [smul_eq_mul, smul_eq_mul, mul_comm]

omit [NeZero d] in
theorem ae_tendsto_mollifyEps_of_locallyIntegrable {ι : Type*} {l : Filter ι}
    {ε : ι → ℝ} (hε : ∀ i, 0 < ε i) (hε_tendsto : Tendsto ε l (𝓝 0))
    {u : E → ℝ} (hu_local : LocallyIntegrable u (volume : Measure E)) :
    ∀ᵐ x₀ ∂(volume : Measure E),
      Tendsto (fun i => mollifyEps (d := d) (hε i) u x₀) l (𝓝 (u x₀)) := by
  have h_bump_rOut : ∀ i,
      (Sobolev.mollifierBumpEps (d := d) (hε i)).rOut
        = ε i := by
    intro i
    show (Sobolev.mollifierBumpEps (d := d) (hε i)).rOut
        = ε i
    rfl
  have h_bump_rIn : ∀ i,
      (Sobolev.mollifierBumpEps (d := d) (hε i)).rIn
        = ε i / 2 := by
    intro i
    show (Sobolev.mollifierBumpEps (d := d) (hε i)).rIn
        = ε i / 2
    rfl
  have h_rOut_tendsto :
      Tendsto
        (fun i =>
          (Sobolev.mollifierBumpEps (d := d) (hε i)).rOut)
        l (𝓝 0) := by
    have h_funeq : (fun i => (Sobolev.mollifierBumpEps
        (d := d) (hε i)).rOut) = ε := by
      funext i; exact h_bump_rOut i
    rw [h_funeq]
    exact hε_tendsto
  have h_ratio :
      ∀ᶠ i in l,
        (Sobolev.mollifierBumpEps (d := d) (hε i)).rOut
          ≤ 2 *
            (Sobolev.mollifierBumpEps (d := d)
              (hε i)).rIn := by
    refine Filter.Eventually.of_forall fun i => ?_
    rw [h_bump_rOut, h_bump_rIn]
    have : ε i = 2 * (ε i / 2) := by ring
    linarith
  have h_ae :=
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (μ := (volume : Measure E)) h_rOut_tendsto h_ratio hu_local
  filter_upwards [h_ae] with x₀ hx₀
  have h_eq : ∀ i,
      ((Sobolev.mollifierBumpEps (d := d)
          (hε i)).normed (volume : Measure E) ⋆[
          ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x₀
        = mollifyEps (d := d) (hε i) u x₀ := by
    intro i
    show ((Sobolev.mollifierBumpEps (d := d)
          (hε i)).normed (volume : Measure E) ⋆[
          ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) x₀
        = mollifyEps (d := d) (hε i) u x₀
    rfl
  refine hx₀.congr ?_
  intro i; exact h_eq i

end Sobolev
