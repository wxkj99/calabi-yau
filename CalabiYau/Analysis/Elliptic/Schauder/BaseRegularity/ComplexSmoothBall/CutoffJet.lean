module

public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.ComplexSmoothBall.Basic
public import CalabiYau.Analysis.Elliptic.Schauder.Cutoff.Elliptic.BallHessian

/-!
# The compactly supported cutoff two-jet

Source: Gilbarg–Trudinger, §6.1, Theorem 6.2, freezing/interpolation proof;
Constantin, Schauder Estimates, pp. 6–9. The estimates follow Constantin, *Schauder Estimates*, pp. 6–9.
-/

@[expose] public section

open Set Matrix
open scoped NNReal ContDiff Topology

namespace CalabiYau.Schauder

/-- Construct the BCF two-jet of the canonical cutoff potential, not an arbitrary extension.
The cutoff equals one on the half-radius ball; the quarter-radius gauge therefore agrees
with the uncut potential. Auxiliary second-jet norm and Hölder constants may depend on the
potential's derivatives, but they disappear from the extracted absorption conclusion. -/
private theorem smooth_of_tsupport_subset {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hSupport : tsupport f ⊆ U) : ContDiff ℝ ∞ f := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport f
  · exact (hf x (hSupport hx)).contDiffAt (hU.mem_nhds (hSupport hx))
  · have hzero : f =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
    exact contDiffAt_const.congr_of_eventuallyEq hzero

private theorem iteratedFDeriv_eq_of_eqOn_open {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {j : ℕ} {U : Set E} {f g : E → F} (hU : IsOpen U)
    (hEq : Set.EqOn f g U) {x : E} (hx : x ∈ U) :
    iteratedFDeriv ℝ j f x = iteratedFDeriv ℝ j g x := by
  have hNear : f =ᶠ[𝓝 x] g := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hEq hy
  exact (hNear.iteratedFDeriv ℝ j).self_of_nhds

theorem exists_realBallCutoffJet :
    ∀ {n : ℕ} {α : ℝ≥0} {u : RealBallModel n → ℝ}
  {U : Set (RealBallModel n)} {x : RealBallModel n} {δ : ℝ},
  0 < α → α < 1 → IsOpen U → 0 < δ → Metric.closedBall x δ ⊆ U →
  ContDiffOn ℝ ∞ u U → Nonempty (RealBallCutoffJet α x δ u) := by
  intro n α u U x δ hα₀ hα₁ hU hδ hδU hu
  let chi : RealBallModel n → ℝ := ballCutoff x (δ / 2) δ
  let f : RealBallModel n → ℝ := fun y => chi y * u y
  have hchi : ContDiff ℝ ∞ chi := by
    dsimp [chi]
    exact ballCutoff_contDiff x (δ / 2) δ
  have hchi_support : HasCompactSupport chi := by
    dsimp [chi]
    exact ballCutoff_hasCompactSupport (by linarith) (by linarith)
  have hf_smooth_on : ContDiffOn ℝ ∞ f U := by
    apply ContDiffOn.mul hchi.contDiffOn hu
  have hf_support : HasCompactSupport f := hchi_support.mul_right (f' := u)
  have hftsClosed : tsupport f ⊆ Metric.closedBall x δ := by
    exact (tsupport_mul_subset_left (f := chi) (g := u)).trans
      (ballCutoff_tsupport_subset_closedBall (by linarith) (by linarith))
  have hfts : tsupport f ⊆ U := hftsClosed.trans hδU
  have hf : ContDiff ℝ ∞ f :=
    smooth_of_tsupport_subset hU hf_smooth_on hfts
  let df : RealBallModel n → RealBallModel n →L[ℝ] ℝ := fderiv ℝ f
  let d2f : RealBallModel n → RealBallModel n →L[ℝ] RealBallModel n →L[ℝ] ℝ :=
    fderiv ℝ df
  let g : RealBallModel n → RealBallModel n →L[ℝ] ℝ := fun z =>
    chi z • fderiv ℝ u z + u z • fderiv ℝ chi z
  have hdf_eq : Set.EqOn df g U := by
    intro z hz
    have hchiDiff : DifferentiableAt ℝ chi z :=
      (hchi.contDiffAt).differentiableAt (by simp)
    have huDiff : DifferentiableAt ℝ u z :=
      (hu z hz).contDiffAt (hU.mem_nhds hz) |>.differentiableAt (by simp)
    dsimp [df, g, f]
    rw [fderiv_fun_mul hchiDiff huDiff]
  let d3f : RealBallModel n → RealBallModel n →L[ℝ]
      RealBallModel n →L[ℝ] RealBallModel n →L[ℝ] ℝ := fderiv ℝ d2f
  have hdf : ContDiff ℝ ∞ df := by
    dsimp [df]
    exact hf.fderiv_right (m := ∞) (by simp)
  have hd2f : ContDiff ℝ ∞ d2f := by
    dsimp [d2f]
    exact hdf.fderiv_right (m := ∞) (by simp)
  have hd3f : ContDiff ℝ ∞ d3f := by
    dsimp [d3f]
    exact hd2f.fderiv_right (m := ∞) (by simp)
  have hdf_support : HasCompactSupport df := by
    dsimp [df]
    exact hf_support.fderiv ℝ
  have hd2f_support : HasCompactSupport d2f := by
    dsimp [d2f]
    exact hdf_support.fderiv ℝ
  let value : BoundedContinuousFunction (RealBallModel n) ℝ :=
    compactSupportBoundedContinuousFunction f hf.continuous hf_support
  let first : BoundedContinuousFunction (RealBallModel n) (RealBallModel n →L[ℝ] ℝ) :=
    compactSupportBoundedContinuousFunction df hdf.continuous hdf_support
  let second : BoundedContinuousFunction (RealBallModel n)
      (RealBallModel n →L[ℝ] RealBallModel n →L[ℝ] ℝ) :=
    compactSupportBoundedContinuousFunction d2f hd2f.continuous hd2f_support
  let third : BoundedContinuousFunction (RealBallModel n)
      (RealBallModel n →L[ℝ] RealBallModel n →L[ℝ] RealBallModel n →L[ℝ] ℝ) :=
    compactSupportBoundedContinuousFunction d3f hd3f.continuous
      (hd2f_support.fderiv ℝ)
  have hfirst : ∀ y, HasFDerivAt (value : RealBallModel n → ℝ) (first y) y := by
    intro y
    change HasFDerivAt f (fderiv ℝ f y) y
    exact (hf.differentiable (by simp) y).hasFDerivAt
  have hsecond : ∀ y, HasFDerivAt
      (first : RealBallModel n → RealBallModel n →L[ℝ] ℝ) (second y) y := by
    intro y
    change HasFDerivAt df (fderiv ℝ df y) y
    exact (hdf.differentiable (by simp) y).hasFDerivAt
  have hthird : ∀ y, HasFDerivAt
      (second : RealBallModel n → RealBallModel n →L[ℝ] RealBallModel n →L[ℝ] ℝ)
      (third y) y := by
    intro y
    change HasFDerivAt d2f (fderiv ℝ d2f y) y
    exact (hd2f.differentiable (by simp) y).hasFDerivAt
  let C : ℝ≥0 := max (2 * ‖second‖₊) ‖third‖₊
  have hholder : HolderWith C α
      (second : RealBallModel n → RealBallModel n →L[ℝ] RealBallModel n →L[ℝ] ℝ) := by
    apply holderWith_of_hasFDerivAt_of_norm_le
      (M := ‖second‖₊) (N := ‖third‖₊) (by positivity) (by exact_mod_cast hα₁.le) hthird
    · intro y
      simpa using second.norm_coe_le_norm y
    · intro y
      simpa using third.norm_coe_le_norm y
  refine ⟨{
    value := value
    first := first
    second := second
    holderConstant := C
    normConstant := ‖second‖₊
    value_eq := ?_
    derivative := hfirst
    second_derivative := hsecond
    second_holder := hholder
    second_norm := ?_
    second_support := ?_
    inner_gauge := ?_
  }⟩
  · intro y
    rfl
  · intro y
    simpa using second.norm_coe_le_norm y
  · intro y hy
    have hdist : δ ≤ dist y x := by
      by_contra h
      apply hy
      exact Metric.mem_ball.mpr (lt_of_not_ge h)
    by_cases hclosed : y ∈ Metric.closedBall x δ
    · have hyU : y ∈ U := hδU hclosed
      have hcut0 : chi y = 0 := by
        dsimp [chi]
        exact ballCutoff_eq_zero_of_le_dist (by linarith) (by linarith) hdist
      have hcut1 : fderiv ℝ chi y = 0 := by
        simpa only [chi, fderiv_ballCutoff] using
          ballCutoffFDeriv_eq_zero_of_le_dist (by linarith) (by linarith) hdist
      have hcut2 : fderiv ℝ (fderiv ℝ chi) y = 0 := by
        simpa only [chi, fderiv_ballCutoff, fderiv_ballCutoffFDeriv] using
          ballCutoffFDeriv2_eq_zero_of_le_dist (by linarith) (by linarith) hdist
      have hnear : df =ᶠ[𝓝 y] g := by
        filter_upwards [hU.mem_nhds hyU] with z hz
        exact hdf_eq hz
      have hderivEq := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hnear
      have huAt : ContDiffAt ℝ ∞ u y := (hu y hyU).contDiffAt (hU.mem_nhds hyU)
      have hduAt : ContDiffAt ℝ ∞ (fderiv ℝ u) y :=
        huAt.fderiv_right (m := ∞) (by simp)
      have hchiAt : ContDiffAt ℝ ∞ chi y := hchi.contDiffAt
      have hdchiAt : ContDiffAt ℝ ∞ (fderiv ℝ chi) y :=
        hchiAt.fderiv_right (m := ∞) (by simp)
      have hterm1Diff : DifferentiableAt ℝ (fun z => chi z • fderiv ℝ u z) y :=
        (hchiAt.differentiableAt (by simp)).smul
          (hduAt.differentiableAt (by simp))
      have hterm2Diff : DifferentiableAt ℝ (fun z => u z • fderiv ℝ chi z) y :=
        (huAt.differentiableAt (by simp)).smul
          (hdchiAt.differentiableAt (by simp))
      have hgFormula : fderiv ℝ g y =
          chi y • fderiv ℝ (fderiv ℝ u) y +
            (fderiv ℝ chi y).smulRight (fderiv ℝ u y) +
          (u y • fderiv ℝ (fderiv ℝ chi) y +
            (fderiv ℝ u y).smulRight (fderiv ℝ chi y)) := by
        dsimp [g]
        rw [fderiv_fun_add hterm1Diff hterm2Diff]
        rw [fderiv_fun_smul (hchiAt.differentiableAt (by simp))
          (hduAt.differentiableAt (by simp))]
        rw [fderiv_fun_smul (huAt.differentiableAt (by simp))
          (hdchiAt.differentiableAt (by simp))]
      change d2f y = 0
      change fderiv ℝ df y = 0
      rw [hderivEq, hgFormula]
      simp [hcut0, hcut1, hcut2]
    · have hnot : y ∉ tsupport df := by
        intro hyts
        have : y ∈ Metric.closedBall x δ :=
          (tsupport_fderiv_subset (𝕜 := ℝ)).trans hftsClosed hyts
        exact hclosed this
      change d2f y = 0
      change fderiv ℝ df y = 0
      exact fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot
  · change eContDiffHolderGaugeOn 2 α (Metric.closedBall x (δ / 4)) f =
      eContDiffHolderGaugeOn 2 α (Metric.closedBall x (δ / 4)) u
    apply eContDiffHolderGaugeOn_congr (alpha := α)
    intro j hj y hy
    apply iteratedFDeriv_eq_of_eqOn_open (U := Metric.ball x (δ / 2))
    · exact Metric.isOpen_ball
    · intro z hz
      have hcut : chi z = 1 := by
        apply ballCutoff_eq_one_of_mem_closedBall (by linarith) (by linarith)
        exact Metric.ball_subset_closedBall hz
      dsimp [f]
      rw [hcut, one_mul]
    · have hdist : dist y x ≤ δ / 4 := by
        simpa [Metric.mem_closedBall, dist_comm] using hy
      apply Metric.mem_ball.mpr
      nlinarith [hdist]

end CalabiYau.Schauder
