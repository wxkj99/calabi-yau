module

public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.ComplexSmoothBall.Basic
public import CalabiYau.Analysis.Elliptic.Schauder.VariableCoefficient.BallInterior

/-!
# Canonical inner cutoff jet identities, finite smooth outer gauge and lower-jet interpolation.

Proof-preserving extraction from the committed SourceInterpolation module
073d0f59b03ec37cc921b9792875e063bec3fb01.
Source: Constantin, Schauder Estimates, equation (9), p. 7 and localization/
lower-jet interpolation, pp. 8–9. Only visibility and namespace are changed.
-/

@[expose] public section

open Set Matrix
open scoped NNReal ContDiff Topology

namespace CalabiYau.Schauder.SourceInterpolationProofs

theorem realBallCutoffJet_value_eq_u_on_inner
    {n : ℕ} {α : ℝ≥0} {x : RealBallModel n} {δ : ℝ}
    {u : RealBallModel n → ℝ} (hδ : 0 < δ)
    (jet : RealBallCutoffJet α x δ u) :
    Set.EqOn (jet.value : RealBallModel n → ℝ) u (Metric.ball x (δ / 2)) := by
  intro y hy
  rw [jet.value_eq y]
  have hcutoff : ballCutoff x (δ / 2) δ y = 1 :=
    ballCutoff_eq_one_of_mem_closedBall (by positivity) (by linarith)
      (Metric.ball_subset_closedBall hy)
  rw [hcutoff, one_mul]
theorem realBallCutoffJet_first_eq_fderiv_on_inner
    {n : ℕ} {α : ℝ≥0} {x : RealBallModel n} {δ : ℝ}
    {u : RealBallModel n → ℝ} (hδ : 0 < δ)
    (jet : RealBallCutoffJet α x δ u)
    (hu : ∀ y ∈ Metric.ball x (δ / 2), ContDiffAt ℝ 1 u y) :
    ∀ y ∈ Metric.ball x (δ / 2), jet.first y = fderiv ℝ u y := by
  intro y hy
  have hEq : (jet.value : RealBallModel n → ℝ) =ᶠ[𝓝 y] u := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hy] with z hz
    exact realBallCutoffJet_value_eq_u_on_inner hδ jet hz
  have hjet := (jet.derivative y).congr_of_eventuallyEq hEq.symm
  exact hjet.unique (((hu y hy).differentiableAt (by norm_num)).hasFDerivAt)
theorem realBallCutoffJet_second_eq_fderiv_fderiv_on_inner
    {n : ℕ} {α : ℝ≥0} {x : RealBallModel n} {δ : ℝ}
    {u : RealBallModel n → ℝ} (hδ : 0 < δ)
    (jet : RealBallCutoffJet α x δ u)
    (hu : ∀ y ∈ Metric.ball x (δ / 2), ContDiffAt ℝ 2 u y) :
    ∀ y ∈ Metric.ball x (δ / 2),
      jet.second y = fderiv ℝ (fderiv ℝ u) y := by
  intro y hy
  have hEq : (jet.first : RealBallModel n → RealBallModel n →L[ℝ] ℝ) =ᶠ[𝓝 y]
      (fderiv ℝ u) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hy] with z hz
    exact realBallCutoffJet_first_eq_fderiv_on_inner hδ jet
      (fun w hw => (hu w hw).of_le (by norm_num)) z hz
  have hjet := (jet.second_derivative y).congr_of_eventuallyEq hEq.symm
  have hcont : ContDiffAt ℝ 1 (fderiv ℝ u) y :=
    (hu y hy).fderiv_right (by norm_num)
  exact hjet.unique ((hcont.differentiableAt (by norm_num)).hasFDerivAt)
theorem realBallGauge_finite_of_smooth
    {n : ℕ} {α : ℝ≥0} {U : Set (RealBallModel n)}
    {c : RealBallModel n} {R : ℝ} {u : RealBallModel n → ℝ}
    (hα : α < 1) (hU : IsOpen U)
    (hRU : Metric.closedBall c R ⊆ U)
    (hsmooth : ContDiffOn ℝ ∞ u U) :
    eContDiffHolderGaugeOn 2 α (Metric.closedBall c R) u ≠ ⊤ := by
  have hu3 : ContDiffOn ℝ (3 : WithTop ℕ∞) u U := by
    intro x hx
    exact (hsmooth x hx).of_le (by
      change ((3 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr (show (3 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top))
  let K := Metric.closedBall c R
  have hK : IsCompact K := isCompact_closedBall c R
  have hIterEq (j : ℕ) (hj : j ≤ 3) :
      EqOn (iteratedFDerivWithin ℝ j u U) (iteratedFDeriv ℝ j u) U := by
    intro x hx
    apply iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
    · exact (hu3.contDiffAt (hU.mem_nhds hx)).of_le (by exact_mod_cast hj)
    · exact hx
  have hnorm (j : ℕ) (hj : j ≤ 3) :
      ContinuousOn (fun x => ‖iteratedFDeriv ℝ j u x‖) K := by
    have hw := hu3.continuousOn_iteratedFDerivWithin
      (by exact_mod_cast hj : (j : WithTop ℕ∞) ≤ (3 : WithTop ℕ∞)) hU.uniqueDiffOn
    exact (hw.congr (hIterEq j hj).symm).norm.mono hRU
  let q : RealBallModel n → ℝ := fun x =>
    ∑ j ∈ Finset.range 4, ‖iteratedFDeriv ℝ j u x‖
  have hq : ContinuousOn q K := by
    exact continuousOn_finsetSum (Finset.range 4) fun j hj =>
      hnorm j (by have := Finset.mem_range.mp hj; omega)
  obtain ⟨B, hB0, hB⟩ := (hK.bddAbove_image hq).exists_ge 0
  let C : ℝ≥0 := ⟨B, hB0⟩
  have hjbound : ∀ j ≤ 3, ∀ x ∈ K, ‖iteratedFDeriv ℝ j u x‖ ≤ C := by
    intro j hj x hx
    have hterm : ‖iteratedFDeriv ℝ j u x‖ ≤ q x := by
      dsimp [q]
      apply Finset.single_le_sum (f := fun i => ‖iteratedFDeriv ℝ i u x‖)
        (fun i _ => norm_nonneg _)
      exact Finset.mem_range.mpr (by omega)
    exact_mod_cast hterm.trans (hB (q x) (mem_image_of_mem q hx))
  have hdiff : ∀ x ∈ K, DifferentiableAt ℝ (iteratedFDeriv ℝ 2 u) x := by
    intro x hx
    exact (hu3.contDiffAt (hU.mem_nhds (hRU hx))).differentiableAt_iteratedFDeriv
      (by norm_num : (2 : WithTop ℕ∞) < (3 : WithTop ℕ∞))
  have hderiv : ∀ x ∈ K, ‖fderiv ℝ (iteratedFDeriv ℝ 2 u) x‖₊ ≤ C := by
    intro x hx
    rw [fderiv_iteratedFDeriv]
    change ‖continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin 3 => RealBallModel n) ℝ
      (iteratedFDeriv ℝ 3 u x)‖₊ ≤ C
    rw [LinearIsometryEquiv.nnnorm_map]
    exact_mod_cast hjbound 3 le_rfl x hx
  have hLip : LipschitzOnWith C (iteratedFDeriv ℝ 2 u) K :=
    Convex.lipschitzOnWith_of_nnnorm_fderiv_le hdiff hderiv (convex_closedBall c R)
  have hHolder : HolderWith (3 * C) α
      (K.domRestrict (iteratedFDeriv ℝ 2 u)) := by
    have hh := holderWith_restrict_of_norm_le_of_lipschitzOnWith
      (epsilon := 1) (by norm_num) hα.le
      (hjbound 2 (by norm_num)) hLip
    convert hh using 1
    · simp
      ring
  have hgauge : eContDiffHolderGaugeOn 2 α K u ≤ (6 * C : ℝ≥0) := by
    have hg := eContDiffHolderGaugeOn_le (fun _ => C) (3 * C)
      (fun j hj => hjbound j (by omega)) hHolder
    simpa [Finset.sum_range_succ, show (6 : ℝ≥0) = 3 + 3 by norm_num,
      mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc] using hg
  exact ne_of_lt (hgauge.trans_lt ENNReal.coe_lt_top)

theorem realBallHessian_norm_le_of_finiteGauge
    {n : ℕ} {α : ℝ≥0} {c : RealBallModel n} {R : ℝ}
    {u : RealBallModel n → ℝ}
    (hfinite : eContDiffHolderGaugeOn 2 α (Metric.closedBall c R) u ≠ ⊤) :
    ∀ x ∈ Metric.closedBall c R,
      ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ realBallGauge α c R u := by
  have hcoe : (realBallGauge α c R u : ENNReal) =
      eContDiffHolderGaugeOn 2 α (Metric.closedBall c R) u := by
    dsimp [realBallGauge]
    exact ENNReal.coe_toNNReal hfinite
  have hbound : eContDiffHolderGaugeOn 2 α (Metric.closedBall c R) u ≤
      (realBallGauge α c R u : ENNReal) := by
    rw [hcoe]
  intro x hx
  have hjet := spatialJet_norm_le hbound (j := 2) le_rfl hx
  calc
    ‖fderiv ℝ (fderiv ℝ u) x‖ =
        ‖hessianCurryEquiv (RealBallModel n) ℝ (iteratedFDeriv ℝ 2 u x)‖ := by
          rw [hessianCurryEquiv_iteratedFDeriv_two_eq_fderiv]
    _ = ‖iteratedFDeriv ℝ 2 u x‖ := by
          rw [(hessianCurryEquiv (RealBallModel n) ℝ).norm_map]
    _ ≤ realBallGauge α c R u := by exact_mod_cast hjet
theorem realBallLowerJet_interpolation
    {n : ℕ} {α M H : ℝ≥0} {c : RealBallModel n} {r R : ℝ}
    {u : RealBallModel n → ℝ} (hα : α < 1)
    (eps₁ eps₂ : ℝ≥0) (heps₁ : 0 < eps₁) (heps₂ : 0 < eps₂)
    (hbuffer : r + (eps₁ : ℝ) < R)
    (hsmooth : ContDiffOn ℝ 2 u (Metric.ball c R))
    (huNorm : ∀ z ∈ Metric.ball c R, ‖u z‖ ≤ M)
    (hHess : ∀ z ∈ Metric.ball c R, ‖fderiv ℝ (fderiv ℝ u) z‖ ≤ H) :
    (∀ x ∈ Metric.closedBall c r,
      ‖fderiv ℝ u x‖ ≤ 2 * M / eps₁ + H * eps₁) ∧
    HolderWith (H * eps₂ ^ ((1 : ℝ≥0) - α : ℝ) +
      2 * (2 * M / eps₁ + H * eps₁) / eps₂ ^ (α : ℝ)) α
      ((Metric.closedBall c r).domRestrict (fderiv ℝ u)) ∧
    HolderWith ((2 * M / eps₁ + H * eps₁) * eps₂ ^ ((1 : ℝ≥0) - α : ℝ) +
      2 * M / eps₂ ^ (α : ℝ)) α ((Metric.closedBall c r).domRestrict u) := by
  let S := Metric.ball c R
  let G : ℝ≥0 := 2 * M / eps₁ + H * eps₁
  have hgradCont : ∀ z ∈ S, ContDiffAt ℝ 1 (fderiv ℝ u) z := by
    intro z hz
    exact (hsmooth.contDiffAt (Metric.isOpen_ball.mem_nhds hz)).fderiv_right (by norm_num)
  have hgradDiff : ∀ z ∈ S, DifferentiableAt ℝ (fderiv ℝ u) z := by
    intro z hz
    exact (hgradCont z hz).differentiableAt (by norm_num)
  have hgradDeriv : ∀ z ∈ S, ‖fderiv ℝ (fderiv ℝ u) z‖₊ ≤ H := by
    intro z hz
    exact_mod_cast hHess z hz
  have hgradLip : LipschitzOnWith H (fderiv ℝ u) S :=
    Convex.lipschitzOnWith_of_nnnorm_fderiv_le hgradDiff hgradDeriv (convex_ball c R)
  have hgradHolder1 : HolderOnWith H 1 (fderiv ℝ u) S := hgradLip.holderOnWith
  have huDiff : ∀ z ∈ S, DifferentiableAt ℝ u z := by
    intro z hz
    exact (hsmooth.contDiffAt (Metric.isOpen_ball.mem_nhds hz)).differentiableAt (by norm_num)
  have hrR : r < R := by
    calc
      r < r + (eps₁ : ℝ) := lt_add_of_pos_right r (by exact_mod_cast heps₁)
      _ < R := hbuffer
  have hstep : ∀ x ∈ Metric.closedBall c r, ∀ v : RealBallModel n,
      ‖v‖ = 1 → x + (eps₁ : ℝ) • v ∈ S := by
    intro x hx v hv
    rw [Metric.mem_ball]
    calc
      dist (x + (eps₁ : ℝ) • v) c ≤
          dist (x + (eps₁ : ℝ) • v) x + dist x c := dist_triangle _ _ _
      _ = eps₁ + dist x c := by
        rw [dist_eq_norm]
        simp only [add_sub_cancel_left, norm_smul, hv, mul_one]
        rw [Real.norm_of_nonneg (by exact_mod_cast heps₁.le)]
      _ ≤ eps₁ + r := by
        gcongr
        exact Metric.mem_closedBall.mp hx
      _ < R := by linarith [hbuffer]
  have hgradBound : ∀ x ∈ Metric.closedBall c r,
      ‖fderiv ℝ u x‖ ≤ (G : ℝ) := by
    intro x hx
    have hxS : x ∈ S := by
      rw [Metric.mem_ball]
      exact (Metric.mem_closedBall.mp hx).trans_lt hrR
    have hraw := norm_fderiv_le_at_scale_on (convex_ball c R) huDiff
      hgradHolder1 huNorm (by exact_mod_cast heps₁) hxS (hstep x hx)
    change ‖fderiv ℝ u x‖ ≤ 2 * (M : ℝ) / (eps₁ : ℝ) +
      (H : ℝ) * (eps₁ : ℝ) ^ (1 : ℝ) at hraw
    rw [Real.rpow_one] at hraw
    simpa only [G, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_div,
      NNReal.coe_ofNat] using hraw
  have hgradLipInner : LipschitzOnWith H (fderiv ℝ u) (Metric.closedBall c r) :=
    hgradLip.mono (Metric.closedBall_subset_ball hrR)
  have hgradHolder := holderWith_restrict_of_norm_le_of_lipschitzOnWith
    (epsilon := eps₂) heps₂ hα.le
    (fun x hx => by exact_mod_cast hgradBound x hx) hgradLipInner
  have huLip : LipschitzOnWith G u (Metric.closedBall c r) := by
    apply (convex_closedBall c r).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    · intro z hz
      exact huDiff z (Metric.closedBall_subset_ball hrR hz)
    · intro z hz
      exact_mod_cast hgradBound z hz
  have huHolder := holderWith_restrict_of_norm_le_of_lipschitzOnWith
    (epsilon := eps₂) heps₂ hα.le
    (fun z hz => huNorm z (Metric.closedBall_subset_ball hrR hz)) huLip
  refine ⟨hgradBound, ?_, ?_⟩
  · simpa only [NNReal.coe_rpow, NNReal.coe_sub, NNReal.coe_one] using hgradHolder
  · simpa only [NNReal.coe_rpow, NNReal.coe_sub, NNReal.coe_one] using huHolder

end CalabiYau.Schauder.SourceInterpolationProofs
