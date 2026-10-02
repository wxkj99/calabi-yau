module

public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.ComplexSmoothBall.GaugeFiniteness
public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.ComplexSmoothBall.FrozenParameters
public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.ComplexSmoothBall.CoefficientExtension
public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.ComplexSmoothBall.CutoffJet
public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.ComplexSmoothBall.SourceInterpolation
public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.ComplexSmoothBall.CoefficientControl
public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.ComplexSmoothBall.GaugeCover
public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.ComplexSmoothBall.RadiusIteration

/-!
# Smooth real-ball interior estimate

Source: Gilbarg–Trudinger, §6.1, Theorem 6.2, freezing/interpolation proof;
Constantin, Schauder Estimates, pp. 6–9. The estimates follow Constantin, *Schauder Estimates*, pp. 6–9.
-/

@[expose] public section

open Set Matrix
open scoped NNReal ContDiff Topology

namespace CalabiYau.Schauder

theorem closedBall_localPatch_subset {n : ℕ} {c x : RealBallModel n}
    {r t R d : ℝ} (hx : x ∈ Metric.closedBall c r) (hrt : r < t) (htR : t ≤ R)
    {U : Set (RealBallModel n)} (hRU : Metric.closedBall c R ⊆ U) :
    Metric.closedBall x (min d ((t-r)/4)) ⊆ U := by
  intro y hy
  apply hRU
  apply Metric.mem_closedBall.mpr
  have hxy := Metric.mem_closedBall.mp hy
  have hxc := Metric.mem_closedBall.mp hx
  have hd : min d ((t-r)/4) ≤ (t-r)/4 := min_le_right _ _
  have hdist := dist_triangle y x c
  linarith

/-- This proof has no placeholder. It uses the actual extracted absorption theorem. -/
theorem smoothRealBallInteriorEstimate {n : ℕ} (hn : 0 < n)
    (α lam K : ℝ≥0) (hα₀ : 0 < α) (hα₁ : α < 1) (hlam : 0 < lam)
    (ρ R : ℝ) (hρ : 0 ≤ ρ) (hρR : ρ < R) :
    ∃ C : ℝ≥0, ∀ {U : Set (RealBallModel n)} {c : RealBallModel n}
      {a : RealBallModel n → Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ}
      {u : RealBallModel n → ℝ} {K₀ K₁ : ℝ≥0},
      IsOpen U → Metric.closedBall c R ⊆ U → RealSmoothBallData α lam K K₀ K₁ U a u →
      eContDiffHolderGaugeOn 2 α (Metric.closedBall c ρ) u ≤ C * (K₁+K₀) := by
  let : Nonempty (Fin n × Fin 2) := ⟨(⟨0, hn⟩, 0)⟩
  obtain ⟨d, ε, M, hd, hε, hM, hparams⟩ := exists_realBallFrozenParameters hn α lam K hα₀ hα₁ hlam
  obtain ⟨p, hp, hsource⟩ := exists_realBallCutoffSourceBounds hn α lam K hα₀ hα₁ hlam R d M
    (hρ.trans_lt hρR) hd hM
  let θ : ℝ≥0 := (2 ^ (p+1))⁻¹
  obtain ⟨A, hA⟩ := hsource θ (by dsimp [θ]; positivity)
  refine ⟨(2 * (2 * (Real.toNNReal (R-ρ))⁻¹) ^ p) * A, ?_⟩
  intro U c a u K₀ K₁ hU hRU hdata
  have hfinite : ∀ s ≤ R, eContDiffHolderGaugeOn 2 α (Metric.closedBall c s) u ≠ ⊤ := by
    intro s hs
    exact smooth_realBallGauge_ne_top hα₁ hU ((Metric.closedBall_subset_closedBall hs).trans hRU)
      hdata.potential_smooth
  have hcoe (s : ℝ) (hs : s ≤ R) : (realBallGauge α c s u : ENNReal) =
      eContDiffHolderGaugeOn 2 α (Metric.closedBall c s) u :=
    ENNReal.coe_toNNReal (hfinite s hs)
  have hmono : ∀ s, ρ ≤ s → s ≤ R → realBallGauge α c s u ≤ realBallGauge α c R u := by
    intro s hρs hs
    apply ENNReal.coe_le_coe.mp
    rw [hcoe s hs, hcoe R le_rfl]
    exact eContDiffHolderGaugeOn_mono (Metric.closedBall_subset_closedBall hs) 2 α u
  have hrec : ∀ r t, ρ ≤ r → r < t → t ≤ R →
      realBallGauge α c r u ≤
        (A * (K₁+K₀)) * (Real.toNNReal (t-r))⁻¹ ^ p + θ * realBallGauge α c t u := by
    intro r t hρr hrt htR
    let δ := min d ((t-r)/4)
    have hδ : 0 < δ := lt_min hd (by linarith)
    have hδd : δ ≤ d := min_le_left _ _
    have hδU (x : RealBallModel n) (hx : x ∈ Metric.closedBall c r) :
        Metric.closedBall x δ ⊆ U := closedBall_localPatch_subset hx hrt htR hRU
    let B := (A * (K₁+K₀)) * (Real.toNNReal (t-r))⁻¹ ^ p + θ * realBallGauge α c t u
    have hfactor : 0 < realBallPatchFactor α δ := by
      dsimp [realBallPatchFactor]
      positivity
    have hlocal : ∀ x ∈ Metric.closedBall c r,
        eContDiffHolderGaugeOn 2 α (Metric.closedBall x (δ/4)) u ≤
          ((B / realBallPatchFactor α δ : ℝ≥0) : ENNReal) := by
      intro x hx
      obtain ⟨coeff⟩ := exists_realBallCoefficientExtension hU hδ (hδU x hx) hdata.coefficients_smooth
      obtain ⟨jet⟩ := exists_realBallCutoffJet hα₀ hα₁ hU hδ (hδU x hx) hdata.potential_smooth
      have hxU : x ∈ U := hδU x hx (Metric.mem_closedBall_self hδ.le)
      have hpos := hdata.positive x hxU
      have hentry : ∀ i j, ‖a x i j‖ ≤ (K : ℝ) := by
        intro i j
        simpa only [norm_iteratedFDeriv_zero] using
          (hdata.coefficient_holder i j).1 0 (by omega) x hxU
      have hfreeze := hparams (a x) hpos (hdata.lower x hxU) hentry δ hδ hδd
      have hcoeff : (fun i j => coeff.coefficient i j x) = a x := by
        ext i j
        exact coeff.agrees i j x (Metric.mem_ball_self hδ)
      have hcoeffPos : Matrix.PosDef (fun i j => coeff.coefficient i j x) := by
        rw [hcoeff]
        exact hpos
      have hctrl := realBallCoefficientExtension_control hα₀ hδ (hδU x hx)
        hdata.coefficient_holder coeff
      obtain ⟨Kf, Bf, hfNorm, hfHolder, hbound⟩ := hA hU hRU hdata r t
        (hρ.trans hρr) hrt htR x hx coeff jet
      have habs := variable_coefficient_schauder_estimate_of_interpolation_scale_on
        hα₀ hα₁ hε (Metric.ball x δ) coeff.coefficient x hcoeffPos
        jet.value jet.first jet.second jet.derivative jet.second_derivative
        hfNorm hfHolder (fun _ _ => K) (fun _ _ => K * Real.toNNReal δ ^ (α : ℝ))
        hctrl.1 hctrl.2 jet.second_norm jet.second_holder jet.second_support
        (by simpa only [hcoeff] using hfreeze.1)
      have hbound' : M * (Kf+Bf+‖jet.value‖₊) ≤ B / realBallPatchFactor α δ := by
        apply (le_div_iff₀ hfactor).mpr
        simpa only [B, mul_assoc, mul_comm, mul_left_comm] using hbound
      have hglobal : eContDiffHolderGaugeOn 2 α Set.univ
          (jet.value : RealBallModel n → ℝ) ≤
          ((B / realBallPatchFactor α δ : ℝ≥0) : ENNReal) := by
        apply habs.trans
        apply ENNReal.coe_le_coe.mpr
        apply le_trans ?_ hbound'
        simpa only [hcoeff] using hfreeze.2 jet.value Kf Bf
      rw [← jet.inner_gauge]
      exact (eContDiffHolderGaugeOn_mono (subset_univ _) 2 α
        (jet.value : RealBallModel n → ℝ)).trans hglobal
    have hcovered := realBallGauge_le_of_patch_bounds hα₀ hα₁ (hρ.trans hρr) hδ hlocal
    apply ENNReal.coe_le_coe.mp
    rw [hcoe r (hrt.le.trans htR)]
    simpa only [← ENNReal.coe_mul, mul_div_cancel₀ _ (ne_of_gt hfactor)] using hcovered
  have hresult := realBall_radius_iteration hρ hρR hp hmono hrec
  rw [← hcoe ρ hρR.le]
  apply ENNReal.coe_le_coe.mpr
  simpa only [mul_assoc] using hresult

end CalabiYau.Schauder
