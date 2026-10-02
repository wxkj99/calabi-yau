module

public import CalabiYau.MongeAmpere.Continuity.Openness.ResidualDerivative.LogDetRemainder.ChartTaylorData
public import CalabiYau.MongeAmpere.Continuity.Openness.ResidualNormalization
import CalabiYau.Geometry.Kahler.Laplacian.FiniteRegularityChart

public section

open scoped Manifold ContDiff NNReal Topology ComplexOrder Matrix.Norms.Frobenius
open MeasureTheory Set

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

private theorem logMongeAmpere_eq_chart_logdet_of_c2
    (ω₁ : KahlerForm n M) (ψ : M → ℝ)
    (hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 ψ)
    (hpositive : ω₁.IsC2Potential ψ) (x : M)
    {y : M} (hy : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source) :
    Real.log (ω₁.mongeAmpere ψ y) =
      Real.log (RCLike.re (ω₁.metricInChart x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y) +
        complexHessian (ψ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)).det) -
      Real.log (RCLike.re (ω₁.metricInChart x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)).det) := by
  have hMA := ω₁.mongeAmpere_eq_inChart_of_contMDiff_two hψ x hy
  have hz : extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y ∈
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
    have hy' : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source := by
      simpa only [extChartAt_source] using hy
    exact (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).map_source hy'
  have hA : (ω₁.metricInChart x
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)).PosDef :=
    ω₁.posDef_metricInChart x hz
  have hAdet : 0 < RCLike.re (ω₁.metricInChart x
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)).det :=
    (RCLike.pos_iff.mp hA.det_pos).1
  have hMApos : 0 < ω₁.mongeAmpere ψ y := by
    change 0 < ContinuousAlternatingMap.relDet (ω₁ y) (ω₁ y + mddbar n ψ y)
    exact ContinuousAlternatingMap.relDet_pos (ω₁.isPositive y) (hpositive.2 y)
  have hBdet : 0 < RCLike.re (ω₁.metricInChart x
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y) +
        complexHessian (ψ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)).det := by
    rw [hMA] at hMApos
    exact (div_pos_iff_of_pos_right hAdet).mp hMApos
  rw [hMA, Real.log_div (ne_of_gt hBdet) (ne_of_gt hAdet)]

private theorem logMongeAmpere_sub_laplacian_eq_logDetTaylorRemainder
    (ω₁ : KahlerForm n M) (ψ : M → ℝ)
    (hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 ψ)
    (hpositive : ω₁.IsC2Potential ψ) (x : M)
    {y : M} (hy : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source) :
    Real.log (ω₁.mongeAmpere ψ y) - ω₁.laplacian ψ y =
      Matrix.logDetTaylorRemainder
        (ω₁.metricInChart x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y))
        (complexHessian (ψ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)) := by
  have hLap := ω₁.laplacian_eq_inChart_of_contMDiff_two ψ hψ x hy
  rw [logMongeAmpere_eq_chart_logdet_of_c2 ω₁ ψ hψ hpositive x hy, hLap]
  rfl

set_option maxHeartbeats 800000 in
variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] in
/-- Matrix log-determinant Taylor identity for the actual evaluated C2 potentials. -/
theorem actualPairwiseTaylor_eq_chartMatrix
    (ω₀ : KahlerForm n M) (F : M → ℝ)
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F)
    (t : ℝ) (φ : M → ℝ)
    (hsol : ω₀.SolvesMongeAmpere (fun x ↦ t * F x + ω₀.pathConstant F t) φ)
    (α : ℝ≥0) [P : ContinuityHolderPair (ω₀.perturb φ hsol.1) α]
    (D : CenteredPathResidualData ω₀ F hF t φ hsol α)
    (L : P.C2 ≃L[ℝ] P.C0)
    (hL : ∀ u, P.evalC0 (L u) = (ω₀.perturb φ hsol.1).laplacian (P.evalC2 u))
    (u v : P.C2) (hu : ‖u‖ < D.radius) (hv : ‖v‖ < D.radius)
    (i : P.finiteChartCover.ι) (z : EuclideanSpace ℂ (Fin n))
    (hz : z ∈ P.finiteChartCover.piece i) :
    actualPairwiseTaylor ω₀ φ L u v
      ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (P.finiteChartCover.base i)).symm z) =
    Matrix.logDetTaylorRemainder
      ((ω₀.perturb φ hsol.1).metricInChart (P.finiteChartCover.base i) z)
      (chartTaylorH P u i z) -
    Matrix.logDetTaylorRemainder
      ((ω₀.perturb φ hsol.1).metricInChart (P.finiteChartCover.base i) z)
      (chartTaylorH P v i z) := by
  let ω₁ := ω₀.perturb φ hsol.1
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (P.finiteChartCover.base i)
  let y := e.symm z
  have hzTarget : z ∈ e.target := P.finiteChartCover.piece_in_target i hz
  have hySource : y ∈ e.source := e.map_target hzTarget
  have hyChart : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) (P.finiteChartCover.base i)).source := by
    simpa only [e, extChartAt_source] using hySource
  have hψu : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 (P.evalC2 u) :=
    (D.radius_potential u hu).1
  have hψv : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 (P.evalC2 v) :=
    (D.radius_potential v hv).1
  have hpotu := D.radius_potential u hu
  have hpotv := D.radius_potential v hv
  have hratio (w : P.C2) (hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ) 2 (P.evalC2 w)) (x : M) :
      ω₀.mongeAmpere (φ + P.evalC2 w) x =
        ω₀.mongeAmpere φ x * ω₁.mongeAmpere (P.evalC2 w) x := by
    change ContinuousAlternatingMap.relDet (ω₀ x)
        (ω₀ x + mddbar n (φ + P.evalC2 w) x) =
      ContinuousAlternatingMap.relDet (ω₀ x) (ω₀ x + mddbar n φ x) *
        ContinuousAlternatingMap.relDet (ω₁ x)
          (ω₁ x + mddbar n (P.evalC2 w) x)
    rw [mddbar_add_of_contMDiff_two
      (hsol.1.1.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) hψ]
    simpa [ω₁, KahlerForm.perturb, add_assoc] using
      (ContinuousAlternatingMap.relDet_mul_relDet (ω₀.isPositive x) (hsol.1.2 x)).symm
  have hratiou : ω₀.mongeAmpere (φ + P.evalC2 u) y / ω₀.mongeAmpere φ y =
      ω₁.mongeAmpere (P.evalC2 u) y := by
    rw [hratio u hψu y]
    have hden : ω₀.mongeAmpere φ y ≠ 0 := (ω₀.mongeAmpere_pos hsol.1 y).ne'
    field_simp
  have hratiov : ω₀.mongeAmpere (φ + P.evalC2 v) y / ω₀.mongeAmpere φ y =
      ω₁.mongeAmpere (P.evalC2 v) y := by
    rw [hratio v hψv y]
    have hden : ω₀.mongeAmpere φ y ≠ 0 := (ω₀.mongeAmpere_pos hsol.1 y).ne'
    field_simp
  have hTu := logMongeAmpere_sub_laplacian_eq_logDetTaylorRemainder
    ω₁ (P.evalC2 u) hψu hpotu (P.finiteChartCover.base i) hyChart
  have hTv := logMongeAmpere_sub_laplacian_eq_logDetTaylorRemainder
    ω₁ (P.evalC2 v) hψv hpotv (P.finiteChartCover.base i) hyChart
  have hzy : e y = z := e.right_inv hzTarget
  rw [hzy] at hTu hTv
  have hTu' : Real.log (ω₁.mongeAmpere (P.evalC2 u) y) -
      ω₁.laplacian (P.evalC2 u) y =
      Matrix.logDetTaylorRemainder (ω₁.metricInChart (P.finiteChartCover.base i) z)
        (chartTaylorH P u i z) := by
    simpa [e, y, chartTaylorH] using hTu
  have hTv' : Real.log (ω₁.mongeAmpere (P.evalC2 v) y) -
      ω₁.laplacian (P.evalC2 v) y =
      Matrix.logDetTaylorRemainder (ω₁.metricInChart (P.finiteChartCover.base i) z)
        (chartTaylorH P v i z) := by
    simpa [e, y, chartTaylorH] using hTv
  have hψdiff : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2
      (P.evalC2 (u - v)) := by
    rw [P.evalC2.map_sub]
    exact hψu.sub hψv
  have hsum := mddbar_add_of_contMDiff_two hψdiff hψv
  have hfun : P.evalC2 (u - v) + P.evalC2 v = P.evalC2 u := by
    funext x
    change P.evalC2 (u - v) x + P.evalC2 v x = P.evalC2 u x
    rw [P.evalC2.map_sub]
    simp
  rw [hfun] at hsum
  have hsumy : mddbar n (P.evalC2 u) y =
      mddbar n (P.evalC2 (u - v)) y + mddbar n (P.evalC2 v) y :=
    congrFun hsum y
  have hdd : mddbar n (P.evalC2 (u - v)) y =
      mddbar n (P.evalC2 u) y - mddbar n (P.evalC2 v) y := by
    calc
      _ = (mddbar n (P.evalC2 (u - v)) y + mddbar n (P.evalC2 v) y) -
          mddbar n (P.evalC2 v) y := by simp
      _ = _ := by rw [hsumy]
  have hlap : ω₁.laplacian (P.evalC2 (u - v)) y =
      ω₁.laplacian (P.evalC2 u) y - ω₁.laplacian (P.evalC2 v) y := by
    change (ContinuousAlternatingMap.relTrace (ω₁ y))
      (mddbar n (P.evalC2 (u - v)) y) = _
    rw [hdd, ContinuousAlternatingMap.relTrace_sub]
    rfl
  have hlinear : P.evalC0 (L (u - v)) y =
      ω₁.laplacian (P.evalC2 u) y - ω₁.laplacian (P.evalC2 v) y := by
    have h := congrFun (hL (u - v)) y
    rw [hlap] at h
    exact h
  have hlogu := congrArg Real.log hratiou
  have hlogv := congrArg Real.log hratiov
  dsimp [actualPairwiseTaylor]
  change Real.log (ω₀.mongeAmpere (φ + P.evalC2 u) y / ω₀.mongeAmpere φ y) -
      Real.log (ω₀.mongeAmpere (φ + P.evalC2 v) y / ω₀.mongeAmpere φ y) -
      P.evalC0 (L (u - v)) y = _
  rw [hlogu, hlogv, hlinear]
  rw [← hTu', ← hTv']
  ring

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] in
theorem rawLogRatio_continuous
    (ω₀ : KahlerForm n M) (F : M → ℝ)
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F)
    (t : ℝ) (φ : M → ℝ)
    (hsol : ω₀.SolvesMongeAmpere (fun x ↦ t * F x + ω₀.pathConstant F t) φ)
    (α : ℝ≥0) [P : ContinuityHolderPair (ω₀.perturb φ hsol.1) α]
    (D : CenteredPathResidualData ω₀ F hF t φ hsol α)
    (u : P.C2) (hu : ‖u‖ < D.radius) :
    Continuous (fun x ↦ Real.log (ω₀.mongeAmpere (φ + P.evalC2 u) x /
      ω₀.mongeAmpere φ x)) := by
  let c : C(M, ℝ) := littleHolderMeanZeroEvaluationCLM
    (ω₀.perturb φ hsol.1) P.finiteChartCover 0 α P.normedDataC0 (D.residual (u, 0))
  have heq : (fun x ↦ Real.log (ω₀.mongeAmpere (φ + P.evalC2 u) x /
      ω₀.mongeAmpere φ x)) = fun x ↦ c x +
        (∫ y, uncenteredContinuityPathResidual ω₀ F t φ hsol
          (P.evalC2 u) 0 y ∂(ω₀.perturb φ hsol.1).volume) /
          (ω₀.perturb φ hsol.1).volume.real univ := by
    funext x
    have heval := D.eval_residual u 0 hu x
    change c x = centeredContinuityPathResidual ω₀ F t φ hsol (P.evalC2 u) 0 x at heval
    simp [centeredContinuityPathResidual, uncenteredContinuityPathResidual] at heval
    simp only [uncenteredContinuityPathResidual, zero_mul, add_zero, sub_self, sub_zero]
    linarith
  rw [heq]
  exact c.continuous.add continuous_const

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] in
theorem actualPairwiseTaylor_continuous
    (ω₀ : KahlerForm n M) (F : M → ℝ)
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F)
    (t : ℝ) (φ : M → ℝ)
    (hsol : ω₀.SolvesMongeAmpere (fun x ↦ t * F x + ω₀.pathConstant F t) φ)
    (α : ℝ≥0) [P : ContinuityHolderPair (ω₀.perturb φ hsol.1) α]
    (D : CenteredPathResidualData ω₀ F hF t φ hsol α)
    (L : P.C2 ≃L[ℝ] P.C0)
    (u v : P.C2) (hu : ‖u‖ < D.radius) (hv : ‖v‖ < D.radius) :
    Continuous (actualPairwiseTaylor ω₀ φ L u v) := by
  let ell : C(M, ℝ) := littleHolderMeanZeroEvaluationCLM
    (ω₀.perturb φ hsol.1) P.finiteChartCover 0 α P.normedDataC0 (L (u - v))
  exact ((rawLogRatio_continuous ω₀ F hF t φ hsol α D u hu).sub
    (rawLogRatio_continuous ω₀ F hF t φ hsol α D v hv)).sub ell.continuous

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] in
theorem actualPairwiseTaylor_centering
    (ω₀ : KahlerForm n M) (F : M → ℝ)
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F)
    (t : ℝ) (φ : M → ℝ)
    (hsol : ω₀.SolvesMongeAmpere (fun x ↦ t * F x + ω₀.pathConstant F t) φ)
    (α : ℝ≥0) [P : ContinuityHolderPair (ω₀.perturb φ hsol.1) α]
    (D : CenteredPathResidualData ω₀ F hF t φ hsol α)
    (L : P.C2 ≃L[ℝ] P.C0) (b : P.C0)
    (hb : ∀ x, P.evalC0 b x =
      (∫ y, F y ∂(ω₀.perturb φ hsol.1).volume) /
        (ω₀.perturb φ hsol.1).volume.real univ - F x)
    (p q : P.C2 × ℝ) (hp : ‖p.1‖ < D.radius) (hq : ‖q.1‖ < D.radius)
    (hvol : 0 < (ω₀.perturb φ hsol.1).volume.real univ) :
    ∀ x, P.evalC0 (D.residual p - D.residual q -
        (L (p.1 - q.1) + (p.2 - q.2) • b)) x =
      actualPairwiseTaylor ω₀ φ L p.1 q.1 x -
        (∫ y, actualPairwiseTaylor ω₀ φ L p.1 q.1 y
          ∂(ω₀.perturb φ hsol.1).volume) /
          (ω₀.perturb φ hsol.1).volume.real univ := by
  let ω₁ := ω₀.perturb φ hsol.1
  let R := actualPairwiseTaylor ω₀ φ L p.1 q.1
  let w := D.residual p - D.residual q - (L (p.1 - q.1) + (p.2 - q.2) • b)
  let c : ℝ :=
    (ω₀.pathConstant F (t + p.2) - ω₀.pathConstant F t) -
    (ω₀.pathConstant F (t + q.2) - ω₀.pathConstant F t) +
    (∫ y, uncenteredContinuityPathResidual ω₀ F t φ hsol (P.evalC2 p.1) p.2 y ∂ω₁.volume) /
      ω₁.volume.real univ -
    (∫ y, uncenteredContinuityPathResidual ω₀ F t φ hsol (P.evalC2 q.1) q.2 y ∂ω₁.volume) /
      ω₁.volume.real univ +
    (p.2 - q.2) * ((∫ y, F y ∂ω₁.volume) / ω₁.volume.real univ)
  have hpoint (x : M) : P.evalC0 w x = R x - c := by
    simp only [w, map_sub, map_add, map_smul, Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
    rw [D.eval_residual p.1 p.2 hp x, D.eval_residual q.1 q.2 hq x, hb x]
    simp only [centeredContinuityPathResidual, uncenteredContinuityPathResidual]
    dsimp [R, actualPairwiseTaylor, c, ω₁]
    simp only [uncenteredContinuityPathResidual, map_sub, Pi.sub_apply]
    ring
  have hwcont : Continuous (fun x ↦ P.evalC0 w x) := by
    let cw : C(M, ℝ) := littleHolderMeanZeroEvaluationCLM ω₁
      P.finiteChartCover 0 α P.normedDataC0 w
    exact cw.continuous
  have hwint : Integrable (fun x ↦ P.evalC0 w x) ω₁.volume :=
    hwcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hmean : ∫ x, P.evalC0 w x ∂ω₁.volume = 0 := by
    change littleHolderMeanFunctional ω₁ P.finiteChartCover 0 α P.normedDataC0
      (w : LittleHolderMeanZero ω₁ P.finiteChartCover 0 α P.normedDataC0) = 0
    exact w.property
  have hI : (∫ x, R x ∂ω₁.volume) = c * ω₁.volume.real univ := by
    calc
      _ = ∫ x, (P.evalC0 w x + c) ∂ω₁.volume := by
        apply integral_congr_ae
        filter_upwards with x
        linarith [hpoint x]
      _ = (∫ x, P.evalC0 w x ∂ω₁.volume) + ∫ _ : M, c ∂ω₁.volume :=
        integral_add hwint (integrable_const c)
      _ = _ := by rw [hmean]; simp [integral_const, smul_eq_mul]; ring
  have hc : c = (∫ y, R y ∂ω₁.volume) / ω₁.volume.real univ := by
    rw [hI, mul_div_cancel_right₀ _ (ne_of_gt hvol)]
  intro x
  change P.evalC0 w x = R x - _
  rw [hpoint x, hc]

theorem holderBoundOn_zero_congr
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} {α C : ℝ≥0} {f g : E → F}
    (hf : HolderBoundOn 0 α C S f) (hfg : ∀ x ∈ S, f x = g x) :
    HolderBoundOn 0 α C S g := by
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    simpa only [norm_iteratedFDeriv_zero, hfg x hx] using hf.1 0 le_rfl x hx
  · intro x hx y hy
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, hfg x hx, hfg y hy]
      using hf.2 x hx y hy

end KahlerForm
