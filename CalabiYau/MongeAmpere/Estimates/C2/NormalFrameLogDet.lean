module

public import CalabiYau.Geometry.Kahler.Curvature.Chart
import all CalabiYau.Geometry.Kahler.Curvature.Chart
public import CalabiYau.Geometry.Kahler.Ricci
public import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.NormalCoordinates.HolomorphicPatch
import all CalabiYau.Mathlib.Analysis.Complex.JacobianLogNorm

public section

open Filter
open scoped Manifold ContDiff Topology

namespace KahlerForm

private lemma holomorphicJacobianMatrix_det_eq {n : ℕ}
    (ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) :
    (holomorphicJacobianMatrix ψ z).det =
      LinearMap.det (fderiv ℂ ψ z).toLinearMap := by
  let b := (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
  have hm : holomorphicJacobianMatrix ψ z =
      LinearMap.toMatrix b b (fderiv ℂ ψ z).toLinearMap := by
    ext i j
    simp [holomorphicJacobianMatrix, EuclideanSpace.clmMatrix,
      LinearMap.toMatrix_apply, EuclideanSpace.basisFun_repr, b]
  rw [hm, LinearMap.det_toMatrix]

private lemma pulledBackMetricInChart_det_factor {n : ℕ}
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₁ : KahlerForm n M) (x : M)
    (ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) :
    (pulledBackMetricInChart ω₁ x ψ z).det =
      (ω₁.metricInChart x (ψ z)).det *
        (Complex.normSq (LinearMap.det (fderiv ℂ ψ z).toLinearMap) : ℂ) := by
  rw [pulledBackMetricInChart, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hm : (holomorphicJacobianMatrix ψ z).map star =
      (starRingEnd ℂ).mapMatrix (holomorphicJacobianMatrix ψ z) := by
    ext i j
    rfl
  rw [hm, ← (starRingEnd ℂ).map_det (holomorphicJacobianMatrix ψ z),
    holomorphicJacobianMatrix_det_eq, Complex.normSq_eq_conj_mul_self]
  ring

private lemma pullback_logdet_factor_eventually {n : ℕ}
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₁ : KahlerForm n M) (x : M)
    (ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (z : EuclideanSpace ℂ (Fin n))
    (hψ : ContDiffAt ℝ 3 ψ z)
    (hψhol : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ ψ w)
    (hchart : ψ z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (hdet : (holomorphicJacobianMatrix ψ z).det ≠ 0) :
    ∀ᶠ w in 𝓝 z,
      Real.log (RCLike.re ((pulledBackMetricInChart ω₁ x ψ w).det)) =
        ω₁.logDetInChart x (ψ w) +
          Real.log (Complex.normSq (LinearMap.det (fderiv ℂ ψ w).toLinearMap)) := by
  have hj : (holomorphicJacobianMatrix ψ z).det =
      LinearMap.det (fderiv ℂ ψ z).toLinearMap :=
    holomorphicJacobianMatrix_det_eq ψ z
  have hdet' : LinearMap.det (fderiv ℂ ψ z).toLinearMap ≠ 0 := by
    simpa [hj] using hdet
  have htarget : ∀ᶠ w in 𝓝 z,
      ψ w ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target :=
    hψ.continuousAt.eventually
      ((isOpen_extChartAt_target x).mem_nhds hchart)
  have hjcont : ContinuousAt
      (fun w : EuclideanSpace ℂ (Fin n) => LinearMap.det (fderiv ℂ ψ w).toLinearMap) z := by
    exact (Complex.jacobianDet_contDiffAt_real_two hψ hψhol).continuousAt
  have hjnear : ∀ᶠ w in 𝓝 z,
      LinearMap.det (fderiv ℂ ψ w).toLinearMap ≠ 0 := hjcont.eventually_ne hdet'
  filter_upwards [htarget, hjnear] with w hwchart hwdet
  have hpos := ω₁.posDef_metricInChart x hwchart
  have hdetpos := hpos.det_pos
  have hdetpos' := (RCLike.pos_iff.mp hdetpos)
  have hG : (ω₁.metricInChart x (ψ w)).det =
      ((ω₁.metricInChart x (ψ w)).det.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hdetpos'.2
  rw [pulledBackMetricInChart_det_factor, hG]
  have hre : RCLike.re
      (((ω₁.metricInChart x (ψ w)).det.re : ℂ) *
        (Complex.normSq (LinearMap.det (fderiv ℂ ψ w).toLinearMap) : ℂ)) =
      (ω₁.metricInChart x (ψ w)).det.re *
        Complex.normSq (LinearMap.det (fderiv ℂ ψ w).toLinearMap) := by
    simp
  rw [hre]
  dsimp [logDetInChart]
  have ha : (ω₁.metricInChart x (ψ w)).det.re ≠ 0 := by
    exact ne_of_gt (by simpa using hdetpos'.1)
  rw [Real.log_mul ha (ne_of_gt (Complex.normSq_pos.2 hwdet))]

private lemma chartPartialBarComplex_ofReal {n : ℕ}
    (f : EuclideanSpace ℂ (Fin n) → ℝ)
    (z : EuclideanSpace ℂ (Fin n)) (p : Fin n)
    (hf : DifferentiableAt ℝ f z) :
    chartPartialBarComplex (fun w => (f w : ℂ)) z p = chartPartialBar f z p := by
  have hder : fderiv ℝ (fun w => (f w : ℂ)) z =
      Complex.ofRealCLM.comp (fderiv ℝ f z) := by
    change fderiv ℝ (Complex.ofRealCLM ∘ f) z = _
    exact (Complex.ofRealCLM.hasFDerivAt.comp z hf.hasFDerivAt).fderiv
  simp only [chartPartialBarComplex, chartPartialBar]
  rw [hder]
  simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]

private lemma complexHessian_add {n : ℕ}
    (f g : EuclideanSpace ℂ (Fin n) → ℝ)
    (z : EuclideanSpace ℂ (Fin n)) (p : Fin n)
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    complexHessian (fun w => f w + g w) z p p =
      complexHessian f z p p + complexHessian g z p p := by
  have hf' : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hg' : DifferentiableAt ℝ (fderiv ℝ g) z :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hfirst : fderiv ℝ (fun w => f w + g w) =ᶠ[𝓝 z]
      fderiv ℝ f + fderiv ℝ g := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with w hwf hwg
    change fderiv ℝ (f + g) w =
      (fderiv ℝ f + fderiv ℝ g) w
    have h := fderiv_add (hwf.differentiableAt (by norm_num))
      (hwg.differentiableAt (by norm_num))
    change fderiv ℝ (f + g) w = fderiv ℝ f w + fderiv ℝ g w
    exact h
  have hsecond : fderiv ℝ (fderiv ℝ (fun w => f w + g w)) z =
      fderiv ℝ (fderiv ℝ f) z + fderiv ℝ (fderiv ℝ g) z := by
    rw [hfirst.fderiv_eq, fderiv_add hf' hg']
  rw [complexHessian_apply (hf.add hg) p p,
    complexHessian_apply hf p p, complexHessian_apply hg p p]
  simp only [hsecond, add_apply, Complex.ofReal_add]
  ring_nf

private lemma jacobianLogNorm_complexHessian_eq_zero {n : ℕ}
    {ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)}
    {z : EuclideanSpace ℂ (Fin n)}
    (hψ : ContDiffAt ℝ 3 ψ z)
    (hψhol : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ ψ w)
    (hdet : LinearMap.det (fderiv ℂ ψ z).toLinearMap ≠ 0)
    (p : Fin n) :
    complexHessian (fun w => Real.log
      (Complex.normSq (LinearMap.det (fderiv ℂ ψ w).toLinearMap))) z p p = 0 := by
  have hreg : ContDiffAt ℝ 2 (fun w => Real.log
      (Complex.normSq (LinearMap.det (fderiv ℂ ψ w).toLinearMap))) z :=
    Complex.jacobianLogNorm_contDiffAt_real_two hψ hψhol hdet
  let e : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single p 1
  have hmix := Complex.jacobianLogNorm_mixed_hessian hψ hψhol hdet e e
  have hdiag := Complex.jacobianLogNorm_mixed_hessian hψ hψhol hdet e (Complex.I • e)
  have hI : fderiv ℝ (fderiv ℝ (fun w => Real.log
      (Complex.normSq (LinearMap.det (fderiv ℂ ψ w).toLinearMap)))) z
      (Complex.I • e) e =
      fderiv ℝ (fderiv ℝ (fun w => Real.log
      (Complex.normSq (LinearMap.det (fderiv ℂ ψ w).toLinearMap)))) z
      e (Complex.I • e) := hmix
  have hII : fderiv ℝ (fderiv ℝ (fun w => Real.log
      (Complex.normSq (LinearMap.det (fderiv ℂ ψ w).toLinearMap)))) z
      (Complex.I • e) (Complex.I • e) =
      -fderiv ℝ (fderiv ℝ (fun w => Real.log
      (Complex.normSq (LinearMap.det (fderiv ℂ ψ w).toLinearMap)))) z e e := by
    simpa [smul_smul, Complex.I_mul_I] using hdiag
  simp only [e] at hI hII
  rw [complexHessian_apply hreg p p]
  rw [hI, hII]
  rw [Complex.ofReal_neg]
  ring

private lemma complexHessian_eq_of_eventuallyEq {n : ℕ}
    (f g : EuclideanSpace ℂ (Fin n) → ℝ)
    (z : EuclideanSpace ℂ (Fin n)) (p : Fin n)
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z)
    (heq : f =ᶠ[𝓝 z] g) : complexHessian f z p p = complexHessian g z p p := by
  obtain ⟨U, hUeq, hUopen, hzU⟩ := mem_nhds_iff.mp heq
  have hDerEq : fderiv ℝ f =ᶠ[𝓝 z] fderiv ℝ g := by
    filter_upwards [hUopen.mem_nhds hzU] with w hw
    have hEqW : f =ᶠ[𝓝 w] g := by
      filter_upwards [hUopen.mem_nhds hw] with y hy
      exact hUeq hy
    exact hEqW.fderiv_eq
  have hSecond : fderiv ℝ (fderiv ℝ f) z = fderiv ℝ (fderiv ℝ g) z :=
    hDerEq.fderiv_eq
  rw [complexHessian_apply hf p p, complexHessian_apply hg p p, hSecond]

/-- The mixed real diagonal derivative of a pulled-back metric's log determinant is the
corresponding mixed derivative of the original metric's log determinant. -/
theorem pulledBackMetricInChart_log_det_mixed_second_real
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₁ : KahlerForm n M) (x : M)
    (ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (z : EuclideanSpace ℂ (Fin n))
    (hψ : ContDiffAt ℝ 3 ψ z)
    (hψhol : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ ψ w)
    (hchart : ψ z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (hdet : (holomorphicJacobianMatrix ψ z).det ≠ 0)
    (p : Fin n) :
    (chartPartialZComplex
      (fun w ↦ chartPartialBarComplex
        (fun v ↦ (Real.log (RCLike.re
          ((pulledBackMetricInChart ω₁ x ψ v).det)) : ℂ)) w p) z p).re =
      (complexHessian ((ω₁.logDetInChart x) ∘ ψ) z p p).re := by
  let f : EuclideanSpace ℂ (Fin n) → ℝ :=
    fun v => Real.log (RCLike.re ((pulledBackMetricInChart ω₁ x ψ v).det))
  let g : EuclideanSpace ℂ (Fin n) → ℝ := fun w =>
    ω₁.logDetInChart x (ψ w) +
      Real.log (Complex.normSq (LinearMap.det (fderiv ℂ ψ w).toLinearMap))
  have hsplit : f =ᶠ[𝓝 z] g := by
    filter_upwards [pullback_logdet_factor_eventually ω₁ x ψ z hψ hψhol hchart hdet]
      with w hw
    simpa [f, g] using hw
  have hdet' : LinearMap.det (fderiv ℂ ψ z).toLinearMap ≠ 0 := by
    have hj := holomorphicJacobianMatrix_det_eq ψ z
    simpa [hj] using hdet
  have hcomp : ContDiffAt ℝ 2 (fun w => ω₁.logDetInChart x (ψ w)) z := by
    have hlog := (ω₁.contDiffOn_logDetInChart x).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hchart)
    have hlog2 : ContDiffAt ℝ 2 (ω₁.logDetInChart x) (ψ z) :=
      hlog.of_le (WithTop.coe_le_coe.mpr
        (show (2 : ℕ∞) ≤ ⊤ from le_top))
    exact hlog2.comp z (hψ.of_le (by norm_num))
  have hJ : ContDiffAt ℝ 2
      (fun w => Real.log (Complex.normSq (LinearMap.det (fderiv ℂ ψ w).toLinearMap))) z :=
    Complex.jacobianLogNorm_contDiffAt_real_two hψ hψhol hdet'
  have hg : ContDiffAt ℝ 2 g z := by
    exact hcomp.add hJ
  have hf : ContDiffAt ℝ 2 f z := hg.congr_of_eventuallyEq hsplit
  have houter : fderiv ℝ
      (fun w => chartPartialBarComplex (fun v => (f v : ℂ)) w p) z =
      fderiv ℝ (fun w => chartPartialBar f w p) z := by
    apply Filter.EventuallyEq.fderiv_eq
    have hFnear : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ 2 f w := hf.eventually (by simp)
    filter_upwards [hFnear] with w hw
    exact chartPartialBarComplex_ofReal f w p (hw.differentiableAt (by norm_num))
  have hH : complexHessian f z p p = complexHessian g z p p :=
    complexHessian_eq_of_eventuallyEq f g z p hf hg hsplit
  rw [show (fun v => (Real.log (RCLike.re ((pulledBackMetricInChart ω₁ x ψ v).det)) : ℂ)) =
      (fun v => (f v : ℂ)) from rfl]
  change (chartPartialZComplex
    (fun w => chartPartialBarComplex (fun v => (f v : ℂ)) w p) z p).re = _
  have houter_re :
      (chartPartialZComplex
        (fun w => chartPartialBarComplex (fun v => (f v : ℂ)) w p) z p).re =
      (chartPartialZComplex (fun w => chartPartialBar f w p) z p).re := by
    unfold chartPartialZComplex
    rw [houter]
  calc
    _ = (chartPartialZComplex (fun w => chartPartialBar f w p) z p).re := houter_re
    _ = (complexHessian f z p p).re := by
      rw [chartPartialZComplex_chartPartialBar f z hf p p]
    _ = (complexHessian g z p p).re := by rw [hH]
    _ = (complexHessian ((ω₁.logDetInChart x) ∘ ψ) z p p).re := by
      have hAdd := complexHessian_add
        (fun w => ω₁.logDetInChart x (ψ w))
        (fun w => Real.log (Complex.normSq
          (LinearMap.det (fderiv ℂ ψ w).toLinearMap))) z p hcomp hJ
      have hAdd' : complexHessian g z p p =
          complexHessian ((ω₁.logDetInChart x) ∘ ψ) z p p +
            complexHessian (fun w => Real.log (Complex.normSq
              (LinearMap.det (fderiv ℂ ψ w).toLinearMap))) z p p := by
        change complexHessian (fun w => ω₁.logDetInChart x (ψ w) +
          Real.log (Complex.normSq (LinearMap.det (fderiv ℂ ψ w).toLinearMap))) z p p = _
        exact hAdd
      rw [hAdd', jacobianLogNorm_complexHessian_eq_zero hψ hψhol hdet' p]
      simp

end KahlerForm
