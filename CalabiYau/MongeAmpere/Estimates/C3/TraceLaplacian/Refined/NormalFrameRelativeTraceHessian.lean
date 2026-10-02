module

public import CalabiYau.MongeAmpere.Estimates.C3.TraceLaplacian.Refined.NormalFrameEquation

/-!
# Transport the relative-trace Hessian to normal coordinates

The relative trace is a scalar. Identify its intrinsic complex Laplacian with
the mixed matrix-trace Hessian in the fixed chart, and transport that Hessian
through a genuinely holomorphic normal-coordinate map. Inverse matrix factors
are ordered as `h⁻¹` contracted with `∂z∂bar tr(g⁻¹h)`; this does not transport
the right-hand-side potential or claim the chart is uniformly sized.

Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §3.3,
Lemma 3.10, pp. 45–46; Yau (1978), §3.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal
open ContinuousAlternatingMap
open scoped ComplexOrder MatrixOrder
open Filter Topology

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

private noncomputable def chartPartialBar
    (f : EuclideanSpace ℂ (Fin n) → ℝ)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n) : ℂ :=
  ((fderiv ℝ f z (EuclideanSpace.single j 1) : ℂ) +
    Complex.I * fderiv ℝ f z (Complex.I • EuclideanSpace.single j 1)) / 2

private noncomputable def chartPartialZComplex
    (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n) : ℂ :=
  (fderiv ℝ f z (EuclideanSpace.single j 1) -
    Complex.I * fderiv ℝ f z (Complex.I • EuclideanSpace.single j 1)) / 2

private theorem c3RefinedTraceRelativeTraceHessian_chartWirtinger
    (f : EuclideanSpace ℂ (Fin n) → ℝ) (z : EuclideanSpace ℂ (Fin n))
    (hf : ContDiffAt ℝ 2 f z) (j k : Fin n) :
    chartPartialZComplex (fun w ↦ chartPartialBar f w k) z j =
      complexHessian f z j k := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsecond (d e : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ fderiv ℝ f w e) z d = fderiv ℝ (fderiv ℝ f) z d e := by
    rw [fderiv_clm_apply hfd (differentiableAt_const e)]
    simp
  have hsecondComplex (d e : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ (fderiv ℝ f w e : ℂ)) z d =
        (fderiv ℝ (fderiv ℝ f) z d e : ℂ) := by
    have hreal := hfd.clm_apply (differentiableAt_const e)
    have h := (Complex.ofRealCLM.hasFDerivAt.comp z hreal.hasFDerivAt).fderiv
    have h' := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L d) h
    change fderiv ℝ (Complex.ofRealCLM ∘ (fun w ↦ fderiv ℝ f w e)) z d = _
    simpa [hsecond] using h'
  have hbarDeriv (d : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ chartPartialBar f w k) z d =
        ((fderiv ℝ (fderiv ℝ f) z d (EuclideanSpace.single k 1) : ℂ) +
          Complex.I * fderiv ℝ (fderiv ℝ f) z d
            (Complex.I • EuclideanSpace.single k 1)) / 2 := by
    let A := fun w ↦ (fderiv ℝ f w (EuclideanSpace.single k 1) : ℂ)
    let B := fun w ↦ (fderiv ℝ f w (Complex.I • EuclideanSpace.single k 1) : ℂ)
    have hA : DifferentiableAt ℝ A z := by
      exact (Complex.ofRealCLM.differentiableAt.comp z
        (hfd.clm_apply (differentiableAt_const _)))
    have hB : DifferentiableAt ℝ B z := by
      exact (Complex.ofRealCLM.differentiableAt.comp z
        (hfd.clm_apply (differentiableAt_const _)))
    have hnum : DifferentiableAt ℝ (fun w ↦ A w + Complex.I * B w) z :=
      hA.add (hB.const_mul Complex.I)
    have hfun : (fun w ↦ chartPartialBar f w k) =
        fun w ↦ (2 : ℂ)⁻¹ * (A w + Complex.I * B w) := by
      funext w
      simp [chartPartialBar, A, B, div_eq_mul_inv]
      ring
    rw [hfun, fderiv_const_mul hnum (2 : ℂ)⁻¹,
      fderiv_fun_add hA (hB.const_mul Complex.I), fderiv_const_mul hB Complex.I]
    dsimp [A, B]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    rw [hsecondComplex d (EuclideanSpace.single k 1),
      hsecondComplex d (Complex.I • EuclideanSpace.single k 1)]
    ring
  change ((fderiv ℝ (fun w ↦ chartPartialBar f w k) z (EuclideanSpace.single j 1) -
    Complex.I * fderiv ℝ (fun w ↦ chartPartialBar f w k) z
      (Complex.I • EuclideanSpace.single j 1)) / 2) = _
  rw [hbarDeriv (EuclideanSpace.single j 1),
    hbarDeriv (Complex.I • EuclideanSpace.single j 1), complexHessian_apply hf j k]
  ring_nf
  simp [Complex.I_sq]
  ring

private theorem c3RefinedTraceRelativeTraceHessian_realCastWirtinger
    (f : EuclideanSpace ℂ (Fin n) → ℝ) (z : EuclideanSpace ℂ (Fin n))
    (hf : ContDiffAt ℝ 2 f z) (p q : Fin n) :
    c3PartialZ (fun w ↦ c3RefinedTracePartialBar
      (fun v ↦ (f v : ℂ)) w q) z p = complexHessian f z p q := by
  have hbar : (fun w ↦ c3RefinedTracePartialBar (fun v ↦ (f v : ℂ)) w q) =ᶠ[𝓝 z]
      fun w ↦ chartPartialBar f w q := by
    filter_upwards [hf.eventually (by norm_num)] with w hw
    have hfd : fderiv ℝ (fun v ↦ (f v : ℂ)) w =
        (Complex.ofRealCLM).comp (fderiv ℝ f w) := by
      change fderiv ℝ (fun v ↦ Complex.ofRealCLM (f v)) w = _
      rw [fderiv_clm_apply (differentiableAt_const Complex.ofRealCLM)
        (hw.differentiableAt (by norm_num))]
      simp
    unfold c3RefinedTracePartialBar chartPartialBar
    rw [hfd]
    simp [ContinuousLinearMap.comp_apply]
  unfold c3PartialZ
  rw [hbar.fderiv_eq]
  change chartPartialZComplex (fun w ↦ chartPartialBar f w q) z p = _
  exact c3RefinedTraceRelativeTraceHessian_chartWirtinger f z hf p q

private theorem c3RefinedTraceRelativeTraceHessian_complexHessianPullback
    (F : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (f : EuclideanSpace ℂ (Fin n) → ℝ) (z : EuclideanSpace ℂ (Fin n))
    (hF : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ F w)
    (hf : ContDiffAt ℝ 2 f (F z)) :
    complexHessian (f ∘ F) z =
      (EuclideanSpace.clmMatrix (fderiv ℂ F z)).transpose *
        complexHessian f (F z) * (EuclideanSpace.clmMatrix (fderiv ℂ F z)).map star := by
  have hdd := ddbar_comp_holomorphic hF hf
  rw [complexHessian, complexHessian, hdd]
  exact (isOneOne_ddbar hf).coeffMatrix_compContinuousLinearMap (fderiv ℂ F z)

private theorem c3RefinedTraceRelativeTraceHessian_traceCongruence
    (A B P Q : Matrix (Fin n) (Fin n) ℂ)
    (hA : IsUnit A.det) (hP : IsUnit P.det) (hQ : IsUnit Q.det) :
    ((P * A * Q)⁻¹ * (P * B * Q)).trace = (A⁻¹ * B).trace := by
  have hInv : (P * A * Q)⁻¹ = Q⁻¹ * A⁻¹ * P⁻¹ := by
    apply Matrix.inv_eq_left_inv
    calc
      (Q⁻¹ * A⁻¹ * P⁻¹) * (P * A * Q) =
          Q⁻¹ * A⁻¹ * (P⁻¹ * P) * A * Q := by simp [Matrix.mul_assoc]
      _ = Q⁻¹ * (A⁻¹ * A) * Q := by
          rw [Matrix.nonsing_inv_mul P hP]
          simp [Matrix.mul_assoc]
      _ = Q⁻¹ * Q := by
          rw [Matrix.nonsing_inv_mul A hA]
          simp
      _ = 1 := Matrix.nonsing_inv_mul Q hQ
  rw [hInv]
  calc
    (Q⁻¹ * A⁻¹ * P⁻¹ * (P * B * Q)).trace =
        (Q⁻¹ * (A⁻¹ * (B * Q))).trace := by
          congr 1
          calc
            Q⁻¹ * A⁻¹ * P⁻¹ * (P * B * Q) =
                Q⁻¹ * A⁻¹ * (P⁻¹ * (P * (B * Q))) := by simp [Matrix.mul_assoc]
            _ = Q⁻¹ * A⁻¹ * (B * Q) := by
                rw [Matrix.nonsing_inv_mul_cancel_left P (B * Q) hP]
            _ = Q⁻¹ * (A⁻¹ * (B * Q)) := by simp [Matrix.mul_assoc]
    _ = ((Q⁻¹ * (A⁻¹ * B)) * Q).trace := by
          congr 1
          simp [Matrix.mul_assoc]
    _ = (Q * (Q⁻¹ * (A⁻¹ * B))).trace := Matrix.trace_mul_comm _ _
    _ = ((Q * Q⁻¹) * (A⁻¹ * B)).trace := by
          congr 1
          simp [Matrix.mul_assoc]
    _ = (A⁻¹ * B).trace := by
          rw [Matrix.mul_nonsing_inv Q hQ]
          simp

private theorem c3RefinedTraceRelativeTraceHessian_hermitianTraceReal
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (A * B).trace.im = 0 := by
  have hstar : star (A * B).trace = (A * B).trace := by
    calc
      star (A * B).trace = (Matrix.conjTranspose (A * B)).trace := by
        rw [Matrix.trace_conjTranspose]
      _ = (B * A).trace := by simp [Matrix.conjTranspose_mul, hA.eq, hB.eq]
      _ = (A * B).trace := Matrix.trace_mul_comm B A
  have h := congrArg Complex.im hstar
  have h' : -(A * B).trace.im = (A * B).trace.im := by
    simpa only [Complex.star_def, Complex.conj_im] using h
  linarith

private theorem c3RefinedTraceRelativeTraceHessian_frameTraceEqIntrinsic
    (ω₀ : KahlerForm n M) (G φ : M → ℝ)
    (hsol : ω₀.SolvesMongeAmpere G φ) (x : M)
    (frame : C3RefinedTraceNormalCoordinateFrame ω₀ φ x)
    (w : EuclideanSpace ℂ (Fin n)) (hw : w ∈ frame.domain) :
    c3RefinedTraceRelativeMatrixTrace
      (c3RefinedTracePulledReferenceMetric ω₀ x frame.coord)
      (c3RefinedTracePulledPerturbedMetric ω₀ φ x frame.coord) w =
      (relTrace (ω₀ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm
        (frame.coord w)))
        (ω₀ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm (frame.coord w)) +
          mddbar n φ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm
            (frame.coord w))) : ℂ) := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let z := frame.coord w
  let y := e.symm z
  let J := EuclideanSpace.clmMatrix (fderiv ℂ frame.coord w)
  let A := ω₀.metricInChart x z
  let H := complexHessian (φ ∘ e.symm) z
  let B := A + H
  have hz : z ∈ e.target := by
    exact frame.in_chart ⟨w, hw, rfl⟩
  have hyChart : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source := by
    have hyE : e.symm z ∈ e.source := e.map_target hz
    change e.symm z ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source
    rw [← extChartAt_source (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))]
    exact hyE
  have hJunit : IsUnit J.det := by
    dsimp [J, z]
    exact frame.jacobian_unit w hw
  have hPunit : IsUnit J.transpose.det := by
    rw [Matrix.det_transpose]
    exact hJunit
  have hQunit : IsUnit (J.map star).det := by
    have hdetQ : (J.map star).det = star J.det :=
      ((starRingEnd ℂ).map_det J).symm
    rw [hdetQ]
    exact hJunit.map (starRingEnd ℂ)
  have hApos : A.PosDef := by
    dsimp [A, z]
    exact ω₀.posDef_metricInChart x hz
  have hAunit : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hApos.isUnit
  have hBmetric : (ω₀.perturb φ hsol.1).metricInChart x z = B := by
    change (ω₀.perturb φ hsol.1).metricInChart x z =
      ω₀.metricInChart x z + complexHessian (φ ∘ e.symm) z
    exact ω₀.metricInChart_perturb hsol.1 x hz
  have hBpos : B.PosDef := by
    rw [← hBmetric]
    exact (ω₀.perturb φ hsol.1).posDef_metricInChart x hz
  have htraceMatrix :
      c3RefinedTraceRelativeMatrixTrace
        (c3RefinedTracePulledReferenceMetric ω₀ x frame.coord)
        (c3RefinedTracePulledPerturbedMetric ω₀ φ x frame.coord) w =
        (A⁻¹ * B).trace := by
    change ((J.transpose * A * J.map star)⁻¹ *
      (J.transpose * B * J.map star)).trace = _
    exact c3RefinedTraceRelativeTraceHessian_traceCongruence A B J.transpose (J.map star) hAunit hPunit hQunit
  have hrel : relTrace (ω₀ y) (ω₀ y + mddbar n φ y) =
      (n : ℝ) + ω₀.laplacian φ y := by
    rw [ContinuousAlternatingMap.relTrace_add,
      ContinuousAlternatingMap.relTrace_self (ω₀.isPositive y)]
    rfl
  have hLap := ω₀.laplacian_eq_inChart hsol.1.1 x (y := y) hyChart
  have hyEq : extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y = z := by
    exact e.right_inv hz
  rw [hyEq] at hLap
  have htraceRe : RCLike.re ((A⁻¹ * B).trace) =
      (n : ℝ) + ω₀.laplacian φ y := by
    rw [hLap]
    have hinv : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hAunit
    calc
      RCLike.re ((A⁻¹ * B).trace) =
          RCLike.re ((A⁻¹ * A).trace) + RCLike.re ((A⁻¹ * H).trace) := by
            dsimp [B]
            simp only [Matrix.mul_add, Matrix.trace_add, Complex.add_re]
      _ = (n : ℝ) + RCLike.re ((A⁻¹ * H).trace) := by
            rw [hinv]
            simp [Matrix.trace_one]
  have htraceIm : (A⁻¹ * B).trace.im = 0 :=
    c3RefinedTraceRelativeTraceHessian_hermitianTraceReal A⁻¹ B hApos.isHermitian.inv hBpos.isHermitian
  rw [htraceMatrix]
  apply Complex.ext
  · change RCLike.re ((A⁻¹ * B).trace) =
      relTrace (ω₀ y) (ω₀ y + mddbar n φ y)
    exact htraceRe.trans hrel.symm
  · exact htraceIm

/-- The perturbed Laplacian of the relative trace in a holomorphic normal
frame, using the actual pulled-back reference and perturbed coefficients.
Both sides vanish when `n = 0`; for constant flat `n = 1` data they vanish;
a unitary linear coordinate change preserves the contracted scalar. -/
theorem c3RefinedTrace_normalFrame_relativeTraceHessian
    (ω₀ : KahlerForm n M) (G φ : M → ℝ)
    (hsol : ω₀.SolvesMongeAmpere G φ) (x : M)
    (frame : C3RefinedTraceNormalCoordinateFrame ω₀ φ x) :
    let g := c3RefinedTracePulledReferenceMetric ω₀ x frame.coord
    let h := c3RefinedTracePulledPerturbedMetric ω₀ φ x frame.coord
    (ω₀.perturb φ hsol.1).laplacian
        (fun y ↦ relTrace (ω₀ y) (ω₀ y + mddbar n φ y)) x =
      RCLike.re (((h frame.center)⁻¹ * Matrix.of (fun p q ↦
        c3PartialZ (fun w ↦ c3RefinedTracePartialBar
          (fun v ↦ c3RefinedTraceRelativeMatrixTrace g h v) w q) frame.center p)).trace) := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let z₀ := e x
  let f : M → ℝ := fun y ↦ relTrace (ω₀ y) (ω₀ y + mddbar n φ y)
  let g := c3RefinedTracePulledReferenceMetric ω₀ x frame.coord
  let h := c3RefinedTracePulledPerturbedMetric ω₀ φ x frame.coord
  let T : EuclideanSpace ℂ (Fin n) → ℂ := fun w ↦
    c3RefinedTraceRelativeMatrixTrace g h w
  let u : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ f (e.symm (frame.coord w))
  have hfId : f = fun y ↦ (n : ℝ) + ω₀.laplacian φ y := by
    funext y
    dsimp [f]
    rw [ContinuousAlternatingMap.relTrace_add,
      ContinuousAlternatingMap.relTrace_self (ω₀.isPositive y)]
    rfl
  have hfSmooth : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f := by
    rw [hfId]
    exact contMDiff_const.add (ω₀.contMDiff_laplacian hsol.1.1)
  have hz₀ : z₀ ∈ e.target := by
    change extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x ∈ _
    exact mem_extChartAt_target x
  have hsymm : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ e.symm z₀ := by
    exact (contMDiffOn_extChartAt_symm x).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz₀)
  have hfChartMD : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (f ∘ e.symm) z₀ :=
    (hfSmooth (e.symm z₀)).comp_of_eq hsymm rfl
  have hfChart : ContDiffAt ℝ ∞ (f ∘ e.symm) z₀ := hfChartMD.contDiffAt
  have hFreal : ContDiffOn ℝ ∞ frame.coord frame.domain :=
    frame.holomorphic.restrict_scalars ℝ
  have hFtwo : ContDiffAt ℝ 2 frame.coord frame.center := by
    have hFcenter := hFreal.contDiffAt
      (frame.open_domain.mem_nhds frame.center_mem)
    exact hFcenter.of_le (WithTop.coe_le_coe.mpr
      (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hfChartTwo : ContDiffAt ℝ 2 (f ∘ e.symm) z₀ :=
    hfChart.of_le (WithTop.coe_le_coe.mpr
      (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hfChartTwoF : ContDiffAt ℝ 2 (f ∘ e.symm) (frame.coord frame.center) := by
    rw [frame.center_eq]
    exact hfChartTwo
  have hUtwo : ContDiffAt ℝ 2 u frame.center := by
    have hcomp := hfChartTwoF.comp frame.center hFtwo
    simpa [u, Function.comp_def] using hcomp
  have hFhol : ∀ᶠ w in 𝓝 frame.center, DifferentiableAt ℂ frame.coord w := by
    filter_upwards [frame.open_domain.mem_nhds frame.center_mem] with w hw
    exact (frame.holomorphic.contDiffAt (frame.open_domain.mem_nhds hw)).differentiableAt
      (by norm_num)
  have hEqOn : ∀ w ∈ frame.domain, T w = (u w : ℂ) := by
    intro w hw
    simpa [T, u, f, g, h, e, Function.comp_def] using
      c3RefinedTraceRelativeTraceHessian_frameTraceEqIntrinsic ω₀ G φ hsol x frame w hw
  have hMixed (p q : Fin n) :
      c3PartialZ (fun w ↦ c3RefinedTracePartialBar T w q) frame.center p =
        complexHessian u frame.center p q := by
    have hbarAt (w : EuclideanSpace ℂ (Fin n)) (hw : w ∈ frame.domain) :
        c3RefinedTracePartialBar T w q =
          c3RefinedTracePartialBar (fun v ↦ (u v : ℂ)) w q := by
      have hlocal : T =ᶠ[𝓝 w] fun v ↦ (u v : ℂ) := by
        filter_upwards [frame.open_domain.mem_nhds hw] with v hv
        exact hEqOn v hv
      unfold c3RefinedTracePartialBar
      rw [hlocal.fderiv_eq]
    have hbar : (fun w ↦ c3RefinedTracePartialBar T w q) =ᶠ[𝓝 frame.center]
        fun w ↦ c3RefinedTracePartialBar (fun v ↦ (u v : ℂ)) w q := by
      filter_upwards [frame.open_domain.mem_nhds frame.center_mem] with w hw
      exact hbarAt w hw
    unfold c3PartialZ
    rw [hbar.fderiv_eq]
    exact c3RefinedTraceRelativeTraceHessian_realCastWirtinger u frame.center hUtwo p q
  have hHessianMatrix :
      Matrix.of (fun p q ↦ c3PartialZ
        (fun w ↦ c3RefinedTracePartialBar T w q) frame.center p) =
        complexHessian u frame.center := by
    ext p q
    exact hMixed p q
  have hJunit : IsUnit (EuclideanSpace.clmMatrix
      (fderiv ℂ frame.coord frame.center)).det :=
    frame.jacobian_unit frame.center frame.center_mem
  let J := EuclideanSpace.clmMatrix (fderiv ℂ frame.coord frame.center)
  let P := J.transpose
  let Q := J.map star
  let A := (ω₀.perturb φ hsol.1).metricInChart x z₀
  let B := complexHessian (f ∘ e.symm) z₀
  have hPunit : IsUnit P.det := by
    rw [Matrix.det_transpose]
    exact hJunit
  have hQunit : IsUnit Q.det := by
    have hdetQ : Q.det = star J.det := by
      dsimp [Q]
      exact ((starRingEnd ℂ).map_det J).symm
    rw [hdetQ]
    exact hJunit.map (starRingEnd ℂ)
  have hApos : A.PosDef := by
    dsimp [A]
    exact (ω₀.perturb φ hsol.1).posDef_metricInChart x hz₀
  have hAunit : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hApos.isUnit
  have hPullHessian : complexHessian u frame.center = P * B * Q := by
    have h := c3RefinedTraceRelativeTraceHessian_complexHessianPullback frame.coord (f ∘ e.symm)
      frame.center hFhol hfChartTwoF
    change complexHessian (fun w ↦ f (e.symm (frame.coord w))) frame.center =
      J.transpose * complexHessian (f ∘ e.symm) (frame.coord frame.center) * J.map star at h
    rw [frame.center_eq] at h
    simpa [u, B, J, P, Q, z₀, e] using h
  have hTracePullback :
      ((P * A * Q)⁻¹ * (P * B * Q)).trace = (A⁻¹ * B).trace :=
    c3RefinedTraceRelativeTraceHessian_traceCongruence A B P Q hAunit hPunit hQunit
  have hmetricPert : (ω₀.perturb φ hsol.1).metricInChart x z₀ =
      ω₀.metricInChart x z₀ + complexHessian (φ ∘ e.symm) z₀ :=
    ω₀.metricInChart_perturb hsol.1 x hz₀
  have hmetricCenter : h frame.center = P * A * Q := by
    change J.transpose * (ω₀.metricInChart x (frame.coord frame.center) +
      complexHessian (φ ∘ e.symm) (frame.coord frame.center)) * J.map star = _
    rw [frame.center_eq, ← hmetricPert]
  have hLap := (ω₀.perturb φ hsol.1).laplacian_eq_inChart hfSmooth x
    (y := x) (by simp)
  have hLapChart : (ω₀.perturb φ hsol.1).laplacian f x =
      RCLike.re ((A⁻¹ * B).trace) := by
    rw [hLap]
  dsimp only
  rw [hLapChart, hHessianMatrix]
  change RCLike.re ((A⁻¹ * B).trace) =
    RCLike.re (((h frame.center)⁻¹ * complexHessian u frame.center).trace)
  rw [hPullHessian, hmetricCenter]
  exact congrArg RCLike.re hTracePullback.symm

end KahlerForm
