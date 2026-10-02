module

public import CalabiYau.MongeAmpere.Estimates.C3.TraceLaplacian.Refined.NormalFrameEquation
public import CalabiYau.Geometry.Kahler.Laplacian

/-!
# Transport the Monge–Ampère potential Hessian to normal coordinates

The intrinsic reference complex Laplacian of `G` equals the ordered trace of
its correctly normalized mixed Wirtinger Hessian in the holomorphic normal
frame. Holomorphicity cancels the nonlinear coordinate map's mixed second jet;
no bound on a point-selected chart's inverse coefficients is asserted.

Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §3.3,
Lemma 3.10, pp. 45–46; Yau (1978), §3, scalar Hessian transport.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal
open ContinuousAlternatingMap
open Filter Topology

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

private theorem c3RefinedTrace_mixedPotentialDerivative_eq_complexHessian
    {n : ℕ} (u : EuclideanSpace ℂ (Fin n) → ℝ) {z : EuclideanSpace ℂ (Fin n)}
    (hu : ContDiffAt ℝ 2 u z) (i j : Fin n) :
    wirtingerDerivInChart (fun w ↦ c3RefinedTracePartialBar (fun v ↦ (u v : ℂ)) w j) z i =
      complexHessian u z i j := by
  let ei : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single i 1
  let ej : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j 1
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ u) z :=
    hu.fderiv_right (m := 1) (by norm_num)
  have hfdDiff : DifferentiableAt ℝ (fderiv ℝ u) z :=
    hfd.differentiableAt (by norm_num)
  have hA : DifferentiableAt ℝ (fun w ↦ fderiv ℝ u w ej) z :=
    hfdDiff.clm_apply (differentiableAt_const _)
  have hB : DifferentiableAt ℝ (fun w ↦ fderiv ℝ u w (Complex.I • ej)) z :=
    hfdDiff.clm_apply (differentiableAt_const _)
  have hAcomplex : DifferentiableAt ℝ (fun w ↦ (fderiv ℝ u w ej : ℂ)) z :=
    Complex.ofRealCLM.differentiableAt.comp z hA
  have hBcomplex : DifferentiableAt ℝ (fun w ↦
      (fderiv ℝ u w (Complex.I • ej) : ℂ)) z :=
    Complex.ofRealCLM.differentiableAt.comp z hB
  have hD (v q : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ fderiv ℝ u w q) z v =
        fderiv ℝ (fderiv ℝ u) z v q := by
    have h := fderiv_clm_apply (u := fun _ : EuclideanSpace ℂ (Fin n) ↦ q)
      hfdDiff (differentiableAt_const _)
    have h' := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ ↦ L v) h
    simpa using h'
  have hAc (v : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ (fderiv ℝ u w ej : ℂ)) z v =
        (fderiv ℝ (fderiv ℝ u) z v ej : ℂ) := by
    have hcomp := (Complex.ofRealCLM.hasFDerivAt.comp z hA.hasFDerivAt).fderiv
    have heval := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L v) hcomp
    simpa [Function.comp_def, hD v ej] using heval
  have hBc (v : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ (fderiv ℝ u w (Complex.I • ej) : ℂ)) z v =
        (fderiv ℝ (fderiv ℝ u) z v (Complex.I • ej) : ℂ) := by
    have hcomp := (Complex.ofRealCLM.hasFDerivAt.comp z hB.hasFDerivAt).fderiv
    have heval := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L v) hcomp
    simpa [Function.comp_def, hD v (Complex.I • ej)] using heval
  have hnum : DifferentiableAt ℝ (fun w ↦
      (fderiv ℝ u w ej : ℂ) + Complex.I * fderiv ℝ u w (Complex.I • ej)) z :=
    hAcomplex.add (hBcomplex.const_mul Complex.I)
  have hbar : (fun w ↦ c3RefinedTracePartialBar
      (fun v ↦ (u v : ℂ)) w j) =ᶠ[𝓝 z]
      fun w ↦ (2 : ℂ)⁻¹ * ((fderiv ℝ u w ej : ℂ) +
        Complex.I * fderiv ℝ u w (Complex.I • ej)) := by
    have hnear₂ : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ 2 u w := hu.eventually (by norm_num)
    have hnear : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ 1 u w :=
      hnear₂.mono (fun _ hw => hw.of_le (by norm_num))
    filter_upwards [hnear] with w hw
    have hdiff : DifferentiableAt ℝ u w := hw.differentiableAt (by norm_num)
    have hcomp (d : EuclideanSpace ℂ (Fin n)) :
        fderiv ℝ (fun v ↦ (u v : ℂ)) w d = (fderiv ℝ u w d : ℂ) := by
      have h := (Complex.ofRealCLM.hasFDerivAt.comp w hdiff.hasFDerivAt).fderiv
      have h' := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L d) h
      simpa [Function.comp_def] using h'
    simp only [c3RefinedTracePartialBar, hcomp, div_eq_mul_inv]
    ring
  have hpartial (v : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ c3RefinedTracePartialBar
        (fun v ↦ (u v : ℂ)) w j) z v =
        (2 : ℂ)⁻¹ * ((fderiv ℝ (fderiv ℝ u) z v ej : ℂ) +
          Complex.I * fderiv ℝ (fderiv ℝ u) z v (Complex.I • ej) : ℂ) := by
    have hfderiv := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hbar
    have heval := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L v) hfderiv
    rw [heval, fderiv_const_mul hnum (2 : ℂ)⁻¹,
      fderiv_fun_add hAcomplex (hBcomplex.const_mul Complex.I),
      fderiv_const_mul hBcomplex Complex.I]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, hAc, hBc]
  unfold wirtingerDerivInChart
  rw [hpartial ei, hpartial (Complex.I • ei)]
  rw [complexHessian_apply hu i j]
  simp only [ei, ej, div_eq_mul_inv]
  ring_nf
  rw [Complex.I_sq]
  ring_nf

private theorem c3RefinedTrace_complexHessian_comp_holomorphic
    {n : ℕ} (u : EuclideanSpace ℂ (Fin n) → ℝ)
    (F : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    {z : EuclideanSpace ℂ (Fin n)}
    (hu : ContDiffAt ℝ 2 u (F z))
    (hF : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ F w) :
    complexHessian (u ∘ F) z =
      (EuclideanSpace.clmMatrix (fderiv ℂ F z)).transpose *
        complexHessian u (F z) * (EuclideanSpace.clmMatrix (fderiv ℂ F z)).map star := by
  have hcomp : ddbar (u ∘ F) z =
      (ddbar u (F z)).compContinuousLinearMap ((fderiv ℂ F z).restrictScalars ℝ) :=
    ddbar_comp_holomorphic hF hu
  rw [complexHessian, complexHessian, hcomp]
  exact (isOneOne_ddbar hu).coeffMatrix_compContinuousLinearMap (fderiv ℂ F z)

private theorem c3RefinedTrace_jacobian_equiv {n : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hdet : IsUnit (EuclideanSpace.clmMatrix A).det) :
    ∃ e : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n),
      (e : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) = A := by
  let b : Module.Basis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)) :=
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
  have hmatrix : LinearMap.toMatrix b b (A.toLinearMap) = EuclideanSpace.clmMatrix A := by
    ext i j
    simp [EuclideanSpace.clmMatrix, b, LinearMap.toMatrix_apply,
      EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
  have hA : IsUnit (A.toLinearMap) := by
    rw [LinearMap.isUnit_iff_isUnit_det, ← LinearMap.det_toMatrix b,
      hmatrix]
    exact hdet
  have hker : (A.toLinearMap).ker = ⊥ := by
    rw [← LinearMap.isUnit_iff_ker_eq_bot]
    exact hA
  have hrange : (A.toLinearMap).range = ⊤ :=
    LinearMap.ker_eq_bot_iff_range_eq_top.mp hker
  have hbij : Function.Bijective A := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      have hxy' : A.toLinearMap (x - y) = 0 := by
        change A (x - y) = 0
        rw [map_sub, hxy]
        simp
      have hker' : x - y ∈ (A.toLinearMap).ker := LinearMap.mem_ker.mpr hxy'
      rw [hker, Submodule.mem_bot] at hker'
      exact sub_eq_zero.mp hker'
    · intro y
      have hy : y ∈ (A.toLinearMap).range := by rw [hrange]; simp
      obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hy
      exact ⟨x, hx⟩
  exact ⟨ContinuousLinearEquiv.ofBijective A hker hrange, rfl⟩

private theorem c3RefinedTrace_hasFTaylorSeriesUpToOn_restrictScalars
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
    [IsScalarTower ℝ ℂ F] {n : ℕ∞ω} {f : E → F}
    {p : E → FormalMultilinearSeries ℂ E F} {s : Set E}
    (h : HasFTaylorSeriesUpToOn n f p s) :
    HasFTaylorSeriesUpToOn n f (fun x => (p x).restrictScalars ℝ) s where
  zero_eq x hx := h.zero_eq x hx
  fderivWithin m hm x hx :=
    ((ContinuousMultilinearMap.restrictScalarsLinear ℝ).hasFDerivAt.comp_hasFDerivWithinAt x <|
      (h.fderivWithin m hm x hx).restrictScalars ℝ :)
  cont m hm := ContinuousMultilinearMap.continuous_restrictScalars.comp_continuousOn (h.cont m hm)

private theorem c3RefinedTrace_contDiffAt_restrictScalars
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
    [IsScalarTower ℝ ℂ F] {n : ℕ} {f : E → F} {x : E}
    (h : ContDiffAt ℂ n f x) : ContDiffAt ℝ n f x := by
  rw [← contDiffWithinAt_univ] at h ⊢
  intro m hm
  rcases h m hm with ⟨u, hu, p, hp⟩
  exact ⟨u, hu, (fun y => (p y).restrictScalars ℝ),
    c3RefinedTrace_hasFTaylorSeriesUpToOn_restrictScalars hp⟩

/-- The fixed reference Laplacian of a smooth real potential is its trace
of `∂z∂bar` in the reference-normal frame. Each Wirtinger operator includes
`1/2`: for flat `n = 1`, `G(z)=|z|²` gives both sides `1`, rather than the real
Laplacian `4`. In dimension zero both sums vanish, and rotation by `i` leaves
the expression invariant. -/
theorem c3RefinedTrace_normalFrame_potentialHessian
    (ω₀ : KahlerForm n M) (G φ : M → ℝ)
    (hG : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G)
    (x : M)
    (frame : C3RefinedTraceNormalCoordinateFrame ω₀ φ x) :
    let H := c3RefinedTracePulledPotential G x frame.coord
    ω₀.laplacian G x =
      ∑ p : Fin n, RCLike.re
        (wirtingerDerivInChart (fun w ↦ c3RefinedTracePartialBar H w p) frame.center p) := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let z₀ := e x
  let u : EuclideanSpace ℂ (Fin n) → ℝ := fun z ↦ G (e.symm z)
  let F := frame.coord
  let H := c3RefinedTracePulledPotential G x F
  have hz₀ : z₀ ∈ e.target := mem_extChartAt_target x
  have hsymm : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ e.symm z₀ := by
    exact (contMDiffOn_extChartAt_symm x).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz₀)
  have huMD : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u z₀ := by
    dsimp [u]
    exact (hG x).comp_of_eq hsymm (e.left_inv (mem_extChartAt_source x))
  have hu : ContDiffAt ℝ 2 u z₀ := by
    exact ((contMDiffAt_iff_contDiffAt).mp huMD).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hF1 : ContDiffOn ℂ 1 F frame.domain :=
    frame.holomorphic.of_le (by norm_num)
  have hFdiff : DifferentiableOn ℂ F frame.domain :=
    hF1.differentiableOn (by norm_num)
  have hFnear : ∀ᶠ w in 𝓝 frame.center, DifferentiableAt ℂ F w := by
    filter_upwards [frame.open_domain.mem_nhds frame.center_mem] with w hw
    exact (hFdiff w hw).differentiableAt (frame.open_domain.mem_nhds hw)
  let A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    fderiv ℂ F frame.center
  have hAunit : IsUnit (EuclideanSpace.clmMatrix A).det := by
    change IsUnit (EuclideanSpace.clmMatrix (fderiv ℂ frame.coord frame.center)).det
    exact frame.jacobian_unit frame.center frame.center_mem
  obtain ⟨Aequiv, hAequiv⟩ := c3RefinedTrace_jacobian_equiv A hAunit
  have hFtwo : ContDiffOn ℂ 2 F frame.domain :=
    frame.holomorphic.of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hFcomplex : ContDiffAt ℂ 2 F frame.center :=
    hFtwo.contDiffAt (frame.open_domain.mem_nhds frame.center_mem)
  have hFreal : ContDiffAt ℝ 2 F frame.center :=
    c3RefinedTrace_contDiffAt_restrictScalars hFcomplex
  have hFcenter : F frame.center = z₀ := by
    dsimp [F, z₀, e]
    exact frame.center_eq
  have huF0 : ContDiffAt ℝ 2 u (F frame.center) := by
    simpa [hFcenter] using hu
  have hcomp := c3RefinedTrace_complexHessian_comp_holomorphic u F huF0 hFnear
  have huF : ContDiffAt ℝ 2 (u ∘ F) frame.center := huF0.comp frame.center hFreal
  have hpartial (p : Fin n) :
      wirtingerDerivInChart (fun w ↦ c3RefinedTracePartialBar H w p) frame.center p =
        complexHessian (u ∘ F) frame.center p p := by
    dsimp [H, c3RefinedTracePulledPotential, u, F, e]
    exact c3RefinedTrace_mixedPotentialDerivative_eq_complexHessian (u ∘ F) huF p p
  have hRef : (EuclideanSpace.clmMatrix A).transpose *
      (ω₀ x).coeffMatrix * (EuclideanSpace.clmMatrix A).map star = 1 := by
    rw [← ω₀.metricInChart_self x, ← frame.center_eq]
    simpa [A, c3RefinedTracePulledReferenceMetric, F] using frame.reference_normal
  have hAlpha : (mddbar n G x).coeffMatrix = complexHessian u z₀ := by
    calc
      _ = ((mddbar n G).chartRep x z₀).coeffMatrix := by
        rw [FormField.chartRep_self]
      _ = _ := by
        rw [chartRep_mddbar hG x hz₀]
        rfl
  have hRefComp :
      ((ω₀ x).compContinuousLinearMap (A.restrictScalars ℝ)).coeffMatrix = 1 := by
    rw [(ω₀.isOneOne x).coeffMatrix_compContinuousLinearMap A]
    rw [hRef]
  have hAlphaComp :
      ((mddbar n G x).compContinuousLinearMap (A.restrictScalars ℝ)).coeffMatrix =
        complexHessian (u ∘ F) frame.center := by
    rw [(isOneOne_mddbar hG x).coeffMatrix_compContinuousLinearMap A]
    rw [hAlpha, ← hFcenter, ← hcomp]
  have hTrace := ContinuousAlternatingMap.relTrace_compContinuousLinearMap
    (ω₀.isOneOne x) (isOneOne_mddbar hG x) Aequiv
  rw [hAequiv] at hTrace
  have hTraceComp :
      relTrace ((ω₀ x).compContinuousLinearMap (A.restrictScalars ℝ))
        ((mddbar n G x).compContinuousLinearMap (A.restrictScalars ℝ)) =
        RCLike.re (complexHessian (u ∘ F) frame.center).trace := by
    rw [relTrace, hRefComp, hAlphaComp]
    simp
  have hsum :
      (∑ p : Fin n, RCLike.re
        (wirtingerDerivInChart (fun w ↦ c3RefinedTracePartialBar H w p) frame.center p)) =
        RCLike.re (complexHessian (u ∘ F) frame.center).trace := by
    rw [Finset.sum_congr rfl (fun p _ ↦ congrArg RCLike.re (hpartial p))]
    simp [Matrix.trace]
  change relTrace (ω₀ x) (mddbar n G x) = _
  rw [← hTrace, hTraceComp, hsum]

end KahlerForm
