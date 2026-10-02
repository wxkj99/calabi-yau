module

public import CalabiYau.MongeAmpere.Estimates.C3.TraceLaplacian.Refined.NormalCoordinateFrame
import CalabiYau.MongeAmpere.Estimates.C2.PullbackMetricSymmetry

/-!
# The Monge–Ampère equation in a holomorphic normal frame

A holomorphic change of coordinates preserves Hermitian symmetry, the Kähler
mixed-derivative identity, and the determinant-ratio equation. These local
facts feed the normal-frame matrix identity; they are not part of the normal
chart's existence theorem or the subsequent scalar transport theorem.

Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §3.2,
Lemma 3.8, pp. 41–43, and §3.3, Lemma 3.10, pp. 45–46; Yau (1978), §3.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- The real potential in the new holomorphic coordinate chart, included into
`ℂ` to match the complex determinant identity and Wirtinger derivatives. -/
noncomputable def c3RefinedTracePulledPotential (G : M → ℝ) (x : M)
    (F : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (w : EuclideanSpace ℂ (Fin n)) : ℂ :=
  ((G ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm (F w)) : ℝ) : ℂ)

/-- The reference and perturbed metric in a normal frame satisfy the exact
smooth Hermitian determinant equation on a neighborhood and Kähler's exchange
of mixed derivatives at its center. No boundedness estimate is included. -/
private theorem hasFTaylorSeriesUpToOn_restrictScalars
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
    [IsScalarTower ℝ ℂ F] {k : ℕ∞ω} {f : E → F}
    {p : E → FormalMultilinearSeries ℂ E F} {s : Set E}
    (h : HasFTaylorSeriesUpToOn k f p s) :
    HasFTaylorSeriesUpToOn k f (fun x => (p x).restrictScalars ℝ) s where
  zero_eq x hx := h.zero_eq x hx
  fderivWithin m hm x hx :=
    ((ContinuousMultilinearMap.restrictScalarsLinear ℝ).hasFDerivAt.comp_hasFDerivWithinAt x <|
      (h.fderivWithin m hm x hx).restrictScalars ℝ :)
  cont m hm := ContinuousMultilinearMap.continuous_restrictScalars.comp_continuousOn (h.cont m hm)

private theorem contDiffAt_restrictScalars
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
    [IsScalarTower ℝ ℂ F] {k : ℕ} {f : E → F} {x : E}
    (h : ContDiffAt ℂ k f x) : ContDiffAt ℝ k f x := by
  rw [← contDiffWithinAt_univ] at h ⊢
  intro m hm
  rcases h m hm with ⟨u, hu, p, hp⟩
  exact ⟨u, hu, (fun y => (p y).restrictScalars ℝ),
    hasFTaylorSeriesUpToOn_restrictScalars hp⟩

private theorem frame_coord_smooth_at (ω₀ : KahlerForm n M) (φ : M → ℝ) (x : M)
    (frame : C3RefinedTraceNormalCoordinateFrame ω₀ φ x) :
    ContDiffAt ℝ ∞ frame.coord frame.center := by
  have hC : ContDiffAt ℂ ∞ frame.coord frame.center :=
    frame.holomorphic.contDiffAt (frame.open_domain.mem_nhds frame.center_mem)
  rw [contDiffAt_infty]
  intro m
  apply contDiffAt_restrictScalars (k := m)
  have hm : (m : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    change ((m : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  exact hC.of_le hm

private theorem frame_jacobian_entry_contDiffAt (ω₀ : KahlerForm n M) (φ : M → ℝ)
    (x : M) (frame : C3RefinedTraceNormalCoordinateFrame ω₀ φ x) (i j : Fin n) :
    ContDiffAt ℝ ∞
      (fun w ↦ EuclideanSpace.clmMatrix (fderiv ℂ frame.coord w) i j) frame.center := by
  have hC : ContDiffAt ℂ ∞ frame.coord frame.center :=
    frame.holomorphic.contDiffAt (frame.open_domain.mem_nhds frame.center_mem)
  have hD : ContDiffAt ℂ ∞ (fderiv ℂ frame.coord) frame.center :=
    hC.fderiv_right (m := ∞) (by simp)
  have hEval : ContDiffAt ℂ ∞
      (fun w ↦ fderiv ℂ frame.coord w (EuclideanSpace.single j 1) i) frame.center := by
    fun_prop (disch := exact hD)
  have hJ : ContDiffAt ℂ ∞
      (fun w ↦ EuclideanSpace.clmMatrix (fderiv ℂ frame.coord w) i j) frame.center := by
    simpa [EuclideanSpace.clmMatrix] using hEval
  rw [contDiffAt_infty]
  intro m
  apply contDiffAt_restrictScalars (k := m)
  have hm : (m : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    change ((m : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  exact hJ.of_le hm

private theorem pulledPotential_contDiffAt
    (ω₀ : KahlerForm n M) (G φ : M → ℝ)
    (hG : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G)
    (x : M) (frame : C3RefinedTraceNormalCoordinateFrame ω₀ φ x) :
    ContDiffAt ℝ ∞ (c3RefinedTracePulledPotential G x frame.coord) frame.center := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  have hz : frame.coord frame.center ∈ e.target :=
    frame.in_chart ⟨frame.center, frame.center_mem, rfl⟩
  have hcoord := frame_coord_smooth_at ω₀ φ x frame
  have hsymm : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ e.symm (frame.coord frame.center) := by
    exact (contMDiffOn_extChartAt_symm
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz)
  have hGchartMD : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (G ∘ e.symm) (frame.coord frame.center) := by
    exact (hG (e.symm (frame.coord frame.center))).comp_of_eq hsymm rfl
  have hGchart : ContDiffAt ℝ ∞ (G ∘ e.symm) (frame.coord frame.center) :=
    (contMDiffAt_iff_contDiffAt).mp hGchartMD
  have hcomp := hGchart.comp frame.center hcoord
  have hcomplex := Complex.ofRealCLM.contDiff.contDiffAt.comp frame.center hcomp
  change ContDiffAt ℝ ∞
    (fun w ↦ ((G ((chartAt (EuclideanSpace ℂ (Fin n)) x).symm (frame.coord w)) : ℝ) : ℂ))
    frame.center
  exact hcomplex

private theorem pulledReferenceMetric_entry_contDiffAt
    (ω₀ : KahlerForm n M) (φ : M → ℝ) (x : M)
    (frame : C3RefinedTraceNormalCoordinateFrame ω₀ φ x) (i j : Fin n) :
    ContDiffAt ℝ ∞ (fun w ↦ c3RefinedTracePulledReferenceMetric ω₀ x frame.coord w i j)
      frame.center := by
  let J := fun w ↦ EuclideanSpace.clmMatrix (fderiv ℂ frame.coord w)
  have hcoord := frame_coord_smooth_at ω₀ φ x frame
  have hJ (a b : Fin n) : ContDiffAt ℝ ∞ (fun w ↦ J w a b) frame.center := by
    simpa [J] using frame_jacobian_entry_contDiffAt ω₀ φ x frame a b
  have hz : frame.coord frame.center ∈
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target :=
    frame.in_chart ⟨frame.center, frame.center_mem, rfl⟩
  have hbase (a b : Fin n) : ContDiffAt ℝ ∞
      (fun z ↦ ω₀.metricInChart x z a b) (frame.coord frame.center) :=
    (ω₀.contDiffOn_metricInChart x a b).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz)
  have hmetric (a b : Fin n) : ContDiffAt ℝ ∞
      (fun w ↦ ω₀.metricInChart x (frame.coord w) a b) frame.center :=
    (hbase a b).comp frame.center hcoord
  have hJstar (a b : Fin n) : ContDiffAt ℝ ∞
      (fun w ↦ star (J w a b)) frame.center := by
    have hc := Complex.conjCLE.contDiff.contDiffAt.comp frame.center (hJ a b)
    simpa [Function.comp_def, Complex.star_def, Complex.conjCLE_apply] using hc
  change ContDiffAt ℝ ∞ (fun w ↦
    ((J w).transpose * ω₀.metricInChart x (frame.coord w) * (J w).map star) i j)
    frame.center
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  fun_prop (disch := assumption)

open Filter Topology in
private theorem pulledPerturbedMetric_entry_contDiffAt
    (ω₀ : KahlerForm n M) (G φ : M → ℝ)
    (hsol : ω₀.SolvesMongeAmpere G φ) (x : M)
    (frame : C3RefinedTraceNormalCoordinateFrame ω₀ φ x) (i j : Fin n) :
    ContDiffAt ℝ ∞
      (fun w ↦ c3RefinedTracePulledPerturbedMetric ω₀ φ x frame.coord w i j)
      frame.center := by
  let ωφ := ω₀.perturb φ hsol.1
  let J := fun w ↦ EuclideanSpace.clmMatrix (fderiv ℂ frame.coord w)
  have hcoord := frame_coord_smooth_at ω₀ φ x frame
  have hJ (a b : Fin n) : ContDiffAt ℝ ∞ (fun w ↦ J w a b) frame.center := by
    simpa [J] using frame_jacobian_entry_contDiffAt ω₀ φ x frame a b
  have hz : frame.coord frame.center ∈
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target :=
    frame.in_chart ⟨frame.center, frame.center_mem, rfl⟩
  have hbase (a b : Fin n) : ContDiffAt ℝ ∞
      (fun z ↦ ωφ.metricInChart x z a b) (frame.coord frame.center) :=
    (ωφ.contDiffOn_metricInChart x a b).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz)
  have hmetric (a b : Fin n) : ContDiffAt ℝ ∞
      (fun w ↦ ωφ.metricInChart x (frame.coord w) a b) frame.center :=
    (hbase a b).comp frame.center hcoord
  have hJstar (a b : Fin n) : ContDiffAt ℝ ∞
      (fun w ↦ star (J w a b)) frame.center := by
    have hc := Complex.conjCLE.contDiff.contDiffAt.comp frame.center (hJ a b)
    simpa [Function.comp_def, Complex.star_def, Complex.conjCLE_apply] using hc
  have hcomp : ContDiffAt ℝ ∞ (fun w ↦
      ((J w).transpose * ωφ.metricInChart x (frame.coord w) * (J w).map star) i j)
      frame.center := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    fun_prop (disch := assumption)
  have hevent : (fun w ↦
      c3RefinedTracePulledPerturbedMetric ω₀ φ x frame.coord w i j) =ᶠ[𝓝 frame.center]
      (fun w ↦ ((J w).transpose * ωφ.metricInChart x (frame.coord w) *
        (J w).map star) i j) := by
    filter_upwards [frame.open_domain.mem_nhds frame.center_mem] with w hw
    have hwchart : frame.coord w ∈
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target :=
      frame.in_chart ⟨w, hw, rfl⟩
    have hmetric := ω₀.metricInChart_perturb hsol.1 x hwchart
    simp only [c3RefinedTracePulledPerturbedMetric, J, ωφ]
    rw [← hmetric]
  exact hcomp.congr_of_eventuallyEq hevent

private theorem hermitian_det_eq_ofReal_re (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) : A.det = (RCLike.re A.det : ℂ) := by
  have hstar : star A.det = A.det := by
    calc
      star A.det = (Matrix.conjTranspose A).det := (Matrix.det_conjTranspose A).symm
      _ = A.det := congrArg Matrix.det hA.eq
  have him := congrArg Complex.im hstar
  have him' : -A.det.im = A.det.im := by simpa using him
  have himzero : A.det.im = 0 := by linarith
  apply Complex.ext
  · rfl
  · simp [himzero]

open scoped ComplexOrder MatrixOrder in
private theorem pulledDeterminantEquation
    (ω₀ : KahlerForm n M) (G φ : M → ℝ)
    (hsol : ω₀.SolvesMongeAmpere G φ) (x : M)
    (frame : C3RefinedTraceNormalCoordinateFrame ω₀ φ x)
    (w : EuclideanSpace ℂ (Fin n)) (hw : w ∈ frame.domain) :
    (c3RefinedTracePulledPerturbedMetric ω₀ φ x frame.coord w).det =
      Complex.exp (c3RefinedTracePulledPotential G x frame.coord w) *
        (c3RefinedTracePulledReferenceMetric ω₀ x frame.coord w).det := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let z := frame.coord w
  let y := e.symm z
  let J := EuclideanSpace.clmMatrix (fderiv ℂ frame.coord w)
  let A := ω₀.metricInChart x z
  let B := A + complexHessian (φ ∘ e.symm) z
  let ωφ := ω₀.perturb φ hsol.1
  have hz : z ∈ e.target := frame.in_chart ⟨w, hw, rfl⟩
  have hy : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source := by
    have hys : y ∈ e.source := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).map_target hz
    rw [← extChartAt_source (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))]
    exact hys
  have hma := (hsol.2 y).symm.trans (ω₀.mongeAmpere_eq_inChart hsol.1.1 x hy)
  have hright : e (e.symm z) = z := e.right_inv hz
  rw [hright] at hma
  have hratio : Real.exp (G y) = RCLike.re B.det / RCLike.re A.det := by
    simpa [e, z, y, A, B] using hma
  have hApos : A.PosDef := ω₀.posDef_metricInChart x hz
  have hBmetric : ωφ.metricInChart x z = B := by
    dsimp [B, A, ωφ]
    rw [ω₀.metricInChart_perturb hsol.1 x hz]
  have hBpos : B.PosDef := by rw [← hBmetric]; exact ωφ.posDef_metricInChart x hz
  have hAreal := hermitian_det_eq_ofReal_re A hApos.isHermitian
  have hBreal := hermitian_det_eq_ofReal_re B hBpos.isHermitian
  have hreal : Real.exp (G y) * RCLike.re A.det = RCLike.re B.det := by
    rw [hratio]
    exact div_mul_cancel₀ _ (ne_of_gt (RCLike.pos_iff.mp hApos.det_pos).1)
  have hbase : B.det = (Real.exp (G y) : ℂ) * A.det := by
    rw [hBreal, hAreal]
    exact_mod_cast hreal.symm
  have hJdet : (J.transpose).det = J.det := Matrix.det_transpose J
  have hJstar : ((J.map star).det) = star J.det :=
    ((starRingEnd ℂ).map_det J).symm
  change (J.transpose * B * J.map star).det =
    Complex.exp (G y : ℂ) * (J.transpose * A * J.map star).det
  rw [Matrix.det_mul, Matrix.det_mul, hJdet, hJstar, hbase]
  rw [← Complex.ofReal_exp]
  simp only [Matrix.det_mul, hJdet, hJstar]
  ring

open scoped ComplexOrder MatrixOrder in
private theorem pulledReferenceMetric_hermitian
    (ω₀ : KahlerForm n M) (φ : M → ℝ) (x : M)
    (frame : C3RefinedTraceNormalCoordinateFrame ω₀ φ x)
    (w : EuclideanSpace ℂ (Fin n)) (hw : w ∈ frame.domain) :
    (c3RefinedTracePulledReferenceMetric ω₀ x frame.coord w).IsHermitian := by
  have hz : frame.coord w ∈
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := frame.in_chart ⟨w, hw, rfl⟩
  have hG : (ω₀.metricInChart x (frame.coord w)).PosDef := ω₀.posDef_metricInChart x hz
  let J := EuclideanSpace.clmMatrix (fderiv ℂ frame.coord w)
  have h := Matrix.isHermitian_mul_mul_conjTranspose (B := J.transpose) hG.isHermitian
  simpa [c3RefinedTracePulledReferenceMetric, J, Matrix.conjTranspose,
    Matrix.transpose_map] using h

open scoped ComplexOrder MatrixOrder in
private theorem pulledPerturbedMetric_hermitian
    (ω₀ : KahlerForm n M) (G φ : M → ℝ)
    (hsol : ω₀.SolvesMongeAmpere G φ) (x : M)
    (frame : C3RefinedTraceNormalCoordinateFrame ω₀ φ x)
    (w : EuclideanSpace ℂ (Fin n)) (hw : w ∈ frame.domain) :
    (c3RefinedTracePulledPerturbedMetric ω₀ φ x frame.coord w).IsHermitian := by
  have hz : frame.coord w ∈
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := frame.in_chart ⟨w, hw, rfl⟩
  let ωφ := ω₀.perturb φ hsol.1
  have hG : (ωφ.metricInChart x (frame.coord w)).PosDef := ωφ.posDef_metricInChart x hz
  let J := EuclideanSpace.clmMatrix (fderiv ℂ frame.coord w)
  have h := Matrix.isHermitian_mul_mul_conjTranspose (B := J.transpose) hG.isHermitian
  have hmetric : ωφ.metricInChart x (frame.coord w) =
      ω₀.metricInChart x (frame.coord w) + complexHessian
        (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) (frame.coord w) := by
    exact ω₀.metricInChart_perturb hsol.1 x hz
  simpa [c3RefinedTracePulledPerturbedMetric, J, Matrix.conjTranspose,
    Matrix.transpose_map, ωφ, hmetric] using h

private noncomputable abbrev normalFrameWirtinger (s : ℂ)
    (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n) : ℂ :=
  (fderiv ℝ f z (EuclideanSpace.single j 1) +
    s * fderiv ℝ f z (Complex.I • EuclideanSpace.single j 1)) / 2

private noncomputable def normalFrameZ (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n) : ℂ :=
  (fderiv ℝ f z (EuclideanSpace.single j 1) -
    Complex.I * fderiv ℝ f z (Complex.I • EuclideanSpace.single j 1)) / 2

private noncomputable def normalFrameBar (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n) : ℂ :=
  (fderiv ℝ f z (EuclideanSpace.single j 1) +
    Complex.I * fderiv ℝ f z (Complex.I • EuclideanSpace.single j 1)) / 2

private theorem normalFrameWirtingerFDeriv (s : ℂ)
    (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (hf : ContDiffAt ℝ 2 f z)
    (j : Fin n) (v : EuclideanSpace ℂ (Fin n)) :
    fderiv ℝ (fun w ↦ normalFrameWirtinger s f w j) z v =
      (fderiv ℝ (fderiv ℝ f) z v (EuclideanSpace.single j 1) +
        s * fderiv ℝ (fderiv ℝ f) z v
          (Complex.I • EuclideanSpace.single j 1)) / 2 := by
  let e : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j 1
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have he : DifferentiableAt ℝ (fun w ↦ fderiv ℝ f w e) z :=
    hfd.clm_apply (differentiableAt_const _)
  have hie : DifferentiableAt ℝ (fun w ↦ fderiv ℝ f w (Complex.I • e)) z :=
    hfd.clm_apply (differentiableAt_const _)
  have h_e (u : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ fderiv ℝ f w e) z u = fderiv ℝ (fderiv ℝ f) z u e := by
    rw [fderiv_clm_apply hfd (differentiableAt_const _)]
    simp
  have h_ie (u : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ fderiv ℝ f w (Complex.I • e)) z u =
        fderiv ℝ (fderiv ℝ f) z u (Complex.I • e) := by
    rw [fderiv_clm_apply hfd (differentiableAt_const _)]
    simp
  have hsum : DifferentiableAt ℝ
      (fun w ↦ fderiv ℝ f w e + s * fderiv ℝ f w (Complex.I • e)) z :=
    he.add (hie.const_mul s)
  have hfun : (fun w ↦ normalFrameWirtinger s f w j) =
      fun w ↦ (2 : ℂ)⁻¹ * (fderiv ℝ f w e + s * fderiv ℝ f w (Complex.I • e)) := by
    funext w
    change (fderiv ℝ f w (EuclideanSpace.single j 1) +
      s * fderiv ℝ f w (Complex.I • EuclideanSpace.single j 1)) / 2 =
      (2 : ℂ)⁻¹ * (fderiv ℝ f w e + s * fderiv ℝ f w (Complex.I • e))
    ring
  rw [hfun, fderiv_const_mul hsum, fderiv_fun_add he (hie.const_mul s),
    fderiv_const_mul hie]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [h_e v, h_ie v]
  simp only [div_eq_mul_inv]
  ring

private theorem normalFrameWirtingerCommute (s t : ℂ)
    (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (hf : ContDiffAt ℝ 2 f z)
    (p q : Fin n) :
    normalFrameWirtinger s (fun w ↦ normalFrameWirtinger t f w q) z p =
      normalFrameWirtinger t (fun w ↦ normalFrameWirtinger s f w p) z q := by
  have hs : IsSymmSndFDerivAt ℝ f z :=
    hf.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  change (fderiv ℝ (fun w ↦ normalFrameWirtinger t f w q) z
      (EuclideanSpace.single p 1) +
    s * fderiv ℝ (fun w ↦ normalFrameWirtinger t f w q) z
      (Complex.I • EuclideanSpace.single p 1)) / 2 =
    (fderiv ℝ (fun w ↦ normalFrameWirtinger s f w p) z (EuclideanSpace.single q 1) +
      t * fderiv ℝ (fun w ↦ normalFrameWirtinger s f w p) z
        (Complex.I • EuclideanSpace.single q 1)) / 2
  rw [normalFrameWirtingerFDeriv t f z hf q (EuclideanSpace.single p 1),
    normalFrameWirtingerFDeriv t f z hf q (Complex.I • EuclideanSpace.single p 1),
    normalFrameWirtingerFDeriv s f z hf p (EuclideanSpace.single q 1),
    normalFrameWirtingerFDeriv s f z hf p (Complex.I • EuclideanSpace.single q 1)]
  have h₁ := hs (EuclideanSpace.single p 1) (EuclideanSpace.single q 1)
  have h₂ := hs (EuclideanSpace.single p 1) (Complex.I • EuclideanSpace.single q 1)
  have h₃ := hs (Complex.I • EuclideanSpace.single p 1) (EuclideanSpace.single q 1)
  have h₄ := hs (Complex.I • EuclideanSpace.single p 1)
    (Complex.I • EuclideanSpace.single q 1)
  rw [h₁, h₂, h₃, h₄]
  ring

open Filter Topology in
private theorem normalFrameBarEventuallyEq (f g : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n)
    (h : f =ᶠ[nhds z] g) :
    (fun w ↦ normalFrameBar f w j) =ᶠ[nhds z] (fun w ↦ normalFrameBar g w j) := by
  have hfd : (fun w ↦ fderiv ℝ f w) =ᶠ[nhds z] (fun w ↦ fderiv ℝ g w) :=
    h.fderiv (𝕜 := ℝ)
  filter_upwards [hfd] with w hw
  unfold normalFrameBar
  rw [hw]

open Filter Topology in
private theorem normalFrameZEventuallyEq (f g : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n)
    (h : f =ᶠ[nhds z] g) :
    (fun w ↦ normalFrameZ f w j) =ᶠ[nhds z] (fun w ↦ normalFrameZ g w j) := by
  have hfd : (fun w ↦ fderiv ℝ f w) =ᶠ[nhds z] (fun w ↦ fderiv ℝ g w) :=
    h.fderiv (𝕜 := ℝ)
  filter_upwards [hfd] with w hw
  change (fderiv ℝ f w (EuclideanSpace.single j 1) -
    Complex.I * fderiv ℝ f w (Complex.I • EuclideanSpace.single j 1)) / 2 =
    (fderiv ℝ g w (EuclideanSpace.single j 1) -
      Complex.I * fderiv ℝ g w (Complex.I • EuclideanSpace.single j 1)) / 2
  rw [hw]

private theorem normalFrameBarStar (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n) (hf : DifferentiableAt ℝ f z) :
    normalFrameBar (fun w ↦ star (f w)) z j = star (normalFrameZ f z j) := by
  have hfd := fderiv_comp (𝕜 := ℝ) (f := f)
    (g := (Complex.conjCLE : ℂ → ℂ)) (x := z) Complex.conjCLE.differentiableAt hf
  have hfun : (fun w ↦ star (f w)) = Complex.conjCLE ∘ f := by
    funext w
    simp
  have hstar : fderiv ℝ (fun w ↦ star (f w)) z =
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ f z) := by
    rw [hfun]
    simpa only [Complex.conjCLE.fderiv] using hfd
  change (fderiv ℝ (fun w ↦ star (f w)) z (EuclideanSpace.single j 1) +
    Complex.I * fderiv ℝ (fun w ↦ star (f w)) z
      (Complex.I • EuclideanSpace.single j 1)) / 2 =
    star ((fderiv ℝ f z (EuclideanSpace.single j 1) -
      Complex.I * fderiv ℝ f z (Complex.I • EuclideanSpace.single j 1)) / 2)
  rw [hstar]
  simp only [ContinuousLinearMap.comp_apply]
  change (star ((fderiv ℝ f z) (EuclideanSpace.single j 1)) +
    Complex.I * star ((fderiv ℝ f z) (Complex.I • EuclideanSpace.single j 1))) / 2 = _
  simp [Complex.conj_I]

private theorem normalFrameBarCommuteZ (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (hf : ContDiffAt ℝ 2 f z)
    (p q : Fin n) :
    normalFrameBar (fun w ↦ normalFrameZ f w p) z q =
      normalFrameZ (fun w ↦ normalFrameBar f w q) z p := by
  have hcomm := normalFrameWirtingerCommute (-Complex.I) Complex.I f z hf p q
  have hz (A : EuclideanSpace ℂ (Fin n) → ℂ)
      (w : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
      normalFrameWirtinger (-Complex.I) A w j = normalFrameZ A w j := by
    change (fderiv ℝ A w (EuclideanSpace.single j 1) +
      (-Complex.I) * fderiv ℝ A w (Complex.I • EuclideanSpace.single j 1)) / 2 =
      (fderiv ℝ A w (EuclideanSpace.single j 1) -
        Complex.I * fderiv ℝ A w (Complex.I • EuclideanSpace.single j 1)) / 2
    ring
  have hb (A : EuclideanSpace ℂ (Fin n) → ℂ)
      (w : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
      normalFrameWirtinger Complex.I A w j = normalFrameBar A w j := rfl
  simpa only [hz, hb] using hcomm.symm

private theorem normalFrameMixedCommute (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (hf : ContDiffAt ℝ 2 f z)
    (p q : Fin n) :
    normalFrameZ (fun w ↦ normalFrameBar f w q) z p =
      normalFrameBar (fun w ↦ normalFrameZ f w p) z q :=
  (normalFrameBarCommuteZ f z hf p q).symm

open Filter Topology in
private theorem normalFrameMatrixMixedCommute
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hg : ∀ i j : Fin n, ContDiffAt ℝ 2 (fun w ↦ g w i j) z)
    (hHerm : ∀ᶠ w in 𝓝 z, (g w).IsHermitian)
    (hK : ∀ᶠ w in 𝓝 z, ∀ i j k : Fin n,
      normalFrameZ (fun v ↦ g v j k) w i = normalFrameZ (fun v ↦ g v i k) w j)
    (p j : Fin n) :
    normalFrameZ (fun w ↦ normalFrameBar (fun v ↦ g v j j) w p) z p =
      normalFrameZ (fun w ↦ normalFrameBar (fun v ↦ g v p p) w j) z j := by
  have hK₁ : (fun w ↦ normalFrameZ (fun v ↦ g v j j) w p) =ᶠ[𝓝 z]
      (fun w ↦ normalFrameZ (fun v ↦ g v p j) w j) := by
    filter_upwards [hK] with w hw
    exact hw p j j
  have hK₂ : (fun w ↦ normalFrameZ (fun v ↦ g v j p) w p) =ᶠ[𝓝 z]
      (fun w ↦ normalFrameZ (fun v ↦ g v p p) w j) := by
    filter_upwards [hK] with w hw
    exact hw p j p
  have hHerm₁ : (fun w ↦ star (g w j p)) =ᶠ[𝓝 z] (fun w ↦ g w p j) := by
    filter_upwards [hHerm] with w hw
    exact hw.apply p j
  have hHerm₂ : (fun w ↦ star (g w p p)) =ᶠ[𝓝 z] (fun w ↦ g w p p) := by
    filter_upwards [hHerm] with w hw
    exact hw.apply p p
  have hnear₁ : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ 2 (fun v ↦ g v j p) w :=
    (hg j p).eventually (by norm_num)
  have hnear₂ : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ 2 (fun v ↦ g v p p) w :=
    (hg p p).eventually (by norm_num)
  have hbarConj :
      (fun w ↦ normalFrameBar (fun v ↦ star (g v j p)) w p) =ᶠ[𝓝 z]
      (fun w ↦ normalFrameBar (fun v ↦ star (g v p p)) w j) := by
    filter_upwards [hK₂, hnear₁, hnear₂] with w hw hnear₁' hnear₂'
    calc
      normalFrameBar (fun v ↦ star (g v j p)) w p =
          star (normalFrameZ (fun v ↦ g v j p) w p) :=
            normalFrameBarStar _ _ _ (hnear₁'.differentiableAt (by norm_num))
      _ = star (normalFrameZ (fun v ↦ g v p p) w j) := congrArg star hw
      _ = normalFrameBar (fun v ↦ star (g v p p)) w j :=
            (normalFrameBarStar _ _ _ (hnear₂'.differentiableAt (by norm_num))).symm
  have hbar : (fun w ↦ normalFrameBar (fun v ↦ g v p j) w p) =ᶠ[𝓝 z]
      (fun w ↦ normalFrameBar (fun v ↦ g v p p) w j) := by
    have hleft := normalFrameBarEventuallyEq
      (fun w ↦ star (g w j p)) (fun w ↦ g w p j) z p hHerm₁
    have hright := normalFrameBarEventuallyEq
      (fun w ↦ star (g w p p)) (fun w ↦ g w p p) z j hHerm₂
    exact hleft.symm.trans (hbarConj.trans hright)
  have hfirst := normalFrameBarEventuallyEq
    (fun w ↦ normalFrameZ (fun v ↦ g v j j) w p)
    (fun w ↦ normalFrameZ (fun v ↦ g v p j) w j) z p hK₁
  have hlast := normalFrameZEventuallyEq
    (fun w ↦ normalFrameBar (fun v ↦ g v p j) w p)
    (fun w ↦ normalFrameBar (fun v ↦ g v p p) w j) z j hbar
  have hcomm₁ := normalFrameMixedCommute (fun w ↦ g w j j) z (hg j j) p p
  have hcomm₂ := normalFrameMixedCommute (fun w ↦ g w p j) z (hg p j) j p
  calc
    normalFrameZ (fun w ↦ normalFrameBar (fun v ↦ g v j j) w p) z p =
        normalFrameBar (fun w ↦ normalFrameZ (fun v ↦ g v j j) w p) z p := hcomm₁
    _ = normalFrameBar (fun w ↦ normalFrameZ (fun v ↦ g v p j) w j) z p := hfirst.self_of_nhds
    _ = normalFrameZ (fun w ↦ normalFrameBar (fun v ↦ g v p j) w p) z j := hcomm₂.symm
    _ = normalFrameZ (fun w ↦ normalFrameBar (fun v ↦ g v p p) w j) z j := hlast.self_of_nhds

open Filter Topology in
private theorem normalFrameActualMetricMixedDerivative
    (ω₀ : KahlerForm n M) (G φ : M → ℝ)
    (hsol : ω₀.SolvesMongeAmpere G φ) (x : M)
    (frame : C3RefinedTraceNormalCoordinateFrame ω₀ φ x)
    (hsmooth : ∀ i j, ContDiffAt ℝ ∞
      (fun w ↦ c3RefinedTracePulledPerturbedMetric ω₀ φ x frame.coord w i j) frame.center)
    (hHermitian : ∀ᶠ w in 𝓝 frame.center,
      (c3RefinedTracePulledPerturbedMetric ω₀ φ x frame.coord w).IsHermitian) :
    ∀ p j : Fin n,
      c3RefinedTraceMatrixMixedPartial
        (c3RefinedTracePulledPerturbedMetric ω₀ φ x frame.coord)
        frame.center p p j j =
      c3RefinedTraceMatrixMixedPartial
        (c3RefinedTracePulledPerturbedMetric ω₀ φ x frame.coord)
        frame.center j j p p := by
  let g := c3RefinedTracePulledPerturbedMetric ω₀ φ x frame.coord
  let ωφ := ω₀.perturb φ hsol.1
  have hgInf : ∀ i j, ContDiffAt ℝ ∞ (fun w ↦ g w i j) frame.center := by
    simpa [g] using hsmooth
  have hle : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  have hg2 : ∀ i j, ContDiffAt ℝ 2 (fun w ↦ g w i j) frame.center := by
    intro i j
    exact (hgInf i j).of_le hle
  have hHerm : ∀ᶠ w in 𝓝 frame.center, (g w).IsHermitian := by
    simpa [g] using hHermitian
  have hψC2 : ContDiffOn ℝ 2 frame.coord frame.domain := by
    intro w hw
    have hC : ContDiffAt ℂ ∞ frame.coord w :=
      frame.holomorphic.contDiffAt (frame.open_domain.mem_nhds hw)
    have hC2 : ContDiffAt ℂ 2 frame.coord w := hC.of_le hle
    have hR2 : ContDiffAt ℝ 2 frame.coord w :=
      contDiffAt_restrictScalars hC2
    exact hR2.contDiffWithinAt
  have hψhol : DifferentiableOn ℂ frame.coord frame.domain := by
    intro w hw
    have hC : ContDiffAt ℂ ∞ frame.coord w :=
      frame.holomorphic.contDiffAt (frame.open_domain.mem_nhds hw)
    exact (hC.differentiableAt (by norm_num)).differentiableWithinAt
  have hmetric (w : EuclideanSpace ℂ (Fin n)) (hw : w ∈ frame.domain) :
      g w = pulledBackMetricInChart ωφ x frame.coord w := by
    let J := EuclideanSpace.clmMatrix (fderiv ℂ frame.coord w)
    have hz : frame.coord w ∈
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target :=
      frame.in_chart ⟨w, hw, rfl⟩
    have hm := ω₀.metricInChart_perturb hsol.1 x hz
    change J.transpose * (ω₀.metricInChart x (frame.coord w) +
        complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
          (frame.coord w)) * J.map star =
      J.transpose * ωφ.metricInChart x (frame.coord w) * J.map star
    rw [← hm]
  have hK : ∀ᶠ w in 𝓝 frame.center, ∀ i j k : Fin n,
      normalFrameZ (fun v ↦ g v j k) w i = normalFrameZ (fun v ↦ g v i k) w j := by
    filter_upwards [frame.open_domain.mem_nhds frame.center_mem] with w hw
    intro i j k
    have hleft : (fun v ↦ g v j k) =ᶠ[𝓝 w]
        (fun v ↦ pulledBackMetricInChart ωφ x frame.coord v j k) := by
      filter_upwards [frame.open_domain.mem_nhds hw] with v hv
      exact congrArg (fun A : Matrix (Fin n) (Fin n) ℂ ↦ A j k) (hmetric v hv)
    have hright : (fun v ↦ g v i k) =ᶠ[𝓝 w]
        (fun v ↦ pulledBackMetricInChart ωφ x frame.coord v i k) := by
      filter_upwards [frame.open_domain.mem_nhds hw] with v hv
      exact congrArg (fun A : Matrix (Fin n) (Fin n) ℂ ↦ A i k) (hmetric v hv)
    have hleftZ := (normalFrameZEventuallyEq _ _ w i hleft).self_of_nhds
    have hrightZ := (normalFrameZEventuallyEq _ _ w j hright).self_of_nhds
    have hchart : Set.MapsTo frame.coord frame.domain
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
      intro v hv
      exact frame.in_chart ⟨v, hv, rfl⟩
    have hKpb := pulledBackMetricInChart_first_derivative_symmetric
      ωφ x frame.coord frame.domain frame.open_domain hψC2 hψhol hchart hw i j k
    calc
      normalFrameZ (fun v ↦ g v j k) w i =
          normalFrameZ (fun v ↦ pulledBackMetricInChart ωφ x frame.coord v j k) w i := hleftZ
      _ = normalFrameZ (fun v ↦ pulledBackMetricInChart ωφ x frame.coord v i k) w j := hKpb
      _ = normalFrameZ (fun v ↦ g v i k) w j := hrightZ.symm
  intro p j
  have hmix := normalFrameMatrixMixedCommute g frame.center hg2 hHerm hK p j
  change normalFrameZ (fun w ↦ normalFrameBar (fun v ↦ g v j j) w p) frame.center p =
    normalFrameZ (fun w ↦ normalFrameBar (fun v ↦ g v p p) w j) frame.center j
  exact hmix

open Filter Topology in
private theorem normalFrameActualEquationInterchange
    (ω₀ : KahlerForm n M) (G φ : M → ℝ)
    (hsol : ω₀.SolvesMongeAmpere G φ) (x : M)
    (frame : C3RefinedTraceNormalCoordinateFrame ω₀ φ x)
    (hsmooth : ∀ i j, ContDiffAt ℝ ∞
      (fun w ↦ c3RefinedTracePulledPerturbedMetric ω₀ φ x frame.coord w i j)
      frame.center)
    (hHermitian : ∀ᶠ w in 𝓝 frame.center,
      (c3RefinedTracePulledPerturbedMetric ω₀ φ x frame.coord w).IsHermitian) :
    ∀ p j : Fin n,
      c3RefinedTraceMatrixMixedPartial
        (c3RefinedTracePulledPerturbedMetric ω₀ φ x frame.coord)
        frame.center p p j j =
      c3RefinedTraceMatrixMixedPartial
        (c3RefinedTracePulledPerturbedMetric ω₀ φ x frame.coord)
        frame.center j j p p := by
  exact normalFrameActualMetricMixedDerivative
    ω₀ G φ hsol x frame hsmooth hHermitian

open Filter Topology in
private theorem normalFrame_actualMetricInterchange
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₀ : KahlerForm n M) (G φ : M → ℝ)
    (hsol : ω₀.SolvesMongeAmpere G φ) (x : M)
    (frame : C3RefinedTraceNormalCoordinateFrame ω₀ φ x) :
    ∀ p j : Fin n,
      c3RefinedTraceMatrixMixedPartial
        (c3RefinedTracePulledPerturbedMetric ω₀ φ x frame.coord)
        frame.center p p j j =
      c3RefinedTraceMatrixMixedPartial
        (c3RefinedTracePulledPerturbedMetric ω₀ φ x frame.coord)
        frame.center j j p p := by
  have hsmooth : ∀ i j, ContDiffAt ℝ ∞
      (fun w ↦ c3RefinedTracePulledPerturbedMetric ω₀ φ x frame.coord w i j)
      frame.center := fun i j =>
        pulledPerturbedMetric_entry_contDiffAt ω₀ G φ hsol x frame i j
  have hHermitian : ∀ᶠ w in 𝓝 frame.center,
      (c3RefinedTracePulledPerturbedMetric ω₀ φ x frame.coord w).IsHermitian := by
    filter_upwards [frame.open_domain.mem_nhds frame.center_mem] with w hw
    exact pulledPerturbedMetric_hermitian ω₀ G φ hsol x frame w hw
  exact normalFrameActualEquationInterchange ω₀ G φ hsol x frame hsmooth hHermitian

theorem c3RefinedTrace_normalFrame_equation_and_kahler
    (ω₀ : KahlerForm n M) (G φ : M → ℝ)
    (hG : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G)
    (hsol : ω₀.SolvesMongeAmpere G φ) (x : M)
    (frame : C3RefinedTraceNormalCoordinateFrame ω₀ φ x) :
    let g := c3RefinedTracePulledReferenceMetric ω₀ x frame.coord
    let h := c3RefinedTracePulledPerturbedMetric ω₀ φ x frame.coord
    let H := c3RefinedTracePulledPotential G x frame.coord
    (∀ i j, ContDiffAt ℝ ∞ (fun w ↦ g w i j) frame.center) ∧
    (∀ i j, ContDiffAt ℝ ∞ (fun w ↦ h w i j) frame.center) ∧
    ContDiffAt ℝ ∞ H frame.center ∧
    (∃ U : Set (EuclideanSpace ℂ (Fin n)), IsOpen U ∧ frame.center ∈ U ∧
      ∀ w ∈ U, g w = (g w).conjTranspose ∧
        h w = (h w).conjTranspose ∧
        (h w).det = Complex.exp (H w) * (g w).det) ∧
    (∀ p j : Fin n, c3RefinedTraceMatrixMixedPartial h frame.center p p j j =
      c3RefinedTraceMatrixMixedPartial h frame.center j j p p) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    exact pulledReferenceMetric_entry_contDiffAt ω₀ φ x frame i j
  · intro i j
    exact pulledPerturbedMetric_entry_contDiffAt ω₀ G φ hsol x frame i j
  · exact pulledPotential_contDiffAt ω₀ G φ hG x frame
  · refine ⟨?_, ?_⟩
    · refine ⟨frame.domain, frame.open_domain, frame.center_mem, ?_⟩
      intro w hw
      refine ⟨?_, ?_, ?_⟩
      · exact (pulledReferenceMetric_hermitian ω₀ φ x frame w hw).eq.symm
      · exact (pulledPerturbedMetric_hermitian ω₀ G φ hsol x frame w hw).eq.symm
      · exact pulledDeterminantEquation ω₀ G φ hsol x frame w hw
    · intro p j
      exact normalFrame_actualMetricInterchange ω₀ G φ hsol x frame p j

end KahlerForm
