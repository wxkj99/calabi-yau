module

public import CalabiYau.Geometry.Kahler.Laplacian
public import CalabiYau.Geometry.Complex.Forms.OneOne
public import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.NormalFrameJets

import CalabiYau.MongeAmpere.Estimates.C2.NormalFrameLaplacian
import CalabiYau.MongeAmpere.Estimates.C2.RelativeTraceRegularity
import CalabiYau.MongeAmpere.Estimates.C2.InverseMetricJet
import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.SecondDerivativeSymmetry
import CalabiYau.MongeAmpere.Estimates.C2.ReferenceCurvatureTransport
import CalabiYau.MongeAmpere.Estimates.C2.ReferenceCurvatureTransport.PullbackConnectionGerm
import CalabiYau.MongeAmpere.Estimates.C2.HermitianFirstJet
import CalabiYau.MongeAmpere.Estimates.C2.RelativeTraceSecondJet
import CalabiYau.MongeAmpere.Estimates.C2.RelativeTraceGerm

/-!
# Laplacian of the unlogged relative trace

This theorem isolates the second-order part of the normal-coordinate calculation.  Put
`u = tr_{ω₀} ω₁`.  In the normal frame, `u` is the trace of the varying coefficient matrix because
the reference matrix is the identity.  Its complex Hessian has two contributions: the mixed second
jets of the varying metric, and the second jet of the inverse reference metric.  The latter is the
signed reference bisectional-curvature contraction.

Unlike the logarithmic expansion, there is no negative square term here.  That term appears only
when the scalar chain rule is applied to `log u`; it is kept separate so that this lemma
contains just the geometric Hessian of the trace.  The denominators `λₚ` come from tracing the
Hessian against the varying metric at the center, while `λⱼ` weights the `j`-th diagonal component
of the varying metric in the curvature term.

The curvature sign is fixed by `chartCurvature`: in reference normal coordinates the curvature
entry is `-∂ₚ∂̄p g⁰_{j j̄}`, and it enters `Δ_{ω₁}u` with the plus sign shown.  This is the same
signed bisectional entry used in the uniform lower-bound theorem.

Degenerate-case audit: for `n = 0` both sums are empty and the Laplacian is zero; for `n = 1` the
formula is the single second jet divided by `λ` plus the reference curvature weighted by `λ/λ`;
on a flat one-dimensional torus with constant metrics all terms vanish.  The pullback convention
remains `J.transpose * G * J.map star` (the `J = i` test in dimension one fixes the coefficient
order).
-/

@[expose] public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

open Filter Topology in
open scoped Matrix.Norms.Elementwise in
private theorem normalized_matrix_inverse_first_jet_zero {n : ℕ}
    {G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    (z : EuclideanSpace ℂ (Fin n))
    (hG : ∀ a b, ContDiffAt ℝ 2 (fun w ↦ G w a b) z)
    (hId : G z = 1) (hFirst : fderiv ℝ G z = 0) :
    fderiv ℝ (fun w ↦ (G w)⁻¹) z = 0 := by
  classical
  have hGmat : ContDiffAt ℝ 2 G z := by
    change ContDiffAt ℝ 2 (fun w i j ↦ G w i j) z
    rw [contDiffAt_pi]
    intro i
    rw [contDiffAt_pi]
    intro j
    exact hG i j
  have hunit : IsUnit (G z).det := by simp [hId]
  have hle : (2 : ℕ∞) ≤ ⊤ := le_top
  have hinv : ContDiffAt ℝ 2 (fun B : Matrix (Fin n) (Fin n) ℂ ↦ B⁻¹) (G z) :=
    (Matrix.contDiffAt_inv hunit).of_le (WithTop.coe_le_coe.mpr hle)
  have hinvG : ContDiffAt ℝ 2 (fun w ↦ (G w)⁻¹) z := hinv.comp z hGmat
  have hdetCont : ContinuousAt (fun w ↦ (G w).det) z := by
    have hd : ContDiffAt ℝ 2 (fun w ↦ (G w).det) z := by
      simp_rw [Matrix.det_apply]
      fun_prop (disch := assumption)
    exact hd.continuousAt
  have hne : ∀ᶠ w in 𝓝 z, (G w).det ≠ 0 := hdetCont.eventually_ne (by simp [hId])
  have hmul (a b : Fin n) :
      (fun w ↦ ∑ l : Fin n, G w a l * (G w)⁻¹ l b) =ᶠ[𝓝 z]
        fun _ ↦ (1 : Matrix (Fin n) (Fin n) ℂ) a b := by
    filter_upwards [hne] with w hw
    have hu : IsUnit (G w).det := isUnit_iff_ne_zero.mpr hw
    simpa only [Matrix.mul_apply] using congrArg (fun B : Matrix (Fin n) (Fin n) ℂ ↦ B a b)
      (Matrix.mul_nonsing_inv (G w) hu)
  have hentryFirst (a b : Fin n) (v : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ G w a b) z v = 0 := by
    have hGrow : ContDiffAt ℝ 2 (fun w ↦ G w a) z :=
      (contDiffAt_apply ℝ (Fin n → ℂ) a (G z)).comp z hGmat
    have hGrowDiff : DifferentiableAt ℝ (fun w ↦ G w a) z :=
      hGrow.differentiableAt (by norm_num)
    have hGdiff : DifferentiableAt ℝ G z := hGmat.differentiableAt (by norm_num)
    have hRowDer := fderiv_apply hGdiff a
    have hEntryDer := fderiv_apply hGrowDiff b
    calc
      fderiv ℝ (fun w ↦ G w a b) z v = (fderiv ℝ (fun w ↦ G w a) z v) b := by
        rw [hEntryDer]
        simp
      _ = (fderiv ℝ G z v) a b := by rw [hRowDer]; rfl
      _ = 0 := by simp [hFirst]
  ext v a b
  have hzero : fderiv ℝ
      (fun w ↦ ∑ l : Fin n, G w a l * (G w)⁻¹ l b) z v = 0 := by
    have hh := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L v)
      (hmul a b).fderiv_eq
    simpa using hh
  have hterms (l : Fin n) : DifferentiableAt ℝ (fun w ↦ G w a l) z :=
    (hG a l).differentiableAt (by norm_num)
  have hinvEntryCont (l : Fin n) :
      ContDiffAt ℝ 2 (fun w ↦ (G w)⁻¹ l b) z :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hinvG l) b
  have hinvEntry (l : Fin n) : DifferentiableAt ℝ (fun w ↦ (G w)⁻¹ l b) z :=
    (hinvEntryCont l).differentiableAt (by norm_num)
  let A : Fin n → EuclideanSpace ℂ (Fin n) → ℂ := fun l w ↦ G w a l
  let B : Fin n → EuclideanSpace ℂ (Fin n) → ℂ := fun l w ↦ (G w)⁻¹ l b
  have hfun : (fun w ↦ ∑ l : Fin n, G w a l * (G w)⁻¹ l b) =
      fun w ↦ ∑ l : Fin n, A l w * B l w := by
    funext w
    simp [A, B]
  have hzero' : fderiv ℝ (fun w ↦ ∑ l : Fin n, A l w * B l w) z v = 0 := by
    rw [← hfun]
    exact hzero
  have hterms' (l : Fin n) : DifferentiableAt ℝ (A l) z := hterms l
  have hinvEntry' (l : Fin n) : DifferentiableAt ℝ (B l) z := hinvEntry l
  have hsum := fderiv_fun_sum (u := Finset.univ)
    (fun l _ ↦ (hterms' l).mul (hinvEntry' l))
  have hh := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L v) hsum
  change (fderiv ℝ (fun y ↦ ∑ i, (A i * B i) y) z) v = 0 at hzero'
  rw [hh] at hzero'
  simp only [_root_.sum_apply] at hzero'
  have hprod (l : Fin n) :
      (fderiv ℝ (A l * B l) z) v =
        fderiv ℝ (A l) z v * B l z + A l z * fderiv ℝ (B l) z v := by
    have hAB : A l * B l = fun w ↦ A l w * B l w := by
      funext w
      simp [Pi.mul_apply]
    have hderivAB := congrArg (fun f : EuclideanSpace ℂ (Fin n) → ℂ =>
      (fderiv ℝ f z) v) hAB
    have h := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L v)
      (fderiv_fun_mul (hterms' l) (hinvEntry' l))
    calc
      _ = (fderiv ℝ (fun w ↦ A l w * B l w) z) v := hderivAB
      _ = A l z * fderiv ℝ (B l) z v + B l z * fderiv ℝ (A l) z v := by simpa using h
      _ = _ := by ring
  simp_rw [hprod] at hzero'
  have hsumInv :
      ∑ l : Fin n, G z a l * fderiv ℝ (fun w ↦ (G w)⁻¹ l b) z v = 0 := by
    simpa [hentryFirst, A, B] using hzero'
  have hInvEntryZero : fderiv ℝ (fun w ↦ (G w)⁻¹ a b) z v = 0 := by
    simp only [hId, Matrix.one_apply] at hsumInv
    classical
    rw [Finset.sum_eq_single a] at hsumInv
    · simpa using hsumInv
    · intro l hl hla
      simp [Ne.symm hla]
    · simp
  have hInvRowCont : ContDiffAt ℝ 2 (fun w ↦ (G w)⁻¹ a) z :=
    contDiffAt_pi.mp hinvG a
  have hInvRowDiff : DifferentiableAt ℝ (fun w ↦ (G w)⁻¹ a) z :=
    hInvRowCont.differentiableAt (by norm_num)
  have hInvMatDiff : DifferentiableAt ℝ (fun w ↦ (G w)⁻¹) z :=
    hinvG.differentiableAt (by norm_num)
  have hInvEntryDer := fderiv_apply hInvRowDiff b
  have hInvRowDer := fderiv_apply hInvMatDiff a
  have hInvEntryEq : fderiv ℝ (fun w ↦ (G w)⁻¹ a b) z v =
      (fderiv ℝ (fun w ↦ (G w)⁻¹) z v) a b := by
    calc
      fderiv ℝ (fun w ↦ (G w)⁻¹ a b) z v =
          (fderiv ℝ (fun w ↦ (G w)⁻¹ a) z v) b := by rw [hInvEntryDer]; simp
      _ = (fderiv ℝ (fun w ↦ (G w)⁻¹) z v) a b := by rw [hInvRowDer]; rfl
  calc
    (fderiv ℝ (fun w ↦ (G w)⁻¹) z v) a b =
        fderiv ℝ (fun w ↦ (G w)⁻¹ a b) z v := hInvEntryEq.symm
    _ = 0 := hInvEntryZero

open Filter Topology in
private theorem second_fderiv_scalar_mul_jet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : E → ℂ) (z : E)
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z)
    (v u : E) :
    fderiv ℝ (fderiv ℝ (fun w ↦ f w * g w)) z v u =
      f z * fderiv ℝ (fderiv ℝ g) z v u +
      fderiv ℝ f z v * fderiv ℝ g z u +
      fderiv ℝ f z u * fderiv ℝ g z v +
      g z * fderiv ℝ (fderiv ℝ f) z v u := by
  have hfc : DifferentiableAt ℝ f z := hf.differentiableAt (by norm_num)
  have hgc : DifferentiableAt ℝ g z := hg.differentiableAt (by norm_num)
  have hfdg : DifferentiableAt ℝ (fun w ↦ fderiv ℝ g w u) z := by
    have hc : ContDiffAt ℝ 1 (fderiv ℝ g) z := hg.fderiv_right (m := 1) (by norm_num)
    exact (hc.clm_apply contDiffAt_const).differentiableAt (by norm_num)
  have hfdf : DifferentiableAt ℝ (fun w ↦ fderiv ℝ f w u) z := by
    have hc : ContDiffAt ℝ 1 (fderiv ℝ f) z := hf.fderiv_right (m := 1) (by norm_num)
    exact (hc.clm_apply contDiffAt_const).differentiableAt (by norm_num)
  have hevent : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ f w ∧ DifferentiableAt ℝ g w := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with w hfw hgw
    exact ⟨hfw.differentiableAt (by norm_num), hgw.differentiableAt (by norm_num)⟩
  have hformula :
      (fun w ↦ fderiv ℝ (fun x ↦ f x * g x) w u) =ᶠ[𝓝 z]
      (fun w ↦ f w * fderiv ℝ g w u + g w * fderiv ℝ f w u) := by
    filter_upwards [hevent] with w hw
    have hmul := fderiv_fun_mul hw.1 hw.2
    simpa using congrArg (fun L : E →L[ℝ] ℂ ↦ L u) hmul
  have hformula' := hformula.fderiv_eq (𝕜 := ℝ) (x := z)
  have hmul1 : fderiv ℝ (fun w ↦ f w * fderiv ℝ g w u) z v =
      f z * fderiv ℝ (fun w ↦ fderiv ℝ g w u) z v +
      fderiv ℝ f z v * fderiv ℝ g z u := by
    rw [fderiv_fun_mul hfc hfdg]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    ring
  have hmul2 : fderiv ℝ (fun w ↦ g w * fderiv ℝ f w u) z v =
      g z * fderiv ℝ (fun w ↦ fderiv ℝ f w u) z v +
      fderiv ℝ g z v * fderiv ℝ f z u := by
    rw [fderiv_fun_mul hgc hfdf]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    ring
  have hprod : ContDiffAt ℝ 2 (fun w ↦ f w * g w) z := hf.mul hg
  have hprodC1 : ContDiffAt ℝ 1 (fderiv ℝ (fun w ↦ f w * g w)) z :=
    hprod.fderiv_right (m := 1) (by norm_num)
  have hLhs :
      fderiv ℝ (fderiv ℝ (fun w ↦ f w * g w)) z v u =
        fderiv ℝ (fun w ↦ fderiv ℝ (fun x ↦ f x * g x) w u) z v := by
    rw [fderiv_clm_apply (hprodC1.differentiableAt (by norm_num))
      (differentiableAt_const u)]
    simp
  have hformulaV := congrArg (fun L : E →L[ℝ] ℂ ↦ L v) hformula'
  have hsplit :
      fderiv ℝ (fun w ↦ f w * fderiv ℝ g w u + g w * fderiv ℝ f w u) z v =
        fderiv ℝ (fun w ↦ f w * fderiv ℝ g w u) z v +
          fderiv ℝ (fun w ↦ g w * fderiv ℝ f w u) z v := by
    have h := fderiv_fun_add (hfc.mul hfdg) (hgc.mul hfdf)
    exact congrArg (fun L : E →L[ℝ] ℂ ↦ L v) h
  rw [hsplit, hmul1, hmul2] at hformulaV
  have hevalg : fderiv ℝ (fun w ↦ fderiv ℝ g w u) z v =
      fderiv ℝ (fderiv ℝ g) z v u := by
    rw [fderiv_clm_apply (hg.fderiv_right (m := 1) (by norm_num) |>.differentiableAt (by norm_num))
      (differentiableAt_const u)]
    simp
  have hevalf : fderiv ℝ (fun w ↦ fderiv ℝ f w u) z v =
      fderiv ℝ (fderiv ℝ f) z v u := by
    rw [fderiv_clm_apply (hf.fderiv_right (m := 1) (by norm_num) |>.differentiableAt (by norm_num))
      (differentiableAt_const u)]
    simp
  rw [hevalg, hevalf] at hformulaV
  rw [hLhs]
  linear_combination hformulaV

private theorem relTrace_contDiffAt_normalFrame
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x) :
    ContDiffAt ℝ 2
      (fun z ↦ relTrace (ω₀ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm
        (F.map z))) (ω₁ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm
        (F.map z)))) F.center := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  have hrel := contDiffAt_relativeTrace_inChart ω₀ ω₁ x
  rw [← F.center_eq_chart_center] at hrel
  have hmap : ContDiffAt ℝ 2 F.map F.center := by
    have hle : (2 : ℕ∞ω) ≤ ∞ := by
      change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top
    exact (F.smooth_map.contDiffAt (F.isOpen_domain.mem_nhds F.center_mem)).of_le hle
  have hcomp := hrel.comp F.center hmap
  simpa [e, Function.comp_def] using hcomp

open scoped Matrix.Norms.Elementwise in
private theorem normalFrame_pulledBackMetric_contDiffAt_two
    (ω₀ ω₁ ωr : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x) :
    ContDiffAt ℝ 2 (pulledBackMetricInChart ωr x F.map) F.center := by
  let G := pulledBackMetricInChart ωr x F.map
  let H := ωr.metricInChart x
  have hH : ∀ a b, ContDiffAt ℝ ∞ (fun w ↦ H w a b) (F.map F.center) := by
    intro a b
    exact (ωr.contDiffOn_metricInChart x a b).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds (F.maps_into_chart F.center F.center_mem))
  have hdet : IsUnit (H (F.map F.center)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1
      (ωr.posDef_metricInChart x (F.maps_into_chart F.center F.center_mem)).isUnit
  have hjac : IsUnit (holomorphicJacobianMatrix F.map F.center).det :=
    isUnit_iff_ne_zero.mpr F.jacobian_det_ne_zero
  have hf : ContDiffOn ℝ 3 F.map F.domain :=
    F.smooth_map.of_le (WithTop.coe_le_coe.mpr le_top)
  have hjet := holomorphicJacobianJetAt_of_contDiffOn F.domain F.isOpen_domain
    F.map hf F.holomorphic_map F.center F.center_mem hjac
  have hC2 := (pullbackConnection_germ F.domain F.isOpen_domain F.map hf F.holomorphic_map
    G H F.center F.center_mem hH hjac hdet (fun _ _ ↦ rfl) hjet).1
  exact contDiffAt_pi.mpr (fun a ↦ contDiffAt_pi.mpr (fun b ↦ hC2 a b))

open Filter Topology in
private theorem normalFrame_pulledBackMetric_hermitian_germ
    (ω₀ ω₁ ωr : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x) :
    ∀ᶠ w in 𝓝 F.center, (pulledBackMetricInChart ωr x F.map w).IsHermitian := by
  filter_upwards [F.isOpen_domain.mem_nhds F.center_mem] with w hw
  have hmetric := (ωr.posDef_metricInChart x (F.maps_into_chart w hw)).isHermitian
  let J := holomorphicJacobianMatrix F.map w
  let H := ωr.metricInChart x (F.map w)
  have hJ1 : (J.map star).conjTranspose = J.transpose := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.transpose_apply]
  have hJ2 : J.transpose.conjTranspose = J.map star := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.transpose_apply]
  change (J.transpose * H * J.map star).conjTranspose = _
  calc
    _ = (J.map star).conjTranspose * H.conjTranspose * J.transpose.conjTranspose := by
      simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hJ1, hmetric.eq, hJ2]; rfl

open Filter Topology in
private theorem complexHessian_diag_re_eventuallyEq
    {f g : EuclideanSpace ℂ (Fin n) → ℝ} {z : EuclideanSpace ℂ (Fin n)}
    (hf : ContDiffAt ℝ 2 f z) (heq : f =ᶠ[𝓝 z] g) (p : Fin n) :
    (complexHessian f z p p).re = (complexHessian g z p p).re := by
  have hg : ContDiffAt ℝ 2 g z := hf.congr_of_eventuallyEq heq.symm
  have hder := (heq.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ) (x := z)
  rw [complexHessian_apply hf, complexHessian_apply hg, hder]

private theorem normalFrame_relative_trace_hessian_curvature_rhs
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x)
    (p : Fin n) :
    (∑ j, normalFrameSecondReal ω₀ ω₁ x F p j) +
        ∑ j, F.eigenvalue j * normalFrameBisectionalCurvature ω₀ ω₁ x F p j =
      (∑ j, (normalFrameMixedSecondDerivative ω₀ ω₁ x F p p j j).re) -
        ∑ j, F.eigenvalue j * (chartPartialZComplex
          (fun z ↦ chartPartialBarComplex
            (fun w ↦ pulledBackMetricInChart ω₀ x F.map w j j) z p)
          F.center p).re := by
  classical
  simp_rw [normalFrameBisectionalCurvature_eq_neg_reference_mixedSecond ω₀ ω₁ x F p]
  simp only [normalFrameSecondReal, normalFrameMixedSecondDerivative]
  simp_rw [mul_neg]
  rw [Finset.sum_neg_distrib]
  abel

open scoped Matrix.Norms.Elementwise in
private theorem normalFrame_relative_trace_hessian_expansion
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x) :
    ∀ p, RCLike.re (complexHessian
      (((fun y ↦ relTrace (ω₀ y) (ω₁ y)) ∘
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) ∘ F.map)
      F.center p p) =
      (∑ j, normalFrameSecondReal ω₀ ω₁ x F p j) +
        ∑ j, F.eigenvalue j * normalFrameBisectionalCurvature ω₀ ω₁ x F p j := by
  intro p
  let G₀ := pulledBackMetricInChart ω₀ x F.map
  let G₁ := pulledBackMetricInChart ω₁ x F.map
  have hC₀ : ContDiffAt ℝ 2 G₀ F.center :=
    normalFrame_pulledBackMetric_contDiffAt_two ω₀ ω₁ ω₀ x F
  have hC₁ : ContDiffAt ℝ 2 G₁ F.center :=
    normalFrame_pulledBackMetric_contDiffAt_two ω₀ ω₁ ω₁ x F
  have hFirstReal : fderiv ℝ G₀ F.center = 0 :=
    Matrix.fderiv_eq_zero_of_eventually_isHermitian_of_partialZ_eq_zero G₀ F.center
      (hC₀.differentiableAt (by norm_num))
      (normalFrame_pulledBackMetric_hermitian_germ ω₀ ω₁ ω₀ x F)
      F.reference_first_derivative_zero
  have hEq := normalFrame_relative_trace_eventually_eq_matrix_trace ω₀ ω₁ x F
  have hTransfer := complexHessian_diag_re_eventuallyEq
    (relTrace_contDiffAt_normalFrame ω₀ ω₁ x F) hEq p
  have hJet := complexHessian_relativeTraceMatrix_diag_of_normal G₀ G₁ F.center
    F.eigenvalue
    (fun j k ↦ contDiffAt_pi.mp (contDiffAt_pi.mp hC₀ j) k)
    (fun j k ↦ contDiffAt_pi.mp (contDiffAt_pi.mp hC₁ j) k)
    F.reference_normalized F.varying_diagonal hFirstReal p
  refine hTransfer.trans (hJet.trans ?_)
  simpa only [normalFrameMixedSecondDerivative, G₀, G₁] using
    (normalFrame_relative_trace_hessian_curvature_rhs ω₀ ω₁ x F p).symm

/-- Exact normal-frame Laplacian of the unlogged relative trace. -/
theorem normalFrame_laplacian_relative_trace
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x) :
    ω₁.laplacian (fun y ↦ relTrace (ω₀ y) (ω₁ y)) x =
      (∑ p, ∑ j, normalFrameSecondReal ω₀ ω₁ x F p j / F.eigenvalue p) +
        ∑ p, ∑ j, (F.eigenvalue p)⁻¹ * F.eigenvalue j *
          normalFrameBisectionalCurvature ω₀ ω₁ x F p j := by
  have hf := contDiffAt_relativeTrace_inChart ω₀ ω₁ x
  rw [← F.center_eq_chart_center] at hf
  rw [normalFrame_laplacian_eq_hessian_sum ω₀ ω₁ x F
    (fun y ↦ relTrace (ω₀ y) (ω₁ y)) hf]
  calc
    _ = ∑ p, ((∑ j, normalFrameSecondReal ω₀ ω₁ x F p j) +
        ∑ j, F.eigenvalue j * normalFrameBisectionalCurvature ω₀ ω₁ x F p j) /
          F.eigenvalue p := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [normalFrame_relative_trace_hessian_expansion ω₀ ω₁ x F p]
    _ = _ := by
      simp_rw [add_div]
      rw [Finset.sum_add_distrib]
      congr 1
      · simp_rw [Finset.sum_div]
      · apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j hj
        simp [div_eq_mul_inv, mul_comm, mul_left_comm]

end KahlerForm
