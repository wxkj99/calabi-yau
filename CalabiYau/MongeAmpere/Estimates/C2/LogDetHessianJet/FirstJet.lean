module

public import CalabiYau.Geometry.Kahler.Curvature.Chart
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import CalabiYau.Mathlib.Analysis.Matrix.PosDef.LogDet
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option maxHeartbeats 1000000

/-!
# The first logarithmic determinant jet as a neighborhood germ

The first matrix differentiation in Székelyhidi, *An Introduction to Extremal Kähler Metrics*,
§1.4, Lemma 1.22 proof, p. 12. This is the barred version of the source's first trace identity,
before any curvature identification. The determinant is real on the Hermitian germ; its positive
real value at the center and entrywise continuity give the local logarithm branch.

The conclusion is a germ, rather than only a center equality, so the parent may differentiate it.
Entrywise real C¹ at the center supplies local differentiability. Positive definiteness is not
needed for this matrix identity, only the stated positive determinant and Hermitian germ.
The chart operator uses the standard factor `1/2`.
-/

public section

open scoped ContDiff Matrix.Norms.Elementwise
open Filter Topology

namespace KahlerForm

private theorem fderiv_log_det_hermitian {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hHerm : A.IsHermitian) (hpos : 0 < A.det.re) :
    fderiv ℝ (fun C : Matrix (Fin n) (Fin n) ℂ => Real.log C.det.re) A B =
      (A⁻¹ * B).trace.re := by
  have hdetStar : star A.det = A.det := by
    rw [← Matrix.det_conjTranspose, hHerm.eq]
  have him : A.det.im = 0 := by
    have h := congrArg Complex.im hdetStar
    have h' : -A.det.im = A.det.im := by
      simpa only [Complex.star_def, Complex.conj_im] using h
    linarith
  have hdetne : A.det ≠ 0 := by
    intro h
    rw [h] at hpos
    simp at hpos
  have hunit : IsUnit A.det := hdetne.isUnit
  have hdetCD : ContDiff ℝ ∞ (fun C : Matrix (Fin n) (Fin n) ℂ => C.det) := by
    simp_rw [Matrix.det_apply']
    refine ContDiff.sum fun σ _ => ?_
    exact contDiff_const.mul (contDiff_prod fun i _ =>
      contDiff_pi.mp (contDiff_pi.mp contDiff_id (σ i)) i)
  have hlogCD : ContDiffAt ℝ ∞
      (fun C : Matrix (Fin n) (Fin n) ℂ => Real.log C.det.re) A := by
    have hrealCD : ContDiff ℝ ∞
        (fun C : Matrix (Fin n) (Fin n) ℂ => C.det.re) := by
      exact Complex.reCLM.contDiff.comp hdetCD
    exact (Real.contDiffAt_log.2 hpos.ne').comp A hrealCD.contDiffAt
  have hfd := (hlogCD.differentiableAt (by norm_num)).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => A + t • B) B 0 := by
    exact (((hasDerivAt_id (0 : ℝ)).smul_const B).const_add A).congr_deriv (one_smul ℝ B)
  have hchain := hfd.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hcomplex := Matrix.hasDerivAt_det_add_smul (K := ℂ) A B 0
  have hcomplex' : HasDerivAt (fun t : ℂ => (A + t • B).det)
      (Matrix.trace (Matrix.adjugate A * B)) 0 := by
    simpa using hcomplex
  have hrealparam : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
    simpa using (RCLike.ofRealCLM : ℝ →L[ℝ] ℂ).hasDerivAt
  have hdetLine : HasDerivAt (fun t : ℝ => (A + t • B).det)
      (Matrix.trace (Matrix.adjugate A * B)) 0 := by
    simpa [Function.comp_def] using
      (hcomplex'.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq
        0 hrealparam (by simp)
  have hrealLine := (Complex.reCLM : ℂ →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt_of_eq
    0 hdetLine (show A.det = (A + (0 : ℝ) • B).det by simp)
  have hrealAt : (Complex.reCLM ∘ fun t : ℝ => (A + t • B).det) 0 = A.det.re := by
    simp
  have hlogLine := hrealLine.log (hrealAt ▸ ne_of_gt hpos)
  have hadj : Matrix.adjugate A = A.det • A⁻¹ := by
    rw [Matrix.inv_def, smul_smul, Ring.mul_inverse_cancel _ hunit, one_smul]
  have hval : (Matrix.trace (Matrix.adjugate A * B)).re / A.det.re =
      (A⁻¹ * B).trace.re := by
    rw [hadj, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.mul_re]
    simp [him]
    field_simp [hpos.ne']
  have hcomp : HasDerivAt (fun t : ℝ => Real.log (A + t • B).det.re)
      ((A⁻¹ * B).trace.re) 0 := by
    convert hlogLine using 1
    · rfl
    · simpa [hrealAt] using hval.symm
  exact hchain.unique hcomp

private theorem fderiv_matrix_entry {n : ℕ}
    (G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hG : ∀ j k, DifferentiableAt ℝ (fun w => G w j k) z)
    (v : EuclideanSpace ℂ (Fin n)) (j k : Fin n) :
    (fderiv ℝ G z v) j k = fderiv ℝ (fun w => G w j k) z v := by
  have hrow (j : Fin n) : DifferentiableAt ℝ (fun w => G w j) z := by
    apply differentiableAt_pi.mpr
    intro k
    exact hG j k
  have hGdiff : DifferentiableAt ℝ G z := by
    apply differentiableAt_pi.mpr
    intro j
    exact hrow j
  have h1 := congrArg
    (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] (Fin n → ℂ) => (L v) k)
    (fderiv_apply hGdiff j)
  have h2 := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ => L v)
    (fderiv_apply (hrow j) k)
  calc
    (fderiv ℝ G z v) j k = (fderiv ℝ (fun w => G w j) z v) k := by
      convert h1.symm using 1; rfl
    _ = fderiv ℝ (fun w => G w j k) z v := by
      convert h2.symm using 1; rfl

private theorem fderiv_hermitian {n : ℕ}
    (G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hG : ∀ j k, DifferentiableAt ℝ (fun w => G w j k) z)
    (hHerm : ∀ᶠ w in 𝓝 z, (G w).IsHermitian)
    (v : EuclideanSpace ℂ (Fin n)) :
    (fderiv ℝ G z v).IsHermitian := by
  refine Matrix.IsHermitian.ext fun j k => ?_
  have hEq : (fun w => G w j k) =ᶠ[𝓝 z] fun w => star (G w k j) := by
    filter_upwards [hHerm] with w hw
    have h := congrFun₂ hw.eq j k
    simpa using h.symm
  have hEqfd := hEq.fderiv_eq (𝕜 := ℝ)
  have hpoint := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ => L v) hEqfd
  let f : EuclideanSpace ℂ (Fin n) → ℂ := fun w => G w k j
  have hcomp := fderiv_comp (f := f) (g := fun x : ℂ => Complex.conjCLE x)
    (x := z) (by fun_prop) (hG k j)
  have hstar : fderiv ℝ (fun w => star (f w)) z =
      Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ f z) := by
    have hstar' : fderiv ℝ (fun w => Complex.conjCLE (f w)) z =
        Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ f z) := by
      rw [show fderiv ℝ (fun x : ℂ => Complex.conjCLE x) (f z) =
          Complex.conjCLE.toContinuousLinearMap from
        Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.fderiv] at hcomp
      simpa [Function.comp_def] using hcomp
    have hfun : (fun w => star (f w)) = fun w => Complex.conjCLE (f w) := by
      funext w
      simp
    rw [hfun]
    exact hstar'
  rw [hstar] at hpoint
  have hcoord (j k : Fin n) :
      (fderiv ℝ G z v) j k = fderiv ℝ (fun w => G w j k) z v :=
    fderiv_matrix_entry G z hG v j k
  have hpoint' : fderiv ℝ (fun w => G w j k) z v =
      star (fderiv ℝ (fun w => G w k j) z v) := by
    simpa [f, ContinuousLinearMap.comp_apply] using hpoint
  calc
    star ((fderiv ℝ G z v) k j) =
        star (fderiv ℝ (fun w => G w k j) z v) := congrArg star (hcoord k j)
    _ = fderiv ℝ (fun w => G w j k) z v := hpoint'.symm
    _ = (fderiv ℝ G z v) j k := (hcoord j k).symm

private theorem trace_hermitian_mul_real {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A * B).trace.im = 0 := by
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

/-- The barred derivative of the real logarithmic determinant equals the inverse-trace
expression on a neighborhood germ of a Hermitian C¹ field with positive center determinant. -/
theorem log_det_bar_first_jet_eventually {n : ℕ}
    (G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (p : Fin n)
    (hG : ∀ j k, ContDiffAt ℝ 1 (fun w ↦ G w j k) z)
    (hHerm : ∀ᶠ w in 𝓝 z, (G w).IsHermitian)
    (hpos : 0 < (G z).det.re) :
    ∀ᶠ w in 𝓝 z,
      chartPartialBarComplex (fun v ↦ (Real.log ((G v).det.re) : ℂ)) w p =
        Matrix.trace ((G w)⁻¹ * Matrix.of (fun j k ↦
          chartPartialBarComplex (fun v ↦ G v j k) w p)) := by
  have hGmat : ContDiffAt ℝ 1 G z := by
    change ContDiffAt ℝ 1 (fun w j k => G w j k) z
    rw [contDiffAt_pi]
    intro j
    rw [contDiffAt_pi]
    intro k
    exact hG j k
  have hGnear : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ 1 G w :=
    hGmat.eventually (by norm_num)
  have hdetcont : ContinuousAt (fun w : EuclideanSpace ℂ (Fin n) => (G w).det.re) z := by
    exact (Complex.continuous_re.continuousAt.comp
      (continuous_id.matrix_det.continuousAt.comp hGmat.continuousAt))
  have hposnear : ∀ᶠ w in 𝓝 z, 0 < (G w).det.re :=
    hdetcont.eventually (isOpen_Ioi.mem_nhds hpos)
  obtain ⟨U, hUsub, hUopen, hzU⟩ := mem_nhds_iff.mp hHerm
  filter_upwards [hGnear, hposnear, hUopen.mem_nhds hzU] with w hwG hwpos hwU
  have hHermnear : ∀ᶠ v in 𝓝 w, (G v).IsHermitian := by
    filter_upwards [hUopen.mem_nhds hwU] with v hv
    exact hUsub hv
  have hGentry (j k : Fin n) : DifferentiableAt ℝ (fun v => G v j k) w := by
    have h := contDiffAt_pi.mp (contDiffAt_pi.mp hwG j) k
    exact h.differentiableAt (by norm_num)
  have hGdiff : DifferentiableAt ℝ G w := by
    change DifferentiableAt ℝ (fun v j k => G v j k) w
    rw [differentiableAt_pi]
    intro j
    rw [differentiableAt_pi]
    intro k
    exact hGentry j k
  have hlogCont : ContDiffAt ℝ ∞
      (fun A : Matrix (Fin n) (Fin n) ℂ => Real.log A.det.re) (G w) := by
    have hdetCD : ContDiff ℝ ∞
        (fun A : Matrix (Fin n) (Fin n) ℂ => A.det.re) := by
      have hdet : ContDiff ℝ ∞
          (fun A : Matrix (Fin n) (Fin n) ℂ => A.det) := by
        simp_rw [Matrix.det_apply']
        refine ContDiff.sum fun σ _ => ?_
        exact contDiff_const.mul (contDiff_prod fun i _ =>
          contDiff_pi.mp (contDiff_pi.mp contDiff_id (σ i)) i)
      exact Complex.reCLM.contDiff.comp hdet
    exact (Real.contDiffAt_log.2 hwpos.ne').comp (G w) hdetCD.contDiffAt
  have hlogdiff := hlogCont.differentiableAt (by norm_num)
  have hchain := fderiv_comp (f := G)
    (g := fun A : Matrix (Fin n) (Fin n) ℂ => Real.log A.det.re)
    (x := w) hlogdiff hGdiff
  have hchain' : fderiv ℝ (fun v => Real.log (G v).det.re) w =
      (fderiv ℝ (fun A : Matrix (Fin n) (Fin n) ℂ => Real.log A.det.re) (G w)).comp
        (fderiv ℝ G w) := by
    change fderiv ℝ ((fun A : Matrix (Fin n) (Fin n) ℂ => Real.log A.det.re) ∘ G) w = _
    exact hchain
  let D := fderiv ℝ G w
  let e := EuclideanSpace.single p (1 : ℂ)
  have hDerHerm (v : EuclideanSpace ℂ (Fin n)) : (D v).IsHermitian := by
    exact fderiv_hermitian G w hGentry hHermnear v
  have hHermAt : (G w).IsHermitian := hUsub hwU
  have hlogDir (v : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun v => Real.log (G v).det.re) w v =
        ((G w)⁻¹ * D v).trace.re := by
    rw [hchain']
    exact fderiv_log_det_hermitian (G w) (D v) hHermAt hwpos
  have hDEntry (v : EuclideanSpace ℂ (Fin n)) (j k : Fin n) :
      (D v) j k = fderiv ℝ (fun x => G x j k) w v := by
    dsimp [D]
    exact fderiv_matrix_entry G w hGentry v j k
  have hbarMatrix : Matrix.of (fun j k =>
      chartPartialBarComplex (fun v => G v j k) w p) =
      (2 : ℂ)⁻¹ • (D e + Complex.I • D (Complex.I • e)) := by
    ext j k
    change (fderiv ℝ (fun v => G v j k) w (EuclideanSpace.single p 1) +
        Complex.I * fderiv ℝ (fun v => G v j k) w
          (Complex.I • EuclideanSpace.single p 1)) / 2 =
      (2 : ℂ)⁻¹ * ((D e) j k + Complex.I * (D (Complex.I • e)) j k)
    rw [hDEntry e j k, hDEntry (Complex.I • e) j k]
    ring
  have hscalarDiff : DifferentiableAt ℝ (fun v => Real.log (G v).det.re) w :=
    hlogdiff.comp w hGdiff
  have hcastDeriv : fderiv ℝ (fun v => (Real.log (G v).det.re : ℂ)) w =
      Complex.ofRealCLM.comp (fderiv ℝ (fun v => Real.log (G v).det.re) w) := by
    change fderiv ℝ (Complex.ofRealCLM ∘ (fun v => Real.log (G v).det.re)) w = _
    exact (Complex.ofRealCLM.hasFDerivAt.comp w hscalarDiff.hasFDerivAt).fderiv
  have hinvHerm : ((G w)⁻¹).IsHermitian := hHermAt.inv
  have htraceReal (v : EuclideanSpace ℂ (Fin n)) :
      (((G w)⁻¹ * D v).trace.im) = 0 :=
    trace_hermitian_mul_real _ _ hinvHerm (hDerHerm v)
  have htraceFormula :
      Matrix.trace ((G w)⁻¹ * ((2 : ℂ)⁻¹ •
        (D e + Complex.I • D (Complex.I • e)))) =
        (Matrix.trace ((G w)⁻¹ * D e) +
          Complex.I * Matrix.trace ((G w)⁻¹ * D (Complex.I • e))) / 2 := by
    rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_add, Matrix.trace_add,
      Matrix.mul_smul, Matrix.trace_smul]
    simp [smul_eq_mul, div_eq_mul_inv]
    ring
  have hpoint :
      chartPartialBarComplex (fun v => (Real.log (G v).det.re : ℂ)) w p =
        Matrix.trace ((G w)⁻¹ * Matrix.of (fun j k =>
          chartPartialBarComplex (fun v => G v j k) w p)) := by
    change (fderiv ℝ (fun v => (Real.log (G v).det.re : ℂ)) w e +
        Complex.I * fderiv ℝ (fun v => (Real.log (G v).det.re : ℂ)) w
          (Complex.I • e)) / 2 = _
    rw [hcastDeriv]
    simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
    rw [hlogDir e, hlogDir (Complex.I • e), hbarMatrix]
    have hre₁ := htraceReal e
    have hre₂ := htraceReal (Complex.I • e)
    rw [htraceFormula]
    apply Complex.ext
    · simp [Complex.add_re, Complex.mul_re, hre₂]
    · simp [Complex.add_im, Complex.mul_im, hre₂]
      exact hre₁
  exact hpoint

end KahlerForm
