module

public import CalabiYau.MongeAmpere.Estimates.C3.TraceLaplacian.Refined.ReferenceCurvatureError
public import CalabiYau.MongeAmpere.Estimates.C2.LogDetHessianJet
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Differentiated determinant equation in a reference-normal frame

Twice differentiating `det h = exp G · det g` at a point where `g=1` and
`h=diag λ` converts the weighted mixed Hessian of `h` into that of `G`,
the squared first derivatives of `h`, and the reference curvature trace.
Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §3.2,
Lemma 3.8, and §3.3, Lemma 3.10, pp. 41–46.
-/

@[expose] public section

open scoped BigOperators Manifold ContDiff NNReal ComplexOrder MatrixOrder
open ContinuousAlternatingMap Filter Topology

namespace KahlerForm

variable {n : ℕ}

private theorem c3RefinedTrace_logDet_diagonal_jet {n : ℕ}
    (F : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (lam : Fin n → ℝ)
    (hF : ∀ j k, ContDiffAt ℝ ∞ (fun w ↦ F w j k) z)
    (hHerm : ∀ᶠ w in 𝓝 z, (F w).IsHermitian)
    (hdiag : F z = Matrix.diagonal (fun j ↦ (lam j : ℂ)))
    (hlam : ∀ j, 0 < lam j) (p : Fin n) :
    (wirtingerDerivInChart (fun w ↦ c3RefinedTracePartialBar
      (fun v ↦ (Real.log ((F v).det.re) : ℂ)) w p) z p).re =
      (∑ j, (wirtingerDerivInChart (fun w ↦ c3RefinedTracePartialBar
        (fun v ↦ F v j j) w p) z p).re / lam j) -
      ∑ j, ∑ k, ‖wirtingerDerivInChart (fun w ↦ F w j k) z p‖ ^ (2 : ℕ) /
        (lam j * lam k) := by
  have hreg : ∀ j k, ContDiffAt ℝ 2 (fun w ↦ F w j k) z :=
    fun j k ↦ (hF j k).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have h := log_det_mixed_second_real_of_diagonal F z lam hreg hHerm hdiag hlam p
  exact h

private theorem c3RefinedTrace_reference_logDet_jet {n : ℕ}
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hg : ∀ i j, ContDiffAt ℝ ∞ (fun w ↦ g w i j) z)
    (hNormal : g z = 1)
    (hFirst : ∀ i j p, wirtingerDerivInChart (fun w ↦ g w i j) z p = 0)
    (hLocal : ∃ U : Set (EuclideanSpace ℂ (Fin n)),
      IsOpen U ∧ z ∈ U ∧ ∀ w ∈ U, g w = (g w).conjTranspose)
    (p : Fin n) :
    (wirtingerDerivInChart (fun w ↦ c3RefinedTracePartialBar
      (fun v ↦ (Real.log ((g v).det.re) : ℂ)) w p) z p).re =
      ∑ j, RCLike.re (c3RefinedTraceMatrixMixedPartial g z p p j j) := by
  obtain ⟨U, hU, hz, hHerm⟩ := hLocal
  have hHermN : ∀ᶠ w in 𝓝 z, (g w).IsHermitian := by
    filter_upwards [hU.mem_nhds hz] with w hw
    simpa [Matrix.IsHermitian] using (hHerm w hw).symm
  have hJet := c3RefinedTrace_logDet_diagonal_jet g z (fun _ ↦ 1) hg hHermN
    (by simpa using hNormal) (fun _ ↦ by norm_num) p
  rw [hJet]
  simp only [div_one, one_mul]
  simp_rw [hFirst]
  simp [c3RefinedTraceMatrixMixedPartial, c3RefinedTraceMatrixPartialZ,
    c3RefinedTraceMatrixPartialBar]

private theorem c3RefinedTrace_hermitian_det_ofReal_re_local {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    A.det = (A.det.re : ℂ) := by
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

private theorem c3RefinedTrace_scalar_log_ratio_local {a b : ℝ} {z : ℂ}
    (ha : 0 < a) (hb : 0 < b)
    (hEq : (a : ℂ) = Complex.exp z * (b : ℂ)) :
    z.re = Real.log a - Real.log b := by
  have hnorm := congrArg norm hEq
  have hreal : Real.exp z.re * b = a := by
    simpa [Complex.norm_exp, norm_mul, Complex.norm_real,
      abs_of_pos ha, abs_of_pos hb] using hnorm.symm
  have hlog : Real.log a = z.re + Real.log b := by
    rw [← hreal, Real.log_mul (ne_of_gt (Real.exp_pos z.re)) hb.ne', Real.log_exp]
  linarith

private theorem c3RefinedTrace_local_logdet_equation {n : ℕ}
    (g h : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (G : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (lam : Fin n → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ ∞ (fun w ↦ g w i j) z)
    (hh : ∀ i j, ContDiffAt ℝ ∞ (fun w ↦ h w i j) z)
    (hNormal : g z = 1)
    (hDiagonal : h z = Matrix.diagonal (fun i ↦ (lam i : ℂ)))
    (hPositive : ∀ i, 0 < lam i)
    (hLocal : ∃ U : Set (EuclideanSpace ℂ (Fin n)), IsOpen U ∧ z ∈ U ∧
      ∀ w ∈ U, g w = (g w).conjTranspose ∧ h w = (h w).conjTranspose ∧
        (h w).det = Complex.exp (G w) * (g w).det) :
    ∀ᶠ w in 𝓝 z,
      (G w).re = Real.log ((h w).det.re) - Real.log ((g w).det.re) := by
  obtain ⟨U, hU, hz, hdata⟩ := hLocal
  have hgCont : ContinuousAt g z := by
    change ContinuousAt (fun w i j ↦ g w i j) z
    rw [continuousAt_pi]
    intro i
    rw [continuousAt_pi]
    intro j
    exact (hg i j).continuousAt
  have hhCont : ContinuousAt h z := by
    change ContinuousAt (fun w i j ↦ h w i j) z
    rw [continuousAt_pi]
    intro i
    rw [continuousAt_pi]
    intro j
    exact (hh i j).continuousAt
  have hcontG : ContinuousAt (fun w ↦ (g w).det.re) z := by
    exact (Complex.continuous_re.continuousAt.comp
      (continuous_id.matrix_det.continuousAt.comp hgCont))
  have hcontH : ContinuousAt (fun w ↦ (h w).det.re) z := by
    exact (Complex.continuous_re.continuousAt.comp
      (continuous_id.matrix_det.continuousAt.comp hhCont))
  have hposG0 : 0 < (g z).det.re := by simp [hNormal]
  have hposH0 : 0 < (h z).det.re := by
    have hPD : (h z).PosDef := by
      rw [hDiagonal, Matrix.posDef_diagonal_iff]
      intro i
      exact_mod_cast hPositive i
    exact (Complex.pos_iff.mp hPD.det_pos).1
  have hposG : ∀ᶠ w in 𝓝 z, 0 < (g w).det.re :=
    hcontG.eventually (isOpen_Ioi.mem_nhds hposG0)
  have hposH : ∀ᶠ w in 𝓝 z, 0 < (h w).det.re :=
    hcontH.eventually (isOpen_Ioi.mem_nhds hposH0)
  filter_upwards [hU.mem_nhds hz, hposG, hposH] with w hw hbg hah
  have hgHerm : (g w).IsHermitian := by
    simpa [Matrix.IsHermitian] using (hdata w hw).1.symm
  have hhHerm : (h w).IsHermitian := by
    simpa [Matrix.IsHermitian] using (hdata w hw).2.1.symm
  have hdetG := c3RefinedTrace_hermitian_det_ofReal_re_local (g w) hgHerm
  have hdetH := c3RefinedTrace_hermitian_det_ofReal_re_local (h w) hhHerm
  have hEq := (hdata w hw).2.2
  rw [hdetH, hdetG] at hEq
  exact c3RefinedTrace_scalar_log_ratio_local hah hbg hEq

private theorem c3RefinedTrace_logdet_contDiffAt {n : ℕ}
    (F : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hF : ∀ i j, ContDiffAt ℝ ∞ (fun w ↦ F w i j) z)
    (hpos : 0 < (F z).det.re) :
    ContDiffAt ℝ ∞ (fun w ↦ Real.log ((F w).det.re)) z := by
  have hdet : ContDiffAt ℝ ∞ (fun w ↦ (F w).det) z := by
    simp_rw [Matrix.det_apply']
    fun_prop (disch := intro i j; exact hF i j)
  have hdetRe : ContDiffAt ℝ ∞ (fun w ↦ (F w).det.re) z := by
    change ContDiffAt ℝ ∞ (RCLike.re ∘ fun w ↦ (F w).det) z
    exact RCLike.reCLM.contDiff.contDiffAt.comp z hdet
  exact (Real.contDiffAt_log.2 hpos.ne').comp z hdetRe

private theorem c3RefinedTrace_logdet_functions_contDiffAt {n : ℕ}
    (g h : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (lam : Fin n → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ ∞ (fun w ↦ g w i j) z)
    (hh : ∀ i j, ContDiffAt ℝ ∞ (fun w ↦ h w i j) z)
    (hNormal : g z = 1)
    (hDiagonal : h z = Matrix.diagonal (fun i ↦ (lam i : ℂ)))
    (hPositive : ∀ i, 0 < lam i) :
    ContDiffAt ℝ 2 (fun w ↦ Real.log ((h w).det.re)) z ∧
      ContDiffAt ℝ 2 (fun w ↦ Real.log ((g w).det.re)) z := by
  have hposG : 0 < (g z).det.re := by simp [hNormal]
  have hposH : 0 < (h z).det.re := by
    have hPD : (h z).PosDef := by
      rw [hDiagonal, Matrix.posDef_diagonal_iff]
      intro i
      exact_mod_cast hPositive i
    exact (Complex.pos_iff.mp hPD.det_pos).1
  constructor
  · exact (c3RefinedTrace_logdet_contDiffAt h z hh hposH).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  · exact (c3RefinedTrace_logdet_contDiffAt g z hg hposG).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))

private theorem c3RefinedTrace_complexHessian_eventuallyEq {n : ℕ}
    (f g : EuclideanSpace ℂ (Fin n) → ℝ)
    (z : EuclideanSpace ℂ (Fin n))
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z)
    (hfg : f =ᶠ[𝓝 z] g) (p : Fin n) :
    complexHessian f z p p = complexHessian g z p p := by
  have hiter : iteratedFDeriv ℝ 2 f z = iteratedFDeriv ℝ 2 g z :=
    (hfg.iteratedFDeriv ℝ 2).eq_of_nhds
  have hsec (v u : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fderiv ℝ f) z v u = fderiv ℝ (fderiv ℝ g) z v u := by
    have h := congrArg (fun T ↦ T ![v, u]) hiter
    simpa only [iteratedFDeriv_two_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one] using h
  rw [complexHessian_apply hf p p, complexHessian_apply hg p p]
  rw [hsec (EuclideanSpace.single p 1) (EuclideanSpace.single p 1),
    hsec (Complex.I • EuclideanSpace.single p 1) (Complex.I • EuclideanSpace.single p 1),
    hsec (EuclideanSpace.single p 1) (Complex.I • EuclideanSpace.single p 1),
    hsec (Complex.I • EuclideanSpace.single p 1) (EuclideanSpace.single p 1)]

private theorem c3RefinedTrace_complexHessian_sub {n : ℕ}
    (f g : EuclideanSpace ℂ (Fin n) → ℝ)
    (z : EuclideanSpace ℂ (Fin n))
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) (p : Fin n) :
    complexHessian (fun w ↦ f w - g w) z p p =
      complexHessian f z p p - complexHessian g z p p := by
  have hfsub : ContDiffAt ℝ 2 (fun w ↦ f w - g w) z := hf.sub hg
  have hiter := iteratedFDeriv_sub_apply hf hg
  change iteratedFDeriv ℝ 2 (fun w ↦ f w - g w) z =
    iteratedFDeriv ℝ 2 f z - iteratedFDeriv ℝ 2 g z at hiter
  have hsec (v u : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fderiv ℝ (fun w ↦ f w - g w)) z v u =
        fderiv ℝ (fderiv ℝ f) z v u - fderiv ℝ (fderiv ℝ g) z v u := by
    have h := congrArg (fun T ↦ T ![v, u]) hiter
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, _root_.sub_apply] at h
    exact h
  rw [complexHessian_apply hfsub p p, complexHessian_apply hf p p,
    complexHessian_apply hg p p]
  rw [hsec (EuclideanSpace.single p 1) (EuclideanSpace.single p 1),
    hsec (Complex.I • EuclideanSpace.single p 1) (Complex.I • EuclideanSpace.single p 1),
    hsec (EuclideanSpace.single p 1) (Complex.I • EuclideanSpace.single p 1),
    hsec (Complex.I • EuclideanSpace.single p 1) (EuclideanSpace.single p 1)]
  simp
  ring

private theorem c3RefinedTrace_mixed_wirtinger_realpart_eq_hessian {n : ℕ}
    (a : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (ha : ContDiffAt ℝ 2 a z) (p : Fin n) :
    (wirtingerDerivInChart (fun w ↦ c3RefinedTracePartialBar a w p) z p).re =
      (complexHessian (fun w ↦ (a w).re) z p p).re := by
  let ep : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single p 1
  have ha1 : ContDiffAt ℝ 1 (fderiv ℝ a) z := ha.fderiv_right (m := 1) (by norm_num)
  have hfdDiff : DifferentiableAt ℝ (fderiv ℝ a) z := ha1.differentiableAt (by norm_num)
  have hA : DifferentiableAt ℝ (fun w ↦ fderiv ℝ a w ep) z :=
    hfdDiff.clm_apply (differentiableAt_const _)
  have hB : DifferentiableAt ℝ (fun w ↦ fderiv ℝ a w (Complex.I • ep)) z :=
    hfdDiff.clm_apply (differentiableAt_const _)
  have hD (d q : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ fderiv ℝ a w q) z d = fderiv ℝ (fderiv ℝ a) z d q := by
    have h := fderiv_clm_apply (u := fun _ : EuclideanSpace ℂ (Fin n) ↦ q)
      hfdDiff (differentiableAt_const _)
    have h' := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L d) h
    simpa using h'
  have hAc (d : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ fderiv ℝ a w ep) z d = fderiv ℝ (fderiv ℝ a) z d ep := hD d ep
  have hBc (d : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ fderiv ℝ a w (Complex.I • ep)) z d =
        fderiv ℝ (fderiv ℝ a) z d (Complex.I • ep) := hD d (Complex.I • ep)
  have hnum : DifferentiableAt ℝ
      (fun w ↦ fderiv ℝ a w ep + Complex.I * fderiv ℝ a w (Complex.I • ep)) z :=
    hA.add (hB.const_mul Complex.I)
  have hbar : (fun w ↦ c3RefinedTracePartialBar a w p) =
      fun w ↦ (2 : ℂ)⁻¹ * (fderiv ℝ a w ep + Complex.I * fderiv ℝ a w (Complex.I • ep)) := by
    funext w
    simp [c3RefinedTracePartialBar, ep, div_eq_mul_inv]
    ring
  have hpartial (d : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ c3RefinedTracePartialBar a w p) z d =
        (2 : ℂ)⁻¹ *
          (fderiv ℝ (fderiv ℝ a) z d ep +
            Complex.I * fderiv ℝ (fderiv ℝ a) z d (Complex.I • ep)) := by
    rw [hbar, fderiv_const_mul hnum (2 : ℂ)⁻¹,
      fderiv_fun_add hA (hB.const_mul Complex.I),
      fderiv_const_mul hB Complex.I]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, hAc, hBc]
  have hq : ContDiffAt ℝ 2 (fun w ↦ (a w).re) z := by
    change ContDiffAt ℝ 2 (RCLike.re ∘ a) z
    exact (RCLike.reCLM.contDiff.contDiffAt.comp z ha)
  unfold wirtingerDerivInChart
  rw [hpartial ep, hpartial (Complex.I • ep), complexHessian_apply hq p p]
  simp only [div_eq_mul_inv]
  have hsymm := ha.isSymmSndFDerivAt (by norm_num [minSmoothness])
  have hsymm₁ : fderiv ℝ (fderiv ℝ a) z ep (Complex.I • ep) =
      fderiv ℝ (fderiv ℝ a) z (Complex.I • ep) ep := hsymm _ _
  have hRe (d e : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fderiv ℝ (fun w ↦ (a w).re)) z d e =
        (fderiv ℝ (fderiv ℝ a) z d e).re := by
    let L : ℂ →L[ℝ] ℝ := RCLike.reCLM
    have hiter := L.iteratedFDeriv_comp_left (f := a) ha (i := 2) (by norm_num)
    have hEval := congrArg (fun T ↦ T ![d, e]) hiter
    have hLeft : iteratedFDeriv ℝ 2 (fun w ↦ (a w).re) z ![d, e] =
        fderiv ℝ (fderiv ℝ (fun w ↦ (a w).re)) z d e := by
      rw [iteratedFDeriv_two_apply]
      simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    have hRight : iteratedFDeriv ℝ 2 a z ![d, e] =
        fderiv ℝ (fderiv ℝ a) z d e := by
      rw [iteratedFDeriv_two_apply]
      simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    have hcomp : iteratedFDeriv ℝ 2 (fun w ↦ (a w).re) z ![d, e] =
        (iteratedFDeriv ℝ 2 a z ![d, e]).re := by
      have h := hEval
      simp [L, Function.comp_def] at h
      exact h
    rw [← hLeft, hcomp, hRight]
  rw [hRe ep ep, hRe (Complex.I • ep) (Complex.I • ep),
    hRe ep (Complex.I • ep), hRe (Complex.I • ep) ep, hsymm₁]
  simp [Complex.I_re, Complex.mul_re]
  ring

private theorem c3RefinedTrace_local_Gjet_from_log_equation {n : ℕ}
    (g h : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (G : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (lam : Fin n → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ ∞ (fun w ↦ g w i j) z)
    (hh : ∀ i j, ContDiffAt ℝ ∞ (fun w ↦ h w i j) z)
    (hG : ContDiffAt ℝ ∞ G z)
    (hNormal : g z = 1)
    (hDiagonal : h z = Matrix.diagonal (fun i ↦ (lam i : ℂ)))
    (hPositive : ∀ i, 0 < lam i)
    (hLocal : ∃ U : Set (EuclideanSpace ℂ (Fin n)), IsOpen U ∧ z ∈ U ∧
      ∀ w ∈ U, g w = (g w).conjTranspose ∧ h w = (h w).conjTranspose ∧
        (h w).det = Complex.exp (G w) * (g w).det)
    (p : Fin n) :
    (wirtingerDerivInChart (fun w ↦ c3RefinedTracePartialBar G w p) z p).re =
      (wirtingerDerivInChart (fun w ↦ c3RefinedTracePartialBar
        (fun v ↦ (Real.log ((h v).det.re) : ℂ)) w p) z p).re -
      (wirtingerDerivInChart (fun w ↦ c3RefinedTracePartialBar
        (fun v ↦ (Real.log ((g v).det.re) : ℂ)) w p) z p).re := by
  have hEq := c3RefinedTrace_local_logdet_equation g h G z lam hg hh
    hNormal hDiagonal hPositive hLocal
  have hsmooth := c3RefinedTrace_logdet_functions_contDiffAt g h z lam
    hg hh hNormal hDiagonal hPositive
  have hG2 : ContDiffAt ℝ 2 G z :=
    hG.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hReG := c3RefinedTrace_mixed_wirtinger_realpart_eq_hessian G z hG2 p
  have hReReg : ContDiffAt ℝ 2 (fun w ↦ (G w).re) z := by
    change ContDiffAt ℝ 2 (RCLike.re ∘ G) z
    exact (RCLike.reCLM.contDiff.contDiffAt.comp z hG2)
  have hHessEq := c3RefinedTrace_complexHessian_eventuallyEq
    (fun w ↦ (G w).re)
    (fun w ↦ Real.log ((h w).det.re) - Real.log ((g w).det.re))
    z hReReg (hsmooth.1.sub hsmooth.2) hEq p
  have hSub := c3RefinedTrace_complexHessian_sub
    (fun w ↦ Real.log ((h w).det.re)) (fun w ↦ Real.log ((g w).det.re))
    z hsmooth.1 hsmooth.2 p
  have hfJet := c3RefinedTrace_mixed_wirtinger_realpart_eq_hessian
    (fun w ↦ (Real.log ((h w).det.re) : ℂ)) z
    (by exact (Complex.ofRealCLM.contDiff.contDiffAt.comp z hsmooth.1)) p
  have hgJet := c3RefinedTrace_mixed_wirtinger_realpart_eq_hessian
    (fun w ↦ (Real.log ((g w).det.re) : ℂ)) z
    (by exact (Complex.ofRealCLM.contDiff.contDiffAt.comp z hsmooth.2)) p
  simp only [Complex.ofReal_re] at hfJet hgJet
  rw [hReG, hHessEq, hSub, hfJet, hgJet]
  simp [Complex.sub_re]

private theorem c3RefinedTrace_partialBar_star_partialZ_star {n : ℕ}
    (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (p : Fin n)
    (hf : DifferentiableAt ℝ f z) :
    c3RefinedTracePartialBar f z p =
      star (wirtingerDerivInChart (fun w ↦ star (f w)) z p) := by
  unfold c3RefinedTracePartialBar wirtingerDerivInChart
  let e := EuclideanSpace.single p (1 : ℂ)
  have hreal := hf.hasFDerivAt
  have hc := (Complex.conjCLE.hasFDerivAt (x := f z)).comp z hreal
  have hstar : fderiv ℝ (fun w ↦ star (f w)) z =
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ f z) := by
    simpa [Function.comp_def, Complex.conjCLE_apply, Complex.star_def] using hc.fderiv
  rw [hstar]
  simp only [ContinuousLinearMap.comp_apply]
  simp [Complex.conj_I]

private theorem c3RefinedTrace_referenceBar_zero {n : ℕ}
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hg : ∀ i j, ContDiffAt ℝ ∞ (fun w ↦ g w i j) z)
    (hFirst : ∀ i j p, wirtingerDerivInChart (fun w ↦ g w i j) z p = 0)
    (hHermitian : ∃ U : Set (EuclideanSpace ℂ (Fin n)),
      IsOpen U ∧ z ∈ U ∧ ∀ w ∈ U, g w = (g w).conjTranspose) :
    ∀ i j p, c3RefinedTracePartialBar (fun w ↦ g w i j) z p = 0 := by
  obtain ⟨U, hU, hz, hHerm⟩ := hHermitian
  intro i j p
  have hlocal : (fun w ↦ star (g w i j)) =ᶠ[𝓝 z] (fun w ↦ g w j i) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    have hij : g w i j = star (g w j i) := by
      have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ ↦ A i j) (hHerm w hw)
      simpa using h
    simpa using congrArg star hij
  have hderiv := hlocal.fderiv_eq (𝕜 := ℝ) (x := z)
  have hpartial : wirtingerDerivInChart (fun w ↦ star (g w i j)) z p =
      wirtingerDerivInChart (fun w ↦ g w j i) z p := by
    unfold wirtingerDerivInChart
    rw [hderiv]
  have hbar := c3RefinedTrace_partialBar_star_partialZ_star
    (fun w ↦ g w i j) z p ((hg i j).differentiableAt (by norm_num))
  rw [hpartial, hFirst j i p] at hbar
  simpa using hbar

private theorem c3RefinedTrace_reference_curvature_eq_neg_mixed {n : ℕ}
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hg : ∀ i j, ContDiffAt ℝ ∞ (fun w ↦ g w i j) z)
    (hNormal : g z = 1)
    (hFirst : ∀ i j p, wirtingerDerivInChart (fun w ↦ g w i j) z p = 0)
    (hHermitian : ∃ U : Set (EuclideanSpace ℂ (Fin n)),
      IsOpen U ∧ z ∈ U ∧ ∀ w ∈ U, g w = (g w).conjTranspose)
    (p j : Fin n) :
    c3RefinedTraceReferenceCurvatureInChart g z p p j j =
      -c3RefinedTraceMatrixMixedPartial g z p p j j := by
  have hbar := c3RefinedTrace_referenceBar_zero g z hg hFirst hHermitian
  have hdet : IsUnit (g z).det := by rw [hNormal]; simp
  have hbarGamma (a : Fin n) : c3RefinedTracePartialBar
      (fun w ↦ christoffelInChart g w a p j) z p =
      -(∑ l, (g z)⁻¹ l a * chartCurvature g z p p j l) := by
    have hcurv := chartChristoffel_bar_eq_curvature_at g z hg hdet a p j p
    simpa [c3RefinedTracePartialBar, christoffelInChart, wirtingerDerivInChart,
      chartPartialBarComplex, chartPartialZComplex] using hcurv
  unfold c3RefinedTraceReferenceCurvatureInChart
  rw [Finset.sum_congr rfl (fun a ha => by rw [hbarGamma a])]
  have hInv : (g z)⁻¹ = 1 := by rw [hNormal]; simp
  rw [hInv, hNormal]
  simp [Matrix.one_apply]
  unfold chartCurvature c3RefinedTraceMatrixMixedPartial
    c3RefinedTraceMatrixPartialZ c3RefinedTraceMatrixPartialBar
  rw [show chartPartialZComplex = wirtingerDerivInChart from rfl,
    show chartPartialBarComplex = c3RefinedTracePartialBar from rfl]
  simp [hFirst, hbar]

private theorem c3RefinedTrace_determinant_sum_glue {n : ℕ}
    (lam : Fin n → ℝ)
    (H G Curv : Fin n → Fin n → ℝ)
    (Q Hlog Glog Gjet : Fin n → ℝ)
    (hGjet : ∀ p, Gjet p = Hlog p - Glog p)
    (hHlog : ∀ p, Hlog p = (∑ j, H p j / lam j) - Q p)
    (hGlog : ∀ p, Glog p = ∑ j, G p j)
    (hCurv : ∀ p j, Curv p j = -G p j) :
    (∑ p : Fin n, ∑ j : Fin n, H j p / lam p) =
      (∑ p, Gjet p) + (∑ p, Q p) - (∑ p, ∑ j, Curv p j) := by
  have hHsum : (∑ p, Hlog p) =
      (∑ p : Fin n, ∑ j : Fin n, H p j / lam j) - ∑ p, Q p := by
    simp_rw [hHlog]
    rw [Finset.sum_sub_distrib]
  have hGlogSum : (∑ p, Glog p) = ∑ p : Fin n, ∑ j : Fin n, G p j := by
    simp_rw [hGlog]
  have hGjetSum : (∑ p, Gjet p) = (∑ p, Hlog p) - ∑ p, Glog p := by
    simp_rw [hGjet]
    rw [Finset.sum_sub_distrib]
  have hCurvSum : (∑ p : Fin n, ∑ j : Fin n, Curv p j) =
      -(∑ p : Fin n, ∑ j : Fin n, G p j) := by
    simp_rw [hCurv]
    simp [Finset.sum_neg_distrib]
  calc
    (∑ p : Fin n, ∑ j : Fin n, H j p / lam p) =
        ∑ p : Fin n, ∑ j : Fin n, H p j / lam j := Finset.sum_comm
    _ = (∑ p, Gjet p) + (∑ p, Q p) - (∑ p, ∑ j, Curv p j) := by
      rw [hGjetSum, hHsum, hGlogSum, hCurvSum]
      ring

/-- Logarithmic mixed differentiation of the local Monge–Ampère determinant
equation. The positive term has denominator `λₚ λₖ`; unlike the eventual
Calabi energy, no inverse eigenvalue occurs at the `j` derivative index.
Hermitian symmetry near the center is required to identify conjugate entries
and to deduce `∂bar g=0` from the normal holomorphic first derivatives. -/
theorem c3RefinedTrace_normalFrame_determinantHessian
    (g h : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (G : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (lam : Fin n → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ ∞ (fun w ↦ g w i j) z)
    (hh : ∀ i j, ContDiffAt ℝ ∞ (fun w ↦ h w i j) z)
    (hG : ContDiffAt ℝ ∞ G z)
    (hNormal : g z = 1)
    (hFirst : ∀ i j p, wirtingerDerivInChart (fun w ↦ g w i j) z p = 0)
    (hDiagonal : h z = Matrix.diagonal (fun i ↦ (lam i : ℂ)))
    (hPositive : ∀ i, 0 < lam i)
    (hLocal : ∃ U : Set (EuclideanSpace ℂ (Fin n)),
      IsOpen U ∧ z ∈ U ∧ ∀ w ∈ U,
        g w = (g w).conjTranspose ∧ h w = (h w).conjTranspose ∧
          (h w).det = Complex.exp (G w) * (g w).det) :
    (∑ p : Fin n, ∑ j : Fin n,
      RCLike.re (c3RefinedTraceMatrixMixedPartial h z j j p p) / lam p) =
      (∑ p : Fin n, RCLike.re
        (wirtingerDerivInChart (fun w ↦ c3RefinedTracePartialBar G w p) z p)) +
      (∑ p : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        ‖wirtingerDerivInChart (fun w ↦ h w j k) z p‖ ^ (2 : ℕ) /
          (lam j * lam k)) -
      (∑ p : Fin n, ∑ j : Fin n,
        RCLike.re (c3RefinedTraceReferenceCurvatureInChart g z p p j j)) := by
  obtain ⟨U, hU, hz, hLocalData⟩ := hLocal
  have hLocal' : ∃ U : Set (EuclideanSpace ℂ (Fin n)), IsOpen U ∧ z ∈ U ∧
      ∀ w ∈ U, g w = (g w).conjTranspose ∧ h w = (h w).conjTranspose ∧
        (h w).det = Complex.exp (G w) * (g w).det := ⟨U, hU, hz, hLocalData⟩
  have hHermG : ∃ U : Set (EuclideanSpace ℂ (Fin n)), IsOpen U ∧ z ∈ U ∧
      ∀ w ∈ U, g w = (g w).conjTranspose :=
    ⟨U, hU, hz, fun w hw => (hLocalData w hw).1⟩
  have hHermHnear : ∀ᶠ w in 𝓝 z, (h w).IsHermitian := by
    filter_upwards [hU.mem_nhds hz] with w hw
    simpa [Matrix.IsHermitian] using (hLocalData w hw).2.1.symm
  let H : Fin n → Fin n → ℝ := fun p j =>
    RCLike.re (c3RefinedTraceMatrixMixedPartial h z p p j j)
  let Gm : Fin n → Fin n → ℝ := fun p j =>
    RCLike.re (c3RefinedTraceMatrixMixedPartial g z p p j j)
  let Curv : Fin n → Fin n → ℝ := fun p j =>
    RCLike.re (c3RefinedTraceReferenceCurvatureInChart g z p p j j)
  let Q : Fin n → ℝ := fun p =>
    ∑ j, ∑ k, ‖wirtingerDerivInChart (fun w ↦ h w j k) z p‖ ^ (2 : ℕ) /
      (lam j * lam k)
  let Hlog : Fin n → ℝ := fun p =>
    RCLike.re (wirtingerDerivInChart (fun w ↦ c3RefinedTracePartialBar
      (fun v ↦ (Real.log ((h v).det.re) : ℂ)) w p) z p)
  let Glog : Fin n → ℝ := fun p =>
    RCLike.re (wirtingerDerivInChart (fun w ↦ c3RefinedTracePartialBar
      (fun v ↦ (Real.log ((g v).det.re) : ℂ)) w p) z p)
  let Gjet : Fin n → ℝ := fun p =>
    RCLike.re (wirtingerDerivInChart (fun w ↦ c3RefinedTracePartialBar G w p) z p)
  have hGjet (p : Fin n) : Gjet p = Hlog p - Glog p := by
    exact c3RefinedTrace_local_Gjet_from_log_equation g h G z lam hg hh hG
      hNormal hDiagonal hPositive hLocal' p
  have hHlog (p : Fin n) : Hlog p = (∑ j, H p j / lam j) - Q p := by
    have hjet := c3RefinedTrace_logDet_diagonal_jet h z lam hh hHermHnear
      hDiagonal hPositive p
    simpa [Hlog, H, Q, c3RefinedTraceMatrixMixedPartial,
      c3RefinedTraceMatrixPartialZ, c3RefinedTraceMatrixPartialBar] using hjet
  have hGlog (p : Fin n) : Glog p = ∑ j, Gm p j := by
    have hjet := c3RefinedTrace_reference_logDet_jet g z hg hNormal hFirst hHermG p
    simpa [Glog, Gm] using hjet
  have hCurv (p j : Fin n) : Curv p j = -Gm p j := by
    change RCLike.re (c3RefinedTraceReferenceCurvatureInChart g z p p j j) =
      -RCLike.re (c3RefinedTraceMatrixMixedPartial g z p p j j)
    rw [c3RefinedTrace_reference_curvature_eq_neg_mixed
      g z hg hNormal hFirst hHermG p j]
    simp
  change (∑ p : Fin n, ∑ j : Fin n, H j p / lam p) =
      (∑ p, Gjet p) + (∑ p, Q p) - (∑ p, ∑ j, Curv p j)
  exact c3RefinedTrace_determinant_sum_glue lam H Gm Curv Q Hlog Glog Gjet
    hGjet hHlog hGlog hCurv

end KahlerForm
