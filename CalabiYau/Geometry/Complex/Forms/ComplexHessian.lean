module

public import CalabiYau.Geometry.Complex.Basic
public import CalabiYau.Geometry.Complex.Forms.OneOne

import Mathlib.Analysis.Calculus.TaylorIntegral
import CalabiYau.Mathlib.Analysis.Complex.Holomorphic.ContDiff
import CalabiYau.Geometry.Complex.Forms.ComplexHessian.ComplexLineHarmonic
import CalabiYau.Geometry.Complex.Forms.ComplexHessian.StrongMaximum

/-!
# The operator `i∂∂̄` on functions

For a real function `f` on `ℂⁿ`, `ddbar f z` is the real `(1,1)`-form `i∂∂̄f` at `z`. It is defined
without any `(p,q)`-form calculus as `i∂∂̄f = ½ d(dᶜf)` with `dᶜf = -df ∘ J`, i.e.

  `ddbar f = -½ d (df ∘ J)`,

using Mathlib's `extDeriv`. For `f` of class `C²` this is
`(u, v) ↦ ½ (D²f(Ju, v) - D²f(u, Jv))` (`ddbar_apply`), its coefficient matrix is the complex
Hessian `f_{jk̄} = ∂²f/∂zⱼ∂z̄ₖ` (`coeffMatrix_ddbar`), and for `f = ‖z‖²` it is the Euclidean
Kähler form `i ∑ dzⱼ ∧ dz̄ⱼ` (`complexHessian_normSq`).

On a complex manifold `M`, `mddbar n φ x` is `ddbar` of `φ` read in the chart at `x`, evaluated at
the centre of the chart (as `mfderiv` is defined from `fderiv`). Since holomorphic changes of
coordinates commute with `i∂∂̄` (`ddbar_comp_holomorphic`), `mddbar n φ` is computed by `ddbar` in
every chart (`chartRep_mddbar`).

## Declarations

* `ddbar`, `complexHessian`: `i∂∂̄f` and `(f_{jk̄})` on `ℂⁿ`.
* `mddbar`, `mdWedgeDBar`: `i∂∂̄φ` and `i∂φ ∧ ∂̄φ` on a complex manifold.
-/

@[expose] public section

open scoped Manifold ContDiff Topology
open Complex Set Filter ContinuousAlternatingMap

variable {n : ℕ}

/-- `i∂∂̄f` at `z`, as a real `(1,1)`-form: `-½ d(df ∘ J)`. -/
noncomputable def ddbar (f : EuclideanSpace ℂ (Fin n) → ℝ) (z : EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ :=
  -(1 / 2 : ℝ) • extDeriv (fun w ↦ ofSubsingleton ℝ (EuclideanSpace ℂ (Fin n)) ℝ (0 : Fin 1)
    ((fderiv ℝ f w).comp (EuclideanSpace.complexStructure n))) z

/-- The complex Hessian `(∂²f/∂zⱼ∂z̄ₖ)`, the coefficient matrix of `i∂∂̄f`. -/
noncomputable def complexHessian (f : EuclideanSpace ℂ (Fin n) → ℝ)
    (z : EuclideanSpace ℂ (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  (ddbar f z).coeffMatrix

section VectorSpace

variable {f g : EuclideanSpace ℂ (Fin n) → ℝ} {z : EuclideanSpace ℂ (Fin n)}

theorem ddbar_apply (hf : ContDiffAt ℝ 2 f z) (u v : EuclideanSpace ℂ (Fin n)) :
    ddbar f z ![u, v] =
      (fderiv ℝ (fderiv ℝ f) z (I • u) v - fderiv ℝ (fderiv ℝ f) z u (I • v)) / 2 := by
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ f) z :=
    hf.fderiv_right (m := 1) (by norm_num)
  let L : (EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) ≃ₗᵢ[ℝ]
      (EuclideanSpace ℂ (Fin n) [⋀^Fin 1]→L[ℝ] ℝ) :=
    ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)
  have hω : DifferentiableAt ℝ
      (fun w ↦ ofSubsingleton ℝ (EuclideanSpace ℂ (Fin n)) ℝ (0 : Fin 1)
        ((fderiv ℝ f w).comp (EuclideanSpace.complexStructure n))) z := by
    have hfd' : DifferentiableAt ℝ (fderiv ℝ f) z := hfd.differentiableAt (by norm_num)
    have hcomp : DifferentiableAt ℝ
        (fun w ↦ (fderiv ℝ f w).comp (EuclideanSpace.complexStructure n)) z := by
      fun_prop
    change DifferentiableAt ℝ (fun w ↦ L ((fderiv ℝ f w).comp (EuclideanSpace.complexStructure n))) z
    exact L.toContinuousLinearMap.differentiableAt.comp z hcomp
  have hfd' : DifferentiableAt ℝ (fderiv ℝ f) z := hfd.differentiableAt (by norm_num)
  have hEvalFderiv (b : Fin 1 → EuclideanSpace ℂ (Fin n))
      (a : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦
        (ofSubsingleton ℝ (EuclideanSpace ℂ (Fin n)) ℝ (0 : Fin 1)
          ((fderiv ℝ f w).comp (EuclideanSpace.complexStructure n))) b) z a =
        fderiv ℝ (fderiv ℝ f) z a (I • b 0) := by
    have hEval : (fun w ↦
        (ofSubsingleton ℝ (EuclideanSpace ℂ (Fin n)) ℝ (0 : Fin 1)
          ((fderiv ℝ f w).comp (EuclideanSpace.complexStructure n))) b) =
        (fun w ↦ fderiv ℝ f w (I • b 0)) := by
      funext w
      simp [EuclideanSpace.complexStructure]
    rw [hEval, fderiv_clm_apply hfd' (differentiableAt_const _)]
    simp
  rw [ddbar, ContinuousAlternatingMap.smul_apply, extDeriv_apply hω]
  simp only [hEvalFderiv]
  simp [Fin.sum_univ_two, Fin.removeNth]
  have hsymm := hf.isSymmSndFDerivAt (by norm_num [minSmoothness])
  rw [hsymm v (I • u)]
  ring

theorem isOneOne_ddbar (hf : ContDiffAt ℝ 2 f z) : (ddbar f z).IsOneOne := by
  intro u v
  rw [ddbar_apply hf (I • u) (I • v), ddbar_apply hf u v]
  simp [smul_smul]
  ring

/-- The coefficients of `i∂∂̄f` are
`∂²f/∂zⱼ∂z̄ₖ = ¼ (f_{xⱼxₖ} + f_{yⱼyₖ} + i (f_{xⱼyₖ} - f_{yⱼxₖ}))`. -/
theorem complexHessian_apply (hf : ContDiffAt ℝ 2 f z) (j k : Fin n) :
    complexHessian f z j k =
      ((fderiv ℝ (fderiv ℝ f) z (EuclideanSpace.single j 1) (EuclideanSpace.single k 1) : ℂ) +
        fderiv ℝ (fderiv ℝ f) z (I • EuclideanSpace.single j 1) (I • EuclideanSpace.single k 1) +
        I * (fderiv ℝ (fderiv ℝ f) z (EuclideanSpace.single j 1) (I • EuclideanSpace.single k 1) -
          fderiv ℝ (fderiv ℝ f) z (I • EuclideanSpace.single j 1) (EuclideanSpace.single k 1))) /
        4 := by
  simp only [complexHessian, ContinuousAlternatingMap.coeffMatrix, Matrix.of_apply]
  rw [ddbar_apply hf, ddbar_apply hf]
  simp [smul_smul]
  ring

/-- Normalization: `i∂∂̄‖z‖² = i ∑ dzⱼ ∧ dz̄ⱼ` has coefficient matrix `1`. -/
theorem complexHessian_normSq (z : EuclideanSpace ℂ (Fin n)) :
    complexHessian (fun w ↦ ‖w‖ ^ 2) z = 1 := by
  let : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin n)) :=
    InnerProductSpace.rclikeToReal ℂ (EuclideanSpace ℂ (Fin n))
  have hf : ContDiffAt ℝ 2 (fun w : EuclideanSpace ℂ (Fin n) ↦ ‖w‖ ^ 2) z := by
    exact contDiffAt_id.norm_sq ℝ
  have hH (a b : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fderiv ℝ (fun w : EuclideanSpace ℂ (Fin n) ↦ ‖w‖ ^ 2)) z a b =
        2 * inner ℝ a b := by
    rw [fderiv_norm_sq]
    rw [fderiv_const_smul (innerSL ℝ).differentiableAt 2]
    rw [(innerSL ℝ).hasFDerivAt.fderiv]
    change (2 • (innerSL ℝ a)) b = 2 * inner ℝ a b
    rw [_root_.smul_apply, innerSL_apply_apply]
    simp
  ext j k
  rw [complexHessian_apply hf, hH, hH, hH, hH]
  simp [real_inner_eq_re_inner ℂ, EuclideanSpace.inner_single_right, inner_smul_left, inner_smul_right, Matrix.one_apply]
  by_cases h : j = k
  · subst k
    simp [I_re]
    norm_num
  · have hk : k ≠ j := fun hkj ↦ h hkj.symm
    simp [h, hk]

theorem ddbar_add (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    ddbar (f + g) z = ddbar f z + ddbar g z := by
  have hf' : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hg' : DifferentiableAt ℝ (fderiv ℝ g) z :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hfirst : fderiv ℝ (fun w ↦ f w + g w) =ᶠ[𝓝 z] fderiv ℝ f + fderiv ℝ g := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with w hwf hwg
    change fderiv ℝ (f + g) w = (fderiv ℝ f + fderiv ℝ g) w
    rw [fderiv_add (hwf.differentiableAt (by norm_num)) (hwg.differentiableAt (by norm_num))]
    rfl
  have hsecond (a b : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fderiv ℝ (fun w ↦ f w + g w)) z a b =
        fderiv ℝ (fderiv ℝ f) z a b + fderiv ℝ (fderiv ℝ g) z a b := by
    rw [hfirst.fderiv_eq, fderiv_add hf' hg']
    rfl
  ext u
  have hu : u = ![u 0, u 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hu]
  change ddbar (fun w ↦ f w + g w) z ![u 0, u 1] =
    (ddbar f z + ddbar g z) ![u 0, u 1]
  rw [ContinuousAlternatingMap.add_apply]
  rw [ddbar_apply (hf.add hg) (u 0) (u 1), ddbar_apply hf (u 0) (u 1),
    ddbar_apply hg (u 0) (u 1), hsecond (I • u 0) (u 1), hsecond (u 0) (I • u 1)]
  ring

theorem ddbar_smul (hf : ContDiffAt ℝ 2 f z) (c : ℝ) : ddbar (c • f) z = c • ddbar f z := by
  have hf' : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hfirst : fderiv ℝ (fun w ↦ c • f w) =ᶠ[𝓝 z] fun w ↦ c • fderiv ℝ f w := by
    filter_upwards [hf.eventually (by norm_num)] with w hw
    change fderiv ℝ (fun y ↦ c • f y) w = c • fderiv ℝ f w
    rw [fderiv_fun_const_smul (hw.differentiableAt (by norm_num)) c]
  have hsecond (a b : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fderiv ℝ (fun w ↦ c • f w)) z a b =
        c * fderiv ℝ (fderiv ℝ f) z a b := by
    rw [hfirst.fderiv_eq, fderiv_fun_const_smul hf' c]
    rfl
  ext u
  have hu : u = ![u 0, u 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hu]
  change ddbar (fun w ↦ c • f w) z ![u 0, u 1] = c • ddbar f z ![u 0, u 1]
  rw [ddbar_apply (hf.const_smul c) (u 0) (u 1), ddbar_apply hf (u 0) (u 1),
    hsecond (I • u 0) (u 1), hsecond (u 0) (I • u 1)]
  ring

theorem ddbar_sub (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    ddbar (f - g) z = ddbar f z - ddbar g z := by
  rw [sub_eq_add_neg]
  change ddbar (f + (fun x ↦ -g x)) z = ddbar f z - ddbar g z
  rw [ddbar_add hf hg.neg]
  have hneg : ddbar (-g) z = -ddbar g z := by
    rw [show -g = (-1 : ℝ) • g by ext x; simp, ddbar_smul hg]
    exact neg_one_smul ℝ (ddbar g z)
  change ddbar f z + ddbar (-g) z = ddbar f z - ddbar g z
  rw [hneg]
  simp [sub_eq_add_neg]

@[simp]
theorem ddbar_const (c : ℝ) : ddbar (fun _ : EuclideanSpace ℂ (Fin n) ↦ c) z = 0 := by
  simp [ddbar, extDeriv]
  exact map_zero _

@[simp]
theorem ddbar_add_const (c : ℝ) : ddbar (fun w ↦ f w + c) z = ddbar f z := by
  simp [ddbar, fderiv_add_const]

/-- `i∂∂̄` commutes with holomorphic changes of coordinates. -/
theorem ddbar_comp_holomorphic {ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)}
    (hψ : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ ψ w) (hf : ContDiffAt ℝ 2 f (ψ z)) :
    ddbar (f ∘ ψ) z =
      (ddbar f (ψ z)).compContinuousLinearMap ((fderiv ℂ ψ z).restrictScalars ℝ) := by
  have hψC2 : ContDiffAt ℝ 2 ψ z := by
    obtain ⟨s, hs, hψs⟩ := Filter.Eventually.exists_mem hψ
    obtain ⟨U, hUs, hU, hzU⟩ := mem_nhds_iff.mp hs
    have hψU : DifferentiableOn ℂ ψ U := fun w hw ↦
      (hψs w (hUs hw)).differentiableWithinAt
    exact Complex.differentiableOn_contDiffAt_real_two hU hzU hψU
  have hψ' : DifferentiableAt ℝ (fderiv ℝ ψ) z :=
    (hψC2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hf' : DifferentiableAt ℝ (fderiv ℝ f) (ψ z) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hψ0 : DifferentiableAt ℝ ψ z := hψC2.differentiableAt (by norm_num)
  let c : EuclideanSpace ℂ (Fin n) →
      EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ := fun w ↦ fderiv ℝ f (ψ w)
  let d : EuclideanSpace ℂ (Fin n) →
      EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) := fun w ↦ fderiv ℝ ψ w
  have hc : DifferentiableAt ℝ c z := hf'.comp z hψ0
  have hd : DifferentiableAt ℝ d z := hψ'
  have hψev : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ 2 ψ w :=
    hψC2.eventually (by norm_num)
  have hfpre : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ 2 f (ψ w) := by
    exact hψC2.continuousAt.preimage_mem_nhds (hf.eventually (by norm_num))
  have hfirst : fderiv ℝ (f ∘ ψ) =ᶠ[𝓝 z] fun w ↦ (c w).comp (d w) := by
    filter_upwards [hψev, hfpre] with w hψw hfw
    simpa [c, d] using
      (fderiv_comp (f := ψ) (g := f) (x := w)
        (hfw.differentiableAt (by norm_num)) (hψw.differentiableAt (by norm_num)))
  have hcderiv : fderiv ℝ c z = (fderiv ℝ (fderiv ℝ f) (ψ z)).comp (fderiv ℝ ψ z) := by
    dsimp [c]
    exact fderiv_comp (f := ψ) (g := fderiv ℝ f) (x := z) hf' hψ0
  have hsecond (a b : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fderiv ℝ (f ∘ ψ)) z a b =
        fderiv ℝ (fderiv ℝ f) (ψ z) (fderiv ℝ ψ z a) (fderiv ℝ ψ z b) +
          fderiv ℝ f (ψ z) (fderiv ℝ (fderiv ℝ ψ) z a b) := by
    rw [hfirst.fderiv_eq, fderiv_clm_comp hc hd, hcderiv]
    simp [c, d, ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.comp_apply]
    rw [show (fun w : EuclideanSpace ℂ (Fin n) ↦ fderiv ℝ ψ w) = fderiv ℝ ψ by
      funext w
      rfl]
    ring
  have hψz : DifferentiableAt ℂ ψ z := hψ.self_of_nhds
  have hψzR : fderiv ℝ ψ z = (fderiv ℂ ψ z).restrictScalars ℝ :=
    hψz.fderiv_restrictScalars ℝ
  let J : EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) :=
    EuclideanSpace.complexStructure n
  have hψJ (b : EuclideanSpace ℂ (Fin n)) :
      (fun w ↦ fderiv ℝ ψ w (J b)) =ᶠ[𝓝 z]
        (fun w ↦ J (fderiv ℝ ψ w b)) := by
    filter_upwards [hψ] with w hw
    rw [hw.fderiv_restrictScalars ℝ]
    change (fderiv ℂ ψ w) ((Complex.I : ℂ) • b) =
      (Complex.I : ℂ) • (fderiv ℂ ψ w b)
    exact (fderiv ℂ ψ w).map_smul Complex.I b
  have hψEval (a b : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ fderiv ℝ ψ w b) z a = fderiv ℝ (fderiv ℝ ψ) z a b := by
    rw [fderiv_clm_apply hψ' (differentiableAt_const b)]
    simp
  have hψEvalJ (a b : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ J (fderiv ℝ ψ w b)) z a =
        J (fderiv ℝ (fderiv ℝ ψ) z a b) := by
    have hinner : DifferentiableAt ℝ (fun w ↦ fderiv ℝ ψ w b) z :=
      hψ'.clm_apply (differentiableAt_const b)
    change fderiv ℝ (J ∘
      (fun w ↦ fderiv ℝ ψ w b)) z a = _
    rw [fderiv_comp (f := fun w ↦ fderiv ℝ ψ w b)
      (g := J) (x := z) J.differentiableAt hinner]
    rw [J.hasFDerivAt.fderiv]
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg J (hψEval a b)
  have hJapply (b : EuclideanSpace ℂ (Fin n)) :
      J b = (Complex.I : ℂ) • b := by
    rfl
  have hψHessJ (a : EuclideanSpace ℂ (Fin n)) :
      (fderiv ℝ (fderiv ℝ ψ) z a).comp J =
        J.comp (fderiv ℝ (fderiv ℝ ψ) z a) := by
    apply ContinuousLinearMap.ext
    intro b
    have hpoint := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ]
        EuclideanSpace ℂ (Fin n) ↦ L a) (hψJ b).fderiv_eq
    rw [hψEval a (J b), hψEvalJ a b] at hpoint
    exact hpoint
  have hψlinear (a b : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fderiv ℝ ψ) z a (J b) =
        J (fderiv ℝ (fderiv ℝ ψ) z a b) := by
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ]
        EuclideanSpace ℂ (Fin n) ↦ L b) (hψHessJ a)
  have hψsymm := hψC2.isSymmSndFDerivAt (by norm_num)
  have hψcancel (u v : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fderiv ℝ ψ) z (J u) v =
        fderiv ℝ (fderiv ℝ ψ) z u (J v) := by
    calc
      fderiv ℝ (fderiv ℝ ψ) z (J u) v =
          fderiv ℝ (fderiv ℝ ψ) z v (J u) := by rw [hψsymm]
      _ = J (fderiv ℝ (fderiv ℝ ψ) z v u) := hψlinear v u
      _ = J (fderiv ℝ (fderiv ℝ ψ) z u v) := by rw [hψsymm]
      _ = fderiv ℝ (fderiv ℝ ψ) z u (J v) := (hψlinear u v).symm
  have hψcomm (v : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ ψ z (J v) = J (fderiv ℝ ψ z v) := by
    rw [hψzR, hJapply v, hJapply ((fderiv ℂ ψ z).restrictScalars ℝ v)]
    change (fderiv ℂ ψ z) ((Complex.I : ℂ) • v) =
      (Complex.I : ℂ) • (fderiv ℂ ψ z v)
    exact (fderiv ℂ ψ z).map_smul Complex.I v
  have hψcommI (v : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ ψ z (I • v) = I • fderiv ℝ ψ z v := by
    calc
      fderiv ℝ ψ z (I • v) = fderiv ℝ ψ z (J v) := by rw [hJapply]
      _ = J (fderiv ℝ ψ z v) := hψcomm v
      _ = I • fderiv ℝ ψ z v := hJapply _
  have hψcancelI (u v : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fderiv ℝ ψ) z (I • u) v =
        fderiv ℝ (fderiv ℝ ψ) z u (I • v) := by
    rw [← hJapply u, ← hJapply v]
    exact hψcancel u v
  have hcompC2 : ContDiffAt ℝ 2 (f ∘ ψ) z := hf.comp z hψC2
  ext u
  have hu : u = ![u 0, u 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hu]
  change ddbar (f ∘ ψ) z ![u 0, u 1] =
    ((ddbar f (ψ z)).compContinuousLinearMap ((fderiv ℂ ψ z).restrictScalars ℝ))
      ![u 0, u 1]
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  have htuple : (fderiv ℂ ψ z).restrictScalars ℝ ∘ ![u 0, u 1] =
      ![(fderiv ℂ ψ z).restrictScalars ℝ (u 0),
        (fderiv ℂ ψ z).restrictScalars ℝ (u 1)] := by
    funext i
    fin_cases i <;> rfl
  rw [htuple, ddbar_apply hcompC2, ddbar_apply hf,
    hsecond (I • u 0) (u 1), hsecond (u 0) (I • u 1), ← hψzR,
    hψcommI (u 0), hψcommI (u 1), hψcancelI (u 0) (u 1)]
  ring

/-- Chain rule: `i∂∂̄(h ∘ f) = h'(f) i∂∂̄f + h''(f) i∂f ∧ ∂̄f`. -/
theorem ddbar_comp_real {h : ℝ → ℝ} (hh : ContDiffAt ℝ 2 h (f z)) (hf : ContDiffAt ℝ 2 f z) :
    ddbar (h ∘ f) z = deriv h (f z) • ddbar f z +
      deriv (deriv h) (f z) • dWedgeDBar (fderiv ℝ f z) := by
  have hf' : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hh' : DifferentiableAt ℝ (fderiv ℝ h) (f z) :=
    (hh.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hf0 : DifferentiableAt ℝ f z := hf.differentiableAt (by norm_num)
  let c : EuclideanSpace ℂ (Fin n) → ℝ →L[ℝ] ℝ := fun w ↦ fderiv ℝ h (f w)
  let d : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ := fun w ↦
    fderiv ℝ f w
  have hc : DifferentiableAt ℝ c z := by
    exact hh'.comp z hf0
  have hd : DifferentiableAt ℝ d z := hf'
  have hcderiv : fderiv ℝ c z =
      (fderiv ℝ (fderiv ℝ h) (f z)).comp (fderiv ℝ f z) := by
    dsimp [c]
    exact fderiv_comp (f := f) (g := fderiv ℝ h) (x := z) hh' hf0
  have hhpre : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ 2 h (f w) := by
    filter_upwards [hf.continuousAt.preimage_mem_nhds (hh.eventually (by norm_num))] with w hw
    change ContDiffAt ℝ 2 h (f w) at hw
    exact hw
  have hfirst : fderiv ℝ (h ∘ f) =ᶠ[𝓝 z] fun w ↦ (c w).comp (d w) := by
    filter_upwards [hf.eventually (by norm_num), hhpre] with w hwf hhw
    simpa [c, d] using
      (fderiv_comp (f := f) (g := h) (x := w) (hhw.differentiableAt (by norm_num))
        (hwf.differentiableAt (by norm_num)))
  have hderiv_diff : DifferentiableAt ℝ (deriv h) (f z) := by
    change DifferentiableAt ℝ (fun y ↦ fderiv ℝ h y 1) (f z)
    exact hh'.clm_apply (differentiableAt_const _)
  have hcompC2 : ContDiffAt ℝ 2 (h ∘ f) z := hh.comp z hf
  have hHessh (r s : ℝ) :
      fderiv ℝ (fderiv ℝ h) (f z) r s = deriv (deriv h) (f z) * r * s := by
    have hEval :
        fderiv ℝ (fun y : ℝ ↦ fderiv ℝ h y s) (f z) r =
          fderiv ℝ (fderiv ℝ h) (f z) r s := by
      rw [fderiv_clm_apply hh' (differentiableAt_const s)]
      simp
    have hEvalFun : (fun y : ℝ ↦ fderiv ℝ h y s) = (fun y ↦ deriv h y * s) := by
      funext y
      exact fderiv_eq_deriv_mul
    calc
      fderiv ℝ (fderiv ℝ h) (f z) r s =
          fderiv ℝ (fun y : ℝ ↦ fderiv ℝ h y s) (f z) r := hEval.symm
      _ = fderiv ℝ (fun y : ℝ ↦ deriv h y * s) (f z) r := by
        rw [hEvalFun]
      _ = deriv (deriv h) (f z) * r * s := by
        rw [fderiv_mul_const hderiv_diff s]
        rw [_root_.smul_apply, fderiv_eq_deriv_mul]
        ring
  have hderiv2_apply (s : ℝ) :
      deriv (fderiv ℝ h) (f z) s = deriv (deriv h) (f z) * s := by
    rw [← fderiv_apply_one_eq_deriv, hHessh]
    simp
  have hHcomp (a b : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fderiv ℝ (h ∘ f)) z a b =
        deriv h (f z) * fderiv ℝ (fderiv ℝ f) z a b +
          deriv (deriv h) (f z) * (fderiv ℝ f z a) * (fderiv ℝ f z b) := by
    rw [hfirst.fderiv_eq, fderiv_clm_comp hc hd, hcderiv]
    simp [ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]
    simp [c, d, hderiv2_apply, mul_comm, mul_left_comm]
  ext u
  have hu : u = ![u 0, u 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hu]
  change ddbar (h ∘ f) z ![u 0, u 1] =
    (deriv h (f z) • ddbar f z +
      deriv (deriv h) (f z) • dWedgeDBar (fderiv ℝ f z)) ![u 0, u 1]
  rw [ddbar_apply hcompC2 (u 0) (u 1), ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.smul_apply,
    ddbar_apply hf (u 0) (u 1), hHcomp (I • u 0) (u 1), hHcomp (u 0) (I • u 1)]
  have hwedge : (dWedgeDBar (fderiv ℝ f z)) ![u 0, u 1] =
      (fderiv ℝ f z (I • u 0) * fderiv ℝ f z (u 1) -
        fderiv ℝ f z (I • u 1) * fderiv ℝ f z (u 0)) / 2 := by
    let ℓ := fderiv ℝ f z
    change ((1 / 2 : ℝ) • ContinuousAlternatingMap.alternatizeUncurryFin
      ((ℓ.comp (Complex.I • ContinuousLinearMap.id ℝ
        (EuclideanSpace ℂ (Fin n)))).smulRight
        (ofSubsingleton ℝ (EuclideanSpace ℂ (Fin n)) ℝ (0 : Fin 1) ℓ)))
      ![u 0, u 1] = _
    simp [ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.removeNth]
    ring
  rw [hwedge]
  ring

/-- At a local maximum, `-i∂∂̄f ≥ 0`. -/
theorem isNonneg_neg_ddbar_of_isLocalMax (hf : ContDiffAt ℝ 2 f z) (hmax : IsLocalMax f z) :
    (-ddbar f z).IsNonneg := by
  have hquad (v : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fderiv ℝ f) z v v ≤ 0 := by
    let line : ℝ → EuclideanSpace ℂ (Fin n) := fun t ↦ z + t • v
    let g : ℝ → ℝ := f ∘ line
    have hlineC : ContDiff ℝ ∞ line := by
      fun_prop
    have hline : ContDiffAt ℝ 2 line 0 := by
      exact hlineC.contDiffAt.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
    have hg : ContDiffAt ℝ 2 g 0 := by
      exact hf.comp_contDiffWithinAt_of_eq 0 hline.contDiffWithinAt (by simp [line])
    have hlineCont : ContinuousAt line 0 := hline.continuousAt
    have hlineTendsto : Tendsto line (𝓝 (0 : ℝ)) (𝓝 z) := by
      simpa [line] using hlineCont.tendsto
    have hgmax : IsLocalMax g 0 := by
      change ∀ᶠ t in 𝓝 (0 : ℝ), g t ≤ g 0
      have h := hlineTendsto.eventually hmax
      simpa [g, line] using h
    have hderivZero : deriv g 0 = 0 := hgmax.deriv_eq_zero
    have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), ContDiffAt ℝ 2 f (z + t • v) := by
      exact hlineTendsto.eventually (hf.eventually (by norm_num))
    have hgDeriv : deriv g =ᶠ[𝓝 (0 : ℝ)] fun t ↦ fderiv ℝ f (z + t • v) v := by
      filter_upwards [hnear] with t ht
      change deriv (fun s : ℝ ↦ f (z + s • v)) t = _
      exact (ht.differentiableAt (by norm_num)).deriv_comp_add_smul
    have hsecond : deriv (deriv g) 0 = fderiv ℝ (fderiv ℝ f) z v v := by
      rw [hgDeriv.deriv_eq]
      have hfx : ContDiffAt ℝ 2 f (z + (0 : ℝ) • v) := by simpa using hf
      simpa [iteratedFDeriv_one_apply, iteratedFDeriv_two_apply] using
        (hfx.deriv_fderiv_add_smul (𝕜 := ℝ) (n := 1) (x := z) (y := v) (t := (0 : ℝ)))
    by_contra hnot
    have hpos : 0 < deriv (deriv g) 0 := lt_of_not_ge hnot |>.trans_eq hsecond.symm
    have hhas : HasDerivAt (deriv g) (deriv (deriv g) 0) 0 :=
      (differentiableAt_of_deriv_ne_zero (ne_of_gt hpos)).hasDerivAt
    have hposSlope : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        0 < t⁻¹ • (deriv g (0 + t) - deriv g 0) := by
      exact hhas.tendsto_slope_zero_right.eventually (isOpen_Ioi.mem_nhds hpos)
    have hderivPos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < deriv g t := by
      filter_upwards [hposSlope, eventually_mem_nhdsWithin] with t ht hmem
      have htpos : 0 < t := hmem
      have hmul : 0 < t⁻¹ * deriv g t := by
        simpa [hderivZero, smul_eq_mul] using ht
      exact (mul_pos_iff_of_pos_left (inv_pos.mpr htpos)).mp hmul
    obtain ⟨rP, hrP, hposBall⟩ := Metric.mem_nhdsWithin_iff.mp hderivPos
    obtain ⟨U, hU, hfU⟩ := hf.contDiffOn (m := (2 : ℕ∞ω)) le_rfl (by simp)
    have hlinePre : line ⁻¹' U ∈ 𝓝 (0 : ℝ) :=
      hlineTendsto.eventually hU
    obtain ⟨rU, hrU, hlineBall⟩ := Metric.mem_nhds_iff.mp hlinePre
    have hmaxSet : {t : ℝ | g t ≤ g 0} ∈ 𝓝 (0 : ℝ) := hgmax
    obtain ⟨rM, hrM, hmaxBall⟩ := Metric.mem_nhds_iff.mp hmaxSet
    let δ : ℝ := min rU (min rP rM) / 2
    have hδpos : 0 < δ := by positivity
    have hminNonneg : 0 ≤ min rU (min rP rM) := le_min hrU.le (le_min hrP.le hrM.le)
    have hδU : δ < rU := by dsimp [δ]; nlinarith [min_le_left rU (min rP rM), hminNonneg]
    have hδP : δ < rP := by
      dsimp [δ]
      have hminP : min rU (min rP rM) ≤ rP :=
        le_trans (min_le_right rU (min rP rM)) (min_le_left rP rM)
      nlinarith [hminP, hminNonneg]
    have hδM : δ < rM := by
      dsimp [δ]
      have hminM : min rU (min rP rM) ≤ rM :=
        le_trans (min_le_right rU (min rP rM)) (min_le_right rP rM)
      nlinarith [hminM, hminNonneg]
    have hsubset : Icc (0 : ℝ) δ ⊆ line ⁻¹' U := by
      intro t ht
      have hball : t ∈ Metric.ball (0 : ℝ) rU := by
        rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg ht.1]
        exact lt_of_le_of_lt ht.2 hδU
      exact hlineBall hball
    have hlineOn : ContDiffOn ℝ 2 line (line ⁻¹' U) :=
      (hlineC.contDiffOn.of_le
        (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))).mono (Set.subset_univ _)
    have hgOn : ContDiffOn ℝ 2 g (line ⁻¹' U) := by
      change ContDiffOn ℝ 2 (f ∘ line) (line ⁻¹' U)
      exact hfU.comp hlineOn (by intro t ht; exact ht)
    have hcont : ContinuousOn g (Icc (0 : ℝ) δ) := hgOn.continuousOn.mono hsubset
    have hderivPosOn : ∀ t ∈ interior (Icc (0 : ℝ) δ), 0 < deriv g t := by
      intro t ht
      have ht' : t ∈ Ioo (0 : ℝ) δ := by simpa [interior_Icc] using ht
      have hball : t ∈ Metric.ball (0 : ℝ) rP := by
        rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (le_of_lt ht'.1)]
        exact lt_trans ht'.2 hδP
      exact hposBall ⟨hball, ht'.1⟩
    have hstrict : StrictMonoOn g (Icc (0 : ℝ) δ) :=
      strictMonoOn_of_deriv_pos (convex_Icc _ _) hcont hderivPosOn
    have hzero : (0 : ℝ) ∈ Icc 0 δ := ⟨le_rfl, le_of_lt hδpos⟩
    have hhalf : δ / 2 ∈ Icc (0 : ℝ) δ := by constructor <;> linarith
    have hinc : g 0 < g (δ / 2) := hstrict hzero hhalf (by linarith [hδpos])
    have hhalfBall : δ / 2 ∈ Metric.ball (0 : ℝ) rM := by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (by linarith [hδpos])]
      exact lt_trans (by linarith [hδpos]) hδM
    have hmaxHalf := hmaxBall hhalfBall
    change g (δ / 2) ≤ g 0 at hmaxHalf
    linarith
  constructor
  · intro u v
    simp only [ContinuousAlternatingMap.neg_apply]
    exact congrArg Neg.neg (isOneOne_ddbar hf u v)
  · intro v
    rw [ContinuousAlternatingMap.neg_apply, ddbar_apply hf v (I • v)]
    have hI2 : I • (I • v) = -v := by
      simp [smul_smul, Complex.I_mul_I]
    rw [hI2]
    have h₁ := hquad v
    have h₂ := hquad (I • v)
    simp only [ContinuousLinearMap.map_neg]
    nlinarith

/-- At a local minimum, `i∂∂̄f ≥ 0`. -/
theorem isNonneg_ddbar_of_isLocalMin (hf : ContDiffAt ℝ 2 f z) (hmin : IsLocalMin f z) :
    (ddbar f z).IsNonneg := by
  have hneg : ContDiffAt ℝ 2 (-f) z := hf.neg
  have hmax : IsLocalMax (-f) z := by
    change ∀ᶠ w in 𝓝 z, -f w ≤ -f z
    filter_upwards [hmin] with w hw
    exact neg_le_neg hw
  have hddbar : ddbar (-f) z = -ddbar f z := by
    rw [show -f = (-1 : ℝ) • f by ext w; simp, ddbar_smul hf]
    exact neg_one_smul ℝ (ddbar f z)
  have hresult := isNonneg_neg_ddbar_of_isLocalMax hneg hmax
  simpa [hddbar] using hresult

theorem ContDiffOn.ddbar {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) : ContDiffOn ℝ ∞ (ddbar f) U := by
  have h_inf : (∞ : ℕ∞ω) + 1 ≤ ∞ :=
    le_of_eq (show (∞ : ℕ∞ω) = ∞ + 1 from rfl).symm
  let η : EuclideanSpace ℂ (Fin n) →
      EuclideanSpace ℂ (Fin n) [⋀^Fin 1]→L[ℝ] ℝ := fun w ↦
    ofSubsingleton ℝ (EuclideanSpace ℂ (Fin n)) ℝ (0 : Fin 1)
      ((fderiv ℝ f w).comp (EuclideanSpace.complexStructure n))
  have hfd : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU h_inf
  let L : (EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) →L[ℝ]
      (EuclideanSpace ℂ (Fin n) [⋀^Fin 1]→L[ℝ] ℝ) :=
    (ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).toContinuousLinearMap
  have hcomp : ContDiffOn ℝ ∞
      (fun w ↦ (fderiv ℝ f w).comp (EuclideanSpace.complexStructure n)) U := by
    fun_prop
  have hη : ContDiffOn ℝ ∞ η U := by
    change ContDiffOn ℝ ∞
      (fun w ↦ L ((fderiv ℝ f w).comp (EuclideanSpace.complexStructure n))) U
    exact hcomp.continuousLinearMap_comp L
  have hη' : ContDiffOn ℝ ∞ (fun w ↦ extDeriv η w) U := by
    have hderiv : ContDiffOn ℝ ∞ (fderiv ℝ η) U := hη.fderiv_of_isOpen hU h_inf
    change ContDiffOn ℝ ∞
      (fun w ↦ alternatizeUncurryFinCLM ℝ (EuclideanSpace ℂ (Fin n)) ℝ (fderiv ℝ η w)) U
    exact hderiv.continuousLinearMap_comp
      (alternatizeUncurryFinCLM ℝ (EuclideanSpace ℂ (Fin n)) ℝ)
  change ContDiffOn ℝ ∞ (fun w ↦ -(1 / 2 : ℝ) • extDeriv η w) U
  exact hη'.const_smul _

end VectorSpace

/-! ### On a complex manifold -/

section Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
section

variable (n)


/-- `i∂∂̄φ` on a complex manifold, computed at each point in the chart centred there. -/
noncomputable def mddbar (φ : M → ℝ) : FormField (EuclideanSpace ℂ (Fin n)) M 2 := fun x ↦
  ddbar (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x)

/-- `i∂φ ∧ ∂̄φ` on a complex manifold, computed at each point in the chart centred there. -/
noncomputable def mdWedgeDBar (φ : M → ℝ) : FormField (EuclideanSpace ℂ (Fin n)) M 2 := fun x ↦
  dWedgeDBar (fderiv ℝ (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x))

end

variable  {φ ψ : M → ℝ}
section

variable [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] {φ ψ : M → ℝ}


/-- `mddbar φ` is computed by `ddbar` in every chart. -/
theorem chartRep_mddbar (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ φ) (x : M)
    {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    (mddbar n φ).chartRep x z =
      ddbar (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let y := e.symm z
  let e' := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y
  let ψ := e' ∘ e.symm
  have hyx : y ∈ e.source := e.map_target hz
  have hyy : y ∈ e'.source := mem_extChartAt_source y
  have hcommon : y ∈ e.source ∩ e'.source := ⟨hyx, hyy⟩
  have hz_eq : e y = z := e.right_inv hz
  have hderivR : tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y =
      fderiv ℝ ψ z := by
    rw [tangentCoordChange_def, hz_eq]
    simp [ψ, e, e']
  have hderivC : tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y =
      fderiv ℂ ψ z := by
    have hz_eqC : extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y = z := by
      simpa only [e, extChartAt_real_eq] using hz_eq
    rw [tangentCoordChange_def, hz_eqC]
    simp [ψ, e, e']
  have hrealComplex : fderiv ℝ ψ z = (fderiv ℂ ψ z).restrictScalars ℝ := by
    calc
      fderiv ℝ ψ z = tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y := hderivR.symm
      _ = (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y).restrictScalars ℝ :=
        tangentCoordChange_real_eq hcommon
      _ = (fderiv ℂ ψ z).restrictScalars ℝ := by rw [hderivC]
  have hsymmC : ContMDiffAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n))
      𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ e.symm z := by
    exact (contMDiffOn_extChartAt_symm (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n))) x).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz)
  have hchartC : ContMDiffAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n))
      𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ e' y :=
    contMDiffAt_extChartAt (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n))) (x := y)
  have hψC : ContMDiffAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n))
      𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ ψ z := by
    exact hchartC.comp_of_eq hsymmC rfl
  have hψcd : ContDiffAt ℂ ∞ ψ z := (contMDiffAt_iff_contDiffAt).mp hψC
  have hψ : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ ψ w := by
    have hψc1 : ContDiffAt ℂ 1 ψ z := hψcd.of_le (by norm_num)
    filter_upwards [hψc1.eventually (by norm_num)] with w hw
    exact hw.differentiableAt (by norm_num)
  have hφchart : ContDiffAt ℝ 2 (φ ∘ e'.symm) (e' y) := by
    have hsymm' : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
        𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ e'.symm (e' y) := by
      exact (contMDiffOn_extChartAt_symm y).contMDiffAt
        ((isOpen_extChartAt_target y).mem_nhds (mem_extChartAt_target y))
    have hcomp := (hφ y).comp_of_eq hsymm' (e'.left_inv hyy)
    exact ((contMDiffAt_iff_contDiffAt).mp hcomp).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hfsource : ∀ᶠ w in 𝓝 z, e.symm w ∈ e'.source := by
    exact (continuousAt_extChartAt_symm'' hz).preimage_mem_nhds
      ((isOpen_extChartAt_source y).mem_nhds hyy)
  have hfun : (φ ∘ e'.symm) ∘ ψ =ᶠ[𝓝 z] φ ∘ e.symm := by
    filter_upwards [hfsource] with w hw
    change φ (e'.symm (e' (e.symm w))) = φ (e.symm w)
    rw [e'.left_inv hw]
  have hddbarCongr {g₁ g₂ : EuclideanSpace ℂ (Fin n) → ℝ}
      (h : g₁ =ᶠ[𝓝 z] g₂) : ddbar g₁ z = ddbar g₂ z := by
    have hfd : fderiv ℝ g₁ =ᶠ[𝓝 z] fderiv ℝ g₂ := h.fderiv
    have hη : (fun w ↦ ofSubsingleton ℝ (EuclideanSpace ℂ (Fin n)) ℝ (0 : Fin 1)
        ((fderiv ℝ g₁ w).comp (EuclideanSpace.complexStructure n))) =ᶠ[𝓝 z]
        (fun w ↦ ofSubsingleton ℝ (EuclideanSpace ℂ (Fin n)) ℝ (0 : Fin 1)
          ((fderiv ℝ g₂ w).comp (EuclideanSpace.complexStructure n))) := by
      filter_upwards [hfd] with w hw
      rw [hw]
    simp only [ddbar]
    rw [Filter.EventuallyEq.extDeriv_eq hη]
  rw [FormField.chartRep_eq_chartRep_comp (α := mddbar n φ) hz hyy]
  rw [FormField.chartRep_self]
  change (ddbar (φ ∘ e'.symm) (e' y)).compContinuousLinearMap (fderiv ℝ ψ z) =
    ddbar (φ ∘ e.symm) z
  calc
    (ddbar (φ ∘ e'.symm) (e' y)).compContinuousLinearMap (fderiv ℝ ψ z) =
        (ddbar (φ ∘ e'.symm) (ψ z)).compContinuousLinearMap
          ((fderiv ℂ ψ z).restrictScalars ℝ) := by
      rw [hrealComplex]
      rfl
    _ = ddbar ((φ ∘ e'.symm) ∘ ψ) z :=
      (ddbar_comp_holomorphic hψ hφchart).symm
    _ = ddbar (φ ∘ e.symm) z := hddbarCongr hfun

/-- `C²` version of `chartRep_mddbar` (for the `C^{2,α}` solutions of the openness step). -/
theorem chartRep_mddbar_of_contMDiff_two
    (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 φ) (x : M)
    {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    (mddbar n φ).chartRep x z =
      ddbar (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let y := e.symm z
  let e' := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y
  let ψ := e' ∘ e.symm
  have hyx : y ∈ e.source := e.map_target hz
  have hyy : y ∈ e'.source := mem_extChartAt_source y
  have hcommon : y ∈ e.source ∩ e'.source := ⟨hyx, hyy⟩
  have hz_eq : e y = z := e.right_inv hz
  have hderivR : tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y =
      fderiv ℝ ψ z := by
    rw [tangentCoordChange_def, hz_eq]
    simp [ψ, e, e']
  have hderivC : tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y =
      fderiv ℂ ψ z := by
    have hz_eqC : extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y = z := by
      simpa only [e, extChartAt_real_eq] using hz_eq
    rw [tangentCoordChange_def, hz_eqC]
    simp [ψ, e, e']
  have hrealComplex : fderiv ℝ ψ z = (fderiv ℂ ψ z).restrictScalars ℝ := by
    calc
      fderiv ℝ ψ z = tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y := hderivR.symm
      _ = (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y).restrictScalars ℝ :=
        tangentCoordChange_real_eq hcommon
      _ = (fderiv ℂ ψ z).restrictScalars ℝ := by rw [hderivC]
  have hsymmC : ContMDiffAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n))
      𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ e.symm z := by
    exact (contMDiffOn_extChartAt_symm (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n))) x).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz)
  have hchartC : ContMDiffAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n))
      𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ e' y :=
    contMDiffAt_extChartAt (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n))) (x := y)
  have hψC : ContMDiffAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n))
      𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ ψ z := by
    exact hchartC.comp_of_eq hsymmC rfl
  have hψcd : ContDiffAt ℂ ∞ ψ z := (contMDiffAt_iff_contDiffAt).mp hψC
  have hψ : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ ψ w := by
    have hψc1 : ContDiffAt ℂ 1 ψ z := hψcd.of_le (by norm_num)
    filter_upwards [hψc1.eventually (by norm_num)] with w hw
    exact hw.differentiableAt (by norm_num)
  have hsymm' : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ e'.symm (e' y) := by
    exact (contMDiffOn_extChartAt_symm y).contMDiffAt
      ((isOpen_extChartAt_target y).mem_nhds (mem_extChartAt_target y))
  have hsymm2 : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 2 e'.symm (e' y) :=
    hsymm'.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hφchart : ContDiffAt ℝ 2 (φ ∘ e'.symm) (e' y) := by
    have hcomp := (hφ y).comp_of_eq hsymm2 (e'.left_inv hyy)
    exact (contMDiffAt_iff_contDiffAt).mp hcomp
  have hfsource : ∀ᶠ w in 𝓝 z, e.symm w ∈ e'.source := by
    exact (continuousAt_extChartAt_symm'' hz).preimage_mem_nhds
      ((isOpen_extChartAt_source y).mem_nhds hyy)
  have hfun : (φ ∘ e'.symm) ∘ ψ =ᶠ[𝓝 z] φ ∘ e.symm := by
    filter_upwards [hfsource] with w hw
    change φ (e'.symm (e' (e.symm w))) = φ (e.symm w)
    rw [e'.left_inv hw]
  have hddbarCongr {g₁ g₂ : EuclideanSpace ℂ (Fin n) → ℝ}
      (h : g₁ =ᶠ[𝓝 z] g₂) : ddbar g₁ z = ddbar g₂ z := by
    have hfd : fderiv ℝ g₁ =ᶠ[𝓝 z] fderiv ℝ g₂ := h.fderiv
    have hη : (fun w ↦ ofSubsingleton ℝ (EuclideanSpace ℂ (Fin n)) ℝ (0 : Fin 1)
        ((fderiv ℝ g₁ w).comp (EuclideanSpace.complexStructure n))) =ᶠ[𝓝 z]
        (fun w ↦ ofSubsingleton ℝ (EuclideanSpace ℂ (Fin n)) ℝ (0 : Fin 1)
          ((fderiv ℝ g₂ w).comp (EuclideanSpace.complexStructure n))) := by
      filter_upwards [hfd] with w hw
      rw [hw]
    simp only [ddbar]
    rw [Filter.EventuallyEq.extDeriv_eq hη]
  rw [FormField.chartRep_eq_chartRep_comp (α := mddbar n φ) hz hyy]
  rw [FormField.chartRep_self]
  change (ddbar (φ ∘ e'.symm) (e' y)).compContinuousLinearMap (fderiv ℝ ψ z) =
    ddbar (φ ∘ e.symm) z
  calc
    (ddbar (φ ∘ e'.symm) (e' y)).compContinuousLinearMap (fderiv ℝ ψ z) =
        (ddbar (φ ∘ e'.symm) (ψ z)).compContinuousLinearMap
          ((fderiv ℂ ψ z).restrictScalars ℝ) := by
      rw [hrealComplex]
      rfl
    _ = ddbar ((φ ∘ e'.symm) ∘ ψ) z :=
      (ddbar_comp_holomorphic hψ hφchart).symm
    _ = ddbar (φ ∘ e.symm) z := hddbarCongr hfun

/-- `mdWedgeDBar φ` is computed by `dWedgeDBar` in every chart. -/
theorem chartRep_mdWedgeDBar (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ φ) (x : M)
    {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    (mdWedgeDBar n φ).chartRep x z =
      dWedgeDBar (fderiv ℝ (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z) := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let y := e.symm z
  let e' := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y
  let f := e' ∘ e.symm
  have hyx : y ∈ e.source := e.map_target hz
  have hyy : y ∈ e'.source := mem_extChartAt_source y
  have hcommon : y ∈ e.source ∩ e'.source := ⟨hyx, hyy⟩
  have hz_eq : e y = z := e.right_inv hz
  have hderiv : tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y =
      fderiv ℝ f z := by
    rw [tangentCoordChange_def, hz_eq]
    simp [f, e, e']
  let A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y
  have hAreal : tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y =
      A.restrictScalars ℝ := tangentCoordChange_real_eq hcommon
  have hsymm : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ e.symm z := by
    exact (contMDiffOn_extChartAt_symm x).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz)
  have htransition : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ f z := by
    exact (contMDiffAt_extChartAt (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
      (x := y)).comp_of_eq hsymm rfl
  have hφy : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ φ y := hφ y
  have hφchart : ContDiffAt ℝ ∞ (φ ∘ e'.symm) (e' y) := by
    have hsymm' : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
        𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ e'.symm (e' y) := by
      exact (contMDiffOn_extChartAt_symm y).contMDiffAt
        ((isOpen_extChartAt_target y).mem_nhds (mem_extChartAt_target y))
    have hcomp := hφy.comp_of_eq hsymm' (e'.left_inv hyy)
    exact (contMDiffAt_iff_contDiffAt).mp hcomp
  have hfsource : ∀ᶠ w in 𝓝 z, e.symm w ∈ e'.source := by
    exact (continuousAt_extChartAt_symm'' hz).preimage_mem_nhds
      ((isOpen_extChartAt_source y).mem_nhds hyy)
  have hfun : (φ ∘ e'.symm) ∘ f =ᶠ[𝓝 z] φ ∘ e.symm := by
    filter_upwards [hfsource] with w hw
    change φ (e'.symm (e' (e.symm w))) = φ (e.symm w)
    rw [e'.left_inv hw]
  have hfderiv : fderiv ℝ (φ ∘ e.symm) z =
      (fderiv ℝ (φ ∘ e'.symm) (f z)).comp (fderiv ℝ f z) := by
    exact (hfun.fderiv_eq (𝕜 := ℝ)).symm.trans <| fderiv_comp (f := f)
      (g := φ ∘ e'.symm) (x := z)
        (hφchart.differentiableAt (by norm_num))
        (htransition.contDiffAt.differentiableAt (by norm_num))
  have hEval (ℓ : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ)
      (u v : EuclideanSpace ℂ (Fin n)) :
      (dWedgeDBar ℓ) ![u, v] = (ℓ (I • u) * ℓ v - ℓ (I • v) * ℓ u) / 2 := by
    change ((1 / 2 : ℝ) • ContinuousAlternatingMap.alternatizeUncurryFin
      ((ℓ.comp (Complex.I • ContinuousLinearMap.id ℝ (EuclideanSpace ℂ (Fin n)))).smulRight
        (ofSubsingleton ℝ (EuclideanSpace ℂ (Fin n)) ℝ (0 : Fin 1) ℓ))) ![u, v] = _
    simp [ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.removeNth]
    ring
  have hnatural (ℓ : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) :
      dWedgeDBar (ℓ.comp (A.restrictScalars ℝ)) =
        (dWedgeDBar ℓ).compContinuousLinearMap (A.restrictScalars ℝ) := by
    ext v
    have hv : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    rw [hEval]
    have htuple : (A.restrictScalars ℝ) ∘ ![v 0, v 1] =
        ![(A.restrictScalars ℝ) (v 0), (A.restrictScalars ℝ) (v 1)] := by
      funext i
      fin_cases i <;> rfl
    rw [htuple, hEval]
    have hAI (w : EuclideanSpace ℂ (Fin n)) :
        A (I • w) = I • A w := A.map_smul I w
    simp [ContinuousLinearMap.comp_apply, hAI]
  rw [FormField.chartRep_eq_chartRep_comp (α := mdWedgeDBar n φ) hz hyy]
  rw [FormField.chartRep_self]
  change (dWedgeDBar (fderiv ℝ (φ ∘ e'.symm) (e' y))).compContinuousLinearMap
      (fderiv ℝ f z) = dWedgeDBar (fderiv ℝ (φ ∘ e.symm) z)
  have hderivA : fderiv ℝ f z = A.restrictScalars ℝ := hderiv.symm.trans hAreal
  have hfderivFun (w : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (φ ∘ e.symm) z w =
        fderiv ℝ (φ ∘ e'.symm) (f z) ((A.restrictScalars ℝ) w) := by
    rw [hfderiv, ContinuousLinearMap.comp_apply, hderivA]
  have hfderivCLM : fderiv ℝ (φ ∘ e.symm) z =
      (fderiv ℝ (φ ∘ e'.symm) (f z)).comp (A.restrictScalars ℝ) :=
    ContinuousLinearMap.ext hfderivFun
  rw [hderivA, hfderivCLM]
  exact (hnatural (fderiv ℝ (φ ∘ e'.symm) (e' y))).symm

theorem isSmooth_mddbar (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ φ) :
    (mddbar n φ).IsSmooth := by
  intro x
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  have hφon : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ φ univ :=
    contMDiffOn_univ.mpr hφ
  have hφsymm : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (φ ∘ e.symm) e.target := by
    exact hφon.comp (contMDiffOn_extChartAt_symm x) (by intro z hz; simp)
  have hφchart : ContDiffOn ℝ ∞ (φ ∘ e.symm) e.target := hφsymm.contDiffOn
  have hddbar : ContDiffOn ℝ ∞ (ddbar (φ ∘ e.symm)) e.target :=
    ContDiffOn.ddbar (isOpen_extChartAt_target x) hφchart
  change ContDiffOn ℝ ∞ ((mddbar n φ).chartRep x) e.target
  exact hddbar.congr (fun z hz ↦ chartRep_mddbar hφ x hz)

theorem isOneOne_mddbar (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ φ) :
    (mddbar n φ).IsOneOne := by
  intro x
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  have hz : e x ∈ e.target := mem_extChartAt_target x
  have hsymm : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ e.symm (e x) := by
    exact (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz)
  have hφM : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (φ ∘ e.symm) (e x) :=
    (hφ x).comp_of_eq hsymm (e.left_inv (mem_extChartAt_source x))
  have hφC : ContDiffAt ℝ 2 (φ ∘ e.symm) (e x) := by
    exact ((contMDiffAt_iff_contDiffAt).mp hφM).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  change (ddbar (φ ∘ e.symm) (e x)).IsOneOne
  exact isOneOne_ddbar hφC

/-- `i∂∂̄φ = d(½ dᶜφ)` is exact. -/
theorem isExact_mddbar (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ φ) :
    (mddbar n φ).IsExact := by
  let J := EuclideanSpace.complexStructure n
  let e := fun x : M => extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let β : FormField (EuclideanSpace ℂ (Fin n)) M 1 := fun x ↦
    -(1 / 2 : ℝ) • ofSubsingleton ℝ (EuclideanSpace ℂ (Fin n)) ℝ (0 : Fin 1)
      ((fderiv ℝ (φ ∘ (e x).symm) ((e x) x)).comp J)
  have hβchart (x : M) {z : EuclideanSpace ℂ (Fin n)}
      (hz : z ∈ (e x).target) :
      β.chartRep x z = -(1 / 2 : ℝ) •
        ofSubsingleton ℝ (EuclideanSpace ℂ (Fin n)) ℝ (0 : Fin 1)
          ((fderiv ℝ (φ ∘ (e x).symm) z).comp J) := by
    let ex := e x
    let y := ex.symm z
    let ey := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y
    let ψ := ey ∘ ex.symm
    have hyx : y ∈ ex.source := ex.map_target hz
    have hyy : y ∈ ey.source := mem_extChartAt_source y
    have hcommon : y ∈ ex.source ∩ ey.source := ⟨hyx, hyy⟩
    have hz_eq : ex y = z := ex.right_inv hz
    have hderiv : tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y =
        fderiv ℝ ψ z := by
      rw [tangentCoordChange_def, hz_eq]
      simp [ψ, ex, ey, e]
    have hsource : ∀ᶠ w in 𝓝 z, ex.symm w ∈ ey.source :=
      (continuousAt_extChartAt_symm'' hz).preimage_mem_nhds
        ((isOpen_extChartAt_source y).mem_nhds hyy)
    have hfun : φ ∘ ex.symm =ᶠ[𝓝 z] (φ ∘ ey.symm) ∘ ψ := by
      filter_upwards [hsource] with w hw
      change φ (ex.symm w) = φ (ey.symm (ey (ex.symm w)))
      rw [ey.left_inv hw]
    have heysymm : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
        𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ ey.symm (ey y) := by
      exact (contMDiffOn_extChartAt_symm y).contMDiffAt
        ((isOpen_extChartAt_target y).mem_nhds (mem_extChartAt_target y))
    have hφM : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
        (φ ∘ ey.symm) (ey y) :=
      (hφ y).comp_of_eq heysymm (ey.left_inv hyy)
    have hφC : ContDiffAt ℝ 1 (φ ∘ ey.symm) (ey y) := by
      exact ((contMDiffAt_iff_contDiffAt).mp hφM).of_le
        (WithTop.coe_le_coe.mpr (by norm_num))
    have hsymm : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
        𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ ex.symm z := by
      exact (contMDiffOn_extChartAt_symm x).contMDiffAt
        ((isOpen_extChartAt_target x).mem_nhds hz)
    have hchart : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
        𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ ey y :=
      contMDiffAt_extChartAt (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (x := y)
    have hψC : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
        𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ ψ z := hchart.comp_of_eq hsymm rfl
    have hψC' : ContDiffAt ℝ 1 ψ z := by
      exact ((contMDiffAt_iff_contDiffAt).mp hψC).of_le
        (WithTop.coe_le_coe.mpr (by norm_num))
    have hderivPhi : fderiv ℝ (φ ∘ ex.symm) z =
        (fderiv ℝ (φ ∘ ey.symm) (ey y)).comp (fderiv ℝ ψ z) := by
      calc
        fderiv ℝ (φ ∘ ex.symm) z = fderiv ℝ ((φ ∘ ey.symm) ∘ ψ) z := hfun.fderiv_eq
        _ = _ := fderiv_comp (f := ψ) (g := φ ∘ ey.symm) (x := z)
          (hφC.differentiableAt (by norm_num)) (hψC'.differentiableAt (by norm_num))
    have hJ (v : EuclideanSpace ℂ (Fin n)) :
        J (fderiv ℝ ψ z v) = fderiv ℝ ψ z (J v) := by
      rw [← hderiv]
      simpa [J, EuclideanSpace.complexStructure] using
        (tangentCoordChange_I_smul hcommon v).symm
    change (β y).compContinuousLinearMap
        (tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y) = _
    rw [hderiv]
    dsimp [β]
    ext v
    change -(1 / 2 : ℝ) •
        fderiv ℝ (φ ∘ ey.symm) (ey y) (J (fderiv ℝ ψ z (v 0))) =
      -(1 / 2 : ℝ) • fderiv ℝ (φ ∘ ex.symm) z (J (v 0))
    rw [hJ (v 0)]
    congr 1
    change ((fderiv ℝ (φ ∘ ey.symm) (ey y)).comp (fderiv ℝ ψ z)) (J (v 0)) = _
    rw [hderivPhi]
  have hβsmooth : β.IsSmooth := by
    intro x
    let ex := e x
    have hφon : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ φ univ :=
      contMDiffOn_univ.mpr hφ
    have hφsymm : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
        (φ ∘ ex.symm) ex.target := by
      exact hφon.comp (contMDiffOn_extChartAt_symm x) (by intro z hz; simp)
    have hφchart : ContDiffOn ℝ ∞ (φ ∘ ex.symm) ex.target := hφsymm.contDiffOn
    have h_inf : (∞ : ℕ∞ω) + 1 ≤ ∞ :=
      le_of_eq (show (∞ : ℕ∞ω) = ∞ + 1 from rfl).symm
    have hfd : ContDiffOn ℝ ∞ (fderiv ℝ (φ ∘ ex.symm)) ex.target :=
      hφchart.fderiv_of_isOpen (isOpen_extChartAt_target x) h_inf
    let L : (EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) →L[ℝ]
        (EuclideanSpace ℂ (Fin n) [⋀^Fin 1]→L[ℝ] ℝ) :=
      (ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).toContinuousLinearMap
    have hcomp : ContDiffOn ℝ ∞
        (fun z ↦ (fderiv ℝ (φ ∘ ex.symm) z).comp J) ex.target := by
      fun_prop
    have hη : ContDiffOn ℝ ∞
        (fun z ↦ -(1 / 2 : ℝ) • ofSubsingleton ℝ (EuclideanSpace ℂ (Fin n)) ℝ
          (0 : Fin 1) ((fderiv ℝ (φ ∘ ex.symm) z).comp J)) ex.target := by
      change ContDiffOn ℝ ∞
        (fun z ↦ -(1 / 2 : ℝ) • L ((fderiv ℝ (φ ∘ ex.symm) z).comp J)) ex.target
      exact (hcomp.continuousLinearMap_comp L).const_smul _
    change ContDiffOn ℝ ∞ (β.chartRep x) ex.target
    exact hη.congr fun z hz ↦ hβchart x hz
  refine ⟨β, hβsmooth, ?_⟩
  funext x
  let ex := e x
  change _root_.extDeriv (β.chartRep x) (ex x) =
    ddbar (φ ∘ ex.symm) (ex x)
  have heq : β.chartRep x =ᶠ[𝓝 (ex x)] fun z ↦
      -(1 / 2 : ℝ) • ofSubsingleton ℝ (EuclideanSpace ℂ (Fin n)) ℝ (0 : Fin 1)
        ((fderiv ℝ (φ ∘ ex.symm) z).comp J) := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)]
      with z hz
    exact hβchart x hz
  rw [Filter.EventuallyEq.extDeriv_eq heq]
  rw [show (fun z : EuclideanSpace ℂ (Fin n) ↦
      -(1 / 2 : ℝ) • ofSubsingleton ℝ (EuclideanSpace ℂ (Fin n)) ℝ (0 : Fin 1)
        ((fderiv ℝ (φ ∘ ex.symm) z).comp J)) =
      -(1 / 2 : ℝ) • (fun z : EuclideanSpace ℂ (Fin n) ↦
        ofSubsingleton ℝ (EuclideanSpace ℂ (Fin n)) ℝ (0 : Fin 1)
          ((fderiv ℝ (φ ∘ ex.symm) z).comp J)) by rfl]
  rw [_root_.extDeriv_smul]
  rfl

theorem isClosed_mddbar (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ φ) :
    (mddbar n φ).IsClosed :=
  (isExact_mddbar hφ).isClosed

end

theorem isNonneg_mdWedgeDBar (φ : M → ℝ) : (mdWedgeDBar n φ).IsNonneg := fun _ ↦
  isNonneg_dWedgeDBar _
section

variable [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] {φ ψ : M → ℝ}


theorem mddbar_add (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ φ)
    (hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ ψ) :
    mddbar n (φ + ψ) = mddbar n φ + mddbar n ψ := by
  funext x
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  have hz : e x ∈ e.target := mem_extChartAt_target x
  have hsymm : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ e.symm (e x) := by
    exact (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz)
  have hφM : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (φ ∘ e.symm) (e x) :=
    (hφ x).comp_of_eq hsymm (e.left_inv (mem_extChartAt_source x))
  have hφC : ContDiffAt ℝ 2 (φ ∘ e.symm) (e x) := by
    exact ((contMDiffAt_iff_contDiffAt).mp hφM).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hψM : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (ψ ∘ e.symm) (e x) :=
    (hψ x).comp_of_eq hsymm (e.left_inv (mem_extChartAt_source x))
  have hψC : ContDiffAt ℝ 2 (ψ ∘ e.symm) (e x) := by
    exact ((contMDiffAt_iff_contDiffAt).mp hψM).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  change ddbar ((φ ∘ e.symm) + (ψ ∘ e.symm)) (e x) =
    ddbar (φ ∘ e.symm) (e x) + ddbar (ψ ∘ e.symm) (e x)
  exact ddbar_add hφC hψC

/-- `C²` version of `mddbar_add`. -/
theorem mddbar_add_of_contMDiff_two (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 φ)
    (hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 ψ) :
    mddbar n (φ + ψ) = mddbar n φ + mddbar n ψ := by
  funext x
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  have hz : e x ∈ e.target := mem_extChartAt_target x
  have hsymm : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ e.symm (e x) := by
    exact (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz)
  have hsymm2 : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 2 e.symm (e x) :=
    hsymm.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hφM : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2
      (φ ∘ e.symm) (e x) :=
    (hφ x).comp_of_eq hsymm2 (e.left_inv (mem_extChartAt_source x))
  have hφC : ContDiffAt ℝ 2 (φ ∘ e.symm) (e x) :=
    (contMDiffAt_iff_contDiffAt).mp hφM
  have hψM : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2
      (ψ ∘ e.symm) (e x) :=
    (hψ x).comp_of_eq hsymm2 (e.left_inv (mem_extChartAt_source x))
  have hψC : ContDiffAt ℝ 2 (ψ ∘ e.symm) (e x) :=
    (contMDiffAt_iff_contDiffAt).mp hψM
  change ddbar ((φ ∘ e.symm) + (ψ ∘ e.symm)) (e x) =
    ddbar (φ ∘ e.symm) (e x) + ddbar (ψ ∘ e.symm) (e x)
  exact ddbar_add hφC hψC

theorem mddbar_smul (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ φ) (c : ℝ) :
    mddbar n (c • φ) = c • mddbar n φ := by
  funext x
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  have hz : e x ∈ e.target := mem_extChartAt_target x
  have hsymm : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ e.symm (e x) := by
    exact (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz)
  have hφM : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (φ ∘ e.symm) (e x) :=
    (hφ x).comp_of_eq hsymm (e.left_inv (mem_extChartAt_source x))
  have hφC : ContDiffAt ℝ 2 (φ ∘ e.symm) (e x) := by
    exact ((contMDiffAt_iff_contDiffAt).mp hφM).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  change ddbar (c • (φ ∘ e.symm)) (e x) = c • ddbar (φ ∘ e.symm) (e x)
  exact ddbar_smul hφC c

theorem mddbar_sub (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ φ)
    (hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ ψ) :
    mddbar n (φ - ψ) = mddbar n φ - mddbar n ψ := by
  funext x
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  have hz : e x ∈ e.target := mem_extChartAt_target x
  have hsymm : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ e.symm (e x) := by
    exact (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz)
  have hφM : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (φ ∘ e.symm) (e x) :=
    (hφ x).comp_of_eq hsymm (e.left_inv (mem_extChartAt_source x))
  have hφC : ContDiffAt ℝ 2 (φ ∘ e.symm) (e x) := by
    exact ((contMDiffAt_iff_contDiffAt).mp hφM).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hψM : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (ψ ∘ e.symm) (e x) :=
    (hψ x).comp_of_eq hsymm (e.left_inv (mem_extChartAt_source x))
  have hψC : ContDiffAt ℝ 2 (ψ ∘ e.symm) (e x) := by
    exact ((contMDiffAt_iff_contDiffAt).mp hψM).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  change ddbar ((φ ∘ e.symm) - (ψ ∘ e.symm)) (e x) =
    ddbar (φ ∘ e.symm) (e x) - ddbar (ψ ∘ e.symm) (e x)
  exact ddbar_sub hφC hψC

end

@[simp]
theorem mddbar_const (c : ℝ) :
    mddbar n (fun _ : M ↦ c) = 0 := by
  funext x
  change ddbar (fun _ : EuclideanSpace ℂ (Fin n) ↦ c) _ = 0
  exact ddbar_const c

@[simp]
theorem mddbar_add_const (c : ℝ) :
    mddbar n (fun x ↦ φ x + c) = mddbar n φ := by
  funext x
  exact ddbar_add_const c
section

variable [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] {φ ψ : M → ℝ}


/-- Chain rule: `i∂∂̄(h ∘ φ) = h'(φ) i∂∂̄φ + h''(φ) i∂φ ∧ ∂̄φ`. -/
theorem mddbar_comp_real (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ φ) {h : ℝ → ℝ}
    (hh : ContDiff ℝ 2 h) :
    mddbar n (h ∘ φ) = fun x ↦ deriv h (φ x) • mddbar n φ x +
      deriv (deriv h) (φ x) • mdWedgeDBar n φ x := by
  funext x
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  have hφM : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (φ ∘ e.symm) (e x) := by
    have hz : e x ∈ e.target := mem_extChartAt_target x
    have hsymm : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
        𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ e.symm (e x) := by
      exact (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x).contMDiffAt
        ((isOpen_extChartAt_target x).mem_nhds hz)
    exact (hφ x).comp_of_eq hsymm (e.left_inv (mem_extChartAt_source x))
  have hφC : ContDiffAt ℝ 2 (φ ∘ e.symm) (e x) := by
    exact ((contMDiffAt_iff_contDiffAt).mp hφM).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hhx : ContDiffAt ℝ 2 h ((φ ∘ e.symm) (e x)) := by
    simpa only [Function.comp_apply, e.left_inv (mem_extChartAt_source x)] using hh.contDiffAt
  change ddbar (h ∘ (φ ∘ e.symm)) (e x) =
    deriv h (φ x) • ddbar (φ ∘ e.symm) (e x) +
      deriv (deriv h) (φ x) • dWedgeDBar (fderiv ℝ (φ ∘ e.symm) (e x))
  simpa only [Function.comp_apply, e.left_inv (mem_extChartAt_source x)] using
    (ddbar_comp_real hhx hφC)

/-- At a local maximum, `-i∂∂̄φ ≥ 0`. -/
theorem isNonneg_neg_mddbar_of_isLocalMax
    (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ φ) {x : M} (hmax : IsLocalMax φ x) :
    (-mddbar n φ x).IsNonneg := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  have hz : e x ∈ e.target := mem_extChartAt_target x
  have hsymm : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ e.symm (e x) := by
    exact (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz)
  have hφM : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (φ ∘ e.symm) (e x) :=
    (hφ x).comp_of_eq hsymm (e.left_inv (mem_extChartAt_source x))
  have hφC : ContDiffAt ℝ 2 (φ ∘ e.symm) (e x) := by
    exact ((contMDiffAt_iff_contDiffAt).mp hφM).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hcenter : e.symm (e x) = x := e.left_inv (mem_extChartAt_source x)
  have hmaxNear : ∀ᶠ y in 𝓝 (e.symm (e x)), φ y ≤ φ (e.symm (e x)) := by
    rw [hcenter]
    exact hmax
  have hmaxC : IsLocalMax (φ ∘ e.symm) (e x) := by
    change ∀ᶠ w in 𝓝 (e x), φ (e.symm w) ≤ φ (e.symm (e x))
    exact hsymm.continuousAt.eventually hmaxNear
  change (-ddbar (φ ∘ e.symm) (e x)).IsNonneg
  exact isNonneg_neg_ddbar_of_isLocalMax hφC hmaxC

/-- A pluriharmonic function on a compact connected complex manifold is constant. -/
theorem eq_const_of_mddbar_eq_zero [CompactSpace M] [ConnectedSpace M]
    (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ φ) (h : mddbar n φ = 0) :
    ∃ c : ℝ, ∀ x, φ x = c := by
  let hφon : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ φ univ :=
    contMDiffOn_univ.mpr hφ
  have hφcont : Continuous φ := hφ.continuous
  obtain ⟨x₀, hx₀, hmax⟩ :=
    isCompact_univ.exists_isMaxOn Set.univ_nonempty hφcont.continuousOn
  have hmaxAll : ∀ y, φ y ≤ φ x₀ := isMaxOn_univ_iff.mp hmax
  let c : ℝ := φ x₀
  let S : Set M := {x | φ x = c}
  have hx₀S : x₀ ∈ S := by simp [S, c]
  have hclosed : IsClosed S := by
    change IsClosed (φ ⁻¹' {c})
    exact isClosed_singleton.preimage hφcont
  have hopen : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hxS
    let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
    let z := e x
    let f : EuclideanSpace ℂ (Fin n) → ℝ := φ ∘ e.symm
    have hxSval : φ x = c := by simpa [S] using hxS
    have hsymm : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
        𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ e.symm e.target :=
      contMDiffOn_extChartAt_symm x
    have hφchartMD : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f e.target := by
      exact hφon.comp hsymm (by intro w hw; simp)
    have hφchart : ContDiffOn ℝ ∞ f e.target := hφchartMD.contDiffOn
    have hz : z ∈ e.target := mem_extChartAt_target x
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
      ((isOpen_extChartAt_target x).mem_nhds hz)
    have hballSub : Metric.ball z r ⊆ e.target := hball
    have hf : ContDiffOn ℝ 2 f (Metric.ball z r) :=
      (hφchart.mono hballSub).of_le
        (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
    have htrace (w : EuclideanSpace ℂ (Fin n)) (hw : w ∈ Metric.ball z r)
        (v : EuclideanSpace ℂ (Fin n)) :
        fderiv ℝ (fderiv ℝ f) w v v +
          fderiv ℝ (fderiv ℝ f) w (I • v) (I • v) = 0 := by
      have hchartZero : (mddbar n φ).chartRep x w = 0 := by
        rw [h]
        simp
      have hddbar : ddbar f w = 0 := by
        rw [chartRep_mddbar hφ x (hballSub hw)] at hchartZero
        exact hchartZero
      have hval : ddbar f w ![v, I • v] = 0 := by
        simpa using congrArg (fun α : _ [⋀^Fin 2]→L[ℝ] ℝ ↦ α ![v, I • v]) hddbar
      have hfAt : ContDiffAt ℝ 2 f w :=
        (hf w hw).contDiffAt (Metric.isOpen_ball.mem_nhds hw)
      rw [ddbar_apply hfAt v (I • v)] at hval
      have hI : I • (I • v) = -v := by simp [smul_smul]
      rw [hI, map_neg] at hval
      linarith
    have hlocalMax : IsMaxOn f (Metric.ball z r) z := by
      intro w hw
      have hcenter : f z = φ x := by
        change φ (e.symm (e x)) = φ x
        rw [e.left_inv (mem_extChartAt_source x)]
      have hxEq : φ x = φ x₀ := by simpa [c] using hxSval
      calc
        f w = φ (e.symm w) := rfl
        _ ≤ φ x₀ := hmaxAll (e.symm w)
        _ = φ x := hxEq.symm
        _ = f z := hcenter.symm
    have hlines : ∀ v : EuclideanSpace ℂ (Fin n), ‖v‖ < r / 2 →
        InnerProductSpace.HarmonicOnNhd (fun t : ℂ ↦ f (z + t • v))
          (Metric.ball (0 : ℂ) 2) := by
      intro v hv
      apply harmonicOnNhd_comp_complexLine (U := Metric.ball z r)
      · exact Metric.isOpen_ball
      · intro t ht
        change (z + t • v) ∈ Metric.ball z r
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
        have ht' : ‖t‖ < 2 := by simpa using ht
        calc
          ‖t • v‖ = ‖t‖ * ‖v‖ := norm_smul _ _
          _ ≤ 2 * ‖v‖ := mul_le_mul_of_nonneg_right ht'.le (norm_nonneg _)
          _ < 2 * (r / 2) := mul_lt_mul_of_pos_left hv (by norm_num)
          _ = r := by ring
      · exact hf
      · exact fun w hw ↦ htrace w hw v
    have hconst := eqOn_ball_of_harmonicOnNhd_complexLine hlocalMax hlines
    let W : Set M := e.source ∩ e ⁻¹' Metric.ball z (r / 2)
    have hWopen : IsOpen W := by
      change IsOpen ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source ∩
        extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x ⁻¹' Metric.ball z (r / 2))
      exact isOpen_extChartAt_preimage' (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x
        Metric.isOpen_ball
    have hxW : x ∈ W := by
      refine ⟨mem_extChartAt_source x, ?_⟩
      change e x ∈ Metric.ball (e x) (r / 2)
      exact Metric.mem_ball_self (by positivity)
    have hWS : W ⊆ S := by
      intro y hy
      rcases hy with ⟨hysrc, hyball⟩
      have hycoord : e y ∈ Metric.ball z (r / 2) := hyball
      have hcenter : f z = φ x := by
        change φ (e.symm (e x)) = φ x
        rw [e.left_inv (mem_extChartAt_source x)]
      have hzval : f z = c := hcenter.trans hxSval
      have hvalue : φ y = c := by
        calc
          φ y = f (e y) := by
            dsimp [f]
            rw [e.left_inv hysrc]
          _ = f z := hconst hycoord
          _ = c := hzval
      exact hvalue
    exact Filter.mem_of_superset (hWopen.mem_nhds hxW) hWS
  have hclopen : IsClopen S := ⟨hclosed, hopen⟩
  have hconnected := (connectedSpace_iff_clopen.mp inferInstance).2 S hclopen
  rcases hconnected with hEmpty | hUniv
  · exact False.elim (by simp [hEmpty] at hx₀S)
  · refine ⟨c, ?_⟩
    intro x
    have hx : x ∈ S := by simp [hUniv]
    change φ x = c at hx
    exact hx

end

end Manifold
