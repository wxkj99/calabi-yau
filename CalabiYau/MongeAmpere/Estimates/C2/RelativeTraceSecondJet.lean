module

public import CalabiYau.Geometry.Kahler.Curvature.Chart.Basic
import CalabiYau.MongeAmpere.Estimates.C2.InverseMetricJet
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace

open scoped ContDiff Matrix.Norms.Elementwise
open Filter Topology

namespace KahlerForm

private theorem contDiffAt_matrix_of_entries
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : E → Matrix (Fin n) (Fin n) ℂ) (z : E)
    (hG : ∀ j k, ContDiffAt ℝ 2 (fun w ↦ G w j k) z) :
    ContDiffAt ℝ 2 G z := by
  change ContDiffAt ℝ 2 (fun w j k ↦ G w j k) z
  rw [contDiffAt_pi]
  intro j
  rw [contDiffAt_pi]
  exact hG j

private theorem fderiv_inv_zero_of_fderiv_zero
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : E → Matrix (Fin n) (Fin n) ℂ) (z : E)
    (hG : ContDiffAt ℝ 2 G z) (hId : G z = 1)
    (hFirst : fderiv ℝ G z = 0) :
    fderiv ℝ (fun w ↦ (G w)⁻¹) z = 0 := by
  have hunit : IsUnit (G z).det := by simp [hId]
  have hInvDiff : DifferentiableAt ℝ (fun B : Matrix (Fin n) (Fin n) ℂ ↦ B⁻¹) (G z) :=
    (Matrix.contDiffAt_inv hunit).differentiableAt (by norm_num)
  have hGdiff : DifferentiableAt ℝ G z := hG.differentiableAt (by norm_num)
  have hcomp := fderiv_comp (f := G)
    (g := fun B : Matrix (Fin n) (Fin n) ℂ ↦ B⁻¹) (x := z) hInvDiff hGdiff
  change fderiv ℝ ((fun B : Matrix (Fin n) (Fin n) ℂ ↦ B⁻¹) ∘ G) z = 0
  calc
    fderiv ℝ ((fun B : Matrix (Fin n) (Fin n) ℂ ↦ B⁻¹) ∘ G) z =
        fderiv ℝ (fun B : Matrix (Fin n) (Fin n) ℂ ↦ B⁻¹) (G z) ∘L fderiv ℝ G z := hcomp
    _ = 0 := by simp [hFirst]

private theorem fderiv_fderiv_mul_jet
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
  have hLhs : fderiv ℝ (fderiv ℝ (fun w ↦ f w * g w)) z v u =
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

private theorem fderiv_fderiv_sum
    {ι : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset ι) (f : ι → E → ℂ) (z : E)
    (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) z) (v u : E) :
    fderiv ℝ (fderiv ℝ (fun w ↦ ∑ i ∈ s, f i w)) z v u =
      ∑ i ∈ s, fderiv ℝ (fderiv ℝ (f i)) z v u := by
  have h := iteratedFDeriv_fun_sum_apply (u := s) (n := 2) (x := z) hf
  have hEval := congrArg (fun T ↦ T ![v, u]) h
  rw [_root_.sum_apply] at hEval
  have hLeft : iteratedFDeriv ℝ 2 (fun w ↦ ∑ i ∈ s, f i w) z ![v, u] =
      fderiv ℝ (fderiv ℝ (fun w ↦ ∑ i ∈ s, f i w)) z v u := by
    rw [iteratedFDeriv_two_apply]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hRight (i : ι) : iteratedFDeriv ℝ 2 (f i) z ![v, u] =
      fderiv ℝ (fderiv ℝ (f i)) z v u := by
    rw [iteratedFDeriv_two_apply]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  calc
    fderiv ℝ (fderiv ℝ (fun w ↦ ∑ i ∈ s, f i w)) z v u =
        iteratedFDeriv ℝ 2 (fun w ↦ ∑ i ∈ s, f i w) z ![v, u] := hLeft.symm
    _ = ∑ i ∈ s, iteratedFDeriv ℝ 2 (f i) z ![v, u] := hEval
    _ = ∑ i ∈ s, fderiv ℝ (fderiv ℝ (f i)) z v u := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hRight i

private theorem fderiv_matrix_entry
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : E → Matrix (Fin n) (Fin n) ℂ) (z : E)
    (hG : ContDiffAt ℝ 2 G z) (i j : Fin n) (d : E) :
    fderiv ℝ (fun w ↦ G w i j) z d = (fderiv ℝ G z d) i j := by
  have hGdiff : DifferentiableAt ℝ G z := hG.differentiableAt (by norm_num)
  have hGrow : ContDiffAt ℝ 2 (fun w ↦ G w i) z :=
    (contDiffAt_apply ℝ (Fin n → ℂ) i (G z)).comp z hG
  have hGrowDiff : DifferentiableAt ℝ (fun w ↦ G w i) z :=
    hGrow.differentiableAt (by norm_num)
  have hRowDer := fderiv_apply hGdiff i
  have hEntryDer := fderiv_apply hGrowDiff j
  calc
    fderiv ℝ (fun w ↦ G w i j) z d = (fderiv ℝ (fun w ↦ G w i) z d) j := by
      rw [hEntryDer]
      simp
    _ = (fderiv ℝ G z d) i j := by rw [hRowDer]; rfl

private theorem fderiv_fderiv_matrix_entry
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : E → Matrix (Fin n) (Fin n) ℂ) (z : E)
    (hG : ContDiffAt ℝ 2 G z) (i j : Fin n) (v u : E) :
    fderiv ℝ (fderiv ℝ (fun w ↦ G w i j)) z v u =
      (fderiv ℝ (fderiv ℝ G) z v u) i j := by
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ :=
    ((ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℝ] ℂ).comp
      (ContinuousLinearMap.proj i : Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin n → ℂ)))
  have hIter := L.iteratedFDeriv_comp_left (f := G) hG (i := 2) (by norm_num)
  have hEval := congrArg (fun T ↦ T ![v, u]) hIter
  have hEntryIter : iteratedFDeriv ℝ 2 (fun w ↦ G w i j) z ![v, u] =
      (iteratedFDeriv ℝ 2 G z ![v, u]) i j := by
    have h := hEval
    simp [L, Function.comp_def] at h
    exact h
  calc
    fderiv ℝ (fderiv ℝ (fun w ↦ G w i j)) z v u =
        iteratedFDeriv ℝ 2 (fun w ↦ G w i j) z ![v, u] := by
          rw [iteratedFDeriv_two_apply]
          simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    _ = (iteratedFDeriv ℝ 2 G z ![v, u]) i j := hEntryIter
    _ = (fderiv ℝ (fderiv ℝ G) z v u) i j := by
          rw [iteratedFDeriv_two_apply]
          rfl

private theorem fderiv_fderiv_re
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E → ℂ) (z : E) (ha : ContDiffAt ℝ 2 a z) (v u : E) :
    fderiv ℝ (fderiv ℝ (fun w ↦ (a w).re)) z v u =
      (fderiv ℝ (fderiv ℝ a) z v u).re := by
  let L : ℂ →L[ℝ] ℝ := RCLike.reCLM
  have hiter := L.iteratedFDeriv_comp_left (f := a) ha (i := 2) (by norm_num)
  have hEval := congrArg (fun T ↦ T ![v, u]) hiter
  have hLeft : iteratedFDeriv ℝ 2 (fun w ↦ (a w).re) z ![v, u] =
      fderiv ℝ (fderiv ℝ (fun w ↦ (a w).re)) z v u := by
    rw [iteratedFDeriv_two_apply]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hRight : iteratedFDeriv ℝ 2 a z ![v, u] =
      fderiv ℝ (fderiv ℝ a) z v u := by
    rw [iteratedFDeriv_two_apply]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hcomp : iteratedFDeriv ℝ 2 (fun w ↦ (a w).re) z ![v, u] =
      (iteratedFDeriv ℝ 2 a z ![v, u]).re := by
    have h := hEval
    simp [L, Function.comp_def] at h
    exact h
  rw [← hLeft, hcomp, hRight]

private theorem realpart_complexWirtinger_eq_hessian
    {n : ℕ} (a : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (ha : ContDiffAt ℝ 2 a z) (p : Fin n) :
    (chartPartialZComplex (fun w ↦ chartPartialBarComplex a w p) z p).re =
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
      fderiv ℝ (fun w ↦ fderiv ℝ a w ep) z d = fderiv ℝ (fderiv ℝ a) z d ep :=
    hD d ep
  have hBc (d : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ fderiv ℝ a w (Complex.I • ep)) z d =
        fderiv ℝ (fderiv ℝ a) z d (Complex.I • ep) := hD d (Complex.I • ep)
  have hnum : DifferentiableAt ℝ
      (fun w ↦ fderiv ℝ a w ep + Complex.I * fderiv ℝ a w (Complex.I • ep)) z :=
    hA.add (hB.const_mul Complex.I)
  have hbar : (fun w ↦ chartPartialBarComplex a w p) =
      fun w ↦ (2 : ℂ)⁻¹ * (fderiv ℝ a w ep + Complex.I * fderiv ℝ a w (Complex.I • ep)) := by
    funext w
    simp [chartPartialBarComplex, ep, div_eq_mul_inv]
    ring
  have hpartial (d : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ chartPartialBarComplex a w p) z d =
        (2 : ℂ)⁻¹ *
          (fderiv ℝ (fderiv ℝ a) z d ep +
            Complex.I * fderiv ℝ (fderiv ℝ a) z d (Complex.I • ep)) := by
    rw [hbar, fderiv_const_mul hnum (2 : ℂ)⁻¹,
      fderiv_fun_add hA (hB.const_mul Complex.I),
      fderiv_const_mul hB Complex.I]
    simp only [add_apply, smul_apply, smul_eq_mul, hAc, hBc]
  have hq : ContDiffAt ℝ 2 (fun w ↦ (a w).re) z := by
    change ContDiffAt ℝ 2 (RCLike.re ∘ a) z
    exact (RCLike.reCLM.contDiff.contDiffAt.comp z ha)
  unfold chartPartialZComplex
  rw [hpartial ep, hpartial (Complex.I • ep), complexHessian_apply hq p p]
  simp only [div_eq_mul_inv]
  have hsymm := ha.isSymmSndFDerivAt (by norm_num [minSmoothness])
  have hsymm₁ : fderiv ℝ (fderiv ℝ a) z ep (Complex.I • ep) =
      fderiv ℝ (fderiv ℝ a) z (Complex.I • ep) ep := hsymm _ _
  have hRe (d e : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fderiv ℝ (fun w ↦ (a w).re)) z d e =
        (fderiv ℝ (fderiv ℝ a) z d e).re := fderiv_fderiv_re a z ha d e
  rw [hRe ep ep, hRe (Complex.I • ep) (Complex.I • ep),
    hRe ep (Complex.I • ep), hRe (Complex.I • ep) ep, hsymm₁]
  simp [Complex.I_re, Complex.mul_re]
  ring

private theorem complexHessian_real_diag
    {n : ℕ} (f : EuclideanSpace ℂ (Fin n) → ℝ)
    (z : EuclideanSpace ℂ (Fin n)) (hf : ContDiffAt ℝ 2 f z) (p : Fin n) :
    (complexHessian f z p p).re =
      (fderiv ℝ (fderiv ℝ f) z (EuclideanSpace.single p 1) (EuclideanSpace.single p 1) +
        fderiv ℝ (fderiv ℝ f) z (Complex.I • EuclideanSpace.single p 1)
          (Complex.I • EuclideanSpace.single p 1)) / 4 := by
  rw [complexHessian_apply hf p p]
  have hsymm := hf.isSymmSndFDerivAt (by norm_num [minSmoothness])
  have hcross := hsymm (EuclideanSpace.single p 1) (Complex.I • EuclideanSpace.single p 1)
  rw [hcross]
  simp

private theorem contDiffAt_relativeTraceMatrix
    {n : ℕ}
    (G₀ G₁ : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hG₀ : ∀ j k, ContDiffAt ℝ 2 (fun w ↦ G₀ w j k) z)
    (hG₁ : ∀ j k, ContDiffAt ℝ 2 (fun w ↦ G₁ w j k) z)
    (hId : G₀ z = 1) :
    ContDiffAt ℝ 2 (fun w ↦ (((G₀ w)⁻¹ * G₁ w).trace)) z := by
  let H : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ := fun w ↦ (G₀ w)⁻¹
  let term : Fin n → Fin n → EuclideanSpace ℂ (Fin n) → ℂ :=
    fun j k w ↦ H w j k * G₁ w k j
  have hG₀all : ContDiffAt ℝ 2 G₀ z := contDiffAt_matrix_of_entries G₀ z hG₀
  have hG₁all : ContDiffAt ℝ 2 G₁ z := contDiffAt_matrix_of_entries G₁ z hG₁
  have hunit : IsUnit (G₀ z).det := by simp [hId]
  have hle : (2 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
    change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.2 (by norm_num : (2 : ℕ∞) ≤ ⊤)
  have hHreg : ContDiffAt ℝ 2 H z :=
    ((Matrix.contDiffAt_inv hunit).of_le hle).comp z hG₀all
  have hHentry (j k : Fin n) : ContDiffAt ℝ 2 (fun w ↦ H w j k) z := by
    have hRow := (contDiffAt_apply ℝ (Fin n → ℂ) j (H z)).comp z hHreg
    exact ((contDiffAt_apply ℝ ℂ k (H z j)).comp z hRow)
  have hG₁entry (j k : Fin n) : ContDiffAt ℝ 2 (fun w ↦ G₁ w j k) z := by
    have hRow := (contDiffAt_apply ℝ (Fin n → ℂ) j (G₁ z)).comp z hG₁all
    exact ((contDiffAt_apply ℝ ℂ k (G₁ z j)).comp z hRow)
  have hterm (j k : Fin n) : ContDiffAt ℝ 2 (term j k) z :=
    (hHentry j k).mul (hG₁entry k j)
  have hInner (j : Fin n) :
      ContDiffAt ℝ 2 (fun w ↦ ∑ k ∈ Finset.univ, term j k w) z :=
    ContDiffAt.sum (fun k hk ↦ hterm j k)
  have hSum : ContDiffAt ℝ 2
      (fun w ↦ ∑ j ∈ Finset.univ, ∑ k ∈ Finset.univ, term j k w) z :=
    ContDiffAt.sum (fun j hj ↦ hInner j)
  have htrace : (fun w ↦ (((G₀ w)⁻¹ * G₁ w).trace)) =
      fun w ↦ ∑ j ∈ Finset.univ, ∑ k ∈ Finset.univ, term j k w := by
    funext w
    simp [term, H, Matrix.trace, Matrix.mul_apply]
  rw [htrace]
  exact hSum

private theorem relativeTraceMatrix_fderiv2
    {n : ℕ}
    (G₀ G₁ : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (eig : Fin n → ℝ)
    (hG₀ : ∀ j k, ContDiffAt ℝ 2 (fun w ↦ G₀ w j k) z)
    (hG₁ : ∀ j k, ContDiffAt ℝ 2 (fun w ↦ G₁ w j k) z)
    (hId : G₀ z = 1)
    (hDiag : G₁ z = Matrix.diagonal (Complex.ofReal ∘ eig))
    (hFirstReal : fderiv ℝ G₀ z = 0) (v u : EuclideanSpace ℂ (Fin n)) :
    fderiv ℝ (fderiv ℝ (fun w ↦ (((G₀ w)⁻¹ * G₁ w).trace))) z v u =
      (∑ j, fderiv ℝ (fderiv ℝ (fun w ↦ G₁ w j j)) z v u) -
        ∑ j, (eig j : ℂ) * fderiv ℝ (fderiv ℝ (fun w ↦ G₀ w j j)) z v u := by
  let H : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ := fun w ↦ (G₀ w)⁻¹
  let term : Fin n → Fin n → EuclideanSpace ℂ (Fin n) → ℂ :=
    fun j k w ↦ H w j k * G₁ w k j
  have hG₀all : ContDiffAt ℝ 2 G₀ z := contDiffAt_matrix_of_entries G₀ z hG₀
  have hG₁all : ContDiffAt ℝ 2 G₁ z := contDiffAt_matrix_of_entries G₁ z hG₁
  have hunit : IsUnit (G₀ z).det := by simp [hId]
  have hle : (2 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
    change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.2 (by norm_num : (2 : ℕ∞) ≤ ⊤)
  have hHreg : ContDiffAt ℝ 2 H z := by
    exact ((Matrix.contDiffAt_inv hunit).of_le hle).comp z hG₀all
  have hHfirst : fderiv ℝ H z = 0 := by
    dsimp [H]
    exact fderiv_inv_zero_of_fderiv_zero G₀ z hG₀all hId hFirstReal
  have hHsecond (v u : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fderiv ℝ H) z v u = -(fderiv ℝ (fderiv ℝ G₀) z v u) := by
    simpa [H] using Matrix.fderiv_fderiv_inv_of_eq_one_of_fderiv_eq_zero
      G₀ z hG₀all hId hFirstReal v u
  have hHentry (j k : Fin n) : ContDiffAt ℝ 2 (fun w ↦ H w j k) z := by
    have hRow := (contDiffAt_apply ℝ (Fin n → ℂ) j (H z)).comp z hHreg
    exact ((contDiffAt_apply ℝ ℂ k (H z j)).comp z hRow)
  have hG₁entry (j k : Fin n) : ContDiffAt ℝ 2 (fun w ↦ G₁ w j k) z := by
    have hRow := (contDiffAt_apply ℝ (Fin n → ℂ) j (G₁ z)).comp z hG₁all
    exact ((contDiffAt_apply ℝ ℂ k (G₁ z j)).comp z hRow)
  have hterm (j k : Fin n) : ContDiffAt ℝ 2 (term j k) z := by
    exact (hHentry j k).mul (hG₁entry k j)
  have hInner (j : Fin n) :
      ContDiffAt ℝ 2 (fun w ↦ ∑ k ∈ Finset.univ, term j k w) z := by
    exact ContDiffAt.sum (fun k hk ↦ hterm j k)
  have hHfirst_entry (j k : Fin n) (d : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ H w j k) z d = 0 := by
    rw [fderiv_matrix_entry H z hHreg j k d]
    simp [hHfirst]
  have hterm_jet (j k : Fin n) :
      fderiv ℝ (fderiv ℝ (term j k)) z v u =
        H z j k * fderiv ℝ (fderiv ℝ (fun w ↦ G₁ w k j)) z v u +
        fderiv ℝ (fun w ↦ H w j k) z v * fderiv ℝ (fun w ↦ G₁ w k j) z u +
        fderiv ℝ (fun w ↦ H w j k) z u * fderiv ℝ (fun w ↦ G₁ w k j) z v +
        G₁ z k j * fderiv ℝ (fderiv ℝ (fun w ↦ H w j k)) z v u := by
    exact fderiv_fderiv_mul_jet (fun w ↦ H w j k) (fun w ↦ G₁ w k j) z
      (hHentry j k) (hG₁entry k j) v u
  have hsumJet :
      fderiv ℝ (fderiv ℝ (fun w ↦ ∑ j ∈ Finset.univ, ∑ k ∈ Finset.univ, term j k w)) z v u =
        ∑ j ∈ Finset.univ, ∑ k ∈ Finset.univ,
          fderiv ℝ (fderiv ℝ (term j k)) z v u := by
    have hOuter := fderiv_fderiv_sum Finset.univ
      (fun j w ↦ ∑ k ∈ Finset.univ, term j k w) z (fun j hj ↦ hInner j) v u
    calc
      _ = ∑ j ∈ Finset.univ,
          fderiv ℝ (fderiv ℝ (fun w ↦ ∑ k ∈ Finset.univ, term j k w)) z v u := by
            simpa using hOuter
      _ = ∑ j ∈ Finset.univ, ∑ k ∈ Finset.univ,
          fderiv ℝ (fderiv ℝ (term j k)) z v u := by
            apply Finset.sum_congr rfl
            intro j hj
            have hInnerJet := fderiv_fderiv_sum Finset.univ (fun k w ↦ term j k w)
              z (fun k hk ↦ hterm j k) v u
            simpa using hInnerJet
  have htrace : (fun w ↦ (((G₀ w)⁻¹ * G₁ w).trace)) =
      fun w ↦ ∑ j ∈ Finset.univ, ∑ k ∈ Finset.univ, term j k w := by
    funext w
    simp [term, H, Matrix.trace, Matrix.mul_apply]
  rw [htrace, hsumJet]
  have hHval (j k : Fin n) : H z j k = if j = k then 1 else 0 := by
    simp [H, hId, Matrix.one_apply]
  have hG₁val (j k : Fin n) : G₁ z k j =
      if k = j then (eig k : ℂ) else 0 := by
    rw [hDiag]
    simp [Matrix.diagonal]
  have hG₁second (j k : Fin n) :
      fderiv ℝ (fderiv ℝ (fun w ↦ G₁ w j k)) z v u =
        (fderiv ℝ (fderiv ℝ G₁) z v u) j k :=
    fderiv_fderiv_matrix_entry G₁ z hG₁all j k v u
  have hHsecondEntry (j k : Fin n) :
      fderiv ℝ (fderiv ℝ (fun w ↦ H w j k)) z v u =
        (fderiv ℝ (fderiv ℝ H) z v u) j k :=
    fderiv_fderiv_matrix_entry H z hHreg j k v u
  have hG₀second (j k : Fin n) :
      fderiv ℝ (fderiv ℝ (fun w ↦ G₀ w j k)) z v u =
        (fderiv ℝ (fderiv ℝ G₀) z v u) j k :=
    fderiv_fderiv_matrix_entry G₀ z hG₀all j k v u
  have hHref (j k : Fin n) :
      fderiv ℝ (fderiv ℝ (fun w ↦ H w j k)) z v u =
        -(fderiv ℝ (fderiv ℝ (fun w ↦ G₀ w j k)) z v u) := by
    calc
      _ = (fderiv ℝ (fderiv ℝ H) z v u) j k := hHsecondEntry j k
      _ = (-(fderiv ℝ (fderiv ℝ G₀) z v u)) j k := by
        exact congrArg (fun A : Matrix (Fin n) (Fin n) ℂ ↦ A j k) (hHsecond v u)
      _ = -(fderiv ℝ (fderiv ℝ (fun w ↦ G₀ w j k)) z v u) := by
        simp only [Matrix.neg_apply]
        exact congrArg Neg.neg (hG₀second j k).symm
  have htermEval (j k : Fin n) :
      fderiv ℝ (fderiv ℝ (term j k)) z v u =
        (if j = k then 1 else 0) *
          fderiv ℝ (fderiv ℝ (fun w ↦ G₁ w k j)) z v u +
        (if k = j then (eig k : ℂ) else 0) *
          (-(fderiv ℝ (fderiv ℝ (fun w ↦ G₀ w j k)) z v u)) := by
    rw [hterm_jet j k, hHfirst_entry j k v, hHfirst_entry j k u,
      hHval j k, hG₁val j k, hHref j k]
    ring
  simp_rw [htermEval]
  simp [Finset.sum_add_distrib, eq_comm, mul_neg]
  ring

/-- The real diagonal mixed jet of the actual relative matrix trace.
Source: Székelyhidi §3.2, Lemma 3.7 proof, p.41, first unnumbered expansion.
The inverse reference mixed jet contributes with a minus sign.
Neither the varying metric nor its determinant is inverted. -/
private theorem complexHessian_relativeTraceMatrix_diag_real
    {n : ℕ}
    (G₀ G₁ : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (eig : Fin n → ℝ)
    (hG₀ : ∀ j k, ContDiffAt ℝ 2 (fun w ↦ G₀ w j k) z)
    (hG₁ : ∀ j k, ContDiffAt ℝ 2 (fun w ↦ G₁ w j k) z)
    (hId : G₀ z = 1)
    (hDiag : G₁ z = Matrix.diagonal (Complex.ofReal ∘ eig))
    (hFirstReal : fderiv ℝ G₀ z = 0) (p : Fin n) :
    (complexHessian (fun w ↦ (((G₀ w)⁻¹ * G₁ w).trace).re) z p p).re =
      (∑ j, (complexHessian (fun w ↦ (G₁ w j j).re) z p p).re) -
        ∑ j, eig j * (complexHessian (fun w ↦ (G₀ w j j).re) z p p).re := by
  let T : EuclideanSpace ℂ (Fin n) → ℂ := fun w ↦ (((G₀ w)⁻¹ * G₁ w).trace)
  let Q : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ (T w).re
  have hTreg := contDiffAt_relativeTraceMatrix G₀ G₁ z hG₀ hG₁ hId
  have hQreg : ContDiffAt ℝ 2 Q z := by
    change ContDiffAt ℝ 2 (RCLike.re ∘ T) z
    exact (RCLike.reCLM.contDiff.contDiffAt.comp z hTreg)
  let ep : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single p 1
  let fp : EuclideanSpace ℂ (Fin n) := Complex.I • ep
  have hSecond (d e : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fderiv ℝ Q) z d e =
        ∑ j, (fderiv ℝ (fderiv ℝ (fun w ↦ G₁ w j j)) z d e).re -
          ∑ j, eig j * (fderiv ℝ (fderiv ℝ (fun w ↦ G₀ w j j)) z d e).re := by
    calc
      _ = (fderiv ℝ (fderiv ℝ T) z d e).re := by
        exact fderiv_fderiv_re T z hTreg d e
      _ = _ := by
        rw [relativeTraceMatrix_fderiv2 G₀ G₁ z eig hG₀ hG₁ hId hDiag hFirstReal d e]
        simp [Complex.sub_re, Complex.re_sum, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re]
  have hG₁regR (j : Fin n) : ContDiffAt ℝ 2 (fun w ↦ (G₁ w j j).re) z := by
    change ContDiffAt ℝ 2 (RCLike.re ∘ (fun w ↦ G₁ w j j)) z
    exact (RCLike.reCLM.contDiff.contDiffAt.comp z (hG₁ j j))
  have hG₀regR (j : Fin n) : ContDiffAt ℝ 2 (fun w ↦ (G₀ w j j).re) z := by
    change ContDiffAt ℝ 2 (RCLike.re ∘ (fun w ↦ G₀ w j j)) z
    exact (RCLike.reCLM.contDiff.contDiffAt.comp z (hG₀ j j))
  have hG₁Hess (j : Fin n) :
      (complexHessian (fun w ↦ (G₁ w j j).re) z p p).re =
        ((fderiv ℝ (fderiv ℝ (fun w ↦ G₁ w j j)) z ep ep).re +
          (fderiv ℝ (fderiv ℝ (fun w ↦ G₁ w j j)) z fp fp).re) / 4 := by
    rw [complexHessian_real_diag (fun w ↦ (G₁ w j j).re) z (hG₁regR j) p]
    rw [fderiv_fderiv_re (fun w ↦ G₁ w j j) z (hG₁ j j) ep ep,
      fderiv_fderiv_re (fun w ↦ G₁ w j j) z (hG₁ j j) fp fp]
  have hG₀Hess (j : Fin n) :
      (complexHessian (fun w ↦ (G₀ w j j).re) z p p).re =
        ((fderiv ℝ (fderiv ℝ (fun w ↦ G₀ w j j)) z ep ep).re +
          (fderiv ℝ (fderiv ℝ (fun w ↦ G₀ w j j)) z fp fp).re) / 4 := by
    rw [complexHessian_real_diag (fun w ↦ (G₀ w j j).re) z (hG₀regR j) p]
    rw [fderiv_fderiv_re (fun w ↦ G₀ w j j) z (hG₀ j j) ep ep,
      fderiv_fderiv_re (fun w ↦ G₀ w j j) z (hG₀ j j) fp fp]
  rw [complexHessian_real_diag Q z hQreg p]
  rw [hSecond ep ep, hSecond fp fp]
  have hsumG₁ :
      (∑ j, (complexHessian (fun w ↦ (G₁ w j j).re) z p p).re) =
        ∑ j, (((fderiv ℝ (fderiv ℝ (fun w ↦ G₁ w j j)) z ep ep).re +
          (fderiv ℝ (fderiv ℝ (fun w ↦ G₁ w j j)) z fp fp).re) / 4) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact hG₁Hess j
  have hsumG₀ :
      (∑ j, eig j * (complexHessian (fun w ↦ (G₀ w j j).re) z p p).re) =
        ∑ j, eig j * (((fderiv ℝ (fderiv ℝ (fun w ↦ G₀ w j j)) z ep ep).re +
          (fderiv ℝ (fderiv ℝ (fun w ↦ G₀ w j j)) z fp fp).re) / 4) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hG₀Hess j]
  rw [hsumG₁, hsumG₀]
  change (∑ j, (fderiv ℝ (fderiv ℝ (fun w ↦ G₁ w j j)) z ep ep).re -
      ∑ j, eig j * (fderiv ℝ (fderiv ℝ (fun w ↦ G₀ w j j)) z ep ep).re +
      (∑ j, (fderiv ℝ (fderiv ℝ (fun w ↦ G₁ w j j)) z fp fp).re -
        ∑ j, eig j * (fderiv ℝ (fderiv ℝ (fun w ↦ G₀ w j j)) z fp fp).re)) / 4 =
      ∑ j, ((fderiv ℝ (fderiv ℝ (fun w ↦ G₁ w j j)) z ep ep).re +
        (fderiv ℝ (fderiv ℝ (fun w ↦ G₁ w j j)) z fp fp).re) / 4 -
        ∑ j, eig j * (((fderiv ℝ (fderiv ℝ (fun w ↦ G₀ w j j)) z ep ep).re +
          (fderiv ℝ (fderiv ℝ (fun w ↦ G₀ w j j)) z fp fp).re) / 4)
  have hA :
      (∑ j, (fderiv ℝ (fderiv ℝ (fun w ↦ G₁ w j j)) z ep ep).re) +
        (∑ j, (fderiv ℝ (fderiv ℝ (fun w ↦ G₁ w j j)) z fp fp).re) =
      ∑ j, ((fderiv ℝ (fderiv ℝ (fun w ↦ G₁ w j j)) z ep ep).re +
        (fderiv ℝ (fderiv ℝ (fun w ↦ G₁ w j j)) z fp fp).re) := by
    rw [← Finset.sum_add_distrib]
  have hB :
      (∑ j, eig j * (fderiv ℝ (fderiv ℝ (fun w ↦ G₀ w j j)) z ep ep).re) +
        (∑ j, eig j * (fderiv ℝ (fderiv ℝ (fun w ↦ G₀ w j j)) z fp fp).re) =
      ∑ j, eig j * ((fderiv ℝ (fderiv ℝ (fun w ↦ G₀ w j j)) z ep ep).re +
        (fderiv ℝ (fderiv ℝ (fun w ↦ G₀ w j j)) z fp fp).re) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  calc
    _ = ((∑ j, (fderiv ℝ (fderiv ℝ (fun w ↦ G₁ w j j)) z ep ep).re +
          ∑ j, (fderiv ℝ (fderiv ℝ (fun w ↦ G₁ w j j)) z fp fp).re) -
        (∑ j, eig j * (fderiv ℝ (fderiv ℝ (fun w ↦ G₀ w j j)) z ep ep).re +
          ∑ j, eig j * (fderiv ℝ (fderiv ℝ (fun w ↦ G₀ w j j)) z fp fp).re)) / 4 := by ring
    _ = ((∑ j, ((fderiv ℝ (fderiv ℝ (fun w ↦ G₁ w j j)) z ep ep).re +
          (fderiv ℝ (fderiv ℝ (fun w ↦ G₁ w j j)) z fp fp).re)) -
        ∑ j, eig j * ((fderiv ℝ (fderiv ℝ (fun w ↦ G₀ w j j)) z ep ep).re +
          (fderiv ℝ (fderiv ℝ (fun w ↦ G₀ w j j)) z fp fp).re)) / 4 := by rw [hA, hB]
    _ = ∑ j, ((fderiv ℝ (fderiv ℝ (fun w ↦ G₁ w j j)) z ep ep).re +
          (fderiv ℝ (fderiv ℝ (fun w ↦ G₁ w j j)) z fp fp).re) / 4 -
        ∑ j, eig j * ((fderiv ℝ (fderiv ℝ (fun w ↦ G₀ w j j)) z ep ep).re +
          (fderiv ℝ (fderiv ℝ (fun w ↦ G₀ w j j)) z fp fp).re) / 4 := by
      rw [sub_div, Finset.sum_div, Finset.sum_div]
    _ = _ := by
      apply congrArg₂ (fun a b : ℝ ↦ a - b)
      · rfl
      · apply Finset.sum_congr rfl
        intro j hj
        ring

public theorem complexHessian_relativeTraceMatrix_diag_of_normal
    {n : ℕ}
    (G₀ G₁ : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (eig : Fin n → ℝ)
    (hG₀ : ∀ j k, ContDiffAt ℝ 2 (fun w ↦ G₀ w j k) z)
    (hG₁ : ∀ j k, ContDiffAt ℝ 2 (fun w ↦ G₁ w j k) z)
    (hId : G₀ z = 1)
    (hDiag : G₁ z = Matrix.diagonal (Complex.ofReal ∘ eig))
    (hFirstReal : fderiv ℝ G₀ z = 0)
    (p : Fin n) :
    (complexHessian (fun w ↦ (((G₀ w)⁻¹ * G₁ w).trace).re) z p p).re =
      (∑ j, (chartPartialZComplex
        (fun w ↦ chartPartialBarComplex (fun v ↦ G₁ v j j) w p) z p).re) -
      ∑ j, eig j * (chartPartialZComplex
        (fun w ↦ chartPartialBarComplex (fun v ↦ G₀ v j j) w p) z p).re := by
  rw [complexHessian_relativeTraceMatrix_diag_real G₀ G₁ z eig
    hG₀ hG₁ hId hDiag hFirstReal p]
  apply congrArg₂ (fun a b : ℝ ↦ a - b)
  · apply Finset.sum_congr rfl
    intro j hj
    exact (realpart_complexWirtinger_eq_hessian (fun w ↦ G₁ w j j) z
      (hG₁ j j) p).symm
  · apply Finset.sum_congr rfl
    intro j hj
    exact congrArg (fun r : ℝ ↦ eig j * r)
      (realpart_complexWirtinger_eq_hessian (fun w ↦ G₀ w j j) z
        (hG₀ j j) p).symm

end KahlerForm
