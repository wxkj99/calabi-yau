module

public import CalabiYau.Mathlib.Analysis.Matrix.PosDef.LogDet

/-!
# The second jet of a matrix inverse in a normalized frame

At a point where a matrix-valued map is the identity and its first real derivative vanishes,
the second derivative of its inverse is the negative second derivative of the map. This is the
algebraic inverse-metric jet used in the reference-curvature term of the C² trace expansion.
The matrix norm is the elementwise norm used by `Matrix.contDiffAt_inv`.
-/

@[expose] public section

open scoped Matrix.Norms.Elementwise
open Filter Topology

namespace Matrix

private theorem contDiffAt_inv_comp
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : E → Matrix (Fin n) (Fin n) ℂ) (z : E)
    (hG : ContDiffAt ℝ 2 G z) (hId : G z = 1) :
    ContDiffAt ℝ 2 (fun w ↦ (G w)⁻¹) z := by
  have hUnit : IsUnit (G z).det := by
    simp [hId]
  have hle : (2 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
    change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.2 (by norm_num : (2 : ℕ∞) ≤ ⊤)
  have hInv : ContDiffAt ℝ (2 : WithTop ℕ∞)
      (fun B : Matrix (Fin n) (Fin n) ℂ ↦ B⁻¹) (G z) :=
    (Matrix.contDiffAt_inv hUnit).of_le hle
  exact ContDiffAt.comp z hInv hG

private theorem eventually_mul_inv_eq_one
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : E → Matrix (Fin n) (Fin n) ℂ) (z : E)
    (hG : ContDiffAt ℝ 2 G z) (hId : G z = 1) :
    ∀ᶠ w in 𝓝 z, G w * (G w)⁻¹ = 1 := by
  have hdetCont : ContinuousAt (fun w ↦ (G w).det) z :=
    continuous_id.matrix_det.continuousAt.comp hG.continuousAt
  have hdetz : (G z).det ≠ 0 := by simp [hId]
  have hdet_ne : ∀ᶠ w in 𝓝 z, (G w).det ≠ 0 :=
    hdetCont.eventually (isOpen_ne.mem_nhds hdetz)
  filter_upwards [hdet_ne] with w hw
  exact Matrix.mul_nonsing_inv (G w) hw.isUnit

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

/-- The ordered second real Fréchet derivative of the inverse at a normalized zero-first-jet
matrix is the negative of the original second derivative. -/
theorem fderiv_fderiv_inv_of_eq_one_of_fderiv_eq_zero
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : E → Matrix (Fin n) (Fin n) ℂ) (z : E)
    (hG : ContDiffAt ℝ 2 G z)
    (hId : G z = 1) (hFirst : fderiv ℝ G z = 0)
    (v u : E) :
    fderiv ℝ (fderiv ℝ (fun w ↦ (G w)⁻¹)) z v u =
      -(fderiv ℝ (fderiv ℝ G) z v u) := by
  have hInvReg := contDiffAt_inv_comp G z hG hId
  let H : E → Matrix (Fin n) (Fin n) ℂ := fun w ↦ (G w)⁻¹
  have hH : H z = 1 := by simp [H, hId]
  have hInvReg : ContDiffAt ℝ 2 H z := by
    simpa [H] using contDiffAt_inv_comp G z hG hId
  have hMat : (fun w ↦ G w * H w) =ᶠ[𝓝 z]
      fun _ ↦ (1 : Matrix (Fin n) (Fin n) ℂ) := by
    filter_upwards [eventually_mul_inv_eq_one G z hG hId] with w hw
    simpa [H] using hw
  have hGdiff : DifferentiableAt ℝ G z := hG.differentiableAt (by norm_num)
  have hfirstEntry (a l : Fin n) (d : E) :
      fderiv ℝ (fun w ↦ G w a l) z d = 0 := by
    have hGrow : ContDiffAt ℝ 2 (fun w ↦ G w a) z :=
      (contDiffAt_apply ℝ (Fin n → ℂ) a (G z)).comp z hG
    have hGrowDiff : DifferentiableAt ℝ (fun w ↦ G w a) z :=
      hGrow.differentiableAt (by norm_num)
    have hRowDer := fderiv_apply hGdiff a
    have hEntryDer := fderiv_apply hGrowDiff l
    calc
      fderiv ℝ (fun w ↦ G w a l) z d = (fderiv ℝ (fun w ↦ G w a) z d) l := by
        rw [hEntryDer]
        simp
      _ = (fderiv ℝ G z d) a l := by
        rw [hRowDer]
        rfl
      _ = 0 := by simp [hFirst]
  have hEntry (a b : Fin n) :
      (fun w ↦ ∑ l : Fin n, G w a l * H w l b) =ᶠ[𝓝 z]
        fun _ ↦ (1 : Matrix (Fin n) (Fin n) ℂ) a b := by
    filter_upwards [hMat] with w hw
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ ↦ M a b) hw
    simpa [Matrix.mul_apply] using h
  have hSecondZero (a b : Fin n) :
      fderiv ℝ (fderiv ℝ (fun w ↦ ∑ l : Fin n, G w a l * H w l b)) z v u = 0 := by
    have h1 := hEntry a b |>.fderiv (𝕜 := ℝ)
    have h2 := h1.fderiv_eq (𝕜 := ℝ) (x := z)
    have hEval := congrArg (fun L : E →L[ℝ] (E →L[ℝ] ℂ) ↦ L v u) h2
    simpa using hEval
  have hSumSecond (a b : Fin n) :
      fderiv ℝ (fderiv ℝ (fun w ↦ ∑ l : Fin n, G w a l * H w l b)) z v u =
        ∑ l : Fin n,
          fderiv ℝ (fderiv ℝ (fun w ↦ G w a l * H w l b)) z v u := by
    have hTerms (l : Fin n) :
        ContDiffAt ℝ 2 (fun w ↦ G w a l * H w l b) z := by
      have hGrow : ContDiffAt ℝ 2 (fun w ↦ G w a) z :=
        (contDiffAt_apply ℝ (Fin n → ℂ) a (G z)).comp z hG
      have hGentry : ContDiffAt ℝ 2 (fun w ↦ G w a l) z := by
        simpa [Function.comp_def] using
          (contDiffAt_apply ℝ ℂ l (G z a)).comp z hGrow
      have hHrow : ContDiffAt ℝ 2 (fun w ↦ H w l) z :=
        (contDiffAt_apply ℝ (Fin n → ℂ) l (H z)).comp z hInvReg
      have hHentry : ContDiffAt ℝ 2 (fun w ↦ H w l b) z := by
        simpa [Function.comp_def] using
          (contDiffAt_apply ℝ ℂ b (H z l)).comp z hHrow
      exact hGentry.mul hHentry
    have h := iteratedFDeriv_fun_sum_apply
      (u := Finset.univ) (n := 2) (x := z) (fun l _ ↦ hTerms l)
    have hEval := congrArg (fun T ↦ T ![v, u]) h
    rw [_root_.sum_apply] at hEval
    have hLeft :
        iteratedFDeriv ℝ 2 (fun w ↦ ∑ l : Fin n, G w a l * H w l b) z ![v, u] =
          fderiv ℝ (fderiv ℝ (fun w ↦ ∑ l : Fin n, G w a l * H w l b)) z v u := by
      rw [iteratedFDeriv_two_apply]
      simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    have hRight (l : Fin n) :
        iteratedFDeriv ℝ 2 (fun w ↦ G w a l * H w l b) z ![v, u] =
          fderiv ℝ (fderiv ℝ (fun w ↦ G w a l * H w l b)) z v u := by
      rw [iteratedFDeriv_two_apply]
      simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    calc
      _ = iteratedFDeriv ℝ 2 (fun w ↦ ∑ l : Fin n, G w a l * H w l b) z ![v, u] := hLeft.symm
      _ = ∑ l : Fin n, iteratedFDeriv ℝ 2 (fun w ↦ G w a l * H w l b) z ![v, u] := hEval
      _ = _ := by
        apply Finset.sum_congr rfl
        intro l hl
        exact hRight l
  have hTermsFormula (a b : Fin n) :
      (∑ l : Fin n,
          fderiv ℝ (fderiv ℝ (fun w ↦ G w a l * H w l b)) z v u) =
        ∑ l : Fin n,
          (G z a l * fderiv ℝ (fderiv ℝ (fun w ↦ H w l b)) z v u +
            fderiv ℝ (fun w ↦ G w a l) z v * fderiv ℝ (fun w ↦ H w l b) z u +
            fderiv ℝ (fun w ↦ G w a l) z u * fderiv ℝ (fun w ↦ H w l b) z v +
            H z l b * fderiv ℝ (fderiv ℝ (fun w ↦ G w a l)) z v u) := by
    apply Finset.sum_congr rfl
    intro l hl
    have hGrow : ContDiffAt ℝ 2 (fun w ↦ G w a) z :=
      (contDiffAt_apply ℝ (Fin n → ℂ) a (G z)).comp z hG
    have hGentry : ContDiffAt ℝ 2 (fun w ↦ G w a l) z := by
      simpa [Function.comp_def] using
        (contDiffAt_apply ℝ ℂ l (G z a)).comp z hGrow
    have hHrow : ContDiffAt ℝ 2 (fun w ↦ H w l) z :=
      (contDiffAt_apply ℝ (Fin n → ℂ) l (H z)).comp z hInvReg
    have hHentry : ContDiffAt ℝ 2 (fun w ↦ H w l b) z := by
      simpa [Function.comp_def] using
        (contDiffAt_apply ℝ ℂ b (H z l)).comp z hHrow
    exact fderiv_fderiv_mul_jet (fun w ↦ G w a l) (fun w ↦ H w l b) z
      hGentry hHentry v u
  ext a b
  have hzero := hSecondZero a b
  rw [hSumSecond, hTermsFormula] at hzero
  have hGvalue (l : Fin n) : G z a l = (1 : Matrix (Fin n) (Fin n) ℂ) a l := by
    rw [hId]
  have hHvalue (l : Fin n) : H z l b = (1 : Matrix (Fin n) (Fin n) ℂ) l b := by
    simp [H, hId]
  have hGterm (l : Fin n) : fderiv ℝ (fun w ↦ G w a l) z v = 0 := hfirstEntry a l v
  have hGterm' (l : Fin n) : fderiv ℝ (fun w ↦ G w a l) z u = 0 := hfirstEntry a l u
  simp only [hGvalue, hHvalue, hGterm, hGterm', Matrix.one_apply, zero_mul] at hzero
  simp only [Finset.sum_add_distrib, add_zero] at hzero
  have hsumH :
      (∑ l : Fin n,
        (if a = l then (1 : ℂ) else 0) * fderiv ℝ (fderiv ℝ (fun w ↦ H w l b)) z v u) =
        fderiv ℝ (fderiv ℝ (fun w ↦ H w a b)) z v u := by
    classical
    rw [Finset.sum_eq_single a]
    · simp
    · intro l hl hla
      simp [Ne.symm hla]
    · simp
  have hsumG :
      (∑ l : Fin n,
        (if l = b then (1 : ℂ) else 0) * fderiv ℝ (fderiv ℝ (fun w ↦ G w a l)) z v u) =
        fderiv ℝ (fderiv ℝ (fun w ↦ G w a b)) z v u := by
    classical
    rw [Finset.sum_eq_single b]
    · simp
    · intro l hl hlb
      simp [hlb]
    · simp
  have hzero' :
      fderiv ℝ (fderiv ℝ (fun w ↦ H w a b)) z v u +
        fderiv ℝ (fderiv ℝ (fun w ↦ G w a b)) z v u = 0 := by
    rw [← hsumH, ← hsumG]
    exact hzero
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ :=
    ((ContinuousLinearMap.proj b : (Fin n → ℂ) →L[ℝ] ℂ).comp
      (ContinuousLinearMap.proj a : Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin n → ℂ)))
  have hHiter := L.iteratedFDeriv_comp_left (f := H) hInvReg (i := 2) (by norm_num)
  have hHiterEval := congrArg (fun T ↦ T ![v, u]) hHiter
  have hHentryIter :
      iteratedFDeriv ℝ 2 (fun w ↦ H w a b) z ![v, u] =
        (iteratedFDeriv ℝ 2 H z ![v, u]) a b := by
    have h := hHiterEval
    simp [L, Function.comp_def] at h
    exact h
  have hHentrySecond :
      fderiv ℝ (fderiv ℝ (fun w ↦ H w a b)) z v u =
        (fderiv ℝ (fderiv ℝ H) z v u) a b := by
    calc
      _ = iteratedFDeriv ℝ 2 (fun w ↦ H w a b) z ![v, u] := by
        rw [iteratedFDeriv_two_apply]
        simp [Matrix.cons_val_zero, Matrix.cons_val_one]
      _ = (iteratedFDeriv ℝ 2 H z ![v, u]) a b := hHentryIter
      _ = _ := by
        rw [iteratedFDeriv_two_apply]
        rfl
  have hGiter := L.iteratedFDeriv_comp_left (f := G) hG (i := 2) (by norm_num)
  have hGiterEval := congrArg (fun T ↦ T ![v, u]) hGiter
  have hGentryIter :
      iteratedFDeriv ℝ 2 (fun w ↦ G w a b) z ![v, u] =
        (iteratedFDeriv ℝ 2 G z ![v, u]) a b := by
    have h := hGiterEval
    simp [L, Function.comp_def] at h
    exact h
  have hGentrySecond :
      fderiv ℝ (fderiv ℝ (fun w ↦ G w a b)) z v u =
        (fderiv ℝ (fderiv ℝ G) z v u) a b := by
    calc
      _ = iteratedFDeriv ℝ 2 (fun w ↦ G w a b) z ![v, u] := by
        rw [iteratedFDeriv_two_apply]
        simp [Matrix.cons_val_zero, Matrix.cons_val_one]
      _ = (iteratedFDeriv ℝ 2 G z ![v, u]) a b := hGentryIter
      _ = _ := by
        rw [iteratedFDeriv_two_apply]
        rfl
  change fderiv ℝ (fderiv ℝ H) z v u a b =
    -(fderiv ℝ (fderiv ℝ G) z v u) a b
  rw [← hHentrySecond, ← hGentrySecond]
  linear_combination hzero'

end Matrix
