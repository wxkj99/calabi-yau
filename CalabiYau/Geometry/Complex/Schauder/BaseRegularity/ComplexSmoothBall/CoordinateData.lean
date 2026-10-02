module

public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.ComplexSmoothBall.Basic
public import CalabiYau.Geometry.Complex.Schauder.RealCoordinateEquiv.Ellipticity

/-!
# Complex-to-real smooth operator data

Source: Gilbarg–Trudinger, §6.1, Theorem 6.2, freezing/interpolation proof;
Constantin, Schauder Estimates, pp. 6–9. The estimates follow Constantin, *Schauder Estimates*, pp. 6–9.
-/

@[expose] public section

open Set Matrix
open scoped NNReal ContDiff Topology

namespace CalabiYau.Schauder

private theorem holderBoundOn_zero_coordinate
    {E G F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃ₗᵢ[ℝ] G) {α C : ℝ≥0} {s : Set E} {f : E → F}
    (h : HolderBoundOn 0 α C s f) :
    HolderBoundOn 0 α C (e '' s) (f ∘ e.symm) := by
  have hval : HolderOnWith C α f s := by
    have hs : HolderOnWith C α (iteratedFDeriv ℝ 0 f) s := h.2
    rw [iteratedFDeriv_zero_eq_comp] at hs
    let c := continuousMultilinearCurryFin0 ℝ E F
    intro x hx y hy
    have hxy := hs x hx y hy
    change edist (c.symm (f x)) (c.symm (f y)) ≤
      (C : ENNReal) * edist x y ^ (α : ℝ) at hxy
    rw [c.symm.edist_map] at hxy
    exact hxy
  refine ⟨?_, ?_⟩
  · intro j hj y hy
    have hj0 : j = 0 := by omega
    subst j
    rcases hy with ⟨x, hx, rfl⟩
    simpa [norm_iteratedFDeriv_zero] using h.1 0 le_rfl x hx
  · rw [iteratedFDeriv_zero_eq_comp]
    let c := continuousMultilinearCurryFin0 ℝ G F
    intro y hy y' hy'
    rcases hy with ⟨x, hx, rfl⟩
    rcases hy' with ⟨x', hx', rfl⟩
    have hxy := hval x hx x' hx'
    change edist (c.symm (f (e.symm (e x)))) (c.symm (f (e.symm (e x')))) ≤
      (C : ENNReal) * edist (e x) (e x') ^ (α : ℝ)
    rw [e.symm_apply_apply, e.symm_apply_apply]
    rw [c.symm.edist_map, e.edist_map]
    exact hxy

private theorem holderBoundOn_neg_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α C : ℝ≥0} {U : Set E} {f : E → F}
    (hf : HolderBoundOn 0 α C U f) : HolderBoundOn 0 α C U (fun x => -f x) := by
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    have hj0 : j = 0 := by omega
    subst j
    have h := hf.1 0 le_rfl x hx
    simpa [norm_iteratedFDeriv_zero] using h
  · rw [iteratedFDeriv_zero_eq_comp]
    let c := continuousMultilinearCurryFin0 ℝ E F
    intro x hx y hy
    have h := hf.2 x hx y hy
    change edist (c.symm (f x)) (c.symm (f y)) ≤
      (C : ENNReal) * edist x y ^ (α : ℝ) at h
    rw [c.symm.edist_map] at h
    change edist (c.symm (-f x)) (c.symm (-f y)) ≤ _
    rw [c.symm.edist_map]
    simpa only [edist_neg_neg] using h

private theorem holderBoundOn_complex_to_quarterRe
    {n : ℕ} {α C : ℝ≥0} {U : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → ℂ}
    (hf : HolderBoundOn 0 α C U f) :
    HolderBoundOn 0 α C U (fun z => (1 / 4 : ℝ) * (f z).re) := by
  have hnorm (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U) : ‖f z‖ ≤ C := by
    simpa [norm_iteratedFDeriv_zero] using hf.1 0 (by omega) z hz
  have hholder : HolderOnWith C α f U := by
    have hs : HolderOnWith C α (iteratedFDeriv ℝ 0 f) U := hf.2
    rw [iteratedFDeriv_zero_eq_comp] at hs
    let c := continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℂ (Fin n)) ℂ
    intro x hx y hy
    have h := hs x hx y hy
    change edist (c.symm (f x)) (c.symm (f y)) ≤
      (C : ENNReal) * edist x y ^ (α : ℝ) at h
    rw [c.symm.edist_map] at h
    exact h
  have hquarter : HolderOnWith C α (fun z => (1 / 4 : ℝ) * (f z).re) U := by
    intro x hx y hy
    have h := hholder x hx y hy
    have hdist : dist ((1 / 4 : ℝ) * (f x).re) ((1 / 4 : ℝ) * (f y).re) ≤ dist (f x) (f y) := by
      rw [Real.dist_eq, dist_eq_norm]
      calc
        |(1 / 4 : ℝ) * (f x).re - (1 / 4 : ℝ) * (f y).re| =
            (1 / 4 : ℝ) * |(f x - f y).re| := by
          rw [show (1 / 4 : ℝ) * (f x).re - (1 / 4 : ℝ) * (f y).re =
            (1 / 4 : ℝ) * ((f x).re - (f y).re) by ring, abs_mul]
          rw [Complex.sub_re]
          norm_num
        _ ≤ |(f x - f y).re| := by nlinarith [abs_nonneg (f x - f y).re]
        _ ≤ ‖f x - f y‖ := Complex.abs_re_le_norm _
    calc
      edist ((1 / 4 : ℝ) * (f x).re) ((1 / 4 : ℝ) * (f y).re) =
          ENNReal.ofReal (dist ((1 / 4 : ℝ) * (f x).re) ((1 / 4 : ℝ) * (f y).re)) := edist_dist _ _
      _ ≤ ENNReal.ofReal (dist (f x) (f y)) := ENNReal.ofReal_le_ofReal hdist
      _ = edist (f x) (f y) := (edist_dist _ _).symm
      _ ≤ (C : ENNReal) * edist x y ^ (α : ℝ) := h
  refine ⟨?_, ?_⟩
  · intro j hj z hz
    have hj0 : j = 0 := by omega
    subst j
    have h := hnorm z hz
    rw [norm_iteratedFDeriv_zero]
    change |(1 / 4 : ℝ) * (f z).re| ≤ (C : ℝ)
    calc
      |(1 / 4 : ℝ) * (f z).re| ≤ |(f z).re| := by
        calc
          |(1 / 4 : ℝ) * (f z).re| = (1 / 4 : ℝ) * |(f z).re| := by rw [abs_mul]; norm_num
          _ ≤ |(f z).re| := by nlinarith [abs_nonneg (f z).re]
      _ ≤ ‖f z‖ := Complex.abs_re_le_norm _
      _ ≤ C := h
  ·
    change HolderOnWith C α (iteratedFDeriv ℝ 0 (fun z => (1 / 4 : ℝ) * (f z).re)) U
    rw [iteratedFDeriv_zero_eq_comp]
    let c := continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℂ (Fin n)) ℝ
    intro x hx y hy
    have h := hquarter x hx y hy
    change edist (c.symm ((1 / 4 : ℝ) * (f x).re))
      (c.symm ((1 / 4 : ℝ) * (f y).re)) ≤ (C : ENNReal) * edist x y ^ (α : ℝ)
    rw [c.symm.edist_map]
    exact h

private theorem holderBoundOn_complex_to_quarterIm
    {n : ℕ} {α C : ℝ≥0} {U : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → ℂ}
    (hf : HolderBoundOn 0 α C U f) :
    HolderBoundOn 0 α C U (fun z => (1 / 4 : ℝ) * (f z).im) := by
  have hnorm (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U) : ‖f z‖ ≤ C := by
    simpa [norm_iteratedFDeriv_zero] using hf.1 0 (by omega) z hz
  have hholder : HolderOnWith C α f U := by
    have hs : HolderOnWith C α (iteratedFDeriv ℝ 0 f) U := hf.2
    rw [iteratedFDeriv_zero_eq_comp] at hs
    let c := continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℂ (Fin n)) ℂ
    intro x hx y hy
    have h := hs x hx y hy
    change edist (c.symm (f x)) (c.symm (f y)) ≤
      (C : ENNReal) * edist x y ^ (α : ℝ) at h
    rw [c.symm.edist_map] at h
    exact h
  have hquarter : HolderOnWith C α (fun z => (1 / 4 : ℝ) * (f z).im) U := by
    intro x hx y hy
    have h := hholder x hx y hy
    have hdist : dist ((1 / 4 : ℝ) * (f x).im) ((1 / 4 : ℝ) * (f y).im) ≤ dist (f x) (f y) := by
      rw [Real.dist_eq, dist_eq_norm]
      calc
        |(1 / 4 : ℝ) * (f x).im - (1 / 4 : ℝ) * (f y).im| =
            (1 / 4 : ℝ) * |(f x - f y).im| := by
          rw [show (1 / 4 : ℝ) * (f x).im - (1 / 4 : ℝ) * (f y).im =
            (1 / 4 : ℝ) * ((f x).im - (f y).im) by ring, abs_mul]
          rw [Complex.sub_im]
          norm_num
        _ ≤ |(f x - f y).im| := by nlinarith [abs_nonneg (f x - f y).im]
        _ ≤ ‖f x - f y‖ := Complex.abs_im_le_norm _
    calc
      edist ((1 / 4 : ℝ) * (f x).im) ((1 / 4 : ℝ) * (f y).im) =
          ENNReal.ofReal (dist ((1 / 4 : ℝ) * (f x).im) ((1 / 4 : ℝ) * (f y).im)) := edist_dist _ _
      _ ≤ ENNReal.ofReal (dist (f x) (f y)) := ENNReal.ofReal_le_ofReal hdist
      _ = edist (f x) (f y) := (edist_dist _ _).symm
      _ ≤ (C : ENNReal) * edist x y ^ (α : ℝ) := h
  refine ⟨?_, ?_⟩
  · intro j hj z hz
    have hj0 : j = 0 := by omega
    subst j
    have h := hnorm z hz
    rw [norm_iteratedFDeriv_zero]
    change |(1 / 4 : ℝ) * (f z).im| ≤ (C : ℝ)
    calc
      |(1 / 4 : ℝ) * (f z).im| ≤ |(f z).im| := by
        calc
          |(1 / 4 : ℝ) * (f z).im| = (1 / 4 : ℝ) * |(f z).im| := by rw [abs_mul]; norm_num
          _ ≤ |(f z).im| := by nlinarith [abs_nonneg (f z).im]
      _ ≤ ‖f z‖ := Complex.abs_im_le_norm _
      _ ≤ C := h
  ·
    change HolderOnWith C α (iteratedFDeriv ℝ 0 (fun z => (1 / 4 : ℝ) * (f z).im)) U
    rw [iteratedFDeriv_zero_eq_comp]
    let c := continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℂ (Fin n)) ℝ
    intro x hx y hy
    have h := hquarter x hx y hy
    change edist (c.symm ((1 / 4 : ℝ) * (f x).im))
      (c.symm ((1 / 4 : ℝ) * (f y).im)) ≤ (C : ENNReal) * edist x y ^ (α : ℝ)
    rw [c.symm.edist_map]
    exact h

private theorem form00 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    realPrincipalCoefficient A (i, 0) (j, 0) = (1 / 4 : ℝ) * (A j i).re := by
  simp [realPrincipalCoefficient, Matrix.smul_apply, smul_eq_mul,
    Matrix.realify_apply, Matrix.transpose_apply]
private theorem form01 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    realPrincipalCoefficient A (i, 0) (j, 1) = -(1 / 4 : ℝ) * (A j i).im := by
  simp [realPrincipalCoefficient, Matrix.smul_apply, smul_eq_mul,
    Matrix.realify_apply, Matrix.transpose_apply]
private theorem form10 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    realPrincipalCoefficient A (i, 1) (j, 0) = (1 / 4 : ℝ) * (A j i).im := by
  simp [realPrincipalCoefficient, Matrix.smul_apply, smul_eq_mul,
    Matrix.realify_apply, Matrix.transpose_apply]
private theorem form11 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    realPrincipalCoefficient A (i, 1) (j, 1) = (1 / 4 : ℝ) * (A j i).re := by
  simp [realPrincipalCoefficient, Matrix.smul_apply, smul_eq_mul,
    Matrix.realify_apply, Matrix.transpose_apply]

private theorem realPrincipalCoefficient_holderBoundOn
    {n : ℕ} {α K : ℝ≥0} {U : Set (EuclideanSpace ℂ (Fin n))}
    {A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ i j, HolderBoundOn 0 α K U (fun z => A z i j)) :
    ∀ p q, HolderBoundOn 0 α K (complexToRealCoordinateEquiv '' U)
      (fun y => realPrincipalCoefficient (A ((complexToRealCoordinateEquiv).symm y)) p q) := by
  intro p q
  rcases p with ⟨i, a⟩
  rcases q with ⟨j, b⟩
  fin_cases a <;> fin_cases b
  ·
    change HolderBoundOn 0 α K (complexToRealCoordinateEquiv '' U)
      (fun y => realPrincipalCoefficient (A ((complexToRealCoordinateEquiv).symm y)) (i, 0) (j, 0))
    have h := holderBoundOn_complex_to_quarterRe (hA j i)
    have hc := holderBoundOn_zero_coordinate (complexToRealCoordinateEquiv (n := n)) h
    have heq : (fun y => realPrincipalCoefficient (A ((complexToRealCoordinateEquiv).symm y)) (i, 0) (j, 0)) =
        ((fun z => (1 / 4 : ℝ) * (A z j i).re) ∘ (complexToRealCoordinateEquiv).symm) := by
      funext y
      simp [form00]
    rw [heq]
    exact hc
  ·
    change HolderBoundOn 0 α K (complexToRealCoordinateEquiv '' U)
      (fun y => realPrincipalCoefficient (A ((complexToRealCoordinateEquiv).symm y)) (i, 0) (j, 1))
    have h := holderBoundOn_neg_zero (hA j i)
    have h := holderBoundOn_complex_to_quarterIm h
    have hc := holderBoundOn_zero_coordinate (complexToRealCoordinateEquiv (n := n)) h
    have heq : (fun y => realPrincipalCoefficient (A ((complexToRealCoordinateEquiv).symm y)) (i, 0) (j, 1)) =
        ((fun z => (1 / 4 : ℝ) * ((-A z j i).im)) ∘ (complexToRealCoordinateEquiv).symm) := by
      funext y
      simp [Complex.neg_im, form01]
    rw [heq]
    exact hc
  ·
    change HolderBoundOn 0 α K (complexToRealCoordinateEquiv '' U)
      (fun y => realPrincipalCoefficient (A ((complexToRealCoordinateEquiv).symm y)) (i, 1) (j, 0))
    have h := holderBoundOn_complex_to_quarterIm (hA j i)
    have hc := holderBoundOn_zero_coordinate (complexToRealCoordinateEquiv (n := n)) h
    have heq : (fun y => realPrincipalCoefficient (A ((complexToRealCoordinateEquiv).symm y)) (i, 1) (j, 0)) =
        ((fun z => (1 / 4 : ℝ) * (A z j i).im) ∘ (complexToRealCoordinateEquiv).symm) := by
      funext y
      simp [form10]
    rw [heq]
    exact hc
  ·
    change HolderBoundOn 0 α K (complexToRealCoordinateEquiv '' U)
      (fun y => realPrincipalCoefficient (A ((complexToRealCoordinateEquiv).symm y)) (i, 1) (j, 1))
    have h := holderBoundOn_complex_to_quarterRe (hA j i)
    have hc := holderBoundOn_zero_coordinate (complexToRealCoordinateEquiv (n := n)) h
    have heq : (fun y => realPrincipalCoefficient (A ((complexToRealCoordinateEquiv).symm y)) (i, 1) (j, 1)) =
        ((fun z => (1 / 4 : ℝ) * (A z j i).re) ∘ (complexToRealCoordinateEquiv).symm) := by
      funext y
      simp [form11]
    rw [heq]
    exact hc

private theorem holderBoundOn_zero_congr_on
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α C : ℝ≥0} {s : Set E} {f g : E → F}
    (hfg : ∀ x ∈ s, f x = g x) (hf : HolderBoundOn 0 α C s f) :
    HolderBoundOn 0 α C s g := by
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    have hj0 : j = 0 := by omega
    subst j
    simpa [norm_iteratedFDeriv_zero, hfg x hx] using hf.1 0 le_rfl x hx
  · rw [iteratedFDeriv_zero_eq_comp]
    let c := continuousMultilinearCurryFin0 ℝ E F
    intro x hx y hy
    have h := hf.2 x hx y hy
    change edist (c.symm (f x)) (c.symm (f y)) ≤
      (C : ENNReal) * edist x y ^ (α : ℝ) at h
    rw [c.symm.edist_map] at h
    change edist (c.symm (g x)) (c.symm (g y)) ≤ _
    rw [c.symm.edist_map]
    rw [← hfg x hx, ← hfg y hy]
    exact h

private theorem complex_realSmoothBallData_adapter :
    ∀ {n : ℕ} {α lam K K₀ K₁ : ℝ≥0}
  {U : Set (EuclideanSpace ℂ (Fin n))}
  {A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
  {u : EuclideanSpace ℂ (Fin n) → ℝ},
  0 < lam → IsOpen U →
  (∀ i j, ContDiffOn ℝ ∞ (fun z => A z i j) U) → ContDiffOn ℝ ∞ u U →
  IsUniformlyEllipticOn A lam U →
  (∀ i j, HolderBoundOn 0 α K U (fun z => A z i j)) →
  HolderBoundOn 0 α K₁ U (complexEllipticOp A u) →
  (∀ z ∈ U, |u z| ≤ K₀) →
  RealSmoothBallData α (lam/4) K K₀ K₁
    ((complexToRealCoordinateEquiv (n := n)).symm ⁻¹' U)
    (fun y => realPrincipalCoefficient (A ((complexToRealCoordinateEquiv (n := n)).symm y)))
    (fun y => u ((complexToRealCoordinateEquiv (n := n)).symm y)) := by
  intro n α lam K K₀ K₁ U A u hLam hU hAsmooth huSmooth hEll hAHolder hSourceHolder hBound
  let e := complexToRealCoordinateEquiv (n := n)
  let V : Set (RealBallModel n) := e.symm ⁻¹' U
  let a : RealBallModel n → Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ :=
    fun y => realPrincipalCoefficient (A (e.symm y))
  let uR : RealBallModel n → ℝ := fun y => u (e.symm y)
  have he : ContDiff ℝ ∞ (e.symm : RealBallModel n → EuclideanSpace ℂ (Fin n)) := by
    fun_prop
  have hVimage : e '' U = V := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [V] using hz
    · intro hy
      exact ⟨e.symm y, hy, e.apply_symm_apply y⟩
  change RealSmoothBallData α (lam/4) K K₀ K₁ V a uR
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p q
    rcases p with ⟨i, aidx⟩
    rcases q with ⟨j, bidx⟩
    have hcomp : ContDiffOn ℝ ∞ (fun y : RealBallModel n => A (e.symm y) j i) V := by
      apply (hAsmooth j i).comp he.contDiffOn
      intro y hy
      exact hy
    have hRe : ContDiffOn ℝ ∞ (fun y : RealBallModel n => (A (e.symm y) j i).re) V :=
      Complex.reCLM.contDiff.comp_contDiffOn hcomp
    have hIm : ContDiffOn ℝ ∞ (fun y : RealBallModel n => (A (e.symm y) j i).im) V :=
      Complex.imCLM.contDiff.comp_contDiffOn hcomp
    have hquarterConst : ContDiffOn ℝ ∞ (fun _ : RealBallModel n => (1 / 4 : ℝ)) V :=
      contDiff_const.contDiffOn
    have hReQuarter : ContDiffOn ℝ ∞
        (fun y : RealBallModel n => (1 / 4 : ℝ) * (A (e.symm y) j i).re) V :=
      by simpa [mul_comm] using hRe.mul hquarterConst
    have hImQuarter : ContDiffOn ℝ ∞
        (fun y : RealBallModel n => (1 / 4 : ℝ) * (A (e.symm y) j i).im) V :=
      by simpa [mul_comm] using hIm.mul hquarterConst
    fin_cases aidx <;> fin_cases bidx
    · simpa [a, realPrincipalCoefficient, Matrix.smul_apply, smul_eq_mul,
        Matrix.realify_apply, Matrix.transpose_apply, e] using hReQuarter
    · simpa [a, realPrincipalCoefficient, Matrix.smul_apply, smul_eq_mul,
        Matrix.realify_apply, Matrix.transpose_apply, e] using hImQuarter.neg
    · simpa [a, realPrincipalCoefficient, Matrix.smul_apply, smul_eq_mul,
        Matrix.realify_apply, Matrix.transpose_apply, e] using hImQuarter
    · simpa [a, realPrincipalCoefficient, Matrix.smul_apply, smul_eq_mul,
        Matrix.realify_apply, Matrix.transpose_apply, e] using hReQuarter
  · have hcomp : ContDiffOn ℝ ∞ uR V := by
      apply huSmooth.comp he.contDiffOn
      intro y hy
      exact hy
    change ContDiffOn ℝ ∞ (fun y => u (e.symm y)) V
    exact hcomp
  · intro y hy
    exact (realPrincipalCoefficient_ellipticity hLam hEll hAHolder (e.symm y) hy).1
  · intro y hy v
    have h := (realPrincipalCoefficient_ellipticity hLam hEll hAHolder (e.symm y) hy).2 v
    simpa using h.1
  · intro p q
    have h := realPrincipalCoefficient_holderBoundOn hAHolder p q
    have h' := h.mono_set (by rw [hVimage])
    simpa [a, e] using h'
  · have hcoord := holderBoundOn_zero_coordinate e hSourceHolder
    have hcoord' := hcoord.mono_set (by rw [hVimage])
    have hpoint : ∀ y ∈ V, realBallSource a uR y = complexEllipticOp A u (e.symm y) := by
      intro y hy
      have hz : e.symm y ∈ U := hy
      have huAtInf : ContDiffAt ℝ ∞ u (e.symm y) :=
        huSmooth.contDiffAt (hU.mem_nhds hz)
      have huAt : ContDiffAt ℝ 2 u (e.symm y) :=
        huAtInf.of_le (WithTop.coe_le_coe.2 (OrderTop.le_top _))
      have heval : complexToRealCoordinateEquiv (e.symm y) = y := by
        change e (e.symm y) = y
        exact e.apply_symm_apply y
      have hmatrix := complexPrincipalOperator_eq_matrixLap
        (A (e.symm y)) u (e.symm y) huAt
      rw [heval] at hmatrix
      dsimp [realBallSource, a, uR]
      change HeatEquation.matrixLap (realPrincipalCoefficient (A (e.symm y)))
          (fderiv ℝ (fderiv ℝ (fun y => u (e.symm y))) y) =
        complexPrincipalOperator (A (e.symm y)) u (e.symm y)
      exact hmatrix.symm
    exact holderBoundOn_zero_congr_on (fun y hy => (hpoint y hy).symm) hcoord'
  · intro y hy
    exact hBound (e.symm y) hy

/-- An isometric coordinate adapter, not an elliptic estimate. -/
theorem complex_realSmoothBallData :
    ∀ {n : ℕ} {α lam K K₀ K₁ : ℝ≥0}
  {U : Set (EuclideanSpace ℂ (Fin n))}
  {A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
  {u : EuclideanSpace ℂ (Fin n) → ℝ},
  0 < lam → IsOpen U →
  (∀ i j, ContDiffOn ℝ ∞ (fun z => A z i j) U) → ContDiffOn ℝ ∞ u U →
  IsUniformlyEllipticOn A lam U →
  (∀ i j, HolderBoundOn 0 α K U (fun z => A z i j)) →
  HolderBoundOn 0 α K₁ U (complexEllipticOp A u) →
  (∀ z ∈ U, |u z| ≤ K₀) →
  RealSmoothBallData α (lam/4) K K₀ K₁
    (complexToRealCoordinateEquiv.symm ⁻¹' U)
    (fun y => realPrincipalCoefficient (A (complexToRealCoordinateEquiv.symm y)))
    (fun y => u (complexToRealCoordinateEquiv.symm y)) := by
  exact complex_realSmoothBallData_adapter

end CalabiYau.Schauder
