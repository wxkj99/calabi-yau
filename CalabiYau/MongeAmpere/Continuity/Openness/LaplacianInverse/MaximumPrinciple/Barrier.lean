module

public import CalabiYau.Geometry.Complex.Schauder
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Radial exponential strict barriers

Gilbarg–Trudinger, §3.2, Lemma 3.4: the exponential radial barrier on an annulus.
For our normalization `L_1 = Δ/4`, the radial formula is
`L_1 v = exp(-a ρ²) (a² ρ² - a n)`.
This proves the differentiation and coefficient estimate used in the comparison argument.
-/

@[expose] public section

open scoped ContDiff NNReal Topology
open Set

private theorem translated_normSq_complexHessian {n : ℕ}
    (c y : EuclideanSpace ℂ (Fin n)) :
    complexHessian (fun w : EuclideanSpace ℂ (Fin n) => ‖w - c‖ ^ 2) y = 1 := by
  let ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) := fun w => w - c
  let q : EuclideanSpace ℂ (Fin n) → ℝ := fun w => ‖w‖ ^ 2
  have hψ : ∀ᶠ w in 𝓝 y, DifferentiableAt ℂ ψ w := by
    filter_upwards with w
    exact differentiableAt_id.sub_const c
  have hq : ContDiffAt ℝ 2 q (ψ y) := by
    dsimp [q]
    exact contDiffAt_id.norm_sq ℝ
  have hcomp := ddbar_comp_holomorphic (f := q) (ψ := ψ) (z := y) hψ hq
  have hderiv : fderiv ℂ ψ y = ContinuousLinearMap.id ℂ _ := by
    simp [ψ, fderiv_sub_const]
  have hform : ddbar (fun w : EuclideanSpace ℂ (Fin n) => ‖w - c‖ ^ 2) y =
      ddbar q (ψ y) := by
    change ddbar (q ∘ ψ) y = ddbar q (ψ y)
    rw [hcomp, hderiv]
    ext v
    rfl
  ext j k
  change (ddbar (fun w : EuclideanSpace ℂ (Fin n) => ‖w - c‖ ^ 2) y).coeffMatrix j k =
    (1 : Matrix (Fin n) (Fin n) ℂ) j k
  rw [hform]
  change (complexHessian q (ψ y)) j k = (1 : Matrix (Fin n) (Fin n) ℂ) j k
  exact congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M j k)
    (complexHessian_normSq (ψ y))

private theorem translated_normSq_complexGradient {n : ℕ}
    (c y : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
    fderiv ℝ (fun w : EuclideanSpace ℂ (Fin n) => ‖w - c‖ ^ 2) y
      (EuclideanSpace.single j 1) = 2 * Complex.re (y j - c j) := by
  let : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin n)) :=
    InnerProductSpace.rclikeToReal ℂ (EuclideanSpace ℂ (Fin n))
  let ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) := fun w => w - c
  let q : EuclideanSpace ℂ (Fin n) → ℝ := fun w => ‖w‖ ^ 2
  have hψ : DifferentiableAt ℝ ψ y := differentiableAt_id.sub_const c
  have hqC : ContDiffAt ℝ 2 q (ψ y) := by
    dsimp [q]
    exact contDiffAt_id.norm_sq ℝ
  have hq : DifferentiableAt ℝ q (ψ y) := hqC.differentiableAt (by norm_num)
  have hcomp := fderiv_comp (f := ψ) (g := q) (x := y) hq hψ
  rw [show (fun w : EuclideanSpace ℂ (Fin n) => ‖w - c‖ ^ 2) = q ∘ ψ by rfl, hcomp]
  rw [fderiv_sub_const, fderiv_norm_sq, fderiv_fun_id]
  change (2 • innerSL ℝ (ψ y)) (EuclideanSpace.single j 1) = _
  rw [_root_.smul_apply, innerSL_apply_apply, real_inner_eq_re_inner ℂ,
    EuclideanSpace.inner_single_right]
  simp [ψ]

private theorem translated_normSq_complexGradient_im {n : ℕ}
    (c y : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
    fderiv ℝ (fun w : EuclideanSpace ℂ (Fin n) => ‖w - c‖ ^ 2) y
      (Complex.I • EuclideanSpace.single j 1) = 2 * Complex.im (y j - c j) := by
  let : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin n)) :=
    InnerProductSpace.rclikeToReal ℂ (EuclideanSpace ℂ (Fin n))
  let ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) := fun w => w - c
  let q : EuclideanSpace ℂ (Fin n) → ℝ := fun w => ‖w‖ ^ 2
  have hψ : DifferentiableAt ℝ ψ y := differentiableAt_id.sub_const c
  have hqC : ContDiffAt ℝ 2 q (ψ y) := by
    dsimp [q]
    exact contDiffAt_id.norm_sq ℝ
  have hq : DifferentiableAt ℝ q (ψ y) := hqC.differentiableAt (by norm_num)
  have hcomp := fderiv_comp (f := ψ) (g := q) (x := y) hq hψ
  rw [show (fun w : EuclideanSpace ℂ (Fin n) => ‖w - c‖ ^ 2) = q ∘ ψ by rfl, hcomp]
  rw [fderiv_sub_const, fderiv_norm_sq, fderiv_fun_id]
  change (2 • innerSL ℝ (ψ y)) (Complex.I • EuclideanSpace.single j 1) = _
  rw [_root_.smul_apply, innerSL_apply_apply, real_inner_eq_re_inner ℂ]
  rw [inner_smul_right, EuclideanSpace.inner_single_right]
  simp [ψ]
  ring

private theorem translated_normSq_gradient_wedge_coeff {n : ℕ}
    (c y : EuclideanSpace ℂ (Fin n)) :
    (ContinuousAlternatingMap.dWedgeDBar
      (fderiv ℝ (fun w : EuclideanSpace ℂ (Fin n) => ‖w - c‖ ^ 2) y)).coeffMatrix =
      Matrix.vecMulVec (fun j => star (y j - c j)) (fun k => y k - c k) := by
  rw [ContinuousAlternatingMap.coeffMatrix_dWedgeDBar]
  ext j k
  simp only [Matrix.vecMulVec_apply, translated_normSq_complexGradient,
    translated_normSq_complexGradient_im]
  congr 1 <;> apply Complex.ext <;>
    (simp [Complex.sub_re, Complex.sub_im] <;> ring_nf)

private theorem translated_radial_composition_hessian {n : ℕ}
    (c y : EuclideanSpace ℂ (Fin n)) (h : ℝ → ℝ)
    (hh : ContDiffAt ℝ 2 h (‖y - c‖ ^ 2)) :
    complexHessian (h ∘ (fun w : EuclideanSpace ℂ (Fin n) => ‖w - c‖ ^ 2)) y =
      deriv h (‖y - c‖ ^ 2) • (1 : Matrix (Fin n) (Fin n) ℂ) +
        deriv (deriv h) (‖y - c‖ ^ 2) •
          Matrix.vecMulVec (fun j => star (y j - c j)) (fun k => y k - c k) := by
  let q : EuclideanSpace ℂ (Fin n) → ℝ := fun w => ‖w - c‖ ^ 2
  let ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) := fun w => w - c
  let q₀ : EuclideanSpace ℂ (Fin n) → ℝ := fun w => ‖w‖ ^ 2
  have hψ : ContDiffAt ℝ 2 ψ y := by
    dsimp [ψ]
    fun_prop
  have hq₀ : ContDiffAt ℝ 2 q₀ (ψ y) := by
    dsimp [q₀]
    exact contDiffAt_id.norm_sq ℝ
  have hq : ContDiffAt ℝ 2 q y := by
    change ContDiffAt ℝ 2 (q₀ ∘ ψ) y
    exact hq₀.comp y hψ
  have hchain := ddbar_comp_real (f := q) hh hq
  have hqH : (ddbar q y).coeffMatrix = 1 := by
    change complexHessian q y = 1
    dsimp [q]
    exact translated_normSq_complexHessian c y
  have hqD : (ContinuousAlternatingMap.dWedgeDBar (fderiv ℝ q y)).coeffMatrix =
      Matrix.vecMulVec (fun j => star (y j - c j)) (fun k => y k - c k) := by
    exact translated_normSq_gradient_wedge_coeff c y
  ext j k
  change (ddbar (h ∘ q) y).coeffMatrix j k = _
  rw [hchain, ContinuousAlternatingMap.coeffMatrix_add,
    ContinuousAlternatingMap.coeffMatrix_smul, ContinuousAlternatingMap.coeffMatrix_smul,
    hqH, hqD]

private theorem radial_outer_re_lower {n : ℕ}
    (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    {c y : EuclideanSpace ℂ (Fin n)} {R : ℝ} {lam : ℝ≥0}
    (hEll : IsUniformlyEllipticOn A lam (Metric.ball c R))
    (hy : y ∈ Metric.ball c R) :
    (lam : ℝ) * ‖y - c‖ ^ 2 ≤
      RCLike.re ((A y * Matrix.vecMulVec (fun j => star (y j - c j))
        (fun k => y k - c k)).trace) := by
  obtain ⟨_, hpos⟩ := hEll y hy
  let p : Fin n → ℂ := fun i => star (y i - c i)
  have hp := hpos p
  have hnorm : (∑ i, ‖p i‖ ^ 2) = ‖y - c‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ i, ‖star ((y - c) i)‖ ^ 2) = _
    simp only [norm_star]
  have hmatrix :
      RCLike.re (dotProduct (star p) ((A y).mulVec p)) =
        RCLike.re ((A y * Matrix.vecMulVec (fun j => star (y j - c j))
          (fun k => y k - c k)).trace) := by
    have hcomplex : dotProduct (star p) ((A y).mulVec p) =
        ((A y) * Matrix.vecMulVec (fun j => star (y j - c j))
          (fun k => y k - c k)).trace := by
      rw [Matrix.dotProduct_mulVec]
      simp only [Matrix.vecMul, dotProduct, Matrix.trace, Matrix.diag_apply,
        Matrix.mul_apply, Matrix.vecMulVec_apply]
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      simp [p, star_sub]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring_nf
    exact congrArg RCLike.re hcomplex
  calc
    (lam : ℝ) * ‖y - c‖ ^ 2 = (lam : ℝ) * ∑ i, ‖p i‖ ^ 2 := by rw [hnorm]
    _ ≤ RCLike.re (dotProduct (star p) ((A y).mulVec p)) := hp
    _ = _ := hmatrix

private theorem radial_trace_re_upper {n : ℕ}
    (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    {c y : EuclideanSpace ℂ (Fin n)} {R : ℝ} {lam K : ℝ≥0}
    (hEll : IsUniformlyEllipticOn A lam (Metric.ball c R))
    (hbound : ∀ y ∈ Metric.ball c R, ∀ j k, ‖A y j k‖ ≤ (K : ℝ))
    (hy : y ∈ Metric.ball c R) :
    RCLike.re (Matrix.trace (A y)) ≤ (n : ℝ) * (K : ℝ) := by
  obtain ⟨hHerm, _⟩ := hEll y hy
  have hdiag (j : Fin n) : RCLike.re (A y j j) ≤ (K : ℝ) := by
    have hre : (A y j j).re ≤ ‖A y j j‖ := Complex.re_le_norm _
    simpa using hre.trans (hbound y hy j j)
  rw [Matrix.trace, map_sum]
  calc
    (∑ i, RCLike.re (A y i i)) ≤ ∑ _i : Fin n, (K : ℝ) :=
      Finset.sum_le_sum (fun i hi => hdiag i)
    _ = (n : ℝ) * (K : ℝ) := by simp

private theorem exponential_barrier_parameter {n : ℕ} {R : ℝ} (hR : 0 < R)
    {lam K : ℝ≥0} (hlam : 0 < lam) :
    ∃ a : ℝ, 0 < a ∧ (n : ℝ) * (K : ℝ) < a * (lam : ℝ) * (R / 2) ^ 2 := by
  let a : ℝ := 4 * ((n : ℝ) * (K : ℝ) + 1) / ((lam : ℝ) * R ^ 2)
  have hlamR : 0 < (lam : ℝ) * R ^ 2 :=
    mul_pos (by exact_mod_cast hlam) (sq_pos_of_pos hR)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hscale :
      a * (lam : ℝ) * (R / 2) ^ 2 = (n : ℝ) * (K : ℝ) + 1 := by
    dsimp [a]
    field_simp [ne_of_gt hlamR]
    ring
  refine ⟨a, ha, ?_⟩
  rw [hscale]
  linarith

private theorem exponential_radial_profile_zero_on_sphere {n : ℕ} (a R : ℝ)
    (c y : EuclideanSpace ℂ (Fin n)) (hy : y ∈ Metric.sphere c R) :
    Real.exp (-a * ‖y - c‖ ^ 2) - Real.exp (-a * R ^ 2) = 0 := by
  have hnorm : ‖y - c‖ = R := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hy
  rw [hnorm]
  ring

private theorem exponential_affine_deriv (a t : ℝ) :
    deriv (fun s : ℝ => Real.exp (-a * s)) t = -a * Real.exp (-a * t) := by
  have hlin : HasDerivAt (fun s : ℝ => -a * s) (-a) t := by
    simpa using (hasDerivAt_id t).const_mul (-a)
  have hexp := (Real.hasDerivAt_exp (-a * t)).comp t hlin
  have hderiv := hexp.deriv
  change deriv (fun s : ℝ => Real.exp (-a * s)) t = _ at hderiv
  simpa [mul_comm] using hderiv

private theorem exponential_affine_second_deriv (a t : ℝ) :
    deriv (deriv (fun s : ℝ => Real.exp (-a * s))) t =
      a ^ 2 * Real.exp (-a * t) := by
  rw [show deriv (fun s : ℝ => Real.exp (-a * s)) =
      fun s : ℝ => -a * Real.exp (-a * s) by
    funext s
    exact exponential_affine_deriv a s]
  rw [deriv_const_mul (-a) (by fun_prop)]
  rw [exponential_affine_deriv a t]
  ring

private theorem translated_normSq_radial_deriv {n : ℕ}
    (c y : EuclideanSpace ℂ (Fin n)) :
    fderiv ℝ (fun w : EuclideanSpace ℂ (Fin n) => ‖w - c‖ ^ 2) y (y - c) =
      2 * ‖y - c‖ ^ 2 := by
  let : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin n)) :=
    InnerProductSpace.rclikeToReal ℂ (EuclideanSpace ℂ (Fin n))
  let ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) := fun w => w - c
  let q : EuclideanSpace ℂ (Fin n) → ℝ := fun w => ‖w‖ ^ 2
  have hψ : DifferentiableAt ℝ ψ y := differentiableAt_id.sub_const c
  have hqC : ContDiffAt ℝ 2 q (ψ y) := by
    dsimp [q]
    exact contDiffAt_id.norm_sq ℝ
  have hq : DifferentiableAt ℝ q (ψ y) := hqC.differentiableAt (by norm_num)
  have hcomp := fderiv_comp (f := ψ) (g := q) (x := y) hq hψ
  rw [show (fun w : EuclideanSpace ℂ (Fin n) => ‖w - c‖ ^ 2) = q ∘ ψ by rfl, hcomp]
  rw [fderiv_sub_const, fderiv_norm_sq, fderiv_fun_id]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  change (2 • innerSL ℝ (ψ y)) (y - c) = _
  rw [_root_.smul_apply, innerSL_apply_apply, real_inner_self_eq_norm_sq]
  ring

private theorem exponential_barrier_hessian {n : ℕ} (a : ℝ)
    (c y : EuclideanSpace ℂ (Fin n)) (R : ℝ) :
    complexHessian (fun w : EuclideanSpace ℂ (Fin n) =>
      Real.exp (-a * ‖w - c‖ ^ 2) - Real.exp (-a * R ^ 2)) y =
      (-a * Real.exp (-a * ‖y - c‖ ^ 2)) • (1 : Matrix (Fin n) (Fin n) ℂ) +
        (a ^ 2 * Real.exp (-a * ‖y - c‖ ^ 2)) •
          Matrix.vecMulVec (fun j => star (y j - c j)) (fun k => y k - c k) := by
  let h : ℝ → ℝ := fun t => Real.exp (-a * t)
  have hh : ContDiffAt ℝ 2 h (‖y - c‖ ^ 2) := by
    dsimp [h]
    fun_prop
  have hψ : ContDiffAt ℝ 2 (fun w : EuclideanSpace ℂ (Fin n) => w - c) y := by
    fun_prop
  have hq₀ : ContDiffAt ℝ 2 (fun w : EuclideanSpace ℂ (Fin n) => ‖w‖ ^ 2) (y - c) :=
    contDiffAt_id.norm_sq ℝ
  have hq : ContDiffAt ℝ 2 (fun w : EuclideanSpace ℂ (Fin n) => ‖w - c‖ ^ 2) y := by
    change ContDiffAt ℝ 2 ((fun w : EuclideanSpace ℂ (Fin n) => ‖w‖ ^ 2) ∘
      (fun w : EuclideanSpace ℂ (Fin n) => w - c)) y
    exact hq₀.comp y hψ
  have hbase : ContDiffAt ℝ 2 (fun w : EuclideanSpace ℂ (Fin n) =>
      Real.exp (-a * ‖w - c‖ ^ 2)) y :=
    (Real.contDiff_exp.contDiffAt.comp y (contDiffAt_const.mul hq))
  have hrad := translated_radial_composition_hessian c y h hh
  rw [exponential_affine_deriv a (‖y - c‖ ^ 2), exponential_affine_second_deriv a (‖y - c‖ ^ 2)] at hrad
  change (ddbar ((fun w : EuclideanSpace ℂ (Fin n) =>
      Real.exp (-a * ‖w - c‖ ^ 2)) -
      (fun _ : EuclideanSpace ℂ (Fin n) => Real.exp (-a * R ^ 2))) y).coeffMatrix = _
  rw [ddbar_sub hbase contDiffAt_const, ddbar_const]
  simp only [sub_zero]
  change complexHessian (h ∘ (fun w : EuclideanSpace ℂ (Fin n) => ‖w - c‖ ^ 2)) y = _
  simpa [h, Function.comp_def] using hrad

/-- A bounded uniformly Hermitian elliptic principal part admits the standard exponential
strict barrier on the outer half of any positive-radius ball. No coefficient derivatives occur. -/
theorem exists_complexEllipticOp_exponential_barrier {n : ℕ}
    (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    {c : EuclideanSpace ℂ (Fin n)} {R : ℝ} (hR : 0 < R)
    {lam K : ℝ≥0} (hlam : 0 < lam)
    (hEll : IsUniformlyEllipticOn A lam (Metric.ball c R))
    (hbound : ∀ y ∈ Metric.ball c R, ∀ j k, ‖A y j k‖ ≤ (K : ℝ)) :
    ∃ a : ℝ, 0 < a ∧
      let v : EuclideanSpace ℂ (Fin n) → ℝ :=
        fun y => Real.exp (-a * ‖y - c‖ ^ 2) - Real.exp (-a * R ^ 2)
      ContDiff ℝ 2 v ∧
      (∀ y ∈ Metric.sphere c R, v y = 0) ∧
      (∀ y ∈ Metric.ball c R \ Metric.closedBall c (R / 2),
        0 < complexEllipticOp A v y) ∧
      ∀ y ∈ Metric.sphere c R, fderiv ℝ v y (y - c) < 0 := by
  obtain ⟨a, ha, hscale⟩ := exponential_barrier_parameter hR hlam
  refine ⟨a, ha, ?_⟩
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hnorm : ContDiff ℝ 2
        (fun y : EuclideanSpace ℂ (Fin n) => ‖y‖ ^ 2) := contDiff_id.norm_sq ℝ
    have hshift : ContDiff ℝ 2
        (fun y : EuclideanSpace ℂ (Fin n) => ‖y - c‖ ^ 2) := by
      have htrans : ContDiff ℝ 2
          (fun y : EuclideanSpace ℂ (Fin n) => y - c) := by fun_prop
      change ContDiff ℝ 2 ((fun y : EuclideanSpace ℂ (Fin n) => ‖y‖ ^ 2) ∘
        (fun y : EuclideanSpace ℂ (Fin n) => y - c))
      exact hnorm.comp htrans
    exact (Real.contDiff_exp.comp (contDiff_const.mul hshift)).sub contDiff_const
  · intro y hy
    exact exponential_radial_profile_zero_on_sphere a R c y hy
  · intro y hy
    rcases hy with ⟨hyBall, hyOuter⟩
    have hnormLower : R / 2 < ‖y - c‖ := by
      have hnot : ¬ dist y c ≤ R / 2 := by
        simpa [Metric.mem_closedBall] using hyOuter
      simpa [dist_eq_norm] using lt_of_not_ge hnot
    have hr2 : (R / 2) ^ 2 < ‖y - c‖ ^ 2 :=
      (sq_lt_sq₀ (by positivity) (by positivity)).2 hnormLower
    have hscaled : a * (lam : ℝ) * (R / 2) ^ 2 <
        a * (lam : ℝ) * ‖y - c‖ ^ 2 :=
      mul_lt_mul_of_pos_left hr2 (mul_pos ha (by exact_mod_cast hlam))
    have hcoeff : (n : ℝ) * (K : ℝ) < a * (lam : ℝ) * ‖y - c‖ ^ 2 :=
      hscale.trans hscaled
    have hlower := radial_outer_re_lower A hEll hyBall
    have hupper := radial_trace_re_upper A hEll hbound hyBall
    have hformula : complexEllipticOp A
        (fun w : EuclideanSpace ℂ (Fin n) =>
          Real.exp (-a * ‖w - c‖ ^ 2) - Real.exp (-a * R ^ 2)) y =
        Real.exp (-a * ‖y - c‖ ^ 2) *
          (a ^ 2 * RCLike.re ((A y * Matrix.vecMulVec
            (fun j => star (y j - c j)) (fun k => y k - c k)).trace) -
           a * RCLike.re (Matrix.trace (A y))) := by
      change RCLike.re ((A y * complexHessian (fun w : EuclideanSpace ℂ (Fin n) =>
        Real.exp (-a * ‖w - c‖ ^ 2) - Real.exp (-a * R ^ 2)) y).trace) = _
      rw [exponential_barrier_hessian]
      simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
        Matrix.mul_one]
      simp [Complex.mul_re, -Complex.ofReal_exp, Complex.ofReal_re, Complex.ofReal_im,
        add_mul, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc]
      rw [← Complex.ofReal_pow a 2]
      simp only [Complex.ofReal_re, Complex.ofReal_im]
      ring_nf
    rw [hformula]
    apply mul_pos (Real.exp_pos _) ?_
    have h1 : a ^ 2 * ((lam : ℝ) * ‖y - c‖ ^ 2) ≤
        a ^ 2 * RCLike.re ((A y * Matrix.vecMulVec
          (fun j => star (y j - c j)) (fun k => y k - c k)).trace) :=
      mul_le_mul_of_nonneg_left hlower (sq_nonneg a)
    have h2 : a * RCLike.re (Matrix.trace (A y)) ≤ a * ((n : ℝ) * (K : ℝ)) :=
      mul_le_mul_of_nonneg_left hupper (le_of_lt ha)
    nlinarith
  · intro y hy
    let q : EuclideanSpace ℂ (Fin n) → ℝ := fun w => ‖w - c‖ ^ 2
    let h : ℝ → ℝ := fun t => Real.exp (-a * t)
    have hqC : ContDiffAt ℝ 2 q y := by
      dsimp [q]
      exact (contDiffAt_id.norm_sq ℝ).comp y (by fun_prop)
    have hqD : DifferentiableAt ℝ q y := hqC.differentiableAt (by norm_num)
    have hhD : DifferentiableAt ℝ h (q y) := by
      dsimp [h]
      fun_prop
    have hcomp := fderiv_comp (f := q) (g := h) (x := y) hhD hqD
    have hnorm : ‖y - c‖ = R := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hy
    have hscalar : deriv h (q y) = -a * Real.exp (-a * q y) := by
      dsimp [h]
      exact exponential_affine_deriv a (q y)
    rw [show (fun w : EuclideanSpace ℂ (Fin n) =>
        Real.exp (-a * ‖w - c‖ ^ 2) - Real.exp (-a * R ^ 2)) =
          (h ∘ q) - (fun _ : EuclideanSpace ℂ (Fin n) => Real.exp (-a * R ^ 2)) by
      funext w
      rfl]
    rw [fderiv_sub (hhD.comp y hqD) (differentiableAt_const _)]
    rw [hcomp]
    simp only [sub_apply, ContinuousLinearMap.comp_apply,
      fderiv_const_apply, zero_apply]
    rw [fderiv_eq_deriv_mul, hscalar, translated_normSq_radial_deriv]
    rw [show q y = ‖y - c‖ ^ 2 by rfl, hnorm]
    have hfirst : -a * Real.exp (-a * R ^ 2) < 0 :=
      mul_neg_of_neg_of_pos (neg_neg_of_pos ha) (Real.exp_pos _)
    have hsecond : 0 < 2 * R ^ 2 := by positivity
    have hprod : (-a * Real.exp (-a * R ^ 2)) * (2 * R ^ 2) < 0 :=
      mul_neg_of_neg_of_pos hfirst hsecond
    nlinarith
