module

public import CalabiYau.Geometry.Kahler.Curvature.Chart.Basic

/-!
# Mixed coordinate derivatives of a smooth germ

Both coordinate derivatives use the factor `1/2`; commutation follows from
symmetry of the second real Fréchet derivative. Pointwise hypotheses do not
require a globally smooth extension. Székelyhidi, §3.3, proof of Lemma 3.9,
PDF p.48 (book p.45), coordinate Chern-curvature calculation.
-/

public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder

namespace KahlerForm

variable {n : ℕ}

/-- A common real directional-derivative model for `∂` and `∂̄`. -/
private noncomputable def chartWirtinger
    (s : ℂ) (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (w : EuclideanSpace ℂ (Fin n)) (j : Fin n) : ℂ :=
  (fderiv ℝ F w (EuclideanSpace.single j 1) +
    s * fderiv ℝ F w (Complex.I • EuclideanSpace.single j 1)) / 2

private theorem chartWirtinger_fderiv (s : ℂ)
    (F : EuclideanSpace ℂ (Fin n) → ℂ) (hF : ContDiff ℝ ∞ F)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n)
    (v : EuclideanSpace ℂ (Fin n)) :
    fderiv ℝ (fun w => chartWirtinger s F w j) z v =
      (fderiv ℝ (fderiv ℝ F) z v (EuclideanSpace.single j 1) +
        s * fderiv ℝ (fderiv ℝ F) z v
          (Complex.I • EuclideanSpace.single j 1)) / 2 := by
  let e : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j 1
  have hfd : DifferentiableAt ℝ (fderiv ℝ F) z :=
    (hF.contDiffAt.fderiv_right (m := ∞)
      (le_of_eq (show (∞ : ℕ∞ω) = ∞ + 1 from rfl).symm)).differentiableAt (by norm_num)
  have he : DifferentiableAt ℝ (fun w => fderiv ℝ F w e) z :=
    hfd.clm_apply (differentiableAt_const _)
  have hie : DifferentiableAt ℝ (fun w => fderiv ℝ F w (Complex.I • e)) z :=
    hfd.clm_apply (differentiableAt_const _)
  have h_e (u : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w => fderiv ℝ F w e) z u = fderiv ℝ (fderiv ℝ F) z u e := by
    rw [fderiv_clm_apply hfd (differentiableAt_const _)]
    simp
  have h_ie (u : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w => fderiv ℝ F w (Complex.I • e)) z u =
        fderiv ℝ (fderiv ℝ F) z u (Complex.I • e) := by
    rw [fderiv_clm_apply hfd (differentiableAt_const _)]
    simp
  have hsum : DifferentiableAt ℝ
      (fun w => fderiv ℝ F w e + s * fderiv ℝ F w (Complex.I • e)) z :=
    he.add (hie.const_mul s)
  have hfun : (fun w => chartWirtinger s F w j) =
      fun w => (2 : ℂ)⁻¹ * (fderiv ℝ F w e + s * fderiv ℝ F w (Complex.I • e)) := by
    funext w
    simp only [chartWirtinger, e, div_eq_mul_inv]
    ring
  rw [hfun, fderiv_const_mul hsum, fderiv_fun_add he (hie.const_mul s),
    fderiv_const_mul hie]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [h_e v, h_ie v]
  simp only [div_eq_mul_inv]
  ring

private theorem chartWirtinger_comm (s t : ℂ)
    (F : EuclideanSpace ℂ (Fin n) → ℂ) (hF : ContDiff ℝ ∞ F)
    (z : EuclideanSpace ℂ (Fin n)) (p q : Fin n) :
    chartWirtinger s (fun w => chartWirtinger t F w q) z p =
      chartWirtinger t (fun w => chartWirtinger s F w p) z q := by
  let ep : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single p 1
  let eq : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single q 1
  have hs : IsSymmSndFDerivAt ℝ F z :=
    hF.contDiffAt.isSymmSndFDerivAt
      (by simpa [minSmoothness_of_isRCLikeNormedField] using
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  change (fderiv ℝ (fun w => chartWirtinger t F w q) z ep +
    s * fderiv ℝ (fun w => chartWirtinger t F w q) z (Complex.I • ep)) / 2 =
    (fderiv ℝ (fun w => chartWirtinger s F w p) z eq +
    t * fderiv ℝ (fun w => chartWirtinger s F w p) z (Complex.I • eq)) / 2
  rw [chartWirtinger_fderiv t F hF z q ep,
    chartWirtinger_fderiv t F hF z q (Complex.I • ep),
    chartWirtinger_fderiv s F hF z p eq,
    chartWirtinger_fderiv s F hF z p (Complex.I • eq)]
  dsimp only [ep, eq] at *
  rw [hs (EuclideanSpace.single p 1) (EuclideanSpace.single q 1),
    hs (EuclideanSpace.single p 1) (Complex.I • EuclideanSpace.single q 1),
    hs (Complex.I • EuclideanSpace.single p 1) (EuclideanSpace.single q 1),
    hs (Complex.I • EuclideanSpace.single p 1) (Complex.I • EuclideanSpace.single q 1)]
  ring

private theorem chartWirtinger_fderiv_at (s : ℂ)
    (F : EuclideanSpace ℂ (Fin n) → ℂ) (z : EuclideanSpace ℂ (Fin n))
    (hF : ContDiffAt ℝ ∞ F z) (j : Fin n)
    (v : EuclideanSpace ℂ (Fin n)) :
    fderiv ℝ (fun w => chartWirtinger s F w j) z v =
      (fderiv ℝ (fderiv ℝ F) z v (EuclideanSpace.single j 1) +
        s * fderiv ℝ (fderiv ℝ F) z v
          (Complex.I • EuclideanSpace.single j 1)) / 2 := by
  let e : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j 1
  have hfd : DifferentiableAt ℝ (fderiv ℝ F) z :=
    (hF.fderiv_right (m := ∞)
      (le_of_eq (show (∞ : ℕ∞ω) = ∞ + 1 from rfl).symm)).differentiableAt (by norm_num)
  have he : DifferentiableAt ℝ (fun w => fderiv ℝ F w e) z :=
    hfd.clm_apply (differentiableAt_const _)
  have hie : DifferentiableAt ℝ (fun w => fderiv ℝ F w (Complex.I • e)) z :=
    hfd.clm_apply (differentiableAt_const _)
  have h_e (u : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w => fderiv ℝ F w e) z u = fderiv ℝ (fderiv ℝ F) z u e := by
    rw [fderiv_clm_apply hfd (differentiableAt_const _)]
    simp
  have h_ie (u : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w => fderiv ℝ F w (Complex.I • e)) z u =
        fderiv ℝ (fderiv ℝ F) z u (Complex.I • e) := by
    rw [fderiv_clm_apply hfd (differentiableAt_const _)]
    simp
  have hsum : DifferentiableAt ℝ
      (fun w => fderiv ℝ F w e + s * fderiv ℝ F w (Complex.I • e)) z :=
    he.add (hie.const_mul s)
  have hfun : (fun w => chartWirtinger s F w j) =
      fun w => (2 : ℂ)⁻¹ * (fderiv ℝ F w e + s * fderiv ℝ F w (Complex.I • e)) := by
    funext w
    simp only [chartWirtinger, e, div_eq_mul_inv]
    ring
  rw [hfun, fderiv_const_mul hsum, fderiv_fun_add he (hie.const_mul s),
    fderiv_const_mul hie]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [h_e v, h_ie v]
  simp only [div_eq_mul_inv]
  ring

private theorem chartWirtinger_comm_at (s t : ℂ)
    (F : EuclideanSpace ℂ (Fin n) → ℂ) (z : EuclideanSpace ℂ (Fin n))
    (hF : ContDiffAt ℝ ∞ F z) (p q : Fin n) :
    chartWirtinger s (fun w => chartWirtinger t F w q) z p =
      chartWirtinger t (fun w => chartWirtinger s F w p) z q := by
  let ep : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single p 1
  let eq : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single q 1
  have hs : IsSymmSndFDerivAt ℝ F z :=
    hF.isSymmSndFDerivAt
      (by simpa [minSmoothness_of_isRCLikeNormedField] using
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  change (fderiv ℝ (fun w => chartWirtinger t F w q) z ep +
    s * fderiv ℝ (fun w => chartWirtinger t F w q) z (Complex.I • ep)) / 2 =
    (fderiv ℝ (fun w => chartWirtinger s F w p) z eq +
    t * fderiv ℝ (fun w => chartWirtinger s F w p) z (Complex.I • eq)) / 2
  rw [chartWirtinger_fderiv_at t F z hF q ep,
    chartWirtinger_fderiv_at t F z hF q (Complex.I • ep),
    chartWirtinger_fderiv_at s F z hF p eq,
    chartWirtinger_fderiv_at s F z hF p (Complex.I • eq)]
  dsimp only [ep, eq] at *
  rw [hs (EuclideanSpace.single p 1) (EuclideanSpace.single q 1),
    hs (EuclideanSpace.single p 1) (Complex.I • EuclideanSpace.single q 1),
    hs (Complex.I • EuclideanSpace.single p 1) (EuclideanSpace.single q 1),
    hs (Complex.I • EuclideanSpace.single p 1) (Complex.I • EuclideanSpace.single q 1)]
  ring

theorem chartPartialBarComplex_chartPartialZComplex_comm_at
    (F : EuclideanSpace ℂ (Fin n) → ℂ) (z : EuclideanSpace ℂ (Fin n))
    (hF : ContDiffAt ℝ ∞ F z) (p q : Fin n) :
    chartPartialBarComplex (fun w => chartPartialZComplex F w p) z q =
      chartPartialZComplex (fun w => chartPartialBarComplex F w q) z p := by
  have hz (A : EuclideanSpace ℂ (Fin n) → ℂ)
      (w : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
      chartWirtinger (-Complex.I) A w j = chartPartialZComplex A w j := by
    simp [chartWirtinger, chartPartialZComplex, div_eq_mul_inv]
    ring
  have hb (w : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
      chartWirtinger Complex.I F w j = chartPartialBarComplex F w j := rfl
  have hzf (j : Fin n) :
      (fun w => chartWirtinger (-Complex.I) F w j) =
        (fun w => chartPartialZComplex F w j) := funext (fun w => hz F w j)
  have hbf (j : Fin n) :
      (fun w => chartWirtinger Complex.I F w j) =
        (fun w => chartPartialBarComplex F w j) := funext (fun w => hb w j)
  calc
    chartPartialBarComplex (fun w => chartPartialZComplex F w p) z q =
        chartWirtinger Complex.I (fun w => chartWirtinger (-Complex.I) F w p) z q := by
      rw [hzf]
      rfl
    _ = chartWirtinger (-Complex.I) (fun w => chartWirtinger Complex.I F w q) z p :=
      (chartWirtinger_comm_at (-Complex.I) Complex.I F z hF p q).symm
    _ = chartPartialZComplex (fun w => chartPartialBarComplex F w q) z p := by
      rw [hbf]
      exact hz (fun w => chartPartialBarComplex F w q) z p

theorem chartPartialZComplex_differentiableAt_at
    (F : EuclideanSpace ℂ (Fin n) → ℂ) (z : EuclideanSpace ℂ (Fin n))
    (hF : ContDiffAt ℝ ∞ F z) (j : Fin n) :
    DifferentiableAt ℝ (fun w => chartPartialZComplex F w j) z := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ F) z :=
    (hF.fderiv_right (m := ∞)
      (le_of_eq (show (∞ : ℕ∞ω) = ∞ + 1 from rfl).symm)).differentiableAt (by norm_num)
  have he : DifferentiableAt ℝ
      (fun w => fderiv ℝ F w (EuclideanSpace.single j 1)) z :=
    hfd.clm_apply (differentiableAt_const _)
  have hie : DifferentiableAt ℝ
      (fun w => fderiv ℝ F w (Complex.I • EuclideanSpace.single j 1)) z :=
    hfd.clm_apply (differentiableAt_const _)
  unfold chartPartialZComplex
  fun_prop (disch := assumption)

theorem chartPartialZComplex_contDiffAt
    (F : EuclideanSpace ℂ (Fin n) → ℂ) (z : EuclideanSpace ℂ (Fin n))
    (hF : ContDiffAt ℝ ∞ F z) (p : Fin n) :
    ContDiffAt ℝ ∞ (fun w => chartPartialZComplex F w p) z := by
  have hfd : ContDiffAt ℝ ∞ (fderiv ℝ F) z := hF.fderiv_right (by simp)
  unfold chartPartialZComplex
  fun_prop (disch := assumption)

end KahlerForm
