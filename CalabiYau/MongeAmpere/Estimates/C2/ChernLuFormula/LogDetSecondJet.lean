module

public import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.NormalFrameJets
import CalabiYau.MongeAmpere.Estimates.C2.LogDetHessianJet
import CalabiYau.MongeAmpere.Estimates.C2.ReferenceCurvatureTransport.HolomorphicJacobianJet

/-!
# Second jet of the varying metric's logarithmic determinant

This is the finite-dimensional matrix differentiation cluster in the Ricci/log-volume expansion.
For a positive Hermitian matrix `G`, the first derivative of `log det G` is
`tr(G⁻¹ ∂G)`.  Differentiating again in the conjugate direction gives the trace of the mixed second
jet minus the quadratic contraction of the two first jets.  At the simultaneous normal-frame
center, `G` is diagonal with entries `λⱼ`, so these contractions become the eigenvalue-weighted sums
in the statement.

The second-jet contribution uses `normalFrameSecondReal ω₀ ω₁ x F p j / λⱼ`.  The matrix inverse
contributes `‖Tₚⱼₖ‖²/(λⱼλₖ)` with the full coefficient-index contraction.  No curvature or
Monge–Ampère equation is involved in this local determinant calculation; curvature enters through
the separate geometric bridge from the intrinsic Ricci expression to this coordinate Hessian.

The coefficient matrix uses holomorphic row indices and antiholomorphic column indices.  The
pullback is `J.transpose * G * J.map star`; in dimension one `J=i` leaves the metric coefficient
unchanged.  For `n=0` the determinant is the determinant of the empty identity matrix, its logarithm
is constant, and all indexed sums are empty.  For `n=1` the formula reduces to the usual second
logarithmic derivative `H/λ-|T|²/λ²`.  Constant metrics on a flat torus give zero on both sides.
-/

@[expose] public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

private theorem diagonal_trace_identity {n : ℕ}
    (lam : Fin n → ℂ) (H : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (Matrix.diagonal lam * H) = ∑ j, lam j * H j j := by
  classical
  simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply]

private theorem diagonal_quadratic_trace_identity {n : ℕ}
    (a b : Fin n → ℂ) (H K : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (Matrix.diagonal a * H * Matrix.diagonal b * K) =
      ∑ j, ∑ k, a j * H j k * b k * K k j := by
  classical
  simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply,
    Finset.mul_sum, mul_assoc]

private theorem diagonal_complex_quadratic_trace {n : ℕ}
    (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℂ) :
    RCLike.re (((Matrix.diagonal (fun i ↦ ((a i)⁻¹ : ℂ)) * H.conjTranspose) *
      Matrix.diagonal (fun i ↦ ((a i)⁻¹ : ℂ)) * H).trace) =
      ∑ i, ∑ j, ‖H j i‖ ^ 2 * (a i)⁻¹ * (a j)⁻¹ := by
  classical
  rw [diagonal_quadratic_trace_identity]
  simp only [Matrix.conjTranspose_apply]
  change Complex.re (∑ i, ∑ j,
    ((a i)⁻¹ : ℂ) * star (H j i) * ((a j)⁻¹ : ℂ) * H j i) = _
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hnorm : ‖H j i‖ ^ 2 = (H j i).re ^ 2 + (H j i).im ^ 2 := by
    rw [← RCLike.normSq_eq_def']
    change Complex.normSq (H j i) = _
    rw [Complex.normSq_apply]
    ring
  simp [Complex.mul_re, Complex.mul_im, hnorm]
  ring

private theorem logDet_chartInv_fderiv_formula {n : ℕ}
    {G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    {z : EuclideanSpace ℂ (Fin n)}
    (hG : ∀ a b, ContDiffAt ℝ 1 (fun w ↦ G w a b) z)
    (hunit : IsUnit (G z)) (i j : Fin n) (v : EuclideanSpace ℂ (Fin n)) :
    fderiv ℝ (fun w ↦ (G w)⁻¹ i j) z v =
      -(((G z)⁻¹ * (Matrix.of (fun a b : Fin n ↦
        fderiv ℝ (fun w ↦ G w a b) z v)) * (G z)⁻¹) i j) := by
  classical
  have hentry (a b : Fin n) : DifferentiableAt ℝ (fun w ↦ G w a b) z :=
    (hG a b).differentiableAt (by norm_num)
  have hinvEntry (a b : Fin n) :
      DifferentiableAt ℝ (fun w ↦ (G w)⁻¹ a b) z :=
    chartInv_differentiableAt hG hunit a b
  have hdet : DifferentiableAt ℝ (fun w ↦ (G w).det) z := by
    simp_rw [Matrix.det_apply]
    fun_prop
  have hdetUnit : IsUnit ((G z).det) :=
    (Matrix.isUnit_iff_isUnit_det (A := G z)).mp hunit
  have hdetEvent : ∀ᶠ w in nhds z, (G w).det ≠ 0 :=
    hdet.continuousAt.eventually_ne hdetUnit.ne_zero
  have hunitEvent : ∀ᶠ w in nhds z, IsUnit (G w) := by
    filter_upwards [hdetEvent] with w hw
    exact (Matrix.isUnit_iff_isUnit_det (A := G w)).mpr (isUnit_iff_ne_zero.mpr hw)
  have hprodEvent (a b : Fin n) :
      (fun w ↦ (G w * (G w)⁻¹) a b) =ᶠ[nhds z]
        fun _ ↦ (1 : Matrix (Fin n) (Fin n) ℂ) a b := by
    filter_upwards [hunitEvent] with w hw
    have hwdet : IsUnit ((G w).det) :=
      (Matrix.isUnit_iff_isUnit_det (A := G w)).mp hw
    rw [Matrix.mul_nonsing_inv (G w) hwdet]
  have hprodSum (a b : Fin n) :
      (fun w ↦ (G w * (G w)⁻¹) a b) =
        fun w ↦ ∑ l : Fin n, G w a l * (G w)⁻¹ l b := by
    funext w
    simp [Matrix.mul_apply]
  have htermDiff (a b l : Fin n) :
      DifferentiableAt ℝ (fun w ↦ G w a l * (G w)⁻¹ l b) z :=
    (hentry a l).mul (hinvEntry l b)
  have hderivSum (a b : Fin n) :
      fderiv ℝ (fun w ↦ ∑ l : Fin n, G w a l * (G w)⁻¹ l b) z v = 0 := by
    have hsumEvent :
        (fun w ↦ ∑ l : Fin n, G w a l * (G w)⁻¹ l b) =ᶠ[nhds z]
          fun _ ↦ (1 : Matrix (Fin n) (Fin n) ℂ) a b :=
      (Filter.EventuallyEq.of_eq (hprodSum a b).symm).trans (hprodEvent a b)
    have h := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L v)
      hsumEvent.fderiv_eq
    simpa using h
  have hentryEq (a b : Fin n) :
      ∑ l : Fin n,
        fderiv ℝ (fun w ↦ G w a l * (G w)⁻¹ l b) z v = 0 := by
    have h := hderivSum a b
    rw [fderiv_fun_sum (u := Finset.univ) (by intro l hl; exact htermDiff a b l)] at h
    simpa only [_root_.sum_apply] using h
  have hentryRel (a b : Fin n) :
      ∑ l : Fin n,
        (G z a l * fderiv ℝ (fun w ↦ (G w)⁻¹ l b) z v +
          fderiv ℝ (fun w ↦ G w a l) z v * (G z)⁻¹ l b) = 0 := by
    have h := hentryEq a b
    simp_rw [fderiv_fun_mul (hentry a _) (hinvEntry _ b)] at h
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul] at h
    simp_rw [mul_comm ((G z)⁻¹ _ _) (fderiv ℝ (fun w ↦ G w a _) z v)] at h
    linear_combination h
  let D : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.of (fun a b ↦ fderiv ℝ (fun w ↦ (G w)⁻¹ a b) z v)
  let H : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.of (fun a b ↦ fderiv ℝ (fun w ↦ G w a b) z v)
  have hmul : G z * D = -(H * (G z)⁻¹) := by
    ext a b
    simp only [D, H, Matrix.mul_apply, Matrix.of_apply]
    have hsum :
        (∑ l : Fin n, G z a l * fderiv ℝ (fun w ↦ (G w)⁻¹ l b) z v) +
          (∑ l : Fin n, fderiv ℝ (fun w ↦ G w a l) z v * (G z)⁻¹ l b) = 0 := by
      calc
        _ = ∑ l : Fin n,
            (G z a l * fderiv ℝ (fun w ↦ (G w)⁻¹ l b) z v +
              fderiv ℝ (fun w ↦ G w a l) z v * (G z)⁻¹ l b) := by
                rw [← Finset.sum_add_distrib]
        _ = 0 := hentryRel a b
    exact (eq_neg_iff_add_eq_zero).2 hsum
  have hleft : (G z)⁻¹ * G z = 1 :=
    Matrix.nonsing_inv_mul (A := G z) ((Matrix.isUnit_iff_isUnit_det (A := G z)).mp hunit)
  have hD : D = -((G z)⁻¹ * H * (G z)⁻¹) := by
    calc
      D = 1 * D := by simp
      _ = ((G z)⁻¹ * G z) * D := by rw [hleft]
      _ = (G z)⁻¹ * (G z * D) := by rw [Matrix.mul_assoc]
      _ = (G z)⁻¹ * (-(H * (G z)⁻¹)) := by rw [hmul]
      _ = -((G z)⁻¹ * H * (G z)⁻¹) := by simp [Matrix.mul_assoc]
  simpa [D, H] using congrArg (fun A : Matrix (Fin n) (Fin n) ℂ ↦ A i j) hD

private theorem logDet_chartInv_partial_formula {n : ℕ}
    {G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    {z : EuclideanSpace ℂ (Fin n)}
    (hG : ∀ a b, ContDiffAt ℝ 1 (fun w ↦ G w a b) z)
    (hunit : IsUnit (G z)) (k j p : Fin n) :
    chartPartialZComplex (fun w ↦ (G w)⁻¹ k j) z p =
      -(((G z)⁻¹ * Matrix.of (fun a b : Fin n ↦
        chartPartialZComplex (fun w ↦ G w a b) z p) * (G z)⁻¹) k j) := by
  let e : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single p 1
  let D₁ : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.of (fun a b ↦ fderiv ℝ (fun w ↦ G w a b) z e)
  let D₂ : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.of (fun a b ↦ fderiv ℝ (fun w ↦ G w a b) z (Complex.I • e))
  let H : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.of (fun a b ↦ chartPartialZComplex (fun w ↦ G w a b) z p)
  have hH : H = (2 : ℂ)⁻¹ • (D₁ - Complex.I • D₂) := by
    ext a b
    change ((fderiv ℝ (fun w ↦ G w a b) z e -
      Complex.I * fderiv ℝ (fun w ↦ G w a b) z (Complex.I • e)) / 2) =
        (2 : ℂ)⁻¹ * (fderiv ℝ (fun w ↦ G w a b) z e -
          Complex.I * fderiv ℝ (fun w ↦ G w a b) z (Complex.I • e))
    ring
  have h₁ := logDet_chartInv_fderiv_formula hG hunit k j e
  have h₂ := logDet_chartInv_fderiv_formula hG hunit k j (Complex.I • e)
  have hD₁ : Matrix.of (fun a b : Fin n ↦ fderiv ℝ (fun w ↦ G w a b) z e) = D₁ := rfl
  have hD₂ : Matrix.of (fun a b : Fin n ↦
      fderiv ℝ (fun w ↦ G w a b) z (Complex.I • e)) = D₂ := rfl
  rw [hD₁] at h₁
  rw [hD₂] at h₂
  change ((fderiv ℝ (fun w ↦ (G w)⁻¹ k j) z e -
    Complex.I * fderiv ℝ (fun w ↦ (G w)⁻¹ k j) z (Complex.I • e)) / 2) =
      -(((G z)⁻¹ * Matrix.of (fun a b : Fin n ↦
        chartPartialZComplex (fun w ↦ G w a b) z p) * (G z)⁻¹) k j)
  rw [Matrix.mul_assoc]
  change ((fderiv ℝ (fun w ↦ (G w)⁻¹ k j) z e -
    Complex.I * fderiv ℝ (fun w ↦ (G w)⁻¹ k j) z (Complex.I • e)) / 2) =
      -((G z)⁻¹ * (H * (G z)⁻¹)) k j
  rw [h₁, h₂, hH]
  have hmatrix : (G z)⁻¹ * ((2 : ℂ)⁻¹ • (D₁ - Complex.I • D₂) * (G z)⁻¹) =
      (2 : ℂ)⁻¹ • ((G z)⁻¹ * D₁ * (G z)⁻¹ -
        Complex.I • ((G z)⁻¹ * D₂ * (G z)⁻¹)) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.smul_mul, Matrix.mul_smul]
    simp [Matrix.mul_assoc]
  rw [hmatrix]
  have hcomp :
      ((G z)⁻¹ * D₁ * (G z)⁻¹ - Complex.I • ((G z)⁻¹ * D₂ * (G z)⁻¹)) k j =
        ((G z)⁻¹ * D₁ * (G z)⁻¹) k j -
          Complex.I * ((G z)⁻¹ * D₂ * (G z)⁻¹) k j := by
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Matrix.smul_apply, smul_eq_mul, hcomp]
  simp only [Matrix.mul_assoc]
  ring_nf

private theorem chartPartialZComplex_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (F : ι → EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (p : Fin n)
    (hF : ∀ i, DifferentiableAt ℝ (F i) z) :
    chartPartialZComplex (fun w ↦ ∑ i, F i w) z p =
      ∑ i, chartPartialZComplex (F i) z p := by
  classical
  let e : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single p 1
  have hsum (v : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ ∑ i, F i w) z v =
        ∑ i, fderiv ℝ (F i) z v := by
    rw [fderiv_fun_sum (u := Finset.univ) (by intro i hi; exact hF i)]
    simp only [sum_apply]
  unfold chartPartialZComplex
  rw [hsum e, hsum (Complex.I • e)]
  calc
    _ = ((∑ i, (fderiv ℝ (F i) z) e) -
        Complex.I * (∑ i, (fderiv ℝ (F i) z) (Complex.I • e))) / 2 := rfl
    _ = (∑ i, ((fderiv ℝ (F i) z) e -
        Complex.I * (fderiv ℝ (F i) z) (Complex.I • e))) / 2 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    _ = ∑ i, ((fderiv ℝ (F i) z) e -
        Complex.I * (fderiv ℝ (F i) z) (Complex.I • e)) / 2 := by rw [Finset.sum_div]

private theorem logDet_mixed_trace_derivative {n : ℕ}
    {G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    {f : EuclideanSpace ℂ (Fin n) → ℂ}
    {z : EuclideanSpace ℂ (Fin n)} (p : Fin n)
    (hG : ∀ a b, ContDiffAt ℝ 1 (fun w ↦ G w a b) z)
    (hunit : IsUnit (G z))
    (hB : ∀ a b, DifferentiableAt ℝ
      (fun w ↦ chartPartialBarComplex (fun v ↦ G v a b) w p) z)
    (hfirst : ∀ᶠ w in nhds z,
      chartPartialBarComplex f w p = Matrix.trace ((G w)⁻¹ *
        Matrix.of (fun a b ↦ chartPartialBarComplex (fun v ↦ G v a b) w p))) :
    chartPartialZComplex (fun w ↦ chartPartialBarComplex f w p) z p =
      (∑ i, ∑ j, (G z)⁻¹ i j *
        chartPartialZComplex
          (fun w ↦ chartPartialBarComplex (fun v ↦ G v j i) w p) z p) -
      ∑ i, ∑ j,
        ((G z)⁻¹ * Matrix.of (fun a b ↦
          chartPartialZComplex (fun w ↦ G w a b) z p) * (G z)⁻¹) i j *
          chartPartialBarComplex (fun v ↦ G v j i) z p := by
  classical
  let B (w : EuclideanSpace ℂ (Fin n)) (a b : Fin n) :=
    chartPartialBarComplex (fun v ↦ G v a b) w p
  have hentry (a b : Fin n) : DifferentiableAt ℝ (fun w ↦ G w a b) z :=
    (hG a b).differentiableAt (by norm_num)
  have hinv (a b : Fin n) : DifferentiableAt ℝ (fun w ↦ (G w)⁻¹ a b) z :=
    chartInv_differentiableAt hG hunit a b
  have hterm (a b : Fin n) : DifferentiableAt ℝ
      (fun w ↦ (G w)⁻¹ a b * B w b a) z := (hinv a b).mul (hB b a)
  have hinner (a : Fin n) : DifferentiableAt ℝ
      (fun w ↦ ∑ b, (G w)⁻¹ a b * B w b a) z := by
    apply DifferentiableAt.fun_sum (u := Finset.univ)
    intro b hb
    exact hterm a b
  have htraceExpansion : (fun w ↦ Matrix.trace ((G w)⁻¹ *
      Matrix.of (fun a b ↦ B w a b))) =
      fun w ↦ ∑ a, ∑ b, (G w)⁻¹ a b * B w b a := by
    funext w
    simp [Matrix.trace, Matrix.mul_apply]
  have hfirstTraceFun :
      (fun w ↦ chartPartialBarComplex f w p) =ᶠ[nhds z]
        fun w ↦ Matrix.trace ((G w)⁻¹ * Matrix.of (fun a b ↦ B w a b)) := by
    filter_upwards [hfirst] with w hw
    exact hw
  have hfirstSumFun :
      (fun w ↦ chartPartialBarComplex f w p) =ᶠ[nhds z]
        fun w ↦ ∑ a, ∑ b, (G w)⁻¹ a b * B w b a :=
    hfirstTraceFun.trans (Filter.EventuallyEq.of_eq htraceExpansion)
  have htraceEq : fderiv ℝ (fun w ↦ chartPartialBarComplex f w p) z =
      fderiv ℝ (fun w ↦ ∑ a, ∑ b, (G w)⁻¹ a b * B w b a) z :=
    hfirstSumFun.fderiv_eq
  have htraceDeriv := congrArg
    (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦
      (L (EuclideanSpace.single p 1) - Complex.I *
        L (Complex.I • EuclideanSpace.single p 1)) / 2) htraceEq
  have hderivTrace :
      chartPartialZComplex (fun w ↦ chartPartialBarComplex f w p) z p =
        chartPartialZComplex (fun w ↦ ∑ a, ∑ b, (G w)⁻¹ a b * B w b a) z p := by
    simpa [chartPartialZComplex] using htraceDeriv
  have hprodPart (a b : Fin n) :
      chartPartialZComplex (fun w ↦ (G w)⁻¹ a b * B w b a) z p =
        chartPartialZComplex (fun w ↦ (G w)⁻¹ a b) z p * B z b a +
          (G z)⁻¹ a b * chartPartialZComplex (fun w ↦ B w b a) z p :=
    chartPartialZComplex_mul (hinv a b) (hB b a) p
  rw [hderivTrace]
  calc
    _ = ∑ a, ∑ b,
        chartPartialZComplex (fun w ↦ (G w)⁻¹ a b * B w b a) z p := by
      rw [chartPartialZComplex_sum _ z p hinner]
      apply Finset.sum_congr rfl
      intro a ha
      rw [chartPartialZComplex_sum _ z p (fun b ↦ hterm a b)]
    _ = ∑ a, ∑ b,
        (chartPartialZComplex (fun w ↦ (G w)⁻¹ a b) z p * B z b a +
          (G z)⁻¹ a b * chartPartialZComplex (fun w ↦ B w b a) z p) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact hprodPart a b
    _ = _ := by
      rw [← Finset.sum_sub_distrib]
      simp_rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [logDet_chartInv_partial_formula hG hunit a b p]
      simp [B, sub_eq_add_neg]
      ring

private theorem normalFrame_logdet_second_jet_at_index
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x)
    (p : Fin n) :
    normalFrameLogDetSecondReal ω₀ ω₁ x F p =
      (∑ j, normalFrameSecondReal ω₀ ω₁ x F p j / F.eigenvalue j) -
        ∑ j, ∑ k,
          ‖normalFrameFirstDerivative F p j k‖ ^ 2 /
            (F.eigenvalue j * F.eigenvalue k) := by
  have hF3 : ContDiffOn ℝ 3 F.map F.domain :=
    F.smooth_map.of_le (WithTop.coe_le_coe.mpr
      (show (3 : ℕ∞) ≤ ⊤ from le_top))
  have hJ := holomorphicJacobianJetAt_of_contDiffOn F.domain F.isOpen_domain F.map
    hF3 F.holomorphic_map F.center F.center_mem F.jacobian_det_ne_zero.isUnit
  have hmap3 : ContDiffAt ℝ 3 F.map F.center := by
    exact (F.smooth_map.contDiffAt
      (F.isOpen_domain.mem_nhds F.center_mem)).of_le
      (WithTop.coe_le_coe.mpr (show (3 : ℕ∞) ≤ ⊤ from le_top))
  have hmap2 : ContDiffAt ℝ 2 F.map F.center := hmap3.of_le (by norm_num)
  have hMetric (a b : Fin n) : ContDiffAt ℝ 2
      (fun w ↦ ω₁.metricInChart x (F.map w) a b) F.center := by
    have hbase := (ω₁.contDiffOn_metricInChart x a b).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds
        (F.maps_into_chart F.center F.center_mem))
    exact hbase.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)) |>.comp
      F.center hmap2
  have hJentry (a j : Fin n) : ContDiffAt ℝ 2
      (fun w ↦ holomorphicJacobianMatrix F.map w a j) F.center :=
    hJ.jacobian_contDiff a j
  have hJstar (a j : Fin n) : ContDiffAt ℝ 2
      (fun w ↦ star (holomorphicJacobianMatrix F.map w a j)) F.center := by
    have h : ContDiffAt ℝ 2
        (fun w ↦ Complex.conjCAE (holomorphicJacobianMatrix F.map w a j)) F.center := by
      exact (Complex.conjCLE.contDiff.contDiffAt).comp F.center (hJentry a j)
    convert h using 1
    ext w
    simp [Complex.conjCAE_apply]
  have hG : ∀ j k, ContDiffAt ℝ 2
      (fun w ↦ pulledBackMetricInChart ω₁ x F.map w j k) F.center := by
    intro j k
    change ContDiffAt ℝ 2 (fun w ↦
      (Matrix.transpose (holomorphicJacobianMatrix F.map w) *
        ω₁.metricInChart x (F.map w) *
          (holomorphicJacobianMatrix F.map w).map star) j k) F.center
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    fun_prop (disch := assumption)
  have hHerm : ∀ᶠ w in nhds F.center,
      (pulledBackMetricInChart ω₁ x F.map w).IsHermitian := by
    filter_upwards [F.isOpen_domain.mem_nhds F.center_mem] with w hw
    have hmetric := (ω₁.posDef_metricInChart x (F.maps_into_chart w hw)).isHermitian
    let J := holomorphicJacobianMatrix F.map w
    let H := ω₁.metricInChart x (F.map w)
    have hJ1 : (J.map star).conjTranspose = J.transpose := by
      ext i j
      simp [J, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.transpose_apply]
    have hJ2 : J.transpose.conjTranspose = J.map star := by
      ext i j
      simp [J, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.transpose_apply]
    change (J.transpose * H * J.map star).conjTranspose = _
    calc
      (J.transpose * H * J.map star).conjTranspose =
          (J.map star).conjTranspose * H.conjTranspose * J.transpose.conjTranspose := by
        simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = J.transpose * H * J.map star := by rw [hJ1, hmetric.eq, hJ2]
      _ = ω₁.pulledBackMetricInChart x F.map w := rfl
  have h := log_det_mixed_second_real_of_diagonal
    (fun w ↦ pulledBackMetricInChart ω₁ x F.map w) F.center F.eigenvalue hG hHerm
    F.varying_diagonal F.eigenvalue_pos p
  simpa [normalFrameLogDetSecondReal, normalFrameSecondReal,
    normalFrameMixedSecondDerivative, normalFrameFirstDerivative] using h

/-- Sum of the diagonal mixed Hessians of `log det` of the pulled-back varying metric, expanded in
the simultaneous normal frame. -/
theorem normalFrame_logdet_second_jet_expansion
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x) :
    (∑ p, normalFrameLogDetSecondReal ω₀ ω₁ x F p) =
      (∑ p, ∑ j, normalFrameSecondReal ω₀ ω₁ x F p j / F.eigenvalue j) -
        ∑ p, ∑ j, ∑ k,
          ‖normalFrameFirstDerivative F p j k‖ ^ 2 /
            (F.eigenvalue j * F.eigenvalue k) := by
  classical
  calc
    _ = ∑ p, ((∑ j, normalFrameSecondReal ω₀ ω₁ x F p j / F.eigenvalue j) -
        ∑ j, ∑ k, ‖normalFrameFirstDerivative F p j k‖ ^ 2 /
          (F.eigenvalue j * F.eigenvalue k)) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact normalFrame_logdet_second_jet_at_index ω₀ ω₁ x F p
    _ = _ := by rw [Finset.sum_sub_distrib]

end KahlerForm
