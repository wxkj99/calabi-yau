module

public import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.NormalCoordinates.HolomorphicPatch
public import CalabiYau.Geometry.Kahler.Curvature.Chart.Basic

/-!
# Finite jets of a holomorphic coordinate germ

Székelyhidi §1.4, pp.11–12 (PDF 29–30), connection and normal-coordinate calculation.
The germ, not complex differentiability at one point, controls the total complex `fderiv`.
Real C3 regularity suffices: the Jacobian and its inverse transpose have real C2 jets.
-/

public section

open scoped ContDiff ComplexOrder MatrixOrder
open Filter Topology

namespace KahlerForm

variable {n : ℕ}

/-- The exact finite Jacobian facts consumed in differentiating the connection formula.
The inverse is the inverse of the transpose, not the inverse Jacobian. -/
structure HolomorphicJacobianJetAt
    (f : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) : Prop where
  jacobian_contDiff : ∀ a j,
    ContDiffAt ℝ 2 (fun w => holomorphicJacobianMatrix f w a j) z
  inverseTranspose_contDiff : ∀ s i,
    ContDiffAt ℝ 2 (fun w => ((holomorphicJacobianMatrix f w).transpose)⁻¹ s i) z
  jacobian_bar_zero : ∀ a j q,
    chartPartialBarComplex (fun w => holomorphicJacobianMatrix f w a j) z q = 0
  jacobian_z_bar_zero : ∀ a j p q,
    chartPartialBarComplex
      (fun w => chartPartialZComplex (fun v => holomorphicJacobianMatrix f v a j) w p)
      z q = 0
  inverseTranspose_bar_zero : ∀ s i q,
    chartPartialBarComplex
      (fun w => ((holomorphicJacobianMatrix f w).transpose)⁻¹ s i) z q = 0

/-- A real C3 holomorphic germ with invertible center Jacobian has the finite jet above.
No invertibility on the whole domain, global inverse, or complex smoothness hypothesis is used. -/
private theorem holomorphicJacobian_entry_contDiffAt
    (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (f : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (hf : ContDiffOn ℝ 3 f U) (hhol : DifferentiableOn ℂ f U)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U) (a j : Fin n) :
    ContDiffAt ℝ 2 (fun w => holomorphicJacobianMatrix f w a j) z := by
  let F : EuclideanSpace ℂ (Fin n) → ℂ := fun w => f w a
  have hF : ContDiffAt ℝ 3 F z := by
    have hfz : ContDiffAt ℝ 3 f z := (hf z hz).contDiffAt (hU.mem_nhds hz)
    have hcoord : ContDiff ℝ 3 (fun x : EuclideanSpace ℂ (Fin n) => x a) := by
      fun_prop
    simpa [F, Function.comp_def] using hcoord.contDiffAt.comp z hfz
  have hfd : ContDiffAt ℝ 2 (fderiv ℝ F) z :=
    hF.fderiv_right (m := 2) (by norm_num)
  have hEq : (fun w => holomorphicJacobianMatrix f w a j) =ᶠ[𝓝 z]
      (fun w => chartPartialZComplex F w j) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    have hfw : DifferentiableAt ℂ f w := (hhol w hw).differentiableAt (hU.mem_nhds hw)
    have hcoord : DifferentiableAt ℂ (fun x : EuclideanSpace ℂ (Fin n) => (f x) a) w := by
      fun_prop (disch := assumption)
    have hreal : fderiv ℝ (fun x : EuclideanSpace ℂ (Fin n) => (f x) a) w =
        (fderiv ℂ (fun x : EuclideanSpace ℂ (Fin n) => (f x) a) w).restrictScalars ℝ :=
      hcoord.fderiv_restrictScalars ℝ
    have hcomp : fderiv ℂ (fun x : EuclideanSpace ℂ (Fin n) => (f x) a) w =
        (EuclideanSpace.proj a).comp (fderiv ℂ f w) := by
      exact (EuclideanSpace.proj a).hasFDerivAt.comp w hfw.hasFDerivAt |>.fderiv
    have hI : fderiv ℂ (fun x : EuclideanSpace ℂ (Fin n) => (f x) a) w
        (Complex.I • EuclideanSpace.single j 1) = Complex.I *
          fderiv ℂ (fun x : EuclideanSpace ℂ (Fin n) => (f x) a) w
            (EuclideanSpace.single j 1) := by simp
    have hmat : holomorphicJacobianMatrix f w a j =
        fderiv ℂ (fun x : EuclideanSpace ℂ (Fin n) => (f x) a) w
          (EuclideanSpace.single j 1) := by
      change (fderiv ℂ f w (EuclideanSpace.single j 1)) a = _
      rw [hcomp]
      rfl
    rw [chartPartialZComplex, hreal, ContinuousLinearMap.coe_restrictScalars', hI, hmat]
    field_simp
    rw [Complex.I_sq]
    ring
  have hpartial : ContDiffAt ℝ 2 (fun w => chartPartialZComplex F w j) z := by
    have he : ContDiffAt ℝ 2 (fun w => fderiv ℝ F w (EuclideanSpace.single j 1)) z :=
      hfd.clm_apply contDiffAt_const
    have hie : ContDiffAt ℝ 2 (fun w => fderiv ℝ F w (Complex.I • EuclideanSpace.single j 1)) z :=
      hfd.clm_apply contDiffAt_const
    unfold chartPartialZComplex
    fun_prop (disch := assumption)
  exact hpartial.congr_of_eventuallyEq hEq

private noncomputable def finiteWirtinger
    (s : ℂ) (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (w : EuclideanSpace ℂ (Fin n)) (j : Fin n) : ℂ :=
  (fderiv ℝ F w (EuclideanSpace.single j 1) +
    s * fderiv ℝ F w (Complex.I • EuclideanSpace.single j 1)) / 2

private theorem finiteWirtinger_fderiv
    (s : ℂ) (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (hF : ContDiffAt ℝ 2 F z)
    (j : Fin n) (v : EuclideanSpace ℂ (Fin n)) :
    fderiv ℝ (fun w => finiteWirtinger s F w j) z v =
      (fderiv ℝ (fderiv ℝ F) z v (EuclideanSpace.single j 1) +
        s * fderiv ℝ (fderiv ℝ F) z v (Complex.I • EuclideanSpace.single j 1)) / 2 := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ F) z :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  let e : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j 1
  have he : DifferentiableAt ℝ (fun w => fderiv ℝ F w e) z :=
    hfd.clm_apply (differentiableAt_const e)
  have hie : DifferentiableAt ℝ (fun w => fderiv ℝ F w (Complex.I • e)) z :=
    hfd.clm_apply (differentiableAt_const (Complex.I • e))
  have h_e (u : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w => fderiv ℝ F w e) z u = fderiv ℝ (fderiv ℝ F) z u e := by
    rw [fderiv_clm_apply hfd (differentiableAt_const e)]
    simp
  have h_ie (u : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w => fderiv ℝ F w (Complex.I • e)) z u =
        fderiv ℝ (fderiv ℝ F) z u (Complex.I • e) := by
    rw [fderiv_clm_apply hfd (differentiableAt_const (Complex.I • e))]
    simp
  have hsum : DifferentiableAt ℝ
      (fun w => fderiv ℝ F w e + s * fderiv ℝ F w (Complex.I • e)) z :=
    he.add (hie.const_mul s)
  have hfun : (fun w => finiteWirtinger s F w j) =
      fun w => (2 : ℂ)⁻¹ * (fderiv ℝ F w e + s * fderiv ℝ F w (Complex.I • e)) := by
    funext w
    simp [finiteWirtinger, e, div_eq_mul_inv]
    ring
  rw [hfun, fderiv_const_mul hsum, fderiv_fun_add he (hie.const_mul s),
    fderiv_const_mul hie]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [h_e v, h_ie v]
  simp only [div_eq_mul_inv]
  ring

private theorem finiteWirtinger_comm
    (F : EuclideanSpace ℂ (Fin n) → ℂ) (z : EuclideanSpace ℂ (Fin n))
    (hF : ContDiffAt ℝ 2 F z) (p q : Fin n) :
    finiteWirtinger Complex.I (fun w => finiteWirtinger (-Complex.I) F w p) z q =
      finiteWirtinger (-Complex.I) (fun w => finiteWirtinger Complex.I F w q) z p := by
  have hs : IsSymmSndFDerivAt ℝ F z :=
    hF.isSymmSndFDerivAt
      (by simp [minSmoothness_of_isRCLikeNormedField])
  have ep : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single p 1
  have eq : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single q 1
  change (fderiv ℝ (fun w => finiteWirtinger (-Complex.I) F w p) z
      (EuclideanSpace.single q 1) +
      Complex.I * fderiv ℝ (fun w => finiteWirtinger (-Complex.I) F w p) z
        (Complex.I • EuclideanSpace.single q 1)) / 2 =
    (fderiv ℝ (fun w => finiteWirtinger Complex.I F w q) z
      (EuclideanSpace.single p 1) +
      (-Complex.I) * fderiv ℝ (fun w => finiteWirtinger Complex.I F w q) z
        (Complex.I • EuclideanSpace.single p 1)) / 2
  rw [finiteWirtinger_fderiv _ F z hF p (EuclideanSpace.single q 1),
    finiteWirtinger_fderiv _ F z hF p (Complex.I • EuclideanSpace.single q 1),
    finiteWirtinger_fderiv _ F z hF q (EuclideanSpace.single p 1),
    finiteWirtinger_fderiv _ F z hF q (Complex.I • EuclideanSpace.single p 1)]
  rw [hs (EuclideanSpace.single p 1) (EuclideanSpace.single q 1),
    hs (EuclideanSpace.single p 1) (Complex.I • EuclideanSpace.single q 1),
    hs (Complex.I • EuclideanSpace.single p 1) (EuclideanSpace.single q 1),
    hs (Complex.I • EuclideanSpace.single p 1) (Complex.I • EuclideanSpace.single q 1)]
  ring

private theorem chartPartialBar_zero_of_differentiableAt_complex
    (F : EuclideanSpace ℂ (Fin n) → ℂ) (z : EuclideanSpace ℂ (Fin n))
    (q : Fin n) (hF : DifferentiableAt ℂ F z) : chartPartialBarComplex F z q = 0 := by
  have hreal : fderiv ℝ F z = (fderiv ℂ F z).restrictScalars ℝ :=
    hF.fderiv_restrictScalars ℝ
  have hsmul : fderiv ℂ F z (Complex.I • EuclideanSpace.single q 1) =
      Complex.I * fderiv ℂ F z (EuclideanSpace.single q 1) := by simp
  unfold chartPartialBarComplex
  rw [hreal, ContinuousLinearMap.coe_restrictScalars', hsmul]
  rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
  ring

private theorem holomorphicJacobian_bar_zero_at
    (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (f : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (hf : ContDiffOn ℝ 3 f U) (hhol : DifferentiableOn ℂ f U)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U) (a j q : Fin n) :
    chartPartialBarComplex (fun w => holomorphicJacobianMatrix f w a j) z q = 0 := by
  let F : EuclideanSpace ℂ (Fin n) → ℂ := fun w => f w a
  have hF : ContDiffAt ℝ 2 F z := by
    have hfz : ContDiffAt ℝ 2 f z :=
      ((hf z hz).of_le (by norm_num)).contDiffAt (hU.mem_nhds hz)
    have hcoord : ContDiff ℝ 2 (fun x : EuclideanSpace ℂ (Fin n) => x a) := by fun_prop
    exact hcoord.contDiffAt.comp z hfz
  have hEq : (fun w => holomorphicJacobianMatrix f w a j) =ᶠ[𝓝 z]
      (fun w => chartPartialZComplex F w j) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    have hfw : DifferentiableAt ℂ f w := (hhol w hw).differentiableAt (hU.mem_nhds hw)
    have hcoord : DifferentiableAt ℂ (fun x : EuclideanSpace ℂ (Fin n) => (f x) a) w := by
      fun_prop (disch := assumption)
    have hreal : fderiv ℝ (fun x : EuclideanSpace ℂ (Fin n) => (f x) a) w =
        (fderiv ℂ (fun x : EuclideanSpace ℂ (Fin n) => (f x) a) w).restrictScalars ℝ :=
      hcoord.fderiv_restrictScalars ℝ
    have hcomp : fderiv ℂ (fun x : EuclideanSpace ℂ (Fin n) => (f x) a) w =
        (EuclideanSpace.proj a).comp (fderiv ℂ f w) := by
      exact (EuclideanSpace.proj a).hasFDerivAt.comp w hfw.hasFDerivAt |>.fderiv
    have hI : fderiv ℂ (fun x : EuclideanSpace ℂ (Fin n) => (f x) a) w
        (Complex.I • EuclideanSpace.single j 1) = Complex.I *
          fderiv ℂ (fun x : EuclideanSpace ℂ (Fin n) => (f x) a) w
            (EuclideanSpace.single j 1) := by simp
    have hmat : holomorphicJacobianMatrix f w a j =
        fderiv ℂ (fun x : EuclideanSpace ℂ (Fin n) => (f x) a) w
          (EuclideanSpace.single j 1) := by
      change (fderiv ℂ f w (EuclideanSpace.single j 1)) a = _
      rw [hcomp]
      rfl
    rw [chartPartialZComplex, hreal, ContinuousLinearMap.coe_restrictScalars', hI, hmat]
    field_simp
    rw [Complex.I_sq]
    ring
  have hbarEq : chartPartialBarComplex (fun w => holomorphicJacobianMatrix f w a j) z q =
      chartPartialBarComplex (fun w => chartPartialZComplex F w j) z q := by
    unfold chartPartialBarComplex
    rw [hEq.fderiv_eq]
  have hbarF : (fun w => chartPartialBarComplex F w q) =ᶠ[𝓝 z]
      (fun _ => (0 : ℂ)) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    have hfw : DifferentiableAt ℂ f w := (hhol w hw).differentiableAt (hU.mem_nhds hw)
    have hFw : DifferentiableAt ℂ F w := by
      dsimp [F]
      fun_prop (disch := assumption)
    exact chartPartialBar_zero_of_differentiableAt_complex F w q hFw
  have hzero : chartPartialZComplex (fun w => chartPartialBarComplex F w q) z j = 0 := by
    unfold chartPartialZComplex
    rw [hbarF.fderiv_eq]
    simp
  have hz (A : EuclideanSpace ℂ (Fin n) → ℂ)
      (w : EuclideanSpace ℂ (Fin n)) (k : Fin n) :
      finiteWirtinger (-Complex.I) A w k = chartPartialZComplex A w k := by
    simp [finiteWirtinger, chartPartialZComplex]
    ring
  have hb (A : EuclideanSpace ℂ (Fin n) → ℂ)
      (w : EuclideanSpace ℂ (Fin n)) (k : Fin n) :
      finiteWirtinger Complex.I A w k = chartPartialBarComplex A w k := rfl
  have hzf (k : Fin n) : (fun w => finiteWirtinger (-Complex.I) F w k) =
      (fun w => chartPartialZComplex F w k) := funext (fun w => hz F w k)
  have hbf (k : Fin n) : (fun w => finiteWirtinger Complex.I F w k) =
      (fun w => chartPartialBarComplex F w k) := funext (fun w => hb F w k)
  calc
    chartPartialBarComplex (fun w => holomorphicJacobianMatrix f w a j) z q =
        chartPartialBarComplex (fun w => chartPartialZComplex F w j) z q := hbarEq
    _ = finiteWirtinger Complex.I (fun w => finiteWirtinger (-Complex.I) F w j) z q := by
      rw [hzf]; rfl
    _ = finiteWirtinger (-Complex.I) (fun w => finiteWirtinger Complex.I F w q) z j :=
      finiteWirtinger_comm F z hF j q
    _ = chartPartialZComplex (fun w => chartPartialBarComplex F w q) z j := by
      rw [hbf]
      exact hz _ _ _
    _ = 0 := hzero

private theorem holomorphicJacobian_z_bar_zero_at
    (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (f : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (hf : ContDiffOn ℝ 3 f U) (hhol : DifferentiableOn ℂ f U)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U) (a j p q : Fin n) :
    chartPartialBarComplex
      (fun w => chartPartialZComplex (fun v => holomorphicJacobianMatrix f v a j) w p)
      z q = 0 := by
  let A : EuclideanSpace ℂ (Fin n) → ℂ := fun w => holomorphicJacobianMatrix f w a j
  have hA : ContDiffAt ℝ 2 A z := holomorphicJacobian_entry_contDiffAt U hU f hf hhol z hz a j
  have hbar : (fun w => chartPartialBarComplex A w q) =ᶠ[𝓝 z]
      fun _ => (0 : ℂ) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact holomorphicJacobian_bar_zero_at U hU f hf hhol w hw a j q
  have hzero : chartPartialZComplex (fun w => chartPartialBarComplex A w q) z p = 0 := by
    unfold chartPartialZComplex
    rw [hbar.fderiv_eq]
    simp
  have hz (B : EuclideanSpace ℂ (Fin n) → ℂ)
      (w : EuclideanSpace ℂ (Fin n)) (k : Fin n) :
      finiteWirtinger (-Complex.I) B w k = chartPartialZComplex B w k := by
    simp [finiteWirtinger, chartPartialZComplex]
    ring
  have hb (B : EuclideanSpace ℂ (Fin n) → ℂ)
      (w : EuclideanSpace ℂ (Fin n)) (k : Fin n) :
      finiteWirtinger Complex.I B w k = chartPartialBarComplex B w k := rfl
  have hzf (k : Fin n) : (fun w => finiteWirtinger (-Complex.I) A w k) =
      (fun w => chartPartialZComplex A w k) := funext (fun w => hz A w k)
  have hbf (k : Fin n) : (fun w => finiteWirtinger Complex.I A w k) =
      (fun w => chartPartialBarComplex A w k) := funext (fun w => hb A w k)
  calc
    chartPartialBarComplex (fun w => chartPartialZComplex A w p) z q =
        finiteWirtinger Complex.I (fun w => finiteWirtinger (-Complex.I) A w p) z q := by
          rw [hzf]; rfl
    _ = finiteWirtinger (-Complex.I) (fun w => finiteWirtinger Complex.I A w q) z p :=
      finiteWirtinger_comm A z hA p q
    _ = chartPartialZComplex (fun w => chartPartialBarComplex A w q) z p := by
      rw [hbf]
      exact hz _ _ _
    _ = 0 := hzero

private theorem finiteChartBar_sum
    {ι : Type*} [Fintype ι] (F : ι → EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (q : Fin n)
    (hF : ∀ i, DifferentiableAt ℝ (F i) z) :
    chartPartialBarComplex (fun w => ∑ i, F i w) z q =
      ∑ i, chartPartialBarComplex (F i) z q := by
  unfold chartPartialBarComplex
  have hfd : fderiv ℝ (fun w => ∑ i, F i w) z = ∑ i, fderiv ℝ (F i) z := by
    simpa using fderiv_fun_sum (u := Finset.univ) (fun i hi => hF i)
  rw [hfd]
  simp only [sum_apply]
  have hsum :
      (∑ i, fderiv ℝ (F i) z (EuclideanSpace.single q 1)) +
        Complex.I * ∑ i, fderiv ℝ (F i) z (Complex.I • EuclideanSpace.single q 1) =
      ∑ i, (fderiv ℝ (F i) z (EuclideanSpace.single q 1) +
        Complex.I * fderiv ℝ (F i) z (Complex.I • EuclideanSpace.single q 1)) := by
    rw [Finset.mul_sum, Finset.sum_add_distrib]
  rw [hsum]
  simp only [div_eq_mul_inv, Finset.sum_mul]

private theorem finiteChartBar_mul
    (F G : EuclideanSpace ℂ (Fin n) → ℂ) (z : EuclideanSpace ℂ (Fin n))
    (q : Fin n) (hF : DifferentiableAt ℝ F z) (hG : DifferentiableAt ℝ G z) :
    chartPartialBarComplex (fun w => F w * G w) z q =
      chartPartialBarComplex F z q * G z + F z * chartPartialBarComplex G z q := by
  unfold chartPartialBarComplex
  rw [fderiv_fun_mul hF hG]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

private theorem finiteChartBar_inverse
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hg : ∀ a b, ContDiffAt ℝ 2 (fun w => g w a b) z)
    (hgi : ∀ a b, ContDiffAt ℝ 2 (fun w => (g w)⁻¹ a b) z)
    (hdet : IsUnit (g z).det) (i j q : Fin n) :
    chartPartialBarComplex (fun w => (g w)⁻¹ i j) z q =
      -(∑ a, ∑ b, (g z)⁻¹ i a * chartPartialBarComplex (fun w => g w a b) z q *
        (g z)⁻¹ b j) := by
  have he (a b : Fin n) : DifferentiableAt ℝ (fun w => g w a b) z :=
    (hg a b).differentiableAt (by norm_num)
  have hi (a b : Fin n) : DifferentiableAt ℝ (fun w => (g w)⁻¹ a b) z :=
    (hgi a b).differentiableAt (by norm_num)
  have hprod (a b : Fin n) :
      (fun w => ∑ t : Fin n, (g w)⁻¹ a t * g w t b) =ᶠ[𝓝 z]
        (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) a b) := by
    have hd : ContinuousAt (fun w => (g w).det) z := by
      have hdc : ContDiffAt ℝ 2 (fun w => (g w).det) z := by
        have hx : ∀ k l, ContDiffAt ℝ 2 (fun w => g w k l) z := hg
        simp_rw [Matrix.det_apply]
        fun_prop (disch := assumption)
      exact hdc.continuousAt
    have hne : ∀ᶠ w in 𝓝 z, (g w).det ≠ 0 := hd.eventually_ne hdet.ne_zero
    filter_upwards [hne] with w hw
    have hu : IsUnit (g w).det := isUnit_iff_ne_zero.mpr hw
    simpa only [Matrix.mul_apply] using congrArg
      (fun M : Matrix (Fin n) (Fin n) ℂ => M a b) (Matrix.nonsing_inv_mul (g w) hu)
  have hzero (a b : Fin n) :
      chartPartialBarComplex (fun w => ∑ t : Fin n, (g w)⁻¹ a t * g w t b) z q = 0 := by
    unfold chartPartialBarComplex
    rw [hprod a b |>.fderiv_eq]
    simp
  have hrel (a b : Fin n) :
      (∑ t, chartPartialBarComplex (fun w => (g w)⁻¹ a t) z q * g z t b) +
      (∑ t, (g z)⁻¹ a t * chartPartialBarComplex (fun w => g w t b) z q) = 0 := by
    have hh := hzero a b
    rw [finiteChartBar_sum (fun t w => (g w)⁻¹ a t * g w t b) z q
      (fun t => (hi a t).mul (he t b))] at hh
    simp_rw [finiteChartBar_mul _ _ z q (hi a _) (he _ b)] at hh
    rwa [Finset.sum_add_distrib] at hh
  let D : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun a b =>
    chartPartialBarComplex (fun w => (g w)⁻¹ a b) z q)
  let H : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun a b =>
    chartPartialBarComplex (fun w => g w a b) z q)
  have hmat : D * g z = -((g z)⁻¹ * H) := by
    ext a b
    simp only [D, H, Matrix.mul_apply, Matrix.of_apply, Matrix.neg_apply]
    exact (eq_neg_iff_add_eq_zero).2 (hrel a b)
  have hresult : D = -((g z)⁻¹ * H * (g z)⁻¹) := by
    calc
      D = D * 1 := by simp
      _ = D * (g z * (g z)⁻¹) := by rw [← Matrix.mul_nonsing_inv (g z) hdet]
      _ = (D * g z) * (g z)⁻¹ := by rw [Matrix.mul_assoc]
      _ = -((g z)⁻¹ * H * (g z)⁻¹) := by rw [hmat]; simp [Matrix.mul_assoc]
  have hentry := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) hresult
  simp only [D, H, Matrix.of_apply, Matrix.neg_apply, Matrix.mul_apply, Finset.sum_mul] at hentry
  rw [Finset.sum_comm]
  exact hentry

private theorem inverseTranspose_finiteJet
    (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (f : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (hf : ContDiffOn ℝ 3 f U) (hhol : DifferentiableOn ℂ f U)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U)
    (hjac : IsUnit (holomorphicJacobianMatrix f z).det) :
    (∀ s i, ContDiffAt ℝ 2
      (fun w => ((holomorphicJacobianMatrix f w).transpose)⁻¹ s i) z) ∧
    (∀ s i q, chartPartialBarComplex
      (fun w => ((holomorphicJacobianMatrix f w).transpose)⁻¹ s i) z q = 0) := by
  let A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w => (holomorphicJacobianMatrix f w).transpose
  have hentry : ∀ i j, ContDiffAt ℝ 2 (fun w => A w i j) z := by
    intro i j
    simpa [A] using holomorphicJacobian_entry_contDiffAt U hU f hf hhol z hz j i
  have hdet' : ContDiffAt ℝ 2
      (fun w => ∑ σ : Equiv.Perm (Fin n),
        Equiv.Perm.sign σ • ∏ i, A w (σ i) i) z := by
    fun_prop (disch := assumption)
  have hdet : ContDiffAt ℝ 2 (fun w => (A w).det) z := by
    convert hdet' using 1
    funext w
    exact Matrix.det_apply (A w)
  have hdet0 : (A z).det ≠ 0 := by
    intro hzero
    apply (isUnit_iff_ne_zero.mp hjac)
    simpa [A, Matrix.det_transpose] using hzero
  have hdetInv : ContDiffAt ℝ 2 (fun w => ((A w).det)⁻¹) z :=
    hdet.inv hdet0
  have hadj : ∀ i j, ContDiffAt ℝ 2 (fun w => (A w).adjugate i j) z := by
    intro i j
    let B : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
      fun w => (A w).updateRow j (Pi.single i 1)
    have hBentry : ∀ k l, ContDiffAt ℝ 2 (fun w => B w k l) z := by
      intro k l
      by_cases h : k = j
      · subst k
        simp [B]
        exact contDiffAt_const
      · simp [B, Matrix.updateRow_apply, h]
        exact hentry k l
    have hminor : ContDiffAt ℝ 2
        (fun w => ∑ σ : Equiv.Perm (Fin n),
          Equiv.Perm.sign σ • ∏ k, B w (σ k) k) z := by
      fun_prop (disch := assumption)
    convert hminor using 1
    funext w
    rw [Matrix.adjugate_apply, Matrix.det_apply]
  have hdetEventually : ∀ᶠ w in 𝓝 z, (A w).det ≠ 0 := by
    exact hdet.continuousAt.eventually_ne hdet0
  have hinvCont : ∀ s i, ContDiffAt ℝ 2 (fun w => (A w)⁻¹ s i) z := by
    intro s i
    have heq : (fun w => (A w)⁻¹ s i) =ᶠ[𝓝 z]
        (fun w => ((A w).det)⁻¹ * (A w).adjugate s i) := by
      filter_upwards [hdetEventually] with w hw
      have hu : IsUnit (A w).det := isUnit_iff_ne_zero.mpr hw
      rw [Matrix.nonsing_inv_apply (A w) hu]
      simp [Units.val_inv_eq_inv_val, Matrix.smul_apply]
    exact (hdetInv.mul (hadj s i)).congr_of_eventuallyEq heq
  have hbarA : ∀ a b q, chartPartialBarComplex (fun w => A w a b) z q = 0 := by
    intro a b q
    exact holomorphicJacobian_bar_zero_at U hU f hf hhol z hz b a q
  have hdetUnit : IsUnit (A z).det := by
    simpa [A, Matrix.det_transpose] using hjac
  have hbar : ∀ s i q, chartPartialBarComplex (fun w => (A w)⁻¹ s i) z q = 0 := by
    intro s i q
    rw [finiteChartBar_inverse A z hentry hinvCont hdetUnit s i q]
    simp [hbarA]
  exact ⟨hinvCont, hbar⟩

theorem holomorphicJacobianJetAt_of_contDiffOn
    (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (f : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (hf : ContDiffOn ℝ 3 f U) (hhol : DifferentiableOn ℂ f U)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U)
    (hjac : IsUnit (holomorphicJacobianMatrix f z).det) :
    HolomorphicJacobianJetAt f z := by
  have hinv := inverseTranspose_finiteJet U hU f hf hhol z hz hjac
  refine ⟨?_, hinv.1, ?_, ?_, hinv.2⟩
  · intro a j
    exact holomorphicJacobian_entry_contDiffAt U hU f hf hhol z hz a j
  · intro a j q
    exact holomorphicJacobian_bar_zero_at U hU f hf hhol z hz a j q
  · intro a j p q
    exact holomorphicJacobian_z_bar_zero_at U hU f hf hhol z hz a j p q

end KahlerForm
