module

public import CalabiYau.Geometry.Kahler.Basic
public import CalabiYau.Geometry.Kahler.Laplacian.Cofactor
public import CalabiYau.Geometry.Kahler.Curvature.Chart.Basic
import CalabiYau.Geometry.Kahler.Curvature.Chart.MixedDerivatives
import CalabiYau.Geometry.Kahler.Curvature.Chart.InverseDerivative
public import CalabiYau.Geometry.Kahler.Curvature.Chart.ConnectionGerm

public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder

namespace KahlerForm

variable {n : ℕ}

/-- The antiholomorphic coordinate derivative distributes over subtraction. -/
theorem chartPartialBarComplex_sub (F G : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (q : Fin n)
    (hF : DifferentiableAt ℝ F z) (hG : DifferentiableAt ℝ G z) :
    chartPartialBarComplex (fun w => F w - G w) z q =
      chartPartialBarComplex F z q - chartPartialBarComplex G z q := by
  unfold chartPartialBarComplex
  rw [fderiv_fun_sub hF hG]
  simp only [sub_apply]
  ring

private theorem clmMatrix_single_eq_sum
    (L : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (j : Fin n) :
    L (EuclideanSpace.single j 1) =
      ∑ a, (EuclideanSpace.clmMatrix L a j) • EuclideanSpace.single a 1 := by
  ext a
  simp [EuclideanSpace.clmMatrix, Pi.single_apply]

private theorem wirtinger_directional_smul
    (D : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ) (c : ℂ)
    (v : EuclideanSpace ℂ (Fin n)) :
    D (c • v) - Complex.I * D (Complex.I • (c • v)) =
      c * (D v - Complex.I * D (Complex.I • v)) := by
  have hc₁ : c • v = c.re • v + c.im • (Complex.I • v) := by
    calc
      c • v = ((c.re : ℂ) + (c.im : ℂ) * Complex.I) • v :=
        congrArg (fun z : ℂ => z • v) (Complex.re_add_im c).symm
      _ = c.re • v + c.im • (Complex.I • v) := by
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ) c.re,
          RCLike.real_smul_eq_coe_smul (K := ℂ) c.im]
        rw [add_smul, smul_smul]
        rfl
  have hc₂ : Complex.I • (c • v) = -c.im • v + c.re • (Complex.I • v) := by
    have hscalar : Complex.I * c = ((-c.im : ℝ) : ℂ) + (c.re : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    calc
      Complex.I • (c • v) = (Complex.I * c) • v := by rw [smul_smul]
      _ = (((-c.im : ℝ) : ℂ) + (c.re : ℂ) * Complex.I) • v := by rw [hscalar]
      _ = -c.im • v + c.re • (Complex.I • v) := by
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ) (-c.im),
          RCLike.real_smul_eq_coe_smul (K := ℂ) c.re]
        rw [add_smul, smul_smul]
        rfl
  rw [hc₂, hc₁]
  simp only [ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_eq_mul]
  conv_rhs => rw [← Complex.re_add_im c]
  ring_nf
  simp only [Complex.I_sq]
  push_cast
  linear_combination

private theorem antiwirtinger_directional_smul
    (D : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ) (c : ℂ)
    (v : EuclideanSpace ℂ (Fin n)) :
    D (c • v) + Complex.I * D (Complex.I • (c • v)) =
      star c * (D v + Complex.I * D (Complex.I • v)) := by
  let Dconj : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ := Complex.conjCLE.toContinuousLinearMap.comp D
  have h := wirtinger_directional_smul Dconj c v
  have hc := congrArg star h
  simpa [Dconj, ContinuousLinearMap.comp_apply, Complex.conjCLE_apply,
    star_sub, star_mul, star_star, Complex.conj_I, mul_comm, mul_left_comm,
    mul_assoc] using hc

private theorem chartPartialZ_comp_holomorphic
    (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (f : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n)
    (hF : DifferentiableAt ℝ F (f z)) (hf : DifferentiableAt ℂ f z) :
    chartPartialZComplex (fun w ↦ F (f w)) z j =
      ∑ a, (EuclideanSpace.clmMatrix (fderiv ℂ f z)) a j *
        chartPartialZComplex F (f z) a := by
  let L := fderiv ℂ f z
  have hfℝ : DifferentiableAt ℝ f z := hf.restrictScalars ℝ
  have hreal : fderiv ℝ f z = L.restrictScalars ℝ := by
    simpa [L] using hf.fderiv_restrictScalars ℝ
  have hcomp := fderiv_comp (f := f) (g := F) (x := z) hF hfℝ
  have hcomp' : fderiv ℝ (fun w ↦ F (f w)) z =
      (fderiv ℝ F (f z)).comp (fderiv ℝ f z) := by
    simpa [Function.comp_def] using hcomp
  let D := fderiv ℝ F (f z)
  let A := EuclideanSpace.clmMatrix L
  let e := EuclideanSpace.single j (1 : ℂ)
  have hvec : L e = ∑ a, (A a j) • EuclideanSpace.single a (1 : ℂ) := by
    simpa [A, e] using clmMatrix_single_eq_sum L j
  unfold chartPartialZComplex
  rw [hcomp', hreal]
  simp only [ContinuousLinearMap.comp_apply]
  change (D (L e) - Complex.I * D (L (Complex.I • e))) / 2 = _
  rw [map_smul, hvec]
  simp only [map_sum, Finset.smul_sum]
  have hsum :
      (∑ a, D ((A a j) • EuclideanSpace.single a (1 : ℂ))) -
        Complex.I * ∑ a, D (Complex.I • ((A a j) • EuclideanSpace.single a (1 : ℂ))) =
      ∑ a, (D ((A a j) • EuclideanSpace.single a (1 : ℂ)) -
        Complex.I * D (Complex.I • ((A a j) • EuclideanSpace.single a (1 : ℂ)))) := by
    rw [Finset.mul_sum, Finset.sum_sub_distrib]
  rw [hsum]
  simp_rw [wirtinger_directional_smul]
  simp only [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  ring

private theorem chartPartialBar_comp_holomorphic
    (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (f : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n)
    (hF : DifferentiableAt ℝ F (f z)) (hf : DifferentiableAt ℂ f z) :
    chartPartialBarComplex (fun w ↦ F (f w)) z j =
      ∑ a, star (EuclideanSpace.clmMatrix (fderiv ℂ f z) a j) *
        chartPartialBarComplex F (f z) a := by
  let L := fderiv ℂ f z
  have hfℝ : DifferentiableAt ℝ f z := hf.restrictScalars ℝ
  have hreal : fderiv ℝ f z = L.restrictScalars ℝ := by
    simpa [L] using hf.fderiv_restrictScalars ℝ
  have hcomp := fderiv_comp (f := f) (g := F) (x := z) hF hfℝ
  have hcomp' : fderiv ℝ (fun w ↦ F (f w)) z =
      (fderiv ℝ F (f z)).comp (fderiv ℝ f z) := by
    simpa [Function.comp_def] using hcomp
  let D := fderiv ℝ F (f z)
  let A := EuclideanSpace.clmMatrix L
  let e := EuclideanSpace.single j (1 : ℂ)
  have hvec : L e = ∑ a, (A a j) • EuclideanSpace.single a (1 : ℂ) := by
    simpa [A, e] using clmMatrix_single_eq_sum L j
  unfold chartPartialBarComplex
  rw [hcomp', hreal]
  simp only [ContinuousLinearMap.comp_apply]
  change (D (L e) + Complex.I * D (L (Complex.I • e))) / 2 = _
  rw [map_smul, hvec]
  simp only [map_sum, Finset.smul_sum]
  have hsum :
      (∑ a, D ((A a j) • EuclideanSpace.single a (1 : ℂ))) +
        Complex.I * ∑ a, D (Complex.I • ((A a j) • EuclideanSpace.single a (1 : ℂ))) =
      ∑ a, (D ((A a j) • EuclideanSpace.single a (1 : ℂ)) +
        Complex.I * D (Complex.I • ((A a j) • EuclideanSpace.single a (1 : ℂ)))) := by
    rw [Finset.mul_sum, Finset.sum_add_distrib]
  rw [hsum]
  simp_rw [antiwirtinger_directional_smul]
  simp only [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  ring

private theorem sum_swap_outer_inner
    {ι : Type*} [Fintype ι] (f : ι → ι → ι → ℂ) :
    (∑ x, ∑ a, ∑ b, f x a b) = ∑ b, ∑ a, ∑ x, f x a b := by
  calc
    _ = ∑ a, ∑ x, ∑ b, f x a b := Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ x, f x a b := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = ∑ b, ∑ a, ∑ x, f x a b := Finset.sum_comm

private theorem chart_pullback_metric_entry_contDiffAt
    (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (f : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (hf : ContDiffOn ℝ ∞ f U) (hhol : DifferentiableOn ℂ f U)
    (g g' : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (hg' : ∀ a b, ContDiffOn ℝ ∞ (fun w => g' w a b) (f '' U))
    (hmetric : ∀ w ∈ U,
      g w = Matrix.transpose (EuclideanSpace.clmMatrix (fderiv ℂ f w)) *
        g' (f w) * (EuclideanSpace.clmMatrix (fderiv ℂ f w)).map star)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U)
    (hjac : IsUnit (EuclideanSpace.clmMatrix (fderiv ℂ f z)).det)
    (a b : Fin n) : ContDiffAt ℝ ∞ (fun w => g w a b) z := by
  have himage := chart_pullback_image_nhds U hU f hf hhol z hz hjac
  have hfs : ContDiffAt ℝ ∞ f z := (hf z hz).contDiffAt (hU.mem_nhds hz)
  have hfzimage : f z ∈ f '' U := ⟨z, hz, rfl⟩
  have hG : ContDiffAt ℝ ∞ (fun y => g' y a b) (f z) :=
    (hg' a b (f z) hfzimage).contDiffAt himage
  have hcomp : ContDiffAt ℝ ∞ (fun w => g' (f w) a b) z := hG.comp z hfs
  have hA (i k : Fin n) :
      ContDiffAt ℝ ∞ (fun w => (EuclideanSpace.clmMatrix (fderiv ℂ f w)) i k) z :=
    chart_pullback_jacobian_entry_contDiffAt U hU f hf hhol z hz i k
  have hAstar (i k : Fin n) :
      ContDiffAt ℝ ∞ (fun w => star (EuclideanSpace.clmMatrix (fderiv ℂ f w) i k)) z := by
    change ContDiffAt ℝ ∞
      (fun w => Complex.conjCLE (EuclideanSpace.clmMatrix (fderiv ℂ f w) i k)) z
    fun_prop (disch := assumption)
  have hpull : ContDiffAt ℝ ∞ (fun w =>
      (Matrix.transpose (EuclideanSpace.clmMatrix (fderiv ℂ f w)) *
        g' (f w) * (EuclideanSpace.clmMatrix (fderiv ℂ f w)).map star) a b) z := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    fun_prop (disch := assumption)
  have hEq : (fun w => g w a b) =ᶠ[nhds z] (fun w =>
      (Matrix.transpose (EuclideanSpace.clmMatrix (fderiv ℂ f w)) *
        g' (f w) * (EuclideanSpace.clmMatrix (fderiv ℂ f w)).map star) a b) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M a b) (hmetric w hw)
  exact hpull.congr_of_eventuallyEq hEq

private theorem chartPartialZComplex_coordinate
    (z : EuclideanSpace ℂ (Fin n)) (a b : Fin n) :
    chartPartialZComplex (fun x : EuclideanSpace ℂ (Fin n) => x a) z b =
      if a = b then 1 else 0 := by
  have hF : DifferentiableAt ℂ (fun x : EuclideanSpace ℂ (Fin n) => x a) z := by
    fun_prop
  have hreal : fderiv ℝ (fun x : EuclideanSpace ℂ (Fin n) => x a) z =
      (fderiv ℂ (fun x : EuclideanSpace ℂ (Fin n) => x a) z).restrictScalars ℝ :=
    hF.fderiv_restrictScalars ℝ
  let P : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ := EuclideanSpace.proj a
  have hderiv : fderiv ℂ (fun x : EuclideanSpace ℂ (Fin n) => x a) z = P := by
    simpa [P] using P.hasFDerivAt.fderiv
  have hsmul : fderiv ℂ (fun x : EuclideanSpace ℂ (Fin n) => x a) z
      (Complex.I • EuclideanSpace.single b 1) = Complex.I *
        fderiv ℂ (fun x : EuclideanSpace ℂ (Fin n) => x a) z
          (EuclideanSpace.single b 1) := by simp
  unfold chartPartialZComplex
  rw [hreal, ContinuousLinearMap.coe_restrictScalars', hsmul, hderiv]
  by_cases hab : a = b <;> simp [P, EuclideanSpace.proj, hab]

private theorem chartPartialZComplex_coordinate_comp
    (f : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) (a j : Fin n)
    (hf : DifferentiableAt ℂ f z) :
    chartPartialZComplex (fun w => (f w) a) z j =
      (EuclideanSpace.clmMatrix (fderiv ℂ f z)) a j := by
  have hF : DifferentiableAt ℝ
      (fun x : EuclideanSpace ℂ (Fin n) => x a) (f z) := by fun_prop
  rw [chartPartialZ_comp_holomorphic (F := fun x : EuclideanSpace ℂ (Fin n) => x a)
    (f := f) (z := z) (j := j) hF hf]
  simp_rw [chartPartialZComplex_coordinate]
  simp

private theorem chartPartialBarComplex_eq_zero_of_differentiableAt_complex
    (F : EuclideanSpace ℂ (Fin n) → ℂ) (z : EuclideanSpace ℂ (Fin n))
    (q : Fin n) (hF : DifferentiableAt ℂ F z) :
    chartPartialBarComplex F z q = 0 := by
  have hreal : fderiv ℝ F z = (fderiv ℂ F z).restrictScalars ℝ :=
    hF.fderiv_restrictScalars ℝ
  have hsmul : fderiv ℂ F z (Complex.I • EuclideanSpace.single q 1) =
      Complex.I * fderiv ℂ F z (EuclideanSpace.single q 1) := by simp
  unfold chartPartialBarComplex
  rw [hreal, ContinuousLinearMap.coe_restrictScalars', hsmul]
  rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
  ring

private theorem chartPartialZComplex_jacobian_contDiffAt
    (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (f : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (hf : ContDiffOn ℝ ∞ f U) (hhol : DifferentiableOn ℂ f U)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U) (a j : Fin n) :
    ContDiffAt ℝ ∞
      (fun w => (EuclideanSpace.clmMatrix (fderiv ℂ f w)) a j) z := by
  let F : EuclideanSpace ℂ (Fin n) → ℂ := fun w => f w a
  have hF : ContDiffAt ℝ ∞ F z := by
    have hfz : ContDiffAt ℝ ∞ f z := (hf z hz).contDiffAt (hU.mem_nhds hz)
    have hcoord : ContDiff ℝ ∞ (fun x : EuclideanSpace ℂ (Fin n) => x a) := by
      fun_prop
    simpa [F, Function.comp_def] using hcoord.contDiffAt.comp z hfz
  have hEq :
      (fun w => (EuclideanSpace.clmMatrix (fderiv ℂ f w)) a j) =ᶠ[nhds z]
        (fun w => chartPartialZComplex F w j) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    have hfw : DifferentiableAt ℂ f w :=
      (hhol w hw).differentiableAt (hU.mem_nhds hw)
    exact (chartPartialZComplex_coordinate_comp f w a j hfw).symm
  exact (chartPartialZComplex_contDiffAt F z hF j).congr_of_eventuallyEq hEq

private theorem chartPartialBarComplex_jacobian_eq_zero
    (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (f : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (hf : ContDiffOn ℝ ∞ f U) (hhol : DifferentiableOn ℂ f U)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U) (a j q : Fin n) :
    chartPartialBarComplex
      (fun w => (EuclideanSpace.clmMatrix (fderiv ℂ f w)) a j) z q = 0 := by
  let F : EuclideanSpace ℂ (Fin n) → ℂ := fun w => f w a
  have hF : ContDiffAt ℝ ∞ F z := by
    have hfz : ContDiffAt ℝ ∞ f z := (hf z hz).contDiffAt (hU.mem_nhds hz)
    have hcoord : ContDiff ℝ ∞ (fun x : EuclideanSpace ℂ (Fin n) => x a) := by
      fun_prop
    simpa [F, Function.comp_def] using hcoord.contDiffAt.comp z hfz
  have hEq :
      (fun w => (EuclideanSpace.clmMatrix (fderiv ℂ f w)) a j) =ᶠ[nhds z]
        (fun w => chartPartialZComplex F w j) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    have hfw : DifferentiableAt ℂ f w :=
      (hhol w hw).differentiableAt (hU.mem_nhds hw)
    exact (chartPartialZComplex_coordinate_comp f w a j hfw).symm
  have hbarEq :
      chartPartialBarComplex
        (fun w => (EuclideanSpace.clmMatrix (fderiv ℂ f w)) a j) z q =
      chartPartialBarComplex (fun w => chartPartialZComplex F w j) z q := by
    unfold chartPartialBarComplex
    rw [hEq.fderiv_eq]
  have hbarF : (fun w => chartPartialBarComplex F w q) =ᶠ[nhds z]
      fun _ => (0 : ℂ) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    have hfw : DifferentiableAt ℂ f w :=
      (hhol w hw).differentiableAt (hU.mem_nhds hw)
    have hFw : DifferentiableAt ℂ F w := by
      dsimp [F]
      fun_prop (disch := assumption)
    exact chartPartialBarComplex_eq_zero_of_differentiableAt_complex F w q hFw
  have hzero : chartPartialZComplex
      (fun w => chartPartialBarComplex F w q) z j = 0 := by
    unfold chartPartialZComplex
    rw [hbarF.fderiv_eq]
    simp
  calc
    chartPartialBarComplex
        (fun w => (EuclideanSpace.clmMatrix (fderiv ℂ f w)) a j) z q =
        chartPartialBarComplex (fun w => chartPartialZComplex F w j) z q := hbarEq
    _ = chartPartialZComplex (fun w => chartPartialBarComplex F w q) z j :=
      chartPartialBarComplex_chartPartialZComplex_comm_at F z hF j q
    _ = 0 := hzero

private theorem chartPartialBarComplex_chartPartialZComplex_jacobian_eq_zero
    (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (f : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (hf : ContDiffOn ℝ ∞ f U) (hhol : DifferentiableOn ℂ f U)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U) (a j p q : Fin n) :
    chartPartialBarComplex
      (fun w => chartPartialZComplex
        (fun x => (EuclideanSpace.clmMatrix (fderiv ℂ f x)) a j) w p) z q = 0 := by
  let A : EuclideanSpace ℂ (Fin n) → ℂ :=
    fun w => (EuclideanSpace.clmMatrix (fderiv ℂ f w)) a j
  have hA : ContDiffAt ℝ ∞ A z := by
    exact chartPartialZComplex_jacobian_contDiffAt U hU f hf hhol z hz a j
  have hbar : (fun w => chartPartialBarComplex A w q) =ᶠ[nhds z]
      fun _ => (0 : ℂ) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact chartPartialBarComplex_jacobian_eq_zero U hU f hf hhol w hw a j q
  have hzero : chartPartialZComplex (fun w => chartPartialBarComplex A w q) z p = 0 := by
    unfold chartPartialZComplex
    rw [hbar.fderiv_eq]
    simp
  calc
    chartPartialBarComplex (fun w => chartPartialZComplex A w p) z q =
        chartPartialZComplex (fun w => chartPartialBarComplex A w q) z p :=
      chartPartialBarComplex_chartPartialZComplex_comm_at A z hA p q
    _ = 0 := hzero

private theorem sum_move_first_to_last4 {ι : Type*} [Fintype ι]
    (f : ι → ι → ι → ι → ℂ) :
    (∑ x, ∑ a, ∑ b, ∑ r, f x a b r) = ∑ a, ∑ b, ∑ r, ∑ x, f x a b r := by
  calc
    _ = ∑ a, ∑ x, ∑ b, ∑ r, f x a b r := Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ x, ∑ r, f x a b r := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ r, ∑ x, f x a b r := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact Finset.sum_comm
private theorem sum_move_first_to_last5 {ι : Type*} [Fintype ι]
    (f : ι → ι → ι → ι → ι → ℂ) :
    (∑ x, ∑ a, ∑ b, ∑ r, ∑ s, f x a b r s) =
      ∑ a, ∑ b, ∑ r, ∑ s, ∑ x, f x a b r s := by
  calc
    _ = ∑ a, ∑ x, ∑ b, ∑ r, ∑ s, f x a b r s := Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ x, ∑ r, ∑ s, f x a b r s := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ r, ∑ x, ∑ s, f x a b r s := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ r, ∑ s, ∑ x, f x a b r s := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro r hr
      exact Finset.sum_comm
/-- The finite-sum identity for the connection under a holomorphic frame change. -/
private theorem chartFrameConnectionFormula
    (A AbarInv H Hinv Ainv Ginv : Matrix (Fin n) (Fin n) ℂ)
    (dA : Fin n → Fin n → Fin n → ℂ)
    (dH : Fin n → Fin n → Fin n → ℂ)
    (p i k : Fin n)
    (hGinv : ∀ l, Ginv l i = ∑ r, ∑ s,
      AbarInv l r * Hinv r s * Ainv s i)
    (hBar : ∀ r b, ∑ l, AbarInv l r * star (A b l) = if b = r then 1 else 0)
    (hH : ∀ a s, ∑ b, Hinv b s * H a b = if a = s then 1 else 0) :
    (∑ l, Ginv l i * (∑ a, ∑ b,
      (dA p a k * H a b + A a k * (∑ c, A c p * dH c a b)) * star (A b l))) =
      (∑ s, Ainv s i * dA p s k) +
        ∑ s, ∑ c, ∑ a, Ainv s i * A a k * A c p *
          (∑ b, Hinv b s * dH c a b) := by
  classical
  have hcontract (a b r s : Fin n) :
      (∑ l, AbarInv l r * Hinv r s * Ainv s i *
        ((dA p a k * H a b + A a k * (∑ c, A c p * dH c a b)) * star (A b l))) =
      Hinv r s * Ainv s i *
        (dA p a k * H a b + A a k * (∑ c, A c p * dH c a b)) *
          (if b = r then 1 else 0) := by
    calc
      _ = ∑ l, (Hinv r s * Ainv s i *
          (dA p a k * H a b + A a k * (∑ c, A c p * dH c a b))) *
            (AbarInv l r * star (A b l)) := by
        apply Finset.sum_congr rfl
        intro l hl
        ring
      _ = (Hinv r s * Ainv s i *
          (dA p a k * H a b + A a k * (∑ c, A c p * dH c a b))) *
            ∑ l, AbarInv l r * star (A b l) := by rw [← Finset.mul_sum]
      _ = _ := by rw [hBar r b]
  simp_rw [hGinv]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [sum_move_first_to_last5]
  have hcontractAll :
      (∑ a, ∑ b, ∑ r, ∑ s, ∑ l,
        AbarInv l r * Hinv r s * Ainv s i *
          ((dA p a k * H a b + ∑ c, A a k * (A c p * dH c a b)) * star (A b l))) =
      ∑ a, ∑ b, ∑ r, ∑ s,
        Hinv r s * Ainv s i *
          (dA p a k * H a b + A a k * (∑ c, A c p * dH c a b)) *
            (if b = r then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro s hs
    convert hcontract a b r s using 1
    rw [← Finset.mul_sum]
  rw [hcontractAll]
  simp_rw [mul_add, add_mul]
  simp_rw [Finset.sum_add_distrib]
  have hfirst :
      (∑ a, ∑ b, ∑ r, ∑ s,
        Hinv r s * Ainv s i * (dA p a k * H a b) * if b = r then 1 else 0) =
      ∑ s, Ainv s i * dA p s k := by
    calc
      _ = ∑ a, ∑ r, ∑ s, ∑ b,
          Hinv r s * Ainv s i * (dA p a k * H a b) * if b = r then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro r hr
        exact Finset.sum_comm
      _ = ∑ a, ∑ r, ∑ s, Hinv r s * Ainv s i * (dA p a k * H a r) := by
        simp [Finset.sum_ite_eq', Finset.mem_univ]
      _ = ∑ a, ∑ s, ∑ r, Hinv r s * Ainv s i * (dA p a k * H a r) := by
        apply Finset.sum_congr rfl
        intro a ha
        exact Finset.sum_comm
      _ = ∑ a, ∑ s, ∑ r,
          (Ainv s i * dA p a k) * (Hinv r s * H a r) := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro s hs
        apply Finset.sum_congr rfl
        intro r hr
        ring
      _ = ∑ a, ∑ s,
          (Ainv s i * dA p a k) * (∑ r, Hinv r s * H a r) := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro s hs
        rw [Finset.mul_sum]
      _ = ∑ a, ∑ s, (Ainv s i * dA p a k) * (if a = s then 1 else 0) := by
        simp_rw [hH]
      _ = ∑ s, Ainv s i * dA p s k := by
        simp [Finset.mem_univ]
  have hsecond :
      (∑ a, ∑ b, ∑ r, ∑ s,
        Hinv r s * Ainv s i * A a k * (∑ c, A c p * dH c a b) *
          if b = r then 1 else 0) =
      ∑ s, ∑ c, ∑ a, ∑ b,
        Ainv s i * A a k * A c p * Hinv b s * dH c a b := by
    calc
      _ = ∑ a, ∑ r, ∑ s, ∑ b,
          Hinv r s * Ainv s i * A a k * (∑ c, A c p * dH c a b) *
            if b = r then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro r hr
        exact Finset.sum_comm
      _ = ∑ a, ∑ r, ∑ s,
          Hinv r s * Ainv s i * A a k * (∑ c, A c p * dH c a r) := by
        simp [Finset.sum_ite_eq', Finset.mem_univ]
      _ = ∑ a, ∑ r, ∑ s, ∑ c,
          Hinv r s * Ainv s i * A a k * A c p * dH c a r := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro r hr
        apply Finset.sum_congr rfl
        intro s hs
        apply Finset.sum_congr rfl
        intro c hc
        ring
      _ = ∑ r, ∑ s, ∑ c, ∑ a,
          Hinv r s * Ainv s i * A a k * A c p * dH c a r := by
        rw [sum_move_first_to_last4]
      _ = ∑ s, ∑ c, ∑ a, ∑ r,
          Hinv r s * Ainv s i * A a k * A c p * dH c a r := by
        rw [sum_move_first_to_last4]
      _ = ∑ s, ∑ c, ∑ a, ∑ r,
          Ainv s i * A a k * A c p * Hinv r s * dH c a r := by
        apply Finset.sum_congr rfl
        intro s hs
        apply Finset.sum_congr rfl
        intro c hc
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro r hr
        ring
  have hsecond' :
      (∑ a, ∑ b, ∑ r, ∑ s,
        Hinv r s * Ainv s i * (A a k * (∑ c, A c p * dH c a b)) *
          if b = r then 1 else 0) =
      ∑ s, ∑ c, ∑ a, ∑ b,
        Ainv s i * A a k * A c p * Hinv b s * dH c a b := by
    simpa [mul_assoc] using hsecond
  rw [hfirst, hsecond']
  simp [mul_assoc]

/-- The pointwise Chern connection-curvature identity for a smooth metric germ.
Only entrywise smoothness at `z` and an invertible metric there are required.
See Székelyhidi, §3.3, proof of Lemma 3.9, PDF p.48 (book p.45). -/
theorem chartChristoffel_bar_eq_curvature_at
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hg : ∀ a b, ContDiffAt ℝ ∞ (fun w => g w a b) z)
    (hdet : IsUnit (g z).det) (i j k q : Fin n) :
    chartPartialBarComplex
      (fun w => ∑ l, (g w)⁻¹ l i * chartPartialZComplex (fun v => g v k l) w j) z q =
      -(∑ l, (g z)⁻¹ l i * chartCurvature g z j q k l) := by
  classical
  have hi (l : Fin n) : DifferentiableAt ℝ (fun w => (g w)⁻¹ l i) z :=
    chartInv_differentiableAt (fun a b => (hg a b).of_le (by norm_num))
      ((Matrix.isUnit_iff_isUnit_det _).2 hdet) l i
  have hz (l : Fin n) :
      DifferentiableAt ℝ (fun w => chartPartialZComplex (fun v => g v k l) w j) z :=
    chartPartialZComplex_differentiableAt_at _ z (hg k l) j
  rw [chartPartialBarComplex_sum
    (fun l w => (g w)⁻¹ l i * chartPartialZComplex (fun v => g v k l) w j)
      z q (fun l => (hi l).mul (hz l))]
  simp_rw [chartPartialBarComplex_mul
    (fun w => (g w)⁻¹ _ i) (fun w => chartPartialZComplex (fun v => g v k _) w j)
      z q (hi _) (hz _)]
  simp_rw [chartPartialBarComplex_inverse_entry_at g z hg hdet _ i q]
  simp_rw [chartPartialBarComplex_chartPartialZComplex_comm_at _ z (hg k _) j q]
  have hcross :
      (∑ x : Fin n, (∑ a, ∑ b,
        (g z)⁻¹ x a * chartPartialBarComplex (fun w => g w a b) z q * (g z)⁻¹ b i) *
        chartPartialZComplex (fun v => g v k x) z j) =
      ∑ l : Fin n, (g z)⁻¹ l i * (∑ a, ∑ b,
        (g z)⁻¹ b a * chartPartialZComplex (fun v => g v k b) z j *
          chartPartialBarComplex (fun w => g w a l) z q) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [sum_swap_outer_inner (fun x a b =>
      (g z)⁻¹ x a * chartPartialBarComplex (fun w => g w a b) z q * (g z)⁻¹ b i *
        chartPartialZComplex (fun v => g v k x) z j)]
    apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    ring
  simp only [chartCurvature]
  simp only [mul_add, mul_neg, neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  linear_combination -hcross
private theorem chartChristoffel_differentiableAt_at
    (H : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (y : EuclideanSpace ℂ (Fin n))
    (hH : ∀ a b, ContDiffAt ℝ ∞ (fun w => H w a b) y)
    (hdet : IsUnit (H y).det) (i j k : Fin n) :
    DifferentiableAt ℝ
      (fun w => ∑ l, (H w)⁻¹ l i * chartPartialZComplex (fun v => H v k l) w j) y := by
  classical
  have hi (l : Fin n) : DifferentiableAt ℝ (fun w => (H w)⁻¹ l i) y :=
    chartInv_differentiableAt (fun a b => (hH a b).of_le (by norm_num))
      ((Matrix.isUnit_iff_isUnit_det _).2 hdet) l i
  have hz (l : Fin n) :
      DifferentiableAt ℝ (fun w => chartPartialZComplex (fun v => H v k l) w j) y :=
    chartPartialZComplex_differentiableAt_at _ y (hH k l) j
  exact DifferentiableAt.fun_sum (fun l hl => (hi l).mul (hz l))

private theorem chart_curvature_lowering
    (A H G : Matrix (Fin n) (Fin n) ℂ)
    (hA : IsUnit A.det) (hH : IsUnit H.det) (hG : IsUnit G.det)
    (hmetric : G = A.transpose * H * A.map star)
    (r : Fin n → ℂ) (T : Fin n → Fin n → Fin n → Fin n → ℂ)
    (p q j k : Fin n)
    (hraised : ∀ i,
      (∑ l, G⁻¹ l i * r l) =
        ∑ s, ∑ c, ∑ a, ∑ b, ∑ d,
          A⁻¹ i s * A c p * A a j * star (A b q) * H⁻¹ d s * T c b a d) :
    r k = ∑ c, ∑ b, ∑ a, ∑ d,
      A c p * star (A b q) * A a j * star (A d k) * T c b a d := by
  classical
  let t : Fin n → ℂ := fun d => ∑ c, ∑ a, ∑ b,
    A c p * A a j * star (A b q) * T c b a d
  have hvec : G⁻¹.transpose.mulVec r = A⁻¹.mulVec (H⁻¹.transpose.mulVec t) := by
    funext i
    rw [show G⁻¹.transpose.mulVec r i = ∑ l, G⁻¹ l i * r l from rfl, hraised i]
    change _ = ∑ s, A⁻¹ i s * ∑ d, H⁻¹ d s * t d
    simp only [t, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    conv_rhs => rw [sum_move_first_to_last4]
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro d hd
    ring
  have hcancelG : G.transpose * G⁻¹.transpose = 1 := by
    rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hG]
    simp
  have htransform : G.transpose * A⁻¹ * H⁻¹.transpose = A.conjTranspose := by
    rw [hmetric, Matrix.transpose_mul, Matrix.transpose_mul]
    change (A.map star).transpose * (H.transpose * A) * A⁻¹ * H⁻¹.transpose = _
    calc
      _ = (A.map star).transpose * H.transpose * (A * A⁻¹) * H⁻¹.transpose := by
        simp only [Matrix.mul_assoc]
      _ = (A.map star).transpose * (H.transpose * H⁻¹.transpose) := by
        rw [Matrix.mul_nonsing_inv _ hA]
        simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = A.conjTranspose := by
        rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hH]
        simp only [Matrix.transpose_one, Matrix.mul_one]
        rfl
  have hr : r = A.conjTranspose.mulVec t := by
    have hh := congrArg (fun v => G.transpose.mulVec v) hvec
    simp only [Matrix.mulVec_mulVec] at hh
    rw [hcancelG, Matrix.one_mulVec] at hh
    rw [← Matrix.mul_assoc, htransform] at hh
    exact hh
  rw [hr]
  change (∑ d, star (A d k) * t d) = _
  simp only [t, Finset.mul_sum]
  rw [sum_move_first_to_last4]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- Under a local holomorphic change of coordinates, curvature of the pulled-back Kähler metric
transforms as a covariant tensor of complex type `(1,1,1,1)`. Here `A` is the complex Jacobian of
`f`, and the metric relation is `g = Aᵀ (g' ∘ f) Ā`. The nonzero Jacobian determinant makes the
coordinate change locally biholomorphic at `z`. -/
theorem chartCurvature_pullback
    (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (f : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (hf : ContDiffOn ℝ ∞ f U) (hhol : DifferentiableOn ℂ f U)
    (g g' : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (hg' : ∀ j k, ContDiffOn ℝ ∞ (fun w => g' w j k) (f '' U))
    (hmetric : ∀ w ∈ U,
      g w = Matrix.transpose (EuclideanSpace.clmMatrix (fderiv ℂ f w)) *
        g' (f w) * (EuclideanSpace.clmMatrix (fderiv ℂ f w)).map star)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U)
    (hjac : IsUnit (EuclideanSpace.clmMatrix (fderiv ℂ f z)).det)
    (hgdet : IsUnit (g' (f z)).det)
    (p q j k : Fin n) :
    chartCurvature g z p q j k =
      ∑ a, ∑ b, ∑ c, ∑ d,
        (EuclideanSpace.clmMatrix (fderiv ℂ f z)) a p *
          star ((EuclideanSpace.clmMatrix (fderiv ℂ f z)) b q) *
          (EuclideanSpace.clmMatrix (fderiv ℂ f z)) c j *
          star ((EuclideanSpace.clmMatrix (fderiv ℂ f z)) d k) *
          chartCurvature g' (f z) a b c d := by
  classical
  let A := fun w => EuclideanSpace.clmMatrix (fderiv ℂ f w)
  have hAt : IsUnit (A z).transpose.det := by
    rw [Matrix.det_transpose]
    exact hjac
  have hAst : IsUnit ((A z).map star).det := by
    rw [← Matrix.det_transpose]
    change IsUnit (A z).conjTranspose.det
    rw [Matrix.det_conjTranspose]
    exact isUnit_star.mpr hjac
  have hGdet : IsUnit (g z).det := by
    rw [hmetric z hz, Matrix.det_mul, Matrix.det_mul]
    exact (hAt.mul hgdet).mul hAst
  have hG (a b : Fin n) : ContDiffAt ℝ ∞ (fun w => g w a b) z :=
    chart_pullback_metric_entry_contDiffAt U hU f hf hhol g g' hg' hmetric z hz hjac a b
  have hH (a b : Fin n) : ContDiffAt ℝ ∞ (fun w => g' w a b) (f z) :=
    (hg' a b (f z) ⟨z, hz, rfl⟩).contDiffAt
      (chart_pullback_image_nhds U hU f hf hhol z hz hjac)
  have hA (a b : Fin n) : ContDiffAt ℝ ∞ (fun w => A w a b) z :=
    chart_pullback_jacobian_entry_contDiffAt U hU f hf hhol z hz a b
  have hAdiff (a b : Fin n) : DifferentiableAt ℝ (fun w => A w a b) z :=
    (hA a b).differentiableAt (by norm_num)
  have hBdiff (a b : Fin n) : DifferentiableAt ℝ (fun w => (A w)⁻¹ a b) z :=
    chartInv_differentiableAt (fun a b => (hA a b).of_le (by norm_num))
      ((Matrix.isUnit_iff_isUnit_det _).2 hjac) a b
  have hbarA (a b : Fin n) : chartPartialBarComplex (fun w => A w a b) z q = 0 :=
    chartPartialBarComplex_jacobian_eq_zero U hU f hf hhol z hz a b q
  have hbarB (a b : Fin n) : chartPartialBarComplex (fun w => (A w)⁻¹ a b) z q = 0 := by
    rw [chartPartialBarComplex_inverse_entry_at A z hA hjac a b q]
    simp_rw [hbarA]
    simp
  have hZAdiff (a b : Fin n) :
      DifferentiableAt ℝ (fun w => chartPartialZComplex (fun v => A v a b) w p) z :=
    (chartPartialZComplex_contDiffAt _ z (hA a b) p).differentiableAt (by norm_num)
  have hbarZA (a b : Fin n) :
      chartPartialBarComplex (fun w => chartPartialZComplex (fun v => A v a b) w p) z q = 0 :=
    chartPartialBarComplex_chartPartialZComplex_jacobian_eq_zero U hU f hf hhol z hz a b p q
  let Γ := fun (s c a : Fin n) (y : EuclideanSpace ℂ (Fin n)) =>
    ∑ l, (g' y)⁻¹ l s * chartPartialZComplex (fun v => g' v a l) y c
  have hΓdiff (s c a : Fin n) : DifferentiableAt ℝ (Γ s c a) (f z) :=
    chartChristoffel_differentiableAt_at g' (f z) hH hgdet s c a
  have hfR : DifferentiableAt ℝ f z :=
    (hf.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)
  have hfC : DifferentiableAt ℂ f z := (hhol z hz).differentiableAt (hU.mem_nhds hz)
  have hΓcompdiff (s c a : Fin n) : DifferentiableAt ℝ (fun w => Γ s c a (f w)) z :=
    (hΓdiff s c a).comp z hfR
  have hbarΓ (s c a b : Fin n) : chartPartialBarComplex (Γ s c a) (f z) b =
      -(∑ d, (g' (f z))⁻¹ d s * chartCurvature g' (f z) c b a d) := by
    exact chartChristoffel_bar_eq_curvature_at g' (f z) hH hgdet s c a b
  have hbarΓcomp (s c a : Fin n) :
      chartPartialBarComplex (fun w => Γ s c a (f w)) z q =
        -(∑ b, ∑ d, star (A z b q) * (g' (f z))⁻¹ d s *
          chartCurvature g' (f z) c b a d) := by
    rw [chartPartialBar_comp_holomorphic (Γ s c a) f z q (hΓdiff s c a) hfC]
    simp_rw [hbarΓ]
    simp only [mul_neg, Finset.sum_neg_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro d hd
    ring
  have hraised (i : Fin n) :
      (∑ l, (g z)⁻¹ l i * chartCurvature g z p q j l) =
        ∑ s, ∑ c, ∑ a, ∑ b, ∑ d,
          (A z)⁻¹ i s * A z c p * A z a j * star (A z b q) *
            (g' (f z))⁻¹ d s * chartCurvature g' (f z) c b a d := by
    let D := fun (s c a : Fin n) w => (A w)⁻¹ i s * A w c p * A w a j
    have hDdiff (s c a : Fin n) : DifferentiableAt ℝ (D s c a) z :=
      ((hBdiff i s).mul (hAdiff c p)).mul (hAdiff a j)
    have hbarD (s c a : Fin n) : chartPartialBarComplex (D s c a) z q = 0 := by
      dsimp only [D]
      rw [chartPartialBarComplex_mul
        (fun w => (A w)⁻¹ i s * A w c p) (fun w => A w a j) z q
        ((hBdiff i s).mul (hAdiff c p)) (hAdiff a j)]
      rw [chartPartialBarComplex_mul
        (fun w => (A w)⁻¹ i s) (fun w => A w c p) z q (hBdiff i s) (hAdiff c p)]
      rw [hbarB, hbarA, hbarA]
      ring
    let term := fun (s c a : Fin n) w => D s c a w * Γ s c a (f w)
    have htdiff (s c a : Fin n) : DifferentiableAt ℝ (term s c a) z :=
      (hDdiff s c a).mul (hΓcompdiff s c a)
    have hbart (s c a : Fin n) : chartPartialBarComplex (term s c a) z q =
        -(D s c a z * ∑ b, ∑ d, star (A z b q) * (g' (f z))⁻¹ d s *
          chartCurvature g' (f z) c b a d) := by
      dsimp only [term]
      rw [chartPartialBarComplex_mul _ _ z q (hDdiff s c a) (hΓcompdiff s c a),
        hbarD, hbarΓcomp]
      ring
    let F := fun w => ∑ s, ∑ c, ∑ a, term s c a w
    have hFdiff : DifferentiableAt ℝ F z :=
      DifferentiableAt.fun_sum (fun s hs => DifferentiableAt.fun_sum
        (fun c hc => DifferentiableAt.fun_sum (fun a ha => htdiff s c a)))
    have hbarF : chartPartialBarComplex F z q =
        -(∑ s, ∑ c, ∑ a, ∑ b, ∑ d,
          (A z)⁻¹ i s * A z c p * A z a j * star (A z b q) *
            (g' (f z))⁻¹ d s * chartCurvature g' (f z) c b a d) := by
      dsimp only [F]
      rw [chartPartialBarComplex_sum _ z q (fun s => DifferentiableAt.fun_sum
        (fun c hc => DifferentiableAt.fun_sum (fun a ha => htdiff s c a)))]
      simp_rw [chartPartialBarComplex_sum
        (fun c w => ∑ a, term _ c a w) z q
        (fun c => DifferentiableAt.fun_sum (fun a ha => htdiff _ c a))]
      simp_rw [chartPartialBarComplex_sum (fun a w => term _ _ a w) z q
        (fun a => htdiff _ _ a)]
      simp_rw [hbart]
      simp only [Finset.sum_neg_distrib]
      congr 1
      simp only [Finset.mul_sum, D]
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro d hd
      ring
    let corr := fun (s : Fin n) w => (A w)⁻¹ i s * chartPartialZComplex (fun v => A v s j) w p
    have hcorrdiff (s : Fin n) : DifferentiableAt ℝ (corr s) z :=
      (hBdiff i s).mul (hZAdiff s j)
    have hbarcorr (s : Fin n) : chartPartialBarComplex (corr s) z q = 0 := by
      dsimp only [corr]
      rw [chartPartialBarComplex_mul _ _ z q (hBdiff i s) (hZAdiff s j),
        hbarB, hbarZA]
      ring
    let J := fun w => ∑ s, corr s w
    have hJdiff : DifferentiableAt ℝ J z :=
      DifferentiableAt.fun_sum (fun s hs => hcorrdiff s)
    have hbarJ : chartPartialBarComplex J z q = 0 := by
      rw [chartPartialBarComplex_sum _ z q hcorrdiff]
      simp_rw [hbarcorr]
      simp
    have hbaradd : chartPartialBarComplex (fun w => F w + J w) z q =
        chartPartialBarComplex F z q + chartPartialBarComplex J z q := by
      unfold chartPartialBarComplex
      rw [fderiv_fun_add hFdiff hJdiff]
      simp only [_root_.add_apply]
      ring
    have hge := chartChristoffel_pullback_eventuallyEq U hU f hf hhol g g' hg'
      hmetric z hz hjac hgdet i p j
    have hbarEq : chartPartialBarComplex
        (fun w => ∑ l, (g w)⁻¹ l i * chartPartialZComplex (fun v => g v j l) w p) z q =
        chartPartialBarComplex (fun w => F w + J w) z q := by
      unfold chartPartialBarComplex
      rw [hge.fderiv_eq]
    rw [chartChristoffel_bar_eq_curvature_at g z hG hGdet i p j q,
      hbaradd, hbarF, hbarJ, add_zero] at hbarEq
    exact neg_injective hbarEq
  exact chart_curvature_lowering (A z) (g' (f z)) (g z) hjac hgdet hGdet
    (hmetric z hz) (fun l => chartCurvature g z p q j l)
    (fun c b a d => chartCurvature g' (f z) c b a d) p q j k hraised

end KahlerForm
