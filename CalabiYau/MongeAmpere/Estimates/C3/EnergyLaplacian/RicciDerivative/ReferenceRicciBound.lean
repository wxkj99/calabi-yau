module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.Basic

/-!
# Trace the existing fixed curvature bounds to Ricci jets

Székelyhidi, §1.4, p. 12: Ricci is a metric contraction of curvature;
metric parallelism contracts its covariant derivative in the same way.
No new compactness theorem is assumed. The already proved reference
curvature and five-slot derivative bounds are explicit premises.
-/

public section

open scoped Manifold ContDiff BigOperators

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

/-- In a reference-unitary frame, tracing has n summands. Nonnegative K,A
therefore give the same finite coefficient n*(K+A) for Ricci and its first jet. -/
private theorem referenceRicci_frame_inverse {n : ℕ}
    (g : Matrix (Fin n) (Fin n) ℂ) (P : Matrix (Fin n) (Fin n) ℂ)
    (hP : P.transpose * g * P.map star = 1) :
    g⁻¹ = P.map star * P.transpose := by
  apply Matrix.inv_eq_left_inv
  have hLeft : P.map star * (P.transpose * g) = 1 := by
    exact mul_eq_one_comm.mp (by simpa only [Matrix.mul_assoc] using hP)
  simpa only [Matrix.mul_assoc] using hLeft

private theorem referenceRicci_frame_trace {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₀ : KahlerForm n M) (x : M)
    (P : Matrix (Fin n) (Fin n) ℂ)
    (hP : referenceOrthonormalFrameMatrix ω₀ x P) (j l : Fin n) :
    c3TwoCovariantFrame P
      (c3RicciInChart (ω₀.metricInChart x)
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x)) j l =
      ∑ s, referenceCurvatureComponent ω₀ x P s s j l := by
  have hInv : (ω₀.metricInChart x
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x))⁻¹ = P.map star * P.transpose :=
    referenceRicci_frame_inverse _ P hP
  simp only [c3TwoCovariantFrame, c3RicciInChart, referenceCurvatureComponent]
  rw [hInv]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_lhs =>
    arg 2; intro a; arg 2; intro b; arg 2; intro c; rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; intro a; arg 2; intro b; rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; intro a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; intro a; arg 2; intro b; rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; intro a; rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; intro a; arg 2; intro b; arg 2; intro c; rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; intro a; arg 2; intro b; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x1 hx1
  apply Finset.sum_congr rfl
  intro x2 hx2
  apply Finset.sum_congr rfl
  intro x3 hx3
  apply Finset.sum_congr rfl
  intro x4 hx4
  apply Finset.sum_congr rfl
  intro x5 hx5
  ring

private theorem referenceRicci_chartPartialZ_mul {n : ℕ}
    (F G : EuclideanSpace ℂ (Fin n) → ℂ) (z : EuclideanSpace ℂ (Fin n))
    (q : Fin n) (hF : DifferentiableAt ℝ F z) (hG : DifferentiableAt ℝ G z) :
    chartPartialZComplex (fun w => F w * G w) z q =
      chartPartialZComplex F z q * G z + F z * chartPartialZComplex G z q := by
  unfold chartPartialZComplex
  rw [fderiv_fun_mul hF hG]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

private theorem referenceRicci_chartPartialZ_sum {n : ℕ}
    {ι : Type*} [Fintype ι] (F : ι → EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n)
    (hF : ∀ i, DifferentiableAt ℝ (F i) z) :
    chartPartialZComplex (fun w => ∑ i, F i w) z j =
      ∑ i, chartPartialZComplex (F i) z j := by
  unfold chartPartialZComplex
  have hfd : fderiv ℝ (fun w => ∑ i, F i w) z = ∑ i, fderiv ℝ (F i) z := by
    simpa using fderiv_fun_sum (u := Finset.univ) (fun i hi => hF i)
  rw [hfd]
  simp only [sum_apply]
  have hsum :
      (∑ i, fderiv ℝ (F i) z (EuclideanSpace.single j 1)) -
        Complex.I * ∑ i, fderiv ℝ (F i) z (Complex.I • EuclideanSpace.single j 1) =
      ∑ i, (fderiv ℝ (F i) z (EuclideanSpace.single j 1) -
        Complex.I * fderiv ℝ (F i) z (Complex.I • EuclideanSpace.single j 1)) := by
    rw [Finset.mul_sum, Finset.sum_sub_distrib]
  rw [hsum]
  simp only [div_eq_mul_inv, Finset.sum_mul]

private theorem referenceRicci_chartPartialZ_inverse_entry {n : ℕ}
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hg : ∀ a b, ContDiffAt ℝ ∞ (fun w => g w a b) z)
    (hdet : IsUnit (g z).det)
    (i j q : Fin n) :
    chartPartialZComplex (fun w => (g w)⁻¹ i j) z q =
      -(∑ a, ∑ b, (g z)⁻¹ i a * chartPartialZComplex (fun w => g w a b) z q *
        (g z)⁻¹ b j) := by
  classical
  have he (a b : Fin n) : DifferentiableAt ℝ (fun w => g w a b) z :=
    (hg a b).differentiableAt (by norm_num)
  have hi (a b : Fin n) : DifferentiableAt ℝ (fun w => (g w)⁻¹ a b) z :=
    chartInv_differentiableAt (fun a b => (hg a b).of_le (by norm_num))
      ((Matrix.isUnit_iff_isUnit_det _).2 hdet) a b
  have hd : ContinuousAt (fun w => (g w).det) z := by
    have hdc : ContDiffAt ℝ ∞ (fun w => (g w).det) z := by
      simp_rw [Matrix.det_apply]
      fun_prop (disch := assumption)
    exact hdc.continuousAt
  have hne : ∀ᶠ w in nhds z, (g w).det ≠ 0 := hd.eventually_ne hdet.ne_zero
  have hu : ∀ᶠ w in nhds z, IsUnit (g w).det := by
    filter_upwards [hne] with w hw
    exact isUnit_iff_ne_zero.mpr hw
  have hprod (a b : Fin n) :
      (fun w => ∑ t : Fin n, (g w)⁻¹ a t * g w t b) =ᶠ[nhds z]
        (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) a b) := by
    filter_upwards [hu] with w hw
    simpa only [Matrix.mul_apply] using congrArg
      (fun M : Matrix (Fin n) (Fin n) ℂ => M a b)
      (Matrix.nonsing_inv_mul (g w) hw)
  have hzero (a b : Fin n) :
      chartPartialZComplex (fun w => ∑ t : Fin n, (g w)⁻¹ a t * g w t b) z q = 0 := by
    unfold chartPartialZComplex
    rw [hprod a b |>.fderiv_eq]
    simp
  have hrel (a b : Fin n) :
      (∑ t : Fin n, chartPartialZComplex (fun w => (g w)⁻¹ a t) z q * g z t b) +
      (∑ t : Fin n, (g z)⁻¹ a t * chartPartialZComplex (fun w => g w t b) z q) = 0 := by
    have hh := hzero a b
    rw [referenceRicci_chartPartialZ_sum
      (fun t w => (g w)⁻¹ a t * g w t b) z q
      (fun t => (hi a t).mul (he t b))] at hh
    simp_rw [referenceRicci_chartPartialZ_mul _ _ z q (hi a _) (he _ b)] at hh
    rwa [Finset.sum_add_distrib] at hh
  let D : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun a b =>
    chartPartialZComplex (fun w => (g w)⁻¹ a b) z q)
  let H : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun a b =>
    chartPartialZComplex (fun w => g w a b) z q)
  have hmat : D * g z = -((g z)⁻¹ * H) := by
    ext a b
    simp only [D, H, Matrix.mul_apply, Matrix.of_apply, Matrix.neg_apply]
    exact (eq_neg_iff_add_eq_zero).2 (hrel a b)
  have hresult : D = -((g z)⁻¹ * H * (g z)⁻¹) := by
    calc
      D = D * 1 := by simp
      _ = D * (g z * (g z)⁻¹) := by rw [Matrix.mul_nonsing_inv (g z) hdet]
      _ = (D * g z) * (g z)⁻¹ := by rw [Matrix.mul_assoc]
      _ = -((g z)⁻¹ * H * (g z)⁻¹) := by rw [hmat]; simp [Matrix.mul_assoc]
  have hentry := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) hresult
  simp only [D, H, Matrix.of_apply, Matrix.neg_apply, Matrix.mul_apply, Finset.sum_mul] at hentry
  rw [Finset.sum_comm]
  exact hentry

omit [T2Space M] [CompactSpace M] in
private theorem referenceRicci_coordinate_trace
    (ω₀ : KahlerForm n M) (x : M) (z : EuclideanSpace ℂ (Fin n))
    (hG : ∀ a b, ContDiffAt ℝ ∞ (fun w => ω₀.metricInChart x w a b) z)
    (hdet : IsUnit (ω₀.metricInChart x z).det)
    (hcurv : ∀ p q j l, DifferentiableAt ℝ
      (fun w => chartCurvature (ω₀.metricInChart x) w p q j l) z)
    (k j l : Fin n) :
    c3ReferenceCovariantTwoTensorZ ω₀ x
        (c3RicciInChart (ω₀.metricInChart x)) z k j l =
      ∑ p, ∑ q, (ω₀.metricInChart x z)⁻¹ q p *
        c3ReferenceCurvatureCovariantDerivativeInChart ω₀ x z k p q j l := by
  let g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w => ω₀.metricInChart x w
  have hinvDiff (a b : Fin n) : DifferentiableAt ℝ (fun w => (g w)⁻¹ a b) z :=
    chartInv_differentiableAt (fun a b => (hG a b).of_le (by norm_num))
      ((Matrix.isUnit_iff_isUnit_det _).2 hdet) a b
  have htermDiff (p q : Fin n) : DifferentiableAt ℝ
      (fun w => (g w)⁻¹ q p * chartCurvature g w p q j l) z :=
    (hinvDiff q p).mul (hcurv p q j l)
  have hinnerDiff (p : Fin n) : DifferentiableAt ℝ
      (fun w => ∑ q, (g w)⁻¹ q p * chartCurvature g w p q j l) z :=
    DifferentiableAt.fun_sum (u := Finset.univ) (fun q _ => htermDiff p q)
  have hRicciDeriv :
      c3PartialZ (fun w => ∑ p, ∑ q,
        (g w)⁻¹ q p * chartCurvature g w p q j l) z k =
      ∑ p, ∑ q,
        (c3PartialZ (fun w => (g w)⁻¹ q p) z k * chartCurvature g z p q j l +
          (g z)⁻¹ q p * c3PartialZ (fun w => chartCurvature g w p q j l) z k) := by
    change chartPartialZComplex (fun w => ∑ p, ∑ q,
      (g w)⁻¹ q p * chartCurvature g w p q j l) z k = _
    rw [referenceRicci_chartPartialZ_sum (fun p w =>
      ∑ q, (g w)⁻¹ q p * chartCurvature g w p q j l) z k hinnerDiff]
    apply Finset.sum_congr rfl
    intro p hp
    rw [referenceRicci_chartPartialZ_sum (fun q w =>
      (g w)⁻¹ q p * chartCurvature g w p q j l) z k (htermDiff p)]
    apply Finset.sum_congr rfl
    intro q hq
    exact referenceRicci_chartPartialZ_mul _ _ z k (hinvDiff q p) (hcurv p q j l)
  have hInvGamma (q p : Fin n) :
      c3PartialZ (fun w => (g w)⁻¹ q p) z k =
        -∑ a, (g z)⁻¹ q a * c3ChristoffelInChart g z p k a := by
    have hInv (q p : Fin n) :
        c3PartialZ (fun w => (g w)⁻¹ q p) z k =
          -∑ a, ∑ b, (g z)⁻¹ q a * c3PartialZ (fun w => g w a b) z k *
            (g z)⁻¹ b p := by
      simpa [c3PartialZ, chartPartialZComplex] using
        referenceRicci_chartPartialZ_inverse_entry g z hG hdet q p k
    rw [hInv]
    simp only [c3ChristoffelInChart, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    ring
  have hsum3 (F : Fin n → Fin n → Fin n → ℂ) :
      (∑ r, ∑ q, ∑ p, F r q p) = ∑ p, ∑ q, ∑ r, F r q p := by
    conv_lhs =>
      arg 2
      intro r
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    conv_lhs =>
      arg 2
      intro p
      rw [Finset.sum_comm]
  have hsum3' (F : Fin n → Fin n → Fin n → ℂ) :
      (∑ r, ∑ p, ∑ q, F r p q) = ∑ p, ∑ q, ∑ r, F r p q := by
    conv_lhs =>
      arg 2
      intro r
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    conv_lhs =>
      arg 2
      intro q
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  have htraceInv :
      (∑ p, ∑ q, c3PartialZ (fun w => (g w)⁻¹ q p) z k * chartCurvature g z p q j l) =
        -(∑ p, ∑ q, ∑ r,
          (g z)⁻¹ q p * c3ChristoffelInChart g z r k p * chartCurvature g z r q j l) := by
    simp_rw [hInvGamma]
    simp only [Finset.sum_mul, neg_mul, Finset.sum_neg_distrib]
    rw [hsum3 (fun r q p => (g z)⁻¹ q p * c3ChristoffelInChart g z r k p *
      chartCurvature g z r q j l)]
  have htraceMetric :
      (∑ r, c3ChristoffelInChart g z r k j *
        ∑ p, ∑ q, (g z)⁻¹ q p * chartCurvature g z p q r l) =
      ∑ p, ∑ q, (g z)⁻¹ q p *
        ∑ r, c3ChristoffelInChart g z r k j * chartCurvature g z p q r l := by
    simp only [Finset.mul_sum]
    rw [hsum3' (fun r p q => c3ChristoffelInChart g z r k j *
      ((g z)⁻¹ q p * chartCurvature g z p q r l))]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro r hr
    ring
  simp only [c3ReferenceCovariantTwoTensorZ, c3RicciInChart,
    c3ReferenceCurvatureCovariantDerivativeInChart]
  rw [hRicciDeriv]
  simp only [Finset.sum_add_distrib]
  rw [htraceInv, htraceMetric]
  simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  dsimp [g]
  ring_nf

omit [T2Space M] [CompactSpace M] in
private theorem referenceRicci_covariantDerivative_frame_trace
    (ω₀ : KahlerForm n M) (x : M) (P : Matrix (Fin n) (Fin n) ℂ)
    (hP : P.transpose * ω₀.metricInChart x
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) * P.map star = 1)
    (k j l : Fin n) :
    c3ThreeCovariantFrame P
      (c3ReferenceCovariantTwoTensorZ ω₀ x
        (c3RicciInChart (ω₀.metricInChart x))
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x)) k j l =
      ∑ s, ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
        P a k * P b s * star (P c s) * P d j * star (P e l) *
          c3ReferenceCurvatureCovariantDerivativeInChart ω₀ x
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) a b c d e := by
  let z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x
  let g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w => ω₀.metricInChart x w
  have hP' : P.transpose * g z * P.map star = 1 := by
    simpa [g, z] using hP
  have hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
    simp [z]
  have hG (a b : Fin n) : ContDiffAt ℝ ∞ (fun w => g w a b) z := by
    exact (ω₀.contDiffOn_metricInChart x a b).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz)
  have hdet : IsUnit (g z).det := by
    have hleft : (P.map star * P.transpose) * g z = 1 := by
      have h' : P.map star * (P.transpose * g z) = 1 :=
        mul_eq_one_comm.mp (by simpa only [Matrix.mul_assoc] using hP')
      simpa only [Matrix.mul_assoc] using h'
    have hdetne : (g z).det ≠ 0 := by
      have heq : (P.map star * P.transpose).det * (g z).det = 1 := by
        have := congrArg Matrix.det hleft
        simpa only [Matrix.det_mul, Matrix.det_one] using this
      intro hz0
      rw [hz0, mul_zero] at heq
      norm_num at heq
    exact isUnit_iff_ne_zero.mpr hdetne
  have hbar (a b q : Fin n) : ContDiffAt ℝ ∞
      (fun w => chartPartialBarComplex (fun v => g v a b) w q) z := by
    have hfd : ContDiffAt ℝ ∞ (fderiv ℝ (fun v => g v a b)) z :=
      (hG a b).fderiv_right (by simp)
    unfold chartPartialBarComplex
    fun_prop (disch := assumption)
  have hZ (a b p : Fin n) : ContDiffAt ℝ ∞
      (fun w => chartPartialZComplex (fun v => g v a b) w p) z := by
    have hfd : ContDiffAt ℝ ∞ (fderiv ℝ (fun v => g v a b)) z :=
      (hG a b).fderiv_right (by simp)
    unfold chartPartialZComplex
    fun_prop (disch := assumption)
  have hZbar (a b q p : Fin n) : DifferentiableAt ℝ
      (fun w => chartPartialZComplex (fun v => chartPartialBarComplex
        (fun u => g u a b) v q) w p) z := by
    have hfd : DifferentiableAt ℝ (fderiv ℝ
        (fun v => chartPartialBarComplex (fun u => g u a b) v q)) z :=
      ((hbar a b q).fderiv_right (m := ∞)
        (le_of_eq (show (∞ : ℕ∞ω) = ∞ + 1 from rfl).symm)).differentiableAt (by norm_num)
    have he : DifferentiableAt ℝ (fun w => fderiv ℝ
        (fun v => chartPartialBarComplex (fun u => g u a b) v q) w (EuclideanSpace.single p 1)) z :=
      hfd.clm_apply (differentiableAt_const _)
    have hie : DifferentiableAt ℝ (fun w => fderiv ℝ
        (fun v => chartPartialBarComplex (fun u => g u a b) v q) w
          (Complex.I • EuclideanSpace.single p 1)) z :=
      hfd.clm_apply (differentiableAt_const _)
    unfold chartPartialZComplex
    fun_prop (disch := assumption)
  have hInvDiff (a b : Fin n) : DifferentiableAt ℝ (fun w => (g w)⁻¹ a b) z :=
    chartInv_differentiableAt (fun a b => (hG a b).of_le (by norm_num))
      ((Matrix.isUnit_iff_isUnit_det _).2 hdet) a b
  have hcurv (p q a b : Fin n) : DifferentiableAt ℝ
      (fun w => chartCurvature g w p q a b) z := by
    unfold chartCurvature
    apply (hZbar a b q p).neg.add
    apply DifferentiableAt.fun_sum
    intro c hc
    apply DifferentiableAt.fun_sum
    intro d hd
    exact ((hInvDiff d c).mul
      ((hZ a d p).differentiableAt (by norm_num))).mul
      ((hbar c b q).differentiableAt (by norm_num))
  have hcoord (a b c : Fin n) :=
    referenceRicci_coordinate_trace ω₀ x z hG hdet hcurv a b c
  have hinv : (g z)⁻¹ = P.map star * P.transpose := by
    have h' : P.map star * (P.transpose * g z) = 1 :=
      mul_eq_one_comm.mp (by simpa only [Matrix.mul_assoc] using hP')
    have hleft : (P.map star * P.transpose) * g z = 1 := by
      simpa only [Matrix.mul_assoc] using h'
    exact Matrix.inv_eq_left_inv hleft
  simp only [c3ThreeCovariantFrame]
  conv_lhs =>
    arg 2
    intro a
    arg 2
    intro b
    arg 2
    intro c
    rw [hcoord a b c]
  simp only [c3ReferenceCurvatureCovariantDerivativeInChart]
  rw [hinv]
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply]
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_lhs =>
    arg 2; intro x1; arg 2; intro x2; arg 2; intro x3; arg 2; intro x4
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; intro x1; arg 2; intro x2; arg 2; intro x3
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; intro x1; arg 2; intro x2
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; intro x1
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; intro i; arg 2; intro x1; arg 2; intro x2
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; intro i; arg 2; intro x1
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; intro i; arg 2; intro x1; arg 2; intro x4; arg 2; intro x2
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; intro i; arg 2; intro x1; arg 2; intro x4
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro x1 hx1
  apply Finset.sum_congr rfl
  intro x4 hx4
  apply Finset.sum_congr rfl
  intro x5 hx5
  apply Finset.sum_congr rfl
  intro x2 hx2
  apply Finset.sum_congr rfl
  intro x3 hx3
  dsimp [z, g]
  ring

omit [T2Space M] [CompactSpace M] in
theorem c3ReferenceRicciFrameBound_of_curvature (ω₀ : KahlerForm n M)
    (K A : ℝ) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hCurv : ∀ x P, referenceOrthonormalFrameMatrix ω₀ x P → ∀ p q j k,
      ‖referenceCurvatureComponent ω₀ x P p q j k‖ ≤ K)
    (hDeriv : ∀ (x : M) (P : Matrix (Fin n) (Fin n) ℂ),
      P.transpose * ω₀.metricInChart x
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) * P.map star = 1 →
        ∀ s p q j k : Fin n,
          ‖∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
            P a s * P b p * star (P c q) * P d j * star (P e k) *
              c3ReferenceCurvatureCovariantDerivativeInChart ω₀ x
                (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) a b c d e‖ ≤ A) :
    ∀ x P, referenceOrthonormalFrameMatrix ω₀ x P →
      c3ReferenceRicciFrameBound ω₀ x
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) P ((n : ℝ) * (K + A)) := by
  intro x P hP
  constructor
  · intro j l
    rw [referenceRicci_frame_trace ω₀ x P hP j l]
    calc
      ‖∑ s, referenceCurvatureComponent ω₀ x P s s j l‖ ≤
          ∑ s, ‖referenceCurvatureComponent ω₀ x P s s j l‖ := norm_sum_le _ _
      _ ≤ ∑ _s : Fin n, K := Finset.sum_le_sum fun s _hs => hCurv x P hP s s j l
      _ = (n : ℝ) * K := by simp
      _ ≤ (n : ℝ) * (K + A) := by
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith [hn, hA]
  · intro k j l
    rw [referenceRicci_covariantDerivative_frame_trace ω₀ x P hP k j l]
    calc
      ‖∑ s, ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
          P a k * P b s * star (P c s) * P d j * star (P e l) *
            c3ReferenceCurvatureCovariantDerivativeInChart ω₀ x
              (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) a b c d e‖ ≤
          ∑ s, ‖∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
            P a k * P b s * star (P c s) * P d j * star (P e l) *
              c3ReferenceCurvatureCovariantDerivativeInChart ω₀ x
                (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) a b c d e‖ := norm_sum_le _ _
      _ ≤ ∑ _s : Fin n, A := Finset.sum_le_sum fun s _hs => hDeriv x P hP k s s j l
      _ = (n : ℝ) * A := by simp
      _ ≤ (n : ℝ) * (K + A) := by
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith [hn, hK]

end KahlerForm
