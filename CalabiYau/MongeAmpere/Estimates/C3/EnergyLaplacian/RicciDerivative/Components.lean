module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.Basic
import CalabiYau.MongeAmpere.Estimates.C2.LogDetHessianJet.FirstJet

/-!
# Curvature-contracted Ricci components

Székelyhidi, §1.4, Lemma 1.22 and its proof, printed p. 12:
contracting the Kähler curvature gives the negative logarithmic Hessian.
The assertion is componentwise, not merely a trace against the background.
-/

public section

open scoped Manifold ContDiff

namespace KahlerForm

open scoped BigOperators
open Filter Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

private theorem chartPartialZComplex_sum_at {n : ℕ} {ι : Type*} [Fintype ι]
    (F : ι → EuclideanSpace ℂ (Fin n) → ℂ) (z : EuclideanSpace ℂ (Fin n)) (p : Fin n)
    (hF : ∀ i, DifferentiableAt ℝ (F i) z) :
    chartPartialZComplex (fun w ↦ ∑ i, F i w) z p = ∑ i, chartPartialZComplex (F i) z p := by
  unfold chartPartialZComplex
  have hfd : fderiv ℝ (fun w ↦ ∑ i, F i w) z = ∑ i, fderiv ℝ (F i) z := by
    simpa using fderiv_fun_sum (u := Finset.univ) (fun i hi ↦ hF i)
  rw [hfd]
  simp only [sum_apply, div_eq_mul_inv]
  conv_rhs => rw [← Finset.sum_mul]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]

/-- Reindex the product part of the mixed logarithmic determinant Hessian using
Kähler symmetry in the two derivative slots. -/
private theorem curvature_quadratic_reindex {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ)
    (X Y : Fin n → Fin n → Fin n → ℂ)
    (hX : ∀ p j b, X p j b = X j p b)
    (hY : ∀ q a l, Y q a l = Y l a q)
    (j l : Fin n) :
    (∑ p, ∑ q, ∑ a, ∑ b, H q p * H b a * X p j b * Y q a l) =
      (∑ r, ∑ s, ∑ a, ∑ b, H r a * X a j b * H b s * Y l s r) := by
  classical
  calc
    _ = ∑ q, ∑ p, ∑ a, ∑ b, H q p * H b a * X p j b * Y q a l := by
      exact Finset.sum_comm
    _ = ∑ q, ∑ a, ∑ p, ∑ b, H q p * H b a * X p j b * Y q a l := by
      apply Finset.sum_congr rfl
      intro q hq
      exact Finset.sum_comm
    _ = ∑ q, ∑ a, ∑ p, ∑ b, H q p * H b a * X j p b * Y l a q := by
      simp_rw [hX, hY]
    _ = ∑ r, ∑ s, ∑ a, ∑ b, H r a * X a j b * H b s * Y l s r := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [← hX a j b]
      ring

/-- Differentiate a barred inverse-trace germ in an independent coordinate direction. -/
private theorem log_det_mixed_inverse_trace_jet_two {n : ℕ}
    {G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    {f : EuclideanSpace ℂ (Fin n) → ℂ} {z : EuclideanSpace ℂ (Fin n)}
    (p q : Fin n)
    (hG : ∀ j k, ContDiffAt ℝ 1 (fun w ↦ G w j k) z)
    (hunit : IsUnit (G z))
    (hB : ∀ j k, DifferentiableAt ℝ
      (fun w ↦ chartPartialBarComplex (fun v ↦ G v j k) w q) z)
    (hfirst : ∀ᶠ w in 𝓝 z,
      chartPartialBarComplex f w q = Matrix.trace ((G w)⁻¹ * Matrix.of (fun j k ↦
        chartPartialBarComplex (fun v ↦ G v j k) w q))) :
    chartPartialZComplex (fun w ↦ chartPartialBarComplex f w q) z p =
      Matrix.trace ((G z)⁻¹ * Matrix.of (fun j k ↦
        chartPartialZComplex
          (fun w ↦ chartPartialBarComplex (fun v ↦ G v j k) w q) z p)) -
      Matrix.trace ((G z)⁻¹ * Matrix.of (fun j k ↦
        chartPartialZComplex (fun w ↦ G w j k) z p) * (G z)⁻¹ *
        Matrix.of (fun j k ↦ chartPartialBarComplex (fun w ↦ G w j k) z q)) := by
  classical
  let B : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ := fun w =>
    Matrix.of (fun j k ↦ chartPartialBarComplex (fun v ↦ G v j k) w q)
  let T : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun j k ↦
    chartPartialZComplex (fun w ↦ G w j k) z p)
  let H : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun j k ↦
    chartPartialZComplex (fun w ↦ chartPartialBarComplex (fun v ↦ G v j k) w q) z p)
  let D : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun j k ↦
    chartPartialZComplex (fun w ↦ (G w)⁻¹ j k) z p)
  have hInv (j k : Fin n) : DifferentiableAt ℝ (fun w ↦ (G w)⁻¹ j k) z :=
    chartInv_differentiableAt hG hunit j k
  have hdet : IsUnit (G z).det := (Matrix.isUnit_iff_isUnit_det _).mp hunit
  have hdetCont : ContinuousAt (fun w ↦ (G w).det) z := by
    have hcont : ContDiffAt ℝ 1 (fun w ↦ (G w).det) z := by
      simp_rw [Matrix.det_apply]
      fun_prop (disch := assumption)
    exact hcont.continuousAt
  have hdetEvent : ∀ᶠ w in 𝓝 z, (G w).det ≠ 0 :=
    hdetCont.eventually_ne hdet.ne_zero
  have hunitEvent : ∀ᶠ w in 𝓝 z, IsUnit (G w) := by
    filter_upwards [hdetEvent] with w hw
    exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hw)
  have hinvprod (a b : Fin n) :
      (fun w ↦ ∑ l : Fin n, G w a l * (G w)⁻¹ l b) =ᶠ[𝓝 z]
        fun _ ↦ (1 : Matrix (Fin n) (Fin n) ℂ) a b := by
    filter_upwards [hunitEvent] with w hw
    simpa only [Matrix.mul_apply] using congrArg (fun M : Matrix (Fin n) (Fin n) ℂ ↦ M a b)
      (Matrix.mul_nonsing_inv (G w) ((Matrix.isUnit_iff_isUnit_det _).mp hw))
  have hentryprod (a b l : Fin n) : DifferentiableAt ℝ
      (fun w ↦ G w a l * (G w)⁻¹ l b) z := by
    exact (hG a l).differentiableAt (by norm_num) |>.mul (hInv l b)
  have hInvDeriv (a b : Fin n) : chartPartialZComplex
      (fun w ↦ ∑ l : Fin n, G w a l * (G w)⁻¹ l b) z p = 0 := by
    have hfd := (hinvprod a b).fderiv_eq (𝕜 := ℝ) (x := z)
    unfold chartPartialZComplex
    rw [hfd]
    simp
  have hInvDerivSum (a b : Fin n) :
      ∑ l : Fin n,
        (chartPartialZComplex (fun w ↦ G w a l) z p * (G z)⁻¹ l b +
          G z a l * chartPartialZComplex (fun w ↦ (G w)⁻¹ l b) z p) = 0 := by
    have h := hInvDeriv a b
    rw [chartPartialZComplex_sum_at (fun l w ↦ G w a l * (G w)⁻¹ l b) z p
      (fun l ↦ hentryprod a b l)] at h
    simp_rw [chartPartialZComplex_mul ((hG a _).differentiableAt (by norm_num))
      (hInv _ _) p] at h
    exact h
  have hGD : G z * D = -(T * (G z)⁻¹) := by
    ext a b
    simp only [D, T, Matrix.mul_apply, Matrix.of_apply, Matrix.neg_apply]
    have h := hInvDerivSum a b
    simp only [Finset.sum_add_distrib] at h
    linear_combination h
  have hleft : (G z)⁻¹ * G z = 1 := Matrix.nonsing_inv_mul (G z) hdet
  have hD : D = -((G z)⁻¹ * T * (G z)⁻¹) := by
    calc
      D = 1 * D := by simp
      _ = ((G z)⁻¹ * G z) * D := by rw [hleft]
      _ = (G z)⁻¹ * (G z * D) := by rw [Matrix.mul_assoc]
      _ = (G z)⁻¹ * (-(T * (G z)⁻¹)) := by rw [hGD]
      _ = -((G z)⁻¹ * T * (G z)⁻¹) := by simp [Matrix.mul_assoc]
  have htracefun : (fun w ↦ Matrix.trace ((G w)⁻¹ * B w)) =
      fun w ↦ ∑ j : Fin n, ∑ k : Fin n, (G w)⁻¹ j k * B w k j := by
    funext w
    simp [B, Matrix.trace, Matrix.mul_apply]
  have hprod (j k : Fin n) : DifferentiableAt ℝ
      (fun w ↦ (G w)⁻¹ j k * B w k j) z := by
    exact (hInv j k).mul (hB k j)
  have hderivTrace : chartPartialZComplex (fun w ↦ Matrix.trace ((G w)⁻¹ * B w)) z p =
      Matrix.trace (D * B z) + Matrix.trace ((G z)⁻¹ * H) := by
    calc
      _ = chartPartialZComplex
          (fun w ↦ ∑ j : Fin n, ∑ k : Fin n, (G w)⁻¹ j k * B w k j) z p := by
            rw [htracefun]
      _ = ∑ j : Fin n, chartPartialZComplex
          (fun w ↦ ∑ k : Fin n, (G w)⁻¹ j k * B w k j) z p :=
            chartPartialZComplex_sum_at _ z p (fun j ↦ DifferentiableAt.fun_sum
              (fun k hk ↦ hprod j k))
      _ = ∑ j : Fin n, ∑ k : Fin n,
          chartPartialZComplex (fun w ↦ (G w)⁻¹ j k * B w k j) z p := by
            apply Finset.sum_congr rfl
            intro j hj
            exact chartPartialZComplex_sum_at _ z p (fun k ↦ hprod j k)
      _ = ∑ j : Fin n, ∑ k : Fin n,
          (chartPartialZComplex (fun w ↦ (G w)⁻¹ j k) z p * B z k j +
            (G z)⁻¹ j k * chartPartialZComplex (fun w ↦ B w k j) z p) := by
            apply Finset.sum_congr rfl
            intro j hj
            apply Finset.sum_congr rfl
            intro k hk
            exact chartPartialZComplex_mul (hInv j k) (hB k j) p
      _ = Matrix.trace (D * B z) + Matrix.trace ((G z)⁻¹ * H) := by
            simp [D, H, B, Matrix.trace, Matrix.mul_apply, Matrix.of_apply,
              Finset.sum_add_distrib]
  have htraceGerm : (fun w ↦ chartPartialBarComplex f w q) =ᶠ[𝓝 z]
      fun w ↦ Matrix.trace ((G w)⁻¹ * B w) := by
    filter_upwards [hfirst] with w hw
    simpa [B] using hw
  have hfirstZ := htraceGerm.fderiv_eq (𝕜 := ℝ) (x := z)
  have hZeq : chartPartialZComplex (fun w ↦ chartPartialBarComplex f w q) z p =
      chartPartialZComplex (fun w ↦ Matrix.trace ((G w)⁻¹ * B w)) z p := by
    unfold chartPartialZComplex
    rw [hfirstZ]
  rw [hZeq, hderivTrace]
  have hquad : Matrix.trace (D * B z) =
      -Matrix.trace ((G z)⁻¹ * T * (G z)⁻¹ * B z) := by
    rw [hD]
    simp [Matrix.mul_assoc]
  rw [hquad]
  simp only [B, H, T, Matrix.mul_assoc]
  ring

/-- The mixed logarithmic-determinant Hessian follows from the imported barred first jet and
its differentiated inverse-trace identity. -/
private theorem c3_log_det_mixed_inverse_trace_jet {n : ℕ}
    {G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    {z : EuclideanSpace ℂ (Fin n)}
    (p q : Fin n)
    (hG : ∀ j k, ContDiffAt ℝ 1 (fun w ↦ G w j k) z)
    (hunit : IsUnit (G z))
    (hHerm : ∀ᶠ w in 𝓝 z, (G w).IsHermitian)
    (hpos : 0 < (G z).det.re)
    (hB : ∀ j k, DifferentiableAt ℝ
      (fun w ↦ chartPartialBarComplex (fun v ↦ G v j k) w q) z) :
    chartPartialZComplex
        (fun w ↦ chartPartialBarComplex (fun v ↦ (Real.log ((G v).det.re) : ℂ)) w q) z p =
      Matrix.trace ((G z)⁻¹ * Matrix.of (fun j k ↦
        chartPartialZComplex
          (fun w ↦ chartPartialBarComplex (fun v ↦ G v j k) w q) z p)) -
      Matrix.trace ((G z)⁻¹ * Matrix.of (fun j k ↦
        chartPartialZComplex (fun w ↦ G w j k) z p) * (G z)⁻¹ *
        Matrix.of (fun j k ↦ chartPartialBarComplex (fun w ↦ G w j k) z q)) := by
  have hfirst := log_det_bar_first_jet_eventually G z q hG hHerm hpos
  exact log_det_mixed_inverse_trace_jet_two p q hG hunit hB hfirst

private theorem chartPartialBarComplex_star_eq_chartPartialZComplex {n : ℕ}
    {f : EuclideanSpace ℂ (Fin n) → ℂ} {z : EuclideanSpace ℂ (Fin n)}
    (hf : DifferentiableAt ℝ f z) (q : Fin n) :
    chartPartialBarComplex (fun w ↦ star (f w)) z q =
      star (chartPartialZComplex f z q) := by
  have hstar (v : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ star (f w)) z v = star (fderiv ℝ f z v) := by
    have h := fderiv_comp (f := f) (g := fun u : ℂ ↦ Complex.conjCLE u)
      (x := z) (by fun_prop) hf
    have h' : fderiv ℝ (fun w ↦ star (f w)) z =
        Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ f z) := by
      have hc : fderiv ℝ (fun u : ℂ ↦ Complex.conjCLE u) (f z) =
          Complex.conjCLE.toContinuousLinearMap :=
        Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.fderiv
      rw [hc] at h
      simpa [Function.comp_def] using h
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun L => L v) h'
  unfold chartPartialBarComplex chartPartialZComplex
  rw [hstar (EuclideanSpace.single q 1), hstar (Complex.I • EuclideanSpace.single q 1)]
  apply Complex.ext <;> simp [div_eq_mul_inv]

open scoped ComplexOrder

private noncomputable def q3ChartWirtinger {n : ℕ}
    (s : ℂ) (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n) : ℂ :=
  (fderiv ℝ F z (EuclideanSpace.single j 1) +
    s * fderiv ℝ F z (Complex.I • EuclideanSpace.single j 1)) / 2

private theorem q3ChartWirtinger_fderiv_at {n : ℕ} (s : ℂ)
    (F : EuclideanSpace ℂ (Fin n) → ℂ) (z : EuclideanSpace ℂ (Fin n))
    (hF : ContDiffAt ℝ ∞ F z) (j : Fin n)
    (v : EuclideanSpace ℂ (Fin n)) :
    fderiv ℝ (fun w => q3ChartWirtinger s F w j) z v =
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
  have hfun : (fun w => q3ChartWirtinger s F w j) =
      fun w => (2 : ℂ)⁻¹ * (fderiv ℝ F w e + s * fderiv ℝ F w (Complex.I • e)) := by
    funext w
    simp only [q3ChartWirtinger, e, div_eq_mul_inv]
    ring
  rw [hfun, fderiv_const_mul hsum, fderiv_fun_add he (hie.const_mul s),
    fderiv_const_mul hie]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [h_e v, h_ie v]
  simp only [div_eq_mul_inv]
  ring

private theorem q3ChartWirtinger_comm_at {n : ℕ} (s t : ℂ)
    (F : EuclideanSpace ℂ (Fin n) → ℂ) (z : EuclideanSpace ℂ (Fin n))
    (hF : ContDiffAt ℝ ∞ F z) (p q : Fin n) :
    q3ChartWirtinger s (fun w => q3ChartWirtinger t F w q) z p =
      q3ChartWirtinger t (fun w => q3ChartWirtinger s F w p) z q := by
  let ep : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single p 1
  let eq : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single q 1
  have hs : IsSymmSndFDerivAt ℝ F z :=
    hF.isSymmSndFDerivAt
      (by simpa [minSmoothness_of_isRCLikeNormedField] using
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  change (fderiv ℝ (fun w => q3ChartWirtinger t F w q) z ep +
    s * fderiv ℝ (fun w => q3ChartWirtinger t F w q) z (Complex.I • ep)) / 2 =
    (fderiv ℝ (fun w => q3ChartWirtinger s F w p) z eq +
    t * fderiv ℝ (fun w => q3ChartWirtinger s F w p) z (Complex.I • eq)) / 2
  rw [q3ChartWirtinger_fderiv_at t F z hF q ep,
    q3ChartWirtinger_fderiv_at t F z hF q (Complex.I • ep),
    q3ChartWirtinger_fderiv_at s F z hF p eq,
    q3ChartWirtinger_fderiv_at s F z hF p (Complex.I • eq)]
  dsimp only [ep, eq] at *
  rw [hs (EuclideanSpace.single p 1) (EuclideanSpace.single q 1),
    hs (EuclideanSpace.single p 1) (Complex.I • EuclideanSpace.single q 1),
    hs (Complex.I • EuclideanSpace.single p 1) (EuclideanSpace.single q 1),
    hs (Complex.I • EuclideanSpace.single p 1) (Complex.I • EuclideanSpace.single q 1)]
  ring

private theorem q3_chartPartialBarComplex_chartPartialZComplex_comm_at {n : ℕ}
    (F : EuclideanSpace ℂ (Fin n) → ℂ) (z : EuclideanSpace ℂ (Fin n))
    (hF : ContDiffAt ℝ ∞ F z) (p q : Fin n) :
    chartPartialBarComplex (fun w => chartPartialZComplex F w p) z q =
      chartPartialZComplex (fun w => chartPartialBarComplex F w q) z p := by
  have hz (A : EuclideanSpace ℂ (Fin n) → ℂ)
      (w : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
      q3ChartWirtinger (-Complex.I) A w j = chartPartialZComplex A w j := by
    simp [q3ChartWirtinger, chartPartialZComplex, div_eq_mul_inv]
    ring
  have hb (w : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
      q3ChartWirtinger Complex.I F w j = chartPartialBarComplex F w j := rfl
  have hzf (j : Fin n) :
      (fun w => q3ChartWirtinger (-Complex.I) F w j) =
        (fun w => chartPartialZComplex F w j) := funext (fun w => hz F w j)
  have hbf (j : Fin n) :
      (fun w => q3ChartWirtinger Complex.I F w j) =
        (fun w => chartPartialBarComplex F w j) := funext (fun w => hb w j)
  calc
    chartPartialBarComplex (fun w => chartPartialZComplex F w p) z q =
        q3ChartWirtinger Complex.I (fun w => q3ChartWirtinger (-Complex.I) F w p) z q := by
      rw [hzf]
      rfl
    _ = q3ChartWirtinger (-Complex.I) (fun w => q3ChartWirtinger Complex.I F w q) z p :=
      (q3ChartWirtinger_comm_at (-Complex.I) Complex.I F z hF p q).symm
    _ = chartPartialZComplex (fun w => chartPartialBarComplex F w q) z p := by
      rw [hbf]
      exact hz (fun w => chartPartialBarComplex F w q) z p

private theorem q3_chartPartialBarComplex_eventuallyEq {n : ℕ}
    (F G : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (q : Fin n)
    (h : F =ᶠ[𝓝 z] G) :
    chartPartialBarComplex F z q = chartPartialBarComplex G z q := by
  have hfd : fderiv ℝ F z = fderiv ℝ G z := (h.fderiv (𝕜 := ℝ)).eq_of_nhds
  unfold chartPartialBarComplex
  rw [hfd]

open scoped ComplexOrder in
private theorem q3_metric_bar_slot_symmetry {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₀ : KahlerForm n M) (x : M) {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (a b q : Fin n) :
    chartPartialBarComplex (fun w ↦ ω₀.metricInChart x w a b) z q =
      chartPartialBarComplex (fun w ↦ ω₀.metricInChart x w a q) z b := by
  let g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w ↦ ω₀.metricInChart x w
  have hG (i j : Fin n) : DifferentiableAt ℝ (fun w ↦ g w i j) z :=
    ((ω₀.contDiffOn_metricInChart x i j).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz)).differentiableAt (by norm_num)
  have hHerm : ∀ᶠ w in 𝓝 z, (g w).IsHermitian := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds hz] with w hw
    exact (ω₀.posDef_metricInChart x hw).isHermitian
  have hEq : (fun w ↦ g w a b) =ᶠ[𝓝 z] fun w ↦ star (g w b a) := by
    filter_upwards [hHerm] with w hw
    exact (hw.apply a b).symm
  calc
    chartPartialBarComplex (fun w ↦ g w a b) z q =
        chartPartialBarComplex (fun w ↦ star (g w b a)) z q :=
      q3_chartPartialBarComplex_eventuallyEq _ _ z q hEq
    _ = star (chartPartialZComplex (fun w ↦ g w b a) z q) :=
      chartPartialBarComplex_star_eq_chartPartialZComplex (hG b a) q
    _ = star (chartPartialZComplex (fun w ↦ g w q a) z b) := by
      apply congrArg star
      simpa [g] using ω₀.kahler_chart_metric_symmetry x hz q b a
    _ = chartPartialBarComplex (fun w ↦ g w a q) z b := by
      have hEq' : (fun w ↦ g w a q) =ᶠ[𝓝 z] fun w ↦ star (g w q a) := by
        filter_upwards [hHerm] with w hw
        exact (hw.apply a q).symm
      calc
        star (chartPartialZComplex (fun w ↦ g w q a) z b) =
            chartPartialBarComplex (fun w ↦ star (g w q a)) z b :=
          (chartPartialBarComplex_star_eq_chartPartialZComplex (hG q a) b).symm
        _ = chartPartialBarComplex (fun w ↦ g w a q) z b :=
          (q3_chartPartialBarComplex_eventuallyEq _ _ z b hEq').symm

private theorem q3_metric_mixed_second_jet_symmetry {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₀ : KahlerForm n M) (x : M) {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (p q j l : Fin n) :
    chartPartialZComplex
        (fun w ↦ chartPartialBarComplex (fun v ↦ ω₀.metricInChart x v j l) w q) z p =
      chartPartialZComplex
        (fun w ↦ chartPartialBarComplex (fun v ↦ ω₀.metricInChart x v p q) w l) z j := by
  let g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w ↦ ω₀.metricInChart x w
  have hG (a b : Fin n) : ContDiffAt ℝ ∞ (fun w ↦ g w a b) z :=
    (ω₀.contDiffOn_metricInChart x a b).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz)
  have htarget : ∀ᶠ w in 𝓝 z,
      w ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target :=
    (isOpen_extChartAt_target x).mem_nhds hz
  have hK :
      (fun w ↦ chartPartialZComplex (fun v ↦ g v j l) w p) =ᶠ[𝓝 z]
      fun w ↦ chartPartialZComplex (fun v ↦ g v p l) w j := by
    filter_upwards [htarget] with w hw
    exact ω₀.kahler_chart_metric_symmetry x hw p j l
  have hKbar := q3_chartPartialBarComplex_eventuallyEq
    (fun w ↦ chartPartialZComplex (fun v ↦ g v j l) w p)
    (fun w ↦ chartPartialZComplex (fun v ↦ g v p l) w j) z q hK
  have hbar :
      (fun w ↦ chartPartialBarComplex (fun v ↦ g v p l) w q) =ᶠ[𝓝 z]
      fun w ↦ chartPartialBarComplex (fun v ↦ g v p q) w l := by
    filter_upwards [htarget] with w hw
    exact q3_metric_bar_slot_symmetry ω₀ x hw p l q
  calc
    chartPartialZComplex
        (fun w ↦ chartPartialBarComplex (fun v ↦ g v j l) w q) z p =
        chartPartialBarComplex
          (fun w ↦ chartPartialZComplex (fun v ↦ g v j l) w p) z q := by
      symm
      exact q3_chartPartialBarComplex_chartPartialZComplex_comm_at
        (fun v ↦ g v j l) z (hG j l) p q
    _ = chartPartialBarComplex
          (fun w ↦ chartPartialZComplex (fun v ↦ g v p l) w j) z q := hKbar
    _ = chartPartialZComplex
          (fun w ↦ chartPartialBarComplex (fun v ↦ g v p l) w q) z j :=
      q3_chartPartialBarComplex_chartPartialZComplex_comm_at
        (fun v ↦ g v p l) z (hG p l) j q
    _ = chartPartialZComplex
          (fun w ↦ chartPartialBarComplex (fun v ↦ g v p q) w l) z j := by
      have hfd := hbar.fderiv_eq (𝕜 := ℝ) (x := z)
      unfold chartPartialZComplex
      rw [hfd]

open scoped ComplexOrder

omit [T2Space M] [CompactSpace M] in
/-- Identify the explicitly contracted chart curvature with the Ricci form's
coefficient matrix, in any actual chart target. -/
theorem c3RicciInChart_eq_ricciForm_coeff (ω₀ : KahlerForm n M) (x : M)
    {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) (j l : Fin n) :
    c3RicciInChart (ω₀.metricInChart x) z j l =
      (ω₀.ricciForm.chartRep x z).coeffMatrix j l := by
  rw [ω₀.chartRep_ricciForm x hz]
  simp only [ContinuousAlternatingMap.coeffMatrix_neg]
  let G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w ↦ ω₀.metricInChart x w
  have hG (a b : Fin n) : ContDiffAt ℝ ∞ (fun w ↦ G w a b) z :=
    (ω₀.contDiffOn_metricInChart x a b).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz)
  have hG1 (a b : Fin n) : ContDiffAt ℝ 1 (fun w ↦ G w a b) z :=
    hG a b |>.of_le (by norm_num)
  have hunit : IsUnit (G z) := (ω₀.posDef_metricInChart x hz).isUnit
  have hHerm : ∀ᶠ w in 𝓝 z, (G w).IsHermitian := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds hz] with w hw
    exact (ω₀.posDef_metricInChart x hw).isHermitian
  have hpos : 0 < (G z).det.re :=
    (RCLike.pos_iff.mp (ω₀.posDef_metricInChart x hz).det_pos).1
  have hB (a b : Fin n) : DifferentiableAt ℝ
      (fun w ↦ chartPartialBarComplex (fun v ↦ G v a b) w l) z := by
    have hfd : DifferentiableAt ℝ (fderiv ℝ (fun v ↦ G v a b)) z :=
      (hG a b).fderiv_right (m := ∞)
        (le_of_eq (show (∞ : ℕ∞ω) = ∞ + 1 from rfl).symm) |>.differentiableAt (by norm_num)
    unfold chartPartialBarComplex
    fun_prop (disch := assumption)
  have hLog := c3_log_det_mixed_inverse_trace_jet
    (G := G) (z := z) j l hG1 hunit hHerm hpos hB
  let H : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun a b ↦
    chartPartialZComplex
      (fun w ↦ chartPartialBarComplex (fun v ↦ G v a b) w l) z j)
  let A : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun a b ↦
    chartPartialZComplex (fun w ↦ G w a b) z j)
  let B : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun a b ↦
    chartPartialBarComplex (fun w ↦ G w a b) z l)
  have hMixed (p q : Fin n) :
      chartPartialZComplex
        (fun w ↦ chartPartialBarComplex (fun v ↦ G v j l) w q) z p =
      chartPartialZComplex
        (fun w ↦ chartPartialBarComplex (fun v ↦ G v p q) w l) z j := by
    simpa [G] using q3_metric_mixed_second_jet_symmetry ω₀ x hz p q j l
  have hX (p j' b : Fin n) :
      chartPartialZComplex (fun w ↦ G w j' b) z p =
        chartPartialZComplex (fun w ↦ G w p b) z j' := by
    exact ω₀.kahler_chart_metric_symmetry x hz p j' b
  have hY (q a l' : Fin n) :
      chartPartialBarComplex (fun w ↦ G w a l') z q =
        chartPartialBarComplex (fun w ↦ G w a q) z l' := by
    simpa [G] using q3_metric_bar_slot_symmetry ω₀ x hz a l' q
  have htraceH : Matrix.trace ((G z)⁻¹ * H) =
      ∑ p, ∑ q, (G z)⁻¹ q p *
        chartPartialZComplex
          (fun w ↦ chartPartialBarComplex (fun v ↦ G v p q) w l) z j := by
    calc
      Matrix.trace ((G z)⁻¹ * H) =
          ∑ p, ∑ q, (G z)⁻¹ p q *
            chartPartialZComplex
              (fun w ↦ chartPartialBarComplex (fun v ↦ G v q p) w l) z j := by
        simp [Matrix.trace, Matrix.mul_apply, H, Matrix.of_apply]
      _ = ∑ p, ∑ q, (G z)⁻¹ q p *
            chartPartialZComplex
              (fun w ↦ chartPartialBarComplex (fun v ↦ G v p q) w l) z j := by
        rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
          (f := fun p q : Fin n => (G z)⁻¹ p q *
            chartPartialZComplex
              (fun w ↦ chartPartialBarComplex (fun v ↦ G v q p) w l) z j)]
  have htraceQ : Matrix.trace ((G z)⁻¹ * A * (G z)⁻¹ * B) =
      ∑ r, ∑ s, ∑ a, ∑ b, (G z)⁻¹ r a *
        chartPartialZComplex (fun w ↦ G w a b) z j *
        (G z)⁻¹ b s * chartPartialBarComplex (fun w ↦ G w s r) z l := by
    have hrotate (f : Fin n → Fin n → Fin n → ℂ) :
        (∑ a, ∑ b, ∑ c, f a b c) = ∑ b, ∑ c, ∑ a, f a b c := by
      calc
        _ = ∑ b, ∑ a, ∑ c, f a b c := Finset.sum_comm
        _ = ∑ b, ∑ c, ∑ a, f a b c := by
          apply Finset.sum_congr rfl
          intro b hb
          exact Finset.sum_comm
    simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, A, B,
      Finset.mul_sum, mul_assoc]
    apply Finset.sum_congr rfl
    intro r hr
    let f : Fin n → Fin n → Fin n → ℂ := fun s a b =>
      (G z)⁻¹ r a * chartPartialZComplex (fun w ↦ G w a b) z j *
        (G z)⁻¹ b s * chartPartialBarComplex (fun w ↦ G w s r) z l
    simpa [f, mul_assoc] using (hrotate f).symm
  have hcurv : c3RicciInChart G z j l =
      -Matrix.trace ((G z)⁻¹ * H) + Matrix.trace ((G z)⁻¹ * A * (G z)⁻¹ * B) := by
    simp only [c3RicciInChart, chartCurvature]
    simp_rw [mul_add, mul_neg]
    simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib]
    rw [show (∑ p, ∑ q, (G z)⁻¹ q p *
        chartPartialZComplex
          (fun w ↦ chartPartialBarComplex (fun v ↦ G v j l) w q) z p) =
      ∑ p, ∑ q, (G z)⁻¹ q p *
        chartPartialZComplex
          (fun w ↦ chartPartialBarComplex (fun v ↦ G v p q) w l) z j by
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro q hq
        rw [hMixed p q]]
    rw [htraceH]
    simp_rw [Finset.mul_sum]
    simp_rw [← mul_assoc]
    have hquad :
        (∑ p, ∑ q, ∑ a, ∑ b, (G z)⁻¹ q p * (G z)⁻¹ b a *
          chartPartialZComplex (fun w ↦ G w j b) z p *
          chartPartialBarComplex (fun w ↦ G w a l) z q) =
        Matrix.trace ((G z)⁻¹ * A * (G z)⁻¹ * B) := by
      calc
        _ = ∑ r, ∑ s, ∑ a, ∑ b, (G z)⁻¹ r a *
            chartPartialZComplex (fun w ↦ G w j b) z a *
            (G z)⁻¹ b s * chartPartialBarComplex (fun w ↦ G w s r) z l := by
              exact curvature_quadratic_reindex ((G z)⁻¹)
                (fun p j' b ↦ chartPartialZComplex (fun w ↦ G w j' b) z p)
                (fun q a l' ↦ chartPartialBarComplex (fun w ↦ G w a l') z q)
                hX hY j l
        _ = Matrix.trace ((G z)⁻¹ * A * (G z)⁻¹ * B) := by
          calc
            _ = ∑ r, ∑ s, ∑ a, ∑ b, (G z)⁻¹ r a *
                chartPartialZComplex (fun w ↦ G w a b) z j *
                (G z)⁻¹ b s * chartPartialBarComplex (fun w ↦ G w s r) z l := by
              apply Finset.sum_congr rfl
              intro r hr
              apply Finset.sum_congr rfl
              intro s hs
              apply Finset.sum_congr rfl
              intro a ha
              apply Finset.sum_congr rfl
              intro b hb
              rw [hX a j b]
            _ = Matrix.trace ((G z)⁻¹ * A * (G z)⁻¹ * B) := htraceQ.symm
    rw [hquad]
  have hf : ContDiffAt ℝ 2 (ω₀.logDetInChart x) z :=
    (ω₀.contDiffOn_logDetInChart x).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz) |>.of_le
        (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hbarCast (w : EuclideanSpace ℂ (Fin n))
      (hw : w ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
      chartPartialBarComplex (fun v ↦ (ω₀.logDetInChart x v : ℂ)) w l =
        chartPartialBar (ω₀.logDetInChart x) w l := by
    have hfw : ContDiffAt ℝ 1 (ω₀.logDetInChart x) w :=
      (ω₀.contDiffOn_logDetInChart x).contDiffAt
        ((isOpen_extChartAt_target x).mem_nhds hw) |>.of_le (by norm_num)
    have hfd := (Complex.ofRealCLM.hasFDerivAt.comp w
      (hfw.differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)).hasFDerivAt).fderiv
    have hfun : (fun v ↦ (ω₀.logDetInChart x v : ℂ)) =
        Complex.ofRealCLM ∘ (ω₀.logDetInChart x) := by
      funext v
      rfl
    rw [← hfun] at hfd
    unfold chartPartialBarComplex chartPartialBar
    rw [hfd]
    simp [ContinuousLinearMap.comp_apply]
  have hbarGerm :
      (fun w ↦ chartPartialBarComplex
        (fun v ↦ (ω₀.logDetInChart x v : ℂ)) w l) =ᶠ[𝓝 z]
      fun w ↦ chartPartialBar (ω₀.logDetInChart x) w l := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds hz] with w hw
    exact hbarCast w hw
  have hbarDeriv := hbarGerm.fderiv_eq (𝕜 := ℝ) (x := z)
  have hHess :
      chartPartialZComplex
        (fun w ↦ chartPartialBarComplex
          (fun v ↦ (ω₀.logDetInChart x v : ℂ)) w l) z j =
        complexHessian (ω₀.logDetInChart x) z j l := by
    unfold chartPartialZComplex
    rw [hbarDeriv]
    exact chartPartialZComplex_chartPartialBar _ z hf j l
  have hLog' :
      chartPartialZComplex
        (fun w ↦ chartPartialBarComplex
          (fun v ↦ (Real.log ((G v).det.re) : ℂ)) w l) z j =
        Matrix.trace ((G z)⁻¹ * H) -
          Matrix.trace ((G z)⁻¹ * A * (G z)⁻¹ * B) := by
    simpa [H, A, B, Matrix.mul_assoc] using hLog
  have hcurvLog : c3RicciInChart G z j l = -
      chartPartialZComplex
        (fun w ↦ chartPartialBarComplex
          (fun v ↦ (Real.log ((G v).det.re) : ℂ)) w l) z j := by
    rw [hcurv, hLog']
    ring
  have hlogfun :
      (fun v ↦ (Real.log ((G v).det.re) : ℂ)) =
        fun v ↦ (ω₀.logDetInChart x v : ℂ) := by
    funext v
    simp [G, logDetInChart]
  rw [hlogfun] at hcurvLog
  rw [hcurvLog, hHess]
  simp [complexHessian]

end KahlerForm
