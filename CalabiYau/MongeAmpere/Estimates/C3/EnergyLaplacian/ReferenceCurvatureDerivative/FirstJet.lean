module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceCurvatureDerivative.Basic
public import CalabiYau.Geometry.Kahler.Curvature.Chart

/-!
# The first jet of the actual curvature pullback

Differentiate the closed four-slot curvature law on a neighborhood. The two
holomorphic Jacobian derivatives remain; the conjugate derivatives vanish.
They will cancel only after subtracting the two connection terms in the
separate covariance identity. Source: Székelyhidi, §3.3, proof of Lemma 3.9,
printed pp. 44–45 (GSM152 PDF physical pages 62–63).
-/

public section

open scoped Manifold ContDiff

namespace KahlerForm

open scoped BigOperators ComplexOrder

open Filter

private theorem auxiliary_detDomains_eventually
    {n : ℕ}
    (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (f : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (hf : ContDiffOn ℝ ∞ f U) (hhol : DifferentiableOn ℂ f U)
    (g' : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (hg' : ∀ a b, ContDiffOn ℝ ∞ (fun w => g' w a b) (f '' U))
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U)
    (hjac : IsUnit (EuclideanSpace.clmMatrix (fderiv ℂ f z)).det)
    (hgdet : IsUnit (g' (f z)).det) :
    ∀ᶠ w in nhds z,
      w ∈ U ∧ IsUnit (EuclideanSpace.clmMatrix (fderiv ℂ f w)).det ∧
        IsUnit (g' (f w)).det := by
  let A := fun w => EuclideanSpace.clmMatrix (fderiv ℂ f w)
  have hAsmooth (a b : Fin n) : ContDiffAt ℝ ∞ (fun w => A w a b) z :=
    chart_pullback_jacobian_entry_contDiffAt U hU f hf hhol z hz a b
  have hAdet : ContinuousAt (fun w => (A w).det) z := by
    have hs : ContDiffAt ℝ ∞ (fun w => (A w).det) z := by
      simp_rw [Matrix.det_apply]
      fun_prop (disch := assumption)
    exact hs.continuousAt
  have himage : f '' U ∈ nhds (f z) :=
    chart_pullback_image_nhds U hU f hf hhol z hz hjac
  have hGsmooth (a b : Fin n) : ContDiffAt ℝ ∞ (fun w => g' w a b) (f z) :=
    (hg' a b (f z) ⟨z, hz, rfl⟩).contDiffAt himage
  have hGdet : ContinuousAt (fun w => (g' w).det) (f z) := by
    have hs : ContDiffAt ℝ ∞ (fun w => (g' w).det) (f z) := by
      simp_rw [Matrix.det_apply]
      fun_prop (disch := assumption)
    exact hs.continuousAt
  have hfz : ContinuousAt f z := (hf.contDiffAt (hU.mem_nhds hz)).continuousAt
  have hAunit : ∀ᶠ w in nhds z, IsUnit (A w).det := by
    filter_upwards [hAdet.eventually_ne hjac.ne_zero] with w hw
    exact isUnit_iff_ne_zero.mpr hw
  have hGunit : ∀ᶠ w in nhds z, IsUnit (g' (f w)).det := by
    filter_upwards [(hGdet.comp hfz).eventually_ne hgdet.ne_zero] with w hw
    exact isUnit_iff_ne_zero.mpr hw
  filter_upwards [hU.mem_nhds hz, hAunit, hGunit] with w hw hA hG
  exact ⟨hw, hA, hG⟩

private theorem auxiliary_curvature_pullback_eventuallyEq
    {n : ℕ}
    (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (f : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (hf : ContDiffOn ℝ ∞ f U) (hhol : DifferentiableOn ℂ f U)
    (g g' : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (hg' : ∀ j k, ContDiffOn ℝ ∞ (fun w => g' w j k) (f '' U))
    (hmetric : ∀ w ∈ U,
      g w = Matrix.transpose (EuclideanSpace.clmMatrix (fderiv ℂ f w)) *
        g' (f w) * (EuclideanSpace.clmMatrix (fderiv ℂ f w)).map star)
    (hkahler : ∀ w ∈ f '' U, ∀ i j k,
      chartPartialZComplex (fun v => g' v j k) w i =
        chartPartialZComplex (fun v => g' v i k) w j)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U)
    (hdetA : ∀ᶠ w in nhds z,
      IsUnit (EuclideanSpace.clmMatrix (fderiv ℂ f w)).det)
    (hdetg : ∀ᶠ w in nhds z, IsUnit (g' (f w)).det)
    (p q j k : Fin n) :
    (fun w => chartCurvature g w p q j k) =ᶠ[nhds z]
      (fun w => ∑ a, ∑ b, ∑ c, ∑ d,
        (EuclideanSpace.clmMatrix (fderiv ℂ f w)) a p *
          star ((EuclideanSpace.clmMatrix (fderiv ℂ f w)) b q) *
          (EuclideanSpace.clmMatrix (fderiv ℂ f w)) c j *
          star ((EuclideanSpace.clmMatrix (fderiv ℂ f w)) d k) *
          chartCurvature g' (f w) a b c d) := by
  filter_upwards [hU.mem_nhds hz, hdetA, hdetg] with w hw hAw hgw
  exact chartCurvature_pullback U hU f hf hhol g g' hg' hmetric hkahler w hw
    hAw hgw p q j k

private theorem auxiliary_contDiffOn_chartPartialZ
    {n : ℕ} {V : Set (EuclideanSpace ℂ (Fin n))} (hV : IsOpen V)
    (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (hF : ContDiffOn ℝ ∞ F V) (p : Fin n) :
    ContDiffOn ℝ ∞ (fun z => chartPartialZComplex F z p) V := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ F) V := by
    simpa using hF.fderiv_of_isOpen hV (by simp)
  have hEval (v : EuclideanSpace ℂ (Fin n)) :
      ContDiffOn ℝ ∞ (fun z => fderiv ℝ F z v) V := by
    let evL : (EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ) →ₗ[ℝ] ℂ := {
      toFun := fun D => D v
      map_add' := by intro D₁ D₂; rfl
      map_smul' := by intro c D; rfl }
    let ev : (EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ) →L[ℝ] ℂ :=
      evL.toContinuousLinearMap
    exact ev.contDiff.comp_contDiffOn hD
  change ContDiffOn ℝ ∞ (fun z =>
    (fderiv ℝ F z (EuclideanSpace.single p 1) -
      Complex.I * fderiv ℝ F z (Complex.I • EuclideanSpace.single p 1)) / 2) V
  have h₁ := hEval (EuclideanSpace.single p (1 : ℂ))
  have h₂ := hEval (Complex.I • EuclideanSpace.single p (1 : ℂ))
  fun_prop (disch := assumption)

private theorem auxiliary_contDiffOn_chartPartialBar
    {n : ℕ} {V : Set (EuclideanSpace ℂ (Fin n))} (hV : IsOpen V)
    (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (hF : ContDiffOn ℝ ∞ F V) (p : Fin n) :
    ContDiffOn ℝ ∞ (fun z => chartPartialBarComplex F z p) V := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ F) V := by
    simpa using hF.fderiv_of_isOpen hV (by simp)
  have hEval (v : EuclideanSpace ℂ (Fin n)) :
      ContDiffOn ℝ ∞ (fun z => fderiv ℝ F z v) V := by
    let evL : (EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ) →ₗ[ℝ] ℂ := {
      toFun := fun D => D v
      map_add' := by intro D₁ D₂; rfl
      map_smul' := by intro c D; rfl }
    let ev : (EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ) →L[ℝ] ℂ :=
      evL.toContinuousLinearMap
    exact ev.contDiff.comp_contDiffOn hD
  change ContDiffOn ℝ ∞ (fun z =>
    (fderiv ℝ F z (EuclideanSpace.single p 1) +
      Complex.I * fderiv ℝ F z (Complex.I • EuclideanSpace.single p 1)) / 2) V
  have h₁ := hEval (EuclideanSpace.single p (1 : ℂ))
  have h₂ := hEval (Complex.I • EuclideanSpace.single p (1 : ℂ))
  fun_prop (disch := assumption)

private theorem auxiliary_chartPartialZ_differentiableAt
    {n : ℕ} (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (hF : ContDiffAt ℝ ∞ F z) (p : Fin n) :
    DifferentiableAt ℝ (fun w => chartPartialZComplex F w p) z := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ F) z :=
    (hF.fderiv_right (m := ∞)
      (le_of_eq (show (∞ : ℕ∞ω) = ∞ + 1 from rfl).symm)).differentiableAt (by norm_num)
  have he : DifferentiableAt ℝ
      (fun w => fderiv ℝ F w (EuclideanSpace.single p 1)) z :=
    hfd.clm_apply (differentiableAt_const _)
  have hie : DifferentiableAt ℝ
      (fun w => fderiv ℝ F w (Complex.I • EuclideanSpace.single p 1)) z :=
    hfd.clm_apply (differentiableAt_const _)
  unfold chartPartialZComplex
  fun_prop (disch := assumption)

private theorem auxiliary_chartPartialBar_differentiableAt
    {n : ℕ} (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (hF : ContDiffAt ℝ ∞ F z) (p : Fin n) :
    DifferentiableAt ℝ (fun w => chartPartialBarComplex F w p) z := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ F) z :=
    (hF.fderiv_right (m := ∞)
      (le_of_eq (show (∞ : ℕ∞ω) = ∞ + 1 from rfl).symm)).differentiableAt (by norm_num)
  have he : DifferentiableAt ℝ
      (fun w => fderiv ℝ F w (EuclideanSpace.single p 1)) z :=
    hfd.clm_apply (differentiableAt_const _)
  have hie : DifferentiableAt ℝ
      (fun w => fderiv ℝ F w (Complex.I • EuclideanSpace.single p 1)) z :=
    hfd.clm_apply (differentiableAt_const _)
  unfold chartPartialBarComplex
  fun_prop (disch := assumption)

private theorem auxiliary_chartPartialBar_contDiffAt
    {n : ℕ} (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (hF : ContDiffAt ℝ ∞ F z) (p : Fin n) :
    ContDiffAt ℝ ∞ (fun w => chartPartialBarComplex F w p) z := by
  have hfd : ContDiffAt ℝ ∞ (fderiv ℝ F) z := hF.fderiv_right (by simp)
  unfold chartPartialBarComplex
  fun_prop (disch := assumption)

private theorem auxiliary_targetCurvature_differentiableAt
    {n : ℕ} (Vsrc : Set (EuclideanSpace ℂ (Fin n)))
    (g' : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (hg' : ∀ a b, ContDiffOn ℝ ∞ (fun w => g' w a b) Vsrc)
    (y : EuclideanSpace ℂ (Fin n)) (hy : y ∈ Vsrc)
    (himage : Vsrc ∈ nhds y) (hdet : IsUnit (g' y).det)
    (p q j k : Fin n) :
    DifferentiableAt ℝ (fun w => chartCurvature g' w p q j k) y := by
  have hGsmooth (a b : Fin n) : ContDiffAt ℝ ∞ (fun w => g' w a b) y :=
    (hg' a b y hy).contDiffAt himage
  have hG1 (a b : Fin n) : ContDiffAt ℝ 1 (fun w => g' w a b) y :=
    (hGsmooth a b).of_le (by norm_num)
  have hGunit : IsUnit (g' y) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr hdet
  have hinv (a b : Fin n) : DifferentiableAt ℝ (fun w => (g' w)⁻¹ a b) y :=
    chartInv_differentiableAt (fun i j => hG1 i j) hGunit a b
  have hZ (a b : Fin n) :
      DifferentiableAt ℝ (fun w => chartPartialZComplex (fun v => g' v a b) w p) y :=
    auxiliary_chartPartialZ_differentiableAt (fun v => g' v a b) y (hGsmooth a b) p
  have hBar (a b : Fin n) :
      DifferentiableAt ℝ (fun w => chartPartialBarComplex (fun v => g' v a b) w q) y :=
    auxiliary_chartPartialBar_differentiableAt (fun v => g' v a b) y (hGsmooth a b) q
  have hBarSmooth (a b : Fin n) : ContDiffAt ℝ ∞
      (fun w => chartPartialBarComplex (fun v => g' v a b) w q) y :=
    auxiliary_chartPartialBar_contDiffAt (fun v => g' v a b) y (hGsmooth a b) q
  have hZBar (a b : Fin n) : DifferentiableAt ℝ
      (fun w => chartPartialZComplex
        (fun x => chartPartialBarComplex (fun v => g' v a b) x q) w p) y :=
    auxiliary_chartPartialZ_differentiableAt
      (fun x => chartPartialBarComplex (fun v => g' v a b) x q) y (hBarSmooth a b) p
  let T (a b : Fin n) (w : EuclideanSpace ℂ (Fin n)) : ℂ :=
    (g' w)⁻¹ b a * chartPartialZComplex (fun v => g' v j b) w p *
      chartPartialBarComplex (fun v => g' v a k) w q
  have hT (a b : Fin n) : DifferentiableAt ℝ (T a b) y :=
    ((hinv b a).mul (hZ j b)).mul (hBar a k)
  have hsumB (a : Fin n) : DifferentiableAt ℝ (fun w => ∑ b, T a b w) y := by
    have heq : (fun w => ∑ b, T a b w) = ∑ b, fun w => T a b w := by
      funext w
      simp
    rw [heq]
    exact DifferentiableAt.sum (u := Finset.univ) (fun b hb => hT a b)
  have hsum : DifferentiableAt ℝ (fun w => ∑ a, ∑ b, T a b w) y := by
    have heq : (fun w => ∑ a, ∑ b, T a b w) = ∑ a, fun w => ∑ b, T a b w := by
      funext w
      simp
    rw [heq]
    exact DifferentiableAt.sum (u := Finset.univ) (fun a ha => hsumB a)
  have hformula : (fun w => chartCurvature g' w p q j k) =
      fun w => -chartPartialZComplex
        (fun x => chartPartialBarComplex (fun v => g' v j k) x q) w p +
        ∑ a, ∑ b, T a b w := by
    funext w
    rfl
  rw [hformula]
  exact (hZBar j k).neg.add hsum

private theorem auxiliary_targetCurvature_differentiableAt_pullback
    {n : ℕ}
    (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (f : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (hf : ContDiffOn ℝ ∞ f U) (hhol : DifferentiableOn ℂ f U)
    (g' : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (hg' : ∀ a b, ContDiffOn ℝ ∞ (fun w => g' w a b) (f '' U))
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U)
    (hjac : IsUnit (EuclideanSpace.clmMatrix (fderiv ℂ f z)).det)
    (hgdet : IsUnit (g' (f z)).det) (a b c d : Fin n) :
    DifferentiableAt ℝ (fun w => chartCurvature g' w a b c d) (f z) := by
  apply auxiliary_targetCurvature_differentiableAt (f '' U) g' hg' (f z)
    ⟨z, hz, rfl⟩ (chart_pullback_image_nhds U hU f hf hhol z hz hjac) hgdet

private theorem auxiliary_chartPartialBar_zero_of_complexDiff
    {n : ℕ} (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (q : Fin n)
    (hF : DifferentiableAt ℂ F z) :
    chartPartialBarComplex F z q = 0 := by
  have hreal : fderiv ℝ F z = (fderiv ℂ F z).restrictScalars ℝ :=
    hF.fderiv_restrictScalars ℝ
  have hI : fderiv ℂ F z (Complex.I • EuclideanSpace.single q (1 : ℂ)) =
      Complex.I * fderiv ℂ F z (EuclideanSpace.single q 1) := by simp
  unfold chartPartialBarComplex
  rw [hreal, ContinuousLinearMap.coe_restrictScalars', hI]
  rw [← mul_assoc, Complex.I_mul_I]
  ring

private theorem auxiliary_chartPartialZ_star_eq_star_bar
    {n : ℕ} (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (q : Fin n)
    (hF : DifferentiableAt ℝ F z) :
    chartPartialZComplex (fun w => star (F w)) z q =
      star (chartPartialBarComplex F z q) := by
  have hstar : fderiv ℝ (fun w => star (F w)) z =
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ F z) := by
    exact (Complex.conjCLE.hasFDerivAt.comp z hF.hasFDerivAt).fderiv
  unfold chartPartialZComplex chartPartialBarComplex
  rw [hstar]
  change (star (fderiv ℝ F z (EuclideanSpace.single q 1)) -
    Complex.I * star (fderiv ℝ F z (Complex.I • EuclideanSpace.single q 1))) / 2 =
      star ((fderiv ℝ F z (EuclideanSpace.single q 1) +
        Complex.I * fderiv ℝ F z (Complex.I • EuclideanSpace.single q 1)) / 2)
  simp [Complex.conj_I]
  ring_nf

private theorem auxiliary_chartPartialZCoordinateComp
    {n : ℕ} (f : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) (a j : Fin n)
    (hf : DifferentiableAt ℂ f z) :
    chartPartialZComplex (fun w => (f w) a) z j =
      EuclideanSpace.clmMatrix (fderiv ℂ f z) a j := by
  let F : EuclideanSpace ℂ (Fin n) → ℂ := fun w => (f w) a
  let π : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ := EuclideanSpace.proj a
  have hF : DifferentiableAt ℂ F z := by
    dsimp [F]
    fun_prop (disch := assumption)
  have hFderiv : fderiv ℂ F z = π.comp (fderiv ℂ f z) := by
    have hcomp := π.hasFDerivAt.comp z hf.hasFDerivAt
    simpa [F, π, Function.comp_def] using hcomp.fderiv
  have hreal : fderiv ℝ F z = (fderiv ℂ F z).restrictScalars ℝ :=
    hF.fderiv_restrictScalars ℝ
  have hI : fderiv ℂ F z (Complex.I • EuclideanSpace.single j (1 : ℂ)) =
      Complex.I * fderiv ℂ F z (EuclideanSpace.single j 1) := by simp
  unfold chartPartialZComplex
  rw [hreal, ContinuousLinearMap.coe_restrictScalars', hI, hFderiv]
  simp [π, EuclideanSpace.clmMatrix]
  let x := ((fderiv ℂ f z) (EuclideanSpace.single j (1 : ℂ))).ofLp a
  have hxx : Complex.I * (Complex.I * x) = -x := by
    calc
      Complex.I * (Complex.I * x) = (Complex.I * Complex.I) * x := by ring
      _ = -x := by rw [Complex.I_mul_I]; ring
  rw [show Complex.I *
      (Complex.I * ((fderiv ℂ f z) (EuclideanSpace.single j (1 : ℂ))).ofLp a) =
        -((fderiv ℂ f z) (EuclideanSpace.single j (1 : ℂ))).ofLp a by
          simpa [x] using hxx]
  ring

private noncomputable def auxiliaryWirtinger
    {n : ℕ} (s : ℂ) (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (w : EuclideanSpace ℂ (Fin n)) (j : Fin n) : ℂ :=
  (fderiv ℝ F w (EuclideanSpace.single j 1) +
    s * fderiv ℝ F w (Complex.I • EuclideanSpace.single j 1)) / 2

private theorem auxiliaryWirtinger_fderiv_at {n : ℕ} (s : ℂ)
    (F : EuclideanSpace ℂ (Fin n) → ℂ) (z : EuclideanSpace ℂ (Fin n))
    (hF : ContDiffAt ℝ ∞ F z) (j : Fin n)
    (v : EuclideanSpace ℂ (Fin n)) :
    fderiv ℝ (fun w => auxiliaryWirtinger s F w j) z v =
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
  have hfun : (fun w => auxiliaryWirtinger s F w j) =
      fun w => (2 : ℂ)⁻¹ * (fderiv ℝ F w e + s * fderiv ℝ F w (Complex.I • e)) := by
    funext w
    simp only [auxiliaryWirtinger, e, div_eq_mul_inv]
    ring
  rw [hfun, fderiv_const_mul hsum, fderiv_fun_add he (hie.const_mul s),
    fderiv_const_mul hie]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [h_e v, h_ie v]
  simp only [div_eq_mul_inv]
  ring

private theorem auxiliaryWirtinger_comm_at {n : ℕ} (s t : ℂ)
    (F : EuclideanSpace ℂ (Fin n) → ℂ) (z : EuclideanSpace ℂ (Fin n))
    (hF : ContDiffAt ℝ ∞ F z) (p q : Fin n) :
    auxiliaryWirtinger s (fun w => auxiliaryWirtinger t F w q) z p =
      auxiliaryWirtinger t (fun w => auxiliaryWirtinger s F w p) z q := by
  let ep : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single p 1
  let eq : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single q 1
  have hs : IsSymmSndFDerivAt ℝ F z :=
    hF.isSymmSndFDerivAt
      (by simpa [minSmoothness_of_isRCLikeNormedField] using
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  change (fderiv ℝ (fun w => auxiliaryWirtinger t F w q) z ep +
    s * fderiv ℝ (fun w => auxiliaryWirtinger t F w q) z (Complex.I • ep)) / 2 =
    (fderiv ℝ (fun w => auxiliaryWirtinger s F w p) z eq +
    t * fderiv ℝ (fun w => auxiliaryWirtinger s F w p) z (Complex.I • eq)) / 2
  rw [auxiliaryWirtinger_fderiv_at t F z hF q ep,
    auxiliaryWirtinger_fderiv_at t F z hF q (Complex.I • ep),
    auxiliaryWirtinger_fderiv_at s F z hF p eq,
    auxiliaryWirtinger_fderiv_at s F z hF p (Complex.I • eq)]
  dsimp only [ep, eq] at *
  rw [hs (EuclideanSpace.single p 1) (EuclideanSpace.single q 1),
    hs (EuclideanSpace.single p 1) (Complex.I • EuclideanSpace.single q 1),
    hs (Complex.I • EuclideanSpace.single p 1) (EuclideanSpace.single q 1),
    hs (Complex.I • EuclideanSpace.single p 1) (Complex.I • EuclideanSpace.single q 1)]
  ring

private theorem auxiliary_chartPartialBar_chartPartialZ_comm_at {n : ℕ}
    (F : EuclideanSpace ℂ (Fin n) → ℂ) (z : EuclideanSpace ℂ (Fin n))
    (hF : ContDiffAt ℝ ∞ F z) (p q : Fin n) :
    chartPartialBarComplex (fun w => chartPartialZComplex F w p) z q =
      chartPartialZComplex (fun w => chartPartialBarComplex F w q) z p := by
  have hz (G : EuclideanSpace ℂ (Fin n) → ℂ)
      (w : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
      auxiliaryWirtinger (-Complex.I) G w j = chartPartialZComplex G w j := by
    simp [auxiliaryWirtinger, chartPartialZComplex, div_eq_mul_inv]
    ring
  have hb (w : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
      auxiliaryWirtinger Complex.I F w j = chartPartialBarComplex F w j := rfl
  have hzf (j : Fin n) :
      (fun w => auxiliaryWirtinger (-Complex.I) F w j) =
        (fun w => chartPartialZComplex F w j) := funext (fun w => hz F w j)
  have hbf (j : Fin n) :
      (fun w => auxiliaryWirtinger Complex.I F w j) =
        (fun w => chartPartialBarComplex F w j) := funext (fun w => hb w j)
  calc
    chartPartialBarComplex (fun w => chartPartialZComplex F w p) z q =
        auxiliaryWirtinger Complex.I (fun w => auxiliaryWirtinger (-Complex.I) F w p) z q := by
      rw [hzf]
      rfl
    _ = auxiliaryWirtinger (-Complex.I)
        (fun w => auxiliaryWirtinger Complex.I F w q) z p :=
      (auxiliaryWirtinger_comm_at (-Complex.I) Complex.I F z hF p q).symm
    _ = chartPartialZComplex (fun w => chartPartialBarComplex F w q) z p := by
      rw [hbf]
      exact hz (fun w => chartPartialBarComplex F w q) z p

private theorem auxiliary_chartPartialBar_jacobian_zero
    {n : ℕ}
    (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (f : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (hf : ContDiffOn ℝ ∞ f U) (hhol : DifferentiableOn ℂ f U)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U) (a j q : Fin n) :
    chartPartialBarComplex
      (fun w => EuclideanSpace.clmMatrix (fderiv ℂ f w) a j) z q = 0 := by
  let F : EuclideanSpace ℂ (Fin n) → ℂ := fun w => (f w) a
  have hFreal : ContDiffAt ℝ ∞ F z := by
    have hfsmooth : ContDiffAt ℝ ∞ f z := (hf z hz).contDiffAt (hU.mem_nhds hz)
    have hcoord : ContDiff ℝ ∞ (fun x : EuclideanSpace ℂ (Fin n) => x a) := by
      fun_prop
    simpa [F, Function.comp_def] using hcoord.contDiffAt.comp z hfsmooth
  have hEq : (fun w => EuclideanSpace.clmMatrix (fderiv ℂ f w) a j) =ᶠ[nhds z]
      fun w => chartPartialZComplex F w j := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact (auxiliary_chartPartialZCoordinateComp f w a j
      ((hhol w hw).differentiableAt (hU.mem_nhds hw))).symm
  have hbarEq := hEq.fderiv_eq (𝕜 := ℝ)
  have hbarF : (fun w => chartPartialBarComplex F w q) =ᶠ[nhds z]
      fun _ => (0 : ℂ) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    have hfw : DifferentiableAt ℂ f w :=
      (hhol w hw).differentiableAt (hU.mem_nhds hw)
    have hFw : DifferentiableAt ℂ F w := by
      dsimp [F]
      fun_prop (disch := assumption)
    exact auxiliary_chartPartialBar_zero_of_complexDiff F w q hFw
  have hzero : chartPartialZComplex
      (fun w => chartPartialBarComplex F w q) z j = 0 := by
    unfold chartPartialZComplex
    rw [hbarF.fderiv_eq]
    simp
  have hcomm := auxiliary_chartPartialBar_chartPartialZ_comm_at F z hFreal j q
  calc
    chartPartialBarComplex
        (fun w => EuclideanSpace.clmMatrix (fderiv ℂ f w) a j) z q =
      chartPartialBarComplex (fun w => chartPartialZComplex F w j) z q := by
        unfold chartPartialBarComplex
        rw [hbarEq]
    _ = chartPartialZComplex (fun w => chartPartialBarComplex F w q) z j := hcomm
    _ = 0 := hzero

private theorem auxiliary_clmMatrix_single_eq_sum {n : ℕ}
    (L : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (j : Fin n) :
    L (EuclideanSpace.single j 1) =
      ∑ a, (EuclideanSpace.clmMatrix L a j) • EuclideanSpace.single a 1 := by
  ext a
  simp [EuclideanSpace.clmMatrix, Pi.single_apply]

private theorem auxiliary_wirtinger_directional_smul {n : ℕ}
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

private theorem auxiliary_chartPartialZ_comp_holomorphic {n : ℕ}
    (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (f : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n)
    (hF : DifferentiableAt ℝ F (f z)) (hf : DifferentiableAt ℂ f z) :
    chartPartialZComplex (fun w => F (f w)) z j =
      ∑ a, (EuclideanSpace.clmMatrix (fderiv ℂ f z)) a j *
        chartPartialZComplex F (f z) a := by
  let L := fderiv ℂ f z
  have hfℝ : DifferentiableAt ℝ f z := hf.restrictScalars ℝ
  have hreal : fderiv ℝ f z = L.restrictScalars ℝ := by
    simpa [L] using hf.fderiv_restrictScalars ℝ
  have hcomp := fderiv_comp (f := f) (g := F) (x := z) hF hfℝ
  have hcomp' : fderiv ℝ (fun w => F (f w)) z =
      (fderiv ℝ F (f z)).comp (fderiv ℝ f z) := by
    simpa [Function.comp_def] using hcomp
  let D := fderiv ℝ F (f z)
  let M := EuclideanSpace.clmMatrix L
  let e := EuclideanSpace.single j (1 : ℂ)
  have hvec : L e = ∑ a, (M a j) • EuclideanSpace.single a (1 : ℂ) := by
    simpa [M, e] using auxiliary_clmMatrix_single_eq_sum L j
  unfold chartPartialZComplex
  rw [hcomp', hreal]
  simp only [ContinuousLinearMap.comp_apply]
  change (D (L e) - Complex.I * D (L (Complex.I • e))) / 2 = _
  rw [map_smul, hvec]
  simp only [map_sum, Finset.smul_sum]
  have hsum :
      (∑ a, D ((M a j) • EuclideanSpace.single a (1 : ℂ))) -
        Complex.I * ∑ a, D (Complex.I • ((M a j) • EuclideanSpace.single a (1 : ℂ))) =
      ∑ a, (D ((M a j) • EuclideanSpace.single a (1 : ℂ)) -
        Complex.I * D (Complex.I • ((M a j) • EuclideanSpace.single a (1 : ℂ)))) := by
    rw [Finset.mul_sum, Finset.sum_sub_distrib]
  rw [hsum]
  simp_rw [auxiliary_wirtinger_directional_smul]
  simp only [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  ring

private theorem auxiliary_five_factor_pullback_firstJet
    {n : ℕ}
    (u v w x H : EuclideanSpace ℂ (Fin n) → ℂ)
    (ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) (p : Fin n)
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z)
    (hw : DifferentiableAt ℝ w z) (hx : DifferentiableAt ℝ x z)
    (hH : DifferentiableAt ℝ H (ψ z)) (hψ : DifferentiableAt ℂ ψ z)
    (hbarV : chartPartialZComplex (fun y => star (v y)) z p = 0)
    (hbarX : chartPartialZComplex (fun y => star (x y)) z p = 0) :
    chartPartialZComplex
      (fun y => u y * star (v y) * w y * star (x y) * H (ψ y)) z p =
      chartPartialZComplex u z p * star (v z) * w z * star (x z) * H (ψ z) +
        u z * star (v z) * chartPartialZComplex w z p * star (x z) * H (ψ z) +
        ∑ t, (EuclideanSpace.clmMatrix (fderiv ℂ ψ z)) t p * u z * star (v z) * w z *
          star (x z) * chartPartialZComplex H (ψ z) t := by
  have hvstar : DifferentiableAt ℝ (fun y => star (v y)) z := by
    exact (Complex.conjCLE.hasFDerivAt.comp z hv.hasFDerivAt).differentiableAt
  have hxstar : DifferentiableAt ℝ (fun y => star (x y)) z := by
    exact (Complex.conjCLE.hasFDerivAt.comp z hx.hasFDerivAt).differentiableAt
  have hψR : DifferentiableAt ℝ ψ z :=
    hψ.hasFDerivAt.restrictScalars ℝ |>.differentiableAt
  have hcomp : DifferentiableAt ℝ (fun y => H (ψ y)) z :=
    (hH.hasFDerivAt.comp z hψR.hasFDerivAt).differentiableAt
  have h1 : DifferentiableAt ℝ (fun y => u y * star (v y)) z := hu.mul hvstar
  have h2 : DifferentiableAt ℝ (fun y => u y * star (v y) * w y) z := h1.mul hw
  have h3 : DifferentiableAt ℝ (fun y => u y * star (v y) * w y * star (x y)) z := h2.mul hxstar
  have hchain : chartPartialZComplex (fun y => H (ψ y)) z p =
      ∑ t, (EuclideanSpace.clmMatrix (fderiv ℂ ψ z)) t p *
        chartPartialZComplex H (ψ z) t :=
    auxiliary_chartPartialZ_comp_holomorphic H ψ z p hH hψ
  rw [chartPartialZComplex_mul h3 hcomp p,
    chartPartialZComplex_mul h2 hxstar p,
    chartPartialZComplex_mul h1 hw p,
    chartPartialZComplex_mul hu hvstar p,
    hbarV, hbarX, hchain]
  simp only [mul_zero, add_zero]
  rw [Finset.mul_sum]
  have hleft :
      (chartPartialZComplex u z p * star (v z) * w z +
        u z * star (v z) * chartPartialZComplex w z p) * star (x z) * H (ψ z) =
      chartPartialZComplex u z p * star (v z) * w z * star (x z) * H (ψ z) +
        u z * star (v z) * chartPartialZComplex w z p * star (x z) * H (ψ z) := by
    ring
  rw [hleft]
  apply congrArg (fun S : ℂ =>
    chartPartialZComplex u z p * star (v z) * w z * star (x z) * H (ψ z) +
      u z * star (v z) * chartPartialZComplex w z p * star (x z) * H (ψ z) + S)
  apply Finset.sum_congr rfl
  intro t ht
  ring

private theorem auxiliary_chartPartialZ_sum
    {n : ℕ} {ι : Type*} [Fintype ι]
    (F : ι → EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (p : Fin n)
    (hF : ∀ i, DifferentiableAt ℝ (F i) z) :
    chartPartialZComplex (fun w => ∑ i, F i w) z p =
      ∑ i, chartPartialZComplex (F i) z p := by
  unfold chartPartialZComplex
  have hfd : fderiv ℝ (fun w => ∑ i, F i w) z = ∑ i, fderiv ℝ (F i) z := by
    simpa using fderiv_fun_sum (u := Finset.univ) (fun i hi => hF i)
  rw [hfd]
  simp only [sum_apply]
  have hsum :
      (∑ i, fderiv ℝ (F i) z (EuclideanSpace.single p 1)) -
        Complex.I * ∑ i, fderiv ℝ (F i) z (Complex.I • EuclideanSpace.single p 1) =
      ∑ i, (fderiv ℝ (F i) z (EuclideanSpace.single p 1) -
        Complex.I * fderiv ℝ (F i) z (Complex.I • EuclideanSpace.single p 1)) := by
    rw [Finset.mul_sum, Finset.sum_sub_distrib]
  rw [hsum]
  simp only [div_eq_mul_inv, Finset.sum_mul]

private theorem auxiliary_chartPartialZ_sum4
    {n : ℕ} {ι κ μ ν : Type*} [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ν]
    (F : ι → κ → μ → ν → EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (p : Fin n)
    (hF : ∀ i j k l, DifferentiableAt ℝ (F i j k l) z) :
    chartPartialZComplex (fun w => ∑ i, ∑ j, ∑ k, ∑ l, F i j k l w) z p =
      ∑ i, ∑ j, ∑ k, ∑ l, chartPartialZComplex (F i j k l) z p := by
  have hL (i j k : _) : DifferentiableAt ℝ (fun w => ∑ l, F i j k l w) z := by
    have heq : (fun w => ∑ l, F i j k l w) = ∑ l, fun w => F i j k l w := by
      funext w
      simp
    rw [heq]
    exact DifferentiableAt.sum (u := Finset.univ) (fun l hl => hF i j k l)
  have hK (i j : _) : DifferentiableAt ℝ (fun w => ∑ k, ∑ l, F i j k l w) z := by
    have heq : (fun w => ∑ k, ∑ l, F i j k l w) = ∑ k, fun w => ∑ l, F i j k l w := by
      funext w
      simp
    rw [heq]
    exact DifferentiableAt.sum (u := Finset.univ) (fun k hk => hL i j k)
  have hJ (i : _) : DifferentiableAt ℝ (fun w => ∑ j, ∑ k, ∑ l, F i j k l w) z := by
    have heq : (fun w => ∑ j, ∑ k, ∑ l, F i j k l w) = ∑ j, fun w => ∑ k, ∑ l, F i j k l w := by
      funext w
      simp
    rw [heq]
    exact DifferentiableAt.sum (u := Finset.univ) (fun j hj => hK i j)
  have hI : DifferentiableAt ℝ (fun w => ∑ i, ∑ j, ∑ k, ∑ l, F i j k l w) z := by
    have heq : (fun w => ∑ i, ∑ j, ∑ k, ∑ l, F i j k l w) = ∑ i, fun w => ∑ j, ∑ k, ∑ l, F i j k l w := by
      funext w
      simp
    rw [heq]
    exact DifferentiableAt.sum (u := Finset.univ) (fun i hi => hJ i)
  have hsumI := auxiliary_chartPartialZ_sum
    (fun i w => ∑ j, ∑ k, ∑ l, F i j k l w) z p hJ
  have hsumJ (i : ι) := auxiliary_chartPartialZ_sum
    (fun j w => ∑ k, ∑ l, F i j k l w) z p (fun j => hK i j)
  have hsumK (i : ι) (j : κ) := auxiliary_chartPartialZ_sum
    (fun k w => ∑ l, F i j k l w) z p (fun k => hL i j k)
  have hsumL (i : ι) (j : κ) (k : μ) := auxiliary_chartPartialZ_sum
    (fun l w => F i j k l w) z p (fun l => hF i j k l)
  rw [hsumI]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hsumJ i]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hsumK i j]
  apply Finset.sum_congr rfl
  intro k hk
  exact hsumL i j k

private theorem auxiliary_sum4_add
    {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (F G : α → β → γ → δ → ℂ) :
    Finset.univ.sum (fun a : α => Finset.univ.sum (fun b : β =>
      Finset.univ.sum (fun c : γ => Finset.univ.sum (fun d : δ => F a b c d + G a b c d)))) =
      Finset.univ.sum (fun a : α => Finset.univ.sum (fun b : β =>
        Finset.univ.sum (fun c : γ => Finset.univ.sum (fun d : δ => F a b c d)))) +
      Finset.univ.sum (fun a : α => Finset.univ.sum (fun b : β =>
        Finset.univ.sum (fun c : γ => Finset.univ.sum (fun d : δ => G a b c d)))) := by
  calc
    _ = Finset.univ.sum (fun a : α => Finset.univ.sum (fun b : β =>
        Finset.univ.sum (fun c : γ =>
          (Finset.univ.sum (fun d : δ => F a b c d) +
            Finset.univ.sum (fun d : δ => G a b c d))))) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      exact Finset.sum_add_distrib
    _ = Finset.univ.sum (fun a : α => Finset.univ.sum (fun b : β =>
        (Finset.univ.sum (fun c : γ => Finset.univ.sum (fun d : δ => F a b c d)) +
          Finset.univ.sum (fun c : γ => Finset.univ.sum (fun d : δ => G a b c d))))) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact Finset.sum_add_distrib
    _ = Finset.univ.sum (fun a : α =>
        (Finset.univ.sum (fun b : β => Finset.univ.sum (fun c : γ =>
          Finset.univ.sum (fun d : δ => F a b c d))) +
          Finset.univ.sum (fun b : β => Finset.univ.sum (fun c : γ =>
            Finset.univ.sum (fun d : δ => G a b c d))))) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_add_distrib
    _ = _ := Finset.sum_add_distrib

private theorem auxiliary_sum_abcdt_comm
    {α β γ δ ε : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [Fintype ε]
    (T : α → β → γ → δ → ε → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ t, T a b c d t) =
      ∑ t, ∑ a, ∑ b, ∑ c, ∑ d, T a b c d t := by
  calc
    _ = ∑ a, ∑ b, ∑ c, ∑ t, ∑ d, T a b c d t := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      exact Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ t, ∑ c, ∑ d, T a b c d t := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact Finset.sum_comm
    _ = ∑ a, ∑ t, ∑ b, ∑ c, ∑ d, T a b c d t := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = ∑ t, ∑ a, ∑ b, ∑ c, ∑ d, T a b c d t := Finset.sum_comm

/-- First holomorphic derivative of the actual metric-curvature pullback.
The assumptions are exactly the closed curvature pullback API, so the assembly
adds no extra chart regularity or globally smooth extension assumption. -/
theorem c3_curvature_pullback_first_jet {n : ℕ}
    (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (f : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (hf : ContDiffOn ℝ ∞ f U) (hhol : DifferentiableOn ℂ f U)
    (g g' : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (hg' : ∀ j k, ContDiffOn ℝ ∞ (fun w => g' w j k) (f '' U))
    (hmetric : ∀ w ∈ U,
      g w = Matrix.transpose (EuclideanSpace.clmMatrix (fderiv ℂ f w)) *
        g' (f w) * (EuclideanSpace.clmMatrix (fderiv ℂ f w)).map star)
    (hkahler : ∀ w ∈ f '' U, ∀ i j k,
      chartPartialZComplex (fun v => g' v j k) w i =
        chartPartialZComplex (fun v => g' v i k) w j)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U)
    (hjac : IsUnit (EuclideanSpace.clmMatrix (fderiv ℂ f z)).det)
    (hgdet : IsUnit (g' (f z)).det) :
    (fun s p q j k => chartPartialZComplex (fun w => chartCurvature g w p q j k) z s) =
      c3FourSlotPullbackZJet (EuclideanSpace.clmMatrix (fderiv ℂ f z))
        (fun s a p => chartPartialZComplex
          (fun w => (EuclideanSpace.clmMatrix (fderiv ℂ f w)) a p) z s)
        (chartCurvature g' (f z))
        (fun s p q j k => chartPartialZComplex
          (fun w => chartCurvature g' w p q j k) (f z) s) := by
  classical
  funext s p q j k
  let A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w => EuclideanSpace.clmMatrix (fderiv ℂ f w)
  let S : Fin n → Fin n → Fin n → Fin n →
      EuclideanSpace ℂ (Fin n) → ℂ := fun a b c d w =>
    A w a p * star (A w b q) * A w c j * star (A w d k) *
      chartCurvature g' (f w) a b c d
  have hdomains := auxiliary_detDomains_eventually U hU f hf hhol g' hg' z hz hjac hgdet
  have hevent := auxiliary_curvature_pullback_eventuallyEq U hU f hf hhol g g' hg' hmetric
    hkahler z hz (Filter.Eventually.mono hdomains (fun w hw => hw.2.1))
    (Filter.Eventually.mono hdomains (fun w hw => hw.2.2)) p q j k
  have hpartial :
      chartPartialZComplex (fun w => chartCurvature g w p q j k) z s =
        chartPartialZComplex (fun w => ∑ a, ∑ b, ∑ c, ∑ d, S a b c d w) z s := by
    unfold chartPartialZComplex
    rw [hevent.fderiv_eq (𝕜 := ℝ)]
  have hAreg (a b : Fin n) : ContDiffAt ℝ ∞ (fun w => A w a b) z :=
    chart_pullback_jacobian_entry_contDiffAt U hU f hf hhol z hz a b
  have hAreal (a b : Fin n) : DifferentiableAt ℝ (fun w => A w a b) z :=
    (hAreg a b).differentiableAt (by norm_num)
  have hAstar (a b : Fin n) : DifferentiableAt ℝ (fun w => star (A w a b)) z := by
    exact (Complex.conjCLE.hasFDerivAt.comp z (hAreal a b).hasFDerivAt).differentiableAt
  have hbarA (a b t : Fin n) :
      chartPartialBarComplex (fun w => A w a b) z t = 0 :=
    auxiliary_chartPartialBar_jacobian_zero U hU f hf hhol z hz a b t
  have hstarJet (a b t : Fin n) :
      chartPartialZComplex (fun w => star (A w a b)) z t = 0 := by
    rw [auxiliary_chartPartialZ_star_eq_star_bar (fun w => A w a b) z t (hAreal a b)]
    simpa using congrArg star (hbarA a b t)
  have hFhol : DifferentiableAt ℂ f z :=
    (hhol z hz).differentiableAt (hU.mem_nhds hz)
  have hRreal (a b c d : Fin n) :
      DifferentiableAt ℝ (fun w => chartCurvature g' w a b c d) (f z) :=
    auxiliary_targetCurvature_differentiableAt_pullback U hU f hf hhol g' hg' z hz
      hjac hgdet a b c d
  have hRcomp (a b c d : Fin n) :
      DifferentiableAt ℝ (fun w => chartCurvature g' (f w) a b c d) z :=
    (hRreal a b c d).comp z
      ((hf.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num))
  have hSdiff (a b c d : Fin n) : DifferentiableAt ℝ (S a b c d) z := by
    dsimp [S]
    exact ((((hAreal a p).mul (hAstar b q)).mul (hAreal c j)).mul
      (hAstar d k)).mul (hRcomp a b c d)
  have hSjet (a b c d : Fin n) :
      chartPartialZComplex (S a b c d) z s =
        chartPartialZComplex (fun w => A w a p) z s * star (A z b q) *
            A z c j * star (A z d k) * chartCurvature g' (f z) a b c d +
          A z a p * star (A z b q) * chartPartialZComplex (fun w => A w c j) z s *
            star (A z d k) * chartCurvature g' (f z) a b c d +
          ∑ t, A z t s * A z a p * star (A z b q) * A z c j * star (A z d k) *
            chartPartialZComplex (fun w => chartCurvature g' w a b c d) (f z) t := by
    exact auxiliary_five_factor_pullback_firstJet
      (fun w => A w a p) (fun w => A w b q) (fun w => A w c j) (fun w => A w d k)
      (fun y => chartCurvature g' y a b c d) f z s
      (hAreal a p) (hAreal b q) (hAreal c j) (hAreal d k)
      (hRreal a b c d) hFhol (hstarJet b q s) (hstarJet d k s)
  have hsumJet :
      chartPartialZComplex (fun w => ∑ a, ∑ b, ∑ c, ∑ d, S a b c d w) z s =
        ∑ a, ∑ b, ∑ c, ∑ d, chartPartialZComplex (S a b c d) z s :=
    auxiliary_chartPartialZ_sum4 S z s hSdiff
  rw [hpartial, hsumJet]
  simp_rw [hSjet]
  delta c3FourSlotPullbackZJet
  dsimp
  simp only [starRingEnd_apply]
  let A0 : Matrix (Fin n) (Fin n) ℂ := EuclideanSpace.clmMatrix (fderiv ℂ f z)
  let dA : Fin n → Fin n → Fin n → ℂ := fun u a i =>
    chartPartialZComplex (fun w => EuclideanSpace.clmMatrix (fderiv ℂ f w) a i) z u
  let R0 : Fin n → Fin n → Fin n → Fin n → ℂ := chartCurvature g' (f z)
  let dR : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ := fun u a b c d =>
    chartPartialZComplex (fun w => chartCurvature g' w a b c d) (f z) u
  let P1 (a b c d : Fin n) : ℂ :=
    dA s a p * star (A0 b q) * A0 c j * star (A0 d k) * R0 a b c d
  let P2 (a b c d : Fin n) : ℂ :=
    A0 a p * star (A0 b q) * dA s c j * star (A0 d k) * R0 a b c d
  let Q (t a b c d : Fin n) : ℂ :=
    A0 t s * A0 a p * star (A0 b q) * A0 c j * star (A0 d k) * dR t a b c d
  change (∑ a, ∑ b, ∑ c, ∑ d,
      ((P1 a b c d + P2 a b c d) + ∑ t, Q t a b c d)) =
    (∑ a, ∑ b, ∑ c, ∑ d,
      ((dA s a p * star (A0 b q) * A0 c j * star (A0 d k) +
        A0 a p * star (A0 b q) * dA s c j * star (A0 d k)) * R0 a b c d)) +
      ∑ t, ∑ a, ∑ b, ∑ c, ∑ d, Q t a b c d
  have hdistrib : (∑ a, ∑ b, ∑ c, ∑ d,
      ((P1 a b c d + P2 a b c d) + ∑ t, Q t a b c d)) =
      (∑ a, ∑ b, ∑ c, ∑ d, (P1 a b c d + P2 a b c d)) +
        ∑ a, ∑ b, ∑ c, ∑ d, ∑ t, Q t a b c d := by
    exact auxiliary_sum4_add (fun a b c d => P1 a b c d + P2 a b c d)
      (fun a b c d => ∑ t, Q t a b c d)
  have hfirst : (∑ a, ∑ b, ∑ c, ∑ d, (P1 a b c d + P2 a b c d)) =
      ∑ a, ∑ b, ∑ c, ∑ d,
        ((dA s a p * star (A0 b q) * A0 c j * star (A0 d k) +
          A0 a p * star (A0 b q) * dA s c j * star (A0 d k)) * R0 a b c d) := by
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro d hd
    dsimp [P1, P2]
    ring
  have hchain : (∑ a, ∑ b, ∑ c, ∑ d, ∑ t, Q t a b c d) =
      ∑ t, ∑ a, ∑ b, ∑ c, ∑ d, Q t a b c d :=
    auxiliary_sum_abcdt_comm (fun a b c d t => Q t a b c d)
  calc
    _ = (∑ a, ∑ b, ∑ c, ∑ d, (P1 a b c d + P2 a b c d)) +
        ∑ a, ∑ b, ∑ c, ∑ d, ∑ t, Q t a b c d := hdistrib
    _ = (∑ a, ∑ b, ∑ c, ∑ d,
        ((dA s a p * star (A0 b q) * A0 c j * star (A0 d k) +
          A0 a p * star (A0 b q) * dA s c j * star (A0 d k)) * R0 a b c d)) +
        ∑ a, ∑ b, ∑ c, ∑ d, ∑ t, Q t a b c d := by rw [hfirst]
    _ = _ := by rw [hchain]

end KahlerForm
