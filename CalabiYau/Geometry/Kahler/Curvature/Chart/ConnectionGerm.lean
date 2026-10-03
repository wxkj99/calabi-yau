module

public import CalabiYau.Geometry.Kahler.Curvature.Chart.Basic
import CalabiYau.Geometry.Kahler.Connection.Transition

/-!
# The local connection germ under a holomorphic coordinate change

Shrink the source to an open neighborhood with nonsingular Jacobian and metric.
Its image is open by the local inverse function theorem, so the existing point
Christoffel law applies at every nearby point. No global image openness or
smooth extension is required. Székelyhidi, §1.4, pp.10–11 (connection product
rule), and §3.3, proof of Lemma 3.9, PDF p.48 (book p.45).
-/

public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder

namespace KahlerForm

variable {n : ℕ}

private theorem clm_equiv_of_matrix_det
    (L : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hdet : IsUnit (EuclideanSpace.clmMatrix L).det) :
    ∃ e : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n),
      e.toContinuousLinearMap = L := by
  let b : Module.Basis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)) :=
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
  let e : EuclideanSpace ℂ (Fin n) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
    Matrix.toLinearEquiv b (EuclideanSpace.clmMatrix L) hdet
  have hmatrix : LinearMap.toMatrix b b L.toLinearMap = EuclideanSpace.clmMatrix L := by
    ext i j
    simp [EuclideanSpace.clmMatrix, LinearMap.toMatrix_apply, b]
  have he : e.toLinearMap = L.toLinearMap := by
    apply (LinearMap.toMatrix b b).injective
    change LinearMap.toMatrix b b (Matrix.toLin b b (EuclideanSpace.clmMatrix L)) =
      LinearMap.toMatrix b b L.toLinearMap
    rw [LinearMap.toMatrix_toLin]
    exact hmatrix.symm
  refine ⟨e.toContinuousLinearEquiv, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  exact congrArg (fun F : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) => F x) he

theorem chart_pullback_image_nhds
    (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (f : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (hf : ContDiffOn ℝ ∞ f U) (hhol : DifferentiableOn ℂ f U)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U)
    (hjac : IsUnit (EuclideanSpace.clmMatrix (fderiv ℂ f z)).det) :
    f '' U ∈ nhds (f z) := by
  let L := fderiv ℂ f z
  have hfw : DifferentiableAt ℂ f z := (hhol z hz).differentiableAt (hU.mem_nhds hz)
  have hreal : fderiv ℝ f z = L.restrictScalars ℝ := by
    simpa [L] using hfw.fderiv_restrictScalars ℝ
  obtain ⟨eC, heC⟩ := clm_equiv_of_matrix_det L hjac
  let eR : EuclideanSpace ℂ (Fin n) ≃L[ℝ] EuclideanSpace ℂ (Fin n) :=
    eC.restrictScalars ℝ
  have heR : (eR : EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n)) =
      (fderiv ℝ f z) := by
    rw [hreal]
    change (eC.toContinuousLinearMap.restrictScalars ℝ) = L.restrictScalars ℝ
    rw [heC]
  have hderivEvent : ∀ᶠ w in nhds z, HasFDerivAt f (fderiv ℝ f w) w := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact (((hf w hw).contDiffAt (hU.mem_nhds hw)).differentiableAt (by norm_num)).hasFDerivAt
  have hcont : ContinuousAt (fderiv ℝ f) z :=
    (hf.continuousOn_fderiv_of_isOpen hU (by simp) z hz).continuousAt (hU.mem_nhds hz)
  have hstrict : HasStrictFDerivAt f (fderiv ℝ f z) z :=
    hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt hderivEvent hcont
  have hstrictR : HasStrictFDerivAt f (eR : EuclideanSpace ℂ (Fin n) →L[ℝ]
      EuclideanSpace ℂ (Fin n)) z := by
    rw [heR]
    exact hstrict
  let φ := hstrictR.toOpenPartialHomeomorph f
  let e := φ.restrOpen U hU
  have hsource : z ∈ e.source := by
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hstrictR.mem_toOpenPartialHomeomorph_source, hz⟩
  have htarget : f z ∈ e.target := by
    have := e.map_source hsource
    simpa [e, φ] using this
  have heq : (e : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)) = f := by
    ext w
    simp [e, φ]
  have himage : e.target ⊆ f '' U := by
    intro y hy
    have hsymm := e.map_target hy
    refine ⟨e.symm y, ?_, ?_⟩
    · exact hsymm.2
    · have hright := e.right_inv hy
      rw [heq] at hright
      exact hright
  exact Filter.mem_of_superset (e.open_target.mem_nhds htarget) himage

theorem chart_pullback_jacobian_entry_contDiffAt
    (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (f : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (hf : ContDiffOn ℝ ∞ f U) (hhol : DifferentiableOn ℂ f U)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U) (a j : Fin n) :
    ContDiffAt ℝ ∞ (fun w => (EuclideanSpace.clmMatrix (fderiv ℂ f w)) a j) z := by
  let e : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j 1
  let F : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) :=
    fun w => fderiv ℝ f w e
  have hfz : ContDiffAt ℝ ∞ f z := (hf z hz).contDiffAt (hU.mem_nhds hz)
  have hfd : ContDiffAt ℝ ∞ (fderiv ℝ f) z := hfz.fderiv_right (by simp)
  have hF : ContDiffAt ℝ ∞ F z := by
    dsimp [F]
    fun_prop (disch := assumption)
  have hraw : ContDiffAt ℝ ∞ (fun w => F w a) z := by
    fun_prop (disch := assumption)
  have hEq : (fun w => (EuclideanSpace.clmMatrix (fderiv ℂ f w)) a j) =ᶠ[nhds z]
      fun w => F w a := by
    filter_upwards [hU.mem_nhds hz] with w hw
    have hfw : DifferentiableAt ℂ f w := (hhol w hw).differentiableAt (hU.mem_nhds hw)
    have hreal : fderiv ℝ f w = (fderiv ℂ f w).restrictScalars ℝ :=
      hfw.fderiv_restrictScalars ℝ
    simp [F, e, EuclideanSpace.clmMatrix, hreal]
  exact hraw.congr_of_eventuallyEq hEq

private theorem chart_connection_local_domains
    (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (f : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (hf : ContDiffOn ℝ ∞ f U) (hhol : DifferentiableOn ℂ f U)
    (g' : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (hg' : ∀ a b, ContDiffOn ℝ ∞ (fun w => g' w a b) (f '' U))
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U)
    (hjac : IsUnit (EuclideanSpace.clmMatrix (fderiv ℂ f z)).det)
    (hgdet : IsUnit (g' (f z)).det) :
    ∃ W V : Set (EuclideanSpace ℂ (Fin n)),
      IsOpen W ∧ IsOpen V ∧ z ∈ W ∧ W ⊆ U ∧ f '' W = V ∧ V ⊆ f '' U ∧
      (∀ w ∈ W, IsUnit (EuclideanSpace.clmMatrix (fderiv ℂ f w)).det) ∧
      (∀ w ∈ W, IsUnit (g' (f w)).det) := by
  classical
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
  have hset : {w | w ∈ U ∧ IsUnit (A w).det ∧ IsUnit (g' (f w)).det} ∈ nhds z := by
    filter_upwards [hU.mem_nhds hz, hAunit, hGunit] with w hw ha hg
    exact ⟨hw, ha, hg⟩
  obtain ⟨W, hWsub, hWopen, hzW⟩ := mem_nhds_iff.mp hset
  have hWU : W ⊆ U := fun w hw => (hWsub hw).1
  have hWjac (w : EuclideanSpace ℂ (Fin n)) (hw : w ∈ W) : IsUnit (A w).det :=
    (hWsub hw).2.1
  have hWmetric (w : EuclideanSpace ℂ (Fin n)) (hw : w ∈ W) :
      IsUnit (g' (f w)).det := (hWsub hw).2.2
  have hVopen : IsOpen (f '' W) := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨w, hw, rfl⟩
    exact chart_pullback_image_nhds W hWopen f (hf.mono hWU) (hhol.mono hWU)
      w hw (hWjac w hw)
  refine ⟨W, f '' W, hWopen, hVopen, hzW, hWU, rfl, ?_, hWjac, hWmetric⟩
  exact Set.image_mono hWU

/-- Finite-order compatibility of real smoothness and local complex differentiability.
This is the remaining regularity bridge, not an additional root hypothesis.
A finite-order proof may use symmetry of the second real derivative and complex
linearity of the first derivative; no multivariable analytic-infinity API is assumed. -/
private theorem chart_real_smooth_holomorphic_contDiffOn_two
    (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (f : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (hf : ContDiffOn ℝ ∞ f U) (hhol : DifferentiableOn ℂ f U) :
    ContDiffOn ℂ 2 f U := by
  classical
  let E := EuclideanSpace ℂ (Fin n)
  let A : E → E →L[ℝ] E := fderiv ℝ f
  let complexifyRealCLM : (L : E →L[ℝ] E) →
      (∀ v, L (Complex.I • v) = Complex.I • L v) → E →L[ℂ] E :=
    fun L hL => by
    let Lc : E →ₗ[ℂ] E := {
      toFun := L
      map_add' := L.map_add
      map_smul' := by
        intro c v
        have hv : c • v = (c.re : ℝ) • v + (c.im : ℝ) • (Complex.I • v) := by
          calc
            c • v = ((c.re : ℂ) + (c.im : ℂ) * Complex.I) • v := by
              conv_lhs => rw [← Complex.re_add_im c]
            _ = (c.re : ℂ) • v + (c.im : ℂ) • (Complex.I • v) := by
              rw [add_smul, ← smul_eq_mul _ Complex.I, smul_assoc]
            _ = (c.re : ℝ) • v + (c.im : ℝ) • (Complex.I • v) := by
              rw [← IsScalarTower.algebraMap_smul (R := ℝ) (A := ℂ) (M := E) (c.re) v,
                ← IsScalarTower.algebraMap_smul (R := ℝ) (A := ℂ) (M := E) (c.im) (Complex.I • v)]
              simp only [← Complex.coe_algebraMap]
        rw [hv, L.map_add, L.map_smul, L.map_smul, hL]
        have hy : c • L v = (c.re : ℝ) • L v + (c.im : ℝ) • (Complex.I • L v) := by
          calc
            c • L v = ((c.re : ℂ) + (c.im : ℂ) * Complex.I) • L v := by
              conv_lhs => rw [← Complex.re_add_im c]
            _ = (c.re : ℂ) • L v + (c.im : ℂ) • (Complex.I • L v) := by
              rw [add_smul, ← smul_eq_mul _ Complex.I, smul_assoc]
            _ = (c.re : ℝ) • L v + (c.im : ℝ) • (Complex.I • L v) := by
              rw [← IsScalarTower.algebraMap_smul (R := ℝ) (A := ℂ) (M := E) (c.re) (L v),
                ← IsScalarTower.algebraMap_smul (R := ℝ) (A := ℂ) (M := E) (c.im) (Complex.I • L v)]
              simp only [← Complex.coe_algebraMap]
        rw [← hy]
        rfl
    }
    exact ⟨Lc, L.continuous⟩
  have fderiv_real_map_complex_linear (x : E) (hx : x ∈ U) (v : E) :
      fderiv ℝ f x (Complex.I • v) = Complex.I • fderiv ℝ f x v := by
    have hcx : DifferentiableAt ℂ f x := hhol x hx |>.differentiableAt (hU.mem_nhds hx)
    rw [hcx.fderiv_restrictScalars ℝ]
    change fderiv ℂ f x (Complex.I • v) = Complex.I • fderiv ℂ f x v
    exact map_smul (fderiv ℂ f x) Complex.I v
  have hA : ContDiffOn ℝ ∞ A U := by
    simpa [A] using hf.fderiv_of_isOpen hU (by simp)
  have real_hessian_symmetric (x : E) (hx : x ∈ U) (v w : E) :
      fderiv ℝ A x v w = fderiv ℝ A x w v := by
    have hA' : HasFDerivAt A (fderiv ℝ A x) x := by
      exact ((hA x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num) |>.hasFDerivAt
    have hF : ∀ᶠ y in nhds x, HasFDerivAt f (fderiv ℝ f y) y := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact (((hf y hy).contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)).hasFDerivAt
    exact second_derivative_symmetric_of_eventually hF hA' v w
  have real_hessian_complex_linear_second (x : E) (hx : x ∈ U) (h v : E) :
      fderiv ℝ A x h (Complex.I • v) = Complex.I • fderiv ℝ A x h v := by
    let H : E →L[ℝ] E →L[ℝ] E := fderiv ℝ A x
    let Iop : E →L[ℝ] E := (Complex.I : ℂ) • ContinuousLinearMap.id ℂ E |>.restrictScalars ℝ
    have hA' : HasFDerivAt A H x := by
      simpa [A, H] using ((hA x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num) |>.hasFDerivAt
    let evv : (E →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E v
    let evi : (E →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E (Complex.I • v)
    have hEq : (fun y => A y (Complex.I • v)) =ᶠ[nhds x] (fun y => Iop (A y v)) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      have hlin := fderiv_real_map_complex_linear y hy v
      simpa [A, Iop] using hlin
    have hleft : HasFDerivAt (fun y => A y (Complex.I • v)) (evi.comp H) x := by
      change HasFDerivAt (evi ∘ A) (evi.comp H) x
      exact evi.hasFDerivAt.comp x hA'
    have hright : HasFDerivAt (fun y => Iop (A y v)) (Iop.comp (evv.comp H)) x := by
      change HasFDerivAt (Iop ∘ evv ∘ A) (Iop.comp (evv.comp H)) x
      exact Iop.hasFDerivAt.comp x (evv.hasFDerivAt.comp x hA')
    have hright' := hright.congr_of_eventuallyEq hEq
    have heq := hleft.unique hright'
    have heval := congrArg (fun L : E →L[ℝ] E => L h) heq
    simpa [H, Iop, ContinuousLinearMap.comp_apply, evv, evi] using heval
  have real_hessian_complex_linear_first (x : E) (hx : x ∈ U) (h v : E) :
      fderiv ℝ A x (Complex.I • h) v = Complex.I • fderiv ℝ A x h v := by
    calc
      fderiv ℝ A x (Complex.I • h) v = fderiv ℝ A x v (Complex.I • h) :=
        real_hessian_symmetric x hx (Complex.I • h) v
      _ = Complex.I • fderiv ℝ A x v h := real_hessian_complex_linear_second x hx v h
      _ = Complex.I • fderiv ℝ A x h v := by
        rw [real_hessian_symmetric x hx h v]
  have real_hessian_bundle_complex (x : E) (hx : x ∈ U) :
      ∃ Hc : E →L[ℂ] E →L[ℂ] E, ∀ h v, Hc h v = fderiv ℝ A x h v := by
    let H : E →L[ℝ] E →L[ℝ] E := fderiv ℝ A x
    let HcL : E →ₗ[ℂ] (E →L[ℂ] E) := {
      toFun := fun h => complexifyRealCLM (H h) (fun v =>
        real_hessian_complex_linear_second x hx h v)
      map_add' := by
        intro h₁ h₂
        apply ContinuousLinearMap.ext
        intro v
        change H (h₁ + h₂) v = H h₁ v + H h₂ v
        simp
      map_smul' := by
        intro c h
        apply ContinuousLinearMap.ext
        intro v
        let ev : (E →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E v
        let Lh : E →L[ℝ] E := ev.comp H
        have hLh (w : E) : Lh (Complex.I • w) = Complex.I • Lh w := by
          change H (Complex.I • w) v = Complex.I • H w v
          exact real_hessian_complex_linear_first x hx w v
        have hsmul := (complexifyRealCLM Lh hLh).map_smul c h
        change H (c • h) v = c • H h v
        exact hsmul
    }
    let Hc : E →L[ℂ] (E →L[ℂ] E) :=
      ⟨HcL, HcL.continuous_of_finiteDimensional⟩
    refine ⟨Hc, ?_⟩
    intro h v
    rfl
  have complex_fderiv_hasFDerivAt (x : E) (hx : x ∈ U) :
      ∃ Hc : E →L[ℂ] E →L[ℂ] E,
        (∀ h v, Hc h v = fderiv ℝ A x h v) ∧
        HasFDerivAt (fderiv ℂ f) Hc x := by
    let H : E →L[ℝ] E →L[ℝ] E := fderiv ℝ A x
    obtain ⟨Hc, hHc⟩ := real_hessian_bundle_complex x hx
    let R : (E →L[ℂ] E) →ₗᵢ[ℝ] (E →L[ℝ] E) := {
      toFun := fun L => L.restrictScalars ℝ
      map_add' := by intro L₁ L₂; ext v; rfl
      map_smul' := by intro c L; ext v; rfl
      norm_map' := fun L => ContinuousLinearMap.norm_restrictScalars L
    }
    let Rc : (E →L[ℂ] E) →L[ℝ] (E →L[ℝ] E) := R.toContinuousLinearMap
    let HcR : E →L[ℝ] (E →L[ℂ] E) := Hc.restrictScalars ℝ
    have hR (y : E) (hy : y ∈ U) : Rc (fderiv ℂ f y) = A y := by
      simpa [Rc, R, A] using
        ((hhol y hy).differentiableAt (hU.mem_nhds hy)).fderiv_restrictScalars ℝ |>.symm
    have hRH : Rc.comp HcR = H := by
      apply ContinuousLinearMap.ext
      intro v
      apply ContinuousLinearMap.ext
      intro w
      change Hc v w = H v w
      exact hHc v w
    have hA' : HasFDerivAt A H x := by
      simpa [A, H] using ((hA x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num) |>.hasFDerivAt
    have hres : (fun y => ‖fderiv ℂ f y - fderiv ℂ f x - HcR (y - x)‖) =ᶠ[nhds x]
        fun y => ‖A y - A x - H (y - x)‖ := by
      filter_upwards [hU.mem_nhds hx] with y hy
      have heq : Rc (fderiv ℂ f y - fderiv ℂ f x - HcR (y - x)) =
          A y - A x - H (y - x) := by
        simp only [map_sub, hR y hy, hR x hx]
        rw [← hRH]
        rfl
      calc
        ‖fderiv ℂ f y - fderiv ℂ f x - HcR (y - x)‖ =
            ‖Rc (fderiv ℂ f y - fderiv ℂ f x - HcR (y - x))‖ := by
              simpa [Rc] using (R.norm_map
                (fderiv ℂ f y - fderiv ℂ f x - HcR (y - x))).symm
        _ = ‖A y - A x - H (y - x)‖ := congrArg norm heq
    have hlittle : (fun y => ‖A y - A x - H (y - x)‖) =o[nhds x] (fun y => y - x) :=
      hA'.isLittleO.norm_left
    have hlittle' := hlittle.congr' hres.symm (by rfl)
    have hG : HasFDerivAt (fderiv ℂ f) HcR x := by
      rw [hasFDerivAt_iff_isLittleO]
      exact hlittle'.of_norm_left
    have hGcomplex : HasFDerivAt (fderiv ℂ f) Hc x :=
      hasFDerivAt_of_restrictScalars ℝ hG rfl
    exact ⟨Hc, hHc, hGcomplex⟩
  let R : (E →L[ℂ] E) →ₗᵢ[ℝ] (E →L[ℝ] E) := {
    toFun := fun L => L.restrictScalars ℝ
    map_add' := by intro L₁ L₂; ext v; rfl
    map_smul' := by intro c L; ext v; rfl
    norm_map' := fun L => ContinuousLinearMap.norm_restrictScalars L
  }
  let S : (E →L[ℂ] (E →L[ℂ] E)) →ₗᵢ[ℝ] (E →L[ℝ] (E →L[ℂ] E)) := {
    toFun := fun L => L.restrictScalars ℝ
    map_add' := by intro L₁ L₂; ext v; rfl
    map_smul' := by intro c L; ext v; rfl
    norm_map' := fun L => ContinuousLinearMap.norm_restrictScalars L
  }
  let Q : (E →L[ℂ] (E →L[ℂ] E)) → (E →L[ℝ] (E →L[ℝ] E)) :=
    fun L => R.toContinuousLinearMap.comp (S L)
  have norm_postcomp_linearIsometry (L : E →L[ℝ] (E →L[ℂ] E)) :
      ‖R.toContinuousLinearMap.comp L‖ = ‖L‖ := by
    apply le_antisymm
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro x
      calc
        ‖R.toContinuousLinearMap (L x)‖ = ‖L x‖ := R.norm_map _
        _ ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro x
      calc
        ‖L x‖ = ‖R.toContinuousLinearMap (L x)‖ := (R.norm_map _).symm
        _ = ‖R.toContinuousLinearMap.comp L x‖ := rfl
        _ ≤ ‖R.toContinuousLinearMap.comp L‖ * ‖x‖ :=
          (R.toContinuousLinearMap.comp L).le_opNorm x
  have isometry_postcomp_linearIsometry :
      Isometry (fun L : E →L[ℝ] (E →L[ℂ] E) => R.toContinuousLinearMap.comp L) := by
    intro L₁ L₂
    rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm]
    congr 1
  have hQ : Isometry Q := by
    intro L₁ L₂
    change edist (R.toContinuousLinearMap.comp (S L₁))
      (R.toContinuousLinearMap.comp (S L₂)) = edist L₁ L₂
    calc
      edist (R.toContinuousLinearMap.comp (S L₁))
          (R.toContinuousLinearMap.comp (S L₂)) = edist (S L₁) (S L₂) :=
        isometry_postcomp_linearIsometry.edist_eq _ _
      _ = edist L₁ L₂ := S.isometry.edist_eq _ _
  let Hcf : E → (E →L[ℂ] (E →L[ℂ] E)) := fun z =>
    if hz : z ∈ U then Classical.choose (real_hessian_bundle_complex z hz) else 0
  let Hreal : E → E →L[ℝ] E →L[ℝ] E := fun z => fderiv ℝ A z
  have hHcf (z : E) (hz : z ∈ U) (v w : E) : Hcf z v w = Hreal z v w := by
    simp only [Hcf, dite_eq_left hz, Hreal]
    exact Classical.choose_spec (real_hessian_bundle_complex z hz) v w
  have hHreal : ContinuousOn Hreal U := by
    simpa [Hreal, A] using hA.continuousOn_fderiv_of_isOpen hU (by simp)
  have hQH : ContinuousOn (fun z => Q (Hcf z)) U := by
    refine ContinuousOn.congr hHreal ?_
    intro z hz
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    change Hcf z v w = Hreal z v w
    exact hHcf z hz v w
  have hHcf_cont : ContinuousOn Hcf U := hQ.comp_continuousOn_iff.mp hQH
  have hsecond : ContinuousOn (fun z => fderiv ℂ (fderiv ℂ f) z) U := by
    refine ContinuousOn.congr hHcf_cont ?_
    intro z hz
    obtain ⟨Hc, hHc, hderiv⟩ := complex_fderiv_hasFDerivAt z hz
    have hEq : fderiv ℂ (fderiv ℂ f) z = Hcf z := by
      calc
        fderiv ℂ (fderiv ℂ f) z = Hc := hderiv.fderiv
        _ = Hcf z := by
          apply ContinuousLinearMap.ext
          intro v
          apply ContinuousLinearMap.ext
          intro w
          rw [hHc v w, hHcf z hz v w]
    exact hEq
  have hgDiff : DifferentiableOn ℂ (fderiv ℂ f) U := by
    intro z hz
    obtain ⟨Hc, hHc, hderiv⟩ := complex_fderiv_hasFDerivAt z hz
    exact hderiv.differentiableAt.differentiableWithinAt
  have hgC1' : ContDiffOn ℂ (0 + 1) (fderiv ℂ f) U := by
    rw [contDiffOn_succ_iff_fderiv_of_isOpen (n := 0) hU]
    refine ⟨hgDiff, ?_, contDiffOn_zero.mpr hsecond⟩
    intro h
    norm_num at h
  have hgC1 : ContDiffOn ℂ 1 (fderiv ℂ f) U := by
    norm_num at hgC1' ⊢
    exact hgC1'
  have hfC2 : ContDiffOn ℂ (1 + 1) f U := by
    rw [contDiffOn_succ_iff_fderiv_of_isOpen (n := 1) hU]
    refine ⟨hhol, ?_, hgC1⟩
    intro h
    norm_num at h
  norm_num at hfC2 ⊢
  exact hfC2

/-- The actual connection functions agree near `z` with the nonlinear transformed
connection expression. All smoothness and holomorphicity assumptions are local.
The forward Jacobian occupies both input slots, its inverse the output slot,
and the inhomogeneous Jacobian-derivative correction has a plus sign. -/
theorem chartChristoffel_pullback_eventuallyEq
    (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (f : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (hf : ContDiffOn ℝ ∞ f U) (hhol : DifferentiableOn ℂ f U)
    (g g' : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (hg' : ∀ a b, ContDiffOn ℝ ∞ (fun w => g' w a b) (f '' U))
    (hmetric : ∀ w ∈ U, g w =
      (EuclideanSpace.clmMatrix (fderiv ℂ f w)).transpose * g' (f w) *
        (EuclideanSpace.clmMatrix (fderiv ℂ f w)).map star)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U)
    (hjac : IsUnit (EuclideanSpace.clmMatrix (fderiv ℂ f z)).det)
    (hgdet : IsUnit (g' (f z)).det) (i j k : Fin n) :
    let A := fun w => EuclideanSpace.clmMatrix (fderiv ℂ f w)
    (fun w => ∑ l, (g w)⁻¹ l i * chartPartialZComplex (fun v => g v k l) w j) =ᶠ[nhds z]
      (fun w =>
        (∑ s, ∑ c, ∑ a, (A w)⁻¹ i s * A w c j * A w a k *
          (∑ l, (g' (f w))⁻¹ l s * chartPartialZComplex (fun v => g' v a l) (f w) c)) +
        ∑ s, (A w)⁻¹ i s * chartPartialZComplex (fun v => A v s k) w j) := by
  dsimp only
  obtain ⟨W, V, hWo, hVo, hzW, hWU, himage, hVsub, hJacW, hGdetW⟩ :=
    chart_connection_local_domains U hU f hf hhol g' hg' z hz hjac hgdet
  have hFC : ContDiffOn ℂ 2 f W :=
    (chart_real_smooth_holomorphic_contDiffOn_two U hU f hf hhol).mono hWU
  have hGV (a b : Fin n) : ContDiffOn ℝ 1 (fun w => g' w a b) V :=
    ((hg' a b).mono hVsub).of_le (by norm_num)
  have hmaps : Set.MapsTo f W V := by
    intro w hw
    rw [← himage]
    exact ⟨w, hw, rfl⟩
  filter_upwards [hWo.mem_nhds hzW] with w hw
  exact chartChristoffel_transition f g' g W V hWo hVo hFC hGV hmaps
    (fun v hv => hmetric v (hWU hv)) w hw
    (EuclideanSpace.clmMatrix (fderiv ℂ f w))⁻¹
    (Matrix.mul_nonsing_inv _ (hJacW w hw))
    (Matrix.nonsing_inv_mul _ (hJacW w hw)) (hGdetW w hw) i j k

end KahlerForm
