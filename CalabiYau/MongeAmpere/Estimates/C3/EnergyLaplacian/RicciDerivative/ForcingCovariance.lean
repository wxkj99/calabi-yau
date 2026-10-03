module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.Basic
public import CalabiYau.Geometry.Kahler.Curvature.ReferenceBound.TransitionFrame
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceCurvatureDerivative.ConnectionJet

/-!
# Transport the forcing Hessian and its covariant derivative

Székelyhidi, §1.4, pp. 10–12: covariant derivatives transform tensorially.
Use the actual nonlinear holomorphic chart overlap, not a constant Jacobian;
the connection correction cancels the differentiated Jacobian term.
-/

public section

open scoped Manifold ContDiff

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
open scoped ComplexOrder MatrixOrder
open ContinuousAlternatingMap
open Filter Topology

section

variable [T2Space M] [CompactSpace M]

private theorem c3_forcing_complexHessian_comp_holomorphic
    {n : ℕ} (u : EuclideanSpace ℂ (Fin n) → ℝ)
    (F : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    {z : EuclideanSpace ℂ (Fin n)}
    (hu : ContDiffAt ℝ 2 u (F z))
    (hF : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ F w) :
    complexHessian (u ∘ F) z =
      (EuclideanSpace.clmMatrix (fderiv ℂ F z)).transpose *
        complexHessian u (F z) * (EuclideanSpace.clmMatrix (fderiv ℂ F z)).map star := by
  have hcomp : ddbar (u ∘ F) z =
      (ddbar u (F z)).compContinuousLinearMap ((fderiv ℂ F z).restrictScalars ℝ) :=
    ddbar_comp_holomorphic hF hu
  rw [complexHessian, complexHessian, hcomp]
  exact (isOneOne_ddbar hu).coeffMatrix_compContinuousLinearMap (fderiv ℂ F z)

private theorem c3_forcing_complexHessian_eq_of_eventuallyEq {n : ℕ}
    (f g : EuclideanSpace ℂ (Fin n) → ℝ)
    (z : EuclideanSpace ℂ (Fin n)) (i j : Fin n)
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z)
    (heq : f =ᶠ[𝓝 z] g) : complexHessian f z i j = complexHessian g z i j := by
  obtain ⟨U, hUeq, hUopen, hzU⟩ := mem_nhds_iff.mp heq
  have hDerEq : fderiv ℝ f =ᶠ[𝓝 z] fderiv ℝ g := by
    filter_upwards [hUopen.mem_nhds hzU] with w hw
    have hEqW : f =ᶠ[𝓝 w] g := by
      filter_upwards [hUopen.mem_nhds hw] with y hy
      exact hUeq hy
    exact hEqW.fderiv_eq
  have hSecond : fderiv ℝ (fderiv ℝ f) z = fderiv ℝ (fderiv ℝ g) z :=
    hDerEq.fderiv_eq
  rw [complexHessian_apply hf i j, complexHessian_apply hg i j, hSecond]

end

private theorem c3_forcing_chartPotential_eventuallyEq
    (G : M → ℝ) (x y : M)
    (hy : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source) :
    let Cy := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y
    let Cx := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
    let F := referenceChartTransition (n := n) x y
    (fun w => G (Cy.symm w)) =ᶠ[𝓝 (Cy y)] (fun w => G (Cx.symm (F w))) := by
  dsimp only
  let Cy := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y
  let Cx := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let F := referenceChartTransition (n := n) x y
  obtain ⟨U, hOpen, hCenter, hTarget, hSource, hImage, hSmooth, hHol⟩ :=
    exists_reference_chart_domain (n := n) x y hy
  filter_upwards [hOpen.mem_nhds hCenter] with w hw
  have hwSource : Cy.symm w ∈ Cx.source := hSource w hw
  have hF : F w = Cx (Cy.symm w) := by
    change (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x)
      ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).symm w) = _
    rfl
  change G (Cy.symm w) = G (Cx.symm (F w))
  rw [hF, Cx.left_inv hwSource]

private theorem c3_forcing_chartPotential_hessian_transition
    (G : M → ℝ)
    (hG : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G)
    (x y : M)
    (hy : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source) :
    let Cy := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y
    let Cx := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
    let z := Cy y
    let F := referenceChartTransition (n := n) x y
    complexHessian (G ∘ Cy.symm) z =
      (EuclideanSpace.clmMatrix (fderiv ℂ F z)).transpose *
        complexHessian (G ∘ Cx.symm) (Cx y) *
          (EuclideanSpace.clmMatrix (fderiv ℂ F z)).map star := by
  dsimp only
  let Cy := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y
  let Cx := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let z := Cy y
  let F := referenceChartTransition (n := n) x y
  obtain ⟨U, hOpen, hCenter, hTarget, hSource, hImage, hSmooth, hHol⟩ :=
    exists_reference_chart_domain (n := n) x y hy
  have hcenter : F z = Cx y := by
    change (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x)
      ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).symm
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y)) = _
    rw [(extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).left_inv
      (mem_extChartAt_source y)]
  have hz : z ∈ U := hCenter
  have hFnear : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ F w := by
    filter_upwards [hOpen.mem_nhds hz] with w hw
    exact (hHol w hw).differentiableAt (hOpen.mem_nhds hw)
  have hFreal : ContDiffAt ℝ 2 F z :=
    (hSmooth.contDiffAt (hOpen.mem_nhds hz)).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hCxTarget : Cx y ∈ Cx.target := Cx.map_source hy
  have hsymm : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ Cx.symm (Cx y) :=
    (contMDiffOn_extChartAt_symm x).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hCxTarget)
  have huMD : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (G ∘ Cx.symm) (F z) := by
    rw [hcenter]
    exact (hG y).comp_of_eq hsymm (Cx.left_inv hy)
  have hu : ContDiffAt ℝ 2 (G ∘ Cx.symm) (F z) := by
    exact ((contMDiffAt_iff_contDiffAt).mp huMD).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hcomp : ContDiffAt ℝ 2 ((G ∘ Cx.symm) ∘ F) z := hu.comp z hFreal
  have heq := c3_forcing_chartPotential_eventuallyEq G x y hy
  have hleft : ContDiffAt ℝ 2 (G ∘ Cy.symm) z := hcomp.congr_of_eventuallyEq heq
  have hHess : complexHessian (G ∘ Cy.symm) z =
      complexHessian ((G ∘ Cx.symm) ∘ F) z := by
    ext a b
    exact c3_forcing_complexHessian_eq_of_eventuallyEq
      (G ∘ Cy.symm) ((G ∘ Cx.symm) ∘ F) z a b hleft hcomp heq
  have hPull := c3_forcing_complexHessian_comp_holomorphic
    (G ∘ Cx.symm) F hu hFnear
  rw [hcenter] at hPull
  rw [hHess, hPull]

private theorem c3_connection_pullback_lowered_actual
    (ω₀ : KahlerForm n M) (x y : M)
    (U : Set (EuclideanSpace ℂ (Fin n))) (hU : ω₀.IsReferenceChartOverlap x y U) :
    let z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y
    let f := referenceChartTransition (n := n) x y
    let zx := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y
    let A := fun w => EuclideanSpace.clmMatrix (fderiv ℂ f w)
    ∀ a s p,
      ∑ i, A z a i * christoffelInChart (ω₀.metricInChart y) z i s p =
        wirtingerDerivInChart (fun w => A w a p) z s +
          ∑ u, ∑ v, A z u s * A z v p *
            christoffelInChart (ω₀.metricInChart x) zx a u v := by
  dsimp only
  rcases hU with ⟨hOpen, hz, himage, hf, hhol, hjac, hmetric⟩
  let f := referenceChartTransition (n := n) x y
  let z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y
  let zx := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y
  let A := fun w => EuclideanSpace.clmMatrix (fderiv ℂ f w)
  have hcenter : f z = zx := by
    change (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x)
      ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).symm
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y)) = _
    rw [(extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).left_inv
      (mem_extChartAt_source y)]
  have hjacA : IsUnit (A z).det := by
    simpa [A, z, f, referenceTransitionMatrix] using hjac
  have hgdet : IsUnit ((ω₀.metricInChart x (f z)).det) := by
    apply (Matrix.isUnit_iff_isUnit_det _).1
    exact (ω₀.posDef_metricInChart x (himage ⟨z, hz, rfl⟩)).isUnit
  have hlow := c3_connection_pullback_lowered U hOpen f hf hhol
    (ω₀.metricInChart y) (ω₀.metricInChart x)
    (fun a b => (ω₀.contDiffOn_metricInChart x a b).mono himage)
    hmetric z hz hjacA hgdet
  intro a s p
  have h := hlow a s p
  rw [show chartPartialZComplex = wirtingerDerivInChart from rfl] at h
  rw [hcenter] at h
  simpa [A, f, z, zx] using h

section

variable [T2Space M] [CompactSpace M]

private def permuteFour {α : Type*} :
    (α × (α × (α × α))) ≃ (α × (α × (α × α))) where
  toFun t := (t.2.2.1, (t.2.2.2, (t.2.1, t.1)))
  invFun t := (t.2.2.2, (t.2.2.1, (t.1, t.2.1)))
  left_inv := by rintro ⟨i, m, a, b⟩; rfl
  right_inv := by rintro ⟨a, b, m, i⟩; rfl

private theorem sum_permuteFour {α R : Type*} [Fintype α] [AddCommMonoid R]
    (f : α → α → α → α → R) :
    (∑ i, ∑ m, ∑ a, ∑ b, f i m a b) =
      ∑ a, ∑ b, ∑ m, ∑ i, f i m a b := by
  let g : α × (α × (α × α)) → R := fun t => f t.2.2.2 t.2.2.1 t.1 t.2.1
  calc
    (∑ i, ∑ m, ∑ a, ∑ b, f i m a b) =
        ∑ t : α × (α × (α × α)), f t.1 t.2.1 t.2.2.1 t.2.2.2 := by
      symm
      simp only [Fintype.sum_prod_type]
    _ = ∑ t : α × (α × (α × α)), g (permuteFour t) := by
      apply Fintype.sum_congr
      intro t
      rfl
    _ = ∑ t : α × (α × (α × α)), g t := by
      exact Equiv.sum_comp permuteFour g
    _ = ∑ a, ∑ b, ∑ m, ∑ i, f i m a b := by
      simp only [g, Fintype.sum_prod_type]

private def permuteSix {α : Type*} :
    (α × (α × (α × (α × (α × α))))) ≃
      (α × (α × (α × (α × (α × α))))) where
  toFun t :=
    (t.2.2.2.1, (t.2.2.2.2.1, (t.2.2.2.2.2,
      (t.2.2.1, (t.2.1, t.1)))))
  invFun t :=
    (t.2.2.2.2.2, (t.2.2.2.2.1, (t.2.2.2.1,
      (t.1, (t.2.1, t.2.2.1)))))
  left_inv := by rintro ⟨i, m, c, a, b, d⟩; rfl
  right_inv := by rintro ⟨a, b, d, c, m, i⟩; rfl

private theorem sum_permuteSix {α R : Type*} [Fintype α] [AddCommMonoid R]
    (f : α → α → α → α → α → α → R) :
    (∑ i, ∑ m, ∑ c, ∑ a, ∑ b, ∑ d, f i m c a b d) =
      ∑ a, ∑ b, ∑ d, ∑ c, ∑ m, ∑ i, f i m c a b d := by
  let g : α × (α × (α × (α × (α × α)))) → R :=
    fun t => f t.2.2.2.2.2 t.2.2.2.2.1 t.2.2.2.1 t.1 t.2.1 t.2.2.1
  calc
    (∑ i, ∑ m, ∑ c, ∑ a, ∑ b, ∑ d, f i m c a b d) =
        ∑ t : α × (α × (α × (α × (α × α)))),
          f t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2 := by
      symm
      simp only [Fintype.sum_prod_type]
    _ = ∑ t : α × (α × (α × (α × (α × α)))), g (permuteSix t) := by
      apply Fintype.sum_congr
      intro t
      rfl
    _ = ∑ t : α × (α × (α × (α × (α × α)))), g t := by
      exact Equiv.sum_comp permuteSix g
    _ = ∑ a, ∑ b, ∑ d, ∑ c, ∑ m, ∑ i, f i m c a b d := by
      simp only [g, Fintype.sum_prod_type]

private theorem c3_complexHessian_comp_holomorphic
    {n : ℕ} (u : EuclideanSpace ℂ (Fin n) → ℝ)
    (F : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    {z : EuclideanSpace ℂ (Fin n)}
    (hu : ContDiffAt ℝ 2 u (F z))
    (hF : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ F w) :
    complexHessian (u ∘ F) z =
      (EuclideanSpace.clmMatrix (fderiv ℂ F z)).transpose *
        complexHessian u (F z) * (EuclideanSpace.clmMatrix (fderiv ℂ F z)).map star := by
  have hcomp : ddbar (u ∘ F) z =
      (ddbar u (F z)).compContinuousLinearMap ((fderiv ℂ F z).restrictScalars ℝ) :=
    ddbar_comp_holomorphic hF hu
  rw [complexHessian, complexHessian, hcomp]
  exact (isOneOne_ddbar hu).coeffMatrix_compContinuousLinearMap (fderiv ℂ F z)

private theorem c3_chartPartialZ_star_eq_star_bar
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

private theorem c3_chartPartialZCoordinateComp
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

private noncomputable def c3Wirtinger
    {n : ℕ} (s : ℂ) (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (w : EuclideanSpace ℂ (Fin n)) (j : Fin n) : ℂ :=
  (fderiv ℝ F w (EuclideanSpace.single j 1) +
    s * fderiv ℝ F w (Complex.I • EuclideanSpace.single j 1)) / 2

private theorem c3Wirtinger_fderiv {n : ℕ} (s : ℂ)
    (F : EuclideanSpace ℂ (Fin n) → ℂ) (z : EuclideanSpace ℂ (Fin n))
    (hF : ContDiffAt ℝ ∞ F z) (j : Fin n)
    (v : EuclideanSpace ℂ (Fin n)) :
    fderiv ℝ (fun w => c3Wirtinger s F w j) z v =
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
  have hfun : (fun w => c3Wirtinger s F w j) =
      fun w => (2 : ℂ)⁻¹ * (fderiv ℝ F w e + s * fderiv ℝ F w (Complex.I • e)) := by
    funext w
    simp only [c3Wirtinger, e, div_eq_mul_inv]
    ring
  rw [hfun, fderiv_const_mul hsum, fderiv_fun_add he (hie.const_mul s),
    fderiv_const_mul hie]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [h_e v, h_ie v]
  simp only [div_eq_mul_inv]
  ring

private theorem c3Wirtinger_comm {n : ℕ} (s t : ℂ)
    (F : EuclideanSpace ℂ (Fin n) → ℂ) (z : EuclideanSpace ℂ (Fin n))
    (hF : ContDiffAt ℝ ∞ F z) (p q : Fin n) :
    c3Wirtinger s (fun w => c3Wirtinger t F w q) z p =
      c3Wirtinger t (fun w => c3Wirtinger s F w p) z q := by
  let ep : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single p 1
  let eq : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single q 1
  have hs : IsSymmSndFDerivAt ℝ F z :=
    hF.isSymmSndFDerivAt
      (by simp [minSmoothness_of_isRCLikeNormedField])
  change (fderiv ℝ (fun w => c3Wirtinger t F w q) z ep +
      s * fderiv ℝ (fun w => c3Wirtinger t F w q) z (Complex.I • ep)) / 2 =
    (fderiv ℝ (fun w => c3Wirtinger s F w p) z eq +
      t * fderiv ℝ (fun w => c3Wirtinger s F w p) z (Complex.I • eq)) / 2
  rw [c3Wirtinger_fderiv t F z hF q ep,
    c3Wirtinger_fderiv t F z hF q (Complex.I • ep),
    c3Wirtinger_fderiv s F z hF p eq,
    c3Wirtinger_fderiv s F z hF p (Complex.I • eq)]
  dsimp only [ep, eq] at *
  rw [hs (EuclideanSpace.single p 1) (EuclideanSpace.single q 1),
    hs (EuclideanSpace.single p 1) (Complex.I • EuclideanSpace.single q 1),
    hs (Complex.I • EuclideanSpace.single p 1) (EuclideanSpace.single q 1),
    hs (Complex.I • EuclideanSpace.single p 1) (Complex.I • EuclideanSpace.single q 1)]
  ring

private theorem c3_chartPartialBarZ_comm_at
    {n : ℕ} (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (hF : ContDiffAt ℝ ∞ F z)
    (p q : Fin n) :
    chartPartialBarComplex (fun w => chartPartialZComplex F w p) z q =
      chartPartialZComplex (fun w => chartPartialBarComplex F w q) z p := by
  have hz (A : EuclideanSpace ℂ (Fin n) → ℂ) (w : EuclideanSpace ℂ (Fin n))
      (j : Fin n) : c3Wirtinger (-Complex.I) A w j = chartPartialZComplex A w j := by
    simp [c3Wirtinger, chartPartialZComplex, div_eq_mul_inv]
    ring
  have hb (w : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
      c3Wirtinger Complex.I F w j = chartPartialBarComplex F w j := rfl
  have hzf (j : Fin n) : (fun w => c3Wirtinger (-Complex.I) F w j) =
      (fun w => chartPartialZComplex F w j) := funext (fun w => hz F w j)
  have hbf (j : Fin n) : (fun w => c3Wirtinger Complex.I F w j) =
      (fun w => chartPartialBarComplex F w j) := funext (fun w => hb w j)
  calc
    chartPartialBarComplex (fun w => chartPartialZComplex F w p) z q =
        c3Wirtinger Complex.I (fun w => c3Wirtinger (-Complex.I) F w p) z q := by
      rw [hzf]
      rfl
    _ = c3Wirtinger (-Complex.I)
        (fun w => c3Wirtinger Complex.I F w q) z p :=
      (c3Wirtinger_comm (-Complex.I) Complex.I F z hF p q).symm
    _ = chartPartialZComplex (fun w => chartPartialBarComplex F w q) z p := by
      rw [hbf]
      exact hz (fun w => chartPartialBarComplex F w q) z p

private theorem c3_chartPartialZComplex_differentiableAt
    {n : ℕ} (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (hF : ContDiffAt ℝ ∞ F z)
    (j : Fin n) : DifferentiableAt ℝ (fun w => chartPartialZComplex F w j) z := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ F) z :=
    (hF.fderiv_right (m := ∞)
      (le_of_eq (show (∞ : ℕ∞ω) = ∞ + 1 from rfl).symm)).differentiableAt (by norm_num)
  have he : DifferentiableAt ℝ (fun w => fderiv ℝ F w (EuclideanSpace.single j 1)) z :=
    hfd.clm_apply (differentiableAt_const _)
  have hie : DifferentiableAt ℝ
      (fun w => fderiv ℝ F w (Complex.I • EuclideanSpace.single j 1)) z :=
    hfd.clm_apply (differentiableAt_const _)
  have hfun : (fun w => chartPartialZComplex F w j) =
      fun w => (2 : ℂ)⁻¹ * (fderiv ℝ F w (EuclideanSpace.single j 1) -
        Complex.I * fderiv ℝ F w (Complex.I • EuclideanSpace.single j 1)) := by
    funext w
    simp [chartPartialZComplex, div_eq_mul_inv]
    ring
  rw [hfun]
  exact he.sub (hie.const_mul Complex.I) |>.const_mul _

private theorem c3_complexHessian_entry_differentiableAt
    {n : ℕ} (u : EuclideanSpace ℂ (Fin n) → ℝ)
    (z : EuclideanSpace ℂ (Fin n)) (hu : ContDiffAt ℝ 3 u z)
    (j k : Fin n) : DifferentiableAt ℝ (fun w => complexHessian u w j k) z := by
  have hu2 : ContDiffAt ℝ 2 u z := hu.of_le (by norm_num)
  have hfd : ContDiffAt ℝ 2 (fderiv ℝ u) z :=
    hu.fderiv_right (m := 2) (by norm_num)
  have hsecond : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ u)) z := by
    exact (hfd.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hterm (v w : EuclideanSpace ℂ (Fin n)) :
      DifferentiableAt ℝ (fun y => fderiv ℝ (fderiv ℝ u) y v w) z := by
    exact (hsecond.clm_apply (differentiableAt_const _)).clm_apply
      (differentiableAt_const _)
  let Q : EuclideanSpace ℂ (Fin n) → ℂ := fun w =>
    ((fderiv ℝ (fderiv ℝ u) w (EuclideanSpace.single j 1) (EuclideanSpace.single k 1) : ℂ) +
      fderiv ℝ (fderiv ℝ u) w (Complex.I • EuclideanSpace.single j 1)
        (Complex.I • EuclideanSpace.single k 1) +
      Complex.I * (fderiv ℝ (fderiv ℝ u) w (EuclideanSpace.single j 1)
          (Complex.I • EuclideanSpace.single k 1) -
        fderiv ℝ (fderiv ℝ u) w (Complex.I • EuclideanSpace.single j 1)
          (EuclideanSpace.single k 1))) / 4
  have hQ : DifferentiableAt ℝ Q z := by
    dsimp [Q]
    fun_prop (disch := assumption)
  have hEq : (fun w => complexHessian u w j k) =ᶠ[𝓝 z] Q := by
    filter_upwards [hu.eventually (by norm_num)] with w huw
    simpa [Q] using complexHessian_apply (huw.of_le (by norm_num)) j k
  exact hQ.congr_of_eventuallyEq hEq

private theorem c3_wirtinger_directional_smul {n : ℕ}
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
    have hscalar : Complex.I * c = ((-c.im : ℝ) : ℂ) + (c.re : ℝ) * Complex.I := by
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

private theorem c3_chartPartialZ_comp
    {n : ℕ} (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) (p : Fin n)
    (hF : DifferentiableAt ℝ F (ψ z)) (hψ : DifferentiableAt ℂ ψ z) :
    chartPartialZComplex (fun w => F (ψ w)) z p =
      ∑ a, (EuclideanSpace.clmMatrix (fderiv ℂ ψ z)) a p *
        chartPartialZComplex F (ψ z) a := by
  have hψR : HasFDerivAt ψ ((fderiv ℂ ψ z).restrictScalars ℝ) z :=
    hψ.hasFDerivAt.restrictScalars ℝ
  have hψreal : fderiv ℝ ψ z = (fderiv ℂ ψ z).restrictScalars ℝ := by
    simpa using hψ.fderiv_restrictScalars ℝ
  have hcomp := fderiv_comp (f := ψ) (g := F) (x := z) hF hψR.differentiableAt
  have hcomp' : fderiv ℝ (fun w => F (ψ w)) z =
      (fderiv ℝ F (ψ z)).comp (fderiv ℝ ψ z) := by
    simpa [Function.comp_def] using hcomp
  let D := fderiv ℝ F (ψ z)
  let L := fderiv ℂ ψ z
  let A := EuclideanSpace.clmMatrix L
  let e := EuclideanSpace.single p (1 : ℂ)
  have hvec : L e = ∑ a, (A a p) • EuclideanSpace.single a (1 : ℂ) := by
    ext a
    simp [A, e, Pi.single_apply]
    change (L (EuclideanSpace.single p (1 : ℂ))).ofLp a =
      (Matrix.of fun (b : Fin n) (c : Fin n) =>
        (L (EuclideanSpace.single c (1 : ℂ))).ofLp b) a p
    simp only [Matrix.of_apply]
  unfold chartPartialZComplex
  rw [hcomp', hψreal]
  simp only [ContinuousLinearMap.comp_apply]
  change (D (L e) - Complex.I * D (L (Complex.I • e))) / 2 = _
  rw [map_smul, hvec]
  simp only [_root_.map_sum, Finset.smul_sum]
  have hsum :
      (∑ a, D ((A a p) • EuclideanSpace.single a (1 : ℂ))) -
        Complex.I * ∑ a, D (Complex.I • ((A a p) • EuclideanSpace.single a (1 : ℂ))) =
      ∑ a, (D ((A a p) • EuclideanSpace.single a (1 : ℂ)) -
        Complex.I * D (Complex.I • ((A a p) • EuclideanSpace.single a (1 : ℂ)))) := by
    rw [Finset.mul_sum, Finset.sum_sub_distrib]
  rw [hsum]
  simp_rw [c3_wirtinger_directional_smul]
  simp only [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  ring

private theorem c3_chartPartialZ_sum
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
  simp only [_root_.sum_apply]
  have hsum :
      (∑ i, fderiv ℝ (F i) z (EuclideanSpace.single p 1)) -
        Complex.I * ∑ i, fderiv ℝ (F i) z (Complex.I • EuclideanSpace.single p 1) =
      ∑ i, (fderiv ℝ (F i) z (EuclideanSpace.single p 1) -
        Complex.I * fderiv ℝ (F i) z (Complex.I • EuclideanSpace.single p 1)) := by
    rw [Finset.mul_sum, Finset.sum_sub_distrib]
  rw [hsum]
  simp only [div_eq_mul_inv, Finset.sum_mul]

private theorem c3_chartPartialZ_conj_jacobian_zero
    {n : ℕ} (f : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (z : EuclideanSpace ℂ (Fin n))
    (hf : ContDiffAt ℝ ∞ f z)
    (hhol : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ f w)
    (a l p : Fin n) :
    chartPartialZComplex
      (fun w => star (EuclideanSpace.clmMatrix (fderiv ℂ f w) a l)) z p = 0 := by
  let F : EuclideanSpace ℂ (Fin n) → ℂ := fun w => f w a
  have hF : ContDiffAt ℝ ∞ F z := by
    have hcoord : ContDiff ℝ ∞ (fun x : EuclideanSpace ℂ (Fin n) => x a) := by
      fun_prop
    simpa [F, Function.comp_def] using hcoord.contDiffAt.comp z hf
  have hAeq :
      (fun w => (EuclideanSpace.clmMatrix (fderiv ℂ f w)) a l) =ᶠ[𝓝 z]
        (fun w => chartPartialZComplex F w l) := by
    filter_upwards [hhol] with w hfw
    have hcoord : DifferentiableAt ℂ (fun v : EuclideanSpace ℂ (Fin n) => v a) (f w) := by
      fun_prop
    exact (c3_chartPartialZCoordinateComp f w a l hfw).symm
  have hAr : DifferentiableAt ℝ
      (fun w => (EuclideanSpace.clmMatrix (fderiv ℂ f w)) a l) z := by
    exact c3_chartPartialZComplex_differentiableAt F z hF l
      |>.congr_of_eventuallyEq hAeq
  have hbarA : chartPartialBarComplex
      (fun w => (EuclideanSpace.clmMatrix (fderiv ℂ f w)) a l) z p = 0 := by
    have hEq := hAeq.fderiv_eq (𝕜 := ℝ)
    rw [show chartPartialBarComplex
        (fun w => (EuclideanSpace.clmMatrix (fderiv ℂ f w)) a l) z p =
        chartPartialBarComplex (fun w => chartPartialZComplex F w l) z p by
          unfold chartPartialBarComplex
          rw [hEq]]
    have hcomm := c3_chartPartialBarZ_comm_at F z hF l p
    rw [hcomm]
    have hbar : (fun w => chartPartialBarComplex F w p) =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
      filter_upwards [hhol] with w hfw
      have hcoord : DifferentiableAt ℂ (fun v : EuclideanSpace ℂ (Fin n) => v a) (f w) := by
        fun_prop
      have hFw : DifferentiableAt ℂ F w := by
        dsimp [F]
        exact hcoord.comp w hfw
      have hreal : fderiv ℝ F w = (fderiv ℂ F w).restrictScalars ℝ :=
        hFw.fderiv_restrictScalars ℝ
      have hI : fderiv ℂ F w (Complex.I • EuclideanSpace.single p (1 : ℂ)) =
          Complex.I * fderiv ℂ F w (EuclideanSpace.single p 1) := by simp
      unfold chartPartialBarComplex
      rw [hreal, ContinuousLinearMap.coe_restrictScalars', hI]
      rw [← mul_assoc, Complex.I_mul_I]
      ring
    unfold chartPartialZComplex
    rw [hbar.fderiv_eq]
    simp
  have hstar := c3_chartPartialZ_star_eq_star_bar
    (fun w => (EuclideanSpace.clmMatrix (fderiv ℂ f w)) a l) z p hAr
  rw [hstar, hbarA]
  simp

private theorem c3_complexHessian_comp_firstJet
    {n : ℕ} (u : EuclideanSpace ℂ (Fin n) → ℝ)
    (F : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) (hhol : DifferentiableOn ℂ F U)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U)
    (hu : ContDiffAt ℝ 3 u (F z)) (a b p : Fin n) :
    chartPartialZComplex (fun w => complexHessian (u ∘ F) w a b) z p =
      (∑ r, ∑ s,
        chartPartialZComplex (fun w => EuclideanSpace.clmMatrix (fderiv ℂ F w) r a) z p *
          star (EuclideanSpace.clmMatrix (fderiv ℂ F z) s b) * complexHessian u (F z) r s) +
      ∑ r, ∑ s, ∑ t,
        EuclideanSpace.clmMatrix (fderiv ℂ F z) r a *
          star (EuclideanSpace.clmMatrix (fderiv ℂ F z) s b) *
          EuclideanSpace.clmMatrix (fderiv ℂ F z) t p *
          chartPartialZComplex (fun w => complexHessian u w r s) (F z) t := by
  classical
  let J : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w => EuclideanSpace.clmMatrix (fderiv ℂ F w)
  let H : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w => complexHessian u w
  let S (r s : Fin n) : EuclideanSpace ℂ (Fin n) → ℂ :=
    fun w => J w r a * star (J w s b) * H (F w) r s
  have hFz : ContDiffAt ℝ ∞ F z := (hF z hz).contDiffAt (hU.mem_nhds hz)
  have hFdiff : DifferentiableAt ℝ F z := hFz.differentiableAt (by norm_num)
  have hFhol : DifferentiableAt ℂ F z := (hhol z hz).differentiableAt (hU.mem_nhds hz)
  have hHdiff (r s : Fin n) : DifferentiableAt ℝ (fun w => H w r s) (F z) := by
    dsimp [H]
    exact c3_complexHessian_entry_differentiableAt u (F z) hu r s
  have hJdiff (r s : Fin n) : DifferentiableAt ℝ (fun w => J w r s) z := by
    let q : EuclideanSpace ℂ (Fin n) → ℂ := fun w => F w r
    have hq : ContDiffAt ℝ ∞ q z := by
      have hcoord : ContDiff ℝ ∞ (fun v : EuclideanSpace ℂ (Fin n) => v r) := by
        fun_prop
      simpa [q, Function.comp_def] using hcoord.contDiffAt.comp z hFz
    have hEq : (fun w => J w r s) =ᶠ[𝓝 z] fun w => chartPartialZComplex q w s := by
      filter_upwards [hU.mem_nhds hz] with w hw
      exact (c3_chartPartialZCoordinateComp F w r s
        ((hhol w hw).differentiableAt (hU.mem_nhds hw))).symm
    exact (c3_chartPartialZComplex_differentiableAt q z hq s).congr_of_eventuallyEq hEq
  have hJstar (r s : Fin n) : DifferentiableAt ℝ (fun w => star (J w r s)) z := by
    exact (Complex.conjCLE.differentiableAt.comp z (hJdiff r s))
  have hHcomp (r s : Fin n) : DifferentiableAt ℝ (fun w => H (F w) r s) z :=
    (hHdiff r s).comp z hFdiff
  have hSdiff (r s : Fin n) : DifferentiableAt ℝ (S r s) z := by
    dsimp [S]
    exact ((hJdiff r a).mul (hJstar s b)).mul (hHcomp r s)
  have hUcomp : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ 3 u (F w) :=
    hFz.continuousAt.preimage_mem_nhds (hu.eventually (by norm_num))
  have hpull :
      (fun w => complexHessian (u ∘ F) w a b) =ᶠ[𝓝 z]
        (fun w => ∑ r, ∑ s, S r s w) := by
    filter_upwards [hU.mem_nhds hz, hUcomp] with w hw huw
    have hholw : ∀ᶠ v in 𝓝 w, DifferentiableAt ℂ F v := by
      filter_upwards [hU.mem_nhds hw] with v hv
      exact (hhol v hv).differentiableAt (hU.mem_nhds hv)
    have hformula := c3_complexHessian_comp_holomorphic
      (u := u) (F := F) (z := w) (huw.of_le (by norm_num)) hholw
    have hmap := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M a b) hformula
    have hentry :
        (∑ s, (∑ r, J w r a * H (F w) r s) * star (J w s b)) =
          ∑ r, ∑ s, J w r a * star (J w s b) * H (F w) r s := by
      calc
        _ = ∑ s, ∑ r, (J w r a * H (F w) r s) * star (J w s b) := by
          simp_rw [Finset.sum_mul]
        _ = ∑ r, ∑ s, (J w r a * H (F w) r s) * star (J w s b) := by
          rw [Finset.sum_comm]
        _ = ∑ r, ∑ s, J w r a * star (J w s b) * H (F w) r s := by
          apply Finset.sum_congr rfl
          intro r hr
          apply Finset.sum_congr rfl
          intro s hs
          ring
    simpa [complexHessian, H, J, S, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply] using hmap.trans hentry
  have hLdiff : DifferentiableAt ℝ
      (fun w => ∑ r, ∑ s, S r s w) z := by
    apply DifferentiableAt.fun_sum
    intro r hr
    apply DifferentiableAt.fun_sum
    intro s hs
    exact hSdiff r s
  have hmain := hLdiff.congr_of_eventuallyEq hpull
  have hsum : chartPartialZComplex (fun w => ∑ r, ∑ s, S r s w) z p =
      ∑ r, ∑ s, chartPartialZComplex (S r s) z p := by
    rw [c3_chartPartialZ_sum _ z p]
    · apply Finset.sum_congr rfl
      intro r hr
      exact c3_chartPartialZ_sum _ z p (fun s => hSdiff r s)
    · intro r
      exact DifferentiableAt.fun_sum (fun s hs => hSdiff r s)
  have hder := hpull.fderiv_eq (𝕜 := ℝ)
  have hpartial :
      chartPartialZComplex (fun w => complexHessian (u ∘ F) w a b) z p =
        chartPartialZComplex (fun w => ∑ r, ∑ s, S r s w) z p := by
    unfold chartPartialZComplex
    rw [hder]
  rw [hpartial, hsum]
  have hjet (r s : Fin n) : chartPartialZComplex (S r s) z p =
      chartPartialZComplex (fun w => J w r a) z p * star (J z s b) * H (F z) r s +
        J z r a * star (J z s b) *
          ∑ t, J z t p * chartPartialZComplex (fun w => H w r s) (F z) t := by
    have hprod : DifferentiableAt ℝ (fun w => J w r a * star (J w s b)) z :=
      (hJdiff r a).mul (hJstar s b)
    have hholz : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ F w := by
      filter_upwards [hU.mem_nhds hz] with w hw
      exact (hhol w hw).differentiableAt (hU.mem_nhds hw)
    rw [chartPartialZComplex_mul hprod (hHcomp r s) p,
      chartPartialZComplex_mul (hJdiff r a) (hJstar s b) p,
      c3_chartPartialZ_conj_jacobian_zero F z hFz hholz s b p,
      c3_chartPartialZ_comp (fun v => H v r s) F z p (hHdiff r s) hFhol]
    · ring
  simp_rw [hjet]
  simp_rw [Finset.sum_add_distrib, Finset.mul_sum]
  simp [J, H]
  ring_nf

end

private theorem c3_forcing_chartPotential_hessian_eventuallyEq
    (G : M → ℝ)
    (hG : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G)
    (x y : M)
    (hy : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source) :
    let Cy := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y
    let Cx := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
    let F := referenceChartTransition (n := n) x y
    ∀ j l, (fun w => complexHessian (G ∘ Cy.symm) w j l) =ᶠ[𝓝 (Cy y)]
      (fun w => complexHessian ((G ∘ Cx.symm) ∘ F) w j l) := by
  dsimp only
  let Cy := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y
  let Cx := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let F := referenceChartTransition (n := n) x y
  let z := Cy y
  obtain ⟨U, hOpen, hCenter, hTarget, hSource, hImage, hSmooth, hHol⟩ :=
    exists_reference_chart_domain (n := n) x y hy
  have hpot : ∀ w ∈ U, G (Cy.symm w) = G (Cx.symm (F w)) := by
    intro w hw
    have hwSource : Cy.symm w ∈ Cx.source := hSource w hw
    have hFw : F w = Cx (Cy.symm w) := by
      change (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x)
        ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).symm w) = _
      rfl
    change G (Cy.symm w) = G (Cx.symm (F w))
    rw [hFw, Cx.left_inv hwSource]
  intro j l
  filter_upwards [hOpen.mem_nhds hCenter] with w hw
  have heq : (fun q => G (Cy.symm q)) =ᶠ[𝓝 w] (fun q => G (Cx.symm (F q))) := by
    filter_upwards [hOpen.mem_nhds hw] with q hq
    exact hpot q hq
  have hCyTarget : w ∈ Cy.target := hTarget hw
  have hsymmY : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ Cy.symm w :=
    (contMDiffOn_extChartAt_symm y).contMDiffAt
      ((isOpen_extChartAt_target y).mem_nhds hCyTarget)
  have hMDy : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (G ∘ Cy.symm) w := by
    exact (hG (Cy.symm w)).comp_of_eq hsymmY rfl
  have huTarget : F w ∈ Cx.target := hImage ⟨w, hw, rfl⟩
  have hsymmX : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ Cx.symm (F w) :=
    (contMDiffOn_extChartAt_symm x).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds huTarget)
  have hMDu : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (G ∘ Cx.symm) (F w) := by
    exact (hG (Cx.symm (F w))).comp_of_eq hsymmX rfl
  have hFAt : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ F w :=
    (contMDiffAt_iff_contDiffAt).mpr (hSmooth.contDiffAt (hOpen.mem_nhds hw))
  have hMDx : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ)
      ∞ ((G ∘ Cx.symm) ∘ F) w := by
    exact hMDu.comp_of_eq hFAt rfl
  have hf : ContDiffAt ℝ 2 (G ∘ Cy.symm) w := by
    exact ((contMDiffAt_iff_contDiffAt).mp hMDy).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hg : ContDiffAt ℝ 2 ((G ∘ Cx.symm) ∘ F) w := by
    exact ((contMDiffAt_iff_contDiffAt).mp hMDx).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  exact c3_forcing_complexHessian_eq_of_eventuallyEq
    (G ∘ Cy.symm) ((G ∘ Cx.symm) ∘ F) w j l hf hg heq

section

variable [T2Space M] [CompactSpace M]

private theorem sumSwapTest {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℂ) :
    (∑ a : α, ∑ b : β, f a b) = ∑ b : β, ∑ a : α, f a b := by
  classical
  exact Finset.sum_comm

private theorem covariantDerivative_sum_contract {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (f : γ → ℂ) (g : α → γ → ℂ) (h : α → β → ℂ) :
    (∑ c, f c * ∑ a, ∑ b, g a c * h a b) =
      ∑ a, ∑ b, (∑ c, g a c * f c) * h a b := by
  classical
  calc
    (∑ c, f c * ∑ a, ∑ b, g a c * h a b) =
        ∑ c, ∑ a, ∑ b, (f c * g a c) * h a b := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = ∑ a, ∑ c, ∑ b, (f c * g a c) * h a b := by
      rw [Finset.sum_comm]
    _ = ∑ a, ∑ b, ∑ c, (f c * g a c) * h a b := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = ∑ a, ∑ b, (∑ c, g a c * f c) * h a b := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c hc
      ring

private theorem covariantDerivative_gamma_reindex {n : ℕ}
    (A : Fin n → Fin n → ℂ) (Γ : Fin n → Fin n → Fin n → ℂ)
    (Q : Fin n → Fin n → ℂ) (k j l : Fin n) :
    (∑ r, ∑ c, (∑ u, ∑ v, A u k * A v j * Γ r u v) *
      star (A c l) * Q r c) =
    ∑ u, ∑ v, ∑ c, A u k * A v j * star (A c l) *
      (∑ r, Γ r u v * Q r c) := by
  classical
  let F : Fin n → Fin n → Fin n → Fin n → ℂ := fun r c u v =>
    A u k * A v j * Γ r u v * star (A c l) * Q r c
  calc
    (∑ r, ∑ c, (∑ u, ∑ v, A u k * A v j * Γ r u v) *
        star (A c l) * Q r c) = ∑ r, ∑ c, ∑ u, ∑ v, F r c u v := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro c hc
      simp only [Finset.sum_mul, F]
    _ =
        ∑ c, ∑ r, ∑ u, ∑ v, F r c u v := by
      exact sumSwapTest (fun r c => ∑ u, ∑ v, F r c u v)
    _ = ∑ c, ∑ u, ∑ r, ∑ v, F r c u v := by
      apply Finset.sum_congr rfl
      intro c hc
      exact sumSwapTest (fun r u => ∑ v, F r c u v)
    _ = ∑ u, ∑ c, ∑ r, ∑ v, F r c u v := by
      exact sumSwapTest (fun c u => ∑ r, ∑ v, F r c u v)
    _ = ∑ u, ∑ c, ∑ v, ∑ r, F r c u v := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro c hc
      exact sumSwapTest (fun r v => F r c u v)
    _ = ∑ u, ∑ v, ∑ c, ∑ r, F r c u v := by
      apply Finset.sum_congr rfl
      intro u hu
      exact sumSwapTest (fun c v => ∑ r, F r c u v)
    _ = ∑ u, ∑ v, ∑ c, A u k * A v j * star (A c l) *
          ∑ r, Γ r u v * Q r c := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro c hc
      change (∑ r, (A u k * A v j * Γ r u v * star (A c l) * Q r c)) = _
      have hfactor : ∀ r, A u k * A v j * Γ r u v * star (A c l) * Q r c =
          (A u k * A v j * star (A c l)) * (Γ r u v * Q r c) := by
        intro r
        ring
      simp_rw [hfactor, ← Finset.mul_sum]

private theorem covariantDerivative_pullback_algebra {n : ℕ}
    (A : Fin n → Fin n → ℂ)
    (dA dBarA : Fin n → Fin n → Fin n → ℂ)
    (Γx Γy : Fin n → Fin n → Fin n → ℂ)
    (Qx Qy : Fin n → Fin n → ℂ)
    (dQx dQy : Fin n → Fin n → Fin n → ℂ)
    (hBar : ∀ a b k, dBarA a b k = 0)
    (hQ : ∀ j l, Qy j l = ∑ a : Fin n, ∑ b : Fin n,
      A a j * star (A b l) * Qx a b)
    (hdQ : ∀ k j l, dQy k j l =
      (∑ a : Fin n, ∑ b : Fin n, dA a j k * star (A b l) * Qx a b) +
      (∑ a : Fin n, ∑ b : Fin n, A a j * dBarA b l k * Qx a b) +
      (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
        A a k * A b j * star (A c l) * dQx a b c))
    (hΓ : ∀ a k j, ∑ i : Fin n, A a i * Γy i k j =
      dA a j k + ∑ u : Fin n, ∑ v : Fin n, A u k * A v j * Γx a u v) :
    ∀ k j l,
      dQy k j l - ∑ i : Fin n, Γy i k j * Qy i l =
        ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, A a k * A b j * star (A c l) *
          (dQx a b c - ∑ r : Fin n, Γx r a b * Qx r c) := by
  classical
  intro k j l
  have hcontract := covariantDerivative_sum_contract
    (fun i : Fin n => Γy i k j) (fun a i => A a i)
    (fun a b => star (A b l) * Qx a b)
  have hCorr :
      (∑ i : Fin n, Γy i k j * Qy i l) =
        ∑ a : Fin n, ∑ b : Fin n,
          (dA a j k + ∑ u : Fin n, ∑ v : Fin n,
            A u k * A v j * Γx a u v) * star (A b l) * Qx a b := by
    calc
      (∑ i, Γy i k j * Qy i l) =
          ∑ i, Γy i k j * ∑ a, ∑ b, A a i * (star (A b l) * Qx a b) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hQ i l]
        congr 1
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        ring
      _ = ∑ a, ∑ b, (∑ i, A a i * Γy i k j) *
            (star (A b l) * Qx a b) := by
        simpa [mul_assoc] using hcontract
      _ = ∑ a, ∑ b, (dA a j k + ∑ u, ∑ v,
            A u k * A v j * Γx a u v) * star (A b l) * Qx a b := by
        simp [hΓ, mul_assoc]
  rw [hdQ k j l, hCorr]
  simp [hBar]
  simp only [add_mul, Finset.sum_add_distrib]
  have hGamma := covariantDerivative_gamma_reindex A Γx Qx k j l
  simp only [mul_sub, Finset.sum_sub_distrib]
  have hGamma' :
      (∑ x : Fin n, ∑ x1 : Fin n,
        (∑ u : Fin n, ∑ v : Fin n, A u k * A v j * Γx x u v) *
          star (A x1 l) * Qx x x1) =
        ∑ x : Fin n, ∑ x1 : Fin n, ∑ x2 : Fin n,
          A x k * A x1 j * star (A x2 l) *
            ∑ r : Fin n, Γx r x x1 * Qx r x2 := by
    simpa [mul_assoc] using hGamma
  simpa using hGamma'

end

set_option maxHeartbeats 1000000 in
private theorem c3_forcing_covariantHessian_transition
    (ω₀ : KahlerForm n M) {G : M → ℝ}
    (hG : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G)
    (x y : M)
    (hy : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source)
    (V : Set (EuclideanSpace ℂ (Fin n)))
    (hV : ω₀.IsReferenceChartOverlap x y V) :
    let zY := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y
    let zX := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y
    ∀ k j l,
      c3ReferenceCovariantTwoTensorZ ω₀ y (c3ForcingHessianInChart G y) zY k j l =
        ∑ a, ∑ b, ∑ c, referenceTransitionMatrix x y a k *
          referenceTransitionMatrix x y b j * star (referenceTransitionMatrix x y c l) *
            c3ReferenceCovariantTwoTensorZ ω₀ x (c3ForcingHessianInChart G x) zX a b c := by
  classical
  dsimp only
  let Cy := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y
  let Cx := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let zY := Cy y
  let zX := Cx y
  let F := referenceChartTransition (n := n) x y
  let A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w => EuclideanSpace.clmMatrix (fderiv ℂ F w)
  let J := referenceTransitionMatrix (n := n) x y
  let Qy : EuclideanSpace ℂ (Fin n) → Fin n → Fin n → ℂ :=
    fun w a b => c3ForcingHessianInChart G y w a b
  let Qx : EuclideanSpace ℂ (Fin n) → Fin n → Fin n → ℂ :=
    fun w a b => c3ForcingHessianInChart G x w a b
  let dA : Fin n → Fin n → Fin n → ℂ := fun a b k =>
    chartPartialZComplex (fun w => A w a b) zY k
  let dBarA : Fin n → Fin n → Fin n → ℂ := fun a b k =>
    chartPartialZComplex (fun w => star (A w a b)) zY k
  let Γy : Fin n → Fin n → Fin n → ℂ :=
    fun i k j => christoffelInChart (ω₀.metricInChart y) zY i k j
  let Γx : Fin n → Fin n → Fin n → ℂ :=
    fun i k j => christoffelInChart (ω₀.metricInChart x) zX i k j
  let dQy : Fin n → Fin n → Fin n → ℂ := fun k j l =>
    wirtingerDerivInChart (fun w => Qy w j l) zY k
  let dQx : Fin n → Fin n → Fin n → ℂ := fun k j l =>
    wirtingerDerivInChart (fun w => Qx w j l) zX k
  rcases hV with ⟨hOpen, hz, himage, hSmooth, hHol, hjac, hmetric⟩
  have hcenter : F zY = zX := by
    change (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x)
      ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).symm
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y)) = _
    rw [(extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).left_inv
      (mem_extChartAt_source y)]
  have hJ : A zY = J := by
    rfl
  have hHess := c3_forcing_chartPotential_hessian_transition G hG x y hy
  have hQ : ∀ a b, Qy zY a b = ∑ r, ∑ s,
      J r a * star (J s b) * Qx zX r s := by
    intro a b
    have hmat := congrArg (fun H : Matrix (Fin n) (Fin n) ℂ => H a b) hHess
    change complexHessian (G ∘ Cy.symm) zY a b = _
    rw [hmat]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      Qx, c3ForcingHessianInChart, J, referenceTransitionMatrix,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro s hs
    ring
  have hFzSmooth : ContDiffAt ℝ ∞ F zY :=
    (hSmooth zY hz).contDiffAt (hOpen.mem_nhds hz)
  have hFzHol : DifferentiableAt ℂ F zY :=
    (hHol zY hz).differentiableAt (hOpen.mem_nhds hz)
  have hCxsymm : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ Cx.symm zX := by
    have hzTarget : zX ∈ Cx.target := Cx.map_source hy
    exact (contMDiffOn_extChartAt_symm x).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hzTarget)
  have huMD : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (G ∘ Cx.symm) (F zY) := by
    rw [hcenter]
    exact (hG y).comp_of_eq hCxsymm (Cx.left_inv hy)
  have hu : ContDiffAt ℝ 3 (G ∘ Cx.symm) (F zY) := by
    exact ((contMDiffAt_iff_contDiffAt).mp huMD).of_le
      (WithTop.coe_le_coe.mpr (show (3 : ℕ∞) ≤ ⊤ from le_top))
  have hfirst (a b k : Fin n) := c3_complexHessian_comp_firstJet
    (G ∘ Cx.symm) F V hOpen hSmooth hHol zY hz hu a b k
  have hPotentialDerivative (a b k : Fin n) :
      chartPartialZComplex (fun w => complexHessian (G ∘ Cy.symm) w a b) zY k =
        chartPartialZComplex
          (fun w => complexHessian ((G ∘ Cx.symm) ∘ F) w a b) zY k := by
    have heq := c3_forcing_chartPotential_hessian_eventuallyEq G hG x y hy a b
    have hder := heq.fderiv_eq (𝕜 := ℝ)
    unfold chartPartialZComplex
    rw [hder]
  have hbar : ∀ a b k, dBarA a b k = 0 := by
    intro a b k
    exact c3_chartPartialZ_conj_jacobian_zero F zY hFzSmooth
      (by
        filter_upwards [hOpen.mem_nhds hz] with w hw
        exact (hHol w hw).differentiableAt (hOpen.mem_nhds hw)) a b k
  have hdQ : ∀ k j l,
      dQy k j l =
        (∑ a, ∑ b, dA a j k * star (J b l) * Qx zX a b) +
        (∑ a, ∑ b, J a j * dBarA b l k * Qx zX a b) +
        (∑ a, ∑ b, ∑ c, J a k * J b j * star (J c l) * dQx a b c) := by
    intro k j l
    have hjet := hfirst j l k
    change wirtingerDerivInChart (fun w => Qy w j l) zY k = _
    rw [show wirtingerDerivInChart = chartPartialZComplex from rfl]
    change chartPartialZComplex
      (fun w => complexHessian (G ∘ Cy.symm) w j l) zY k = _
    rw [hPotentialDerivative j l k, hjet]
    rw [← hJ]
    simp [hbar]
    simp [dA, dQx, Qx, c3ForcingHessianInChart, A, Cx, hcenter]
    have hswap (f : Fin n → Fin n → Fin n → ℂ) :
        (∑ r, ∑ s, ∑ t, f r s t) = ∑ t, ∑ r, ∑ s, f r s t := by
      calc
        (∑ r, ∑ s, ∑ t, f r s t) = ∑ r, ∑ t, ∑ s, f r s t := by
          apply Finset.sum_congr rfl
          intro r hr
          exact Finset.sum_comm
        _ = ∑ t, ∑ r, ∑ s, f r s t := Finset.sum_comm
    rw [hswap]
    rw [show wirtingerDerivInChart = chartPartialZComplex from rfl]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc
    ring
  have hGamma : ∀ a k j, ∑ i, J a i * Γy i k j =
      dA a j k + ∑ u, ∑ v, J u k * J v j * Γx a u v := by
    intro a k j
    have hlow := c3_connection_pullback_lowered_actual ω₀ x y V
      ⟨hOpen, hz, himage, hSmooth, hHol, hjac, hmetric⟩
    simpa only [A, J, dA, Γy, Γx, Cy, Cx, zY, zX, F,
      referenceTransitionMatrix, wirtingerDerivInChart, chartPartialZComplex] using hlow a k j
  have hAlg := covariantDerivative_pullback_algebra
    (A := fun a b => J a b) (dA := dA) (dBarA := dBarA) (Γx := Γx) (Γy := Γy)
    (Qx := fun a b => Qx zX a b) (Qy := fun a b => Qy zY a b)
    (dQx := dQx) (dQy := dQy) hbar hQ hdQ hGamma
  intro k j l
  have h := hAlg k j l
  simpa [c3ReferenceCovariantTwoTensorZ, wirtingerDerivInChart, Qx, Qy, Γy, Γx,
    Cy, Cx, zY, zX, J, dQx, dQy, dBarA] using h

-- The algebraic identity follows from the two tensor-coordinate identities.
private theorem forcingFrameBound_chart_transition_algebraic
    (ω₀ : KahlerForm n M) {G : M → ℝ}
    (_hG : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G)
    (x y : M)
    (_hy : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source)
    (V : Set (EuclideanSpace ℂ (Fin n)))
    (_hV : ω₀.IsReferenceChartOverlap x y V)
    (P : Matrix (Fin n) (Fin n) ℂ) (A : ℝ)
    (hH : ∀ j l,
      c3ForcingHessianInChart G y
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y) j l =
        ∑ a, ∑ b, referenceTransitionMatrix x y a j *
          star (referenceTransitionMatrix x y b l) *
            c3ForcingHessianInChart G x
              (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y) a b)
    (hD : ∀ k j l,
      c3ReferenceCovariantTwoTensorZ ω₀ y (c3ForcingHessianInChart G y)
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y) k j l =
        ∑ a, ∑ b, ∑ c, referenceTransitionMatrix x y a k *
          referenceTransitionMatrix x y b j *
            star (referenceTransitionMatrix x y c l) *
              c3ReferenceCovariantTwoTensorZ ω₀ x
                (c3ForcingHessianInChart G x)
                (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y) a b c) :
    ForcingFrameBound ω₀ G y
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y) P A ↔
      ForcingFrameBound ω₀ G x
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)
        (referenceTransitionMatrix x y * P) A := by
  let J : Matrix (Fin n) (Fin n) ℂ := referenceTransitionMatrix x y
  let zY := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y
  let zX := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y
  have hH' : ∀ j l,
      c3ForcingHessianInChart G y zY j l =
        ∑ a, ∑ b, J a j * star (J b l) *
          c3ForcingHessianInChart G x zX a b := by
    simpa [J, zY, zX] using hH
  have hD' : ∀ k j l,
      c3ReferenceCovariantTwoTensorZ ω₀ y (c3ForcingHessianInChart G y)
          zY k j l =
        ∑ a, ∑ b, ∑ c, J a k * J b j * star (J c l) *
          c3ReferenceCovariantTwoTensorZ ω₀ x (c3ForcingHessianInChart G x)
            zX a b c := by
    simpa [J, zY, zX] using hD
  have h2 : ∀ j l,
      c3TwoCovariantFrame P (c3ForcingHessianInChart G y zY) j l =
        c3TwoCovariantFrame (J * P) (c3ForcingHessianInChart G x zX) j l := by
    intro j l
    change (∑ a, ∑ b, P a j * star (P b l) *
        c3ForcingHessianInChart G y zY a b) =
      (∑ a, ∑ b, (J * P) a j * star ((J * P) b l) *
        c3ForcingHessianInChart G x zX a b)
    simp_rw [hH']
    simp only [Matrix.mul_apply, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
    let f : Fin n → Fin n → Fin n → Fin n → ℂ := fun i m a b =>
      P i j * star (P m l) * J a i * star (J b m) *
        c3ForcingHessianInChart G x zX a b
    calc
      _ = ∑ i, ∑ m, ∑ a, ∑ b, f i m a b := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro m hm
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        ring
      _ = ∑ a, ∑ b, ∑ m, ∑ i, f i m a b := sum_permuteFour f
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        apply Finset.sum_congr rfl
        intro m hm
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have h3 : ∀ k j l,
      c3ThreeCovariantFrame P
          (c3ReferenceCovariantTwoTensorZ ω₀ y (c3ForcingHessianInChart G y) zY) k j l =
        c3ThreeCovariantFrame (J * P)
          (c3ReferenceCovariantTwoTensorZ ω₀ x (c3ForcingHessianInChart G x) zX) k j l := by
    intro k j l
    change (∑ a, ∑ b, ∑ c, P a k * P b j * star (P c l) *
        c3ReferenceCovariantTwoTensorZ ω₀ y (c3ForcingHessianInChart G y)
          zY a b c) =
      (∑ a, ∑ b, ∑ c, (J * P) a k * (J * P) b j *
        star ((J * P) c l) *
          c3ReferenceCovariantTwoTensorZ ω₀ x (c3ForcingHessianInChart G x)
            zX a b c)
    simp_rw [hD']
    simp only [Matrix.mul_apply, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
    let f : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → ℂ :=
      fun i m c a b d => P i k * P m j * star (P c l) * J a i * J b m *
        star (J d c) *
          c3ReferenceCovariantTwoTensorZ ω₀ x (c3ForcingHessianInChart G x)
            zX a b d
    calc
      _ = ∑ i, ∑ m, ∑ c, ∑ a, ∑ b, ∑ d, f i m c a b d := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro m hm
        apply Finset.sum_congr rfl
        intro c hc
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        apply Finset.sum_congr rfl
        intro d hd
        ring
      _ = ∑ a, ∑ b, ∑ d, ∑ c, ∑ m, ∑ i, f i m c a b d := sum_permuteSix f
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        apply Finset.sum_congr rfl
        intro d hd
        apply Finset.sum_congr rfl
        intro c hc
        apply Finset.sum_congr rfl
        intro m hm
        apply Finset.sum_congr rfl
        intro i hi
        ring
  change (∀ j l, ‖c3TwoCovariantFrame P
      (c3ForcingHessianInChart G y zY) j l‖ ≤ A) ∧
    (∀ k j l, ‖c3ThreeCovariantFrame P
      (c3ReferenceCovariantTwoTensorZ ω₀ y (c3ForcingHessianInChart G y) zY)
      k j l‖ ≤ A) ↔
    (∀ j l, ‖c3TwoCovariantFrame (J * P)
      (c3ForcingHessianInChart G x zX) j l‖ ≤ A) ∧
    (∀ k j l, ‖c3ThreeCovariantFrame (J * P)
      (c3ReferenceCovariantTwoTensorZ ω₀ x (c3ForcingHessianInChart G x) zX)
      k j l‖ ≤ A)
  constructor
  · rintro ⟨h₂, h₃⟩
    exact ⟨fun j l ↦ by rw [← h2 j l]; exact h₂ j l,
      fun k j l ↦ by rw [← h3 k j l]; exact h₃ k j l⟩
  · rintro ⟨h₂, h₃⟩
    exact ⟨fun j l ↦ by rw [h2 j l]; exact h₂ j l,
      fun k j l ↦ by rw [h3 k j l]; exact h₃ k j l⟩

/-- The very same component bound holds after transporting the frame to a
fixed chart containing y. Source membership must be explicit: the overlap
predicate alone permits total off-source extensions. No smoothness of the
selected moving centre chart is assumed. -/
theorem forcingFrameBound_chart_transition (ω₀ : KahlerForm n M)
    {G : M → ℝ} (hG : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G)
    (x y : M) (hy : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source)
    (V : Set (EuclideanSpace ℂ (Fin n)))
    (hV : ω₀.IsReferenceChartOverlap x y V)
    (P : Matrix (Fin n) (Fin n) ℂ) (A : ℝ) :
    ForcingFrameBound ω₀ G y
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y) P A ↔
      ForcingFrameBound ω₀ G x
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)
        (referenceTransitionMatrix x y * P) A := by
  have hH : ∀ j l,
      c3ForcingHessianInChart G y
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y) j l =
        ∑ a, ∑ b, referenceTransitionMatrix x y a j *
          star (referenceTransitionMatrix x y b l) *
            c3ForcingHessianInChart G x
              (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y) a b := by
    intro j l
    have hmatrix := c3_forcing_chartPotential_hessian_transition G hG x y hy
    have hmatrix' :
        complexHessian
            (G ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).symm)
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y) =
          (referenceTransitionMatrix x y).transpose *
            complexHessian
              (G ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
              (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y) *
            (referenceTransitionMatrix x y).map star := by
      simpa [referenceTransitionMatrix] using hmatrix
    change complexHessian
        (G ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).symm)
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y) j l = _
    rw [hmatrix']
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      c3ForcingHessianInChart, Finset.sum_mul]
    let f : Fin n → Fin n → ℂ := fun a b =>
      referenceTransitionMatrix x y a j * star (referenceTransitionMatrix x y b l) *
        complexHessian
          (G ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y) a b
    calc
      _ = ∑ a, ∑ b, f b a := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        dsimp [f]
        ring
      _ = ∑ a, ∑ b, f a b := by
        rw [Finset.sum_comm]
  have hD := c3_forcing_covariantHessian_transition ω₀ hG x y hy V hV
  exact forcingFrameBound_chart_transition_algebraic ω₀ hG x y hy V hV P A hH hD

end KahlerForm
