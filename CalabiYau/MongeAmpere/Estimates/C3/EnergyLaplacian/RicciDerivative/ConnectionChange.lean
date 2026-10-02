module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.Basic

/-!
# Change the differentiated Ricci tensor to the reference connection

Székelyhidi, §1.4, pp. 10–12, covariant differentiation of a (1,1) tensor;
§3.3, Bianchi line after (3.15), p. 45. The general-MA component identity
is an explicit premise supplied by ComponentIdentity. No Einstein premise.
-/

public section

open scoped Manifold ContDiff ComplexOrder

namespace KahlerForm

private theorem c3ZPartial_differentiableAt {n : ℕ}
    (F : EuclideanSpace ℂ (Fin n) → ℂ) (z : EuclideanSpace ℂ (Fin n))
    (hF : ContDiffAt ℝ ∞ F z) (p : Fin n) :
    DifferentiableAt ℝ (fun w ↦ chartPartialZComplex F w p) z := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ F) z :=
    (hF.fderiv_right (m := ∞)
      (le_of_eq (show (∞ : ℕ∞ω) = ∞ + 1 from rfl).symm)).differentiableAt (by norm_num)
  have he : DifferentiableAt ℝ
      (fun w ↦ fderiv ℝ F w (EuclideanSpace.single p 1)) z :=
    hfd.clm_apply (differentiableAt_const _)
  have hie : DifferentiableAt ℝ
      (fun w ↦ fderiv ℝ F w (Complex.I • EuclideanSpace.single p 1)) z :=
    hfd.clm_apply (differentiableAt_const _)
  unfold chartPartialZComplex
  fun_prop (disch := assumption)

private theorem c3BarPartial_contDiffAt {n : ℕ}
    (F : EuclideanSpace ℂ (Fin n) → ℂ) (z : EuclideanSpace ℂ (Fin n))
    (hF : ContDiffAt ℝ ∞ F z) (q : Fin n) :
    ContDiffAt ℝ ∞ (fun w ↦ chartPartialBarComplex F w q) z := by
  have hfd : ContDiffAt ℝ ∞ (fderiv ℝ F) z := hF.fderiv_right (by simp)
  unfold chartPartialBarComplex
  fun_prop

private theorem c3Curvature_differentiableAt {n : ℕ}
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hg : ∀ a b, ContDiffAt ℝ ∞ (fun w ↦ g w a b) z)
    (hunit : IsUnit (g z)) (p q j k : Fin n) :
    DifferentiableAt ℝ (fun w ↦ chartCurvature g w p q j k) z := by
  have hG1 (a b : Fin n) : ContDiffAt ℝ 1 (fun w ↦ g w a b) z :=
    (hg a b).of_le (by norm_num)
  have hinv (a b : Fin n) : DifferentiableAt ℝ (fun w ↦ (g w)⁻¹ a b) z :=
    chartInv_differentiableAt (fun i l ↦ hG1 i l) hunit a b
  have hZ (a b : Fin n) : DifferentiableAt ℝ
      (fun w ↦ chartPartialZComplex (fun v ↦ g v a b) w p) z :=
    c3ZPartial_differentiableAt _ z (hg a b) p
  have hBar (a b : Fin n) : DifferentiableAt ℝ
      (fun w ↦ chartPartialBarComplex (fun v ↦ g v a b) w q) z :=
    (c3BarPartial_contDiffAt (fun v ↦ g v a b) z (hg a b) q).differentiableAt
      (by norm_num)
  have hBarSmooth (a b : Fin n) : ContDiffAt ℝ ∞
      (fun w ↦ chartPartialBarComplex (fun v ↦ g v a b) w q) z :=
    c3BarPartial_contDiffAt (fun v ↦ g v a b) z (hg a b) q
  have hZBar (a b : Fin n) : DifferentiableAt ℝ
      (fun w ↦ chartPartialZComplex
        (fun t ↦ chartPartialBarComplex (fun v ↦ g v a b) t q) w p) z :=
    c3ZPartial_differentiableAt _ z (hBarSmooth a b) p
  let T (a b : Fin n) (w : EuclideanSpace ℂ (Fin n)) : ℂ :=
    (g w)⁻¹ b a * chartPartialZComplex (fun v ↦ g v j b) w p *
      chartPartialBarComplex (fun v ↦ g v a k) w q
  have hT (a b : Fin n) : DifferentiableAt ℝ (T a b) z :=
    ((hinv b a).mul (hZ j b)).mul (hBar a k)
  have hsumB (a : Fin n) : DifferentiableAt ℝ (fun w ↦ ∑ b, T a b w) z := by
    have heq : (fun w ↦ ∑ b, T a b w) = ∑ b, fun w ↦ T a b w := by
      funext w
      simp
    rw [heq]
    exact DifferentiableAt.sum (u := Finset.univ) (fun b hb ↦ hT a b)
  have hsum : DifferentiableAt ℝ (fun w ↦ ∑ a, ∑ b, T a b w) z := by
    have heq : (fun w ↦ ∑ a, ∑ b, T a b w) = ∑ a, fun w ↦ ∑ b, T a b w := by
      funext w
      simp
    rw [heq]
    exact DifferentiableAt.sum (u := Finset.univ) (fun a ha ↦ hsumB a)
  have hformula : (fun w ↦ chartCurvature g w p q j k) =
      fun w ↦ -chartPartialZComplex
        (fun t ↦ chartPartialBarComplex (fun v ↦ g v j k) t q) w p +
        ∑ a, ∑ b, T a b w := by
    funext w
    rfl
  rw [hformula]
  exact (hZBar j k).neg.add hsum

private theorem c3ComplexHessian_contDiffOn {n : ℕ}
    {U : Set (EuclideanSpace ℂ (Fin n))} {u : EuclideanSpace ℂ (Fin n) → ℝ}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U) (i j : Fin n) :
    ContDiffOn ℝ 1 (fun w ↦ complexHessian u w i j) U := by
  have hD1 : ContDiffOn ℝ 2 (fderiv ℝ u) U :=
    hu.fderiv_of_isOpen hU (WithTop.coe_le_coe.mpr le_top)
  have hD2 : ContDiffOn ℝ 1 (fderiv ℝ (fderiv ℝ u)) U :=
    hD1.fderiv_of_isOpen hU (by norm_num)
  have hQ (v w : EuclideanSpace ℂ (Fin n)) :
      ContDiffOn ℝ 1 (fun x ↦ fderiv ℝ (fderiv ℝ u) x v w) U :=
    (hD2.clm_apply contDiffOn_const).clm_apply contDiffOn_const
  let q : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦
    ((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) : ℂ) +
      fderiv ℝ (fderiv ℝ u) x (Complex.I • EuclideanSpace.single i 1)
        (Complex.I • EuclideanSpace.single j 1) +
      Complex.I * (fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
        (Complex.I • EuclideanSpace.single j 1) -
      fderiv ℝ (fderiv ℝ u) x (Complex.I • EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1))) / 4
  have hq : ContDiffOn ℝ 1 q U := by
    dsimp [q]
    simp only [← Complex.ofRealCLM_apply]
    fun_prop
  apply hq.congr
  intro x hx
  exact complexHessian_apply ((hu.contDiffAt (hU.mem_nhds hx)).of_le
    (WithTop.coe_le_coe.mpr le_top)) i j

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

omit [T2Space M] [CompactSpace M] in
/-- Differentiate an actual open-chart Ricci identity and replace the perturbed
connection by the reference connection plus the connection difference. -/
@[deprecated "unused hypothesis `hφ`; will be removed" (since := "2026-10-02")]
theorem c3BochnerRicciDerivativeTerm_eq_error (ω₀ : KahlerForm n M)
    {G φ : M → ℝ} (hG : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G)
    (hφ : ω₀.IsPotential φ) (x : M)
    (hcomponents : ∀ z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target,
      ∀ j l, c3RicciInChart (c3PerturbedMetricInChart ω₀ φ x) z j l =
        c3RicciInChart (ω₀.metricInChart x) z j l - c3ForcingHessianInChart G x z j l) :
    c3BochnerRicciDerivativeTerm ω₀ φ x = c3RicciDerivativeError ω₀ G φ x := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let z := e x
  let g₀ : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ := fun w ↦ ω₀.metricInChart x w
  let gφ := c3PerturbedMetricInChart ω₀ φ x
  let T := c3ConnectionDifferenceInChart ω₀ φ x
  let R : EuclideanSpace ℂ (Fin n) → Fin n → Fin n → ℂ := c3RicciInChart g₀
  let H : EuclideanSpace ℂ (Fin n) → Fin n → Fin n → ℂ :=
    fun w j l ↦ c3ForcingHessianInChart G x w j l
  have hz : z ∈ e.target := by
    change (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x) x ∈
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target
    exact (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).map_source
      (mem_extChartAt_source (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x)
  have hnear : ∀ᶠ w in nhds z, w ∈ e.target :=
    (isOpen_extChartAt_target x).mem_nhds hz
  have hRicci (j l : Fin n) :
      (fun w ↦ c3RicciInChart gφ w j l) =ᶠ[nhds z]
        (fun w ↦ R w j l - H w j l) := by
    filter_upwards [hnear] with w hw
    exact hcomponents w hw j l
  have hpartial (j l k : Fin n) :
      c3PartialZ (fun w ↦ c3RicciInChart gφ w j l) z k =
        c3PartialZ (fun w ↦ R w j l - H w j l) z k := by
    unfold c3PartialZ
    rw [hRicci j l |>.fderiv_eq (𝕜 := ℝ)]
  have hcenter : ∀ j l, c3RicciInChart gφ z j l = R z j l - H z j l :=
    fun j l ↦ hcomponents z hz j l
  have hRdiff (j l : Fin n) : DifferentiableAt ℝ (fun w ↦ R w j l) z := by
    have hmetric (a b : Fin n) : ContDiffAt ℝ ∞ (fun w ↦ g₀ w a b) z := by
      dsimp [g₀]
      exact (ω₀.contDiffOn_metricInChart x a b).contDiffAt
        ((isOpen_extChartAt_target x).mem_nhds hz)
    have hunit : IsUnit (g₀ z) := (ω₀.posDef_metricInChart x hz).isUnit
    have hInv (a b : Fin n) : DifferentiableAt ℝ (fun w ↦ (g₀ w)⁻¹ a b) z :=
      chartInv_differentiableAt (fun c d ↦ (hmetric c d).of_le (by norm_num))
        hunit a b
    have hCurv (p q : Fin n) : DifferentiableAt ℝ
        (fun w ↦ chartCurvature g₀ w p q j l) z :=
      c3Curvature_differentiableAt g₀ z hmetric hunit p q j l
    dsimp [R]
    change DifferentiableAt ℝ
      (fun w ↦ ∑ p, ∑ q, (g₀ w)⁻¹ q p * chartCurvature g₀ w p q j l) z
    apply DifferentiableAt.fun_sum
    intro p hp
    apply DifferentiableAt.fun_sum
    intro q hq
    exact (hInv q p).mul (hCurv p q)
  have hHdiff (j l : Fin n) : DifferentiableAt ℝ (fun w ↦ H w j l) z := by
    let ψ := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm
    let F : EuclideanSpace ℂ (Fin n) → ℝ := G ∘ ψ
    have hFmd : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F e.target := by
      have hGmd : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G Set.univ :=
        contMDiffOn_univ.mpr hG
      exact hGmd.comp (contMDiffOn_extChartAt_symm x) (by intro w hw; simp)
    have hF : ContDiffOn ℝ ∞ F e.target := hFmd.contDiffOn
    have hH := c3ComplexHessian_contDiffOn
      (isOpen_extChartAt_target x) hF j l
    change DifferentiableAt ℝ (fun w ↦ complexHessian F w j l) z
    exact (hH.contDiffAt ((isOpen_extChartAt_target x).mem_nhds hz)).differentiableAt
      (by norm_num)
  have hpartialSub (j l k : Fin n) :
      c3PartialZ (fun w ↦ R w j l - H w j l) z k =
        c3PartialZ (fun w ↦ R w j l) z k - c3PartialZ (fun w ↦ H w j l) z k := by
    unfold c3PartialZ
    rw [fderiv_fun_sub (hRdiff j l) (hHdiff j l)]
    simp only [sub_apply]
    ring_nf
  have hGamma (r k j : Fin n) :
      c3ChristoffelInChart gφ z r k j =
        c3ChristoffelInChart g₀ z r k j + T z r k j := by
    change c3ChristoffelInChart
        (fun w ↦ ω₀.metricInChart x w +
          complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) w)
        z r k j = c3ChristoffelInChart g₀ z r k j + T z r k j
    dsimp [T, c3ConnectionDifferenceInChart, g₀]
    ring
  have hCov (k j l : Fin n) :
      c3PartialZ (fun w ↦ c3RicciInChart gφ w j l) z k -
        ∑ r, c3ChristoffelInChart gφ z r k j * c3RicciInChart gφ z r l =
      c3ReferenceCovariantTwoTensorZ ω₀ x R z k j l -
        c3ReferenceCovariantTwoTensorZ ω₀ x H z k j l -
          ∑ r, T z r k j * (R z r l - H z r l) := by
    rw [hpartial j l k, hpartialSub j l k]
    simp only [c3ReferenceCovariantTwoTensorZ]
    simp_rw [hGamma, hcenter]
    simp only [mul_sub]
    simp_rw [add_mul]
    dsimp [g₀]
    rw [Finset.sum_sub_distrib]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [Finset.sum_sub_distrib]
    ring_nf
  have hRaised (i j k : Fin n) :
      c3RaisedRicciDerivative gφ z i j k =
        ∑ l, (gφ z)⁻¹ l i *
          (c3ReferenceCovariantTwoTensorZ ω₀ x R z k j l -
            c3ReferenceCovariantTwoTensorZ ω₀ x H z k j l -
              ∑ r, T z r k j * (R z r l - H z r l)) := by
    simp only [c3RaisedRicciDerivative]
    exact Finset.sum_congr rfl (fun l _ ↦ congrArg (fun q : ℂ ↦ (gφ z)⁻¹ l i * q) (hCov k j l))
  unfold c3BochnerRicciDerivativeTerm c3RicciDerivativeError
  dsimp only [e, z, gφ, T, R, H]
  apply congrArg (fun Q : Fin n → Fin n → Fin n → ℂ => (c3Pair gφ z Q (T z)).re)
  funext i j k
  exact hRaised i j k

end KahlerForm
