module

public import CalabiYau.Geometry.Kahler.Volume
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import CalabiYau.Geometry.Manifold.Coordinates.Calculus.FixedBaseDerivative
import CalabiYau.Geometry.Kahler.Laplacian.EuclideanDivergence
import CalabiYau.Geometry.Kahler.Laplacian.Cofactor
import CalabiYau.Geometry.Kahler.Laplacian.ChartGreen

/-!
# The complex Laplacian of a Kähler form

For a Kähler form `ω₀ = i ∑ g_{jk̄} dzⱼ ∧ dz̄ₖ` and a real function `f`,

* `KahlerForm.laplacian ω₀ f = tr_ω₀ (i∂∂̄f) = g^{jk̄} f_{jk̄}`, the complex Laplacian;
* `KahlerForm.gradNormSq ω₀ f = tr_ω₀ (i∂f ∧ ∂̄f) = g^{jk̄} fⱼ f_{k̄} = |∂f|²_ω₀`.

With the Riemannian metric `g(u, v) = ω₀(u, Jv)`, the Laplace–Beltrami operator is
`Δ_g = 2 · laplacian` and `|∇f|²_g = 2 · gradNormSq` (bridge lemmas to the extracted Riemannian
geometry belong to track G). For instance on `ℂ` with `ω₀ = i dz ∧ dz̄`,
`laplacian f = ¼ (f_xx + f_yy)` and `gradNormSq f = ¼ (f_x² + f_y²)`.

The global statements (Green's formula) are the only input from integration theory used by the
Monge–Ampère estimates and by Calabi's uniqueness argument; they follow from Stokes' theorem
and the Kähler identity `∂ₗ g_{jk̄} = ∂ⱼ g_{lk̄}`.
-/
@[expose] public section

open scoped Manifold ContDiff ComplexOrder
open Set MeasureTheory ContinuousAlternatingMap
namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] (ω₀ : KahlerForm n M)
/-- The complex Laplacian `Δ_ω₀ f = tr_ω₀ (i∂∂̄f) = g^{jk̄} f_{jk̄}`. -/
noncomputable def laplacian (f : M → ℝ) (x : M) : ℝ :=
  relTrace (ω₀ x) (mddbar n f x)
/-- `|∂f|²_ω₀ = tr_ω₀ (i∂f ∧ ∂̄f) = g^{jk̄} fⱼ f_{k̄}`. -/
noncomputable def gradNormSq (f : M → ℝ) (x : M) : ℝ :=
  relTrace (ω₀ x) (mdWedgeDBar n f x)
variable {ω₀} {f g : M → ℝ}

/-- The Laplacian in a chart: `Δ f = re tr (g⁻¹ (f_{jk̄}))`. -/
theorem laplacian_eq_inChart (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f) (x : M)
    {y : M} (hy : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source) :
    ω₀.laplacian f y = RCLike.re
      ((ω₀.metricInChart x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y))⁻¹ *
        complexHessian (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)).trace := by
  let ψ := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let z := ψ y
  have hy' : y ∈ ψ.source := by simpa [ψ, ← extChartAt_source] using hy
  have hz : z ∈ ψ.target := ψ.map_source hy'
  have hzpoint : ψ.symm z = y := ψ.left_inv hy'
  have hychart : y ∈
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).source := by simp
  have hyC : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source := by
    simpa [extChartAt_real_eq, ← extChartAt_source] using hy
  have hyCy : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source := by simp
  have hOverlap : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source ∩
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).source := ⟨hy', hychart⟩
  let A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n) := {
    toLinearEquiv := {
      toFun := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y
      invFun := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y x y
      left_inv := by
        intro v
        have htriple : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source ∩
          (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source ∩
            (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source := by
          exact ⟨⟨hyC, hyCy⟩, hyC⟩
        have hc := tangentCoordChange_comp (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
          (w := x) (x := y) (y := x) (z := y) (v := v) htriple
        calc
          _ = tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x x y v := hc
          _ = v := tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
            (x := x) (z := y) hyC
      right_inv := by
        intro v
        have htriple : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source ∩
            (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source ∩
            (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source := by
          exact ⟨⟨hyCy, hyC⟩, hyCy⟩
        have hc := tangentCoordChange_comp (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
          (w := y) (x := x) (y := y) (z := y) (v := v) htriple
        calc
          _ = tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y y y v := hc
          _ = v := tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
            (x := y) (z := y) (by simp)
      map_add' := by intro u v; exact (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y).map_add u v
      map_smul' := by intro c v; exact (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y).map_smul c v
    }
    continuous_toFun := (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y).continuous
    continuous_invFun := (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y x y).continuous
  }
  have hA : fderiv ℝ
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y ∘
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z =
      (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ := by
    have hdef : tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y =
        fderiv ℝ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y ∘
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z := by
      rw [tangentCoordChange_def]
      simp [z, ψ]
    calc
      _ = tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y := hdef.symm
      _ = (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y).restrictScalars ℝ :=
        tangentCoordChange_real_eq hOverlap
      _ = _ := rfl
  have hrep (β : FormField (EuclideanSpace ℂ (Fin n)) M 2) :
      β.chartRep x z = (β y).compContinuousLinearMap
        ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ) := by
    rw [FormField.chartRep_eq_chartRep_comp (x := x) (x' := y) (z := z) hz]
    · rw [hzpoint, FormField.chartRep_self, hA]
    · have heq : (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z = y := by
        simpa [ψ] using hzpoint
      rw [heq]
      exact hychart
  have htrace := ContinuousAlternatingMap.relTrace_compContinuousLinearMap
    (ω₀.isOneOne y) (isOneOne_mddbar hf y) A
  have hddbar := chartRep_mddbar hf x hz
  calc
    ω₀.laplacian f y = relTrace (ω₀ y) (mddbar n f y) := rfl
    _ = relTrace ((ω₀ y).compContinuousLinearMap
          ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ))
        ((mddbar n f y).compContinuousLinearMap
          ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)) :=
      htrace.symm
    _ = RCLike.re
        ((ω₀.metricInChart x z)⁻¹ * complexHessian (f ∘ ψ.symm) z).trace := by
      rw [← hrep ω₀.toFormField, ← hrep (mddbar n f), hddbar]
      rfl

theorem laplacian_add (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ g) :
    ω₀.laplacian (f + g) = ω₀.laplacian f + ω₀.laplacian g := by
  funext x
  simp [laplacian, mddbar_add hf hg, ContinuousAlternatingMap.relTrace_add]

theorem laplacian_smul (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f) (c : ℝ) :
    ω₀.laplacian (c • f) = c • ω₀.laplacian f := by
  funext x
  simp [laplacian, mddbar_smul hf c, ContinuousAlternatingMap.relTrace_smul]

@[simp]
theorem laplacian_const (c : ℝ) : ω₀.laplacian (fun _ ↦ c) = 0 := by
  funext x
  simp [laplacian]

@[simp]
theorem laplacian_add_const (c : ℝ) : ω₀.laplacian (fun x ↦ f x + c) = ω₀.laplacian f := by
  funext x
  simp [laplacian]

set_option maxHeartbeats 1000000 in
theorem contMDiff_laplacian (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (ω₀.laplacian f) := by
  let I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
  have hchart (x : M) :
      ContDiffOn ℝ ∞ (fun z ↦ ω₀.laplacian f ((extChartAt I x).symm z))
        (extChartAt I x).target := by
    let e := extChartAt I x
    let u : EuclideanSpace ℂ (Fin n) → ℝ := f ∘ e.symm
    have huMD : ContMDiffOn I 𝓘(ℝ) ∞ u e.target := by
      have hfun : ContMDiffOn I 𝓘(ℝ) ∞ f Set.univ := contMDiffOn_univ.mpr hf
      exact hfun.comp (contMDiffOn_extChartAt_symm x) (by intro z hz; simp)
    have hu : ContDiffOn ℝ ∞ u e.target := huMD.contDiffOn
    have h_inf : (∞ : ℕ∞ω) + 1 ≤ ∞ := le_of_eq (show (∞ : ℕ∞ω) = ∞ + 1 from rfl).symm
    have hfd : ContDiffOn ℝ ∞ (fderiv ℝ u) e.target :=
      hu.fderiv_of_isOpen (isOpen_extChartAt_target x) h_inf
    have hfd₂ : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ u)) e.target :=
      hfd.fderiv_of_isOpen (isOpen_extChartAt_target x) h_inf
    let G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
      fun z ↦ ω₀.metricInChart x z
    have hG_entry (j k : Fin n) : ContDiffOn ℝ ∞ (fun z ↦ G z j k) e.target := by
      exact ω₀.contDiffOn_metricInChart x j k
    have hdet : ContDiffOn ℝ ∞ (fun z ↦ (G z).det) e.target := by
      simp_rw [Matrix.det_apply]
      fun_prop (disch := assumption)
    have hdet_ne {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ e.target) : (G z).det ≠ 0 := by
      have hpos := (RCLike.pos_iff.mp (ω₀.posDef_metricInChart x hz).det_pos).1
      exact fun h ↦ hpos.ne' (congrArg RCLike.re h)
    have hdetInv : ContDiffOn ℝ ∞ (fun z ↦ ((G z).det)⁻¹) e.target :=
      hdet.inv (fun z hz ↦ hdet_ne hz)
    have hUpdate (r c s t : Fin n) :
        ContDiffOn ℝ ∞ (fun z ↦ (G z).updateRow r (Pi.single c (1 : ℂ)) s t) e.target := by
      simp_rw [Matrix.updateRow_apply]
      by_cases hrs : s = r
      · subst s
        simp only [Pi.single_apply]
        exact contDiffOn_const
      · simp only [if_neg hrs]
        exact hG_entry s t
    have hAdj_entry (j k : Fin n) :
        ContDiffOn ℝ ∞ (fun z ↦ (G z).adjugate j k) e.target := by
      simp_rw [Matrix.adjugate_apply, Matrix.det_apply']
      apply ContDiffOn.sum
      intro σ hσ
      have hp : ContDiffOn ℝ ∞ (fun z ↦
          ∏ i, (G z).updateRow k (Pi.single j (1 : ℂ)) (σ i) i) e.target := by
        exact contDiffOn_prod (t := Finset.univ) (fun i hi ↦ hUpdate k j (σ i) i)
      change ContDiffOn ℝ ∞ (fun z ↦
        ((Equiv.Perm.sign σ : ℤ) : ℂ) *
          ∏ i, (G z).updateRow k (Pi.single j (1 : ℂ)) (σ i) i) e.target
      exact contDiffOn_const.mul hp
    have hInv_entry (j k : Fin n) :
        ContDiffOn ℝ ∞ (fun z ↦ (G z)⁻¹ j k) e.target := by
      have hmul : ContDiffOn ℝ ∞
          (fun z ↦ ((G z).det)⁻¹ * (G z).adjugate j k) e.target :=
        hdetInv.mul (hAdj_entry j k)
      refine hmul.congr ?_
      intro z hz
      rw [Matrix.inv_def]
      simp [Matrix.smul_apply, smul_eq_mul]
    have hH_entry (j k : Fin n) :
        ContDiffOn ℝ ∞ (fun z ↦ (complexHessian u z) j k) e.target := by
      have hformula : ContDiffOn ℝ ∞ (fun z ↦
          ((fderiv ℝ (fderiv ℝ u) z (EuclideanSpace.single j 1) (EuclideanSpace.single k 1) : ℂ) +
            fderiv ℝ (fderiv ℝ u) z (Complex.I • EuclideanSpace.single j 1)
              (Complex.I • EuclideanSpace.single k 1) +
            Complex.I * (fderiv ℝ (fderiv ℝ u) z (EuclideanSpace.single j 1)
                (Complex.I • EuclideanSpace.single k 1) -
              fderiv ℝ (fderiv ℝ u) z (Complex.I • EuclideanSpace.single j 1)
                (EuclideanSpace.single k 1))) / 4) e.target := by
        simp only [← Complex.ofRealCLM_apply]
        fun_prop
      refine hformula.congr ?_
      intro z hz
      have hu₂ : ContDiffAt ℝ 2 u z := by
        exact (hu.contDiffAt ((isOpen_extChartAt_target x).mem_nhds hz)).of_le
          (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
      change (complexHessian u z) j k = _
      exact complexHessian_apply hu₂ j k
    have htraceEntry (i j : Fin n) : ContDiffOn ℝ ∞
        (fun z ↦ Complex.reCLM ((G z)⁻¹ i j * (complexHessian u z) j i)) e.target := by
      exact Complex.reCLM.contDiff.comp_contDiffOn ((hInv_entry i j).mul (hH_entry j i))
    have htraceInner (i : Fin n) : ContDiffOn ℝ ∞ (fun z ↦
        ∑ j, Complex.reCLM ((G z)⁻¹ i j * (complexHessian u z) j i)) e.target := by
      apply ContDiffOn.sum
      intro j hj
      exact htraceEntry i j
    have htrace : ContDiffOn ℝ ∞ (fun z ↦
        ∑ i, ∑ j, Complex.reCLM ((G z)⁻¹ i j * (complexHessian u z) j i)) e.target := by
      apply ContDiffOn.sum
      intro i hi
      exact htraceInner i
    have htrace' : ContDiffOn ℝ ∞
        (fun z ↦ RCLike.re (((G z)⁻¹ * complexHessian u z).trace)) e.target := by
      change ContDiffOn ℝ ∞
        (fun z ↦ Complex.reCLM (((G z)⁻¹ * complexHessian u z).trace)) e.target
      apply htrace.congr
      intro z hz
      simp [Matrix.mul_apply, Matrix.trace, Complex.reCLM_apply]
    refine htrace'.congr ?_
    intro z hz
    have hy : e.symm z ∈ e.source := e.map_target hz
    have hy' : e.symm z ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source := by
      rw [← extChartAt_source (I := I)]
      exact hy
    rw [ω₀.laplacian_eq_inChart hf x (y := e.symm z) hy']
    rw [e.right_inv hz]
  rw [contMDiff_iff]
  refine ⟨?_, ?_⟩
  · apply continuous_iff_continuousAt.2
    intro x
    let e := extChartAt I x
    let g := fun z ↦ ω₀.laplacian f (e.symm z)
    have hg : ContDiffAt ℝ ∞ g (e x) :=
      (hchart x).contDiffAt ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))
    have hgcomp : ContinuousAt (fun p ↦ g (e p)) x :=
      hg.continuousAt.comp
        (contMDiffAt_extChartAt (I := I) (n := ∞) (x := x)).continuousAt
    have hEq : (fun p ↦ g (e p)) =ᶠ[nhds x] ω₀.laplacian f := by
      filter_upwards [(isOpen_extChartAt_source (I := I) x).mem_nhds
        (mem_extChartAt_source (I := I) x)] with p hp
      dsimp [g]
      rw [e.left_inv hp]
    exact hgcomp.congr_of_eventuallyEq hEq.symm
  · intro x y
    simp only [mfld_simps, chartAt_self_eq]
    have hI : (I.symm : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)) = id := by rfl
    have hx := hchart x
    simp only [mfld_simps] at hx
    rw [hI] at hx
    change ContDiffOn ℝ ∞ (fun z ↦ ω₀.laplacian f
      ((chartAt (EuclideanSpace ℂ (Fin n)) x).symm z))
      (chartAt (EuclideanSpace ℂ (Fin n)) x).target
    simpa [ModelWithCorners.range_eq_univ] using hx

theorem contMDiff_gradNormSq (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (ω₀.gradNormSq f) := by
  have hpow : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (fun x ↦ f x ^ 2) := by
    have hmul : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (f * f) := hf.mul hf
    have heq : (fun x ↦ f x ^ 2) = f * f := by
      funext x
      simp [pow_two]
    refine hmul.congr ?_
    intro x
    exact congrFun heq x
  have hΔpow := contMDiff_laplacian (ω₀ := ω₀) hpow
  have hΔf := contMDiff_laplacian (ω₀ := ω₀) hf
  have hidentity (x : M) : ω₀.gradNormSq f x =
      (ω₀.laplacian (fun x ↦ f x ^ 2) x - 2 * f x * ω₀.laplacian f x) / 2 := by
    have hchain : ω₀.laplacian (fun x ↦ f x ^ 2) x =
        2 * f x * ω₀.laplacian f x + 2 * ω₀.gradNormSq f x := by
      rw [laplacian]
      rw [show (fun x ↦ f x ^ 2) = (fun t : ℝ ↦ t ^ 2) ∘ f by rfl]
      have hdd := mddbar_comp_real (n := n) hf
        (h := fun t : ℝ ↦ t ^ 2) (contDiff_id.pow 2)
      rw [congrFun hdd x]
      simp only [ContinuousAlternatingMap.relTrace_add,
        ContinuousAlternatingMap.relTrace_smul]
      have hd1 : deriv (fun t : ℝ ↦ t ^ 2) = fun t ↦ 2 * t := by
        funext t
        simp
      have hd2' : deriv (fun t : ℝ ↦ 2 * t) = fun _ ↦ 2 := by
        funext t
        simp
      rw [hd1, hd2']
      simp [laplacian, gradNormSq]
    field_simp
    linarith
  have hfun : ω₀.gradNormSq f = fun x ↦
      (ω₀.laplacian (fun x ↦ f x ^ 2) x - 2 * f x * ω₀.laplacian f x) / 2 := by
    funext x
    exact hidentity x
  rw [hfun]
  have hterm : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (fun x ↦ 2 * f x * ω₀.laplacian f x) := by
    exact (contMDiff_const.mul hf).mul hΔf
  have hsub := hΔpow.sub hterm
  simpa using hsub.div_const (2 : ℝ)

theorem gradNormSq_nonneg (f : M → ℝ) (x : M) : 0 ≤ ω₀.gradNormSq f x := by
  have hnonneg := isNonneg_mdWedgeDBar (n := n) f
  exact ContinuousAlternatingMap.relTrace_nonneg (ω₀.isPositive x) (hnonneg x)

/-- `|∂f|² = 0` exactly at the critical points of `f`. -/
theorem gradNormSq_eq_zero_iff (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f)
    (x : M) :
    ω₀.gradNormSq f x = 0 ↔ mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) f x = 0 := by
  change ContinuousAlternatingMap.relTrace (ω₀ x)
      (dWedgeDBar (fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x))) = 0 ↔ _
  rw [ContinuousAlternatingMap.relTrace_dWedgeDBar_eq_zero_iff (ω₀.isPositive x)]
  have hdiff : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) f x :=
    hf.mdifferentiableAt (by norm_num)
  simp [mfderiv, hdiff, writtenInExtChartAt, chartAt_self_eq]
  rfl

/-- Chain rule: `Δ(h ∘ f) = h'(f) Δf + h''(f) |∂f|²`. -/
theorem laplacian_comp (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f) {h : ℝ → ℝ}
    (hh : ContDiff ℝ 2 h) (x : M) :
    ω₀.laplacian (h ∘ f) x =
      deriv h (f x) * ω₀.laplacian f x + deriv (deriv h) (f x) * ω₀.gradNormSq f x := by
  rw [laplacian, mddbar_comp_real hf hh]
  simp only [ContinuousAlternatingMap.relTrace_add,
    ContinuousAlternatingMap.relTrace_smul]
  rfl

/-- **Maximum principle** (pointwise): at a local maximum, `Δf ≤ 0`; more generally
`tr_α (i∂∂̄f) ≤ 0` for every positive `(1,1)`-form `α`. -/
theorem relTrace_mddbar_nonpos_of_isLocalMax
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f) {x : M} (hx : IsLocalMax f x)
    {α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ} (hα : α.IsPositive) :
    relTrace α (mddbar n f x) ≤ 0 := by
  let ψ := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let z := ψ x
  let f' := f ∘ ψ.symm
  have hcoord :=
    (contMDiffAt_iff_of_mem_source (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
      (I' := 𝓘(ℝ)) (x := x) (x' := x) (y := f x) (by simp) (by simp)).1 (hf x)
  have hC2 : ContDiffAt ℝ 2 f' z := by
    have hle : (2 : ℕ∞ω) ≤ ∞ := by
      change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top
    have h := hcoord.2.of_le hle
    have h' : ContDiffWithinAt ℝ 2 f' Set.univ z := by
      simpa [f', ψ, z, chartAt_self_eq, ModelWithCorners.range_eq_univ] using h
    exact contDiffWithinAt_univ.mp h'
  have hmax : IsLocalMax f' z := by
    have hx' : IsLocalMax f (ψ.symm z) := by simpa [ψ, z] using hx
    exact hx'.comp_continuous (continuousAt_extChartAt_symm x)
  have hnonneg : (-ddbar f' z).IsNonneg :=
    isNonneg_neg_ddbar_of_isLocalMax hC2 hmax
  have htrace : 0 ≤ relTrace α (-ddbar f' z) :=
    ContinuousAlternatingMap.relTrace_nonneg hα hnonneg
  rw [ContinuousAlternatingMap.relTrace_neg] at htrace
  have htrace' : relTrace α (ddbar f' z) ≤ 0 := by linarith
  simpa [mddbar, f', ψ, z] using htrace'

theorem laplacian_nonpos_of_isLocalMax
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f) {x : M} (hx : IsLocalMax f x) :
    ω₀.laplacian f x ≤ 0 :=
  relTrace_mddbar_nonpos_of_isLocalMax hf hx (ω₀.isPositive x)

/-! ### Green's formula -/

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M]

theorem integral_laplacian (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f) :
    ∫ x, ω₀.laplacian f x ∂ω₀.volume = 0 := by
  classical
  have hgradDiag (i : M) (g : M → ℝ)
      (hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ g)
      {z : EuclideanSpace ℂ (Fin n)}
      (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target) :
      ω₀.gradNormSq g ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm z) =
        chartGradientPair (ω₀.metricInChart i)
          (fun w ↦ g ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm w))
          (fun w ↦ g ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm w)) z := by
    change relTrace (ω₀ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm z))
      (mdWedgeDBar n g ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm z)) = _
    exact (ω₀.chartGradientPair_eq_relTrace_mdWedgeDBar i g hg hz).symm
  have hgradPolar (i : M) (u v : M → ℝ)
      (hu : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u)
      (hv : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ v)
      {z : EuclideanSpace ℂ (Fin n)}
      (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target) :
      chartGradientPair (ω₀.metricInChart i)
          (fun w ↦ u ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm w))
          (fun w ↦ v ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm w)) z =
        (ω₀.gradNormSq (u + v)
            ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm z) -
          ω₀.gradNormSq u ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm z) -
          ω₀.gradNormSq v ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm z)) / 2 := by
    simpa [gradNormSq] using
      ω₀.chartGradientPair_polarization_relTrace i u v hu hv hz
  let ρ : SmoothPartitionOfUnity M 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M univ :=
    (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M).choose
  have hρ : ρ.IsSubordinate fun i ↦ (chartAt (EuclideanSpace ℂ (Fin n)) i).source :=
    (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M).choose_spec
  let S : Finset M :=
    (ρ.locallyFinite.closure.finite_nonempty_inter_compact isCompact_univ).toFinset
  let μ : M → Measure M := fun i ↦
    (ω₀.chartVolume i).withDensity fun y ↦ ENNReal.ofReal (ρ i y)
  have hρzero (i : M) (hi : i ∉ S) : ∀ y, ρ i y = 0 := by
    intro y
    by_contra hne
    have hy : y ∈ tsupport (ρ i) := subset_tsupport _ hne
    have hiS : i ∈ (ρ.locallyFinite.closure.finite_nonempty_inter_compact
        isCompact_univ).toFinset := by
      simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      exact ⟨y, hy, mem_univ y⟩
    exact hi (by simpa only [S] using hiS)
  have hμzero (i : M) (hi : i ∉ S) : μ i = 0 := by
    have hfun : (fun y ↦ ENNReal.ofReal (ρ i y)) = 0 := by
      funext y
      simp [hρzero i hi y]
    simp [μ, hfun]
  have hvol : ω₀.volume = Measure.sum μ := by
    simpa only [μ] using ω₀.volume_eq_sum_of_isSubordinate ρ hρ
  have hcont : Continuous (ω₀.laplacian f) :=
    (ω₀.contMDiff_laplacian hf).continuous
  have hcompact : HasCompactSupport (ω₀.laplacian f) :=
    HasCompactSupport.of_compactSpace _
  have hint : Integrable (ω₀.laplacian f) ω₀.volume :=
    hcont.integrable_of_hasCompactSupport hcompact
  have hsum := MeasureTheory.hasSum_integral_measure (μ := μ) hint
  have hsum' :
      ∑' i : M, ∫ y, ω₀.laplacian f y ∂μ i =
        ∫ x, ω₀.laplacian f x ∂ω₀.volume := by
    rw [hvol]
    exact hsum.tsum_eq
  have hsum_fin :
      ∑' i : M, ∫ y, ω₀.laplacian f y ∂μ i =
        ∑ i ∈ S, ∫ y, ω₀.laplacian f y ∂μ i := by
    rw [tsum_eq_sum (s := S) (fun i hi ↦ by simp [hμzero i hi])]
  have hρfinsupport (x : M) : ρ.finsupport x ⊆ S := by
    intro i hi
    by_contra hiS
    have hz : ρ i x = 0 := hρzero i hiS x
    have hnot : i ∉ ρ.finsupport x := by
      simp only [SmoothPartitionOfUnity.mem_finsupport]
      simp [hz]
    exact hnot hi
  have hρsum (x : M) : ∑ i ∈ S, ρ i x = 1 :=
    ρ.sum_finsupport' (x₀ := x) (mem_univ x) (hρfinsupport x)
  let crossGrad : M → M → ℝ := fun i y ↦
    (ω₀.gradNormSq (fun x ↦ ρ i x + f x) y -
      ω₀.gradNormSq (ρ i) y - ω₀.gradNormSq f y) / 2
  have hvolumeDensityCont (i : M) :
      ContinuousOn (ω₀.volumeDensityInChart i)
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target := by
    change ContinuousOn
      (fun z ↦ (2 : ℝ) ^ n * (ω₀.metricInChart i z).det.re)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target
    have hdet : ContinuousOn (fun z ↦ (ω₀.metricInChart i z).det)
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target := by
      classical
      simp_rw [Matrix.det_apply]
      exact continuousOn_finsetSum Finset.univ fun σ _ ↦
        continuousOn_const.smul <| continuousOn_finsetProd Finset.univ fun j _ ↦
          (ω₀.contDiffOn_metricInChart i (σ j) j).continuousOn
    have hre : ContinuousOn (fun z ↦ (ω₀.metricInChart i z).det.re)
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target :=
      Complex.continuous_re.continuousOn.comp hdet (fun _ _ ↦ Set.mem_univ _)
    exact continuousOn_const.mul hre
  have hchartTerm (i : M) :
      ∫ y, ω₀.laplacian f y ∂μ i =
        -∫ y, crossGrad i y ∂ω₀.volume.restrict
          (chartAt (EuclideanSpace ℂ (Fin n)) i).source := by
    let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i
    let ν : Measure (EuclideanSpace ℂ (Fin n)) :=
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))).restrict c.target
    let d : EuclideanSpace ℂ (Fin n) → ENNReal :=
      fun z ↦ ENNReal.ofReal (ω₀.volumeDensityInChart i z)
    let ψ : M → ℝ := fun y ↦ ρ i y * ω₀.laplacian f y
    let χ : EuclideanSpace ℂ (Fin n) → ℝ :=
      fun z ↦ if z ∈ c.target then ρ i (c.symm z) else 0
    have hρsource : tsupport (ρ i) ⊆ c.source := by
      simpa [c, ← extChartAt_source] using hρ i
    have hρcompact : IsCompact (tsupport (ρ i)) :=
      (isClosed_tsupport (ρ i)).isCompact
    let K : Set (EuclideanSpace ℂ (Fin n)) := c '' tsupport (ρ i)
    have hK : IsCompact K :=
      hρcompact.image_of_continuousOn ((continuousOn_extChartAt i).mono hρsource)
    have hKtarget : K ⊆ c.target := by
      rintro z ⟨y, hy, rfl⟩
      exact c.map_source (hρsource hy)
    have hχsupport : Function.support χ ⊆ K := by
      intro z hz
      change χ z ≠ 0 at hz
      have hzt : z ∈ c.target := by
        by_contra hnot
        exact hz (by simp [χ, hnot])
      have hy : c.symm z ∈ tsupport (ρ i) := by
        apply subset_tsupport
        have hρnz : ρ i (c.symm z) ≠ 0 := by
          simpa [χ, hzt] using hz
        exact hρnz
      exact ⟨c.symm z, hy, c.right_inv hzt⟩
    have hχtsupport : tsupport χ ⊆ K := by
      rw [tsupport]
      exact (closure_mono hχsupport).trans hK.isClosed.closure_subset
    have hχcompact : HasCompactSupport χ := HasCompactSupport.intro hK (by
      intro z hz
      by_contra hne
      exact hz (hχsupport (Function.mem_support.mpr hne)))
    have hχtarget : tsupport χ ⊆ c.target := hχtsupport.trans hKtarget
    have hχon : ContDiffOn ℝ ∞ (fun z ↦ ρ i (c.symm z)) c.target := by
      have hρMD : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (ρ i) Set.univ :=
        contMDiffOn_univ.mpr (ρ i).contMDiff
      exact (hρMD.comp (contMDiffOn_extChartAt_symm i)
        (by intro z hz; simp)).contDiffOn
    have hχcont : ContDiff ℝ ∞ χ := by
      apply contDiff_iff_contDiffAt.mpr
      intro z
      by_cases hz : z ∈ c.target
      · have heq : χ =ᶠ[nhds z] fun w ↦ ρ i (c.symm w) := by
          filter_upwards [(isOpen_extChartAt_target i).mem_nhds hz] with w hw
          have hw' : w ∈ c.target := by simpa [c] using hw
          simp [χ, hw']
        exact (hχon.contDiffAt ((isOpen_extChartAt_target i).mem_nhds hz)).congr_of_eventuallyEq heq
      · have hzK : z ∉ K := fun hzK ↦ hz (hKtarget hzK)
        have heq : χ =ᶠ[nhds z] fun _ ↦ (0 : ℝ) := by
          filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hzK] with w hw
          have hwzero : χ w = 0 := by
            by_contra hne
            exact hw (hχsupport (Function.mem_support.mpr hne))
          exact hwzero
        exact (contDiff_const.contDiffAt).congr_of_eventuallyEq heq
    have hplateau : ∃ β : EuclideanSpace ℂ (Fin n) → ℝ,
        ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧ tsupport β ⊆ c.target ∧
          ∃ O : Set (EuclideanSpace ℂ (Fin n)), IsOpen O ∧ K ⊆ O ∧ O ⊆ c.target ∧
            ∀ z ∈ O, β z = 1 := by
      by_cases hKne : K.Nonempty
      · let Ix := {z // z ∈ K}
        have hbump (x : Ix) : ∃ b : EuclideanSpace ℂ (Fin n) → ℝ,
            tsupport b ⊆ c.target ∧ HasCompactSupport b ∧ ContDiff ℝ ∞ b ∧
              Set.range b ⊆ Set.Icc 0 1 ∧ b x = 1 := by
          exact exists_contDiff_tsupport_subset
            ((isOpen_extChartAt_target i).mem_nhds (hKtarget x.2))
        choose b hbsupp hbcomp hbcont hbrange hbvalue using hbump
        let V : Ix → Set (EuclideanSpace ℂ (Fin n)) := fun x ↦ {z | 0 < b x z}
        have hVopen (x : Ix) : IsOpen (V x) :=
          isOpen_lt continuous_const (hbcont x).continuous
        have hcover : K ⊆ ⋃ x : Ix, V x := by
          intro z hz
          let x : Ix := ⟨z, hz⟩
          refine Set.mem_iUnion.2 ⟨x, ?_⟩
          change 0 < b x z
          rw [hbvalue x]
          norm_num
        obtain ⟨t, ht⟩ := hK.elim_finite_subcover V hVopen hcover
        let s : EuclideanSpace ℂ (Fin n) → ℝ := fun z ↦ ∑ x ∈ t, b x z
        have hscont : ContDiff ℝ ∞ s := by
          dsimp [s]
          exact ContDiff.sum fun x hx ↦ hbcont x
        have hbn (x : Ix) (z : EuclideanSpace ℂ (Fin n)) : 0 ≤ b x z :=
          (hbrange x ⟨z, rfl⟩).1
        have hsnonneg (z : EuclideanSpace ℂ (Fin n)) : 0 ≤ s z := by
          simp only [s]
          exact Finset.sum_nonneg fun x hx ↦ hbn x z
        have hspos {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ K) : 0 < s z := by
          rcases Set.mem_iUnion₂.1 (ht hz) with ⟨x, hxt, hxV⟩
          have hbx : 0 < b x z := by simpa [V] using hxV
          change 0 < ∑ x ∈ t, b x z
          exact (Finset.sum_pos_iff_of_nonneg (fun y hy ↦ hbn y z)).2 ⟨x, hxt, hbx⟩
        let K' : Set (EuclideanSpace ℂ (Fin n)) := ⋃ x ∈ t, tsupport (b x)
        have hK' : IsCompact K' :=
          t.isCompact_biUnion fun x hx ↦ hbcomp x
        have hK'target : K' ⊆ c.target := by
          intro z hz
          rcases Set.mem_iUnion₂.1 hz with ⟨x, hxt, hzx⟩
          exact hbsupp x hzx
        have hsuppS : Function.support s ⊆ K' := by
          intro z hz
          change s z ≠ 0 at hz
          by_contra hzK'
          have hzero (x : Ix) (hx : x ∈ t) : b x z = 0 := by
            have hnot : z ∉ tsupport (b x) := by
              intro hz'
              exact hzK' (Set.mem_iUnion₂.2 ⟨x, hx, hz'⟩)
            have hnot' : z ∉ Function.support (b x) := fun hz' ↦ hnot (subset_tsupport _ hz')
            exact not_not.mp hnot'
          have hsumzero : s z = 0 := by
            dsimp [s]
            exact Finset.sum_eq_zero fun x hx ↦ hzero x hx
          exact hz hsumzero
        have hsZero {z : EuclideanSpace ℂ (Fin n)} (hz : z ∉ K') : s z = 0 := by
          by_contra hne
          exact hz (hsuppS (Function.mem_support.mpr hne))
        obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hKne hscont.continuous.continuousOn
        let δ : ℝ := s z₀ / 2
        have hδ : 0 < δ := by
          dsimp [δ]
          linarith [hspos hz₀]
        let β : EuclideanSpace ℂ (Fin n) → ℝ := fun z ↦ Real.smoothTransition (s z / δ)
        have hβcont : ContDiff ℝ ∞ β := by
          dsimp [β]
          exact Real.smoothTransition.contDiff.comp (hscont.mul contDiff_const)
        have hβone {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ K) : β z = 1 := by
          dsimp [β, δ]
          rw [Real.smoothTransition.one_of_one_le]
          apply (one_le_div hδ).2
          calc
            δ ≤ s z₀ := by dsimp [δ]; linarith [hspos hz₀]
            _ ≤ s z := hmin hz
        have hβloc {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ K) :
            β =ᶠ[nhds z] fun _ ↦ (1 : ℝ) := by
          have hzδ : δ < s z := by
            calc
              δ < s z₀ := by dsimp [δ]; linarith [hspos hz₀]
              _ ≤ s z := hmin hz
          have hneigh : {w | δ < s w} ∈ nhds z :=
            (isOpen_lt continuous_const hscont.continuous).mem_nhds hzδ
          filter_upwards [hneigh] with w hw
          dsimp [β]
          exact Real.smoothTransition.one_of_one_le ((one_le_div hδ).2 hw.le)
        have hβsupport : Function.support β ⊆ K' := by
          intro z hz
          change β z ≠ 0 at hz
          by_contra hzK'
          have hzzero := hsZero hzK'
          exact hz (by simp [β, hzzero, Real.smoothTransition.zero])
        have hβtsupport : tsupport β ⊆ K' := by
          rw [tsupport]
          exact (closure_mono hβsupport).trans hK'.isClosed.closure_subset
        have hβcompact : HasCompactSupport β :=
          HasCompactSupport.intro hK' (by
            intro z hz
            by_contra hne
            exact hz (hβsupport (Function.mem_support.mpr hne)))
        let O : Set (EuclideanSpace ℂ (Fin n)) := {z | δ < s z}
        have hOopen : IsOpen O := by
          dsimp [O]
          exact isOpen_lt continuous_const hscont.continuous
        have hOK : K ⊆ O := by
          intro z hz
          dsimp [O]
          calc
            δ < s z₀ := by dsimp [δ]; linarith [hspos hz₀]
            _ ≤ s z := hmin hz
        have hOtarget : O ⊆ c.target := by
          intro z hz
          have hspos' : s z ≠ 0 := ne_of_gt (lt_trans hδ hz)
          have hzK' : z ∈ K' := hsuppS (Function.mem_support.mpr hspos')
          exact hK'target hzK'
        have hβoneO : ∀ z ∈ O, β z = 1 := by
          intro z hz
          dsimp [O] at hz
          dsimp [β]
          exact Real.smoothTransition.one_of_one_le ((one_le_div hδ).2 hz.le)
        exact ⟨β, hβcont, hβcompact, hβtsupport.trans hK'target,
          O, hOopen, hOK, hOtarget, hβoneO⟩
      · have hKempty : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hKne
        refine ⟨0, contDiff_const, ?_, by simp, ∅, isOpen_empty, ?_, empty_subset _, ?_⟩
        · exact HasCompactSupport.intro isCompact_empty (by intro z hz; simpa using hz)
        · simp [hKempty]
        · simp
    obtain ⟨β, hβcont, hβcompact, hβsupport, O, hOopen, hOK, hOtarget, hβoneO⟩ := hplateau
    let F : EuclideanSpace ℂ (Fin n) → ℝ := fun z ↦ f (c.symm z)
    let v : EuclideanSpace ℂ (Fin n) → ℝ :=
      fun z ↦ f i + β z * (F z - f i)
    have hFOn : ContDiffOn ℝ ∞ F c.target := by
      have hfMD : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f Set.univ :=
        contMDiffOn_univ.mpr hf
      exact (hfMD.comp (contMDiffOn_extChartAt_symm i)
        (by intro z hz; simp)).contDiffOn
    have hvOn : ContDiffOn ℝ ∞ v c.target := by
      let g : EuclideanSpace ℂ (Fin n) → ℝ := fun _ ↦ f i
      have hg : ContDiffOn ℝ ∞ g c.target := contDiffOn_const
      change ContDiffOn ℝ ∞ (fun z ↦ g z + β z * (F z - g z)) c.target
      exact hg.add (hβcont.contDiffOn.mul (hFOn.sub hg))
    have hvcont : ContDiff ℝ ∞ v := by
      apply contDiff_iff_contDiffAt.mpr
      intro z
      by_cases hz : z ∈ c.target
      · exact hvOn.contDiffAt ((isOpen_extChartAt_target i).mem_nhds hz)
      · have hβzero : β =ᶠ[nhds z] fun _ ↦ (0 : ℝ) := by
          filter_upwards [(isClosed_tsupport β).isOpen_compl.mem_nhds
            (fun hzβ ↦ hz (hβsupport hzβ))] with w hw
          have hwzero : β w = 0 := by
            by_contra hne
            exact hw (subset_tsupport β (Function.mem_support.mpr hne))
          exact hwzero
        have hveq : v =ᶠ[nhds z] fun _ ↦ f i := by
          filter_upwards [hβzero] with w hw
          simp [v, hw]
        exact (contDiff_const.contDiffAt).congr_of_eventuallyEq hveq
    have hvEqOn : EqOn v F O := by
      intro z hz
      simp [v, F, hβoneO z hz]
    have hfirstEq {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ O) :
        fderiv ℝ v z = fderiv ℝ F z := by
      have heq : v =ᶠ[nhds z] F := by
        filter_upwards [hOopen.mem_nhds hz] with w hw
        exact hvEqOn hw
      exact heq.fderiv_eq (𝕜 := ℝ)
    have hsecondEq {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ O) :
        fderiv ℝ (fderiv ℝ v) z = fderiv ℝ (fderiv ℝ F) z := by
      have heq : (fun w ↦ fderiv ℝ v w) =ᶠ[nhds z] fun w ↦ fderiv ℝ F w := by
        filter_upwards [hOopen.mem_nhds hz] with w hw
        exact hfirstEq hw
      exact heq.fderiv_eq (𝕜 := ℝ)
    have hessianEq {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ K) :
        complexHessian v z = complexHessian F z := by
      have hzO := hOK hz
      have hv₂ : ContDiffAt ℝ 2 v z :=
        hvcont.contDiffAt.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
      have hF₂ : ContDiffAt ℝ 2 F z :=
        (hFOn.contDiffAt ((isOpen_extChartAt_target i).mem_nhds (hOtarget hzO))).of_le
          (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
      ext j k
      rw [complexHessian_apply hv₂ j k, complexHessian_apply hF₂ j k]
      simp [hsecondEq hzO]
    have hchartLapGeneric (g : M → ℝ)
        (hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ g)
        {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ c.target) :
        ω₀.laplacian g (c.symm z) = RCLike.re
          ((ω₀.metricInChart i z)⁻¹ * complexHessian (g ∘ c.symm) z).trace := by
      have hy : c.symm z ∈ (chartAt (EuclideanSpace ℂ (Fin n)) i).source := by
        simpa [c, ← extChartAt_source] using c.map_target hz
      have hLap := ω₀.laplacian_eq_inChart hg i hy
      rw [c.right_inv hz] at hLap
      exact hLap
    have hchartLaplacian {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ c.target) :
        ω₀.laplacian f (c.symm z) = RCLike.re
          ((ω₀.metricInChart i z)⁻¹ * complexHessian (f ∘ c.symm) z).trace :=
      hchartLapGeneric f hf hz
    have hsymm : AEMeasurable c.symm ν := by
      exact (continuousOn_extChartAt_symm i).aemeasurable
        (isOpen_extChartAt_target i).measurableSet
    have hdcont : ContinuousOn d c.target := by
      exact ENNReal.continuous_ofReal.continuousOn.comp
        (hvolumeDensityCont i) (fun _ _ ↦ Set.mem_univ _)
    have hd : AEMeasurable d ν :=
      hdcont.aemeasurable (isOpen_extChartAt_target i).measurableSet
    have hsymm' : AEMeasurable c.symm (ν.withDensity d) :=
      hsymm.mono_ac (withDensity_absolutelyContinuous ν d)
    have hψcont : Continuous ψ :=
      (ρ i).contMDiff.continuous |>.mul hcont
    have hψmeas : AEStronglyMeasurable ψ (ω₀.chartVolume i) :=
      hψcont.aestronglyMeasurable
    have hρmeas : Measurable (fun y ↦ ENNReal.ofReal (ρ i y)) :=
      ENNReal.measurable_ofReal.comp (ρ i).contMDiff.continuous.measurable
    have hρtop : ∀ᵐ y ∂ω₀.chartVolume i, ENNReal.ofReal (ρ i y) < ⊤ :=
      Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top
    have hstart :
        ∫ y, ω₀.laplacian f y ∂μ i = ∫ y, (ρ i y) * ω₀.laplacian f y
          ∂ω₀.chartVolume i := by
      change ∫ y, ω₀.laplacian f y ∂(ω₀.chartVolume i).withDensity
        (fun y ↦ ENNReal.ofReal (ρ i y)) = _
      rw [integral_withDensity_eq_integral_toReal_smul hρmeas hρtop]
      congr 1
      funext y
      simp [ENNReal.toReal_ofReal, ρ.nonneg]
    have hcoord :
        ∫ y, ω₀.laplacian f y ∂μ i =
          ∫ z in c.target, ω₀.volumeDensityInChart i z * ρ i (c.symm z) *
            ω₀.laplacian f (c.symm z)
            ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := by
      calc
        ∫ y, ω₀.laplacian f y ∂μ i = ∫ y, ψ y ∂ω₀.chartVolume i := by
          simpa [ψ] using hstart
        _ = ∫ z, ψ (c.symm z) ∂(ν.withDensity d) := by
          rw [chartVolume]
          exact MeasureTheory.integral_map hsymm' hψmeas
        _ = ∫ z, (d z).toReal * ψ (c.symm z) ∂ν := by
          simpa only [smul_eq_mul] using
            integral_withDensity_eq_integral_toReal_smul₀ hd
              (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)
              (fun z ↦ ψ (c.symm z))
        _ = ∫ z in c.target, (d z).toReal * ψ (c.symm z)
            ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := by
          simp [ν]
        _ = _ := by
          refine MeasureTheory.setIntegral_congr_fun
            (isOpen_extChartAt_target i).measurableSet ?_
          intro z hz
          have hden : (d z).toReal = ω₀.volumeDensityInChart i z := by
            simp [d, ENNReal.toReal_ofReal, le_of_lt (ω₀.volumeDensityInChart_pos i hz)]
          change (d z).toReal * ψ (c.symm z) =
            ω₀.volumeDensityInChart i z * ρ i (c.symm z) *
              ω₀.laplacian f (c.symm z)
          rw [hden, show ψ (c.symm z) = ρ i (c.symm z) * ω₀.laplacian f (c.symm z) by rfl]
          ring
    have hcoordHessian :
        ∫ z in c.target, ω₀.volumeDensityInChart i z * ρ i (c.symm z) *
            ω₀.laplacian f (c.symm z)
            ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) =
          ∫ z in c.target, ω₀.volumeDensityInChart i z * χ z *
            RCLike.re ((ω₀.metricInChart i z)⁻¹ * complexHessian F z).trace
            ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := by
      refine MeasureTheory.setIntegral_congr_fun
        (isOpen_extChartAt_target i).measurableSet ?_
      intro z hz
      change ω₀.volumeDensityInChart i z * ρ i (c.symm z) *
          ω₀.laplacian f (c.symm z) = _
      rw [hchartLaplacian hz]
      change ω₀.volumeDensityInChart i z * ρ i (c.symm z) *
          RCLike.re ((ω₀.metricInChart i z)⁻¹ * complexHessian (f ∘ c.symm) z).trace =
        ω₀.volumeDensityInChart i z * χ z *
          RCLike.re ((ω₀.metricInChart i z)⁻¹ * complexHessian F z).trace
      rw [show χ z = ρ i (c.symm z) by simp [χ, hz]]
      have hF : complexHessian F z = complexHessian (f ∘ c.symm) z := rfl
      rw [hF]
    have hIBP := chart_integral_by_parts (ω₀ := ω₀) i χ
      (fun _ : EuclideanSpace ℂ (Fin n) ↦ 1) v
      hχcont contDiff_const hvcont hχcompact hχtarget
    have hcoordToV :
        ∫ z in c.target, ω₀.volumeDensityInChart i z * χ z *
            RCLike.re ((ω₀.metricInChart i z)⁻¹ * complexHessian F z).trace
            ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) =
          ∫ z in c.target, ω₀.volumeDensityInChart i z * χ z *
            RCLike.re ((ω₀.metricInChart i z)⁻¹ * complexHessian v z).trace
            ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := by
      refine MeasureTheory.setIntegral_congr_fun
        (isOpen_extChartAt_target i).measurableSet ?_
      intro z hz
      by_cases hχz : χ z = 0
      · simp [hχz]
      · have hzK : z ∈ K := hχsupport (Function.mem_support.mpr hχz)
        change ω₀.volumeDensityInChart i z * χ z *
            RCLike.re ((ω₀.metricInChart i z)⁻¹ * complexHessian F z).trace =
          ω₀.volumeDensityInChart i z * χ z *
            RCLike.re ((ω₀.metricInChart i z)⁻¹ * complexHessian v z).trace
        simp only [hessianEq hzK]
    have hconstant :
        (fun z ↦ chartGradientPair (ω₀.metricInChart i) (fun _ ↦ 1) v z) = 0 := by
      funext z
      have hdz : chartPartialZ (fun _ : EuclideanSpace ℂ (Fin n) ↦ (1 : ℝ)) z = 0 := by
        unfold chartPartialZ
        rw [fderiv_const_apply]
        funext j
        simp
      unfold chartGradientPair
      rw [hdz]
      have hvec : Matrix.vecMulVec (0 : Fin n → ℂ) (chartPartialBar v z) = 0 := by
        ext j k
        simp [Matrix.vecMulVec]
      rw [hvec]
      simp
    have hIBP' :
        ∫ z in c.target, ω₀.volumeDensityInChart i z * χ z *
            RCLike.re ((ω₀.metricInChart i z)⁻¹ * complexHessian v z).trace
            ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) =
          -∫ z in c.target, ω₀.volumeDensityInChart i z *
            chartGradientPair (ω₀.metricInChart i) χ v z
            ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := by
      change ∫ z in (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target,
          (2 ^ n * RCLike.re (ω₀.metricInChart i z).det) * χ z *
            RCLike.re ((ω₀.metricInChart i z)⁻¹ * complexHessian v z).trace =
        -∫ z in (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target,
          (2 ^ n * RCLike.re (ω₀.metricInChart i z).det) *
            chartGradientPair (ω₀.metricInChart i) χ v z
            ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n)))
      simpa [hconstant, volumeDensityInChart, mul_assoc] using hIBP
    have hpairEq (z : EuclideanSpace ℂ (Fin n)) :
        chartGradientPair (ω₀.metricInChart i) χ v z =
          chartGradientPair (ω₀.metricInChart i) χ F z := by
      by_cases hzK : z ∈ K
      · have hfd := hfirstEq (hOK hzK)
        unfold chartGradientPair
        have hbar : chartPartialBar v z = chartPartialBar F z := by
          unfold chartPartialBar
          simp [hfd]
        rw [hbar]
      · have hzχ : z ∉ tsupport χ := fun hzχ ↦ hzK (hχtsupport hzχ)
        have heq : χ =ᶠ[nhds z] fun _ ↦ (0 : ℝ) := by
          filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hzχ] with w hw
          have hnot : w ∉ Function.support χ := fun hws ↦ hw (subset_tsupport _ hws)
          exact not_not.mp hnot
        have hfd : fderiv ℝ χ z = 0 := by
          simpa using heq.fderiv_eq (𝕜 := ℝ)
        unfold chartGradientPair
        have hzderiv : chartPartialZ χ z = 0 := by
          unfold chartPartialZ
          rw [hfd]
          funext j
          simp
        rw [hzderiv]
        simp [Matrix.vecMulVec]
    have hpairInt :
        ∫ z in c.target, ω₀.volumeDensityInChart i z *
            chartGradientPair (ω₀.metricInChart i) χ v z
            ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) =
          ∫ z in c.target, ω₀.volumeDensityInChart i z *
            chartGradientPair (ω₀.metricInChart i) χ F z
            ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := by
      refine MeasureTheory.setIntegral_congr_fun
        (isOpen_extChartAt_target i).measurableSet ?_
      intro z hz
      change ω₀.volumeDensityInChart i z *
          chartGradientPair (ω₀.metricInChart i) χ v z =
        ω₀.volumeDensityInChart i z *
          chartGradientPair (ω₀.metricInChart i) χ F z
      simp only [hpairEq z]
    let P : M → ℝ := crossGrad i
    have hpairPolar (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ c.target) :
        chartGradientPair (ω₀.metricInChart i) χ F z = P (c.symm z) := by
      let U : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ ρ i (c.symm w)
      let V : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ f (c.symm w)
      have hχloc : χ =ᶠ[nhds z] U := by
        have hztarget : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target := by
          simpa [c] using hz
        filter_upwards [(isOpen_extChartAt_target i).mem_nhds hztarget]
          with w hw
        have hw' : w ∈ c.target := by simpa [c] using hw
        simp [χ, U, hw']
      have hpartialZ : chartPartialZ χ z = chartPartialZ U z := by
        have hfdχ : fderiv ℝ χ z = fderiv ℝ U z := hχloc.fderiv_eq
        unfold chartPartialZ
        rw [hfdχ]
      have hF : F = V := by
        funext w
        rfl
      have hpair : chartGradientPair (ω₀.metricInChart i) χ F z =
          chartGradientPair (ω₀.metricInChart i) U V z := by
        unfold chartGradientPair
        rw [hpartialZ, hF]
      have hpolar := hgradPolar i (ρ i) f (ρ i).contMDiff hf hz
      dsimp [P, crossGrad, U, V, c] at *
      exact hpair.trans hpolar
    have hsumMD : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
        (fun x ↦ ρ i x + f x) := (ρ i).contMDiff.add hf
    have hPcont : Continuous P := by
      dsimp [P]
      exact (((ω₀.contMDiff_gradNormSq hsumMD).continuous.sub
        (ω₀.contMDiff_gradNormSq (ρ i).contMDiff).continuous).sub
        (ω₀.contMDiff_gradNormSq hf).continuous).div_const 2
    have hPmeas : AEStronglyMeasurable P (ω₀.chartVolume i) :=
      hPcont.aestronglyMeasurable
    have hPmap :
        ∫ y, P y ∂ω₀.chartVolume i = ∫ z, P (c.symm z) ∂(ν.withDensity d) := by
      rw [chartVolume]
      exact MeasureTheory.integral_map hsymm' hPmeas
    have hPdensity :
        ∫ z, P (c.symm z) ∂(ν.withDensity d) =
          ∫ z, (d z).toReal * P (c.symm z) ∂ν := by
      simpa only [smul_eq_mul] using
        integral_withDensity_eq_integral_toReal_smul₀ hd
          (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)
          (fun z ↦ P (c.symm z))
    have hPchart :
        ∫ z in c.target, ω₀.volumeDensityInChart i z * P (c.symm z)
            ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) =
          ∫ y, P y ∂ω₀.volume.restrict (chartAt (EuclideanSpace ℂ (Fin n)) i).source := by
      have hdenInt :
          ∫ z in c.target, (d z).toReal * P (c.symm z)
              ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) =
            ∫ y, P y ∂ω₀.chartVolume i := by
        calc
          _ = ∫ z, (d z).toReal * P (c.symm z) ∂ν := by simp [ν]
          _ = ∫ z, P (c.symm z) ∂(ν.withDensity d) := hPdensity.symm
          _ = _ := hPmap.symm
      have hchartAE : ∀ᵐ y ∂ω₀.chartVolume i,
          y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) i).source := by
        have hsymmExt : AEMeasurable (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm
            (ν.withDensity d) := by
          simpa [c] using hsymm'
        have htargetAE : ∀ᵐ z ∂(ν.withDensity d), z ∈ c.target := by
          have hνtarget : ∀ᵐ z ∂ν, z ∈ c.target := by
            dsimp [ν]
            exact MeasureTheory.ae_restrict_mem
              (isOpen_extChartAt_target i).measurableSet
          rw [MeasureTheory.ae_withDensity_iff' hd]
          filter_upwards [hνtarget] with z hz _
          exact hz
        rw [chartVolume]
        exact (MeasureTheory.ae_map_iff hsymmExt
          (chartAt (EuclideanSpace ℂ (Fin n)) i).open_source.measurableSet).2
          (htargetAE.mono fun z hz ↦ by
            have hz' : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target := by
              simpa [c] using hz
            have hsource := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).map_target hz'
            rw [extChartAt_source] at hsource
            change (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm z ∈
              (chartAt (EuclideanSpace ℂ (Fin n)) i).source
            exact hsource)
      have hchartRestrict :
          (ω₀.chartVolume i).restrict (chartAt (EuclideanSpace ℂ (Fin n)) i).source =
            ω₀.chartVolume i := Measure.restrict_eq_self_of_ae_mem hchartAE
      calc
        _ = ∫ z in c.target, (d z).toReal * P (c.symm z)
              ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := by
          refine MeasureTheory.setIntegral_congr_fun
            (isOpen_extChartAt_target i).measurableSet ?_
          intro z hz
          have hden : (d z).toReal = ω₀.volumeDensityInChart i z := by
            simp [d, ENNReal.toReal_ofReal,
              le_of_lt (ω₀.volumeDensityInChart_pos i hz)]
          simp only [hden]
        _ = ∫ y, P y ∂ω₀.chartVolume i := hdenInt
        _ = ∫ y, P y ∂(ω₀.chartVolume i).restrict
              (chartAt (EuclideanSpace ℂ (Fin n)) i).source := by
          rw [hchartRestrict]
        _ = ∫ y, P y ∂ω₀.volume.restrict
              (chartAt (EuclideanSpace ℂ (Fin n)) i).source :=
          ω₀.integral_chartVolume_restrict_chartSource_eq_integral_volume_restrict i P
    have hpairPolarInt :
        ∫ z in c.target, ω₀.volumeDensityInChart i z *
            chartGradientPair (ω₀.metricInChart i) χ F z
            ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) =
          ∫ z in c.target, ω₀.volumeDensityInChart i z * P (c.symm z)
            ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := by
      refine MeasureTheory.setIntegral_congr_fun
        (isOpen_extChartAt_target i).measurableSet ?_
      intro z hz
      change ω₀.volumeDensityInChart i z *
          chartGradientPair (ω₀.metricInChart i) χ F z =
        ω₀.volumeDensityInChart i z * P (c.symm z)
      rw [hpairPolar z hz]
    calc
      ∫ y, ω₀.laplacian f y ∂μ i = _ := hcoord.trans hcoordHessian
      _ = _ := hcoordToV
      _ = _ := hIBP'
      _ = _ := congrArg Neg.neg hpairInt
      _ = _ := congrArg Neg.neg hpairPolarInt
      _ = _ := by
        simpa [P, crossGrad] using congrArg Neg.neg hPchart
  have hρsmooth (i : M) : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (ρ i) := (ρ i).contMDiff
  have hadd (i : M) : (fun x : M ↦ ρ i x) + f = fun x ↦ ρ i x + f x := rfl
  have hcrossGrad_sum (y : M) : ∑ i ∈ S, crossGrad i y = 0 := by
    simpa [crossGrad, gradNormSq, hadd] using
      ω₀.chartGradientPair_partition_sum_zero S (fun i y ↦ ρ i y) hρsum hρsmooth f hf y
  have hcrossGrad_zero_outside (i y : M)
      (hy : y ∉ (chartAt (EuclideanSpace ℂ (Fin n)) i).source) :
      crossGrad i y = 0 := by
    let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y
    let z := c y
    let U : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ ρ i (c.symm w)
    let V : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ f (c.symm w)
    have hz : z ∈ c.target := mem_extChartAt_target y
    have hleft : c.symm z = y := c.left_inv (mem_extChartAt_source y)
    have hρsource : tsupport (ρ i) ⊆ (chartAt (EuclideanSpace ℂ (Fin n)) i).source := by
      simpa [← extChartAt_source] using hρ i
    have hyNot : y ∉ tsupport (ρ i) := fun hy' ↦ hy (hρsource hy')
    have hopen : (tsupport (ρ i))ᶜ ∈ nhds y :=
      (isClosed_tsupport (ρ i)).isOpen_compl.mem_nhds hyNot
    have hzero {x : M} (hx : x ∉ tsupport (ρ i)) : ρ i x = 0 := by
      by_contra hne
      exact hx (subset_tsupport _ hne)
    have hpre : c.symm ⁻¹' (tsupport (ρ i))ᶜ ∈ nhds z := by
      have hopen' : (tsupport (ρ i))ᶜ ∈ nhds (c.symm z) := by
        simpa [hleft] using hopen
      exact (continuousAt_extChartAt_symm y).preimage_mem_nhds hopen'
    have hUzero : U =ᶠ[nhds z] fun _ ↦ (0 : ℝ) := by
      filter_upwards [hpre] with w hw
      exact hzero hw
    have hfdU : fderiv ℝ U z = 0 := by
      rw [hUzero.fderiv_eq]
      simp
    have hpartialZero : chartPartialZ U z = 0 := by
      funext j
      simp [chartPartialZ, hfdU]
    have hvecZero : Matrix.vecMulVec (0 : Fin n → ℂ) (chartPartialBar V z) = 0 := by
      ext a b
      simp [Matrix.vecMulVec]
    have hpairZero : chartGradientPair (ω₀.metricInChart y) U V z = 0 := by
      unfold chartGradientPair
      rw [hpartialZero, hvecZero]
      simp
    have hp := hgradPolar y (ρ i) f (ρ i).contMDiff hf hz
    rw [hleft] at hp
    have hAdd : (ρ i + f) = (fun x ↦ ρ i x + f x) := rfl
    rw [hAdd] at hp
    have hpolar : crossGrad i y = chartGradientPair (ω₀.metricInChart y) U V z := by
      simpa only [crossGrad, U, V] using hp.symm
    exact hpolar.trans hpairZero
  have hcrossGrad_cont (i : M) : Continuous (crossGrad i) := by
    dsimp [crossGrad]
    exact (((ω₀.contMDiff_gradNormSq ((ρ i).contMDiff.add hf)).continuous.sub
      (ω₀.contMDiff_gradNormSq (ρ i).contMDiff).continuous).sub
      (ω₀.contMDiff_gradNormSq hf).continuous).div_const 2
  have hcrossGrad_int (i : M) : Integrable (crossGrad i) ω₀.volume :=
    (hcrossGrad_cont i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcrossGrad_restrict (i : M) :
      ∫ y, crossGrad i y ∂ω₀.volume.restrict
          (chartAt (EuclideanSpace ℂ (Fin n)) i).source =
        ∫ y, crossGrad i y ∂ω₀.volume := by
    calc
      _ = ∫ y in (chartAt (EuclideanSpace ℂ (Fin n)) i).source,
            crossGrad i y ∂ω₀.volume := rfl
      _ = _ := MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun y hy ↦ hcrossGrad_zero_outside i y hy)
  rw [← hsum', hsum_fin]
  calc
    ∑ i ∈ S, ∫ y, ω₀.laplacian f y ∂μ i =
        ∑ i ∈ S, -∫ y, crossGrad i y ∂ω₀.volume.restrict
          (chartAt (EuclideanSpace ℂ (Fin n)) i).source := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hchartTerm i
    _ = -∑ i ∈ S, ∫ y, crossGrad i y ∂ω₀.volume.restrict
          (chartAt (EuclideanSpace ℂ (Fin n)) i).source := by
      rw [Finset.sum_neg_distrib]
    _ = -∑ i ∈ S, ∫ y, crossGrad i y ∂ω₀.volume := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact hcrossGrad_restrict i
    _ = -∫ y, ∑ i ∈ S, crossGrad i y ∂ω₀.volume := by
      rw [← MeasureTheory.integral_finsetSum S (fun i hi ↦ hcrossGrad_int i)]
    _ = 0 := by
      have hsumzero : (fun y : M ↦ ∑ i ∈ S, crossGrad i y) = 0 := by
        funext y
        exact hcrossGrad_sum y
      rw [hsumzero]
      simp

theorem integral_mul_laplacian_comm (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ g) :
    ∫ x, f x * ω₀.laplacian g x ∂ω₀.volume = ∫ x, g x * ω₀.laplacian f x ∂ω₀.volume := by
  classical
  let ρ : SmoothPartitionOfUnity M 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M univ :=
    (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M).choose
  have hρ : ρ.IsSubordinate fun i ↦ (chartAt (EuclideanSpace ℂ (Fin n)) i).source :=
    (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M).choose_spec
  let S : Finset M :=
    (ρ.locallyFinite.closure.finite_nonempty_inter_compact isCompact_univ).toFinset
  let μ : M → Measure M := fun i ↦
    (ω₀.chartVolume i).withDensity fun y ↦ ENNReal.ofReal (ρ i y)
  have hμzero (i : M) (hi : i ∉ S) : μ i = 0 := by
    have hρzero : ∀ y, ρ i y = 0 := by
      intro y
      by_contra hne
      have hy : y ∈ tsupport (ρ i) := subset_tsupport _ hne
      have hiS : i ∈ (ρ.locallyFinite.closure.finite_nonempty_inter_compact
          isCompact_univ).toFinset := by
        simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
        exact ⟨y, hy, mem_univ y⟩
      exact hi (by simpa only [S] using hiS)
    have hfun : (fun y ↦ ENNReal.ofReal (ρ i y)) = 0 := by
      funext y
      simp [hρzero y]
    simp [μ, hfun]
  have hvol : ω₀.volume = Measure.sum μ := by
    simpa only [μ] using ω₀.volume_eq_sum_of_isSubordinate ρ hρ
  have hleftcont : Continuous (fun x ↦ f x * ω₀.laplacian g x) :=
    hf.continuous.mul (ω₀.contMDiff_laplacian hg).continuous
  have hrightcont : Continuous (fun x ↦ g x * ω₀.laplacian f x) :=
    hg.continuous.mul (ω₀.contMDiff_laplacian hf).continuous
  have hleftcompact : HasCompactSupport (fun x ↦ f x * ω₀.laplacian g x) :=
    HasCompactSupport.of_compactSpace _
  have hrightcompact : HasCompactSupport (fun x ↦ g x * ω₀.laplacian f x) :=
    HasCompactSupport.of_compactSpace _
  have hleftint : Integrable (fun x ↦ f x * ω₀.laplacian g x) ω₀.volume :=
    hleftcont.integrable_of_hasCompactSupport hleftcompact
  have hrightint : Integrable (fun x ↦ g x * ω₀.laplacian f x) ω₀.volume :=
    hrightcont.integrable_of_hasCompactSupport hrightcompact
  have hleftsum := MeasureTheory.hasSum_integral_measure (μ := μ) hleftint
  have hrightsum := MeasureTheory.hasSum_integral_measure (μ := μ) hrightint
  have hleftsum' :
      ∑' i : M, ∫ y, f y * ω₀.laplacian g y ∂μ i =
        ∫ x, f x * ω₀.laplacian g x ∂ω₀.volume := by
    rw [hvol]
    exact hleftsum.tsum_eq
  have hrightsum' :
      ∑' i : M, ∫ y, g y * ω₀.laplacian f y ∂μ i =
        ∫ x, g x * ω₀.laplacian f x ∂ω₀.volume := by
    rw [hvol]
    exact hrightsum.tsum_eq
  have hleftsum_fin :
      ∑' i : M, ∫ y, f y * ω₀.laplacian g y ∂μ i =
        ∑ i ∈ S, ∫ y, f y * ω₀.laplacian g y ∂μ i := by
    rw [tsum_eq_sum (s := S) (fun i hi ↦ by simp [hμzero i hi])]
  have hrightsum_fin :
      ∑' i : M, ∫ y, g y * ω₀.laplacian f y ∂μ i =
        ∑ i ∈ S, ∫ y, g y * ω₀.laplacian f y ∂μ i := by
    rw [tsum_eq_sum (s := S) (fun i hi ↦ by simp [hμzero i hi])]
  rw [← hleftsum', ← hrightsum', hleftsum_fin, hrightsum_fin]
  have hchartTerm (i : M) (F : M → ℝ) (hF : Continuous F) :
      ∫ y, F y ∂μ i =
        ∫ z in (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target,
          ω₀.volumeDensityInChart i z *
            ρ i ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm z) *
            F ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm z)
            ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := by
    change ∫ y, F y ∂(ω₀.chartVolume i).withDensity
      (fun y ↦ ENNReal.ofReal (ρ i y)) = _
    exact integral_chartVolume_withDensity ω₀ i (ρ i) (ρ i).contMDiff
      (fun y ↦ ρ.nonneg i y) F hF
  have hρfinsupport (x : M) : ρ.finsupport x ⊆ S := by
    intro i hi
    by_contra hiS
    have hz : ρ i x = 0 := by
      have hρzero : ∀ y, ρ i y = 0 := by
        intro y
        by_contra hne
        have hy : y ∈ tsupport (ρ i) := subset_tsupport _ hne
        have hiS' : i ∈ S := by
          simp only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
          exact ⟨y, hy, mem_univ y⟩
        exact hiS (by simpa only [S] using hiS')
      exact hρzero x
    have hnot : i ∉ ρ.finsupport x := by
      simp only [SmoothPartitionOfUnity.mem_finsupport]
      simp [hz]
    exact hnot hi
  have hρsum (x : M) : ∑ i ∈ S, ρ i x = 1 :=
    ρ.sum_finsupport' (x₀ := x) (mem_univ x) (hρfinsupport x)
  have hρsmooth (i : M) :
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (ρ i) := (ρ i).contMDiff
  let cross (i : M) (u : M → ℝ) (y : M) : ℝ :=
    (ω₀.gradNormSq (fun x ↦ ρ i x + u x) y -
      ω₀.gradNormSq (ρ i) y - ω₀.gradNormSq u y) / 2
  have hcross_sum (u : M → ℝ)
      (hu : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u) (y : M) :
      ∑ i ∈ S, cross i u y = 0 := by
    have hadd (i : M) : (fun x : M ↦ ρ i x) + u = fun x ↦ ρ i x + u x := rfl
    simpa [cross, gradNormSq, hadd] using
      ω₀.chartGradientPair_partition_sum_zero S (fun i y ↦ ρ i y)
        hρsum hρsmooth u hu y
  have hcross_cont (i : M) (u : M → ℝ)
      (hu : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u) :
      Continuous (cross i u) := by
    dsimp [cross]
    exact (((ω₀.contMDiff_gradNormSq ((ρ i).contMDiff.add hu)).continuous.sub
      (ω₀.contMDiff_gradNormSq (ρ i).contMDiff).continuous).sub
      (ω₀.contMDiff_gradNormSq hu).continuous).div_const 2
  have hresidual_int (i : M) :
      Integrable (fun y ↦ g y * cross i f y - f y * cross i g y) ω₀.volume := by
    exact ((hg.continuous.mul (hcross_cont i f hf)).sub
      (hf.continuous.mul (hcross_cont i g hg))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hresidual_sum :
      ∑ i ∈ S, ∫ y, g y * cross i f y - f y * cross i g y ∂ω₀.volume = 0 := by
    rw [← MeasureTheory.integral_finsetSum S (fun i hi ↦ hresidual_int i)]
    have hzero : (fun y : M ↦ ∑ i ∈ S,
        (g y * cross i f y - f y * cross i g y)) = 0 := by
      funext y
      calc
        ∑ i ∈ S, (g y * cross i f y - f y * cross i g y) =
            g y * (∑ i ∈ S, cross i f y) - f y * (∑ i ∈ S, cross i g y) := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        _ = 0 := by rw [hcross_sum f hf y, hcross_sum g hg y]; ring
    rw [hzero]
    simp
  have hweightedLap (i : M) (χ U V : EuclideanSpace ℂ (Fin n) → ℝ)
      (u v : M → ℝ) (O : Set (EuclideanSpace ℂ (Fin n)))
      (hχeq : ∀ z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target,
        χ z = ρ i ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm z))
      (hO : IsOpen O)
      (hKO : (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i) '' tsupport (ρ i) ⊆ O)
      (hu : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u)
      (hv : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ v)
      (hUeq : EqOn U (fun z ↦ u ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm z)) O)
      (hVeq : EqOn V (fun z ↦ v ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm z)) O)
      (hV : ContDiff ℝ ∞ V) :
      ∫ y, u y * ω₀.laplacian v y ∂μ i =
        ∫ z in (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target,
          ω₀.volumeDensityInChart i z * χ z * U z *
            RCLike.re ((ω₀.metricInChart i z)⁻¹ * complexHessian V z).trace
            ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := by
    let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i
    have hFOn : ContDiffOn ℝ ∞ (fun z ↦ v (c.symm z)) c.target := by
      exact ((contMDiffOn_univ.mpr hv).comp (contMDiffOn_extChartAt_symm i)
        (by intro z hz; simp)).contDiffOn
    refine (hchartTerm i (fun y ↦ u y * ω₀.laplacian v y)
      ((hu.continuous).mul (ω₀.contMDiff_laplacian hv).continuous)).trans ?_
    refine MeasureTheory.setIntegral_congr_fun
      (isOpen_extChartAt_target i).measurableSet ?_
    intro z hz
    change ω₀.volumeDensityInChart i z * ρ i (c.symm z) *
        (u (c.symm z) * ω₀.laplacian v (c.symm z)) =
      ω₀.volumeDensityInChart i z * χ z * U z *
        RCLike.re ((ω₀.metricInChart i z)⁻¹ * complexHessian V z).trace
    have hy : c.symm z ∈ (chartAt (EuclideanSpace ℂ (Fin n)) i).source := by
      simpa [c, ← extChartAt_source] using c.map_target hz
    have hρ : χ z = ρ i (c.symm z) := by simpa [c] using hχeq z hz
    by_cases hρzero : ρ i (c.symm z) = 0
    · simp [hρ, hρzero]
    · have hzK : z ∈ c '' tsupport (ρ i) :=
        ⟨c.symm z, subset_tsupport _ hρzero, c.right_inv hz⟩
      have hzO : z ∈ O := hKO hzK
      have hUz : U z = u (c.symm z) := hUeq hzO
      have hV₂ : ContDiffAt ℝ 2 V z := by
        have hle : (2 : ℕ∞ω) ≤ ∞ := by
          change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
          exact WithTop.coe_le_coe.mpr le_top
        exact hV.contDiffAt.of_le
          hle
      have hF₂ : ContDiffAt ℝ 2 (fun w ↦ v (c.symm w)) z := by
        have hle : (2 : ℕ∞ω) ≤ ∞ := by
          change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
          exact WithTop.coe_le_coe.mpr le_top
        exact (hFOn.contDiffAt ((isOpen_extChartAt_target i).mem_nhds hz)).of_le
          hle
      have hsecond : fderiv ℝ (fderiv ℝ V) z =
          fderiv ℝ (fderiv ℝ (fun w ↦ v (c.symm w))) z := by
        have hfirst (w : EuclideanSpace ℂ (Fin n)) (hw : w ∈ O) :
            fderiv ℝ V w = fderiv ℝ (fun t ↦ v (c.symm t)) w := by
          have heq : V =ᶠ[nhds w] fun t ↦ v (c.symm t) := by
            filter_upwards [hO.mem_nhds hw] with t ht
            exact hVeq ht
          exact heq.fderiv_eq
        have heq : (fun w ↦ fderiv ℝ V w) =ᶠ[nhds z]
            fun w ↦ fderiv ℝ (fun t ↦ v (c.symm t)) w := by
          filter_upwards [hO.mem_nhds hzO] with w hw
          exact hfirst w hw
        exact heq.fderiv_eq
      have hHess : complexHessian V z =
          complexHessian (fun w ↦ v (c.symm w)) z := by
        ext j k
        rw [complexHessian_apply hV₂ j k, complexHessian_apply hF₂ j k]
        simp [hsecond]
      have hHessComp : complexHessian V z =
          complexHessian (v ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm) z := by
        simpa [Function.comp_def, c] using hHess
      have hLap := ω₀.laplacian_eq_inChart hv i hy
      rw [show extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i (c.symm z) = z by
        exact c.right_inv hz] at hLap
      rw [hLap, hHessComp, hUz, hρ]
      ring_nf
  have hchart_comm (i : M) :
      (∫ y, f y * ω₀.laplacian g y ∂μ i -
        ∫ y, g y * ω₀.laplacian f y ∂μ i) =
        ∫ y, g y * cross i f y - f y * cross i g y ∂ω₀.volume := by
    have hF : Continuous (fun y ↦ f y * cross i g y) := hf.continuous.mul (hcross_cont i g hg)
    have hG : Continuous (fun y ↦ g y * cross i f y) := hg.continuous.mul (hcross_cont i f hf)
    obtain ⟨χ, _, O, U, V, hχcont, hχcompact, hχtarget, hχsupport, hχeq,
      _, _, _, hOopen, hKO, _, _, hUcont, hUeq, hVcont, hVeq, hresF, hresG⟩ :=
      exists_chart_cutoff_extensions_with_residual ω₀ i (ρ i) f g
        (ρ i).contMDiff (hρ i) hf hg hF hG
    have hleft := hweightedLap i χ U V f g O hχeq hOopen hKO hf hg hUeq hVeq hVcont
    have hright := hweightedLap i χ V U g f O hχeq hOopen hKO hg hf hVeq hUeq hUcont
    have hgreen := ω₀.chart_integral_by_parts_comm i χ U V hχcont hUcont hVcont
      hχcompact hχtarget
    have hresid :
        (∫ z in (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target,
          ω₀.volumeDensityInChart i z * V z *
            chartGradientPair (ω₀.metricInChart i) χ U z
            ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) -
         ∫ z in (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target,
          ω₀.volumeDensityInChart i z * U z *
            chartGradientPair (ω₀.metricInChart i) χ V z
            ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n)))) =
          ∫ y, g y * cross i f y - f y * cross i g y ∂ω₀.volume := by
      have hgfintegrable : Integrable (fun y ↦ g y * cross i f y) ω₀.volume := by
        exact (hg.continuous.mul (hcross_cont i f hf)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      have hfgintegrable : Integrable (fun y ↦ f y * cross i g y) ω₀.volume := by
        exact (hf.continuous.mul (hcross_cont i g hg)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      rw [hresG, hresF]
      change ∫ y, g y * cross i f y ∂ω₀.volume -
          ∫ y, f y * cross i g y ∂ω₀.volume =
        ∫ y, g y * cross i f y - f y * cross i g y ∂ω₀.volume
      rw [← MeasureTheory.integral_sub hgfintegrable hfgintegrable]
    calc
      _ = (∫ z in (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target,
          ω₀.volumeDensityInChart i z * χ z * U z *
            RCLike.re ((ω₀.metricInChart i z)⁻¹ * complexHessian V z).trace
            ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) -
         ∫ z in (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target,
          ω₀.volumeDensityInChart i z * χ z * V z *
            RCLike.re ((ω₀.metricInChart i z)⁻¹ * complexHessian U z).trace
            ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n)))) := by
        rw [hleft, hright]
      _ = _ := by simpa [volumeDensityInChart] using hgreen
      _ = _ := hresid
  have hsum_comm :
      ∑ i ∈ S, (∫ y, f y * ω₀.laplacian g y ∂μ i -
        ∫ y, g y * ω₀.laplacian f y ∂μ i) = 0 := by
    calc
      _ = ∑ i ∈ S, ∫ y, g y * cross i f y - f y * cross i g y ∂ω₀.volume := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hchart_comm i
      _ = 0 := hresidual_sum
  rw [Finset.sum_sub_distrib] at hsum_comm
  linarith

/-- **Green's formula**, energy form: `∫ f Δf = -∫ |∂f|²`. -/
theorem integral_mul_laplacian_self
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f) :
    ∫ x, f x * ω₀.laplacian f x ∂ω₀.volume = -∫ x, ω₀.gradNormSq f x ∂ω₀.volume := by
  let q : M → ℝ := f * f
  have hq : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ q := by
    simpa [q] using hf.mul hf
  let halfq : M → ℝ := fun x ↦ q x / 2
  have hhalfq : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ halfq := by
    simpa [halfq] using hq.div_const (2 : ℝ)
  have hpoint (x : M) : ω₀.laplacian halfq x =
      f x * ω₀.laplacian f x + ω₀.gradNormSq f x := by
    have hchain := laplacian_comp (ω₀ := ω₀) hf
      (h := fun t : ℝ ↦ t ^ 2) (contDiff_id.pow 2) x
    have hhalf : halfq = (1 / 2 : ℝ) • q := by
      funext y
      change q y / 2 = (1 / 2) * q y
      ring
    rw [hhalf, laplacian_smul hq (1 / 2 : ℝ)]
    have hderiv₁ : deriv (fun t : ℝ ↦ t ^ 2) = fun t ↦ 2 * t := by
      funext t
      simp
    have hderiv₂ : deriv (deriv (fun t : ℝ ↦ t ^ 2)) = fun _ ↦ 2 := by
      rw [hderiv₁]
      funext t
      simp
    have hchain' : ω₀.laplacian q x =
        2 * f x * ω₀.laplacian f x + 2 * ω₀.gradNormSq f x := by
      change ω₀.laplacian (fun t : M ↦ f t ^ 2) x = _ at hchain
      have hqeq : q = (fun t : M ↦ f t ^ 2) := by
        funext t
        simp [q, pow_two]
      rw [← hqeq, hderiv₂, hderiv₁] at hchain
      simpa [mul_assoc] using hchain
    change (1 / 2 : ℝ) * ω₀.laplacian q x = _
    rw [hchain']
    ring
  have hpointFun : (fun x : M ↦ ω₀.laplacian halfq x) =
      fun x ↦ f x * ω₀.laplacian f x + ω₀.gradNormSq f x := by
    funext x
    exact hpoint x
  have hfirstCont : Continuous (fun x : M ↦ f x * ω₀.laplacian f x) :=
    hf.continuous.mul (ω₀.contMDiff_laplacian hf).continuous
  have hsecondCont : Continuous (ω₀.gradNormSq f) :=
    (ω₀.contMDiff_gradNormSq hf).continuous
  have hfirstInt : Integrable (fun x : M ↦ f x * ω₀.laplacian f x) ω₀.volume :=
    hfirstCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsecondInt : Integrable (ω₀.gradNormSq f) ω₀.volume :=
    hsecondCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsumInt := integral_add hfirstInt hsecondInt
  have hzero := ω₀.integral_laplacian hhalfq
  rw [hpointFun, hsumInt] at hzero
  linarith

/-- Harmonic functions on a compact connected Kähler manifold are constant. -/
theorem eq_const_of_laplacian_eq_zero [ConnectedSpace M]
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f) (h : ω₀.laplacian f = 0) :
    ∃ c : ℝ, ∀ x, f x = c := by
  have henergy := ω₀.integral_mul_laplacian_self hf
  have hleft : ∫ x, f x * ω₀.laplacian f x ∂ω₀.volume = 0 := by
    have hfun : (fun x ↦ f x * ω₀.laplacian f x) = fun _ ↦ (0 : ℝ) := by
      funext x
      rw [show ω₀.laplacian f x = 0 from congrFun h x, mul_zero]
    rw [hfun]
    simp
  have hgradInt : ∫ x, ω₀.gradNormSq f x ∂ω₀.volume = 0 := by
    rw [hleft] at henergy
    linarith
  have hgradCont : Continuous (ω₀.gradNormSq f) := (ω₀.contMDiff_gradNormSq hf).continuous
  have hnonneg : 0 ≤ᵐ[ω₀.volume] ω₀.gradNormSq f :=
    Filter.Eventually.of_forall (ω₀.gradNormSq_nonneg f)
  have hgradIntable : Integrable (ω₀.gradNormSq f) ω₀.volume :=
    hgradCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hae : (ω₀.gradNormSq f) =ᵐ[ω₀.volume] fun _ ↦ (0 : ℝ) :=
    (integral_eq_zero_iff_of_nonneg_ae hnonneg hgradIntable).mp hgradInt
  have heq := MeasureTheory.Measure.eqOn_open_of_ae_eq (μ := ω₀.volume)
    (U := Set.univ) (f := ω₀.gradNormSq f) (g := fun _ : M ↦ (0 : ℝ))
    (by rw [MeasureTheory.Measure.restrict_univ]; exact hae) isOpen_univ
    hgradCont.continuousOn continuous_zero.continuousOn
  have hcritical : ∀ x, ω₀.gradNormSq f x = 0 := by
    intro x
    exact heq (Set.mem_univ x)
  have hmfzero : ∀ x, mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) f x = 0 := by
    intro x
    exact (ω₀.gradNormSq_eq_zero_iff hf x).mp (hcritical x)
  have hloc := CalabiYau.isLocallyConstant_of_mfderiv_eq_zero
    (hf.mdifferentiable (by simp)) hmfzero
  obtain ⟨c, hc⟩ := hloc.exists_eq_const
  exact ⟨c, fun x ↦ congrFun hc x⟩

end KahlerForm
