module

public import CalabiYau.Geometry.Kahler.Riemannian.Volume
public import CalabiYau.Mathlib.Analysis.Matrix.PosDef.LogDet
import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.TraceWedge
import CalabiYau.Geometry.Complex.Forms.DifferentialForm
import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.SignedTopFormIntegral
import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.TopFormIntegral.ChartDensity
import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.MeanZero.PrimitiveStokes
import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.Stokes

/-!
# Mean-zero trace of an exact real `(1,1)`-form

For a smooth exact real `(1,1)`-form `α = dβ` and a Kähler form `ω`, the trace-wedge identity
`(tr_ω α) ωⁿ = n α ∧ ωⁿ⁻¹` and the Stokes theorem applied to `β ∧ ωⁿ⁻¹` show that the trace has
zero mean with respect to the measure `ω.volume = ωⁿ/n!`. Smoothness of the trace is recorded
alongside the mean-zero calculation, since both are inputs to the scalar Poisson theorem.

In dimension zero every real two-form is zero; dimension one gives `α = (tr_ω α) ω`.
No connectedness is used. The complex orientation and `ω.volume` normalization are fixed by
`KahlerForm.volume`; the required trace-wedge and Stokes theorems are assumed in the
future proof, not axioms or hypotheses of this statement.

Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics*, Lemma 1.14;
Wells, *Differential Analysis on Complex Manifolds*, IV §5 (exterior Leibniz and Stokes).
-/

@[expose] public section

open scoped Manifold ContDiff Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open MeasureTheory
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*}

section

variable [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M] [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

private theorem relTrace_chartRep_eq (α β : FormField (EuclideanSpace ℂ (Fin n)) M 2)
    (x y : M) (hy : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source)
    (hα : (α y).IsOneOne) (hβ : (β y).IsOneOne) :
    relTrace (α y) (β y) =
      relTrace (α.chartRep x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y))
        (β.chartRep x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)) := by
  have hyR : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source := by
    rw [extChartAt_source]
    exact hy
  have hyyR : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).source :=
    mem_extChartAt_source y
  have hyxC : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source := by
    simpa only [← extChartAt_real_eq] using hyR
  have hyyC : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source := by
    simpa only [← extChartAt_real_eq] using hyyR
  let A := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y
  let B := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y x y
  have hBA : ∀ v, B (A v) = v := by
    intro v
    exact (tangentCoordChange_comp (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
      (w := x) (x := y) (y := x) (z := y) (v := v)
      ⟨⟨hyxC, hyyC⟩, hyxC⟩).trans
      (tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
        (x := x) (z := y) (v := v) hyxC)
  have hAB : ∀ v, A (B v) = v := by
    intro v
    exact (tangentCoordChange_comp (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
      (w := y) (x := x) (y := y) (z := y) (v := v)
      ⟨⟨hyyC, hyxC⟩, hyyC⟩).trans
      (tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) )
        (x := y) (z := y) (v := v) hyyC)
  let AEquiv : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n) := {
    toLinearEquiv := {
      toFun := A
      invFun := B
      left_inv := hBA
      right_inv := hAB
      map_add' := A.map_add
      map_smul' := A.map_smul }
    continuous_toFun := A.continuous
    continuous_invFun := B.continuous }
  let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  have hyz : c y ∈ c.target := c.map_source hyR
  have hrepα := FormField.chartRep_eq_chartRep_comp (α := α) hyz
    (by rw [c.left_inv hyR]; exact hyyR)
  have hrepβ := FormField.chartRep_eq_chartRep_comp (α := β) hyz
    (by rw [c.left_inv hyR]; exact hyyR)
  have hderiv : fderiv ℝ
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y ∘ c.symm) (c y) =
        A.restrictScalars ℝ := by
    have h := tangentCoordChange_real_eq ⟨hyR, hyyR⟩
    rw [tangentCoordChange_def, extChartAt_real_eq] at h
    dsimp [c, A]
    simpa [ModelWithCorners.range_eq_univ, fderivWithin_univ] using h
  have hcenter : extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y
      (c.symm (c y)) = extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y := by
    rw [c.left_inv hyR]
  rw [hcenter, FormField.chartRep_self] at hrepα hrepβ
  rw [hderiv] at hrepα hrepβ
  have hAEquiv : (AEquiv : EuclideanSpace ℂ (Fin n) →L[ℂ]
      EuclideanSpace ℂ (Fin n)) = A := by
    ext v
    rfl
  have htrace := relTrace_compContinuousLinearMap hα hβ AEquiv
  rw [hrepα, hrepβ]
  simpa only [hAEquiv] using htrace.symm

end

section

variable [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M] [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

private noncomputable def alternatingEvalCLM
    (v : Fin 2 → EuclideanSpace ℂ (Fin n)) :
    (EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) →L[ℝ] ℝ := by
  let f : (EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun α ↦ α v
      map_add' := by intro α β; simp
      map_smul' := by intro c α; simp }
  exact f.mkContinuous (∏ i, ‖v i‖) (by
    intro α
    calc
      ‖f α‖ = ‖α v‖ := rfl
      _ ≤ ‖α‖ * ∏ i, ‖v i‖ := ContinuousAlternatingMap.le_opNorm α v
      _ = (∏ i, ‖v i‖) * ‖α‖ := by ring)

private noncomputable def coeffEntryCLM (j k : Fin n) :
    (EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) →L[ℝ] ℂ :=
  (1 / 2 : ℝ) •
    (Complex.ofRealCLM.comp (alternatingEvalCLM ![
      EuclideanSpace.single j 1, Complex.I • EuclideanSpace.single k 1]) -
      Complex.I • Complex.ofRealCLM.comp (alternatingEvalCLM ![
        EuclideanSpace.single j 1, EuclideanSpace.single k 1]))

private theorem coeffMatrix_entry_eq
    (α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) (j k : Fin n) :
    α.coeffMatrix j k = coeffEntryCLM j k α := by
  simp [coeffEntryCLM, alternatingEvalCLM, ContinuousAlternatingMap.coeffMatrix]
  ring

end

section

variable [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M] [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

private theorem chartRep_coeff_entry_contDiffOn
    (α : FormField (EuclideanSpace ℂ (Fin n)) M 2) (hα : α.IsSmooth)
    (x : M) (j k : Fin n) :
    ContDiffOn ℝ ∞
      (fun z => (α.chartRep x z).coeffMatrix j k)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
  have hcomp : ContDiffOn ℝ ∞
      (fun z => coeffEntryCLM j k (α.chartRep x z))
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target :=
    (coeffEntryCLM j k).contDiff.comp_contDiffOn (hα x)
  refine hcomp.congr ?_
  intro z hz
  exact coeffMatrix_entry_eq (α.chartRep x z) j k

end

section

variable [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M] [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

private theorem matrix_inv_entry_contDiffAt
    (G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hG : ContDiffAt ℝ ∞ G z) (hunit : IsUnit (G z).det)
    (i j : Fin n) :
    ContDiffAt ℝ ∞ (fun w => (G w)⁻¹ i j) z := by
  have hinv : ContDiffAt ℝ ∞ (fun w => (G w)⁻¹) z :=
    (Matrix.contDiffAt_inv hunit).comp z hG
  exact contDiffAt_pi.mp (contDiffAt_pi.mp hinv i) j

end

section

variable [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M] [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

private theorem trace_chartRep_contDiffOn
    (ω₀ : KahlerForm n M) (α : FormField (EuclideanSpace ℂ (Fin n)) M 2)
    (hα : α.IsSmooth) (x : M) :
    ContDiffOn ℝ ∞
      (fun z => relTrace (ω₀.toFormField.chartRep x z) (α.chartRep x z))
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
  let G := fun z => ω₀.metricInChart x z
  let H := fun z => (α.chartRep x z).coeffMatrix
  have hG : ContDiffOn ℝ ∞ G
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
    apply contDiffOn_pi.mpr
    intro i
    apply contDiffOn_pi.mpr
    intro j
    exact ω₀.contDiffOn_metricInChart x i j
  have hHentry (i j : Fin n) : ContDiffOn ℝ ∞ (fun z => H z i j)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
    simpa only [H] using chartRep_coeff_entry_contDiffOn α hα x i j
  have hInvEntry (i j : Fin n) : ContDiffOn ℝ ∞ (fun z => (G z)⁻¹ i j)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
    intro z hz
    have hGat := hG.contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz)
    have hu : IsUnit (G z).det :=
      (ne_of_gt (ω₀.posDef_metricInChart x hz).det_pos).isUnit
    exact (matrix_inv_entry_contDiffAt G z hGat hu i j).contDiffWithinAt
  have htraceEntry (i j : Fin n) : ContDiffOn ℝ ∞
      (fun z => Complex.reCLM ((G z)⁻¹ i j * H z j i))
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
    exact Complex.reCLM.contDiff.comp_contDiffOn ((hInvEntry i j).mul (hHentry j i))
  have htraceInner (i : Fin n) : ContDiffOn ℝ ∞ (fun z =>
      ∑ j, Complex.reCLM ((G z)⁻¹ i j * H z j i))
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
    apply ContDiffOn.sum
    intro j hj
    exact htraceEntry i j
  have htrace : ContDiffOn ℝ ∞ (fun z =>
      ∑ i, ∑ j, Complex.reCLM ((G z)⁻¹ i j * H z j i))
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
    apply ContDiffOn.sum
    intro i hi
    exact htraceInner i
  refine htrace.congr ?_
  intro z hz
  simp [G, H, KahlerForm.metricInChart, ContinuousAlternatingMap.relTrace,
    Matrix.mul_apply, Matrix.trace, Complex.reCLM_apply]

private theorem relTrace_contMDiff
    (ω₀ : KahlerForm n M) (α : FormField (EuclideanSpace ℂ (Fin n)) M 2)
    (hαsmooth : α.IsSmooth) (hαone : ∀ y, (α y).IsOneOne) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (fun y => relTrace (ω₀ y) (α y)) := by
  let I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
  let f : M → ℝ := fun y => relTrace (ω₀ y) (α y)
  have hchart (x : M) : ContDiffOn ℝ ∞
      (fun z => f ((extChartAt I x).symm z)) (extChartAt I x).target := by
    refine (trace_chartRep_contDiffOn ω₀ α hαsmooth x).congr ?_
    intro z hz
    let e := extChartAt I x
    have hy := e.map_target hz
    have hy' : e.symm z ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source := by
      rw [← extChartAt_source (I := I)]
      exact hy
    have h := relTrace_chartRep_eq ω₀.toFormField α x (e.symm z) hy'
      (ω₀.isOneOne (e.symm z)) (hαone (e.symm z))
    rw [e.right_inv hz] at h
    change relTrace (ω₀.toFormField (e.symm z)) (α (e.symm z)) = _
    exact h
  rw [contMDiff_iff]
  refine ⟨?_, ?_⟩
  · apply continuous_iff_continuousAt.2
    intro x
    let e := extChartAt I x
    let g := fun z => f (e.symm z)
    have hg : ContDiffAt ℝ ∞ g (e x) :=
      (hchart x).contDiffAt
        ((isOpen_extChartAt_target (I := I) x).mem_nhds (mem_extChartAt_target (I := I) x))
    have hgcomp : ContinuousAt (fun p => g (e p)) x :=
      hg.continuousAt.comp
        (contMDiffAt_extChartAt (I := I) (n := ∞) (x := x)).continuousAt
    have hEq : (fun p => g (e p)) =ᶠ[nhds x] f := by
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
    change ContDiffOn ℝ ∞ (fun z => f ((chartAt (EuclideanSpace ℂ (Fin n)) x).symm z))
      (chartAt (EuclideanSpace ℂ (Fin n)) x).target
    simpa [ModelWithCorners.range_eq_univ] using hx

private theorem exact_form_trace_isSmooth (ω₀ : KahlerForm n M)
    {α : FormField (EuclideanSpace ℂ (Fin n)) M 2}
    (hαsmooth : α.IsSmooth) (hαone : α.IsOneOne) (_hαexact : α.IsExact) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (fun x => ContinuousAlternatingMap.relTrace (ω₀ x) (α x)) :=
  relTrace_contMDiff ω₀ α hαsmooth hαone

end

private theorem cast_cast {a b c : ℕ} (h : a = b) (h' : b = c)
    (α : FormField (EuclideanSpace ℂ (Fin n)) M a) :
    cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M) h')
      (cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M) h) α) =
      cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M) (h.trans h')) α := by
  cases h
  cases h'
  rfl

private theorem cast_apply_domDomCongr {k l : ℕ} (h : k = l)
    (α : FormField (EuclideanSpace ℂ (Fin n)) M k) (x : M) :
    cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M) h) α x =
      (α x).domDomCongr (Fin.castOrderIso h) := by
  cases h
  rfl

section

variable [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M] [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

private theorem smooth_cast {k l : ℕ} (h : k = l)
    {α : FormField (EuclideanSpace ℂ (Fin n)) M k} (hα : α.IsSmooth) :
    (cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M) h) α).IsSmooth := by
  cases h
  exact hα

private theorem toFormField_cast_degree {k l : ℕ} (h : k = l)
    (θ : CalabiYau.DifferentialForm 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M k) :
    (cast (congrArg (CalabiYau.DifferentialForm 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M) h) θ).toFormField =
      cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M) h) θ.toFormField := by
  cases h
  rfl

private theorem extDeriv_wedge_eq_left_of_closed_right
    {k l : ℕ} (α : FormField (EuclideanSpace ℂ (Fin n)) M k)
    (β : FormField (EuclideanSpace ℂ (Fin n)) M l)
    (hα : α.IsSmooth) (hβ : β.IsSmooth) (hβc : β.IsClosed) :
    (FormField.wedge α β).extDeriv = FormField.derivWedgeLeft α β := by
  have hβzero : β.extDeriv = 0 := hβc
  have hwedgezero : FormField.wedge α (0 : FormField (EuclideanSpace ℂ (Fin n)) M (l + 1)) = 0 := by
    have h := FormField.wedge_add α (0 : FormField (EuclideanSpace ℂ (Fin n)) M (l + 1)) 0
    have h' : FormField.wedge α (0 : FormField (EuclideanSpace ℂ (Fin n)) M (l + 1)) =
        FormField.wedge α 0 + FormField.wedge α 0 := by simpa using h
    have h'' := congrArg (fun z => z - FormField.wedge α (0 : FormField (EuclideanSpace ℂ (Fin n)) M (l + 1))) h'
    have hzero : (0 : FormField (EuclideanSpace ℂ (Fin n)) M (k + (l + 1))) =
        FormField.wedge α 0 := by simpa using h''
    exact hzero.symm
  rw [FormField.extDeriv_wedge hα hβ, FormField.derivWedgeRight]
  rw [hβzero, hwedgezero]
  simp

private theorem signed_density_mixedWedge_factor (hn : 0 < n)
    (ω₀ : KahlerForm n M) (α : FormField (EuclideanSpace ℂ (Fin n)) M 2)
    (hα : α.IsOneOne) (x : M) :
    ω₀.signedTopFormDensity
      (fun y => mixedWedgeOfPos hn (α y) (ω₀ y)) x =
      (Nat.factorial (n - 1) : ℝ) * relTrace (ω₀ x) (α x) := by
  have hdenpos : 0 < topFormCoeff (ω₀.topFormVolume x) := by
    rw [← FormField.chartRep_self ω₀.topFormVolume x,
      ω₀.topFormVolume_chartCoeff x (mem_extChartAt_target x)]
    rw [volumeDensityInChart]
    exact mul_pos (by positivity)
      (RCLike.pos_iff.mp (ω₀.posDef_metricInChart x (mem_extChartAt_target x)).det_pos).1
  have hden : topFormCoeff (ω₀.topFormVolume x) ≠ 0 := hdenpos.ne'
  have htop : topFormCoeff (ω₀.topFormVolume x) =
      (Nat.factorial n : ℝ)⁻¹ * topFormCoeff (wedgePow (ω₀ x) n) := by
    simp [KahlerForm.topFormVolume, ContinuousAlternatingMap.topFormCoeff]
  have hpow : topFormCoeff (wedgePow (ω₀ x) n) ≠ 0 := by
    intro hp
    apply hden
    rw [htop, hp]
    simp
  have htrace := ContinuousAlternatingMap.trace_wedge hn (ω₀ x) (α x)
    (ω₀.isPositive x) (hα x)
  have hcoeff : relTrace (ω₀ x) (α x) * topFormCoeff (wedgePow (ω₀ x) n) =
      (n : ℝ) * topFormCoeff (mixedWedgeOfPos hn (α x) (ω₀ x)) := by
    simpa [topFormCoeff] using congrArg topFormCoeff htrace
  have hfactorial : (Nat.factorial n : ℝ) =
      (n : ℝ) * (Nat.factorial (n - 1) : ℝ) := by
    have hn' : n = (n - 1) + 1 := by omega
    rw [hn', Nat.factorial_succ]
    simp [Nat.cast_mul]
  change topFormCoeff (mixedWedgeOfPos hn (α x) (ω₀ x)) /
      topFormCoeff (ω₀.topFormVolume x) = _
  rw [htop]
  field_simp [hpow, hden]
  calc
    _ = topFormCoeff (mixedWedgeOfPos hn (α x) (ω₀ x)) *
        ((n : ℝ) * (Nat.factorial (n - 1) : ℝ)) := by rw [← hfactorial]
    _ = ((n : ℝ) * topFormCoeff (mixedWedgeOfPos hn (α x) (ω₀ x))) *
        (Nat.factorial (n - 1) : ℝ) := by ring
    _ = (relTrace (ω₀ x) (α x) * topFormCoeff (wedgePow (ω₀ x) n)) *
        (Nat.factorial (n - 1) : ℝ) := by rw [← hcoeff]
    _ = _ := by ring


end

section

variable [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M] [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
variable [MeasurableSpace M] [BorelSpace M]

private theorem signedTopFormIntegral_eq_factorial_mul_trace (hn : 0 < n)
    (ω₀ : KahlerForm n M) (α : FormField (EuclideanSpace ℂ (Fin n)) M 2)
    (hα : α.IsOneOne)
    (Θ : CalabiYau.DifferentialForm 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M (2 * n))
    (hΘ : ∀ x, CalabiYau.DifferentialForm.toFormFieldLinearMap Θ x =
      mixedWedgeOfPos hn (α x) (ω₀ x)) :
    ω₀.signedTopFormIntegral Θ =
      (Nat.factorial (n - 1) : ℝ) *
        (∫ x, relTrace (ω₀ x) (α x) ∂ω₀.volume) := by
  rw [KahlerForm.signedTopFormIntegral_apply]
  calc
    ∫ x, ω₀.signedTopFormDensity
        (CalabiYau.DifferentialForm.toFormFieldLinearMap Θ) x ∂ω₀.volume =
      ∫ x, ω₀.signedTopFormDensity (fun y => mixedWedgeOfPos hn
        (α y) (ω₀ y)) x ∂ω₀.volume := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x => by
            change topFormCoeff (CalabiYau.DifferentialForm.toFormFieldLinearMap Θ x) /
                topFormCoeff (ω₀.topFormVolume x) =
              topFormCoeff (mixedWedgeOfPos hn (α x) (ω₀ x)) /
                topFormCoeff (ω₀.topFormVolume x)
            rw [hΘ x]
    _ = ∫ x, (Nat.factorial (n - 1) : ℝ) * relTrace (ω₀ x) (α x)
        ∂ω₀.volume := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x =>
            signed_density_mixedWedge_factor hn ω₀ α hα x
    _ = (Nat.factorial (n - 1) : ℝ) *
        (∫ x, relTrace (ω₀ x) (α x) ∂ω₀.volume) := by
          rw [integral_const_mul]

private theorem integral_trace_extDeriv_eq_zero (hn : 0 < n) (ω₀ : KahlerForm n M)
    (β : FormField (EuclideanSpace ℂ (Fin n)) M 1) (hβsmooth : β.IsSmooth)
    (hβone : β.extDeriv.IsOneOne)
    (_htraceIntegrable : Integrable (fun x => relTrace (ω₀ x) (β.extDeriv x)) ω₀.volume) :
    (∫ x, relTrace (ω₀ x) (β.extDeriv x) ∂ω₀.volume) = 0 := by
  obtain ⟨Θ, hΘ, hStokes⟩ := primitiveWedge_has_zero_signedIntegral hn ω₀ β hβsmooth
  have hfactor := signedTopFormIntegral_eq_factorial_mul_trace hn ω₀ β.extDeriv hβone Θ hΘ
  rw [hStokes] at hfactor
  have hfact : (Nat.factorial (n - 1) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - 1)
  exact (mul_eq_zero.mp hfactor.symm).resolve_left hfact

/-- The smooth trace of a smooth exact real `(1,1)`-form has zero Kähler mean. -/
theorem trace_smooth_and_integral_eq_zero_of_isExact (ω₀ : KahlerForm n M)
    {α : FormField (EuclideanSpace ℂ (Fin n)) M 2}
    (hαsmooth : α.IsSmooth) (hαone : α.IsOneOne) (hαexact : α.IsExact) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (fun x => ContinuousAlternatingMap.relTrace (ω₀ x) (α x)) ∧
      (∫ x, ContinuousAlternatingMap.relTrace (ω₀ x) (α x) ∂ω₀.volume) = 0 := by
  have htraceSmooth := exact_form_trace_isSmooth ω₀ hαsmooth hαone hαexact
  refine ⟨htraceSmooth, ?_⟩
  cases n with
  | zero =>
      simp [ContinuousAlternatingMap.relTrace, Matrix.trace]
  | succ n =>
      rcases hαexact with ⟨β, hβsmooth, rfl⟩
      apply integral_trace_extDeriv_eq_zero (Nat.succ_pos n) ω₀ β hβsmooth hαone
      exact htraceSmooth.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

end

end KahlerForm
