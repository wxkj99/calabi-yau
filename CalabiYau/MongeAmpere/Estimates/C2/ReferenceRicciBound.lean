module

public import CalabiYau.Geometry.Kahler.Ricci
public import CalabiYau.Geometry.Complex.Forms.Positive

/-!
# Bounded reference Ricci trace

The Ricci form of a smooth Kähler form is smooth. On a compact manifold its trace against that
form is bounded; this is the fixed scalar term absorbed in the `C²` estimate.
-/

@[expose] public section

open scoped Manifold ContDiff
open ContinuousAlternatingMap
open Filter
open scoped Topology

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [T2Space M] [CompactSpace M]

private theorem continuousAt_relTrace_of_isPositive
    {α β : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ}
    (hα : α.IsPositive) :
    ContinuousAt (fun p : (EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) ×
      (EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) =>
        relTrace p.1 p.2) (α, β) := by
  have hcoeff : Continuous (ContinuousAlternatingMap.coeffMatrix :
      (EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) → Matrix (Fin n) (Fin n) ℂ) := by
    fun_prop [ContinuousAlternatingMap.coeffMatrix]
  have hdet_pos : 0 < RCLike.re (ContinuousAlternatingMap.coeffMatrix α).det :=
    (RCLike.pos_iff.mp ((ContinuousAlternatingMap.isPositive_iff.mp hα).2.det_pos)).1
  have hdet_ne : (ContinuousAlternatingMap.coeffMatrix α).det ≠ 0 := by
    intro h
    rw [h] at hdet_pos
    norm_num at hdet_pos
  have hdetAt : ContinuousAt (fun A : Matrix (Fin n) (Fin n) ℂ => A.det)
      (ContinuousAlternatingMap.coeffMatrix α) := by fun_prop
  have hAdjAt : ContinuousAt (fun A : Matrix (Fin n) (Fin n) ℂ => A.adjugate)
      (ContinuousAlternatingMap.coeffMatrix α) := by fun_prop
  have hinvDetAt : ContinuousAt
      (fun A : Matrix (Fin n) (Fin n) ℂ => Ring.inverse A.det)
      (ContinuousAlternatingMap.coeffMatrix α) := by
    have hinvAt : ContinuousAt (fun z : ℂ => Ring.inverse z)
        (ContinuousAlternatingMap.coeffMatrix α).det := by
      simpa only [Ring.inverse_eq_inv] using continuousAt_inv₀ hdet_ne
    exact hinvAt.comp hdetAt
  have hinvMatrix : ContinuousAt (fun A : Matrix (Fin n) (Fin n) ℂ => A⁻¹)
      (ContinuousAlternatingMap.coeffMatrix α) := by
    change ContinuousAt
      (fun A : Matrix (Fin n) (Fin n) ℂ => Ring.inverse A.det • A.adjugate)
      (ContinuousAlternatingMap.coeffMatrix α)
    exact hinvDetAt.smul hAdjAt
  have hαcoeff : ContinuousAt ContinuousAlternatingMap.coeffMatrix α := hcoeff.continuousAt
  have hβcoeff : ContinuousAt ContinuousAlternatingMap.coeffMatrix β := hcoeff.continuousAt
  have hαcoeffPair : ContinuousAt (fun p => ContinuousAlternatingMap.coeffMatrix p.1)
      (α, β) := ContinuousAt.comp' hαcoeff continuousAt_fst
  have hinvCoeff : ContinuousAt (fun p => (ContinuousAlternatingMap.coeffMatrix p.1)⁻¹)
      (α, β) := ContinuousAt.comp' hinvMatrix hαcoeffPair
  have hβcoeffPair : ContinuousAt (fun p => ContinuousAlternatingMap.coeffMatrix p.2)
      (α, β) := ContinuousAt.comp' hβcoeff continuousAt_snd
  have hmul : ContinuousAt (fun p =>
      (ContinuousAlternatingMap.coeffMatrix p.1)⁻¹ * ContinuousAlternatingMap.coeffMatrix p.2)
      (α, β) := hinvCoeff.mul hβcoeffPair
  let mat := (ContinuousAlternatingMap.coeffMatrix α)⁻¹ *
    ContinuousAlternatingMap.coeffMatrix β
  have htrace : ContinuousAt (fun A : Matrix (Fin n) (Fin n) ℂ => A.trace) mat := by fun_prop
  have hreal : ContinuousAt (fun z : ℂ => RCLike.re z) mat.trace :=
    RCLike.continuous_re.continuousAt
  have htracePair : ContinuousAt (fun p =>
      ((ContinuousAlternatingMap.coeffMatrix p.1)⁻¹ *
        ContinuousAlternatingMap.coeffMatrix p.2).trace) (α, β) :=
    ContinuousAt.comp' htrace hmul
  change ContinuousAt (fun p => RCLike.re
    ((ContinuousAlternatingMap.coeffMatrix p.1)⁻¹ *
      ContinuousAlternatingMap.coeffMatrix p.2).trace) (α, β)
  exact ContinuousAt.comp' hreal htracePair

omit [T2Space M] [CompactSpace M] in
private theorem relTrace_chartRep_eq (ω₀ : KahlerForm n M) (x y : M)
    (hy : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source) :
    relTrace (ω₀ y) (ω₀.ricciForm y) =
      relTrace (ω₀.toFormField.chartRep x
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y))
        (ω₀.ricciForm.chartRep x
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)) := by
  -- The chart transition between the chart at `x` and the centred chart at `y` is
  -- complex linear, so its pullback preserves relative trace.
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
      (tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
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
  have hrep₀ := FormField.chartRep_eq_chartRep_comp
    (α := ω₀.toFormField) hyz (by rw [c.left_inv hyR]; exact hyyR)
  have hrep₁ := FormField.chartRep_eq_chartRep_comp
    (α := ω₀.ricciForm) hyz (by rw [c.left_inv hyR]; exact hyyR)
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
  rw [hcenter, FormField.chartRep_self] at hrep₀ hrep₁
  rw [hderiv] at hrep₀ hrep₁
  have hω : (ω₀ y).IsOneOne := ω₀.isOneOne y
  have hρ : (ω₀.ricciForm y).IsOneOne := ω₀.isOneOne_ricciForm y
  have hAEquiv : (AEquiv : EuclideanSpace ℂ (Fin n) →L[ℂ]
      EuclideanSpace ℂ (Fin n)) = A := by
    ext v
    rfl
  have htrace := relTrace_compContinuousLinearMap hω hρ AEquiv
  rw [hrep₀, hrep₁]
  simpa only [hAEquiv] using htrace.symm

omit [T2Space M] [CompactSpace M] in
private theorem continuousAt_relTrace_ricciForm (ω₀ : KahlerForm n M) (x : M) :
    ContinuousAt (fun y => relTrace (ω₀ y) (ω₀.ricciForm y)) x := by
  let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let forms (z : EuclideanSpace ℂ (Fin n)) :=
    (ω₀.toFormField.chartRep x z, ω₀.ricciForm.chartRep x z)
  let tr (p : (EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) ×
      (EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)) := relTrace p.1 p.2
  have hω : ContDiffAt ℝ ∞ (ω₀.toFormField.chartRep x) (c x) :=
    (ω₀.isSmooth x).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))
  have hρ : ContDiffAt ℝ ∞ (ω₀.ricciForm.chartRep x) (c x) :=
    (ω₀.isSmooth_ricciForm x).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))
  have hforms : ContinuousAt forms (c x) := by
    exact hω.continuousAt.prodMk hρ.continuousAt
  have hrel : ContinuousAt tr (forms (c x)) := by
    have h := continuousAt_relTrace_of_isPositive (α := ω₀ x)
      (β := ω₀.ricciForm x) (ω₀.isPositive x)
    change ContinuousAt tr
      (ω₀.toFormField.chartRep x (c x), ω₀.ricciForm.chartRep x (c x))
    have hωcenter : ω₀.toFormField.chartRep x (c x) = ω₀ x := by
      exact FormField.chartRep_self ω₀.toFormField x
    have hρcenter : ω₀.ricciForm.chartRep x (c x) = ω₀.ricciForm x := by
      exact FormField.chartRep_self ω₀.ricciForm x
    rw [hωcenter, hρcenter]
    simpa [tr] using h
  have hlocal : ContinuousAt (fun z => tr (forms z)) (c x) :=
    hrel.comp' hforms
  have hchart : ContinuousAt c x := continuousAt_extChartAt x
  have hcomp : ContinuousAt (fun y => tr (forms (c y))) x := hlocal.comp' hchart
  have heq : (fun y => relTrace (ω₀ y) (ω₀.ricciForm y)) =ᶠ[𝓝 x]
      (fun y => tr (forms (c y))) := by
    filter_upwards [extChartAt_source_mem_nhds
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x] with y hy
    exact relTrace_chartRep_eq ω₀ x y (by simpa only [extChartAt_source] using hy)
  exact hcomp.congr_of_eventuallyEq heq

omit [T2Space M] in
/-- A uniform absolute bound for the reference Ricci scalar
`tr_{ω₀} Ric(ω₀)`. -/
theorem exists_abs_relTrace_ricciForm_le (ω₀ : KahlerForm n M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, |relTrace (ω₀ x) (ω₀.ricciForm x)| ≤ C := by
  let f : M → ℝ := fun x => |relTrace (ω₀ x) (ω₀.ricciForm x)|
  have hf : Continuous f := by
    apply continuous_iff_continuousAt.2
    intro x
    simpa [f] using (continuousAt_relTrace_ricciForm ω₀ x).abs
  have hbounded : BddAbove (f '' Set.univ) :=
    isCompact_univ.bddAbove_image hf.continuousOn
  obtain ⟨B, hB⟩ := hbounded
  refine ⟨max 0 B, le_max_left _ _, ?_⟩
  intro x
  have hx : f x ≤ B := hB (Set.mem_image_of_mem f (Set.mem_univ x))
  exact hx.trans (le_max_right _ _)

end KahlerForm
