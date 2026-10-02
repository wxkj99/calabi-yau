module

public import CalabiYau.Geometry.Kahler.Basic
import CalabiYau.Mathlib.Analysis.Matrix.PosDef.LogDet
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Regularity of the relative trace

The relative trace of two Kähler forms is smooth in a holomorphic chart. The proof combines smooth
chart coefficients with smooth matrix inversion and invariance under complex-linear chart changes.
-/

@[expose] public section

open scoped Manifold ContDiff Matrix.Norms.Elementwise ComplexOrder
open ContinuousAlternatingMap Filter

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

private theorem contDiffAt_chart_metric_relativeTrace
    (ω₀ ω₁ : KahlerForm n M) (x : M) :
    ContDiffAt ℝ 2
      (fun z : EuclideanSpace ℂ (Fin n) =>
        RCLike.re ((ω₀.metricInChart x z)⁻¹ * ω₁.metricInChart x z).trace)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) := by
  let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let G := ω₀.metricInChart x
  let H := ω₁.metricInChart x
  have hG : ContDiffAt ℝ ∞ G (c x) := by
    change ContDiffAt ℝ ∞ (fun z i j => ω₀.metricInChart x z i j) (c x)
    rw [contDiffAt_pi]
    intro i
    rw [contDiffAt_pi]
    intro j
    exact (ω₀.contDiffOn_metricInChart x i j).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))
  have hH : ContDiffAt ℝ ∞ H (c x) := by
    change ContDiffAt ℝ ∞ (fun z i j => ω₁.metricInChart x z i j) (c x)
    rw [contDiffAt_pi]
    intro i
    rw [contDiffAt_pi]
    intro j
    exact (ω₁.contDiffOn_metricInChart x i j).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))
  have hGpos : (G (c x)).PosDef := by
    change (ω₀.metricInChart x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x)).PosDef
    exact ω₀.posDef_metricInChart x (mem_extChartAt_target x)
  have hGunit : IsUnit (G (c x)) := hGpos.isUnit
  have hdet : IsUnit (G (c x)).det := (Matrix.isUnit_iff_isUnit_det _).mp hGunit
  have hInv : ContDiffAt ℝ ∞ (fun z => (G z)⁻¹) (c x) :=
    (Matrix.contDiffAt_inv hdet).comp (c x) hG
  have hInvEntry (i j : Fin n) :
      ContDiffAt ℝ ∞ (fun z => (G z)⁻¹ i j) (c x) :=
    (contDiffAt_pi.mp (contDiffAt_pi.mp hInv i) j)
  have hHEnt (i j : Fin n) :
      ContDiffAt ℝ ∞ (fun z => H z i j) (c x) :=
    (contDiffAt_pi.mp (contDiffAt_pi.mp hH i) j)
  have htraceEntry (i j : Fin n) : ContDiffAt ℝ ∞
      (fun z => Complex.reCLM ((G z)⁻¹ i j * H z j i)) (c x) := by
    exact Complex.reCLM.contDiff.comp_contDiffAt (c x)
      ((hInvEntry i j).mul (hHEnt j i))
  have htraceInner (i : Fin n) : ContDiffAt ℝ ∞
      (fun z => ∑ j : Fin n, Complex.reCLM ((G z)⁻¹ i j * H z j i)) (c x) := by
    apply ContDiffAt.sum (s := Finset.univ)
    intro j hj
    exact htraceEntry i j
  have hsum : ContDiffAt ℝ ∞
      (fun z => ∑ i : Fin n, ∑ j : Fin n,
        Complex.reCLM ((G z)⁻¹ i j * H z j i)) (c x) := by
    apply ContDiffAt.sum (s := Finset.univ)
    intro i hi
    exact htraceInner i
  have hformula : (fun z : EuclideanSpace ℂ (Fin n) =>
      RCLike.re ((G z)⁻¹ * H z).trace) =
      fun z => ∑ i : Fin n, ∑ j : Fin n,
        RCLike.re ((G z)⁻¹ i j * H z j i) := by
    funext z
    simp [Matrix.trace, Matrix.mul_apply]
  rw [hformula]
  exact hsum.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))

private theorem relativeTrace_eq_chart_metric
    (ω₀ ω₁ : KahlerForm n M) (x : M) (z : EuclideanSpace ℂ (Fin n))
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    ContinuousAlternatingMap.relTrace (ω₀ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z))
        (ω₁ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z)) =
      RCLike.re ((ω₀.metricInChart x z)⁻¹ * ω₁.metricInChart x z).trace := by
  let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let y := c.symm z
  have hyR : y ∈ c.source := c.map_target hz
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
  have hyz : c y ∈ c.target := c.map_source hyR
  have hrep₀ := FormField.chartRep_eq_chartRep_comp (α := ω₀.toFormField) hyz
    (by rw [c.left_inv hyR]; exact hyyR)
  have hrep₁ := FormField.chartRep_eq_chartRep_comp (α := ω₁.toFormField) hyz
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
  rw [hcenter, FormField.chartRep_self] at hrep₀ hrep₁
  rw [hderiv] at hrep₀ hrep₁
  have htrace := ContinuousAlternatingMap.relTrace_compContinuousLinearMap
    (ω₀.isOneOne y) (ω₁.isOneOne y) AEquiv
  have hAEquiv : (AEquiv : EuclideanSpace ℂ (Fin n) →L[ℂ]
      EuclideanSpace ℂ (Fin n)) = A := by
    ext v
    rfl
  rw [hAEquiv] at htrace
  rw [← hrep₀, ← hrep₁] at htrace
  have hresult : ContinuousAlternatingMap.relTrace (ω₀ y) (ω₁ y) =
      ContinuousAlternatingMap.relTrace (ω₀.toFormField.chartRep x (c y))
        (ω₁.toFormField.chartRep x (c y)) := by
    exact htrace.symm
  rw [show c y = z by exact c.right_inv hz] at hresult
  simpa [y, c, KahlerForm.metricInChart, ContinuousAlternatingMap.relTrace] using hresult

/-- The relative trace of two Kähler forms is smooth in the chart centered at any point. -/
theorem contDiffAt_relativeTrace_inChart (ω₀ ω₁ : KahlerForm n M) (x : M) :
    ContDiffAt ℝ 2
      ((fun y ↦ ContinuousAlternatingMap.relTrace (ω₀ y) (ω₁ y)) ∘
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) := by
  let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let F : EuclideanSpace ℂ (Fin n) → ℝ := fun z =>
    ContinuousAlternatingMap.relTrace (ω₀ (c.symm z)) (ω₁ (c.symm z))
  let Q : EuclideanSpace ℂ (Fin n) → ℝ := fun z =>
    RCLike.re ((ω₀.metricInChart x z)⁻¹ * ω₁.metricInChart x z).trace
  have hQ : ContDiffAt ℝ 2 Q (c x) := by
    simpa [Q, c] using contDiffAt_chart_metric_relativeTrace ω₀ ω₁ x
  have hEq : F =ᶠ[nhds (c x)] Q := by
    filter_upwards [((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))]
      with z hz
    exact relativeTrace_eq_chart_metric ω₀ ω₁ x z hz
  have hF : ContDiffAt ℝ 2 F (c x) := hQ.congr_of_eventuallyEq hEq
  simpa [F, c, Function.comp_def] using hF

end KahlerForm
