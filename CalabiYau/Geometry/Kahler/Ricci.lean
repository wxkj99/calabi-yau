module

public import CalabiYau.Geometry.Kahler.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import CalabiYau.Analysis.Complex.JacobianLogNorm

/-!
# The Ricci form and the first Chern class

The **Ricci form** of a Kähler form `ω₀ = i ∑ g_{jk̄} dzⱼ ∧ dz̄ₖ` is

  `Ric(ω₀) = -i∂∂̄ log det(g_{jk̄})`,

computed in any holomorphic chart; under a change of chart `det g` is multiplied by
`|det(∂w/∂z)|²`, whose logarithm is pluriharmonic, so the result is chart independent
(`chartRep_ricciForm`). `KahlerForm.ricciForm` computes it at each point in the chart centred
there. It is the `(1,1)`-form associated with the Ricci tensor of the Riemannian metric
`g(u, v) = ω₀(u, Jv)`: `Ric(ω₀)(u, v) = Ric_g(Ju, v)` (bridge lemma to the extracted Riemannian
curvature: track R).

For two Kähler forms, `Ric(ω₀) - Ric(ω₁) = i∂∂̄ log (ω₁ⁿ / ω₀ⁿ)`
(`ricciForm_sub_ricciForm`), so the de Rham class `[Ric(ω₀)]` is independent of `ω₀`. By
Chern–Weil theory it is `2π c₁(M)`. We **define** "`γ` represents `c₁(M)` in real de Rham
cohomology" (`FormField.RepresentsFirstChernClass`) as "`γ - Ric(ω₀) / 2π` is exact for some
(equivalently, by `representsFirstChernClass_iff`, every) Kähler form `ω₀`". This is the only
notion of `c₁` used in the statement of the Calabi conjecture; its agreement with the topological
first Chern class of `T^{1,0}M` is Chern–Weil theory, which is outside the scope of the project.
-/

@[expose] public section

open scoped Manifold ContDiff
open Filter ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] (ω₀ : KahlerForm n M)

/-- `log det(g_{jk̄})` in the chart at `x`. -/
private theorem chartRep_isOneOne_in_chart (x : M) {y : M}
    (hy : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source) :
    (ω₀.toFormField.chartRep x
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)).IsOneOne := by
  have hyxR : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source := by
    rw [extChartAt_source]
    exact hy
  have hyyR : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).source :=
    mem_extChartAt_source y
  have hyxC : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source := by
    simpa only [← extChartAt_real_eq] using hyxR
  have hyyC : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source := by
    simpa only [← extChartAt_real_eq] using hyyR
  let A := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y
  let B := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y x y
  have hBA : ∀ v, B (A v) = v := by
    intro v
    calc
      B (A v) = tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x x y v := by
        exact tangentCoordChange_comp (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
          (w := x) (x := y) (y := x) (z := y) (v := v)
          ⟨⟨hyxC, hyyC⟩, hyxC⟩
      _ = v := tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
        (x := x) (z := y) (v := v) hyxC
  have hAB : ∀ v, A (B v) = v := by
    intro v
    calc
      A (B v) = tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y y y v := by
        exact tangentCoordChange_comp (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
          (w := y) (x := x) (y := y) (z := y) (v := v)
          ⟨⟨hyyC, hyxC⟩, hyyC⟩
      _ = v := tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
        (x := y) (z := y) (v := v) hyyC
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
  have hrep := FormField.chartRep_eq_chartRep_comp (α := ω₀.toFormField)
    (x := x) (x' := y) (z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)
    ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).map_source hyxR)
    (by rw [(extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).left_inv hyxR]; exact hyyR)
  have hAreal : tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y =
      A.restrictScalars ℝ := tangentCoordChange_real_eq ⟨hyxR, hyyR⟩
  have hderiv : fderiv ℝ
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y ∘
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y) = A.restrictScalars ℝ := by
    have h := hAreal
    rw [tangentCoordChange_def, extChartAt_real_eq] at h
    simpa [ModelWithCorners.range_eq_univ, fderivWithin_univ] using h
  rw [hderiv] at hrep
  have hcenter : extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y
      ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)) =
      extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y := by
    rw [(extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).left_inv hyxR]
  rw [hcenter, FormField.chartRep_self] at hrep
  have hbase := (ω₀.isOneOne y).compContinuousLinearMap AEquiv
  have hAEquiv : (AEquiv : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) = A := by
    ext v
    rfl
  rw [hAEquiv] at hbase
  rw [← hrep] at hbase
  exact hbase

private theorem metricInChart_transition_eq (x₀ x₁ : M) {y : M}
    (hy₀ : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source)
    (hy₁ : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₁).source) :
    ω₀.metricInChart x₀ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ y) =
      Matrix.transpose (EuclideanSpace.clmMatrix
        (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀ x₁ y)) *
        ω₀.metricInChart x₁ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁ y) *
        (EuclideanSpace.clmMatrix
          (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀ x₁ y)).map star := by
  let c₀ := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀
  let c₁ := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁
  let A := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀ x₁ y
  have hy₀' : y ∈ c₀.source := by
    rw [extChartAt_source]
    exact hy₀
  have hy₁' : y ∈ c₁.source := by
    rw [extChartAt_source]
    exact hy₁
  have hz₀ : c₀ y ∈ c₀.target := c₀.map_source hy₀'
  have hAreal : tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ x₁ y =
      A.restrictScalars ℝ := by
    exact tangentCoordChange_real_eq ⟨hy₀', hy₁'⟩
  have hderiv : fderiv ℝ (c₁ ∘ c₀.symm) (c₀ y) = A.restrictScalars ℝ := by
    have h := hAreal
    dsimp [A, c₀, c₁] at h ⊢
    rw [tangentCoordChange_def, extChartAt_real_eq] at h
    simpa [ModelWithCorners.range_eq_univ, fderivWithin_univ] using h
  have hrep := FormField.chartRep_eq_chartRep_comp (α := ω₀.toFormField)
    (x := x₀) (x' := x₁) (z := c₀ y) hz₀ (by rw [c₀.left_inv hy₀']; exact hy₁')
  rw [hderiv] at hrep
  have hcenter :
      extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁
          ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ y)) =
        extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁ y := by
    rw [(extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).left_inv hy₀']
  rw [hcenter] at hrep
  have hcoeff := congrArg (fun α : _ [⋀^Fin 2]→L[ℝ] ℝ => α.coeffMatrix) hrep
  rw [ContinuousAlternatingMap.IsOneOne.coeffMatrix_compContinuousLinearMap
    (chartRep_isOneOne_in_chart ω₀ x₁ hy₁) A] at hcoeff
  change (ω₀.toFormField.chartRep x₀
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ y)).coeffMatrix =
    (EuclideanSpace.clmMatrix A).transpose *
      (ω₀.toFormField.chartRep x₁
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁ y)).coeffMatrix *
      (EuclideanSpace.clmMatrix A).map star
  exact hcoeff

private theorem metricInChart_det_transition_normSq (x₀ x₁ : M) {y : M}
    (hy₀ : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source)
    (hy₁ : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₁).source) :
    (ω₀.metricInChart x₀ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ y)).det.re =
      Complex.normSq
          (EuclideanSpace.clmMatrix
            (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀ x₁ y)).det *
        (ω₀.metricInChart x₁ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁ y)).det.re := by
  let A := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀ x₁ y
  let B := EuclideanSpace.clmMatrix A
  let G₀ := ω₀.metricInChart x₀ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ y)
  let G₁ := ω₀.metricInChart x₁ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁ y)
  have hmat := metricInChart_transition_eq ω₀ x₀ x₁ hy₀ hy₁
  have hmat' : G₀ = B.transpose * G₁ * B.map star := by
    simpa [A, B, G₀, G₁] using hmat
  have hmapdet : (B.map star).det = star B.det := by
    simpa [B] using ((starRingEnd ℂ).map_det (EuclideanSpace.clmMatrix A)).symm
  have hdet : G₀.det = (B.det * G₁.det) * star B.det := by
    calc
      G₀.det = (B.transpose * G₁ * B.map star).det := congrArg Matrix.det hmat'
      _ = (B.det * G₁.det) * star B.det := by
        rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hmapdet]
  have hdet' : G₀.det = (Complex.normSq B.det : ℂ) * G₁.det := by
    calc
      G₀.det = (B.det * G₁.det) * star B.det := hdet
      _ = (B.det * star B.det) * G₁.det := by ring
      _ = (Complex.normSq B.det : ℂ) * G₁.det := by
        exact congrArg (fun z : ℂ => z * G₁.det) (Complex.mul_conj B.det)
  have hre := congrArg Complex.re hdet'
  change G₀.det.re = Complex.normSq B.det * G₁.det.re
  simpa using hre

private theorem logDetInChart_transition (x₀ x₁ : M) {y : M}
    (hy₀ : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source)
    (hy₁ : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₁).source) :
    Real.log (RCLike.re (ω₀.metricInChart x₀
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ y)).det) -
      Real.log (RCLike.re (ω₀.metricInChart x₁
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁ y)).det) =
      Real.log (Complex.normSq
        (EuclideanSpace.clmMatrix
          (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀ x₁ y)).det) := by
  let a := Complex.normSq
    (EuclideanSpace.clmMatrix
      (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀ x₁ y)).det
  let d₀ := RCLike.re (ω₀.metricInChart x₀
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ y)).det
  let d₁ := RCLike.re (ω₀.metricInChart x₁
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁ y)).det
  have hdet : d₀ = a * d₁ := by
    exact metricInChart_det_transition_normSq ω₀ x₀ x₁ hy₀ hy₁
  have hd₀ : 0 < d₀ := by
    change 0 < RCLike.re _
    exact (RCLike.pos_iff.mp
      (ω₀.posDef_metricInChart x₀ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).map_source
        (by rw [extChartAt_source]; exact hy₀))).det_pos).1
  have hd₁ : 0 < d₁ := by
    change 0 < RCLike.re _
    exact (RCLike.pos_iff.mp
      (ω₀.posDef_metricInChart x₁ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁).map_source
        (by rw [extChartAt_source]; exact hy₁))).det_pos).1
  have ha : 0 < a := by
    by_contra hn
    have hle : a ≤ 0 := le_of_not_gt hn
    have hnonneg : 0 ≤ a := Complex.normSq_nonneg _
    have hzero : a = 0 := le_antisymm hle hnonneg
    rw [hzero] at hdet
    rw [hdet] at hd₀
    norm_num at hd₀
  change Real.log d₀ - Real.log d₁ = Real.log a
  rw [hdet, Real.log_mul ha.ne' hd₁.ne']
  ring
noncomputable def logDetInChart (x : M) (z : EuclideanSpace ℂ (Fin n)) : ℝ :=
  Real.log (RCLike.re (ω₀.metricInChart x z).det)

/-- The Ricci form `Ric(ω₀) = -i∂∂̄ log det(g_{jk̄})`. -/
noncomputable def ricciForm : FormField (EuclideanSpace ℂ (Fin n)) M 2 := fun x ↦
  -ddbar (ω₀.logDetInChart x) (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x)

/-- A Kähler form is Ricci-flat if its Ricci form vanishes. -/
def IsRicciFlat : Prop :=
  ω₀.ricciForm = 0

/-- The Ricci form is computed by `-i∂∂̄ log det g` in every chart. -/
theorem chartRep_ricciForm (x : M) {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    ω₀.ricciForm.chartRep x z = -ddbar (ω₀.logDetInChart x) z := by
  let I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
  let IC := 𝓘(ℂ, EuclideanSpace ℂ (Fin n))
  let e := extChartAt I x
  let eC := extChartAt IC x
  let y := e.symm z
  let ψ := extChartAt I y ∘ e.symm
  let gₓ := ω₀.logDetInChart x
  let gᵧ := ω₀.logDetInChart y
  have hyx : y ∈ e.source := e.map_target hz
  have hyy : y ∈ (extChartAt I y).source := mem_extChartAt_source y
  have hz' : e.symm z ∈ (extChartAt I y).source := by
    change y ∈ (extChartAt I y).source
    exact hyy
  have hpoint : extChartAt I y (e.symm z) = extChartAt I y y := rfl
  have hψz : ψ z = extChartAt I y y := rfl
  have hzC : z ∈ eC.target := by
    change z ∈ (extChartAt IC x).target
    rw [← extChartAt_real_eq x]
    exact hz
  have hz'yC : eC.symm z ∈ (extChartAt IC y).source := by
    change (extChartAt IC x).symm z ∈ (extChartAt IC y).source
    rw [← extChartAt_real_eq x, ← extChartAt_real_eq y]
    exact hz'
  let U := eC.target ∩ eC.symm ⁻¹' (extChartAt IC y).source
  have hUopen : IsOpen U := by
    change IsOpen (eC.target ∩ eC.symm ⁻¹' (extChartAt IC y).source)
    exact (continuousOn_extChartAt_symm (I := IC) x).isOpen_inter_preimage
      (isOpen_extChartAt_target x) (isOpen_extChartAt_source y)
  have hzU : z ∈ U := ⟨hzC, hz'yC⟩
  have hψon : DifferentiableOn ℂ ψ U := by
    change DifferentiableOn ℂ (extChartAt IC y ∘ (extChartAt IC x).symm)
      (eC.target ∩ eC.symm ⁻¹' (extChartAt IC y).source)
    rw [← eC.image_source_inter_eq']
    exact differentiableOn_extChartAt_comp_symm x y
  have hψhol : ∀ᶠ w in nhds z, DifferentiableAt ℂ ψ w := by
    filter_upwards [hUopen.mem_nhds hzU] with w hw
    exact hψon.differentiableAt (hUopen.mem_nhds hw)
  have htransition (w : EuclideanSpace ℂ (Fin n)) (hw : w ∈ U) :
      gᵧ (ψ w) - gₓ w =
        -Real.log (Complex.normSq
          (EuclideanSpace.clmMatrix (fderiv ℂ ψ w)).det) := by
    let p := e.symm w
    have hp₀ : p ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source := by
      rw [← extChartAt_source (I := I) x]
      exact e.map_target hw.1
    have hchart (a : M) : extChartAt I a = extChartAt IC a := by
      simp [I, IC]
    have hsymm : e.symm = eC.symm := congrArg PartialEquiv.symm (hchart x)
    have hp₁ : p ∈ (chartAt (EuclideanSpace ℂ (Fin n)) y).source := by
      rw [← extChartAt_source (I := I) y]
      change e.symm w ∈ (extChartAt I y).source
      rw [hsymm]
      exact hw.2
    have hderiv : fderiv ℂ ψ w = tangentCoordChange IC x y p := by
      rw [tangentCoordChange_def]
      have hcoord : extChartAt IC x p = w := by
        dsimp [p, e, eC, I, IC]
        exact e.right_inv hw.1
      rw [hcoord]
      change fderiv ℂ (extChartAt IC y ∘ (extChartAt IC x).symm) w =
        fderivWithin ℂ (extChartAt IC y ∘ (extChartAt IC x).symm)
          (Set.range IC) w
      simp [ModelWithCorners.range_eq_univ]
    have hlog := logDetInChart_transition ω₀ x y hp₀ hp₁
    have hcoord₀ : e p = w := e.right_inv hw.1
    have hcoord₁ : ψ w = extChartAt I y p := rfl
    rw [hcoord₀, ← hcoord₁] at hlog
    have hlog' : gₓ w - gᵧ (ψ w) =
        Real.log (Complex.normSq
          (EuclideanSpace.clmMatrix (fderiv ℂ ψ w)).det) := by
      change Real.log (RCLike.re (ω₀.metricInChart x w).det) -
          Real.log (RCLike.re (ω₀.metricInChart y (ψ w)).det) =
        Real.log (Complex.normSq
          (EuclideanSpace.clmMatrix (fderiv ℂ ψ w)).det)
      simpa [hderiv, IC, extChartAt_real_eq] using hlog
    linarith
  have htransition_eventually :
      (fun w ↦ gᵧ (ψ w) - gₓ w) =ᶠ[nhds z]
        (fun w ↦ -Real.log (Complex.normSq
          (EuclideanSpace.clmMatrix (fderiv ℂ ψ w)).det)) := by
    filter_upwards [hUopen.mem_nhds hzU] with w hw
    exact htransition w hw
  have hsymmR : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) I ∞ e.symm z :=
    (contMDiffOn_extChartAt_symm (I := I) x).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz)
  have houterR : ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞
      (extChartAt I y) y := contMDiffAt_extChartAt (I := I) (n := ∞) (x := y)
  have hψR : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ ψ z := houterR.comp_of_eq hsymmR rfl
  have hlogDetAt (a : M) {w : EuclideanSpace ℂ (Fin n)}
      (hw : w ∈ (extChartAt I a).target) :
      ContDiffAt ℝ ∞ (ω₀.logDetInChart a) w := by
    let g : EuclideanSpace ℂ (Fin n) → ℂ := fun w ↦ (ω₀.metricInChart a w).det
    let q : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ RCLike.re (g w)
    have hentry (j k : Fin n) :
        ContDiffOn ℝ ∞ (fun w ↦ ω₀.metricInChart a w j k)
          (extChartAt I a).target := ω₀.contDiffOn_metricInChart a j k
    have hg : ContDiffOn ℝ ∞ g (extChartAt I a).target := by
      dsimp [g]
      simp_rw [Matrix.det_apply']
      fun_prop (disch := assumption)
    have hq : ContDiffOn ℝ ∞ q (extChartAt I a).target := by
      have h := Complex.reCLM.contDiff.contDiffOn.comp hg (Set.mapsTo_univ _ _)
      convert h using 1
      ext w
      simp [q, Complex.reCLM_apply]
    have hne : q w ≠ 0 := by
      change RCLike.re (ω₀.metricInChart a w).det ≠ 0
      exact ne_of_gt (RCLike.pos_iff.mp (ω₀.posDef_metricInChart a hw).det_pos).1
    change ContDiffAt ℝ ∞ (Real.log ∘ q) w
    exact (Real.contDiffAt_log.2 hne).comp w
      (hq.contDiffAt ((isOpen_extChartAt_target a).mem_nhds hw))
  have hgᵧ : ContDiffAt ℝ ∞ gᵧ (ψ z) := by
    rw [hψz]
    exact hlogDetAt y (mem_extChartAt_target y)
  have hgₓ : ContDiffAt ℝ ∞ gₓ z := hlogDetAt x hz
  have hcomp : ContDiffAt ℝ ∞ (fun w ↦ gᵧ (ψ w)) z := hgᵧ.comp z hψR.contDiffAt
  have h₂ᵧ : ContDiffAt ℝ 2 gᵧ (ψ z) :=
    hgᵧ.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have h₂ₓ : ContDiffAt ℝ 2 gₓ z :=
    hgₓ.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have h₂comp : ContDiffAt ℝ 2 (fun w ↦ gᵧ (ψ w)) z :=
    hcomp.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  let jacLog : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦
    Real.log (Complex.normSq
      (EuclideanSpace.clmMatrix (fderiv ℂ ψ w)).det)
  have h₂F : ContDiffAt ℝ 2 (fun w ↦ gᵧ (ψ w) - gₓ w) z :=
    h₂comp.sub h₂ₓ
  have h₂negJacLog : ContDiffAt ℝ 2 (fun w ↦ -jacLog w) z :=
    h₂F.congr_of_eventuallyEq (by simpa [jacLog] using htransition_eventually.symm)
  have h₂jacLog : ContDiffAt ℝ 2 jacLog z := by
    simpa [jacLog] using h₂negJacLog.neg
  have hderivJac :
      (fun w ↦ fderiv ℝ (fun w ↦ gᵧ (ψ w) - gₓ w) w) =ᶠ[nhds z]
        (fun w ↦ fderiv ℝ (fun w ↦ -jacLog w) w) := by
    filter_upwards [htransition_eventually.eventuallyEq_nhds] with w hw
    exact hw.fderiv_eq
  let β₁ (w : EuclideanSpace ℂ (Fin n)) :=
    ofSubsingleton ℝ (EuclideanSpace ℂ (Fin n)) ℝ (0 : Fin 1)
      ((fderiv ℝ (fun w ↦ gᵧ (ψ w) - gₓ w) w).comp
        (EuclideanSpace.complexStructure n))
  let β₂ (w : EuclideanSpace ℂ (Fin n)) :=
    ofSubsingleton ℝ (EuclideanSpace ℂ (Fin n)) ℝ (0 : Fin 1)
      ((fderiv ℝ (fun w ↦ -jacLog w) w).comp
        (EuclideanSpace.complexStructure n))
  have hβ : β₁ =ᶠ[nhds z] β₂ := by
    filter_upwards [hderivJac] with w hw
    simp [β₁, β₂, hw]
  have hddJac : ddbar (fun w ↦ gᵧ (ψ w) - gₓ w) z =
      ddbar (fun w ↦ -jacLog w) z := by
    change -(1 / 2 : ℝ) • _root_.extDeriv β₁ z =
      -(1 / 2 : ℝ) • _root_.extDeriv β₂ z
    rw [Filter.EventuallyEq.extDeriv_eq hβ]
  have hddNegJac : ddbar (fun w ↦ -jacLog w) z = -ddbar jacLog z := by
    change ddbar (-jacLog) z = -ddbar jacLog z
    have h := ddbar_smul h₂jacLog (-1 : ℝ)
    simpa using h
  have hp₀ : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source := by
    rw [← extChartAt_source (I := I) x]
    exact hyx
  have hp₁ : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) y).source := by
    rw [← extChartAt_source (I := I) y]
    exact hyy
  have hcoord₀ : extChartAt I x y = z := by
    exact e.right_inv hz
  have hmetric :
      (ω₀.metricInChart x z).det.re =
        Complex.normSq (EuclideanSpace.clmMatrix
          (tangentCoordChange IC x y y)).det *
          (ω₀.metricInChart y (ψ z)).det.re := by
    have h := metricInChart_det_transition_normSq ω₀ x y hp₀ hp₁
    rw [hcoord₀, ← hψz] at h
    exact h
  have hd₀ : 0 < (ω₀.metricInChart x z).det.re := by
    exact (RCLike.pos_iff.mp (ω₀.posDef_metricInChart x hz).det_pos).1
  have hd₁ : 0 < (ω₀.metricInChart y (ψ z)).det.re := by
    rw [hψz]
    exact (RCLike.pos_iff.mp
      (ω₀.posDef_metricInChart y (mem_extChartAt_target y)).det_pos).1
  have hnorm : 0 < Complex.normSq (EuclideanSpace.clmMatrix
      (tangentCoordChange IC x y y)).det := by
    rw [hmetric] at hd₀
    exact (mul_pos_iff_of_pos_right hd₁).mp hd₀
  have hmatrixne : (EuclideanSpace.clmMatrix
      (tangentCoordChange IC x y y)).det ≠ 0 := Complex.normSq_pos.mp hnorm
  have hchart (a : M) : extChartAt I a = extChartAt IC a := by
    simp [I, IC]
  have hsymm : e.symm = eC.symm := congrArg PartialEquiv.symm (hchart x)
  have hψeq : ψ = extChartAt IC y ∘ eC.symm := by
    change extChartAt I y ∘ e.symm = extChartAt IC y ∘ eC.symm
    rw [hchart y, hsymm]
  have hy_eq : eC.symm z = y := by
    change eC.symm z = e.symm z
    rw [hsymm.symm]
  have hcoordC : eC y = z := by
    rw [← hy_eq]
    exact eC.right_inv hzC
  have hderiv : fderiv ℂ ψ z = tangentCoordChange IC x y y := by
    rw [hψeq, tangentCoordChange_def]
    rw [hcoordC]
    change fderiv ℂ (extChartAt IC y ∘ eC.symm) z =
      fderivWithin ℂ (extChartAt IC y ∘ eC.symm) (Set.range IC) z
    simp [ModelWithCorners.range_eq_univ]
  have hmatrix :
      EuclideanSpace.clmMatrix (tangentCoordChange IC x y y) =
        LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
          (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
          (tangentCoordChange IC x y y).toLinearMap := by
    ext i j
    simp [EuclideanSpace.clmMatrix, LinearMap.toMatrix_apply,
      EuclideanSpace.basisFun_apply]
  have hdetEq :
      LinearMap.det (tangentCoordChange IC x y y).toLinearMap =
        (EuclideanSpace.clmMatrix (tangentCoordChange IC x y y)).det := by
    calc
      LinearMap.det (tangentCoordChange IC x y y).toLinearMap =
          Matrix.det (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
            (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
            (tangentCoordChange IC x y y).toLinearMap) :=
        (LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
          (tangentCoordChange IC x y y).toLinearMap).symm
      _ = (EuclideanSpace.clmMatrix (tangentCoordChange IC x y y)).det := by
        rw [← hmatrix]
  have hdet : LinearMap.det (fderiv ℂ ψ z).toLinearMap ≠ 0 := by
    rw [hderiv, hdetEq]
    exact hmatrixne
  have hpluri : ddbar jacLog z = 0 := by
    /- This is the local pluriharmonicity of the logarithm of the squared norm of a
       nonvanishing holomorphic Jacobian. -/
    have hmatrixDet (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
        LinearMap.det A.toLinearMap = (EuclideanSpace.clmMatrix A).det := by
      have hmatrix :
          EuclideanSpace.clmMatrix A =
            LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
              (EuclideanSpace.basisFun (Fin n) ℂ).toBasis A.toLinearMap := by
        ext i j
        simp [EuclideanSpace.clmMatrix, LinearMap.toMatrix_apply,
          EuclideanSpace.basisFun_apply]
      calc
        LinearMap.det A.toLinearMap =
            Matrix.det (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
              (EuclideanSpace.basisFun (Fin n) ℂ).toBasis A.toLinearMap) :=
          (LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
            A.toLinearMap).symm
        _ = (EuclideanSpace.clmMatrix A).det := by rw [← hmatrix]
    have hjacLog : jacLog = fun w =>
        Real.log (Complex.normSq (LinearMap.det (fderiv ℂ ψ w).toLinearMap)) := by
      funext w
      dsimp [jacLog]
      rw [hmatrixDet]
    have h₂jacLog' : ContDiffAt ℝ 2
        (fun w => Real.log (Complex.normSq (LinearMap.det (fderiv ℂ ψ w).toLinearMap))) z := by
      rw [← hjacLog]
      exact h₂jacLog
    have hψ3 : ContDiffAt ℝ 3 ψ z :=
      hψR.contDiffAt.of_le
        (WithTop.coe_le_coe.mpr (show (3 : ℕ∞) ≤ ⊤ from le_top))
    have hmixed := Complex.jacobianLogNorm_mixed_hessian hψ3 hψhol hdet
    rw [hjacLog]
    ext u
    have hu : u = ![u 0, u 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hu]
    change ddbar
      (fun w : EuclideanSpace ℂ (Fin n) =>
        Real.log (Complex.normSq (LinearMap.det (fderiv ℂ ψ w).toLinearMap))) z
      ![u 0, u 1] = 0
    rw [ddbar_apply h₂jacLog' (u 0) (u 1), hmixed (u 0) (u 1)]
    ring
  have hJac : ddbar (fun w ↦ gᵧ (ψ w) - gₓ w) z = 0 := by
    rw [hddJac, hddNegJac, hpluri]
    simp
  have hsub := ddbar_sub h₂comp h₂ₓ
  have hsub' : ddbar (fun w ↦ gᵧ (ψ w) - gₓ w) z =
      ddbar (fun w ↦ gᵧ (ψ w)) z - ddbar gₓ z := by
    have hfun : (fun w ↦ gᵧ (ψ w)) - gₓ =
        (fun w ↦ gᵧ (ψ w) - gₓ w) := rfl
    rw [← hfun]
    exact hsub
  have hddEq : ddbar (fun w ↦ gᵧ (ψ w)) z = ddbar gₓ z := by
    rw [hsub'] at hJac
    exact sub_eq_zero.mp hJac
  have hψdiff : DifferentiableAt ℂ ψ z := hψhol.self_of_nhds
  have hderiv : fderiv ℝ ψ z = (fderiv ℂ ψ z).restrictScalars ℝ :=
    hψdiff.fderiv_restrictScalars ℝ
  have hddcomp := ddbar_comp_holomorphic hψhol h₂ᵧ
  rw [FormField.chartRep_eq_chartRep_comp (α := ω₀.ricciForm) hz hz', hpoint,
    FormField.chartRep_self]
  change (-ddbar gᵧ (extChartAt I y y)).compContinuousLinearMap (fderiv ℝ ψ z) =
    -ddbar gₓ z
  rw [hψz] at hddcomp
  calc
    (-ddbar gᵧ (extChartAt I y y)).compContinuousLinearMap (fderiv ℝ ψ z) =
        -(ddbar gᵧ (extChartAt I y y)).compContinuousLinearMap (fderiv ℝ ψ z) := by
      ext v
      simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    _ = -(ddbar gᵧ (extChartAt I y y)).compContinuousLinearMap
        ((fderiv ℂ ψ z).restrictScalars ℝ) := by rw [hderiv]
    _ = -ddbar (fun w ↦ gᵧ (ψ w)) z := congrArg Neg.neg hddcomp.symm
    _ = -ddbar gₓ z := congrArg Neg.neg hddEq

theorem contDiffOn_logDetInChart (x : M) :
    ContDiffOn ℝ ∞ (ω₀.logDetInChart x) (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
  let g : EuclideanSpace ℂ (Fin n) → ℂ := fun z ↦ (ω₀.metricInChart x z).det
  let f : EuclideanSpace ℂ (Fin n) → ℝ := fun z ↦ RCLike.re (g z)
  have hEntry (i j : Fin n) :
      ContDiffOn ℝ ∞ (fun z ↦ ω₀.metricInChart x z i j)
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target :=
    ω₀.contDiffOn_metricInChart x i j
  have hg : ContDiffOn ℝ ∞ g (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
    dsimp [g]
    simp_rw [Matrix.det_apply']
    fun_prop (disch := assumption)
  have hf : ContDiffOn ℝ ∞ f (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
    have h := Complex.reCLM.contDiff.contDiffOn.comp hg (Set.mapsTo_univ _ _)
    convert h using 1
    ext z
    simp [f, Complex.reCLM_apply]
  have hmap : Set.MapsTo f (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target {0}ᶜ := by
    intro z hz
    change f z ≠ 0
    dsimp [f, g]
    exact ne_of_gt (RCLike.pos_iff.mp (ω₀.posDef_metricInChart x hz).det_pos).1
  change ContDiffOn ℝ ∞ (Real.log ∘ f) _
  exact ContDiffOn.comp Real.contDiffOn_log hf hmap

theorem isSmooth_ricciForm : ω₀.ricciForm.IsSmooth := by
  intro x
  have hdd : ContDiffOn ℝ ∞ (fun z ↦ -ddbar (ω₀.logDetInChart x) z)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target :=
    ((contDiffOn_logDetInChart ω₀ x).ddbar (isOpen_extChartAt_target x)).neg
  exact hdd.congr (fun z hz ↦ chartRep_ricciForm ω₀ x hz)

theorem isOneOne_ricciForm : ω₀.ricciForm.IsOneOne := by
  intro x
  let z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x
  have hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
    exact mem_extChartAt_target x
  have hlog : ContDiffAt ℝ ∞ (ω₀.logDetInChart x) z :=
    (contDiffOn_logDetInChart ω₀ x).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz)
  change (-ddbar (ω₀.logDetInChart x) z).IsOneOne
  exact (isOneOne_ddbar (hlog.of_le
    (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))).neg

/-- Change of Kähler form: `Ric(ω₁) = Ric(ω₀) - i∂∂̄ log (ω₁ⁿ / ω₀ⁿ)`. -/
theorem ricciForm_eq_sub_mddbar (ω₁ : KahlerForm n M) :
    ω₁.ricciForm = ω₀.ricciForm - mddbar n (fun x ↦ Real.log (relDet (ω₀ x) (ω₁ x))) := by
  funext x
  let I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
  let IC := 𝓘(ℂ, EuclideanSpace ℂ (Fin n))
  let e := extChartAt I x
  let z := e x
  let f : M → ℝ := fun y ↦ Real.log (relDet (ω₀ y) (ω₁ y))
  let fChart : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ f (e.symm w)
  let g₀ : EuclideanSpace ℂ (Fin n) → ℝ := ω₀.logDetInChart x
  let g₁ : EuclideanSpace ℂ (Fin n) → ℝ := ω₁.logDetInChart x
  change -ddbar g₁ z = -ddbar g₀ z - ddbar fChart z
  have hrel {w : EuclideanSpace ℂ (Fin n)} (hw : w ∈ e.target) :
      relDet (ω₀ (e.symm w)) (ω₁ (e.symm w)) =
        RCLike.re (ω₁.metricInChart x w).det / RCLike.re (ω₀.metricInChart x w).det := by
    let y := e.symm w
    have hyx : y ∈ e.source := e.map_target hw
    have hyy : y ∈ (extChartAt I y).source := mem_extChartAt_source y
    have hw' : e.symm w ∈ (extChartAt I y).source := by
      change y ∈ (extChartAt I y).source
      exact hyy
    have hpoint : extChartAt I y (e.symm w) = extChartAt I y y := rfl
    have hxC : y ∈ (extChartAt IC x).source := by
      rw [← extChartAt_real_eq x]
      exact hyx
    have hyC : y ∈ (extChartAt IC y).source := by
      rw [← extChartAt_real_eq y]
      exact hyy
    have hxyR : y ∈ e.source ∩ (extChartAt I y).source := ⟨hyx, hyy⟩
    let A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
      tangentCoordChange IC x y y
    let B : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
      tangentCoordChange IC y x y
    have hAB (v : EuclideanSpace ℂ (Fin n)) : A (B v) = v := by
      calc
        A (B v) = tangentCoordChange IC y y y v := by
          exact tangentCoordChange_comp (I := IC) (w := y) (x := x) (y := y) (z := y)
            (h := ⟨⟨hyC, hxC⟩, hyC⟩) (v := v)
        _ = v := tangentCoordChange_self (I := IC) (x := y) (z := y) hyC
    have hBA (v : EuclideanSpace ℂ (Fin n)) : B (A v) = v := by
      calc
        B (A v) = tangentCoordChange IC x x y v := by
          exact tangentCoordChange_comp (I := IC) (w := x) (x := y) (y := x) (z := y)
            (h := ⟨⟨hxC, hyC⟩, hxC⟩) (v := v)
        _ = v := tangentCoordChange_self (I := IC) (x := x) (z := y) hxC
    have hAinj : Function.Injective A := by
      intro u v huv
      calc
        u = B (A u) := (hBA u).symm
        _ = B (A v) := congrArg B huv
        _ = v := hBA v
    have hAsurj : Function.Surjective A := by
      intro v
      exact ⟨B v, hAB v⟩
    let eA : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n) :=
      let eLin := LinearEquiv.ofBijective A.toLinearMap ⟨hAinj, hAsurj⟩
      eLin.toContinuousLinearEquivOfContinuous eLin.toLinearMap.continuous_of_finiteDimensional
    have hAreal : tangentCoordChange I x y y = A.restrictScalars ℝ :=
      tangentCoordChange_real_eq hxyR
    have htransition :
        fderiv ℝ (extChartAt I y ∘ e.symm) w = A.restrictScalars ℝ := by
      calc
        _ = tangentCoordChange I x y y := by
          rw [tangentCoordChange_def, e.right_inv hw, ModelWithCorners.range_eq_univ,
            fderivWithin_univ]
        _ = A.restrictScalars ℝ := hAreal
    have hrep (α : FormField (EuclideanSpace ℂ (Fin n)) M 2) :
        α.chartRep x w = (α y).compContinuousLinearMap (A.restrictScalars ℝ) := by
      rw [FormField.chartRep_eq_chartRep_comp hw hw', htransition, hpoint]
      exact congrArg (fun β ↦ β.compContinuousLinearMap (A.restrictScalars ℝ))
        (FormField.chartRep_self α y)
    have hrel' := (relDet_compContinuousLinearMap (ω₀.isOneOne y) (ω₁.isOneOne y) eA).symm
    have hAe : (eA : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) = A := by
      ext v
      rfl
    rw [hAe] at hrel'
    rw [← hrep ω₀.toFormField, ← hrep ω₁.toFormField] at hrel'
    change relDet (ω₀ y) (ω₁ y) =
      RCLike.re (ω₁.metricInChart x w).det / RCLike.re (ω₀.metricInChart x w).det
    rw [hrel']
    rfl
  have hEq : fChart =ᶠ[nhds z] (fun w ↦ g₁ w - g₀ w) := by
    filter_upwards [extChartAt_target_mem_nhds x] with w hw
    have hpos₀ : 0 < RCLike.re (ω₀.metricInChart x w).det :=
      (RCLike.pos_iff.mp (ω₀.posDef_metricInChart x hw).det_pos).1
    have hpos₁ : 0 < RCLike.re (ω₁.metricInChart x w).det :=
      (RCLike.pos_iff.mp (ω₁.posDef_metricInChart x hw).det_pos).1
    change Real.log (relDet (ω₀ (e.symm w)) (ω₁ (e.symm w))) =
      Real.log (RCLike.re (ω₁.metricInChart x w).det) -
        Real.log (RCLike.re (ω₀.metricInChart x w).det)
    rw [hrel hw, Real.log_div hpos₁.ne' hpos₀.ne']
  have hderiv :
      (fun w ↦ fderiv ℝ fChart w) =ᶠ[nhds z]
        (fun w ↦ fderiv ℝ (fun w ↦ g₁ w - g₀ w) w) := by
    filter_upwards [hEq.eventuallyEq_nhds] with w hw
    exact hw.fderiv_eq
  let β₁ (w : EuclideanSpace ℂ (Fin n)) :=
    ofSubsingleton ℝ (EuclideanSpace ℂ (Fin n)) ℝ (0 : Fin 1)
      ((fderiv ℝ fChart w).comp (EuclideanSpace.complexStructure n))
  let β₂ (w : EuclideanSpace ℂ (Fin n)) :=
    ofSubsingleton ℝ (EuclideanSpace ℂ (Fin n)) ℝ (0 : Fin 1)
      ((fderiv ℝ (fun w ↦ g₁ w - g₀ w) w).comp (EuclideanSpace.complexStructure n))
  have hβ : β₁ =ᶠ[nhds z] β₂ := by
    filter_upwards [hderiv] with w hw
    simp [β₁, β₂, hw]
  have hdd : ddbar fChart z = ddbar (fun w ↦ g₁ w - g₀ w) z := by
    change -(1 / 2 : ℝ) • _root_.extDeriv β₁ z =
      -(1 / 2 : ℝ) • _root_.extDeriv β₂ z
    rw [Filter.EventuallyEq.extDeriv_eq hβ]
  have hlog₀ : ContDiffAt ℝ ∞ g₀ z :=
    (contDiffOn_logDetInChart ω₀ x).contDiffAt (extChartAt_target_mem_nhds x)
  have hlog₁ : ContDiffAt ℝ ∞ g₁ z :=
    (contDiffOn_logDetInChart ω₁ x).contDiffAt (extChartAt_target_mem_nhds x)
  have h₂₀ : ContDiffAt ℝ 2 g₀ z :=
    hlog₀.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have h₂₁ : ContDiffAt ℝ 2 g₁ z :=
    hlog₁.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hsub := ddbar_sub h₂₁ h₂₀
  have hsub' : ddbar (fun w ↦ g₁ w - g₀ w) z = ddbar g₁ z - ddbar g₀ z := by
    have hfun : g₁ - g₀ = (fun w ↦ g₁ w - g₀ w) := rfl
    rw [← hfun]
    exact hsub
  rw [hdd, hsub']
  abel

theorem contMDiff_log_relDet (ω₁ : KahlerForm n M) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (fun x ↦ Real.log (relDet (ω₀ x) (ω₁ x))) := by
  let I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
  let IC := 𝓘(ℂ, EuclideanSpace ℂ (Fin n))
  let f : M → ℝ := fun x ↦ Real.log (relDet (ω₀ x) (ω₁ x))
  have hchart (x : M) :
      ContDiffOn ℝ ∞ (fun z ↦ f ((extChartAt I x).symm z)) (extChartAt I x).target := by
    let e := extChartAt I x
    let g₀ : EuclideanSpace ℂ (Fin n) → ℝ :=
      fun z ↦ RCLike.re (ω₀.metricInChart x z).det
    let g₁ : EuclideanSpace ℂ (Fin n) → ℝ :=
      fun z ↦ RCLike.re (ω₁.metricInChart x z).det
    have hg₀ : ContDiffOn ℝ ∞ g₀ e.target := by
      have h := Real.contDiff_exp.contDiffOn.comp (contDiffOn_logDetInChart ω₀ x)
        (Set.mapsTo_univ _ _)
      apply h.congr
      intro z hz
      change g₀ z = Real.exp (ω₀.logDetInChart x z)
      symm
      exact Real.exp_log
        (RCLike.pos_iff.mp (ω₀.posDef_metricInChart x hz).det_pos).1
    have hg₁ : ContDiffOn ℝ ∞ g₁ e.target := by
      have h := Real.contDiff_exp.contDiffOn.comp (contDiffOn_logDetInChart ω₁ x)
        (Set.mapsTo_univ _ _)
      apply h.congr
      intro z hz
      change g₁ z = Real.exp (ω₁.logDetInChart x z)
      symm
      exact Real.exp_log
        (RCLike.pos_iff.mp (ω₁.posDef_metricInChart x hz).det_pos).1
    have hg₀_pos {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ e.target) : 0 < g₀ z := by
      dsimp [g₀]
      exact (RCLike.pos_iff.mp (ω₀.posDef_metricInChart x hz).det_pos).1
    have hg₁_pos {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ e.target) : 0 < g₁ z := by
      dsimp [g₁]
      exact (RCLike.pos_iff.mp (ω₁.posDef_metricInChart x hz).det_pos).1
    have hratio : ContDiffOn ℝ ∞ (fun z ↦ g₁ z / g₀ z) e.target :=
      hg₁.div hg₀ (fun z hz ↦ (hg₀_pos hz).ne')
    have hratio_ne : Set.MapsTo (fun z ↦ g₁ z / g₀ z) e.target {0}ᶜ := by
      intro z hz
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact (div_pos (hg₁_pos hz) (hg₀_pos hz)).ne'
    have hlogratio : ContDiffOn ℝ ∞ (fun z ↦ Real.log (g₁ z / g₀ z)) e.target :=
      ContDiffOn.comp Real.contDiffOn_log hratio hratio_ne
    apply hlogratio.congr
    intro z hz
    let y := e.symm z
    have hyx : y ∈ e.source := e.map_target hz
    have hyy : y ∈ (extChartAt I y).source := mem_extChartAt_source y
    have hz' : e.symm z ∈ (extChartAt I y).source := by
      change y ∈ (extChartAt I y).source
      exact hyy
    have hpoint : extChartAt I y (e.symm z) = extChartAt I y y := by
      rfl
    have hxC : y ∈ (extChartAt IC x).source := by
      rw [← extChartAt_real_eq x]
      exact hyx
    have hyC : y ∈ (extChartAt IC y).source := by
      rw [← extChartAt_real_eq y]
      exact hyy
    have hxyR : y ∈ e.source ∩ (extChartAt I y).source := ⟨hyx, hyy⟩
    let A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
      tangentCoordChange IC x y y
    let B : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
      tangentCoordChange IC y x y
    have hAB (v : EuclideanSpace ℂ (Fin n)) : A (B v) = v := by
      calc
        A (B v) = tangentCoordChange IC y y y v := by
          exact tangentCoordChange_comp (I := IC) (w := y) (x := x) (y := y) (z := y)
            (h := ⟨⟨hyC, hxC⟩, hyC⟩) (v := v)
        _ = v := tangentCoordChange_self (I := IC) (x := y) (z := y) hyC
    have hBA (v : EuclideanSpace ℂ (Fin n)) : B (A v) = v := by
      calc
        B (A v) = tangentCoordChange IC x x y v := by
          exact tangentCoordChange_comp (I := IC) (w := x) (x := y) (y := x) (z := y)
            (h := ⟨⟨hxC, hyC⟩, hxC⟩) (v := v)
        _ = v := tangentCoordChange_self (I := IC) (x := x) (z := y) hxC
    have hAinj : Function.Injective A := by
      intro u v huv
      calc
        u = B (A u) := (hBA u).symm
        _ = B (A v) := congrArg B huv
        _ = v := hBA v
    have hAsurj : Function.Surjective A := by
      intro v
      exact ⟨B v, hAB v⟩
    let eA : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n) :=
      let eLin := LinearEquiv.ofBijective A.toLinearMap ⟨hAinj, hAsurj⟩
      eLin.toContinuousLinearEquivOfContinuous eLin.toLinearMap.continuous_of_finiteDimensional
    have hAreal : tangentCoordChange I x y y = A.restrictScalars ℝ :=
      tangentCoordChange_real_eq hxyR
    have htransition :
        fderiv ℝ (extChartAt I y ∘ e.symm) z = A.restrictScalars ℝ := by
      calc
        _ = tangentCoordChange I x y y := by
          rw [tangentCoordChange_def, e.right_inv hz, ModelWithCorners.range_eq_univ,
            fderivWithin_univ]
        _ = A.restrictScalars ℝ := hAreal
    have hrep (α : FormField (EuclideanSpace ℂ (Fin n)) M 2) :
        α.chartRep x z = (α y).compContinuousLinearMap (A.restrictScalars ℝ) := by
      rw [FormField.chartRep_eq_chartRep_comp hz hz', htransition, hpoint]
      exact congrArg (fun β ↦ β.compContinuousLinearMap (A.restrictScalars ℝ))
        (FormField.chartRep_self α y)
    have hrel := (relDet_compContinuousLinearMap (ω₀.isOneOne y) (ω₁.isOneOne y) eA).symm
    have hAe : (eA : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) = A := by
      ext v
      rfl
    rw [hAe] at hrel
    rw [← hrep ω₀.toFormField, ← hrep ω₁.toFormField] at hrel
    calc
      f y = Real.log (relDet (ω₀ y) (ω₁ y)) := rfl
      _ = Real.log (relDet (ω₀.toFormField.chartRep x z)
          (ω₁.toFormField.chartRep x z)) := congrArg Real.log hrel
      _ = Real.log (g₁ z / g₀ z) := rfl
  rw [contMDiff_iff]
  refine ⟨?_, ?_⟩
  · apply continuous_iff_continuousAt.2
    intro x
    let e := extChartAt I x
    let g := fun z ↦ f (e.symm z)
    have hg : ContDiffAt ℝ ∞ g (e x) :=
      (hchart x).contDiffAt ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))
    have hgcomp : ContinuousAt (fun p ↦ g (e p)) x :=
      hg.continuousAt.comp
        (contMDiffAt_extChartAt
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (n := ∞) (x := x)).continuousAt
    have hEq : (fun p ↦ g (e p)) =ᶠ[nhds x] f := by
      filter_upwards [
        (isOpen_extChartAt_source (I := I) x).mem_nhds
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
    change ContDiffOn ℝ ∞
      (fun z ↦ Real.log (relDet
        (ω₀ ((chartAt (EuclideanSpace ℂ (Fin n)) x).symm z))
        (ω₁ ((chartAt (EuclideanSpace ℂ (Fin n)) x).symm z))))
      (chartAt (EuclideanSpace ℂ (Fin n)) x).target
    simpa [f, Function.comp_apply, ModelWithCorners.range_eq_univ] using hx

/-- **Metric independence of the Ricci class**, explicit form:
`Ric(ω₀) - Ric(ω₁) = i∂∂̄ log (ω₁ⁿ / ω₀ⁿ)`. -/
theorem ricciForm_sub_ricciForm (ω₁ : KahlerForm n M) :
    ω₀.ricciForm - ω₁.ricciForm = mddbar n (fun x ↦ Real.log (relDet (ω₀ x) (ω₁ x))) := by
  rw [ricciForm_eq_sub_mddbar ω₀ ω₁]
  abel

/-- The Ricci form of `ω₀ + i∂∂̄φ`: `Ric(ω_φ) = Ric(ω₀) - i∂∂̄ log ((ω₀ + i∂∂̄φ)ⁿ / ω₀ⁿ)`. -/
theorem ricciForm_perturb {φ : M → ℝ} (hφ : ω₀.IsPotential φ) :
    (ω₀.perturb φ hφ).ricciForm =
      ω₀.ricciForm - mddbar n (fun x ↦ Real.log (relDet (ω₀ x) (ω₀ x + mddbar n φ x))) := by
  simpa only [perturb_apply] using ricciForm_eq_sub_mddbar ω₀ (ω₀.perturb φ hφ)

end KahlerForm

namespace FormField

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- The real `2`-form `γ` represents the first Chern class `c₁(M)` in de Rham cohomology:
`[γ] = [Ric(ω₀) / 2π]` for some Kähler form `ω₀` (Chern–Weil). -/
def RepresentsFirstChernClass (γ : FormField (EuclideanSpace ℂ (Fin n)) M 2) : Prop :=
  ∃ ω₀ : KahlerForm n M, (γ - (2 * Real.pi)⁻¹ • ω₀.ricciForm).IsExact

/-- The choice of Kähler form in `RepresentsFirstChernClass` is irrelevant. -/
theorem representsFirstChernClass_iff (ω₀ : KahlerForm n M)
    {γ : FormField (EuclideanSpace ℂ (Fin n)) M 2} :
    γ.RepresentsFirstChernClass ↔ (γ - (2 * Real.pi)⁻¹ • ω₀.ricciForm).IsExact := by
  constructor
  · rintro ⟨ω₁, hγ⟩
    have hdiff : ((2 * Real.pi)⁻¹ • (ω₁.ricciForm - ω₀.ricciForm)).IsExact := by
      have hrel : ω₁.ricciForm - ω₀.ricciForm =
          -mddbar n (fun x ↦ Real.log (relDet (ω₀ x) (ω₁ x))) := by
        calc
          ω₁.ricciForm - ω₀.ricciForm = -(ω₀.ricciForm - ω₁.ricciForm) := by abel
          _ = -mddbar n (fun x ↦ Real.log (relDet (ω₀ x) (ω₁ x))) := by
            rw [KahlerForm.ricciForm_sub_ricciForm ω₀ ω₁]
      rw [hrel]
      simpa [smul_neg, neg_smul] using
        (isExact_mddbar (KahlerForm.contMDiff_log_relDet ω₀ ω₁)).smul (-(2 * Real.pi)⁻¹)
    convert hγ.add hdiff using 1; module
  · intro hγ
    exact ⟨ω₀, hγ⟩

end FormField
