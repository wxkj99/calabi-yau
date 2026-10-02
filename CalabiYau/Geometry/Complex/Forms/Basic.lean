module

public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
# Real differential forms on a manifold, in charts

A real `k`-form field on a manifold `M` modelled on a real normed space `E` is represented
**unbundled**, as a function `α : M → E [⋀^Fin k]→L[ℝ] ℝ`, where `α x` is expressed in Mathlib's
identification of `T_xM` with `E` (the one used by `mfderiv` and `tangentCoordChange`, i.e. via
`chartAt E x`). Smoothness, the exterior derivative, closedness and exactness are defined through
the coordinate representation `FormField.chartRep` in the charts `extChartAt 𝓘(ℝ, E) x` and
Mathlib's `extDeriv` on normed spaces.

This is deliberately a thin layer on Mathlib only, so that the statements of the main theorems
(`Comparator/Challenge.lean`) depend on as few definitions as possible. The extracted bundled
forms (`DifferentialForm`, `exteriorDerivative`, `deRhamCohomology`) are related to this layer by
bridge lemmas in a separate module; a smooth `FormField` is exactly the underlying function of a
bundled smooth form.

## Declarations

* `FormField E M k`: unbundled real `k`-form fields.
* `FormField.chartRep α x`: the coordinate expression of `α` in the chart at `x`.
* `FormField.IsSmooth`, `FormField.extDeriv`, `FormField.IsClosed`, `FormField.IsExact`.

## Implementation notes

`FormField.extDeriv α x` is `extDeriv (α.chartRep x)` evaluated at the centre `extChartAt x x`:
the exterior derivative is computed in the chart at the point itself. `chartRep_extDeriv` shows
that for smooth forms it can be computed in any chart. Outside the domain of a chart, and for
non-smooth forms, the definitions take junk values.
-/

@[expose] public section

open scoped Manifold ContDiff
open Set

/-- Unbundled real `k`-form fields on `M`: `α x` is an alternating `k`-form on `T_xM = E`. -/
abbrev FormField (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (M : Type*) (k : ℕ) :=
  M → E [⋀^Fin k]→L[ℝ] ℝ

namespace FormField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {k : ℕ}

/-- The coordinate expression of `α` in the chart at `x`: at `z` in the chart target, the form
`α y`, `y = (extChartAt x).symm z`, transported from the chart at `y` to the chart at `x`. -/
noncomputable def chartRep (α : FormField E M k) (x : M) (z : E) : E [⋀^Fin k]→L[ℝ] ℝ :=
  (α ((extChartAt 𝓘(ℝ, E) x).symm z)).compContinuousLinearMap
    (tangentCoordChange 𝓘(ℝ, E) x ((extChartAt 𝓘(ℝ, E) x).symm z)
      ((extChartAt 𝓘(ℝ, E) x).symm z))

/-- A form field is smooth if its coordinate expression is smooth in every chart. -/
def IsSmooth (α : FormField E M k) : Prop :=
  ∀ x : M, ContDiffOn ℝ ∞ (α.chartRep x) (extChartAt 𝓘(ℝ, E) x).target

/-- The exterior derivative, computed at each point in the chart centred there. -/
noncomputable def extDeriv (α : FormField E M k) : FormField E M (k + 1) := fun x ↦
  _root_.extDeriv (α.chartRep x) (extChartAt 𝓘(ℝ, E) x x)

/-- A form field is closed if its exterior derivative vanishes. -/
def IsClosed (α : FormField E M k) : Prop :=
  α.extDeriv = 0

/-- A `(k + 1)`-form field is exact if it is the exterior derivative of a smooth `k`-form field.
Two closed forms define the same de Rham class iff their difference is exact. -/
def IsExact (α : FormField E M (k + 1)) : Prop :=
  ∃ β : FormField E M k, β.IsSmooth ∧ β.extDeriv = α

/-! ### Coordinate expressions -/

/-- At the centre of its chart, the coordinate expression is the form itself. -/
theorem chartRep_self (α : FormField E M k) (x : M) :
    α.chartRep x (extChartAt 𝓘(ℝ, E) x x) = α x := by
  have hx : x ∈ (extChartAt 𝓘(ℝ, E) x).source := mem_extChartAt_source x
  change (α ((extChartAt 𝓘(ℝ, E) x).symm (extChartAt 𝓘(ℝ, E) x x))).compContinuousLinearMap
      (tangentCoordChange 𝓘(ℝ, E) x
        ((extChartAt 𝓘(ℝ, E) x).symm (extChartAt 𝓘(ℝ, E) x x))
        ((extChartAt 𝓘(ℝ, E) x).symm (extChartAt 𝓘(ℝ, E) x x))) = α x
  rw [(extChartAt 𝓘(ℝ, E) x).left_inv hx]
  have htc : tangentCoordChange 𝓘(ℝ, E) x x x = ContinuousLinearMap.id ℝ E := by
    ext v
    exact tangentCoordChange_self hx
  rw [htc]
  ext v
  rfl

/-- Change of charts: on the overlap, the coordinate expressions in two charts are related by the
derivative of the coordinate change. -/
theorem chartRep_eq_chartRep_comp {α : FormField E M k} {x x' : M} {z : E}
    (hz : z ∈ (extChartAt 𝓘(ℝ, E) x).target)
    (hz' : (extChartAt 𝓘(ℝ, E) x).symm z ∈ (extChartAt 𝓘(ℝ, E) x').source) :
    α.chartRep x z =
      (α.chartRep x'
          (extChartAt 𝓘(ℝ, E) x' ((extChartAt 𝓘(ℝ, E) x).symm z))).compContinuousLinearMap
      (fderiv ℝ (extChartAt 𝓘(ℝ, E) x' ∘ (extChartAt 𝓘(ℝ, E) x).symm) z) := by
  let y := (extChartAt 𝓘(ℝ, E) x).symm z
  have hyx : y ∈ (extChartAt 𝓘(ℝ, E) x).source := (extChartAt 𝓘(ℝ, E) x).map_target hz
  have hyx' : y ∈ (extChartAt 𝓘(ℝ, E) x').source := hz'
  have hz_eq : extChartAt 𝓘(ℝ, E) x y = z := (extChartAt 𝓘(ℝ, E) x).right_inv hz
  have hderiv : tangentCoordChange 𝓘(ℝ, E) x x' y =
      fderiv ℝ (extChartAt 𝓘(ℝ, E) x' ∘ (extChartAt 𝓘(ℝ, E) x).symm) z := by
    rw [tangentCoordChange_def, hz_eq]
    simp
  ext v
  simp only [chartRep, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  rw [(extChartAt 𝓘(ℝ, E) x').left_inv hyx']
  change α y (fun i => tangentCoordChange 𝓘(ℝ, E) x y y (v i)) =
    α y (fun i => tangentCoordChange 𝓘(ℝ, E) x' y y
      (fderiv ℝ (extChartAt 𝓘(ℝ, E) x' ∘ (extChartAt 𝓘(ℝ, E) x).symm) z (v i)))
  apply congrArg (α y)
  funext i
  rw [← hderiv]
  exact (tangentCoordChange_comp (I := 𝓘(ℝ, E))
    (w := x) (x := x') (y := y) (z := y) (v := v i)
    ⟨⟨hyx, hyx'⟩, mem_extChartAt_source y⟩).symm

@[simp]
theorem chartRep_add (α β : FormField E M k) (x : M) :
    (α + β).chartRep x = α.chartRep x + β.chartRep x := by
  ext z v
  simp [chartRep, ContinuousAlternatingMap.compContinuousLinearMap_apply]

@[simp]
theorem chartRep_smul (c : ℝ) (α : FormField E M k) (x : M) :
    (c • α).chartRep x = c • α.chartRep x := by
  ext z v
  simp [chartRep, ContinuousAlternatingMap.compContinuousLinearMap_apply]

@[simp]
theorem chartRep_zero (x : M) : (0 : FormField E M k).chartRep x = 0 := by
  ext z v
  simp [chartRep, ContinuousAlternatingMap.compContinuousLinearMap_apply]

/-! ### Smoothness -/

theorem isSmooth_zero : (0 : FormField E M k).IsSmooth := by
  intro x
  rw [chartRep_zero]
  exact contDiffOn_const

theorem IsSmooth.add {α β : FormField E M k} (hα : α.IsSmooth) (hβ : β.IsSmooth) :
    (α + β).IsSmooth := by
  intro x
  rw [chartRep_add]
  exact (hα x).add (hβ x)

theorem IsSmooth.smul {α : FormField E M k} (hα : α.IsSmooth) (c : ℝ) : (c • α).IsSmooth := by
  intro x
  rw [chartRep_smul]
  exact (hα x).const_smul c

theorem IsSmooth.neg {α : FormField E M k} (hα : α.IsSmooth) : (-α).IsSmooth := by
  simpa only [neg_one_smul] using hα.smul (-1)

theorem IsSmooth.sub {α β : FormField E M k} (hα : α.IsSmooth) (hβ : β.IsSmooth) :
    (α - β).IsSmooth := by
  simpa only [sub_eq_add_neg] using hα.add hβ.neg

/-! ### Exterior derivative -/

/-- For a smooth form, the exterior derivative can be computed in any chart. -/
theorem chartRep_extDeriv {α : FormField E M k} (hα : α.IsSmooth) (x : M) {z : E}
    (hz : z ∈ (extChartAt 𝓘(ℝ, E) x).target) :
    α.extDeriv.chartRep x z = _root_.extDeriv (α.chartRep x) z := by
  let y := (extChartAt 𝓘(ℝ, E) x).symm z
  let f := extChartAt 𝓘(ℝ, E) y ∘ (extChartAt 𝓘(ℝ, E) x).symm
  have hz_eq : extChartAt 𝓘(ℝ, E) x y = z := (extChartAt 𝓘(ℝ, E) x).right_inv hz
  have hfz : f z = extChartAt 𝓘(ℝ, E) y y := by rfl
  have hy : y ∈ (extChartAt 𝓘(ℝ, E) y).source := mem_extChartAt_source y
  have hderiv : tangentCoordChange 𝓘(ℝ, E) x y y = fderiv ℝ f z := by
    rw [tangentCoordChange_def, hz_eq]
    simp [f]
  have hlocal : α.chartRep x =ᶠ[nhds z] fun u =>
      (α.chartRep y (f u)).compContinuousLinearMap (fderiv ℝ f u) := by
    have hznhds := (isOpen_extChartAt_target x).mem_nhds hz
    have hynhds := (continuousAt_extChartAt_symm'' hz).preimage_mem_nhds
      ((isOpen_extChartAt_source y).mem_nhds hy)
    filter_upwards [Filter.inter_mem hznhds hynhds] with u hu
    simpa [f] using (chartRep_eq_chartRep_comp (α := α) (x := x) (x' := y)
      (z := u) hu.1 hu.2)
  have hω : DifferentiableAt ℝ (α.chartRep y) (f z) := by
    have hycont := (hα y).contDiffAt (extChartAt_target_mem_nhds y)
    rw [hfz]
    exact hycont.differentiableAt (by simp)
  have hsymm : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (extChartAt 𝓘(ℝ, E) x).symm z := by
    apply (contMDiffOn_extChartAt_symm x).contMDiffAt
    exact (isOpen_extChartAt_target x).mem_nhds hz
  have hchart : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ f z := by
    exact (contMDiffAt_extChartAt (I := 𝓘(ℝ, E)) (x := y)).comp_of_eq
      hsymm rfl
  have hpull := _root_.extDeriv_pullback hω hchart.contDiffAt (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr (OrderTop.le_top (α := ℕ∞) _))
  rw [chartRep_eq_chartRep_comp (α := α.extDeriv) (x := x) (x' := y)
    (z := z) hz hy, chartRep_self]
  calc
    (α.extDeriv y).compContinuousLinearMap (fderiv ℝ f z) =
        (_root_.extDeriv (α.chartRep y) (f z)).compContinuousLinearMap (fderiv ℝ f z) := by
          rw [hfz]
          rfl
    _ = _root_.extDeriv (fun u => (α.chartRep y (f u)).compContinuousLinearMap
        (fderiv ℝ f u)) z := hpull.symm
    _ = _root_.extDeriv (α.chartRep x) z :=
      (Filter.EventuallyEq.extDeriv_eq hlocal).symm

theorem extDeriv_add {α β : FormField E M k} (hα : α.IsSmooth) (hβ : β.IsSmooth) :
    (α + β).extDeriv = α.extDeriv + β.extDeriv := by
  funext x
  change _root_.extDeriv ((α + β).chartRep x) (extChartAt 𝓘(ℝ, E) x x) =
    _root_.extDeriv (α.chartRep x) (extChartAt 𝓘(ℝ, E) x x) +
      _root_.extDeriv (β.chartRep x) (extChartAt 𝓘(ℝ, E) x x)
  rw [chartRep_add]
  apply _root_.extDeriv_add
  · exact ((hα x).contDiffAt (extChartAt_target_mem_nhds x)).differentiableAt (by simp)
  · exact ((hβ x).contDiffAt (extChartAt_target_mem_nhds x)).differentiableAt (by simp)

theorem extDeriv_smul {α : FormField E M k} (c : ℝ) :
    (c • α).extDeriv = c • α.extDeriv := by
  funext x
  change _root_.extDeriv ((c • α).chartRep x) (extChartAt 𝓘(ℝ, E) x x) =
    c • _root_.extDeriv (α.chartRep x) (extChartAt 𝓘(ℝ, E) x x)
  rw [chartRep_smul]
  exact _root_.extDeriv_smul c _

@[simp]
theorem extDeriv_zero : (0 : FormField E M k).extDeriv = 0 := by
  funext x
  change _root_.extDeriv ((0 : FormField E M k).chartRep x) (extChartAt 𝓘(ℝ, E) x x) = 0
  rw [chartRep_zero]
  change ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ
      (fderiv ℝ (fun _ : E => (0 : E [⋀^Fin k]→L[ℝ] ℝ)) _) = 0
  have hf : fderiv ℝ (fun _ : E => (0 : E [⋀^Fin k]→L[ℝ] ℝ))
      (extChartAt 𝓘(ℝ, E) x x) = 0 := by simp
  rw [hf]
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ).map_zero

/-- `d ∘ d = 0` on smooth forms. -/
theorem extDeriv_extDeriv {α : FormField E M k} (hα : α.IsSmooth) :
    α.extDeriv.extDeriv = 0 := by
  funext x
  let z := extChartAt 𝓘(ℝ, E) x x
  change _root_.extDeriv (α.extDeriv.chartRep x) z = 0
  have hEq : Filter.EventuallyEq (nhds z) (α.extDeriv.chartRep x)
      fun u => _root_.extDeriv (α.chartRep x) u := by
    filter_upwards [extChartAt_target_mem_nhds x] with u hu
    exact chartRep_extDeriv hα x hu
  rw [Filter.EventuallyEq.extDeriv_eq hEq]
  exact _root_.extDeriv_extDeriv_apply
    ((hα x).contDiffAt (extChartAt_target_mem_nhds x)) (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr (OrderTop.le_top (α := ℕ∞) _))

/-! ### Closed and exact forms -/

theorem IsClosed.add {α β : FormField E M k} (hα : α.IsSmooth) (hβ : β.IsSmooth)
    (hα' : α.IsClosed) (hβ' : β.IsClosed) : (α + β).IsClosed := by
  change (α + β).extDeriv = 0
  rw [extDeriv_add hα hβ, hα', hβ']
  simp

theorem IsClosed.smul {α : FormField E M k} (hα' : α.IsClosed) (c : ℝ) :
    (c • α).IsClosed := by
  change (c • α).extDeriv = 0
  rw [extDeriv_smul c, hα']
  simp

theorem IsExact.isClosed {α : FormField E M (k + 1)} (h : α.IsExact) : α.IsClosed := by
  obtain ⟨β, hβ, rfl⟩ := h
  change β.extDeriv.extDeriv = 0
  exact extDeriv_extDeriv hβ

theorem IsExact.add {α β : FormField E M (k + 1)} (hα : α.IsExact) (hβ : β.IsExact) :
    (α + β).IsExact := by
  obtain ⟨γα, hγα, rfl⟩ := hα
  obtain ⟨γβ, hγβ, rfl⟩ := hβ
  refine ⟨γα + γβ, hγα.add hγβ, ?_⟩
  exact extDeriv_add hγα hγβ

theorem IsExact.smul {α : FormField E M (k + 1)} (hα : α.IsExact) (c : ℝ) :
    (c • α).IsExact := by
  obtain ⟨β, hβ, rfl⟩ := hα
  refine ⟨c • β, hβ.smul c, ?_⟩
  exact extDeriv_smul c

theorem IsExact.neg {α : FormField E M (k + 1)} (hα : α.IsExact) : (-α).IsExact := by
  simpa only [neg_one_smul] using hα.smul (-1)

theorem IsExact.sub {α β : FormField E M (k + 1)} (hα : α.IsExact) (hβ : β.IsExact) :
    (α - β).IsExact := by
  simpa only [sub_eq_add_neg] using hα.add hβ.neg

end FormField
