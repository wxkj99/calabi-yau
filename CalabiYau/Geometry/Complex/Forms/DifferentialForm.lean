module

public import CalabiYau.Geometry.Complex.Forms.Basic
public import CalabiYau.Geometry.Manifold.DifferentialForm.Basic
public import CalabiYau.Geometry.Manifold.Bundle.TangentSpace

/-!
# Smooth unbundled forms and smooth alternating tangent-bundle sections

The representation of `FormField E M k` uses the tangent model at each varying point.
It is not in general a smooth map from `M` to the fixed space of alternating maps.
`tangentSection_chart` identifies its **fixed-chart** representative with the actual
alternating tangent-bundle trivialization. The tangent identification is explicitly
`CalabiYau.tangentSpaceModelContinuousLinearEquiv`, rather than a tensor-model embedding.

`isSmooth_iff_contMDiff_tangentSection` proves the two smoothness notions equivalent;
`smoothEquivDifferentialForm` bundles this equivalence. The bridge is real-linear and
commutes with the two exterior derivatives, with no factor, sign or factorial change.
On the model space itself, `isSmooth_model_iff` reduces to ordinary `ContDiff`.

## Source and conventions

Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 14: differential forms as
smooth sections of exterior powers of the cotangent bundle, and the coordinate formula
for their exterior derivative. The bundled coordinate formula used here is the extracted
differential-geometry `DifferentialForm.exteriorDerivative_localRepresentation`.

The model is `𝓘(ℝ, E)`, hence boundaryless; no additional boundary, orientation, metric,
compactness, positive dimension, or finite-dimensionality assumption is needed.
All degrees, including degree zero, are allowed. Off-chart junk is compared only on
chart targets or in a neighborhood of a chart centre.
-/

@[expose] public section

open scoped Manifold ContDiff Topology
open Bundle Set Filter

namespace FormField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {k : ℕ}

attribute [local instance] CalabiYau.normedAddCommGroupTangentSpace
  CalabiYau.normedSpaceTangentSpace

/-- Interpret the form value using the canonical tangent-to-model identification. -/
noncomputable def tangentSection (α : FormField E M k) (x : M) :
    Bundle.continuousAlternatingMap ℝ (Fin k) E (TangentSpace 𝓘(ℝ, E)) ℝ
      (Bundle.Trivial M ℝ) x :=
  (α x).compContinuousLinearMap
    (CalabiYau.tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).toContinuousLinearMap

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
@[simp] theorem tangentSection_apply (α : FormField E M k) (x : M)
    (v : Fin k → TangentSpace 𝓘(ℝ, E) x) :
    tangentSection α x v = α x (fun i =>
      CalabiYau.tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x (v i)) := rfl

/-- The alternating bundle chart is exactly `FormField.chartRep` on the chart target. -/
theorem tangentSection_chart (α : FormField E M k) (c : M) {z : E}
    (hz : z ∈ (extChartAt 𝓘(ℝ, E) c).target) :
    (trivializationAt (E [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) E (TangentSpace 𝓘(ℝ, E)) ℝ
        (Bundle.Trivial M ℝ)) c
      ⟨(extChartAt 𝓘(ℝ, E) c).symm z, tangentSection α ((extChartAt 𝓘(ℝ, E) c).symm z)⟩).2 =
      α.chartRep c z := by
  rw [CalabiYau.continuousAlternatingMap_trivializationAt_apply]
  have hy : (extChartAt 𝓘(ℝ, E) c).symm z ∈ (chartAt E c).source := by
    simpa only [extChartAt_source] using (extChartAt 𝓘(ℝ, E) c).map_target hz
  rw [TangentBundle.symmL_trivializationAt_eq_core hy]
  ext v
  rfl

theorem IsSmooth.contMDiff_tangentSection {α : FormField E M k} (hα : α.IsSmooth) :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] ℝ) x (tangentSection α x)) := by
  intro c
  let e := trivializationAt (E [⋀^Fin k]→L[ℝ] ℝ)
    (Bundle.continuousAlternatingMap ℝ (Fin k) E (TangentSpace 𝓘(ℝ, E)) ℝ
      (Bundle.Trivial M ℝ)) c
  rw [Bundle.Trivialization.contMDiffAt_section_iff e
    (mem_baseSet_trivializationAt (E [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) E (TangentSpace 𝓘(ℝ, E)) ℝ
        (Bundle.Trivial M ℝ)) c)]
  have hs := ((hα c).contDiffAt (extChartAt_target_mem_nhds c)).contMDiffAt
  have hc := (contMDiffAt_extChartAt (I := 𝓘(ℝ, E)) (n := ∞) (x := c))
  have hcomp := hs.comp c hc
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_extChartAt_source (I := 𝓘(ℝ, E)) c).mem_nhds
    (mem_extChartAt_source c)] with x hx
  have hid := tangentSection_chart α c ((extChartAt 𝓘(ℝ, E) c).map_source hx)
  rw [(extChartAt 𝓘(ℝ, E) c).left_inv hx] at hid
  exact hid

/-- Bundle a chartwise smooth form as a smooth alternating tangent-bundle section. -/
noncomputable def toDifferentialForm (α : FormField E M k) (hα : α.IsSmooth) :
    CalabiYau.DifferentialForm 𝓘(ℝ, E) M k :=
  ⟨tangentSection α, hα.contMDiff_tangentSection⟩

end FormField

namespace CalabiYau.DifferentialForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {k : ℕ}

attribute [local instance] CalabiYau.normedAddCommGroupTangentSpace
  CalabiYau.normedSpaceTangentSpace

/-- Unbundle a smooth differential form via the inverse tangent-model identification. -/
noncomputable def toFormField (β : CalabiYau.DifferentialForm 𝓘(ℝ, E) M k) :
    FormField E M k := fun x => (β x).compContinuousLinearMap
      (CalabiYau.tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm.toContinuousLinearMap

@[simp] theorem toFormField_apply (β : CalabiYau.DifferentialForm 𝓘(ℝ, E) M k)
    (x : M) (v : Fin k → E) :
    β.toFormField x v = β x (fun i =>
      (CalabiYau.tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm (v i)) := rfl

@[simp] theorem tangentSection_toFormField
    (β : CalabiYau.DifferentialForm 𝓘(ℝ, E) M k) (x : M) :
    FormField.tangentSection β.toFormField x = β x := by
  ext v
  rfl

theorem toFormField_chartRep (β : CalabiYau.DifferentialForm 𝓘(ℝ, E) M k)
    (c : M) {z : E} (hz : z ∈ (extChartAt 𝓘(ℝ, E) c).target) :
    β.toFormField.chartRep c z =
      (trivializationAt (E [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) E (TangentSpace 𝓘(ℝ, E)) ℝ
          (Bundle.Trivial M ℝ)) c
        ⟨(extChartAt 𝓘(ℝ, E) c).symm z, β ((extChartAt 𝓘(ℝ, E) c).symm z)⟩).2 := by
  rw [← FormField.tangentSection_chart β.toFormField c hz, tangentSection_toFormField]

theorem isSmooth_toFormField (β : CalabiYau.DifferentialForm 𝓘(ℝ, E) M k) :
    β.toFormField.IsSmooth := by
  intro c
  exact (localRep_contDiffOn β c).congr (fun z hz => toFormField_chartRep β c hz)

@[simp] theorem toFormField_toDifferentialForm (α : FormField E M k) (hα : α.IsSmooth) :
    (α.toDifferentialForm hα).toFormField = α := by
  funext x
  ext v
  rfl

@[simp] theorem toDifferentialForm_toFormField
    (β : CalabiYau.DifferentialForm 𝓘(ℝ, E) M k) :
    β.toFormField.toDifferentialForm β.isSmooth_toFormField = β := by
  apply ContMDiffSection.ext
  intro x
  exact tangentSection_toFormField β x

@[simp] theorem toFormField_add (β γ : CalabiYau.DifferentialForm 𝓘(ℝ, E) M k) :
    (β + γ).toFormField = β.toFormField + γ.toFormField := by
  funext x
  ext v
  rfl

@[simp] theorem toFormField_smul (r : ℝ) (β : CalabiYau.DifferentialForm 𝓘(ℝ, E) M k) :
    (r • β).toFormField = r • β.toFormField := by
  funext x
  ext v
  rfl

/-- The unbundling map is real-linear. Its range consists precisely of smooth form fields. -/
noncomputable def toFormFieldLinearMap :
    CalabiYau.DifferentialForm 𝓘(ℝ, E) M k →ₗ[ℝ] FormField E M k where
  toFun := toFormField
  map_add' := toFormField_add
  map_smul' := toFormField_smul

theorem toFormField_exteriorDerivative
    (β : CalabiYau.DifferentialForm 𝓘(ℝ, E) M k) :
    (exteriorDerivative β).toFormField = β.toFormField.extDeriv := by
  funext x
  rw [← FormField.chartRep_self (exteriorDerivative β).toFormField x,
    toFormField_chartRep (exteriorDerivative β) x (mem_extChartAt_target x)]
  have hlocal := exteriorDerivative_localRepresentation β (mem_extChartAt_source x)
    (BoundarylessManifold.isInteriorPoint (I := 𝓘(ℝ, E)) (M := M) (x := x))
  rw [(extChartAt 𝓘(ℝ, E) x).left_inv (mem_extChartAt_source x), exteriorDerivative_apply]
  rw [show exteriorDerivativeAt β x = exteriorDerivativeAtInterior β x
    (BoundarylessManifold.isInteriorPoint (I := 𝓘(ℝ, E)) (M := M) (x := x)) from rfl]
  rw [hlocal]
  apply Filter.EventuallyEq.extDeriv_eq
  filter_upwards [extChartAt_target_mem_nhds (I := 𝓘(ℝ, E)) x] with z hz
  exact (toFormField_chartRep β x hz).symm

@[simp] theorem toDifferentialForm_apply (α : FormField E M k) (hα : α.IsSmooth) (x : M) :
    α.toDifferentialForm hα x = α.tangentSection x := rfl

end CalabiYau.DifferentialForm

namespace FormField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {k : ℕ}

end FormField
