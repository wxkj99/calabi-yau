module

public import CalabiYau.Geometry.Kahler.Laplacian

/-!
# Restriction of Kähler data to open submanifolds

The open subtype carries Mathlib's induced atlas. The underlying form field is exactly the
pointwise restriction of the original field. Smoothness and exterior-derivative naturality form
the restriction results show that actual exact primitives remain exact and the open set inherits
the actual restricted Kähler form, including smoothness, positivity and closedness.

Hausdorffness is stated explicitly for the form/Kähler restriction cluster, retaining the source
book's manifold convention. Arbitrary open subsets need not be compact or connected. The scalar
Hessian identity is a germ-local chart identity and requires neither those global assumptions nor
smoothness of the function.

This core does not assert Poisson solvability. In the compact-component application the source
trace has intrinsic mean zero with respect to the restricted Kähler form's own volume; no ambient
volume comparison is used. Neither a global-mean-zero solver on a disconnected manifold nor an
unconditional `∂∂̄` lemma is assumed or proved here.

Source: Wells, *Differential Analysis on Complex Manifolds*, I §3, open restriction/pullback of
forms and exterior-derivative naturality; Mathlib's induced open-submanifold atlas and germ-local
calculus. The consuming scalar component argument is Székelyhidi, Lemma 1.14.
-/

@[expose] public section

open scoped Manifold ContDiff Topology
open ContinuousAlternatingMap Filter

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]

/-- Pointwise restriction to an open submanifold with its induced atlas. -/
def FormField.restrictOpen {k : ℕ}
    (α : FormField (EuclideanSpace ℂ (Fin n)) M k) (U : TopologicalSpace.Opens M) :
    FormField (EuclideanSpace ℂ (Fin n)) U k := fun x => α (x : M)

private theorem open_chart_source (U : TopologicalSpace.Opens M) (x : U) :
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source =
      (Subtype.val : U → M) ⁻¹'
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (x : M)).source := by
  simp only [extChartAt_source, TopologicalSpace.Opens.chartAt_eq,
    OpenPartialHomeomorph.subtypeRestr_source]

private theorem open_chart_symm (U : TopologicalSpace.Opens M) (x : U)
    {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z : M) =
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (x : M)).symm z := by
  let eU := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let eM := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (x : M)
  have hyM : ((eU.symm z : U) : M) ∈ eM.source := by
    have hy := eU.map_target hz
    rw [open_chart_source U x] at hy
    exact hy
  have heval : eM ((eU.symm z : U) : M) = z := eU.right_inv hz
  calc
    ((eU.symm z : U) : M) = eM.symm (eM ((eU.symm z : U) : M)) :=
      (eM.left_inv hyM).symm
    _ = eM.symm z := by rw [heval]

private theorem open_chart_target_subset (U : TopologicalSpace.Opens M) (x : U) :
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target ⊆
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (x : M)).target := by
  intro z hz
  let eU := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let eM := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (x : M)
  have hyM : ((eU.symm z : U) : M) ∈ eM.source := by
    have hy := eU.map_target hz
    rw [open_chart_source U x] at hy
    exact hy
  have heval : eM ((eU.symm z : U) : M) = z := eU.right_inv hz
  rw [← heval]
  exact eM.map_source hyM

variable [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M]

omit [T2Space M] in
private theorem open_tangentCoordChange (U : TopologicalSpace.Opens M)
    (x y z : U) (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source) :
    tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y z =
      tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (x : M) (y : M) (z : M) := by
  let eUx := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let eUy := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y
  let eMx := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (x : M)
  let eMy := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (y : M)
  have hzT : eUx z ∈ eUx.target := eUx.map_source hz
  have hEq : eUy ∘ eUx.symm =ᶠ[𝓝 (eUx z)] eMy ∘ eMx.symm := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds hzT] with w hw
    change eMy ((eUx.symm w : U) : M) = eMy (eMx.symm w)
    rw [open_chart_symm U x hw]
  simp only [tangentCoordChange_def, modelWithCornersSelf_coe, Set.range_id,
    fderivWithin_univ]
  exact hEq.fderiv_eq

omit [T2Space M] in
private theorem open_chartRep {k : ℕ} (U : TopologicalSpace.Opens M)
    (α : FormField (EuclideanSpace ℂ (Fin n)) M k) (x : U)
    {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    (α.restrictOpen U).chartRep x z = α.chartRep (x : M) z := by
  let eU := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let eM := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (x : M)
  change (α ((eU.symm z : U) : M)).compContinuousLinearMap
      (tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x (eU.symm z) (eU.symm z)) =
    (α (eM.symm z)).compContinuousLinearMap
      (tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (x : M) (eM.symm z) (eM.symm z))
  rw [open_tangentCoordChange U x (eU.symm z) (eU.symm z) (eU.map_target hz)]
  rw [open_chart_symm U x hz]

omit [T2Space M] in
/-- Smooth form restriction and exterior-derivative naturality for the induced open atlas. -/
theorem FormField.isSmooth_extDeriv_restrictOpen {k : ℕ}
    (α : FormField (EuclideanSpace ℂ (Fin n)) M k) (hα : α.IsSmooth)
    (U : TopologicalSpace.Opens M) :
    (α.restrictOpen U).IsSmooth ∧
      α.extDeriv.restrictOpen U = (α.restrictOpen U).extDeriv := by
  constructor
  · intro x
    exact ((hα (x : M)).mono (open_chart_target_subset U x)).congr
      (fun z hz => open_chartRep U α x hz)
  · funext x
    change _root_.extDeriv (α.chartRep (x : M))
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (x : M) (x : M)) =
      _root_.extDeriv ((α.restrictOpen U).chartRep x)
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x)
    have hcenter : extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x =
        extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (x : M) (x : M) := rfl
    rw [← hcenter]
    apply Filter.EventuallyEq.extDeriv_eq
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds
      (mem_extChartAt_target x)] with z hz
    exact (open_chartRep U α x hz).symm

omit [T2Space M] in
/-- An actual smooth exact primitive restricts to an exact primitive. -/
theorem FormField.isExact_restrictOpen {k : ℕ}
    (α : FormField (EuclideanSpace ℂ (Fin n)) M (k + 1)) (hα : α.IsExact)
    (U : TopologicalSpace.Opens M) : (α.restrictOpen U).IsExact := by
  obtain ⟨β, hβ, hβα⟩ := hα
  obtain ⟨hβU, hderiv⟩ := β.isSmooth_extDeriv_restrictOpen hβ U
  refine ⟨β.restrictOpen U, hβU, ?_⟩
  rw [← hderiv, hβα]

/-- The Kähler form on the actual open submanifold, with the original pointwise field. -/
noncomputable def KahlerForm.restrictOpen (ω₀ : KahlerForm n M)
    (U : TopologicalSpace.Opens M) : KahlerForm n U where
  toFormField := ω₀.toFormField.restrictOpen U
  isSmooth' := (ω₀.toFormField.isSmooth_extDeriv_restrictOpen ω₀.isSmooth U).1
  isPositive' := fun x => ω₀.isPositive (x : M)
  isClosed' := by
    have hderiv := (ω₀.toFormField.isSmooth_extDeriv_restrictOpen ω₀.isSmooth U).2
    change (ω₀.toFormField.restrictOpen U).extDeriv = 0
    rw [← hderiv]
    have hclosed : ω₀.toFormField.extDeriv = 0 := ω₀.isClosed
    rw [hclosed]
    rfl

omit [T2Space M] in
/-- Restriction preserves the pointwise Kähler form exactly. -/
@[simp]
theorem KahlerForm.restrictOpen_apply (ω₀ : KahlerForm n M)
    (U : TopologicalSpace.Opens M) (x : U) : ω₀.restrictOpen U x = ω₀ (x : M) := rfl

