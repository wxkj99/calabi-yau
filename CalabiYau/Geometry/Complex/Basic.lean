module

public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Complex manifolds as real manifolds

A compact complex manifold of complex dimension `n` is modelled in Mathlib as
`[ChartedSpace (EuclideanSpace ℂ (Fin n)) M] [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]`:
the transition maps are complex analytic. All real-analytic notions of this project (smooth real
functions, real differential forms, measures, Laplacians, the extracted Riemannian geometry) use
the **same charts** with the real model `𝓘(ℝ, E)`. This file provides the bridge.

## Declarations

* `IsManifold.real_of_complex`: a complex manifold is a smooth real manifold for `𝓘(ℝ, E)`
  (instance).
* `extChartAt_real_eq`: the extended charts of the two models coincide.
* `tangentCoordChange_real_eq`: the real tangent coordinate change is the restriction of scalars
  of the complex one; in particular it is `ℂ`-linear.

## Conventions

* `TangentSpace 𝓘(ℝ, E) x` is `E` (Mathlib identifies it with `E` via `chartAt E x`). Since the
  coordinate changes are `ℂ`-linear, multiplication by `Complex.I` on `E` is a well-defined
  endomorphism `J` of every tangent space: this is the (integrable) almost complex structure.
  We never introduce `J` as separate data.
* A smooth real function is `ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f`.
-/

@[expose] public section

open scoped Manifold ContDiff
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- A complex (analytic) manifold is a smooth real manifold, with the same charts. -/
instance (priority := 100) IsManifold.real_of_complex [IsManifold 𝓘(ℂ, E) ω M] :
    IsManifold 𝓘(ℝ, E) ∞ M :=
  isManifold_of_contDiffOn 𝓘(ℝ, E) ∞ M fun e e' he he' ↦ by
    have h := HasGroupoid.compatible (G := contDiffGroupoid ω 𝓘(ℂ, E)) he he'
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at h
    exact (h.1.of_le le_top).restrict_scalars ℝ

section Charts

variable [IsManifold 𝓘(ℂ, E) ω M]

omit [IsManifold 𝓘(ℂ, E) ω M] in
/-- The extended charts of the complex and of the real model coincide. -/
theorem extChartAt_real_eq (x : M) : extChartAt 𝓘(ℝ, E) x = extChartAt 𝓘(ℂ, E) x := rfl

/-- The real tangent coordinate change is the restriction of scalars of the complex one, on the
common domain of the two charts. -/
theorem tangentCoordChange_real_eq {x y z : M}
    (hz : z ∈ (extChartAt 𝓘(ℝ, E) x).source ∩ (extChartAt 𝓘(ℝ, E) y).source) :
    tangentCoordChange 𝓘(ℝ, E) x y z =
      (tangentCoordChange 𝓘(ℂ, E) x y z).restrictScalars ℝ := by
  rw [tangentCoordChange_def, tangentCoordChange_def, extChartAt_real_eq]
  simp only [extChartAt_real_eq]
  have hz' : extChartAt 𝓘(ℂ, E) x z ∈
      ((extChartAt 𝓘(ℂ, E) x).symm ≫ extChartAt 𝓘(ℂ, E) y).source := by
    rw [PartialEquiv.trans_source'', PartialEquiv.symm_symm, PartialEquiv.symm_target]
    exact mem_image_of_mem _ hz
  have hdiff : DifferentiableWithinAt ℂ
      (extChartAt 𝓘(ℂ, E) y ∘ (extChartAt 𝓘(ℂ, E) x).symm)
      (Set.range (𝓘(ℂ, E))) (extChartAt 𝓘(ℂ, E) x z) :=
    (contDiffWithinAt_ext_coord_change y x hz').differentiableWithinAt one_ne_zero
  have hdiff' : DifferentiableWithinAt ℂ
      (extChartAt 𝓘(ℂ, E) y ∘ (extChartAt 𝓘(ℂ, E) x).symm) Set.univ
      (extChartAt 𝓘(ℂ, E) x z) := by
    simpa [ModelWithCorners.range_eq_univ] using hdiff
  rw [ModelWithCorners.range_eq_univ, ModelWithCorners.range_eq_univ]
  rw [fderivWithin_univ, fderivWithin_univ]
  have hdiffAt : DifferentiableAt ℂ
      (extChartAt 𝓘(ℂ, E) y ∘ (extChartAt 𝓘(ℂ, E) x).symm)
      (extChartAt 𝓘(ℂ, E) x z) := hdiff'.differentiableAt (by simp)
  simpa only [fderivWithin_univ] using hdiffAt.fderiv_restrictScalars ℝ

/-- The real tangent coordinate change commutes with the complex structure `J = Complex.I • ·`. -/
theorem tangentCoordChange_I_smul {x y z : M}
    (hz : z ∈ (extChartAt 𝓘(ℝ, E) x).source ∩ (extChartAt 𝓘(ℝ, E) y).source) (v : E) :
    tangentCoordChange 𝓘(ℝ, E) x y z (Complex.I • v) =
      Complex.I • tangentCoordChange 𝓘(ℝ, E) x y z v := by
  rw [tangentCoordChange_real_eq hz]
  exact (tangentCoordChange 𝓘(ℂ, E) x y z).map_smul Complex.I v

/-- The coordinate change `extChartAt y ∘ (extChartAt x).symm` is holomorphic on the image of the
overlap of the two chart domains. -/
theorem differentiableOn_extChartAt_comp_symm (x y : M) :
    DifferentiableOn ℂ (extChartAt 𝓘(ℂ, E) y ∘ (extChartAt 𝓘(ℂ, E) x).symm)
      (extChartAt 𝓘(ℂ, E) x '' ((extChartAt 𝓘(ℂ, E) x).source ∩
        (extChartAt 𝓘(ℂ, E) y).source)) := by
  convert (contDiffOn_ext_coord_change (I := 𝓘(ℂ, E)) y x).differentiableOn one_ne_zero using 1
  rw [PartialEquiv.trans_source'']
  simp only [PartialEquiv.symm_symm, PartialEquiv.symm_target]

end Charts
