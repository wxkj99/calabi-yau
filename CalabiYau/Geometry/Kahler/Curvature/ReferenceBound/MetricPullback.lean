module

public import CalabiYau.Geometry.Kahler.Curvature.ReferenceBound.Basic

/-!
# Hermitian metric coefficients under a holomorphic chart change

A Kähler form is a global real two-form. Pulling its local representation from the
`x`-chart to the `y`-chart gives the Hermitian matrix congruence
`g_y = A.transpose * (g_x ∘ f) * A.map star`, where `A = D_ℂ f`.
Both charts must actually contain the represented point; no claim is made about the
arbitrary extension of a partial chart outside its source.
-/

@[expose] public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- The metric coefficient matrix in the chart at `y` is the conjugate pullback of the
coefficient matrix in the chart at `x`. The equalities hold at every point of the overlap,
so applying this lemma throughout an open overlap permits differentiating the identity. -/
theorem referenceMetricInChart_pullback (ω₀ : KahlerForm n M) (x y : M)
    (z : EuclideanSpace ℂ (Fin n))
    (hyz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).target)
    (hxz : (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).symm z ∈
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source) :
    ω₀.metricInChart y z =
      Matrix.transpose (EuclideanSpace.clmMatrix
          (fderiv ℂ (referenceChartTransition (n := n) x y) z)) *
        ω₀.metricInChart x (referenceChartTransition (n := n) x y z) *
          (EuclideanSpace.clmMatrix
            (fderiv ℂ (referenceChartTransition (n := n) x y) z)).map star := by
  let cy := extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y
  let cx := extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x
  let p := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).symm z
  have hpYReal : p ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).source := by
    exact (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).map_target hyz
  have hpY : p ∈ cy.source := by
    change p ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source
    rw [← extChartAt_real_eq]
    exact hpYReal
  have hpX : p ∈ cx.source := by
    change p ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source
    rw [← extChartAt_real_eq]
    exact hxz
  have hcoord : cy p = z := by
    change (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y) p = z
    rw [← extChartAt_real_eq]
    exact (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).right_inv hyz
  have hzTransition : z ∈ ((extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).symm ≫
      extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source := by
    rw [PartialEquiv.trans_source'', PartialEquiv.symm_symm, PartialEquiv.symm_target]
    exact ⟨p, ⟨hpY, hpX⟩, hcoord⟩
  have hfWithin : DifferentiableWithinAt ℂ
      (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x ∘
        (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).symm)
      (Set.range (𝓘(ℂ, EuclideanSpace ℂ (Fin n)))) z :=
    (contDiffWithinAt_ext_coord_change x y hzTransition).differentiableWithinAt one_ne_zero
  have hfWithinUniv : DifferentiableWithinAt ℂ
      (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x ∘
        (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).symm) Set.univ z := by
    simpa [ModelWithCorners.range_eq_univ] using hfWithin
  have hfComplex : DifferentiableAt ℂ
      (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x ∘
        (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).symm) z :=
    hfWithinUniv.differentiableAt (by simp)
  let f := referenceChartTransition (n := n) x y
  have htransition : f =
      extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x ∘
        (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).symm := by
    funext w
    change extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
        ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).symm w) =
      extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x
        ((extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).symm w)
    rw [extChartAt_real_eq x, extChartAt_real_eq y]
  have hf : DifferentiableAt ℂ f z := by
    rw [htransition]
    exact hfComplex
  have hderiv :
      fderiv ℝ
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x ∘
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).symm) z =
        (fderiv ℂ f z).restrictScalars ℝ :=
    hf.fderiv_restrictScalars ℝ
  have hrep := FormField.chartRep_eq_chartRep_comp
    (α := ω₀.toFormField) (x := y) (x' := x) hyz hxz
  rw [hderiv] at hrep
  have hpoint : f z = (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x) p := rfl
  have hOverlap : p ∈
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source ∩
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) p).source := by
    refine ⟨hpX, ?_⟩
    exact mem_extChartAt_source p
  have hpXChart : p ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source := by
    rw [← extChartAt_source (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x]
    exact hpX
  have hbase : (ω₀.toFormField.chartRep x (f z)).IsOneOne := by
    rw [hpoint]
    dsimp [FormField.chartRep]
    rw [(chartAt (EuclideanSpace ℂ (Fin n)) x).left_inv hpXChart]
    change ((ω₀.toFormField p).compContinuousLinearMap
      (tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x p p)).IsOneOne
    rw [tangentCoordChange_real_eq hOverlap]
    exact (ω₀.isOneOne p).compContinuousLinearMap
      (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x p p)
  rw [← hpoint] at hrep
  have hmatrix := congrArg ContinuousAlternatingMap.coeffMatrix hrep
  rw [hbase.coeffMatrix_compContinuousLinearMap] at hmatrix
  simpa [f, metricInChart] using hmatrix

end KahlerForm
