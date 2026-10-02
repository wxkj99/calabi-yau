module

public import CalabiYau.Geometry.Kahler.Curvature.ReferenceBound.Basic

/-!
# Open domains for centered holomorphic chart changes

The transition is considered only on a genuine open chart overlap. In particular, the
inverse of the `y`-chart must land in the source of the `x`-chart. Merely requiring the
image of the globally extended transition function to lie in the `x`-target would not
suffice to identify its value with the manifold coordinate change off the chart source.
-/

@[expose] public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- Around the center of the `y`-chart there is an open overlap with the `x`-chart on which
the coordinate transition is smooth and holomorphic. The inverse-chart source condition
prevents using the arbitrary extension of the partial chart outside its actual domain. -/
theorem exists_reference_chart_domain (x y : M)
    (hy : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source) :
    ∃ U : Set (EuclideanSpace ℂ (Fin n)),
      IsOpen U ∧
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y) ∈ U ∧
      U ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).target ∧
      (∀ z ∈ U, (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).symm z ∈
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source) ∧
      referenceChartTransition (n := n) x y '' U ⊆
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target ∧
      ContDiffOn ℝ ∞ (referenceChartTransition (n := n) x y) U ∧
      DifferentiableOn ℂ (referenceChartTransition (n := n) x y) U := by
  let Cx := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let Cy := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y
  let U : Set (EuclideanSpace ℂ (Fin n)) := Cy.target ∩ Cy.symm ⁻¹' Cx.source
  have hUopen : IsOpen U := by
    dsimp [U]
    exact (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
      (n := ∞) y).continuousOn.isOpen_inter_preimage
      (isOpen_extChartAt_target (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) y)
      (isOpen_extChartAt_source (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x)
  have hcenter : Cy y ∈ U := by
    dsimp [U]
    constructor
    · exact Cy.map_source (mem_extChartAt_source y)
    · simp only [Set.mem_preimage]
      rw [PartialEquiv.left_inv]
      · exact hy
      · exact mem_extChartAt_source y
  have hUtarget : U ⊆ Cy.target := Set.inter_subset_left
  have hUsource : ∀ z ∈ U, Cy.symm z ∈ Cx.source := fun z hz => hz.2
  have hImage : referenceChartTransition (n := n) x y '' U ⊆ Cx.target := by
    rintro w ⟨z, hz, rfl⟩
    change Cx (Cy.symm z) ∈ Cx.target
    exact Cx.map_source (hUsource z hz)
  have hsubset : U ⊆ Cy '' (Cy.source ∩ Cx.source) := by
    intro z hz
    refine ⟨Cy.symm z, ⟨?_, hUsource z hz⟩, ?_⟩
    · exact Cy.map_target hz.1
    · exact PartialEquiv.right_inv Cy hz.1
  have hcontReal : ContDiffOn ℝ ∞
      (referenceChartTransition (n := n) x y) U := by
    have h := contDiffOn_ext_coord_change
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (n := ∞) x y
    have h' : ContDiffOn ℝ ∞
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x ∘
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).symm)
        (Cy '' (Cy.source ∩ Cx.source)) := by
      convert! h using 1
      rw [PartialEquiv.trans_source'']
      simp only [PartialEquiv.symm_symm, PartialEquiv.symm_target]
      simp only [Cy, Cx]
    have h'' := h'.mono hsubset
    simpa [referenceChartTransition, Cx, Cy] using h''
  have hdiff : DifferentiableOn ℂ
      (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x ∘
        (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).symm) U := by
    have h := differentiableOn_extChartAt_comp_symm
      (E := EuclideanSpace ℂ (Fin n)) (M := M) y x
    exact h.mono hsubset
  have hdiff' : DifferentiableOn ℂ
      (referenceChartTransition (n := n) x y) U := by
    simpa [referenceChartTransition, Cx, Cy, extChartAt_real_eq] using hdiff
  refine ⟨U, hUopen, hcenter, hUtarget, hUsource, ?_, hcontReal, hdiff'⟩
  simpa [Cx] using hImage

end KahlerForm
