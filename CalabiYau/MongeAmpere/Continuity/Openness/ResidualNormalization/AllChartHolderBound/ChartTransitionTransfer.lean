module

public import CalabiYau.MongeAmpere.Continuity.Openness.HolderSpaces
public import CalabiYau.MongeAmpere.Continuity.Openness.ResidualNormalization.AllChartHolderBound.HolderComposition
public import CalabiYau.MongeAmpere.Continuity.Openness.ResidualNormalization.AllChartHolderBound.CompactPatching

/-!
# Transfer finite-cover Hölder bounds to arbitrary charts

A bound on one finite compact chart cover is not yet the atlas-free `HolderBoundedInCharts`
conclusion.  Use compactness and smooth coordinate changes to transfer the full C²,α bound to every
compact subset of every chart.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology

namespace KahlerForm

variable {α : ℝ≥0}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

/-- A globally C² function with a uniform `C^{2,α}` bound on each piece of one finite compact chart
cover is bounded in `C^{2,α}` on every compact subset of every chart. -/
theorem holderBoundedInCharts_of_fixedCoverBound (cover : CompactChartCover E M)
    (f : M → ℝ) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) 2 f)
    (hα : α ≤ 1)
    (hfixed : HolderBoundedOnFiniteChartCover cover 2 α {f}) :
    HolderBoundedInCharts E 2 α {f} := by
  classical
  intro x K hK hKt
  let e := extChartAt 𝓘(ℝ, E) x
  let localData (a : K) :=
    exists_compact_chartTransition_holderBoundOn_neighborhood cover f hf hα hfixed x a.1
      (hKt a.2)
  let W (a : K) : Set E := Classical.choose (localData a)
  have hW (a : K) : IsCompact (W a) ∧ (a : E) ∈ interior (W a) ∧
      W a ⊆ e.target ∧ ∃ C : ℝ≥0,
        HolderBoundOn 2 α C (W a) (f ∘ e.symm) := by
    simpa [W, localData, e] using Classical.choose_spec (localData a)
  have hUopen (a : K) : IsOpen (interior (W a)) := isOpen_interior
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun a : K => interior (W a)) hUopen (by
    intro z hz
    exact Set.mem_iUnion.2 ⟨⟨z, hz⟩, (hW ⟨z, hz⟩).2.1⟩)
  let ι := {a : K // a ∈ t}
  let : Fintype ι := Fintype.ofFinite ι
  let patch (a : ι) : Set E := W a.1
  have hpatch (a : ι) : IsCompact (patch a) := (hW a.1).1
  have hcover : K ⊆ ⋃ a : ι, interior (patch a) := by
    intro z hz
    obtain ⟨a, ha, haz⟩ := Set.mem_iUnion₂.mp (ht hz)
    exact Set.mem_iUnion.2 ⟨⟨a, ha⟩, by simpa [patch] using haz⟩
  have hlocal (a : ι) : ∃ C : ℝ≥0, HolderBoundOn 2 α C (patch a) (f ∘ e.symm) :=
    (hW a.1).2.2.2
  obtain ⟨C, hC⟩ :=
    exists_holderBoundOn_of_finite_compact_patch hK patch hcover hlocal
  refine ⟨C, ?_⟩
  intro g hg
  have hgf : g = f := Set.mem_singleton_iff.mp hg
  simpa [hgf, e] using hC

end KahlerForm
