-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Topology/Manifold/InteriorBoundary.lean
-- Locally modified.
module
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

@[expose] public section

open Manifold Set
open scoped Manifold Topology

namespace ModelWithCorners

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

theorem dense_interior : Dense (I.interior M) := by
  rw [dense_iff_inter_open]
  intro V hVopen hVne
  obtain ⟨x, hxV⟩ := hVne
  have hxsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hxext : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source]; exact hxsrc
  let s : Set M := V ∩ (chartAt H x).source
  have hs_open : IsOpen s := hVopen.inter (chartAt H x).open_source
  have hxs : x ∈ s := ⟨hxV, hxsrc⟩
  have h_img_nhdW : (extChartAt I x) '' s ∈ 𝓝[range I] (extChartAt I x x) := by
    rw [← map_extChartAt_nhds (x := x)]
    exact Filter.image_mem_map (hs_open.mem_nhds hxs)
  obtain ⟨U, hU_open, hU_mem, hU_sub⟩ := mem_nhdsWithin.mp h_img_nhdW
  have hxImg_inRange : extChartAt I x x ∈ range I :=
    extChartAt_target_subset_range x ((extChartAt I x).map_source hxext)
  have hxImg_inClosure : extChartAt I x x ∈ closure (interior (range I)) := by
    rw [← I.range_eq_closure_interior]; exact hxImg_inRange
  obtain ⟨p, hp_U, hp_int⟩ := mem_closure_iff.mp hxImg_inClosure U hU_open hU_mem
  obtain ⟨y, hys, hyEq⟩ := hU_sub ⟨hp_U, interior_subset hp_int⟩
  refine ⟨y, hys.1, ?_⟩
  have hp_inExtTarget : ((chartAt H x).extend I) y ∈
      interior ((chartAt H x).extend I).target := by
    have hI_inInterior : I ((chartAt H x) y) ∈ interior (range I) := by
      change extChartAt I x y ∈ interior (range I)
      rw [hyEq]; exact hp_int
    exact (chartAt H x).mem_interior_extend_target
      ((chartAt H x).map_source hys.2) hI_inInterior
  exact (I.isInteriorPoint_iff_of_mem_atlas (n := 1) one_ne_zero
    (chart_mem_atlas H x) hys.2).mpr hp_inExtTarget

end ModelWithCorners
