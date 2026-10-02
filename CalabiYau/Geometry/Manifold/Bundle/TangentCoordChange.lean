-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Bundle/TangentCoordChange.lean
-- Locally modified.
module
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent

@[expose] public section

noncomputable section

open Set
open scoped Topology Manifold ContDiff

namespace CalabiYau

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ∞ M]

theorem fderiv_chartChange_eq_tangentCoordChange {x₀ x : M}
    (hx : x ∈ (extChartAt IM x₀).source) (hxi : ModelWithCorners.IsInteriorPoint IM x) :
    fderiv ℝ ((extChartAt IM x₀) ∘ (extChartAt IM x).symm) ((extChartAt IM x) x) =
      tangentCoordChange IM x x₀ x := by
  have hw : HasFDerivWithinAt ((extChartAt IM x₀) ∘ (extChartAt IM x).symm)
      (tangentCoordChange IM x x₀ x) (range IM) ((extChartAt IM x) x) := by
    have hy : x ∈ (extChartAt IM x).source ∩ (extChartAt IM x₀).source :=
      ⟨by simp, hx⟩
    simpa using hasFDerivWithinAt_tangentCoordChange (I := IM) (x := x) (y := x₀) (z := x) hy
  exact (hw.hasFDerivAt (mem_interior_iff_mem_nhds.mp hxi)).fderiv

theorem fderiv_chartChange_rev_eq_tangentCoordChange {x₀ x : M}
    (hx : x ∈ (extChartAt IM x₀).source) (hxi : ModelWithCorners.IsInteriorPoint IM x) :
    fderiv ℝ ((extChartAt IM x) ∘ (extChartAt IM x₀).symm) ((extChartAt IM x₀) x) =
      tangentCoordChange IM x₀ x x := by
  have hw : HasFDerivWithinAt ((extChartAt IM x) ∘ (extChartAt IM x₀).symm)
      (tangentCoordChange IM x₀ x x) (range IM) ((extChartAt IM x₀) x) := by
    have hy : x ∈ (extChartAt IM x₀).source ∩ (extChartAt IM x).source :=
      ⟨hx, by simp⟩
    simpa using hasFDerivWithinAt_tangentCoordChange (I := IM) (x := x₀) (y := x) (z := x) hy
  have hmem : (extChartAt IM x₀) x ∈ interior (range IM) := by
    have htarget : (extChartAt IM x₀) x ∈ interior ((extChartAt IM x₀).target) :=
      (ModelWithCorners.isInteriorPoint_iff_of_mem_atlas (I := IM) (n := 1)
        (e := (chartAt HM x₀)) (hn := by norm_num)
        (he := chart_mem_atlas (H := HM) x₀)
        (hx := by simpa [extChartAt_source] using hx)).1 hxi
    exact interior_mono (by intro y hy; rw [extChartAt_target] at hy; exact hy.2) htarget
  exact (hw.hasFDerivAt (mem_interior_iff_mem_nhds.mp hmem)).fderiv

omit [IsManifold IM ∞ M] in
theorem symmL_coordChange [IsManifold IM 1 M] {p q x : M}
    (hp : x ∈ (extChartAt IM p).source) (hq : x ∈ (extChartAt IM q).source)
    (v : EM) :
    (trivializationAt EM (TangentSpace IM) q).symmL ℝ x
        (tangentCoordChange IM p q x v) =
      (trivializationAt EM (TangentSpace IM) p).symmL ℝ x v := by
  have hchange :
      (trivializationAt EM (TangentSpace IM) q).continuousLinearMapAt ℝ x ∘L
          (trivializationAt EM (TangentSpace IM) p).symmL ℝ x =
        tangentCoordChange IM p q x := by
    rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (by simpa
      [extChartAt_source] using hq),
      TangentBundle.symmL_trivializationAt_eq_core (by simpa [extChartAt_source] using hp)]
    apply ContinuousLinearMap.ext
    intro w
    have hx : x ∈ (extChartAt IM p).source ∩ (extChartAt IM x).source ∩
        (extChartAt IM q).source := ⟨⟨hp, by simp⟩, hq⟩
    change tangentCoordChange IM x q x
        (tangentCoordChange IM p x x w) = tangentCoordChange IM p q x w
    exact tangentCoordChange_comp (w := p) (x := x) (y := q) (z := x) hx
  rw [← hchange]
  change (trivializationAt EM (TangentSpace IM) q).symmL ℝ x
      ((trivializationAt EM (TangentSpace IM) q).continuousLinearMapAt ℝ x
        ((trivializationAt EM (TangentSpace IM) p).symmL ℝ x v)) = _
  exact Bundle.Trivialization.symmL_continuousLinearMapAt (R := ℝ)
    (trivializationAt EM (TangentSpace IM) q)
    (by simpa [extChartAt_source] using hq)
    ((trivializationAt EM (TangentSpace IM) p).symmL ℝ x v)

end CalabiYau

end
