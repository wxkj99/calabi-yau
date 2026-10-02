-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Geometry/Metric/Basic.lean
-- Locally modified.
module
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent

@[expose] public section

namespace CalabiYau

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]

abbrev SmoothRiemannianMetric
    (I : ModelWithCorners Real E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] : Type _ :=
  Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M -> Type _)

@[ext]
theorem SmoothRiemannianMetric.ext_inner
    {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {g h : SmoothRiemannianMetric I M}
    (hinner : ∀ (x : M) (v w : TangentSpace I x),
      g.inner x v w = h.inner x v w) :
    g = h := by
  obtain ⟨gi, gs, gp, gb, gc⟩ := g
  obtain ⟨hi, hs, hp, hb, hc⟩ := h
  have hfield : gi = hi :=
    funext fun x =>
      ContinuousLinearMap.ext fun v =>
        ContinuousLinearMap.ext fun w => hinner x v w
  subst hfield
  rfl

theorem metric_inner_self_nonneg
    {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    0 ≤ g.inner x v v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (g.pos x v hv).le

end CalabiYau
