-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/H1Compl/Defs.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.SmoothScalar.PreHOne
public import Mathlib.Topology.UniformSpace.Completion
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.InnerProductSpace.Completion

@[expose] public section

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace CalabiYau
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

abbrev H1Compl (g : SmoothRiemannianMetric I M) : Type _ :=
  UniformSpace.Completion (SmoothScalar g)

noncomputable def smoothToH1Compl (g : SmoothRiemannianMetric I M) :
    SmoothScalar g →L[ℝ] H1Compl g :=
  UniformSpace.Completion.toComplL

@[simp] lemma smoothToH1Compl_apply (g : SmoothRiemannianMetric I M)
    (f : SmoothScalar g) :
    smoothToH1Compl (I := I) (M := M) g f = (f : H1Compl g) :=
  rfl

end Laplacian
end Analysis
end CalabiYau

end
