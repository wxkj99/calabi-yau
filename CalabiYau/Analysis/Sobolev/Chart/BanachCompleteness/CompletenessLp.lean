-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Chart/BanachCompleteness/CompletenessLp.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Chart.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Group.NullSubmodule
public import Mathlib.Analysis.Normed.Group.Uniform
public import CalabiYau.Analysis.Sobolev.Euclidean.Completeness.IteratedSobolevBanach
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Topology.UniformSpace.UniformEmbedding
public import CalabiYau.Analysis.Sobolev.Chart.RiemannianMeasureComparison
public import CalabiYau.Analysis.Sobolev.Manifold.RiemannianRellich
public import CalabiYau.Analysis.Sobolev.Manifold.Embedding.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

@[expose] public section

-- Private declarations used in public declarations require the compatibility option below.

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold
open scoped Manifold ContDiff ENNReal NNReal

namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [IsManifold I ∞ M] in
lemma chartPushed_eq_chartPushedRaw_pou_mul_on_target
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushed (I := I) (M := M) ρ α u y =
      chartPushedRaw I α (fun x => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) y := by
  classical
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
    (fun x => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) hy]
  unfold chartPushed
  rfl

end Chart
end Sobolev
