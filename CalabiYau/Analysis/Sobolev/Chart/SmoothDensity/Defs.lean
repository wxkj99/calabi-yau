-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Chart/SmoothDensity/Defs.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Chart.Defs
public import CalabiYau.Analysis.Sobolev.Chart.AtlasNorm.Atlas
public import CalabiYau.Analysis.Sobolev.Euclidean.Density
public import CalabiYau.Analysis.Sobolev.Euclidean.Multiplication.Multiply
public import CalabiYau.Geometry.Riemannian.Volume.Chart.MeasureComparison
public import CalabiYau.Analysis.Sobolev.Chart.BanachCompleteness.CompletenessLp
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist

@[expose] public section

-- Private declarations used in public declarations require the compatibility option below.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
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

variable (I) in
def chartPullback (α : M)
    (ψ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) : M → ℝ := by
  classical
  exact fun x =>
    if x ∈ (chartAt H α).source then
      ψ (toEuclidean (extChartAt I α x))
    else 0

omit [IsManifold I ∞ M] in
lemma chartPullback_apply_of_mem (α : M)
    (ψ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    {x : M} (hx : x ∈ (chartAt H α).source) :
    chartPullback I α ψ x = ψ (toEuclidean (extChartAt I α x)) := by
  classical
  unfold chartPullback
  simp [hx]

omit [IsManifold I ∞ M] in
lemma chartPullback_apply_of_notMem (α : M)
    (ψ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    {x : M} (hx : x ∉ (chartAt H α).source) :
    chartPullback I α ψ x = 0 := by
  classical
  unfold chartPullback
  simp [hx]

end Chart
end Sobolev
