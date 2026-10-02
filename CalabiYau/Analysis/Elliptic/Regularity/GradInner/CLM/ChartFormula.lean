-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/GradInner/CLM/ChartFormula.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.GradInner.CLM.Defs
public import CalabiYau.Analysis.Elliptic.Regularity.ChartBilinear.Smooth
public import CalabiYau.Analysis.Elliptic.Regularity.LaplacianDomain.Chart.VariationalData
public import CalabiYau.Analysis.Elliptic.MetricExtension
public import CalabiYau.Geometry.Riemannian.Operator.Gradient.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

@[expose] public section
open CalabiYau.Riemannian

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Topology Function
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace Matrix

namespace CalabiYau
namespace Analysis
namespace Laplacian
namespace GradInnerCLMChartFormula

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Laplacian.MetricExtension
  hiding chartTargetEuclid
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.ChartBilinearSmooth
open CalabiYau.Analysis.Laplacian.LaplacianDomainChartData
open Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

def partialDerivOnEuclid (α : M) (i : Fin (Module.finrank ℝ E)) (u : M → ℝ) :
    EuclN → ℝ := fun y =>
  CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (scalarOnE (I := I) α u) ((toEuclidean (E := E)).symm y)

end GradInnerCLMChartFormula
end Laplacian
end Analysis
end CalabiYau

end
