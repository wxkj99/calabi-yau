-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/H1Compl/GradientChartBridge.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.ChartBilinear.H1ComplFromDom
public import CalabiYau.Analysis.Elliptic.Regularity.H1Compl.ChartLp
public import CalabiYau.Analysis.Sobolev.Chart.Defs
public import CalabiYau.Geometry.Riemannian.Operator.Gradient.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

@[expose] public section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace CalabiYau
namespace Analysis
namespace Laplacian
namespace H1ComplGradientChartBridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Laplacian.MetricExtension
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.ChartBilinearH1ComplFromDom
open CalabiYau.Analysis.Laplacian.H1ComplToLpChartBridge

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

noncomputable def chartPushedPartial
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E)) (v : SmoothScalar g) : EuclN → ℝ :=
  fun y =>
    (fderiv ℝ (Sobolev.Chart.chartPushed (I := I) (M := M)
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α v.toFun) y)
      (EuclideanSpace.single j 1)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma chartPushedPartial_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E)) (v : SmoothScalar g) (y : EuclN) :
    chartPushedPartial (I := I) (M := M) g α j v y =
      (fderiv ℝ (Sobolev.Chart.chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α v.toFun) y)
        (EuclideanSpace.single j 1) := rfl

noncomputable def chartPushedPartialLp
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E)) (v : SmoothScalar g)
    (h : MemLp (chartPushedPartial (I := I) (M := M) g α j v) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α))) :
    Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
      (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)) :=
  h.toLp _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma norm_chartPushedPartialLp
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E)) (v : SmoothScalar g)
    (h : MemLp (chartPushedPartial (I := I) (M := M) g α j v) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α))) :
    ‖chartPushedPartialLp (I := I) (M := M) g α j v h‖ =
      ENNReal.toReal (eLpNorm (chartPushedPartial (I := I) (M := M) g α j v) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid (I := I) (M := M)
            α))) := by
  unfold chartPushedPartialLp
  exact MeasureTheory.Lp.norm_toLp _ _

end H1ComplGradientChartBridge
end Laplacian
end Analysis
end CalabiYau

end
