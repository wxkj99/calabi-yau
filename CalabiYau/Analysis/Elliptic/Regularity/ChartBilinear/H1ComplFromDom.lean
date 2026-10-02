-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/ChartBilinear/H1ComplFromDom.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.ChartBilinear.H1Compl
public import CalabiYau.Analysis.Elliptic.Regularity.ChartBilinear.Smooth
public import CalabiYau.Analysis.Elliptic.Operator.VariationalLaplacian
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace CalabiYau
namespace Analysis
namespace Laplacian
namespace ChartBilinearH1ComplFromDom

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Laplacian.MetricExtension
open CalabiYau.Analysis.Laplacian.ChartLocalLaplacian
open CalabiYau.Laplacian.ChartMeasureEquiv
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.ChartBilinearSmooth
open Sobolev.NirenbergEuclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_smooth_approx_seq
    (g : SmoothRiemannianMetric I M) (u_h : H1Compl g) :
    ∃ v : ℕ → SmoothScalar g,
      Tendsto (fun n => smoothToH1Compl (I := I) (M := M) g (v n)) atTop (𝓝 u_h) := by
  classical
  have h_dense :
      u_h ∈ closure (Set.range (smoothToH1Compl (I := I) (M := M) g)) := by
    rw [(denseRange_smoothToH1Compl (I := I) (M := M) g).closure_eq]
    exact Set.mem_univ _
  obtain ⟨s, hs_mem, hs_tendsto⟩ := mem_closure_iff_seq_limit.mp h_dense
  refine ⟨fun n => Classical.choose (hs_mem n), ?_⟩
  have h_eq : (fun n => smoothToH1Compl (I := I) (M := M) g
        (Classical.choose (hs_mem n))) = s := by
    funext n
    exact Classical.choose_spec (hs_mem n)
  rw [h_eq]
  exact hs_tendsto

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_smooth_approx_seq_lp
    (g : SmoothRiemannianMetric I M)
    (f_h : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ∃ v : ℕ → SmoothScalar g,
      Tendsto (fun n => smoothToLp (I := I) (M := M) g (v n)) atTop (𝓝 f_h) := by
  classical
  have h_dense :
      f_h ∈ closure (Set.range (smoothToLp (I := I) (M := M) g)) := by
    rw [(denseRange_smoothToLp (I := I) (M := M) g).closure_eq]
    exact Set.mem_univ _
  obtain ⟨s, hs_mem, hs_tendsto⟩ := mem_closure_iff_seq_limit.mp h_dense
  refine ⟨fun n => Classical.choose (hs_mem n), ?_⟩
  have h_eq : (fun n => smoothToLp (I := I) (M := M) g
        (Classical.choose (hs_mem n))) = s := by
    funext n
    exact Classical.choose_spec (hs_mem n)
  rw [h_eq]
  exact hs_tendsto

end ChartBilinearH1ComplFromDom
end Laplacian
end Analysis
end CalabiYau
