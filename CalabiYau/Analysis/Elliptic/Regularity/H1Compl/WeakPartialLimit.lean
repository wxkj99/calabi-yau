-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/H1Compl/WeakPartialLimit.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.H1Compl.GradientLipschitzBound
public import CalabiYau.Analysis.Elliptic.Regularity.ChartBilinear.H1ComplFromDom
public import CalabiYau.Analysis.Elliptic.Regularity.LaplacianDomain.L2
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

@[expose] public section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace CalabiYau
namespace Analysis
namespace Laplacian
namespace H1ComplWeakPartialLimit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Laplacian.MetricExtension
  hiding chartTargetEuclid
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.ChartBilinearH1ComplFromDom
open CalabiYau.Analysis.Laplacian.H1ComplGradientChartBridge
open CalabiYau.Analysis.Laplacian.H1ComplGradientLipschitz
open CalabiYau.Analysis.Laplacian.H1ComplGradientLipschitzBound
open CalabiYau.Analysis.Laplacian.H1ComplToLpChartBridge
open Sobolev.Chart

variable [NeZero (Module.finrank ℝ E)] in
private local instance : MeasurableSpace E := borel E
variable [NeZero (Module.finrank ℝ E)] in
private local instance : BorelSpace E := ⟨rfl⟩
variable [NeZero (Module.finrank ℝ E)] in
private local instance : MeasurableSpace M := borel M
variable [NeZero (Module.finrank ℝ E)] in
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

variable [NeZero (Module.finrank ℝ E)] in
structure ChartPushedPartialLipschitz
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E)) where
  C : ℝ
  C_nonneg : 0 ≤ C
  bound : ∀ v : SmoothScalar g,
    ‖chartPushedPartialLpLin (I := I) (M := M) g α j v‖ ≤ C * ‖v‖

noncomputable def chartPushedPartialCLM
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedPartialLipschitz (I := I) (M := M) g α j) :
    SmoothScalar g →L[ℝ]
      Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
  (chartPushedPartialLpLin (I := I) (M := M) g α j).mkContinuous hLip.C
    hLip.bound

@[simp] lemma chartPushedPartialCLM_apply
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedPartialLipschitz (I := I) (M := M) g α j)
    (v : SmoothScalar g) :
    chartPushedPartialCLM (I := I) (M := M) g α j hLip v =
      chartPushedPartialLpLin (I := I) (M := M) g α j v := rfl

private lemma denseRange_smoothToH1Compl_local
    (g : SmoothRiemannianMetric I M) :
    DenseRange (smoothToH1Compl (I := I) (M := M) g) := by
  unfold smoothToH1Compl
  rw [show (UniformSpace.Completion.toComplL : SmoothScalar g → H1Compl g) =
      ((↑) : SmoothScalar g → UniformSpace.Completion (SmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

private lemma isUniformInducing_smoothToH1Compl_local
    (g : SmoothRiemannianMetric I M) :
    IsUniformInducing (smoothToH1Compl (I := I) (M := M) g) := by
  unfold smoothToH1Compl
  rw [show (UniformSpace.Completion.toComplL : SmoothScalar g → H1Compl g) =
      ((↑) : SmoothScalar g → UniformSpace.Completion (SmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.isUniformInducing_coe (SmoothScalar g)

noncomputable def partialCLM
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedPartialLipschitz (I := I) (M := M) g α j) :
    H1Compl g →L[ℝ]
      Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
  ContinuousLinearMap.extend
    (chartPushedPartialCLM (I := I) (M := M) g α j hLip)
    (smoothToH1Compl (I := I) (M := M) g)

lemma partialCLM_smoothToH1Compl
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedPartialLipschitz (I := I) (M := M) g α j)
    (v : SmoothScalar g) :
    partialCLM (I := I) (M := M) g α j hLip
        (smoothToH1Compl (I := I) (M := M) g v) =
      chartPushedPartialCLM (I := I) (M := M) g α j hLip v := by
  unfold partialCLM
  exact ContinuousLinearMap.extend_eq
    (chartPushedPartialCLM (I := I) (M := M) g α j hLip)
    (e := smoothToH1Compl (I := I) (M := M) g)
    (denseRange_smoothToH1Compl_local (I := I) (M := M) g)
    (isUniformInducing_smoothToH1Compl_local (I := I) (M := M) g) v

noncomputable def chartPushedWeakPartialLp
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedPartialLipschitz (I := I) (M := M) g α j)
    (u_h : H1Compl g) :
    Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α)) :=
  partialCLM (I := I) (M := M) g α j hLip u_h

theorem chartPushedWeakPartialLp_smoothToH1Compl
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedPartialLipschitz (I := I) (M := M) g α j)
    (v : SmoothScalar g) :
    chartPushedWeakPartialLp (I := I) (M := M) g α j hLip
        (smoothToH1Compl (I := I) (M := M) g v) =
      chartPushedPartialLp (I := I) (M := M) g α j v
        (chartPushedPartial_memLp (I := I) (M := M) g α j v) := by
  unfold chartPushedWeakPartialLp
  rw [partialCLM_smoothToH1Compl]
  rfl

theorem chartPushedWeakPartialLp_continuous
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedPartialLipschitz (I := I) (M := M) g α j) :
    Continuous (chartPushedWeakPartialLp (I := I) (M := M) g α j hLip) := by
  unfold chartPushedWeakPartialLp
  exact (partialCLM (I := I) (M := M) g α j hLip).continuous

end H1ComplWeakPartialLimit
end Laplacian
end Analysis
end CalabiYau

end
