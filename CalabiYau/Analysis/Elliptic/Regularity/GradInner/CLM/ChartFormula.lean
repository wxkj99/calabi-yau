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

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [I.Boundaryless] [T2Space M]
    [CompactSpace M] in
@[simp] lemma partialDerivOnEuclid_def (α : M) (i : Fin (Module.finrank ℝ E))
    (u : M → ℝ) (y : EuclN) :
    partialDerivOnEuclid (I := I) (M := M) α i u y =
      CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (scalarOnE (I := I) α u)
        ((toEuclidean (E := E)).symm y) := rfl

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] in
theorem gradInner_eq_chart_formula
    (g : SmoothRiemannianMetric I M) (α : M)
    {ρα u : M → ℝ}
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    g.inner ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (gradFun (I := I) g ρα
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (gradFun (I := I) g u
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        invGramOnEuclid (I := I) g α i j y *
          partialDerivOnEuclid (I := I) (M := M) α i ρα y *
          partialDerivOnEuclid (I := I) (M := M) α j u y := by
  classical
  set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
  have h_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
    toEuclidean_symm_mem_target (I := I) hy
  have hx_source : x ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target h_target
  have hx_chart_source : x ∈ (chartAt H α).source := by
    rwa [extChartAt_source_eq_chartAt_source (I := I)] at hx_source
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]; exact hx_chart_source
  have hx_int : extChartAt I α x ∈ interior (extChartAt I α).target := by
    have h_φx : extChartAt I α x = (toEuclidean (E := E)).symm y := by
      rw [hx_def]; exact (extChartAt I α).right_inv h_target
    rw [h_φx]
    exact extChartAt_target_subset_interior_of_boundaryless (I := I) α h_target
  have h_step1 := inner_gradFun_eq_chartInvGram_sum
    (I := I) g α ρα u hx_base hx_int
  have hφx_eq : extChartAt I α x = (toEuclidean (E := E)).symm y := by
    rw [hx_def]; exact (extChartAt I α).right_inv h_target
  have h_invGram : ∀ i j : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g α x i j =
        invGramOnEuclid (I := I) g α i j y := by
    intro i j
    unfold invGramOnEuclid; rfl
  have h_partial : ∀ k : Fin (Module.finrank ℝ E),
      ∀ u' : M → ℝ,
        CalabiYau.Tensor.Coordinates.partialDeriv (E := E) k (scalarOnE (I := I) α u') (extChartAt I α x) =
          partialDerivOnEuclid (I := I) (M := M) α k u' y := by
    intro k u'
    rw [hφx_eq]
    rfl
  rw [h_step1]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [h_partial i ρα, h_partial j u, h_invGram i j]

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] in
theorem chartPushedRaw_gradInnerSmooth_pointwise
    (g : SmoothRiemannianMetric I M) (α : M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    g.inner ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (gradFun (I := I) g ρα
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (gradFun (I := I) g v.toFun
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        invGramOnEuclid (I := I) g α i j y *
          partialDerivOnEuclid (I := I) (M := M) α i ρα y *
          partialDerivOnEuclid (I := I) (M := M) α j v.toFun y :=
  gradInner_eq_chart_formula (I := I) (M := M) g α hy

def chartFormulaRhsSmooth (g : SmoothRiemannianMetric I M) (α : M)
    (ρα : C^∞⟮I, M; ℝ⟯) (u : M → ℝ) : EuclN → ℝ := fun y =>
  ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
    invGramOnEuclid (I := I) g α i j y *
      partialDerivOnEuclid (I := I) (M := M) α i ρα y *
      partialDerivOnEuclid (I := I) (M := M) α j u y

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartFormulaRhsSmooth_def (g : SmoothRiemannianMetric I M) (α : M)
    (ρα : C^∞⟮I, M; ℝ⟯) (u : M → ℝ) (y : EuclN) :
    chartFormulaRhsSmooth (I := I) (M := M) g α ρα u y =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        invGramOnEuclid (I := I) g α i j y *
          partialDerivOnEuclid (I := I) (M := M) α i ρα y *
          partialDerivOnEuclid (I := I) (M := M) α j u y := rfl

end GradInnerCLMChartFormula
end Laplacian
end Analysis
end CalabiYau

end
