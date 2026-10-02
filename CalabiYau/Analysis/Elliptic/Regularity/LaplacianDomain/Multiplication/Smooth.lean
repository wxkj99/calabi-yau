-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/LaplacianDomain/Multiplication/Smooth.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.LaplacianDomain.Multiplication.LeibnizSource
public import CalabiYau.Analysis.Elliptic.Regularity.Iterated.Defs
public import CalabiYau.Analysis.Elliptic.Regularity.LaplacianDomain.Variational.ArbitraryTest
public import CalabiYau.Analysis.Elliptic.Regularity.SmoothScalar.PreHOne
public import CalabiYau.Analysis.Elliptic.Regularity.LaplacianDomain.Chart.LocalRegularity

@[expose] public section

noncomputable section

open Bundle Manifold MeasureTheory Filter Topology
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace CalabiYau
namespace Analysis
namespace Laplacian
namespace LaplacianDomainSmoothMul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Analysis.Laplacian.LaplacianDomainVariationalLimit
open CalabiYau.Analysis.Laplacian.LaplacianDomainVariationalLimitGeneral

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

noncomputable def fHLeibnizResidualCLM
    (g : SmoothRiemannianMetric I M) (α : M) :
    H1Compl (I := I) (M := M) g →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  -((2 : ℝ) • gradInnerCLM (I := I) (M := M) g
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)) -
    (smoothMulLp (I := I) (M := M) g
      (laplacianOfChartPOU (I := I) (M := M) g α)).comp
      (h1ComplToLp (I := I) (M := M) g)

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma fHLeibnizResidualCLM_apply
    (g : SmoothRiemannianMetric I M) (α : M) (u_h : H1Compl g) :
    fHLeibnizResidualCLM (I := I) (M := M) g α u_h =
      -((2 : ℝ) • gradInnerCLM (I := I) (M := M) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h) -
        smoothMulLp (I := I) (M := M) g
          (laplacianOfChartPOU (I := I) (M := M) g α)
          (h1ComplToLp (I := I) (M := M) g u_h) := by
  unfold fHLeibnizResidualCLM
  rfl

end LaplacianDomainSmoothMul
end Laplacian
end Analysis
end CalabiYau

end
