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
      (H1ComplToLp (I := I) (M := M) g)

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma fHLeibnizResidualCLM_apply
    (g : SmoothRiemannianMetric I M) (α : M) (u_h : H1Compl g) :
    fHLeibnizResidualCLM (I := I) (M := M) g α u_h =
      -((2 : ℝ) • gradInnerCLM (I := I) (M := M) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h) -
        smoothMulLp (I := I) (M := M) g
          (laplacianOfChartPOU (I := I) (M := M) g α)
          (H1ComplToLp (I := I) (M := M) g u_h) := by
  unfold fHLeibnizResidualCLM
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem fHLeibnizResidualCLM_smoothToH1Compl
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    fHLeibnizResidualCLM (I := I) (M := M) g α
        (smoothToH1Compl (I := I) (M := M) g v) =
      -((2 : ℝ) • gradInnerSmooth (I := I) (M := M) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) v) -
        smoothMulLp (I := I) (M := M) g
          (laplacianOfChartPOU (I := I) (M := M) g α)
          (smoothToLp (I := I) (M := M) g v) := by
  rw [fHLeibnizResidualCLM_apply]
  rw [H1ComplToLp_smoothToH1Compl]
  rw [gradInnerCLM_smoothToH1Compl]

noncomputable def phiMulUH
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    H1Compl (I := I) (M := M) g :=
  resolvent (I := I) (M := M) g
    (leibnizCompensatedSource (I := I) (M := M) g α u_h hu_h)

omit [NeZero (Module.finrank ℝ E)] in
theorem phiMulU_h_mem_laplacianDomain
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    phiMulUH (I := I) (M := M) g α hu_h ∈
      laplacianDomain (I := I) (M := M) g := by
  unfold phiMulUH
  rw [laplacianDomain_mem_iff]
  exact ⟨leibnizCompensatedSource (I := I) (M := M) g α u_h hu_h, rfl⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianDomain_preimage_phiMulU_h
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    laplacianDomain.preimage (I := I) (M := M) g
        ⟨phiMulUH (I := I) (M := M) g α hu_h,
          phiMulU_h_mem_laplacianDomain (I := I) (M := M) g α hu_h⟩ =
      leibnizCompensatedSource (I := I) (M := M) g α u_h hu_h := by
  unfold phiMulUH
  apply resolvent_injective (I := I) (M := M) g
  rw [resolvent_laplacianDomain_preimage_eq]

omit [NeZero (Module.finrank ℝ E)] in
theorem phiMulU_h_smoothToH1Compl
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    phiMulUH (I := I) (M := M) g α
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) =
      smoothToH1Compl (I := I) (M := M) g
        (pouScalar (I := I) (M := M) α v) := by
  unfold phiMulUH
  have h_lp_eq :
      leibnizCompensatedSource (I := I) (M := M) g α
          (smoothToH1Compl (I := I) (M := M) g v)
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) =
      smoothToLp (I := I) (M := M) g
        (pouScalar (I := I) (M := M) α v).oneSubLapClassical := by
    apply MeasureTheory.Lp.ext
    have h_aeEq := pouScalar_oneSubLap_aeEq_fHLeibniz_smooth (I := I) (M := M) g α v
    have h_smoothToLp_coeFn :
        ((smoothToLp (I := I) (M := M) g
            (pouScalar (I := I) (M := M) α v).oneSubLapClassical :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g]
        (pouScalar (I := I) (M := M) α v).oneSubLapClassical.toFun :=
      MemLp.coeFn_toLp
        (pouScalar (I := I) (M := M) α v).oneSubLapClassical.memLp_two
    exact h_aeEq.symm.trans h_smoothToLp_coeFn.symm
  rw [h_lp_eq]
  exact (smoothToH1Compl_eq_resolvent_oneSubLap
    (I := I) (M := M) (pouScalar (I := I) (M := M) α v)).symm

end LaplacianDomainSmoothMul
end Laplacian
end Analysis
end CalabiYau

end
