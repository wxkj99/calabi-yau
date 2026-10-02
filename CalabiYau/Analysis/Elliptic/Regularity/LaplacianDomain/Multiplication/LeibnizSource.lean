-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/LaplacianDomain/Multiplication/LeibnizSource.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.GradInner.CLM.Defs
public import CalabiYau.Analysis.Elliptic.Regularity.SmoothScalar.MulLp
public import CalabiYau.Analysis.Elliptic.Operator.VariationalLaplacian
public import CalabiYau.Geometry.Riemannian.Operator.Laplacian.Basic

@[expose] public section
open CalabiYau.Riemannian

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace CalabiYau
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

noncomputable def laplacianOfChartPOU (g : SmoothRiemannianMetric I M) (α : M) :
    C^∞⟮I, M; ℝ⟯ :=
  ⟨ΔG (I := I) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯),
    Δ_g_contMDiff (I := I) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)⟩

@[simp] lemma laplacianOfChartPOU_apply
    (g : SmoothRiemannianMetric I M) (α : M) (x : M) :
    (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x =
      ΔG (I := I) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x := rfl

noncomputable def leibnizCompensatedSource (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl g) (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
      (h1ComplToLp (I := I) (M := M) g u_h -
        laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩)
    - (2 : ℝ) • gradInnerCLM (I := I) (M := M) g
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h
    - smoothMulLp (I := I) (M := M) g
        (laplacianOfChartPOU (I := I) (M := M) g α)
        (h1ComplToLp (I := I) (M := M) g u_h)

lemma fHLeibniz_def (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl g) (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    leibnizCompensatedSource (I := I) (M := M) g α u_h hu_h =
      smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          (h1ComplToLp (I := I) (M := M) g u_h -
            laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩)
        - (2 : ℝ) • gradInnerCLM (I := I) (M := M) g
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h
        - smoothMulLp (I := I) (M := M) g
            (laplacianOfChartPOU (I := I) (M := M) g α)
            (h1ComplToLp (I := I) (M := M) g u_h) := rfl

theorem fHLeibniz_smoothToH1Compl (g : SmoothRiemannianMetric I M) (α : M)
    (v : SmoothScalar g) :
    leibnizCompensatedSource (I := I) (M := M) g α
        (smoothToH1Compl (I := I) (M := M) g v)
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) =
      smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          (smoothToLp (I := I) (M := M) g v.oneSubLapClassical)
        - (2 : ℝ) • gradInnerSmooth (I := I) (M := M) g
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) v
        - smoothMulLp (I := I) (M := M) g
            (laplacianOfChartPOU (I := I) (M := M) g α)
            (smoothToLp (I := I) (M := M) g v) := by
  rw [fHLeibniz_def]
  have h_oneSubLap :
      h1ComplToLp (I := I) (M := M) g
          (smoothToH1Compl (I := I) (M := M) g v) -
        laplacianOp (I := I) (M := M) g
          ⟨smoothToH1Compl (I := I) (M := M) g v,
            smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v⟩ =
      smoothToLp (I := I) (M := M) g v.oneSubLapClassical := by
    rw [h1ComplToLp_smoothToH1Compl, laplacianOp_smoothToH1Compl]
    abel
  rw [h_oneSubLap]
  rw [gradInnerCLM_smoothToH1Compl]
  rw [h1ComplToLp_smoothToH1Compl]

end Laplacian
end Analysis
end CalabiYau

end
