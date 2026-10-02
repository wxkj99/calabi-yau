-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/GradInner/CLM/Leibniz.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.GradInner.CLM.Defs
public import CalabiYau.Analysis.Elliptic.Regularity.LaplacianDomain.Multiplication.H1Completion
public import CalabiYau.Analysis.Elliptic.Regularity.SmoothScalar.MulLp
public import CalabiYau.Analysis.Elliptic.Regularity.LaplacianDomain.L2
public import CalabiYau.Analysis.Elliptic.Regularity.LaplacianDomain.Chart.VariationalData
public import CalabiYau.Geometry.Riemannian.Operator.Gradient.NormSquared

@[expose] public section
open CalabiYau.Riemannian

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Topology Function
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace Matrix

namespace CalabiYau
namespace Analysis
namespace Laplacian
namespace GradInnerCLMLeibniz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Laplacian.LaplacianDomainSmoothMul
open CalabiYau.Analysis.Laplacian.LaplacianDomainChartData
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

noncomputable def gradRhoSqSmooth
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) :
    C^∞⟮I, M; ℝ⟯ :=
  ⟨normGradSqFun (I := I) g (ρα : M → ℝ),
    normGradSqFun_contMDiff (I := I) g ρα.contMDiff⟩

omit [T2Space M] [CompactSpace M] in
@[simp] lemma gradRhoSqSmooth_apply
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) (x : M) :
    (gradRhoSqSmooth (I := I) (M := M) g ρα : M → ℝ) x =
      g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g ρα x) := rfl

noncomputable def leibnizLhsCLM
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) :
    H1Compl g →L[ℝ] Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (smoothMulLp (I := I) (M := M) g ρα).comp
    (gradInnerCLM (I := I) (M := M) g ρα)

@[simp] lemma leibnizLhsCLM_apply
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) (u_h : H1Compl g) :
    leibnizLhsCLM (I := I) (M := M) g ρα u_h =
      smoothMulLp (I := I) (M := M) g ρα
        (gradInnerCLM (I := I) (M := M) g ρα u_h) := rfl

noncomputable def leibnizRhsCLM
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) :
    H1Compl g →L[ℝ] Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (gradInnerCLM (I := I) (M := M) g ρα).comp
    (smoothMulH1Compl (I := I) (M := M) g ρα) -
  (smoothMulLp (I := I) (M := M) g
    (gradRhoSqSmooth (I := I) (M := M) g ρα)).comp
    (h1ComplToLp (I := I) (M := M) g)

@[simp] lemma leibnizRhsCLM_apply
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) (u_h : H1Compl g) :
    leibnizRhsCLM (I := I) (M := M) g ρα u_h =
      gradInnerCLM (I := I) (M := M) g ρα
          (smoothMulH1Compl (I := I) (M := M) g ρα u_h) -
        smoothMulLp (I := I) (M := M) g
          (gradRhoSqSmooth (I := I) (M := M) g ρα)
          (h1ComplToLp (I := I) (M := M) g u_h) := by
  unfold leibnizRhsCLM
  rfl

lemma chartPushedRawLpFromLp_coeFn_sub
    (g : SmoothRiemannianMetric I M) (α : M)
    (F G : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ((chartPushedRawLpFromLp (I := I) (M := M) g α (F - G) :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      (fun y => ((chartPushedRawLpFromLp (I := I) (M := M) g α F :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y -
        ((chartPushedRawLpFromLp (I := I) (M := M) g α G :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) := by
  classical
  have h_FG_coeFn := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α (F - G)
  have h_F_coeFn := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α F
  have h_G_coeFn := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α G
  set diffFun : M → ℝ := fun x =>
    ((F : Lp ℝ 2 _) : M → ℝ) x - ((G : Lp ℝ 2 _) : M → ℝ) x with hdiffFun_def
  have h_sub_coe : ((F - G : Lp ℝ 2 _) : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g] diffFun :=
    MeasureTheory.Lp.coeFn_sub F G
  have h_FG_meas : Measurable ((F - G : Lp ℝ 2 _) : M → ℝ) :=
    (Lp.stronglyMeasurable (F - G)).measurable
  have hF_meas : Measurable ((F : Lp ℝ 2 _) : M → ℝ) :=
    (Lp.stronglyMeasurable F).measurable
  have hG_meas : Measurable ((G : Lp ℝ 2 _) : M → ℝ) :=
    (Lp.stronglyMeasurable G).measurable
  have hdiff_meas : Measurable diffFun := hF_meas.sub hG_meas
  have h_chartPushedRaw_FG :
      chartPushedRaw (I := I) α ((F - G : Lp ℝ 2 _) : M → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      chartPushedRaw (I := I) α diffFun :=
    chartPushedRaw_aeEq_of_aeEq (I := I) (M := M) g α
      h_FG_meas hdiff_meas h_sub_coe
  have h_chartPushedRaw_diff_pointwise :
      ∀ y : EuclN,
        chartPushedRaw (I := I) α diffFun y =
          chartPushedRaw (I := I) α ((F : Lp ℝ 2 _) : M → ℝ) y -
            chartPushedRaw (I := I) α ((G : Lp ℝ 2 _) : M → ℝ) y := by
    intro y
    by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
    · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) (α := α) diffFun hy,
        chartPushedRaw_apply_of_mem (I := I) (M := M) (α := α)
          ((F : Lp ℝ 2 _) : M → ℝ) hy,
        chartPushedRaw_apply_of_mem (I := I) (M := M) (α := α)
          ((G : Lp ℝ 2 _) : M → ℝ) hy]
    · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) (α := α) diffFun hy,
        chartPushedRaw_apply_of_notMem (I := I) (M := M) (α := α)
          ((F : Lp ℝ 2 _) : M → ℝ) hy,
        chartPushedRaw_apply_of_notMem (I := I) (M := M) (α := α)
          ((G : Lp ℝ 2 _) : M → ℝ) hy]
      ring
  filter_upwards [h_FG_coeFn, h_F_coeFn, h_G_coeFn, h_chartPushedRaw_FG]
    with y hy_FG hy_F hy_G hy_chart
  rw [hy_FG, hy_chart, h_chartPushedRaw_diff_pointwise y]
  rw [← hy_F, ← hy_G]

end GradInnerCLMLeibniz
end Laplacian
end Analysis

end CalabiYau

end
