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
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
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
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma gradRhoSqSmooth_apply
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) (x : M) :
    (gradRhoSqSmooth (I := I) (M := M) g ρα : M → ℝ) x =
      g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g ρα x) := rfl

omit [T2Space M] [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma gradInner_leibniz_pointwise
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) (x : M) :
    (ρα : M → ℝ) x *
        g.inner x (gradFun (I := I) g ρα x)
          (gradFun (I := I) g v.toFun x) =
      g.inner x (gradFun (I := I) g ρα x)
          (gradFun (I := I) g
            (smoothScalarMulFun (I := I) (M := M) g ρα v).toFun x) -
        (gradRhoSqSmooth (I := I) (M := M) g ρα : M → ℝ) x * v.toFun x := by
  classical
  have h_grad := gradFun_smoothScalarMulFun (I := I) (M := M) g ρα v x
  rw [h_grad]
  rw [ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul,
    ContinuousLinearMap.map_smul]
  simp only [smul_eq_mul, gradRhoSqSmooth_apply]
  ring

omit [NeZero (Module.finrank ℝ E)] in
theorem gradInner_leibniz_smooth_Lp
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    smoothMulLp (I := I) (M := M) g ρα
        (gradInnerSmooth (I := I) (M := M) g ρα v) =
      gradInnerSmooth (I := I) (M := M) g ρα
          (smoothScalarMulFun (I := I) (M := M) g ρα v) -
        smoothMulLp (I := I) (M := M) g
          (gradRhoSqSmooth (I := I) (M := M) g ρα)
          (smoothToLp (I := I) (M := M) g v) := by
  classical
  apply MeasureTheory.Lp.ext
  have h_lhs_aeEq : (smoothMulLp (I := I) (M := M) g ρα
        (gradInnerSmooth (I := I) (M := M) g ρα v) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      fun x : M => (ρα : M → ℝ) x *
        g.inner x (gradFun (I := I) g ρα x)
          (gradFun (I := I) g v.toFun x) := by
    have h1 := smoothMulLp_apply_coeFn (I := I) (M := M) g ρα
      (gradInnerSmooth (I := I) (M := M) g ρα v)
    have h2 := gradInnerSmooth_coeFn (I := I) (M := M) g ρα v
    refine h1.trans ?_
    filter_upwards [h2] with x hx
    rw [hx]
  have h_rhs1_aeEq : (gradInnerSmooth (I := I) (M := M) g ρα
        (smoothScalarMulFun (I := I) (M := M) g ρα v) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      fun x : M =>
        g.inner x (gradFun (I := I) g ρα x)
          (gradFun (I := I) g
            (smoothScalarMulFun (I := I) (M := M) g ρα v).toFun x) :=
    gradInnerSmooth_coeFn (I := I) (M := M) g ρα
      (smoothScalarMulFun (I := I) (M := M) g ρα v)
  have h_rhs2_aeEq : (smoothMulLp (I := I) (M := M) g
        (gradRhoSqSmooth (I := I) (M := M) g ρα)
        (smoothToLp (I := I) (M := M) g v) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      fun x : M =>
        (gradRhoSqSmooth (I := I) (M := M) g ρα : M → ℝ) x * v.toFun x := by
    have h1 := smoothMulLp_apply_coeFn (I := I) (M := M) g
      (gradRhoSqSmooth (I := I) (M := M) g ρα)
      (smoothToLp (I := I) (M := M) g v)
    have h2 : ((smoothToLp (I := I) (M := M) g v :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g] v.toFun :=
      MeasureTheory.MemLp.coeFn_toLp v.memLp_two
    refine h1.trans ?_
    filter_upwards [h2] with x hx
    rw [hx]
  have h_diff_coe := MeasureTheory.Lp.coeFn_sub
    (gradInnerSmooth (I := I) (M := M) g ρα
      (smoothScalarMulFun (I := I) (M := M) g ρα v))
    (smoothMulLp (I := I) (M := M) g
      (gradRhoSqSmooth (I := I) (M := M) g ρα)
      (smoothToLp (I := I) (M := M) g v))
  refine h_lhs_aeEq.trans ?_
  refine EventuallyEq.symm ?_
  filter_upwards [h_diff_coe, h_rhs1_aeEq, h_rhs2_aeEq]
    with x hx_diff hx_rhs1 hx_rhs2
  rw [hx_diff, Pi.sub_apply, hx_rhs1, hx_rhs2]
  exact (gradInner_leibniz_pointwise (I := I) (M := M) g ρα v x).symm

noncomputable def leibnizLhsCLM
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) :
    H1Compl g →L[ℝ] Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (smoothMulLp (I := I) (M := M) g ρα).comp
    (gradInnerCLM (I := I) (M := M) g ρα)

omit [NeZero (Module.finrank ℝ E)] in
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
    (H1ComplToLp (I := I) (M := M) g)

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma leibnizRhsCLM_apply
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) (u_h : H1Compl g) :
    leibnizRhsCLM (I := I) (M := M) g ρα u_h =
      gradInnerCLM (I := I) (M := M) g ρα
          (smoothMulH1Compl (I := I) (M := M) g ρα u_h) -
        smoothMulLp (I := I) (M := M) g
          (gradRhoSqSmooth (I := I) (M := M) g ρα)
          (H1ComplToLp (I := I) (M := M) g u_h) := by
  unfold leibnizRhsCLM
  rfl

omit [NeZero (Module.finrank ℝ E)] in
private lemma leibnizCLM_agree_on_smooth
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    leibnizLhsCLM (I := I) (M := M) g ρα
        (smoothToH1Compl (I := I) (M := M) g v) =
      leibnizRhsCLM (I := I) (M := M) g ρα
          (smoothToH1Compl (I := I) (M := M) g v) := by
  classical
  rw [leibnizLhsCLM_apply, leibnizRhsCLM_apply]
  rw [gradInnerCLM_smoothToH1Compl]
  rw [smoothMulH1Compl_smoothToH1Compl, gradInnerCLM_smoothToH1Compl,
    H1ComplToLp_smoothToH1Compl]
  exact gradInner_leibniz_smooth_Lp (I := I) (M := M) g ρα v

omit [NeZero (Module.finrank ℝ E)] in
private lemma denseRange_smoothToH1Compl_aux
    (g : SmoothRiemannianMetric I M) :
    DenseRange (smoothToH1Compl (I := I) (M := M) g) := by
  unfold smoothToH1Compl
  rw [show (UniformSpace.Completion.toComplL : SmoothScalar g → H1Compl g) =
      ((↑) : SmoothScalar g → UniformSpace.Completion (SmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

omit [NeZero (Module.finrank ℝ E)] in
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

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartPushedRawLpFromLp_smoothMulLp_coeFn
    (g : SmoothRiemannianMetric I M) (_h : NeZero (Module.finrank ℝ E))
    (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    (F : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ((chartPushedRawLpFromLp (I := I) (M := M) g α
        (smoothMulLp (I := I) (M := M) g φ F) :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      (fun y =>
        chartPushedRaw (I := I) α (fun x : M => (φ : M → ℝ) x) y *
        ((chartPushedRawLpFromLp (I := I) (M := M) g α F :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) := by
  let := _h
  classical
  have h_smoothMulLp_coeFn := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α
    (smoothMulLp (I := I) (M := M) g φ F)
  have h_F_coeFn := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α F
  have h_M_aeEq : ((smoothMulLp (I := I) (M := M) g φ F :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => (φ : M → ℝ) x * ((F : Lp ℝ 2 _) : M → ℝ) x) :=
    smoothMulLp_apply_coeFn (I := I) (M := M) g φ F
  have hF_meas : Measurable ((F : Lp ℝ 2 _) : M → ℝ) :=
    (Lp.stronglyMeasurable F).measurable
  have h_smoothMulLp_meas :
      Measurable ((smoothMulLp (I := I) (M := M) g φ F :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
    (Lp.stronglyMeasurable _).measurable
  have h_prod_meas :
      Measurable (fun x : M => (φ : M → ℝ) x * ((F : Lp ℝ 2 _) : M → ℝ) x) :=
    φ.contMDiff.continuous.measurable.mul hF_meas
  have h_chartPushedRaw_aeEq :
      chartPushedRaw (I := I) α
        ((smoothMulLp (I := I) (M := M) g φ F :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      chartPushedRaw (I := I) α
        (fun x : M => (φ : M → ℝ) x * ((F : Lp ℝ 2 _) : M → ℝ) x) :=
    chartPushedRaw_aeEq_of_aeEq (I := I) (M := M) g α
      h_smoothMulLp_meas h_prod_meas h_M_aeEq
  have h_pointwise : ∀ y : EuclN,
      chartPushedRaw (I := I) α
          (fun x : M => (φ : M → ℝ) x * ((F : Lp ℝ 2 _) : M → ℝ) x) y =
        chartPushedRaw (I := I) α (fun x : M => (φ : M → ℝ) x) y *
          chartPushedRaw (I := I) α ((F : Lp ℝ 2 _) : M → ℝ) y := by
    intro y
    by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
    · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) (α := α) _ hy,
        chartPushedRaw_apply_of_mem (I := I) (M := M) (α := α)
          (fun x : M => (φ : M → ℝ) x) hy,
        chartPushedRaw_apply_of_mem (I := I) (M := M) (α := α)
          ((F : Lp ℝ 2 _) : M → ℝ) hy]
    · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) (α := α) _ hy,
        chartPushedRaw_apply_of_notMem (I := I) (M := M) (α := α)
          (fun x : M => (φ : M → ℝ) x) hy,
        chartPushedRaw_apply_of_notMem (I := I) (M := M) (α := α)
          ((F : Lp ℝ 2 _) : M → ℝ) hy]
      ring
  filter_upwards [h_smoothMulLp_coeFn, h_F_coeFn, h_chartPushedRaw_aeEq]
    with y hy_smoothMul hy_F hy_chart
  rw [hy_smoothMul, hy_chart, h_pointwise y]
  rw [← hy_F]

end GradInnerCLMLeibniz
end Laplacian
end Analysis

end CalabiYau

end
