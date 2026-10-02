-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/LaplacianDomain/Variational/Identity.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.ChartPushed.PulledIntegralContinuity
public import CalabiYau.Analysis.Elliptic.Regularity.LaplacianDomain.Variational.ArbitraryTest
public import CalabiYau.Analysis.Elliptic.Regularity.LaplacianDomain.Variational.SmoothApproximation
public import CalabiYau.Analysis.Elliptic.Regularity.LaplacianDomain.Multiplication.LeibnizSource
public import CalabiYau.Analysis.Elliptic.Regularity.GradInner.CLM.Defs
public import CalabiYau.Analysis.Elliptic.Regularity.SmoothScalar.MulLp
public import CalabiYau.Analysis.Elliptic.Regularity.ChartBilinear.H1ComplFromDom
public import CalabiYau.Analysis.Elliptic.Regularity.H1Compl.WeakPartialLimit
public import CalabiYau.Analysis.Elliptic.Regularity.H1Compl.GradientH1LipschitzBound
public import CalabiYau.Analysis.Elliptic.Regularity.ChartPushed.WeakPartialOnVolume
public import CalabiYau.Analysis.Elliptic.Operator.VariationalLaplacian
public import CalabiYau.Analysis.Elliptic.Operator.SmoothBridge
public import CalabiYau.Analysis.Elliptic.Operator.Variational
public import CalabiYau.Geometry.Riemannian.Operator.Gradient.NormSquared

@[expose] public section
open CalabiYau.Riemannian

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace CalabiYau
namespace Analysis
namespace Laplacian
namespace LaplacianDomainVariationalIdentity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Laplacian.MetricExtension
  hiding chartTargetEuclid
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.ChartBilinearH1ComplFromDom
open CalabiYau.Analysis.Laplacian.ChartPulledIntegralContinuity
open CalabiYau.Analysis.Laplacian.LaplacianDomainVariationalLimit
open CalabiYau.Analysis.Laplacian.LaplacianDomainVariationalLimitGeneral
open CalabiYau.Analysis.Laplacian.H1ComplWeakPartialLimit
open CalabiYau.Analysis.Laplacian.H1ComplGradientH1LipschitzBound
open Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] in
lemma densityPsi_cont
    {g : SmoothRiemannianMetric I M} {α : M}
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Continuous (fun y : EuclN => densityOnEuclid (I := I) g α y * ψ y) := by
  classical
  refine continuous_iff_continuousAt.mpr fun y => ?_
  by_cases hy : y ∈ tsupport ψ
  · have hy_T : y ∈ chartTargetEuclid (I := I) (M := M) α := hψ_support hy
    have hOpen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α
    have h_dens : ContinuousAt (densityOnEuclid (I := I) g α) y :=
      ((densityOnEuclid_contDiffOn (I := I) g α).continuousOn).continuousAt
        (hOpen.mem_nhds hy_T)
    exact h_dens.mul hψ.continuous.continuousAt
  · have h_compl_open : IsOpen (tsupport ψ)ᶜ := (isClosed_tsupport _).isOpen_compl
    have h_ev : (fun y => densityOnEuclid (I := I) g α y * ψ y) =ᶠ[𝓝 y]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [h_compl_open.mem_nhds hy] with z hz
      have hψ_z : ψ z = 0 := image_eq_zero_of_notMem_tsupport hz
      rw [hψ_z, mul_zero]
    refine ContinuousAt.congr ?_ h_ev.symm
    exact continuousAt_const

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [CompactSpace M] in
lemma densityPsi_cs
    {g : SmoothRiemannianMetric I M} {α : M}
    {ψ : EuclN → ℝ} (hψ_cs : HasCompactSupport ψ) :
    HasCompactSupport (fun y : EuclN => densityOnEuclid (I := I) g α y * ψ y) := by
  refine HasCompactSupport.intro (hψ_cs : IsCompact (tsupport ψ)) (fun y hy => ?_)
  have hψ_y : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy
  change densityOnEuclid (I := I) g α y * ψ y = 0
  rw [hψ_y, mul_zero]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [CompactSpace M] in
lemma densityPsi_support
    {g : SmoothRiemannianMetric I M} {α : M}
    {ψ : EuclN → ℝ}
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    tsupport (fun y : EuclN => densityOnEuclid (I := I) g α y * ψ y) ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  refine subset_trans (closure_mono ?_) hψ_support
  intro y hy
  rw [Function.mem_support] at hy
  by_contra hyψ
  apply hy
  have hψ_y : ψ y = 0 := Function.notMem_support.mp hyψ
  change densityOnEuclid (I := I) g α y * ψ y = 0
  rw [hψ_y, mul_zero]

omit [NeZero (Module.finrank ℝ E)] in
lemma smoothToLp_tendsto_H1ComplToLp_of_h1_tendsto
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl g} {v : ℕ → SmoothScalar g}
    (h_tendsto : Tendsto (fun n => smoothToH1Compl (I := I) (M := M) g (v n))
      atTop (𝓝 u_h)) :
    Tendsto (fun n => smoothToLp (I := I) (M := M) g (v n)) atTop
      (𝓝 (H1ComplToLp (I := I) (M := M) g u_h)) := by
  classical
  have h_compose : Tendsto (fun n => H1ComplToLp (I := I) (M := M) g
      (smoothToH1Compl (I := I) (M := M) g (v n))) atTop
      (𝓝 (H1ComplToLp (I := I) (M := M) g u_h)) :=
    ((H1ComplToLp (I := I) (M := M) g).continuous.tendsto _).comp h_tendsto
  have h_eq : (fun n => H1ComplToLp (I := I) (M := M) g
      (smoothToH1Compl (I := I) (M := M) g (v n))) =
      (fun n => smoothToLp (I := I) (M := M) g (v n)) := by
    funext n
    exact H1ComplToLp_smoothToH1Compl (I := I) (M := M) g (v n)
  rw [← h_eq]; exact h_compose

private noncomputable def gradInnerSmoothScalar
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) : SmoothScalar g where
  toFun := fun x : M => g.inner x (gradFun (I := I) g ρα x)
    (gradFun (I := I) g v.toFun x)
  smooth := by
    let vMap : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯ := ⟨v.toFun, v.smooth⟩
    have h := contMDiff_g_inner_of_smooth_sections (I := I) (M := M) g
      (gradG (I := I) g ρα) (gradG (I := I) g vMap)
    refine h.congr (fun x => ?_)
    change g.inner x ((gradG (I := I) g ρα :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g vMap :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g v.toFun x)
    rw [grad_g_apply, grad_g_apply]
    rfl

omit [T2Space M] [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma gradInnerSmoothScalar_toFun
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    (gradInnerSmoothScalar (I := I) (M := M) g ρα v).toFun =
      fun x : M => g.inner x (gradFun (I := I) g ρα x)
        (gradFun (I := I) g v.toFun x) := rfl

omit [NeZero (Module.finrank ℝ E)] in
private lemma gradInnerSmooth_eq_smoothToLp
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    gradInnerSmooth (I := I) (M := M) g ρα v =
      smoothToLp (I := I) (M := M) g
        (gradInnerSmoothScalar (I := I) (M := M) g ρα v) := by
  classical
  apply MeasureTheory.Lp.ext
  have h_grad := gradInnerSmooth_coeFn (I := I) (M := M) g ρα v
  have h_lp_h : ((smoothToLp (I := I) (M := M) g
        (gradInnerSmoothScalar (I := I) (M := M) g ρα v) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (gradInnerSmoothScalar (I := I) (M := M) g ρα v).toFun :=
    MemLp.coeFn_toLp (gradInnerSmoothScalar (I := I) (M := M) g ρα v).memLp_two
  filter_upwards [h_grad, h_lp_h] with x hx_grad hx_lp_h
  rw [hx_grad, hx_lp_h]
  rfl

private noncomputable def rhoOneSubLapSmoothScalar
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    SmoothScalar g where
  toFun := fun x : M => (ρα : M → ℝ) x * v.oneSubLapClassical.toFun x
  smooth := ρα.contMDiff.mul v.oneSubLapClassical.smooth

omit [NeZero (Module.finrank ℝ E)] in
private lemma smoothMulLp_oneSubLap_eq_smoothToLp
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    smoothMulLp (I := I) (M := M) g ρα
        (smoothToLp (I := I) (M := M) g v.oneSubLapClassical) =
      smoothToLp (I := I) (M := M) g
        (rhoOneSubLapSmoothScalar (I := I) (M := M) g ρα v) := by
  classical
  apply MeasureTheory.Lp.ext
  have h_mul := smoothMulLp_apply_coeFn (I := I) (M := M) g ρα
    (smoothToLp (I := I) (M := M) g v.oneSubLapClassical)
  have h_lp1 : ((smoothToLp (I := I) (M := M) g v.oneSubLapClassical
        : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g] v.oneSubLapClassical.toFun :=
    MemLp.coeFn_toLp v.oneSubLapClassical.memLp_two
  have h_lp_h : ((smoothToLp (I := I) (M := M) g
        (rhoOneSubLapSmoothScalar (I := I) (M := M) g ρα v) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (rhoOneSubLapSmoothScalar (I := I) (M := M) g ρα v).toFun :=
    MemLp.coeFn_toLp (rhoOneSubLapSmoothScalar (I := I) (M := M) g ρα v).memLp_two
  refine h_mul.trans ?_
  filter_upwards [h_lp1, h_lp_h] with x hx_lp1 hx_lp_h
  change (ρα : M → ℝ) x * ((smoothToLp (I := I) (M := M) g v.oneSubLapClassical
        : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x =
    ((smoothToLp (I := I) (M := M) g
        (rhoOneSubLapSmoothScalar (I := I) (M := M) g ρα v) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
  rw [hx_lp1, hx_lp_h]
  rfl

private noncomputable def laplacianRhoMulSmoothScalar
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    SmoothScalar g where
  toFun := fun x : M =>
    (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x * v.toFun x
  smooth :=
    (laplacianOfChartPOU (I := I) (M := M) g α).contMDiff.mul v.smooth

omit [NeZero (Module.finrank ℝ E)] in
private lemma smoothMulLp_laplacianRho_eq_smoothToLp
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    smoothMulLp (I := I) (M := M) g (laplacianOfChartPOU (I := I) (M := M) g α)
        (smoothToLp (I := I) (M := M) g v) =
      smoothToLp (I := I) (M := M) g
        (laplacianRhoMulSmoothScalar (I := I) (M := M) g α v) := by
  classical
  apply MeasureTheory.Lp.ext
  have h_mul := smoothMulLp_apply_coeFn (I := I) (M := M) g
    (laplacianOfChartPOU (I := I) (M := M) g α)
    (smoothToLp (I := I) (M := M) g v)
  have h_lp1 : ((smoothToLp (I := I) (M := M) g v
        : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g] v.toFun :=
    MemLp.coeFn_toLp v.memLp_two
  have h_lp_h : ((smoothToLp (I := I) (M := M) g
        (laplacianRhoMulSmoothScalar (I := I) (M := M) g α v) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (laplacianRhoMulSmoothScalar (I := I) (M := M) g α v).toFun :=
    MemLp.coeFn_toLp (laplacianRhoMulSmoothScalar (I := I) (M := M) g α v).memLp_two
  refine h_mul.trans ?_
  filter_upwards [h_lp1, h_lp_h] with x hx_lp1 hx_lp_h
  change (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x *
      ((smoothToLp (I := I) (M := M) g v
        : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x =
    ((smoothToLp (I := I) (M := M) g
        (laplacianRhoMulSmoothScalar (I := I) (M := M) g α v) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
  rw [hx_lp1, hx_lp_h]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma chartPulledIntegralCLM_gradInnerSmooth_tendsto
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    {u_h : H1Compl g}
    {v : ℕ → SmoothScalar g}
    (h_tendsto : Tendsto (fun n => smoothToH1Compl (I := I) (M := M) g (v n))
      atTop (𝓝 u_h)) :
    Tendsto (fun n => chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
        (gradInnerSmooth (I := I) (M := M) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) (v n))) atTop
      (𝓝 (chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
        (gradInnerCLM (I := I) (M := M) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h))) := by
  classical
  have h_eq_n : ∀ n,
      gradInnerSmooth (I := I) (M := M) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) (v n) =
        gradInnerCLM (I := I) (M := M) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          (smoothToH1Compl (I := I) (M := M) g (v n)) :=
    fun n => (gradInnerCLM_smoothToH1Compl (I := I) (M := M) g _ (v n)).symm
  have h_funeq : (fun n => chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
        (gradInnerSmooth (I := I) (M := M) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) (v n))) =
      (fun n => chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
        (gradInnerCLM (I := I) (M := M) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          (smoothToH1Compl (I := I) (M := M) g (v n)))) := by
    funext n; rw [h_eq_n n]
  rw [h_funeq]
  exact chartPulledIntegralCLM_tendsto (I := I) (M := M) g α
    (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
    (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
    (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
    (((gradInnerCLM (I := I) (M := M) g
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)).continuous.tendsto _).comp h_tendsto)

omit [NeZero (Module.finrank ℝ E)] in
lemma chartPulledIntegralCLM_smoothMulLp_tendsto
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    {u_h : H1Compl g}
    {v : ℕ → SmoothScalar g}
    (h_tendsto : Tendsto (fun n => smoothToH1Compl (I := I) (M := M) g (v n))
      atTop (𝓝 u_h)) :
    Tendsto (fun n => chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
        (smoothMulLp (I := I) (M := M) g
          (laplacianOfChartPOU (I := I) (M := M) g α)
          (smoothToLp (I := I) (M := M) g (v n)))) atTop
      (𝓝 (chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
        (smoothMulLp (I := I) (M := M) g
          (laplacianOfChartPOU (I := I) (M := M) g α)
          (H1ComplToLp (I := I) (M := M) g u_h)))) := by
  classical
  have h_lp_tendsto : Tendsto (fun n => smoothToLp (I := I) (M := M) g (v n))
      atTop (𝓝 (H1ComplToLp (I := I) (M := M) g u_h)) :=
    smoothToLp_tendsto_H1ComplToLp_of_h1_tendsto (I := I) (M := M) g h_tendsto
  have h_smoothMul_tendsto : Tendsto (fun n =>
      smoothMulLp (I := I) (M := M) g
          (laplacianOfChartPOU (I := I) (M := M) g α)
          (smoothToLp (I := I) (M := M) g (v n))) atTop
      (𝓝 (smoothMulLp (I := I) (M := M) g
        (laplacianOfChartPOU (I := I) (M := M) g α)
        (H1ComplToLp (I := I) (M := M) g u_h))) :=
    ((smoothMulLp (I := I) (M := M) g
        (laplacianOfChartPOU (I := I) (M := M) g α)).continuous.tendsto _).comp
      h_lp_tendsto
  exact chartPulledIntegralCLM_tendsto (I := I) (M := M) g α
    (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
    (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
    (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
    h_smoothMul_tendsto

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartPulledIntegralCLM_smoothToLp_eq_lpInner
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ} (hθ_cont : Continuous θ) (hθ_cs : HasCompactSupport θ)
    (hθ_support : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (h_smooth : SmoothScalar g) :
    chartPulledIntegralCLM (I := I) (M := M) g α hθ_cont hθ_cs hθ_support
        (smoothToLp (I := I) (M := M) g h_smooth) =
      ⟪chartPulledIntegralWeightLp (I := I) (M := M) g α hθ_cont hθ_cs hθ_support,
        smoothToLp (I := I) (M := M) g h_smooth⟫_ℝ := by
  unfold chartPulledIntegralCLM
  rw [innerSL_apply_apply]

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartPulledIntegralCLM_smoothMulLp_oneSubLap_eq_lpInner
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (v : SmoothScalar g) :
    chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
        (smoothMulLp (I := I) (M := M) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          (smoothToLp (I := I) (M := M) g v.oneSubLapClassical)) =
      ⟪chartPulledIntegralWeightLp (I := I) (M := M) g α
          (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
          (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
          (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support),
        smoothToLp (I := I) (M := M) g
          (rhoOneSubLapSmoothScalar (I := I) (M := M) g
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) v)⟫_ℝ := by
  rw [smoothMulLp_oneSubLap_eq_smoothToLp]
  exact chartPulledIntegralCLM_smoothToLp_eq_lpInner (I := I) (M := M) g α
    (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
    (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
    (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
    (rhoOneSubLapSmoothScalar (I := I) (M := M) g
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) v)

omit [NeZero (Module.finrank ℝ E)] in
private lemma h1Inner_smoothToH1Compl_eq_lpInner_oneSubLap_of_laplacianDomain
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (w : SmoothScalar g) :
    ⟪u_h, smoothToH1Compl (I := I) (M := M) g w⟫_ℝ =
      ⟪smoothToLp (I := I) (M := M) g w,
        H1ComplToLp (I := I) (M := M) g u_h -
          laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩⟫_ℝ := by
  classical
  set f : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_h⟩
  have h_u_eq : (⟨u_h, hu_h⟩ : laplacianDomain (I := I) (M := M) g).val =
      resolvent (I := I) (M := M) g f :=
    (resolvent_laplacianDomain_preimage_eq (I := I) (M := M) g ⟨u_h, hu_h⟩).symm
  have h_res := resolvent_inner_eq_lpFunctional (I := I) (M := M) g f
    (smoothToH1Compl (I := I) (M := M) g w)
  have h_subst : ⟪u_h, smoothToH1Compl (I := I) (M := M) g w⟫_ℝ =
      ⟪resolvent (I := I) (M := M) g f,
        smoothToH1Compl (I := I) (M := M) g w⟫_ℝ := by
    rw [show u_h = (⟨u_h, hu_h⟩ : laplacianDomain (I := I) (M := M) g).val from rfl,
      h_u_eq]
  rw [h_subst, h_res]
  rw [H1ComplToLp_smoothToH1Compl]
  have h_f_eq : f = H1ComplToLp (I := I) (M := M) g u_h -
      laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩ := by
    have h_lap_apply :=
      laplacianOp_apply (I := I) (M := M) g ⟨u_h, hu_h⟩
    rw [h_lap_apply]
    abel
  rw [← h_f_eq]

private noncomputable def rhoChartWeightSmoothScalarOn
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ}
    (_hθ_cont : Continuous θ)
    (hθ_contDiffOn : ContDiffOn ℝ ∞ θ (chartTargetEuclid (I := I) (M := M) α))
    (_hθ_cs : HasCompactSupport θ)
    (_hθ_support : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    SmoothScalar g where
  toFun := fun x : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
      chartPulledIntegralWeight (I := I) (M := M) g α θ x
  smooth := by
    classical
    intro x
    set ρα_smooth : C^∞⟮I, M; ℝ⟯ := chartAtlasPOU I M α
    set ρα : M → ℝ := (ρα_smooth : M → ℝ)
    have hρα_subord :
        tsupport (fun y : M => (ρα_smooth : M → ℝ) y) ⊆ (chartAt H α).source :=
      CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M α
    by_cases hxsrc : x ∈ (chartAt H α).source
    · have h_open : IsOpen ((chartAt H α).source) := (chartAt H α).open_source
      have h_nhds : (chartAt H α).source ∈ 𝓝 x := h_open.mem_nhds hxsrc
      have h_eq_evt : (fun y : M => ρα y *
          chartPulledIntegralWeight (I := I) (M := M) g α θ y) =ᶠ[𝓝 x]
          fun y : M => ρα y *
            (θ ((toEuclidean (E := E)) ((extChartAt I α) y)) /
              chartDensity g α y) := by
        filter_upwards [h_nhds] with y hy
        rw [chartPulledIntegralWeight_apply_of_mem
          (I := I) (M := M) g α θ hy]
      refine (ContMDiffAt.congr_of_eventuallyEq ?_ h_eq_evt)
      have hρα_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ ρα x := ρα_smooth.contMDiff x
      have h_ext_on : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α)
          (chartAt H α).source :=
        contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)
      have h_eucl_contDiff : ContDiff ℝ (⊤ : ℕ∞)
          ((toEuclidean : E ≃L[ℝ] EuclN) : E → EuclN) :=
        (toEuclidean : E ≃L[ℝ] EuclN).contDiff
      have h_eucl_contMDiff : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclN) ∞
          ((toEuclidean : E ≃L[ℝ] EuclN) : E → EuclN) :=
        (contMDiff_iff_contDiff (n := (⊤ : ℕ∞))).mpr h_eucl_contDiff
      have h_extChart_at : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I α) x :=
        (h_ext_on x hxsrc).contMDiffAt (h_open.mem_nhds hxsrc)
      have h_chartMap_contMDiffAt :
          ContMDiffAt I 𝓘(ℝ, EuclN) ∞
            (fun y : M => (toEuclidean (E := E)) ((extChartAt I α) y)) x :=
        h_eucl_contMDiff.contMDiffAt.comp x h_extChart_at
      have hxtarget : (toEuclidean (E := E)) ((extChartAt I α) x) ∈
          chartTargetEuclid (I := I) (M := M) α := by
        refine ⟨(extChartAt I α) x, ?_, rfl⟩
        have hxE : x ∈ (extChartAt I α).source := by
          rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
            (I := I) (M := M)]
          exact hxsrc
        exact (extChartAt I α).map_source hxE
      have h_target_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
        Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α
      have hθ_mdOn : ContMDiffOn 𝓘(ℝ, EuclN) 𝓘(ℝ, ℝ) ∞ θ
          (chartTargetEuclid (I := I) (M := M) α) :=
        (contMDiffOn_iff_contDiffOn).mpr hθ_contDiffOn
      have hθ_at : ContMDiffAt 𝓘(ℝ, EuclN) 𝓘(ℝ, ℝ) ∞ θ
          ((toEuclidean (E := E)) ((extChartAt I α) x)) :=
        (hθ_mdOn _ hxtarget).contMDiffAt (h_target_open.mem_nhds hxtarget)
      have h_theta_comp_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
          (fun y : M => θ ((toEuclidean (E := E)) ((extChartAt I α) y))) x :=
        hθ_at.comp x h_chartMap_contMDiffAt
      have h_dens_contMDiffOn : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (chartDensity g α)
          (chartAt H α).source := by
        rw [show (chartAt H α).source =
            (trivializationAt E (TangentSpace I) α).baseSet from
          (CalabiYau.RiemannianVolume.trivializationAt_baseSet_eq_chartAt_source
            (I := I) (M := M) α).symm]
        exact CalabiYau.RiemannianVolume.chartDensity_contMDiffOn
          (I := I) g α
      have h_dens_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (chartDensity g α) x :=
        (h_dens_contMDiffOn x hxsrc).contMDiffAt (h_open.mem_nhds hxsrc)
      have hxbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
        rw [CalabiYau.RiemannianVolume.trivializationAt_baseSet_eq_chartAt_source
          (I := I) (M := M)]
        exact hxsrc
      have h_dens_pos : 0 < chartDensity g α x :=
        CalabiYau.RiemannianVolume.chartDensity_pos (I := I) g α hxbase
      have h_dens_ne_zero : chartDensity g α x ≠ 0 := h_dens_pos.ne'
      exact hρα_at.mul (h_theta_comp_at.div₀ h_dens_at h_dens_ne_zero)
    · have hx_off : x ∉ tsupport (fun y : M => ρα y) := fun h => hxsrc (hρα_subord h)
      have h_compl_open : IsOpen ((tsupport (fun y : M => ρα y))ᶜ) :=
        (isClosed_tsupport _).isOpen_compl
      have h_eq_evt : (fun y : M => ρα y *
          chartPulledIntegralWeight (I := I) (M := M) g α θ y) =ᶠ[𝓝 x]
          (fun _ : M => (0 : ℝ)) := by
        filter_upwards [h_compl_open.mem_nhds hx_off] with y hy_off
        have hρα_zero : ρα y = 0 := image_eq_zero_of_notMem_tsupport hy_off
        rw [hρα_zero, zero_mul]
      refine (ContMDiffAt.congr_of_eventuallyEq ?_ h_eq_evt)
      exact contMDiffAt_const

omit [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma rhoChartWeightSmoothScalarOn_toFun
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ}
    (hθ_cont : Continuous θ)
    (hθ_contDiffOn : ContDiffOn ℝ ∞ θ (chartTargetEuclid (I := I) (M := M) α))
    (hθ_cs : HasCompactSupport θ)
    (hθ_support : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (rhoChartWeightSmoothScalarOn (I := I) (M := M) g α
        hθ_cont hθ_contDiffOn hθ_cs hθ_support).toFun =
      fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
        chartPulledIntegralWeight (I := I) (M := M) g α θ x := rfl

omit [NeZero (Module.finrank ℝ E)] in
private lemma smoothMulLp_chartWeight_eq_smoothToLp_rhoWeightOn
    (g : SmoothRiemannianMetric I M) (α : M)
    {θ : EuclN → ℝ}
    (hθ_cont : Continuous θ)
    (hθ_contDiffOn : ContDiffOn ℝ ∞ θ (chartTargetEuclid (I := I) (M := M) α))
    (hθ_cs : HasCompactSupport θ)
    (hθ_support : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
        (chartPulledIntegralWeightLp (I := I) (M := M) g α
          hθ_cont hθ_cs hθ_support) =
      smoothToLp (I := I) (M := M) g
        (rhoChartWeightSmoothScalarOn (I := I) (M := M) g α
          hθ_cont hθ_contDiffOn hθ_cs hθ_support) := by
  classical
  apply MeasureTheory.Lp.ext
  have h_mul := smoothMulLp_apply_coeFn (I := I) (M := M) g
    (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
    (chartPulledIntegralWeightLp (I := I) (M := M) g α
      hθ_cont hθ_cs hθ_support)
  have h_w_coe : (chartPulledIntegralWeightLp (I := I) (M := M) g α
        hθ_cont hθ_cs hθ_support :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      chartPulledIntegralWeight (I := I) (M := M) g α θ :=
    MemLp.coeFn_toLp (chartPulledIntegralWeight_memLp
      (I := I) (M := M) g α hθ_cont hθ_cs hθ_support)
  have h_rhs_coe : ((smoothToLp (I := I) (M := M) g
        (rhoChartWeightSmoothScalarOn (I := I) (M := M) g α
          hθ_cont hθ_contDiffOn hθ_cs hθ_support) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (rhoChartWeightSmoothScalarOn
        (I := I) (M := M) g α hθ_cont hθ_contDiffOn hθ_cs hθ_support).toFun :=
    MemLp.coeFn_toLp (rhoChartWeightSmoothScalarOn (I := I) (M := M) g α
      hθ_cont hθ_contDiffOn hθ_cs hθ_support).memLp_two
  refine h_mul.trans ?_
  filter_upwards [h_w_coe, h_rhs_coe] with x hx_w hx_rhs
  change ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
      ((chartPulledIntegralWeightLp (I := I) (M := M) g α
        hθ_cont hθ_cs hθ_support :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x =
    ((smoothToLp (I := I) (M := M) g
        (rhoChartWeightSmoothScalarOn (I := I) (M := M) g α
          hθ_cont hθ_contDiffOn hθ_cs hθ_support) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x
  rw [hx_w, hx_rhs]
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [CompactSpace M] in
private lemma densityPsi_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContDiffOn ℝ ∞ (fun y : EuclN => densityOnEuclid (I := I) g α y * ψ y)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (densityOnEuclid_contDiffOn (I := I) g α).mul hψ.contDiffOn

omit [NeZero (Module.finrank ℝ E)] in
lemma chartPulledIntegralCLM_smoothMulLp_oneSubLap_tendsto
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {v : ℕ → SmoothScalar g}
    (h_tendsto : Tendsto (fun n => smoothToH1Compl (I := I) (M := M) g (v n))
      atTop (𝓝 u_h)) :
    Tendsto (fun n => chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
        (smoothMulLp (I := I) (M := M) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          (smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical))) atTop
      (𝓝 (chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
        (smoothMulLp (I := I) (M := M) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          (H1ComplToLp (I := I) (M := M) g u_h -
            laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩)))) := by
  classical
  set θ : EuclN → ℝ := fun y : EuclN =>
    densityOnEuclid (I := I) g α y * ψ y with hθ_def
  have hθ_cont : Continuous θ :=
    densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support
  have hθ_cs : HasCompactSupport θ :=
    densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs
  have hθ_support : tsupport θ ⊆ chartTargetEuclid (I := I) (M := M) α :=
    densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support
  have hθ_contDiffOn : ContDiffOn ℝ ∞ θ
      (chartTargetEuclid (I := I) (M := M) α) :=
    densityPsi_contDiffOn (I := I) (M := M) g α hψ
  let w_smooth : SmoothScalar g :=
    rhoChartWeightSmoothScalarOn (I := I) (M := M) g α
      hθ_cont hθ_contDiffOn hθ_cs hθ_support
  have h_clm_eq_inner_n : ∀ n,
      chartPulledIntegralCLM (I := I) (M := M) g α hθ_cont hθ_cs hθ_support
          (smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
            (smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical)) =
        ⟪chartPulledIntegralWeightLp (I := I) (M := M) g α
            hθ_cont hθ_cs hθ_support,
          smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
            (smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical)⟫_ℝ := by
    intro n
    unfold chartPulledIntegralCLM
    rw [innerSL_apply_apply]
  have h_inner_assoc_n : ∀ n,
      ⟪chartPulledIntegralWeightLp (I := I) (M := M) g α
          hθ_cont hθ_cs hθ_support,
        smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          (smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical)⟫_ℝ =
      ⟪smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          (chartPulledIntegralWeightLp (I := I) (M := M) g α
            hθ_cont hθ_cs hθ_support),
        smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical⟫_ℝ := by
    intro n
    rw [L2.inner_def, L2.inner_def]
    have h_lhs_mul := smoothMulLp_apply_coeFn (I := I) (M := M) g
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
      (smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical)
    have h_rhs_mul := smoothMulLp_apply_coeFn (I := I) (M := M) g
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
      (chartPulledIntegralWeightLp (I := I) (M := M) g α
        hθ_cont hθ_cs hθ_support)
    refine integral_congr_ae ?_
    filter_upwards [h_lhs_mul, h_rhs_mul] with x hx_lhs hx_rhs
    have h_inner_lhs : ⟪((chartPulledIntegralWeightLp (I := I) (M := M) g α
            hθ_cont hθ_cs hθ_support :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x,
          ((smoothMulLp (I := I) (M := M) g
              (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
              (smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical) :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x⟫_ℝ =
        ((smoothMulLp (I := I) (M := M) g
              (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
              (smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical) :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
          ((chartPulledIntegralWeightLp (I := I) (M := M) g α
              hθ_cont hθ_cs hθ_support :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x :=
        rfl
    have h_inner_rhs : ⟪((smoothMulLp (I := I) (M := M) g
              (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
              (chartPulledIntegralWeightLp (I := I) (M := M) g α
                hθ_cont hθ_cs hθ_support) :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x,
          ((smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x⟫_ℝ =
        ((smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
          ((smoothMulLp (I := I) (M := M) g
              (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
              (chartPulledIntegralWeightLp (I := I) (M := M) g α
                hθ_cont hθ_cs hθ_support) :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x :=
        rfl
    rw [h_inner_lhs, h_inner_rhs, hx_lhs, hx_rhs]
    ring
  have h_smooth_replace_n : ∀ n,
      ⟪smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          (chartPulledIntegralWeightLp (I := I) (M := M) g α
            hθ_cont hθ_cs hθ_support),
        smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical⟫_ℝ =
      ⟪smoothToLp (I := I) (M := M) g w_smooth,
        smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical⟫_ℝ := by
    intro n
    rw [smoothMulLp_chartWeight_eq_smoothToLp_rhoWeightOn (I := I) (M := M) g α
      hθ_cont hθ_contDiffOn hθ_cs hθ_support]
  have h_bridge_n : ∀ n,
      ⟪smoothToLp (I := I) (M := M) g w_smooth,
        smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical⟫_ℝ =
      smoothScalarH1Inner (I := I) (M := M) (v n) w_smooth := by
    intro n
    have h := smoothScalarH1Inner_eq_lpInner_oneSubLap (v n) w_smooth
    rw [h, real_inner_comm]
  have h_h1_n : ∀ n,
      smoothScalarH1Inner (I := I) (M := M) (v n) w_smooth =
      ⟪smoothToH1Compl (I := I) (M := M) g (v n),
        smoothToH1Compl (I := I) (M := M) g w_smooth⟫_ℝ :=
    fun n => (inner_smoothToH1Compl_smoothToH1Compl (v n) w_smooth).symm
  have h_per_n : ∀ n,
      chartPulledIntegralCLM (I := I) (M := M) g α hθ_cont hθ_cs hθ_support
          (smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
            (smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical)) =
        ⟪smoothToH1Compl (I := I) (M := M) g (v n),
          smoothToH1Compl (I := I) (M := M) g w_smooth⟫_ℝ := by
    intro n
    rw [h_clm_eq_inner_n n, h_inner_assoc_n n, h_smooth_replace_n n,
      h_bridge_n n, h_h1_n n]
  have h_lim_lhs : Tendsto (fun n =>
        ⟪smoothToH1Compl (I := I) (M := M) g (v n),
          smoothToH1Compl (I := I) (M := M) g w_smooth⟫_ℝ) atTop
      (𝓝 ⟪u_h, smoothToH1Compl (I := I) (M := M) g w_smooth⟫_ℝ) := by
    have h_inner_y_cont : Continuous fun u : H1Compl g =>
        ⟪smoothToH1Compl (I := I) (M := M) g w_smooth, u⟫_ℝ :=
      (innerSL ℝ (smoothToH1Compl (I := I) (M := M) g w_smooth)).continuous
    have h_swap_fn : (fun n =>
        ⟪smoothToH1Compl (I := I) (M := M) g (v n),
          smoothToH1Compl (I := I) (M := M) g w_smooth⟫_ℝ) =
        (fun n =>
          ⟪smoothToH1Compl (I := I) (M := M) g w_smooth,
            smoothToH1Compl (I := I) (M := M) g (v n)⟫_ℝ) := by
      funext n; exact real_inner_comm _ _
    have h_swap_lim :
        ⟪u_h, smoothToH1Compl (I := I) (M := M) g w_smooth⟫_ℝ =
        ⟪smoothToH1Compl (I := I) (M := M) g w_smooth, u_h⟫_ℝ :=
      real_inner_comm _ _
    rw [h_swap_fn, h_swap_lim]
    exact (h_inner_y_cont.tendsto _).comp h_tendsto
  have h_res :
      ⟪u_h, smoothToH1Compl (I := I) (M := M) g w_smooth⟫_ℝ =
        ⟪smoothToLp (I := I) (M := M) g w_smooth,
          H1ComplToLp (I := I) (M := M) g u_h -
            laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩⟫_ℝ :=
    h1Inner_smoothToH1Compl_eq_lpInner_oneSubLap_of_laplacianDomain
      (I := I) (M := M) g hu_h w_smooth
  have h_target_eq :
      ⟪smoothToLp (I := I) (M := M) g w_smooth,
        H1ComplToLp (I := I) (M := M) g u_h -
          laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩⟫_ℝ =
        chartPulledIntegralCLM (I := I) (M := M) g α hθ_cont hθ_cs hθ_support
          (smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
            (H1ComplToLp (I := I) (M := M) g u_h -
              laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩)) := by
    rw [← smoothMulLp_chartWeight_eq_smoothToLp_rhoWeightOn (I := I) (M := M) g α
      hθ_cont hθ_contDiffOn hθ_cs hθ_support]
    have h_assoc :
        ⟪smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
            (chartPulledIntegralWeightLp (I := I) (M := M) g α
              hθ_cont hθ_cs hθ_support),
          H1ComplToLp (I := I) (M := M) g u_h -
            laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩⟫_ℝ =
        ⟪chartPulledIntegralWeightLp (I := I) (M := M) g α
            hθ_cont hθ_cs hθ_support,
          smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
            (H1ComplToLp (I := I) (M := M) g u_h -
              laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩)⟫_ℝ := by
      rw [L2.inner_def, L2.inner_def]
      have h_lhs_mul := smoothMulLp_apply_coeFn (I := I) (M := M) g
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
        (chartPulledIntegralWeightLp (I := I) (M := M) g α
          hθ_cont hθ_cs hθ_support)
      have h_rhs_mul := smoothMulLp_apply_coeFn (I := I) (M := M) g
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
        (H1ComplToLp (I := I) (M := M) g u_h -
          laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩)
      refine integral_congr_ae ?_
      filter_upwards [h_lhs_mul, h_rhs_mul] with x hx_lhs hx_rhs
      have h_inner_lhs :
          ⟪((smoothMulLp (I := I) (M := M) g
                (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
                (chartPulledIntegralWeightLp (I := I) (M := M) g α
                  hθ_cont hθ_cs hθ_support) :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x,
            ((H1ComplToLp (I := I) (M := M) g u_h -
                laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩ :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x⟫_ℝ =
          ((H1ComplToLp (I := I) (M := M) g u_h -
                laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩ :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            ((smoothMulLp (I := I) (M := M) g
                (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
                (chartPulledIntegralWeightLp (I := I) (M := M) g α
                  hθ_cont hθ_cs hθ_support) :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x :=
        rfl
      have h_inner_rhs :
          ⟪((chartPulledIntegralWeightLp (I := I) (M := M) g α
                hθ_cont hθ_cs hθ_support :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x,
            ((smoothMulLp (I := I) (M := M) g
                (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
                (H1ComplToLp (I := I) (M := M) g u_h -
                  laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩) :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x⟫_ℝ =
          ((smoothMulLp (I := I) (M := M) g
                (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
                (H1ComplToLp (I := I) (M := M) g u_h -
                  laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩) :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x *
            ((chartPulledIntegralWeightLp (I := I) (M := M) g α
                hθ_cont hθ_cs hθ_support :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x :=
        rfl
      rw [h_inner_lhs, h_inner_rhs, hx_lhs, hx_rhs]
      ring
    rw [h_assoc]
    unfold chartPulledIntegralCLM
    rw [innerSL_apply_apply]
  rw [show (fun n : ℕ => chartPulledIntegralCLM (I := I) (M := M) g α
        hθ_cont hθ_cs hθ_support
        (smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          (smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical))) =
      fun n : ℕ =>
        ⟪smoothToH1Compl (I := I) (M := M) g (v n),
          smoothToH1Compl (I := I) (M := M) g w_smooth⟫_ℝ from
      funext h_per_n]
  rw [show chartPulledIntegralCLM (I := I) (M := M) g α hθ_cont hθ_cs hθ_support
      (smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
        (H1ComplToLp (I := I) (M := M) g u_h -
          laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩)) =
      ⟪u_h, smoothToH1Compl (I := I) (M := M) g w_smooth⟫_ℝ from ?_]
  · exact h_lim_lhs
  · rw [h_res, h_target_eq]

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianDomain_variational_identity_clm_form
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
        (smoothMulLp (I := I) (M := M) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          (H1ComplToLp (I := I) (M := M) g u_h -
            laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩)) -
      (2 : ℝ) *
        chartPulledIntegralCLM (I := I) (M := M) g α
          (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
          (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
          (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
          (gradInnerCLM (I := I) (M := M) g
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h) -
      chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
        (smoothMulLp (I := I) (M := M) g
          (laplacianOfChartPOU (I := I) (M := M) g α)
          (H1ComplToLp (I := I) (M := M) g u_h)) =
    chartPulledIntegralCLM (I := I) (M := M) g α
      (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
      (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
      (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
      (leibnizCompensatedSource (I := I) (M := M) g α u_h hu_h) := by
  classical
  obtain ⟨v, h_v_tendsto⟩ :=
    exists_smooth_approx_seq (I := I) (M := M) g u_h
  have h_lim_1 := chartPulledIntegralCLM_smoothMulLp_oneSubLap_tendsto
    (I := I) (M := M) g α hψ hψ_cs hψ_support hu_h h_v_tendsto
  have h_lim_2 := chartPulledIntegralCLM_gradInnerSmooth_tendsto
    (I := I) (M := M) g α hψ hψ_cs hψ_support h_v_tendsto
  have h_lim_3 := chartPulledIntegralCLM_smoothMulLp_tendsto
    (I := I) (M := M) g α hψ hψ_cs hψ_support h_v_tendsto
  have h_lhs_lim : Tendsto (fun n =>
      chartPulledIntegralCLM (I := I) (M := M) g α
          (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
          (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
          (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
          (smoothMulLp (I := I) (M := M) g
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
            (smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical)) -
        (2 : ℝ) *
          chartPulledIntegralCLM (I := I) (M := M) g α
            (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
            (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
            (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
            (gradInnerSmooth (I := I) (M := M) g
              (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) (v n)) -
        chartPulledIntegralCLM (I := I) (M := M) g α
          (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
          (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
          (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
          (smoothMulLp (I := I) (M := M) g
            (laplacianOfChartPOU (I := I) (M := M) g α)
            (smoothToLp (I := I) (M := M) g (v n)))) atTop
      (𝓝 (chartPulledIntegralCLM (I := I) (M := M) g α
            (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
            (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
            (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
            (smoothMulLp (I := I) (M := M) g
              (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
              (H1ComplToLp (I := I) (M := M) g u_h -
                laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩)) -
          (2 : ℝ) *
            chartPulledIntegralCLM (I := I) (M := M) g α
              (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
              (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
              (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
              (gradInnerCLM (I := I) (M := M) g
                (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h) -
          chartPulledIntegralCLM (I := I) (M := M) g α
            (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
            (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
            (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
            (smoothMulLp (I := I) (M := M) g
              (laplacianOfChartPOU (I := I) (M := M) g α)
              (H1ComplToLp (I := I) (M := M) g u_h)))) := by
    refine (h_lim_1.sub ?_).sub h_lim_3
    exact (tendsto_const_nhds.mul h_lim_2 : Tendsto _ _ _)
  have h_smooth_eq_n : ∀ n,
      chartPulledIntegralCLM (I := I) (M := M) g α
          (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
          (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
          (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
          (smoothMulLp (I := I) (M := M) g
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
            (smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical)) -
        (2 : ℝ) *
          chartPulledIntegralCLM (I := I) (M := M) g α
            (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
            (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
            (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
            (gradInnerSmooth (I := I) (M := M) g
              (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) (v n)) -
        chartPulledIntegralCLM (I := I) (M := M) g α
          (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
          (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
          (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
          (smoothMulLp (I := I) (M := M) g
            (laplacianOfChartPOU (I := I) (M := M) g α)
            (smoothToLp (I := I) (M := M) g (v n))) =
      chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
        (leibnizCompensatedSource (I := I) (M := M) g α
          (smoothToH1Compl (I := I) (M := M) g (v n))
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) (v n))) := by
    intro n
    rw [fHLeibniz_smoothToH1Compl (I := I) (M := M) g α (v n)]
    simp only [ContinuousLinearMap.map_sub, ContinuousLinearMap.map_smul,
      smul_eq_mul]
  have h_lhs_smooth_form : Tendsto (fun n =>
      chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
        (leibnizCompensatedSource (I := I) (M := M) g α
          (smoothToH1Compl (I := I) (M := M) g (v n))
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) (v n))))
      atTop
      (𝓝 (chartPulledIntegralCLM (I := I) (M := M) g α
            (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
            (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
            (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
            (smoothMulLp (I := I) (M := M) g
              (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
              (H1ComplToLp (I := I) (M := M) g u_h -
                laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩)) -
          (2 : ℝ) *
            chartPulledIntegralCLM (I := I) (M := M) g α
              (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
              (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
              (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
              (gradInnerCLM (I := I) (M := M) g
                (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h) -
          chartPulledIntegralCLM (I := I) (M := M) g α
            (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
            (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
            (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
            (smoothMulLp (I := I) (M := M) g
              (laplacianOfChartPOU (I := I) (M := M) g α)
              (H1ComplToLp (I := I) (M := M) g u_h)))) := by
    have h_fun_eq : (fun n =>
        chartPulledIntegralCLM (I := I) (M := M) g α
          (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
          (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
          (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
          (leibnizCompensatedSource (I := I) (M := M) g α
            (smoothToH1Compl (I := I) (M := M) g (v n))
            (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) (v n)))) =
        (fun n =>
          chartPulledIntegralCLM (I := I) (M := M) g α
              (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
              (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
              (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
              (smoothMulLp (I := I) (M := M) g
                (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
                (smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical)) -
            (2 : ℝ) *
              chartPulledIntegralCLM (I := I) (M := M) g α
                (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
                (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
                (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
                (gradInnerSmooth (I := I) (M := M) g
                  (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) (v n)) -
            chartPulledIntegralCLM (I := I) (M := M) g α
              (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
              (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
              (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
              (smoothMulLp (I := I) (M := M) g
                (laplacianOfChartPOU (I := I) (M := M) g α)
                (smoothToLp (I := I) (M := M) g (v n)))) := by
      funext n
      exact (h_smooth_eq_n n).symm
    rw [h_fun_eq]
    exact h_lhs_lim
  have h_rhs_eq : chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
        (leibnizCompensatedSource (I := I) (M := M) g α u_h hu_h) =
      chartPulledIntegralCLM (I := I) (M := M) g α
          (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
          (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
          (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
          (smoothMulLp (I := I) (M := M) g
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
            (H1ComplToLp (I := I) (M := M) g u_h -
              laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩)) -
        (2 : ℝ) *
          chartPulledIntegralCLM (I := I) (M := M) g α
            (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
            (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
            (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
            (gradInnerCLM (I := I) (M := M) g
              (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h) -
        chartPulledIntegralCLM (I := I) (M := M) g α
          (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
          (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
          (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
          (smoothMulLp (I := I) (M := M) g
            (laplacianOfChartPOU (I := I) (M := M) g α)
            (H1ComplToLp (I := I) (M := M) g u_h)) := by
    rw [fHLeibniz_def]
    simp only [ContinuousLinearMap.map_sub, ContinuousLinearMap.map_smul,
      smul_eq_mul]
  exact h_rhs_eq.symm

end LaplacianDomainVariationalIdentity
end Laplacian
end Analysis
end CalabiYau

end
