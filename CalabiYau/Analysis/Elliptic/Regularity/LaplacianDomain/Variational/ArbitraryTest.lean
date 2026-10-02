-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/LaplacianDomain/Variational/ArbitraryTest.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.LaplacianDomain.Variational.SmoothApproximation
public import CalabiYau.Analysis.Sobolev.Intrinsic.Equivalence.IntrinsicToChart.ComponentNormBound
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Global.PartitionOfUnity
public import CalabiYau.Geometry.Riemannian.Operator.Laplacian.Basic
public import CalabiYau.Geometry.Riemannian.Operator.Gradient.Basic

@[expose] public section
open CalabiYau.Riemannian

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace CalabiYau
namespace Analysis
namespace Laplacian
namespace LaplacianDomainVariationalLimitGeneral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Laplacian.MetricExtension
  hiding chartTargetEuclid
open CalabiYau.Analysis.Laplacian.LaplacianDomainVariationalLimit
open Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [CompactSpace M] in
theorem gradFun_smul_smooth_eq_pointwise
    (g : SmoothRiemannianMetric I M)
    {φ v : M → ℝ}
    (hφ : ContMDiff I 𝓘(ℝ, ℝ) ∞ φ)
    (hv : ContMDiff I 𝓘(ℝ, ℝ) ∞ v) (x : M) :
    gradFun (I := I) g (fun y : M => φ y * v y) x =
      φ x • gradFun (I := I) g v x + v x • gradFun (I := I) g φ x := by
  classical
  have hρ_md := hφ.mdifferentiable (by simp) x
  have hu_md := hv.mdifferentiable (by simp) x
  apply CalabiYau.Riemannian.metricFlatLinear_injective
    (I := I) g x
  ext w
  change g.inner x
      (gradFun (I := I) g (fun y : M => φ y * v y) x) w =
    g.inner x (φ x • gradFun (I := I) g v x + v x • gradFun (I := I) g φ x) w
  rw [inner_gradFun (I := I) g _ x w]
  have h_fun_eq : (fun y : M => φ y * v y) = φ * v := by funext y; rfl
  set d_φ : TangentSpace I x →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) φ x with hd_φ_def
  set d_v : TangentSpace I x →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) v x with hd_v_def
  have h_mfderiv_mul : mfderiv I 𝓘(ℝ, ℝ) (fun y : M => φ y * v y) x w =
      φ x * d_v w + v x * d_φ w := by
    rw [h_fun_eq]
    have h_φ_at : HasMFDerivAt I 𝓘(ℝ, ℝ) φ x d_φ := hρ_md.hasMFDerivAt
    have h_v_at : HasMFDerivAt I 𝓘(ℝ, ℝ) v x d_v := hu_md.hasMFDerivAt
    have hAt : HasMFDerivAt I 𝓘(ℝ, ℝ) (φ * v) x
        ((φ x • d_v + v x • d_φ : TangentSpace I x →L[ℝ] ℝ)) :=
      h_φ_at.mul h_v_at
    rw [hAt.mfderiv]
    change ((φ x • d_v + v x • d_φ : TangentSpace I x →L[ℝ] ℝ)) w =
        φ x * d_v w + v x * d_φ w
    rw [add_apply, smul_apply,
        smul_apply]
    simp [smul_eq_mul]
  rw [h_mfderiv_mul]
  symm
  have h_add : (g.inner x)
      (φ x • gradFun (I := I) g v x +
       v x • gradFun (I := I) g φ x) =
      (g.inner x) (φ x • gradFun (I := I) g v x) +
      (g.inner x) (v x • gradFun (I := I) g φ x) :=
    (g.inner x).map_add _ _
  change ((g.inner x)
      (φ x • gradFun (I := I) g v x +
       v x • gradFun (I := I) g φ x)) w =
    φ x * d_v w + v x * d_φ w
  rw [h_add]
  rw [show (((g.inner x) (φ x • gradFun (I := I) g v x)) +
      ((g.inner x) (v x • gradFun (I := I) g φ x))) w =
      ((g.inner x) (φ x • gradFun (I := I) g v x)) w +
      ((g.inner x) (v x • gradFun (I := I) g φ x)) w from rfl]
  rw [(g.inner x).map_smul, (g.inner x).map_smul]
  rw [show (φ x • (g.inner x) (gradFun (I := I) g v x)) w =
      φ x • ((g.inner x) (gradFun (I := I) g v x)) w from rfl]
  rw [show (v x • (g.inner x) (gradFun (I := I) g φ x)) w =
      v x • ((g.inner x) (gradFun (I := I) g φ x)) w from rfl]
  simp only [smul_eq_mul]
  rw [show ((g.inner x) (gradFun (I := I) g v x)) w = d_v w from by
    rw [hd_v_def]
    exact inner_gradFun (I := I) g v x w]
  rw [show ((g.inner x) (gradFun (I := I) g φ x)) w = d_φ w from by
    rw [hd_φ_def]
    exact inner_gradFun (I := I) g φ x w]

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] in
private lemma grad_g_smul_smooth_section_eq
    (g : SmoothRiemannianMetric I M)
    {φ v : M → ℝ}
    (hφ : ContMDiff I 𝓘(ℝ, ℝ) ∞ φ)
    (hv : ContMDiff I 𝓘(ℝ, ℝ) ∞ v) :
    (gradG (I := I) g
        (⟨φ * v, hφ.mul hv⟩ : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯) :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) =
      smoothSmul (I := I) φ hφ
          (gradG (I := I) g (⟨v, hv⟩ : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯) :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) +
        smoothSmul (I := I) v hv
          (gradG (I := I) g (⟨φ, hφ⟩ : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯) :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) := by
  let φvMap : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯ := ⟨φ * v, hφ.mul hv⟩
  let vMap : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯ := ⟨v, hv⟩
  let φMap : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯ := ⟨φ, hφ⟩
  change (gradG (I := I) g φvMap :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) =
    smoothSmul (I := I) φ hφ
        (gradG (I := I) g vMap :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) +
      smoothSmul (I := I) v hv
        (gradG (I := I) g φMap :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
  ext x
  rw [ContMDiffSection.coe_add]
  rw [grad_g_apply]
  change gradFun (I := I) g (fun y : M => φ y * v y) x =
    (smoothSmul (I := I) φ hφ
        (gradG (I := I) g vMap :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)) x +
      (smoothSmul (I := I) v hv
        (gradG (I := I) g φMap :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)) x
  rw [smoothSmul_apply, smoothSmul_apply]
  simp only [grad_g_apply]
  exact gradFun_smul_smooth_eq_pointwise (I := I) (M := M) g hφ hv x

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] in
private lemma tangentSectionAction_grad_g_eq_inner_grad
    (g : SmoothRiemannianMetric I M)
    {φ v : M → ℝ}
    (_hφ : ContMDiff I 𝓘(ℝ, ℝ) ∞ φ)
    (hv : ContMDiff I 𝓘(ℝ, ℝ) ∞ v) (x : M) :
    tangentSectionAction (I := I)
        (gradG (I := I) g (⟨v, hv⟩ : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯) :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) φ x =
      g.inner x (gradFun (I := I) g φ x) (gradFun (I := I) g v x) := by
  let vMap : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯ := ⟨v, hv⟩
  change tangentSectionAction (I := I)
      (gradG (I := I) g vMap :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) φ x = _
  unfold tangentSectionAction
  rw [show ((gradG (I := I) g vMap :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
        gradFun (I := I) g v x from
      grad_g_apply (I := I) g vMap x]
  exact (inner_gradFun (I := I) g φ x _).symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [T2Space M] in
theorem Δ_g_smul_eq
    (g : SmoothRiemannianMetric I M)
    {φ v : M → ℝ}
    (hφ : ContMDiff I 𝓘(ℝ, ℝ) ∞ φ)
    (hv : ContMDiff I 𝓘(ℝ, ℝ) ∞ v) (x : M) :
    ΔG (I := I) g
        (⟨φ * v, hφ.mul hv⟩ : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯) x =
      φ x * ΔG (I := I) g
        (⟨v, hv⟩ : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯) x +
        2 * g.inner x (gradFun (I := I) g φ x) (gradFun (I := I) g v x) +
        v x * ΔG (I := I) g
          (⟨φ, hφ⟩ : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯) x := by
  classical
  let φvMap : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯ := ⟨φ * v, hφ.mul hv⟩
  let vMap : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯ := ⟨v, hv⟩
  let φMap : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯ := ⟨φ, hφ⟩
  change ΔG (I := I) g φvMap x =
    φ x * ΔG (I := I) g vMap x +
      2 * g.inner x (gradFun (I := I) g φ x) (gradFun (I := I) g v x) +
      v x * ΔG (I := I) g φMap x
  rw [Δ_g_def]
  rw [grad_g_smul_smooth_section_eq (I := I) (M := M) g hφ hv]
  rw [divergence_g_add (I := I) g]
  rw [divergence_g_smoothSmul (I := I) g φ hφ _ x]
  rw [divergence_g_smoothSmul (I := I) g v hv _ x]
  rw [tangentSectionAction_grad_g_eq_inner_grad (I := I) (M := M) g hφ hv x]
  rw [tangentSectionAction_grad_g_eq_inner_grad (I := I) (M := M) g hv hφ x]
  rw [show divergenceG (I := I) g
          (gradG (I := I) g vMap) x =
        ΔG (I := I) g vMap x from
      (Δ_g_def (I := I) g vMap x).symm,
      show divergenceG (I := I) g
          (gradG (I := I) g φMap) x =
        ΔG (I := I) g φMap x from
      (Δ_g_def (I := I) g φMap x).symm]
  have h_symm : g.inner x (gradFun (I := I) g v x) (gradFun (I := I) g φ x) =
      g.inner x (gradFun (I := I) g φ x) (gradFun (I := I) g v x) :=
    g.symm x _ _
  rw [h_symm]
  ring

omit [NeZero (Module.finrank ℝ E)] in
theorem pouScalar_oneSubLapClassical_pointwise_leibniz
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) (x : M) :
    (pouScalar (I := I) (M := M) α v).oneSubLapClassical.toFun x =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
          v.oneSubLapClassical.toFun x -
        2 * g.inner x (gradFun (I := I) g
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
          (gradFun (I := I) g v.toFun x) -
        v.toFun x *
          ΔG (I := I) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x := by
  classical
  set ρα : M → ℝ := ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hρα_def
  set V : M → ℝ := v.toFun with hV_def
  have hρα_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ ρα :=
    (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff
  have hV_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ V := v.smooth
  have h_pou_toFun :
      (pouScalar (I := I) (M := M) α v).toFun =
        fun y : M => ρα y * V y := rfl
  change (pouScalar (I := I) (M := M) α v).toFun x -
      ΔG (I := I) g ⟨(pouScalar (I := I) (M := M) α v).toFun,
        (pouScalar (I := I) (M := M) α v).smooth⟩ x =
    ρα x * v.oneSubLapClassical.toFun x -
      2 * g.inner x (gradFun (I := I) g
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
        (gradFun (I := I) g v.toFun x) -
      v.toFun x *
        ΔG (I := I) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x
  have h_lap_eq : ΔG (I := I) g ⟨(pouScalar (I := I) (M := M) α v).toFun,
    (pouScalar (I := I) (M := M) α v).smooth⟩ x =
        ΔG (I := I) g ⟨ρα * V, hρα_smooth.mul hV_smooth⟩ x := rfl
  rw [h_lap_eq]
  rw [Δ_g_smul_eq (I := I) (M := M) g hρα_smooth hV_smooth x]
  rw [h_pou_toFun]
  change ρα x * V x -
      (ρα x * ΔG (I := I) g ⟨_, hV_smooth⟩ x +
        2 * g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g V x) +
        V x * ΔG (I := I) g ⟨_, hρα_smooth⟩ x) =
    ρα x * (V x - ΔG (I := I) g ⟨v.toFun, v.smooth⟩ x) -
      2 * g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g V x) -
      V x * ΔG (I := I) g ⟨_, hρα_smooth⟩ x
  have h_lap_v_eq :
      ΔG (I := I) g ⟨v.toFun, v.smooth⟩ x = ΔG (I := I) g ⟨_, hV_smooth⟩ x := rfl
  rw [h_lap_v_eq]
  ring

omit [NeZero (Module.finrank ℝ E)] in
private lemma fHLeibniz_smoothCase_coeFn_aeEq
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    ((leibnizCompensatedSource (I := I) (M := M) g α
          (smoothToH1Compl (I := I) (M := M) g v)
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)
          : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
        : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
          v.oneSubLapClassical.toFun x -
        2 * g.inner x (gradFun (I := I) g
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
          (gradFun (I := I) g v.toFun x) -
        v.toFun x *
          ΔG (I := I) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x) := by
  classical
  rw [fHLeibniz_smoothToH1Compl (I := I) (M := M) g α v]
  set ρα : C^∞⟮I, M; ℝ⟯ := chartAtlasPOU I M α with hρα_def
  set ρα_fun : M → ℝ := (ρα : M → ℝ) with hρα_fun_def
  set Δρα : C^∞⟮I, M; ℝ⟯ := laplacianOfChartPOU (I := I) (M := M) g α
    with hΔρα_def
  have h_sub1 := MeasureTheory.Lp.coeFn_sub
      ((smoothMulLp (I := I) (M := M) g ρα
          (smoothToLp (I := I) (M := M) g v.oneSubLapClassical)
        - (2 : ℝ) • gradInnerSmooth (I := I) (M := M) g ρα v))
      (smoothMulLp (I := I) (M := M) g Δρα
          (smoothToLp (I := I) (M := M) g v))
  have h_sub2 := MeasureTheory.Lp.coeFn_sub
      (smoothMulLp (I := I) (M := M) g ρα
        (smoothToLp (I := I) (M := M) g v.oneSubLapClassical))
      ((2 : ℝ) • gradInnerSmooth (I := I) (M := M) g ρα v)
  have h_mul1 := smoothMulLp_apply_coeFn (I := I) (M := M) g ρα
    (smoothToLp (I := I) (M := M) g v.oneSubLapClassical)
  have h_mul2 := smoothMulLp_apply_coeFn (I := I) (M := M) g Δρα
    (smoothToLp (I := I) (M := M) g v)
  have h_smul := MeasureTheory.Lp.coeFn_smul (2 : ℝ)
    (gradInnerSmooth (I := I) (M := M) g ρα v)
  have h_grad := gradInnerSmooth_coeFn (I := I) (M := M) g ρα v
  have h_smoothToLp1 :
      ((smoothToLp (I := I) (M := M) g v.oneSubLapClassical
         : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g] v.oneSubLapClassical.toFun :=
    MemLp.coeFn_toLp v.oneSubLapClassical.memLp_two
  have h_smoothToLp2 :
      ((smoothToLp (I := I) (M := M) g v
         : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g] v.toFun :=
    MemLp.coeFn_toLp v.memLp_two
  filter_upwards [h_sub1, h_sub2, h_mul1, h_mul2, h_smul, h_grad, h_smoothToLp1,
    h_smoothToLp2] with x hx1 hx2 hx_mul1 hx_mul2 hx_smul hx_grad hx_lp1 hx_lp2
  rw [hx1]
  change ((smoothMulLp (I := I) (M := M) g ρα
            (smoothToLp (I := I) (M := M) g v.oneSubLapClassical) -
          (2 : ℝ) • gradInnerSmooth (I := I) (M := M) g ρα v
         : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x -
        ((smoothMulLp (I := I) (M := M) g Δρα
            (smoothToLp (I := I) (M := M) g v)
         : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x =
      ρα_fun x * v.oneSubLapClassical.toFun x -
        2 * g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g v.toFun x) -
        v.toFun x *
          ΔG (I := I) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x
  rw [hx2]
  change ((smoothMulLp (I := I) (M := M) g ρα
            (smoothToLp (I := I) (M := M) g v.oneSubLapClassical)
         : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x -
        (((2 : ℝ) • gradInnerSmooth (I := I) (M := M) g ρα v
         : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x -
        ((smoothMulLp (I := I) (M := M) g Δρα
            (smoothToLp (I := I) (M := M) g v)
         : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x =
      ρα_fun x * v.oneSubLapClassical.toFun x -
        2 * g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g v.toFun x) -
        v.toFun x *
          ΔG (I := I) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x
  rw [hx_mul1, hx_mul2, hx_smul]
  change ρα_fun x * ((smoothToLp (I := I) (M := M) g v.oneSubLapClassical
            : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x -
        ((2 : ℝ) • ((gradInnerSmooth (I := I) (M := M) g ρα v
            : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) x -
        (Δρα : M → ℝ) x *
          ((smoothToLp (I := I) (M := M) g v
            : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x =
      ρα_fun x * v.oneSubLapClassical.toFun x -
        2 * g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g v.toFun x) -
        v.toFun x *
          ΔG (I := I) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x
  rw [show ((2 : ℝ) • ((gradInnerSmooth (I := I) (M := M) g ρα v
            : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) x =
      (2 : ℝ) • ((gradInnerSmooth (I := I) (M := M) g ρα v
            : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x from rfl]
  rw [hx_grad, hx_lp1, hx_lp2]
  change ρα_fun x * v.oneSubLapClassical.toFun x -
        (2 : ℝ) • g.inner x (gradFun (I := I) g ρα x)
          (gradFun (I := I) g v.toFun x) -
        ΔG (I := I) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x * v.toFun x =
      ρα_fun x * v.oneSubLapClassical.toFun x -
        2 * g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g v.toFun x) -
        v.toFun x *
          ΔG (I := I) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x
  rw [smul_eq_mul]
  ring

omit [NeZero (Module.finrank ℝ E)] in
theorem pouScalar_oneSubLap_aeEq_fHLeibniz_smooth
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    (pouScalar (I := I) (M := M) α v).oneSubLapClassical.toFun =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      ((leibnizCompensatedSource (I := I) (M := M) g α
          (smoothToH1Compl (I := I) (M := M) g v)
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)
          : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
        : M → ℝ) := by
  classical
  have h := fHLeibniz_smoothCase_coeFn_aeEq (I := I) (M := M) g α v
  have h_pointwise : ∀ x : M,
      (pouScalar (I := I) (M := M) α v).oneSubLapClassical.toFun x =
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
            v.oneSubLapClassical.toFun x -
          2 * g.inner x (gradFun (I := I) g
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
            (gradFun (I := I) g v.toFun x) -
          v.toFun x *
            ΔG (I := I) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x :=
    pouScalar_oneSubLapClassical_pointwise_leibniz (I := I) (M := M) g α v
  refine Filter.EventuallyEq.trans (Filter.Eventually.of_forall h_pointwise) ?_
  exact h.symm

end LaplacianDomainVariationalLimitGeneral
end Laplacian
end Analysis
end CalabiYau

end
