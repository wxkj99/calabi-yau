-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Operator/SmoothBridge.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Operator.DirichletForm
public import CalabiYau.Geometry.Riemannian.Metric.PointwiseInner.Bounds
public import CalabiYau.Geometry.Riemannian.Operator.Gradient.Basic
public import CalabiYau.Analysis.Elliptic.Operator.Variational

@[expose] public section
open CalabiYau.Riemannian

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Function
open scoped Manifold Topology ContDiff ENNReal NNReal Matrix BigOperators
  RealInnerProductSpace InnerProductSpace

namespace CalabiYau
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open Sobolev.IntrinsicH1Lp

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

noncomputable def SmoothScalar.oneSubLapClassical {g : SmoothRiemannianMetric I M}
    (u : SmoothScalar g) : SmoothScalar g where
  toFun := u.toFun - ΔG (I := I) g ⟨u.toFun, u.smooth⟩
  smooth := u.smooth.sub (Δ_g_contMDiff (I := I) g ⟨u.toFun, u.smooth⟩)

omit [CompactSpace M] in
noncomputable def SmoothScalar.laplacian {g : SmoothRiemannianMetric I M}
    (u : SmoothScalar g) : SmoothScalar g where
  toFun := ΔG (I := I) g ⟨u.toFun, u.smooth⟩
  smooth := Δ_g_contMDiff (I := I) g ⟨u.toFun, u.smooth⟩

omit [CompactSpace M] in
@[simp] lemma SmoothScalar.laplacian_toFun
    {g : SmoothRiemannianMetric I M} (u : SmoothScalar g) :
    u.laplacian.toFun = ΔG (I := I) g ⟨u.toFun, u.smooth⟩ := rfl

omit [CompactSpace M] in
@[simp] lemma SmoothScalar.oneSubLapClassical_toFun
    {g : SmoothRiemannianMetric I M} (u : SmoothScalar g) :
    (u.oneSubLapClassical).toFun =
      u.toFun - ΔG (I := I) g ⟨u.toFun, u.smooth⟩ := rfl

omit [CompactSpace M] in
@[simp] lemma SmoothScalar.sub_oneSubLapClassical
    {g : SmoothRiemannianMetric I M} (u : SmoothScalar g) :
    u - u.oneSubLapClassical = u.laplacian := by
  apply SmoothScalar.ext
  funext x
  simp [SmoothScalar.oneSubLapClassical_toFun]

theorem smoothScalarH1Inner_eq_integral_oneSubLap_mul
    {g : SmoothRiemannianMetric I M}
    (u v : SmoothScalar g) :
    smoothScalarH1Inner (I := I) (M := M) u v =
      ∫ x, (u.toFun x - ΔG (I := I) g ⟨u.toFun, u.smooth⟩ x) * v.toFun x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  unfold smoothScalarH1Inner
  have : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have hv_cs : HasCompactSupport v.toFun := HasCompactSupport.of_compactSpace _
  have hu_cs : HasCompactSupport u.toFun := HasCompactSupport.of_compactSpace _
  have hgreen :
      ∫ x, g.inner x ((gradG (I := I) g ⟨v.toFun, v.smooth⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((gradG (I := I) g ⟨u.toFun, u.smooth⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        -∫ x, v.toFun x * ΔG (I := I) g ⟨u.toFun, u.smooth⟩ x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    green_first_integral_inner_grad_eq_neg_integral_smul_laplacian (I := I) g v.smooth u.smooth
      hu_cs
  have hsymm :
      (∫ x, g.inner x ((gradG (I := I) g ⟨u.toFun, u.smooth⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((gradG (I := I) g ⟨v.toFun, v.smooth⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ x, g.inner x ((gradG (I := I) g ⟨v.toFun, v.smooth⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((gradG (I := I) g ⟨u.toFun, u.smooth⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x
    exact g.symm x _ _
  rw [hsymm, hgreen]
  have hΔu_cont : Continuous (ΔG (I := I) g ⟨u.toFun, u.smooth⟩) :=
    (Δ_g_contMDiff (I := I) g ⟨u.toFun, u.smooth⟩).continuous
  have hu_cont : Continuous u.toFun := u.smooth.continuous
  have hv_cont : Continuous v.toFun := v.smooth.continuous
  have h_uv : Integrable (fun x : M => u.toFun x * v.toFun x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    (hu_cont.mul hv_cont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h_vΔu : Integrable (fun x : M => v.toFun x * ΔG (I := I) g ⟨u.toFun, u.smooth⟩ x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    (hv_cont.mul hΔu_cont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpt : ∀ x : M,
      (u.toFun x - ΔG (I := I) g ⟨u.toFun, u.smooth⟩ x) * v.toFun x =
        u.toFun x * v.toFun x - v.toFun x * ΔG (I := I) g ⟨u.toFun, u.smooth⟩ x := by
    intro x; ring
  rw [show (fun x : M =>
      (u.toFun x - ΔG (I := I) g ⟨u.toFun, u.smooth⟩ x) * v.toFun x) =
      (fun x : M =>
        u.toFun x * v.toFun x - v.toFun x * ΔG (I := I) g ⟨u.toFun, u.smooth⟩ x) from
      funext hpt]
  rw [integral_sub h_uv h_vΔu]
  ring

theorem smoothScalarH1Inner_eq_lpInner_oneSubLap
    {g : SmoothRiemannianMetric I M} (u v : SmoothScalar g) :
    smoothScalarH1Inner (I := I) (M := M) u v =
      ⟪smoothToLp (I := I) (M := M) g u.oneSubLapClassical,
        smoothToLp (I := I) (M := M) g v⟫_ℝ := by
  rw [smoothScalarH1Inner_eq_integral_oneSubLap_mul]
  rw [L2.inner_def
    (smoothToLp (I := I) (M := M) g u.oneSubLapClassical)
    (smoothToLp (I := I) (M := M) g v)]
  have hae_lhs : (smoothToLp (I := I) (M := M) g u.oneSubLapClassical :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
      u.oneSubLapClassical.toFun :=
    MemLp.coeFn_toLp u.oneSubLapClassical.memLp_two
  have hae_rhs : (smoothToLp (I := I) (M := M) g v :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
      v.toFun :=
    MemLp.coeFn_toLp v.memLp_two
  refine integral_congr_ae ?_
  filter_upwards [hae_lhs, hae_rhs] with x hl hr
  rw [hl, hr]
  rw [SmoothScalar.oneSubLapClassical_toFun]
  change (u.toFun x - ΔG (I := I) g ⟨u.toFun, u.smooth⟩ x) * v.toFun x =
    @inner ℝ _ _ ((u.toFun - ΔG (I := I) g ⟨u.toFun, u.smooth⟩) x) (v.toFun x)
  rw [Pi.sub_apply]
  rw [show @inner ℝ _ _ (u.toFun x - ΔG (I := I) g ⟨u.toFun, u.smooth⟩ x) (v.toFun x) =
      v.toFun x * (u.toFun x - ΔG (I := I) g ⟨u.toFun, u.smooth⟩ x) from
      RCLike.inner_apply _ _]
  ring

lemma inner_smoothToH1Compl_smoothToH1Compl
    {g : SmoothRiemannianMetric I M} (u v : SmoothScalar g) :
    ⟪smoothToH1Compl (I := I) (M := M) g u,
        smoothToH1Compl (I := I) (M := M) g v⟫_ℝ =
      smoothScalarH1Inner (I := I) (M := M) u v := by
  unfold smoothToH1Compl
  change ⟪((u : H1Compl g) : H1Compl g),
        ((v : H1Compl g) : H1Compl g)⟫_ℝ =
      smoothScalarH1Inner (I := I) (M := M) u v
  rw [UniformSpace.Completion.inner_coe (𝕜 := ℝ) u v]
  rfl

lemma h1ComplBilin_smoothToH1Compl_smoothToH1Compl
    {g : SmoothRiemannianMetric I M} (u v : SmoothScalar g) :
    h1ComplBilin (I := I) (M := M) g
        (smoothToH1Compl (I := I) (M := M) g u)
        (smoothToH1Compl (I := I) (M := M) g v) =
      smoothScalarH1Inner (I := I) (M := M) u v := by
  rw [h1ComplBilin_apply]
  exact inner_smoothToH1Compl_smoothToH1Compl u v

theorem smoothScalar_bilin_eq_lpFunctional_smooth
    {g : SmoothRiemannianMetric I M}
    (u v : SmoothScalar g) :
    h1ComplBilin (I := I) (M := M) g
        (smoothToH1Compl (I := I) (M := M) g u)
        (smoothToH1Compl (I := I) (M := M) g v) =
      lpFunctionalCLM (I := I) (M := M) g
        (smoothToLp (I := I) (M := M) g u.oneSubLapClassical)
        (smoothToH1Compl (I := I) (M := M) g v) := by
  rw [h1ComplBilin_smoothToH1Compl_smoothToH1Compl,
    smoothScalarH1Inner_eq_lpInner_oneSubLap]
  rw [lpFunctionalCLM_apply, h1ComplToLp_smoothToH1Compl]
  exact real_inner_comm _ _

theorem denseRange_smoothToH1Compl (g : SmoothRiemannianMetric I M) :
    DenseRange (smoothToH1Compl (I := I) (M := M) g) := by
  unfold smoothToH1Compl
  rw [show (UniformSpace.Completion.toComplL : SmoothScalar g → H1Compl g) =
      ((↑) : SmoothScalar g → UniformSpace.Completion (SmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

theorem smoothToH1Compl_bilin_eq_lpFunctional
    {g : SmoothRiemannianMetric I M}
    (u : SmoothScalar g) (w : H1Compl g) :
    h1ComplBilin (I := I) (M := M) g
        (smoothToH1Compl (I := I) (M := M) g u) w =
      lpFunctionalCLM (I := I) (M := M) g
        (smoothToLp (I := I) (M := M) g u.oneSubLapClassical) w := by
  let L : H1Compl g → ℝ := fun w =>
    h1ComplBilin (I := I) (M := M) g (smoothToH1Compl (I := I) (M := M) g u) w
  let R : H1Compl g → ℝ := fun w =>
    lpFunctionalCLM (I := I) (M := M) g
      (smoothToLp (I := I) (M := M) g u.oneSubLapClassical) w
  change L w = R w
  have hL_cont : Continuous L :=
    (h1ComplBilin (I := I) (M := M) g
      (smoothToH1Compl (I := I) (M := M) g u)).continuous
  have hR_cont : Continuous R :=
    (lpFunctionalCLM (I := I) (M := M) g
      (smoothToLp (I := I) (M := M) g u.oneSubLapClassical)).continuous
  have hLR_smooth :
      L ∘ (smoothToH1Compl (I := I) (M := M) g) =
        R ∘ (smoothToH1Compl (I := I) (M := M) g) := by
    funext v
    exact smoothScalar_bilin_eq_lpFunctional_smooth u v
  exact congrFun
    ((denseRange_smoothToH1Compl (I := I) (M := M) g).equalizer
      hL_cont hR_cont hLR_smooth) w

theorem smoothToH1Compl_eq_resolvent_oneSubLap
    {g : SmoothRiemannianMetric I M}
    (u : SmoothScalar g) :
    smoothToH1Compl (I := I) (M := M) g u =
      resolvent (I := I) (M := M) g
        (smoothToLp (I := I) (M := M) g u.oneSubLapClassical) := by
  apply ext_inner_right ℝ
  intro w
  rw [show ⟪smoothToH1Compl (I := I) (M := M) g u, w⟫_ℝ =
        h1ComplBilin (I := I) (M := M) g
          (smoothToH1Compl (I := I) (M := M) g u) w from rfl]
  rw [smoothToH1Compl_bilin_eq_lpFunctional u w]
  rw [resolvent_inner_eq_lpFunctional]
  rw [lpFunctionalCLM_apply]

end Laplacian
end Analysis
end CalabiYau

end
