-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Intrinsic/Equivalence/ChartToIntrinsic/GradientPartition.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Intrinsic.Equivalence.Basic
public import CalabiYau.Analysis.Sobolev.Intrinsic.Lp.Basic
public import CalabiYau.Analysis.Sobolev.Approximation.Density.FirstOrder
public import CalabiYau.Analysis.Sobolev.Chart.RiemannianMeasureComparison
public import CalabiYau.Analysis.Sobolev.Manifold.Measure.UniformChartComparison
public import CalabiYau.Analysis.Sobolev.Manifold.Embedding.Subcritical
public import CalabiYau.Analysis.Sobolev.Manifold.Morrey.Basic
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Global.IntegrationByParts
public import CalabiYau.Geometry.Riemannian.Operator.Laplacian.Basic
public import CalabiYau.Geometry.Riemannian.Volume.Family.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

@[expose] public section

open CalabiYau.Riemannian

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace Sobolev
namespace Equivalence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open Sobolev.Chart
open Sobolev.Intrinsic
open Sobolev.IntrinsicLp

private lemma gradFun_eq_zero_off_tsupport_smooth
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {f : M → ℝ} (_hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : M}
    (hx : x ∉ tsupport f) :
    CalabiYau.Riemannian.gradFun (I := I) g f x =
      (0 : TangentSpace I x) := by
  apply CalabiYau.Riemannian.gradFun_eq_zero_of_mfderiv_eq_zero
  have hopen : IsOpen (tsupport f)ᶜ := (isClosed_tsupport _).isOpen_compl
  have hx_mem : x ∈ (tsupport f)ᶜ := hx
  have h_nhds : (tsupport f)ᶜ ∈ 𝓝 x := hopen.mem_nhds hx_mem
  have heqz : f =ᶠ[𝓝 x] (fun _ : M => (0 : ℝ)) := by
    filter_upwards [h_nhds] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  have hmfd : mfderiv I 𝓘(ℝ, ℝ) f x =
      mfderiv I 𝓘(ℝ, ℝ) (fun _ : M => (0 : ℝ)) x :=
    Filter.EventuallyEq.mfderiv_eq heqz
  rw [hmfd]
  exact mfderiv_const

noncomputable def gNormGrad
    (g : CalabiYau.SmoothRiemannianMetric I M)
    (u : M → ℝ) (x : M) : ℝ :=
  Real.sqrt
    (g.inner x
      (CalabiYau.Riemannian.gradFun
        (I := I) g u x)
      (CalabiYau.Riemannian.gradFun
        (I := I) g u x))

lemma gNormGrad_nonneg
    (g : CalabiYau.SmoothRiemannianMetric I M)
    (u : M → ℝ) (x : M) :
    0 ≤ gNormGrad (I := I) (M := M) g u x :=
  Real.sqrt_nonneg _

lemma gNormGrad_eq_zero_of_notMem_tsupport
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {x : M}
    (hx : x ∉ tsupport f) :
    gNormGrad (I := I) (M := M) g f x = 0 := by
  unfold gNormGrad
  rw [gradFun_eq_zero_off_tsupport_smooth (I := I) (M := M) g hf hx]
  simp

private lemma gradFun_eq_sum_gradFun_pou_mul
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (x : M) :
    CalabiYau.Riemannian.gradFun (I := I) g u x =
      ∑ α ∈ CalabiYau.RiemannianVolume.chartAtlasPOUFinset (I := I) (M := M),
        CalabiYau.Riemannian.gradFun (I := I) g
          (fun y : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) y * u y) x := by
  classical
  set S : Finset M :=
    CalabiYau.RiemannianVolume.chartAtlasPOUFinset (I := I) (M := M) with hS_def
  set h : M → M → ℝ := fun α y =>
    ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) y * u y with hh_def
  have hh_smooth : ∀ α ∈ S, ContMDiff I 𝓘(ℝ, ℝ) ∞ (h α) := fun α _ =>
    (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯).contMDiff.mul hu
  have hh_diff : ∀ α ∈ S, ∀ x : M, MDifferentiableAt I 𝓘(ℝ, ℝ) (h α) x :=
    fun α hα x => (hh_smooth α hα).mdifferentiable (by simp) x
  have hu_eq_local : u =ᶠ[𝓝 x] (fun y => ∑ α ∈ S, h α y) := by
    refine Filter.Eventually.of_forall (fun y => ?_)
    change u y = ∑ α ∈ S, h α y
    have h_sum : (∑ α ∈ S, h α y) = (∑ α ∈ S,
        ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) y) * u y := by
      rw [Finset.sum_mul]
    rw [h_sum]
    rw [Sobolev.Chart.chartAtlasPOU_finset_sum_eq_one
      (I := I) (M := M) y, one_mul]
  have h_mfderiv_eq : mfderiv I 𝓘(ℝ, ℝ) u x =
      mfderiv I 𝓘(ℝ, ℝ) (fun y => ∑ α ∈ S, h α y) x :=
    Filter.EventuallyEq.mfderiv_eq hu_eq_local
  have h_gradFun_eq : CalabiYau.Riemannian.gradFun
      (I := I) g u x =
      CalabiYau.Riemannian.gradFun (I := I) g
        (fun y => ∑ α ∈ S, h α y) x := by
    unfold CalabiYau.Riemannian.gradFun
    unfold CalabiYau.Riemannian.metricSharp
    rw [h_mfderiv_eq]
  rw [h_gradFun_eq]
  have heq : (fun y => ∑ i ∈ S, h i y) = ∑ i ∈ S, h i := by
    funext y
    simp only [Finset.sum_apply]
  rw [heq]
  exact gradientFun_sum (I := I) g S (fun i hi => hh_diff i hi x)

lemma gNormGrad_le_finset_sum_pou_mul
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (x : M) :
    gNormGrad (I := I) (M := M) g u x ≤
      ∑ α ∈ CalabiYau.RiemannianVolume.chartAtlasPOUFinset (I := I) (M := M),
        gNormGrad (I := I) (M := M) g
          (fun y : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) y * u y) x := by
  classical
  unfold gNormGrad
  rw [gradFun_eq_sum_gradFun_pou_mul (I := I) (M := M) g hu x]
  set v : M → TangentSpace I x := fun α =>
    CalabiYau.Riemannian.gradFun (I := I) g
      (fun y : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) y * u y) x with hv_def
  set S : Finset M :=
    CalabiYau.RiemannianVolume.chartAtlasPOUFinset (I := I) (M := M) with hS_def
  have hg_ip : ∀ v : TangentSpace I x, 0 ≤ g.inner x v v := by
    intro v
    by_cases hv : v = 0
    · rw [hv]
      simp [(g.inner x).map_zero]
    · exact (g.pos x v hv).le
  have h_triangle : ∀ S' : Finset M, ∀ w : M → TangentSpace I x,
      Real.sqrt (g.inner x (∑ α ∈ S', w α) (∑ α ∈ S', w α)) ≤
        ∑ α ∈ S', Real.sqrt (g.inner x (w α) (w α)) := by
    intro S' w
    classical
    induction S' using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      rw [show g.inner x (0 : TangentSpace I x) (0 : TangentSpace I x) = 0 from by
        have h := (g.inner x).map_zero
        simp [h]]
      rw [Real.sqrt_zero]
    | insert α₀ S₀ hα₀_notMem ih =>
      rw [Finset.sum_insert hα₀_notMem, Finset.sum_insert hα₀_notMem]
      set a : TangentSpace I x := w α₀
      set b : TangentSpace I x := ∑ α ∈ S₀, w α
      have hsym : g.inner x a b = g.inner x b a := g.symm x a b
      have h_innerab_sq : (g.inner x a b)^2 ≤
          g.inner x a a * g.inner x b b := by
        have h_expand : ∀ t : ℝ, g.inner x (a + t • b) (a + t • b) =
            g.inner x a a + 2 * t * g.inner x a b + t^2 * g.inner x b b := by
          intro t
          have h1 : g.inner x (a + t • b) (a + t • b) =
              g.inner x a (a + t • b) + g.inner x (t • b) (a + t • b) := by
            have := (g.inner x).map_add a (t • b)
            have h_apply : ((g.inner x).map_add a (t • b)).symm =
              ((g.inner x).map_add a (t • b)).symm := rfl
            rw [show ((g.inner x) (a + t • b)) =
                ((g.inner x) a) + ((g.inner x) (t • b)) from
              (g.inner x).map_add a (t • b)]
            simp [add_apply]
          have h2 : g.inner x a (a + t • b) =
              g.inner x a a + t * g.inner x a b := by
            have h_dist : (g.inner x a) (a + t • b) =
                (g.inner x a) a + (g.inner x a) (t • b) :=
              (g.inner x a).map_add a (t • b)
            have h_smul : (g.inner x a) (t • b) = t * (g.inner x a) b := by
              rw [(g.inner x a).map_smul, smul_eq_mul]
            rw [h_dist, h_smul]
          have h3 : g.inner x (t • b) (a + t • b) =
              t * g.inner x b a + t^2 * g.inner x b b := by
            have h_smul1 : (g.inner x) (t • b) = t • ((g.inner x) b) :=
              (g.inner x).map_smul t b
            rw [h_smul1]
            change t * (g.inner x b) (a + t • b) =
              t * g.inner x b a + t^2 * g.inner x b b
            rw [(g.inner x b).map_add]
            rw [(g.inner x b).map_smul]
            simp [smul_eq_mul]
            ring
          rw [h1, h2, h3]
          rw [hsym]
          ring
        have h_polynom : ∀ t : ℝ, 0 ≤
            g.inner x a a + 2 * t * g.inner x a b + t^2 * g.inner x b b := fun t => by
          rw [← h_expand t]; exact hg_ip _
        have h_innerbb_nn : 0 ≤ g.inner x b b := hg_ip b
        have h_inneraa_nn : 0 ≤ g.inner x a a := hg_ip a
        by_cases h_bb_zero : g.inner x b b = 0
        · have h_zero : g.inner x a b = 0 := by
            by_contra h_ne
            set t₀ : ℝ := -(g.inner x a a + 1) / (2 * g.inner x a b)
            have h_poly_t₀ := h_polynom t₀
            rw [h_bb_zero] at h_poly_t₀
            have h_simp : g.inner x a a + 2 * t₀ * g.inner x a b + t₀^2 * 0 =
                g.inner x a a + 2 * t₀ * g.inner x a b := by ring
            rw [h_simp] at h_poly_t₀
            have h_2ne : 2 * g.inner x a b ≠ 0 := by
              intro h2
              have : g.inner x a b = 0 := by linarith
              exact h_ne this
            have h_eval : 2 * t₀ * g.inner x a b = -(g.inner x a a + 1) := by
              change 2 * (-(g.inner x a a + 1) / (2 * g.inner x a b)) * g.inner x a b =
                -(g.inner x a a + 1)
              field_simp
            linarith
          rw [h_zero]
          have hbb_nn : 0 ≤ g.inner x a a * g.inner x b b :=
            mul_nonneg h_inneraa_nn h_innerbb_nn
          linarith [sq_nonneg (g.inner x a b), h_zero]
        · have h_bb_pos : 0 < g.inner x b b :=
            lt_of_le_of_ne h_innerbb_nn (Ne.symm h_bb_zero)
          set t₀ : ℝ := -g.inner x a b / g.inner x b b
          have h_poly_t₀ := h_polynom t₀
          have h_eval : g.inner x a a + 2 * t₀ * g.inner x a b + t₀^2 * g.inner x b b =
              g.inner x a a - (g.inner x a b)^2 / g.inner x b b := by
            change g.inner x a a + 2 * (-g.inner x a b / g.inner x b b) * g.inner x a b +
                (-g.inner x a b / g.inner x b b)^2 * g.inner x b b =
              g.inner x a a - (g.inner x a b)^2 / g.inner x b b
            field_simp
            ring
          rw [h_eval] at h_poly_t₀
          have h_step : (g.inner x a b)^2 / g.inner x b b ≤ g.inner x a a := by linarith
          rw [div_le_iff₀ h_bb_pos] at h_step
          linarith
      have h_a_nn : 0 ≤ g.inner x a a := hg_ip a
      have h_b_nn : 0 ≤ g.inner x b b := hg_ip b
      have h_sqrt_ab_le : Real.sqrt ((g.inner x a b)^2) ≤
          Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b) := by
        rw [show Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b) =
            Real.sqrt (g.inner x a a * g.inner x b b) from
          (Real.sqrt_mul h_a_nn _).symm]
        exact Real.sqrt_le_sqrt h_innerab_sq
      have h_abs_ab : |g.inner x a b| = Real.sqrt ((g.inner x a b)^2) := by
        rw [Real.sqrt_sq_eq_abs]
      have h_inner_ab_le : g.inner x a b ≤
          Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b) :=
        le_trans (le_abs_self _) (h_abs_ab ▸ h_sqrt_ab_le)
      have h_apb_eq : g.inner x (a + b) (a + b) =
          g.inner x a a + 2 * g.inner x a b + g.inner x b b := by
        have h_step : g.inner x (a + b) (a + b) =
            g.inner x a (a + b) + g.inner x b (a + b) := by
          have h1 : (g.inner x) (a + b) = (g.inner x) a + (g.inner x) b :=
            (g.inner x).map_add a b
          calc (g.inner x (a + b)) (a + b)
              = ((g.inner x) a + (g.inner x) b) (a + b) := by rw [h1]
            _ = (g.inner x) a (a + b) + (g.inner x) b (a + b) := rfl
        rw [h_step]
        rw [(g.inner x a).map_add, (g.inner x b).map_add]
        rw [hsym]
        ring
      have h_apb_nn : 0 ≤ g.inner x (a + b) (a + b) := hg_ip (a + b)
      have h_rhs_sq_nn : (0 : ℝ) ≤ Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b) :=
        add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      have h_target : g.inner x (a + b) (a + b) ≤
          (Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b))^2 := by
        rw [h_apb_eq]
        have h_sqrt_a : Real.sqrt (g.inner x a a)^2 = g.inner x a a :=
          Real.sq_sqrt h_a_nn
        have h_sqrt_b : Real.sqrt (g.inner x b b)^2 = g.inner x b b :=
          Real.sq_sqrt h_b_nn
        nlinarith only [h_inner_ab_le, h_sqrt_a, h_sqrt_b,
          Real.sqrt_nonneg (g.inner x a a), Real.sqrt_nonneg (g.inner x b b)]
      have h_apb_sqrt_le : Real.sqrt (g.inner x (a + b) (a + b)) ≤
          Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b) := by
        have h := Real.sqrt_le_sqrt h_target
        rw [Real.sqrt_sq h_rhs_sq_nn] at h
        exact h
      refine h_apb_sqrt_le.trans ?_
      have h_b_le := ih
      have h_a_eq : Real.sqrt (g.inner x a a) =
          Real.sqrt (g.inner x (w α₀) (w α₀)) := by rw [show a = w α₀ from rfl]
      have h_b_eq : Real.sqrt (g.inner x b b) =
          Real.sqrt (g.inner x (∑ α ∈ S₀, w α) (∑ α ∈ S₀, w α)) := by
        rw [show b = ∑ α ∈ S₀, w α from rfl]
      linarith
  exact h_triangle S v

end Equivalence
end Sobolev
