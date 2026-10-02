-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/GradInner/CLM/Defs.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.LaplacianDomain.L2
public import CalabiYau.Geometry.Riemannian.Metric.PointwiseInner.Bounds
public import CalabiYau.Geometry.Riemannian.Operator.Gradient.NormSquared
public import Mathlib.Analysis.Normed.Operator.Extend

@[expose] public section
open CalabiYau.Riemannian
open CalabiYau.Laplacian

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
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

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩



variable [I.Boundaryless] in
lemma gradInnerSmooth_continuous
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) :
    Continuous (fun x : M =>
      g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g v.toFun x)) := by
  have h := TangentBundle.continuous_g_inner_of_smooth_sections (I := I) (M := M) g
    (gradG (I := I) g ρα) (gradG (I := I) g ⟨v.toFun, v.smooth⟩)
  refine h.congr ?_
  intro x
  change g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g v.toFun x) =
    g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g v.toFun x)
  rfl

section

variable [I.Boundaryless] [T2Space M] [CompactSpace M]
lemma gradInnerSmooth_memLp_two
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) :
    MemLp (fun x : M =>
        g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g v.toFun x)) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  have : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  exact (gradInnerSmooth_continuous (I := I) (M := M) g ρα v).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

noncomputable def gradInnerSmooth
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (gradInnerSmooth_memLp_two (I := I) (M := M) g ρα v).toLp _

lemma gradInnerSmooth_coeFn
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) :
    (gradInnerSmooth (I := I) (M := M) g ρα v :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => g.inner x (gradFun (I := I) g ρα x)
        (gradFun (I := I) g v.toFun x)) :=
  MemLp.coeFn_toLp _

end

lemma gradInnerSmooth_pt_add
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v w : SmoothScalar g) (x : M) :
    g.inner x (gradFun (I := I) g ρα x)
        (gradFun (I := I) g (v + w).toFun x) =
      g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g v.toFun x) +
        g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g w.toFun x) := by
  have hgrad_add : gradFun (I := I) g (v + w).toFun x =
      gradFun (I := I) g v.toFun x + gradFun (I := I) g w.toFun x := by
    have hfun : (v + w).toFun = v.toFun + w.toFun := rfl
    rw [hfun]
    exact gradFun_add (I := I) g (v.smooth.mdifferentiable (by simp) x)
      (w.smooth.mdifferentiable (by simp) x)
  rw [hgrad_add, ContinuousLinearMap.map_add]

variable [I.Boundaryless] in
lemma gradInnerSmooth_pt_smul
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (c : ℝ) (v : SmoothScalar g) (x : M) :
    g.inner x (gradFun (I := I) g ρα x)
        (gradFun (I := I) g (c • v).toFun x) =
      c * g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g v.toFun x) := by
  have hgrad_smul : gradFun (I := I) g (c • v).toFun x =
      c • gradFun (I := I) g v.toFun x := by
    have h := SmoothScalar.grad_g_smul_apply (I := I) (g := g) c v x
    change gradFun (I := I) g (c • v).toFun x =
      c • gradFun (I := I) g v.toFun x at h
    exact h
  rw [hgrad_smul]
  rw [ContinuousLinearMap.map_smul, smul_eq_mul]

section

variable [I.Boundaryless] [T2Space M] [CompactSpace M]
theorem gradInnerSmooth_add
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v w : SmoothScalar g) :
    gradInnerSmooth (I := I) (M := M) g ρα (v + w) =
      gradInnerSmooth (I := I) (M := M) g ρα v +
        gradInnerSmooth (I := I) (M := M) g ρα w := by
  apply MeasureTheory.Lp.ext
  have h_sum_coe := MeasureTheory.Lp.coeFn_add
    (gradInnerSmooth (I := I) (M := M) g ρα v)
    (gradInnerSmooth (I := I) (M := M) g ρα w)
  have h_lhs := gradInnerSmooth_coeFn (I := I) (M := M) g ρα (v + w)
  have h_v := gradInnerSmooth_coeFn (I := I) (M := M) g ρα v
  have h_w := gradInnerSmooth_coeFn (I := I) (M := M) g ρα w
  refine h_lhs.trans ?_
  refine EventuallyEq.symm ?_
  filter_upwards [h_sum_coe, h_v, h_w] with x h_sum h_v_eq h_w_eq
  rw [h_sum, Pi.add_apply, h_v_eq, h_w_eq]
  exact (gradInnerSmooth_pt_add (I := I) (M := M) g ρα v w x).symm

theorem gradInnerSmooth_smul
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (c : ℝ) (v : SmoothScalar g) :
    gradInnerSmooth (I := I) (M := M) g ρα (c • v) =
      c • gradInnerSmooth (I := I) (M := M) g ρα v := by
  apply MeasureTheory.Lp.ext
  have h_smul_coe := MeasureTheory.Lp.coeFn_smul c
    (gradInnerSmooth (I := I) (M := M) g ρα v)
  have h_lhs := gradInnerSmooth_coeFn (I := I) (M := M) g ρα (c • v)
  have h_v := gradInnerSmooth_coeFn (I := I) (M := M) g ρα v
  refine h_lhs.trans ?_
  refine EventuallyEq.symm ?_
  filter_upwards [h_smul_coe, h_v] with x h_smul h_v_eq
  rw [h_smul, Pi.smul_apply, h_v_eq, smul_eq_mul]
  exact (gradInnerSmooth_pt_smul (I := I) (M := M) g ρα c v x).symm

noncomputable def gradInnerSmoothLin
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) :
    SmoothScalar g →ₗ[ℝ] Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) where
  toFun v := gradInnerSmooth (I := I) (M := M) g ρα v
  map_add' v w := gradInnerSmooth_add (I := I) (M := M) g ρα v w
  map_smul' c v := gradInnerSmooth_smul (I := I) (M := M) g ρα c v

@[simp] lemma gradInnerSmoothLin_apply
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) :
    gradInnerSmoothLin (I := I) (M := M) g ρα v =
      gradInnerSmooth (I := I) (M := M) g ρα v := rfl

end

section

variable [I.Boundaryless] [CompactSpace M]
lemma exists_gradSupBound
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : M,
        Real.sqrt (g.inner x (gradFun (I := I) g ρα x)
          (gradFun (I := I) g ρα x)) ≤ C := by
  classical
  have hcont : Continuous (fun x : M => Real.sqrt
      (g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g ρα x))) := by
    have h_in := gradInnerSmooth_continuous (I := I) (M := M) g ρα
      ⟨ρα, ρα.contMDiff⟩
    exact Real.continuous_sqrt.comp h_in
  have hCpt := (isCompact_univ (X := M)).image hcont
  obtain ⟨C₀, hC₀⟩ := hCpt.bddAbove
  refine ⟨max C₀ 0, le_max_right _ _, fun x => ?_⟩
  have hxC : Real.sqrt (g.inner x (gradFun (I := I) g ρα x)
      (gradFun (I := I) g ρα x)) ≤ C₀ :=
    hC₀ ⟨x, Set.mem_univ _, rfl⟩
  exact hxC.trans (le_max_left _ _)

noncomputable def gradSupBound
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) : ℝ :=
  Classical.choose (exists_gradSupBound (I := I) (M := M) g ρα)

lemma gradSupBound_nonneg
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) :
    0 ≤ gradSupBound (I := I) (M := M) g ρα :=
  (Classical.choose_spec
    (exists_gradSupBound (I := I) (M := M) g ρα)).1

lemma sqrt_inner_grad_self_le_gradSupBound
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) (x : M) :
    Real.sqrt (g.inner x (gradFun (I := I) g ρα x)
        (gradFun (I := I) g ρα x)) ≤ gradSupBound (I := I) (M := M) g ρα :=
  (Classical.choose_spec
    (exists_gradSupBound (I := I) (M := M) g ρα)).2 x

end

lemma abs_gradInner_le_sqrt_mul_sqrt
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) (x : M) :
    |g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g v.toFun x)| ≤
      Real.sqrt (g.inner x (gradFun (I := I) g ρα x)
          (gradFun (I := I) g ρα x)) *
      Real.sqrt (g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x)) :=
  abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g x _ _

variable [I.Boundaryless] [CompactSpace M] in
lemma abs_gradInner_le_gradSupBound_mul_sqrt
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) (x : M) :
    |g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g v.toFun x)| ≤
      gradSupBound (I := I) (M := M) g ρα *
        Real.sqrt (g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x)) := by
  have h1 := abs_gradInner_le_sqrt_mul_sqrt (I := I) (M := M) g ρα v x
  have h2 := sqrt_inner_grad_self_le_gradSupBound (I := I) (M := M) g ρα x
  have h_sqrt_v_nn : 0 ≤ Real.sqrt (g.inner x (gradFun (I := I) g v.toFun x)
      (gradFun (I := I) g v.toFun x)) := Real.sqrt_nonneg _
  exact h1.trans (mul_le_mul_of_nonneg_right h2 h_sqrt_v_nn)

variable [I.Boundaryless] [T2Space M] [CompactSpace M] in
lemma norm_gradInnerSmooth_sq
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) :
    ‖gradInnerSmooth (I := I) (M := M) g ρα v‖ ^ 2 =
      ∫ x, (g.inner x (gradFun (I := I) g ρα x)
            (gradFun (I := I) g v.toFun x)) ^ 2
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  have h := real_inner_self_eq_norm_sq (gradInnerSmooth (I := I) (M := M) g ρα v)
  rw [L2.inner_def (𝕜 := ℝ)] at h
  have hae_coe := gradInnerSmooth_coeFn (I := I) (M := M) g ρα v
  have hae : (fun a : M =>
        @inner ℝ _ _
          ((gradInnerSmooth (I := I) (M := M) g ρα v :
              Lp ℝ 2 _) a)
          ((gradInnerSmooth (I := I) (M := M) g ρα v :
              Lp ℝ 2 _) a)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun a : M =>
        (g.inner a (gradFun (I := I) g ρα a)
          (gradFun (I := I) g v.toFun a)) ^ 2) := by
    filter_upwards [hae_coe] with a hae_a
    rw [hae_a]
    rw [show (g.inner a (gradFun (I := I) g ρα a)
          (gradFun (I := I) g v.toFun a)) ^ 2 =
        g.inner a (gradFun (I := I) g ρα a)
          (gradFun (I := I) g v.toFun a) *
        g.inner a (gradFun (I := I) g ρα a)
          (gradFun (I := I) g v.toFun a) from sq _]
    rfl
  rw [integral_congr_ae hae] at h
  exact h.symm

variable [I.Boundaryless] [CompactSpace M] in
lemma sq_gradInner_le_gradSupBound_sq_mul
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) (x : M) :
    (g.inner x (gradFun (I := I) g ρα x) (gradFun (I := I) g v.toFun x)) ^ 2 ≤
      gradSupBound (I := I) (M := M) g ρα ^ 2 *
        g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x) := by
  have h_abs := abs_gradInner_le_gradSupBound_mul_sqrt (I := I) (M := M) g ρα v x
  have h_abs_nn : 0 ≤ |g.inner x (gradFun (I := I) g ρα x)
      (gradFun (I := I) g v.toFun x)| := abs_nonneg _
  have h_rhs_nn : 0 ≤ gradSupBound (I := I) (M := M) g ρα *
      Real.sqrt (g.inner x (gradFun (I := I) g v.toFun x)
        (gradFun (I := I) g v.toFun x)) :=
    mul_nonneg (gradSupBound_nonneg (I := I) (M := M) g ρα) (Real.sqrt_nonneg _)
  have h_sq := mul_self_le_mul_self h_abs_nn h_abs
  have h_lhs_sq : |g.inner x (gradFun (I := I) g ρα x)
        (gradFun (I := I) g v.toFun x)| *
      |g.inner x (gradFun (I := I) g ρα x)
        (gradFun (I := I) g v.toFun x)| =
      (g.inner x (gradFun (I := I) g ρα x)
        (gradFun (I := I) g v.toFun x)) ^ 2 := by
    rw [← sq, sq_abs]
  have h_v_self_nn : 0 ≤ g.inner x (gradFun (I := I) g v.toFun x)
      (gradFun (I := I) g v.toFun x) :=
    metric_inner_self_nonneg (I := I) (M := M) g x _
  have h_rhs_sq : (gradSupBound (I := I) (M := M) g ρα *
        Real.sqrt (g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x))) *
      (gradSupBound (I := I) (M := M) g ρα *
        Real.sqrt (g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x))) =
      gradSupBound (I := I) (M := M) g ρα ^ 2 *
        g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x) := by
    rw [show (gradSupBound (I := I) (M := M) g ρα *
            Real.sqrt _) *
          (gradSupBound (I := I) (M := M) g ρα *
            Real.sqrt _) =
        gradSupBound (I := I) (M := M) g ρα ^ 2 *
          (Real.sqrt _ * Real.sqrt _) from by ring]
    rw [Real.mul_self_sqrt h_v_self_nn]
  rw [h_lhs_sq] at h_sq
  rw [h_rhs_sq] at h_sq
  exact h_sq

section

variable [I.Boundaryless] [T2Space M] [CompactSpace M]
lemma norm_gradInnerSmooth_sq_le_gradSupBound_sq_mul_integral
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) :
    ‖gradInnerSmooth (I := I) (M := M) g ρα v‖ ^ 2 ≤
      gradSupBound (I := I) (M := M) g ρα ^ 2 *
        (∫ x, g.inner x (gradFun (I := I) g v.toFun x)
            (gradFun (I := I) g v.toFun x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  rw [norm_gradInnerSmooth_sq]
  have hpt : ∀ x : M,
      (g.inner x (gradFun (I := I) g ρα x)
          (gradFun (I := I) g v.toFun x)) ^ 2 ≤
      gradSupBound (I := I) (M := M) g ρα ^ 2 *
        g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x) :=
    sq_gradInner_le_gradSupBound_sq_mul (I := I) (M := M) g ρα v
  have : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have hLHS_int : Integrable (fun x : M =>
      (g.inner x (gradFun (I := I) g ρα x)
        (gradFun (I := I) g v.toFun x)) ^ 2)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hcont : Continuous (fun x : M =>
        (g.inner x (gradFun (I := I) g ρα x)
          (gradFun (I := I) g v.toFun x)) ^ 2) :=
      (gradInnerSmooth_continuous (I := I) (M := M) g ρα v).pow 2
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hRHS_int : Integrable (fun x : M =>
      g.inner x (gradFun (I := I) g v.toFun x)
        (gradFun (I := I) g v.toFun x))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hcont : Continuous (fun x : M =>
        g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x)) :=
      gradInnerSmooth_continuous (I := I) (M := M) g
        ⟨v.toFun, v.smooth⟩ v
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hRHS_const_int : Integrable (fun x : M =>
      gradSupBound (I := I) (M := M) g ρα ^ 2 *
        g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hRHS_int.const_mul _
  have h_int_le := integral_mono_ae hLHS_int hRHS_const_int
    (Filter.Eventually.of_forall hpt)
  rw [integral_const_mul] at h_int_le
  exact h_int_le

lemma integral_inner_grad_self_le_h1_norm_sq
    {g : SmoothRiemannianMetric I M} (v : SmoothScalar g) :
    (∫ x, g.inner x (gradFun (I := I) g v.toFun x)
        (gradFun (I := I) g v.toFun x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
    ‖v‖ ^ 2 := by
  rw [SmoothScalar.norm_sq_eq_inner_self]
  unfold smoothScalarH1Inner
  have h_l2_nonneg :=
    SmoothScalar.integral_mul_self_nonneg (I := I) (M := M) (g := g) v
  have h_grad_eq :
      (∫ x, g.inner x ((gradG (I := I) g ⟨v.toFun, v.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((gradG (I := I) g ⟨v.toFun, v.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      (∫ x, g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x
    rfl
  linarith [h_grad_eq]

theorem norm_gradInnerSmooth_le
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) :
    ‖gradInnerSmooth (I := I) (M := M) g ρα v‖ ≤
      gradSupBound (I := I) (M := M) g ρα * ‖v‖ := by
  have h_sq : ‖gradInnerSmooth (I := I) (M := M) g ρα v‖ ^ 2 ≤
      (gradSupBound (I := I) (M := M) g ρα * ‖v‖) ^ 2 := by
    calc ‖gradInnerSmooth (I := I) (M := M) g ρα v‖ ^ 2
        ≤ gradSupBound (I := I) (M := M) g ρα ^ 2 *
            (∫ x, g.inner x (gradFun (I := I) g v.toFun x)
                (gradFun (I := I) g v.toFun x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g)) :=
          norm_gradInnerSmooth_sq_le_gradSupBound_sq_mul_integral
            (I := I) (M := M) g ρα v
      _ ≤ gradSupBound (I := I) (M := M) g ρα ^ 2 * ‖v‖ ^ 2 := by
          have h_int_le := integral_inner_grad_self_le_h1_norm_sq (g := g) v
          have h_C_sq_nn : 0 ≤ gradSupBound (I := I) (M := M) g ρα ^ 2 := sq_nonneg _
          exact mul_le_mul_of_nonneg_left h_int_le h_C_sq_nn
      _ = (gradSupBound (I := I) (M := M) g ρα * ‖v‖) ^ 2 := by ring
  have h_lhs_nn : 0 ≤ ‖gradInnerSmooth (I := I) (M := M) g ρα v‖ := norm_nonneg _
  have h_rhs_nn : 0 ≤ gradSupBound (I := I) (M := M) g ρα * ‖v‖ :=
    mul_nonneg (gradSupBound_nonneg (I := I) (M := M) g ρα) (norm_nonneg _)
  exact abs_le_of_sq_le_sq' h_sq h_rhs_nn |>.2

noncomputable def gradInnerCLMOnSmooth
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) :
    SmoothScalar g →L[ℝ] Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (gradInnerSmoothLin (I := I) (M := M) g ρα).mkContinuous
    (gradSupBound (I := I) (M := M) g ρα)
    (fun v => norm_gradInnerSmooth_le (I := I) (M := M) g ρα v)

@[simp] lemma gradInnerCLMOnSmooth_apply
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) :
    gradInnerCLMOnSmooth (I := I) (M := M) g ρα v =
      gradInnerSmooth (I := I) (M := M) g ρα v := rfl

private lemma denseRange_toComplL_smoothScalar
    (g : SmoothRiemannianMetric I M) :
    DenseRange (UniformSpace.Completion.toComplL :
      SmoothScalar g →L[ℝ] H1Compl g) := by
  rw [show (UniformSpace.Completion.toComplL : SmoothScalar g → H1Compl g) =
      ((↑) : SmoothScalar g → UniformSpace.Completion (SmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

private lemma isUniformInducing_toComplL_smoothScalar
    (g : SmoothRiemannianMetric I M) :
    IsUniformInducing
      (UniformSpace.Completion.toComplL :
        SmoothScalar g →L[ℝ] H1Compl g) := by
  rw [show (UniformSpace.Completion.toComplL : SmoothScalar g → H1Compl g) =
      ((↑) : SmoothScalar g → UniformSpace.Completion (SmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.isUniformInducing_coe (SmoothScalar g)

noncomputable def gradInnerCLM
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯) :
    H1Compl g →L[ℝ] Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  ContinuousLinearMap.extend (gradInnerCLMOnSmooth (I := I) (M := M) g ρα)
    (UniformSpace.Completion.toComplL :
      SmoothScalar g →L[ℝ] H1Compl g)

theorem gradInnerCLM_smoothToH1Compl
    (g : SmoothRiemannianMetric I M) (ρα : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) :
    gradInnerCLM (I := I) (M := M) g ρα
        (smoothToH1Compl (I := I) (M := M) g v) =
      gradInnerSmooth (I := I) (M := M) g ρα v := by
  unfold gradInnerCLM
  have h := ContinuousLinearMap.extend_eq
    (gradInnerCLMOnSmooth (I := I) (M := M) g ρα)
    (e := UniformSpace.Completion.toComplL)
    (denseRange_toComplL_smoothScalar (I := I) (M := M) g)
    (isUniformInducing_toComplL_smoothScalar (I := I) (M := M) g) v
  exact h

end

end Laplacian
end Analysis
end CalabiYau

end
