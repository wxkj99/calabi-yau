-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/LaplacianDomain/Multiplication/H1Completion.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.LaplacianDomain.Multiplication.Smooth
public import CalabiYau.Analysis.Elliptic.Regularity.LaplacianDomain.Variational.ArbitraryTest
public import Mathlib.Analysis.Normed.Operator.Extend

@[expose] public section
open CalabiYau.Riemannian


noncomputable section

open Bundle Manifold MeasureTheory Filter Topology
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace CalabiYau
namespace Laplacian
namespace LaplacianDomainSmoothMul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Analysis.Laplacian.LaplacianDomainVariationalLimit
open CalabiYau.Analysis.Laplacian.LaplacianDomainVariationalLimitGeneral
open CalabiYau.Analysis.Laplacian.LaplacianDomainSmoothMul
open CalabiYau.Analysis.Laplacian

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩



noncomputable def smoothScalarMulFun
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    SmoothScalar g where
  toFun := fun x : M => (φ : M → ℝ) x * v.toFun x
  smooth := φ.contMDiff.mul v.smooth

@[simp] lemma smoothScalarMulFun_toFun
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    (smoothScalarMulFun (I := I) (M := M) g φ v).toFun =
      fun x : M => (φ : M → ℝ) x * v.toFun x := rfl

lemma smoothScalarMulFun_add
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v w : SmoothScalar g) :
    smoothScalarMulFun (I := I) (M := M) g φ (v + w) =
      smoothScalarMulFun (I := I) (M := M) g φ v +
        smoothScalarMulFun (I := I) (M := M) g φ w := by
  apply SmoothScalar.ext
  funext x
  change (φ : M → ℝ) x * (v + w).toFun x =
    (smoothScalarMulFun (I := I) (M := M) g φ v +
      smoothScalarMulFun (I := I) (M := M) g φ w).toFun x
  rw [SmoothScalar.toFun_add_apply,
    SmoothScalar.toFun_add_apply,
    smoothScalarMulFun_toFun, smoothScalarMulFun_toFun]
  ring

lemma smoothScalarMulFun_smul
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (c : ℝ) (v : SmoothScalar g) :
    smoothScalarMulFun (I := I) (M := M) g φ (c • v) =
      c • smoothScalarMulFun (I := I) (M := M) g φ v := by
  apply SmoothScalar.ext
  funext x
  change (φ : M → ℝ) x * (c • v).toFun x =
    (c • smoothScalarMulFun (I := I) (M := M) g φ v).toFun x
  rw [SmoothScalar.toFun_smul_apply, SmoothScalar.toFun_smul_apply,
    smoothScalarMulFun_toFun]
  ring

noncomputable def smoothScalarMulLin
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    SmoothScalar g →ₗ[ℝ] SmoothScalar g where
  toFun v := smoothScalarMulFun (I := I) (M := M) g φ v
  map_add' v w := smoothScalarMulFun_add (I := I) (M := M) g φ v w
  map_smul' c v := smoothScalarMulFun_smul (I := I) (M := M) g φ c v

@[simp] lemma smoothScalarMulLin_apply
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    smoothScalarMulLin (I := I) (M := M) g φ v =
      smoothScalarMulFun (I := I) (M := M) g φ v := rfl

variable [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in
lemma gradFun_smoothScalarMulFun
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (x : M) :
    gradFun (I := I) g (smoothScalarMulFun (I := I) (M := M) g φ v).toFun x =
      (φ : M → ℝ) x • gradFun (I := I) g v.toFun x +
        v.toFun x • gradFun (I := I) g (φ : M → ℝ) x := by
  change gradFun (I := I) g (fun y : M => (φ : M → ℝ) y * v.toFun y) x =
    (φ : M → ℝ) x • gradFun (I := I) g v.toFun x +
      v.toFun x • gradFun (I := I) g (φ : M → ℝ) x
  exact LaplacianDomainVariationalLimitGeneral.gradFun_smul_smooth_eq_pointwise
    (I := I) (M := M) g φ.contMDiff v.smooth x

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] in
private lemma sq_phi_mul_v_le
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (x : M) :
    ((φ : M → ℝ) x * v.toFun x) ^ 2 ≤
      phiSupBound (I := I) (M := M) g φ ^ 2 * v.toFun x ^ 2 := by
  have h_abs := abs_phi_le_phiSupBound (I := I) (M := M) g φ x
  have h_abs_nn : (0 : ℝ) ≤ |((φ : M → ℝ) x)| := abs_nonneg _
  have h_v_sq_nn : (0 : ℝ) ≤ v.toFun x ^ 2 := sq_nonneg _
  have h_phi_sq_le : ((φ : M → ℝ) x) ^ 2 ≤ phiSupBound (I := I) (M := M) g φ ^ 2 := by
    have h_sq_eq : ((φ : M → ℝ) x) ^ 2 = |((φ : M → ℝ) x)| ^ 2 := (sq_abs _).symm
    rw [h_sq_eq]
    exact pow_le_pow_left₀ h_abs_nn h_abs 2
  have h_eq : ((φ : M → ℝ) x * v.toFun x) ^ 2 =
      ((φ : M → ℝ) x) ^ 2 * v.toFun x ^ 2 := by ring
  rw [h_eq]
  exact mul_le_mul_of_nonneg_right h_phi_sq_le h_v_sq_nn

private lemma metric_inner_self_nonneg
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    0 ≤ g.inner x v v :=
  SmoothRiemannianMetric_inner_self_nonneg g x v

variable [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in
private lemma inner_grad_self_nonneg
    (g : SmoothRiemannianMetric I M) (φ : M → ℝ) (x : M) :
    0 ≤ g.inner x (gradFun (I := I) g φ x) (gradFun (I := I) g φ x) :=
  metric_inner_self_nonneg (I := I) (M := M) g x _

variable [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in
private lemma inner_grad_phi_mul_v_le
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (x : M) :
    g.inner x (gradFun (I := I) g
        (smoothScalarMulFun (I := I) (M := M) g φ v).toFun x)
      (gradFun (I := I) g
        (smoothScalarMulFun (I := I) (M := M) g φ v).toFun x) ≤
    2 * (((φ : M → ℝ) x) ^ 2 *
        g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x)) +
      2 * ((v.toFun x) ^ 2 *
        g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (φ : M → ℝ) x)) := by
  rw [gradFun_smoothScalarMulFun]
  set A : TangentSpace I x := (φ : M → ℝ) x • gradFun (I := I) g v.toFun x
  set B : TangentSpace I x := v.toFun x • gradFun (I := I) g (φ : M → ℝ) x
  have h_expand :
      g.inner x (A + B) (A + B) =
        g.inner x A A + 2 * g.inner x A B + g.inner x B B := by
    have h1 : g.inner x (A + B) (A + B) =
        g.inner x A (A + B) + g.inner x B (A + B) := by
      rw [(g.inner x).map_add]; rfl
    rw [h1]
    have h_A_split : g.inner x A (A + B) = g.inner x A A + g.inner x A B :=
      (g.inner x A).map_add A B
    have h_B_split : g.inner x B (A + B) = g.inner x B A + g.inner x B B :=
      (g.inner x B).map_add A B
    have h_BA_eq_AB : g.inner x B A = g.inner x A B := g.symm x B A
    rw [h_A_split, h_B_split, h_BA_eq_AB]
    ring
  rw [h_expand]
  have h_CS_bound : 2 * g.inner x A B ≤ g.inner x A A + g.inner x B B := by
    have h_abs_CS : |g.inner x A B| ≤
        Real.sqrt (g.inner x A A) * Real.sqrt (g.inner x B B) :=
      abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g x A B
    have h_AA_nn := metric_inner_self_nonneg (I := I) (M := M) g x A
    have h_BB_nn := metric_inner_self_nonneg (I := I) (M := M) g x B
    have h_AM : 2 * (Real.sqrt (g.inner x A A) * Real.sqrt (g.inner x B B)) ≤
        (Real.sqrt (g.inner x A A)) ^ 2 + (Real.sqrt (g.inner x B B)) ^ 2 := by
      have : 0 ≤ (Real.sqrt (g.inner x A A) - Real.sqrt (g.inner x B B)) ^ 2 :=
        sq_nonneg _
      nlinarith
    have h_sqrt_sq_A : (Real.sqrt (g.inner x A A)) ^ 2 = g.inner x A A :=
      Real.sq_sqrt h_AA_nn
    have h_sqrt_sq_B : (Real.sqrt (g.inner x B B)) ^ 2 = g.inner x B B :=
      Real.sq_sqrt h_BB_nn
    rw [h_sqrt_sq_A, h_sqrt_sq_B] at h_AM
    have h_2abs_le : 2 * |g.inner x A B| ≤
        2 * (Real.sqrt (g.inner x A A) * Real.sqrt (g.inner x B B)) := by
      have h_abs_nn : 0 ≤ |g.inner x A B| := abs_nonneg _
      linarith
    have h_le_abs : g.inner x A B ≤ |g.inner x A B| := le_abs_self _
    linarith
  have h_AA : g.inner x A A =
      ((φ : M → ℝ) x) ^ 2 *
        g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x) := by
    change g.inner x ((φ : M → ℝ) x • gradFun (I := I) g v.toFun x)
        ((φ : M → ℝ) x • gradFun (I := I) g v.toFun x) =
      ((φ : M → ℝ) x) ^ 2 *
        g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x)
    rw [(g.inner x).map_smul, smul_apply,
      (g.inner x _).map_smul]
    change (φ : M → ℝ) x • (φ : M → ℝ) x •
        g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x) =
      ((φ : M → ℝ) x) ^ 2 *
        g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x)
    rw [smul_eq_mul, smul_eq_mul]
    ring
  have h_BB : g.inner x B B =
      (v.toFun x) ^ 2 *
        g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (φ : M → ℝ) x) := by
    change g.inner x (v.toFun x • gradFun (I := I) g (φ : M → ℝ) x)
        (v.toFun x • gradFun (I := I) g (φ : M → ℝ) x) =
      (v.toFun x) ^ 2 *
        g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (φ : M → ℝ) x)
    rw [(g.inner x).map_smul, smul_apply,
      (g.inner x _).map_smul]
    change v.toFun x • v.toFun x •
        g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (φ : M → ℝ) x) =
      (v.toFun x) ^ 2 *
        g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (φ : M → ℝ) x)
    rw [smul_eq_mul, smul_eq_mul]
    ring
  rw [h_AA, h_BB] at h_CS_bound ⊢
  linarith [h_CS_bound]

variable [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [CompactSpace M] in
private lemma integral_sq_phi_mul_v_le
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    (∫ x, ((φ : M → ℝ) x * v.toFun x) ^ 2
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
      phiSupBound (I := I) (M := M) g φ ^ 2 *
        (∫ x, v.toFun x ^ 2
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  have : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have h_phi_cont : Continuous (φ : M → ℝ) := φ.contMDiff.continuous
  have h_v_cont : Continuous v.toFun := v.smooth.continuous
  have h_LHS_cont : Continuous (fun x : M => ((φ : M → ℝ) x * v.toFun x) ^ 2) :=
    (h_phi_cont.mul h_v_cont).pow 2
  have h_RHS_cont : Continuous (fun x : M => v.toFun x ^ 2) := h_v_cont.pow 2
  have h_LHS_int : Integrable (fun x : M => ((φ : M → ℝ) x * v.toFun x) ^ 2)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    h_LHS_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h_RHS_int : Integrable (fun x : M => v.toFun x ^ 2)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    h_RHS_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h_RHS_cmul_int : Integrable (fun x : M =>
      phiSupBound (I := I) (M := M) g φ ^ 2 * v.toFun x ^ 2)
      (riemannianVolumeMeasure (I := I) (M := M) g) := h_RHS_int.const_mul _
  have h_pt : ∀ x : M, ((φ : M → ℝ) x * v.toFun x) ^ 2 ≤
      phiSupBound (I := I) (M := M) g φ ^ 2 * v.toFun x ^ 2 :=
    sq_phi_mul_v_le (I := I) (M := M) g φ v
  have h_int_le := integral_mono_ae h_LHS_int h_RHS_cmul_int
    (Filter.Eventually.of_forall h_pt)
  rw [integral_const_mul] at h_int_le
  exact h_int_le

variable [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M] in
private lemma integral_inner_grad_phi_mul_v_le
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    (∫ x, g.inner x (gradFun (I := I) g
          (smoothScalarMulFun (I := I) (M := M) g φ v).toFun x)
        (gradFun (I := I) g
          (smoothScalarMulFun (I := I) (M := M) g φ v).toFun x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
      2 * phiSupBound (I := I) (M := M) g φ ^ 2 *
        (∫ x, g.inner x (gradFun (I := I) g v.toFun x)
              (gradFun (I := I) g v.toFun x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
      2 * gradSupBound (I := I) (M := M) g φ ^ 2 *
        (∫ x, v.toFun x ^ 2
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  have : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have h_phi_cont : Continuous (φ : M → ℝ) := φ.contMDiff.continuous
  have h_v_cont : Continuous v.toFun := v.smooth.continuous
  have h_inner_eq_v : ∀ x : M,
      g.inner x ((gradG (I := I) g ⟨v.toFun, v.smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g ⟨v.toFun, v.smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      g.inner x (gradFun (I := I) g v.toFun x)
        (gradFun (I := I) g v.toFun x) := by
    intro x; rfl
  have h_inner_cont_v : Continuous (fun x : M => g.inner x
      (gradFun (I := I) g v.toFun x)
      (gradFun (I := I) g v.toFun x)) :=
    (TangentBundle.continuous_g_inner_of_smooth_sections (I := I) (M := M) g
      (gradG (I := I) g ⟨v.toFun, v.smooth⟩) (gradG (I := I) g ⟨v.toFun,
        v.smooth⟩)).congr h_inner_eq_v
  have h_inner_eq_phi : ∀ x : M,
      g.inner x ((gradG (I := I) g φ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g φ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
        (gradFun (I := I) g (φ : M → ℝ) x) := by
    intro x; rfl
  have h_inner_cont_phi : Continuous (fun x : M => g.inner x
      (gradFun (I := I) g (φ : M → ℝ) x)
      (gradFun (I := I) g (φ : M → ℝ) x)) :=
    (TangentBundle.continuous_g_inner_of_smooth_sections (I := I) (M := M) g
      (gradG (I := I) g φ)
        (gradG (I := I) g φ)).congr h_inner_eq_phi
  have h_inner_eq_phiv : ∀ x : M,
      g.inner x ((gradG (I := I) g ⟨(smoothScalarMulFun (I := I) (M := M) g φ v).toFun,
        (smoothScalarMulFun (I := I) (M := M) g φ v).smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g ⟨(smoothScalarMulFun (I := I) (M := M) g φ v).toFun,
          (smoothScalarMulFun (I := I) (M := M) g φ v).smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      g.inner x (gradFun (I := I) g
          (smoothScalarMulFun (I := I) (M := M) g φ v).toFun x)
        (gradFun (I := I) g
          (smoothScalarMulFun (I := I) (M := M) g φ v).toFun x) := by
    intro x; rfl
  have h_LHS_cont : Continuous (fun x : M =>
      g.inner x (gradFun (I := I) g
          (smoothScalarMulFun (I := I) (M := M) g φ v).toFun x)
        (gradFun (I := I) g
          (smoothScalarMulFun (I := I) (M := M) g φ v).toFun x)) :=
    (TangentBundle.continuous_g_inner_of_smooth_sections (I := I) (M := M) g
      (gradG (I := I) g ⟨(smoothScalarMulFun (I := I) (M := M) g φ v).toFun,
        (smoothScalarMulFun (I := I) (M := M) g φ v).smooth⟩)
        (gradG (I := I) g ⟨(smoothScalarMulFun (I := I) (M := M) g φ v).toFun,
          (smoothScalarMulFun (I := I) (M := M) g φ v).smooth⟩)).congr h_inner_eq_phiv
  have h_grad_phi2_v_v_cont : Continuous (fun x : M =>
      ((φ : M → ℝ) x) ^ 2 *
        g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x)) :=
    (h_phi_cont.pow 2).mul h_inner_cont_v
  have h_grad_v2_phi_phi_cont : Continuous (fun x : M =>
      (v.toFun x) ^ 2 *
        g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (φ : M → ℝ) x)) :=
    (h_v_cont.pow 2).mul h_inner_cont_phi
  have h_LHS_int : Integrable _
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    h_LHS_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h_RHS1_int : Integrable (fun x : M =>
      ((φ : M → ℝ) x) ^ 2 *
        g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    h_grad_phi2_v_v_cont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h_RHS2_int : Integrable (fun x : M =>
      (v.toFun x) ^ 2 *
        g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (φ : M → ℝ) x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    h_grad_v2_phi_phi_cont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h_RHS_int : Integrable (fun x : M =>
      2 * (((φ : M → ℝ) x) ^ 2 *
        g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x)) +
      2 * ((v.toFun x) ^ 2 *
        g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (φ : M → ℝ) x)))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    (h_RHS1_int.const_mul 2).add (h_RHS2_int.const_mul 2)
  have h_pt : ∀ x : M, g.inner x (gradFun (I := I) g
          (smoothScalarMulFun (I := I) (M := M) g φ v).toFun x)
        (gradFun (I := I) g
          (smoothScalarMulFun (I := I) (M := M) g φ v).toFun x) ≤
      2 * (((φ : M → ℝ) x) ^ 2 *
        g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x)) +
      2 * ((v.toFun x) ^ 2 *
        g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (φ : M → ℝ) x)) :=
    inner_grad_phi_mul_v_le (I := I) (M := M) g φ v
  have h_int_le := integral_mono_ae h_LHS_int h_RHS_int
    (Filter.Eventually.of_forall h_pt)
  have h_int_eq : (∫ x, 2 * (((φ : M → ℝ) x) ^ 2 *
        g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x)) +
      2 * ((v.toFun x) ^ 2 *
        g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (φ : M → ℝ) x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
    2 * (∫ x, (((φ : M → ℝ) x) ^ 2 *
          g.inner x (gradFun (I := I) g v.toFun x)
            (gradFun (I := I) g v.toFun x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
    2 * (∫ x, ((v.toFun x) ^ 2 *
          g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
            (gradFun (I := I) g (φ : M → ℝ) x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
    rw [integral_add (h_RHS1_int.const_mul 2) (h_RHS2_int.const_mul 2),
      integral_const_mul, integral_const_mul]
  rw [h_int_eq] at h_int_le
  have h_int1_le : (∫ x, (((φ : M → ℝ) x) ^ 2 *
        g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
      phiSupBound (I := I) (M := M) g φ ^ 2 *
        (∫ x, g.inner x (gradFun (I := I) g v.toFun x)
              (gradFun (I := I) g v.toFun x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
    have h_pt1 : ∀ x : M, ((φ : M → ℝ) x) ^ 2 *
        g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x) ≤
        phiSupBound (I := I) (M := M) g φ ^ 2 *
        g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x) := by
      intro x
      have h_inner_nn := inner_grad_self_nonneg (I := I) (M := M) g v.toFun x
      have h_phi_sq_le : ((φ : M → ℝ) x) ^ 2 ≤
          phiSupBound (I := I) (M := M) g φ ^ 2 := by
        have h_abs := abs_phi_le_phiSupBound (I := I) (M := M) g φ x
        have h_abs_nn : (0 : ℝ) ≤ |((φ : M → ℝ) x)| := abs_nonneg _
        have h_sq_eq : ((φ : M → ℝ) x) ^ 2 = |((φ : M → ℝ) x)| ^ 2 := (sq_abs _).symm
        rw [h_sq_eq]
        exact pow_le_pow_left₀ h_abs_nn h_abs 2
      exact mul_le_mul_of_nonneg_right h_phi_sq_le h_inner_nn
    have h_inner_v_int : Integrable (fun x : M => g.inner x
        (gradFun (I := I) g v.toFun x) (gradFun (I := I) g v.toFun x))
        (riemannianVolumeMeasure (I := I) (M := M) g) :=
      h_inner_cont_v.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have h_cmul_int := h_inner_v_int.const_mul (phiSupBound (I := I) (M := M) g φ ^ 2)
    have := integral_mono_ae h_RHS1_int h_cmul_int (Filter.Eventually.of_forall h_pt1)
    rw [integral_const_mul] at this
    exact this
  have h_int2_le : (∫ x, ((v.toFun x) ^ 2 *
        g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (φ : M → ℝ) x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
      gradSupBound (I := I) (M := M) g φ ^ 2 *
        (∫ x, v.toFun x ^ 2
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
    have h_pt2 : ∀ x : M, (v.toFun x) ^ 2 *
        g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (φ : M → ℝ) x) ≤
        gradSupBound (I := I) (M := M) g φ ^ 2 *
        v.toFun x ^ 2 := by
      intro x
      have h_v_sq_nn : (0 : ℝ) ≤ v.toFun x ^ 2 := sq_nonneg _
      have h_inner_phi_nn := inner_grad_self_nonneg (I := I) (M := M) g (φ : M → ℝ) x
      have h_sqrt_le := sqrt_inner_grad_self_le_gradSupBound (I := I) (M := M) g φ x
      have h_sqrt_nn : 0 ≤ Real.sqrt (g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (φ : M → ℝ) x)) := Real.sqrt_nonneg _
      have h_inner_eq : (Real.sqrt (g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (φ : M → ℝ) x))) ^ 2 =
          g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (φ : M → ℝ) x) := Real.sq_sqrt h_inner_phi_nn
      have h_inner_le : g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (φ : M → ℝ) x) ≤
          gradSupBound (I := I) (M := M) g φ ^ 2 := by
        calc g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
              (gradFun (I := I) g (φ : M → ℝ) x) =
            (Real.sqrt (g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
              (gradFun (I := I) g (φ : M → ℝ) x))) ^ 2 := h_inner_eq.symm
          _ ≤ gradSupBound (I := I) (M := M) g φ ^ 2 :=
            pow_le_pow_left₀ h_sqrt_nn h_sqrt_le 2
      calc (v.toFun x) ^ 2 * g.inner x (gradFun (I := I) g (φ : M → ℝ) x)
              (gradFun (I := I) g (φ : M → ℝ) x) ≤
          (v.toFun x) ^ 2 * gradSupBound (I := I) (M := M) g φ ^ 2 :=
            mul_le_mul_of_nonneg_left h_inner_le h_v_sq_nn
        _ = gradSupBound (I := I) (M := M) g φ ^ 2 * v.toFun x ^ 2 := by ring
    have h_v_sq_int : Integrable (fun x : M => v.toFun x ^ 2)
        (riemannianVolumeMeasure (I := I) (M := M) g) := by
      have h_v_sq_cont : Continuous (fun x : M => v.toFun x ^ 2) := h_v_cont.pow 2
      exact h_v_sq_cont.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have h_cmul_int := h_v_sq_int.const_mul (gradSupBound (I := I) (M := M) g φ ^ 2)
    have := integral_mono_ae h_RHS2_int h_cmul_int (Filter.Eventually.of_forall h_pt2)
    rw [integral_const_mul] at this
    exact this
  linarith

variable [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M] in
noncomputable def smoothMulH1ComplConst
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) : ℝ :=
  Real.sqrt (2 * (phiSupBound (I := I) (M := M) g φ ^ 2 +
    gradSupBound (I := I) (M := M) g φ ^ 2))

variable [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless]  [CompactSpace M] in
lemma smoothMulH1ComplConst_nonneg
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    0 ≤ smoothMulH1ComplConst (I := I) (M := M) g φ :=
  Real.sqrt_nonneg _

variable [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless]  [CompactSpace M] in
lemma smoothMulH1ComplConst_sq
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    smoothMulH1ComplConst (I := I) (M := M) g φ ^ 2 =
      2 * (phiSupBound (I := I) (M := M) g φ ^ 2 +
        gradSupBound (I := I) (M := M) g φ ^ 2) := by
  unfold smoothMulH1ComplConst
  rw [Real.sq_sqrt]
  have h_phi_nn := sq_nonneg (phiSupBound (I := I) (M := M) g φ)
  have h_grad_nn := sq_nonneg (gradSupBound (I := I) (M := M) g φ)
  linarith

section

variable [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
theorem norm_smoothScalarMulFun_sq_le
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    ‖smoothScalarMulFun (I := I) (M := M) g φ v‖ ^ 2 ≤
      smoothMulH1ComplConst (I := I) (M := M) g φ ^ 2 * ‖v‖ ^ 2 := by
  rw [SmoothScalar.norm_sq_eq_inner_self,
    SmoothScalar.norm_sq_eq_inner_self v]
  unfold smoothScalarH1Inner
  rw [smoothMulH1ComplConst_sq]
  have h_lhs_l2 : (∫ x, (smoothScalarMulFun (I := I) (M := M) g φ v).toFun x *
        (smoothScalarMulFun (I := I) (M := M) g φ v).toFun x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      (∫ x, ((φ : M → ℝ) x * v.toFun x) ^ 2
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x
    change ((φ : M → ℝ) x * v.toFun x) * ((φ : M → ℝ) x * v.toFun x) =
      ((φ : M → ℝ) x * v.toFun x) ^ 2
    rw [sq]
  rw [h_lhs_l2]
  have h_rhs_l2 : (∫ x, v.toFun x * v.toFun x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      (∫ x, v.toFun x ^ 2
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x
    change v.toFun x * v.toFun x = v.toFun x ^ 2
    rw [sq]
  rw [h_rhs_l2]
  have h_grad_int_v : (∫ x, g.inner x
        ((gradG (I := I) g ⟨v.toFun, v.smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g ⟨v.toFun, v.smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      (∫ x, g.inner x (gradFun (I := I) g v.toFun x)
        (gradFun (I := I) g v.toFun x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x; rfl
  have h_grad_int_phiv : (∫ x, g.inner x
        ((gradG (I := I) g ⟨(smoothScalarMulFun (I := I) (M := M) g φ v).toFun,
          (smoothScalarMulFun (I := I) (M := M) g φ v).smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g ⟨(smoothScalarMulFun (I := I) (M := M) g φ v).toFun,
          (smoothScalarMulFun (I := I) (M := M) g φ v).smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      (∫ x, g.inner x (gradFun (I := I) g
          (smoothScalarMulFun (I := I) (M := M) g φ v).toFun x)
        (gradFun (I := I) g
          (smoothScalarMulFun (I := I) (M := M) g φ v).toFun x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x; rfl
  rw [h_grad_int_v, h_grad_int_phiv]
  have h_l2_le := integral_sq_phi_mul_v_le (I := I) (M := M) g φ v
  have h_grad_le := integral_inner_grad_phi_mul_v_le (I := I) (M := M) g φ v
  have h_v_l2_nn : 0 ≤ ∫ x, v.toFun x ^ 2
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine integral_nonneg ?_; intro x; exact sq_nonneg _
  have h_v_grad_nn : 0 ≤ ∫ x, g.inner x (gradFun (I := I) g v.toFun x)
      (gradFun (I := I) g v.toFun x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine integral_nonneg ?_; intro x
    exact inner_grad_self_nonneg (I := I) (M := M) g v.toFun x
  have h_phi_sq_nn := sq_nonneg (phiSupBound (I := I) (M := M) g φ)
  have h_grad_sq_nn := sq_nonneg (gradSupBound (I := I) (M := M) g φ)
  nlinarith [h_l2_le, h_grad_le]

theorem norm_smoothScalarMulFun_le
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    ‖smoothScalarMulFun (I := I) (M := M) g φ v‖ ≤
      smoothMulH1ComplConst (I := I) (M := M) g φ * ‖v‖ := by
  have h_sq := norm_smoothScalarMulFun_sq_le (I := I) (M := M) g φ v
  have h_lhs_nn : 0 ≤ ‖smoothScalarMulFun (I := I) (M := M) g φ v‖ := norm_nonneg _
  have h_rhs_nn : 0 ≤ smoothMulH1ComplConst (I := I) (M := M) g φ * ‖v‖ :=
    mul_nonneg (smoothMulH1ComplConst_nonneg (I := I) (M := M) g φ) (norm_nonneg _)
  have h_sq_le : ‖smoothScalarMulFun (I := I) (M := M) g φ v‖ ^ 2 ≤
      (smoothMulH1ComplConst (I := I) (M := M) g φ * ‖v‖) ^ 2 := by
    have h_eq : (smoothMulH1ComplConst (I := I) (M := M) g φ * ‖v‖) ^ 2 =
        smoothMulH1ComplConst (I := I) (M := M) g φ ^ 2 * ‖v‖ ^ 2 := by ring
    rw [h_eq]
    exact h_sq
  exact abs_le_of_sq_le_sq' h_sq_le h_rhs_nn |>.2

lemma norm_smoothScalarMulLin_le
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    ‖smoothScalarMulLin (I := I) (M := M) g φ v‖ ≤
      smoothMulH1ComplConst (I := I) (M := M) g φ * ‖v‖ :=
  norm_smoothScalarMulFun_le (I := I) (M := M) g φ v

noncomputable def smoothScalarMul
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    SmoothScalar g →L[ℝ] SmoothScalar g :=
  (smoothScalarMulLin (I := I) (M := M) g φ).mkContinuous
    (smoothMulH1ComplConst (I := I) (M := M) g φ)
    (fun v => norm_smoothScalarMulLin_le (I := I) (M := M) g φ v)

@[simp] lemma smoothScalarMul_apply
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    smoothScalarMul (I := I) (M := M) g φ v =
      smoothScalarMulFun (I := I) (M := M) g φ v := rfl

noncomputable def smoothMulH1ComplOnSmooth
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    SmoothScalar g →L[ℝ] H1Compl g :=
  (smoothToH1Compl (I := I) (M := M) g).comp
    (smoothScalarMul (I := I) (M := M) g φ)

@[simp] private lemma smoothMulH1ComplOnSmooth_apply
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    smoothMulH1ComplOnSmooth (I := I) (M := M) g φ v =
      smoothToH1Compl (I := I) (M := M) g
        (smoothScalarMulFun (I := I) (M := M) g φ v) := rfl

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

noncomputable def smoothMulH1Compl
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    H1Compl g →L[ℝ] H1Compl g :=
  ContinuousLinearMap.extend (smoothMulH1ComplOnSmooth (I := I) (M := M) g φ)
    (UniformSpace.Completion.toComplL :
      SmoothScalar g →L[ℝ] H1Compl g)

theorem smoothMulH1Compl_smoothToH1Compl
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    smoothMulH1Compl (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      smoothToH1Compl (I := I) (M := M) g
        (smoothScalarMulFun (I := I) (M := M) g φ v) := by
  unfold smoothMulH1Compl
  exact ContinuousLinearMap.extend_eq
    (smoothMulH1ComplOnSmooth (I := I) (M := M) g φ)
    (e := UniformSpace.Completion.toComplL)
    (denseRange_toComplL_smoothScalar (I := I) (M := M) g)
    (isUniformInducing_toComplL_smoothScalar (I := I) (M := M) g) v

private lemma h1ComplToLp_smoothMulH1Compl_eq_smoothMulLp_H1ComplToLp_on_smooth
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    h1ComplToLp (I := I) (M := M) g
        (smoothMulH1Compl (I := I) (M := M) g φ
          (smoothToH1Compl (I := I) (M := M) g v)) =
      smoothMulLp (I := I) (M := M) g φ
        (h1ComplToLp (I := I) (M := M) g
          (smoothToH1Compl (I := I) (M := M) g v)) := by
  rw [smoothMulH1Compl_smoothToH1Compl, h1ComplToLp_smoothToH1Compl,
    h1ComplToLp_smoothToH1Compl]
  apply MeasureTheory.Lp.ext
  have h_lhs_aeEq : (smoothToLp (I := I) (M := M) g
          (smoothScalarMulFun (I := I) (M := M) g φ v) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      fun x : M => (φ : M → ℝ) x * v.toFun x := by
    have h := MemLp.coeFn_toLp
      (smoothScalarMulFun (I := I) (M := M) g φ v).memLp_two
    refine h.trans ?_
    refine Filter.Eventually.of_forall ?_
    intro x; rfl
  have h_smoothToLp_v_aeEq : (smoothToLp (I := I) (M := M) g v :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g] v.toFun :=
    MemLp.coeFn_toLp v.memLp_two
  have h_rhs_aeEq := smoothMulLp_apply_coeFn (I := I) (M := M) g φ
    (smoothToLp (I := I) (M := M) g v)
  refine h_lhs_aeEq.trans ?_
  refine EventuallyEq.symm ?_
  filter_upwards [h_rhs_aeEq, h_smoothToLp_v_aeEq] with x h_rhs h_v
  rw [h_rhs, h_v]

theorem h1ComplToLp_smoothMulH1Compl_eq_smoothMulLp_H1ComplToLp
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    (h1ComplToLp (I := I) (M := M) g).comp
        (smoothMulH1Compl (I := I) (M := M) g φ) =
      (smoothMulLp (I := I) (M := M) g φ).comp
        (h1ComplToLp (I := I) (M := M) g) := by
  have h_dense := denseRange_toComplL_smoothScalar (I := I) (M := M) g
  apply ContinuousLinearMap.ext
  intro u
  refine h_dense.induction_on (p := fun u => _ = _) u ?_ ?_
  · refine isClosed_eq ?_ ?_
    · exact ((h1ComplToLp (I := I) (M := M) g).comp
        (smoothMulH1Compl (I := I) (M := M) g φ)).continuous
    · exact ((smoothMulLp (I := I) (M := M) g φ).comp
        (h1ComplToLp (I := I) (M := M) g)).continuous
  · intro v
    show ((h1ComplToLp (I := I) (M := M) g).comp
        (smoothMulH1Compl (I := I) (M := M) g φ))
          (UniformSpace.Completion.toComplL v) =
      ((smoothMulLp (I := I) (M := M) g φ).comp
        (h1ComplToLp (I := I) (M := M) g))
          (UniformSpace.Completion.toComplL v)
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    exact h1ComplToLp_smoothMulH1Compl_eq_smoothMulLp_H1ComplToLp_on_smooth
      (I := I) (M := M) g φ v

@[simp] theorem h1ComplToLp_smoothMulH1Compl
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (u : H1Compl g) :
    h1ComplToLp (I := I) (M := M) g (smoothMulH1Compl (I := I) (M := M) g φ u) =
      smoothMulLp (I := I) (M := M) g φ
        (h1ComplToLp (I := I) (M := M) g u) := by
  have h := h1ComplToLp_smoothMulH1Compl_eq_smoothMulLp_H1ComplToLp
    (I := I) (M := M) g φ
  exact congrArg (fun f => f u) h

noncomputable def smoothLaplacianBundle
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    C^∞⟮I, M; ℝ⟯ :=
  ⟨ΔG (I := I) g φ,
    Δ_g_contMDiff (I := I) g φ⟩

end

variable [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] in
@[simp] lemma smoothLaplacianBundle_apply
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (x : M) :
    (smoothLaplacianBundle (I := I) (M := M) g φ : M → ℝ) x =
      ΔG (I := I) g φ x := rfl

variable [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M] in
noncomputable def leibnizCompensatedSourceResidualCLMOfSmoothFactor
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) :
    H1Compl (I := I) (M := M) g →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  -((2 : ℝ) • gradInnerCLM (I := I) (M := M) g φ) -
    (smoothMulLp (I := I) (M := M) g
      (smoothLaplacianBundle (I := I) (M := M) g φ)).comp
      (h1ComplToLp (I := I) (M := M) g)

variable [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M] in
@[simp] lemma leibnizCompensatedSourceResidualCLMOfSmoothFactor_apply
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (u_h : H1Compl g) :
    leibnizCompensatedSourceResidualCLMOfSmoothFactor (I := I) (M := M) g φ u_h =
      -((2 : ℝ) • gradInnerCLM (I := I) (M := M) g φ u_h) -
        smoothMulLp (I := I) (M := M) g
          (smoothLaplacianBundle (I := I) (M := M) g φ)
          (h1ComplToLp (I := I) (M := M) g u_h) := by
  unfold leibnizCompensatedSourceResidualCLMOfSmoothFactor
  rfl

variable [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M] in
private noncomputable def smoothMulH1ComplInnerCLM
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (vT : SmoothScalar g) :
    H1Compl g →L[ℝ] ℝ :=
  ((innerSL ℝ : H1Compl g →L[ℝ] H1Compl g →L[ℝ] ℝ).flip
    (smoothToH1Compl (I := I) (M := M) g vT)).comp
    (smoothMulH1Compl (I := I) (M := M) g φ)

variable [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M] in
@[simp] private lemma smoothMulH1ComplInnerCLM_apply
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (vT : SmoothScalar g)
    (u_h : H1Compl g) :
    smoothMulH1ComplInnerCLM (I := I) (M := M) g φ vT u_h =
      ⟪smoothMulH1Compl (I := I) (M := M) g φ u_h,
        smoothToH1Compl (I := I) (M := M) g vT⟫_ℝ := by
  unfold smoothMulH1ComplInnerCLM
  rfl

variable [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M] in
private noncomputable def innerSmoothMulH1ComplCLM
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (vT : SmoothScalar g) :
    H1Compl g →L[ℝ] ℝ :=
  (innerSL ℝ : H1Compl g →L[ℝ] H1Compl g →L[ℝ] ℝ).flip
    (smoothMulH1Compl (I := I) (M := M) g φ
      (smoothToH1Compl (I := I) (M := M) g vT))

variable [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M] in
@[simp] private lemma innerSmoothMulH1ComplCLM_apply
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (vT : SmoothScalar g)
    (u_h : H1Compl g) :
    innerSmoothMulH1ComplCLM (I := I) (M := M) g φ vT u_h =
      ⟪u_h, smoothMulH1Compl (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g vT)⟫_ℝ := rfl

variable [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M] in
private noncomputable def rewrittenRHSCLM
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (vT : SmoothScalar g) :
    H1Compl g →L[ℝ] ℝ :=
  innerSmoothMulH1ComplCLM (I := I) (M := M) g φ vT +
    ((innerSL ℝ : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ]
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ] ℝ)
      (smoothToLp (I := I) (M := M) g vT)).comp
      (leibnizCompensatedSourceResidualCLMOfSmoothFactor (I := I) (M := M) g φ)

variable [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M] in
@[simp] private lemma rewrittenRHSCLM_apply
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (vT : SmoothScalar g)
    (u_h : H1Compl g) :
    rewrittenRHSCLM (I := I) (M := M) g φ vT u_h =
      ⟪u_h, smoothMulH1Compl (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g vT)⟫_ℝ +
      ⟪smoothToLp (I := I) (M := M) g vT,
        leibnizCompensatedSourceResidualCLMOfSmoothFactor (I := I) (M := M) g φ u_h⟫_ℝ := by
  unfold rewrittenRHSCLM
  rfl

end LaplacianDomainSmoothMul
end Laplacian
end CalabiYau

end
