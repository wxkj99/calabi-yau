-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/LaplacianDomain/L2.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.H1Compl.Defs
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Analysis.Normed.Operator.Extend

@[expose] public section
open CalabiYau.Riemannian

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

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

omit [I.Boundaryless] in
lemma SmoothScalar.memLp_two {g : SmoothRiemannianMetric I M}
    (f : SmoothScalar g) :
    MemLp f.toFun 2 (riemannianVolumeMeasure (I := I) (M := M) g) := by
  have : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  exact f.smooth.continuous.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

noncomputable def smoothToLpLin (g : SmoothRiemannianMetric I M) :
    SmoothScalar g →ₗ[ℝ] Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) where
  toFun f := f.memLp_two.toLp f.toFun
  map_add' f h := by
    have h_lhs_rfl : (f + h).memLp_two.toLp (f + h).toFun =
        (f.memLp_two.add h.memLp_two).toLp (f.toFun + h.toFun) := rfl
    rw [h_lhs_rfl, MemLp.toLp_add]
  map_smul' c f := by
    have h_lhs_rfl : (c • f).memLp_two.toLp (c • f).toFun =
        (f.memLp_two.const_smul c).toLp (c • f.toFun) := rfl
    rw [h_lhs_rfl, MemLp.toLp_const_smul]
    rfl

omit [I.Boundaryless] in
@[simp] lemma smoothToLpLin_apply (g : SmoothRiemannianMetric I M)
    (f : SmoothScalar g) :
    smoothToLpLin (I := I) (M := M) g f = f.memLp_two.toLp f.toFun := rfl

omit [I.Boundaryless] in
lemma SmoothScalar.norm_smoothToLp_sq {g : SmoothRiemannianMetric I M}
    (f : SmoothScalar g) :
    ‖smoothToLpLin (I := I) (M := M) g f‖ ^ 2 =
      ∫ x, f.toFun x * f.toFun x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  have h := real_inner_self_eq_norm_sq (smoothToLpLin (I := I) (M := M) g f)
  rw [L2.inner_def (𝕜 := ℝ)] at h
  have hae : (fun a : M =>
        @inner ℝ _ _
          ((smoothToLpLin (I := I) (M := M) g f : Lp ℝ 2 _) a)
          ((smoothToLpLin (I := I) (M := M) g f : Lp ℝ 2 _) a)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun a : M => f.toFun a * f.toFun a) := by
    have hae_coe : (smoothToLpLin (I := I) (M := M) g f : Lp ℝ 2 _) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g] f.toFun :=
      MemLp.coeFn_toLp f.memLp_two
    filter_upwards [hae_coe] with a hae_a
    rw [hae_a]
    rfl
  rw [integral_congr_ae hae] at h
  exact h.symm

lemma SmoothScalar.norm_sq_eq_inner_self {g : SmoothRiemannianMetric I M}
    (f : SmoothScalar g) :
    ‖f‖ ^ 2 = smoothScalarH1Inner (I := I) (M := M) f f := by
  have h := real_inner_self_eq_norm_sq f
  rw [SmoothScalar.inner_def] at h
  exact h.symm

lemma SmoothScalar.norm_smoothToLp_sq_le {g : SmoothRiemannianMetric I M}
    (f : SmoothScalar g) :
    ‖smoothToLpLin (I := I) (M := M) g f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  rw [f.norm_smoothToLp_sq, f.norm_sq_eq_inner_self]
  unfold smoothScalarH1Inner
  have h_grad_nonneg :
      0 ≤ ∫ x, g.inner x ((gradG (I := I) g ⟨f.toFun, f.smooth⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((gradG (I := I) g ⟨f.toFun, f.smooth⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    f.integral_inner_grad_self_nonneg
  linarith

lemma SmoothScalar.norm_smoothToLp_le {g : SmoothRiemannianMetric I M}
    (f : SmoothScalar g) :
    ‖smoothToLpLin (I := I) (M := M) g f‖ ≤ ‖f‖ := by
  have h_sq := f.norm_smoothToLp_sq_le
  have h_lhs_nn : 0 ≤ ‖smoothToLpLin (I := I) (M := M) g f‖ := norm_nonneg _
  have h_rhs_nn : 0 ≤ ‖f‖ := norm_nonneg _
  exact abs_le_of_sq_le_sq' h_sq h_rhs_nn |>.2

lemma SmoothScalar.norm_smoothToLp_le_one_mul {g : SmoothRiemannianMetric I M}
    (f : SmoothScalar g) :
    ‖smoothToLpLin (I := I) (M := M) g f‖ ≤ 1 * ‖f‖ := by
  rw [one_mul]; exact f.norm_smoothToLp_le

noncomputable def smoothToLp (g : SmoothRiemannianMetric I M) :
    SmoothScalar g →L[ℝ] Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (smoothToLpLin (I := I) (M := M) g).mkContinuous 1
    (fun f => f.norm_smoothToLp_le_one_mul)

@[simp] lemma smoothToLp_apply (g : SmoothRiemannianMetric I M)
    (f : SmoothScalar g) :
    smoothToLp (I := I) (M := M) g f =
      f.memLp_two.toLp f.toFun := rfl

theorem smoothToLp_injective (g : SmoothRiemannianMetric I M) :
    Function.Injective (smoothToLp (I := I) (M := M) g) := by
  intro f h hfh
  apply SmoothScalar.ext
  funext x
  have hf_ae : (smoothToLp (I := I) (M := M) g f : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g] f.toFun :=
    MemLp.coeFn_toLp f.memLp_two
  have hh_ae : (smoothToLp (I := I) (M := M) g h : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g] h.toFun :=
    MemLp.coeFn_toLp h.memLp_two
  have hlp_ae : (smoothToLp (I := I) (M := M) g f : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
      (smoothToLp (I := I) (M := M) g h : M → ℝ) := by
    rw [hfh]
  have hfun_ae : f.toFun =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g] h.toFun :=
    hf_ae.symm.trans (hlp_ae.trans hh_ae)
  let : (riemannianVolumeMeasure (I := I) (M := M) g).IsOpenPosMeasure :=
    riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) g
  exact congrFun ((Continuous.ae_eq_iff_eq
    (riemannianVolumeMeasure (I := I) (M := M) g)
    f.smooth.continuous h.smooth.continuous).mp hfun_ae) x

private lemma denseRange_toComplL_smoothScalar (g : SmoothRiemannianMetric I M) :
    DenseRange (UniformSpace.Completion.toComplL : SmoothScalar g →L[ℝ] H1Compl g) := by
  rw [show (UniformSpace.Completion.toComplL : SmoothScalar g → H1Compl g) =
      ((↑) : SmoothScalar g → UniformSpace.Completion (SmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

private lemma isUniformInducing_toComplL_smoothScalar
    (g : SmoothRiemannianMetric I M) :
    IsUniformInducing
      (UniformSpace.Completion.toComplL : SmoothScalar g →L[ℝ] H1Compl g) := by
  rw [show (UniformSpace.Completion.toComplL : SmoothScalar g → H1Compl g) =
      ((↑) : SmoothScalar g → UniformSpace.Completion (SmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.isUniformInducing_coe (SmoothScalar g)

noncomputable def H1ComplToLp (g : SmoothRiemannianMetric I M) :
    H1Compl g →L[ℝ] Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  ContinuousLinearMap.extend (smoothToLp (I := I) (M := M) g)
    (UniformSpace.Completion.toComplL : SmoothScalar g →L[ℝ] H1Compl g)

lemma H1ComplToLp_smoothToH1Compl (g : SmoothRiemannianMetric I M)
    (f : SmoothScalar g) :
    H1ComplToLp (I := I) (M := M) g
        (smoothToH1Compl (I := I) (M := M) g f) =
      smoothToLp (I := I) (M := M) g f := by
  unfold H1ComplToLp
  exact ContinuousLinearMap.extend_eq (smoothToLp (I := I) (M := M) g)
    (e := UniformSpace.Completion.toComplL)
    (denseRange_toComplL_smoothScalar (I := I) (M := M) g)
    (isUniformInducing_toComplL_smoothScalar (I := I) (M := M) g) f

end Laplacian
end Analysis
end CalabiYau

end
