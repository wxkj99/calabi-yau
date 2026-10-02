-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Intrinsic/Equivalence/ChartToIntrinsic/ExtensionDerivative.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Intrinsic.Equivalence.Basic
public import CalabiYau.Analysis.Sobolev.Intrinsic.Lp.Basic
public import CalabiYau.Analysis.Sobolev.Approximation.Density.FirstOrder
public import CalabiYau.Geometry.Riemannian.Volume.Chart.MeasureComparison
public import CalabiYau.Analysis.Sobolev.Manifold.Measure.UniformChartComparison
public import CalabiYau.Analysis.Sobolev.Manifold.Embedding.Subcritical
public import CalabiYau.Analysis.Sobolev.Manifold.Morrey.Basic
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Global.IntegrationByParts
public import CalabiYau.Geometry.Riemannian.Operator.Laplacian.Basic
public import CalabiYau.Geometry.Riemannian.Volume.Family.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

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

local notation "EuclN_E" =>
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private lemma sq_partials_scalarOnE_le_norm_fderiv_scalarOnE_sq
    (g : CalabiYau.SmoothRiemannianMetric I M)
    (α : M) (f : M → ℝ) (y : E) :
    (∑ k : Fin (Module.finrank ℝ E),
        (CalabiYau.Tensor.Coordinates.partialDeriv
            (E := E) k
            (CalabiYau.DivergenceTheorem.scalarOnE
              (I := I) α f) y)^2) ≤
      (∑ k : Fin (Module.finrank ℝ E),
        ‖(CalabiYau.Tensor.Coordinates.chartModelBasis E) k‖^2) *
          ‖fderiv ℝ
            (CalabiYau.DivergenceTheorem.scalarOnE
              (I := I) α f) y‖^2 := by
  classical
  let _ := g
  have h_each : ∀ k,
      (CalabiYau.Tensor.Coordinates.partialDeriv
          (E := E) k
          (CalabiYau.DivergenceTheorem.scalarOnE
            (I := I) α f) y)^2 ≤
        ‖(CalabiYau.Tensor.Coordinates.chartModelBasis E) k‖^2 *
          ‖fderiv ℝ
            (CalabiYau.DivergenceTheorem.scalarOnE
              (I := I) α f) y‖^2 := by
    intro k
    have hop_le := (fderiv ℝ
        (CalabiYau.DivergenceTheorem.scalarOnE
          (I := I) α f) y).le_opNorm ((CalabiYau.Tensor.Coordinates.chartModelBasis E) k)
    have hsq_le : (CalabiYau.Tensor.Coordinates.partialDeriv
            (E := E) k
            (CalabiYau.DivergenceTheorem.scalarOnE
              (I := I) α f) y)^2 ≤
          (‖fderiv ℝ
            (CalabiYau.DivergenceTheorem.scalarOnE
              (I := I) α f) y‖ * ‖(CalabiYau.Tensor.Coordinates.chartModelBasis E) k‖)^2 := by
      unfold CalabiYau.Tensor.Coordinates.partialDeriv
      have habs : |(fderiv ℝ
            (CalabiYau.DivergenceTheorem.scalarOnE
              (I := I) α f) y) ((CalabiYau.Tensor.Coordinates.chartModelBasis E) k)| ≤
          ‖fderiv ℝ
            (CalabiYau.DivergenceTheorem.scalarOnE
              (I := I) α f) y‖ * ‖(CalabiYau.Tensor.Coordinates.chartModelBasis E) k‖ := by
        have h_norm_eq : ‖(fderiv ℝ
            (CalabiYau.DivergenceTheorem.scalarOnE
              (I := I) α f) y) ((CalabiYau.Tensor.Coordinates.chartModelBasis E) k)‖ =
            |(fderiv ℝ
              (CalabiYau.DivergenceTheorem.scalarOnE
                (I := I) α f) y) ((CalabiYau.Tensor.Coordinates.chartModelBasis E) k)| :=
          Real.norm_eq_abs _
        rw [← h_norm_eq]
        exact hop_le
      have h_sq_abs :
          ((fderiv ℝ
              (CalabiYau.DivergenceTheorem.scalarOnE
                (I := I) α f) y) ((CalabiYau.Tensor.Coordinates.chartModelBasis E) k))^2 =
          |(fderiv ℝ
              (CalabiYau.DivergenceTheorem.scalarOnE
                (I := I) α f) y) ((CalabiYau.Tensor.Coordinates.chartModelBasis E) k)|^2 := by
        rw [sq_abs]
      rw [h_sq_abs]
      have hABS_nn : 0 ≤ |(fderiv ℝ
            (CalabiYau.DivergenceTheorem.scalarOnE
              (I := I) α f) y) ((CalabiYau.Tensor.Coordinates.chartModelBasis E) k)| := abs_nonneg _
      have hRHS_nn : 0 ≤ ‖fderiv ℝ
          (CalabiYau.DivergenceTheorem.scalarOnE
            (I := I) α f) y‖ * ‖(CalabiYau.Tensor.Coordinates.chartModelBasis E) k‖ :=
        mul_nonneg (norm_nonneg _) (norm_nonneg _)
      exact pow_le_pow_left₀ hABS_nn habs 2
    refine hsq_le.trans ?_
    rw [mul_pow]
    rw [mul_comm]
  refine (Finset.sum_le_sum (s := Finset.univ) (fun k _ => h_each k)).trans ?_
  rw [← Finset.sum_mul]

noncomputable def toEuclideanBasisSqSum : ℝ :=
  ∑ k : Fin (Module.finrank ℝ E),
    ‖(toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) ((CalabiYau.Tensor.Coordinates.chartModelBasis E) k)‖^2

lemma toEuclideanBasisSqSum_nonneg :
    (0 : ℝ) ≤ toEuclideanBasisSqSum (E := E) :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

omit [IsManifold I ∞ M] in
private lemma chartSmoothExt_toEuclidean_eq_scalarOnE
    (α : M) (f : M → ℝ) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    Sobolev.Chart.chartSmoothExt
        (I := I) (M := M) α f
        ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) y) =
      CalabiYau.DivergenceTheorem.scalarOnE
        (I := I) α f y := by
  classical
  unfold Sobolev.Chart.chartSmoothExt
  have hsymm : (toEuclidean (E := E)).symm
      ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) y) = y :=
    (toEuclidean (E := E)).symm_apply_apply y
  simp only [hsymm, hy, if_true]
  rfl

omit [IsManifold I ∞ M] in
lemma sq_partials_scalarOnE_le_chartSmoothExt_fderiv
    [I.Boundaryless]
    (α : M) {f : M → ℝ}
    (h_smooth_ext : ContDiff ℝ ∞
        (Sobolev.Chart.chartSmoothExt
          (I := I) (M := M) α f)) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    (∑ k : Fin (Module.finrank ℝ E),
        (CalabiYau.Tensor.Coordinates.partialDeriv
            (E := E) k
            (CalabiYau.DivergenceTheorem.scalarOnE
              (I := I) α f) y)^2) ≤
      toEuclideanBasisSqSum (E := E) *
        ‖fderiv ℝ
          (Sobolev.Chart.chartSmoothExt
            (I := I) (M := M) α f)
          ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) y)‖^2 := by
  classical
  have h_target_open : IsOpen (extChartAt I α).target :=
    isOpen_extChartAt_target (I := I) α
  have h_target_nhds : (extChartAt I α).target ∈ 𝓝 y :=
    h_target_open.mem_nhds hy
  have h_eqf : (CalabiYau.DivergenceTheorem.scalarOnE
      (I := I) α f) =ᶠ[𝓝 y]
      ((Sobolev.Chart.chartSmoothExt
        (I := I) (M := M) α f) ∘
        (fun z : E => (toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) z)) := by
    filter_upwards [h_target_nhds] with z hz
    exact (chartSmoothExt_toEuclidean_eq_scalarOnE (I := I) (M := M) α f hz).symm
  have h_fderiv_eq : fderiv ℝ
      (CalabiYau.DivergenceTheorem.scalarOnE
        (I := I) α f) y =
      fderiv ℝ
        ((Sobolev.Chart.chartSmoothExt
          (I := I) (M := M) α f) ∘
          (fun z : E => (toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) z)) y :=
    h_eqf.fderiv_eq
  have h_ChartSmoothExt_diffAt : DifferentiableAt ℝ
      (Sobolev.Chart.chartSmoothExt
        (I := I) (M := M) α f)
      ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) y) :=
    h_smooth_ext.differentiable (by simp) _
  have h_TE_diffAt : DifferentiableAt ℝ
      (fun z : E => (toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) z) y :=
    (toEuclidean (E := E) : E ≃L[ℝ] EuclN_E).differentiable.differentiableAt
  have h_fderiv_comp : fderiv ℝ
      ((Sobolev.Chart.chartSmoothExt
        (I := I) (M := M) α f) ∘
        (fun z : E => (toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) z)) y =
      (fderiv ℝ
        (Sobolev.Chart.chartSmoothExt
          (I := I) (M := M) α f)
        ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) y)).comp
        (fderiv ℝ
          (fun z : E => (toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) z) y) :=
    fderiv_comp y h_ChartSmoothExt_diffAt h_TE_diffAt
  have h_TE_fderiv : fderiv ℝ
      (fun z : E => (toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) z) y =
      ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) :
        E →L[ℝ] EuclN_E) :=
    (toEuclidean (E := E) : E ≃L[ℝ] EuclN_E).fderiv
  rw [h_TE_fderiv] at h_fderiv_comp
  have h_each : ∀ k,
      (CalabiYau.Tensor.Coordinates.partialDeriv
          (E := E) k
          (CalabiYau.DivergenceTheorem.scalarOnE
            (I := I) α f) y)^2 ≤
        ‖fderiv ℝ
          (Sobolev.Chart.chartSmoothExt
            (I := I) (M := M) α f)
          ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) y)‖^2 *
        ‖(toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) ((CalabiYau.Tensor.Coordinates.chartModelBasis E) k)‖^2 := by
    intro k
    have h_partial_eq :
        CalabiYau.Tensor.Coordinates.partialDeriv
            (E := E) k
            (CalabiYau.DivergenceTheorem.scalarOnE
              (I := I) α f) y =
          (fderiv ℝ
            (Sobolev.Chart.chartSmoothExt
              (I := I) (M := M) α f)
            ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) y))
              ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E)
                ((CalabiYau.Tensor.Coordinates.chartModelBasis E) k)) := by
      unfold CalabiYau.Tensor.Coordinates.partialDeriv
      rw [h_fderiv_eq, h_fderiv_comp]
      rfl
    rw [h_partial_eq]
    have h_op_bound :
        ‖(fderiv ℝ
            (Sobolev.Chart.chartSmoothExt
              (I := I) (M := M) α f)
            ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) y))
            ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E)
              ((CalabiYau.Tensor.Coordinates.chartModelBasis E) k))‖ ≤
          ‖fderiv ℝ
            (Sobolev.Chart.chartSmoothExt
              (I := I) (M := M) α f)
            ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) y)‖ *
          ‖(toEuclidean (E := E) : E ≃L[ℝ] EuclN_E)
            ((CalabiYau.Tensor.Coordinates.chartModelBasis E) k)‖ :=
      (fderiv ℝ
        (Sobolev.Chart.chartSmoothExt
          (I := I) (M := M) α f)
        ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) y)).le_opNorm _
    have h_lhs_norm : ‖(fderiv ℝ
        (Sobolev.Chart.chartSmoothExt
          (I := I) (M := M) α f)
        ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) y))
        ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E)
          ((CalabiYau.Tensor.Coordinates.chartModelBasis E) k))‖ =
        |((fderiv ℝ
          (Sobolev.Chart.chartSmoothExt
            (I := I) (M := M) α f)
          ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) y))
          ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E)
            ((CalabiYau.Tensor.Coordinates.chartModelBasis E) k)))| :=
      Real.norm_eq_abs _
    rw [h_lhs_norm] at h_op_bound
    have h_sq_abs :
        ((fderiv ℝ
          (Sobolev.Chart.chartSmoothExt
            (I := I) (M := M) α f)
          ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) y))
            ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E)
              ((CalabiYau.Tensor.Coordinates.chartModelBasis E) k)))^2 =
        |((fderiv ℝ
            (Sobolev.Chart.chartSmoothExt
              (I := I) (M := M) α f)
            ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) y))
            ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E)
              ((CalabiYau.Tensor.Coordinates.chartModelBasis E) k)))|^2 :=
      (sq_abs _).symm
    rw [h_sq_abs]
    have h_op_nn : 0 ≤ ‖fderiv ℝ
        (Sobolev.Chart.chartSmoothExt
          (I := I) (M := M) α f)
        ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) y)‖ *
        ‖(toEuclidean (E := E) : E ≃L[ℝ] EuclN_E)
          ((CalabiYau.Tensor.Coordinates.chartModelBasis E) k)‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have h_abs_nn :
        0 ≤ |((fderiv ℝ
              (Sobolev.Chart.chartSmoothExt
                (I := I) (M := M) α f)
              ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) y))
              ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E)
                ((CalabiYau.Tensor.Coordinates.chartModelBasis E) k)))| :=
      abs_nonneg _
    have h_pow_le := pow_le_pow_left₀ h_abs_nn h_op_bound 2
    refine h_pow_le.trans ?_
    rw [mul_pow]
  refine (Finset.sum_le_sum (s := Finset.univ) (fun k _ => h_each k)).trans ?_
  unfold toEuclideanBasisSqSum
  rw [← Finset.mul_sum]
  rw [mul_comm]

omit [IsManifold I ∞ M] in
lemma chartSmoothExt_eq_zero_off_image_tsupport_local
    (α : M) {f : M → ℝ} {y : EuclN_E}
    (hy_off : y ∉ (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport f))) :
    Sobolev.Chart.chartSmoothExt
        (I := I) (M := M) α f y = 0 := by
  classical
  by_cases hy_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target
  · have hsymm_source : (extChartAt I α).symm
        ((toEuclidean (E := E)).symm y) ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hy_target
    have hxsupp : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∉ tsupport f := by
      intro hin
      apply hy_off
      refine ⟨(toEuclidean (E := E)).symm y, ?_, ?_⟩
      · refine ⟨(extChartAt I α).symm ((toEuclidean (E := E)).symm y), hin, ?_⟩
        exact (extChartAt I α).right_inv hy_target
      · exact (toEuclidean (E := E)).apply_symm_apply y
    have hf_zero : f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) = 0 :=
      image_eq_zero_of_notMem_tsupport hxsupp
    change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
              f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            else (0 : ℝ)) = 0
    rw [if_pos hy_target, hf_zero]
  · change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
              f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            else (0 : ℝ)) = 0
    rw [if_neg hy_target]

omit [FiniteDimensional ℝ E] in
private lemma euclN_norm_le_sum_components_norms_local (w : EuclN_E) :
    ‖w‖ ≤ ∑ i : Fin (Module.finrank ℝ E), ‖w i‖ := by
  classical
  have h_w_sum : w = ∑ i : Fin (Module.finrank ℝ E),
      EuclideanSpace.single i (w i) := by
    ext j
    simp [Finset.sum_apply]
  conv_lhs => rw [h_w_sum]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  simp

omit [FiniteDimensional ℝ E] in
private lemma norm_fderiv_le_sum_partials_local_local (ψ : EuclN_E → ℝ)
    (y : EuclN_E) :
    ‖fderiv ℝ ψ y‖ ≤
      ∑ i : Fin (Module.finrank ℝ E),
        ‖(fderiv ℝ ψ y) (EuclideanSpace.single i (1 : ℝ))‖ := by
  classical
  set v : EuclN_E :=
    (InnerProductSpace.toDual ℝ EuclN_E).symm (fderiv ℝ ψ y) with hv_def
  have hv_map : (InnerProductSpace.toDual ℝ EuclN_E) v = fderiv ℝ ψ y := by
    simp [v]
  have h_fderiv_norm_eq_v : ‖fderiv ℝ ψ y‖ = ‖v‖ := by simp [v]
  have h_v_eq_components : v =
      WithLp.toLp 2 (fun i : Fin (Module.finrank ℝ E) =>
        (fderiv ℝ ψ y) (EuclideanSpace.single i 1)) := by
    ext i
    calc
      v i = inner ℝ v (EuclideanSpace.single i (1 : ℝ)) := by
        simpa using
          (EuclideanSpace.inner_single_right (i := i) (a := (1 : ℝ)) v).symm
      _ = ((InnerProductSpace.toDual ℝ EuclN_E) v) (EuclideanSpace.single i (1 : ℝ)) := by
        rw [InnerProductSpace.toDual_apply_apply]
      _ = (fderiv ℝ ψ y) (EuclideanSpace.single i (1 : ℝ)) := by rw [hv_map]
      _ = (WithLp.toLp 2 (fun j : Fin (Module.finrank ℝ E) =>
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))) i := by simp
  rw [h_fderiv_norm_eq_v, h_v_eq_components]
  refine (euclN_norm_le_sum_components_norms_local _).trans ?_
  apply le_of_eq
  refine Finset.sum_congr rfl ?_
  intro i _
  simp

omit [FiniteDimensional ℝ E] in
private lemma eLpNorm_norm_fderiv_le_sum_eLpNorm_partials_local
    {q : ℝ≥0∞} (hq_one : 1 ≤ q) {μ : Measure EuclN_E}
    {ψ : EuclN_E → ℝ} (h_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    eLpNorm (fun z : EuclN_E => ‖fderiv ℝ ψ z‖) q μ ≤
      ∑ i : Fin (Module.finrank ℝ E),
        eLpNorm
          (fun z : EuclN_E => (fderiv ℝ ψ z) (EuclideanSpace.single i 1)) q μ := by
  classical
  have h_aesm_comp : ∀ i : Fin (Module.finrank ℝ E),
      AEStronglyMeasurable
        (fun z : EuclN_E => (fderiv ℝ ψ z) (EuclideanSpace.single i 1)) μ := by
    intro i
    have h_cont : Continuous
        (fun z : EuclN_E => (fderiv ℝ ψ z) (EuclideanSpace.single i 1)) :=
      (h_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
    exact h_cont.aestronglyMeasurable
  have h_pt : ∀ z : EuclN_E,
      ‖fderiv ℝ ψ z‖ ≤ ∑ i : Fin (Module.finrank ℝ E),
        ‖(fderiv ℝ ψ z) (EuclideanSpace.single i 1)‖ :=
    fun z => norm_fderiv_le_sum_partials_local_local ψ z
  have h_step1 : eLpNorm (fun z : EuclN_E => ‖fderiv ℝ ψ z‖) q μ ≤
      eLpNorm (fun z : EuclN_E =>
        ∑ i : Fin (Module.finrank ℝ E),
          ‖(fderiv ℝ ψ z) (EuclideanSpace.single i 1)‖) q μ := by
    apply eLpNorm_mono_real
    intro z
    have hh := h_pt z
    have h_norm : ‖‖fderiv ℝ ψ z‖‖ = ‖fderiv ℝ ψ z‖ :=
      Real.norm_of_nonneg (norm_nonneg _)
    rw [h_norm]
    exact hh
  refine h_step1.trans ?_
  have h_sum_le := eLpNorm_sum_le (μ := μ) (p := q)
    (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
    (f := fun i => fun z : EuclN_E =>
      ‖(fderiv ℝ ψ z) (EuclideanSpace.single i 1)‖)
    (fun i _ => (h_aesm_comp i).norm) hq_one
  have h_lhs_eq :
      (fun z : EuclN_E =>
        ∑ i : Fin (Module.finrank ℝ E),
          ‖(fderiv ℝ ψ z) (EuclideanSpace.single i 1)‖) =
        ∑ i : Fin (Module.finrank ℝ E),
          fun z : EuclN_E => ‖(fderiv ℝ ψ z) (EuclideanSpace.single i 1)‖ := by
    funext z
    simp [Finset.sum_apply]
  rw [h_lhs_eq]
  refine h_sum_le.trans ?_
  apply Finset.sum_le_sum
  intro i _
  rw [eLpNorm_norm]

omit [FiniteDimensional ℝ E] in
private lemma classical_partial_ae_eq_chosenWeakPartial_local_local
    {q : ℝ≥0∞} (hq_one : 1 ≤ q) {Ω : Set EuclN_E} (hΩ_open : IsOpen Ω)
    {ψ : EuclN_E → ℝ} (h_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_compact : HasCompactSupport ψ) (hψ_support : tsupport ψ ⊆ Ω)
    (i : Fin (Module.finrank ℝ E)) :
    (fun z : EuclN_E => (fderiv ℝ ψ z) (EuclideanSpace.single i 1))
      =ᵐ[volume.restrict Ω]
      Sobolev.Euclidean.chosenWeakPartialOrZero
        q i ψ Ω := by
  classical
  have hψ_mem : Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 q ψ Ω :=
    Sobolev.Euclidean.MemWkp_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hΩ_open h_smooth hψ_compact hψ_support hq_one 1
  have hψ_W1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) q ψ Ω :=
    Sobolev.Euclidean.MemWkp.one_iff_memW1p.mp hψ_mem
  have h_classical_isWeak :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
        (fun z : EuclN_E => (fderiv ℝ ψ z) (EuclideanSpace.single i 1)) ψ Ω :=
    DeGiorgi.HasWeakPartialDeriv.of_contDiff (Ω := Ω) (i := i) (f := ψ)
      hΩ_open (h_smooth.of_le (by norm_cast))
  have h_chosen_isWeak :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
        (Sobolev.Euclidean.chosenWeakPartialOrZero
          q i ψ Ω) ψ Ω :=
    Sobolev.Euclidean.chosenWeakPartialOrZero_isWeakPartial_of_mem
      hψ_W1p i
  have h_classical_local : LocallyIntegrable
      (fun z : EuclN_E => (fderiv ℝ ψ z) (EuclideanSpace.single i 1))
      (volume.restrict Ω) := by
    have h_cont : Continuous
        (fun z : EuclN_E => (fderiv ℝ ψ z) (EuclideanSpace.single i 1)) :=
      (h_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
    exact h_cont.locallyIntegrable.mono_measure Measure.restrict_le_self
  have h_chosen_local : LocallyIntegrable
      (Sobolev.Euclidean.chosenWeakPartialOrZero
        q i ψ Ω)
      (volume.restrict Ω) :=
    (Sobolev.Euclidean.chosenWeakPartialOrZero_memLp_of_mem
      hψ_W1p i).locallyIntegrable hq_one
  exact DeGiorgi.HasWeakPartialDeriv.ae_eq (Ω := Ω) hΩ_open
    h_classical_isWeak h_chosen_isWeak h_classical_local h_chosen_local

omit [FiniteDimensional ℝ E] in
lemma eLpNorm_norm_fderiv_le_d_mul_wkpNorm_local
    [NeZero (Module.finrank ℝ E)]
    {q : ℝ≥0∞} (hq_one : 1 ≤ q) {Ω : Set EuclN_E} (hΩ_open : IsOpen Ω)
    {ψ : EuclN_E → ℝ} (h_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_compact : HasCompactSupport ψ) (hψ_support : tsupport ψ ⊆ Ω) :
    eLpNorm (fun z : EuclN_E => ‖fderiv ℝ ψ z‖) q (volume.restrict Ω) ≤
      ((Module.finrank ℝ E : ℕ) : ℝ≥0∞) *
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 q ψ Ω := by
  classical
  have h_grad_le := eLpNorm_norm_fderiv_le_sum_eLpNorm_partials_local
    (q := q) hq_one (μ := volume.restrict Ω) h_smooth
  refine h_grad_le.trans ?_
  have h_each_eq : ∀ i : Fin (Module.finrank ℝ E),
      eLpNorm
        (fun z : EuclN_E => (fderiv ℝ ψ z) (EuclideanSpace.single i 1)) q
        (volume.restrict Ω) =
      eLpNorm
        (Sobolev.Euclidean.chosenWeakPartialOrZero
          q i ψ Ω) q (volume.restrict Ω) := fun i =>
    eLpNorm_congr_ae (classical_partial_ae_eq_chosenWeakPartial_local_local
      hq_one hΩ_open h_smooth hψ_compact hψ_support i)
  have h_step1 :
      ∑ i : Fin (Module.finrank ℝ E),
        eLpNorm
          (fun z : EuclN_E => (fderiv ℝ ψ z) (EuclideanSpace.single i 1)) q
          (volume.restrict Ω)
        = ∑ i : Fin (Module.finrank ℝ E),
          eLpNorm
            (Sobolev.Euclidean.chosenWeakPartialOrZero
              q i ψ Ω) q (volume.restrict Ω) :=
    Finset.sum_congr rfl (fun i _ => h_each_eq i)
  rw [h_step1]
  have hWkpEq :
      Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 q ψ Ω =
        ∑ j ∈ Finset.range 2,
          ∑ β : Fin j → Fin (Module.finrank ℝ E),
            eLpNorm
              (Sobolev.Euclidean.iterWeakPartial
                (d := Module.finrank ℝ E) q j β ψ Ω)
              q (volume.restrict Ω) :=
    Sobolev.Euclidean.wkpNorm_eq_sum 1 q ψ Ω
  have h_j1_term :
      (∑ β : Fin 1 → Fin (Module.finrank ℝ E),
          eLpNorm
            (Sobolev.Euclidean.iterWeakPartial
              (d := Module.finrank ℝ E) q 1 β ψ Ω) q (volume.restrict Ω)) =
        ∑ i : Fin (Module.finrank ℝ E),
          eLpNorm
            (Sobolev.Euclidean.chosenWeakPartialOrZero
              q i ψ Ω) q (volume.restrict Ω) := by
    have h_unfold : ∀ β : Fin 1 → Fin (Module.finrank ℝ E),
        eLpNorm
          (Sobolev.Euclidean.iterWeakPartial
            (d := Module.finrank ℝ E) q 1 β ψ Ω) q (volume.restrict Ω) =
          eLpNorm
            (Sobolev.Euclidean.chosenWeakPartialOrZero
              q (β 0) ψ Ω) q (volume.restrict Ω) := by
      intro β
      have hit :
          Sobolev.Euclidean.iterWeakPartial
              (d := Module.finrank ℝ E) q 1 β ψ Ω =
            Sobolev.Euclidean.chosenWeakPartialOrZero
              q (β 0) ψ Ω := by
        rw [Sobolev.Euclidean.iterWeakPartial_succ]
        simp [Sobolev.Euclidean.iterWeakPartial_zero]
      rw [hit]
    rw [Finset.sum_congr rfl (fun β _ => h_unfold β)]
    let e : (Fin 1 → Fin (Module.finrank ℝ E)) ≃ Fin (Module.finrank ℝ E) :=
      { toFun := fun β => β 0
        invFun := fun i _ => i
        left_inv := fun β => by
          funext j
          have hj : j = 0 := Subsingleton.elim _ _
          rw [hj]
        right_inv := fun _ => rfl }
    exact Fintype.sum_equiv e
      (fun β =>
        eLpNorm
          (Sobolev.Euclidean.chosenWeakPartialOrZero
            q (β 0) ψ Ω) q (volume.restrict Ω))
      (fun i =>
        eLpNorm
          (Sobolev.Euclidean.chosenWeakPartialOrZero
            q i ψ Ω) q (volume.restrict Ω))
      (fun _ => rfl)
  have h_le_wkp :
      (∑ i : Fin (Module.finrank ℝ E),
          eLpNorm
            (Sobolev.Euclidean.chosenWeakPartialOrZero
              q i ψ Ω) q (volume.restrict Ω)) ≤
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 q ψ Ω := by
    rw [hWkpEq, Finset.sum_range_succ, Finset.sum_range_one, ← h_j1_term]
    refine le_add_of_nonneg_left ?_
    exact zero_le
  refine h_le_wkp.trans ?_
  have hd_pos : 0 < Module.finrank ℝ E := NeZero.pos _
  have hd_one_le : (1 : ℝ≥0∞) ≤ ((Module.finrank ℝ E : ℕ) : ℝ≥0∞) := by
    exact_mod_cast hd_pos
  conv_lhs => rw [show Sobolev.Euclidean.iteratedWeakSobolevNorm
    (d := Module.finrank ℝ E) 1 q ψ Ω = 1 *
    Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) 1 q ψ Ω from
    (one_mul _).symm]
  gcongr

lemma wkpNorm_chartSmoothExt_pou_mul_le_wkpNormChart
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    (α : M) {q : ℝ≥0∞} (hq_one : 1 ≤ q) (u : M → ℝ) :
    Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 q
        (Sobolev.Chart.chartSmoothExt
          (I := I) (M := M) α
          (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x))
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) ≤
      wkpNormChart (I := I) (M := M) 1 q u := by
  classical
  have h_ae :
      Sobolev.Chart.chartSmoothExt
          (I := I) (M := M) α
          (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x)
        =ᵐ[volume.restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)]
        Sobolev.Chart.chartPushed
          (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u := by
    refine (MeasureTheory.ae_restrict_iff'
      (Sobolev.Chart.chartTargetEuclid_measurableSet
        (I := I) (M := M) α)).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy
    have hsymm_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
      rw [Sobolev.Chart.chartTargetEuclid_eq_preimage_symm
        (I := I) (M := M)] at hy
      exact hy
    change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
      else (0 : ℝ)) =
      Sobolev.Chart.chartPushed
        (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u y
    rw [if_pos hsymm_target]
    rfl
  have h_eq :
      Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 q
          (Sobolev.Chart.chartSmoothExt
            (I := I) (M := M) α
            (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) x * u x))
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α) =
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 q
          (Sobolev.Chart.chartPushed
            (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α) :=
    Sobolev.Euclidean.wkpNorm_congr_ae
      (d := Module.finrank ℝ E) hq_one
      (Sobolev.Chart.chartTargetEuclid_isOpen
        (I := I) (M := M) α) h_ae
  rw [h_eq]
  let _ := g
  unfold wkpNormChart
  exact ENNReal.le_tsum α

end Equivalence
end Sobolev
