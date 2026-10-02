-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Spectral/Tensor/ChartTensor/Inner/InnerJointCont.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Riemannian.TensorInner.ChartTensor.Inner.Defs
public import CalabiYau.Geometry.Manifold.Tensor.RSTensor.Defs
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open Bundle Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace CalabiYau.ChartTensor

open CalabiYau.Tensor
open CalabiYau.RiemannianVolume
open CalabiYau.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section Algebra

private lemma chartTensorInnerPointwise_rs_model_basis_expand
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α b : M)
    {ι : Type*} [Fintype ι]
    (basis : Module.Basis ι ℝ (TensorRSModel r s ℝ E))
    (T : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwiseRsModel (I := I) (M := M) g r s α b T T =
      ∑ i : ι, ∑ j : ι,
        (basis.coord i T) * (basis.coord j T) *
          chartTensorInnerPointwiseRsModel (I := I) (M := M) g r s α b
            (basis i) (basis j) := by
  classical
  set a : ι → ℝ := fun i => basis.coord i T with ha_def
  have hT : T = ∑ i : ι, a i • basis i := by
    have hrepr := basis.linearCombination_repr T
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype] at hrepr
    · exact hrepr.symm
    · intros; rw [zero_smul]
  have hgen_left : ∀ (S : TensorRSModel r s ℝ E),
      chartTensorInnerPointwiseRsModel (I := I) (M := M) g r s α b
        (∑ i : ι, a i • basis i) S =
        ∑ i : ι, (a i) *
          chartTensorInnerPointwiseRsModel (I := I) (M := M) g r s α b
            (basis i) S := by
    intro S
    let LL : TensorRSModel r s ℝ E →ₗ[ℝ] ℝ :=
      { toFun := fun T' =>
          chartTensorInnerPointwiseRsModel (I := I) (M := M) g r s α b T' S
        map_add' := fun T₁ T₂ =>
          chartTensorInnerPointwise_rs_model_add_left
            (I := I) (M := M) g r s α b T₁ T₂ S
        map_smul' := fun c T' => by
          change chartTensorInnerPointwiseRsModel (I := I) (M := M)
              g r s α b (c • T') S = c • _
          rw [chartTensorInnerPointwise_rs_model_smul_left]
          rfl }
    have hLL_sum : LL (∑ i : ι, a i • basis i) = ∑ i : ι, LL (a i • basis i) :=
      map_sum LL _ _
    change LL _ = _
    rw [hLL_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [LL.map_smul]
    rfl
  have hgen_right : ∀ (i : ι),
      chartTensorInnerPointwiseRsModel (I := I) (M := M) g r s α b
        (basis i) (∑ j : ι, a j • basis j) =
        ∑ j : ι, (a j) *
          chartTensorInnerPointwiseRsModel (I := I) (M := M) g r s α b
            (basis i) (basis j) := by
    intro i
    let RR : TensorRSModel r s ℝ E →ₗ[ℝ] ℝ :=
      { toFun := fun S' =>
          chartTensorInnerPointwiseRsModel (I := I) (M := M)
            g r s α b (basis i) S'
        map_add' := fun S₁ S₂ =>
          chartTensorInnerPointwise_rs_model_add_right
            (I := I) (M := M) g r s α b (basis i) S₁ S₂
        map_smul' := fun c S' => by
          change chartTensorInnerPointwiseRsModel (I := I) (M := M)
              g r s α b (basis i) (c • S') = c • _
          rw [chartTensorInnerPointwise_rs_model_smul_right]
          rfl }
    have hRR_sum : RR (∑ j : ι, a j • basis j) = ∑ j : ι, RR (a j • basis j) :=
      map_sum RR _ _
    change RR _ = _
    rw [hRR_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [RR.map_smul]
    rfl
  calc chartTensorInnerPointwiseRsModel (I := I) (M := M) g r s α b T T
      = chartTensorInnerPointwiseRsModel (I := I) (M := M) g r s α b
          (∑ i : ι, a i • basis i) (∑ j : ι, a j • basis j) := by rw [← hT]
    _ = ∑ i : ι, (a i) *
          chartTensorInnerPointwiseRsModel (I := I) (M := M) g r s α b
            (basis i) (∑ j : ι, a j • basis j) := hgen_left _
    _ = ∑ i : ι, (a i) *
          ∑ j : ι, (a j) *
            chartTensorInnerPointwiseRsModel (I := I) (M := M)
              g r s α b (basis i) (basis j) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [hgen_right i]
    _ = ∑ i : ι, ∑ j : ι, (a i) * (a j) *
          chartTensorInnerPointwiseRsModel (I := I) (M := M)
            g r s α b (basis i) (basis j) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro j _
          ring

end Algebra

section JointCont

variable [NeZero (Module.finrank ℝ E)]

omit [NeZero (Module.finrank ℝ E)] in
theorem chartTensorInnerPointwise_rs_model_quadratic_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ContinuousOn
      (fun bT : M × TensorRSModel r s ℝ E =>
          chartTensorInnerPointwiseRsModel (I := I) (M := M)
            g r s α bT.1 bT.2 bT.2)
      ((trivializationAt E (TangentSpace I) α).baseSet ×ˢ Set.univ) := by
  classical
  let ι := Fin (Module.finrank ℝ (TensorRSModel r s ℝ E))
  let basis : Module.Basis ι ℝ (TensorRSModel r s ℝ E) :=
    Module.finBasis ℝ (TensorRSModel r s ℝ E)
  let φ : ι → (TensorRSModel r s ℝ E →ₗ[ℝ] ℝ) := fun i => basis.coord i
  have hφ_cont : ∀ i, Continuous (φ i) := fun i =>
    LinearMap.continuous_of_finiteDimensional (φ i)
  set baseSet : Set M := (trivializationAt E (TangentSpace I) α).baseSet
    with hbaseSet_def
  have hF_cont : ∀ i j : ι,
      ContinuousOn
        (fun b : M => chartTensorInnerPointwiseRsModel
          (I := I) (M := M) g r s α b (basis i) (basis j))
        baseSet := fun i j =>
    (chartTensorInnerPointwise_rs_model_contMDiffOn
        (I := I) (M := M) g r s α (basis i) (basis j)).continuousOn
  have hexpand : ∀ b T,
      chartTensorInnerPointwiseRsModel (I := I) (M := M) g r s α b T T =
        ∑ i : ι, ∑ j : ι,
          (φ i T) * (φ j T) *
            chartTensorInnerPointwiseRsModel
              (I := I) (M := M) g r s α b (basis i) (basis j) := by
    intro b T
    exact
      chartTensorInnerPointwise_rs_model_basis_expand
        (I := I) (M := M) g r s α b basis T
  have hcontOn :
      ContinuousOn
        (fun bT : M × TensorRSModel r s ℝ E =>
            ∑ i : ι, ∑ j : ι,
              (φ i bT.2) * (φ j bT.2) *
                chartTensorInnerPointwiseRsModel
                  (I := I) (M := M) g r s α bT.1 (basis i) (basis j))
        (baseSet ×ˢ Set.univ) := by
    refine continuousOn_finsetSum _ ?_
    intro i _
    refine continuousOn_finsetSum _ ?_
    intro j _
    have hφi : ContinuousOn
        (fun bT : M × TensorRSModel r s ℝ E => φ i bT.2)
        (baseSet ×ˢ Set.univ) :=
      ((hφ_cont i).comp continuous_snd).continuousOn
    have hφj : ContinuousOn
        (fun bT : M × TensorRSModel r s ℝ E => φ j bT.2)
        (baseSet ×ˢ Set.univ) :=
      ((hφ_cont j).comp continuous_snd).continuousOn
    have hF : ContinuousOn
        (fun bT : M × TensorRSModel r s ℝ E =>
          chartTensorInnerPointwiseRsModel
            (I := I) (M := M) g r s α bT.1 (basis i) (basis j))
        (baseSet ×ˢ Set.univ) :=
      (hF_cont i j).comp continuousOn_fst (fun _ hp => hp.1)
    exact (hφi.mul hφj).mul hF
  refine hcontOn.congr ?_
  intro bT _
  exact (hexpand bT.1 bT.2)

end JointCont

end CalabiYau.ChartTensor

end
