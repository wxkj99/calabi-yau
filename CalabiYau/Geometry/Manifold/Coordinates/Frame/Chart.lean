-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Geometry/Coordinates/Frame/Chart.lean
-- Locally modified.
module
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
public import CalabiYau.Geometry.Manifold.Tensor.Coordinates.ModelBasis
public import CalabiYau.Geometry.Manifold.Bundle.TangentSpace
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace CalabiYau.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in
lemma trivializationAt_baseSet_eq_chartAt_source (x₀ : M) :
    (trivializationAt E (TangentSpace I) x₀).baseSet =
      (chartAt H x₀).source :=
  rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] in
lemma extChartAt_source_eq_chartAt_source (x₀ : M) :
    (extChartAt I x₀).source = (chartAt H x₀).source := by
  rw [extChartAt_source]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in
lemma extChartAt_symm_mem_trivializationAt_baseSet (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    (extChartAt I x₀).symm y ∈
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  have hsource : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source :=
    (extChartAt I x₀).map_target hy
  rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
  exact hsource

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Module.Finite ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
def chartBasisVecFiber (x₀ : M) (i : Fin (Module.finrank ℝ E)) (x : M) :
    TangentSpace I x :=
  (trivializationAt E (TangentSpace I) x₀).symmL ℝ x ((chartModelBasis E) i)

def chartBasisVec (x₀ : M) (i : Fin (Module.finrank ℝ E)) :
    M → TotalSpace E (TangentSpace I : M → Type _) :=
  fun x => TotalSpace.mk' E x (chartBasisVecFiber (I := I) x₀ i x)

@[simp] lemma chartBasisVec_snd (x₀ : M) (i : Fin (Module.finrank ℝ E)) (x : M) :
    (chartBasisVec (I := I) x₀ i x).2 = chartBasisVecFiber (I := I) x₀ i x := rfl

@[simp] lemma chartBasisVec_proj (x₀ : M) (i : Fin (Module.finrank ℝ E)) (x : M) :
    (chartBasisVec (I := I) x₀ i x).proj = x := rfl

lemma trivializationAt_chartBasisVec_snd
    (x₀ : M) (i : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    (trivializationAt E (TangentSpace I) x₀
        ⟨x, chartBasisVecFiber (I := I) x₀ i x⟩).2
      = (chartModelBasis E) i := by
  have h := (trivializationAt E (TangentSpace I) x₀).apply_mk_symm hx
    ((chartModelBasis E) i)
  rw [chartBasisVecFiber, Trivialization.symmL_apply _ hx]
  exact congrArg Prod.snd h

lemma chartBasisVec_contMDiffOn
    (x₀ : M) (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (chartBasisVec (I := I) x₀ i)
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  have hiff :=
    ((trivializationAt E (TangentSpace I) x₀)).contMDiffOn_section_baseSet_iff
      (IB := I) (n := ∞) (s := fun x => chartBasisVecFiber (I := I) x₀ i x)
  refine hiff.mpr ?_
  have hconst : ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun _ : M => (chartModelBasis E) i)
      (trivializationAt E (TangentSpace I) x₀).baseSet :=
    contMDiffOn_const
  refine hconst.congr ?_
  intro x hx
  exact (trivializationAt_chartBasisVec_snd (I := I) x₀ i hx)

def chartBasisFamily (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
  (chartModelBasis E).map
    (ContinuousLinearEquiv.toLinearEquiv
      ((trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt ℝ x hx).symm)

lemma chartBasisFamily_apply (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (i : Fin (Module.finrank ℝ E)) :
    chartBasisFamily (I := I) x₀ hx i =
      chartBasisVecFiber (I := I) x₀ i x := by
  unfold chartBasisFamily chartBasisVecFiber
  rw [Module.Basis.map_apply]
  exact congrFun ((trivializationAt E (TangentSpace I) x₀).symm_continuousLinearEquivAt_eq hx)
    ((chartModelBasis E) i)

lemma chartBasisFamily_linearIndependent (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    LinearIndependent ℝ
      (fun i : Fin (Module.finrank ℝ E) =>
        chartBasisVecFiber (I := I) x₀ i x) := by
  have h := (chartBasisFamily (I := I) x₀ hx).linearIndependent
  have hcongr : (chartBasisFamily (I := I) x₀ hx : Fin (Module.finrank ℝ E) → TangentSpace I x)
      = fun i => chartBasisVecFiber (I := I) x₀ i x := by
    funext i
    exact chartBasisFamily_apply (I := I) x₀ hx i
  rw [← hcongr]
  exact h

end

end CalabiYau.Tensor.Coordinates
