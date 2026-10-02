-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Tensor/RSTensor/Defs.lean
-- Locally modified.
/-
Authors: Yuan Liao, Jack McCarthy
Modified by: Ziyang Qin
-/
module
public import CalabiYau.Geometry.Manifold.Tensor.Multilinear.Bundle.Fiber
public import CalabiYau.Geometry.Manifold.Tensor.Multilinear.Curry.Basic
public import CalabiYau.Geometry.Manifold.Bundle.TangentSpace
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
open CalabiYau.Tensor.Multilinear

namespace CalabiYau
namespace Tensor0SBundle
noncomputable section

open Bundle Set IsManifold ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]
variable {x' : M}
variable {r s : ℕ}

omit [IsManifold I 1 M] in
@[instance_reducible]
noncomputable instance tangentSpaceNormedAddCommGroup (x : M) :
    NormedAddCommGroup (TangentSpace I x) where
  toNorm := by
    unfold TangentSpace
    infer_instance
  toAddCommGroup := instAddCommGroupTangentSpace I x
  toMetricSpace :=
    let m : MetricSpace (TangentSpace I x) := by
      unfold TangentSpace
      infer_instance
    m.replaceTopology (by unfold TangentSpace; rfl)
  dist_eq := by
    intro v w
    unfold TangentSpace at v w ⊢
    exact NormedAddCommGroup.dist_eq v w

omit [IsManifold I 1 M] in
@[instance_reducible]
noncomputable instance tangentSpaceNormedSpace (x : M) :
    NormedSpace 𝕜 (TangentSpace I x) where
  toModule := instModuleTangentSpace I x
  norm_smul_le := by
    intro c v
    unfold TangentSpace at v ⊢
    exact norm_smul_le c v

omit [IsManifold I 1 M] in
instance tangentSpace_finiteDimensional (x : M) :
    FiniteDimensional 𝕜 (TangentSpace I x) := by
  change FiniteDimensional 𝕜 E
  infer_instance

omit [IsManifold I 1 M] in
instance tangentSpace_moduleFree (x : M) :
    Module.Free 𝕜 (TangentSpace I x) := by
  change Module.Free 𝕜 E
  infer_instance

local instance tangentSpaceFiberBundleExplicit :
    FiberBundle E (TangentSpace I : M → Type _) :=
  TangentSpace.fiberBundle (I := I) (M := M)

local instance tangentSpace_vectorBundleExplicit :
    VectorBundle 𝕜 E (TangentSpace I : M → Type _) :=
  TangentSpace.vectorBundle (I := I) (M := M)

@[reducible]
def Tensor0SModel (s : ℕ) (𝕜 : Type*) (E : Type*) [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [_hfd : FiniteDimensional 𝕜 E] :=
  let _ := _hfd
  ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜

@[ext]
theorem Tensor0SModel.ext {f g : Tensor0SModel s 𝕜 E}
    (h : ∀ v, f v = g v) : f = g := by
  dsimp [Tensor0SModel] at f g
  exact ContinuousMultilinearMap.ext h

@[reducible]
def TensorRSModel (r s : ℕ) (𝕜 : Type*) (E : Type*) [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] :=
  (Tensor0SModel r 𝕜 E) →L[𝕜] (Tensor0SModel s 𝕜 E)

def Tensor0SSpace (s : ℕ) (I : ModelWithCorners 𝕜 E H)
    [hMfd : IsManifold I 1 M] (x : M) : Type _ :=
  let _ := hMfd
  Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I : M → Type _) x

@[reducible]
instance tensor0SSpaceTopologicalSpace (s : ℕ) (x : M) :
    TopologicalSpace (Tensor0SSpace s I x) :=
  inferInstanceAs (TopologicalSpace (Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I : M → Type _) x))

@[reducible]
instance tensor0SSpaceAddCommGroup (s : ℕ) (x : M) :
    AddCommGroup (Tensor0SSpace s I x) :=
  inferInstanceAs (AddCommGroup (Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I : M → Type _) x))

@[reducible]
instance tensor0SSpaceModule (s : ℕ) (x : M) :
    Module 𝕜 (Tensor0SSpace s I x) :=
  inferInstanceAs (Module 𝕜 (Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I : M → Type _) x))

instance tensor0SSpace_isTopologicalAddGroup (s : ℕ) (x : M) :
    IsTopologicalAddGroup (Tensor0SSpace s I x) :=
  @Bundle.continuousMultilinearMap.instIsTopologicalAddGroup
    𝕜 _ M _ E _ _ (TangentSpace I : M → Type _)
    (fun y => tangentSpaceNormedAddCommGroup y)
    (fun y => tangentSpaceNormedSpace y) _ tangentSpaceFiberBundleExplicit
    tangentSpace_vectorBundleExplicit s x

instance tensor0SSpace_continuousAdd (s : ℕ) (x : M) :
    ContinuousAdd (Tensor0SSpace s I x) :=
  @Bundle.continuousMultilinearMap.instContinuousAdd
    𝕜 _ M _ E _ _ (TangentSpace I : M → Type _)
    (fun y => tangentSpaceNormedAddCommGroup y)
    (fun y => tangentSpaceNormedSpace y) _ tangentSpaceFiberBundleExplicit
    tangentSpace_vectorBundleExplicit s x

instance tensor0SSpace_continuousSMul (s : ℕ) (x : M) :
    ContinuousSMul 𝕜 (Tensor0SSpace s I x) :=
  @Bundle.continuousMultilinearMap.instContinuousSMul
    𝕜 _ M _ E _ _ (TangentSpace I : M → Type _)
    (fun y => tangentSpaceNormedAddCommGroup y)
    (fun y => tangentSpaceNormedSpace y) _ tangentSpaceFiberBundleExplicit
    tangentSpace_vectorBundleExplicit s x

instance tensor0SSpace_t2Space (s : ℕ) (x : M) :
    T2Space (Tensor0SSpace s I x) :=
  @Bundle.continuousMultilinearMap.instT2Space
    𝕜 _ M _ E _ _ (TangentSpace I : M → Type _)
    (fun y => tangentSpaceNormedAddCommGroup y)
    (fun y => tangentSpaceNormedSpace y) _ tangentSpaceFiberBundleExplicit
    tangentSpace_vectorBundleExplicit s x

instance tensor0SSpace_moduleFree (s : ℕ) (x : M) :
    Module.Free 𝕜 (Tensor0SSpace s I x) :=
  inferInstanceAs (Module.Free 𝕜
    (Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I : M → Type _) x))

@[reducible]
instance tensor0SSpaceInstFunLike (s : ℕ) (x : M) :
    FunLike (Tensor0SSpace s I x) (Fin s → TangentSpace I x) 𝕜 :=
  inferInstanceAs (FunLike
    (Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I : M → Type _) x) _ _)

instance tensor0SSpace_isZeroApply (s : ℕ) (x : M) :
    IsZeroApply (Tensor0SSpace s I x) (Fin s → TangentSpace I x) 𝕜 where
  zero_apply _ := rfl

instance tensor0SSpace_isAddApply (s : ℕ) (x : M) :
    IsAddApply (Tensor0SSpace s I x) (Fin s → TangentSpace I x) 𝕜 where
  add_apply _ _ _ := rfl

instance tensor0SSpace_isNegApply (s : ℕ) (x : M) :
    IsNegApply (Tensor0SSpace s I x) (Fin s → TangentSpace I x) 𝕜 where
  neg_apply _ _ := rfl

instance tensor0SSpace_isSubApply (s : ℕ) (x : M) :
    IsSubApply (Tensor0SSpace s I x) (Fin s → TangentSpace I x) 𝕜 where
  sub_apply _ _ _ := rfl

instance tensor0SSpace_isSMulApply (s : ℕ) (x : M) :
    IsSMulApply 𝕜 (Tensor0SSpace s I x) (Fin s → TangentSpace I x) 𝕜 where
  smul_apply _ _ _ := rfl

omit [FiniteDimensional 𝕜 E] in
@[ext]
theorem tensor0SSpace_ext (s : ℕ) (x : M)
    {T T' : Tensor0SSpace s I x}
    (h : ∀ v : Fin s → TangentSpace I x, T v = T' v) : T = T' :=
  ContinuousMultilinearMap.ext (M₁ := fun _ : Fin s => TangentSpace I x) (M₂ := 𝕜) h

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem Tensor0SSpace.zero_apply (s : ℕ) (x : M)
    (v : Fin s → TangentSpace I x) :
    (0 : Tensor0SSpace s I x) v = 0 := rfl

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem Tensor0SSpace.add_apply (s : ℕ) (x : M)
    (A B : Tensor0SSpace s I x) (v : Fin s → TangentSpace I x) :
    (A + B) v = A v + B v := rfl

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem Tensor0SSpace.smul_apply (s : ℕ) (x : M)
    (c : 𝕜) (A : Tensor0SSpace s I x) (v : Fin s → TangentSpace I x) :
    (c • A) v = c • A v := rfl

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem Tensor0SSpace.nsmul_apply (s : ℕ) (x : M)
    (n : ℕ) (A : Tensor0SSpace s I x) (v : Fin s → TangentSpace I x) :
    (n • A) v = n • A v := rfl

omit [FiniteDimensional 𝕜 E] in
theorem Tensor0SSpace.neg_apply (s : ℕ) (x : M)
    (A : Tensor0SSpace s I x) (v : Fin s → TangentSpace I x) :
    (-A) v = -A v := by
  rw [show -A = (-1 : 𝕜) • A by exact (neg_one_smul 𝕜 A).symm,
    Tensor0SSpace.smul_apply, neg_one_smul]

omit [FiniteDimensional 𝕜 E] in
theorem Tensor0SSpace.sub_apply (s : ℕ) (x : M)
    (A B : Tensor0SSpace s I x) (v : Fin s → TangentSpace I x) :
    (A - B) v = A v - B v := by
  rw [sub_eq_add_neg, Tensor0SSpace.add_apply, Tensor0SSpace.neg_apply,
    sub_eq_add_neg]

omit [FiniteDimensional 𝕜 E] in
theorem Tensor0SSpace.sum_apply {α : Type*} (t : Finset α) (s : ℕ) (x : M)
    (A : α → Tensor0SSpace s I x) (v : Fin s → TangentSpace I x) :
    (∑ i ∈ t, A i) v = ∑ i ∈ t, A i v := by
  classical
  induction t using Finset.induction with
  | empty => simp only [Finset.sum_empty, Tensor0SSpace.zero_apply]
  | insert a t ha =>
      simp only [Finset.sum_insert ha, Tensor0SSpace.add_apply, *]

omit [FiniteDimensional 𝕜 E] in
noncomputable def Tensor0SSpace.domDomCongr {s s' : ℕ} {x : M}
    (A : Tensor0SSpace s I x) (e : Fin s ≃ Fin s') :
    Tensor0SSpace s' I x := by
  unfold Tensor0SSpace at A ⊢
  exact ContinuousMultilinearMap.domDomCongr e A

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem Tensor0SSpace.domDomCongr_apply {s s' : ℕ} {x : M}
    (e : Fin s ≃ Fin s') (A : Tensor0SSpace s I x)
    (v : Fin s' → TangentSpace I x) :
    A.domDomCongr e v = A (fun i => v (e i)) := by
  unfold Tensor0SSpace.domDomCongr Tensor0SSpace
  rfl

omit [FiniteDimensional 𝕜 E] in
theorem Tensor0SSpace.map_update_smul {s : ℕ} {x : M}
    (A : Tensor0SSpace s I x) (m : Fin s → TangentSpace I x)
    (i : Fin s) (c : 𝕜) (v : TangentSpace I x) :
    A (Function.update m i (c • v)) = c • A (Function.update m i v) :=
  ContinuousMultilinearMap.map_update_smul A m i c v

omit [FiniteDimensional 𝕜 E] in
theorem Tensor0SSpace.map_update_add {s : ℕ} {x : M}
    (A : Tensor0SSpace s I x) (m : Fin s → TangentSpace I x)
    (i : Fin s) (v w : TangentSpace I x) :
    A (Function.update m i (v + w)) =
      A (Function.update m i v) + A (Function.update m i w) :=
  ContinuousMultilinearMap.map_update_add A m i v w

omit [FiniteDimensional 𝕜 E] in
theorem Tensor0SSpace.map_smul_univ {s : ℕ} {x : M}
    (A : Tensor0SSpace s I x) (c : Fin s → 𝕜)
    (v : Fin s → TangentSpace I x) :
    A (fun i => c i • v i) = (∏ i, c i) • A v :=
  ContinuousMultilinearMap.map_smul_univ A c v

omit [FiniteDimensional 𝕜 E] in
theorem Tensor0SSpace.map_sum {s : ℕ} {x : M}
    (A : Tensor0SSpace s I x) {α : Fin s → Type*}
    [∀ i, Fintype (α i)]
    (g : ∀ i, α i → TangentSpace I x) :
    A (fun i => ∑ j, g i j) = ∑ r : ∀ i, α i, A (fun i => g i (r i)) :=
  ContinuousMultilinearMap.map_sum A g

omit [FiniteDimensional 𝕜 E] in
private theorem tensor0SSpace_topology_eq (s : ℕ) (x : M) :
    (inferInstance : TopologicalSpace (Tensor0SSpace s I x)) =
    (inferInstanceAs (TopologicalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜))) :=
  @Bundle.continuousMultilinearMap.topology_eq
    𝕜 _ M _ E _ _ (TangentSpace I : M → Type _)
    (fun y => tangentSpaceNormedAddCommGroup y)
    (fun y => tangentSpaceNormedSpace y) _ tangentSpaceFiberBundleExplicit
    tangentSpace_vectorBundleExplicit s x

@[reducible]
instance tensor0SSpaceNormedAddCommGroup (s : ℕ) (x : M) :
    NormedAddCommGroup (Tensor0SSpace s I x) :=
  let normed := Bundle.continuousMultilinearMap.instNormedAddCommGroup
    (𝕜 := 𝕜) (B := M) (F := E) (E := (TangentSpace I : M → Type _)) s x
  { normed with
    toAddCommGroup := tensor0SSpaceAddCommGroup s x
    toMetricSpace := normed.toMetricSpace.replaceTopology
      (tensor0SSpace_topology_eq (I := I) s x) }

@[reducible]
instance tensor0SSpaceNormedSpace (s : ℕ) (x : M) :
    NormedSpace 𝕜 (Tensor0SSpace s I x) :=
  { Bundle.continuousMultilinearMap.instNormedSpace
      (𝕜 := 𝕜) (B := M) (F := E) (E := (TangentSpace I : M → Type _)) s x with
    toModule := tensor0SSpaceModule s x }

@[reducible]
def CotangentSpace (I : ModelWithCorners 𝕜 E H) [IsManifold I 1 M] (x : M) :=
  Tensor0SSpace 1 I x

@[reducible]
def TensorRSSpace (r s : ℕ) (I : ModelWithCorners 𝕜 E H) [IsManifold I 1 M] (x : M) : Type _ :=
  Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x

@[reducible]
instance tensorRSSpaceTopologicalSpace (r s : ℕ) (x : M) :
    TopologicalSpace (TensorRSSpace r s I x) :=
  inferInstanceAs (TopologicalSpace (Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x))

@[reducible]
instance tensorRSSpaceAddCommGroup (r s : ℕ) (x : M) :
    AddCommGroup (TensorRSSpace r s I x) :=
  inferInstanceAs (AddCommGroup (Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x))

@[reducible]
instance tensorRSSpaceModule (r s : ℕ) (x : M) :
    Module 𝕜 (TensorRSSpace r s I x) :=
  inferInstanceAs (Module 𝕜 (Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x))

instance tensorRSSpace_isTopologicalAddGroup (r s : ℕ) (x : M) :
    IsTopologicalAddGroup (TensorRSSpace r s I x) :=
  inferInstanceAs (IsTopologicalAddGroup
    (Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x))

instance tensorRSSpace_continuousAdd (r s : ℕ) (x : M) :
    ContinuousAdd (TensorRSSpace r s I x) :=
  inferInstanceAs (ContinuousAdd (Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x))

instance tensorRSSpace_moduleFree (r s : ℕ) (x : M) :
    Module.Free 𝕜 (TensorRSSpace r s I x) :=
  inferInstanceAs (Module.Free 𝕜 (Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x))

@[reducible]
instance tensorRSSpaceInstFunLike (r s : ℕ) (x : M) :
    FunLike (TensorRSSpace r s I x) (Tensor0SSpace r I x) (Tensor0SSpace s I x) :=
  inferInstanceAs (FunLike (Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x) _ _)

instance tensorRSSpace_instContinuousLinearMapClass (r s : ℕ) (x : M) :
    ContinuousLinearMapClass (TensorRSSpace r s I x) 𝕜
      (Tensor0SSpace r I x) (Tensor0SSpace s I x) :=
  inferInstanceAs (ContinuousLinearMapClass
    (Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x) 𝕜 _ _)

instance tensorRSSpace_isZeroApply (r s : ℕ) (x : M) :
    IsZeroApply (TensorRSSpace r s I x) (Tensor0SSpace r I x) (Tensor0SSpace s I x) where
  zero_apply _ := rfl

instance tensorRSSpace_isAddApply (r s : ℕ) (x : M) :
    IsAddApply (TensorRSSpace r s I x) (Tensor0SSpace r I x) (Tensor0SSpace s I x) where
  add_apply _ _ _ := rfl

instance tensorRSSpace_isNegApply (r s : ℕ) (x : M) :
    IsNegApply (TensorRSSpace r s I x) (Tensor0SSpace r I x) (Tensor0SSpace s I x) where
  neg_apply _ _ := rfl

instance tensorRSSpace_isSubApply (r s : ℕ) (x : M) :
    IsSubApply (TensorRSSpace r s I x) (Tensor0SSpace r I x) (Tensor0SSpace s I x) where
  sub_apply _ _ _ := rfl

instance tensorRSSpace_isSMulApply (r s : ℕ) (x : M) :
    IsSMulApply 𝕜 (TensorRSSpace r s I x) (Tensor0SSpace r I x)
      (Tensor0SSpace s I x) where
  smul_apply _ _ _ := rfl

def TensorRSSpace.toCLM {r s : ℕ} {x : M} (T : TensorRSSpace r s I x) :
    Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x := T

def TensorRSSpace.ofCLM {r s : ℕ} {x : M}
    (T : Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x) : TensorRSSpace r s I x := T

omit [FiniteDimensional 𝕜 E] in
@[ext]
theorem tensorRSSpace_ext (r s : ℕ) (x : M)
    {T T' : TensorRSSpace r s I x}
    (h : ∀ v : Tensor0SSpace r I x,
      (show Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x from T) v =
      (show Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x from T') v) : T = T' :=
  ContinuousLinearMap.ext
    (f := (show Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x from T))
    (g := (show Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x from T')) h

instance (s : ℕ) :
    NormedAddCommGroup (Tensor0SModel s 𝕜 E) := by
  unfold Tensor0SModel
  letI : NormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) := inferInstance
  infer_instance

instance tensor0SModelNormedSpace (s : ℕ) :
    NormedSpace 𝕜 (Tensor0SModel s 𝕜 E) := by
  unfold Tensor0SModel
  exact @ContinuousMultilinearMap.normedSpace 𝕜 (Fin s) (fun _ : Fin s => E) 𝕜 _ _ _ _ _ _ 𝕜 _ _ _

instance (r s : ℕ) :
    NormedAddCommGroup (TensorRSModel r s 𝕜 E) := by
  unfold TensorRSModel
  unfold Tensor0SModel
  letI : NormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) := inferInstance
  letI hs : NormedSpace 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) := inferInstance
  letI hr : NormedSpace 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜) := inferInstance
  apply @ContinuousLinearMap.toNormedAddCommGroup 𝕜 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
     _ _ _ _ hr hs _ _

instance tensorRSModelNormedAddCommGroup (r s : ℕ) :
    NormedAddCommGroup (TensorRSModel r s 𝕜 E) :=
  inferInstance

instance tensorRSModelNormedSpace (r s : ℕ) :
    NormedSpace 𝕜 (TensorRSModel r s 𝕜 E) := by
  unfold TensorRSModel
  unfold Tensor0SModel
  letI h : SMulCommClass 𝕜 𝕜 (ContinuousMultilinearMap 𝕜 (fun (x : Fin s) ↦ E) 𝕜) := inferInstance
  exact @ContinuousLinearMap.toNormedSpace 𝕜 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
    _ _ _ _ _ _ _ _ 𝕜 _ _ h

noncomputable instance tensor0SSpace_finiteDimensional (s : ℕ) (x : M) :
    FiniteDimensional 𝕜 (Tensor0SSpace s I x) :=
  @Bundle.continuousMultilinearMap.instFiniteDimensional
    𝕜 _ M _ E _ _ (TangentSpace I : M → Type _)
    (fun y => tangentSpaceNormedAddCommGroup y)
    (fun y => tangentSpaceNormedSpace y) _ tangentSpaceFiberBundleExplicit
    tangentSpace_vectorBundleExplicit _ s x

@[simp]
theorem finrank_tensor0SSpace [CompleteSpace 𝕜] (s : ℕ) (x : M) :
    Module.finrank 𝕜 (Tensor0SSpace s I x) = (Module.finrank 𝕜 E) ^ s :=
  @Bundle.continuousMultilinearMap.finrank_eq
    𝕜 _ M _ E _ _ (TangentSpace I : M → Type _)
    (fun y => tangentSpaceNormedAddCommGroup y)
    (fun y => tangentSpaceNormedSpace y) _ tangentSpaceFiberBundleExplicit
    tangentSpace_vectorBundleExplicit _ _ s x

noncomputable instance tensorRSModel_finiteDimensional (r s : ℕ) :
    FiniteDimensional 𝕜 (TensorRSModel r s 𝕜 E) := by
  unfold TensorRSModel
  have : FiniteDimensional 𝕜 (Tensor0SModel r 𝕜 E) :=
    continuousMultilinearMap_finiteDimensional r
  have : FiniteDimensional 𝕜 (Tensor0SModel s 𝕜 E) :=
    continuousMultilinearMap_finiteDimensional s
  exact ContinuousLinearMap.finiteDimensional

@[simp]
theorem finrank_tensorRSModel [CompleteSpace 𝕜] (r s : ℕ) :
    Module.finrank 𝕜 (TensorRSModel r s 𝕜 E) = (Module.finrank 𝕜 E) ^ (r + s) := by
  have : FiniteDimensional 𝕜 (Tensor0SModel r 𝕜 E) :=
    continuousMultilinearMap_finiteDimensional r
  have : FiniteDimensional 𝕜 (Tensor0SModel s 𝕜 E) :=
    continuousMultilinearMap_finiteDimensional s
  have : Module.Free 𝕜 (Tensor0SModel s 𝕜 E) := inferInstance
  have e : (Tensor0SModel r 𝕜 E →L[𝕜] Tensor0SModel s 𝕜 E) ≃ₗ[𝕜]
      (Tensor0SModel r 𝕜 E →ₗ[𝕜] Tensor0SModel s 𝕜 E) :=
    LinearMap.toContinuousLinearMap.symm
  change Module.finrank 𝕜 (Tensor0SModel r 𝕜 E →L[𝕜] Tensor0SModel s 𝕜 E) =
      (Module.finrank 𝕜 E) ^ (r + s)
  rw [e.finrank_eq, Module.finrank_linearMap 𝕜 𝕜,
    finrank_continuousMultilinearMap r, finrank_continuousMultilinearMap s, ← pow_add]

noncomputable instance tensorRSSpace_finiteDimensional (r s : ℕ) (x : M) :
    FiniteDimensional 𝕜 (TensorRSSpace r s I x) := by
  unfold TensorRSSpace
  exact ContinuousLinearMap.finiteDimensional

@[simp]
theorem finrank_tensorRSSpace [CompleteSpace 𝕜] (r s : ℕ) (x : M) :
    Module.finrank 𝕜 (TensorRSSpace r s I x) = (Module.finrank 𝕜 E) ^ (r + s) := by
  have : Module.Free 𝕜 (Tensor0SSpace s I x) := inferInstance
  have e : (Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x) ≃ₗ[𝕜]
      (Tensor0SSpace r I x →ₗ[𝕜] Tensor0SSpace s I x) :=
    LinearMap.toContinuousLinearMap.symm
  change Module.finrank 𝕜 (Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x) =
      (Module.finrank 𝕜 E) ^ (r + s)
  rw [e.finrank_eq, Module.finrank_linearMap 𝕜 𝕜,
    finrank_tensor0SSpace r x, finrank_tensor0SSpace s x, ← pow_add]

omit [FiniteDimensional 𝕜 E] in
private theorem tensor0SSpace_type_eq (s : ℕ) (x : M) :
    Tensor0SSpace s I x =
    ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜 := by
  unfold Tensor0SSpace Bundle.continuousMultilinearMap
  rfl

omit [FiniteDimensional 𝕜 E] [IsManifold I 1 M] in
private def tensor0SModelContinuousLinearEquiv (s : ℕ) (x : M) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin s => TangentSpace I x) 𝕜 ≃L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜 where
  toFun T := T.compContinuousLinearMap fun _ =>
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm.toContinuousLinearMap
  invFun T := T.compContinuousLinearMap fun _ =>
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).toContinuousLinearMap
  left_inv T := by
    ext v
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
  right_inv T := by
    ext v
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
  map_add' T U := by
    ext v
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, add_apply]
  map_smul' c T := by
    ext v
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, smul_apply, RingHom.id_apply]
  continuous_toFun :=
    (ContinuousMultilinearMap.compContinuousLinearMapL (F := 𝕜) fun _ =>
      (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm.toContinuousLinearMap).continuous
  continuous_invFun :=
    (ContinuousMultilinearMap.compContinuousLinearMapL (F := 𝕜) fun _ =>
      (tangentSpaceModelContinuousLinearEquiv (I := I) x).toContinuousLinearMap).continuous

omit [FiniteDimensional 𝕜 E] [IsManifold I 1 M] in
def tensor0SSpaceFiberContinuousLinearEquiv (s : ℕ) (x : M) :
    Tensor0SSpace s I x ≃L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : Fin s => TangentSpace I x) 𝕜 where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := by
    change @Continuous (Tensor0SSpace s I x)
      (ContinuousMultilinearMap 𝕜 (fun _ => TangentSpace I x) 𝕜)
      (instTopologicalSpaceContinuousMultilinearMap 𝕜 s E (TangentSpace I : M → Type _) x)
      ContinuousMultilinearMap.instTopologicalSpace id
    rw [show (instTopologicalSpaceContinuousMultilinearMap 𝕜 s E
      (TangentSpace I : M → Type _) x) = ContinuousMultilinearMap.instTopologicalSpace from by
        unfold TangentSpace
        exact tensor0SSpace_topology_eq (I := I) s x]
    exact @continuous_id _ ContinuousMultilinearMap.instTopologicalSpace
  continuous_invFun := by
    change @Continuous (ContinuousMultilinearMap 𝕜 (fun _ => TangentSpace I x) 𝕜)
      (Tensor0SSpace s I x) ContinuousMultilinearMap.instTopologicalSpace
      (instTopologicalSpaceContinuousMultilinearMap 𝕜 s E (TangentSpace I : M → Type _) x) id
    rw [show (instTopologicalSpaceContinuousMultilinearMap 𝕜 s E
      (TangentSpace I : M → Type _) x) = ContinuousMultilinearMap.instTopologicalSpace from by
        unfold TangentSpace
        exact tensor0SSpace_topology_eq (I := I) s x]
    exact @continuous_id _ ContinuousMultilinearMap.instTopologicalSpace

def tensor0SSpaceContinuousLinearEquiv (s : ℕ) (x : M) :
    Tensor0SSpace s I x ≃L[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜 :=
  (tensor0SSpaceFiberContinuousLinearEquiv (I := I) s x).trans
    (tensor0SModelContinuousLinearEquiv (I := I) s x)

namespace Tensor0SSpace

omit [FiniteDimensional 𝕜 E] [IsManifold I 1 M] in
def eval {s : ℕ} {x : M} (T : Tensor0SSpace s I x)
    (v : Fin s → TangentSpace I x) : 𝕜 :=
  tensor0SSpaceFiberContinuousLinearEquiv (I := I) s x T v

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem eval_zero {s : ℕ} {x : M} (v : Fin s → TangentSpace I x) :
    eval (0 : Tensor0SSpace s I x) v = 0 := by
  rfl

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem eval_add {s : ℕ} {x : M} (A B : Tensor0SSpace s I x)
    (v : Fin s → TangentSpace I x) :
    eval (A + B) v = eval A v + eval B v := by
  rfl

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem eval_smul {s : ℕ} {x : M} (c : 𝕜) (A : Tensor0SSpace s I x)
    (v : Fin s → TangentSpace I x) :
    eval (c • A) v = c • eval A v := by
  rfl

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem eval_sub {s : ℕ} {x : M} (A B : Tensor0SSpace s I x)
    (v : Fin s → TangentSpace I x) :
    eval (A - B) v = eval A v - eval B v := by
  rfl

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem eval_neg {s : ℕ} {x : M} (A : Tensor0SSpace s I x)
    (v : Fin s → TangentSpace I x) :
    eval (-A) v = -eval A v := by
  rfl

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem eval_domDomCongr {s s' : ℕ} {x : M} (A : Tensor0SSpace s I x)
    (e : Fin s ≃ Fin s') (v : Fin s' → TangentSpace I x) :
    eval (A.domDomCongr e) v = eval A (v ∘ e) := by
  rfl

omit [FiniteDimensional 𝕜 E] in
theorem eval_eq {s : ℕ} {x : M} (T : Tensor0SSpace s I x)
    (v : Fin s → TangentSpace I x) : eval T v = T v := rfl

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem eval_fiber_equiv_symm {s : ℕ} {x : M}
    (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => TangentSpace I x) 𝕜)
    (v : Fin s → TangentSpace I x) :
    eval ((tensor0SSpaceFiberContinuousLinearEquiv (I := I) s x).symm T) v = T v := by
  rfl

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem eval_sum {α : Type*} (t : Finset α) {s : ℕ} {x : M}
    (A : α → Tensor0SSpace s I x) (v : Fin s → TangentSpace I x) :
    eval (∑ i ∈ t, A i) v = ∑ i ∈ t, eval (A i) v := by
  rw [eval_eq, Tensor0SSpace.sum_apply]
  simp only [eval_eq]

def toModel {s : ℕ} {x : M} (T : Tensor0SSpace s I x) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜 :=
  tensor0SSpaceContinuousLinearEquiv s x T

def toModelL (s : ℕ) (x : M) :
    Tensor0SSpace s I x →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜 :=
  (tensor0SSpaceContinuousLinearEquiv s x).toContinuousLinearMap

def ofModel {s : ℕ} {x : M}
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) :
    Tensor0SSpace s I x :=
  (tensor0SSpaceContinuousLinearEquiv s x).symm f

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem eval_ofModel {s : ℕ} {x : M}
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
    (v : Fin s → TangentSpace I x) :
    eval (ofModel (I := I) (x := x) f) v =
      f (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (v i)) := by
  rfl

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem toModelL_apply {s : ℕ} {x : M} (T : Tensor0SSpace s I x) :
    toModelL s x T = toModel T := rfl

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem toModel_apply {s : ℕ} {x : M} (T : Tensor0SSpace s I x)
    (v : Fin s → TangentSpace I x) :
    toModel T v = T v := by
  unfold toModel tensor0SSpaceContinuousLinearEquiv
  rfl

omit [FiniteDimensional 𝕜 E] in
theorem toModel_apply_tangent {s : ℕ} {x : M} (T : Tensor0SSpace s I x)
    (v : Fin s → TangentSpace I x) :
    toModel T (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (v i)) =
      eval T v := by
  rfl

omit [FiniteDimensional 𝕜 E] in
theorem toModel_apply_model_vector {s : ℕ} {x : M} (T : Tensor0SSpace s I x)
    (v : Fin s → E) :
    toModel T v =
      T (fun i => (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v i)) := by
  rfl

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem toModel_add {s : ℕ} {x : M} (T₁ T₂ : Tensor0SSpace s I x) :
    toModel (T₁ + T₂) = toModel T₁ + toModel T₂ :=
  map_add (tensor0SSpaceContinuousLinearEquiv s x) T₁ T₂

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem toModel_smul {s : ℕ} {x : M} (c : 𝕜) (T : Tensor0SSpace s I x) :
    toModel (c • T) = c • toModel T :=
  map_smul (tensor0SSpaceContinuousLinearEquiv s x) c T

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem toModel_zero {s : ℕ} {x : M} :
    toModel (0 : Tensor0SSpace s I x) = 0 :=
  map_zero (tensor0SSpaceContinuousLinearEquiv s x)

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem toModel_neg {s : ℕ} {x : M} (T : Tensor0SSpace s I x) :
    toModel (-T) = -toModel T :=
  map_neg (tensor0SSpaceContinuousLinearEquiv s x) T

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem toModel_sub {s : ℕ} {x : M} (T₁ T₂ : Tensor0SSpace s I x) :
    toModel (T₁ - T₂) = toModel T₁ - toModel T₂ :=
  map_sub (tensor0SSpaceContinuousLinearEquiv s x) T₁ T₂

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem ofModel_toModel {s : ℕ} {x : M} (T : Tensor0SSpace s I x) :
    ofModel (toModel T) = T :=
  (tensor0SSpaceContinuousLinearEquiv s x).symm_apply_apply T

omit [FiniteDimensional 𝕜 E] in
@[simp]
theorem toModel_ofModel {s : ℕ} {x : M}
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) :
    toModel (ofModel (I := I) (x := x) f) = f :=
  (tensor0SSpaceContinuousLinearEquiv s x).apply_symm_apply f

omit [FiniteDimensional 𝕜 E] in
theorem toModel_continuous {s : ℕ} {x : M} :
    Continuous (fun T : Tensor0SSpace s I x => toModel T) :=
  (tensor0SSpaceContinuousLinearEquiv s x).continuous_toFun

omit [FiniteDimensional 𝕜 E] in
theorem toModel_injective {s : ℕ} {x : M} :
    Function.Injective (fun T : Tensor0SSpace s I x => toModel T) :=
  (tensor0SSpaceContinuousLinearEquiv s x).injective

omit [FiniteDimensional 𝕜 E] in
theorem toModel_surjective {s : ℕ} {x : M} :
    Function.Surjective (fun T : Tensor0SSpace s I x => toModel T) :=
  (tensor0SSpaceContinuousLinearEquiv s x).surjective

omit [FiniteDimensional 𝕜 E] in
theorem toModel_bijective {s : ℕ} {x : M} :
    Function.Bijective (fun T : Tensor0SSpace s I x => toModel T) :=
  (tensor0SSpaceContinuousLinearEquiv s x).bijective

end Tensor0SSpace

def tensorRSSpaceContinuousLinearEquiv (r s : ℕ) (x : M) :
    TensorRSSpace r s I x ≃L[𝕜] TensorRSModel r s 𝕜 E := by
  unfold TensorRSSpace
  exact (tensor0SSpaceContinuousLinearEquiv (I := I) r x).arrowCongr
    (tensor0SSpaceContinuousLinearEquiv (I := I) s x)

omit [FiniteDimensional 𝕜 E] in
private theorem tensorRSSpace_type_eq (r s : ℕ) (x : M) :
    TensorRSSpace r s I x =
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜 →L[𝕜]
     ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) := by
  unfold TensorRSSpace Tensor0SSpace Bundle.continuousMultilinearMap
  congr 1 <;> exact tensor0SSpace_topology_eq (I := I) _ x

private def tensorRSSpace_toModelAddHom (r s : ℕ) (x : M) :
    TensorRSSpace r s I x →+ TensorRSModel r s 𝕜 E :=
  { toFun := fun T => tensorRSSpaceContinuousLinearEquiv (I := I) r s x T
    map_zero' := map_zero (tensorRSSpaceContinuousLinearEquiv (I := I) r s x)
    map_add' := map_add (tensorRSSpaceContinuousLinearEquiv (I := I) r s x) }

noncomputable instance tensorRSSpaceNormedAddCommGroup (r s : ℕ) (x : M) :
    NormedAddCommGroup (TensorRSSpace r s I x) :=
  NormedAddCommGroup.induced (TensorRSSpace r s I x) (TensorRSModel r s 𝕜 E)
    (tensorRSSpace_toModelAddHom (I := I) r s x)
    (tensorRSSpaceContinuousLinearEquiv (I := I) r s x).injective

noncomputable instance tensorRSSpaceNormedSpace (r s : ℕ) (x : M) :
    NormedSpace 𝕜 (TensorRSSpace r s I x) where
  norm_smul_le := by
    intro c T
    change ‖tensorRSSpaceContinuousLinearEquiv (I := I) r s x (c • T)‖ ≤
      ‖c‖ * ‖tensorRSSpaceContinuousLinearEquiv (I := I) r s x T‖
    rw [map_smul]
    exact norm_smul_le c (tensorRSSpaceContinuousLinearEquiv (I := I) r s x T)

instance tensorRSSpace_continuousSMul (r s : ℕ) (x : M) :
    ContinuousSMul 𝕜 (TensorRSSpace r s I x) :=
  inferInstanceAs (ContinuousSMul 𝕜 (Tensor0SSpace r I x →L[𝕜] Tensor0SSpace s I x))

namespace TensorRSSpace

def toModel {r s : ℕ} {x : M} (T : TensorRSSpace r s I x) :
    TensorRSModel r s 𝕜 E :=
  tensorRSSpaceContinuousLinearEquiv (I := I) r s x T

def toModelL (r s : ℕ) (x : M) :
    TensorRSSpace r s I x →L[𝕜] TensorRSModel r s 𝕜 E :=
  (tensorRSSpaceContinuousLinearEquiv (I := I) r s x).toContinuousLinearMap

def ofModel {r s : ℕ} {x : M} (f : TensorRSModel r s 𝕜 E) :
    TensorRSSpace r s I x :=
  (tensorRSSpaceContinuousLinearEquiv (I := I) r s x).symm f

@[simp]
theorem toModelL_apply {r s : ℕ} {x : M} (T : TensorRSSpace r s I x) :
    (toModelL (I := I) r s x).toFun T = toModel T := rfl

@[simp]
theorem toModel_apply_toModel {r s : ℕ} {x : M} (T : TensorRSSpace r s I x)
    (A : Tensor0SSpace r I x) :
    toModel T (Tensor0SSpace.toModel A) = Tensor0SSpace.toModel (T A) := by
  rfl

@[simp]
theorem toModel_add {r s : ℕ} {x : M} (T₁ T₂ : TensorRSSpace r s I x) :
    toModel (T₁ + T₂) = toModel T₁ + toModel T₂ :=
  map_add (tensorRSSpaceContinuousLinearEquiv (I := I) r s x) T₁ T₂

@[simp]
theorem toModel_smul {r s : ℕ} {x : M} (c : 𝕜) (T : TensorRSSpace r s I x) :
    toModel (c • T) = c • toModel T :=
  map_smul (tensorRSSpaceContinuousLinearEquiv (I := I) r s x) c T

@[simp]
theorem toModel_zero {r s : ℕ} {x : M} :
    toModel (0 : TensorRSSpace r s I x) = 0 :=
  (tensorRSSpaceContinuousLinearEquiv (I := I) r s x).toLinearEquiv.map_zero

@[simp]
theorem toModel_neg {r s : ℕ} {x : M} (T : TensorRSSpace r s I x) :
    toModel (-T) = -toModel T :=
  (tensorRSSpaceContinuousLinearEquiv (I := I) r s x).toLinearEquiv.map_neg T

@[simp]
theorem toModel_sub {r s : ℕ} {x : M} (T₁ T₂ : TensorRSSpace r s I x) :
    toModel (T₁ - T₂) = toModel T₁ - toModel T₂ :=
  (tensorRSSpaceContinuousLinearEquiv (I := I) r s x).toLinearEquiv.map_sub T₁ T₂

@[simp]
theorem ofModel_toModel {r s : ℕ} {x : M} (T : TensorRSSpace r s I x) :
    ofModel (toModel T) = T :=
  (tensorRSSpaceContinuousLinearEquiv (I := I) r s x).symm_apply_apply T

@[simp]
theorem toModel_ofModel {r s : ℕ} {x : M} (f : TensorRSModel r s 𝕜 E) :
    toModel (ofModel (I := I) (x := x) f) = f :=
  (tensorRSSpaceContinuousLinearEquiv (I := I) r s x).apply_symm_apply f

theorem toModel_continuous {r s : ℕ} {x : M} :
    Continuous (fun T : TensorRSSpace r s I x => toModel T) :=
  (tensorRSSpaceContinuousLinearEquiv (I := I) r s x).continuous_toFun

theorem toModel_injective {r s : ℕ} {x : M} :
    Function.Injective (fun T : TensorRSSpace r s I x => toModel T) :=
  (tensorRSSpaceContinuousLinearEquiv (I := I) r s x).injective

theorem toModel_surjective {r s : ℕ} {x : M} :
    Function.Surjective (fun T : TensorRSSpace r s I x => toModel T) :=
  (tensorRSSpaceContinuousLinearEquiv (I := I) r s x).surjective

theorem toModel_bijective {r s : ℕ} {x : M} :
    Function.Bijective (fun T : TensorRSSpace r s I x => toModel T) :=
  (tensorRSSpaceContinuousLinearEquiv (I := I) r s x).bijective

end TensorRSSpace

noncomputable def tensor0SCurry (s : ℕ) (x : M) :
    Tensor0SSpace (s+1) I x ≃L[𝕜]
    (TangentSpace I x →L[𝕜] Tensor0SSpace s I x) :=
  (tensor0SSpaceFiberContinuousLinearEquiv (I := I) (s + 1) x).trans
    ((continuousMultilinearCurryLeftEquiv 𝕜
      (fun _ : Fin (s + 1) => TangentSpace I x) 𝕜).toContinuousLinearEquiv.trans
        ((ContinuousLinearEquiv.refl 𝕜 (TangentSpace I x)).arrowCongr
          (tensor0SSpaceFiberContinuousLinearEquiv (I := I) s x).symm))

instance tensor0SBundleTopology (s : ℕ) :
    TopologicalSpace (TotalSpace
      (Tensor0SModel s 𝕜 E)
      (fun x : M => Tensor0SSpace s I x)) :=
  Bundle.continuousMultilinearMap.topologicalSpaceTotalSpace 𝕜 s E (TangentSpace I : M → Type _)

@[simp]
noncomputable instance tensor0SBundleFiber (s : ℕ) :
    FiberBundle
      (Tensor0SModel s 𝕜 E)
      (fun x : M => Tensor0SSpace s I x) :=
  Bundle.continuousMultilinearMap.fiberBundle 𝕜 s E (TangentSpace I : M → Type _)

@[simp]
noncomputable instance tensor0SBundle_vector (s : ℕ) :
    VectorBundle 𝕜
      (Tensor0SModel s 𝕜 E)
      (fun x : M => Tensor0SSpace s I x) :=
  Bundle.continuousMultilinearMap.vectorBundle 𝕜 s E (TangentSpace I : M → Type _)

instance isManifold_infty_succ [IsManifold I ∞ M] :
    IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
  have h : ((∞ : WithTop ℕ∞) + 1) = ∞ := by simp
  rw [h]; infer_instance

variable (n : WithTop ℕ∞) [IsManifold I (n + 1) M]

@[simp]
noncomputable instance tensor0SBundle_smooth (s : ℕ) :
    ContMDiffVectorBundle n
      (Tensor0SModel s 𝕜 E)
      (fun x : M => Tensor0SSpace s I x) I := by
  have : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  have : (Bundle.continuousMultilinearMap.vectorPrebundle
      𝕜 s E (TangentSpace I : M → Type _)).IsContMDiff I n :=
    Bundle.continuousMultilinearMap.vectorPrebundle.isSmooth s I n
  exact (Bundle.continuousMultilinearMap.vectorPrebundle
    𝕜 s E (TangentSpace I : M → Type _)).contMDiffVectorBundle I

noncomputable instance tensorRSBundleTopology (r s : ℕ) :
    TopologicalSpace (TotalSpace (TensorRSModel r s 𝕜 E)
      (fun x : M => TensorRSSpace r s I x)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id 𝕜)
    (Tensor0SModel r 𝕜 E)
    (fun (x : M) => Tensor0SSpace r I x)
    (Tensor0SModel s 𝕜 E)
    (fun (x : M) => Tensor0SSpace s I x)

noncomputable instance tensorRSBundleFiber (r s : ℕ) :
    @FiberBundle M (TensorRSModel r s 𝕜 E) _ (by infer_instance : TopologicalSpace _)
      (fun x : M => TensorRSSpace r s I x)
      (tensorRSBundleTopology r s)
      (fun x : M => tensorRSSpaceTopologicalSpace r s x) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id 𝕜)
    (Tensor0SModel r 𝕜 E)
    (fun (x : M) => Tensor0SSpace r I x)
    (Tensor0SModel s 𝕜 E)
    (fun (x : M) => Tensor0SSpace s I x)

noncomputable instance tensorRSBundle_vector (r s : ℕ) :
    @VectorBundle 𝕜 M (TensorRSModel r s 𝕜 E) (fun x : M => TensorRSSpace r s I x) _
      (fun x => by infer_instance) (fun x => by infer_instance)
      (tensorRSModelNormedAddCommGroup r s) (tensorRSModelNormedSpace r s) _
      (tensorRSBundleTopology r s) _
      (tensorRSBundleFiber r s) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E) 𝕜)
    (fun (x : M) => Tensor0SSpace r I x)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
    (fun (x : M) => Tensor0SSpace s I x)

noncomputable instance tensorRSBundle_smooth (r s : ℕ) :
    @ContMDiffVectorBundle n 𝕜 M (TensorRSModel r s 𝕜 E) (fun x : M => TensorRSSpace r s I x)
      _ E _ _ H _ I _ _ _ _ _ _
      (tensorRSBundleTopology r s) _
      (tensorRSBundleFiber r s)
      (tensorRSBundle_vector r s) :=
  ContMDiffVectorBundle.continuousLinearMap

omit [FiniteDimensional 𝕜 E] in
theorem tensor0SSpace_continuousLinearEquiv_apply (s : ℕ) (x : M)
    (T : Tensor0SSpace s I x) :
    tensor0SSpaceContinuousLinearEquiv (I := I) (M := M) s x T = T := rfl

omit [FiniteDimensional 𝕜 E] in
theorem tensor0SSpace_continuousLinearEquiv_symm_apply (s : ℕ) (x : M)
    (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) :
    (tensor0SSpaceContinuousLinearEquiv (I := I) (M := M) s x).symm T = T := rfl

omit [FiniteDimensional 𝕜 E] in
theorem tensor0SSpace_continuousLinearEquiv_apply_apply (s : ℕ) (x : M)
    (T : Tensor0SSpace s I x) (v : Fin s → E) :
    tensor0SSpaceContinuousLinearEquiv (I := I) (M := M) s x T v =
      T (fun i => (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v i)) := by
  rfl

omit [FiniteDimensional 𝕜 E] in
theorem tensor0SSpace_continuousLinearEquiv_symm_apply_apply (s : ℕ) (x : M)
    (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜)
    (v : Fin s → TangentSpace I x) :
    (tensor0SSpaceContinuousLinearEquiv (I := I) (M := M) s x).symm T v =
      T (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (v i)) := by
  rfl

theorem tensorRSSpace_continuousLinearEquiv_symm_apply_apply (r s : ℕ) (x : M)
    (T : TensorRSModel r s 𝕜 E) (β : Tensor0SSpace r I x)
    (v : Fin s → TangentSpace I x) :
    (tensorRSSpaceContinuousLinearEquiv (I := I) (M := M) r s x).symm T β v =
      T (Tensor0SSpace.toModel (I := I) (M := M) β)
        (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (v i)) := by
  rfl

theorem tensorRSSpace_continuousLinearEquiv_apply_apply (r s : ℕ) (x : M)
    (T : TensorRSSpace r s I x) (β : Tensor0SModel r 𝕜 E) (v : Fin s → E) :
    tensorRSSpaceContinuousLinearEquiv (I := I) (M := M) r s x T β v =
      T ((tensor0SSpaceContinuousLinearEquiv (I := I) (M := M) r x).symm β)
        (fun i => (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v i)) := by
  rfl

theorem tensorRSSpace_continuousLinearEquiv_symm_toContinuousLinearMap_apply_apply
    (r s : ℕ) (x : M) (T : TensorRSModel r s 𝕜 E) (β : Tensor0SSpace r I x)
    (v : Fin s → TangentSpace I x) :
    (tensorRSSpaceContinuousLinearEquiv (I := I) (M := M) r s x).symm.toContinuousLinearMap
        T β v =
      T (Tensor0SSpace.toModel (I := I) (M := M) β)
        (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (v i)) := by
  exact tensorRSSpace_continuousLinearEquiv_symm_apply_apply r s x T β v

omit [FiniteDimensional 𝕜 E] in
theorem tensor0SSpace_continuousLinearEquiv_coe (s : ℕ) (x : M) :
    (tensor0SSpaceContinuousLinearEquiv (I := I) (M := M) s x : _ → _) = id := rfl

omit [FiniteDimensional 𝕜 E] in
theorem tensor0SSpace_continuousLinearEquiv_symm_coe (s : ℕ) (x : M) :
    ((tensor0SSpaceContinuousLinearEquiv (I := I) (M := M) s x).symm : _ → _) = id := rfl

omit [FiniteDimensional 𝕜 E] in
theorem tensor0SSpaceFiberContinuousLinearEquiv_apply (s : ℕ) (x : M)
    (T : Tensor0SSpace s I x) :
    tensor0SSpaceFiberContinuousLinearEquiv (I := I) (M := M) s x T = T := rfl

omit [FiniteDimensional 𝕜 E] in
theorem tensor0SSpaceFiberContinuousLinearEquiv_apply_apply (s : ℕ) (x : M)
    (T : Tensor0SSpace s I x) (v : Fin s → TangentSpace I x) :
    tensor0SSpaceFiberContinuousLinearEquiv (I := I) (M := M) s x T v = T v := rfl

theorem tensor0SSpaceFiberContinuousLinearEquiv_model_symm_apply (s : ℕ) (x : M)
    (T : Tensor0SModel s 𝕜 E) (v : Fin s → TangentSpace I x) :
    tensor0SSpaceFiberContinuousLinearEquiv (I := I) (M := M) s x
        ((tensor0SSpaceContinuousLinearEquiv (I := I) (M := M) s x).symm T) v =
      T (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (v i)) := by
  rfl

omit [FiniteDimensional 𝕜 E] in
theorem tensor0SSpaceFiberContinuousLinearEquiv_symm_apply (s : ℕ) (x : M)
    (T : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => TangentSpace I x) 𝕜) :
    (tensor0SSpaceFiberContinuousLinearEquiv (I := I) (M := M) s x).symm T = T := rfl

omit [FiniteDimensional 𝕜 E] in
theorem TensorRSSpace.zero_apply (r s : ℕ) (x : M)
    (A : Tensor0SSpace r I x) :
    (0 : TensorRSSpace r s I x) A = 0 := rfl

omit [FiniteDimensional 𝕜 E] in
theorem TensorRSSpace.add_apply (r s : ℕ) (x : M)
    (T U : TensorRSSpace r s I x) (A : Tensor0SSpace r I x) :
    (T + U) A = T A + U A := rfl

omit [FiniteDimensional 𝕜 E] in
theorem TensorRSSpace.smul_apply (r s : ℕ) (x : M)
    (c : 𝕜) (T : TensorRSSpace r s I x) (A : Tensor0SSpace r I x) :
    (c • T) A = c • T A := rfl

end
end Tensor0SBundle
end CalabiYau
