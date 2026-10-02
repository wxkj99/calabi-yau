-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Tensor/Product/Fiber.lean
-- Locally modified.
/-
Authors: Jack McCarthy
-/
module
public import CalabiYau.Geometry.Manifold.Tensor.Product.HomEquiv
public import Mathlib.Topology.VectorBundle.Basic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
open CalabiYau.Tensor.Product

noncomputable section

open Bundle Set

open scoped TensorProduct Topology

section TensorProductFiber

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {B : Type*} [TopologicalSpace B]
variable (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
variable (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
variable (E₁ : B → Type*) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
variable (E₂ : B → Type*) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

namespace Bundle.TensorProduct

@[reducible] noncomputable def tensorFiberTopology (x : B) : TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
  TopologicalSpace.induced
    (TensorProduct.map
      ((trivializationAt F₁ E₁ x).continuousLinearEquivAt 𝕜 x
        (mem_baseSet_trivializationAt F₁ E₁ x)).toLinearMap
      ((trivializationAt F₂ E₂ x).continuousLinearEquivAt 𝕜 x
        (mem_baseSet_trivializationAt F₂ E₂ x)).toLinearMap)
    (instNormedAddCommGroupTensor 𝕜 F₁ F₂).toUniformSpace.toTopologicalSpace

private noncomputable def trivEquiv (x : B) :
    (E₁ x ⊗[𝕜] E₂ x) ≃ₗ[𝕜] (F₁ ⊗[𝕜] F₂) :=
  TensorProduct.congr
    ((trivializationAt F₁ E₁ x).continuousLinearEquivAt 𝕜 x
      (mem_baseSet_trivializationAt F₁ E₁ x)).toLinearEquiv
    ((trivializationAt F₂ E₂ x).continuousLinearEquivAt 𝕜 x
      (mem_baseSet_trivializationAt F₂ E₂ x)).toLinearEquiv

instance tensorFiberTopology_isTopologicalAddGroup (x : B) :
    @IsTopologicalAddGroup (E₁ x ⊗[𝕜] E₂ x) (tensorFiberTopology 𝕜 F₁ F₂ E₁ E₂ x) _ := by
  change @IsTopologicalAddGroup _ (TopologicalSpace.induced _ _) _
  exact topologicalAddGroup_induced _

instance tensorFiberTopology_continuousSMul (x : B) :
    @ContinuousSMul 𝕜 (E₁ x ⊗[𝕜] E₂ x) _ _
      (tensorFiberTopology 𝕜 F₁ F₂ E₁ E₂ x) := by
  change @ContinuousSMul 𝕜 _ _ _ (TopologicalSpace.induced _ _)
  exact continuousSMul_induced _

instance tensorFiberTopology_t2Space (x : B) :
    @T2Space (E₁ x ⊗[𝕜] E₂ x) (tensorFiberTopology 𝕜 F₁ F₂ E₁ E₂ x) := by
  let : TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) := tensorFiberTopology 𝕜 F₁ F₂ E₁ E₂ x
  exact T2Space.of_injective_continuous (trivEquiv 𝕜 F₁ F₂ E₁ E₂ x).injective <| by
    change @Continuous _ _ (TopologicalSpace.induced _ _) _ _
    exact continuous_induced_dom

noncomputable def continuousLinearEquivAt (x : B) :
    letI := tensorFiberTopology 𝕜 F₁ F₂ E₁ E₂ x
    (E₁ x ⊗[𝕜] E₂ x) ≃L[𝕜] (F₁ ⊗[𝕜] F₂) := by
  letI := tensorFiberTopology 𝕜 F₁ F₂ E₁ E₂ x
  exact ⟨trivEquiv 𝕜 F₁ F₂ E₁ E₂ x,
    continuous_induced_dom,
    LinearMap.continuous_of_finiteDimensional
      (trivEquiv 𝕜 F₁ F₂ E₁ E₂ x).symm.toLinearMap⟩

variable {𝕜 E₁ E₂}

def toModel (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
    [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
    {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
    [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
    [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
    {x : B} (t : E₁ x ⊗[𝕜] E₂ x) : F₁ ⊗[𝕜] F₂ :=
  trivEquiv 𝕜 F₁ F₂ E₁ E₂ x t

def fromModel (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
    [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
    {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
    [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
    [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
    {x : B} (f : F₁ ⊗[𝕜] F₂) : E₁ x ⊗[𝕜] E₂ x :=
  (trivEquiv 𝕜 F₁ F₂ E₁ E₂ x).symm f

variable (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
variable (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
variable {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
variable {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂] in
@[simp]
theorem toModel_add {x : B} (t₁ t₂ : E₁ x ⊗[𝕜] E₂ x) :
    toModel F₁ F₂ (t₁ + t₂) = toModel F₁ F₂ t₁ + toModel F₁ F₂ t₂ :=
  map_add (trivEquiv 𝕜 F₁ F₂ E₁ E₂ x) t₁ t₂

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂] in
@[simp]
theorem toModel_smul {x : B} (c : 𝕜) (t : E₁ x ⊗[𝕜] E₂ x) :
    toModel F₁ F₂ (c • t) = c • toModel F₁ F₂ t :=
  map_smul (trivEquiv 𝕜 F₁ F₂ E₁ E₂ x) c t

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂] in
@[simp]
theorem toModel_zero {x : B} :
    toModel F₁ F₂ (0 : E₁ x ⊗[𝕜] E₂ x) = 0 :=
  map_zero (trivEquiv 𝕜 F₁ F₂ E₁ E₂ x)

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂] in
@[simp]
theorem fromModel_toModel {x : B} (t : E₁ x ⊗[𝕜] E₂ x) :
    fromModel F₁ F₂ (toModel F₁ F₂ t) = t :=
  (trivEquiv 𝕜 F₁ F₂ E₁ E₂ x).symm_apply_apply t

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂] in
@[simp]
theorem toModel_fromModel {x : B} (f : F₁ ⊗[𝕜] F₂) :
    toModel F₁ F₂ (fromModel F₁ F₂ (x := x) f : E₁ x ⊗[𝕜] E₂ x) = f :=
  (trivEquiv 𝕜 F₁ F₂ E₁ E₂ x).apply_symm_apply f

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂] in
theorem toModel_injective {x : B} :
    Function.Injective (fun t : E₁ x ⊗[𝕜] E₂ x => toModel F₁ F₂ t) :=
  (trivEquiv 𝕜 F₁ F₂ E₁ E₂ x).injective

end Bundle.TensorProduct

end TensorProductFiber

end
