-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Tensor/Product/Bundle.lean
-- Locally modified.
/-
Authors: Yuan Liao, Jack McCarthy
Modified by: Ziyang Qin
-/
module
public import CalabiYau.Geometry.Manifold.Tensor.Product.Pretrivialization
public import CalabiYau.Geometry.Manifold.Tensor.Product.Fiber

@[expose] public section

open CalabiYau.Tensor.Product

open scoped Topology
open scoped TensorProduct

noncomputable section

open Bundle Set Topology
open scoped Bundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

variable {B : Type*}
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  (E₁ : B → Type*) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)]

variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  (E₂ : B → Type*) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)]

variable {E₁ E₂}
variable [TopologicalSpace B]

section
section TensorFiberTopology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {B : Type*} [TopologicalSpace B]
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]

variable (E₁ : B → Type*) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]

variable (E₂ : B → Type*) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

@[reducible] noncomputable def tensorFiberTopologicalSpace (x : B) :
    TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) := by
  classical
  letI : TopologicalSpace (F₁ ⊗[𝕜] F₂) := inferInstance
  let L₁ : E₁ x ≃L[𝕜] F₁ :=
    (trivializationAt F₁ E₁ x).continuousLinearEquivAt 𝕜 x
      (mem_baseSet_trivializationAt F₁ E₁ x)
  let L₂ : E₂ x ≃L[𝕜] F₂ :=
    (trivializationAt F₂ E₂ x).continuousLinearEquivAt 𝕜 x
      (mem_baseSet_trivializationAt F₂ E₂ x)
  exact TopologicalSpace.induced
    (fun t : E₁ x ⊗[𝕜] E₂ x =>
      TensorProduct.map L₁.toLinearMap L₂.toLinearMap t)
    inferInstance

@[reducible] noncomputable def tensorFiberTopologicalSpaceInst
    (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    (B : Type*) [TopologicalSpace B]
    (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
    (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    (E₁ : B → Type*) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
    [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
    (E₂ : B → Type*) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
    [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
    [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
    (x : B) : TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
  tensorFiberTopologicalSpace (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂)
    (E₁ := E₁) (E₂ := E₂) x

end TensorFiberTopology
end

section

universe u𝕜 uB uF₁ uF₂ uE₁ uE₂
namespace Bundle.TensorProduct

open _root_.Bundle.Pretrivialization
open scoped Manifold

class TensorFiberTopologies
    (𝕜 : Type u𝕜) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    (B : Type uB) [TopologicalSpace B]
    (F₁ : Type uF₁) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
    (F₂ : Type uF₂) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
    (E₁ : B → Type uE₁) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
      [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
      [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
    (E₂ : B → Type uE₂) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
      [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
      [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂] :
    Type (max uB (max (uE₁+1) (uE₂+1))) where
  (fiberTop : ∀ x : B, TopologicalSpace (E₁ x ⊗[𝕜] E₂ x))

attribute [reducible, instance] TensorFiberTopologies.fiberTop

variable [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
     [∀ (x : B), ContinuousAdd (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
variable [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂]
    [VectorBundle 𝕜 F₂ E₂] [∀ (x : B), ContinuousAdd (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]

noncomputable instance instNormedAddCommGroupTensor :
    NormedAddCommGroup (F₁ ⊗[𝕜] F₂) :=
by
  classical
  let e := clmEquiv (𝕜:=𝕜) (F₁:=F₁) (F₂:=F₂)
  refine NormedAddCommGroup.induced
    (𝓕 := (F₁ ⊗[𝕜] F₂) →+ (cDual 𝕜 F₁ →L[𝕜] F₂))
    (E := (F₁ ⊗[𝕜] F₂))
    (F := (cDual 𝕜 F₁ →L[𝕜] F₂))
    (f := e.toLinearMap.toAddMonoidHom)
    ?_
  exact e.injective

noncomputable instance instNormedSpaceModelTensor :
    NormedSpace 𝕜 (F₁ ⊗[𝕜] F₂) :=
by
  classical
  let e := clmEquiv (𝕜:=𝕜) (F₁:=F₁) (F₂:=F₂)
  refine NormedSpace.induced
    (F := (F₁ ⊗[𝕜] F₂) →ₗ[𝕜] (cDual 𝕜 F₁ →L[𝕜] F₂))
    (𝕜 := 𝕜)
    (E := (F₁ ⊗[𝕜] F₂))
    (G := (cDual 𝕜 F₁ →L[𝕜] F₂))
    e.toLinearMap

noncomputable instance tensorFiberTopologies
    (𝕜 : Type u𝕜) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    (B : Type uB) [TopologicalSpace B]
    (F₁ : Type uF₁) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
    (F₂ : Type uF₂) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
    (E₁ : B → Type uE₁) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
      [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
      [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
    (E₂ : B → Type uE₂) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
      [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
      [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂] :
    TensorFiberTopologies 𝕜 B F₁ F₂ E₁ E₂ :=
  ⟨fun x =>
    tensorFiberTopology (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂) x⟩

noncomputable def vectorPrebundle :
    @VectorPrebundle
      𝕜
      B
      (F₁ ⊗[𝕜] F₂)
      (fun x ↦ E₁ x ⊗[𝕜] E₂ x)
      _
      _
      _
      instNormedAddCommGroupTensor
      instNormedSpaceModelTensor
      _
      (fun x => tensorFiberTopology (𝕜:=𝕜) (F₁:=F₁) (F₂:=F₂) (E₁:=E₁) (E₂:=E₂) x)
      :=
  letI := tensorFiberTopology (𝕜:=𝕜) (F₁:=F₁) (F₂:=F₂) (E₁:=E₁) (E₂:=E₂)
  {
    pretrivializationAtlas :=
      {e | ∃ (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
        (_ : MemTrivializationAtlas e₁) (_ : MemTrivializationAtlas e₂),
          e = Pretrivialization.tensorProduct (𝕜 := 𝕜) e₁ e₂}
    pretrivialization_linear' := by
      rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩
      apply Pretrivialization.tensorProduct.isLinear
    pretrivializationAt := fun x =>
      Pretrivialization.tensorProduct (𝕜 := 𝕜) (trivializationAt F₁ E₁ x) (trivializationAt F₂ E₂ x)
    mem_base_pretrivializationAt := fun x =>
      ⟨mem_baseSet_trivializationAt F₁ E₁ x, mem_baseSet_trivializationAt F₂ E₂ x⟩
    pretrivialization_mem_atlas := fun x =>
      ⟨trivializationAt F₁ E₁ x, trivializationAt F₂ E₂ x, inferInstance, inferInstance, rfl⟩
    exists_coordChange := by
      rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
      refine ⟨Pretrivialization.tensorProductCoordChange (𝕜 := 𝕜) (e₁ := e₁) (e₁' := e₁')
                (e₂ := e₂) (e₂' := e₂'),
              ?_, Pretrivialization.tensorProductCoordChange_apply (𝕜 := 𝕜)
                (e₁ := e₁) (e₁' := e₁') (e₂ := e₂) (e₂' := e₂')⟩
      change ContinuousOn
        (Pretrivialization.tensorProductCoordChange (𝕜 := 𝕜) e₁ e₁' e₂ e₂')
        (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet))
      exact Pretrivialization.continuousOn_tensorProductCoordChange (𝕜 := 𝕜)
    totalSpaceMk_isInducing := by
      intro b
      let : TopologicalSpace (E₁ b ⊗[𝕜] E₂ b) :=
         tensorFiberTopology (𝕜:=𝕜) (F₁:=F₁) (F₂:=F₂) (E₁:=E₁) (E₂:=E₂) b
      let L₁ : E₁ b ≃L[𝕜] F₁ :=
        (trivializationAt F₁ E₁ b).continuousLinearEquivAt 𝕜 b
          (mem_baseSet_trivializationAt _ _ _)
      let L₂ : E₂ b ≃L[𝕜] F₂ :=
        (trivializationAt F₂ E₂ b).continuousLinearEquivAt 𝕜 b
          (mem_baseSet_trivializationAt _ _ _)
      have hind : IsInducing (TensorProduct.map L₁.toLinearMap L₂.toLinearMap) := ⟨rfl⟩
      have : IsInducing fun x ↦ (b, TensorProduct.map L₁.toLinearMap L₂.toLinearMap x) :=
        isInducing_const_prod.mpr hind
      convert this using 1
      funext x
      simp only [Function.comp_apply, Pretrivialization.tensorProduct_apply,
                  Prod.mk.injEq, true_and]
      have hL1 :
          (↑(Trivialization.continuousLinearMapAt 𝕜 (trivializationAt F₁ E₁ b) b) :
              E₁ b →ₗ[𝕜] F₁) =
            (↑L₁.toLinearEquiv : E₁ b →ₗ[𝕜] F₁) := by
        ext w
        simpa [L₁] using
          congrArg (fun f => f w)
            (Trivialization.coe_continuousLinearEquivAt_eq (R := 𝕜)
              (trivializationAt F₁ E₁ b)
              (mem_baseSet_trivializationAt F₁ E₁ b)).symm
      have hL2 :
          (↑(Trivialization.continuousLinearMapAt 𝕜 (trivializationAt F₂ E₂ b) b) :
              E₂ b →ₗ[𝕜] F₂) =
            (↑L₂.toLinearEquiv : E₂ b →ₗ[𝕜] F₂) := by
        ext w
        simpa [L₂] using
          congrArg (fun f => f w)
            (Trivialization.coe_continuousLinearEquivAt_eq (R := 𝕜)
              (trivializationAt F₂ E₂ b)
              (mem_baseSet_trivializationAt F₂ E₂ b)).symm
      simp [hL1, hL2]
  }

noncomputable instance topologicalSpaceTotalSpace :
    TopologicalSpace
      (TotalSpace (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)) := by
  classical
  letI (x : B) : TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
    Bundle.TensorProduct.tensorFiberTopology
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂) x
  exact
    (Bundle.TensorProduct.vectorPrebundle
        (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)).totalSpaceTopology

@[reducible] noncomputable def tensorFiberTop :
    (b : B) → TopologicalSpace (E₁ b ⊗[𝕜] E₂ b) :=
  fun b =>
    Bundle.TensorProduct.tensorFiberTopology
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂) b

@[reducible] noncomputable def tensorTotalSpaceTop :
    TopologicalSpace
      (TotalSpace (F₁ ⊗[𝕜] F₂) (fun x : B ↦ E₁ x ⊗[𝕜] E₂ x)) :=
  letI : (b : B) → TopologicalSpace (E₁ b ⊗[𝕜] E₂ b) :=
    tensorFiberTop (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
  (Bundle.TensorProduct.vectorPrebundle
    (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)).totalSpaceTopology
attribute [local instance] tensorTotalSpaceTop

noncomputable instance fiberBundle :
    @FiberBundle
      B
      (F₁ ⊗[𝕜] F₂)
      inferInstance
      inferInstance
      (fun x : B ↦ E₁ x ⊗[𝕜] E₂ x)
      (tensorTotalSpaceTop
        (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂))
      (tensorFiberTop
        (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)) := by
  classical
  letI : (b : B) → TopologicalSpace (E₁ b ⊗[𝕜] E₂ b) :=
    tensorFiberTop (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
  exact
    (Bundle.TensorProduct.vectorPrebundle
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)).toFiberBundle
attribute [local instance] fiberBundle

noncomputable instance vectorBundle :
    letI : (x : B) → TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      tensorFiberTop
        (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    VectorBundle 𝕜 (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x) := by
  classical
  let : (x : B) → TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
    tensorFiberTop
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
  exact
    (Bundle.TensorProduct.vectorPrebundle
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)).toVectorBundle

variable (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
variable [he₁ : MemTrivializationAtlas e₁] [he₂ : MemTrivializationAtlas e₂]

noncomputable def _root_.Bundle.Trivialization.tensorProduct :
    letI : (x : B) → TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      tensorFiberTop (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    Trivialization (F₁ ⊗[𝕜] F₂) (π (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)) := by
  classical
  letI : (x : B) → TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
    tensorFiberTop (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
  exact
    VectorPrebundle.trivializationOfMemPretrivializationAtlas _
      ⟨e₁, e₂, he₁, he₂, rfl⟩

noncomputable instance memTrivializationAtlas :
    letI : (x : B) → TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      tensorFiberTop (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    MemTrivializationAtlas
      (e₁.tensorProduct (𝕜 := 𝕜) e₂ :
        Trivialization (F₁ ⊗[𝕜] F₂) (π (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x))) := by
  let : (b : B) → TopologicalSpace (E₁ b ⊗[𝕜] E₂ b) := fun b ↦ inferInstance
  exact ⟨_, ⟨e₁, e₂, he₁, he₂, rfl⟩, rfl⟩

section WeakTrivialization

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

variable {B : Type*}
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  (E₁ : B → Type*) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)]

variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  (E₂ : B → Type*) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)]

variable {E₁ E₂}
variable [TopologicalSpace B]

variable [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
variable [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

variable (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
variable [he₁ : MemTrivializationAtlas e₁] [he₂ : MemTrivializationAtlas e₂]

@[simp]
theorem _root_.Trivialization.baseSet_tensorProduct :
    (e₁.tensorProduct (𝕜 := 𝕜) e₂).baseSet = e₁.baseSet ∩ e₂.baseSet :=
  rfl

theorem _root_.Trivialization.tensorProduct_apply
    (p : TotalSpace (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)) :
    e₁.tensorProduct (𝕜 := 𝕜) e₂ p =
      ⟨p.1, TensorProduct.map
        (e₁.continuousLinearMapAt 𝕜 p.1).toLinearMap
        (e₂.continuousLinearMapAt 𝕜 p.1).toLinearMap p.2⟩ :=
  rfl

@[simp, mfld_simps]
theorem tensorProduct_trivializationAt_source (x₀ : B) :
      letI : (x : B) → TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      tensorFiberTop (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    (trivializationAt (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x) x₀).source =
      π (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x) ⁻¹'
        ((trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet) :=
  rfl

@[simp, mfld_simps]
theorem tensorProduct_trivializationAt_target (x₀ : B) :
      letI : (x : B) → TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      tensorFiberTop (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    (trivializationAt (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x) x₀).target =
      ((trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet) ×ˢ Set.univ :=
  rfl

@[simp]
theorem tensorProduct_trivializationAt_baseSet (x₀ : B) :
    letI : (x : B) → TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      tensorFiberTop (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    (trivializationAt (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x) x₀).baseSet =
      ((trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet) :=
  rfl

end WeakTrivialization

end Bundle.TensorProduct

end

open scoped Manifold

section Smooth

open Pretrivialization

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  (IB : ModelWithCorners 𝕜 EB HB)
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
variable (n : WithTop ℕ∞)
variable [∀ (x : B), ContinuousAdd (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
variable [∀ (x : B), ContinuousAdd (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
variable [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB]

instance Bundle.TensorProduct.vectorPrebundle.isContMDiff :
    letI (x : B) : TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      Bundle.TensorProduct.tensorFiberTopology 𝕜 F₁ F₂ E₁ E₂ x
    (Bundle.TensorProduct.vectorPrebundle
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)).IsContMDiff IB n := by
  let (x : B) : TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
    Bundle.TensorProduct.tensorFiberTopology 𝕜 F₁ F₂ E₁ E₂ x
  exact {
    exists_contMDiffCoordChange := by
      rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
      have := he₁; have := he₂; have := he₁'; have := he₂'
      refine ⟨tensorProductCoordChange (𝕜 := 𝕜) e₁ e₁' e₂ e₂',
        contMDiffOn_tensorProductCoordChange IB n, ?_⟩
      rintro b hb v
      exact tensorProductCoordChange_apply (𝕜 := 𝕜) e₁ e₁' e₂ e₂' b hb v
  }

instance ContMDiffVectorBundle.tensorProduct :
    letI (x : B) : TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      Bundle.TensorProduct.tensorFiberTopology 𝕜 F₁ F₂ E₁ E₂ x
    ContMDiffVectorBundle n (F₁ ⊗[𝕜] F₂) (fun x => E₁ x ⊗[𝕜] E₂ x) IB := by
  let (x : B) : TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
    Bundle.TensorProduct.tensorFiberTopology 𝕜 F₁ F₂ E₁ E₂ x
  exact (Bundle.TensorProduct.vectorPrebundle
    (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂)
    (E₁ := E₁) (E₂ := E₂)).contMDiffVectorBundle IB

end Smooth
