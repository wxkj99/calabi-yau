-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Tensor/Product/Pretrivialization.lean
-- Locally modified.
/-
Authors: Yuan Liao, Jack McCarthy
Modified by: Ziyang Qin
-/
module
public import CalabiYau.Geometry.Manifold.Tensor.Product.Defs
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Topology.FiberBundle.Basic

@[expose] public section

open scoped Topology
open scoped TensorProduct

noncomputable section

open Bundle Set Topology
open scoped Bundle TensorProduct

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

variable {B : Type*}
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  (E₁ : B → Type*) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)]

variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  (E₂ : B → Type*) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)]

variable {E₁ E₂}
variable [TopologicalSpace B] (e₁ e₁' : Trivialization F₁ (π F₁ E₁))
  (e₂ e₂' : Trivialization F₂ (π F₂ E₂))

namespace Pretrivialization

def tensorProductCoordChange [e₁.IsLinear 𝕜] [e₁'.IsLinear 𝕜] [e₂.IsLinear 𝕜] [e₂'.IsLinear 𝕜]
    (b : B) : (F₁ ⊗[𝕜] F₂) →L[𝕜] (F₁ ⊗[𝕜] F₂) :=
  TensorProduct.mapLFiniteDimensional (e₁.coordChangeL 𝕜 e₁' b) (e₂.coordChangeL 𝕜 e₂' b)

variable {e₁ e₁' e₂ e₂'}
variable [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁]
variable [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂]

theorem continuousOn_tensorProductCoordChange
    [VectorBundle 𝕜 F₁ E₁] [VectorBundle 𝕜 F₂ E₂]
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
    ContinuousOn (tensorProductCoordChange (𝕜 := 𝕜) e₁ e₁' e₂ e₂')
      (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) := by
  classical
  have h₁ := continuousOn_coordChange 𝕜 e₁ e₁'
  have h₂ := continuousOn_coordChange 𝕜 e₂ e₂'
  let s : Set B := (e₁.baseSet ∩ e₂.baseSet) ∩ (e₁'.baseSet ∩ e₂'.baseSet)
  have hs1 : s ⊆ (e₁.baseSet ∩ e₁'.baseSet) := fun b hb => ⟨hb.1.1, hb.2.1⟩
  have hs2 : s ⊆ (e₂.baseSet ∩ e₂'.baseSet) := fun b hb => ⟨hb.1.2, hb.2.2⟩
  have h₁' : ContinuousOn (fun b => (e₁.coordChangeL 𝕜 e₁' b : F₁ →L[𝕜] F₁)) s :=
    h₁.mono hs1
  have h₂' : ContinuousOn (fun b => (e₂.coordChangeL 𝕜 e₂' b : F₂ →L[𝕜] F₂)) s :=
    h₂.mono hs2
  have huncurry : Continuous (fun p : (F₁ →L[𝕜] F₁) × (F₂ →L[𝕜] F₂) =>
                              TensorProduct.mapLBilinear p.1 p.2) :=
    (TensorProduct.mapLBilinear (𝕜 := 𝕜) (F₁ := F₁) (F₂ := F₂)
      (G₁ := F₁) (G₂ := F₂)).continuous₂
  have hprod : ContinuousOn (fun b =>
        ((e₁.coordChangeL 𝕜 e₁' b : F₁ →L[𝕜] F₁),
         (e₂.coordChangeL 𝕜 e₂' b : F₂ →L[𝕜] F₂))) s :=
    h₁'.prodMk h₂'
  refine (huncurry.comp_continuousOn hprod).congr ?_
  intro b hb
  simp only [Function.comp_apply]
  exact rfl

variable (𝕜 e₁ e₁' e₂ e₂')
variable [e₁.IsLinear 𝕜] [e₁'.IsLinear 𝕜] [e₂.IsLinear 𝕜] [e₂'.IsLinear 𝕜]

def tensorProduct :
    Pretrivialization (F₁ ⊗[𝕜] F₂) (π (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)) where
  toFun p := ⟨p.1, TensorProduct.map
    (e₁.continuousLinearMapAt 𝕜 p.1).toLinearMap
    (e₂.continuousLinearMapAt 𝕜 p.1).toLinearMap p.2⟩
  invFun p := ⟨p.1, TensorProduct.map
    (e₁.symmL 𝕜 p.1).toLinearMap
    (e₂.symmL 𝕜 p.1).toLinearMap p.2⟩
  source := Bundle.TotalSpace.proj ⁻¹' (e₁.baseSet ∩ e₂.baseSet)
  target := (e₁.baseSet ∩ e₂.baseSet) ×ˢ Set.univ
  map_source' := fun ⟨_, _⟩ h ↦ ⟨h, Set.mem_univ _⟩
  map_target' := fun ⟨_, _⟩ h ↦ h.1
  left_inv' := fun ⟨x, v⟩ ⟨h₁, h₂⟩ ↦ by
      simp only [TotalSpace.mk_inj]
      rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
      have eq1 : (e₁.symmL 𝕜 x).toLinearMap.comp (e₁.continuousLinearMapAt 𝕜 x).toLinearMap =
         LinearMap.id := by
        ext w
        simp only [LinearMap.comp_apply, LinearMap.id_apply]
        apply Trivialization.symmL_continuousLinearMapAt e₁ h₁
      have eq2 : (e₂.symmL 𝕜 x).toLinearMap.comp (e₂.continuousLinearMapAt 𝕜 x).toLinearMap =
        LinearMap.id := by
        ext w
        simp only [LinearMap.comp_apply, LinearMap.id_apply]
        apply Trivialization.symmL_continuousLinearMapAt e₂ h₂
      rw [eq1, eq2, TensorProduct.map_id, LinearMap.id_apply]
  right_inv' := fun ⟨x, t⟩ ⟨⟨h₁, h₂⟩, _⟩ ↦ by
      simp only [Prod.mk.injEq, true_and]
      rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
      have eq1 : (e₁.continuousLinearMapAt 𝕜 x).toLinearMap.comp (e₁.symmL 𝕜 x).toLinearMap =
         LinearMap.id := by
        ext w
        simp only [LinearMap.comp_apply, LinearMap.id_apply]
        apply Trivialization.continuousLinearMapAt_symmL e₁ h₁
      have eq2 : (e₂.continuousLinearMapAt 𝕜 x).toLinearMap.comp (e₂.symmL 𝕜 x).toLinearMap =
         LinearMap.id := by
        ext w
        simp only [LinearMap.comp_apply, LinearMap.id_apply]
        apply Trivialization.continuousLinearMapAt_symmL e₂ h₂
      rw [eq1, eq2, TensorProduct.map_id, LinearMap.id_apply]
  open_target := (e₁.open_baseSet.inter e₂.open_baseSet).prod isOpen_univ
  baseSet := e₁.baseSet ∩ e₂.baseSet
  open_baseSet := e₁.open_baseSet.inter e₂.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

omit [FiniteDimensional 𝕜 F₂] in
theorem tensorProduct_apply (p : TotalSpace (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)) :
    (tensorProduct 𝕜 e₁ e₂) p =
      ⟨p.1, TensorProduct.map
        (e₁.continuousLinearMapAt 𝕜 p.1).toLinearMap
        (e₂.continuousLinearMapAt 𝕜 p.1).toLinearMap p.2⟩ :=
  rfl

instance tensorProduct.isLinear :
    (Pretrivialization.tensorProduct 𝕜 e₁ e₂).IsLinear 𝕜 where
  linear x hx :=
  by
    classical
    refine
      { map_add := ?_
        map_smul := ?_ }
    · intro t t'
      simp [Pretrivialization.tensorProduct_apply]
    · intro c t
      simp [Pretrivialization.tensorProduct_apply]

omit [FiniteDimensional 𝕜 F₂] in
theorem tensorProduct_symm_apply_of_mem {b : B} (hb : b ∈ e₁.baseSet ∩ e₂.baseSet) (t : F₁ ⊗[𝕜] F₂) :
    (tensorProduct 𝕜 e₁ e₂).symm b t =
      TensorProduct.map
        (e₁.symmL 𝕜 b).toLinearMap
        (e₂.symmL 𝕜 b).toLinearMap t := by
  rw [Pretrivialization.symm_apply]
  · rfl
  · exact hb

theorem tensorProductCoordChange_apply (b : B)
    (hb : b ∈ e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) (t : F₁ ⊗[𝕜] F₂) :
    tensorProductCoordChange (𝕜 := 𝕜) e₁ e₁' e₂ e₂' b t =
      (tensorProduct 𝕜 e₁' e₂' ⟨b, (tensorProduct 𝕜 e₁ e₂).symm b t⟩).2 := by
  simp only [tensorProductCoordChange, TensorProduct.mapLFiniteDimensional]
  simp only [LinearMap.coe_toContinuousLinearMap',
    tensorProduct_symm_apply_of_mem (𝕜 := 𝕜) (e₁ := e₁) (e₂ := e₂) hb.1,
    tensorProduct_apply]
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
  congr 1 ; ext v
  rename_i v x
  have hb1 : b ∈ e₁.baseSet ∩ e₁'.baseSet := ⟨hb.1.1, hb.2.1⟩
  have hb2 : b ∈ e₂.baseSet ∩ e₂'.baseSet := ⟨hb.1.2, hb.2.2⟩
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_self,
    TensorProduct.curry_apply, TensorProduct.map_tmul, ContinuousLinearMap.coe_coe,
    ContinuousLinearEquiv.coe_coe, LinearMap.coe_comp, Trivialization.continuousLinearMapAt_apply,
    Function.comp_apply]
  rw [Trivialization.coordChangeL_apply (R := 𝕜) (e := e₁) (e' := e₁') (b := b) hb1 (y := v)]
  rw [Trivialization.coordChangeL_apply (R := 𝕜) (e := e₂) (e' := e₂') (b := b) hb2 (y := x)]
  simp only [TensorProduct.tmul, AddCon.coe_mk', Trivialization.linearMapAt]
  simp only [Pretrivialization.linearMapAt]
  have hb1' : b ∈ e₁'.toPretrivialization.baseSet := by
    change b ∈ e₁'.baseSet
    exact hb.2.1
  have hb2' : b ∈ e₂'.toPretrivialization.baseSet := by
    change b ∈ e₂'.baseSet
    exact hb.2.2
  simp only [hb1', ↓reduceDIte, LinearEquiv.coe_coe,
    Pretrivialization.linearEquivAt_apply, hb2']
  rw [Trivialization.symmL_apply _ hb.1.1,
    Trivialization.symmL_apply _ hb.1.2]
  rfl

end Pretrivialization

section

open Pretrivialization

open scoped Manifold

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
variable {e₁ e₁' : Trivialization F₁ (π F₁ E₁)}
  {e₂ e₂' : Trivialization F₂ (π F₂ E₂)}
variable (n : WithTop ℕ∞)

theorem contMDiffOn_tensorProductCoordChange
    [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB]
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
    ContMDiffOn IB 𝓘(𝕜, (F₁ ⊗[𝕜] F₂) →L[𝕜] (F₁ ⊗[𝕜] F₂)) n
      (Pretrivialization.tensorProductCoordChange (𝕜 := 𝕜) e₁ e₁' e₂ e₂')
      (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) := by
  have h₁ : ContMDiffOn IB 𝓘(𝕜, F₁ →L[𝕜] F₁) n
      (fun b => (e₁.coordChangeL 𝕜 e₁' b : F₁ →L[𝕜] F₁))
      (e₁.baseSet ∩ e₁'.baseSet) := contMDiffOn_coordChangeL (IB := IB) e₁ e₁'
  have h₂ : ContMDiffOn IB 𝓘(𝕜, F₂ →L[𝕜] F₂) n
      (fun b => (e₂.coordChangeL 𝕜 e₂' b : F₂ →L[𝕜] F₂))
      (e₂.baseSet ∩ e₂'.baseSet) := contMDiffOn_coordChangeL (IB := IB) e₂ e₂'
  have h_comp₁ : ContMDiffOn IB 𝓘(𝕜, (F₂ →L[𝕜] F₂) →L[𝕜]
      ((F₁ ⊗[𝕜] F₂) →L[𝕜] (F₁ ⊗[𝕜] F₂))) n
      (fun b => TensorProduct.mapLBilinear (𝕜 := 𝕜)
        (e₁.coordChangeL 𝕜 e₁' b : F₁ →L[𝕜] F₁))
      (e₁.baseSet ∩ e₁'.baseSet) :=
    (TensorProduct.mapLBilinear (𝕜 := 𝕜) (F₁ := F₁) (G₁ := F₁)
      (F₂ := F₂) (G₂ := F₂)).contMDiff.comp_contMDiffOn h₁
  have hs1 : e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet) ⊆
      e₁.baseSet ∩ e₁'.baseSet := fun b hb => ⟨hb.1.1, hb.2.1⟩
  have hs2 : e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet) ⊆
      e₂.baseSet ∩ e₂'.baseSet := fun b hb => ⟨hb.1.2, hb.2.2⟩
  exact (h_comp₁.mono hs1).clm_apply (h₂.mono hs2)

end
