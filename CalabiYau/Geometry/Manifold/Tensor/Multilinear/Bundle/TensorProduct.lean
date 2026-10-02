-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Tensor/Multilinear/Bundle/TensorProduct.lean
-- Locally modified.
/-
Authors: Jack McCarthy
-/
module
public import CalabiYau.Geometry.Manifold.Tensor.Multilinear.Bundle.Fiber
public import CalabiYau.Geometry.Manifold.Tensor.Multilinear.Bundle.Section
public import CalabiYau.Geometry.Manifold.Tensor.Product.Basis
public import CalabiYau.Geometry.Manifold.Tensor.Product.Bundle
public import CalabiYau.Geometry.Manifold.Bundle.Section
public import Mathlib.RingTheory.TensorProduct.Finite

@[expose] public section

open CalabiYau.Tensor.Multilinear

noncomputable section

open Bundle Set

open scoped Manifold Topology Bundle ContDiff BigOperators TensorProduct

namespace Bundle.continuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {B : Type*} [TopologicalSpace B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
variable [TopologicalSpace (TotalSpace F E)]
variable [FiberBundle F E] [VectorBundle 𝕜 F E]

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]

noncomputable def productFun {s q : ℕ} {x : B}
    (α : Bundle.continuousMultilinearMap 𝕜 s F E x)
    (β : Bundle.continuousMultilinearMap 𝕜 q F E x) :
    Bundle.continuousMultilinearMap 𝕜 (s + q) F E x :=
  ofModel (F := F) (E := E)
    ((toModel (F := F) (E := E) α |>.smulRight
      (toModel (F := F) (E := E) β)).uncurrySum.domDomCongr finSumFinEquiv)

scoped infixl:70 " ⊗ₘ " => productFun

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
theorem product_fun_apply {s q : ℕ} {x : B}
    (α : Bundle.continuousMultilinearMap 𝕜 s F E x)
    (β : Bundle.continuousMultilinearMap 𝕜 q F E x)
    (v : Fin (s + q) → E x) :
    productFun α β v = α (v ∘ Fin.castAdd q) * β (v ∘ Fin.natAdd s) := by
  have hx : x ∈ (trivializationAt F E x).baseSet := mem_baseSet_trivializationAt F E x
  change (continuousLinearEquivAt (F := F) (E := E) (s + q) x).symm
    ((toModel (F := F) (E := E) α |>.smulRight
      (toModel (F := F) (E := E) β)).uncurrySum.domDomCongr finSumFinEquiv) v = _
  have hsymm : ∀ (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin (s + q) => F) 𝕜)
      (w : Fin (s + q) → E x),
      (continuousLinearEquivAt (F := F) (E := E) (s + q) x).symm f w =
      f (fun i => (trivializationAt F E x).continuousLinearMapAt 𝕜 x (w i)) := by
    intro f w; rfl
  rw [hsymm]
  simp only [ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.uncurrySum_apply,
    ContinuousMultilinearMap.smulRight_apply]
  conv_lhs =>
    rw [show ∀ (c : 𝕜) (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜)
        (w : Fin q → F), (c • f) w = c * f w
      from fun c f w => by simp [smul_apply, smul_eq_mul]]
  simp_rw [show ∀ (n : ℕ) (T : Bundle.continuousMultilinearMap 𝕜 n F E x)
      (w : Fin n → F), toModel T w =
      T (fun i => (trivializationAt F E x).symmL 𝕜 x (w i)) from fun _ _ _ => rfl,
    Function.comp, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
  congr 1
  · congr 1; funext i; simp only [Function.comp]
    exact (trivializationAt F E x).symmₗ_linearMapAt hx _
  · congr 1; funext i; simp only [Function.comp]
    exact (trivializationAt F E x).symmₗ_linearMapAt hx _

theorem triv_coord_product {s q d : ℕ}
    (b : Module.Basis (Fin d) 𝕜 F)
    (σ : Fin (s + q) → Fin d) (x₀ x : B)
    (α : Bundle.continuousMultilinearMap 𝕜 s F E x)
    (β : Bundle.continuousMultilinearMap 𝕜 q F E x) :
    (continuousMultilinearMapBasis b (s + q)).repr
      (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin (s + q) => F) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 (s + q) F E x) x₀
        ⟨x, productFun α β⟩).2 σ =
    (continuousMultilinearMapBasis b s).repr
      (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x) x₀ ⟨x, α⟩).2
        (σ ∘ Fin.castAdd q) *
    (continuousMultilinearMapBasis b q).repr
      (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 q F E x) x₀ ⟨x, β⟩).2
        (σ ∘ Fin.natAdd s) := by
  simp_rw [continuousMultilinearMap_basis_repr]
  have htriv : ∀ (n : ℕ) (T : Bundle.continuousMultilinearMap 𝕜 n F E x)
      (w : Fin n → F),
      (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin n => F) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 n F E x) x₀ ⟨x, T⟩).2 w =
      T (fun i => (trivializationAt F E x₀).symmL 𝕜 x (w i)) := by
    intro n T w; rfl
  simp_rw [htriv, product_fun_apply]
  rfl

noncomputable def equiv (s q : ℕ) (x : B) :
    Bundle.continuousMultilinearMap 𝕜 (s + q) F E x ≃ₗ[𝕜]
    TensorProduct 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x)
      (Bundle.continuousMultilinearMap 𝕜 q F E x) := by
  haveI := instFiniteDimensional (𝕜 := 𝕜) (F := F) (E := E) s x
  haveI := instFiniteDimensional (𝕜 := 𝕜) (F := F) (E := E) q x
  haveI := instFiniteDimensional (𝕜 := 𝕜) (F := F) (E := E) (s + q) x
  haveI : Module.Free 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x) :=
    Module.Free.of_divisionRing 𝕜 _
  haveI : Module.Free 𝕜 (Bundle.continuousMultilinearMap 𝕜 q F E x) :=
    Module.Free.of_divisionRing 𝕜 _
  haveI : Module.Free 𝕜 (Bundle.continuousMultilinearMap 𝕜 (s + q) F E x) :=
    Module.Free.of_divisionRing 𝕜 _
  haveI : FiniteDimensional 𝕜 (TensorProduct 𝕜
      (Bundle.continuousMultilinearMap 𝕜 s F E x)
      (Bundle.continuousMultilinearMap 𝕜 q F E x)) :=
    Module.Finite.tensorProduct 𝕜 _ _
  exact LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_tensorProduct,
        finrank_eq (𝕜 := 𝕜) (F := F) (E := E) s x,
        finrank_eq (𝕜 := 𝕜) (F := F) (E := E) q x,
        finrank_eq (𝕜 := 𝕜) (F := F) (E := E) (s + q) x, pow_add])

end Bundle.continuousMultilinearMap

end

noncomputable section

open Bundle Set ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff BigOperators TensorProduct

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]

local notation "MLF" s => ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]

namespace Bundle.continuousMultilinearMap

end Bundle.continuousMultilinearMap

namespace CalabiYau.MultilinearSection

variable (n : WithTop ℕ∞) [ContMDiffVectorBundle n F E IB]

section Product

variable {s q : ℕ}

noncomputable def product
    (α : MultilinearSection 𝕜 F IB E n s)
    (β : MultilinearSection 𝕜 F IB E n q) :
    MultilinearSection 𝕜 F IB E n (s + q) :=
  ⟨fun x => (α x).productFun (β x), by
    let d := Module.finrank 𝕜 F
    let b : Module.Basis (Fin d) 𝕜 F := Module.finBasis 𝕜 F
    rw [contMDiff_multilinearSection_iff_coord E n b]
    intro σ x₀
    have hα := ((contMDiff_multilinearSection_iff_coord E n b
      (fun x => (α x : Bundle.continuousMultilinearMap 𝕜 s F E x))).mp α.contMDiff)
    have hβ := ((contMDiff_multilinearSection_iff_coord E n b
      (fun x => (β x : Bundle.continuousMultilinearMap 𝕜 q F E x))).mp β.contMDiff)
    simp_rw [Bundle.continuousMultilinearMap.triv_coord_product b σ x₀ _ (α _) (β _)]
    exact (contMDiffAt_const (c := ContinuousLinearMap.mul 𝕜 𝕜).clm_apply
      (hα (σ ∘ Fin.castAdd q) x₀)).clm_apply (hβ (σ ∘ Fin.natAdd s) x₀)⟩

@[simp] theorem product_zero (α : MultilinearSection 𝕜 F IB E n s) :
    product (IB := IB) n α (0 : MultilinearSection 𝕜 F IB E n q)
      = (0 : MultilinearSection 𝕜 F IB E n (s + q)) := by
  refine DFunLike.ext _ _ fun x => ?_
  ext V
  change Bundle.continuousMultilinearMap.productFun (α x)
    ((0 : MultilinearSection 𝕜 F IB E n q) x) V = _
  simp [Bundle.continuousMultilinearMap.product_fun_apply, ContMDiffSection.coe_zero]

end Product

section TensorProductInstances

variable {s q : ℕ}

local instance multilinearTensorFiberTopology {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜]
    {B : Type*} [TopologicalSpace B] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
    [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] [VectorBundle 𝕜 F E] (s q : ℕ) :
    ∀ x : B, TopologicalSpace (Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                                Bundle.continuousMultilinearMap 𝕜 q F E x) :=
  Bundle.TensorProduct.tensorFiberTopology 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜)
    (Bundle.continuousMultilinearMap 𝕜 s F E)
    (Bundle.continuousMultilinearMap 𝕜 q F E)

local instance multilinearTensorFiberBundle {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜]
    {B : Type*} [TopologicalSpace B] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
    [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] [VectorBundle 𝕜 F E] (s q : ℕ) :
    FiberBundle
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜 ⊗[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜)
      (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 q F E x) :=
  Bundle.TensorProduct.fiberBundle (𝕜 := 𝕜)
    (F₁ := ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (F₂ := ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜)
    (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
    (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)

local instance multilinearTensorVectorBundle {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜]
    {B : Type*} [TopologicalSpace B] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
    [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] [VectorBundle 𝕜 F E] (s q : ℕ) :
    VectorBundle 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜 ⊗[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜)
      (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 q F E x) :=
  Bundle.TensorProduct.vectorBundle (𝕜 := 𝕜)
    (F₁ := ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (F₂ := ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜)
    (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
    (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)

section BundleEquiv

open Bundle.continuousMultilinearMap

end BundleEquiv

end TensorProductInstances

end CalabiYau.MultilinearSection

end
