-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Tensor/Product/Basis.lean
-- Locally modified.
/-
Authors: Jack McCarthy
Modified by: Ziyang Qin
-/
module
public import CalabiYau.Geometry.Manifold.Tensor.Product.Bundle
public import Mathlib.LinearAlgebra.TensorProduct.Basis

@[expose] public section

namespace CalabiYau.Tensor.Product

noncomputable section

open scoped TensorProduct

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]

noncomputable instance tensorProduct_finiteDimensional :
    FiniteDimensional 𝕜 (F₁ ⊗[𝕜] F₂) :=
  Module.Finite.tensorProduct 𝕜 F₁ F₂

noncomputable def tensorProductBasis {d₁ d₂ : ℕ}
    (b₁ : Module.Basis (Fin d₁) 𝕜 F₁) (b₂ : Module.Basis (Fin d₂) 𝕜 F₂) :
    Module.Basis (Fin d₁ × Fin d₂) 𝕜 (F₁ ⊗[𝕜] F₂) :=
  b₁.tensorProduct b₂

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂] in
@[simp]
theorem tensorProduct_basis_apply {d₁ d₂ : ℕ}
    (b₁ : Module.Basis (Fin d₁) 𝕜 F₁) (b₂ : Module.Basis (Fin d₂) 𝕜 F₂)
    (i : Fin d₁) (j : Fin d₂) :
    tensorProductBasis b₁ b₂ (i, j) = b₁ i ⊗ₜ b₂ j :=
  Module.Basis.tensorProduct_apply b₁ b₂ i j

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂] in
theorem tensorProduct_basis_apply_pair {d₁ d₂ : ℕ}
    (b₁ : Module.Basis (Fin d₁) 𝕜 F₁) (b₂ : Module.Basis (Fin d₂) 𝕜 F₂)
    (p : Fin d₁ × Fin d₂) :
    tensorProductBasis b₁ b₂ p = b₁ p.1 ⊗ₜ b₂ p.2 :=
  Module.Basis.tensorProduct_apply' b₁ b₂ p

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂] in
theorem tensorProduct_basis_repr_tmul {d₁ d₂ : ℕ}
    (b₁ : Module.Basis (Fin d₁) 𝕜 F₁) (b₂ : Module.Basis (Fin d₂) 𝕜 F₂)
    (v : F₁) (w : F₂) (i : Fin d₁) (j : Fin d₂) :
    (tensorProductBasis b₁ b₂).repr (v ⊗ₜ w) (i, j) = b₁.repr v i * b₂.repr w j := by
  change (b₁.tensorProduct b₂).repr (v ⊗ₜ w) (i, j) = _
  rw [Module.Basis.tensorProduct_repr_tmul_apply, smul_eq_mul, mul_comm]

section smooth

open _root_.Bundle Set

open scoped Manifold Topology Bundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable (E₁ : B → Type*) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
variable (E₂ : B → Type*) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
variable [∀ x, ContinuousAdd (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
variable [∀ x, ContinuousAdd (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
variable (n : WithTop ℕ∞)
variable [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB]

omit [∀ x, ContinuousAdd (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
  [∀ x, ContinuousAdd (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB] in
theorem contMDiff_tensorProductSection_iff_coord
    {d₁ d₂ : ℕ}
    (b₁ : Module.Basis (Fin d₁) 𝕜 F₁)
    (b₂ : Module.Basis (Fin d₂) 𝕜 F₂)
    (f : ∀ x : B, E₁ x ⊗[𝕜] E₂ x) :
    letI := _root_.Bundle.TensorProduct.tensorFiberTopology 𝕜 F₁ F₂ E₁ E₂
    letI := _root_.Bundle.TensorProduct.fiberBundle
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    ContMDiff IB (IB.prod 𝓘(𝕜, F₁ ⊗[𝕜] F₂)) n
      (fun x => TotalSpace.mk' (F₁ ⊗[𝕜] F₂) x (f x)) ↔
    ∀ p : Fin d₁ × Fin d₂, ∀ x₀ : B,
      ContMDiffAt IB 𝓘(𝕜, 𝕜) n
        (fun x => (tensorProductBasis b₁ b₂).repr
          (trivializationAt (F₁ ⊗[𝕜] F₂)
            (fun x => E₁ x ⊗[𝕜] E₂ x) x₀ ⟨x, f x⟩).2 p) x₀ := by
  let := _root_.Bundle.TensorProduct.tensorFiberTopology 𝕜 F₁ F₂ E₁ E₂
  let := _root_.Bundle.TensorProduct.fiberBundle
    (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
  let : ChartedSpace (ModelProd HB (F₁ ⊗[𝕜] F₂))
      (TotalSpace (F₁ ⊗[𝕜] F₂) (fun x => E₁ x ⊗[𝕜] E₂ x)) :=
    FiberBundle.chartedSpace
  set Bb := tensorProductBasis b₁ b₂
  constructor
  · intro hf p x₀
    have hsec := (contMDiffAt_section x₀).mp hf.contMDiffAt
    exact (LinearMap.toContinuousLinearMap (Bb.coord p)).contMDiffAt.comp x₀ hsec
  · intro hcoord x₀
    rw [contMDiffAt_section]
    let g := fun x => (trivializationAt (F₁ ⊗[𝕜] F₂)
        (fun x => E₁ x ⊗[𝕜] E₂ x) x₀ ⟨x, f x⟩).2
    change ContMDiffAt IB 𝓘(𝕜, F₁ ⊗[𝕜] F₂) n g x₀
    rw [show g = fun x => Bb.equivFun.symm (Bb.equivFun (g x)) from
        funext fun x => (Bb.equivFun.symm_apply_apply (g x)).symm]
    exact (Bb.equivFun.symm.toContinuousLinearEquiv.toContinuousLinearMap.contMDiffAt).comp x₀
      (contMDiffAt_pi_space.mpr fun p => hcoord p x₀)

end smooth

end

end CalabiYau.Tensor.Product
