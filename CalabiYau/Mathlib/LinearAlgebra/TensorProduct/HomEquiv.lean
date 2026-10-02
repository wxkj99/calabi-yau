-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Tensor/Product/HomEquiv.lean
-- Locally modified.
/-
Authors: Yuan Liao, Jack McCarthy
-/
module
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars

@[expose] public section


namespace CalabiYau.Tensor.Product

open scoped Topology TensorProduct

noncomputable section

section TensorNorm

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
variable (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]

omit [FiniteDimensional 𝕜 F₂] in
noncomputable def tensorHomEquiv : (F₁ ⊗[𝕜] F₂) ≃ₗ[𝕜] ((Module.Dual 𝕜 F₁) →ₗ[𝕜] F₂) := by
  let f : Module.Dual 𝕜 (Module.Dual 𝕜 F₁) ≃ₗ[𝕜] F₁ := (Module.evalEquiv 𝕜 F₁).symm
  have h₀ : (Module.Dual 𝕜 (Module.Dual 𝕜 F₁)) ⊗[𝕜] F₂ ≃ₗ[𝕜] (F₁ ⊗[𝕜] F₂) :=
    let g : (Module.Dual 𝕜 (Module.Dual 𝕜 F₁) ⊗[𝕜] F₂) →ₗ[𝕜] (F₁ ⊗[𝕜] F₂) :=
      TensorProduct.lift ((TensorProduct.mk 𝕜 F₁ F₂) ∘ₗ f.toLinearMap)
    let ginv : (F₁ ⊗[𝕜] F₂) →ₗ[𝕜] (Module.Dual 𝕜 (Module.Dual 𝕜 F₁) ⊗[𝕜] F₂) :=
      TensorProduct.lift
        ((TensorProduct.mk 𝕜 (Module.Dual 𝕜 (Module.Dual 𝕜 F₁)) F₂) ∘ₗ f.symm.toLinearMap)
    have left_inv₀ : ginv ∘ₗ g = LinearMap.id := by
      ext v w
      unfold ginv g
      simp
    have left_inv : ∀ x, ginv (g x) = x := by
      intro x
      rw [←@Function.comp_apply _ _ _ ginv g x]
      have h : (ginv ∘ₗ g : (Module.Dual 𝕜 (Module.Dual 𝕜 F₁) ⊗[𝕜] F₂) →
        (Module.Dual 𝕜 (Module.Dual 𝕜 F₁) ⊗[𝕜] F₂)) = ginv ∘ g := by simp
      rw [←h, left_inv₀]
      simp
    have right_inv₀ : g ∘ₗ ginv = LinearMap.id := by
      ext v w
      unfold ginv g
      simp
    have right_inv : ∀ x, g (ginv x) = x := by
      intro x
      rw [←@Function.comp_apply _ _ _ g ginv x]
      have h : (g ∘ₗ ginv : (F₁ ⊗[𝕜] F₂) → (F₁ ⊗[𝕜] F₂)) = g ∘ ginv := by simp
      rw [←h, right_inv₀]
      simp
    LinearEquiv.mk g ginv left_inv right_inv
  have h₁ := (dualTensorHomEquiv 𝕜 (Module.Dual 𝕜 F₁) F₂)
  exact LinearEquiv.trans (LinearEquiv.symm h₀) h₁

abbrev cDual := F₁ →L[𝕜] 𝕜

omit [FiniteDimensional 𝕜 F₂]

def cDualEqivDual : cDual 𝕜 F₁ ≃ₗ[𝕜] Module.Dual 𝕜 F₁ := by
  unfold cDual Module.Dual
  exact (@LinearMap.toContinuousLinearMap 𝕜 _ F₁ _ _ _ _ _ 𝕜 _ _ _ _ _ _ _ _).symm

def cDualClmEquivDualLm : (cDual 𝕜 F₁ →L[𝕜] F₂) ≃ₗ[𝕜] (Module.Dual 𝕜 F₁ →ₗ[𝕜] F₂) := by
  have e : (cDual 𝕜 F₁ →L[𝕜] F₂) ≃ₗ[𝕜] (cDual 𝕜 F₁ →ₗ[𝕜] F₂) := LinearMap.toContinuousLinearMap.symm
  have e' : (cDual 𝕜 F₁ →ₗ[𝕜] F₂) ≃ₗ[𝕜] (Module.Dual 𝕜 F₁ →ₗ[𝕜] F₂) :=
    LinearEquiv.congrLeft F₂ 𝕜 (cDualEqivDual 𝕜 F₁)
  exact LinearEquiv.trans e e'

noncomputable def clmEquiv : (F₁ ⊗[𝕜] F₂) ≃ₗ[𝕜] (cDual 𝕜 F₁ →L[𝕜] F₂) :=
  LinearEquiv.trans (tensorHomEquiv 𝕜 F₁ F₂) (cDualClmEquivDualLm 𝕜 F₁ F₂).symm

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

noncomputable instance instNormedSpaceTensor :
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

end TensorNorm

end

end CalabiYau.Tensor.Product
