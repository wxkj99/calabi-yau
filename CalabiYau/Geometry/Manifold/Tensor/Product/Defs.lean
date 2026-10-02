-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Tensor/Product/Defs.lean
-- Locally modified.
/-
Authors: Yuan Liao, Jack McCarthy
-/
module
public import CalabiYau.Geometry.Manifold.Tensor.Product.HomEquiv
public import CalabiYau.Geometry.Manifold.Tensor.RSTensor.Defs

public import CalabiYau.Geometry.Manifold.Tensor.Alternating.Curry

@[expose] public section

open scoped Topology TensorProduct

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]

variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]

section MapL

variable {G₁ G₂ : Type*}
  [NormedAddCommGroup G₁] [NormedSpace 𝕜 G₁] [FiniteDimensional 𝕜 G₁]
  [NormedAddCommGroup G₂] [NormedSpace 𝕜 G₂] [FiniteDimensional 𝕜 G₂]

noncomputable def TensorProduct.mapLFiniteDimensional (L₁ : F₁ →L[𝕜] G₁) (L₂ : F₂ →L[𝕜] G₂) :
    (F₁ ⊗[𝕜] F₂) →L[𝕜] (G₁ ⊗[𝕜] G₂) :=
  (TensorProduct.map L₁.toLinearMap L₂.toLinearMap).toContinuousLinearMap

omit [FiniteDimensional 𝕜 G₂] in
@[simp]
theorem TensorProduct.mapLFiniteDimensional_tmul (L₁ : F₁ →L[𝕜] G₁) (L₂ : F₂ →L[𝕜] G₂) (v : F₁) (w : F₂) :
    TensorProduct.mapLFiniteDimensional L₁ L₂ (v ⊗ₜ w) = L₁ v ⊗ₜ L₂ w := by
  simp [TensorProduct.mapLFiniteDimensional, TensorProduct.map_tmul]

omit [FiniteDimensional 𝕜 G₂] in
theorem TensorProduct.mapLFiniteDimensional_add_left (L₁ L₁' : F₁ →L[𝕜] G₁) (L₂ : F₂ →L[𝕜] G₂) :
    TensorProduct.mapLFiniteDimensional (L₁ + L₁') L₂ =
      TensorProduct.mapLFiniteDimensional L₁ L₂ + TensorProduct.mapLFiniteDimensional L₁' L₂ := by
  ext x; simp [TensorProduct.mapLFiniteDimensional, TensorProduct.map_add_left]

omit [FiniteDimensional 𝕜 G₂] in
theorem TensorProduct.mapLFiniteDimensional_add_right (L₁ : F₁ →L[𝕜] G₁) (L₂ L₂' : F₂ →L[𝕜] G₂) :
    TensorProduct.mapLFiniteDimensional L₁ (L₂ + L₂') =
      TensorProduct.mapLFiniteDimensional L₁ L₂ + TensorProduct.mapLFiniteDimensional L₁ L₂' := by
  ext x; simp [TensorProduct.mapLFiniteDimensional, TensorProduct.map_add_right]

omit [FiniteDimensional 𝕜 G₂] in
theorem TensorProduct.mapLFiniteDimensional_smul_left (c : 𝕜) (L₁ : F₁ →L[𝕜] G₁) (L₂ : F₂ →L[𝕜] G₂) :
    TensorProduct.mapLFiniteDimensional (c • L₁) L₂ = c • TensorProduct.mapLFiniteDimensional L₁ L₂ := by
  ext x; simp [TensorProduct.mapLFiniteDimensional, TensorProduct.map_smul_left]

omit [FiniteDimensional 𝕜 G₂] in
theorem TensorProduct.mapLFiniteDimensional_smul_right (c : 𝕜) (L₁ : F₁ →L[𝕜] G₁) (L₂ : F₂ →L[𝕜] G₂) :
    TensorProduct.mapLFiniteDimensional L₁ (c • L₂) = c • TensorProduct.mapLFiniteDimensional L₁ L₂ := by
  ext x; simp [TensorProduct.mapLFiniteDimensional, TensorProduct.map_smul_right]

noncomputable def TensorProduct.mapLBilinear :
    (F₁ →L[𝕜] G₁) →L[𝕜] (F₂ →L[𝕜] G₂) →L[𝕜]
      ((F₁ ⊗[𝕜] F₂) →L[𝕜] (G₁ ⊗[𝕜] G₂)) := by
  classical
  haveI : FiniteDimensional 𝕜 (F₁ →L[𝕜] G₁) := ContinuousLinearMap.finiteDimensional
  haveI : FiniteDimensional 𝕜 (F₂ →L[𝕜] G₂) := ContinuousLinearMap.finiteDimensional
  haveI : FiniteDimensional 𝕜 ((F₂ →L[𝕜] G₂) →L[𝕜] F₁ ⊗[𝕜] F₂ →L[𝕜] G₁ ⊗[𝕜] G₂)
    := ContinuousLinearMap.finiteDimensional
  let innerLM (L₁ : F₁ →L[𝕜] G₁) :
      (F₂ →L[𝕜] G₂) →ₗ[𝕜] ((F₁ ⊗[𝕜] F₂) →L[𝕜] (G₁ ⊗[𝕜] G₂)) :=
    { toFun := fun L₂ => TensorProduct.mapLFiniteDimensional (𝕜 := 𝕜) L₁ L₂
      map_add' := TensorProduct.mapLFiniteDimensional_add_right (𝕜 := 𝕜) (L₁ := L₁)
      map_smul' := fun c L₂ =>
        TensorProduct.mapLFiniteDimensional_smul_right (𝕜 := 𝕜) (L₁ := L₁) (L₂ := L₂) c }
  let innerCLM (L₁ : F₁ →L[𝕜] G₁) :
      (F₂ →L[𝕜] G₂) →L[𝕜] ((F₁ ⊗[𝕜] F₂) →L[𝕜] (G₁ ⊗[𝕜] G₂)) :=
    (innerLM (L₁ := L₁)).toContinuousLinearMap
  let outerLM :
      (F₁ →L[𝕜] G₁) →ₗ[𝕜]
        ((F₂ →L[𝕜] G₂) →L[𝕜] ((F₁ ⊗[𝕜] F₂) →L[𝕜] (G₁ ⊗[𝕜] G₂))) :=
    { toFun := fun L₁ => innerCLM (L₁ := L₁)
      map_add' := by
        intro L₁ L₁'
        ext L₂ x
        simpa [innerCLM, innerLM] using congrArg (fun f => f x)
          (TensorProduct.mapLFiniteDimensional_add_left (𝕜 := 𝕜) (L₂ := L₂) (L₁ := L₁) (L₁' := L₁'))
      map_smul' := by
        intro c L₁
        ext L₂ x
        simpa [innerCLM, innerLM] using congrArg (fun f => f x)
          (TensorProduct.mapLFiniteDimensional_smul_left (𝕜 := 𝕜) (L₂ := L₂) (L₁ := L₁) c) }
  have h : Continuous outerLM := @LinearMap.continuous_of_finiteDimensional
    _ _ (F₁ →L[𝕜] G₁) _ _ _ _ _ ((F₂ →L[𝕜] G₂) →L[𝕜] ((F₁ ⊗[𝕜] F₂) →L[𝕜] (G₁ ⊗[𝕜] G₂)))
    _ _ _ _ _ _ _ _ outerLM
  let f : (F₁ →L[𝕜] G₁) →L[𝕜]
        ((F₂ →L[𝕜] G₂) →L[𝕜] ((F₁ ⊗[𝕜] F₂) →L[𝕜] (G₁ ⊗[𝕜] G₂))) :=
    ContinuousLinearMap.mk outerLM h
  exact f

theorem TensorProduct.mapLBilinear_contDiff :
    ContDiff 𝕜 ⊤ (fun p : (F₁ →L[𝕜] G₁) × (F₂ →L[𝕜] G₂) =>
      TensorProduct.mapLBilinear (𝕜 := 𝕜) p.1 p.2) :=
  ((TensorProduct.mapLBilinear (𝕜 := 𝕜) (F₁ := F₁) (G₁ := G₁)
    (F₂ := F₂) (G₂ := G₂)).contDiff.comp contDiff_fst).clm_apply
    (contDiff_snd)

end MapL

namespace CalabiYau
namespace Tensor0SBundle

open Bundle Set IsManifold ContinuousLinearMap

open scoped Manifold Bundle ContDiff BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]

end Tensor0SBundle
end CalabiYau

namespace ContinuousAlternatingMap

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {N' : Type*} [NormedAddCommGroup N'] [NormedSpace 𝕜 N']
  {N'' : Type*} [NormedAddCommGroup N''] [NormedSpace 𝕜 N'']
  {m n : ℕ}

def tensorProductMap (g : M [⋀^Fin m]→L[𝕜] N) (h : M [⋀^Fin n]→L[𝕜] N')
    (f : N →L[𝕜] N' →L[𝕜] N'') :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin (m + n) => M) N'' :=
  (ContinuousMultilinearMap.uncurrySum
    ((f.compContinuousAlternatingMap₂ g h).toContinuousMultilinearMap
      |>.flipAlternating.toContinuousMultilinearMap.flipMultilinear))
  |>.domDomCongr finSumFinEquiv

@[simp]
theorem tensorProductMap_apply (g : M [⋀^Fin m]→L[𝕜] N) (h : M [⋀^Fin n]→L[𝕜] N')
    (f : N →L[𝕜] N' →L[𝕜] N'') (w : Fin (m + n) → M) :
    tensorProductMap g h f w =
      f (g (w ∘ Fin.castAdd n)) (h (w ∘ Fin.natAdd m)) := by
  unfold tensorProductMap
  simp only [ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.uncurrySum_apply,
    ContinuousMultilinearMap.flipMultilinear_apply,
    coe_toContinuousMultilinearMap,
    ContinuousMultilinearMap.flipAlternating_apply,
    ContinuousLinearMap.compContinuousAlternatingMap₂_apply]
  rfl

end ContinuousAlternatingMap
