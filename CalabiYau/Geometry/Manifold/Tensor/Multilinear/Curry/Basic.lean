-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Tensor/Multilinear/Curry/Basic.lean
-- Locally modified.
/-
Authors: Jack McCarthy
-/
module
public import CalabiYau.Geometry.Manifold.Tensor.Multilinear.Bundle.Defs

@[expose] public section

namespace CalabiYau.Tensor.Multilinear

noncomputable section

open _root_.Bundle Set

open scoped Manifold Topology Bundle ContDiff BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

noncomputable def continuousMultilinearMapCurryEquiv (r r' : ℕ) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin (r + r') => F) 𝕜 ≃ₗᵢ[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r' => F) 𝕜) :=
  (ContinuousMultilinearMap.domDomCongrₗᵢ 𝕜 F 𝕜 finSumFinEquiv.symm).trans
    (ContinuousMultilinearMap.currySumEquiv 𝕜 (Fin r) (Fin r') F 𝕜)

noncomputable def continuousMultilinearMapCurryLeft (r r' : ℕ) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin (r + r') => F) 𝕜 →L[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r' => F) 𝕜) :=
  (continuousMultilinearMapCurryEquiv r r' (𝕜 := 𝕜) (F := F)).toContinuousLinearEquiv

noncomputable def continuousMultilinearMapUncurryLeft (r r' : ℕ) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r' => F) 𝕜) →L[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin (r + r') => F) 𝕜 :=
  (continuousMultilinearMapCurryEquiv r r' (𝕜 := 𝕜) (F := F)).symm.toContinuousLinearEquiv

@[simp]
theorem continuousMultilinearMap_curryLeft_uncurryLeft (r r' : ℕ)
    (g : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r' => F) 𝕜)) :
    (continuousMultilinearMapCurryLeft (𝕜 := 𝕜) (F := F) r r')
      ((continuousMultilinearMapUncurryLeft (𝕜 := 𝕜) (F := F) r r') g) = g := by
  simp [continuousMultilinearMapCurryLeft, continuousMultilinearMapUncurryLeft]

@[simp]
theorem continuousMultilinearMap_uncurryLeft_curryLeft (r r' : ℕ)
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin (r + r') => F) 𝕜) :
    (continuousMultilinearMapUncurryLeft (𝕜 := 𝕜) (F := F) r r')
      ((continuousMultilinearMapCurryLeft (𝕜 := 𝕜) (F := F) r r') f) = f := by
  simp only [continuousMultilinearMapCurryLeft, continuousMultilinearMapUncurryLeft]
  exact (continuousMultilinearMapCurryEquiv r r').toContinuousLinearEquiv.symm_apply_apply f

end

end CalabiYau.Tensor.Multilinear
