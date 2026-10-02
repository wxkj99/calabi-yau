-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Tensor/Multilinear/Flip.lean
-- Locally modified.
/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Coauthors: Jack McCarthy
-/

module
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Operator.Mul

@[expose] public section

noncomputable section Flip

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {ι : Type*} [Fintype ι]
  {E : ι → Type*} [(i : ι) → SeminormedAddCommGroup (E i)] [(i : ι) → NormedSpace 𝕜 (E i)]
  {G : Type*} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
  {G' : Type*} [SeminormedAddCommGroup G'] [NormedSpace 𝕜 G']

def LinearIsometryEquiv.flipMultilinear :
    (G →L[𝕜] ContinuousMultilinearMap 𝕜 E G') ≃ₗᵢ[𝕜]
      (ContinuousMultilinearMap 𝕜 E (G →L[𝕜] G')) where
  toFun := ContinuousLinearMap.flipMultilinear
  invFun := (ContinuousLinearMap.flipMultilinearEquiv 𝕜 E G G').invFun
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv := congrFun rfl
  right_inv := congrFun rfl
  norm_map' f := le_antisymm
    (ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m ↦
      ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x ↦ calc
        ‖f.flipMultilinear m x‖ = ‖f x m‖ := rfl
        _ ≤ ‖f x‖ * ∏ i, ‖m i‖ := (f x).le_opNorm m
        _ ≤ (‖f‖ * ‖x‖) * ∏ i, ‖m i‖ := mul_le_mul_of_nonneg_right (f.le_opNorm x) (by positivity)
        _ = ‖f‖ * (∏ i, ‖m i‖) * ‖x‖ := by ring)
    (ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x ↦
      ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m ↦ calc
        ‖f x m‖ = ‖f.flipMultilinear m x‖ := rfl
        _ ≤ ‖f.flipMultilinear m‖ * ‖x‖ := (f.flipMultilinear m).le_opNorm x
        _ ≤ (‖f.flipMultilinear‖ * ∏ i, ‖m i‖) * ‖x‖ :=
          mul_le_mul_of_nonneg_right (f.flipMultilinear.le_opNorm m) (by positivity)
        _ = ‖f.flipMultilinear‖ * ‖x‖ * ∏ i, ‖m i‖ := by ring)

namespace ContinuousMultilinearMap

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {M' : Type*} [NormedAddCommGroup M'] [NormedSpace 𝕜 M']
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {ι : Type*} [Fintype ι]
  {ι' : Type*} [Fintype ι']

def flipMultilinear (f : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ M)
    (ContinuousMultilinearMap 𝕜 (fun _ : ι' ↦ M') N)) :
    ContinuousMultilinearMap 𝕜 (fun _ : ι' ↦ M') (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ M) N) :=
  MultilinearMap.mkContinuous
    { toFun := fun m =>
        MultilinearMap.mkContinuous
          { toFun := fun m' => f m' m
            map_update_add' := fun m' i x y ↦ by
              change (f (Function.update m' i (x + y))) m
                = (f (Function.update m' i x)) m + (f (Function.update m' i y)) m
              rw [ContinuousMultilinearMap.map_update_add, add_apply]
            map_update_smul' := fun m' i c x ↦ by
              change (f (Function.update m' i (c • x))) m = c • (f (Function.update m' i x)) m
              rw [ContinuousMultilinearMap.map_update_smul, smul_apply] }
          (‖f‖ * ∏ i, ‖m i‖) (fun m' ↦ calc
            ‖f m' m‖ ≤ ‖f m'‖ * ∏ i, ‖m i‖ := (f m').le_opNorm m
            _ ≤ (‖f‖ * ∏ i, ‖m' i‖) * ∏ i, ‖m i‖ := mul_le_mul_of_nonneg_right (f.le_opNorm m')
              (by positivity)
            _ = (‖f‖ * ∏ i, ‖m i‖) * ∏ i, ‖m' i‖ := by ring)
      map_update_add' := fun m i x y
        ↦ by ext m'; exact ContinuousMultilinearMap.map_update_add (f m') m i x y
      map_update_smul' := fun m i c x
        ↦ by ext m'; exact ContinuousMultilinearMap.map_update_smul (f m') m i c x }
    ‖f‖ (fun m ↦ ContinuousMultilinearMap.opNorm_le_bound
      (mul_nonneg (norm_nonneg f) (by positivity)) fun m' ↦ calc
        ‖f m' m‖ ≤ ‖f m'‖ * ∏ i, ‖m i‖ := (f m').le_opNorm m
        _ ≤ (‖f‖ * ∏ i, ‖m' i‖) * ∏ i, ‖m i‖ := mul_le_mul_of_nonneg_right
          (f.le_opNorm m') (by positivity)
        _ = (‖f‖ * ∏ i, ‖m i‖) * ∏ i, ‖m' i‖ := by ring)

theorem flipMultilinear_apply (f : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ M)
    (ContinuousMultilinearMap 𝕜 (fun _ : ι' ↦ M') N)) (m : ι → M) (m' : ι' → M') :
    f.flipMultilinear m' m = f m m' :=
  rfl

end ContinuousMultilinearMap
end Flip
