-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Tensor/Multilinear/Composition.lean
-- Locally modified.
/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Coauthors: Jack McCarthy
-/
module
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional

@[expose] public section

noncomputable section Comp

namespace ContinuousLinearMap

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {M' : Type*} [NormedAddCommGroup M'] [NormedSpace 𝕜 M']
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {ι : Type*} [Finite ι]

end ContinuousLinearMap

section Continuous

variable
  (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  (ι : Type*) [Finite ι]
  (F₁ F₂ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [ContinuousAdd F₁]

end Continuous

section Smooth
variable {𝕜 ι F₁ F₂} [NontriviallyNormedField 𝕜] [Fintype ι]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]

theorem ContinuousMultilinearMap.compContinuousLinearMapL_diag_contDiff :
  ContDiff 𝕜 ⊤ (fun p : F₁ →L[𝕜] F₁ ↦
  (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : ι ↦ p) :
    ContinuousMultilinearMap 𝕜 (fun _ ↦ F₁) F₂ →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ ↦ F₁) F₂))
  := by
  let φ : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁ →L[𝕜] F₁) _ :=
    ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
    𝕜 (fun _ : ι ↦ F₁) (fun _ : ι ↦ F₁) F₂
  change ContDiff 𝕜 ⊤ (fun p : F₁ →L[𝕜] F₁ ↦ φ (fun _ : ι ↦ p))
  rw [show (fun p : F₁ →L[𝕜] F₁ => φ (fun _ : ι => p)) =
    (φ : (ι → (F₁ →L[𝕜] F₁)) → _) ∘ (fun p : F₁ →L[𝕜] F₁ => (fun _ : ι => p)) from rfl]
  exact (ContinuousMultilinearMap.contDiff φ).comp
    (contDiff_pi.2 (fun _ => contDiff_id))

theorem ContinuousMultilinearMap.compContinuousLinearMapL_diag_contDiff_of_space
    {F₁' : Type*} [NormedAddCommGroup F₁'] [NormedSpace 𝕜 F₁'] :
    ContDiff 𝕜 ⊤ (fun p : F₁ →L[𝕜] F₁' ↦
      (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : ι ↦ p) :
        ContinuousMultilinearMap 𝕜 (fun _ ↦ F₁') F₂ →L[𝕜]
        ContinuousMultilinearMap 𝕜 (fun _ ↦ F₁) F₂)) := by
  let φ : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁ →L[𝕜] F₁') _ :=
    ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
    𝕜 (fun _ : ι ↦ F₁) (fun _ : ι ↦ F₁') F₂
  change ContDiff 𝕜 ⊤ (fun p : F₁ →L[𝕜] F₁' ↦ φ (fun _ : ι ↦ p))
  rw [show (fun p : F₁ →L[𝕜] F₁' => φ (fun _ : ι => p)) =
    (φ : (ι → (F₁ →L[𝕜] F₁')) → _) ∘ (fun p : F₁ →L[𝕜] F₁' => (fun _ : ι => p)) from rfl]
  exact (ContinuousMultilinearMap.contDiff φ).comp
    (contDiff_pi.2 (fun _ => contDiff_id))

end Smooth

end Comp
