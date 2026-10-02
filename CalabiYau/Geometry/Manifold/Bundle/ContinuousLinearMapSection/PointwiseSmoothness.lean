-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Bundle/ContinuousLinearMapSection/PointwiseSmoothness.lean
-- Locally modified.
module
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Geometry.Manifold.Diffeomorph

@[expose] public section

-- The upstream module-system setting is documented in NOTICE.

noncomputable section

open Function
open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable {X : Type*} [TopologicalSpace X] [ChartedSpace HB X]
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [FiniteDimensional 𝕜 F₁]
variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
variable {n : WithTop ℕ∞}

lemma contMDiffAt_clm_of_pointwise
    {A : X → (F₁ →L[𝕜] F₂)} {x : X}
    (h : ∀ v, ContMDiffAt IB 𝓘(𝕜, F₂) n (fun q => A q v) x) :
    ContMDiffAt IB 𝓘(𝕜, F₁ →L[𝕜] F₂) n A x := by
  let d := Module.finrank 𝕜 F₁
  have hd : d = Module.finrank 𝕜 (Fin d → 𝕜) := (Module.finrank_fin_fun 𝕜).symm
  let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : F₂ ≃L[𝕜] F₂)).trans
    (ContinuousLinearEquiv.piRing (Fin d))
  rw [← id_comp A, ← e₂.symm_comp_self]
  exact e₂.symm.contDiff.contMDiff.contMDiffAt.comp _
    (contMDiffAt_pi_space.mpr fun _ => h _)

lemma contMDiffWithinAt_clm_of_pointwise
    {A : X → (F₁ →L[𝕜] F₂)} {s : Set X} {x : X}
    (h : ∀ v, ContMDiffWithinAt IB 𝓘(𝕜, F₂) n (fun q => A q v) s x) :
    ContMDiffWithinAt IB 𝓘(𝕜, F₁ →L[𝕜] F₂) n A s x := by
  let d := Module.finrank 𝕜 F₁
  have hd : d = Module.finrank 𝕜 (Fin d → 𝕜) := (Module.finrank_fin_fun 𝕜).symm
  let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : F₂ ≃L[𝕜] F₂)).trans
    (ContinuousLinearEquiv.piRing (Fin d))
  rw [← id_comp A, ← e₂.symm_comp_self]
  exact e₂.symm.contDiff.contMDiff.contMDiffAt.comp_contMDiffWithinAt _
    (contMDiffWithinAt_pi_space.mpr fun _ => h _)
