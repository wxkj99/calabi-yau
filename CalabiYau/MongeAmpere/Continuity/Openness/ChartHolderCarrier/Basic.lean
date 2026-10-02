module

public import CalabiYau.Geometry.Manifold.Holder.ChartNorm
public import Mathlib.Geometry.Manifold.ContMDiffMap
public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.Analysis.Normed.Module.Completion

/-!
# Smooth core for the finite-chart Hölder completion

This file defines the concrete smooth-function core, its finite-chart gauge, and the completion
carrier. The normed-space structure is obtained from the finite-gauge, definiteness,
triangle, and scalar laws.
-/

@[expose] public section

noncomputable section

open scoped Manifold ContDiff NNReal ENNReal Topology

namespace KahlerForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The concrete smooth-function core for order `k` and exponent `α` on a fixed finite chart
cover. The completion of this core in its finite-chart gauge is the intended little-Hölder carrier.
-/
structure SmoothChartHolderCore (cover : CompactChartCover E M)
    (k : ℕ) (α : ℝ≥0) where
  smoothMap : ContMDiffMap (𝓘(ℝ, E)) (modelWithCornersSelf ℝ ℝ) M ℝ ∞

noncomputable def smoothChartHolderCoreEquivSmoothMap (cover : CompactChartCover E M)
    (k : ℕ) (α : ℝ≥0) :
    SmoothChartHolderCore cover k α ≃
      ContMDiffMap (𝓘(ℝ, E)) (modelWithCornersSelf ℝ ℝ) M ℝ ∞ where
  toFun f := f.smoothMap
  invFun f := ⟨f⟩
  left_inv f := by cases f; rfl
  right_inv _ := rfl

instance (cover : CompactChartCover E M) (k : ℕ) (α : ℝ≥0) :
    AddCommGroup (SmoothChartHolderCore cover k α) :=
  (smoothChartHolderCoreEquivSmoothMap cover k α).addCommGroup

instance (cover : CompactChartCover E M) (k : ℕ) (α : ℝ≥0) :
    Module ℝ (SmoothChartHolderCore cover k α) :=
  (smoothChartHolderCoreEquivSmoothMap cover k α).module ℝ

instance (cover : CompactChartCover E M) (k : ℕ) (α : ℝ≥0) :
    CoeFun (SmoothChartHolderCore cover k α) (fun _ ↦ M → ℝ) where
  coe f := f.smoothMap

/-- The gauge of a smooth core element, computed from its underlying function. -/
noncomputable def smoothChartHolderGauge (cover : CompactChartCover E M)
    (k : ℕ) (α : ℝ≥0) (f : SmoothChartHolderCore cover k α) : ℝ≥0∞ :=
  finiteChartHolderGauge cover k α f

/-- Point evaluation on the smooth core, before extension to its completion. -/
noncomputable def smoothChartHolderPointValue (cover : CompactChartCover E M)
    (k : ℕ) (α : ℝ≥0) (x : M) (f : SmoothChartHolderCore cover k α) : ℝ :=
  f.smoothMap x

/-- The coordinate `j`-jet of a smooth core element on each chart piece. This is the raw jet data
whose continuous extension to the little-Hölder completion is used in the openness argument. -/
noncomputable def smoothChartHolderJetData (cover : CompactChartCover E M)
    (k : ℕ) (α : ℝ≥0) (j : ℕ) (f : SmoothChartHolderCore cover k α) :
    ∀ i, cover.piece i → E [×j]→L[ℝ] ℝ := fun i z => iteratedFDeriv ℝ j
    (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z

/-- The norm on the fixed smooth core is defined from the finite-chart gauge. -/
noncomputable instance smoothChartHolderCoreNorm
    (cover : CompactChartCover E M) (k : ℕ) (α : ℝ≥0) :
    Norm (SmoothChartHolderCore cover k α) where
  norm f := (smoothChartHolderGauge cover k α f).toReal

/-- Normed data for the fixed smooth core. `NormedSpace.Core` is relative to the canonical
AddCommGroup and Module on `SmoothChartHolderCore`; the normed instances constructed from it reuse
these operations. The finite-gauge field rules out the `toReal ⊤ = 0` defect. -/
structure SmoothChartHolderNormedData (cover : CompactChartCover E M)
    (k : ℕ) (α : ℝ≥0) where
  finiteGauge : ∀ f : SmoothChartHolderCore cover k α,
    HasFiniteChartHolderGauge cover k α f.smoothMap
  normedCore : NormedSpace.Core ℝ (SmoothChartHolderCore cover k α)

/-- The canonical normed additive group structure on the smooth core, built over its already
transported pointwise AddCommGroup. -/
@[instance_reducible]
noncomputable def smoothChartHolderCoreNormedAddCommGroup
    (cover : CompactChartCover E M) (k : ℕ) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover k α) :
    NormedAddCommGroup (SmoothChartHolderCore cover k α) :=
  NormedAddCommGroup.ofCore N.normedCore

/-- The canonical real normed-space structure on the smooth core. -/
@[instance_reducible]
noncomputable def smoothChartHolderCoreNormedSpace
    (cover : CompactChartCover E M) (k : ℕ) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover k α) :
    letI : NormedAddCommGroup (SmoothChartHolderCore cover k α) :=
      smoothChartHolderCoreNormedAddCommGroup cover k α N
    NormedSpace ℝ (SmoothChartHolderCore cover k α) := by
  letI : NormedAddCommGroup (SmoothChartHolderCore cover k α) :=
    smoothChartHolderCoreNormedAddCommGroup cover k α N
  exact NormedSpace.ofCore N.normedCore

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The canonical norm on the smooth core is definitionally the finite-chart gauge. -/
theorem smoothChartHolderCore_norm_eq_gauge
    (cover : CompactChartCover E M) (k : ℕ) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover k α) (f : SmoothChartHolderCore cover k α) :
    letI : NormedAddCommGroup (SmoothChartHolderCore cover k α) :=
      smoothChartHolderCoreNormedAddCommGroup cover k α N
    letI : NormedSpace ℝ (SmoothChartHolderCore cover k α) :=
      smoothChartHolderCoreNormedSpace cover k α N
    ‖f‖ = (smoothChartHolderGauge cover k α f).toReal := rfl

/-- The little-Hölder carrier is the normed completion of the fixed smooth core equipped with
`N`'s gauge norm. -/
abbrev LittleHolder (cover : CompactChartCover E M) (k : ℕ) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover k α) :=
  letI : NormedAddCommGroup (SmoothChartHolderCore cover k α) :=
    smoothChartHolderCoreNormedAddCommGroup cover k α N
  letI : NormedSpace ℝ (SmoothChartHolderCore cover k α) :=
    smoothChartHolderCoreNormedSpace cover k α N
  UniformSpace.Completion (SmoothChartHolderCore cover k α)

/-- The completion extension of a map from the smooth core to a complete separated target.
Evaluation and bounded chart-jet maps use this construction after their concrete bounds are
proved. -/
noncomputable def littleHolderExtension
    (cover : CompactChartCover E M) (k : ℕ) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover k α)
    {Y : Type*} [UniformSpace Y] [CompleteSpace Y] [T0Space Y]
    (g : SmoothChartHolderCore cover k α → Y) :
    LittleHolder cover k α N → Y := by
  letI : NormedAddCommGroup (SmoothChartHolderCore cover k α) :=
    smoothChartHolderCoreNormedAddCommGroup cover k α N
  letI : NormedSpace ℝ (SmoothChartHolderCore cover k α) :=
    smoothChartHolderCoreNormedSpace cover k α N
  exact UniformSpace.Completion.extension g

end KahlerForm
