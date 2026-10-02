module

public import CalabiYau.MongeAmpere.Continuity.Basic
public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderMeanZero
public import CalabiYau.Geometry.Complex.Holder

/-!
# Concrete mean-zero little Hölder carriers for openness

The C² and C⁰ carriers are mean-zero kernels inside the completions of the actual smooth finite-chart
cores. Their norm is the finite-chart gauge; evaluation is the continuous extension to `C(M, ℝ)`.
This module does not postulate arbitrary Banach carrier types or evaluation maps.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology
open MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- A `C²` potential whose perturbed form is positive.  The finite regularity is what the
implicit-function step supplies; the Schauder bootstrap later upgrades it to a smooth potential. -/
def IsC2Potential (ω₀ : KahlerForm n M) (φ : M → ℝ) : Prop :=
  ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 φ ∧
    (ω₀.toFormField + mddbar n φ).IsPositive

/-- A finite-regularity solution of the Monge–Ampère equation. -/
def SolvesMongeAmpereC2 (ω₀ : KahlerForm n M) (G φ : M → ℝ) : Prop :=
  ω₀.IsC2Potential φ ∧ ∀ x, ω₀.mongeAmpere φ x = Real.exp (G x)

/-- A family is bounded on a fixed finite compact chart cover in the `C^{k,α}` sense. -/
def HolderBoundedOnFiniteChartCover {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    (cover : CompactChartCover E M) (k : ℕ) (α : ℝ≥0) (S : Set (M → ℝ)) : Prop :=
  ∃ C : ℝ≥0, ∀ f ∈ S, ∀ i,
    HolderBoundOn k α C (cover.piece i)
      (f ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm)

/-- The concrete finite-chart data for the mean-zero little Hölder spaces at orders zero and two.
The underlying core spaces, completions, integral kernels, and evaluation maps are all fixed by the
gauge construction in the imported helper modules. -/
class ContinuityHolderPair (ω₁ : KahlerForm n M) (α : ℝ≥0) where
  finiteChartCover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M
  normedDataC2 : SmoothChartHolderNormedData finiteChartCover 2 α
  normedDataC0 : SmoothChartHolderNormedData finiteChartCover 0 α

namespace ContinuityHolderPair

variable {ω₁ : KahlerForm n M} {α : ℝ≥0}

/-- The C² potential carrier is the mean-zero kernel inside the concrete order-two completion. -/
noncomputable abbrev C2 (P : ContinuityHolderPair ω₁ α) :=
  MeanZeroLittleHolderC2 ω₁ P.finiteChartCover α P.normedDataC2

/-- The C⁰ target carrier is the mean-zero kernel inside the concrete order-zero completion. -/
noncomputable abbrev C0 (P : ContinuityHolderPair ω₁ α) :=
  MeanZeroLittleHolderC0 ω₁ P.finiteChartCover α P.normedDataC0

noncomputable instance normedAddCommGroupC2 (P : ContinuityHolderPair ω₁ α) :
    NormedAddCommGroup P.C2 := by
  letI : NormedAddCommGroup
      (SmoothChartHolderCore P.finiteChartCover 2 α) :=
    smoothChartHolderCoreNormedAddCommGroup P.finiteChartCover 2 α P.normedDataC2
  letI : NormedSpace ℝ (SmoothChartHolderCore P.finiteChartCover 2 α) :=
    smoothChartHolderCoreNormedSpace P.finiteChartCover 2 α P.normedDataC2
  infer_instance

noncomputable instance normedSpaceC2 (P : ContinuityHolderPair ω₁ α) :
    NormedSpace ℝ P.C2 := by
  letI : NormedAddCommGroup P.C2 := normedAddCommGroupC2 P
  letI : NormedAddCommGroup
      (SmoothChartHolderCore P.finiteChartCover 2 α) :=
    smoothChartHolderCoreNormedAddCommGroup P.finiteChartCover 2 α P.normedDataC2
  letI : NormedSpace ℝ (SmoothChartHolderCore P.finiteChartCover 2 α) :=
    smoothChartHolderCoreNormedSpace P.finiteChartCover 2 α P.normedDataC2
  infer_instance

noncomputable instance completeSpaceC2 (P : ContinuityHolderPair ω₁ α) :
    CompleteSpace P.C2 := by
  let : NormedAddCommGroup
      (SmoothChartHolderCore P.finiteChartCover 2 α) :=
    smoothChartHolderCoreNormedAddCommGroup P.finiteChartCover 2 α P.normedDataC2
  let : NormedSpace ℝ (SmoothChartHolderCore P.finiteChartCover 2 α) :=
    smoothChartHolderCoreNormedSpace P.finiteChartCover 2 α P.normedDataC2
  infer_instance

noncomputable instance normedAddCommGroupC0 (P : ContinuityHolderPair ω₁ α) :
    NormedAddCommGroup P.C0 := by
  letI : NormedAddCommGroup
      (SmoothChartHolderCore P.finiteChartCover 0 α) :=
    smoothChartHolderCoreNormedAddCommGroup P.finiteChartCover 0 α P.normedDataC0
  letI : NormedSpace ℝ (SmoothChartHolderCore P.finiteChartCover 0 α) :=
    smoothChartHolderCoreNormedSpace P.finiteChartCover 0 α P.normedDataC0
  infer_instance

noncomputable instance normedSpaceC0 (P : ContinuityHolderPair ω₁ α) :
    NormedSpace ℝ P.C0 := by
  letI : NormedAddCommGroup P.C0 := normedAddCommGroupC0 P
  letI : NormedAddCommGroup
      (SmoothChartHolderCore P.finiteChartCover 0 α) :=
    smoothChartHolderCoreNormedAddCommGroup P.finiteChartCover 0 α P.normedDataC0
  letI : NormedSpace ℝ (SmoothChartHolderCore P.finiteChartCover 0 α) :=
    smoothChartHolderCoreNormedSpace P.finiteChartCover 0 α P.normedDataC0
  infer_instance

noncomputable instance completeSpaceC0 (P : ContinuityHolderPair ω₁ α) :
    CompleteSpace P.C0 := by
  let : NormedAddCommGroup
      (SmoothChartHolderCore P.finiteChartCover 0 α) :=
    smoothChartHolderCoreNormedAddCommGroup P.finiteChartCover 0 α P.normedDataC0
  let : NormedSpace ℝ (SmoothChartHolderCore P.finiteChartCover 0 α) :=
    smoothChartHolderCoreNormedSpace P.finiteChartCover 0 α P.normedDataC0
  infer_instance

/-- Evaluation of a mean-zero C² carrier element as a function on M. -/
noncomputable def evalC2 (P : ContinuityHolderPair ω₁ α) : P.C2 →ₗ[ℝ] (M → ℝ) where
  toFun u x :=
    littleHolderMeanZeroEvaluationCLM ω₁ P.finiteChartCover 2 α P.normedDataC2 u x
  map_add' u v := by
    funext x
    simp
  map_smul' c u := by
    funext x
    simp

/-- Evaluation of a mean-zero C⁰ carrier element as a function on M. -/
noncomputable def evalC0 (P : ContinuityHolderPair ω₁ α) : P.C0 →ₗ[ℝ] (M → ℝ) where
  toFun u x :=
    littleHolderMeanZeroEvaluationCLM ω₁ P.finiteChartCover 0 α P.normedDataC0 u x
  map_add' u v := by
    funext x
    simp
  map_smul' c u := by
    funext x
    simp

end ContinuityHolderPair

end KahlerForm
