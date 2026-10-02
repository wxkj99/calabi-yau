module

public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderCarrier
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Algebra.LinearMapCompletion
public import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Continuous evaluation into the continuous-function space

The finite-chart Hölder gauge controls the global sup norm. This gives a continuous-linear map on
the concrete smooth core; Mathlib's linear-map completion API extends it to the little-Hölder
completion.
-/

@[expose] public section

noncomputable section

open scoped Manifold ContDiff NNReal ENNReal Topology

namespace KahlerForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable [CompactSpace M]

/-- The smooth core embeds linearly into the continuous functions on the compact manifold. -/
def smoothChartHolderContinuousMapLinearMap
    (cover : CompactChartCover E M) (k : ℕ) (α : ℝ≥0) :
    SmoothChartHolderCore cover k α →ₗ[ℝ] C(M, ℝ) where
  toFun f := ⟨f.smoothMap, f.smoothMap.contMDiff.continuous⟩
  map_add' f g := by
    apply ContinuousMap.ext
    intro x
    change (f + g).smoothMap x = f.smoothMap x + g.smoothMap x
    rfl
  map_smul' c f := by
    apply ContinuousMap.ext
    intro x
    change (c • f).smoothMap x = c • f.smoothMap x
    rfl

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in

/-- The global continuous-function map is bounded by the finite-chart gauge in its sup norm.
This is the concrete C⁰ estimate needed to extend evaluation to the little-Hölder completion. -/
theorem smoothChartHolderContinuousMapLinearMap_bound
    (cover : CompactChartCover E M) (k : ℕ) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover k α) (f : SmoothChartHolderCore cover k α) :
    ‖smoothChartHolderContinuousMapLinearMap cover k α f‖ ≤
      (smoothChartHolderGauge cover k α f).toReal := by
  classical
  apply (ContinuousMap.norm_le _ ENNReal.toReal_nonneg).2
  intro x
  rcases cover.interior_covers x with ⟨i, hx⟩
  rcases hx with ⟨z, hz, hzx⟩
  have hz' : z ∈ cover.piece i := interior_subset hz
  have hjet := CalabiYau.Schauder.spatialJet_le_eContDiffHolderGaugeOn k α
    (cover.piece i)
    (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm)
    (j := 0) (Nat.zero_le k) z hz'
  have hpiece :
      CalabiYau.Schauder.eContDiffHolderGaugeOn k α (cover.piece i)
        (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) ≤
        smoothChartHolderGauge cover k α f := by
    change CalabiYau.Schauder.eContDiffHolderGaugeOn k α (cover.piece i)
        (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) ≤
        ⨆ j, CalabiYau.Schauder.eContDiffHolderGaugeOn k α (cover.piece j)
          (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base j)).symm)
    exact le_iSup
      (fun j : cover.ι => CalabiYau.Schauder.eContDiffHolderGaugeOn k α
        (cover.piece j)
        (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base j)).symm)) i
  have hpoint : ENNReal.ofReal ‖f.smoothMap x‖ ≤ smoothChartHolderGauge cover k α f := by
    calc
      ENNReal.ofReal ‖f.smoothMap x‖ =
          ENNReal.ofReal ‖iteratedFDeriv ℝ 0
            (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z‖ := by
        rw [← hzx]
        simp only [norm_iteratedFDeriv_zero, Function.comp_apply]
      _ ≤ CalabiYau.Schauder.eContDiffHolderGaugeOn k α (cover.piece i)
          (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) := hjet
      _ ≤ smoothChartHolderGauge cover k α f := hpiece
  exact (ENNReal.ofReal_le_iff_le_toReal (N.finiteGauge f).ne_top).mp hpoint

/-- Promote the global C⁰ map to a continuous linear map using its finite-chart gauge bound. -/
noncomputable def smoothChartHolderContinuousMapCLM
    (cover : CompactChartCover E M) (k : ℕ) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover k α) :
    letI : NormedAddCommGroup (SmoothChartHolderCore cover k α) :=
      smoothChartHolderCoreNormedAddCommGroup cover k α N
    letI : NormedSpace ℝ (SmoothChartHolderCore cover k α) :=
      smoothChartHolderCoreNormedSpace cover k α N
    SmoothChartHolderCore cover k α →L[ℝ] C(M, ℝ) := by
  letI : NormedAddCommGroup (SmoothChartHolderCore cover k α) :=
    smoothChartHolderCoreNormedAddCommGroup cover k α N
  letI : NormedSpace ℝ (SmoothChartHolderCore cover k α) :=
    smoothChartHolderCoreNormedSpace cover k α N
  refine (smoothChartHolderContinuousMapLinearMap cover k α).mkContinuous 1 (fun f => ?_)
  calc
    ‖smoothChartHolderContinuousMapLinearMap cover k α f‖ ≤
        (smoothChartHolderGauge cover k α f).toReal :=
      smoothChartHolderContinuousMapLinearMap_bound cover k α N f
    _ = ‖f‖ := (smoothChartHolderCore_norm_eq_gauge cover k α N f).symm
    _ = 1 * ‖f‖ := by ring

/-- Extend global C⁰ evaluation to the little-Hölder completion. -/
noncomputable def smoothChartHolderContinuousMapExtension
    (cover : CompactChartCover E M) (k : ℕ) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover k α) :
    letI : NormedAddCommGroup (SmoothChartHolderCore cover k α) :=
      smoothChartHolderCoreNormedAddCommGroup cover k α N
    letI : NormedSpace ℝ (SmoothChartHolderCore cover k α) :=
      smoothChartHolderCoreNormedSpace cover k α N
    LittleHolder cover k α N →L[ℝ] C(M, ℝ) := by
  letI : NormedAddCommGroup (SmoothChartHolderCore cover k α) :=
    smoothChartHolderCoreNormedAddCommGroup cover k α N
  letI : NormedSpace ℝ (SmoothChartHolderCore cover k α) :=
    smoothChartHolderCoreNormedSpace cover k α N
  exact (smoothChartHolderContinuousMapCLM cover k α N).fromCompletion

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
@[simp]
theorem smoothChartHolderContinuousMapExtension_coe
    (cover : CompactChartCover E M) (k : ℕ) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover k α)
    (f : SmoothChartHolderCore cover k α) :
    letI : NormedAddCommGroup (SmoothChartHolderCore cover k α) :=
      smoothChartHolderCoreNormedAddCommGroup cover k α N
    letI : NormedSpace ℝ (SmoothChartHolderCore cover k α) :=
      smoothChartHolderCoreNormedSpace cover k α N
    smoothChartHolderContinuousMapExtension cover k α N f =
      smoothChartHolderContinuousMapLinearMap cover k α f := by
  let : NormedAddCommGroup (SmoothChartHolderCore cover k α) :=
    smoothChartHolderCoreNormedAddCommGroup cover k α N
  let : NormedSpace ℝ (SmoothChartHolderCore cover k α) :=
    smoothChartHolderCoreNormedSpace cover k α N
  simp only [smoothChartHolderContinuousMapExtension,
    ContinuousLinearMap.fromCompletion_apply_coe,
    smoothChartHolderContinuousMapCLM, LinearMap.mkContinuous_apply]

end KahlerForm
