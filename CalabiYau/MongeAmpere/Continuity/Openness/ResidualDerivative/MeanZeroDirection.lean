module

public import CalabiYau.MongeAmpere.Continuity.Openness.ResidualNormalization

/-!
# The centered parameter direction in the mean-zero target

The derivative in the path parameter is the mean-zero function `avg_{ω₁} F - F`. The positive
volume permits the scalar mean correction, and smooth-core realization places the corrected
function in the little-Hölder target.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology
open MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]

omit [ConnectedSpace M] in
/-- The centered derivative in the scalar path parameter is represented by an element of the
mean-zero little-Hölder target. -/
theorem exists_centeredResidual_meanZeroDirection (ω₁ : KahlerForm n M) (F : M → ℝ)
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F)
    (α : ℝ≥0) [P : ContinuityHolderPair ω₁ α]
    (hvol : 0 < ω₁.volume.real Set.univ) :
    ∃ b : P.C0, ∀ x,
      P.evalC0 b x =
        (∫ y, F y ∂ω₁.volume) / ω₁.volume.real Set.univ - F x := by
  let cover := P.finiteChartCover
  let N := P.normedDataC0
  let : NormedAddCommGroup (SmoothChartHolderCore cover 0 α) :=
    smoothChartHolderCoreNormedAddCommGroup cover 0 α N
  let : NormedSpace ℝ (SmoothChartHolderCore cover 0 α) :=
    smoothChartHolderCoreNormedSpace cover 0 α N
  let V : ℝ := ω₁.volume.real Set.univ
  let c : ℝ := (∫ y, F y ∂ω₁.volume) / V
  let fMap : ContMDiffMap (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
      (modelWithCornersSelf ℝ ℝ) M ℝ ∞ := ⟨F, hF⟩
  let core : SmoothChartHolderCore cover 0 α :=
    ⟨ContMDiffMap.const (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
      (I' := modelWithCornersSelf ℝ ℝ) (M := M) (M' := ℝ) (n := ∞) c - fMap⟩
  have hFint : Integrable F ω₁.volume :=
    hF.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)
  have hmean : ∫ x, (c - F x) ∂ω₁.volume = 0 := by
    rw [integral_sub (integrable_const c) hFint]
    simp only [integral_const]
    dsimp [c, V]
    field_simp [ne_of_gt hvol]
    ring
  have hcoreMean :
      littleHolderMeanFunctional ω₁ cover 0 α N (core : LittleHolder cover 0 α N) = 0 := by
    simp [littleHolderMeanFunctional, continuousVolumeIntegralCLM,
      boundedContinuousVolumeIntegralCLM, boundedContinuousVolumeIntegralLinearMap,
      smoothChartHolderContinuousMapExtension_coe,
      smoothChartHolderContinuousMapLinearMap, core, fMap]
    change (∫ x, (c - F x) ∂ω₁.volume) = 0
    exact hmean
  let b : P.C0 := ⟨(core : LittleHolder cover 0 α N), hcoreMean⟩
  refine ⟨b, ?_⟩
  intro x
  simp [b, ContinuityHolderPair.evalC0, littleHolderMeanZeroEvaluationCLM,
    smoothChartHolderContinuousMapExtension_coe,
    smoothChartHolderContinuousMapLinearMap, core, fMap]
  change c - F x = (∫ y, F y ∂ω₁.volume) / ω₁.volume.real Set.univ - F x
  dsimp [c, V]

end KahlerForm
