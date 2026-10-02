module

public import CalabiYau.MongeAmpere.Continuity.Openness.LaplacianInverse.ForwardBound

/-!
# Extend the smooth-core forward map

Use the bounded forward operator on the smooth mean-zero cores and the density of those cores to
extend it to a continuous linear map from `P.C2` to `P.C0`. Its action on the
smooth-core range supplies the limit compatibility needed for the completed Laplacian formula.

The order-zero target of the core operator is an actual smooth mean-zero core element. This
prevents the gauge estimate alone from being mistaken for a map into the normed smooth core.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology
open Set MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- `A` agrees with the smooth-core forward Laplacian on every mean-zero smooth order-two input,
where the input and output are represented by their actual evaluations in `P.C2` and `P.C0`. -/
def IsSmoothMeanZeroForwardExtension {ω₁ : KahlerForm n M} {α : ℝ≥0}
    (P : ContinuityHolderPair ω₁ α) (A : P.C2 →L[ℝ] P.C0) : Prop :=
  ∀ f : smoothMeanZeroChartHolderCore ω₁ P.finiteChartCover 2 α P.normedDataC2,
    ∃ u : P.C2,
      P.evalC2 u = (f : SmoothChartHolderCore P.finiteChartCover 2 α).smoothMap ∧
      ∃ g : smoothMeanZeroChartHolderCore ω₁ P.finiteChartCover 0 α P.normedDataC0,
        (g : SmoothChartHolderCore P.finiteChartCover 0 α).smoothMap =
          ω₁.laplacian (f : SmoothChartHolderCore P.finiteChartCover 2 α).smoothMap ∧
        P.evalC0 (A u) = (g : SmoothChartHolderCore P.finiteChartCover 0 α).smoothMap

omit [ConnectedSpace M] in
/-- The bounded forward core map extends continuously to the mean-zero completions and agrees
with the pointwise Laplacian on the dense smooth mean-zero order-two core. -/
theorem exists_smoothCore_laplacian_extension [Nonempty M]
    (ω₁ : KahlerForm n M) (α : ℝ≥0) [P : ContinuityHolderPair ω₁ α]
    (hForward : HasBoundedForwardLaplacian ω₁ P.finiteChartCover α) :
    ∃ A : P.C2 →L[ℝ] P.C0, IsSmoothMeanZeroForwardExtension P A := by
  classical
  let cover := P.finiteChartCover
  let N₂ := P.normedDataC2
  let N₀ := P.normedDataC0
  let : NormedAddCommGroup (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedAddCommGroup cover 2 α N₂
  let : NormedSpace ℝ (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedSpace cover 2 α N₂
  let : NormedAddCommGroup (SmoothChartHolderCore cover 0 α) :=
    smoothChartHolderCoreNormedAddCommGroup cover 0 α N₀
  let : NormedSpace ℝ (SmoothChartHolderCore cover 0 α) :=
    smoothChartHolderCoreNormedSpace cover 0 α N₀
  rcases hForward with ⟨C, hC⟩
  have hTcore₀ (g : SmoothChartHolderCore cover 0 α) :
      littleHolderMeanFunctional ω₁ cover 0 α N₀
          (g : LittleHolder cover 0 α N₀) =
        (continuousVolumeIntegralCLM ω₁)
          (smoothChartHolderContinuousMapLinearMap cover 0 α g) := by
    simp [littleHolderMeanFunctional, smoothChartHolderContinuousMapExtension_coe,
      smoothChartHolderContinuousMapLinearMap]
  have hTcore₂ (f : SmoothChartHolderCore cover 2 α) :
      littleHolderMeanFunctional ω₁ cover 2 α N₂
          (f : LittleHolder cover 2 α N₂) =
        (continuousVolumeIntegralCLM ω₁)
          (smoothChartHolderContinuousMapLinearMap cover 2 α f) := by
    simp [littleHolderMeanFunctional, smoothChartHolderContinuousMapExtension_coe,
      smoothChartHolderContinuousMapLinearMap]
  let pick (f : SmoothChartHolderCore cover 2 α) : SmoothChartHolderCore cover 0 α :=
    Classical.choose (hC f).2
  have pick_spec (f : SmoothChartHolderCore cover 2 α) :
      (pick f).smoothMap = ω₁.laplacian f.smoothMap ∧
      (∫ x, (pick f).smoothMap x ∂ω₁.volume = 0) ∧
      finiteChartHolderGauge cover 0 α (pick f).smoothMap < ⊤ ∧
      (finiteChartHolderGauge cover 0 α (pick f).smoothMap).toReal ≤
        (C : ℝ) * (finiteChartHolderGauge cover 2 α f.smoothMap).toReal :=
    Classical.choose_spec (hC f).2
  let out (f : SmoothChartHolderCore cover 2 α) : P.C0 :=
    ⟨(pick f : LittleHolder cover 0 α N₀), by
      change littleHolderMeanFunctional ω₁ cover 0 α N₀
        (pick f : LittleHolder cover 0 α N₀) = 0
      rw [hTcore₀]
      change ∫ x, (pick f).smoothMap x ∂ω₁.volume = 0
      exact (pick_spec f).2.1⟩
  have hEvalC0 : Function.Injective P.evalC0 := by
    have hEval := littleHolderMeanZeroEvaluationC0CLM_injective
      ω₁ cover α N₀
    intro u v huv
    apply hEval
    ext x
    exact congrFun huv x
  have hpoint (f : SmoothChartHolderCore cover 2 α) :
      P.evalC0 (out f) = ω₁.laplacian f.smoothMap := by
    funext x
    simp [ContinuityHolderPair.evalC0, out,
      littleHolderMeanZeroEvaluationCLM,
      smoothChartHolderContinuousMapExtension_coe,
      smoothChartHolderContinuousMapLinearMap, pick_spec f]
  have hAdd (f g : SmoothChartHolderCore cover 2 α) :
      out (f + g) = out f + out g := by
    apply hEvalC0
    rw [map_add, hpoint (f + g), hpoint f, hpoint g]
    exact ω₁.laplacian_add f.smoothMap.contMDiff g.smoothMap.contMDiff
  have hSmul (r : ℝ) (f : SmoothChartHolderCore cover 2 α) :
      out (r • f) = r • out f := by
    apply hEvalC0
    rw [map_smul, hpoint (r • f), hpoint f]
    exact ω₁.laplacian_smul f.smoothMap.contMDiff r
  let L : SmoothChartHolderCore cover 2 α →ₗ[ℝ] P.C0 :=
    { toFun := out
      map_add' := hAdd
      map_smul' := hSmul }
  have hBound (f : SmoothChartHolderCore cover 2 α) :
      ‖L f‖ ≤ (C : ℝ) * ‖f‖ := by
    dsimp [L, out]
    change ‖(pick f : LittleHolder cover 0 α N₀)‖ ≤
      (C : ℝ) * ‖f‖
    rw [UniformSpace.Completion.norm_coe,
      smoothChartHolderCore_norm_eq_gauge cover 0 α N₀ (pick f),
      smoothChartHolderCore_norm_eq_gauge cover 2 α N₂ f]
    exact (pick_spec f).2.2.2
  let Lc : SmoothChartHolderCore cover 2 α →L[ℝ] P.C0 := L.mkContinuous C hBound
  let B : LittleHolder cover 2 α N₂ →L[ℝ] P.C0 := Lc.fromCompletion
  let A : P.C2 →L[ℝ] P.C0 := B.comp (P.C2).subtypeL
  have hfmean (f : smoothMeanZeroChartHolderCore ω₁ cover 2 α N₂) :
      ∫ x, (f : SmoothChartHolderCore cover 2 α).smoothMap x ∂ω₁.volume = 0 := by
    have hf : (continuousVolumeIntegralCLM ω₁)
        (smoothChartHolderContinuousMapLinearMap cover 2 α
          (f : SmoothChartHolderCore cover 2 α)) = 0 := by
      change ((continuousVolumeIntegralCLM ω₁).comp
        (smoothChartHolderContinuousMapCLM cover 2 α N₂)).toLinearMap
          (f : SmoothChartHolderCore cover 2 α) = 0
      exact f.property
    simpa [continuousVolumeIntegralCLM, boundedContinuousVolumeIntegralCLM,
      boundedContinuousVolumeIntegralLinearMap,
      smoothChartHolderContinuousMapLinearMap] using hf
  let embed (f : smoothMeanZeroChartHolderCore ω₁ cover 2 α N₂) : P.C2 :=
    ⟨((f : SmoothChartHolderCore cover 2 α) : LittleHolder cover 2 α N₂), by
      change littleHolderMeanFunctional ω₁ cover 2 α N₂
        ((f : SmoothChartHolderCore cover 2 α) : LittleHolder cover 2 α N₂) = 0
      rw [hTcore₂]
      simpa [continuousVolumeIntegralCLM, boundedContinuousVolumeIntegralCLM,
        boundedContinuousVolumeIntegralLinearMap,
        smoothChartHolderContinuousMapLinearMap] using hfmean f⟩
  refine ⟨A, ?_⟩
  intro f
  refine ⟨embed f, ?_, ?_⟩
  · funext x
    simp [embed, ContinuityHolderPair.evalC2, littleHolderMeanZeroEvaluationCLM,
      smoothChartHolderContinuousMapExtension_coe]
    rfl
  · let g : smoothMeanZeroChartHolderCore ω₁ cover 0 α N₀ :=
      ⟨pick (f : SmoothChartHolderCore cover 2 α), (pick_spec _).2.1⟩
    refine ⟨g, (pick_spec _).1, ?_⟩
    have hAu : A (embed f) = out (f : SmoothChartHolderCore cover 2 α) := by
      apply Subtype.ext
      change B ((f : SmoothChartHolderCore cover 2 α) : LittleHolder cover 2 α N₂) =
        ((pick (f : SmoothChartHolderCore cover 2 α) : SmoothChartHolderCore cover 0 α) :
          LittleHolder cover 0 α N₀)
      simp [B, Lc, L, out]
    rw [hAu]
    funext x
    simp [ContinuityHolderPair.evalC0, out, g,
      littleHolderMeanZeroEvaluationCLM,
      smoothChartHolderContinuousMapExtension_coe]
    rfl

end KahlerForm
