module

public import CalabiYau.Geometry.Kahler.Volume
public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderEvaluation
public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderMeanZero.C0FaithfulEvaluation
public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderMeanZero.C2FaithfulEvaluation
public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderJets
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-!
# Mean-zero little-Hölder carriers

For a background Kähler volume, the mean-zero carrier is the kernel of the bounded integral
functional on the concrete little-Hölder completion. This makes it a closed subspace by
construction; no arbitrary mean-zero carrier or evaluation field is assumed.
-/

@[expose] public section

noncomputable section

open scoped Manifold ContDiff NNReal Topology
open MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ M]

/-- Integrate a bounded continuous real function against the background Kähler volume. -/
def boundedContinuousVolumeIntegralLinearMap (ω₁ : KahlerForm n M) :
    BoundedContinuousFunction M ℝ →ₗ[ℝ] ℝ where
  toFun f := ∫ x, f x ∂ω₁.volume
  map_add' f g := by
    exact integral_add (f.integrable ω₁.volume) (g.integrable ω₁.volume)
  map_smul' c f := by
    exact integral_smul c f

/-- The integral on bounded continuous functions is continuous, with operator norm bounded by
the total volume. -/
noncomputable def boundedContinuousVolumeIntegralCLM (ω₁ : KahlerForm n M) :
    BoundedContinuousFunction M ℝ →L[ℝ] ℝ :=
  boundedContinuousVolumeIntegralLinearMap ω₁ |>.mkContinuous
    (ω₁.volume.real Set.univ)
    (fun f ↦ BoundedContinuousFunction.norm_integral_le_mul_norm ω₁.volume f)

/-- The background volume integral as a continuous linear functional on continuous functions. -/
noncomputable def continuousVolumeIntegralCLM (ω₁ : KahlerForm n M) : C(M, ℝ) →L[ℝ] ℝ :=
  (boundedContinuousVolumeIntegralCLM ω₁).comp
    ((ContinuousMap.linearIsometryBoundedOfCompact (α := M) (𝕜 := ℝ) (E := ℝ))
      |>.toContinuousLinearEquiv.toContinuousLinearMap)

/-- The bounded mean functional on the little-Hölder completion. -/
noncomputable def littleHolderMeanFunctional
    (ω₁ : KahlerForm n M)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (k : ℕ) (α : ℝ≥0) (N : SmoothChartHolderNormedData cover k α) :
    letI : NormedAddCommGroup (SmoothChartHolderCore cover k α) :=
      smoothChartHolderCoreNormedAddCommGroup cover k α N
    letI : NormedSpace ℝ (SmoothChartHolderCore cover k α) :=
      smoothChartHolderCoreNormedSpace cover k α N
    LittleHolder cover k α N →L[ℝ] ℝ := by
  letI : NormedAddCommGroup (SmoothChartHolderCore cover k α) :=
    smoothChartHolderCoreNormedAddCommGroup cover k α N
  letI : NormedSpace ℝ (SmoothChartHolderCore cover k α) :=
    smoothChartHolderCoreNormedSpace cover k α N
  exact (continuousVolumeIntegralCLM ω₁).comp
    (smoothChartHolderContinuousMapExtension cover k α N)

/-- The mean-zero little-Hölder carrier is exactly the kernel of integration on the completion. -/
noncomputable def littleHolderMeanZeroSubmodule
    (ω₁ : KahlerForm n M)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (k : ℕ) (α : ℝ≥0) (N : SmoothChartHolderNormedData cover k α) :
    letI : NormedAddCommGroup (SmoothChartHolderCore cover k α) :=
      smoothChartHolderCoreNormedAddCommGroup cover k α N
    letI : NormedSpace ℝ (SmoothChartHolderCore cover k α) :=
      smoothChartHolderCoreNormedSpace cover k α N
    Submodule ℝ (LittleHolder cover k α N) :=
  by
    letI : NormedAddCommGroup (SmoothChartHolderCore cover k α) :=
      smoothChartHolderCoreNormedAddCommGroup cover k α N
    letI : NormedSpace ℝ (SmoothChartHolderCore cover k α) :=
      smoothChartHolderCoreNormedSpace cover k α N
    exact (littleHolderMeanFunctional ω₁ cover k α N).ker

/-- Smooth mean-zero functions form the kernel of the integral restricted to the smooth core. -/
noncomputable def smoothMeanZeroChartHolderCore
    (ω₁ : KahlerForm n M)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (k : ℕ) (α : ℝ≥0) (N : SmoothChartHolderNormedData cover k α) :
    letI : NormedAddCommGroup (SmoothChartHolderCore cover k α) :=
      smoothChartHolderCoreNormedAddCommGroup cover k α N
    letI : NormedSpace ℝ (SmoothChartHolderCore cover k α) :=
      smoothChartHolderCoreNormedSpace cover k α N
    Submodule ℝ (SmoothChartHolderCore cover k α) := by
  letI : NormedAddCommGroup (SmoothChartHolderCore cover k α) :=
    smoothChartHolderCoreNormedAddCommGroup cover k α N
  letI : NormedSpace ℝ (SmoothChartHolderCore cover k α) :=
    smoothChartHolderCoreNormedSpace cover k α N
  exact ((continuousVolumeIntegralCLM ω₁).comp
    (smoothChartHolderContinuousMapCLM cover k α N)).toLinearMap.ker

/-- The concrete mean-zero little-Hölder carrier. -/
abbrev LittleHolderMeanZero
    (ω₁ : KahlerForm n M)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (k : ℕ) (α : ℝ≥0) (N : SmoothChartHolderNormedData cover k α) :=
  littleHolderMeanZeroSubmodule ω₁ cover k α N

/-- The order-zero mean-zero carrier used for the C⁰ normed space in the openness pair. -/
abbrev MeanZeroLittleHolderC0
    (ω₁ : KahlerForm n M)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (α : ℝ≥0) (N : SmoothChartHolderNormedData cover 0 α) :=
  LittleHolderMeanZero ω₁ cover 0 α N

/-- The order-two mean-zero carrier used for the potential space in the openness pair. -/
abbrev MeanZeroLittleHolderC2
    (ω₁ : KahlerForm n M)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (α : ℝ≥0) (N : SmoothChartHolderNormedData cover 2 α) :=
  LittleHolderMeanZero ω₁ cover 2 α N

omit [IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ M] in
/-- The mean-zero carrier is closed in the little-Hölder completion. -/
theorem littleHolderMeanZeroSubmodule_isClosed
    (ω₁ : KahlerForm n M)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (k : ℕ) (α : ℝ≥0) (N : SmoothChartHolderNormedData cover k α) :
    letI : NormedAddCommGroup (SmoothChartHolderCore cover k α) :=
      smoothChartHolderCoreNormedAddCommGroup cover k α N
    letI : NormedSpace ℝ (SmoothChartHolderCore cover k α) :=
      smoothChartHolderCoreNormedSpace cover k α N
    IsClosed (littleHolderMeanZeroSubmodule ω₁ cover k α N : Set (LittleHolder cover k α N)) := by
  let : NormedAddCommGroup (SmoothChartHolderCore cover k α) :=
    smoothChartHolderCoreNormedAddCommGroup cover k α N
  let : NormedSpace ℝ (SmoothChartHolderCore cover k α) :=
    smoothChartHolderCoreNormedSpace cover k α N
  exact (littleHolderMeanFunctional ω₁ cover k α N).isClosed_ker

/-- The mean-zero little-Hölder carrier is complete, as the closed kernel of the mean functional. -/
noncomputable instance littleHolderMeanZeroCompleteSpace
    (ω₁ : KahlerForm n M)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (k : ℕ) (α : ℝ≥0) (N : SmoothChartHolderNormedData cover k α) :
    letI : NormedAddCommGroup (SmoothChartHolderCore cover k α) :=
      smoothChartHolderCoreNormedAddCommGroup cover k α N
    letI : NormedSpace ℝ (SmoothChartHolderCore cover k α) :=
      smoothChartHolderCoreNormedSpace cover k α N
    CompleteSpace (LittleHolderMeanZero ω₁ cover k α N) := by
  let : NormedAddCommGroup (SmoothChartHolderCore cover k α) :=
    smoothChartHolderCoreNormedAddCommGroup cover k α N
  let : NormedSpace ℝ (SmoothChartHolderCore cover k α) :=
    smoothChartHolderCoreNormedSpace cover k α N
  let : IsClosed (littleHolderMeanZeroSubmodule ω₁ cover k α N :
      Set (LittleHolder cover k α N)) :=
    littleHolderMeanZeroSubmodule_isClosed ω₁ cover k α N
  infer_instance

/-- Restrict the completed C⁰ evaluation map to the closed mean-zero carrier. -/
noncomputable def littleHolderMeanZeroEvaluationCLM
    (ω₁ : KahlerForm n M)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (k : ℕ) (α : ℝ≥0) (N : SmoothChartHolderNormedData cover k α) :
    letI : NormedAddCommGroup (SmoothChartHolderCore cover k α) :=
      smoothChartHolderCoreNormedAddCommGroup cover k α N
    letI : NormedSpace ℝ (SmoothChartHolderCore cover k α) :=
      smoothChartHolderCoreNormedSpace cover k α N
    LittleHolderMeanZero ω₁ cover k α N →L[ℝ] C(M, ℝ) := by
  letI : NormedAddCommGroup (SmoothChartHolderCore cover k α) :=
    smoothChartHolderCoreNormedAddCommGroup cover k α N
  letI : NormedSpace ℝ (SmoothChartHolderCore cover k α) :=
    smoothChartHolderCoreNormedSpace cover k α N
  exact (smoothChartHolderContinuousMapExtension cover k α N).comp
    (littleHolderMeanZeroSubmodule ω₁ cover k α N).subtypeL

omit [IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ M] in
/-- Restriction of completed C⁰ evaluation to the mean-zero carrier remains faithful. -/
theorem littleHolderMeanZeroEvaluationC0CLM_injective
    (ω₁ : KahlerForm n M)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (α : ℝ≥0) (N : SmoothChartHolderNormedData cover 0 α) :
    Function.Injective (littleHolderMeanZeroEvaluationCLM ω₁ cover 0 α N) := by
  intro x y hxy
  apply Subtype.ext
  exact smoothChartHolderContinuousMapExtension_C0_injective cover α N hxy

/-- Restriction of completed C² evaluation to the mean-zero carrier remains faithful. -/
theorem littleHolderMeanZeroEvaluationC2CLM_injective
    (ω₁ : KahlerForm n M)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (α : ℝ≥0) (N : SmoothChartHolderNormedData cover 2 α) :
    Function.Injective (littleHolderMeanZeroEvaluationCLM ω₁ cover 2 α N) := by
  intro x y hxy
  apply Subtype.ext
  exact smoothChartHolderContinuousMapExtension_C2_injective cover α N hxy

omit [IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ M] in
/-- Smooth mean-zero core functions are dense in the mean-zero completion. The positive total
volume hypothesis makes the standard correction `f ↦ f - (∫ f / vol(M))·1` well-defined. -/
theorem closure_smoothMeanZeroChartHolderCore_coe
    (ω₁ : KahlerForm n M)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (k : ℕ) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover k α)
    (hvol : 0 < ω₁.volume.real Set.univ) :
    letI : NormedAddCommGroup (SmoothChartHolderCore cover k α) :=
      smoothChartHolderCoreNormedAddCommGroup cover k α N
    letI : NormedSpace ℝ (SmoothChartHolderCore cover k α) :=
      smoothChartHolderCoreNormedSpace cover k α N
    closure (Set.range fun f : smoothMeanZeroChartHolderCore ω₁ cover k α N =>
      ((f : SmoothChartHolderCore cover k α) : LittleHolder cover k α N)) =
        (LittleHolderMeanZero ω₁ cover k α N : Set (LittleHolder cover k α N)) := by
  let : NormedAddCommGroup (SmoothChartHolderCore cover k α) :=
    smoothChartHolderCoreNormedAddCommGroup cover k α N
  let : NormedSpace ℝ (SmoothChartHolderCore cover k α) :=
    smoothChartHolderCoreNormedSpace cover k α N
  classical
  let T := littleHolderMeanFunctional ω₁ cover k α N
  let oneCore : SmoothChartHolderCore cover k α :=
    ⟨ContMDiffMap.const (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
      (I' := modelWithCornersSelf ℝ ℝ) (M := M) (M' := ℝ) (n := ∞) 1⟩
  let oneComp : LittleHolder cover k α N := oneCore
  let V : ℝ := ω₁.volume.real Set.univ
  have hTone : T oneComp = V := by
    simp [T, oneComp, oneCore, littleHolderMeanFunctional,
      continuousVolumeIntegralCLM, boundedContinuousVolumeIntegralCLM,
      boundedContinuousVolumeIntegralLinearMap,
      smoothChartHolderContinuousMapExtension_coe,
      smoothChartHolderContinuousMapLinearMap]
    change (∫ _ : M, (1 : ℝ) ∂ω₁.volume) = V
    rw [integral_const, smul_eq_mul, mul_one]
  have hTcore (f : SmoothChartHolderCore cover k α) :
      T (f : LittleHolder cover k α N) =
        ((continuousVolumeIntegralCLM ω₁) (smoothChartHolderContinuousMapLinearMap
          cover k α f)) := by
    simp [T, littleHolderMeanFunctional, smoothChartHolderContinuousMapExtension_coe,
      smoothChartHolderContinuousMapLinearMap]
  let A : SmoothChartHolderCore cover k α →ₗ[ℝ] ℝ :=
    (continuousVolumeIntegralCLM ω₁).toLinearMap.comp
      (smoothChartHolderContinuousMapLinearMap cover k α)
  let P : LittleHolder cover k α N →L[ℝ] LittleHolder cover k α N :=
    ContinuousLinearMap.id ℝ _ - (V⁻¹) • T.smulRight oneComp
  have hPker (x : LittleHolder cover k α N)
      (hx : T x = 0) : P x = x := by
    simp [P, hx]
  have hPcore (f : SmoothChartHolderCore cover k α) :
      P (f : LittleHolder cover k α N) ∈
        Set.range (fun g : smoothMeanZeroChartHolderCore ω₁ cover k α N =>
          ((g : SmoothChartHolderCore cover k α) : LittleHolder cover k α N)) := by
    let g : SmoothChartHolderCore cover k α := f - (V⁻¹ * T (f : LittleHolder cover k α N)) • oneCore
    have hAf : A f = T (f : LittleHolder cover k α N) := (hTcore f).symm
    have hAone : A oneCore = V := by
      calc
        A oneCore = T (oneCore : LittleHolder cover k α N) := (hTcore oneCore).symm
        _ = V := hTone
    have hgmean : A g = 0 := by
      rw [map_sub, map_smul, hAf, hAone]
      simp
      field_simp [V, ne_of_gt hvol]
      ring
    have hg : g ∈ smoothMeanZeroChartHolderCore ω₁ cover k α N := by
      change A g = 0
      exact hgmean
    refine ⟨⟨g, hg⟩, ?_⟩
    change (g : LittleHolder cover k α N) = P (f : LittleHolder cover k α N)
    let e : SmoothChartHolderCore cover k α →L[ℝ] LittleHolder cover k α N :=
      UniformSpace.Completion.toComplL
    change e (f - (V⁻¹ * T (f : LittleHolder cover k α N)) • oneCore) =
      (f : LittleHolder cover k α N) -
        V⁻¹ • (T (f : LittleHolder cover k α N) • oneComp)
    rw [e.map_sub, e.map_smul, smul_smul]
    simp [e, oneComp]
  have hdense : Dense (Set.range fun f : SmoothChartHolderCore cover k α =>
      (f : LittleHolder cover k α N)) := by
    exact UniformSpace.Completion.denseRange_coe
  have hPimage : Set.range (P : LittleHolder cover k α N → LittleHolder cover k α N) ⊆
      closure (P '' Set.range (fun f : SmoothChartHolderCore cover k α =>
        (f : LittleHolder cover k α N))) :=
    P.continuous.range_subset_closure_image_dense hdense
  apply le_antisymm
  · apply closure_minimal
    · intro x hx
      rcases hx with ⟨f, rfl⟩
      change T (f : LittleHolder cover k α N) = 0
      rw [hTcore]
      change A f = 0
      exact f.property
    · exact T.isClosed_ker
  · intro x hx
    have hxT : T x = 0 := by simpa [T, littleHolderMeanZeroSubmodule] using hx
    have hxP : P x = x := hPker x hxT
    have hxRange : x ∈ closure (P '' Set.range (fun f : SmoothChartHolderCore cover k α =>
        (f : LittleHolder cover k α N))) := by
      rw [← hxP]
      exact hPimage ⟨x, rfl⟩
    refine closure_mono ?_ hxRange
    rintro y ⟨z, hz, rfl⟩
    rcases hz with ⟨f, rfl⟩
    exact hPcore f

end KahlerForm
