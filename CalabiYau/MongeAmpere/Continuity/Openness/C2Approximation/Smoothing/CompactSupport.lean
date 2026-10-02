module

public import CalabiYau.Analysis.Sobolev.Tools.Mollification.WeakDerivative
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Compactly supported normalized convolutions inside an open set

Hirsch, *Differential Topology*, §2, Theorems 2.3–2.4: use a positive normalized
bump of sufficiently small radius so the convolution of a compactly supported
function stays in the given coordinate domain. The bump radii tend to zero.
The support conclusion concerns the **closed** support, not merely the pointwise
support. In dimension zero the volume measure still normalizes a bump supported
at the only point; if the function vanishes, the fixed support may be empty.
-/

@[expose] public section

open scoped ContDiff Convolution Topology
open Filter MeasureTheory MeasureTheory.Measure ContinuousLinearMap

/-- A fixed-support family of genuine normalized convolutions, with bump radii
shrinking to zero. Keeping the actual convolutions in the data prevents later
jet convergence statements from being satisfied by unrelated smooth functions. -/
structure EuclideanC2ConvolutionData
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    (f : E → ℝ) (U : Set E) where
  kernel : ℕ → ContDiffBump (0 : E)
  approximation : ℕ → E → ℝ
  convolution_eq : ∀ j,
    approximation j =
      (kernel j).normed (volume : Measure E) ⋆[lsmul ℝ ℝ, volume] f
  radius_tendsto : Tendsto (fun j => (kernel j).rOut) atTop (nhds 0)
  supportBound : Set E
  supportBound_compact : IsCompact supportBound
  supportBound_subset : supportBound ⊆ U
  smooth : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (approximation j)
  support_in_bound : ∀ j, tsupport (approximation j) ⊆ supportBound

-- Bounded (not isometric) transport between a normed real model and a
-- Euclidean coordinate model gives an alternative constructive route. The
-- factor ‖T‖ ^ r must be retained.

-- The off-diagonal real Hessian gives a concrete non-isometry witness:
-- the off-diagonal real Hessian has norm two on the sup-norm plane. It guards
-- against silently transporting second jets with unit operator-norm constant.

private noncomputable def normalizedKernelRadius (δ : ℝ) (j : ℕ) : ℝ :=
  (δ / 2) * (1 / ((j : ℝ) + 1))

private noncomputable def actualNormalizedKernelFamily
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (δ : ℝ) (hδ : 0 < δ) : ℕ → ContDiffBump (0 : E) := fun j => {
  rIn := normalizedKernelRadius δ j / 2
  rOut := normalizedKernelRadius δ j
  rIn_pos := by dsimp [normalizedKernelRadius]; positivity
  rIn_lt_rOut := by
    have hr : 0 < normalizedKernelRadius δ j := by
      dsimp [normalizedKernelRadius]
      positivity
    exact half_lt_self hr
}

private theorem normalizedKernelRadius_tendsto (δ : ℝ) :
    Tendsto (fun j : ℕ => normalizedKernelRadius δ j) atTop (nhds 0) := by
  have hbase : Tendsto (fun j : ℕ => (1 : ℝ) / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  dsimp only [normalizedKernelRadius]
  simpa only [mul_zero] using hbase.const_mul (δ / 2)

private theorem actualNormalizedKernel_nonneg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [IsLocallyFiniteMeasure (volume : Measure E)]
    [(volume : Measure E).IsOpenPosMeasure]
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) (x : E) :
    0 ≤ ((actualNormalizedKernelFamily E δ hδ j).normed (volume : Measure E)) x := by
  exact (actualNormalizedKernelFamily E δ hδ j).nonneg_normed x

private theorem actualNormalizedKernel_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [IsLocallyFiniteMeasure (volume : Measure E)]
    [(volume : Measure E).IsOpenPosMeasure]
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
    (∫ x, ((actualNormalizedKernelFamily E δ hδ j).normed (volume : Measure E)) x ∂(volume : Measure E)) = 1 := by
  exact (actualNormalizedKernelFamily E δ hδ j).integral_normed

private theorem actualNormalizedConvolution_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [IsAddHaarMeasure (volume : Measure E)]
    {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞)
      ((actualNormalizedKernelFamily E δ hδ j).normed (volume : Measure E) ⋆[lsmul ℝ ℝ, volume] f) := by
  exact HasCompactSupport.contDiff_convolution_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ)
    ((actualNormalizedKernelFamily E δ hδ j).hasCompactSupport_normed
      (μ := (volume : Measure E)))
    ((actualNormalizedKernelFamily E δ hδ j).contDiff_normed
      (μ := (volume : Measure E)))
    (hf.continuous.locallyIntegrable)

private theorem actualNormalizedConvolution_support
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [IsAddHaarMeasure (volume : Measure E)]
    {f : E → ℝ} (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
    tsupport ((actualNormalizedKernelFamily E δ hδ j).normed (volume : Measure E) ⋆[lsmul ℝ ℝ, volume] f) ⊆
      Metric.cthickening (δ / 2) (tsupport f) := by
  change closure (Function.support
      ((actualNormalizedKernelFamily E δ hδ j).normed (volume : Measure E) ⋆[lsmul ℝ ℝ, volume] f)) ⊆
    Metric.cthickening (δ / 2) (tsupport f)
  apply (closure_mono ?_).trans
  · exact Metric.closure_thickening_subset_cthickening (δ / 2) (tsupport f)
  · intro x hx
    have hx' := (MeasureTheory.support_convolution_subset
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := (volume : Measure E))) hx
    rcases Set.mem_add.mp hx' with ⟨a, ha, b, hb, rfl⟩
    have ha' : a ∈ Metric.ball (0 : E) (normalizedKernelRadius δ j) := by
      change a ∈ Function.support ((actualNormalizedKernelFamily E δ hδ j).normed (volume : Measure E)) at ha
      rw [(actualNormalizedKernelFamily E δ hδ j).support_normed_eq (μ := (volume : Measure E))] at ha
      exact ha
    apply Metric.mem_thickening_iff.mpr
    refine ⟨b, ?_, ?_⟩
    · exact subset_closure hb
    · rw [dist_eq_norm]
      have hab : a + b - b = a := by abel
      rw [hab]
      have haNorm : ‖a‖ < normalizedKernelRadius δ j := by
        simpa [Metric.mem_ball, dist_zero_right] using ha'
      calc
        ‖a‖ < normalizedKernelRadius δ j := haNorm
        _ ≤ δ / 2 := by
          have hj : (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 := by
            have hpos : 0 < (j : ℝ) + 1 := by positivity
            rw [div_le_iff₀ hpos]
            norm_num
          dsimp [normalizedKernelRadius]
          calc
            (δ / 2) * (1 / ((j : ℝ) + 1)) ≤ (δ / 2) * 1 :=
              mul_le_mul_of_nonneg_left hj (by positivity)
            _ = δ / 2 := by ring

private theorem exists_actualNormalizedConvolutionData
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [IsAddHaarMeasure (volume : Measure E)]
    {f : E → ℝ} {U : Set E} (hU : IsOpen U)
    (hf : ContDiff ℝ 2 f) (hcompact : HasCompactSupport f)
    (hsupport : tsupport f ⊆ U) :
    ∃ A : EuclideanC2ConvolutionData E f U,
      (∀ j x, 0 ≤ ((A.kernel j).normed (volume : Measure E)) x) ∧
      (∀ j, (∫ x, ((A.kernel j).normed (volume : Measure E)) x ∂(volume : Measure E)) = 1) := by
  classical
  let K := tsupport f
  have hK : IsCompact K := hcompact
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hsupport
  let φ : ℕ → ContDiffBump (0 : E) := actualNormalizedKernelFamily E δ hδ
  let g : ℕ → E → ℝ := fun j =>
    φ j |>.normed (volume : Measure E) ⋆[lsmul ℝ ℝ, volume] f
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨φ, g, ?_, ?_, Metric.cthickening (δ / 2) K, ?_, ?_, ?_, ?_⟩
    · intro j
      rfl
    · change Tendsto (fun j : ℕ => (actualNormalizedKernelFamily E δ hδ j).rOut)
        atTop (𝓝 0)
      change Tendsto (fun j : ℕ => normalizedKernelRadius δ j) atTop (𝓝 0)
      exact normalizedKernelRadius_tendsto δ
    · exact hK.cthickening
    · exact (Metric.cthickening_mono (by linarith) K).trans hδU
    · intro j
      exact actualNormalizedConvolution_smooth hf δ hδ j
    · intro j
      change tsupport (g j) ⊆ Metric.cthickening (δ / 2) (tsupport f)
      exact actualNormalizedConvolution_support δ hδ j
  · intro j x
    exact actualNormalizedKernel_nonneg δ hδ j x
  · intro j
    exact actualNormalizedKernel_integral δ hδ j

/-- Fixed compact support and smoothness for an approximate identity of
normalized real bump convolutions. No inner-product or isometric change of
coordinates is assumed: `E` may have any finite-dimensional real norm. -/
theorem exists_euclideanC2ConvolutionData
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [IsAddHaarMeasure (volume : Measure E)]
    {f : E → ℝ} {U : Set E} (hU : IsOpen U)
    (hf : ContDiff ℝ 2 f) (hcompact : HasCompactSupport f)
    (hsupport : tsupport f ⊆ U) :
    Nonempty (EuclideanC2ConvolutionData E f U) := by
  obtain ⟨A, _hkernel_nonneg, _hkernel_integral⟩ :=
    exists_actualNormalizedConvolutionData hU hf hcompact hsupport
  exact ⟨A⟩
