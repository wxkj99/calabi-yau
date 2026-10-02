module

public import CalabiYau.MongeAmpere.Continuity.Openness.C2Approximation.Smoothing.CompactSupport
public import CalabiYau.MongeAmpere.Continuity.Openness.C2Approximation.Smoothing.DerivativeInterchange
public import CalabiYau.MongeAmpere.Continuity.Openness.C2Approximation.Smoothing.UniformTwoJet

/-!
# Uniform C² convergence under compactly supported convolution

The weak-partial integration-by-parts identity identifies derivatives of a mollification with
mollifications of the classical derivatives.  Normalized bump estimates then give uniform
convergence of every real coordinate jet through order two, with supports kept in a fixed compact
subset of the prescribed open chart.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology

/-- Data for mollifying a compactly supported C² function without allowing the support to leave its
open coordinate domain. -/
structure EuclideanC2MollificationData
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (U : Set E) where
  approximation : ℕ → E → ℝ
  supportBound : Set E
  supportBound_compact : IsCompact supportBound
  supportBound_subset : supportBound ⊆ U
  smooth : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (approximation j)
  support_in_bound : ∀ j, tsupport (approximation j) ⊆ supportBound
  jetsTendsto : ∀ ε : ℝ≥0, 0 < ε →
    ∃ N, ∀ j, N ≤ j → ∀ r ≤ 2, ∀ x,
      ‖iteratedFDeriv ℝ r (approximation j - f) x‖ ≤ ε

/-- A normalized compactly supported mollifier approximates a C² function and both of its real
coordinate derivatives uniformly.  The fixed support bound allows later extension by zero in a
chart.  In real dimension zero, take the locally constant function itself. -/
theorem exists_euclideanC2MollificationData
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → ℝ} {U : Set E} (hU : IsOpen U)
    (hf : ContDiff ℝ 2 f) (hcompact : HasCompactSupport f)
    (hsupport : tsupport f ⊆ U) :
    Nonempty (EuclideanC2MollificationData E f U) := by
  classical
  -- An arbitrary finite-dimensional norm gives a topological real vector
  -- space, not a canonical inner-product measure. A basis supplies Haar
  -- volume; no claim is made that the basis preserves operator norms.
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  let : MeasureTheory.MeasureSpace E :=
    ⟨(Module.finBasis ℝ E).addHaar⟩
  have : MeasureTheory.Measure.IsAddHaarMeasure
      (MeasureTheory.volume : MeasureTheory.Measure E) :=
    isAddHaarMeasure_basis_addHaar (Module.finBasis ℝ E)
  obtain ⟨A⟩ := exists_euclideanC2ConvolutionData hU hf hcompact hsupport
  refine ⟨⟨A.approximation, A.supportBound, A.supportBound_compact,
    A.supportBound_subset, A.smooth, A.support_in_bound, ?_⟩⟩
  exact euclideanC2Convolution_uniform_twoJet A hf hcompact
    (fun j r hr x => euclideanC2Convolution_iteratedFDeriv A hf j r hr x)
