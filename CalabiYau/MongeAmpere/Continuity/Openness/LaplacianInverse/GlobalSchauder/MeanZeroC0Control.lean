module

public import CalabiYau.MongeAmpere.Continuity.Openness.LaplacianInverse.GlobalSchauder.MeanZeroC0ControlBasic
public import CalabiYau.MongeAmpere.Continuity.Openness.LaplacianInverse.GlobalSchauder.MeanZeroC0BadSequence
public import CalabiYau.MongeAmpere.Continuity.Openness.LaplacianInverse.GlobalSchauder.MeanZeroC0UniformBound
public import CalabiYau.MongeAmpere.Continuity.Openness.LaplacianInverse.GlobalSchauder.MeanZeroC0JetCompactness
public import CalabiYau.MongeAmpere.Continuity.Openness.LaplacianInverse.GlobalSchauder.MeanZeroC0HarmonicKernel

/-!
# Mean-zero control of the zeroth-order term

The compactness argument removes constants by normalizing the sequence in `C⁰`. The local
Schauder estimate yields a uniform C^{2,α} bound; finite-chart compactness gives a C² limit of
all jets through order two, so its Laplacian vanishes. C² harmonic rigidity and the zero-mean
condition then contradict the normalization. The local estimate is Gilbarg–Trudinger,
Theorem 6.2; C² compactness is Lemma 6.36 and C² harmonic rigidity is Theorem 3.5.
Székelyhidi, Theorem 2.10, gives the compact-manifold Schauder setting with a lower-order term.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology
open MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- Compact mean-zero `C⁰` control, using the finite-chart local Schauder estimate. -/
theorem exists_meanZero_laplacian_C0_control [Nonempty M]
    (ω₁ : KahlerForm n M) (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (α : ℝ≥0) (hα₀ : 0 < α) (hα₁ : α < 1)
    (hLocal : HasFiniteChartLocalLaplacianHolderEstimate ω₁ cover α) :
    HasMeanZeroLaplacianC0Control ω₁ cover α := by
  by_contra hNoControl
  obtain ⟨u, huSmooth, huMean, huBound, huNorm, huFinite, huSmall⟩ :=
    exists_normalized_counterexample_of_no_meanZero_laplacian_C0_control
      ω₁ cover α hNoControl
  have huC2 := exists_uniform_normalized_laplacian_C2_gauge_bound
    ω₁ cover α hLocal u huSmooth huBound huFinite huSmall
  obtain ⟨s, hs, f, hfC2, hJet, hUniform, hMean, hLap, hUnit⟩ :=
    exists_normalized_meanZero_laplacian_C2_compactness
      ω₁ cover α hα₀ hα₁ u huSmooth huMean huNorm
        huC2 huFinite huSmall
  have hZero := eq_zero_of_C2_laplacian_eq_zero_and_integral_zero
    ω₁ f hfC2 hLap hMean
  obtain ⟨x, hx⟩ := hUnit
  rw [hZero x] at hx
  norm_num at hx

end KahlerForm
