module

public import CalabiYau.MongeAmpere.Continuity.Openness.SmoothBootstrap.DifferenceQuotientIdentity
public import CalabiYau.MongeAmpere.Continuity.Openness.SmoothBootstrap.DifferenceQuotientBounds.MatrixInverse
public import CalabiYau.MongeAmpere.Continuity.Openness.SmoothBootstrap.DifferenceQuotientBounds.AveragedInverse
public import CalabiYau.MongeAmpere.Continuity.Openness.SmoothBootstrap.DifferenceQuotientBounds.BackgroundSecant

/-!
# Uniform coefficient and forcing bounds

Compact chart control of the `C^{2,α}` solution and smooth background data gives a common
ellipticity constant and `C^{0,α}` bounds for the averaged inverse and the translated forcing on
relatively compact subdomains.  The step-size radius and constants are independent of nonzero `h`.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology
open Matrix Set

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- Uniform ellipticity and `C^{0,α}` bounds for the coefficients and known forcing in every
nonzero difference-quotient equation on a compactly contained chart domain. -/
def HasUniformDifferenceQuotientBounds (ω₀ : KahlerForm n M) (G φ : M → ℝ)
    (α : ℝ≥0) : Prop :=
  ∀ x : M,
    ∀ U : Set (EuclideanSpace ℂ (Fin n)), IsOpen U → IsCompact (closure U) →
      closure U ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target →
      ∀ v : EuclideanSpace ℂ (Fin n),
        ∃ δ lam K : ℝ≥0, 0 < δ ∧ 0 < lam ∧
          ∀ h : ℝ, h ≠ 0 → |h| < δ →
            (∀ z ∈ U, z + h • v ∈
              (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) →
              let A := averagedChartInverse ω₀ φ x v h
              IsUniformlyEllipticOn A lam U ∧
                (∀ j l, HolderBoundOn 0 α K U fun z ↦ A z j l) ∧
                HolderBoundOn 0 α K U (chartDifferenceQuotientRhs ω₀ G φ x v h)

/-- The `C^{2,α}` chart gauge, positivity, and smooth data give uniform ellipticity and
`C^{0,α}` coefficient and forcing estimates for the quotient equations. -/
theorem solvesMongeAmpereC2_hasUniformDifferenceQuotientBounds
    (ω₀ : KahlerForm n M) (α : ℝ≥0) (hα₀ : 0 < α) (hα₁ : α < 1)
    {G φ : M → ℝ}
    (hG : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G)
    (hφ : ω₀.SolvesMongeAmpereC2 G φ)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (hφGauge : HasFiniteChartHolderGauge cover 2 α φ)
    (hEquation : HasChartLogDetEquation ω₀ G φ) :
    HasUniformDifferenceQuotientBounds ω₀ G φ α := by
  intro x U hU hUcompact hUchart v
  obtain ⟨δ, lam, Kmat, Krhs, hδ, hlam, hBounds⟩ :=
    exists_uniform_chart_segment_bounds ω₀ α hα₀ hα₁ hG hφ cover hφGauge
      hEquation x U hU hUcompact hUchart v
  let P : Set ℝ := {h | h ≠ 0 ∧ |h| < δ}
  have hSegmentData (h : ℝ) (hh : h ∈ P) := hBounds h hh.1 hh.2
  obtain ⟨Kinv, hInverseHolder⟩ :=
    exists_uniform_holderBoundOn_matrix_inverse α lam Kmat hα₀ hα₁ hlam U P
      (fun h s z ↦ chartBootstrapSegmentMatrix ω₀ φ x v h s z)
      (by
        intro h hh s hs
        exact (hSegmentData h hh).2.2.1 s hs)
      (by
        intro h hh s hs j l
        exact (hSegmentData h hh).2.2.2.1 s hs j l)
  refine ⟨δ, lam, max Kinv Krhs, hδ, hlam, ?_⟩
  intro h hne hh _htranslate
  have hhP : h ∈ P := ⟨hne, hh⟩
  obtain ⟨_hTranslation, hEllAvg, hEllSegment, hMatrixHolder, hIntegrable,
    hContinuous, hRhs⟩ := hSegmentData h hhP
  have hInverseAt (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (j l : Fin n) :
      HolderBoundOn 0 α Kinv U
        (fun z ↦ (chartBootstrapSegmentMatrix ω₀ φ x v h s z)⁻¹ j l) :=
    hInverseHolder h hhP s hs j l
  refine ⟨hEllAvg, ?_, ?_⟩
  · intro j l
    have hAverage := exists_holderBoundOn_interval_average α Kinv hα₀ hα₁ U
      (fun s z ↦ (chartBootstrapSegmentMatrix ω₀ φ x v h s z)⁻¹ j l)
      (fun s hs ↦ hInverseAt s hs j l)
      (fun z hz ↦ hIntegrable z hz j l)
      (fun z hz ↦ hContinuous z hz j l)
    simpa [averagedChartInverse, chartBootstrapSegmentMatrix] using
      hAverage.mono_const (le_max_left Kinv (max Kinv Krhs))
  · exact hRhs.mono_const (le_max_right Kinv Krhs)

end KahlerForm
