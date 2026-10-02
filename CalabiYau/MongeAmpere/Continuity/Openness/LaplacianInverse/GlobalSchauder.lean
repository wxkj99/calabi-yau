module

public import CalabiYau.MongeAmpere.Continuity.Openness.HolderSpaces
public import CalabiYau.Geometry.Kahler.Poisson
public import CalabiYau.Analysis.Elliptic.Schauder
public import CalabiYau.MongeAmpere.Continuity.Openness.LaplacianInverse.GlobalSchauder.LocalEstimate
public import CalabiYau.MongeAmpere.Continuity.Openness.LaplacianInverse.GlobalSchauder.MeanZeroC0Control
public import CalabiYau.MongeAmpere.Continuity.Openness.LaplacianInverse.GlobalSchauder.LaplacianCore

/-!
# Global mean-zero Schauder bound

This is the global estimate needed to make the smooth mean-zero Poisson solution operator
bounded in the fixed finite-chart gauges. The local interior estimate is not itself the result:
the `C⁰` term must be controlled globally using compactness, mean zero, and the triviality of the
smooth harmonic kernel on a connected compact Kähler manifold. The chartwise constants must then
be made uniform over the fixed finite cover.

The statement records finiteness of both gauges explicitly, so its `toReal` inequality is not
vacuous at `⊤` and can safely be used in the normed-core constructions.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology
open Set MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- The global mean-zero Schauder inequality, with the smooth Laplacian output explicitly
represented by an order-zero smooth core element. -/
def HasGlobalMeanZeroLaplacianBound (ω₁ : KahlerForm n M)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M) (α : ℝ≥0) : Prop :=
  ∃ C : ℝ≥0, ∀ f : SmoothChartHolderCore cover 2 α,
    (∫ x, f.smoothMap x ∂ω₁.volume = 0) →
    finiteChartHolderGauge cover 2 α f.smoothMap < ⊤ ∧
    ∃ g : SmoothChartHolderCore cover 0 α,
      g.smoothMap = ω₁.laplacian f.smoothMap ∧
      (∫ x, g.smoothMap x ∂ω₁.volume = 0) ∧
      finiteChartHolderGauge cover 0 α g.smoothMap < ⊤ ∧
      (finiteChartHolderGauge cover 2 α f.smoothMap).toReal ≤
        (C : ℝ) * (finiteChartHolderGauge cover 0 α g.smoothMap).toReal

/-- A single finite constant controls the global order-two gauge of every smooth mean-zero
function by the order-zero gauge of its complex Laplacian. This is the compact-manifold form of
the global mean-zero Schauder estimate; a local estimate without removal of its `C⁰` term would
not imply this assertion. -/
theorem exists_global_meanZero_laplacian_holder_bound [Nonempty M]
    (ω₁ : KahlerForm n M) (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (α : ℝ≥0) (hα₀ : 0 < α) (hα₁ : α < 1)
    (hSch : InteriorSchauderEstimate n) :
    HasGlobalMeanZeroLaplacianBound ω₁ cover α := by
  obtain ⟨C₁, hLocal⟩ := exists_finiteChart_local_laplacian_holder_estimate
    ω₁ cover α hα₀ hα₁ hSch
  obtain ⟨C₀, hC0⟩ := exists_meanZero_laplacian_C0_control
    (ω₁ := ω₁) (cover := cover) (α := α) hα₀ hα₁ ⟨C₁, hLocal⟩
  refine ⟨C₁ * (1 + C₀), ?_⟩
  intro f hfMeanZero
  obtain ⟨g, hgMap, hgMeanZero, hgFinite⟩ :=
    exists_smooth_laplacian_core ω₁ cover α hα₁
      f.smoothMap f.smoothMap.contMDiff
  have hfLapFinite : finiteChartHolderGauge cover 0 α (ω₁.laplacian f.smoothMap) < ⊤ := by
    rw [← hgMap]
    exact hgFinite
  have hPoint : ∀ x, |f.smoothMap x| ≤
      (C₀ : ℝ) * (finiteChartHolderGauge cover 0 α
        (ω₁.laplacian f.smoothMap)).toReal :=
    hC0 f.smoothMap f.smoothMap.contMDiff hfMeanZero hfLapFinite
  obtain ⟨hfFinite₂, hfFiniteLap, hfEstimate⟩ :=
    hLocal f.smoothMap f.smoothMap.contMDiff
      ((C₀ : ℝ) * (finiteChartHolderGauge cover 0 α
        (ω₁.laplacian f.smoothMap)).toReal) hPoint
  refine ⟨hfFinite₂, g, hgMap, hgMeanZero, hgFinite, ?_⟩
  calc
    (finiteChartHolderGauge cover 2 α f.smoothMap).toReal ≤
        (C₁ : ℝ) * ((finiteChartHolderGauge cover 0 α
          (ω₁.laplacian f.smoothMap)).toReal +
            (C₀ : ℝ) * (finiteChartHolderGauge cover 0 α
              (ω₁.laplacian f.smoothMap)).toReal) := hfEstimate
    _ = ((C₁ * (1 + C₀) : ℝ≥0) : ℝ) *
        (finiteChartHolderGauge cover 0 α g.smoothMap).toReal := by
      rw [← hgMap]
      push_cast
      ring

end KahlerForm
