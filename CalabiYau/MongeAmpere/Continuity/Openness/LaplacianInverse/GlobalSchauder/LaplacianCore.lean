module

public import CalabiYau.MongeAmpere.Continuity.Openness.HolderSpaces
public import CalabiYau.MongeAmpere.Continuity.Openness.CompactChartCover
public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderCarrier.Basic
public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderCarrier.SmoothGaugeFiniteness
public import CalabiYau.Geometry.Kahler.Laplacian

/-!
# Smooth-core packaging of the Laplacian

The target of the global estimate is the actual order-zero smooth core, not merely a smooth
function carrying an unbundled gauge estimate. Smoothness of the Laplacian and Green's formula
supply the core element and its mean-zero property; compact chartwise Hölder bounds supply gauge
finiteness.
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
/-- The smooth Laplacian of a smooth function is an order-zero core element, with finite gauge
and mean zero. -/
theorem exists_smooth_laplacian_core (ω₁ : KahlerForm n M)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M) (α : ℝ≥0)
    (hα₀ : 0 < α) (hα₁ : α < 1) (f : M → ℝ)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f) :
    ∃ g : SmoothChartHolderCore cover 0 α,
      g.smoothMap = ω₁.laplacian f ∧
      (∫ x, g.smoothMap x ∂ω₁.volume = 0) ∧
      finiteChartHolderGauge cover 0 α g.smoothMap < ⊤ := by
  let g : SmoothChartHolderCore cover 0 α :=
    ⟨⟨ω₁.laplacian f, ω₁.contMDiff_laplacian hf⟩⟩
  refine ⟨g, rfl, ?_, ?_⟩
  · exact ω₁.integral_laplacian hf
  · exact smoothChartHolderGauge_finite cover 0 α hα₀ hα₁ g

end KahlerForm
