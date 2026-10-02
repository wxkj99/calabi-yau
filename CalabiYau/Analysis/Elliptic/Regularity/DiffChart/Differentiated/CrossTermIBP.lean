-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/DiffChart/Differentiated/CrossTermIBP.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.ChosenFirstPartialW1p
public import CalabiYau.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplFromDomainPow
public import CalabiYau.Analysis.Sobolev.Euclidean.Multiplication.SmoothCoefWeakPartialIBP
public import CalabiYau.Analysis.Sobolev.Euclidean.Density

@[expose] public section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace DifferentiatedCrossTermIBP

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau
open CalabiYau.Analysis.Laplacian
open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.ChartPushedWeakPartialOnVolume
open CalabiYau.Analysis.Laplacian.H1ComplGradientH1LipschitzBound
open CalabiYau.Analysis.Laplacian.H1ComplWeakPartialLimit
open CalabiYau.Analysis.Laplacian.LaplacianDomainChartData
open CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl
open Sobolev.Chart
open Sobolev.Euclidean
open Sobolev.NirenbergEuclidean
open CalabiYau.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
    [SigmaCompactSpace M] in
lemma exists_smooth_global_extension
    {φ : EuclN → ℝ} (α : M)
    (hφ_chart : ContDiffOn ℝ (⊤ : ℕ∞) φ (chartTargetEuclid (I := I) (M := M) α))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ (δ : ℝ) (φExt : EuclN → ℝ),
      0 < δ ∧
      Metric.cthickening δ K ⊆ chartTargetEuclid (I := I) (M := M) α ∧
      ContDiff ℝ (⊤ : ℕ∞) φExt ∧
      (∀ y ∈ Metric.cthickening δ K, φExt y = φ y) := by
  classical
  obtain ⟨δ, η, hδ_pos, hδ_subset, hη_smooth, hη_cs, _hη_range, hη_one, hη_tsupp⟩ :=
    exists_smooth_cutoff_with_neighborhood
      (d := Module.finrank ℝ E) hK_compact
      (chartTargetEuclid_isOpen (I := I) (M := M) α) hK_in
  let φExt : EuclN → ℝ := fun y => η y * φ y
  refine ⟨δ, φExt, hδ_pos, hδ_subset, ?_, ?_⟩
  · have h_open_chart : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    have h_open_compl : IsOpen ((tsupport η)ᶜ) :=
      (isClosed_tsupport _).isOpen_compl
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy_support : y ∈ tsupport η
    · have hy_chart : y ∈ chartTargetEuclid (I := I) (M := M) α := hη_tsupp hy_support
      have hη_at : ContDiffAt ℝ (⊤ : ℕ∞) η y := hη_smooth.contDiffAt
      have hφ_at : ContDiffAt ℝ (⊤ : ℕ∞) φ y :=
        (hφ_chart y hy_chart).contDiffAt (h_open_chart.mem_nhds hy_chart)
      exact hη_at.mul hφ_at
    · have h_neighborhood : (tsupport η)ᶜ ∈ 𝓝 y := h_open_compl.mem_nhds hy_support
      have h_eq_zero : φExt =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := by
        filter_upwards [h_neighborhood] with z hz
        have hηz : η z = 0 := image_eq_zero_of_notMem_tsupport hz
        change η z * φ z = 0
        rw [hηz, zero_mul]
      have h_const : ContDiffAt ℝ (⊤ : ℕ∞) (fun _ : EuclN => (0 : ℝ)) y :=
        contDiffAt_const
      exact h_const.congr_of_eventuallyEq h_eq_zero
  · intro y hy
    change η y * φ y = φ y
    rw [hη_one y hy]
    ring

end DifferentiatedCrossTermIBP
end Laplacian
end Analysis
end DifferentialGeometry

end
