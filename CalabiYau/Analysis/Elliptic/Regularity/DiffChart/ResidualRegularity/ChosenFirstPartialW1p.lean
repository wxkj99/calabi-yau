-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/DiffChart/ResidualRegularity/ChosenFirstPartialW1p.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplFromDomainPow
public import CalabiYau.Analysis.Elliptic.Regularity.ChartPushed.WeakPartialOnVolume
public import CalabiYau.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev

@[expose] public section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace CalabiYau
namespace Analysis
namespace Laplacian
namespace DiffChartChosenFirstPartial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

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
open Sobolev.NirenbergEuclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

noncomputable def chartPushedChosenFirstPartial
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (i : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  Sobolev.Euclidean.chosenWeakPartialOrZero
    (d := Module.finrank ℝ E) 2 i
    (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
      ((h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
    (chartTargetEuclid (I := I) (M := M) α)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma locallyIntegrable_of_memLp_two_compact_open_subset
    (K Ω' : Set EuclN) (_hK_compact : IsCompact K) (hΩ'_subset_K : Ω' ⊆ K)
    (hΩ'_meas : MeasurableSet Ω')
    {f : EuclN → ℝ}
    (hf_memLp_K : MemLp f 2 ((volume : Measure EuclN).restrict K)) :
    LocallyIntegrable f ((volume : Measure EuclN).restrict Ω') := by
  have h_eq : ((volume : Measure EuclN).restrict K).restrict Ω' =
      (volume : Measure EuclN).restrict Ω' := by
    rw [Measure.restrict_restrict hΩ'_meas]
    congr 1
    exact Set.inter_eq_self_of_subset_left hΩ'_subset_K
  have hf_memLp_Ω' : MemLp f 2 ((volume : Measure EuclN).restrict Ω') := by
    rw [← h_eq]; exact hf_memLp_K.restrict Ω'
  exact hf_memLp_Ω'.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
    [SigmaCompactSpace M] in
private lemma chartTargetEuclid_sigmaCompact_cover
    (α : M) :
    ∃ K : ℕ → Set EuclN,
      (∀ n, IsCompact (K n)) ∧
      (∀ n, K n ⊆ chartTargetEuclid (I := I) (M := M) α) ∧
      (⋃ n, K n) = chartTargetEuclid (I := I) (M := M) α := by
  classical
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have : LocallyCompactSpace ↥(chartTargetEuclid (I := I) (M := M) α) :=
    hΩ_open.locallyCompactSpace
  have : SecondCountableTopology ↥(chartTargetEuclid (I := I) (M := M) α) :=
    inferInstance
  have : SigmaCompactSpace ↥(chartTargetEuclid (I := I) (M := M) α) :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  obtain ⟨K_sub, hK_sub_compact, hK_sub_cov⟩ :=
    SigmaCompactSpace.exists_compact_covering
      (X := ↥(chartTargetEuclid (I := I) (M := M) α))
  refine ⟨fun n => ((↑) : ↥(chartTargetEuclid (I := I) (M := M) α) → EuclN) '' K_sub n,
    ?_, ?_, ?_⟩
  · intro n
    exact (hK_sub_compact n).image continuous_subtype_val
  · intro n y ⟨z, _, hz_eq⟩
    rw [← hz_eq]
    exact z.2
  · apply Set.eq_of_subset_of_subset
    · rw [Set.iUnion_subset_iff]
      intro n y ⟨z, _, hz_eq⟩
      rw [← hz_eq]
      exact z.2
    · intro y hy
      let z : ↥(chartTargetEuclid (I := I) (M := M) α) := ⟨y, hy⟩
      have hz_in : z ∈ (⋃ n, K_sub n) := by rw [hK_sub_cov]; trivial
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz_in
      exact Set.mem_iUnion.mpr ⟨n, z, hn, rfl⟩

end DiffChartChosenFirstPartial
end Laplacian
end Analysis
end CalabiYau

end
