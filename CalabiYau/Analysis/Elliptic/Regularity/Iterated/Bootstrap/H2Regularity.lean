-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/Iterated/Bootstrap/H2Regularity.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.Iterated.Defs
public import CalabiYau.Analysis.Elliptic.Regularity.ChartPushed.WeakPartialOnVolume
public import CalabiYau.Analysis.Sobolev.Approximation.Density.Smooth
public import CalabiYau.Analysis.Elliptic.Regularity.LaplacianDomain.Chart.LocalRegularity

@[expose] public section

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace CalabiYau
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open _root_.Sobolev
open _root_.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

open CalabiYau.Analysis.Laplacian.H1ComplToLpChartBridge
open CalabiYau.Analysis.Laplacian.ChartPushedWeakPartialOnVolume
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartPushed_lp_class_locally_memLp_volume
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_lp : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp
      (chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α
        ((u_lp : M → ℝ))) 2
      ((volume : Measure EuclN).restrict K) := by
  classical
  have h_lp_meas : Measurable ((u_lp : M → ℝ)) :=
    (Lp.stronglyMeasurable u_lp).measurable
  have h_lp_memLp_global : MemLp ((u_lp : M → ℝ)) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) := Lp.memLp u_lp
  have h_memLp_w := chartPushed_memLp_chartPulledWeightedMeasure_restrict_of_memLp
    (I := I) (M := M) g α h_lp_meas h_lp_memLp_global
  exact memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure
    h_memLp_w hK_compact hK_compact.isClosed.measurableSet hK_in

omit [NeZero (Module.finrank ℝ E)] in
theorem memWkpChart_zero_of_lp
    (g : SmoothRiemannianMetric I M)
    (u_lp : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    MemWkpChart (I := I) (M := M) 0 2 ((u_lp : M → ℝ)) := by
  intro α
  rw [Sobolev.Euclidean.MemWkp_zero]
  set K : Set EuclN := chartImagePOUTsupport (I := I) (M := M) α with hK_def
  have hK_compact : IsCompact K :=
    chartImagePOUTsupport_isCompact (I := I) (M := M) α
  have hK_in_target : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartImagePOUTsupport_subset_target (I := I) (M := M) α
  have h_memLp_K : MemLp
      (chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α
        ((u_lp : M → ℝ))) 2
      ((volume : Measure EuclN).restrict K) :=
    chartPushed_lp_class_locally_memLp_volume (I := I) (M := M) g α u_lp
      hK_compact hK_in_target
  set f : EuclN → ℝ := chartPushed (I := I) (M := M)
    (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α ((u_lp : M → ℝ))
    with hf_def
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have h_chart_meas : MeasurableSet
      (chartTargetEuclid (I := I) (M := M) α) :=
    Sobolev.Chart.chartTargetEuclid_measurableSet
      (I := I) (M := M) α
  have h_zero_off : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α, y ∉ K → f y = 0 :=
    fun y hy hy_off => chartPushed_eq_zero_off_chartImagePOUTsupport
      (I := I) (M := M) α ((u_lp : M → ℝ)) hy hy_off
  have h_pointwise_eq : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      f y = Set.indicator K f y := by
    intro y hy
    by_cases hyK : y ∈ K
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK, h_zero_off y hy hyK]
  have h_ind_memLp_global : MemLp (Set.indicator K f) 2 (volume : Measure EuclN) := by
    rw [MeasureTheory.memLp_indicator_iff_restrict hK_meas]
    exact h_memLp_K
  have h_ind_memLp_chartTarget : MemLp (Set.indicator K f) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    h_ind_memLp_global.restrict _
  have h_ae_eq : (fun y => f y) =ᵐ[(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α)]
      (fun y => Set.indicator K f y) :=
    (MeasureTheory.ae_restrict_iff' h_chart_meas).mpr
      (Filter.Eventually.of_forall (fun y hy => h_pointwise_eq y hy))
  exact h_ind_memLp_chartTarget.ae_eq h_ae_eq.symm

omit [NeZero (Module.finrank ℝ E)] in
theorem iteratedH2Regularity_zero
    (g : SmoothRiemannianMetric I M)
    (u_h : H1Compl (I := I) (M := M) g) :
    Sobolev.Chart.MemWkpChart
      (I := I) (M := M) 0 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
  memWkpChart_zero_of_lp (I := I) (M := M) g
    (H1ComplToLp (I := I) (M := M) g u_h)

theorem iteratedH2Regularity_one
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 1) :
    Sobolev.Chart.MemWkpChart
      (I := I) (M := M) 2 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
    Sobolev.Chart.wkpNormChart
      (I := I) (M := M) 2 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤ := by
  rw [laplacianDomainPow_one] at hu_h
  exact laplacianDomain_memWkpChart_two
    (I := I) (M := M) g hu_h

theorem laplacianDomainPow_memWkpChart_two_k_le_one
    (g : SmoothRiemannianMetric I M)
    {k : ℕ} (hk : k ≤ 1)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    Sobolev.Chart.MemWkpChart
      (I := I) (M := M) (2 * k) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  interval_cases k
  · simpa using iteratedH2Regularity_zero (I := I) (M := M) g u_h
  · have h_one : 2 * 1 = 2 := by norm_num
    rw [h_one]
    exact (iteratedH2Regularity_one (I := I) (M := M) g hu_h).1

end Laplacian
end Analysis
end CalabiYau

end
