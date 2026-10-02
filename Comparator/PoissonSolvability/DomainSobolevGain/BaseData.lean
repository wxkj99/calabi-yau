module

public import Comparator.PoissonSolvability.DomainSobolevGain.DifferentiatedData
public import Comparator.PoissonSolvability.DomainSobolevGain.ChosenPartial

/-!
# Ordinary-domain base data with explicit chart H²

Following differential-geometry, the construction in
`Iterated/VariationalIdentity/DifferentiatedData.lean`.
The forcing remains the compensated ordinary-domain `fChart`.
-/

@[expose] public section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace CalabiYau.PoissonDomainRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.Analysis.Laplacian
open CalabiYau.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.LaplacianDomainChartData
open CalabiYau.Analysis.Laplacian.DiffChartChosenFirstPartial
open Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

namespace IteratedDiffChartBilinearData

omit [NeZero (Module.finrank ℝ E)] in
private lemma chosenMthMixed_one_cons_eq_chartPushedChosenFirstPartial
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (i : Fin (Module.finrank ℝ E)) :
    chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h 1
        (Fin.cons i (Fin.elim0)) =
      chartPushedChosenFirstPartial (I := I) (M := M) g α u_h i := by
  rfl

omit [NeZero (Module.finrank ℝ E)] in
private lemma chosenMthMixed_zero_elim0_eq_chartPushed
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) :
    chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h 0
        (Fin.elim0) =
      chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ) := rfl

private lemma base_u_chart_ae_eq_chartPushed
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
        hu_h).uChart =ᵐ[
      (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ) := by
  classical
  have h_coeFn :=
    Analysis.Laplacian.LaplacianDomainVariationalIdentityIntegralForm.chartPushedLpFromLp_coeFn
      (I := I) (M := M) g α (H1ComplToLp (I := I) (M := M) g u_h)
  have h_meas : MeasurableSet
      (chartTargetEuclid (I := I) (M := M) α) :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  have h_v_abs_w :
      (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α) ≪
      (chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α) := by
    intro A hA
    unfold chartPulledWeightedMeasure at hA
    rw [show ((volume : Measure EuclN).withDensity
        (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))).restrict
        (chartTargetEuclid (I := I) (M := M) α) =
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)).withDensity
          (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
      from MeasureTheory.restrict_withDensity h_meas _] at hA
    rw [MeasureTheory.withDensity_apply_eq_zero'
      (μ := (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α))
      (f := fun y : EuclN => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
      (ENNReal.measurable_ofReal.comp_aemeasurable
        ((densityOnEuclid_continuousOn (I := I) g α).aemeasurable h_meas))] at hA
    rw [Measure.restrict_apply' h_meas]
    rw [Measure.restrict_apply' h_meas] at hA
    refine MeasureTheory.measure_mono_null ?_ hA
    intro y ⟨hy_A, hy_chart⟩
    refine ⟨⟨?_, hy_A⟩, hy_chart⟩
    have h_pos : 0 < densityOnEuclid (I := I) g α y :=
      densityOnEuclid_pos (I := I) g α hy_chart
    exact (ENNReal.ofReal_pos.mpr h_pos).ne'
  exact h_v_abs_w.ae_le h_coeFn

def ofBase_of_chartH2
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (hChartH2 : MemWkpChart (I := I) (M := M) 2 2
      ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)) :
    IteratedDiffChartBilinearData (I := I) (M := M) g α u_h 0 where
  directions := Fin.elim0
  diffChartForcing :=
    (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
      hu_h).fChart
  fChartEffective_memLp_weighted :=
    (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
      hu_h).f_chart_memLp_weighted
  m_diff_variational_identity := by
    classical
    intro ψ hψ_smooth hψ_cs hψ_support
    set hu_h_lap : u_h ∈ laplacianDomain (I := I) (M := M) g := hu_h
    set D := chartBilinearH1ComplDataOfLaplacianDomain
      (I := I) (M := M) g α hu_h_lap with hD_def
    have h_base := D.variational_identity ψ hψ_smooth hψ_cs hψ_support
    have h_u_ae := base_u_chart_ae_eq_chartPushed
      (I := I) (M := M) g α hu_h_lap
    have h_principal_eq :
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h 1
                  (Fin.cons i (Fin.elim0)) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weakPartial i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN) := by
      refine MeasureTheory.integral_congr_ae ?_
      have h_wp_all : ∀ i, (chartBilinearH1ComplDataOfLaplacianDomain
            (I := I) (M := M) g α hu_h_lap).weakPartial i =ᵐ[
            (volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)]
          chartPushedChosenFirstPartial (I := I) (M := M) g α u_h i :=
        fun i => chartPushedWeakPartialLp_ae_eq_chosenFirstPartial_on_chartTarget_of_chartH2
          (I := I) (M := M) g α hChartH2 i
      have h_ae_eqs : ∀ i,
          ∀ᵐ y ∂((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)),
            chartPushedChosenFirstPartial (I := I) (M := M) g α u_h i y =
            (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M)
              g α hu_h_lap).weakPartial i y := by
        intro i
        filter_upwards [h_wp_all i] with y hy
        exact hy.symm
      have h_all_ae :
          ∀ᵐ y ∂((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)),
            ∀ i : Fin (Module.finrank ℝ E),
              chartPushedChosenFirstPartial (I := I) (M := M) g α u_h i y =
              (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M)
                g α hu_h_lap).weakPartial i y := by
        rw [Filter.eventually_all]
        exact h_ae_eqs
      filter_upwards [h_all_ae] with y hy
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [chosenMthMixed_one_cons_eq_chartPushedChosenFirstPartial
        (I := I) (M := M) g α u_h i, hy i]
    have h_mass_eq :
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h 0
              (Fin.elim0) y * ψ y
          ∂(volume : Measure EuclN) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            D.uChart y * ψ y
          ∂(volume : Measure EuclN) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [h_u_ae] with y hy
      rw [chosenMthMixed_zero_elim0_eq_chartPushed]
      rw [hy]
    rw [h_principal_eq, h_mass_eq]
    exact h_base

end IteratedDiffChartBilinearData
end CalabiYau.PoissonDomainRegularity
