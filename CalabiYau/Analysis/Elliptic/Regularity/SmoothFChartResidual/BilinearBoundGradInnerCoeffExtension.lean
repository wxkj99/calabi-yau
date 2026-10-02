-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/SmoothFChartResidual/BilinearBoundGradInnerCoeffExtension.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplResidual
public import CalabiYau.Analysis.Elliptic.Regularity.GradInner.CLM.ChartFormula
public import CalabiYau.Analysis.Sobolev.Chart.SmoothDensity.StrictCutoffPushforwardBound
public import CalabiYau.Analysis.Sobolev.Chart.SmoothDensity.SmoothMul
public import CalabiYau.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuantK
public import CalabiYau.Analysis.Sobolev.Manifold.Morrey.HigherOrder
public import CalabiYau.Analysis.Sobolev.Manifold.Embedding.Iterated

@[expose] public section
open CalabiYau.Riemannian

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace CalabiYau
namespace Analysis
namespace Laplacian
namespace SmoothFChartResidualBilinearBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.LaplacianDomainChartData
open CalabiYau.Analysis.Laplacian.DiffChartBilinearH1ComplResidual
open CalabiYau.Analysis.Laplacian.GradInnerCLMChartFormula
open CalabiYau.Analysis.Sobolev.Chart
open _root_.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [T2Space M] [SigmaCompactSpace M]

noncomputable def gradInnerCoefIM
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) : M → ℝ :=
  fun x : M =>
    chartStrictCutoff (I := I) (M := M) α x *
      gradChartCoeff (I := I) g α
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) i x

private lemma gradInnerCoefI_M_eq_zero_of_cutoff_zero
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) {x : M}
    (hx : chartStrictCutoff (I := I) (M := M) α x = 0) :
    gradInnerCoefIM (I := I) (M := M) g α i x = 0 := by
  unfold gradInnerCoefIM
  rw [hx]; ring

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma gradInnerCoefI_M_smooth
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (gradInnerCoefIM (I := I) (M := M) g α i) := by
  classical
  intro x₀
  by_cases hx_source : x₀ ∈ (chartAt H α).source
  · have h_chart_source_open : IsOpen ((chartAt H α).source) :=
      (chartAt H α).open_source
    have h_cut_smooth : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (chartStrictCutoff (I := I) (M := M) α) x₀ :=
      (chartStrictCutoff_contMDiff (I := I) (M := M) α).contMDiffAt
    have hbase : x₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source]; exact hx_source
    have h_base_open : IsOpen ((trivializationAt E (TangentSpace I) α).baseSet) := by
      rw [trivializationAt_baseSet_eq_chartAt_source]; exact h_chart_source_open
    have hα_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff
    have h_coeff_on : ContMDiffOn I 𝓘(ℝ) ∞
        (gradChartCoeff (I := I) g α
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) i)
        (trivializationAt E (TangentSpace I) α).baseSet := by
      unfold gradChartCoeff
      refine contMDiffOn_finsetSum (fun j _ => ?_)
      refine ContMDiffOn.mul ?_ ?_
      · exact chartInvGramMatrix_entry_contMDiffOn (I := I) g α i j
      · have h_extChartOn_M : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α)
            (chartAt H α).source :=
          contMDiffOn_extChartAt (I := I) (x := α)
        have h_extChartOn : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α)
            (trivializationAt E (TangentSpace I) α).baseSet := by
          have h_eq : (trivializationAt E (TangentSpace I) α).baseSet =
              (chartAt H α).source := by
            rw [trivializationAt_baseSet_eq_chartAt_source]
          rw [h_eq]; exact h_extChartOn_M
        have h_scalar_target : ContDiffOn ℝ ∞
            (scalarOnE (I := I) α
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))
            (extChartAt I α).target :=
          CalabiYau.DivergenceTheorem.scalarOnE_contDiffOn
            (I := I) α hα_smooth
        have h_target_open : IsOpen ((extChartAt I α).target) :=
          isOpen_extChartAt_target (I := I) α
        have h_partial_E_on : ContDiffOn ℝ ∞
            (fun y : E => CalabiYau.Tensor.Coordinates.partialDeriv (E := E) j
              (scalarOnE (I := I) α
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y)
            (extChartAt I α).target := by
          unfold CalabiYau.Tensor.Coordinates.partialDeriv
          have h_fderiv_smooth :
              ContDiffOn ℝ ∞ (fun y : E => fderiv ℝ
                (scalarOnE (I := I) α
                  ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y)
                (extChartAt I α).target := by
            have h_le : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
              rw [show ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 = ((⊤ : ℕ∞) : WithTop ℕ∞) from by simp]
            exact h_scalar_target.fderiv_of_isOpen h_target_open h_le
          exact h_fderiv_smooth.clm_apply contDiffOn_const
        have h_partial_M_E : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
            (fun y : E => CalabiYau.Tensor.Coordinates.partialDeriv (E := E) j
              (scalarOnE (I := I) α
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y)
            (extChartAt I α).target :=
          (contMDiffOn_iff_contDiffOn).mpr h_partial_E_on
        have h_maps : Set.MapsTo (extChartAt I α)
            (trivializationAt E (TangentSpace I) α).baseSet
            (extChartAt I α).target := by
          intro x hx
          have hsrc : x ∈ (chartAt H α).source := by
            rw [trivializationAt_baseSet_eq_chartAt_source] at hx; exact hx
          have h_ext_source : x ∈ (extChartAt I α).source := by
            rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hsrc
          exact (extChartAt I α).map_source h_ext_source
        exact h_partial_M_E.comp h_extChartOn h_maps
    exact h_cut_smooth.mul ((h_coeff_on x₀ hbase).contMDiffAt
      (h_base_open.mem_nhds hbase))
  · have hx_compl : x₀ ∈ ((chartAt H α).source)ᶜ := hx_source
    have h_ev_zero : ∀ᶠ x in 𝓝 x₀,
        chartStrictCutoff (I := I) (M := M) α x = 0 := by
      have h_ev_nhdsSet :=
        chartStrictCutoff_eventually_zero_nhdsSet_compl_source (I := I) (M := M) α
      exact h_ev_nhdsSet.filter_mono (nhds_le_nhdsSet hx_compl)
    have h_ev_zero_coef : ∀ᶠ x in 𝓝 x₀,
        gradInnerCoefIM (I := I) (M := M) g α i x = 0 := by
      filter_upwards [h_ev_zero] with x hx
      exact gradInnerCoefI_M_eq_zero_of_cutoff_zero (I := I) (M := M) g α i hx
    have h_const : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun _ : M => (0 : ℝ)) x₀ :=
      contMDiffAt_const
    exact h_const.congr_of_eventuallyEq h_ev_zero_coef

lemma tsupport_gradInnerCoefI_M_subset
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    tsupport (gradInnerCoefIM (I := I) (M := M) g α i) ⊆ (chartAt H α).source := by
  classical
  have h_support_subset : Function.support (gradInnerCoefIM (I := I) (M := M) g α i) ⊆
      Function.support (chartStrictCutoff (I := I) (M := M) α) := by
    intro x hx
    by_contra hxoff
    apply hx
    have h0 : chartStrictCutoff (I := I) (M := M) α x = 0 := by
      simpa [Function.mem_support, not_not] using hxoff
    exact gradInnerCoefI_M_eq_zero_of_cutoff_zero (I := I) (M := M) g α i h0
  have h_tsupp_subset : tsupport (gradInnerCoefIM (I := I) (M := M) g α i) ⊆
      tsupport (chartStrictCutoff (I := I) (M := M) α) :=
    closure_minimal (h_support_subset.trans (subset_tsupport _))
      (isClosed_tsupport _)
  exact h_tsupp_subset.trans (chartStrictCutoff_tsupport_subset (I := I) (M := M) α)

noncomputable def Λgrad
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  smoothExtensionScalar (I := I) (M := M) α
    (gradInnerCoefIM (I := I) (M := M) g α i)

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma Λgrad_contDiff
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ (⊤ : ℕ∞) (Λgrad (I := I) (M := M) g α i) := by
  unfold Λgrad
  exact contDiff_smoothExtensionScalar (I := I) (M := M) α
    (gradInnerCoefI_M_smooth (I := I) (M := M) g α i)
    (tsupport_gradInnerCoefI_M_subset (I := I) (M := M) g α i)

end SmoothFChartResidualBilinearBound
end Laplacian
end Analysis
end CalabiYau

end
