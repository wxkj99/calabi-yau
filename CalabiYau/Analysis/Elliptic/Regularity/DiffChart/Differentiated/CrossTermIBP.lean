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

theorem chosenSecondPartialChartPushedU_isWeakPartial_of_chartPushedWeakPartialLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i l : Fin (Module.finrank ℝ E)) :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) l
      (chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l)
      (((chartPushedWeakPartialLp (I := I) (M := M) g α i
        (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α i) u_h
       ) : EuclN → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) :=
  hasWeakPartialDeriv_chosenSecond_of_chartPushedWeakPartialLp
    (I := I) (M := M) g α hu_h i l

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

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma weightedInvGramDerivOnEuclid_contDiffOn_chart
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (weightedInvGramDerivOnEuclid (I := I) g α i j l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h := weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α i j l
  exact h

private lemma cross_derivative_term_ibp_single
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (direction : Fin (Module.finrank ℝ E))
    (i j : Fin (Module.finrank ℝ E))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      weightedInvGramDerivOnEuclid (I := I) g α i j direction y *
        (((chartPushedWeakPartialLp (I := I) (M := M) g α i
          (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α i) u_h
         ) : EuclN → ℝ)) y *
        (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
      ∂(volume : Measure EuclN))
    = -((∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j direction) y)
            (EuclideanSpace.single j 1) *
          (((chartPushedWeakPartialLp (I := I) (M := M) g α i
            (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α i) u_h
           ) : EuclN → ℝ)) y * ψ y
          ∂(volume : Measure EuclN))
      + (∫ y in chartTargetEuclid (I := I) (M := M) α,
          weightedInvGramDerivOnEuclid (I := I) g α i j direction y *
            chosenSecondPartialChartPushedU
              (I := I) (M := M) g α u_h i j y * ψ y
          ∂(volume : Measure EuclN))) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set φ : EuclN → ℝ := weightedInvGramDerivOnEuclid (I := I) g α i j direction
    with hφ_def
  have hφ_chart : ContDiffOn ℝ (⊤ : ℕ∞) φ Ω :=
    weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α i j direction
  set v : EuclN → ℝ :=
    (((chartPushedWeakPartialLp (I := I) (M := M) g α i
        (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α i) u_h
       ) : EuclN → ℝ)) with hv_def
  set w : Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun j' => chosenSecondPartialChartPushedU
      (I := I) (M := M) g α u_h i j' with hw_def
  have hw_isWeakPartial : ∀ j' : Fin (Module.finrank ℝ E),
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) j' (w j') v Ω :=
    fun j' =>
      chosenSecondPartialChartPushedU_isWeakPartial_of_chartPushedWeakPartialLp
        (I := I) (M := M) g α hu_h i j'
  set K : Set EuclN := tsupport ψ with hK_def
  have hK_compact : IsCompact K := hψ_cs
  have hK_in : K ⊆ Ω := hψ_support
  obtain ⟨δ, φExt, hδ_pos, hδ_subset, hφExt_smooth, hφExt_eq⟩ :=
    exists_smooth_global_extension (I := I) (M := M) (φ := φ) α
      hφ_chart hK_compact hK_in
  have hv_localMemLp : ∀ K' : Set EuclN, IsCompact K' → K' ⊆ Ω →
      MemLp v 2 ((volume : Measure EuclN).restrict K') := by
    intro K' hK'_compact hK'_in
    have h := chartPushedWeakPartialLp_locally_memLp
      (I := I) (M := M) g α i u_h hK'_compact hK'_in
    exact h
  have hw_localMemLp : ∀ (j' : Fin (Module.finrank ℝ E)) (K' : Set EuclN),
      IsCompact K' → K' ⊆ Ω →
      MemLp (w j') 2 ((volume : Measure EuclN).restrict K') := by
    intro j' K' hK'_compact hK'_in
    have h := chosenSecondPartialChartPushedU_locally_memLp
      (I := I) (M := M) g α hu_h i j' hK'_compact hK'_in
    exact h
  have h_ibp_ext :=
    CalabiYau.Analysis.Sobolev.Euclidean.integral_smul_weak_partial_eq
      (d := Module.finrank ℝ E) (Ω := Ω) hΩ_open
      (φ := φExt) hφExt_smooth (v := v) (w := w)
      hv_localMemLp hw_localMemLp hw_isWeakPartial j
      (ψ := ψ) hψ_smooth hψ_cs hψ_support
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have hcthick_subset : Metric.cthickening δ K ⊆ Ω := hδ_subset
  have hK_in_thickening : K ⊆ Metric.cthickening δ K :=
    Metric.self_subset_cthickening _
  have h_fderiv_zero_outside_K : ∀ x ∉ K, fderiv ℝ ψ x = 0 := by
    intro x hx
    have h_compl_open : IsOpen (Kᶜ) := (isClosed_tsupport _).isOpen_compl
    have hx_in_compl : x ∈ Kᶜ := hx
    have hψ_zero_neighborhood : ∀ᶠ y in 𝓝 x, ψ y = 0 := by
      filter_upwards [h_compl_open.mem_nhds hx_in_compl] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    have hψ_const_zero : fderiv ℝ ψ x = fderiv ℝ (fun _ : EuclN => (0 : ℝ)) x := by
      apply Filter.EventuallyEq.fderiv_eq
      filter_upwards [hψ_zero_neighborhood] with y hy
      rw [hy]
    rw [hψ_const_zero]; simp
  have hLHS_eq :
      ∫ y in Ω, φExt y * v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1) ∂(volume : Measure EuclN) =
      ∫ y in Ω, φ y * v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1) ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y hy => ?_)
    by_cases hy_K : y ∈ K
    · rw [hφExt_eq y (hK_in_thickening hy_K)]
    · rw [h_fderiv_zero_outside_K y hy_K]
      simp
  have h_fderiv_φExt_eq_φ_on_K : ∀ y ∈ K, ∀ j' : Fin (Module.finrank ℝ E),
      (fderiv ℝ φExt y) (EuclideanSpace.single j' 1) =
      (fderiv ℝ φ y) (EuclideanSpace.single j' 1) := by
    intro y hy_K j'
    have hy_thick : y ∈ Metric.cthickening δ K := hK_in_thickening hy_K
    have hy_thick_open : y ∈ Metric.thickening δ K := by
      rw [Metric.mem_thickening_iff]
      refine ⟨y, hy_K, ?_⟩
      simp [hδ_pos]
    have h_thick_open : IsOpen (Metric.thickening δ K) := Metric.isOpen_thickening
    have h_neighborhood : Metric.thickening δ K ∈ 𝓝 y := h_thick_open.mem_nhds hy_thick_open
    have h_thick_sub : Metric.thickening δ K ⊆ Metric.cthickening δ K :=
      Metric.thickening_subset_cthickening _ _
    have h_eq_neighborhood : φExt =ᶠ[𝓝 y] φ := by
      filter_upwards [h_neighborhood] with z hz
      exact hφExt_eq z (h_thick_sub hz)
    have h_fderiv_eq : fderiv ℝ φExt y = fderiv ℝ φ y :=
      Filter.EventuallyEq.fderiv_eq h_eq_neighborhood
    rw [h_fderiv_eq]
  have hLeibniz1_eq :
      ∫ y in Ω, (fderiv ℝ φExt y) (EuclideanSpace.single j 1) * v y * ψ y
        ∂(volume : Measure EuclN) =
      ∫ y in Ω, (fderiv ℝ φ y) (EuclideanSpace.single j 1) * v y * ψ y
        ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y hy => ?_)
    by_cases hy_K : y ∈ K
    · rw [h_fderiv_φExt_eq_φ_on_K y hy_K j]
    · have hψy : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy_K
      rw [hψy]; ring
  have hLeibniz2_eq :
      ∫ y in Ω, φExt y * w j y * ψ y ∂(volume : Measure EuclN) =
      ∫ y in Ω, φ y * w j y * ψ y ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y hy => ?_)
    by_cases hy_K : y ∈ K
    · rw [hφExt_eq y (hK_in_thickening hy_K)]
    · have hψy : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy_K
      rw [hψy]; ring
  rw [← hLHS_eq, ← hLeibniz1_eq, ← hLeibniz2_eq]
  exact h_ibp_ext

end DifferentiatedCrossTermIBP
end Laplacian
end Analysis
end DifferentialGeometry

end
