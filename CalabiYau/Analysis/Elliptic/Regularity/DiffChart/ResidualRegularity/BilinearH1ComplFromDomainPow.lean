-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/DiffChart/ResidualRegularity/BilinearH1ComplFromDomainPow.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.DiffChart.Differentiated.BilinearH1Compl
public import CalabiYau.Analysis.Elliptic.Regularity.LaplacianDomain.Chart.VariationalData
public import CalabiYau.Analysis.Elliptic.Regularity.Iterated.Bootstrap.H2RegularitySuccessor
public import CalabiYau.Analysis.Sobolev.Chart.Defs
public import CalabiYau.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev
public import CalabiYau.Analysis.Elliptic.Regularity.LaplacianDomain.Variational.IntegralIdentity

@[expose] public section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace CalabiYau
namespace Analysis
namespace Laplacian
namespace DiffChartBilinearH1Compl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Laplacian.MetricExtension
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.ChartPushedWeakPartialOnVolume
open CalabiYau.Analysis.Laplacian.H1ComplGradientH1LipschitzBound
open CalabiYau.Analysis.Laplacian.H1ComplWeakPartialLimit
open CalabiYau.Analysis.Laplacian.LaplacianDomainChartData
open CalabiYau.Analysis.Laplacian.LaplacianDomainVariationalIdentityIntegralForm
open Sobolev.NirenbergEuclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

noncomputable def chosenSecondPartialChartPushedU
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (i j : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  Sobolev.Euclidean.chosenWeakPartialOrZero
    (d := Module.finrank ℝ E) 2 j
    (Sobolev.Euclidean.chosenWeakPartialOrZero
      (d := Module.finrank ℝ E) 2 i
      (Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α))
    (Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α)

private lemma chosenSecondPartialChartPushedU_memLp_two
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i j : Fin (Module.finrank ℝ E)) :
    MemLp (chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j) 2
      ((volume : Measure EuclN).restrict
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)) := by
  have h_memWkp_2 : Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
    have h_memWkpChart := (laplacianDomainPow_two_h2_plus_rhs_h2
      (I := I) (M := M) g hu_h).1.1
    exact h_memWkpChart α
  have h_inner_memW1p : DeGiorgi.MemW1p 2
      (Sobolev.Euclidean.chosenWeakPartialOrZero
        (d := Module.finrank ℝ E) 2 i
        (Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α))
      (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
    have h_step := h_memWkp_2.chosenWeakPartial_mem i
    rw [Sobolev.Euclidean.MemWkp.one_iff_memW1p] at h_step
    exact h_step
  exact Sobolev.Euclidean.chosenWeakPartialOrZero_memLp_of_mem
    h_inner_memW1p j

theorem chosenSecondPartialChartPushedU_locally_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i j : Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α) :
    MemLp (chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j) 2
      ((volume : Measure EuclN).restrict K) := by
  have h_global := chosenSecondPartialChartPushedU_memLp_two
    (I := I) (M := M) g α hu_h i j
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have h_chartTarget_open :
      IsOpen (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
    Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have h_eq : ((volume : Measure EuclN).restrict
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)).restrict K =
        (volume : Measure EuclN).restrict K := by
    rw [Measure.restrict_restrict hK_meas]
    congr 1
    exact Set.inter_eq_self_of_subset_left hK_in
  rw [← h_eq]
  exact h_global.restrict K

private noncomputable def chosenInnerPartialChartPushedU
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (i : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  Sobolev.Euclidean.chosenWeakPartialOrZero
    (d := Module.finrank ℝ E) 2 i
    (Sobolev.Chart.chartPushed
      (I := I) (M := M) (chartAtlasPOU I M) α
      ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
    (Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α)

private lemma chartPushed_memW1p_of_laplacianDomainPow_two
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    DeGiorgi.MemW1p 2
      (Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  have h_memWkp_2 : Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
    have h_memWkpChart := (laplacianDomainPow_two_h2_plus_rhs_h2
      (I := I) (M := M) g hu_h).1.1
    exact h_memWkpChart α
  exact h_memWkp_2.memW1p

private lemma chosenInnerPartialChartPushedU_memW1p
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i : Fin (Module.finrank ℝ E)) :
    DeGiorgi.MemW1p 2
      (chosenInnerPartialChartPushedU (I := I) (M := M) g α u_h i)
      (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  have h_memWkp_2 : Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
    have h_memWkpChart := (laplacianDomainPow_two_h2_plus_rhs_h2
      (I := I) (M := M) g hu_h).1.1
    exact h_memWkpChart α
  have h_step := h_memWkp_2.chosenWeakPartial_mem i
  rw [Sobolev.Euclidean.MemWkp.one_iff_memW1p] at h_step
  exact h_step

private lemma chosenInnerPartialChartPushedU_isWeakPartial
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i : Fin (Module.finrank ℝ E)) :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (chosenInnerPartialChartPushedU (I := I) (M := M) g α u_h i)
      (Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  have h_chartPushed_memW1p := chartPushed_memW1p_of_laplacianDomainPow_two
    (I := I) (M := M) g α hu_h
  exact Sobolev.Euclidean.chosenWeakPartialOrZero_isWeakPartial_of_mem
    h_chartPushed_memW1p i

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

private lemma chartPushedWeakPartialLp_ae_eq_chosenInner_on_open
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i : Fin (Module.finrank ℝ E))
    {Ω' K : Set EuclN} (hΩ'_open : IsOpen Ω') (hK_compact : IsCompact K)
    (hΩ'_subset_K : Ω' ⊆ K)
    (hK_in : K ⊆ Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α) :
    ((chartPushedWeakPartialLp (I := I) (M := M) g α i
        (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α i) u_h
       ) : EuclN → ℝ) =ᵐ[(volume : Measure EuclN).restrict Ω']
      chosenInnerPartialChartPushedU (I := I) (M := M) g α u_h i := by
  classical
  have h_chartPushed_isWeakPartial :=
    hasWeakPartialDeriv_chartPushedWeakPartialLp_on_chartTarget
      (I := I) (M := M) g α i u_h
  have h_chosenInner_isWeakPartial :=
    chosenInnerPartialChartPushedU_isWeakPartial
      (I := I) (M := M) g α hu_h i
  have hΩ'_subset_chartTarget : Ω' ⊆
      Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α := hΩ'_subset_K.trans hK_in
  have h_chartPushed_restr :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
        (((chartPushedWeakPartialLp (I := I) (M := M) g α i
          (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α i) u_h
         ) : EuclN → ℝ))
        (Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        Ω' :=
    DeGiorgi.HasWeakPartialDeriv.restrict hΩ'_open hΩ'_subset_chartTarget
      h_chartPushed_isWeakPartial
  have h_chosenInner_restr :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
        (chosenInnerPartialChartPushedU (I := I) (M := M) g α u_h i)
        (Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        Ω' :=
    DeGiorgi.HasWeakPartialDeriv.restrict hΩ'_open hΩ'_subset_chartTarget
      h_chosenInner_isWeakPartial
  have h_chartPushed_memLp_K : MemLp
      (((chartPushedWeakPartialLp (I := I) (M := M) g α i
        (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α i) u_h
       ) : EuclN → ℝ)) 2 ((volume : Measure EuclN).restrict K) :=
    chartPushedWeakPartialLp_locally_memLp (I := I) (M := M) g α i u_h
      hK_compact hK_in
  have h_chosenInner_memLp_chartTarget : MemLp
      (chosenInnerPartialChartPushedU (I := I) (M := M) g α u_h i) 2
      ((volume : Measure EuclN).restrict
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)) := by
    unfold chosenInnerPartialChartPushedU
    exact Sobolev.Euclidean.chosenWeakPartialOrZero_memLp_of_mem
      (chartPushed_memW1p_of_laplacianDomainPow_two
        (I := I) (M := M) g α hu_h) i
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have h_chartTarget_restrict_K : ((volume : Measure EuclN).restrict
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)).restrict K =
      (volume : Measure EuclN).restrict K := by
    rw [Measure.restrict_restrict hK_meas]
    congr 1
    exact Set.inter_eq_self_of_subset_left hK_in
  have h_chosenInner_memLp_K : MemLp
      (chosenInnerPartialChartPushedU (I := I) (M := M) g α u_h i) 2
      ((volume : Measure EuclN).restrict K) := by
    rw [← h_chartTarget_restrict_K]
    exact h_chosenInner_memLp_chartTarget.restrict K
  have hΩ'_meas : MeasurableSet Ω' := hΩ'_open.measurableSet
  have h_chartPushed_localInt : LocallyIntegrable
      (((chartPushedWeakPartialLp (I := I) (M := M) g α i
        (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α i) u_h
       ) : EuclN → ℝ))
      ((volume : Measure EuclN).restrict Ω') :=
    locallyIntegrable_of_memLp_two_compact_open_subset
      K Ω' hK_compact hΩ'_subset_K hΩ'_meas h_chartPushed_memLp_K
  have h_chosenInner_localInt : LocallyIntegrable
      (chosenInnerPartialChartPushedU (I := I) (M := M) g α u_h i)
      ((volume : Measure EuclN).restrict Ω') :=
    locallyIntegrable_of_memLp_two_compact_open_subset
      K Ω' hK_compact hΩ'_subset_K hΩ'_meas h_chosenInner_memLp_K
  exact DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ'_open
    h_chartPushed_restr h_chosenInner_restr
    h_chartPushed_localInt h_chosenInner_localInt

theorem hasWeakPartialDeriv_chosenSecond_of_chartPushedWeakPartialLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i k : Fin (Module.finrank ℝ E)) :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      (chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i k)
      (((chartPushedWeakPartialLp (I := I) (M := M) g α i
        (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α i) u_h
       ) : EuclN → ℝ))
      (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  classical
  have h_chosenSecond_def :
      chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i k =
      Sobolev.Euclidean.chosenWeakPartialOrZero
        (d := Module.finrank ℝ E) 2 k
        (chosenInnerPartialChartPushedU (I := I) (M := M) g α u_h i)
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) := by
    unfold chosenSecondPartialChartPushedU chosenInnerPartialChartPushedU
    rfl
  have h_inner_memW1p := chosenInnerPartialChartPushedU_memW1p
    (I := I) (M := M) g α hu_h i
  have h_chosenSecond_isWeakPartial_inner :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
        (chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i k)
        (chosenInnerPartialChartPushedU (I := I) (M := M) g α u_h i)
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) := by
    rw [h_chosenSecond_def]
    exact Sobolev.Euclidean.chosenWeakPartialOrZero_isWeakPartial_of_mem
      h_inner_memW1p k
  intro ψ hψ_smooth hψ_cs hψ_support
  have hΩ_open :
      IsOpen (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
    Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  obtain ⟨δ, hδ_pos, hδ_subset⟩ :
      ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ (tsupport ψ) ⊆
        Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α :=
    hψ_cs.exists_cthickening_subset_open hΩ_open hψ_support
  set Ω' : Set EuclN := Metric.thickening δ (tsupport ψ) with hΩ'_def
  set K : Set EuclN := Metric.cthickening δ (tsupport ψ) with hK_def
  have hΩ'_open : IsOpen Ω' := Metric.isOpen_thickening
  have hK_compact : IsCompact K := hψ_cs.cthickening
  have hΩ'_subset_K : Ω' ⊆ K := Metric.thickening_subset_cthickening δ (tsupport ψ)
  have hK_in : K ⊆ Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α := hδ_subset
  have h_tsupport_in_Ω' : tsupport ψ ⊆ Ω' :=
    Metric.self_subset_thickening hδ_pos _
  have hΩ'_subset_chartTarget : Ω' ⊆
      Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α := hΩ'_subset_K.trans hK_in
  have h_ae : (((chartPushedWeakPartialLp (I := I) (M := M) g α i
        (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α i) u_h
       ) : EuclN → ℝ)) =ᵐ[(volume : Measure EuclN).restrict Ω']
      chosenInnerPartialChartPushedU (I := I) (M := M) g α u_h i :=
    chartPushedWeakPartialLp_ae_eq_chosenInner_on_open
      (I := I) (M := M) g α hu_h i hΩ'_open hK_compact hΩ'_subset_K hK_in
  have h_chosenSecond_isWeakPartial_inner_Ω' :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
        (chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i k)
        (chosenInnerPartialChartPushedU (I := I) (M := M) g α u_h i)
        Ω' :=
    DeGiorgi.HasWeakPartialDeriv.restrict hΩ'_open hΩ'_subset_chartTarget
      h_chosenSecond_isWeakPartial_inner
  have h_chosenSecond_isWeakPartial_chartPushed_Ω' :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
        (chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i k)
        (((chartPushedWeakPartialLp (I := I) (M := M) g α i
          (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α i) u_h
         ) : EuclN → ℝ))
        Ω' :=
    Sobolev.Euclidean.hasWeakPartialDeriv_congr_ae
      hΩ'_open k h_ae.symm h_chosenSecond_isWeakPartial_inner_Ω'
  have h_identity := h_chosenSecond_isWeakPartial_chartPushed_Ω'
    ψ hψ_smooth hψ_cs h_tsupport_in_Ω'
  set f := ((chartPushedWeakPartialLp (I := I) (M := M) g α i
    (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α i) u_h
   ) : EuclN → ℝ) with hf_def
  set g_chart := chosenSecondPartialChartPushedU
    (I := I) (M := M) g α u_h i k with hg_chart_def
  have h_chartTarget_meas :
      MeasurableSet (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := hΩ_open.measurableSet
  have hΩ'_meas : MeasurableSet Ω' := hΩ'_open.measurableSet
  have h_fderiv_zero : ∀ x ∉ tsupport ψ, fderiv ℝ ψ x = 0 := by
    intro x hx
    have h_compl_open : IsOpen ((tsupport ψ)ᶜ) :=
      (isClosed_tsupport _).isOpen_compl
    have hx_in_compl : x ∈ (tsupport ψ)ᶜ := hx
    have hψ_zero_neighborhood : ∀ᶠ y in 𝓝 x, ψ y = 0 := by
      filter_upwards [h_compl_open.mem_nhds hx_in_compl] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    have hψ_const_zero : fderiv ℝ ψ x = fderiv ℝ (fun _ : EuclN => (0 : ℝ)) x := by
      apply Filter.EventuallyEq.fderiv_eq
      filter_upwards [hψ_zero_neighborhood] with y hy
      rw [hy]
    rw [hψ_const_zero]; simp
  have h_LHS_eq :
      ∫ x in Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
        f x * (fderiv ℝ ψ x) (EuclideanSpace.single k 1) =
      ∫ x in Ω', f x * (fderiv ℝ ψ x) (EuclideanSpace.single k 1) := by
    rw [show ∫ x in Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α,
          f x * (fderiv ℝ ψ x) (EuclideanSpace.single k 1) =
        ∫ x in Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α,
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α).indicator
            (fun x => f x * (fderiv ℝ ψ x) (EuclideanSpace.single k 1)) x
        from by
      refine (MeasureTheory.setIntegral_congr_fun h_chartTarget_meas (fun x hx => ?_)).symm
      rw [Set.indicator_of_mem hx]]
    rw [show ∫ x in Ω', f x * (fderiv ℝ ψ x) (EuclideanSpace.single k 1) =
        ∫ x in Ω', (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α).indicator
            (fun x => f x * (fderiv ℝ ψ x) (EuclideanSpace.single k 1)) x from by
      refine (MeasureTheory.setIntegral_congr_fun hΩ'_meas (fun x hx => ?_)).symm
      rw [Set.indicator_of_mem (hΩ'_subset_chartTarget hx)]]
    have h_outside_Ω' :
        ∀ x ∈ (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) \ Ω',
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α).indicator
          (fun x => f x * (fderiv ℝ ψ x) (EuclideanSpace.single k 1)) x = 0 := by
      intro x ⟨hx_in_chart, hx_notin_Ω'⟩
      rw [Set.indicator_of_mem hx_in_chart]
      have hx_notin_tsupport : x ∉ tsupport ψ := fun hx => hx_notin_Ω' (h_tsupport_in_Ω' hx)
      rw [h_fderiv_zero x hx_notin_tsupport]; simp
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := volume) (f := _) (s := Ω')]
    · rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (μ := volume) (f := _)
        (s := Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)]
      intro x hx
      by_cases hx_in_chart : x ∈ Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α
      · exact absurd hx_in_chart hx
      · rw [Set.indicator_of_notMem hx_in_chart]
    intro x hx
    by_cases hx_in_chart : x ∈ Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α
    · exact h_outside_Ω' x ⟨hx_in_chart, hx⟩
    · rw [Set.indicator_of_notMem hx_in_chart]
  have h_RHS_eq :
      ∫ x in Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
        g_chart x * ψ x =
      ∫ x in Ω', g_chart x * ψ x := by
    rw [show ∫ x in Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α,
          g_chart x * ψ x =
        ∫ x in Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α,
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α).indicator
            (fun x => g_chart x * ψ x) x
        from by
      refine (MeasureTheory.setIntegral_congr_fun h_chartTarget_meas (fun x hx => ?_)).symm
      rw [Set.indicator_of_mem hx]]
    rw [show ∫ x in Ω', g_chart x * ψ x =
        ∫ x in Ω', (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α).indicator
            (fun x => g_chart x * ψ x) x from by
      refine (MeasureTheory.setIntegral_congr_fun hΩ'_meas (fun x hx => ?_)).symm
      rw [Set.indicator_of_mem (hΩ'_subset_chartTarget hx)]]
    have h_outside_Ω' :
        ∀ x ∈ (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) \ Ω',
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α).indicator
          (fun x => g_chart x * ψ x) x = 0 := by
      intro x ⟨hx_in_chart, hx_notin_Ω'⟩
      rw [Set.indicator_of_mem hx_in_chart]
      have hx_notin_tsupport : x ∉ tsupport ψ := fun hx => hx_notin_Ω' (h_tsupport_in_Ω' hx)
      have hψ_x_zero : ψ x = 0 := image_eq_zero_of_notMem_tsupport hx_notin_tsupport
      rw [hψ_x_zero, mul_zero]
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := volume) (f := _) (s := Ω')]
    · rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (μ := volume) (f := _)
        (s := Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)]
      intro x hx
      by_cases hx_in_chart : x ∈ Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α
      · exact absurd hx_in_chart hx
      · rw [Set.indicator_of_notMem hx_in_chart]
    intro x hx
    by_cases hx_in_chart : x ∈ Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α
    · exact h_outside_Ω' x ⟨hx_in_chart, hx⟩
    · rw [Set.indicator_of_notMem hx_in_chart]
  rw [h_LHS_eq, h_RHS_eq]
  exact h_identity

noncomputable def chosenFChartDeriv
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (direction : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  Sobolev.Euclidean.chosenWeakPartialOrZero
    (d := Module.finrank ℝ E) 2 direction
    (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h)).fChart
    (Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α)

omit [SigmaCompactSpace M] in
lemma chosenFChartDeriv_isWeakPartial
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (direction : Fin (Module.finrank ℝ E))
    (h_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).fChart
      (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α)) :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) direction
      (chosenFChartDeriv (I := I) (M := M) g α hu_h direction)
      (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).fChart
      (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  unfold chosenFChartDeriv
  exact Sobolev.Euclidean.chosenWeakPartialOrZero_isWeakPartial_of_mem
    h_memW1p direction

omit [SigmaCompactSpace M] in
private lemma chosenFChartDeriv_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (direction : Fin (Module.finrank ℝ E))
    (h_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).fChart
      (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α)) :
    MemLp (chosenFChartDeriv (I := I) (M := M) g α hu_h direction) 2
      ((volume : Measure EuclN).restrict
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)) := by
  unfold chosenFChartDeriv
  exact Sobolev.Euclidean.chosenWeakPartialOrZero_memLp_of_mem
    h_memW1p direction

omit [SigmaCompactSpace M] in
private lemma chosenFChartDeriv_locally_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (direction : Fin (Module.finrank ℝ E))
    (h_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).fChart
      (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α) :
    MemLp (chosenFChartDeriv (I := I) (M := M) g α hu_h direction) 2
      ((volume : Measure EuclN).restrict K) := by
  have h_global := chosenFChartDeriv_memLp (I := I) (M := M) g α hu_h direction
    h_memW1p
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have h_eq : ((volume : Measure EuclN).restrict
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)).restrict K =
      (volume : Measure EuclN).restrict K := by
    rw [Measure.restrict_restrict hK_meas]
    congr 1
    exact Set.inter_eq_self_of_subset_left hK_in
  rw [← h_eq]
  exact h_global.restrict K

noncomputable def diffChartBilinearH1ComplDataOfLaplacianDomainPowTwo
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (direction : Fin (Module.finrank ℝ E))
    (h_base_f_chart_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).fChart
      (chartTargetEuclid (I := I) (M := M) α))
    (h_identity :
      ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                (chosenSecondPartialChartPushedU
                  (I := I) (M := M) g α u_h i direction) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).weakPartial direction y * ψ y
          ∂(volume : Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            chosenFChartDeriv (I := I) (M := M) g α hu_h direction y * ψ y
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α i j direction y *
                (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
                  (laplacianDomainPow_succ_subset_laplacianDomain
                    (I := I) (M := M) g 1 hu_h)).weakPartial i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α direction y *
            (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).uChart y * ψ y
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α direction y *
            (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).fChart y * ψ y
          ∂(volume : Measure EuclN))) :
    DiffChartBilinearH1ComplData (I := I) (M := M) g α where
  base := chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
    (laplacianDomainPow_succ_subset_laplacianDomain (I := I) (M := M) g 1 hu_h)
  direction := direction
  uChartDeriv := (chartBilinearH1ComplDataOfLaplacianDomain
    (I := I) (M := M) g α
    (laplacianDomainPow_succ_subset_laplacianDomain
      (I := I) (M := M) g 1 hu_h)).weakPartial direction
  fChartDeriv := chosenFChartDeriv (I := I) (M := M) g α hu_h direction
  weakPartialDeriv := fun i =>
    chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i direction
  u_chart_deriv_isWeakPartial :=
    (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h)).weak_partial_isWeakPartial direction
  f_chart_deriv_isWeakPartial :=
    chosenFChartDeriv_isWeakPartial (I := I) (M := M) g α hu_h direction
      h_base_f_chart_memW1p
  weak_partial_deriv_isWeakPartial := fun i =>
    hasWeakPartialDeriv_chosenSecond_of_chartPushedWeakPartialLp
      (I := I) (M := M) g α hu_h i direction
  u_chart_deriv_locally_memLp K hK_compact hK_in :=
    (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h)).weak_partial_locally_memLp direction K
      hK_compact hK_in
  f_chart_deriv_locally_memLp _K hK_compact hK_in := by
    have h_global : MemLp
        (chosenFChartDeriv (I := I) (M := M) g α hu_h direction) 2
        ((volume : Measure EuclN).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)) := by
      unfold chosenFChartDeriv
      exact Sobolev.Euclidean.chosenWeakPartialOrZero_memLp_of_mem
        h_base_f_chart_memW1p direction
    have hK_meas : MeasurableSet _K := hK_compact.isClosed.measurableSet
    have h_eq : ((volume : Measure EuclN).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)).restrict _K =
        (volume : Measure EuclN).restrict _K := by
      rw [Measure.restrict_restrict hK_meas]
      congr 1
      exact Set.inter_eq_self_of_subset_left hK_in
    rw [← h_eq]
    exact h_global.restrict _K
  weak_partial_deriv_locally_memLp i _K hK_compact hK_in :=
    chosenSecondPartialChartPushedU_locally_memLp
      (I := I) (M := M) g α hu_h i direction hK_compact hK_in
  differentiated_variational_identity := h_identity

noncomputable def fChartPiecePreimage
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) : EuclN → ℝ :=
  Sobolev.Chart.chartPushed
    (I := I) (M := M) (chartAtlasPOU I M) α
    ((laplacianDomain.preimage (I := I) (M := M) g
        ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h⟩ :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)

lemma fChartPiecePreimage_memWkp_two_two
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (fChartPiecePreimage (I := I) (M := M) g α hu_h)
      (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  unfold fChartPiecePreimage
  exact (laplacianDomainPow_two_h2_plus_rhs_h2
    (I := I) (M := M) g hu_h).2.1 α

private lemma fChartPiecePreimage_memW1p
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (fChartPiecePreimage (I := I) (M := M) g α hu_h)
      (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  have h_memWkp := fChartPiecePreimage_memWkp_two_two
    (I := I) (M := M) g α hu_h
  exact h_memWkp.memW1p

private noncomputable def smoothMulLpRhoPreimage
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
    (laplacianDomain.preimage (I := I) (M := M) g
      ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h⟩)

noncomputable def fHLeibnizResidualLp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  -((2 : ℝ) • gradInnerCLM (I := I) (M := M) g
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h) -
    smoothMulLp (I := I) (M := M) g
      (laplacianOfChartPOU (I := I) (M := M) g α)
      (H1ComplToLp (I := I) (M := M) g u_h)

omit [NeZero (Module.finrank ℝ E)] in
private lemma fHLeibniz_eq_piecePreimage_add_residual
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    leibnizCompensatedSource (I := I) (M := M) g α u_h
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h) =
      smoothMulLpRhoPreimage (I := I) (M := M) g α hu_h +
        fHLeibnizResidualLp (I := I) (M := M) g α u_h := by
  classical
  unfold smoothMulLpRhoPreimage fHLeibnizResidualLp
  rw [fHLeibniz_def]
  have h_diff_eq :
      H1ComplToLp (I := I) (M := M) g u_h -
        laplacianOp (I := I) (M := M) g
          ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h⟩ =
      laplacianDomain.preimage (I := I) (M := M) g
        ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h⟩ := by
    rw [laplacianOp_apply]
    abel
  rw [h_diff_eq]
  abel

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartPushedRawLpFromLp_coeFn_add
    (g : SmoothRiemannianMetric I M) (α : M)
    (F G : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ((chartPushedRawLpFromLp (I := I) (M := M) g α (F + G) :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α))) : EuclN → ℝ)
      =ᵐ[(chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)]
      (fun y => ((chartPushedRawLpFromLp (I := I) (M := M) g α F :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α))) : EuclN → ℝ) y +
        ((chartPushedRawLpFromLp (I := I) (M := M) g α G :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α))) : EuclN → ℝ) y) := by
  classical
  have h_FG_coeFn := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α (F + G)
  have h_F_coeFn := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α F
  have h_G_coeFn := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α G
  set sumFun : M → ℝ := fun x =>
    ((F : Lp ℝ 2 _) : M → ℝ) x + ((G : Lp ℝ 2 _) : M → ℝ) x with hsumFun_def
  have h_sum_coe : ((F + G : Lp ℝ 2 _) : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g] sumFun :=
    MeasureTheory.Lp.coeFn_add F G
  have h_FG_meas : Measurable ((F + G : Lp ℝ 2 _) : M → ℝ) :=
    (Lp.stronglyMeasurable (F + G)).measurable
  have hF_meas : Measurable ((F : Lp ℝ 2 _) : M → ℝ) :=
    (Lp.stronglyMeasurable F).measurable
  have hG_meas : Measurable ((G : Lp ℝ 2 _) : M → ℝ) :=
    (Lp.stronglyMeasurable G).measurable
  have hsum_meas : Measurable sumFun := hF_meas.add hG_meas
  have h_chartPushedRaw_FG :
      Sobolev.Chart.chartPushedRaw (I := I) α
        ((F + G : Lp ℝ 2 _) : M → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)]
      Sobolev.Chart.chartPushedRaw (I := I) α
        sumFun :=
    CalabiYau.Analysis.Laplacian.LaplacianDomainChartData.chartPushedRaw_aeEq_of_aeEq
      (I := I) (M := M) g α h_FG_meas hsum_meas h_sum_coe
  have h_chartPushedRaw_sum_pointwise :
      ∀ y : EuclN,
        Sobolev.Chart.chartPushedRaw (I := I) α
          sumFun y =
        Sobolev.Chart.chartPushedRaw (I := I) α
          ((F : Lp ℝ 2 _) : M → ℝ) y +
        Sobolev.Chart.chartPushedRaw (I := I) α
          ((G : Lp ℝ 2 _) : M → ℝ) y := by
    intro y
    by_cases hy : y ∈ Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α
    · rw [Sobolev.Chart.chartPushedRaw_apply_of_mem
        (I := I) (M := M) (α := α) sumFun hy,
        Sobolev.Chart.chartPushedRaw_apply_of_mem
          (I := I) (M := M) (α := α) ((F : Lp ℝ 2 _) : M → ℝ) hy,
        Sobolev.Chart.chartPushedRaw_apply_of_mem
          (I := I) (M := M) (α := α) ((G : Lp ℝ 2 _) : M → ℝ) hy]
    · rw [Sobolev.Chart.chartPushedRaw_apply_of_notMem
        (I := I) (M := M) (α := α) sumFun hy,
        Sobolev.Chart.chartPushedRaw_apply_of_notMem
          (I := I) (M := M) (α := α) ((F : Lp ℝ 2 _) : M → ℝ) hy,
        Sobolev.Chart.chartPushedRaw_apply_of_notMem
          (I := I) (M := M) (α := α) ((G : Lp ℝ 2 _) : M → ℝ) hy]
      ring
  filter_upwards [h_FG_coeFn, h_F_coeFn, h_G_coeFn, h_chartPushedRaw_FG]
    with y hy_FG hy_F hy_G hy_chart
  rw [hy_FG, hy_chart, h_chartPushedRaw_sum_pointwise y]
  rw [← hy_F, ← hy_G]

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartPushedRawLpFromLp_smoothMulLpRhoPreimage_coeFn_aeEq
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    ((chartPushedRawLpFromLp (I := I) (M := M) g α
        (smoothMulLpRhoPreimage (I := I) (M := M) g α hu_h) :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α))) : EuclN → ℝ)
      =ᵐ[(chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)]
      fChartPiecePreimage (I := I) (M := M) g α hu_h := by
  classical
  have h_coeFn := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α
    (smoothMulLpRhoPreimage (I := I) (M := M) g α hu_h)
  have h_smoothMulLp_ae : (smoothMulLpRhoPreimage (I := I) (M := M) g α hu_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x *
        ((laplacianDomain.preimage (I := I) (M := M) g
          ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h⟩ :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x) := by
    unfold smoothMulLpRhoPreimage
    exact smoothMulLp_apply_coeFn (I := I) (M := M) g _ _
  have h_smoothMul_meas :
      Measurable ((smoothMulLpRhoPreimage (I := I) (M := M) g α hu_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
    (Lp.stronglyMeasurable _).measurable
  have h_prod_meas :
      Measurable (fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x *
        ((laplacianDomain.preimage (I := I) (M := M) g
          ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h⟩ :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x) := by
    refine Measurable.mul ?_ ?_
    · exact ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff.continuous).measurable
    · exact (Lp.stronglyMeasurable _).measurable
  have h_chartPushedRaw_ae :
      Sobolev.Chart.chartPushedRaw (I := I) α
        ((smoothMulLpRhoPreimage (I := I) (M := M) g α hu_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)]
      Sobolev.Chart.chartPushedRaw (I := I) α
        (fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x *
          ((laplacianDomain.preimage (I := I) (M := M) g
            ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h⟩ :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x) :=
    CalabiYau.Analysis.Laplacian.LaplacianDomainChartData.chartPushedRaw_aeEq_of_aeEq
      (I := I) (M := M) g α h_smoothMul_meas h_prod_meas h_smoothMulLp_ae
  have h_chartTarget_meas : MeasurableSet
      (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
    (Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α).measurableSet
  have h_weighted_restrict_self :
      ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)),
      y ∈ Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α := by
    rw [ae_restrict_iff' h_chartTarget_meas]
    exact Filter.Eventually.of_forall (fun _ h => h)
  filter_upwards [h_coeFn, h_chartPushedRaw_ae, h_weighted_restrict_self]
    with y hy_coeFn hy_chart hy_in
  rw [hy_coeFn, hy_chart]
  unfold fChartPiecePreimage
  exact (Sobolev.Chart.chartPushed_eq_chartPushedRaw_pou_mul_on_target
    (I := I) (M := M) (chartAtlasPOU I M) α
    ((laplacianDomain.preimage (I := I) (M := M) g
      ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h⟩ :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) hy_in).symm

private lemma base_f_chart_ae_eq_piecePreimage_add_residual_chartPulled
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h)).fChart
      =ᵐ[(chartPulledWeightedMeasure (I := I) g α).restrict
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)]
      (fun y => fChartPiecePreimage (I := I) (M := M) g α hu_h y +
        ((chartPushedRawLpFromLp (I := I) (M := M) g α
            (fHLeibnizResidualLp (I := I) (M := M) g α u_h) :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (Sobolev.Chart.chartTargetEuclid
              (I := I) (M := M) α))) : EuclN → ℝ) y) := by
  classical
  have h_base_def := chartBilinearH1ComplData_of_laplacianDomain_f_chart_def
    (I := I) (M := M) g α
    (laplacianDomainPow_succ_subset_laplacianDomain
      (I := I) (M := M) g 1 hu_h)
  have h_fHLeibniz_decomp := fHLeibniz_eq_piecePreimage_add_residual
    (I := I) (M := M) g α hu_h
  have h_chartPushedRaw_add_ae :=
    chartPushedRawLpFromLp_coeFn_add (I := I) (M := M) g α
      (smoothMulLpRhoPreimage (I := I) (M := M) g α hu_h)
      (fHLeibnizResidualLp (I := I) (M := M) g α u_h)
  have h_piece1 := chartPushedRawLpFromLp_smoothMulLpRhoPreimage_coeFn_aeEq
    (I := I) (M := M) g α hu_h
  rw [h_base_def, h_fHLeibniz_decomp]
  filter_upwards [h_chartPushedRaw_add_ae, h_piece1] with y hy_add hy_piece1
  rw [hy_add, hy_piece1]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma vol_abs_chartPulledWeighted_on_chartTarget
    (g : SmoothRiemannianMetric I M) (α : M) :
    (volume : Measure EuclN).restrict
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) ≪
      (chartPulledWeightedMeasure (I := I) g α).restrict
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) := by
  intro A hA
  have h_chartTarget_meas : MeasurableSet
      (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
    (Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α).measurableSet
  unfold chartPulledWeightedMeasure at hA
  rw [show ((volume : Measure EuclN).withDensity
      (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))).restrict
      (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) =
      ((volume : Measure EuclN).restrict
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)).withDensity
        (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
    from MeasureTheory.restrict_withDensity h_chartTarget_meas _] at hA
  rw [MeasureTheory.withDensity_apply_eq_zero'
    (μ := (volume : Measure EuclN).restrict
      (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α))
    (f := fun y : EuclN => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
    (ENNReal.measurable_ofReal.comp_aemeasurable
      ((densityOnEuclid_continuousOn (I := I) g α).aemeasurable h_chartTarget_meas))]
    at hA
  rw [Measure.restrict_apply' h_chartTarget_meas]
  rw [Measure.restrict_apply' h_chartTarget_meas] at hA
  refine MeasureTheory.measure_mono_null ?_ hA
  intro y ⟨hy_A, hy_chart⟩
  refine ⟨⟨?_, hy_A⟩, hy_chart⟩
  have h_pos : 0 < densityOnEuclid (I := I) g α y :=
    densityOnEuclid_pos (I := I) g α hy_chart
  exact (ENNReal.ofReal_pos.mpr h_pos).ne'

lemma base_f_chart_ae_eq_piecePreimage_add_residual_chartPulled_on_vol
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h)).fChart
      =ᵐ[(volume : Measure EuclN).restrict
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)]
      (fun y => fChartPiecePreimage (I := I) (M := M) g α hu_h y +
        ((chartPushedRawLpFromLp (I := I) (M := M) g α
            (fHLeibnizResidualLp (I := I) (M := M) g α u_h) :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (Sobolev.Chart.chartTargetEuclid
              (I := I) (M := M) α))) : EuclN → ℝ) y) := by
  exact (vol_abs_chartPulledWeighted_on_chartTarget (I := I) (M := M) g α).ae_le
    (base_f_chart_ae_eq_piecePreimage_add_residual_chartPulled
      (I := I) (M := M) g α hu_h)

noncomputable def fChartResidual
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) : EuclN → ℝ :=
  ((chartPushedRawLpFromLp (I := I) (M := M) g α
      (fHLeibnizResidualLp (I := I) (M := M) g α u_h) :
    Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
      (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α))) : EuclN → ℝ)

lemma base_f_chart_memW1p_from_residual_memW1p
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_residual_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (fChartResidual (I := I) (M := M) g α u_h)
      (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α)) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).fChart
      (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  classical
  have h_decomp := base_f_chart_ae_eq_piecePreimage_add_residual_chartPulled_on_vol
    (I := I) (M := M) g α hu_h
  have h_piece1_memW1p := fChartPiecePreimage_memW1p (I := I) (M := M) g α hu_h
  have h_sum_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (fun y => fChartPiecePreimage (I := I) (M := M) g α hu_h y +
          fChartResidual (I := I) (M := M) g α u_h y)
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) :=
    Sobolev.Euclidean.MemW1p.add
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_piece1_memW1p h_residual_memW1p
  have hΩ : IsOpen
      (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
    Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  exact (Sobolev.Euclidean.MemW1p_congr_ae hΩ
    h_decomp.symm).mp h_sum_memW1p

noncomputable def diffChartBilinearH1ComplDataOfLaplacianDomainPowTwoOfResidualMemW1p
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (direction : Fin (Module.finrank ℝ E))
    (h_residual_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (fChartResidual (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α))
    (h_identity :
      ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                (chosenSecondPartialChartPushedU
                  (I := I) (M := M) g α u_h i direction) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).weakPartial direction y * ψ y
          ∂(volume : Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            chosenFChartDeriv (I := I) (M := M) g α hu_h direction y * ψ y
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α i j direction y *
                (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
                  (laplacianDomainPow_succ_subset_laplacianDomain
                    (I := I) (M := M) g 1 hu_h)).weakPartial i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α direction y *
            (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).uChart y * ψ y
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α direction y *
            (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).fChart y * ψ y
          ∂(volume : Measure EuclN))) :
    DiffChartBilinearH1ComplData (I := I) (M := M) g α :=
  diffChartBilinearH1ComplDataOfLaplacianDomainPowTwo
    (I := I) (M := M) g α hu_h direction
    (base_f_chart_memW1p_from_residual_memW1p
      (I := I) (M := M) g α hu_h h_residual_memW1p)
    h_identity

end DiffChartBilinearH1Compl
end Laplacian
end Analysis
end CalabiYau

end
