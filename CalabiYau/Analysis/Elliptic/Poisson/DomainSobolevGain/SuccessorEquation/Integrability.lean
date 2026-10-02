module

public import CalabiYau.Analysis.Elliptic.Poisson.DomainSobolevGain.SuccessorEquation.MixedIntegrationByParts

/-!
# Compact-test integrability for successor equation products

Proof-preserving extraction from the checked successor weak-equation assembly.
Source: DifferentialGeometry `7a48598d35109aa99d1cc678e2724c213cdf4ff3`,
`Iterated/VariationalIdentity/InductiveSuccessor.lean:579-640; MixedPartials.lean:144-258`.
The forcing is the actual `SuccessorSource` definition; no copied forcing definition is used.
-/

public section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace CalabiYau.PoissonDomainRegularity.SuccessorEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.Analysis.Laplacian
open CalabiYau.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open Sobolev.Euclidean
open CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl
open CalabiYau.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.DifferentiatedCrossTermIBP

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
    [SigmaCompactSpace M] in
lemma integrable_triple_helper
    {α : M} {K : Set EuclN}
    (hK_compact : IsCompact K)
    (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    {a : EuclN → ℝ}
    (ha : ContinuousOn a (chartTargetEuclid (I := I) (M := M) α))
    {u : EuclN → ℝ} (hu : IntegrableOn u K (volume : Measure EuclN))
    {h : EuclN → ℝ} (hh_cont : Continuous h) (hh_support : tsupport h ⊆ K) :
    Integrable (fun y => a y * u y * h y)
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hK_closed : IsClosed K := hK_compact.isClosed
  set h_prod : EuclN → ℝ := fun y => a y * h y
  have hh_prod_support : tsupport h_prod ⊆ K := by
    refine closure_minimal (fun y hy => ?_) hK_closed
    by_contra hy_notin
    have hh_y : h y = 0 := image_eq_zero_of_notMem_tsupport
      (fun h_in => hy_notin (hh_support h_in))
    have h_eq_zero : a y * h y = 0 := by rw [hh_y, mul_zero]
    exact hy h_eq_zero
  have hh_prod_cont : Continuous h_prod := by
    rw [continuous_iff_continuousAt]
    intro y
    by_cases hy : y ∈ K
    · exact (ha.continuousAt (hΩ_open.mem_nhds (hK_in hy))).mul hh_cont.continuousAt
    · have h_compl_open : IsOpen (Kᶜ) := hK_closed.isOpen_compl
      have h_eq_zero : ∀ᶠ z in 𝓝 y, h_prod z = 0 := by
        filter_upwards [h_compl_open.mem_nhds hy] with z hz
        have hh_z : h z = 0 := image_eq_zero_of_notMem_tsupport
          (fun h_in => hz (hh_support h_in))
        change a z * h z = 0; rw [hh_z, mul_zero]
      rw [continuousAt_congr h_eq_zero]; exact continuousAt_const
  have hh_prod_contOn_K : ContinuousOn h_prod K := hh_prod_cont.continuousOn
  have hu_h_int_K : IntegrableOn (fun y => u y * h_prod y) K
      (volume : Measure EuclN) :=
    hu.mul_continuousOn hh_prod_contOn_K hK_compact
  have h_vanish : ∀ y, y ∉ K → u y * h_prod y = 0 := by
    intro y hy
    have hp : h_prod y = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hy_support => hy (hh_prod_support hy_support))
    simp [hp]
  have h_eq_ind :
      (fun y => u y * h_prod y) = K.indicator (fun y => u y * h_prod y) := by
    funext y
    by_cases hy : y ∈ K
    · simp [Set.indicator_of_mem hy]
    · simp [Set.indicator_of_notMem hy, h_vanish y hy]
  have ind_int : Integrable (K.indicator (fun y => u y * h_prod y))
      (volume : Measure EuclN) :=
    (integrable_indicator_iff hK_meas).mpr hu_h_int_K
  have full_int : Integrable (fun y => u y * h_prod y) (volume : Measure EuclN) := by
    rw [h_eq_ind]; exact ind_int
  have h_reassoc : (fun y => u y * h_prod y) = (fun y => a y * u y * h y) := by
    funext y; change u y * (a y * h y) = _; ring
  rw [h_reassoc] at full_int
  exact full_int.restrict

omit [NeZero (Module.finrank ℝ E)] in
lemma chosenMthMixedPartialChartPushedU_locally_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ)
    (h_parent : MemWkp (d := Module.finrank ℝ E) m 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α))
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    {K : Set EuclN} (_hK : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (chosenMthMixedPartialChartPushedU g α u_h m dirs) 2
      ((volume : Measure EuclN).restrict K) := by
  exact (chosenMthMixedPartialChartPushedU_memLp_two g α u_h m h_parent dirs).mono_measure
    (Measure.restrict_mono_set _ hK_in)

theorem successor_sum_sum_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → κ → ℝ) (c : ℝ) :
    (∑ i, ∑ j, f i j) * c = ∑ i, ∑ j, f i j * c := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_mul _ _ _)

end CalabiYau.PoissonDomainRegularity.SuccessorEquation
