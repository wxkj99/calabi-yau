module

public import Comparator.PoissonSolvability.DomainSobolevGain.SuccessorEquation.MixedIntegrationByParts

/-!
# Almost-everywhere support of selected chart partials and density cancellation

Proof-preserving extraction from the checked successor weak-equation assembly.
Source: DifferentialGeometry `7a48598d35109aa99d1cc678e2724c213cdf4ff3`,
`Iterated/VariationalIdentity/InductiveSuccessor.lean:124-249; SuccessorSource.lean:251-339`.
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

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma chosenWeakPartialOrZero_ae_zero_on_open_subset_of_ae_zero
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω V : Set EuclN}
    (_hΩ : IsOpen Ω) (hV : IsOpen V) (hV_sub : V ⊆ Ω)
    {u : EuclN → ℝ}
    (hu : DeGiorgi.MemW1p (d := Module.finrank ℝ E) p u Ω)
    (hu_ae_zero_V : u =ᵐ[(volume : Measure EuclN).restrict V] (fun _ => (0 : ℝ)))
    (i : Fin (Module.finrank ℝ E)) :
    chosenWeakPartialOrZero (d := Module.finrank ℝ E) p i u Ω
      =ᵐ[(volume : Measure EuclN).restrict V] (fun _ : EuclN => (0 : ℝ)) := by
  classical
  have hu_V : DeGiorgi.MemW1p (d := Module.finrank ℝ E) p u V := by
    refine ⟨?_, ?_⟩
    · exact hu.1.mono_measure
        (MeasureTheory.Measure.restrict_mono_set _ hV_sub)
    · intro j
      obtain ⟨g, hg_memLp, hg_weak⟩ := hu.2 j
      refine ⟨g, ?_, ?_⟩
      · exact hg_memLp.mono_measure
          (MeasureTheory.Measure.restrict_mono_set _ hV_sub)
      · exact DeGiorgi.HasWeakPartialDeriv.restrict hV hV_sub hg_weak
  have h_partial_V : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (chosenWeakPartialOrZero (d := Module.finrank ℝ E) p i u V) u V :=
    chosenWeakPartialOrZero_isWeakPartial_of_mem hu_V i
  have h_partial_Ω : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (chosenWeakPartialOrZero (d := Module.finrank ℝ E) p i u Ω) u Ω :=
    chosenWeakPartialOrZero_isWeakPartial_of_mem hu i
  have h_partial_Ω_V : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (chosenWeakPartialOrZero (d := Module.finrank ℝ E) p i u Ω) u V :=
    DeGiorgi.HasWeakPartialDeriv.restrict hV hV_sub h_partial_Ω
  have h_chosen_V_zero :
      chosenWeakPartialOrZero (d := Module.finrank ℝ E) p i u V
        =ᵐ[(volume : Measure EuclN).restrict V] (fun _ : EuclN => (0 : ℝ)) :=
    chosenWeakPartialOrZero_ae_zero_of_ae_zero (d := Module.finrank ℝ E)
      hp hV hu_ae_zero_V i
  have hg_lp_Ω : MemLp (chosenWeakPartialOrZero (d := Module.finrank ℝ E) p i u Ω) p
      ((volume : Measure EuclN).restrict Ω) :=
    chosenWeakPartialOrZero_memLp_of_mem hu i
  have hg_lp_Ω_V : MemLp (chosenWeakPartialOrZero (d := Module.finrank ℝ E) p i u Ω) p
      ((volume : Measure EuclN).restrict V) :=
    hg_lp_Ω.mono_measure (MeasureTheory.Measure.restrict_mono_set _ hV_sub)
  have hg_local_Ω_V : LocallyIntegrable
      (chosenWeakPartialOrZero (d := Module.finrank ℝ E) p i u Ω)
      ((volume : Measure EuclN).restrict V) :=
    hg_lp_Ω_V.locallyIntegrable hp
  have hgV_lp : MemLp (chosenWeakPartialOrZero (d := Module.finrank ℝ E) p i u V) p
      ((volume : Measure EuclN).restrict V) :=
    chosenWeakPartialOrZero_memLp_of_mem hu_V i
  have hgV_local : LocallyIntegrable
      (chosenWeakPartialOrZero (d := Module.finrank ℝ E) p i u V)
      ((volume : Measure EuclN).restrict V) :=
    hgV_lp.locallyIntegrable hp
  have h_unique :
      chosenWeakPartialOrZero (d := Module.finrank ℝ E) p i u Ω
        =ᵐ[(volume : Measure EuclN).restrict V]
        chosenWeakPartialOrZero (d := Module.finrank ℝ E) p i u V :=
    DeGiorgi.HasWeakPartialDeriv.ae_eq hV h_partial_Ω_V h_partial_V
      hg_local_Ω_V hgV_local
  exact h_unique.trans h_chosen_V_zero

omit [NeZero (Module.finrank ℝ E)] in
lemma chartPushed_u_h_ae_zero_off_chartImagePOUTsupport
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) :
    chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) := by
  have h_diff_open : IsOpen
      (chartTargetEuclid (I := I) (M := M) α \
        chartImagePOUTsupport (I := I) (M := M) α) :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).sdiff
      (chartImagePOUTsupport_isCompact (I := I) (M := M) α).isClosed
  refine (ae_restrict_iff' h_diff_open.measurableSet).mpr ?_
  refine Filter.Eventually.of_forall ?_
  intro y hy
  exact chartPushed_eq_zero_off_chartImagePOUTsupport
    (I := I) (M := M) α _ hy.1 hy.2

omit [NeZero (Module.finrank ℝ E)] in
lemma chosenMthMixedPartialChartPushedU_ae_zero_off_chartImagePOUTsupport
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ) :
    ∀ (_h_parent : MemWkp (d := Module.finrank ℝ E) m 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α))
    (idx : Fin m → Fin (Module.finrank ℝ E)),
      chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m idx
        =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartImagePOUTsupport (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)) := by
  induction m with
  | zero =>
      intro _h_parent _idx
      simpa [chosenMthMixedPartialChartPushedU] using
        chartPushed_u_h_ae_zero_off_chartImagePOUTsupport
          (I := I) (M := M) g α u_h
  | succ m ih =>
      intro h_parent idx
      have h_parent_m : MemWkp (d := Module.finrank ℝ E) m 2
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
            ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
          (chartTargetEuclid (I := I) (M := M) α) := h_parent.le_succ
      have h_inner_ae := ih h_parent_m (Fin.init idx)
      have h_inner_memWkp : MemWkp (d := Module.finrank ℝ E) 1 2
          (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m
            (Fin.init idx))
          (chartTargetEuclid (I := I) (M := M) α) := by
        have h_parent_m_plus_1 : MemWkp (d := Module.finrank ℝ E) (1 + m) 2
            (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
              ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
            (chartTargetEuclid (I := I) (M := M) α) := by
          rw [Nat.add_comm]
          exact h_parent
        exact chosenMthMixedPartialChartPushedU_memWkp_of_chartPushed_memWkp
          (I := I) (M := M) g α u_h m 1 h_parent_m_plus_1 (Fin.init idx)
      have h_inner_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
          (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m
            (Fin.init idx))
          (chartTargetEuclid (I := I) (M := M) α) := by
        rw [MemWkp.one_iff_memW1p] at h_inner_memWkp
        exact h_inner_memWkp
      have h_diff_open : IsOpen
          (chartTargetEuclid (I := I) (M := M) α \
            chartImagePOUTsupport (I := I) (M := M) α) :=
        (chartTargetEuclid_isOpen (I := I) (M := M) α).sdiff
          (chartImagePOUTsupport_isCompact (I := I) (M := M) α).isClosed
      have h_diff_subset : chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α ⊆
            chartTargetEuclid (I := I) (M := M) α := fun _ hy => hy.1
      have h_step :=
        chosenWeakPartialOrZero_ae_zero_on_open_subset_of_ae_zero
          (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
          (chartTargetEuclid_isOpen (I := I) (M := M) α)
          h_diff_open h_diff_subset
          h_inner_memW1p h_inner_ae (idx (Fin.last m))
      exact h_step

omit [NeZero (Module.finrank ℝ E)] in
theorem density_mul_successorChartForcing_eq_indicator_numerator
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (fChartEffectivePrev : EuclN → ℝ)
    (l : Fin (Module.finrank ℝ E))
    (y : EuclN)
    (hy : y ∈ Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α) :
    densityOnEuclid (I := I) g α y *
        successorChartForcing (I := I) (M := M) g α u_h m dirs fChartEffectivePrev l y =
      Set.indicator (chartImagePOUTsupport (I := I) (M := M) α)
        (fun z => successorChartForcingNumerator
          (I := I) (M := M) g α u_h m dirs fChartEffectivePrev l z) y := by
  classical
  unfold successorChartForcing
  by_cases hy_K : y ∈ chartImagePOUTsupport (I := I) (M := M) α
  · rw [Set.indicator_of_mem hy_K, Set.indicator_of_mem hy_K]
    have h_pos : 0 < densityOnEuclid (I := I) g α y :=
      densityOnEuclid_pos (I := I) g α hy
    field_simp
  · rw [Set.indicator_of_notMem hy_K, Set.indicator_of_notMem hy_K, mul_zero]

end CalabiYau.PoissonDomainRegularity.SuccessorEquation
