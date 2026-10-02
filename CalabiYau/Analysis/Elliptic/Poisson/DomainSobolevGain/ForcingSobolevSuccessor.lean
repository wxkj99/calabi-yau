module

public import CalabiYau.Analysis.Elliptic.Poisson.DomainSobolevGain.SuccessorSource
import CalabiYau.Analysis.Elliptic.Poisson.DomainSobolevGain.QuotientSobolevRegularity

/-!
# One descending Sobolev order of the compensated forcing

Adapted from DifferentialGeometry at `7a48598d35109aa99d1cc678e2724c213cdf4ff3`,
`Iterated/NirenbergInterior/EffectiveSourceSuccessorRegularity.lean`, lines 1045–1154.
For a fixed terminal order `r`, use `K = r - (m + 1)`. The required solution
order is then `m + 2 + K = r + 1`, not the target order `r + 2`.
-/

@[expose] public section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace CalabiYau.PoissonDomainRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.Analysis.Laplacian
open CalabiYau.Laplacian.MetricExtension hiding chartTargetEuclid chartTargetEuclid_isOpen
open Sobolev.Chart
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

variable [NeZero (Module.finrank ℝ E)] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem candidate_chosenPartial_ae_zero_on_open_sub
    {d : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω V : Set (EuclideanSpace ℝ (Fin d))}
    (hV : IsOpen V) (hV_sub : V ⊆ Ω)
    {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : Sobolev.Euclidean.MemW1p (d := d) p u Ω)
    (hu_zero : u =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin d))).restrict V]
      (fun _ => (0 : ℝ))) (i : Fin d) :
    Sobolev.Euclidean.chosenWeakPartialOrZero p i u Ω
      =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin d))).restrict V]
        (fun _ => (0 : ℝ)) := by
  classical
  have huV : Sobolev.Euclidean.MemW1p (d := d) p u V := by
    refine ⟨hu.1.mono_measure (Measure.restrict_mono_set _ hV_sub), ?_⟩
    intro j
    obtain ⟨g, hg, hw⟩ := hu.2 j
    exact ⟨g, hg.mono_measure (Measure.restrict_mono_set _ hV_sub),
      Sobolev.Euclidean.HasWeakPartialDeriv.restrict hV_sub hw⟩
  have hΩV := Sobolev.Euclidean.HasWeakPartialDeriv.restrict hV_sub
    (Sobolev.Euclidean.chosenWeakPartialOrZero_isWeakPartial_of_mem hu i)
  have hVweak := Sobolev.Euclidean.chosenWeakPartialOrZero_isWeakPartial_of_mem huV i
  have huniq := Sobolev.Euclidean.HasWeakPartialDeriv.ae_eq hV hΩV hVweak
    (((Sobolev.Euclidean.chosenWeakPartialOrZero_memLp_of_mem hu i).mono_measure
      (Measure.restrict_mono_set _ hV_sub)).locallyIntegrable hp)
    ((Sobolev.Euclidean.chosenWeakPartialOrZero_memLp_of_mem huV i).locallyIntegrable hp)
  exact huniq.trans
    (Sobolev.Euclidean.chosenWeakPartialOrZero_ae_zero_of_ae_zero hp hV hu_zero i)

private theorem candidate_mixedPartial_memWkp_of_chartPushed_memWkp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ) :
    ∀ (k : ℕ),
      Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) (k + m) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α) →
      ∀ (idx : Fin m → Fin (Module.finrank ℝ E)),
        Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) k 2
          (chosenMthMixedPartialChartPushedU g α u_h m idx)
          (chartTargetEuclid (I := I) (M := M) α) := by
  induction m with
  | zero =>
      intro k h_parent _idx
      simpa [chosenMthMixedPartialChartPushedU] using h_parent
  | succ m ih =>
      intro k h_parent idx
      have h_parent' : Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E)
          ((k + 1) + m) 2
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
            ((h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
          (chartTargetEuclid (I := I) (M := M) α) := by
        simpa only [Nat.add_assoc, Nat.add_comm 1 m] using h_parent
      exact (ih (k + 1) h_parent' (Fin.init idx)).chosenWeakPartial_mem
        (idx (Fin.last m))

private theorem candidate_selectedMixed_ae_zero_of_exact_chart_order
    (g : SmoothRiemannianMetric I M) (α : M) (u_h : H1Compl g) (m : ℕ) :
    Sobolev.Euclidean.MemWkp m 2
      (chartPushed (chartAtlasPOU I M) α ((h1ComplToLp g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) →
    ∀ dirs : Fin m → Fin (Module.finrank ℝ E),
      chosenMthMixedPartialChartPushedU g α u_h m dirs
        =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartImagePOUTsupport (I := I) (M := M) α)] (fun _ => (0 : ℝ)) := by
  induction m with
  | zero =>
      intro _h dirs
      have hV := (chartTargetEuclid_isOpen (I := I) (M := M) α).sdiff
        (chartImagePOUTsupport_isCompact (I := I) (M := M) α).isClosed
      refine (ae_restrict_iff' hV.measurableSet).mpr (Filter.Eventually.of_forall ?_)
      intro y hy
      exact chartPushed_eq_zero_off_chartImagePOUTsupport (I := I) (M := M) α _ hy.1 hy.2
  | succ m ih =>
      intro h dirs
      have h_inner := Sobolev.Euclidean.MemWkp.one_iff_memW1p.mp
        (candidate_mixedPartial_memWkp_of_chartPushed_memWkp g α u_h m 1
          (by simpa only [Nat.add_comm] using h.le_of_le (by omega)) (Fin.init dirs))
      have h_low : Sobolev.Euclidean.MemWkp m 2
          (chartPushed (chartAtlasPOU I M) α ((h1ComplToLp g u_h) : M → ℝ))
          (chartTargetEuclid (I := I) (M := M) α) :=
        h.le_of_le (by omega)
      exact candidate_chosenPartial_ae_zero_on_open_sub
        (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        ((chartTargetEuclid_isOpen (I := I) (M := M) α).sdiff
          (chartImagePOUTsupport_isCompact (I := I) (M := M) α).isClosed)
        Set.sdiff_subset h_inner (ih h_low (Fin.init dirs)) (dirs (Fin.last m))

/-- Source-faithful forcing regularity with the exact finite solution order. -/
theorem successorChartForcing_memWkp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m K : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (previousForcing : EuclN → ℝ) (l : Fin (Module.finrank ℝ E))
    (h_previous_memWkp : Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (K + 1) 2 previousForcing
      (chartTargetEuclid (I := I) (M := M) α))
    (h_previous_ae_zero :
      previousForcing =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)))
    (h_chart_H_u : Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 2 + K) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α)) :
    Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) K 2
      (successorChartForcing g α u_h m dirs previousForcing l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  let Ω := chartTargetEuclid (I := I) (M := M) α
  let C := chartImagePOUTsupport (I := I) (M := M) α
  have hΩopen : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hCc : IsCompact C := chartImagePOUTsupport_isCompact (I := I) (M := M) α
  have hCΩ : C ⊆ Ω := chartImagePOUTsupport_subset_target (I := I) (M := M) α
  have hquot := successorChartForcingQuotient_memWkp g α u_h m K dirs
    previousForcing l h_previous_memWkp h_previous_ae_zero h_chart_H_u
  have hq1 : Sobolev.Euclidean.MemW1p (d := Module.finrank ℝ E) 2 previousForcing Ω :=
    Sobolev.Euclidean.MemWkp.one_iff_memW1p.mp
      (h_previous_memWkp.le_of_le (by omega))
  have hX : ∀ (i j : Fin (Module.finrank ℝ E)), chosenMthMixedPartialChartPushedU g α u_h (m + 1)
      (Fin.cons i dirs) =ᵐ[(volume : Measure EuclN).restrict (Ω \ C)] (fun _ => 0) := by
    intro i j
    exact candidate_selectedMixed_ae_zero_of_exact_chart_order g α u_h (m + 1)
      (h_chart_H_u.le_of_le (by omega)) (Fin.cons i dirs)
  have hY : ∀ i j, chosenMthMixedPartialChartPushedU g α u_h (m + 2)
      (Fin.cons i (Fin.snoc dirs j)) =ᵐ[(volume : Measure EuclN).restrict (Ω \ C)]
        (fun _ => 0) := by
    intro i j
    exact candidate_selectedMixed_ae_zero_of_exact_chart_order g α u_h (m + 2)
      (h_chart_H_u.le_of_le (by omega)) (Fin.cons i (Fin.snoc dirs j))
  have hZ : chosenMthMixedPartialChartPushedU g α u_h m dirs
      =ᵐ[(volume : Measure EuclN).restrict (Ω \ C)] (fun _ => 0) :=
    candidate_selectedMixed_ae_zero_of_exact_chart_order g α u_h m
      (h_chart_H_u.le_of_le (by omega)) dirs
  have hnum_zero : successorChartForcingNumerator g α u_h m dirs previousForcing l
      =ᵐ[(volume : Measure EuclN).restrict (Ω \ C)] (fun _ => 0) := by
    exact successor_numerator_ae_zero hΩopen hCc.isClosed
      (fun i j y => (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
        (EuclideanSpace.single j 1))
      (fun i j => weightedInvGramDerivOnEuclid (I := I) g α i j l)
      (fun i _ => chosenMthMixedPartialChartPushedU g α u_h (m + 1) (Fin.cons i dirs))
      (fun i j => chosenMthMixedPartialChartPushedU g α u_h (m + 2)
        (Fin.cons i (Fin.snoc dirs j)))
      (densityDerivOnEuclid (I := I) g α l) (densityOnEuclid (I := I) g α)
      (chosenMthMixedPartialChartPushedU g α u_h m dirs) previousForcing hq1 l
      (fun i j => hX i j) hY hZ h_previous_ae_zero
  have hquot_zero : (fun y => successorChartForcingNumerator g α u_h m dirs previousForcing l y /
        densityOnEuclid (I := I) g α y)
      =ᵐ[(volume : Measure EuclN).restrict (Ω \ C)] (fun _ => (0 : ℝ)) := by
    filter_upwards [hnum_zero] with y hy
    rw [hy, zero_div]
  have hzvol : ∀ᵐ y ∂(volume : Measure EuclN), y ∈ Ω \ C →
      successorChartForcingNumerator g α u_h m dirs previousForcing l y /
        densityOnEuclid (I := I) g α y = 0 :=
    (ae_restrict_iff' (hΩopen.measurableSet.diff hCc.isClosed.measurableSet)).mp hquot_zero
  have hAE : (fun y => Set.indicator C
      (fun y => successorChartForcingNumerator g α u_h m dirs previousForcing l y /
        densityOnEuclid (I := I) g α y) y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
        (fun y => successorChartForcingNumerator g α u_h m dirs previousForcing l y /
          densityOnEuclid (I := I) g α y) := by
    apply (ae_restrict_iff' hΩopen.measurableSet).mpr
    filter_upwards [hzvol] with y hy
    intro hyΩ
    by_cases hyC : y ∈ C
    · simp [Set.indicator_of_mem hyC]
    · rw [Set.indicator_of_notMem hyC, hy ⟨hyΩ, hyC⟩]
  exact (Sobolev.Euclidean.MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩopen hAE).mpr hquot

/-- The indicator guarantees AE-zero off support without any regularity hypothesis. -/
theorem successorChartForcing_ae_zero_off_support
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (previousForcing : EuclN → ℝ) (l : Fin (Module.finrank ℝ E)) :
    successorChartForcing g α u_h m dirs previousForcing l
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)) := by
  have h_meas : MeasurableSet
      (chartTargetEuclid (I := I) (M := M) α \
        chartImagePOUTsupport (I := I) (M := M) α) :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet.diff
      (chartImagePOUTsupport_isCompact (I := I) (M := M) α).isClosed.measurableSet
  refine (ae_restrict_iff' h_meas).mpr ?_
  exact Filter.Eventually.of_forall fun y hy =>
    Set.indicator_of_notMem hy.2 _

end CalabiYau.PoissonDomainRegularity
