-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Manifold/Rellich/OnManifold.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Manifold.Rellich.Compactness
public import CalabiYau.Analysis.Sobolev.Manifold.Measure.UniformChartComparison

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [T2Space M] [CompactSpace M]

variable [I.Boundaryless] in
private noncomputable def chartCompactM (α : M) :
    Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
  toEuclidean ''
    ((extChartAt I α) ''
      (tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ)))

private lemma extChartAt_image_tsupport_pou_compact_subset_target (α : M) :
    IsCompact ((extChartAt I α) ''
        (tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ))) ∧
      (extChartAt I α) ''
        (tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ)) ⊆
        (extChartAt I α).target := by
  have hsubord :
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M).IsSubordinate
        (fun α : M => (chartAt H α).source) :=
    CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate (I := I) (M := M)
  have hsupp_sub : tsupport
      ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆
      (chartAt H α).source := hsubord α
  exact image_extChartAt_tsupport_compact_subset_target
    (I := I) (M := M)
    (u := ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
      : M → ℝ))
    (α := α) hsupp_sub

private lemma chartCompactM_isCompact (α : M) :
    IsCompact (chartCompactM (I := I) (M := M) α) := by
  unfold chartCompactM
  exact (extChartAt_image_tsupport_pou_compact_subset_target
    (I := I) (M := M) α).1.image (toEuclidean (E := E)).continuous

private lemma chartCompactM_subset_chartTargetEuclid (α : M) :
    chartCompactM (I := I) (M := M) α ⊆ chartTargetEuclid (I := I) (M := M) α := by
  unfold chartCompactM chartTargetEuclid
  rintro y ⟨z, hz, rfl⟩
  refine ⟨z, ?_, rfl⟩
  exact (extChartAt_image_tsupport_pou_compact_subset_target
    (I := I) (M := M) α).2 hz

section

variable [I.Boundaryless]
private noncomputable def chartThickeningRadiusM (α : M) : ℝ :=
  ((chartCompactM_isCompact (I := I) (M := M) α).exists_thickening_subset_open
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (chartCompactM_subset_chartTargetEuclid (I := I) (M := M) α)).choose

private lemma chartThickeningRadiusM_pos (α : M) :
    0 < chartThickeningRadiusM (I := I) (M := M) α :=
  ((chartCompactM_isCompact (I := I) (M := M) α).exists_thickening_subset_open
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (chartCompactM_subset_chartTargetEuclid (I := I) (M := M) α)).choose_spec.1

private lemma chartThickeningRadiusM_subset (α : M) :
    Metric.thickening (chartThickeningRadiusM (I := I) (M := M) α)
        (chartCompactM (I := I) (M := M) α) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
  ((chartCompactM_isCompact (I := I) (M := M) α).exists_thickening_subset_open
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (chartCompactM_subset_chartTargetEuclid (I := I) (M := M) α)).choose_spec.2

private noncomputable def chartNeighborhoodM (α : M) :
    Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
  Metric.thickening (chartThickeningRadiusM (I := I) (M := M) α)
    (chartCompactM (I := I) (M := M) α)

private lemma chartNeighborhoodM_isOpen (α : M) :
    IsOpen (chartNeighborhoodM (I := I) (M := M) α) :=
  Metric.isOpen_thickening

private lemma chartNeighborhoodM_isBounded (α : M) :
    Bornology.IsBounded (chartNeighborhoodM (I := I) (M := M) α) :=
  (chartCompactM_isCompact (I := I) (M := M) α).isBounded.thickening

private lemma chartNeighborhoodM_subset_chartTargetEuclid (α : M) :
    chartNeighborhoodM (I := I) (M := M) α ⊆ chartTargetEuclid (I := I) (M := M) α :=
  chartThickeningRadiusM_subset (I := I) (M := M) α

private lemma chartCompactM_subset_chartNeighborhoodM (α : M) :
    chartCompactM (I := I) (M := M) α ⊆ chartNeighborhoodM (I := I) (M := M) α :=
  Metric.self_subset_thickening
    (chartThickeningRadiusM_pos (I := I) (M := M) α)
    (chartCompactM (I := I) (M := M) α)

end

private lemma chartPushedRaw_pou_mul_eq_zero_off_chartCompactM
    (α : M) (u : M → ℝ)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∉ chartCompactM (I := I) (M := M) α) :
    chartPushedRaw (I := I) (M := M) α
      (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x) y = 0 := by
  classical
  by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
  · have hsmul :
        tsupport (fun x : M =>
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x) ⊆
          tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
      have h_eq : (fun x : M =>
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x) =
          (fun x : M =>
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) x • u x) := by
        funext x; rfl
      rw [h_eq]
      exact tsupport_smul_subset_left
        (f := fun x : M => ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) (g := u)
    apply chartPushedRaw_eq_zero_off_image_tsupport
      (I := I) (M := M)
      (u := fun x : M => ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * u x)
      (α := α) hy_target
    intro hcontra
    apply hy
    obtain ⟨z, hz_chart_image, hzy⟩ := hcontra
    obtain ⟨x, hx_support, hxz⟩ := hz_chart_image
    refine ⟨z, ⟨x, ?_, hxz⟩, hzy⟩
    exact hsmul hx_support
  · exact chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy_target

variable [I.Boundaryless] in
private lemma chartPushedRaw_pou_mul_tsupport_subset_chartNeighborhoodM
    (α : M) (u : M → ℝ) :
    tsupport (chartPushedRaw (I := I) (M := M) α
      (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x)) ⊆
      chartNeighborhoodM (I := I) (M := M) α := by
  have h_support_sub :
      Function.support (chartPushedRaw (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x)) ⊆
        chartCompactM (I := I) (M := M) α := by
    intro y hy
    by_contra hcontra
    apply hy
    exact chartPushedRaw_pou_mul_eq_zero_off_chartCompactM
      (I := I) (M := M) α u hcontra
  have h_compact_closed : IsClosed (chartCompactM (I := I) (M := M) α) :=
    (chartCompactM_isCompact (I := I) (M := M) α).isClosed
  have h_tsupp_sub :
      tsupport (chartPushedRaw (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x)) ⊆
        chartCompactM (I := I) (M := M) α := by
    rw [tsupport]
    exact h_compact_closed.closure_subset_iff.mpr h_support_sub
  exact h_tsupp_sub.trans (chartCompactM_subset_chartNeighborhoodM (I := I) (M := M) α)

private lemma chartPushedRaw_pou_mul_hasCompactSupport_aux
    (α : M) (u : M → ℝ) :
    HasCompactSupport (chartPushedRaw (I := I) (M := M) α
      (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x)) := by
  have h_support_sub :
      Function.support (chartPushedRaw (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x)) ⊆
        chartCompactM (I := I) (M := M) α := by
    intro y hy
    by_contra hcontra
    apply hy
    exact chartPushedRaw_pou_mul_eq_zero_off_chartCompactM
      (I := I) (M := M) α u hcontra
  have h_compact_closed : IsClosed (chartCompactM (I := I) (M := M) α) :=
    (chartCompactM_isCompact (I := I) (M := M) α).isClosed
  have h_tsupp_sub :
      tsupport (chartPushedRaw (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x)) ⊆
        chartCompactM (I := I) (M := M) α := by
    rw [tsupport]
    exact h_compact_closed.closure_subset_iff.mpr h_support_sub
  exact (chartCompactM_isCompact (I := I) (M := M) α).of_isClosed_subset
    isClosed_closure h_tsupp_sub

section

variable [I.Boundaryless]
private lemma memW1p_chartPushedRaw_pou_mul_chartNeighborhoodM
    {p : ℝ≥0∞}
    {u : M → ℝ}
    (hu : MemWkpChart (I := I) (M := M) 1 p u)
    (α : M) :
    Sobolev.Euclidean.MemW1p (d := Module.finrank ℝ E) p
      (chartPushedRaw (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x))
      (chartNeighborhoodM (I := I) (M := M) α) := by
  have h_target := memW1p_chartPushedRaw_pou_mul_of_memWkpChart
    (I := I) (M := M) hu α
  have hwT : Sobolev.Euclidean.MemW1pWitness (d := Module.finrank ℝ E) p
      (chartPushedRaw (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x))
      (chartTargetEuclid (I := I) (M := M) α) :=
    Sobolev.Euclidean.MemW1p.someWitness h_target
  have hwN : Sobolev.Euclidean.MemW1pWitness (d := Module.finrank ℝ E) p
      (chartPushedRaw (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x))
      (chartNeighborhoodM (I := I) (M := M) α) :=
    hwT.restrict
      (chartNeighborhoodM_subset_chartTargetEuclid (I := I) (M := M) α)
  exact hwN.memW1p

private lemma memW01p_chartPushedRaw_pou_mul_chartNeighborhoodM
    [NeZero (Module.finrank ℝ E)]
    {p : ℝ} (hp_one : 1 < p)
    {u : M → ℝ}
    (hu : MemWkpChart (I := I) (M := M) 1 (ENNReal.ofReal p) u)
    (α : M) :
    Sobolev.Euclidean.MemW01p (d := Module.finrank ℝ E) (ENNReal.ofReal p)
      (chartPushedRaw (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x))
      (chartNeighborhoodM (I := I) (M := M) α) := by
  have h_w1p := memW1p_chartPushedRaw_pou_mul_chartNeighborhoodM
    (I := I) (M := M) hu α
  have h_support := chartPushedRaw_pou_mul_tsupport_subset_chartNeighborhoodM
    (I := I) (M := M) α u
  have h_compact := chartPushedRaw_pou_mul_hasCompactSupport_aux
    (I := I) (M := M) α u
  exact Sobolev.Euclidean.memW01p_of_memW1p_of_tsupport_subset
    (chartNeighborhoodM_isOpen (I := I) (M := M) α) hp_one h_w1p h_compact h_support

private lemma eLpNorm_chartPushedRaw_pou_mul_chartNeighborhoodM_le
    {p : ℝ≥0∞} (u : M → ℝ) (α : M) :
    eLpNorm (chartPushedRaw (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x)) p
        ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartNeighborhoodM (I := I) (M := M) α)) ≤
      eLpNorm (chartPushedRaw (I := I) (M := M) α
          (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x)) p
        ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
  refine eLpNorm_mono_measure _ ?_
  exact MeasureTheory.Measure.restrict_mono_set _
    (chartNeighborhoodM_subset_chartTargetEuclid (I := I) (M := M) α)

private lemma exists_chart_rellich_subseq_aux_M
    [NeZero (Module.finrank ℝ E)]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {p : ℝ} (hp_one : 1 < p)
    {u : ℕ → M → ℝ}
    (hu_mem : ∀ n, MemWkpChart (I := I) (M := M) 1 (ENNReal.ofReal p) (u n))
    {R : ℝ}
    (hu_bdd : ∀ n, wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p) (u n) ≤
      ENNReal.ofReal R)
    (α : M) (ψ : ℕ → ℕ) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ w_α : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ,
        MemLp w_α (ENNReal.ofReal p)
            ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (chartNeighborhoodM (I := I) (M := M) α)) ∧
        Filter.Tendsto
          (fun k => eLpNorm
              (fun y => chartPushedRaw (I := I) (M := M) α
                (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
                  : C^∞⟮I, M; ℝ⟯) x * u (ψ (σ k)) x) y - w_α y)
              (ENNReal.ofReal p)
              ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
                (chartNeighborhoodM (I := I) (M := M) α)))
          Filter.atTop (𝓝 0) := by
  classical
  set v : ℕ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ := fun n =>
    chartPushedRaw (I := I) (M := M) α
      (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u (ψ n) x) with hv_def
  have hv_mem : ∀ n, Sobolev.Euclidean.MemW01p (d := Module.finrank ℝ E) (ENNReal.ofReal p)
      (v n) (chartNeighborhoodM (I := I) (M := M) α) := by
    intro n
    exact memW01p_chartPushedRaw_pou_mul_chartNeighborhoodM
      (I := I) (M := M) hp_one (hu_mem (ψ n)) α
  have hv_bdd_fun : ∀ n, eLpNorm (v n) (ENNReal.ofReal p)
      ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
        (chartNeighborhoodM (I := I) (M := M) α)) ≤ ENNReal.ofReal R := by
    intro n
    have h_step1 : eLpNorm (v n) (ENNReal.ofReal p)
        ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartNeighborhoodM (I := I) (M := M) α)) ≤
        eLpNorm (v n) (ENNReal.ofReal p)
          ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
      rw [hv_def]
      exact eLpNorm_chartPushedRaw_pou_mul_chartNeighborhoodM_le
        (I := I) (M := M) (u := u (ψ n)) α
    have h_step2 : eLpNorm (v n) (ENNReal.ofReal p)
        ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartTargetEuclid (I := I) (M := M) α)) =
        eLpNorm (chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α (u (ψ n)))
          (ENNReal.ofReal p)
          ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
      rw [hv_def]
      exact eLpNorm_chartPushedRaw_pou_mul_eq_chartPushed
        (I := I) (M := M) g (u (ψ n)) α
    rw [h_step2] at h_step1
    refine h_step1.trans ?_
    exact (eLpNorm_chartPushed_le_wkpNormChart
      (I := I) (M := M) (u (ψ n)) α).trans
      (hu_bdd (ψ n))
  have hv_bdd_grad : ∀ n,
      ∑ i : Fin (Module.finrank ℝ E),
        eLpNorm (fun x => (Classical.choose (hv_mem n).2).weakGrad x i)
          (ENNReal.ofReal p)
          ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
            (chartNeighborhoodM (I := I) (M := M) α)) ≤ ENNReal.ofReal R := by
    intro n
    refine le_trans ?_ (hu_bdd (ψ n))
    have hp_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
      simpa using (ENNReal.ofReal_le_ofReal hp_one.le :
        ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal p)
    have h_term_bound : ∀ i : Fin (Module.finrank ℝ E),
        eLpNorm (fun x => (Classical.choose (hv_mem n).2).weakGrad x i)
            (ENNReal.ofReal p)
            ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (chartNeighborhoodM (I := I) (M := M) α)) ≤
          eLpNorm
            (Sobolev.Euclidean.chosenWeakPartialOrZero
              (d := Module.finrank ℝ E) (ENNReal.ofReal p) i
              (chartPushed (I := I) (M := M)
                (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α (u (ψ n)))
              (chartTargetEuclid (I := I) (M := M) α)) (ENNReal.ofReal p)
            ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (chartTargetEuclid (I := I) (M := M) α)) := by
      intro i
      have hChart_w1p :
          Sobolev.Euclidean.MemW1p (d := Module.finrank ℝ E) (ENNReal.ofReal p)
            (chartPushed (I := I) (M := M)
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α (u (ψ n)))
            (chartTargetEuclid (I := I) (M := M) α) := by
        have h := (hu_mem (ψ n)) α
        exact Sobolev.Euclidean.MemWkp.one_iff_memW1p.mp h
      have hChart_chosen_isWeak :
          Sobolev.Euclidean.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
            (Sobolev.Euclidean.chosenWeakPartialOrZero
              (d := Module.finrank ℝ E) (ENNReal.ofReal p) i
              (chartPushed (I := I) (M := M)
                (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α (u (ψ n)))
              (chartTargetEuclid (I := I) (M := M) α))
            (chartPushed (I := I) (M := M)
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α (u (ψ n)))
            (chartTargetEuclid (I := I) (M := M) α) :=
        Sobolev.Euclidean.chosenWeakPartialOrZero_isWeakPartial_of_mem
          hChart_w1p i
      have hChart_chosen_isWeak_NeighborhoodM :
          Sobolev.Euclidean.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
            (Sobolev.Euclidean.chosenWeakPartialOrZero
              (d := Module.finrank ℝ E) (ENNReal.ofReal p) i
              (chartPushed (I := I) (M := M)
                (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α (u (ψ n)))
              (chartTargetEuclid (I := I) (M := M) α))
            (chartPushed (I := I) (M := M)
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α (u (ψ n)))
            (chartNeighborhoodM (I := I) (M := M) α) :=
        Sobolev.Euclidean.HasWeakPartialDeriv.restrict
          (chartNeighborhoodM_subset_chartTargetEuclid (I := I) (M := M) α)
          hChart_chosen_isWeak
      have h_full := chartPushed_eq_chartPushedRaw_pou_ae (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α (u (ψ n))
      have h_restrict_le : (volume :
          Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartNeighborhoodM (I := I) (M := M) α) ≤
        (volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartTargetEuclid (I := I) (M := M) α) :=
        MeasureTheory.Measure.restrict_mono_set _
          (chartNeighborhoodM_subset_chartTargetEuclid (I := I) (M := M) α)
      have h_ae_NeighborhoodM :
          chartPushed (I := I) (M := M)
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α (u (ψ n))
            =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (chartNeighborhoodM (I := I) (M := M) α)]
            chartPushedRaw (I := I) (M := M) α
              (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
                : C^∞⟮I, M; ℝ⟯) x * u (ψ n) x) :=
        h_full.filter_mono (MeasureTheory.ae_mono h_restrict_le)
      have hChart_chosen_isWeak_raw :
          Sobolev.Euclidean.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
            (Sobolev.Euclidean.chosenWeakPartialOrZero
              (d := Module.finrank ℝ E) (ENNReal.ofReal p) i
              (chartPushed (I := I) (M := M)
                (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α (u (ψ n)))
              (chartTargetEuclid (I := I) (M := M) α))
            (chartPushedRaw (I := I) (M := M) α
              (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
                : C^∞⟮I, M; ℝ⟯) x * u (ψ n) x))
            (chartNeighborhoodM (I := I) (M := M) α) :=
        Sobolev.Euclidean.hasWeakPartialDeriv_congr_ae i h_ae_NeighborhoodM
          hChart_chosen_isWeak_NeighborhoodM
      have hWit_isWeak := (Classical.choose (hv_mem n).2).isWeakGrad i
      have hWit_local :=
        ((Classical.choose (hv_mem n).2).weakGrad_component_memLp i).locallyIntegrable hp_le
      have hChosen_memLp :
          MemLp
            (Sobolev.Euclidean.chosenWeakPartialOrZero
              (d := Module.finrank ℝ E) (ENNReal.ofReal p) i
              (chartPushed (I := I) (M := M)
                (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α (u (ψ n)))
              (chartTargetEuclid (I := I) (M := M) α)) (ENNReal.ofReal p)
            ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (chartTargetEuclid (I := I) (M := M) α)) :=
        Sobolev.Euclidean.chosenWeakPartialOrZero_memLp_of_mem
          hChart_w1p i
      have hChosen_memLp_NeighborhoodM :
          MemLp
            (Sobolev.Euclidean.chosenWeakPartialOrZero
              (d := Module.finrank ℝ E) (ENNReal.ofReal p) i
              (chartPushed (I := I) (M := M)
                (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α (u (ψ n)))
              (chartTargetEuclid (I := I) (M := M) α)) (ENNReal.ofReal p)
            ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (chartNeighborhoodM (I := I) (M := M) α)) :=
        hChosen_memLp.mono_measure
          (MeasureTheory.Measure.restrict_mono_set _
            (chartNeighborhoodM_subset_chartTargetEuclid (I := I) (M := M) α))
      have hChosen_local := hChosen_memLp_NeighborhoodM.locallyIntegrable hp_le
      have h_ae_grad :
          (fun x => (Classical.choose (hv_mem n).2).weakGrad x i) =ᵐ[
            (volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (chartNeighborhoodM (I := I) (M := M) α)]
          Sobolev.Euclidean.chosenWeakPartialOrZero
            (d := Module.finrank ℝ E) (ENNReal.ofReal p) i
            (chartPushed (I := I) (M := M)
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α (u (ψ n)))
            (chartTargetEuclid (I := I) (M := M) α) :=
        Sobolev.Euclidean.HasWeakPartialDeriv.ae_eq
          (chartNeighborhoodM_isOpen (I := I) (M := M) α) hWit_isWeak
          hChart_chosen_isWeak_raw hWit_local hChosen_local
      rw [eLpNorm_congr_ae h_ae_grad]
      exact eLpNorm_mono_measure _
        (MeasureTheory.Measure.restrict_mono_set _
          (chartNeighborhoodM_subset_chartTargetEuclid (I := I) (M := M) α))
    refine le_trans (Finset.sum_le_sum (fun i _ => h_term_bound i)) ?_
    have h_grad_sum_le_wkpNorm :
        ∑ i : Fin (Module.finrank ℝ E),
          eLpNorm
            (Sobolev.Euclidean.chosenWeakPartialOrZero
              (d := Module.finrank ℝ E) (ENNReal.ofReal p) i
              (chartPushed (I := I) (M := M)
                (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α (u (ψ n)))
              (chartTargetEuclid (I := I) (M := M) α)) (ENNReal.ofReal p)
            ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (chartTargetEuclid (I := I) (M := M) α)) ≤
          Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 1 (ENNReal.ofReal p)
            (chartPushed (I := I) (M := M)
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α (u (ψ n)))
            (chartTargetEuclid (I := I) (M := M) α) := by
      unfold Sobolev.Euclidean.iteratedWeakSobolevNorm
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      refine le_trans ?_ le_add_self
      let hEquiv : (Fin 1 → Fin (Module.finrank ℝ E)) ≃ Fin (Module.finrank ℝ E) := {
        toFun := fun f => f 0
        invFun := fun i _ => i
        left_inv := by
          intro f
          funext k
          fin_cases k
          rfl
        right_inv := fun i => rfl }
      have hEquiv_app : ∀ f : Fin 1 → Fin (Module.finrank ℝ E), hEquiv f = f 0 := fun _ => rfl
      have h_sum_eq :
          ∑ α' : Fin 1 → Fin (Module.finrank ℝ E),
            eLpNorm
              (Sobolev.Euclidean.iterWeakPartial
                (d := Module.finrank ℝ E) (ENNReal.ofReal p) 1 α'
                (chartPushed (I := I) (M := M)
                  (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α (u (ψ n)))
                (chartTargetEuclid (I := I) (M := M) α)) (ENNReal.ofReal p)
              ((volume :
                Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
                (chartTargetEuclid (I := I) (M := M) α)) =
          ∑ i : Fin (Module.finrank ℝ E),
            eLpNorm
              (Sobolev.Euclidean.chosenWeakPartialOrZero
                (d := Module.finrank ℝ E) (ENNReal.ofReal p) i
                (chartPushed (I := I) (M := M)
                  (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α (u (ψ n)))
                (chartTargetEuclid (I := I) (M := M) α)) (ENNReal.ofReal p)
              ((volume :
                Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
                (chartTargetEuclid (I := I) (M := M) α)) := by
        apply Finset.sum_bijective hEquiv (Equiv.bijective hEquiv)
        · intro a; simp
        · intro α' _
          have h_iter :
              Sobolev.Euclidean.iterWeakPartial
                (d := Module.finrank ℝ E) (ENNReal.ofReal p) 1 α'
                (chartPushed (I := I) (M := M)
                  (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α (u (ψ n)))
                (chartTargetEuclid (I := I) (M := M) α) =
              Sobolev.Euclidean.chosenWeakPartialOrZero
                (d := Module.finrank ℝ E) (ENNReal.ofReal p) (α' 0)
                (chartPushed (I := I) (M := M)
                  (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α (u (ψ n)))
                (chartTargetEuclid (I := I) (M := M) α) := by
            rw [Sobolev.Euclidean.iterWeakPartial_succ]
            rw [Sobolev.Euclidean.iterWeakPartial_zero]
          rw [h_iter, hEquiv_app α']
      rw [← h_sum_eq]
    refine h_grad_sum_le_wkpNorm.trans ?_
    exact ENNReal.le_tsum α
  have h_neighborhood_open := chartNeighborhoodM_isOpen (I := I) (M := M) α
  have h_neighborhood_bdd := chartNeighborhoodM_isBounded (I := I) (M := M) α
  have hp_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using (ENNReal.ofReal_le_ofReal hp_one.le :
      ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal p)
  have hp_top : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  rcases Sobolev.rellich_kondrachov_W01p_seq
    (d := Module.finrank ℝ E) h_neighborhood_open h_neighborhood_bdd hp_le hp_top hv_mem
    hv_bdd_fun hv_bdd_grad with ⟨σ, hσ_mono, w_α, hw_α_memLp, h_tendsto⟩
  exact ⟨σ, hσ_mono, w_α, hw_α_memLp, h_tendsto⟩

private lemma exists_diagonal_chart_extraction_M
    [NeZero (Module.finrank ℝ E)]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {p : ℝ} (hp_one : 1 < p)
    {u : ℕ → M → ℝ}
    (hu_mem : ∀ n, MemWkpChart (I := I) (M := M) 1 (ENNReal.ofReal p) (u n))
    {R : ℝ}
    (hu_bdd : ∀ n, wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p) (u n) ≤
      ENNReal.ofReal R)
    (S : Finset M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ α ∈ S, ∃ w_α : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ,
        MemLp w_α (ENNReal.ofReal p)
            ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (chartNeighborhoodM (I := I) (M := M) α)) ∧
        Filter.Tendsto
          (fun k => eLpNorm
              (fun y => chartPushedRaw (I := I) (M := M) α
                (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
                  : C^∞⟮I, M; ℝ⟯) x * u (φ k) x) y - w_α y)
              (ENNReal.ofReal p)
              ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
                (chartNeighborhoodM (I := I) (M := M) α)))
          Filter.atTop (𝓝 0) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨id, strictMono_id, fun α hα => ?_⟩
      exact absurd hα (Finset.notMem_empty α)
  | insert a S' ha_notin ih =>
      rcases ih with ⟨φ_S', hφ_S'_mono, hP_S'⟩
      rcases exists_chart_rellich_subseq_aux_M (I := I) (M := M) g hp_one
        hu_mem hu_bdd a φ_S' with
        ⟨σ_a, hσ_a_mono, w_a, hw_a_memLp, h_tendsto_a⟩
      refine ⟨φ_S' ∘ σ_a, hφ_S'_mono.comp hσ_a_mono, ?_⟩
      intro α hα
      rcases Finset.mem_insert.mp hα with rfl | hα_S'
      · refine ⟨w_a, hw_a_memLp, ?_⟩
        exact h_tendsto_a
      · rcases hP_S' α hα_S' with ⟨w_α, hw_α_memLp, h_tendsto_α⟩
        refine ⟨w_α, hw_α_memLp, ?_⟩
        exact h_tendsto_α.comp (Filter.tendsto_atTop_atTop_of_monotone hσ_a_mono.monotone
          (fun n => ⟨n, hσ_a_mono.id_le n⟩))

end

end Chart
end Sobolev

noncomputable section

namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [T2Space M] [CompactSpace M]

private lemma chartAtlasPOU_measurable_aux (α : M) :
    Measurable
      ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
  ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
    : C^∞⟮I, M; ℝ⟯).contMDiff.continuous).measurable

private lemma pou_mul_measurable_aux (α : M) {u : M → ℝ} (hu : Measurable u) :
    Measurable (fun x : M =>
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x) :=
  (chartAtlasPOU_measurable_aux (I := I) (M := M) α).mul hu

private lemma pou_mul_sub_measurable_aux (α : M) {u v : M → ℝ}
    (hu : Measurable u) (hv : Measurable v) :
    Measurable (fun x : M =>
      ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x) -
        ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * v x)) :=
  ((chartAtlasPOU_measurable_aux (I := I) (M := M) α).mul hu).sub
    ((chartAtlasPOU_measurable_aux (I := I) (M := M) α).mul hv)

private lemma tsupport_pou_mul_subset_tsupport_pou_aux
    (α : M) (u : M → ℝ) :
    tsupport (fun x : M =>
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x) ⊆
      tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
  have h_eq : (fun x : M =>
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x) =
      (fun x : M =>
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x • u x) := by
    funext x; rfl
  rw [h_eq]
  exact tsupport_smul_subset_left _ _

private lemma tsupport_pou_mul_sub_subset_tsupport_pou_aux
    (α : M) (u v : M → ℝ) :
    tsupport (fun x : M =>
      ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x) -
        ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * v x)) ⊆
      tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
  classical
  have h_support : Function.support (fun x : M =>
      ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x) -
        ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * v x)) ⊆
      Function.support (fun x : M =>
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x) ∪
        Function.support (fun x : M =>
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * v x) := by
    intro x hx
    by_contra hcontra
    apply hx
    rw [Set.mem_union, not_or] at hcontra
    obtain ⟨hu_zero, hv_zero⟩ := hcontra
    have hu_eq :
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x = 0 :=
      Function.notMem_support.mp hu_zero
    have hv_eq :
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * v x = 0 :=
      Function.notMem_support.mp hv_zero
    change ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x) -
        ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * v x) = 0
    rw [hu_eq, hv_eq, sub_zero]
  have h_tsupp_closed : IsClosed
      (tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ)) := isClosed_tsupport _
  rw [tsupport]
  refine h_tsupp_closed.closure_subset_iff.mpr ?_
  intro x hx
  rcases h_support hx with hu_support | hv_support
  · exact tsupport_pou_mul_subset_tsupport_pou_aux (I := I) (M := M) α u
      (subset_tsupport _ hu_support)
  · exact tsupport_pou_mul_subset_tsupport_pou_aux (I := I) (M := M) α v
      (subset_tsupport _ hv_support)

variable [I.Boundaryless] in
private lemma memLp_pou_mul_riemannianMeasure_aux
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {p : ℝ} (hp_one : 1 < p)
    {u : M → ℝ} (hu_meas : Measurable u)
    (hu : MemWkpChart (I := I) (M := M) 1 (ENNReal.ofReal p) u)
    (α : M) :
    MemLp (fun x : M =>
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x) (ENNReal.ofReal p)
        (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M)) := by
  classical
  have hp_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using (ENNReal.ofReal_le_ofReal hp_one.le :
      ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal p)
  have hp_top : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_raw_w1p :
      Sobolev.Euclidean.MemW1p (d := Module.finrank ℝ E) (ENNReal.ofReal p)
        (chartPushedRaw (I := I) (M := M) α
          (fun x : M =>
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) x * u x))
        (chartTargetEuclid (I := I) (M := M) α) :=
    memW1p_chartPushedRaw_pou_mul_of_memWkpChart (I := I) (M := M) hu α
  have h_raw_memLp :
      MemLp (chartPushedRaw (I := I) (M := M) α
          (fun x : M =>
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) x * u x)) (ENNReal.ofReal p)
        ((volume : Measure (EuclideanSpace ℝ
            (Fin (Module.finrank ℝ E)))).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := h_raw_w1p.1
  set K : Set M := tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
    : C^∞⟮I, M; ℝ⟯) : M → ℝ)
  have hK_compact : IsCompact K :=
    (isClosed_tsupport _).isCompact
  have hK_sub : K ⊆ (chartAt H α).source :=
    CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate (I := I) (M := M) α
  obtain ⟨C, _hC_pos, hC_bnd⟩ :=
    eLpNorm_riemannianMeasure_le_const_mul_eLpNorm_chartPushedRaw_uniform_of_subset
      (I := I) (M := M) g α hK_compact hK_sub hp_le hp_top
  have h_bnd := hC_bnd
    (pou_mul_measurable_aux (I := I) (M := M) α hu_meas)
    (tsupport_pou_mul_subset_tsupport_pou_aux (I := I) (M := M) α u)
  refine ⟨(pou_mul_measurable_aux (I := I) (M := M) α hu_meas).aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt h_bnd ?_
  apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
  exact h_raw_memLp.2

private lemma eLpNorm_pou_mul_diff_riemannianMeasure_le
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {p : ℝ} (hp_one : 1 < p) (α : M) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {u v : M → ℝ}, Measurable u → Measurable v →
        eLpNorm (fun x : M =>
            ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
                : C^∞⟮I, M; ℝ⟯) x * u x) -
              ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
                : C^∞⟮I, M; ℝ⟯) x * v x)) (ENNReal.ofReal p)
            (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M)) ≤
          ENNReal.ofReal C *
            eLpNorm (chartPushedRaw (I := I) (M := M) α
                (fun x : M =>
                  ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
                      : C^∞⟮I, M; ℝ⟯) x * u x) -
                    ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
                      : C^∞⟮I, M; ℝ⟯) x * v x))) (ENNReal.ofReal p)
              ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
                (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have hp_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using (ENNReal.ofReal_le_ofReal hp_one.le :
      ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal p)
  have hp_top : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  set K : Set M := tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
    : C^∞⟮I, M; ℝ⟯) : M → ℝ)
  have hK_compact : IsCompact K :=
    (isClosed_tsupport _).isCompact
  have hK_sub : K ⊆ (chartAt H α).source :=
    CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate (I := I) (M := M) α
  obtain ⟨C, hC_pos, hC_bnd⟩ :=
    eLpNorm_riemannianMeasure_le_const_mul_eLpNorm_chartPushedRaw_uniform_of_subset
      (I := I) (M := M) g α hK_compact hK_sub hp_le hp_top
  refine ⟨C, hC_pos, ?_⟩
  intro u v hu_meas hv_meas
  have h_diff_meas := pou_mul_sub_measurable_aux (I := I) (M := M) α hu_meas hv_meas
  have h_diff_support := tsupport_pou_mul_sub_subset_tsupport_pou_aux
    (I := I) (M := M) α u v
  exact hC_bnd h_diff_meas h_diff_support

section

variable [I.Boundaryless]
private lemma eLpNorm_chartPushedRaw_diff_chartTarget_eq_chartNeighborhoodM
    {p : ℝ} (_hp_one : 1 < p) (α : M) (u v : M → ℝ) :
    eLpNorm (chartPushedRaw (I := I) (M := M) α
        (fun x : M =>
          ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) x * u x) -
            ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) x * v x))) (ENNReal.ofReal p)
        ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartTargetEuclid (I := I) (M := M) α)) =
      eLpNorm (chartPushedRaw (I := I) (M := M) α
          (fun x : M =>
            ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
                : C^∞⟮I, M; ℝ⟯) x * u x) -
              ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
                : C^∞⟮I, M; ℝ⟯) x * v x))) (ENNReal.ofReal p)
        ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartNeighborhoodM (I := I) (M := M) α)) := by
  classical
  have h_zero_off_compact : ∀ y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)),
      y ∉ chartCompactM (I := I) (M := M) α →
      chartPushedRaw (I := I) (M := M) α
        (fun x : M =>
          ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) x * u x) -
            ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) x * v x)) y = 0 := by
    intro y hy
    have h_split := chartPushedRaw_sub (I := I) (M := M) α
      (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x)
      (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * v x)
    have h_app : chartPushedRaw (I := I) (M := M) α
          (fun x : M =>
            ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
                : C^∞⟮I, M; ℝ⟯) x * u x) -
              ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
                : C^∞⟮I, M; ℝ⟯) x * v x)) y =
        chartPushedRaw (I := I) (M := M) α
          (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x) y -
        chartPushedRaw (I := I) (M := M) α
          (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * v x) y := congrFun h_split y
    rw [h_app]
    rw [chartPushedRaw_pou_mul_eq_zero_off_chartCompactM (I := I) (M := M) α u hy]
    rw [chartPushedRaw_pou_mul_eq_zero_off_chartCompactM (I := I) (M := M) α v hy]
    ring
  have h_indic :
      (chartPushedRaw (I := I) (M := M) α
          (fun x : M =>
            ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
                : C^∞⟮I, M; ℝ⟯) x * u x) -
              ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
                : C^∞⟮I, M; ℝ⟯) x * v x))) =
        (chartNeighborhoodM (I := I) (M := M) α).indicator
          (chartPushedRaw (I := I) (M := M) α
            (fun x : M =>
              ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
                  : C^∞⟮I, M; ℝ⟯) x * u x) -
                ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
                  : C^∞⟮I, M; ℝ⟯) x * v x))) := by
    funext y
    by_cases hy_NeighborhoodM : y ∈ chartNeighborhoodM (I := I) (M := M) α
    · rw [Set.indicator_of_mem hy_NeighborhoodM]
    · rw [Set.indicator_of_notMem hy_NeighborhoodM]
      have hy_not_compact : y ∉ chartCompactM (I := I) (M := M) α := by
        intro hy_compact
        exact hy_NeighborhoodM (chartCompactM_subset_chartNeighborhoodM (I := I) (M := M) α hy_compact)
      exact h_zero_off_compact y hy_not_compact
  rw [h_indic]
  rw [eLpNorm_indicator_eq_eLpNorm_restrict
    (chartNeighborhoodM_isOpen (I := I) (M := M) α).measurableSet]
  rw [eLpNorm_indicator_eq_eLpNorm_restrict
    (chartNeighborhoodM_isOpen (I := I) (M := M) α).measurableSet]
  rw [MeasureTheory.Measure.restrict_restrict
    (chartNeighborhoodM_isOpen (I := I) (M := M) α).measurableSet]
  rw [MeasureTheory.Measure.restrict_restrict
    (chartNeighborhoodM_isOpen (I := I) (M := M) α).measurableSet]
  rw [Set.inter_eq_self_of_subset_left
    (chartNeighborhoodM_subset_chartTargetEuclid (I := I) (M := M) α)]
  rw [Set.inter_self]

private lemma eLpNorm_chartPushed_jk_NeighborhoodM_le_of_tendsto
    {p : ℝ} (hp_one : 1 < p)
    {u : ℕ → M → ℝ}
    (hu_mem : ∀ n, MemWkpChart (I := I) (M := M) 1 (ENNReal.ofReal p) (u n))
    (α : M) {φ : ℕ → ℕ}
    {w_α : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ}
    (hw_α_aestrong : AEStronglyMeasurable w_α
      ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
        (chartNeighborhoodM (I := I) (M := M) α)))
    (h_tendsto :
      Filter.Tendsto
        (fun k => eLpNorm
            (fun y => chartPushedRaw (I := I) (M := M) α
              (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
                : C^∞⟮I, M; ℝ⟯) x * u (φ k) x) y - w_α y)
            (ENNReal.ofReal p)
            ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (chartNeighborhoodM (I := I) (M := M) α)))
        Filter.atTop (𝓝 0)) :
    ∀ ε > 0, ∃ N, ∀ j ≥ N, ∀ k ≥ N,
      eLpNorm
          (fun y => chartPushedRaw (I := I) (M := M) α
            (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) x * u (φ j) x) y -
            chartPushedRaw (I := I) (M := M) α
              (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
                : C^∞⟮I, M; ℝ⟯) x * u (φ k) x) y) (ENNReal.ofReal p)
          ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
            (chartNeighborhoodM (I := I) (M := M) α)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero] at h_tendsto
  rcases h_tendsto (ENNReal.ofReal (ε / 2)) (ENNReal.ofReal_pos.mpr (by linarith))
    with ⟨N, hN⟩
  refine ⟨N, fun j hj k hk => ?_⟩
  have h_chart_jraw_aestrong : AEStronglyMeasurable (chartPushedRaw (I := I) (M := M) α
      (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u (φ j) x))
      ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
        (chartNeighborhoodM (I := I) (M := M) α)) :=
    (memW1p_chartPushedRaw_pou_mul_chartNeighborhoodM
      (I := I) (M := M) (hu_mem (φ j)) α).1.1
  have h_chart_kraw_aestrong : AEStronglyMeasurable (chartPushedRaw (I := I) (M := M) α
      (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u (φ k) x))
      ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
        (chartNeighborhoodM (I := I) (M := M) α)) :=
    (memW1p_chartPushedRaw_pou_mul_chartNeighborhoodM
      (I := I) (M := M) (hu_mem (φ k)) α).1.1
  have h_triangle :
      eLpNorm
        (fun y => chartPushedRaw (I := I) (M := M) α
          (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u (φ j) x) y -
          chartPushedRaw (I := I) (M := M) α
            (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) x * u (φ k) x) y) (ENNReal.ofReal p)
        ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartNeighborhoodM (I := I) (M := M) α)) ≤
      eLpNorm
        (fun y => chartPushedRaw (I := I) (M := M) α
          (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u (φ j) x) y - w_α y) (ENNReal.ofReal p)
        ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartNeighborhoodM (I := I) (M := M) α)) +
      eLpNorm
        (fun y => w_α y - chartPushedRaw (I := I) (M := M) α
          (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u (φ k) x) y) (ENNReal.ofReal p)
        ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartNeighborhoodM (I := I) (M := M) α)) := by
    have h := eLpNorm_add_le (μ :=
        (volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartNeighborhoodM (I := I) (M := M) α))
      (p := ENNReal.ofReal p)
      (f := fun y => chartPushedRaw (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u (φ j) x) y - w_α y)
      (g := fun y => w_α y - chartPushedRaw (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u (φ k) x) y)
      (h_chart_jraw_aestrong.sub hw_α_aestrong)
      (hw_α_aestrong.sub h_chart_kraw_aestrong)
      (by simpa using (ENNReal.ofReal_le_ofReal hp_one.le :
        ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal p))
    rw [show
      (fun y => chartPushedRaw (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u (φ j) x) y -
        chartPushedRaw (I := I) (M := M) α
          (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u (φ k) x) y) =
      (fun y =>
        (chartPushedRaw (I := I) (M := M) α
          (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u (φ j) x) y - w_α y) +
        (w_α y - chartPushedRaw (I := I) (M := M) α
          (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u (φ k) x) y)) by funext y; ring]
    exact h
  have h_w_swap_k :
      eLpNorm
        (fun y => w_α y - chartPushedRaw (I := I) (M := M) α
          (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u (φ k) x) y) (ENNReal.ofReal p)
        ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartNeighborhoodM (I := I) (M := M) α)) =
      eLpNorm
        (fun y => chartPushedRaw (I := I) (M := M) α
          (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u (φ k) x) y - w_α y) (ENNReal.ofReal p)
        ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartNeighborhoodM (I := I) (M := M) α)) := by
    have h_fn_eq :
        (fun y => w_α y - chartPushedRaw (I := I) (M := M) α
          (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u (φ k) x) y) =
        -(fun y => chartPushedRaw (I := I) (M := M) α
          (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u (φ k) x) y - w_α y) := by
      funext y
      simp only [Pi.neg_apply, neg_sub]
    rw [h_fn_eq]
    exact eLpNorm_neg _ _ _
  rw [h_w_swap_k] at h_triangle
  have hjN := hN j hj
  have hkN := hN k hk
  have h_sum :
      ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) = ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_add (by linarith : (0 : ℝ) ≤ ε / 2)
      (by linarith : (0 : ℝ) ≤ ε / 2)]
    congr 1
    ring
  refine h_triangle.trans ?_
  rw [← h_sum]
  exact add_le_add hjN hkN

private lemma exists_riemannianMeasure_limit_pou_mul
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {p : ℝ} (hp_one : 1 < p)
    {u : ℕ → M → ℝ}
    (hu_meas : ∀ n, Measurable (u n))
    (hu_mem : ∀ n, MemWkpChart (I := I) (M := M) 1 (ENNReal.ofReal p) (u n))
    (α : M) {φ : ℕ → ℕ}
    {w_α : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ}
    (hw_α_memLp : MemLp w_α (ENNReal.ofReal p)
      ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
        (chartNeighborhoodM (I := I) (M := M) α)))
    (h_tendsto :
      Filter.Tendsto
        (fun k => eLpNorm
            (fun y => chartPushedRaw (I := I) (M := M) α
              (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
                : C^∞⟮I, M; ℝ⟯) x * u (φ k) x) y - w_α y)
            (ENNReal.ofReal p)
            ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (chartNeighborhoodM (I := I) (M := M) α)))
        Filter.atTop (𝓝 0)) :
    ∃ v_α : M → ℝ, MemLp v_α (ENNReal.ofReal p)
        (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M)) ∧
      Filter.Tendsto
        (fun k => eLpNorm
            (fun x : M =>
              ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
                  : C^∞⟮I, M; ℝ⟯) x * u (φ k) x) - v_α x)
            (ENNReal.ofReal p)
            (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M)))
        Filter.atTop (𝓝 0) := by
  classical
  set μ_g : Measure M :=
    CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M) with hμ_g_def
  set fSeq : ℕ → M → ℝ := fun k x =>
    (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) x * u (φ k) x with hf_seq_def
  have hf_seq_mem : ∀ n, MemLp (fSeq n) (ENNReal.ofReal p) μ_g := fun n =>
    memLp_pou_mul_riemannianMeasure_aux (I := I) (M := M) g hp_one
      (hu_meas (φ n)) (hu_mem (φ n)) α
  have hp_fact : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    simpa using (ENNReal.ofReal_le_ofReal hp_one.le :
      ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal p)⟩
  let F : ℕ → MeasureTheory.Lp ℝ (ENNReal.ofReal p) μ_g := fun n =>
    (hf_seq_mem n).toLp (fSeq n)
  have hF_cauchy : CauchySeq F := by
    rw [MeasureTheory.Lp.cauchySeq_Lp_iff_cauchySeq_eLpNorm]
    have hCauchy_manifold : ∀ ε > 0, ∃ N, ∀ j ≥ N, ∀ k ≥ N,
        eLpNorm (fun x : M => fSeq j x - fSeq k x) (ENNReal.ofReal p) μ_g ≤
          ENNReal.ofReal ε := by
      intro ε hε
      obtain ⟨C, hC_pos, hC_bnd⟩ :=
        eLpNorm_pou_mul_diff_riemannianMeasure_le
          (I := I) (M := M) g hp_one α
      set ε₀ : ℝ := ε / C
      have hε₀_pos : 0 < ε₀ := div_pos hε hC_pos
      rcases eLpNorm_chartPushed_jk_NeighborhoodM_le_of_tendsto
        (I := I) (M := M) hp_one hu_mem α hw_α_memLp.1 h_tendsto ε₀ hε₀_pos with ⟨N, hN⟩
      refine ⟨N, fun j hj k hk => ?_⟩
      have h_chart_jk_NeighborhoodM := hN j hj k hk
      have h_diff_eq_swap :
          chartPushedRaw (I := I) (M := M) α
            (fun x : M =>
              ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
                  : C^∞⟮I, M; ℝ⟯) x * u (φ j) x) -
                ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
                  : C^∞⟮I, M; ℝ⟯) x * u (φ k) x)) =
          (fun y => chartPushedRaw (I := I) (M := M) α
              (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
                : C^∞⟮I, M; ℝ⟯) x * u (φ j) x) y -
            chartPushedRaw (I := I) (M := M) α
              (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
                : C^∞⟮I, M; ℝ⟯) x * u (φ k) x) y) :=
        chartPushedRaw_sub (I := I) (M := M) α
          (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u (φ j) x)
          (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u (φ k) x)
      have h_eq := eLpNorm_chartPushedRaw_diff_chartTarget_eq_chartNeighborhoodM
        (I := I) (M := M) hp_one α (u (φ j)) (u (φ k))
      have h_chart_jk_target :
          eLpNorm (chartPushedRaw (I := I) (M := M) α
              (fun x : M =>
                ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
                    : C^∞⟮I, M; ℝ⟯) x * u (φ j) x) -
                  ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
                    : C^∞⟮I, M; ℝ⟯) x * u (φ k) x))) (ENNReal.ofReal p)
              ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
                (chartTargetEuclid (I := I) (M := M) α)) ≤
          ENNReal.ofReal ε₀ := by
        rw [h_eq, h_diff_eq_swap]
        exact h_chart_jk_NeighborhoodM
      have h_bnd := hC_bnd (hu_meas (φ j)) (hu_meas (φ k))
      refine h_bnd.trans ?_
      refine (mul_le_mul' le_rfl h_chart_jk_target).trans ?_
      rw [← ENNReal.ofReal_mul hC_pos.le]
      apply ENNReal.ofReal_le_ofReal
      show C * ε₀ ≤ ε
      have h_eq : C * (ε / C) = ε := by
        field_simp
      calc C * ε₀ = C * (ε / C) := by rw [show ε₀ = ε / C from rfl]
        _ = ε := h_eq
        _ ≤ ε := le_refl _
    refine ENNReal.tendsto_atTop_zero.mpr ?_
    intro ε hε
    by_cases hε_top : ε = ⊤
    · refine ⟨⟨0, 0⟩, fun n _hn => ?_⟩
      rw [hε_top]; exact le_top
    have hε_real_pos : 0 < ε.toReal :=
      ENNReal.toReal_pos (ne_of_gt hε) hε_top
    rcases hCauchy_manifold ε.toReal hε_real_pos with ⟨N, hN⟩
    refine ⟨⟨N, N⟩, fun nm hnm => ?_⟩
    have hj : N ≤ nm.1 := hnm.1
    have hk : N ≤ nm.2 := hnm.2
    have h_le := hN nm.1 hj nm.2 hk
    have h_ae_eq : ((F nm.1 : M → ℝ) - (F nm.2 : M → ℝ)) =ᵐ[μ_g]
        (fun x => fSeq nm.1 x - fSeq nm.2 x) := by
      filter_upwards [(hf_seq_mem nm.1).coeFn_toLp, (hf_seq_mem nm.2).coeFn_toLp,
        Lp.coeFn_sub (F nm.1) (F nm.2)] with x hx1 hx2 hx_sub
      show ((F nm.1 : M → ℝ) - (F nm.2 : M → ℝ)) x = fSeq nm.1 x - fSeq nm.2 x
      have h_pi : ((F nm.1 : M → ℝ) - (F nm.2 : M → ℝ)) x =
          (F nm.1 : M → ℝ) x - (F nm.2 : M → ℝ) x := rfl
      rw [h_pi, hx1, hx2]
    rw [eLpNorm_congr_ae h_ae_eq]
    exact h_le.trans (ENNReal.ofReal_toReal hε_top).le
  obtain ⟨F_lim, hF_tendsto⟩ := cauchySeq_tendsto_of_complete hF_cauchy
  refine ⟨↑F_lim, MeasureTheory.Lp.memLp F_lim, ?_⟩
  have hF_lim_memLp : MemLp (↑F_lim : M → ℝ) (ENNReal.ofReal p) μ_g :=
    MeasureTheory.Lp.memLp F_lim
  have h_iff := MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm
    (fi := Filter.atTop) (f := F) (f_lim := (↑F_lim : M → ℝ)) hF_lim_memLp
  have h_coe_eq : F_lim = hF_lim_memLp.toLp (↑F_lim : M → ℝ) := by
    apply MeasureTheory.Lp.ext
    exact (MemLp.coeFn_toLp hF_lim_memLp).symm
  rw [h_coe_eq] at hF_tendsto
  have h_eLp_tendsto : Filter.Tendsto
      (fun k => eLpNorm ((F k : M → ℝ) - (↑F_lim : M → ℝ)) (ENNReal.ofReal p) μ_g)
      Filter.atTop (𝓝 0) := h_iff.mp hF_tendsto
  have h_eLpFn_eq : (fun k => eLpNorm ((F k : M → ℝ) - (↑F_lim : M → ℝ)) (ENNReal.ofReal p) μ_g) =
      fun k => eLpNorm (fun x => fSeq k x - (↑F_lim : M → ℝ) x) (ENNReal.ofReal p) μ_g := by
    funext k
    apply eLpNorm_congr_ae
    filter_upwards [(hf_seq_mem k).coeFn_toLp] with x hx
    show ((F k : M → ℝ) - (↑F_lim : M → ℝ)) x = fSeq k x - (↑F_lim : M → ℝ) x
    have : ((F k : M → ℝ) - (↑F_lim : M → ℝ)) x = (F k : M → ℝ) x - (↑F_lim : M → ℝ) x := rfl
    rw [this, hx]
  rw [h_eLpFn_eq] at h_eLp_tendsto
  exact h_eLp_tendsto

end

theorem rellich_kondrachov_chart_seq
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {p : ℝ} (hp_one : 1 < p)
    {u : ℕ → M → ℝ}
    (hu_meas : ∀ n, Measurable (u n))
    (hu_mem : ∀ n, MemWkpChart (I := I) (M := M) 1 (ENNReal.ofReal p) (u n))
    {R : ℝ}
    (hu_bdd : ∀ n, wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p) (u n) ≤
      ENNReal.ofReal R) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ u_lim : M → ℝ,
        MemLp u_lim (ENNReal.ofReal p)
          (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M)) ∧
        Filter.Tendsto
          (fun j => eLpNorm (fun x => u (φ j) x - u_lim x) (ENNReal.ofReal p)
            (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M)))
          Filter.atTop (𝓝 0) := by
  classical
  set S : Finset M :=
    CalabiYau.RiemannianVolume.chartAtlasPOUFinset (I := I) (M := M) with hS_def
  rcases exists_diagonal_chart_extraction_M (I := I) (M := M) g hp_one
    hu_mem hu_bdd S with ⟨φ, hφ_mono, hP_S⟩
  have h_per_α : ∀ α ∈ S, ∃ v_α : M → ℝ,
      MemLp v_α (ENNReal.ofReal p)
        (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M)) ∧
      Filter.Tendsto
        (fun k => eLpNorm
            (fun x : M =>
              ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
                  : C^∞⟮I, M; ℝ⟯) x * u (φ k) x) - v_α x)
            (ENNReal.ofReal p)
            (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M)))
        Filter.atTop (𝓝 0) := by
    intro α hα
    rcases hP_S α hα with ⟨w_α, hw_α_memLp, h_tendsto⟩
    exact exists_riemannianMeasure_limit_pou_mul
      (I := I) (M := M) g hp_one hu_meas hu_mem α hw_α_memLp h_tendsto
  let v : ∀ α ∈ S, M → ℝ := fun α hα => (h_per_α α hα).choose
  have hv_memLp : ∀ α (hα : α ∈ S), MemLp (v α hα) (ENNReal.ofReal p)
      (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M)) := fun α hα =>
    ((h_per_α α hα).choose_spec).1
  have hv_tendsto : ∀ α (hα : α ∈ S),
      Filter.Tendsto
        (fun k => eLpNorm
            (fun x : M =>
              ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
                  : C^∞⟮I, M; ℝ⟯) x * u (φ k) x) - v α hα x)
            (ENNReal.ofReal p)
            (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M)))
        Filter.atTop (𝓝 0) := fun α hα => ((h_per_α α hα).choose_spec).2
  let u_lim : M → ℝ := fun x => ∑ α ∈ S.attach, v α.1 α.2 x
  have hu_lim_memLp : MemLp u_lim (ENNReal.ofReal p)
      (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M)) := by
    exact memLp_finsetSum S.attach (fun α _ => hv_memLp α.1 α.2)
  refine ⟨φ, hφ_mono, u_lim, hu_lim_memLp, ?_⟩
  refine ENNReal.tendsto_atTop_zero.mpr ?_
  intro ε hε
  set n := S.attach.card
  by_cases hn : n = 0
  · refine ⟨0, fun j _hj => ?_⟩
    have hS_empty : S = ∅ := by
      rw [Finset.card_eq_zero] at hn
      exact Finset.attach_eq_empty_iff.mp hn
    have h_pou_zero : ∀ α : M, ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) = 0 := by
      intro α
      have hα : α ∉ S := by rw [hS_empty]; exact Finset.notMem_empty α
      funext x
      exact CalabiYau.RiemannianVolume.chartAtlasPOU_weight_zero_of_notMem
        (I := I) (M := M) hα x
    by_cases hM_ne : Nonempty M
    · exfalso
      have h_one := chartAtlasPOU_finset_sum_eq_one (I := I) (M := M)
        (Classical.choice hM_ne)
      have h_S : CalabiYau.RiemannianVolume.chartAtlasPOUFinset
          (I := I) (M := M) = ∅ := hS_empty
      rw [h_S] at h_one
      simp at h_one
    · have hM_empty : ¬ Nonempty M := hM_ne
      have h_diff_zero : (fun x : M => u (φ j) x - u_lim x) = 0 := by
        funext x
        exact absurd ⟨x⟩ hM_empty
      rw [h_diff_zero]
      rw [eLpNorm_zero]
      exact zero_le
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
  have h_per_α_eLp : ∀ α ∈ S.attach, ∃ N : ℕ, ∀ k ≥ N,
      eLpNorm
          (fun x : M =>
            ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α.1
                : C^∞⟮I, M; ℝ⟯) x * u (φ k) x - v α.1 α.2 x))
          (ENNReal.ofReal p)
          (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M)) ≤
        ε / n := by
    intro α _hα
    have h_tendsto := hv_tendsto α.1 α.2
    rw [ENNReal.tendsto_atTop_zero] at h_tendsto
    have hε_n_pos : (0 : ℝ≥0∞) < ε / n := by
      apply ENNReal.div_pos hε.ne'
      exact ENNReal.natCast_ne_top _
    rcases h_tendsto (ε / n) hε_n_pos with ⟨N, hN⟩
    exact ⟨N, fun k hk => hN k hk⟩
  choose N hN using h_per_α_eLp
  set Nfun : { α : M // α ∈ S } → ℕ := fun α => N α (Finset.mem_attach S α)
  set N_max : ℕ := S.attach.sup Nfun
  refine ⟨N_max, fun j hj => ?_⟩
  have hj_ge_N : ∀ α ∈ S.attach, j ≥ Nfun α := fun α hα =>
    le_trans (Finset.le_sup (f := Nfun) hα) hj
  have h_diff_eq :
      (fun x : M => u (φ j) x - u_lim x) =
      (fun x => ∑ α ∈ S.attach,
        ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α.1
          : C^∞⟮I, M; ℝ⟯) x * u (φ j) x - v α.1 α.2 x)) := by
    funext x
    change u (φ j) x - (∑ α ∈ S.attach, v α.1 α.2 x) =
      ∑ α ∈ S.attach, ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α.1
        : C^∞⟮I, M; ℝ⟯) x * u (φ j) x - v α.1 α.2 x)
    have h_pou_x : (∑ α ∈ S.attach, (CalabiYau.RiemannianVolume.chartAtlasPOU I M α.1
          : C^∞⟮I, M; ℝ⟯) x * u (φ j) x) = u (φ j) x := by
      have h_attach := Finset.sum_attach S
        (f := fun α : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u (φ j) x)
      rw [h_attach, ← Finset.sum_mul,
        chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x, one_mul]
    have h_distrib :
        ∑ α ∈ S.attach,
          ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α.1
            : C^∞⟮I, M; ℝ⟯) x * u (φ j) x - v α.1 α.2 x) =
        (∑ α ∈ S.attach,
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M α.1
            : C^∞⟮I, M; ℝ⟯) x * u (φ j) x) - (∑ α ∈ S.attach, v α.1 α.2 x) :=
      Finset.sum_sub_distrib (s := S.attach)
        (f := fun α => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α.1
            : C^∞⟮I, M; ℝ⟯) x * u (φ j) x)
        (g := fun α => v α.1 α.2 x)
    rw [h_distrib, h_pou_x]
  rw [h_diff_eq]
  have h_each_aestrong : ∀ α ∈ S.attach,
      AEStronglyMeasurable
        (fun x : M =>
          ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α.1
            : C^∞⟮I, M; ℝ⟯) x * u (φ j) x - v α.1 α.2 x))
        (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M)) := by
    intro α _hα
    have h_pou_meas := pou_mul_measurable_aux (I := I) (M := M) α.1 (hu_meas (φ j))
    have h_v_meas := (hv_memLp α.1 α.2).1
    exact h_pou_meas.aestronglyMeasurable.sub h_v_meas
  have hp_le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using (ENNReal.ofReal_le_ofReal hp_one.le :
      ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal p)
  have h_pi_sum : (fun x : M => ∑ α ∈ S.attach,
      ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α.1
        : C^∞⟮I, M; ℝ⟯) x * u (φ j) x - v α.1 α.2 x)) =
      ∑ α ∈ S.attach,
        (fun x : M =>
          ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α.1
            : C^∞⟮I, M; ℝ⟯) x * u (φ j) x - v α.1 α.2 x)) := by
    funext x
    rw [Finset.sum_apply]
  rw [h_pi_sum]
  refine (eLpNorm_sum_le h_each_aestrong hp_le).trans ?_
  have h_each_le : ∀ α ∈ S.attach,
      eLpNorm (fun x : M => ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α.1
            : C^∞⟮I, M; ℝ⟯) x * u (φ j) x - v α.1 α.2 x)) (ENNReal.ofReal p)
          (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M)) ≤
        ε / n := fun α hα => hN α (Finset.mem_attach S α) j (hj_ge_N α hα)
  refine le_trans (Finset.sum_le_sum h_each_le) ?_
  rw [Finset.sum_const]
  rw [nsmul_eq_mul]
  have h_card_eq : (S.attach.card : ℝ≥0∞) = (n : ℝ≥0∞) := rfl
  rw [h_card_eq, ENNReal.mul_div_cancel (by exact_mod_cast hn_pos.ne')
    (ENNReal.natCast_ne_top n)]

end Chart
end Sobolev
