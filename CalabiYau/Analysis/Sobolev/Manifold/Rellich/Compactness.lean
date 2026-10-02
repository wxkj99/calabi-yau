-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Manifold/Rellich/Compactness.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Manifold.RiemannianRellich
public import CalabiYau.Analysis.Sobolev.Chart.RiemannianMeasureComparison
public import CalabiYau.Analysis.Sobolev.Euclidean.Embedding.Rellich.Basic
public import CalabiYau.Analysis.Sobolev.Chart.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Group.NullSubmodule
public import Mathlib.Analysis.Normed.Group.Uniform
public import CalabiYau.Analysis.Sobolev.Chart.BanachCompleteness.CompletenessLp
public import CalabiYau.Geometry.Riemannian.Volume.Basic
public import CalabiYau.Analysis.Sobolev.Euclidean.W1p
public import CalabiYau.Analysis.Sobolev.Euclidean.W1p.Approximation
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist

@[expose] public section


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

omit [IsManifold I ∞ M] in
lemma chartPushed_eq_chartPushedRaw_pou_ae
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ) :
    chartPushed (I := I) (M := M) ρ α u
      =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      chartPushedRaw (I := I) (M := M) α
        (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) := by
  filter_upwards [self_mem_ae_restrict
    (chartTargetEuclid_measurableSet (I := I) (M := M) α)] with y hy
  exact chartPushed_eq_chartPushedRaw_pou_mul_on_target
    (I := I) (M := M) ρ α u hy

variable [T2Space M] [CompactSpace M]
private lemma extChartAt_image_tsupport_pou_compact
    (α : M) :
    IsCompact ((extChartAt I α) ''
      (tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
        : M → ℝ))) ∧
    (extChartAt I α) ''
      (tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
        : M → ℝ)) ⊆
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
    (u := ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))
    (α := α) hsupp_sub

omit [T2Space M] [CompactSpace M] in
omit [IsManifold I ∞ M] in
lemma chartPushedRaw_sub
    (α : M) (u v : M → ℝ) :
    chartPushedRaw (I := I) (M := M) α (fun x => u x - v x) =
      fun y => chartPushedRaw (I := I) (M := M) α u y -
        chartPushedRaw (I := I) (M := M) α v y := by
  classical
  funext y
  unfold chartPushedRaw
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · simp [hy]
  · simp [hy]

variable [I.Boundaryless] in
lemma memW1p_chartPushedRaw_pou_mul_of_memWkpChart
    {p : ℝ≥0∞}
    {u : M → ℝ}
    (hu : MemWkpChart (I := I) (M := M) 1 p u)
    (α : M) :
    Sobolev.Euclidean.MemW1p (d := Module.finrank ℝ E) p
      (chartPushedRaw (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_ae := chartPushed_eq_chartPushedRaw_pou_ae
    (I := I) (M := M)
    (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u
  have h_chart_pushed : Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 p
      (chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
      (chartTargetEuclid (I := I) (M := M) α) := hu α
  have h_chart_pushed_w1p :
      Sobolev.Euclidean.MemW1p (d := Module.finrank ℝ E) p
        (chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
        (chartTargetEuclid (I := I) (M := M) α) :=
    Sobolev.Euclidean.MemWkp.one_iff_memW1p.mp
      h_chart_pushed
  have hopen := chartTargetEuclid_isOpen (I := I) (M := M) α
  exact (Sobolev.Euclidean.MemW1p_congr_ae
    (d := Module.finrank ℝ E) (p := p) h_ae).mp h_chart_pushed_w1p

lemma eLpNorm_chartPushedRaw_pou_mul_eq_chartPushed
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞}
    (u : M → ℝ) (α : M) :
    eLpNorm (chartPushedRaw (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x)) p
        ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartTargetEuclid (I := I) (M := M) α)) =
      eLpNorm (chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u) p
        ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
  let _ := g
  refine eLpNorm_congr_ae ?_
  exact (chartPushed_eq_chartPushedRaw_pou_ae (I := I) (M := M)
    (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u).symm

lemma eLpNorm_chartPushed_le_wkpNormChart
    {p : ℝ≥0∞}
    (u : M → ℝ) (α : M) :
    eLpNorm (chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u) p
        ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartTargetEuclid (I := I) (M := M) α)) ≤
      wkpNormChart (I := I) (M := M) 1 p u := by
  classical
  have hbound1 :
      eLpNorm (chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u) p
          ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
            (chartTargetEuclid (I := I) (M := M) α)) ≤
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 p
          (chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
          (chartTargetEuclid (I := I) (M := M) α) := by
    unfold Sobolev.Euclidean.iteratedWeakSobolevNorm
    rw [Finset.sum_range_succ]
    refine le_trans ?_ le_self_add
    rw [Finset.sum_range_one]
    have hUniq : ∀ α : Fin 0 → Fin (Module.finrank ℝ E), α = (fun i : Fin 0 => i.elim0) :=
      fun α => by funext i; exact i.elim0
    have : Unique (Fin 0 → Fin (Module.finrank ℝ E)) :=
      { default := fun i : Fin 0 => i.elim0
        uniq := fun α => (hUniq α).symm ▸ rfl }
    rw [Fintype.sum_unique
      (f := fun α' : Fin 0 → Fin (Module.finrank ℝ E) =>
        eLpNorm
          (Sobolev.Euclidean.iterWeakPartial
            (d := Module.finrank ℝ E) p 0 α'
            (chartPushed (I := I) (M := M)
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
            (chartTargetEuclid (I := I) (M := M) α)) p
          ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
            (chartTargetEuclid (I := I) (M := M) α)))]
    rw [Sobolev.Euclidean.iterWeakPartial_zero]
  exact hbound1.trans (ENNReal.le_tsum α)

end Chart
end Sobolev

noncomputable section

namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [T2Space M] [CompactSpace M]
private lemma chartAtlasPOU_measurable (α : M) :
    Measurable
      ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
  ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
    : C^∞⟮I, M; ℝ⟯).contMDiff.continuous).measurable

private lemma tsupport_pou_mul_subset_tsupport_pou
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

private lemma tsupport_pou_mul_subset_chart_source
    (α : M) (u : M → ℝ) :
    tsupport (fun x : M =>
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x) ⊆ (chartAt H α).source :=
  (tsupport_pou_mul_subset_tsupport_pou (I := I) (M := M) α u).trans
    (CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate
      (I := I) (M := M) α)

variable [I.Boundaryless] in
private noncomputable def kPouCompact (α : M) : Set E :=
  (extChartAt I α) ''
    (tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ))

private lemma kPouCompact_isCompact (α : M) :
    IsCompact (kPouCompact (I := I) (M := M) α) :=
  (extChartAt_image_tsupport_pou_compact (I := I) (M := M) α).1

end Chart
end Sobolev
