-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Integration/Measure/Chart/Rellich.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Euclidean.Embedding.Rellich.Basic
public import CalabiYau.Analysis.Sobolev.Chart.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Group.NullSubmodule
public import Mathlib.Analysis.Normed.Group.Uniform
public import CalabiYau.Geometry.Riemannian.Volume.Basic
public import CalabiYau.Geometry.Riemannian.Volume.Family.Basic
public import CalabiYau.Geometry.Riemannian.Volume.Properties
public import CalabiYau.Geometry.Riemannian.Volume.Invariance
public import CalabiYau.Analysis.Sobolev.Euclidean.W1p
public import CalabiYau.Mathlib.MeasureTheory.Function.LpSpace.Convergence
public import CalabiYau.Analysis.Sobolev.Euclidean.W1p.Approximation
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold
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

lemma chartAtlasPOU_finset_sum_eq_one
    [T2Space M] [CompactSpace M]
    (x : M) :
    ∑ α ∈ CalabiYau.RiemannianVolume.chartAtlasPOUFinset (I := I) (M := M),
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M α : M → ℝ) x = 1 := by
  classical
  have hsubset :
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M).finsupport x ⊆
        CalabiYau.RiemannianVolume.chartAtlasPOUFinset (I := I) (M := M) := by
    intro α hα
    rw [CalabiYau.RiemannianVolume.chartAtlasPOU_finset_mem]
    rw [SmoothPartitionOfUnity.mem_finsupport] at hα
    exact ⟨x, hα⟩
  exact (CalabiYau.RiemannianVolume.chartAtlasPOU I M).sum_finsupport' x
    (Set.mem_univ x) hsubset

theorem riemannianMeasure_lintegral_eq_chartLocalMeasure_of_supportIn
    [T2Space M] [CompactSpace M]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    (α : M)
    {F : M → ℝ≥0∞} (hF : Measurable F)
    (hF_support : ∀ x, x ∉ (chartAt H α).source → F x = 0) :
    ∫⁻ x, F x ∂(CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M)) =
      ∫⁻ x, F x ∂(CalabiYau.RiemannianVolume.chartLocalMeasure (I := I) g α) := by
  classical
  rw [CalabiYau.RiemannianVolume.riemannianMeasure_lintegral_eq
    (I := I) g (CalabiYau.RiemannianVolume.chartAtlasPOU I M) hF]
  set S : Finset M :=
    CalabiYau.RiemannianVolume.chartAtlasPOUFinset (I := I) (M := M) with hS_def
  have htsum_eq_finsum :
      ∑' β : M, ∫⁻ x, ENNReal.ofReal
              ((CalabiYau.RiemannianVolume.chartAtlasPOU I M β : M → ℝ) x)
              * F x
            ∂(CalabiYau.RiemannianVolume.chartLocalMeasure (I := I) g β) =
        ∑ β ∈ S, ∫⁻ x, ENNReal.ofReal
              ((CalabiYau.RiemannianVolume.chartAtlasPOU I M β : M → ℝ) x)
              * F x
            ∂(CalabiYau.RiemannianVolume.chartLocalMeasure (I := I) g β) := by
    rw [tsum_eq_sum]
    intro β hβ
    have hρ_zero : ∀ x : M,
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M β : M → ℝ) x = 0 := fun x =>
      CalabiYau.RiemannianVolume.chartAtlasPOU_weight_zero_of_notMem
        (I := I) (M := M) hβ x
    have hint_zero : ∀ x : M, ENNReal.ofReal
        ((CalabiYau.RiemannianVolume.chartAtlasPOU I M β : M → ℝ) x) * F x = 0 := by
      intro x
      rw [hρ_zero x]
      simp
    have hintegrand : (fun x : M => ENNReal.ofReal
        ((CalabiYau.RiemannianVolume.chartAtlasPOU I M β : M → ℝ) x) * F x) =
        (fun _ : M => (0 : ℝ≥0∞)) := by
      funext x
      exact hint_zero x
    rw [hintegrand]
    simp
  rw [htsum_eq_finsum]
  have h_each_eq : ∀ β ∈ S,
      ∫⁻ x, ENNReal.ofReal
            ((CalabiYau.RiemannianVolume.chartAtlasPOU I M β : M → ℝ) x) * F x
          ∂(CalabiYau.RiemannianVolume.chartLocalMeasure (I := I) g β) =
        ∫⁻ x, ENNReal.ofReal
            ((CalabiYau.RiemannianVolume.chartAtlasPOU I M β : M → ℝ) x) * F x
          ∂(CalabiYau.RiemannianVolume.chartLocalMeasure (I := I) g α) := by
    intro β hβS
    apply CalabiYau.RiemannianVolume.chartLocalMeasure_lintegral_eq_of_support_in_overlap
      (I := I) g β α
    · exact ((CalabiYau.RiemannianVolume.measurable_ofReal_pou_weight
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) β)).mul hF
    · intro x hx_not_overlap
      simp only [Set.mem_inter_iff, not_and] at hx_not_overlap
      by_cases hxβ : x ∈ (chartAt H β).source
      · have hxα : x ∉ (chartAt H α).source := hx_not_overlap hxβ
        rw [hF_support x hxα]
        simp
      · have hρβ_zero :
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M β : M → ℝ) x = 0 := by
          have hsub :=
            CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate (I := I) (M := M) β
          have hxnotsupp : x ∉ tsupport
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M β : M → ℝ) := by
            intro hcontra
            exact hxβ (hsub hcontra)
          exact image_eq_zero_of_notMem_tsupport hxnotsupp
        rw [hρβ_zero]
        simp
  rw [Finset.sum_congr rfl h_each_eq]
  have hF_eq : ∀ x : M,
      ENNReal.ofReal
          (∑ β ∈ S, (CalabiYau.RiemannianVolume.chartAtlasPOU I M β : M → ℝ) x) * F x =
        ∑ β ∈ S, ENNReal.ofReal
          ((CalabiYau.RiemannianVolume.chartAtlasPOU I M β : M → ℝ) x) * F x := by
    intro x
    have hnonneg : ∀ β ∈ S,
        0 ≤ (CalabiYau.RiemannianVolume.chartAtlasPOU I M β : M → ℝ) x := fun β _ =>
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M).nonneg β x
    have hsum_eq : ENNReal.ofReal
          (∑ β ∈ S, (CalabiYau.RiemannianVolume.chartAtlasPOU I M β : M → ℝ) x) =
        ∑ β ∈ S, ENNReal.ofReal
          ((CalabiYau.RiemannianVolume.chartAtlasPOU I M β : M → ℝ) x) := by
      induction S using Finset.cons_induction with
      | empty => simp
      | cons a s has ih =>
          rw [Finset.sum_cons, Finset.sum_cons]
          have hnonneg' :
              0 ≤ (CalabiYau.RiemannianVolume.chartAtlasPOU I M a : M → ℝ) x :=
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M).nonneg a x
          have hsum_nn :
              0 ≤ ∑ β ∈ s, (CalabiYau.RiemannianVolume.chartAtlasPOU I M β : M → ℝ) x :=
            Finset.sum_nonneg fun β _ =>
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M).nonneg β x
          rw [ENNReal.ofReal_add hnonneg' hsum_nn]
          have hih : ENNReal.ofReal
              (∑ β ∈ s, (CalabiYau.RiemannianVolume.chartAtlasPOU I M β : M → ℝ) x) =
            ∑ β ∈ s, ENNReal.ofReal
              ((CalabiYau.RiemannianVolume.chartAtlasPOU I M β : M → ℝ) x) := by
            apply ih
          rw [hih]
    rw [hsum_eq, Finset.sum_mul]
  have hsum_one : ∀ x : M,
      ENNReal.ofReal
          (∑ β ∈ S, (CalabiYau.RiemannianVolume.chartAtlasPOU I M β : M → ℝ) x) =
        1 := by
    intro x
    rw [chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x]
    simp
  rw [← MeasureTheory.lintegral_finsetSum]
  · refine MeasureTheory.lintegral_congr (fun x => ?_)
    rw [← hF_eq x, hsum_one x, one_mul]
  · intro β _
    exact ((CalabiYau.RiemannianVolume.measurable_ofReal_pou_weight
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M) β)).mul hF

end Chart
end Sobolev
