-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Integration/Measure/Chart/Rellich.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Euclidean.Embedding.Rellich.Basic
public import CalabiYau.Analysis.Sobolev.Chart.Defs
public import CalabiYau.Analysis.Sobolev.Chart.AtlasNorm.Atlas
public import CalabiYau.Geometry.Riemannian.Volume.Basic
public import CalabiYau.Geometry.Riemannian.Volume.Family.Basic
public import CalabiYau.Geometry.Riemannian.Volume.Properties
public import CalabiYau.Geometry.Riemannian.Volume.Invariance
public import CalabiYau.Analysis.DeGiorgi.SobolevSpace
public import CalabiYau.Analysis.DeGiorgi.LpFunctionToolkit
public import CalabiYau.Analysis.DeGiorgi.SobolevSpace.Approximation
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

def pullbackToM
    (I : ModelWithCorners ℝ E H) (α : M)
    (w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) : M → ℝ := by
  classical
  exact fun x =>
    if x ∈ (chartAt H α).source then
      w (toEuclidean (extChartAt I α x))
    else 0

omit [IsManifold I ∞ M] in
lemma pullbackToM_apply_of_mem (α : M)
    (w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    {x : M} (hx : x ∈ (chartAt H α).source) :
    pullbackToM (M := M) I α w x =
      w (toEuclidean (extChartAt I α x)) := by
  classical
  unfold pullbackToM; simp [hx]

omit [IsManifold I ∞ M] in
lemma pullbackToM_apply_of_notMem (α : M)
    (w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    {x : M} (hx : x ∉ (chartAt H α).source) :
    pullbackToM (M := M) I α w x = 0 := by
  classical
  unfold pullbackToM; simp [hx]

omit [IsManifold I ∞ M] in
lemma pullbackToM_support_subset_source (α : M)
    (w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) :
    Function.support (pullbackToM (M := M) I α w) ⊆ (chartAt H α).source := by
  intro x hx
  by_contra h
  apply hx
  exact pullbackToM_apply_of_notMem (M := M) (I := I) α w h

omit [IsManifold I ∞ M] in
lemma pullbackToM_zero_of_notMem_source (α : M)
    (w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    {x : M} (hx : x ∉ (chartAt H α).source) :
    pullbackToM (M := M) I α w x = 0 :=
  pullbackToM_apply_of_notMem (M := M) (I := I) α w hx

omit [IsManifold I ∞ M] in
lemma pullbackToM_add (α : M)
    (w₁ w₂ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) :
    pullbackToM (M := M) I α (fun y => w₁ y + w₂ y) =
      fun x => pullbackToM (M := M) I α w₁ x +
        pullbackToM (M := M) I α w₂ x := by
  classical
  funext x
  unfold pullbackToM
  by_cases hx : x ∈ (chartAt H α).source
  · simp [hx]
  · simp [hx]

omit [IsManifold I ∞ M] in
lemma pullbackToM_sub (α : M)
    (w₁ w₂ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) :
    pullbackToM (M := M) I α (fun y => w₁ y - w₂ y) =
      fun x => pullbackToM (M := M) I α w₁ x -
        pullbackToM (M := M) I α w₂ x := by
  classical
  funext x
  unfold pullbackToM
  by_cases hx : x ∈ (chartAt H α).source
  · simp [hx]
  · simp [hx]

omit [IsManifold I ∞ M] in
lemma pullbackToM_chartPushed
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source))
    (α : M) (u : M → ℝ) :
    pullbackToM (M := M) I α
      (chartPushed (I := I) (M := M) ρ α u) =
        fun x => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x := by
  classical
  funext x
  by_cases hx : x ∈ (chartAt H α).source
  · rw [pullbackToM_apply_of_mem (M := M) (I := I) α _ hx]
    unfold chartPushed
    have htoeucl : toEuclidean.symm (toEuclidean (extChartAt I α x)) = extChartAt I α x := by
      simp
    rw [htoeucl]
    have hsymm : (extChartAt I α).symm (extChartAt I α x) = x := by
      apply (extChartAt I α).left_inv
      rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)]
      exact hx
    rw [hsymm]
  · rw [pullbackToM_apply_of_notMem (M := M) (I := I) α _ hx]
    have hxnotsupp : x ∉ tsupport ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
      intro hcontra
      exact hx (hρ α hcontra)
    have hρα_zero : ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0 :=
      image_eq_zero_of_notMem_tsupport hxnotsupp
    rw [hρα_zero]
    ring

end Chart
end Sobolev
