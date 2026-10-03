-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Manifold/Embedding/Basic.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Chart.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Group.NullSubmodule
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Topology.Bornology.BoundedOperation

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

theorem Euclidean.wkpNorm_zero_le_wkpNorm
    {d : ℕ} {k : ℕ} {p : ℝ≥0∞} {u : EuclideanSpace ℝ (Fin d) → ℝ}
      {Ω : Set (EuclideanSpace ℝ (Fin d))} :
    eLpNorm u p (MeasureTheory.volume.restrict Ω) ≤
      Sobolev.Euclidean.iteratedWeakSobolevNorm (d := d) k p u Ω := by
  classical
  let innerSum : ℕ → ℝ≥0∞ := fun j =>
    ∑ α : Fin j → Fin d,
      eLpNorm
        (Sobolev.Euclidean.iterWeakPartial
          (d := d) p j α u Ω) p (MeasureTheory.volume.restrict Ω)
  have hWkp : Sobolev.Euclidean.iteratedWeakSobolevNorm (d := d) k p u
    Ω =
      ∑ j ∈ Finset.range (k + 1), innerSum j :=
    Sobolev.Euclidean.wkpNorm_eq_sum k p u Ω
  have h_inner0 : innerSum 0 = eLpNorm u p (MeasureTheory.volume.restrict Ω) := by
    simp only [innerSum]
    have hUniq : ∀ α : Fin 0 → Fin d, α = (fun i : Fin 0 => i.elim0) := fun α => by
      funext i; exact i.elim0
    have : Unique (Fin 0 → Fin d) :=
      { default := fun i : Fin 0 => i.elim0
        uniq := fun α => (hUniq α).symm ▸ rfl }
    rw [Fintype.sum_unique
          (f := fun α : Fin 0 → Fin d =>
            eLpNorm (Sobolev.Euclidean.iterWeakPartial
              (d := d) p 0 α u Ω) p (MeasureTheory.volume.restrict Ω))]
    simp [Sobolev.Euclidean.iterWeakPartial_zero]
  have h0 : (0 : ℕ) ∈ Finset.range (k + 1) := by
    rw [Finset.mem_range]; omega
  have h_le : innerSum 0 ≤ ∑ j ∈ Finset.range (k + 1), innerSum j :=
    Finset.single_le_sum (f := innerSum) (fun _ _ => bot_le) h0
  rw [hWkp]
  rw [← h_inner0]
  exact h_le

theorem eLpNorm_chartPushed_p_le_wkpNorm_one
    [T2Space M] [SigmaCompactSpace M] {p : ℝ≥0∞} (u : M → ℝ) (α : M) :
    eLpNorm
        (chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
        p
        (MeasureTheory.volume.restrict (chartTargetEuclid (I := I) (M := M) α))
      ≤ wkpNormChart (I := I) (M := M) 1 p u := by
  classical
  have h_per_α :
      eLpNorm
          (chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
          p
          (MeasureTheory.volume.restrict (chartTargetEuclid (I := I) (M := M) α))
        ≤ Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 1 p
            (chartPushed (I := I) (M := M)
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
            (chartTargetEuclid (I := I) (M := M) α) :=
    Euclidean.wkpNorm_zero_le_wkpNorm
  have h_le_tsum : Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 p
        (chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ∑' β : M,
          Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 1 p
            (chartPushed (I := I) (M := M)
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M) β u)
            (chartTargetEuclid (I := I) (M := M) β) := by
    exact ENNReal.le_tsum (f := fun β : M =>
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 p
        (chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) β u)
        (chartTargetEuclid (I := I) (M := M) β)) α
  exact h_per_α.trans h_le_tsum

omit [IsManifold I ∞ M] in
private theorem chartPushed_eq_zero_off_image_tsupport
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (α : M) (u : M → ℝ) {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α)
    (hy_off : y ∉ toEuclidean '' ((extChartAt I α) '' (tsupport (ρ α : M → ℝ)))) :
    chartPushed (I := I) (M := M) ρ α u y = 0 := by
  obtain ⟨z, hz_target, hzy⟩ := hy_target
  have hsymm_source : (extChartAt I α).symm z ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hz_target
  have hz_eq : (extChartAt I α) ((extChartAt I α).symm z) = z :=
    (extChartAt I α).right_inv hz_target
  by_contra hne
  apply hy_off
  refine ⟨z, ?_, hzy⟩
  refine ⟨(extChartAt I α).symm z, ?_, hz_eq⟩
  have hy_eq : toEuclidean.symm y = z := by
    rw [← hzy]
    exact toEuclidean.symm_apply_apply z
  unfold chartPushed at hne
  rw [hy_eq] at hne
  have hρ_ne : (ρ α : C^∞⟮I, M; ℝ⟯) ((extChartAt I α).symm z) ≠ 0 := by
    intro h0
    apply hne
    rw [h0]; ring
  exact subset_tsupport _ (Function.mem_support.mpr hρ_ne)

variable {u : M → ℝ}

theorem chartPushed_support_subset_compact_in_target
    [T2Space M] [SigmaCompactSpace M]
    (α : M) (u : M → ℝ) :
    ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      y ∉ toEuclidean ''
            ((extChartAt I α) ''
              (tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M) α : M → ℝ))) →
        chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u y = 0 := by
  intro y hy_target hy_off
  exact chartPushed_eq_zero_off_image_tsupport (I := I) (M := M)
    (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u hy_target hy_off

end Chart
end Sobolev
