-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Approximation/Density/Preliminaries.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Chart.SmoothDensity.ChartSobolevDensity
public import CalabiYau.Analysis.Sobolev.Chart.ChartTransition.ChartPullbackSmooth
public import CalabiYau.Analysis.Sobolev.Chart.ChartTransition.Transition
public import CalabiYau.Analysis.Sobolev.Chart.SmoothDensity.Defs
public import CalabiYau.Analysis.Sobolev.Euclidean.Density
public import CalabiYau.Analysis.Sobolev.Chart.Defs
public import CalabiYau.Geometry.Riemannian.Volume.Family.Basic

@[expose] public section

-- Private declarations used in public declarations require the compatibility option below.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace Sobolev
namespace Chart

variable {E H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem contMDiff_finsetSum_chartPullback
    [T2Space M]
    {ι : Type*} (S : Finset ι) (α : ι → M)
    (ψ : ι → EuclN → ℝ)
    (hψ_smooth : ∀ i ∈ S, ContDiff ℝ (⊤ : ℕ∞) (ψ i))
    (hψ_compact : ∀ i ∈ S, HasCompactSupport (ψ i))
    (hψ_support : ∀ i ∈ S,
      tsupport (ψ i) ⊆ chartTargetEuclid (I := I) (M := M) (α i)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => ∑ i ∈ S, chartPullback I (α i) (ψ i) x) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact contMDiff_const
  | insert i S hiS ih =>
      have h_smooth_i : ContMDiff I 𝓘(ℝ, ℝ) ∞ (chartPullback I (α i) (ψ i)) :=
        chartPullback_contMDiff (I := I) (M := M) (α i)
          (hψ_smooth i (Finset.mem_insert_self i S))
          (hψ_compact i (Finset.mem_insert_self i S))
          (hψ_support i (Finset.mem_insert_self i S))
      have ih' : ContMDiff I 𝓘(ℝ, ℝ) ∞
          (fun x : M => ∑ j ∈ S, chartPullback I (α j) (ψ j) x) := by
        refine ih ?_ ?_ ?_
        · intro j hj
          exact hψ_smooth j (Finset.mem_insert.mpr (Or.inr hj))
        · intro j hj
          exact hψ_compact j (Finset.mem_insert.mpr (Or.inr hj))
        · intro j hj
          exact hψ_support j (Finset.mem_insert.mpr (Or.inr hj))
      have h_eq : (fun x : M => ∑ j ∈ insert i S, chartPullback I (α j) (ψ j) x) =
          (fun x : M => chartPullback I (α i) (ψ i) x +
            ∑ j ∈ S, chartPullback I (α j) (ψ j) x) := by
        funext x
        rw [Finset.sum_insert hiS]
      rw [h_eq]
      exact h_smooth_i.add ih'

omit [IsManifold I ∞ M] in
lemma chartPushed_finset_sum
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M)
    {ι : Type*} (S : Finset ι) (f : ι → M → ℝ) :
    chartPushed (I := I) (M := M) ρ α (fun x => ∑ i ∈ S, f i x) =
      (fun y => ∑ i ∈ S,
        chartPushed (I := I) (M := M) ρ α (f i) y) := by
  classical
  funext y
  unfold chartPushed
  rw [Finset.mul_sum]

theorem wkpNormChart_eq_finset_sum
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (k : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p) (u : M → ℝ) :
    wkpNormChart (I := I) (M := M) k p u =
      ∑ α ∈ CalabiYau.RiemannianVolume.chartAtlasPOUFinset
              (I := I) (M := M),
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p
          (chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
          (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  unfold wkpNormChart
  set f : M → ℝ≥0∞ := fun α =>
    Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) k p
      (chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
      (chartTargetEuclid (I := I) (M := M) α) with hf_def
  have hf_zero_off : ∀ α : M, α ∉
      CalabiYau.RiemannianVolume.chartAtlasPOUFinset
        (I := I) (M := M) → f α = 0 := by
    intro α hα
    have hρ_zero : ∀ x : M, (CalabiYau.RiemannianVolume.chartAtlasPOU
        I M α : M → ℝ) x = 0 := by
      intro x
      exact CalabiYau.RiemannianVolume.chartAtlasPOU_weight_zero_of_notMem
        (I := I) (M := M) hα x
    have hChartPushed_zero : chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u =
        (fun _ => (0 : ℝ)) := by
      funext y
      unfold chartPushed
      rw [hρ_zero]
      ring
    change Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) k p
      (chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
      (chartTargetEuclid (I := I) (M := M) α) = 0
    rw [hChartPushed_zero]
    exact Sobolev.Euclidean.wkpNorm_zero_fun_zero
      (d := Module.finrank ℝ E) hp
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
  rw [tsum_eq_sum hf_zero_off]

end Chart
end Sobolev
