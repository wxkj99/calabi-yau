-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Manifold/Morrey/HigherOrder.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Euclidean.Embedding.Morrey.HigherOrder
public import CalabiYau.Analysis.Sobolev.Manifold.Morrey.Basic
public import CalabiYau.Analysis.Sobolev.Chart.SmoothDensity.ChartSobolevDensity

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function Sobolev.Chart
  Sobolev.EuclideanMorrey
open scoped Manifold ContDiff ENNReal NNReal

namespace CalabiYau
namespace Analysis
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

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [T2Space M] [CompactSpace M] [I.Boundaryless]

private lemma memWkp_chartSmoothExt_pou_mul
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (k : ℕ) :
    Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k p
      (chartSmoothExt (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set h : EuclN → ℝ := chartSmoothExt (I := I) (M := M) α
    (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) x * u x) with hh_def
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hh_smooth : ContDiff ℝ ∞ h := by
    rw [hh_def]
    exact contDiff_chartSmoothExt_pou_mul (I := I) (M := M) α
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M)
      (CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M) hu
  have hh_smooth_top : ContDiff ℝ (⊤ : ℕ∞) h := hh_smooth
  have hh_compact : HasCompactSupport h := by
    rw [hh_def]
    exact hasCompactSupport_chartSmoothExt_pou_mul (I := I) (M := M) α
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M)
      (CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M) u
  have hh_support : tsupport h ⊆ Ω := by
    rw [hh_def, hΩ_def]
    have h1 : tsupport (chartSmoothExt (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x)) ⊆ chartCarrier (I := I) (M := M) α :=
      tsupport_chartSmoothExt_pou_mul_subset_chartCarrier (I := I) (M := M) α u
    exact h1.trans (chartCarrier_subset_chartTargetEuclid (I := I) (M := M) α)
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  exact Sobolev.Euclidean.MemWkp_of_smooth_compactSupport
    (d := Module.finrank ℝ E) hΩ_open hh_smooth_top hh_compact hh_support hp_one k

private lemma memWkp_chartPushed_of_contMDiff
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (k : ℕ) :
    Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k p
      (chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hExt := memWkp_chartSmoothExt_pou_mul (I := I) (M := M) α hu hp_one k
  have h_ae := chartSmoothExt_ae_eq_chartPushed (I := I) (M := M) α u
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  refine (Sobolev.Euclidean.MemWkp_congr_ae
    (d := Module.finrank ℝ E) hp_one hΩ_open h_ae).mp hExt

theorem memWkpChart_of_contMDiff_k
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (k : ℕ)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    MemWkpChart (I := I) (M := M) k p u := by
  intro α
  exact memWkp_chartPushed_of_contMDiff (I := I) (M := M) α hu hp_one k

end Chart
end Sobolev
end Analysis
end CalabiYau
