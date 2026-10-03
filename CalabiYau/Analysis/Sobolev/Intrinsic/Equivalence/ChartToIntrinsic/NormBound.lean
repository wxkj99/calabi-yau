-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Intrinsic/Equivalence/ChartToIntrinsic/NormBound.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Intrinsic.Equivalence.Basic
public import CalabiYau.Analysis.Sobolev.Intrinsic.Lp.Basic
public import CalabiYau.Analysis.Sobolev.Approximation.Density.FirstOrder
public import CalabiYau.Analysis.Sobolev.Chart.RiemannianMeasureComparison
public import CalabiYau.Analysis.Sobolev.Manifold.Measure.UniformChartComparison
public import CalabiYau.Analysis.Sobolev.Manifold.Embedding.Subcritical
public import CalabiYau.Analysis.Sobolev.Manifold.Morrey.Basic
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Global.IntegrationByParts
public import CalabiYau.Geometry.Riemannian.Operator.Laplacian.Basic
public import CalabiYau.Geometry.Riemannian.Volume.Family.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace Sobolev
namespace Equivalence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open Sobolev.Chart
open Sobolev.Intrinsic
open Sobolev.IntrinsicLp

theorem eLpNorm_riemannianVolumeMeasure_le_const_mul_wkpNormChart_uniform
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] (g : CalabiYau.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, Measurable u →
        eLpNorm u p
            (CalabiYau.RiemannianVolume.riemannianVolumeMeasure I M g) ≤
          ENNReal.ofReal C *
            wkpNormChart (I := I) (M := M) 1 p u := by
  classical
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  let : MeasurableSpace M := borel M
  have : BorelSpace M := ⟨rfl⟩
  set S : Finset M :=
    CalabiYau.RiemannianVolume.chartAtlasPOUFinset (I := I) (M := M)
    with hS_def
  set ρ := CalabiYau.RiemannianVolume.chartAtlasPOU I M with hρ_def
  have h_bridge_α : ∀ α : M, ∃ C_α : ℝ, 0 < C_α ∧
      ∀ {u : M → ℝ}, Measurable u → tsupport u ⊆ tsupport (ρ α : M → ℝ) →
        eLpNorm u p
            (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g ρ)
          ≤ ENNReal.ofReal C_α *
              eLpNorm
                (Sobolev.Chart.chartPushedRaw I α u) p
                ((volume :
                  Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
                  (Sobolev.Chart.chartTargetEuclid
                    (I := I) (M := M) α)) := by
    intro α
    set Kα : Set M := tsupport (ρ α : M → ℝ) with hKα_def
    have hKα_compact : IsCompact Kα := (isClosed_tsupport _).isCompact
    have hKα_sub : Kα ⊆ (chartAt H α).source :=
      CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M α
    obtain ⟨C_α, hC_α_pos, hbound⟩ :=
      eLpNorm_riemannianMeasure_le_const_mul_eLpNorm_chartPushedRaw_uniform_of_subset
        (I := I) (M := M) g α hKα_compact hKα_sub hp_one hp_top
    exact ⟨C_α, hC_α_pos, hbound⟩
  set Cα : M → ℝ := fun α => Classical.choose (h_bridge_α α) with hCα_def
  have hCα_pos : ∀ α : M, 0 < Cα α := fun α => (Classical.choose_spec (h_bridge_α α)).1
  have hCα_bound : ∀ α : M, ∀ {u : M → ℝ}, Measurable u →
      tsupport u ⊆ tsupport (ρ α : M → ℝ) →
      eLpNorm u p
          (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g ρ)
        ≤ ENNReal.ofReal (Cα α) *
            eLpNorm
              (Sobolev.Chart.chartPushedRaw I α u) p
              ((volume :
                Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
                (Sobolev.Chart.chartTargetEuclid
                  (I := I) (M := M) α)) := fun α =>
    (Classical.choose_spec (h_bridge_α α)).2
  refine ⟨∑ α ∈ S, Cα α, Finset.sum_nonneg (fun α _ => (hCα_pos α).le), ?_⟩
  intro u hu_meas
  rw [CalabiYau.RiemannianVolume.riemannianVolumeMeasure_def
    (I := I) (M := M) g]
  have h_eLpNorm_eq :
      eLpNorm u p (CalabiYau.RiemannianVolume.riemannianMeasure
          (I := I) g ρ) =
        eLpNorm (∑ α ∈ S, fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) p
          (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g ρ) := by
    refine eLpNorm_congr_ae ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Finset.sum_apply]
    change u x = ∑ α ∈ S, (ρ α : M → ℝ) x * u x
    have hsum : ∑ α ∈ S, (ρ α : M → ℝ) x = 1 :=
      Sobolev.Chart.chartAtlasPOU_finset_sum_eq_one
        (I := I) (M := M) x
    rw [← Finset.sum_mul, hsum, one_mul]
  rw [h_eLpNorm_eq]
  refine (eLpNorm_sum_le hp_one).trans ?_
  have h_per_α : ∀ α ∈ S,
      eLpNorm (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) p
        (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g ρ) ≤
      ENNReal.ofReal (Cα α) *
        wkpNormChart (I := I) (M := M) 1 p u := by
    intro α _
    have h_support : tsupport (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) ⊆
        tsupport (ρ α : M → ℝ) := by
      have h_eq : (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) =
          (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x • u x) := by funext x; rfl
      rw [h_eq]
      exact tsupport_smul_subset_left
        (f := fun x : M => ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) (g := u)
    have h_meas : Measurable (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) :=
      (ρ α).contMDiff.continuous.measurable.mul hu_meas
    have h_bridge := hCα_bound α h_meas h_support
    refine h_bridge.trans ?_
    have h_ae :=
      Sobolev.Chart.chartPushed_eq_chartPushedRaw_pou_ae
        (I := I) (M := M) ρ α u
    have h_eLpNorm_eq :
        eLpNorm
            (Sobolev.Chart.chartPushedRaw I α
              (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x)) p
            ((volume :
              Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (Sobolev.Chart.chartTargetEuclid
                (I := I) (M := M) α)) =
          eLpNorm
            (Sobolev.Chart.chartPushed
              (I := I) (M := M) ρ α u) p
            ((volume :
              Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (Sobolev.Chart.chartTargetEuclid
                (I := I) (M := M) α)) :=
      eLpNorm_congr_ae h_ae.symm
    rw [h_eLpNorm_eq]
    have h1 :=
      Sobolev.Chart.eLpNorm_chartPushed_p_le_wkpNorm_one
        (I := I) (M := M) (p := p) u α
    gcongr
  refine (Finset.sum_le_sum h_per_α).trans ?_
  rw [← Finset.sum_mul]
  gcongr
  rw [show (∑ α ∈ S, ENNReal.ofReal (Cα α)) = ENNReal.ofReal (∑ α ∈ S, Cα α) from ?_]
  refine (ENNReal.ofReal_sum_of_nonneg (fun α _ => (hCα_pos α).le)).symm

end Equivalence
end Sobolev
