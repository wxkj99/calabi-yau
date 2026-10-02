-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Integration/DivergenceTheorem/Global/CompactSupport.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Local.Formula
public import CalabiYau.Geometry.Riemannian.Operator.DirectionalDerivative
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Local.IntegrationByParts
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Local.ChartInvariance
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Global.PartitionOfUnity
public import CalabiYau.Geometry.Riemannian.Volume.Family.Basic
public import CalabiYau.Geometry.Riemannian.Volume.Basic
public import CalabiYau.Geometry.Riemannian.Volume.Invariance
public import CalabiYau.Geometry.Riemannian.Volume.Properties
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.Algebra.Support

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix ENNReal

namespace CalabiYau.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

lemma chartLocalMeasure_integral_eq_of_support_in_overlap
    (g : SmoothRiemannianMetric I M) (x₀ x₁ : M)
    (f : M → ℝ)
    (hsupp : ∀ x, x ∉ (chartAt H x₀).source ∩ (chartAt H x₁).source → f x = 0) :
    ∫ x, f x ∂(chartLocalMeasure (I := I) g x₀) =
      ∫ x, f x ∂(chartLocalMeasure (I := I) g x₁) := by
  set U : Set M := (chartAt H x₀).source ∩ (chartAt H x₁).source with hU_def
  have h₀ : ∫ x, f x ∂(chartLocalMeasure (I := I) g x₀)
      = ∫ x in U, f x ∂(chartLocalMeasure (I := I) g x₀) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hsupp).symm
  have h₁ : ∫ x, f x ∂(chartLocalMeasure (I := I) g x₁)
      = ∫ x in U, f x ∂(chartLocalMeasure (I := I) g x₁) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hsupp).symm
  rw [h₀, h₁]
  change ∫ x, f x ∂((chartLocalMeasure (I := I) g x₀).restrict U)
      = ∫ x, f x ∂((chartLocalMeasure (I := I) g x₁).restrict U)
  rw [chartLocalMeasure_restrict_overlap_eq (I := I) g x₀ x₁]

private lemma integrable_of_compactSupport_subset_chartSource
    [CompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf_cont : Continuous f)
    (hf_support : tsupport f ⊆ (chartAt H α).source) :
    Integrable f (chartLocalMeasure (I := I) g α) := by
  classical
  have hsupp_compact : IsCompact (tsupport f) :=
    .of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _)
  have hμ_support : chartLocalMeasure (I := I) g α (tsupport f) < ⊤ :=
    chartLocalMeasure_compact_lt_top (I := I) g α hsupp_compact hf_support
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖f x‖ ≤ C := by
    have hCpt := (isCompact_univ (X := M)).image hf_cont.norm
    obtain ⟨C, hCmem⟩ := hCpt.bddAbove
    exact ⟨C, fun x => hCmem ⟨x, Set.mem_univ _, rfl⟩⟩
  have hbnd : ∀ᵐ x ∂(chartLocalMeasure (I := I) g α),
      ENNReal.ofReal ‖f x‖ ≤
        ENNReal.ofReal C * (tsupport f).indicator (fun _ => (1 : ℝ≥0∞)) x := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    by_cases hx : x ∈ tsupport f
    · rw [Set.indicator_of_mem hx, mul_one]
      exact ENNReal.ofReal_le_ofReal (hC x)
    · rw [Set.indicator_of_notMem hx, mul_zero]
      have hfx_zero : f x = 0 := by
        by_contra hne
        exact hx (subset_tsupport _ hne)
      rw [hfx_zero]; simp
  refine ⟨hf_cont.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  calc ∫⁻ x, ENNReal.ofReal ‖f x‖ ∂(chartLocalMeasure (I := I) g α)
      ≤ ∫⁻ x, ENNReal.ofReal C *
            (tsupport f).indicator (fun _ => (1 : ℝ≥0∞)) x
            ∂(chartLocalMeasure (I := I) g α) := lintegral_mono_ae hbnd
    _ = ENNReal.ofReal C * chartLocalMeasure (I := I) g α (tsupport f) := by
          rw [lintegral_const_mul _ ((measurable_const).indicator
            (isClosed_tsupport _).measurableSet)]
          rw [lintegral_indicator (isClosed_tsupport _).measurableSet]
          rw [setLIntegral_const, one_mul]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμ_support

end CalabiYau.DivergenceTheorem
