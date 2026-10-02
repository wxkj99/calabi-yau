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

end CalabiYau.DivergenceTheorem
