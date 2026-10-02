module
public import CalabiYau.Geometry.Manifold.DifferentialForm.Stokes.Global.FormIntegral

/-!
# Finite weighted assembly for the constructed reference-form integral

Given the actual positive finite chart partition, per-chart weighted coefficient
identities, and genuine integrability of each weighted density term, assemble the
chart sums into the global density integral. This is finite partition algebra only;
it does not construct a new functional or assert a chartwise Stokes theorem.

Source: Lee, *Introduction to Smooth Manifolds*, 2nd ed., equation (16.2), p. 405,
Propositions 16.5–16.6(a), pp. 405–407.
-/

@[expose] public section

open MeasureTheory Set
open scoped Topology Manifold ContDiff

namespace CalabiYau.DifferentialForm

variable {d : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (Fin d → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ M]
  [MeasurableSpace M] [T2Space M] [CompactSpace M]

/-- The constructed reference integral equals a density integral once every
weighted chart coefficient has its independently proved native-density formula. -/
theorem referenceFormIntegral_eq_densityIntegral_of_chartwise
    (ν : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d)
    (hν : ∀ p : M, ν p ≠ 0)
    (A : FinitePositiveChartPartition ν)
    (η : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d)
    (μ : Measure M) (f : M → ℝ)
    (hInt : ∀ i ∈ A.indices, Integrable (fun x => A.partition i x * f x) μ)
    (hlocal : ∀ i ∈ A.indices,
      (∫ y : Fin d → ℝ, (A.charts i).sign.val *
        (A.partition i ((extChartAt 𝓘(ℝ, Fin d → ℝ) (A.charts i).center).symm y) *
          chartTopCoefficient (A.charts i).center η y) ∂(volume : Measure (Fin d → ℝ))) =
        ∫ x, A.partition i x * f x ∂μ) :
    referenceFormIntegral ν hν η = ∫ x, f x ∂μ := by
  rw [referenceFormIntegral_apply_weighted ν hν A η]
  calc
    _ = ∑ i ∈ A.indices, ∫ x, A.partition i x * f x ∂μ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hlocal i hi
    _ = ∫ x, ∑ i ∈ A.indices, A.partition i x * f x ∂μ := by
      symm
      apply integral_finsetSum
      intro i hi
      exact hInt i hi
    _ = ∫ x, f x ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [← Finset.sum_mul, A.sum_eq_one x, one_mul]

end CalabiYau.DifferentialForm
