module
public import CalabiYau.Geometry.Manifold.DifferentialForm.Stokes.Global.FiniteAtlas

/-!
# Independence and supported localization of constructed form integrals

Lee, *Introduction to Smooth Manifolds*, 2nd ed., Proposition 16.5,
pp. 405–406. The existing common-refinement theorem compares two actual
finite chart sums. Positivity for the same bundled reference form supplies
compatibility on every component of each restricted overlap.
-/

@[expose] public section

open Set
open scoped Topology Manifold ContDiff

noncomputable section

namespace CalabiYau.DifferentialForm

variable {d : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (Fin d → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ M]
  [T2Space M] [CompactSpace M]

/-- Atlas and partition choices do not change the constructed linear map when
both sets of restricted charts are positive for the same reference form. -/
theorem FinitePositiveChartPartition.integral_eq
    {ν : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d}
    (A B : FinitePositiveChartPartition ν) :
    A.integral = B.integral := by
  apply LinearMap.ext
  intro η
  exact partitionChartIntegral_eq A.charts B.charts A.partition B.partition
    A.indices B.indices A.sum_eq_one B.sum_eq_one A.subordinate B.subordinate
    (fun i hi j hj => OrientedLocalChart.compatible_of_isPositiveFor
      (A.charts i) (B.charts j) ν (A.positive i hi) (B.positive j hj)) η

/-- The local formula is for CLOSED support inside a restricted positive
chart domain, not for a whole canonical source with an assumed uniform sign. -/
theorem FinitePositiveChartPartition.integral_eq_of_supported
    {ν : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d}
    (A : FinitePositiveChartPartition ν)
    (C : OrientedLocalChart d M) (hC : C.IsPositiveFor ν)
    (η : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d)
    (hη : closure {p : M | η p ≠ 0} ⊆ C.domain) :
    A.integral η = signedChartIntegral C η := by
  exact partitionChartIntegral_eq_of_supported A.charts A.partition A.indices
    A.sum_eq_one A.subordinate C
    (fun i hi => OrientedLocalChart.compatible_of_isPositiveFor
      (A.charts i) C ν (A.positive i hi) hC) η hη

end CalabiYau.DifferentialForm
