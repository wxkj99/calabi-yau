module
public import CalabiYau.Geometry.Manifold.DifferentialForm.Stokes.Global.FormIntegral
public import CalabiYau.Geometry.Manifold.DifferentialForm.Stokes.Global.OrientedPatching

/-!
# Stokes for the defined, choice-independent top-form integral

Lee, *Introduction to Smooth Manifolds*, 2nd ed., Theorem 16.11,
pp. 411–414. The finite positive atlas defining `referenceFormIntegral` also
localizes the primitive. The actual supported chart formula, already proved
by common refinement, discharges the intermediate chart-formula premise.

There is no arbitrary functional, chart formula, local Stokes identity, or
sign on an entire canonical chart source among the hypotheses. Positivity
is required only on the restricted chart domains selected in the construction.
The reference form fixes orientation, not a scalar integration density.
-/

@[expose] public section

open Set
open scoped Topology Manifold ContDiff

noncomputable section

namespace CalabiYau.DifferentialForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (Fin (n + 1) → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin (n + 1) → ℝ) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, Fin (n + 1) → ℝ) M]
  [T2Space M] [CompactSpace M]

/-- Stokes for the actual constructed integral on a compact oriented
boundaryless manifold of positive real dimension. `n = 0` means dimension
one, not a predecessor-form assertion in real dimension zero. Neither
connectedness nor nonemptiness is required. -/
theorem referenceFormIntegral_stokes
    (ν : DifferentialForm 𝓘(ℝ, Fin (n + 1) → ℝ) M (n + 1))
    (hν : ∀ p : M, ν p ≠ 0)
    (η : DifferentialForm 𝓘(ℝ, Fin (n + 1) → ℝ) M n) :
    referenceFormIntegral ν hν (exteriorDerivative η) = 0 := by
  let A := referenceFormPartition ν hν
  apply global_stokes_of_restricted_oriented_integral_formula
    (referenceFormIntegral ν hν) A.charts A.partition A.indices A.sum_eq_one
    A.subordinate ?_ η
  intro i hi γ hγ
  exact referenceFormIntegral_eq_signedChartIntegral ν hν
    (A.charts i) (A.positive i hi) γ hγ

end CalabiYau.DifferentialForm
