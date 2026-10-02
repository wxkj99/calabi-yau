module
public import CalabiYau.Geometry.Manifold.DifferentialForm.Basic

/-!
# The coefficient of a smooth top form in a specified manifold chart

Lee, *Introduction to Smooth Manifolds*, 2nd ed., §16, integration of
compactly supported forms in a coordinate chart. The ordered standard basis
fixes the sign even in dimensions zero and one. The coefficient is extended
by zero outside the chart target; no orientation or global integration is
presupposed.
-/

@[expose] public section

open Set
open scoped Topology Manifold ContDiff

noncomputable section

namespace CalabiYau.DifferentialForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (Fin n → ℝ) M] [IsManifold (𝓘(ℝ, Fin n → ℝ)) ∞ M]

/-- The scalar coefficient of a top-degree form in the ordered coordinate
basis of `extChartAt`, extended by zero off the coordinate image. There is no
absolute value: a reflection changes the coefficient's sign. -/
def chartTopCoefficient (x : M)
    (η : DifferentialForm (𝓘(ℝ, Fin n → ℝ)) M n) (y : Fin n → ℝ) : ℝ := by
  classical
  exact if y ∈ (extChartAt (𝓘(ℝ, Fin n → ℝ)) x).target then
    (trivializationAt ((Fin n → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin n) (Fin n → ℝ)
        (TangentSpace (𝓘(ℝ, Fin n → ℝ))) ℝ (Bundle.Trivial M ℝ)) x
      ⟨(extChartAt (𝓘(ℝ, Fin n → ℝ)) x).symm y,
        η ((extChartAt (𝓘(ℝ, Fin n → ℝ)) x).symm y)⟩).2
      (fun i : Fin n => Pi.single i (1 : ℝ))
  else 0

/-- Additivity of the actual chart coefficient (including the zero extension).
At `n=0` the ordered basis is empty; at `n=1` the sole vector is `1`.
No factor of two occurs in either case. -/
theorem chartTopCoefficient_add (x : M)
    (η ζ : DifferentialForm (𝓘(ℝ, Fin n → ℝ)) M n) (y : Fin n → ℝ) :
    chartTopCoefficient x (η + ζ) y =
      chartTopCoefficient x η y + chartTopCoefficient x ζ y := by
  classical
  unfold chartTopCoefficient
  split_ifs with hy
  · rw [continuousAlternatingMap_trivializationAt_apply,
      continuousAlternatingMap_trivializationAt_apply,
      continuousAlternatingMap_trivializationAt_apply]
    rw [add_apply, ContinuousAlternatingMap.compContinuousLinearMap_add]
    simp
  · simp

/-- Homogeneity of the signed chart coefficient, including a negative scalar. -/
theorem chartTopCoefficient_smul (x : M) (c : ℝ)
    (η : DifferentialForm (𝓘(ℝ, Fin n → ℝ)) M n) (y : Fin n → ℝ) :
    chartTopCoefficient x (c • η) y = c * chartTopCoefficient x η y := by
  classical
  unfold chartTopCoefficient
  split_ifs with hy
  · rw [continuousAlternatingMap_trivializationAt_apply,
      continuousAlternatingMap_trivializationAt_apply]
    rw [smul_apply, ContinuousAlternatingMap.compContinuousLinearMap_smul]
    simp
  · simp

end CalabiYau.DifferentialForm
