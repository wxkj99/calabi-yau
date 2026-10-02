module
public import CalabiYau.Geometry.Manifold.DifferentialForm.Stokes.Global.Independence

/-!
# The constructed global integral for a smooth reference orientation

Lee, *Introduction to Smooth Manifolds*, 2nd ed., equation (16.2), p. 405,
Proposition 16.5, pp. 405–406, and Proposition 16.6(a), p. 407. Select an
existing finite positive atlas and subordinate partition, construct the
finite-sum real-linear map, and prove that every other positive choice gives
the same map. Closed chart-supported forms have the actual signed local formula.

The reference `ν` is a bundled smooth nonvanishing top form. In a Kähler
application it is the actual bundled and transported `ωⁿ/n!`; no extra factor
is inserted here. This module neither assumes nor constructs a measure on M.
The Kähler bundle/model transport and the application of the completed local
Stokes theorem are separate frontiers. No arbitrary `Φ` or assumed chart
formula occurs in the definition or its characterization.
-/

@[expose] public section

open Set MeasureTheory
open scoped Topology Manifold ContDiff

noncomputable section

namespace CalabiYau.DifferentialForm

variable {d : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (Fin d → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ M]
  [T2Space M] [CompactSpace M]

/-- Select actual positive chart and partition data from the existing finite
atlas theorem. The nonvanishing hypothesis is on the bundled reference form. -/
def referenceFormPartition
    (ν : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d)
    (hν : ∀ p : M, ν p ≠ 0) : FinitePositiveChartPartition ν :=
  Classical.choice (exists_finitePositiveChartPartition ν hν)

/-- The global real-linear integral constructed from a finite positive atlas.
Independence below removes dependence on the selected atlas and partition. -/
def referenceFormIntegral
    (ν : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d)
    (hν : ∀ p : M, ν p ≠ 0) :
    DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d →ₗ[ℝ] ℝ :=
  (referenceFormPartition ν hν).integral

@[simp] theorem referenceFormIntegral_zero
    (ν : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d)
    (hν : ∀ p : M, ν p ≠ 0) : referenceFormIntegral ν hν 0 = 0 :=
  (referenceFormIntegral ν hν).map_zero

/-- Every finite positive choice computes the same constructed linear map. -/
theorem referenceFormIntegral_eq
    (ν : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d)
    (hν : ∀ p : M, ν p ≠ 0) (A : FinitePositiveChartPartition ν) :
    referenceFormIntegral ν hν = A.integral := by
  exact (referenceFormPartition ν hν).integral_eq A

/-- The actual supported chart formula, with restricted reference positivity
and closed-support containment explicit rather than assumed for arbitrary Φ. -/
theorem referenceFormIntegral_eq_signedChartIntegral
    (ν : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d)
    (hν : ∀ p : M, ν p ≠ 0)
    (C : OrientedLocalChart d M) (hC : C.IsPositiveFor ν)
    (η : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d)
    (hη : closure {p : M | η p ≠ 0} ⊆ C.domain) :
    referenceFormIntegral ν hν η = signedChartIntegral C η := by
  exact (referenceFormPartition ν hν).integral_eq_of_supported C hC η hη

/-- Compute the selected global map in any finite positive partition by the
explicit weighted signed coordinate formula against coordinate Lebesgue volume. -/
theorem referenceFormIntegral_apply_weighted
    (ν : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d)
    (hν : ∀ p : M, ν p ≠ 0) (A : FinitePositiveChartPartition ν)
    (η : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d) :
    referenceFormIntegral ν hν η = ∑ i ∈ A.indices,
      ∫ y : Fin d → ℝ, (A.charts i).sign.val *
        (A.partition i ((extChartAt 𝓘(ℝ, Fin d → ℝ) (A.charts i).center).symm y) *
          chartTopCoefficient (A.charts i).center η y) ∂volume := by
  rw [referenceFormIntegral_eq ν hν A]
  exact A.integral_apply_weighted η

end CalabiYau.DifferentialForm

section ConcreteChecks

open CalabiYau CalabiYau.DifferentialForm

-- Flat coordinates: this is the signed coefficient itself, not a density ratio.
-- In d=0 the basis is empty; in d=1 its sole vector is 1.
example {d : ℕ}
    (η : DifferentialForm 𝓘(ℝ, Fin d → ℝ) (Fin d → ℝ) d)
    (x y : Fin d → ℝ) :
    chartTopCoefficient x η y = η y (fun i : Fin d => Pi.single i (1 : ℝ)) := by
  classical
  unfold chartTopCoefficient
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_target, Set.mem_univ, if_true]
  rw [continuousAlternatingMap_trivializationAt_apply, TangentBundle.symmL_model_space]
  rfl

-- Genuine orientation reversal changes the integral sign in every dimension.
-- Unlike a coordinate reflection, here the coefficient is left unchanged.
example {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (Fin d → ℝ) M] [IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ M]
    (C D : OrientedLocalChart d M) (hc : D.center = C.center)
    (hs : (D.sign : ℝ) = -(C.sign : ℝ))
    (η : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d) :
    signedChartIntegral D η = -signedChartIntegral C η := by
  unfold signedChartIntegral
  rw [hc, hs]
  ring

end ConcreteChecks
