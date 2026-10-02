module

public import CalabiYau.MongeAmpere.Continuity.Openness.HolderSpaces

/-!
# Chart matrices and the uncentered continuity-path residual

The uncentered residual is defined here for use in the little-Hölder composition.
Both matrix functions are the actual metric plus complex Hessian, not auxiliary matrix-valued oracles.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology
open MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- The uncentered logarithmic residual before subtracting its volume average. -/
noncomputable def uncenteredContinuityPathResidual (ω₀ : KahlerForm n M) (F : M → ℝ)
    (t : ℝ) (φ : M → ℝ) (_hsol : ω₀.SolvesMongeAmpere
      (fun x ↦ t * F x + ω₀.pathConstant F t) φ)
    (u : M → ℝ) (δ : ℝ) : M → ℝ :=
  fun x ↦ Real.log (ω₀.mongeAmpere (φ + u) x / ω₀.mongeAmpere φ x) -
    (δ * F x + (ω₀.pathConstant F (t + δ) - ω₀.pathConstant F t))

/-- The actual perturbed metric matrix for a smooth order-two core element. -/
noncomputable def smoothCorePerturbedChartMatrix
    (ω₁ : KahlerForm n M)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (α : ℝ≥0) (v : SmoothChartHolderCore cover 2 α)
    (i : cover.ι) (z : EuclideanSpace ℂ (Fin n)) :
    Matrix (Fin n) (Fin n) ℂ :=
  ω₁.metricInChart (cover.base i) z +
    complexHessian
      (v.smoothMap ∘
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) z

/-- The same chart formula at the actual evaluated C² limit. -/
noncomputable def evaluatedPerturbedChartMatrix
    (ω₁ : KahlerForm n M) (α : ℝ≥0) [P : ContinuityHolderPair ω₁ α]
    (u : P.C2) (i : P.finiteChartCover.ι) (z : EuclideanSpace ℂ (Fin n)) :
    Matrix (Fin n) (Fin n) ℂ :=
  ω₁.metricInChart (P.finiteChartCover.base i) z +
    complexHessian
      ((P.evalC2 u) ∘
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (P.finiteChartCover.base i)).symm) z

end KahlerForm
