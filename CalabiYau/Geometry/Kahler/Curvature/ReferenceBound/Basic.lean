module

public import CalabiYau.Geometry.Kahler.Basic
public import CalabiYau.Geometry.Kahler.Curvature.Chart

/-!
# Reference curvature in orthonormal complex frames

The coefficient matrix has holomorphic row and antiholomorphic column indices.  Consequently
`P.transpose * g * P.map star = 1`, and four curvature slots contract in the order
`P`, `star P`, `P`, `star P`.  This low-level formulation is used by the fixed-chart estimate and
the chart-transition theorem.
-/

@[expose] public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- The coordinate matrix of an orthonormal complex frame at `x`, using the metric coefficient
matrix in the chart centered at `x`. -/
def IsReferenceOrthonormalFrame (ω₀ : KahlerForm n M) (x : M)
    (P : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  Matrix.transpose P *
      ω₀.metricInChart x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) * P.map star = 1

/-- A component of the reference curvature tensor evaluated in the orthonormal frame whose column
matrix is `P`. -/
noncomputable def referenceCurvatureComponent (ω₀ : KahlerForm n M) (x : M)
    (P : Matrix (Fin n) (Fin n) ℂ) (p q j k : Fin n) : ℂ :=
  ∑ a, ∑ b, ∑ c, ∑ d,
    P a p * star (P b q) * P c j * star (P d k) *
      chartCurvature (fun z ↦ ω₀.metricInChart x z)
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) a b c d

/-- Coordinate transition from the chart at `y` into the chart at `x`; only values on the
open overlap are used. -/
noncomputable def referenceChartTransition (x y : M) :
    EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) :=
  (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x) ∘
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).symm

/-- The complex Jacobian of the centered chart transition, evaluated at `y`. -/
noncomputable def referenceTransitionMatrix (x y : M) : Matrix (Fin n) (Fin n) ℂ :=
  EuclideanSpace.clmMatrix (fderiv ℂ (referenceChartTransition (n := n) x y)
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y))

end KahlerForm
