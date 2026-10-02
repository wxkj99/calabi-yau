-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Tensor/Coordinates/PartialDerivative.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Manifold.Tensor.Coordinates.ModelBasis
public import Mathlib.Analysis.Calculus.FDeriv.Basic

@[expose] public section

noncomputable section

namespace CalabiYau.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]

def partialDeriv (i : Fin (Module.finrank ℝ E)) (u : E → ℝ) (y : E) : ℝ :=
  fderiv ℝ u y ((chartModelBasis E) i)

end CalabiYau.Tensor.Coordinates
