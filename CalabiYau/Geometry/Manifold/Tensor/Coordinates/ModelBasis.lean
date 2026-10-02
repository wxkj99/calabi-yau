-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Tensor/Coordinates/ModelBasis.lean
-- Locally modified.
module
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Dimension.Free

@[expose] public section

noncomputable section

namespace CalabiYau.Tensor.Coordinates

@[irreducible] def chartModelBasis (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] :
    Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
  (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis.map
    (toEuclidean (E := E)).symm.toLinearEquiv

@[simp] lemma chartModelBasis_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (i : Fin (Module.finrank ℝ E)) :
    chartModelBasis E i =
      (toEuclidean (E := E)).symm (EuclideanSpace.single i (1 : ℝ)) := by
  classical
  with_unfolding_all
    change (toEuclidean (E := E)).symm.toLinearEquiv
        ((EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis i) =
      (toEuclidean (E := E)).symm (EuclideanSpace.single i (1 : ℝ))
  simp [OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_apply (𝕜 := ℝ) (ι := Fin (Module.finrank ℝ E))]

end CalabiYau.Tensor.Coordinates
