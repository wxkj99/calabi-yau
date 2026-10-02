-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Tensor/RSTensor/Algebra/Contraction.lean
-- Locally modified.
/-
Authors: Yuan Liao, Jack McCarthy
Modified by: Ziyang Qin
-/
module
public import CalabiYau.Geometry.Manifold.Tensor.RSTensor.Defs
public import CalabiYau.Geometry.Manifold.Tensor.Multilinear.Curry.Basic
public import CalabiYau.Geometry.Manifold.Tensor.Multilinear.Bundle.TensorProduct
public import CalabiYau.Geometry.Manifold.Tensor.RSTensor.Coordinates.Field
public import CalabiYau.Geometry.Manifold.Tensor.Multilinear.PredualBasis
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Topology.VectorBundle.Basic
public import Mathlib.LinearAlgebra.Trace
