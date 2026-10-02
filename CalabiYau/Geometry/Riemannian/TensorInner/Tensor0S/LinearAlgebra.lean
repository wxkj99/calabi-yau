-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Geometry/Metric/TensorInner/Tensor0S/LinearAlgebra.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Riemannian.TensorInner.Cotangent.InverseMetric
public import CalabiYau.Geometry.Manifold.Connection.MetricCompatibility.Defs
public import CalabiYau.Geometry.Manifold.Coordinates.MetricCompatibility.Inverse
public import CalabiYau.Geometry.Manifold.Coordinates.MetricCompatibility.Covariant
public import CalabiYau.Geometry.Manifold.Coordinates.MetricCompatibility.Coordinate
public import CalabiYau.Geometry.Manifold.Coordinates.NablaComponents.Tensor0S
public import CalabiYau.Geometry.Manifold.Coordinates.NablaComponents.TwoTensor
public import CalabiYau.Geometry.Manifold.Connection.TensorNabla.Iterated.Basic
public import CalabiYau.Geometry.Manifold.Bundle.PartialMfderiv.Basic
public import CalabiYau.Geometry.Manifold.Bundle.PartialMfderiv.ModelMixed
public import CalabiYau.Geometry.Manifold.Coordinates.Calculus.FixedBaseDerivative
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
public import CalabiYau.Geometry.Riemannian.TensorInner.FiberMetric.Tensor0SMetric
