-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Geometry/Metric/TensorInner/FiberMetric/Tensor0SMetric.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Riemannian.TensorInner.Cotangent.Riemannian
public import CalabiYau.Geometry.Riemannian.Metric.MetricFiberData.Hom
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
