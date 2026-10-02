-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Geometry/Metric/TensorInner/Tensor0S/Chart/ContinuousLinearMap.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Manifold.Tensor.RSTensor.Defs
public import CalabiYau.Geometry.Riemannian.TensorInner.Tangent.Riemannian
public import CalabiYau.Geometry.Riemannian.Metric.PointwiseInner.Defs
public import CalabiYau.Geometry.Riemannian.Metric.PointwiseInner.Algebra
public import CalabiYau.Geometry.Riemannian.Metric.PointwiseInner.DualMetric
public import CalabiYau.Geometry.Riemannian.Metric.Coordinates.ChartGram
public import CalabiYau.Geometry.Riemannian.TensorInner.Tensor0S.Chart.Inner
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Topology.VectorBundle.Riemannian
public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
