-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Integration/L2/CompactSupport.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Manifold.Connection.Realization.Embedding
public import CalabiYau.Geometry.Manifold.Connection.Realization.ConcreteConnection
public import CalabiYau.Geometry.Riemannian.L2.Basic
public import CalabiYau.Geometry.Riemannian.Volume.Properties
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.ContMDiffMap
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.SmoothApprox
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
