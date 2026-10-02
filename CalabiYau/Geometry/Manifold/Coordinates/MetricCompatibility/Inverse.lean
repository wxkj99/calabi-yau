-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Geometry/Coordinates/MetricCompatibility/Inverse.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Manifold.Connection.MetricCompatibility.Defs
public import CalabiYau.Geometry.Manifold.Coordinates.Connection.Christoffel
public import CalabiYau.Geometry.Manifold.Coordinates.Frame.Coordinate
public import CalabiYau.Geometry.Riemannian.Curvature.Riemann.RawFields
public import CalabiYau.Geometry.Riemannian.Operator.Scalar.Calculus
public import CalabiYau.Geometry.Riemannian.TensorInner.Cotangent.InverseMetric
public import CalabiYau.Geometry.Manifold.Bundle.PartialMfderiv.Basic
public import CalabiYau.Geometry.Manifold.Bundle.PartialMfderiv.ModelMixed
public import CalabiYau.Geometry.Manifold.Coordinates.Calculus.FixedBaseDerivative
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
