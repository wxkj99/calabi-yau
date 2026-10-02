-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Euclidean/Embedding/Morrey/Basic.lean
-- Locally modified.
module
public import CalabiYau.Analysis.DeGiorgi.SobolevSpace.Witnesses
public import CalabiYau.Analysis.DeGiorgi.SobolevSpace.Approximation
public import CalabiYau.Analysis.DeGiorgi.Poincare
public import CalabiYau.Analysis.DeGiorgi.SobolevPoincare
public import CalabiYau.Analysis.DeGiorgi.UnitBallApproximation
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Integral.Average
public import CalabiYau.Analysis.Sobolev.Euclidean.Embedding.Morrey.RieszKernel
public import CalabiYau.Analysis.Sobolev.Euclidean.Embedding.Morrey.SmoothHolderBound
public import CalabiYau.Analysis.Sobolev.Euclidean.Embedding.Morrey.SmoothInequality
