-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/External/DeGiorgi/UnitBallApproximation.lean
-- Locally modified.
module
public import CalabiYau.Analysis.DeGiorgi.UnitBallApproximationCore

@[expose] public section


/-!
# Chapter 02: Unit-Ball Approximation

This module is the public entry point for the unit-ball approximation results.

It re-exports the detailed implementation from
`DeGiorgi.UnitBallApproximationCore`, so downstream files can import the
approximation results through a stable public import.
-/
