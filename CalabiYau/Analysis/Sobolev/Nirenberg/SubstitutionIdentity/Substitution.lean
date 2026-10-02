-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Nirenberg/SubstitutionIdentity/Substitution.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Nirenberg.H2Regularity.Defs
public import CalabiYau.Analysis.Sobolev.Nirenberg.TestFunction.Basic
public import CalabiYau.Analysis.Sobolev.Nirenberg.TestFunction.SmoothRegularity

@[expose] public section

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open Sobolev
open Sobolev.NirenbergEuclidean
open Sobolev.NirenbergTestFunction
open scoped ENNReal NNReal Convolution Pointwise BigOperators InnerProductSpace

namespace Sobolev.NirenbergSubstitution

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

end Sobolev.NirenbergSubstitution
