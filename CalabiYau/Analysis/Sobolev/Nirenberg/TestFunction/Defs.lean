-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Nirenberg/TestFunction/Defs.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Tools.DifferenceQuotient

@[expose] public section

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open scoped ENNReal NNReal Convolution Pointwise BigOperators

namespace Sobolev.NirenbergTestFunction

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

noncomputable def nirenbergTestFunction
    (k : Fin d) (h : ℝ) (η u : E → ℝ) : E → ℝ :=
  Sobolev.diffQuot k (-h)
    (fun y : E => η y ^ 2 *
      Sobolev.diffQuot k h u y)

end Sobolev.NirenbergTestFunction
