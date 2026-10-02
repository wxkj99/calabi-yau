-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/External/DeGiorgi/Common.lean
-- Locally modified.
-- Modified 2026-04-28: updated internal import paths for project namespace
module
public import Mathlib

@[expose] public section

/-!
# Common Prelude

This module is the shared prelude for the De Giorgi development.

Policy:

- imports come directly from `Mathlib`;
- declarations in this directory live under `DeGiorgi`;
- shared opens and scoped notations live here so the theorem files stay small.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace DeGiorgi

end DeGiorgi
