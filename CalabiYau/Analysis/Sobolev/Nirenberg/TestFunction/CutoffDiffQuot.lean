-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Nirenberg/TestFunction/CutoffDiffQuot.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Tools.DifferenceQuotient.WeakDerivative

@[expose] public section

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open Sobolev
open scoped ENNReal NNReal Convolution Pointwise BigOperators

namespace Sobolev.NirenbergTestFunction

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
theorem hasWeakPartialDeriv_cutoff_sq_mul_diffQuot
    (k j : Fin d) (h : ℝ) {η u g_j : E → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hu_localInt :
      LocallyIntegrable u ((volume : Measure E).restrict Set.univ))
    (hg_j_localInt :
      LocallyIntegrable g_j ((volume : Measure E).restrict Set.univ))
    (hwp : Sobolev.Euclidean.HasWeakPartialDeriv (d := d) j g_j u Set.univ) :
    Sobolev.Euclidean.HasWeakPartialDeriv (d := d) j
      (fun y => (η y)^2 * diffQuot k h g_j y +
        ((fderiv ℝ (fun z => (η z)^2) y) (EuclideanSpace.single j 1)) *
          diffQuot k h u y)
      (fun y => (η y)^2 * diffQuot k h u y) Set.univ := by
  have h_wp_dq :
      Sobolev.Euclidean.HasWeakPartialDeriv (d := d) j
        (diffQuot k h g_j) (diffQuot k h u) Set.univ :=
    hasWeakPartialDeriv_diffQuot (d := d) k j h hu_localInt hg_j_localInt hwp
  have h_dq_u_localInt :
      LocallyIntegrable (diffQuot k h u)
        ((volume : Measure E).restrict Set.univ) := by
    rw [Measure.restrict_univ] at hu_localInt ⊢
    exact locallyIntegrable_diffQuot (d := d) k h hu_localInt
  have h_dq_g_localInt :
      LocallyIntegrable (diffQuot k h g_j)
        ((volume : Measure E).restrict Set.univ) := by
    rw [Measure.restrict_univ] at hg_j_localInt ⊢
    exact locallyIntegrable_diffQuot (d := d) k h hg_j_localInt
  exact Sobolev.Euclidean.HasWeakPartialDeriv.mul_smooth (Ω := Set.univ)
    h_wp_dq (hη.pow 2) h_dq_u_localInt h_dq_g_localInt

end Sobolev.NirenbergTestFunction
