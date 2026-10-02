-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Euclidean/WeakDerivative/Distribution.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Euclidean.W1p.WeakDerivative
public import Mathlib.Analysis.Distribution.Distribution

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Sobolev.Euclidean

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
theorem integrable_mul_fderiv_apply_of_memLp
    {Ω : Set E} {w : E → ℝ} (hw : MemLp w 2 (volume.restrict Ω))
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (i : Fin d) :
    Integrable (fun x => w x * (fderiv ℝ φ x) (EuclideanSpace.single i 1))
      (volume.restrict Ω) := by
  have hdφ : MemLp (fun x : E => (fderiv ℝ φ x) (EuclideanSpace.single i 1)) 2
      (volume.restrict Ω) :=
    (((hφ.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
      continuous_const).memLp_of_hasCompactSupport
        (hφc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1))).restrict _
  exact MemLp.integrable_mul hw hdφ

end Sobolev.Euclidean
