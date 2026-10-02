module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Finite-measure comparison of Lp norms

On a finite measure space, the L² norm controls the L^(4/3) norm with the expected
measure factor. This comparison is used in the two-dimensional Sobolev inequality.
-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory

/-- On a finite measure space, the `L^(4/3)` norm is bounded by the `L²` norm
multiplied by the measure of the whole space to the power `1/4`. -/
theorem lpNorm_fourThirds_le_measure_univ_rpow_mul_lpNorm_two
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : AEStronglyMeasurable f μ)
    (hmem : MemLp f (ENNReal.ofReal (2 : ℝ)) μ) :
    lpNorm f (ENNReal.ofReal (4 / 3 : ℝ)) μ ≤
      (μ Set.univ).toReal ^ (1 / 4 : ℝ) * lpNorm f (ENNReal.ofReal (2 : ℝ)) μ := by
  have hcmp := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (p := ENNReal.ofReal (4 / 3 : ℝ)) (q := ENNReal.ofReal (2 : ℝ))
    (f := f) (μ := μ) (by norm_num) hf
  have hcmp' : eLpNorm f (ENNReal.ofReal (4 / 3 : ℝ)) μ ≤
      eLpNorm f (ENNReal.ofReal (2 : ℝ)) μ * (μ Set.univ) ^ (1 / 4 : ℝ) := by
    convert hcmp using 1; norm_num [ENNReal.toReal_ofReal]
  have hfactor : (μ Set.univ) ^ (1 / 4 : ℝ) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) (measure_ne_top μ Set.univ)
  have hRHS : eLpNorm f (ENNReal.ofReal (2 : ℝ)) μ *
      (μ Set.univ) ^ (1 / 4 : ℝ) ≠ ⊤ :=
    ENNReal.mul_ne_top hmem.eLpNorm_ne_top hfactor.ne
  have hreal := ENNReal.toReal_mono hRHS hcmp'
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, toReal_eLpNorm hf,
    toReal_eLpNorm hmem.aestronglyMeasurable] at hreal
  simpa [mul_comm] using hreal

end MeasureTheory
