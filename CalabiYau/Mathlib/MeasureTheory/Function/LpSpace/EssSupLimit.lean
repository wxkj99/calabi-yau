module

public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov

import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

public section

open Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

/-- Uniform bounds on finite, positive `Lᵖ` seminorms whose exponents tend to infinity
bound the essential supremum seminorm. -/
theorem eLpNormEssSup_le_of_eLpNorm_le_of_tendsto
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    {p : ℕ → ℝ≥0∞} {C : ℝ≥0∞}
    (hf : AEStronglyMeasurable f μ)
    (hp0 : ∀ k, p k ≠ 0)
    (hpTop : ∀ k, p k ≠ ∞)
    (hp_tendsto : Tendsto (fun k => (p k).toReal) atTop atTop)
    (hbound : ∀ k, eLpNorm f (p k) μ ≤ C) :
    eLpNormEssSup f μ ≤ C := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε hCtop
  let c : ℝ≥0∞ := C + ε
  have hcTop : c ≠ ∞ := by
    exact ENNReal.add_ne_top.mpr ⟨ne_of_lt hCtop, ENNReal.coe_ne_top⟩
  have hcPos : 0 < c := by positivity
  have hcNeZero : c ≠ 0 := ne_of_gt hcPos
  have hcGT : C < c := by
    dsimp [c]
    simpa using ENNReal.add_lt_add_left (ne_of_lt hCtop) (ENNReal.coe_pos.2 hε)
  have hq : c⁻¹ * C < 1 := by
    calc
      c⁻¹ * C < c⁻¹ * c := ENNReal.mul_lt_mul_right
        (ENNReal.inv_ne_zero.2 hcTop) (ENNReal.inv_ne_top.2 hcNeZero) hcGT
      _ = 1 := ENNReal.inv_mul_cancel hcNeZero hcTop
  have hpow_tendsto : Tendsto (fun k => (c⁻¹ * C) ^ (p k).toReal) atTop (𝓝 0) :=
    (ENNReal.tendsto_rpow_atTop_of_base_lt_one hq).comp hp_tendsto
  have hmeasure : μ {x | c ≤ ‖f x‖ₑ} = 0 := by
    refine bot_unique <| ge_of_tendsto' hpow_tendsto fun k => ?_
    calc
      μ {x | c ≤ ‖f x‖ₑ} ≤ c⁻¹ ^ (p k).toReal * eLpNorm f (p k) μ ^ (p k).toReal :=
        meas_ge_le_mul_pow_eLpNorm_enorm μ (hp0 k) (hpTop k) hf (ne_of_gt hcPos)
          (by intro h; exact (hcTop h).elim)
      _ = (c⁻¹ * eLpNorm f (p k) μ) ^ (p k).toReal := by
        rw [← ENNReal.mul_rpow_of_nonneg _ _ (ENNReal.toReal_nonneg)]
      _ ≤ (c⁻¹ * C) ^ (p k).toReal := by
        gcongr
        exact hbound k
  have hae_lt : ∀ᵐ x ∂μ, ‖f x‖ₑ < c := by
    rw [ae_iff]
    simpa [not_lt] using hmeasure
  have hae_le : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ c := hae_lt.mono fun _ hx => hx.le
  calc
    eLpNormEssSup f μ ≤ c := eLpNormEssSup_le_of_ae_enorm_bound hae_le
    _ = C + ε := rfl

end MeasureTheory
