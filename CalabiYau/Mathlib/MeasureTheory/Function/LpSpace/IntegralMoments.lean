module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Moment constraints under strong L² convergence

On a finite measure space, strong convergence in L² preserves the mean and the squared L² norm.
This is the measure-theoretic compactness step used in the Poincaré existence argument.
-/

@[expose] public section

open Filter Topology
open scoped ENNReal

namespace MeasureTheory

private theorem lpNorm_two_sq_eq_integral_sq
    {M : Type*} [MeasurableSpace M] {μ : Measure M} {g : M → ℝ}
    (hg : AEStronglyMeasurable g μ) :
    lpNorm g (ENNReal.ofReal 2) μ ^ 2 = ∫ x, g x ^ 2 ∂μ := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hg]
  rw [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (2 : ℝ))]
  norm_num only
  have hnonneg : 0 ≤ ∫ x, ‖g x‖ ^ (2 : ℝ) ∂μ :=
    integral_nonneg fun x => by positivity
  rw [← Real.sqrt_eq_rpow]
  rw [sq, Real.mul_self_sqrt hnonneg]
  congr 1
  funext x
  rw [Real.norm_eq_abs]
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact sq_abs (g x)

/-- Strong `L²` convergence on a finite measure space preserves the zero-mean and unit-second-
 moment constraints. -/
theorem tendsto_integral_moments_of_eLpNorm
    {M : Type*} [MeasurableSpace M] {μ : Measure M} [IsFiniteMeasure μ]
    (u : M → ℝ) (f : ℕ → M → ℝ)
    (hu : MemLp u (ENNReal.ofReal 2) μ)
    (hf : ∀ k, MemLp (f k) (ENNReal.ofReal 2) μ)
    (hconv : Tendsto
      (fun k => eLpNorm (fun x => f k x - u x) (ENNReal.ofReal 2) μ)
      atTop (𝓝 0))
    (hmean : ∀ k, ∫ x, f k x ∂μ = 0)
    (hsq : ∀ k, ∫ x, (f k x) ^ 2 ∂μ = 1) :
    (∫ x, u x ∂μ = 0) ∧ (∫ x, (u x) ^ 2 ∂μ = 1) := by
  let p : ℝ≥0∞ := ENNReal.ofReal 2
  have hp : (1 : ℝ≥0∞) ≤ p := by norm_num [p]
  have hconvP : Tendsto
      (fun k => eLpNorm (fun x => f k x - u x) p μ) atTop (𝓝 0) := by
    simpa [p] using hconv
  have hL1 : Tendsto
      (fun k => eLpNorm (fun x => f k x - u x) 1 μ) atTop (𝓝 0) := by
    have hbound : ∀ k, eLpNorm (fun x => f k x - u x) 1 μ ≤
        eLpNorm (fun x => f k x - u x) p μ *
          μ Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal) := by
      intro k
      exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := p) hp
        ((hf k).sub hu).aestronglyMeasurable
    have hupper : Tendsto
        (fun k => eLpNorm (fun x => f k x - u x) p μ *
          μ Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal)) atTop (𝓝 0) := by
      simpa [p] using ENNReal.Tendsto.mul_const hconvP (by
        right
        finiteness)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun k => (zero_le : (0 : ℝ≥0∞) ≤ eLpNorm (fun x => f k x - u x) 1 μ)) hbound
  have hFkIntegrable : ∀ᶠ k : ℕ in atTop, Integrable (f k) μ := by
    filter_upwards [] with k
    exact memLp_one_iff_integrable.mp ((hf k).mono_exponent (by norm_num))
  have hmeanlim : Tendsto (fun k => ∫ x, f k x ∂μ) atTop (𝓝 (∫ x, u x ∂μ)) :=
    tendsto_integral_of_L1' u hFkIntegrable hL1
  have hmean0 : Tendsto (fun k => ∫ x, f k x ∂μ) atTop (𝓝 0) := by
    simpa only [hmean] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hmeanU : ∫ x, u x ∂μ = 0 := tendsto_nhds_unique hmeanlim hmean0
  have hLpConv : Tendsto
      (fun k => lpNorm (fun x => f k x - u x) p μ) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv
    convert h using 1
    · funext k
      exact (toReal_eLpNorm (p := p)).symm
    · simp
  have hFnorm : ∀ k, lpNorm (f k) p μ = 1 := by
    intro k
    have hsquare : lpNorm (f k) p μ ^ 2 = 1 := by
      have hidentity := lpNorm_two_sq_eq_integral_sq (μ := μ) (g := f k) (hf k).aestronglyMeasurable
      simpa [p] using hidentity.trans (hsq k)
    have hnonneg : 0 ≤ lpNorm (f k) p μ := lpNorm_nonneg
    nlinarith
  have hdistAbs : Tendsto
      (fun k => |lpNorm (f k) p μ - lpNorm u p μ|) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hLpConv
      (fun k => abs_nonneg (lpNorm (f k) p μ - lpNorm u p μ))
      (fun k => by
        have h₁ : lpNorm (f k) p μ ≤ lpNorm u p μ + lpNorm (fun x => f k x - u x) p μ := by
          exact lpNorm_le_lpNorm_add_lpNorm_sub' (hg := hu) (f := f k) hp
        have h₂ : lpNorm u p μ ≤ lpNorm (f k) p μ + lpNorm (fun x => f k x - u x) p μ := by
          have h₂' := lpNorm_le_lpNorm_add_lpNorm_sub' (hg := hf k) (f := u) hp
          calc
            lpNorm u p μ ≤ lpNorm (f k) p μ + lpNorm (u - f k) p μ := by simpa [p] using h₂'
            _ = lpNorm (f k) p μ + lpNorm (fun x => f k x - u x) p μ := by
              rw [lpNorm_sub_comm]
              have hfun : f k - u = (fun x => f k x - u x) := by
                funext x
                rfl
              rw [hfun]
        rw [abs_le]
        constructor <;> linarith)
  have hUnorm : lpNorm u p μ = 1 := by
    have hconst : Tendsto (fun _ : ℕ => |1 - lpNorm u p μ|) atTop (𝓝 0) := by
      refine hdistAbs.congr' (Filter.Eventually.of_forall fun k => ?_)
      rw [hFnorm k]
    have : 0 = |1 - lpNorm u p μ| := tendsto_nhds_unique hconst tendsto_const_nhds
    have habs : |1 - lpNorm u p μ| = 0 := this.symm
    have hnonneg : 0 ≤ lpNorm u p μ := lpNorm_nonneg
    rw [abs_eq_zero] at habs
    linarith
  refine ⟨hmeanU, ?_⟩
  have hidentity := lpNorm_two_sq_eq_integral_sq (μ := μ) (g := u) hu.aestronglyMeasurable
  calc
    (∫ x, (u x) ^ 2 ∂μ) = lpNorm u p μ ^ 2 := by simpa [p] using hidentity.symm
    _ = 1 := by rw [hUnorm]; norm_num

end MeasureTheory
