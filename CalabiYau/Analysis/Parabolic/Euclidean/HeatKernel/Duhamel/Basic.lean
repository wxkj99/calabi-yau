-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Parabolic/Euclidean/HeatKernel/Duhamel/Basic.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Parabolic.Euclidean.HeatKernel.Derivatives.Cancellation
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section


noncomputable section

open MeasureTheory Real Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace HeatEquation

section TimeKernel

def heatScale12 (t : ℝ) : ℝ :=
  t ^ (-(1 : ℝ) / 2)

theorem heatScale12_eq {t : ℝ} (ht : 0 < t) :
    heatScale12 t = (heatScale t)⁻¹ := by
  unfold heatScale12 heatScale
  rw [Real.sqrt_eq_rpow]
  convert Real.rpow_neg ht.le (1 / 2 : ℝ) using 1
  ring_nf

theorem scale12_intble {t : ℝ} :
    IntervalIntegrable (fun s : ℝ => heatScale12 (t - s)) volume 0 t := by
  have hpow : IntervalIntegrable (fun u : ℝ => u ^ (-(1 : ℝ) / 2)) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have href := hpow.symm.comp_sub_left t
  simpa only [heatScale12, sub_self, sub_zero] using href

theorem timeScale12_int {t : ℝ} :
    ∫ s : ℝ in 0..t, heatScale12 (t - s) =
      2 * t ^ (1 / 2 : ℝ) := by
  unfold heatScale12
  rw [intervalIntegral.integral_comp_sub_left
    (fun u : ℝ => u ^ (-(1 : ℝ) / 2)) t]
  simp only [sub_self, sub_zero]
  rw [integral_rpow (Or.inl (by norm_num))]
  have hexp : -(1 : ℝ) / 2 + 1 = 1 / 2 := by ring
  rw [hexp, Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  ring

end TimeKernel

section Duhamel

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def heatD2Duhamel (t : ℝ) (v w : V) (f : ℝ → V → F) (x : V) : F :=
  ∫ s : ℝ in 0..t, heatD2Convolution (t - s) v w (f s) x

omit [Nontrivial V] [CompleteSpace F] in
theorem heatD2Duhamel_comm (t : ℝ) (v w : V) (f : ℝ → V → F) (x : V) :
    heatD2Duhamel t v w f x = heatD2Duhamel t w v f x := by
  unfold heatD2Duhamel
  apply intervalIntegral.integral_congr
  intro s _
  exact heatD2Convolution_comm (t - s) v w (f s) x

end Duhamel

end HeatEquation

end
