-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Estimates/Absorption.lean
-- Locally modified.
module
public import CalabiYau.Mathlib.Analysis.Holder.Basic

@[expose] public section


noncomputable section

open scoped ENNReal NNReal

namespace CalabiYau.Schauder

theorem nnreal_le_div_one_sub_of_le_add_mul
    {x c epsilon : NNReal} (hepsilon : epsilon < 1)
    (h : x ≤ c + epsilon * x) :
    x ≤ c / (1 - epsilon) := by
  rw [← NNReal.coe_le_coe]
  rw [NNReal.coe_div, NNReal.coe_sub hepsilon.le, NNReal.coe_one]
  rw [le_div_iff₀ (sub_pos.mpr (by exact_mod_cast hepsilon))]
  have hreal : (x : Real) ≤ c + epsilon * x := by exact_mod_cast h
  nlinarith

theorem ennreal_le_coe_div_one_sub_of_le_add_mul
    {x : ENNReal} {c epsilon : NNReal} (hx : x ≠ ∞)
    (hepsilon : epsilon < 1)
    (h : x ≤ c + epsilon * x) :
    x ≤ (c / (1 - epsilon) : NNReal) := by
  have hcoeff : (epsilon : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hc : (c : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hproduct : (epsilon : ENNReal) * x ≠ ∞ :=
    ENNReal.mul_ne_top hcoeff hx
  have hrhs : (c : ENNReal) + epsilon * x ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨hc, hproduct⟩
  have hnn := (ENNReal.toNNReal_le_toNNReal hx hrhs).2 h
  have hnn' : x.toNNReal ≤ c + epsilon * x.toNNReal := by
    simpa only [ENNReal.toNNReal_add hc hproduct,
      ENNReal.toNNReal_coe, ENNReal.toNNReal_mul] using hnn
  have habsorb := nnreal_le_div_one_sub_of_le_add_mul hepsilon hnn'
  rw [← ENNReal.coe_toNNReal hx]
  exact_mod_cast habsorb

end CalabiYau.Schauder

end
