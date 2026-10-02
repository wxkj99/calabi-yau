-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Parabolic/Euclidean/HeatKernel/Convolution/Lp.lean
-- Locally modified.
module
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

@[expose] public section


noncomputable section

open MeasureTheory Real
open scoped ENNReal RealInnerProductSpace

namespace HeatEquation

section KernelOperator

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (p ≠ ∞)]

end KernelOperator

section OperatorKernel

variable {V F G : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (p ≠ ∞)]

end OperatorKernel

section Gaussian

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem gauss_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : V => Real.exp (-a * ‖x‖ ^ 2)) := by
  apply (integrable_fun_norm_addHaar (volume : Measure V)
    (f := fun r : ℝ => Real.exp (-a * r ^ 2))).2
  have h := integrableOn_rpow_mul_exp_neg_mul_sq ha
    (s := ((Module.finrank ℝ V - 1 : ℕ) : ℝ))
    (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg _))
  simpa only [smul_eq_mul, Real.rpow_natCast] using h

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem gaussMoment_int (k : ℕ) {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : V => ‖x‖ ^ k * Real.exp (-a * ‖x‖ ^ 2)) := by
  apply (integrable_fun_norm_addHaar (volume : Measure V)
    (f := fun r : ℝ => r ^ k * Real.exp (-a * r ^ 2))).2
  have h := integrableOn_rpow_mul_exp_neg_mul_sq ha
    (s := ((Module.finrank ℝ V - 1 + k : ℕ) : ℝ))
    (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg _))
  simpa only [smul_eq_mul, Real.rpow_natCast, pow_add, mul_assoc] using h

def baseHeatMass (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    : ℝ :=
  (Real.pi / (4 : ℝ)⁻¹) ^ (Module.finrank ℝ V / 2 : ℝ)

def baseHeat (x : V) : ℝ :=
  (baseHeatMass V)⁻¹ * Real.exp (-(4 : ℝ)⁻¹ * ‖x‖ ^ 2)

theorem baseHeatMass_pos : 0 < baseHeatMass V := by
  unfold baseHeatMass
  exact Real.rpow_pos_of_pos (div_pos Real.pi_pos (by positivity)) _

theorem baseHeat_nonneg (x : V) : 0 ≤ baseHeat x := by
  exact mul_nonneg (inv_nonneg.mpr (baseHeatMass_pos (V := V)).le)
    (Real.exp_pos _).le

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem baseHeat_int : Integrable (baseHeat : V → ℝ) := by
  unfold baseHeat
  exact (gauss_integrable (V := V) (by positivity : (0 : ℝ) < (4 : ℝ)⁻¹)).const_mul _

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem integral_baseHeat : ∫ x : V, baseHeat x = 1 := by
  unfold baseHeat
  rw [integral_const_mul,
    GaussianFourier.integral_rexp_neg_mul_sq_norm
      (V := V) (by positivity : (0 : ℝ) < (4 : ℝ)⁻¹)]
  exact inv_mul_cancel₀ (baseHeatMass_pos (V := V)).ne'

def heatScale (t : ℝ) : ℝ := Real.sqrt t

def heatKernel (t : ℝ) (x : V) : ℝ :=
  ((heatScale t) ^ Module.finrank ℝ V)⁻¹ *
    baseHeat ((heatScale t)⁻¹ • x)

theorem heatScale_pos {t : ℝ} (ht : 0 < t) : 0 < heatScale t := by
  simpa [heatScale] using Real.sqrt_pos.2 ht

theorem heatKernel_nonneg {t : ℝ} (ht : 0 < t) (x : V) :
    0 ≤ heatKernel t x := by
  unfold heatKernel
  exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _))
    (baseHeat_nonneg _)

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatKernel_int {t : ℝ} (ht : 0 < t) :
    Integrable (heatKernel t : V → ℝ) := by
  unfold heatKernel
  exact (baseHeat_int (V := V)).comp_smul (inv_ne_zero (heatScale_pos ht).ne') |>.const_mul _

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem integral_heatKernel {t : ℝ} (ht : 0 < t) :
    ∫ x : V, heatKernel t x = 1 := by
  let r := heatScale t
  have hr : 0 < r := heatScale_pos ht
  unfold heatKernel
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg (volume : Measure V) baseHeat hr.le,
    integral_baseHeat]
  simp only [smul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (pow_ne_zero _ hr.ne')

end Gaussian

section GaussianDeriv

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def baseD1 (v x : V) : ℝ :=
  -(2 : ℝ)⁻¹ * ⟪x, v⟫ * baseHeat x

def baseD2 (v w x : V) : ℝ :=
  ((4 : ℝ)⁻¹ * ⟪x, v⟫ * ⟪x, w⟫ -
      (2 : ℝ)⁻¹ * ⟪v, w⟫) * baseHeat x

theorem baseD2_comm (v w x : V) :
    baseD2 v w x = baseD2 w v x := by
  unfold baseD2
  rw [real_inner_comm v w]
  ring

def baseD1Map (x : V) : V →L[ℝ] ℝ :=
  (-(2 : ℝ)⁻¹ * baseHeat x) • innerSL ℝ x

def baseD2Map (v x : V) : V →L[ℝ] ℝ :=
  ((4 : ℝ)⁻¹ * ⟪x, v⟫ * baseHeat x) • innerSL ℝ x -
    ((2 : ℝ)⁻¹ * baseHeat x) • innerSL ℝ v

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
def baseD2CurriedMap (x : V) : V →L[ℝ] (V →L[ℝ] ℝ) :=
  (innerSL ℝ x).smulRight
      (((4 : ℝ)⁻¹ * baseHeat x) • innerSL ℝ x) -
    ((2 : ℝ)⁻¹ * baseHeat x) •
      (innerSL ℝ (E := V)).toContinuousLinearMap

@[simp] theorem baseD1Map_apply (x v : V) :
    baseD1Map x v = baseD1 v x := by
  simp [baseD1Map, baseD1]
  ring

@[simp] theorem baseD2Map_apply (v x w : V) :
    baseD2Map v x w = baseD2 v w x := by
  simp [baseD2Map, baseD2]
  ring

variable [FiniteDimensional ℝ V] in
@[simp] theorem baseD2CurriedMap_apply (x w v : V) :
    baseD2CurriedMap x w v = baseD2 v w x := by
  simp only [baseD2CurriedMap, baseD2, sub_apply,
    ContinuousLinearMap.smulRight_apply, smul_apply,
    innerSL_apply_apply, smul_eq_mul]
  have hinner :
      ((innerSL ℝ (E := V)).toContinuousLinearMap w) v = ⟪w, v⟫ := rfl
  rw [hinner, real_inner_comm w v]
  ring

theorem baseHeat_hasFDeriv (x : V) :
    HasFDerivAt (baseHeat : V → ℝ) (baseD1Map x) x := by
  have hq := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (-(4 : ℝ)⁻¹)
  have he := hq.exp
  have hc := he.const_mul (baseHeatMass V)⁻¹
  have hc' := hc.congr_fderiv (g' := baseD1Map x) (by
    ext v
    simp [baseD1Map, baseHeat]
    ring)
  simpa only [baseHeat] using! hc'

theorem baseD1_hasFDeriv (v x : V) :
    HasFDerivAt (baseD1 v) (baseD2Map v x) x := by
  have hi : HasFDerivAt (fun y : V => ⟪y, v⟫) (innerSL ℝ v) x := by
    simpa [real_inner_comm] using (innerSL ℝ v).hasFDerivAt
  have h := (hi.mul (baseHeat_hasFDeriv x)).const_mul (-(2 : ℝ)⁻¹)
  have h' := h.congr_fderiv (g' := baseD2Map v x) (by
    ext w
    simp only [baseD1Map, baseD2Map, sub_apply, add_apply, smul_apply,
      innerSL_apply_apply, smul_eq_mul]
    ring
    )
  have hfun : baseD1 v =
      fun y => -(2 : ℝ)⁻¹ * (⟪y, v⟫ * baseHeat y) := by
    funext y
    simp only [baseD1]
    ring
  rw [hfun]
  exact h'

variable [FiniteDimensional ℝ V] in
theorem baseD1Map_hasFDeriv (x : V) :
    HasFDerivAt (baseD1Map (V := V)) (baseD2CurriedMap x) x := by
  have hc := (baseHeat_hasFDeriv (V := V) x).const_mul (-(2 : ℝ)⁻¹)
  have hi : HasFDerivAt
      (fun y : V => (innerSL ℝ (E := V)).toContinuousLinearMap y)
      (innerSL ℝ (E := V)).toContinuousLinearMap x :=
    (innerSL ℝ (E := V)).toContinuousLinearMap.hasFDerivAt
  have h := hc.smul hi
  have h' := h.congr_fderiv (g' := baseD2CurriedMap x) (by
    ext w v
    simp only [baseD2CurriedMap, sub_apply, add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul]
    have hinner :
        ((innerSL ℝ (E := V)).toContinuousLinearMap w) v = ⟪w, v⟫ := rfl
    have hinnerX :
        ((innerSL ℝ (E := V)).toContinuousLinearMap x) v = ⟪x, v⟫ := rfl
    rw [hinner, hinnerX, baseD1Map_apply]
    unfold baseD1
    ring)
  simpa only [baseD1Map] using! h'

def baseD1Maj (x : V) : ℝ :=
  (2 : ℝ)⁻¹ * ‖x‖ * baseHeat x

def baseD2Maj (x : V) : ℝ :=
  ((4 : ℝ)⁻¹ * ‖x‖ ^ 2 + (2 : ℝ)⁻¹) * baseHeat x

theorem baseD1Maj_nonneg (x : V) : 0 ≤ baseD1Maj x := by
  unfold baseD1Maj
  exact mul_nonneg (mul_nonneg (by positivity) (norm_nonneg x)) (baseHeat_nonneg x)

theorem baseD2Maj_nonneg (x : V) : 0 ≤ baseD2Maj x := by
  unfold baseD2Maj
  exact mul_nonneg (add_nonneg (mul_nonneg (by positivity) (sq_nonneg ‖x‖)) (by positivity))
    (baseHeat_nonneg x)

theorem baseD1_bound (v x : V) :
    ‖baseD1 v x‖ ≤ ‖v‖ * baseD1Maj x := by
  rw [baseD1, baseD1Maj, Real.norm_eq_abs, abs_mul, abs_mul, abs_neg,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹),
    abs_of_nonneg (baseHeat_nonneg x)]
  calc
    (2 : ℝ)⁻¹ * |⟪x, v⟫| * baseHeat x
        ≤ (2 : ℝ)⁻¹ * (‖x‖ * ‖v‖) * baseHeat x := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm x v) (by positivity))
        (baseHeat_nonneg x)
    _ = ‖v‖ * ((2 : ℝ)⁻¹ * ‖x‖ * baseHeat x) := by ring

theorem baseD2_bound (v w x : V) :
    ‖baseD2 v w x‖ ≤ ‖v‖ * ‖w‖ * baseD2Maj x := by
  rw [baseD2, baseD2Maj, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (baseHeat_nonneg x)]
  have htri :
      |(4 : ℝ)⁻¹ * ⟪x, v⟫ * ⟪x, w⟫ - (2 : ℝ)⁻¹ * ⟪v, w⟫| ≤
        (4 : ℝ)⁻¹ * |⟪x, v⟫| * |⟪x, w⟫| +
          (2 : ℝ)⁻¹ * |⟪v, w⟫| := by
    calc
      |(4 : ℝ)⁻¹ * ⟪x, v⟫ * ⟪x, w⟫ - (2 : ℝ)⁻¹ * ⟪v, w⟫|
          = |(4 : ℝ)⁻¹ * ⟪x, v⟫ * ⟪x, w⟫ +
              -((2 : ℝ)⁻¹ * ⟪v, w⟫)| := by ring_nf
      _ ≤ |(4 : ℝ)⁻¹ * ⟪x, v⟫ * ⟪x, w⟫| +
            |-((2 : ℝ)⁻¹ * ⟪v, w⟫)| := abs_add_le _ _
      _ = (4 : ℝ)⁻¹ * |⟪x, v⟫| * |⟪x, w⟫| +
            (2 : ℝ)⁻¹ * |⟪v, w⟫| := by
        rw [abs_mul, abs_mul, abs_neg, abs_mul,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (4 : ℝ)⁻¹),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹)]
  calc
    |(4 : ℝ)⁻¹ * ⟪x, v⟫ * ⟪x, w⟫ - (2 : ℝ)⁻¹ * ⟪v, w⟫| * baseHeat x
        ≤ ((4 : ℝ)⁻¹ * |⟪x, v⟫| * |⟪x, w⟫| +
            (2 : ℝ)⁻¹ * |⟪v, w⟫|) * baseHeat x := by
          exact mul_le_mul_of_nonneg_right htri (baseHeat_nonneg x)
    _ ≤ ((4 : ℝ)⁻¹ * (‖x‖ * ‖v‖) * (‖x‖ * ‖w‖) +
            (2 : ℝ)⁻¹ * (‖v‖ * ‖w‖)) * baseHeat x := by
          apply mul_le_mul_of_nonneg_right _ (baseHeat_nonneg x)
          apply add_le_add
          · have hp : |⟪x, v⟫| * |⟪x, w⟫| ≤
                (‖x‖ * ‖v‖) * (‖x‖ * ‖w‖) :=
              mul_le_mul (abs_real_inner_le_norm x v) (abs_real_inner_le_norm x w)
                (abs_nonneg _) (mul_nonneg (norm_nonneg x) (norm_nonneg v))
            calc
              (4 : ℝ)⁻¹ * |⟪x, v⟫| * |⟪x, w⟫|
                  = (4 : ℝ)⁻¹ * (|⟪x, v⟫| * |⟪x, w⟫|) := by ring
              _ ≤ (4 : ℝ)⁻¹ * ((‖x‖ * ‖v‖) * (‖x‖ * ‖w‖)) :=
                mul_le_mul_of_nonneg_left hp (by positivity)
              _ = (4 : ℝ)⁻¹ * (‖x‖ * ‖v‖) * (‖x‖ * ‖w‖) := by ring
          · exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm v w) (by positivity)
    _ = ‖v‖ * ‖w‖ *
          (((4 : ℝ)⁻¹ * ‖x‖ ^ 2 + (2 : ℝ)⁻¹) * baseHeat x) := by ring

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem baseD1Maj_int : Integrable (baseD1Maj : V → ℝ) := by
  have h := (gaussMoment_int (V := V) 1
    (by positivity : (0 : ℝ) < (4 : ℝ)⁻¹)).const_mul
      ((2 : ℝ)⁻¹ * (baseHeatMass V)⁻¹)
  have heq : baseD1Maj = fun x : V =>
      ((2 : ℝ)⁻¹ * (baseHeatMass V)⁻¹) *
        (‖x‖ ^ 1 * Real.exp (-(4 : ℝ)⁻¹ * ‖x‖ ^ 2)) := by
    funext x
    unfold baseD1Maj baseHeat
    ring
  rw [heq]
  exact h

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem baseD2Maj_int : Integrable (baseD2Maj : V → ℝ) := by
  have h2 := (gaussMoment_int (V := V) 2
    (by positivity : (0 : ℝ) < (4 : ℝ)⁻¹)).const_mul
      ((4 : ℝ)⁻¹ * (baseHeatMass V)⁻¹)
  have h0 := (gaussMoment_int (V := V) 0
    (by positivity : (0 : ℝ) < (4 : ℝ)⁻¹)).const_mul
      ((2 : ℝ)⁻¹ * (baseHeatMass V)⁻¹)
  have heq : baseD2Maj = fun x : V =>
      ((4 : ℝ)⁻¹ * (baseHeatMass V)⁻¹) *
          (‖x‖ ^ 2 * Real.exp (-(4 : ℝ)⁻¹ * ‖x‖ ^ 2)) +
        ((2 : ℝ)⁻¹ * (baseHeatMass V)⁻¹) *
          (‖x‖ ^ 0 * Real.exp (-(4 : ℝ)⁻¹ * ‖x‖ ^ 2)) := by
    funext x
    unfold baseD2Maj baseHeat
    ring
  rw [heq]
  exact h2.add h0

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
def heatC1 (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] : ℝ :=
  ∫ x : V, baseD1Maj x

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
def heatC2 (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] : ℝ :=
  ∫ x : V, baseD2Maj x

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem heatC1_nonneg : 0 ≤ heatC1 V :=
  integral_nonneg baseD1Maj_nonneg

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem heatC2_nonneg : 0 ≤ heatC2 V :=
  integral_nonneg baseD2Maj_nonneg

def heatD1Maj (t : ℝ) (x : V) : ℝ :=
  ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ *
    baseD1Maj ((heatScale t)⁻¹ • x)

def heatD2Maj (t : ℝ) (x : V) : ℝ :=
  ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ * (heatScale t)⁻¹ *
    baseD2Maj ((heatScale t)⁻¹ • x)

theorem heatD1Maj_nonneg {t : ℝ} (ht : 0 < t) (x : V) :
    0 ≤ heatD1Maj t x := by
  unfold heatD1Maj
  exact mul_nonneg
    (mul_nonneg (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _))
      (inv_nonneg.mpr (heatScale_pos ht).le))
    (baseD1Maj_nonneg _)

theorem heatD2Maj_nonneg {t : ℝ} (ht : 0 < t) (x : V) :
    0 ≤ heatD2Maj t x := by
  unfold heatD2Maj
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _))
        (inv_nonneg.mpr (heatScale_pos ht).le))
      (inv_nonneg.mpr (heatScale_pos ht).le))
    (baseD2Maj_nonneg _)

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatD1Maj_int {t : ℝ} (ht : 0 < t) :
    Integrable (heatD1Maj t : V → ℝ) := by
  unfold heatD1Maj
  exact (baseD1Maj_int (V := V)).comp_smul
    (inv_ne_zero (heatScale_pos ht).ne') |>.const_mul _

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatD2Maj_int {t : ℝ} (ht : 0 < t) :
    Integrable (heatD2Maj t : V → ℝ) := by
  unfold heatD2Maj
  exact (baseD2Maj_int (V := V)).comp_smul
    (inv_ne_zero (heatScale_pos ht).ne') |>.const_mul _

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem integral_heatD1Maj {t : ℝ} (ht : 0 < t) :
    ∫ x : V, heatD1Maj t x = (heatScale t)⁻¹ * heatC1 V := by
  have hr : 0 < heatScale t := heatScale_pos ht
  unfold heatD1Maj heatC1
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg (volume : Measure V) baseD1Maj hr.le]
  simp only [smul_eq_mul]
  field_simp [hr.ne']

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem integral_heatD2Maj {t : ℝ} (ht : 0 < t) :
    ∫ x : V, heatD2Maj t x = t⁻¹ * heatC2 V := by
  have hr : 0 < heatScale t := heatScale_pos ht
  have hsqrt : heatScale t ^ 2 = t := by
    simpa [heatScale] using Real.sq_sqrt ht.le
  unfold heatD2Maj heatC2
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg (volume : Measure V) baseD2Maj hr.le]
  simp only [smul_eq_mul]
  have hscale : (heatScale t)⁻¹ * (heatScale t)⁻¹ = t⁻¹ := by
    field_simp [hr.ne', ht.ne']
    nlinarith [hsqrt]
  calc
    (heatScale t ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ *
          (heatScale t)⁻¹ *
          (heatScale t ^ Module.finrank ℝ V * ∫ x : V, baseD2Maj x)
        = ((heatScale t)⁻¹ * (heatScale t)⁻¹) *
            ∫ x : V, baseD2Maj x := by
          field_simp [hr.ne']
    _ = t⁻¹ * ∫ x : V, baseD2Maj x := by rw [hscale]

def heatD1 (t : ℝ) (v x : V) : ℝ :=
  ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ *
    baseD1 v ((heatScale t)⁻¹ • x)

def heatD2 (t : ℝ) (v w x : V) : ℝ :=
  ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ * (heatScale t)⁻¹ *
    baseD2 v w ((heatScale t)⁻¹ • x)

theorem heatD2_comm (t : ℝ) (v w x : V) :
    heatD2 t v w x = heatD2 t w v x := by
  unfold heatD2
  rw [baseD2_comm]

def heatD1Map (t : ℝ) (x : V) : V →L[ℝ] ℝ :=
  (((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹) •
    baseD1Map ((heatScale t)⁻¹ • x)

def heatD2Map (t : ℝ) (v x : V) : V →L[ℝ] ℝ :=
  (((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ *
      (heatScale t)⁻¹) •
    baseD2Map v ((heatScale t)⁻¹ • x)

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
def heatD2CurriedMap (t : ℝ) (x : V) : V →L[ℝ] (V →L[ℝ] ℝ) :=
  (((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ *
      (heatScale t)⁻¹) •
    baseD2CurriedMap ((heatScale t)⁻¹ • x)

@[simp] theorem heatD1Map_apply (t : ℝ) (x v : V) :
    heatD1Map t x v = heatD1 t v x := by
  simp [heatD1Map, heatD1]

@[simp] theorem heatD2Map_apply (t : ℝ) (v x w : V) :
    heatD2Map t v x w = heatD2 t v w x := by
  simp [heatD2Map, heatD2]

variable [FiniteDimensional ℝ V] in
@[simp] theorem heatD2CurriedMap_apply (t : ℝ) (x w v : V) :
    heatD2CurriedMap t x w v = heatD2 t v w x := by
  simp only [heatD2CurriedMap, smul_apply, smul_eq_mul,
    baseD2CurriedMap_apply]
  rfl

theorem heatKernel_hasFDeriv {t : ℝ} (x : V) :
    HasFDerivAt (heatKernel t) (heatD1Map t x) x := by
  let S : V →L[ℝ] V := (heatScale t)⁻¹ • ContinuousLinearMap.id ℝ V
  have hS : HasFDerivAt (fun y : V => (heatScale t)⁻¹ • y) S x := by
    simpa [S] using! S.hasFDerivAt
  have h := ((baseHeat_hasFDeriv ((heatScale t)⁻¹ • x)).comp x hS).const_mul
    (((heatScale t) ^ Module.finrank ℝ V)⁻¹)
  have h' := h.congr_fderiv (g' := heatD1Map t x) (by
    ext v
    simp [heatD1Map, S, baseD1Map]
    ring)
  simpa only [heatKernel] using! h'

theorem heatD1_hasFDeriv {t : ℝ} (v x : V) :
    HasFDerivAt (heatD1 t v) (heatD2Map t v x) x := by
  let S : V →L[ℝ] V := (heatScale t)⁻¹ • ContinuousLinearMap.id ℝ V
  have hS : HasFDerivAt (fun y : V => (heatScale t)⁻¹ • y) S x := by
    simpa [S] using! S.hasFDerivAt
  have h := ((baseD1_hasFDeriv v ((heatScale t)⁻¹ • x)).comp x hS).const_mul
    (((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹)
  have h' := h.congr_fderiv (g' := heatD2Map t v x) (by
    ext w
    simp [heatD2Map, S, baseD2Map]
    ring)
  simpa only [heatD1] using! h'

variable [FiniteDimensional ℝ V] in
theorem heatD1Map_hasFDeriv (t : ℝ) (x : V) :
    HasFDerivAt (heatD1Map (V := V) t) (heatD2CurriedMap t x) x := by
  let S : V →L[ℝ] V := (heatScale t)⁻¹ • ContinuousLinearMap.id ℝ V
  have hS : HasFDerivAt (fun y : V => (heatScale t)⁻¹ • y) S x := by
    simpa [S] using! S.hasFDerivAt
  have hb : HasFDerivAt (baseD1Map (V := V))
      (baseD2CurriedMap ((heatScale t)⁻¹ • x)) ((heatScale t)⁻¹ • x) :=
    baseD1Map_hasFDeriv _
  have h := (hb.comp x hS).const_smul
    (((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹)
  have h' := h.congr_fderiv (g' := heatD2CurriedMap t x) (by
    ext w v
    simp only [heatD2CurriedMap, S, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, map_smul,
      smul_eq_mul]
    ring)
  simpa only [heatD1Map] using! h'

theorem heatD1_bound {t : ℝ} (ht : 0 < t) (v x : V) :
    ‖heatD1 t v x‖ ≤ ‖v‖ * heatD1Maj t x := by
  unfold heatD1 heatD1Maj
  rw [Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _)),
    abs_of_nonneg (inv_nonneg.mpr (heatScale_pos ht).le)]
  calc
    ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ *
        ‖baseD1 v ((heatScale t)⁻¹ • x)‖
      ≤ ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ *
          (‖v‖ * baseD1Maj ((heatScale t)⁻¹ • x)) := by
        exact mul_le_mul_of_nonneg_left (baseD1_bound v _)
          (mul_nonneg (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _))
            (inv_nonneg.mpr (heatScale_pos ht).le))
    _ = ‖v‖ * (((heatScale t) ^ Module.finrank ℝ V)⁻¹ *
          (heatScale t)⁻¹ * baseD1Maj ((heatScale t)⁻¹ • x)) := by ring

theorem heatD2_bound {t : ℝ} (ht : 0 < t) (v w x : V) :
    ‖heatD2 t v w x‖ ≤ ‖v‖ * ‖w‖ * heatD2Maj t x := by
  unfold heatD2 heatD2Maj
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
  simp only [abs_inv, abs_pow, abs_of_nonneg (heatScale_pos ht).le]
  calc
    ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ * (heatScale t)⁻¹ *
        ‖baseD2 v w ((heatScale t)⁻¹ • x)‖
      ≤ ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ * (heatScale t)⁻¹ *
          (‖v‖ * ‖w‖ * baseD2Maj ((heatScale t)⁻¹ • x)) := by
        exact mul_le_mul_of_nonneg_left (baseD2_bound v w _)
          (mul_nonneg
            (mul_nonneg (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _))
              (inv_nonneg.mpr (heatScale_pos ht).le))
            (inv_nonneg.mpr (heatScale_pos ht).le))
    _ = ‖v‖ * ‖w‖ * (((heatScale t) ^ Module.finrank ℝ V)⁻¹ *
          (heatScale t)⁻¹ * (heatScale t)⁻¹ *
          baseD2Maj ((heatScale t)⁻¹ • x)) := by ring

theorem heatD1Map_norm_le {t : Real} (ht : 0 < t) (x : V) :
    ‖heatD1Map t x‖ ≤ heatD1Maj t x := by
  apply ContinuousLinearMap.opNorm_le_bound (heatD1Map t x)
    (heatD1Maj_nonneg ht x)
  intro v
  rw [heatD1Map_apply]
  exact (heatD1_bound ht v x).trans_eq (by ring)

theorem heatD2Map_norm_le {t : Real} (ht : 0 < t) (v x : V) :
    ‖heatD2Map t v x‖ ≤ ‖v‖ * heatD2Maj t x := by
  apply ContinuousLinearMap.opNorm_le_bound (heatD2Map t v x)
    (mul_nonneg (norm_nonneg v) (heatD2Maj_nonneg ht x))
  intro w
  rw [heatD2Map_apply]
  exact (heatD2_bound ht v w x).trans_eq (by ring)

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatD1_int {t : ℝ} (ht : 0 < t) (v : V) :
    Integrable (heatD1 t v : V → ℝ) := by
  refine ((heatD1Maj_int (V := V) ht).const_mul ‖v‖).mono'
    (by
      apply Continuous.aestronglyMeasurable
      unfold heatD1 baseD1 baseHeat baseHeatMass heatScale
      fun_prop) ?_
  filter_upwards with x
  exact heatD1_bound ht v x

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatD2_int {t : ℝ} (ht : 0 < t) (v w : V) :
    Integrable (heatD2 t v w : V → ℝ) := by
  refine (((heatD2Maj_int (V := V) ht).const_mul ‖w‖).const_mul ‖v‖).mono'
    (by
      apply Continuous.aestronglyMeasurable
      unfold heatD2 baseD2 baseHeat baseHeatMass heatScale
      fun_prop) ?_
  filter_upwards with x
  simpa [mul_assoc] using heatD2_bound ht v w x

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem integral_norm_D1 {t : ℝ} (ht : 0 < t) (v : V) :
    (∫ x : V, ‖heatD1 t v x‖) ≤
      ‖v‖ * (heatScale t)⁻¹ * heatC1 V := by
  calc
    (∫ x : V, ‖heatD1 t v x‖)
        ≤ ∫ x : V, ‖v‖ * heatD1Maj t x := by
      exact integral_mono (heatD1_int ht v).norm
        ((heatD1Maj_int (V := V) ht).const_mul ‖v‖)
        (fun x => heatD1_bound ht v x)
    _ = ‖v‖ * ((heatScale t)⁻¹ * heatC1 V) := by
      rw [integral_const_mul, integral_heatD1Maj ht]
    _ = ‖v‖ * (heatScale t)⁻¹ * heatC1 V := by ring

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem integral_norm_D2 {t : ℝ} (ht : 0 < t) (v w : V) :
    (∫ x : V, ‖heatD2 t v w x‖) ≤
      ‖v‖ * ‖w‖ * t⁻¹ * heatC2 V := by
  calc
    (∫ x : V, ‖heatD2 t v w x‖)
        ≤ ∫ x : V, (‖v‖ * ‖w‖) * heatD2Maj t x := by
      exact integral_mono (heatD2_int ht v w).norm
        ((heatD2Maj_int (V := V) ht).const_mul (‖v‖ * ‖w‖))
        (fun x => by simpa [mul_assoc] using heatD2_bound ht v w x)
    _ = (‖v‖ * ‖w‖) * (t⁻¹ * heatC2 V) := by
      rw [integral_const_mul, integral_heatD2Maj ht]
    _ = ‖v‖ * ‖w‖ * t⁻¹ * heatC2 V := by ring

end GaussianDeriv

section HeatLp

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (p ≠ ∞)]

end HeatLp


end HeatEquation
