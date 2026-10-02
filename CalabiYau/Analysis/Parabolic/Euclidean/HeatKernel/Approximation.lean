-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Parabolic/Euclidean/HeatKernel/Approximation.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Parabolic.Euclidean.HeatKernel.Convolution.Supremum
public import Mathlib.Topology.MetricSpace.HolderNorm

@[expose] public section

-- and its private helpers occur in public declarations.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open Filter MeasureTheory Real
open scoped Interval RealInnerProductSpace NNReal Topology

namespace HeatEquation

section HalfMoment

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V]

def baseHeatHalf (x : V) : ℝ :=
  Real.sqrt ‖x‖ * baseHeat x

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
omit [FiniteDimensional ℝ V] in
theorem baseHeatHalf_nonneg (x : V) : 0 ≤ baseHeatHalf x := by
  unfold baseHeatHalf
  exact mul_nonneg (Real.sqrt_nonneg _) (baseHeat_nonneg x)

private theorem baseHeatFirst_int :
    Integrable (fun x : V => ‖x‖ * baseHeat x) := by
  have h := (gaussMoment_int (V := V) 1
    (by positivity : (0 : ℝ) < (4 : ℝ)⁻¹)).const_mul (baseHeatMass V)⁻¹
  have heq : (fun x : V => ‖x‖ * baseHeat x) = fun x : V =>
      (baseHeatMass V)⁻¹ *
        (‖x‖ ^ 1 * Real.exp (-(4 : ℝ)⁻¹ * ‖x‖ ^ 2)) := by
    funext x
    unfold baseHeat
    ring
  rw [heq]
  exact h

theorem baseHeatHalf_int : Integrable (baseHeatHalf : V → ℝ) := by
  have hmajor : Integrable (fun x : V => (1 + ‖x‖) * baseHeat x) := by
    have h := (baseHeat_int (V := V)).add (baseHeatFirst_int (V := V))
    have heq : (fun x : V => (1 + ‖x‖) * baseHeat x) =
        fun x : V => baseHeat x + ‖x‖ * baseHeat x := by
      funext x
      ring
    rw [heq]
    exact h
  refine hmajor.mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    unfold baseHeatHalf baseHeat baseHeatMass
    fun_prop
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (baseHeatHalf_nonneg x)]
  have hsqrt : Real.sqrt ‖x‖ ≤ 1 + ‖x‖ := by
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity, by nlinarith [norm_nonneg x]⟩
  exact mul_le_mul_of_nonneg_right hsqrt (baseHeat_nonneg x)

def heatC0Half (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] : ℝ :=
  ∫ x : V, baseHeatHalf x

omit [Nontrivial V] in
theorem heatC0Half_nonneg : 0 ≤ heatC0Half V :=
  integral_nonneg baseHeatHalf_nonneg

def heatHalf (t : ℝ) (x : V) : ℝ :=
  ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * Real.sqrt (heatScale t) *
    baseHeatHalf ((heatScale t)⁻¹ • x)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
omit [FiniteDimensional ℝ V] in
theorem heatHalf_nonneg {t : ℝ} (ht : 0 < t) (x : V) :
    0 ≤ heatHalf t x := by
  unfold heatHalf
  exact mul_nonneg
    (mul_nonneg (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _))
      (Real.sqrt_nonneg _))
    (baseHeatHalf_nonneg _)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
omit [FiniteDimensional ℝ V] in
theorem heatHalf_eq {t : ℝ} (ht : 0 < t) (x : V) :
    heatHalf t x = Real.sqrt ‖x‖ * heatKernel t x := by
  have hr : 0 < heatScale t := heatScale_pos ht
  have hx : x = heatScale t • ((heatScale t)⁻¹ • x) := by
    simp [hr.ne']
  have hsqrt : Real.sqrt ‖x‖ =
      Real.sqrt (heatScale t) * Real.sqrt ‖(heatScale t)⁻¹ • x‖ := by
    calc
      Real.sqrt ‖x‖ = Real.sqrt ‖heatScale t • ((heatScale t)⁻¹ • x)‖ :=
        congrArg (fun z : V => Real.sqrt ‖z‖) hx
      _ = Real.sqrt (heatScale t * ‖(heatScale t)⁻¹ • x‖) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      _ = Real.sqrt (heatScale t) * Real.sqrt ‖(heatScale t)⁻¹ • x‖ :=
        Real.sqrt_mul hr.le _
  unfold heatHalf heatKernel baseHeatHalf
  rw [hsqrt]
  ring

theorem heatHalf_int {t : ℝ} (ht : 0 < t) :
    Integrable (heatHalf t : V → ℝ) := by
  unfold heatHalf
  exact (baseHeatHalf_int (V := V)).comp_smul
    (inv_ne_zero (heatScale_pos ht).ne') |>.const_mul _

omit [Nontrivial V] in
theorem integral_heatHalf {t : ℝ} (ht : 0 < t) :
    ∫ x : V, heatHalf t x = Real.sqrt (heatScale t) * heatC0Half V := by
  have hr : 0 < heatScale t := heatScale_pos ht
  unfold heatHalf heatC0Half
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg (volume : Measure V) baseHeatHalf hr.le]
  simp only [smul_eq_mul]
  field_simp [hr.ne']

end HalfMoment

section ApproxIdentity

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] [Nontrivial V] [NormedSpace ℝ F] [CompleteSpace F] in
private theorem holder_half {K : ℝ≥0} {u : V → F}
    (hu : HolderWith K (1 / 2 : ℝ≥0) u) (x y : V) :
    ‖u (x - y) - u x‖ ≤ (K : ℝ) * Real.sqrt ‖y‖ := by
  have hxy : dist (x - y) x = ‖y‖ := by
    rw [dist_eq_norm]
    have : (x - y) - x = -y := by abel
    rw [this, norm_neg]
  have h := hu.dist_le (x - y) x
  rw [dist_eq_norm, hxy] at h
  simpa [Real.sqrt_eq_rpow] using h

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] [CompleteSpace F] in
omit [FiniteDimensional ℝ V] in
private theorem approx_integrand {t : ℝ} (ht : 0 < t) {K : ℝ≥0}
    {u : V → F} (hu : HolderWith K (1 / 2 : ℝ≥0) u) (x y : V) :
    ‖heatKernel t y • (u (x - y) - u x)‖ ≤
      (K : ℝ) * heatHalf t y := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg ht y)]
  calc
    heatKernel t y * ‖u (x - y) - u x‖
        ≤ heatKernel t y * ((K : ℝ) * Real.sqrt ‖y‖) :=
      mul_le_mul_of_nonneg_left (holder_half hu x y) (heatKernel_nonneg ht y)
    _ = (K : ℝ) * heatHalf t y := by
      rw [heatHalf_eq ht]
      ring

theorem heatSup_id_norm {t : ℝ} (ht : 0 < t) {K : ℝ≥0}
    {u : BoundedContinuousFunction V F} (hu : HolderWith K (1 / 2 : ℝ≥0) u) (x : V) :
    ‖heatSup t u x - u x‖ ≤
      (K : ℝ) * Real.sqrt (heatScale t) * heatC0Half V := by
  have hdiff : Integrable
      (fun y : V => heatKernel t y • (u (x - y) - u x)) := by
    refine ((heatHalf_int (V := V) ht).const_mul (K : ℝ)).mono' ?_ ?_
    · apply Continuous.aestronglyMeasurable
      unfold heatKernel baseHeat baseHeatMass heatScale
      fun_prop
    filter_upwards with y
    exact approx_integrand ht hu x y
  have hraw := supKernel_int (heatKernel_int (V := V) ht) u x
  have hconst := (heatKernel_int (V := V) ht).smul_const (u x)
  have heq : heatSup t u x - u x =
      ∫ y : V, heatKernel t y • (u (x - y) - u x) := by
    unfold heatSup supKernel
    calc
      (∫ y : V, heatKernel t y • u (x - y)) - u x =
          (∫ y : V, heatKernel t y • u (x - y)) -
            ∫ y : V, heatKernel t y • u x := by
        rw [integral_smul_const, integral_heatKernel ht, one_smul]
      _ = ∫ y : V,
          heatKernel t y • u (x - y) - heatKernel t y • u x :=
        (integral_sub hraw hconst).symm
      _ = ∫ y : V, heatKernel t y • (u (x - y) - u x) := by
        apply integral_congr_ae
        filter_upwards with y
        rw [smul_sub]
  rw [heq]
  calc
    ‖∫ y : V, heatKernel t y • (u (x - y) - u x)‖
        ≤ ∫ y : V, (K : ℝ) * heatHalf t y :=
      norm_integral_le_of_norm_le ((heatHalf_int (V := V) ht).const_mul (K : ℝ))
        (Filter.Eventually.of_forall fun y => approx_integrand ht hu x y)
    _ = (K : ℝ) * (Real.sqrt (heatScale t) * heatC0Half V) := by
      rw [integral_const_mul, integral_heatHalf ht]
    _ = (K : ℝ) * Real.sqrt (heatScale t) * heatC0Half V := by ring

def baseHeatHolder (alpha : NNReal) (x : V) : Real :=
  ‖x‖ ^ (alpha : Real) * baseHeat x

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
omit [FiniteDimensional ℝ V] in
theorem baseHeatHolder_nonneg (alpha : NNReal) (x : V) :
    0 ≤ baseHeatHolder alpha x :=
  mul_nonneg (Real.rpow_nonneg (norm_nonneg x) _) (baseHeat_nonneg x)

theorem baseHeatHolder_int {alpha : NNReal} (halpha : alpha ≤ 1) :
    Integrable (baseHeatHolder alpha : V → Real) := by
  have hmajor : Integrable (fun x : V => (1 + ‖x‖) * baseHeat x) := by
    have h := (baseHeat_int (V := V)).add (baseHeatFirst_int (V := V))
    have heq : (fun x : V => (1 + ‖x‖) * baseHeat x) =
        fun x : V => baseHeat x + ‖x‖ * baseHeat x := by
      funext x
      ring
    rw [heq]
    exact h
  refine hmajor.mono' ?_ ?_
  · have hpow : Continuous (fun x : V => ‖x‖ ^ (alpha : Real)) :=
      continuous_norm.rpow_const (fun _ => Or.inr alpha.coe_nonneg)
    have hheat : Continuous (baseHeat : V → Real) := by
      unfold baseHeat baseHeatMass
      fun_prop
    exact (hpow.mul hheat).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (baseHeatHolder_nonneg alpha x)]
  have hrpow : ‖x‖ ^ (alpha : Real) ≤ 1 + ‖x‖ := by
    by_cases hx : ‖x‖ ≤ 1
    · exact (Real.rpow_le_one (norm_nonneg x) hx alpha.coe_nonneg).trans
        (le_add_of_nonneg_right (norm_nonneg x))
    · have hx' : 1 ≤ ‖x‖ := le_of_not_ge hx
      exact (Real.rpow_le_self_of_one_le hx' (by exact_mod_cast halpha)).trans
        (le_add_of_nonneg_left zero_le_one)
  exact mul_le_mul_of_nonneg_right hrpow (baseHeat_nonneg x)

def heatC0Holder (alpha : NNReal) : Real :=
  ∫ x : V, baseHeatHolder alpha x

omit [Nontrivial V] in
theorem heatC0Holder_nonneg (alpha : NNReal) :
    0 ≤ heatC0Holder (V := V) alpha :=
  integral_nonneg (baseHeatHolder_nonneg alpha)

def heatHolder (alpha : NNReal) (t : Real) (x : V) : Real :=
  ((heatScale t) ^ Module.finrank Real V)⁻¹ *
    (heatScale t) ^ (alpha : Real) *
      baseHeatHolder alpha ((heatScale t)⁻¹ • x)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
omit [FiniteDimensional ℝ V] in
theorem heatHolder_nonneg (alpha : NNReal) {t : Real} (ht : 0 < t) (x : V) :
    0 ≤ heatHolder alpha t x := by
  unfold heatHolder
  exact mul_nonneg
    (mul_nonneg
      (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _))
      (Real.rpow_nonneg (heatScale_pos ht).le _))
    (baseHeatHolder_nonneg alpha _)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
omit [FiniteDimensional ℝ V] in
theorem heatHolder_eq (alpha : NNReal) {t : Real} (ht : 0 < t) (x : V) :
    heatHolder alpha t x = ‖x‖ ^ (alpha : Real) * heatKernel t x := by
  have hr : 0 < heatScale t := heatScale_pos ht
  have hx : x = heatScale t • ((heatScale t)⁻¹ • x) := by
    simp [hr.ne']
  have hrpow : ‖x‖ ^ (alpha : Real) =
      (heatScale t) ^ (alpha : Real) *
        ‖(heatScale t)⁻¹ • x‖ ^ (alpha : Real) := by
    calc
      ‖x‖ ^ (alpha : Real) =
          ‖heatScale t • ((heatScale t)⁻¹ • x)‖ ^ (alpha : Real) :=
        congrArg (fun z : V => ‖z‖ ^ (alpha : Real)) hx
      _ = (heatScale t * ‖(heatScale t)⁻¹ • x‖) ^ (alpha : Real) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      _ = (heatScale t) ^ (alpha : Real) *
          ‖(heatScale t)⁻¹ • x‖ ^ (alpha : Real) :=
        Real.mul_rpow hr.le (norm_nonneg _)
  unfold heatHolder heatKernel baseHeatHolder
  rw [hrpow]
  ring

theorem heatHolder_int {alpha : NNReal} (halpha : alpha ≤ 1)
    {t : Real} (ht : 0 < t) :
    Integrable (heatHolder (V := V) alpha t) := by
  unfold heatHolder
  exact (baseHeatHolder_int (V := V) halpha).comp_smul
    (inv_ne_zero (heatScale_pos ht).ne') |>.const_mul _

omit [Nontrivial V] in
theorem integral_heatHolder (alpha : NNReal) {t : Real} (ht : 0 < t) :
    ∫ x : V, heatHolder alpha t x =
      (heatScale t) ^ (alpha : Real) * heatC0Holder (V := V) alpha := by
  have hr : 0 < heatScale t := heatScale_pos ht
  unfold heatHolder heatC0Holder
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg
      (volume : Measure V) (baseHeatHolder alpha) hr.le]
  simp only [smul_eq_mul]
  field_simp [hr.ne']

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] [Nontrivial V] [NormedSpace ℝ F] [CompleteSpace F] in
private theorem holder_shift {alpha K : NNReal} {u : V → F}
    (hu : HolderWith K alpha u) (x y : V) :
    ‖u (x - y) - u x‖ ≤ (K : Real) * ‖y‖ ^ (alpha : Real) := by
  have hxy : dist (x - y) x = ‖y‖ := by
    rw [dist_eq_norm]
    have : (x - y) - x = -y := by abel
    rw [this, norm_neg]
  have h := hu.dist_le (x - y) x
  rw [dist_eq_norm, hxy] at h
  exact h

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] [CompleteSpace F] in
omit [FiniteDimensional ℝ V] in
private theorem holder_approx_integrand {alpha K : NNReal}
    {t : Real} (ht : 0 < t) {u : V → F} (hu : HolderWith K alpha u)
    (x y : V) :
    ‖heatKernel t y • (u (x - y) - u x)‖ ≤
      (K : Real) * heatHolder alpha t y := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg ht y)]
  calc
    heatKernel t y * ‖u (x - y) - u x‖ ≤
        heatKernel t y * ((K : Real) * ‖y‖ ^ (alpha : Real)) :=
      mul_le_mul_of_nonneg_left (holder_shift hu x y) (heatKernel_nonneg ht y)
    _ = (K : Real) * heatHolder alpha t y := by
      rw [heatHolder_eq alpha ht]
      ring

theorem heatSup_id_norm_of_holder {alpha K : NNReal}
    (halpha : alpha ≤ 1) {t : Real} (ht : 0 < t)
    {u : BoundedContinuousFunction V F} (hu : HolderWith K alpha u) (x : V) :
    ‖heatSup t u x - u x‖ ≤
      (K : Real) * (heatScale t) ^ (alpha : Real) *
        heatC0Holder (V := V) alpha := by
  have hdiff : Integrable
      (fun y : V => heatKernel t y • (u (x - y) - u x)) := by
    refine ((heatHolder_int (V := V) halpha ht).const_mul (K : Real)).mono' ?_ ?_
    · apply Continuous.aestronglyMeasurable
      unfold heatKernel baseHeat baseHeatMass heatScale
      fun_prop
    filter_upwards with y
    exact holder_approx_integrand ht hu x y
  have hraw := supKernel_int (heatKernel_int (V := V) ht) u x
  have hconst := (heatKernel_int (V := V) ht).smul_const (u x)
  have heq : heatSup t u x - u x =
      ∫ y : V, heatKernel t y • (u (x - y) - u x) := by
    unfold heatSup supKernel
    calc
      (∫ y : V, heatKernel t y • u (x - y)) - u x =
          (∫ y : V, heatKernel t y • u (x - y)) -
            ∫ y : V, heatKernel t y • u x := by
        rw [integral_smul_const, integral_heatKernel ht, one_smul]
      _ = ∫ y : V,
          heatKernel t y • u (x - y) - heatKernel t y • u x :=
        (integral_sub hraw hconst).symm
      _ = ∫ y : V, heatKernel t y • (u (x - y) - u x) := by
        apply integral_congr_ae
        filter_upwards with y
        rw [smul_sub]
  rw [heq]
  calc
    ‖∫ y : V, heatKernel t y • (u (x - y) - u x)‖ ≤
        ∫ y : V, (K : Real) * heatHolder alpha t y :=
      norm_integral_le_of_norm_le
        ((heatHolder_int (V := V) halpha ht).const_mul (K : Real))
        (Filter.Eventually.of_forall fun y => holder_approx_integrand ht hu x y)
    _ = (K : Real) *
        ((heatScale t) ^ (alpha : Real) * heatC0Holder (V := V) alpha) := by
      rw [integral_const_mul, integral_heatHolder alpha ht]
    _ = (K : Real) * (heatScale t) ^ (alpha : Real) *
        heatC0Holder (V := V) alpha := by ring

theorem heatSup_zero_of_holder {alpha K : NNReal} (halpha0 : 0 < alpha)
    (halpha1 : alpha ≤ 1) (u : BoundedContinuousFunction V F)
    (hu : HolderWith K alpha u) (x : V) :
    Tendsto (fun t : Real => heatSup t u x) (𝓝[>] (0 : Real)) (𝓝 (u x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hscale : Tendsto heatScale (𝓝[>] (0 : Real)) (𝓝 0) := by
    have hfull : Tendsto (fun t : Real => Real.sqrt t) (𝓝 0) (𝓝 0) := by
      simpa only [Real.sqrt_zero] using Real.continuous_sqrt.tendsto (0 : Real)
    change Tendsto (fun t : Real => Real.sqrt t) (𝓝[>] 0) (𝓝 0)
    exact hfull.mono_left nhdsWithin_le_nhds
  have halphaReal : 0 < (alpha : Real) := by exact_mod_cast halpha0
  have hrpow : Tendsto (fun t : Real => (heatScale t) ^ (alpha : Real))
      (𝓝[>] (0 : Real)) (𝓝 0) := by
    have hcont := Real.continuousAt_rpow_const 0 (alpha : Real)
      (Or.inr halphaReal.le)
    change Tendsto ((fun x : Real => x ^ (alpha : Real)) ∘ heatScale)
      (𝓝[>] 0) (𝓝 0)
    simpa only [Real.zero_rpow halphaReal.ne'] using hcont.tendsto.comp hscale
  have hupper : Tendsto
      (fun t : Real => (K : Real) * (heatScale t) ^ (alpha : Real) *
        heatC0Holder (V := V) alpha)
      (𝓝[>] (0 : Real)) (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      (hrpow.const_mul (K : Real)).mul_const (heatC0Holder (V := V) alpha)
  refine squeeze_zero' (Filter.Eventually.of_forall fun t => norm_nonneg _) ?_ hupper
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact heatSup_id_norm_of_holder halpha1 ht hu x

end ApproxIdentity

end HeatEquation
