-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Parabolic/Euclidean/HeatKernel/Derivatives/Cancellation.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Parabolic.Euclidean.HeatKernel.Convolution.Lp
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Topology.MetricSpace.HolderNorm

@[expose] public section

-- and its private helpers occur in public declarations.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open MeasureTheory Real
open scoped ENNReal RealInnerProductSpace NNReal

namespace HeatEquation

section ZeroMean

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V]

theorem integral_heatD2_zero {t : ℝ} (ht : 0 < t) (v w : V) :
    ∫ x : V, heatD2 t v w x = 0 := by
  have hder : ∀ x : V,
      fderiv ℝ (heatD1 t v) x w = heatD2 t v w x := by
    intro x
    rw [(heatD1_hasFDeriv v x).fderiv, heatD2Map_apply]
  have hparts :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := (volume : Measure V))
      (f := fun _ : V => (1 : ℝ)) (g := heatD1 t v) (v := w)
      (by
        have hzero :
            (fun x : V => (fderiv ℝ (fun _ : V => (1 : ℝ)) x) w *
              heatD1 t v x) = 0 := by
          funext x
          rw [fderiv_const_apply, zero_apply, zero_mul]
          rfl
        rw [hzero]
        exact integrable_zero V ℝ (volume : Measure V))
      (by simpa only [one_mul, hder] using heatD2_int ht v w)
      (by simpa only [one_mul] using heatD1_int ht v)
      (fun x _ => differentiableAt_const (𝕜 := ℝ) (x := x) (1 : ℝ))
      (fun x _ => (heatD1_hasFDeriv v x).differentiableAt)
  simpa only [one_mul, hder, fderiv_const_apply, zero_apply,
    zero_mul, integral_zero, neg_zero] using hparts

end ZeroMean

section HalfMoment

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V]

def baseD2Half (x : V) : ℝ :=
  Real.sqrt ‖x‖ * baseD2Maj x

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem baseD2Half_nonneg (x : V) : 0 ≤ baseD2Half x := by
  unfold baseD2Half
  exact mul_nonneg (Real.sqrt_nonneg _) (baseD2Maj_nonneg x)

private theorem baseD2First_int :
    Integrable (fun x : V => ‖x‖ * baseD2Maj x) := by
  have h3 := (gaussMoment_int (V := V) 3
    (by positivity : (0 : ℝ) < (4 : ℝ)⁻¹)).const_mul
      ((4 : ℝ)⁻¹ * (baseHeatMass V)⁻¹)
  have h1 := (gaussMoment_int (V := V) 1
    (by positivity : (0 : ℝ) < (4 : ℝ)⁻¹)).const_mul
      ((2 : ℝ)⁻¹ * (baseHeatMass V)⁻¹)
  have heq : (fun x : V => ‖x‖ * baseD2Maj x) = fun x : V =>
      ((4 : ℝ)⁻¹ * (baseHeatMass V)⁻¹) *
          (‖x‖ ^ 3 * Real.exp (-(4 : ℝ)⁻¹ * ‖x‖ ^ 2)) +
        ((2 : ℝ)⁻¹ * (baseHeatMass V)⁻¹) *
          (‖x‖ ^ 1 * Real.exp (-(4 : ℝ)⁻¹ * ‖x‖ ^ 2)) := by
    funext x
    unfold baseD2Maj baseHeat
    ring
  rw [heq]
  exact h3.add h1

theorem baseD2Half_int : Integrable (baseD2Half : V → ℝ) := by
  have hmajor : Integrable (fun x : V => (1 + ‖x‖) * baseD2Maj x) := by
    have h := (baseD2Maj_int (V := V)).add (baseD2First_int (V := V))
    have heq : (fun x : V => (1 + ‖x‖) * baseD2Maj x) =
        fun x : V => baseD2Maj x + ‖x‖ * baseD2Maj x := by
      funext x
      ring
    rw [heq]
    exact h
  refine hmajor.mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    unfold baseD2Half baseD2Maj baseHeat baseHeatMass
    fun_prop
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (baseD2Half_nonneg x)]
  have hsqrt : Real.sqrt ‖x‖ ≤ 1 + ‖x‖ := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith [norm_nonneg x]
  exact mul_le_mul_of_nonneg_right hsqrt (baseD2Maj_nonneg x)

def heatC2Half (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] : ℝ :=
  ∫ x : V, baseD2Half x

omit [Nontrivial V] in
theorem heatC2Half_nonneg : 0 ≤ heatC2Half V :=
  integral_nonneg baseD2Half_nonneg

def heatD2Half (t : ℝ) (x : V) : ℝ :=
  ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * t⁻¹ *
    Real.sqrt (heatScale t) * baseD2Half ((heatScale t)⁻¹ • x)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatD2Half_nonneg {t : ℝ} (ht : 0 < t) (x : V) :
    0 ≤ heatD2Half t x := by
  unfold heatD2Half
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _))
        (inv_nonneg.mpr ht.le))
      (Real.sqrt_nonneg _))
    (baseD2Half_nonneg _)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
omit [FiniteDimensional ℝ V] in
theorem heatD2Half_eq {t : ℝ} (ht : 0 < t) (x : V) :
    heatD2Half t x = Real.sqrt ‖x‖ * heatD2Maj t x := by
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
  unfold heatD2Half heatD2Maj baseD2Half
  have hsquare : heatScale t ^ 2 = t := by
    simpa [heatScale] using Real.sq_sqrt ht.le
  have hscale : t⁻¹ = (heatScale t)⁻¹ * (heatScale t)⁻¹ := by
    field_simp [hr.ne', ht.ne']
    nlinarith [hsquare]
  rw [hsqrt, hscale]
  ring

theorem heatD2Half_int {t : ℝ} (ht : 0 < t) :
    Integrable (heatD2Half t : V → ℝ) := by
  unfold heatD2Half
  exact (baseD2Half_int (V := V)).comp_smul
    (inv_ne_zero (heatScale_pos ht).ne') |>.const_mul _

omit [Nontrivial V] in
theorem integral_heatD2Half {t : ℝ} (ht : 0 < t) :
    ∫ x : V, heatD2Half t x =
      t⁻¹ * Real.sqrt (heatScale t) * heatC2Half V := by
  have hr : 0 < heatScale t := heatScale_pos ht
  unfold heatD2Half heatC2Half
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg (volume : Measure V) baseD2Half hr.le]
  simp only [smul_eq_mul]
  field_simp [hr.ne']

def heatScale34 (t : ℝ) : ℝ :=
  t ^ (-(3 : ℝ) / 4)

theorem heatScale34_eq {t : ℝ} (ht : 0 < t) :
    t⁻¹ * Real.sqrt (heatScale t) = heatScale34 t := by
  unfold heatScale34 heatScale
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_neg_one,
    ← Real.rpow_mul ht.le, ← Real.rpow_add ht]
  congr 1
  ring

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatD2_half_bound {t : ℝ} (ht : 0 < t) (v w x : V) :
    ‖heatD2 t v w x‖ * Real.sqrt ‖x‖ ≤
      ‖v‖ * ‖w‖ * heatD2Half t x := by
  rw [heatD2Half_eq ht]
  calc
    ‖heatD2 t v w x‖ * Real.sqrt ‖x‖
        ≤ (‖v‖ * ‖w‖ * heatD2Maj t x) * Real.sqrt ‖x‖ :=
      mul_le_mul_of_nonneg_right (heatD2_bound ht v w x) (Real.sqrt_nonneg _)
    _ = ‖v‖ * ‖w‖ * (Real.sqrt ‖x‖ * heatD2Maj t x) := by ring

theorem integral_halfD2 {t : ℝ} (ht : 0 < t) (v w : V) :
    (∫ x : V, ‖heatD2 t v w x‖ * Real.sqrt ‖x‖) ≤
      ‖v‖ * ‖w‖ * heatScale34 t * heatC2Half V := by
  have hmajor : Integrable
      (fun x : V => (‖v‖ * ‖w‖) * heatD2Half t x) :=
    (heatD2Half_int (V := V) ht).const_mul _
  have hleft : Integrable
      (fun x : V => ‖heatD2 t v w x‖ * Real.sqrt ‖x‖) := by
    refine hmajor.mono' ?_ ?_
    · apply Continuous.aestronglyMeasurable
      unfold heatD2 baseD2 baseHeat baseHeatMass heatScale
      fun_prop
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))]
    exact heatD2_half_bound ht v w x
  calc
    (∫ x : V, ‖heatD2 t v w x‖ * Real.sqrt ‖x‖)
        ≤ ∫ x : V, (‖v‖ * ‖w‖) * heatD2Half t x :=
      integral_mono hleft hmajor (fun x => heatD2_half_bound ht v w x)
    _ = (‖v‖ * ‖w‖) *
        (t⁻¹ * Real.sqrt (heatScale t) * heatC2Half V) := by
      rw [integral_const_mul, integral_heatD2Half ht]
    _ = ‖v‖ * ‖w‖ * heatScale34 t * heatC2Half V := by
      rw [heatScale34_eq ht]
      ring

end HalfMoment

section CancelOperator

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def heatD2Cancel (t : ℝ) (v w : V) (f : V → F) (x : V) : F :=
  ∫ y : V, heatD2 t v w y • (f (x - y) - f x)

def heatD2Convolution (t : ℝ) (v w : V) (f : V → F) (x : V) : F :=
  ∫ y : V, heatD2 t v w y • f (x - y)

omit [Nontrivial V] [CompleteSpace F] in
theorem heatD2Convolution_comm (t : ℝ) (v w : V) (f : V → F) (x : V) :
    heatD2Convolution t v w f x = heatD2Convolution t w v f x := by
  unfold heatD2Convolution
  apply integral_congr_ae
  filter_upwards with y
  rw [heatD2_comm]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] [Nontrivial V] [NormedSpace ℝ F] [CompleteSpace F] in
private theorem holder_half_bound {K : ℝ≥0} {f : V → F}
    (hf : HolderWith K (1 / 2 : ℝ≥0) f) (x y : V) :
    ‖f (x - y) - f x‖ ≤ (K : ℝ) * Real.sqrt ‖y‖ := by
  have hxy : dist (x - y) x = ‖y‖ := by
    rw [dist_eq_norm]
    have : (x - y) - x = -y := by abel
    rw [this, norm_neg]
  have h := hf.dist_le (x - y) x
  rw [dist_eq_norm, hxy] at h
  simpa [Real.sqrt_eq_rpow] using h

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] [CompleteSpace F] in
private theorem cancel_bound {t : ℝ} (ht : 0 < t) {K : ℝ≥0}
    {f : V → F} (hf : HolderWith K (1 / 2 : ℝ≥0) f)
    (v w x y : V) :
    ‖heatD2 t v w y • (f (x - y) - f x)‖ ≤
      (‖v‖ * ‖w‖ * (K : ℝ)) * heatD2Half t y := by
  calc
    ‖heatD2 t v w y • (f (x - y) - f x)‖
        = ‖heatD2 t v w y‖ * ‖f (x - y) - f x‖ := by
          rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖heatD2 t v w y‖ * ((K : ℝ) * Real.sqrt ‖y‖) :=
      mul_le_mul_of_nonneg_left (holder_half_bound hf x y) (norm_nonneg _)
    _ ≤ (‖v‖ * ‖w‖ * heatD2Maj t y) *
        ((K : ℝ) * Real.sqrt ‖y‖) := by
      gcongr
      exact heatD2_bound ht v w y
    _ = (‖v‖ * ‖w‖ * (K : ℝ)) * heatD2Half t y := by
      rw [heatD2Half_eq ht]
      ring

omit [CompleteSpace F] in
theorem heatD2Cancel_int {t : ℝ} (ht : 0 < t) {K : ℝ≥0}
    {f : V → F} (hf : HolderWith K (1 / 2 : ℝ≥0) f)
    (v w x : V) :
    Integrable (fun y : V => heatD2 t v w y • (f (x - y) - f x)) := by
  have hfcont : Continuous f := hf.continuous (by norm_num)
  have hmajor : Integrable
      (fun y : V => (‖v‖ * ‖w‖ * (K : ℝ)) * heatD2Half t y) :=
    (heatD2Half_int (V := V) ht).const_mul _
  refine hmajor.mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    unfold heatD2 baseD2 baseHeat baseHeatMass heatScale
    fun_prop
  · filter_upwards with y
    exact cancel_bound ht hf v w x y

omit [CompleteSpace F] in
theorem heatD2Convolution_int {t : ℝ} (ht : 0 < t) {K : ℝ≥0}
    {f : V → F} (hf : HolderWith K (1 / 2 : ℝ≥0) f)
    (v w x : V) :
    Integrable (fun y : V => heatD2 t v w y • f (x - y)) := by
  have hcancel := heatD2Cancel_int ht hf v w x
  have hconst := (heatD2_int ht v w).smul_const (f x)
  refine (hcancel.add hconst).congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [Pi.add_apply, smul_sub, sub_add_cancel]

theorem heatD2Convolution_eq_cancel {t : ℝ} (ht : 0 < t) {K : ℝ≥0}
    {f : V → F} (hf : HolderWith K (1 / 2 : ℝ≥0) f)
    (v w x : V) :
    heatD2Convolution t v w f x = heatD2Cancel t v w f x := by
  have hcancel := heatD2Cancel_int ht hf v w x
  have hconst := (heatD2_int ht v w).smul_const (f x)
  unfold heatD2Convolution heatD2Cancel
  calc
    (∫ y : V, heatD2 t v w y • f (x - y)) =
        ∫ y : V, heatD2 t v w y • (f (x - y) - f x) +
          heatD2 t v w y • f x := by
      apply integral_congr_ae
      filter_upwards with y
      simp only [smul_sub, sub_add_cancel]
    _ = (∫ y : V, heatD2 t v w y • (f (x - y) - f x)) +
          ∫ y : V, heatD2 t v w y • f x := integral_add hcancel hconst
    _ = ∫ y : V, heatD2 t v w y • (f (x - y) - f x) := by
      rw [integral_smul_const, integral_heatD2_zero ht, zero_smul, add_zero]

omit [CompleteSpace F] in
theorem heatD2Cancel_norm {t : ℝ} (ht : 0 < t) {K : ℝ≥0}
    {f : V → F} (hf : HolderWith K (1 / 2 : ℝ≥0) f)
    (v w x : V) :
    ‖heatD2Cancel t v w f x‖ ≤
      ‖v‖ * ‖w‖ * (K : ℝ) * heatScale34 t * heatC2Half V := by
  unfold heatD2Cancel
  calc
    ‖∫ y : V, heatD2 t v w y • (f (x - y) - f x)‖
        ≤ ∫ y : V, (‖v‖ * ‖w‖ * (K : ℝ)) * heatD2Half t y :=
      norm_integral_le_of_norm_le
        ((heatD2Half_int (V := V) ht).const_mul _)
        (Filter.Eventually.of_forall fun y => cancel_bound ht hf v w x y)
    _ = (‖v‖ * ‖w‖ * (K : ℝ)) *
        (t⁻¹ * Real.sqrt (heatScale t) * heatC2Half V) := by
      rw [integral_const_mul, integral_heatD2Half ht]
    _ = ‖v‖ * ‖w‖ * (K : ℝ) * heatScale34 t * heatC2Half V := by
      rw [heatScale34_eq ht]
      ring

end CancelOperator

end HeatEquation
