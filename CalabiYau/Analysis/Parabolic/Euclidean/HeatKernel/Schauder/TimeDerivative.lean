-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Parabolic/Euclidean/HeatKernel/Schauder/TimeDerivative.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Parabolic.Euclidean.HeatKernel.Schauder.ThirdDerivative
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

-- and its private helpers occur in public declarations.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open MeasureTheory Real Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace HeatEquation

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

def baseD2DtHolder (alpha : NNReal) (x : V) : Real :=
  ‖x‖ ^ (alpha : Real) * baseD2DtMaj x

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
omit [FiniteDimensional ℝ V] in
theorem baseD2DtHolder_nonneg (alpha : NNReal) (x : V) :
    0 ≤ baseD2DtHolder alpha x :=
  mul_nonneg (Real.rpow_nonneg (norm_nonneg x) _) (baseD2DtMaj_nonneg x)

private theorem baseD2DtFirst_int :
    Integrable (fun x : V ↦ ‖x‖ * baseD2DtMaj x) := by
  let c : Real := ((Module.finrank Real V : Real) + 2) / 2
  have h5 := (gaussMoment_int (V := V) 5
    (by positivity : (0 : Real) < (4 : Real)⁻¹)).const_mul
      ((16 : Real)⁻¹ * (baseHeatMass V)⁻¹)
  have h3 := (gaussMoment_int (V := V) 3
    (by positivity : (0 : Real) < (4 : Real)⁻¹)).const_mul
      ((c * (4 : Real)⁻¹ + (3 / 8 : Real)) * (baseHeatMass V)⁻¹)
  have h1 := (gaussMoment_int (V := V) 1
    (by positivity : (0 : Real) < (4 : Real)⁻¹)).const_mul
      ((c * (2 : Real)⁻¹) * (baseHeatMass V)⁻¹)
  have heq : (fun x : V ↦ ‖x‖ * baseD2DtMaj x) = fun x : V ↦
      ((16 : Real)⁻¹ * (baseHeatMass V)⁻¹) *
          (‖x‖ ^ 5 * Real.exp (-(4 : Real)⁻¹ * ‖x‖ ^ 2)) +
        ((c * (4 : Real)⁻¹ + (3 / 8 : Real)) * (baseHeatMass V)⁻¹) *
          (‖x‖ ^ 3 * Real.exp (-(4 : Real)⁻¹ * ‖x‖ ^ 2)) +
        ((c * (2 : Real)⁻¹) * (baseHeatMass V)⁻¹) *
          (‖x‖ ^ 1 * Real.exp (-(4 : Real)⁻¹ * ‖x‖ ^ 2)) := by
    funext x
    unfold baseD2DtMaj baseD2Maj baseD3Maj baseHeat
    dsimp [c]
    ring
  rw [heq]
  exact (h5.add h3).add h1

theorem baseD2DtHolder_int {alpha : NNReal} (halpha : alpha ≤ 1) :
    Integrable (baseD2DtHolder alpha : V → Real) := by
  have hmajor : Integrable (fun x : V ↦ (1 + ‖x‖) * baseD2DtMaj x) := by
    have h := (baseD2DtMaj_int (V := V)).add baseD2DtFirst_int
    have heq : (fun x : V ↦ (1 + ‖x‖) * baseD2DtMaj x) =
        fun x : V ↦ baseD2DtMaj x + ‖x‖ * baseD2DtMaj x := by
      funext x
      ring
    rw [heq]
    exact h
  refine hmajor.mono' ?_ ?_
  · have hpow : Continuous (fun x : V ↦ ‖x‖ ^ (alpha : Real)) :=
      continuous_norm.rpow_const (fun _ ↦ Or.inr alpha.coe_nonneg)
    have hmaj : Continuous (baseD2DtMaj : V → Real) := by
      unfold baseD2DtMaj baseD2Maj baseD3Maj baseHeat baseHeatMass
      fun_prop
    exact (hpow.mul hmaj).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (baseD2DtHolder_nonneg alpha x)]
  have hrpow : ‖x‖ ^ (alpha : Real) ≤ 1 + ‖x‖ := by
    by_cases hx : ‖x‖ ≤ 1
    · exact (Real.rpow_le_one (norm_nonneg x) hx alpha.coe_nonneg).trans
        (le_add_of_nonneg_right (norm_nonneg x))
    · have hx' : 1 ≤ ‖x‖ := le_of_not_ge hx
      exact (Real.rpow_le_self_of_one_le hx' (by exact_mod_cast halpha)).trans
        (le_add_of_nonneg_left zero_le_one)
  exact mul_le_mul_of_nonneg_right hrpow (baseD2DtMaj_nonneg x)

def heatC2DtHolder (alpha : NNReal) : Real :=
  ∫ x : V, baseD2DtHolder alpha x

omit [Nontrivial V] in
theorem heatC2DtHolder_nonneg (alpha : NNReal) :
    0 ≤ heatC2DtHolder (V := V) alpha :=
  integral_nonneg (baseD2DtHolder_nonneg alpha)

def heatD2DtHolder (alpha : NNReal) (t : Real) (x : V) : Real :=
  ((heatScale t) ^ Module.finrank Real V)⁻¹ * (t ^ 2)⁻¹ *
    (heatScale t) ^ (alpha : Real) *
      baseD2DtHolder alpha ((heatScale t)⁻¹ • x)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
omit [FiniteDimensional ℝ V] in
theorem heatD2DtHolder_eq (alpha : NNReal) {t : Real}
    (ht : 0 < t) (x : V) :
    heatD2DtHolder alpha t x =
      ‖x‖ ^ (alpha : Real) * heatD2DtMaj t x := by
  have hr : 0 < heatScale t := heatScale_pos ht
  have hx : x = heatScale t • ((heatScale t)⁻¹ • x) := by
    simp [hr.ne']
  have hrpow : ‖x‖ ^ (alpha : Real) =
      (heatScale t) ^ (alpha : Real) *
        ‖(heatScale t)⁻¹ • x‖ ^ (alpha : Real) := by
    calc
      ‖x‖ ^ (alpha : Real) =
          ‖heatScale t • ((heatScale t)⁻¹ • x)‖ ^ (alpha : Real) :=
        congrArg (fun z : V ↦ ‖z‖ ^ (alpha : Real)) hx
      _ = (heatScale t * ‖(heatScale t)⁻¹ • x‖) ^ (alpha : Real) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      _ = (heatScale t) ^ (alpha : Real) *
          ‖(heatScale t)⁻¹ • x‖ ^ (alpha : Real) :=
        Real.mul_rpow hr.le (norm_nonneg _)
  unfold heatD2DtHolder heatD2DtMaj baseD2DtHolder
  rw [hrpow]
  ring

theorem heatD2DtHolder_int {alpha : NNReal} (halpha : alpha ≤ 1)
    {t : Real} (ht : 0 < t) :
    Integrable (heatD2DtHolder (V := V) alpha t) := by
  unfold heatD2DtHolder
  exact (baseD2DtHolder_int (V := V) halpha).comp_smul
    (inv_ne_zero (heatScale_pos ht).ne') |>.const_mul _

omit [Nontrivial V] in
theorem integral_heatD2DtHolder (alpha : NNReal) {t : Real}
    (ht : 0 < t) :
    ∫ x : V, heatD2DtHolder alpha t x =
      (t ^ 2)⁻¹ * (heatScale t) ^ (alpha : Real) *
        heatC2DtHolder (V := V) alpha := by
  have hr : 0 < heatScale t := heatScale_pos ht
  unfold heatD2DtHolder heatC2DtHolder
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg
      (volume : Measure V) (baseD2DtHolder alpha) hr.le]
  simp only [smul_eq_mul]
  field_simp [hr.ne']

def holderSecondTimeHeatScale (alpha : NNReal) (t : Real) : Real :=
  t ^ ((alpha : Real) / 2 - 2)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem holderSecondTimeHeatScale_eq (alpha : NNReal) {t : Real}
    (ht : 0 < t) :
    (t ^ 2)⁻¹ * (heatScale t) ^ (alpha : Real) =
      holderSecondTimeHeatScale alpha t := by
  unfold holderSecondTimeHeatScale heatScale
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one,
    ← Real.rpow_natCast, ← Real.rpow_mul ht.le, ← Real.rpow_mul ht.le,
    ← Real.rpow_add ht]
  congr 1
  ring

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
omit [FiniteDimensional ℝ V] in
theorem heatD2Dt_holder_bound (alpha : NNReal) {t : Real}
    (ht : 0 < t) (v w x : V) :
    ‖heatD2Dt t v w x‖ * ‖x‖ ^ (alpha : Real) ≤
      ‖v‖ * ‖w‖ * heatD2DtHolder alpha t x := by
  rw [heatD2DtHolder_eq alpha ht]
  calc
    ‖heatD2Dt t v w x‖ * ‖x‖ ^ (alpha : Real) ≤
        (‖v‖ * ‖w‖ * heatD2DtMaj t x) * ‖x‖ ^ (alpha : Real) :=
      mul_le_mul_of_nonneg_right (heatD2Dt_bound ht v w x)
        (Real.rpow_nonneg (norm_nonneg x) _)
    _ = ‖v‖ * ‖w‖ *
        (‖x‖ ^ (alpha : Real) * heatD2DtMaj t x) := by ring

theorem integral_holderD2Dt {alpha : NNReal} (halpha : alpha ≤ 1)
    {t : Real} (ht : 0 < t) (v w : V) :
    (∫ x : V, ‖heatD2Dt t v w x‖ * ‖x‖ ^ (alpha : Real)) ≤
      ‖v‖ * ‖w‖ * holderSecondTimeHeatScale alpha t *
        heatC2DtHolder (V := V) alpha := by
  have hmajor : Integrable
      (fun x : V ↦ (‖v‖ * ‖w‖) * heatD2DtHolder alpha t x) :=
    (heatD2DtHolder_int (V := V) halpha ht).const_mul _
  have hleft : Integrable
      (fun x : V ↦ ‖heatD2Dt t v w x‖ * ‖x‖ ^ (alpha : Real)) := by
    refine hmajor.mono' ?_ ?_
    · apply Continuous.aestronglyMeasurable
      have hpow : Continuous (fun x : V ↦ ‖x‖ ^ (alpha : Real)) :=
        continuous_norm.rpow_const (fun _ ↦ Or.inr alpha.coe_nonneg)
      have hd2dt : Continuous (fun x : V ↦ heatD2Dt t v w x) := by
        unfold heatD2Dt baseD2Dt baseD2 baseD3 baseHeat baseHeatMass heatScale
        fun_prop
      exact hd2dt.norm.mul hpow
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg x) _))]
    exact heatD2Dt_holder_bound alpha ht v w x
  calc
    (∫ x : V, ‖heatD2Dt t v w x‖ * ‖x‖ ^ (alpha : Real)) ≤
        ∫ x : V, (‖v‖ * ‖w‖) * heatD2DtHolder alpha t x :=
      integral_mono hleft hmajor
        (fun x ↦ heatD2Dt_holder_bound alpha ht v w x)
    _ = (‖v‖ * ‖w‖) *
        ((t ^ 2)⁻¹ * (heatScale t) ^ (alpha : Real) *
          heatC2DtHolder (V := V) alpha) := by
      rw [integral_const_mul, integral_heatD2DtHolder alpha ht]
    _ = ‖v‖ * ‖w‖ * holderSecondTimeHeatScale alpha t *
        heatC2DtHolder (V := V) alpha := by
      rw [holderSecondTimeHeatScale_eq alpha ht]
      ring

theorem holderSecondTimeHeatScale_intervalIntegrable {alpha : NNReal}
    {a b : Real} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (holderSecondTimeHeatScale alpha) volume a b := by
  unfold holderSecondTimeHeatScale
  apply ContinuousOn.intervalIntegrable
  intro t ht
  apply (Real.continuousAt_rpow_const t ((alpha : Real) / 2 - 2)
    (Or.inl ?_)).continuousWithinAt
  rw [uIcc_of_le hab] at ht
  exact (ha.trans_le ht.1).ne'

theorem holderSecondTimeHeatScale_integral_le {alpha : NNReal}
    (halpha : alpha < 2) {d T : Real} (hd : 0 < d) (hT : d ≤ T) :
    ∫ t : Real in d..T, holderSecondTimeHeatScale alpha t ≤
      (2 / (2 - (alpha : Real))) * d ^ ((alpha : Real) / 2 - 1) := by
  let q : Real := (alpha : Real) / 2 - 1
  have halpha_real : (alpha : Real) < 2 := by exact_mod_cast halpha
  have hT0 : 0 < T := hd.trans_le hT
  have hq : q < 0 := by
    dsimp [q]
    linarith
  have hqne : q ≠ 0 := hq.ne
  have hden : 2 - (alpha : Real) ≠ 0 := by linarith
  have hden' : (alpha : Real) - 2 ≠ 0 := by linarith
  have hpne : (alpha : Real) / 2 - 2 ≠ -1 := by
    intro heq
    linarith
  have hzero : 0 ∉ uIcc d T := by
    rw [uIcc_of_le hT]
    simp only [mem_Icc, not_and_or]
    exact Or.inl (not_le.mpr hd)
  unfold holderSecondTimeHeatScale
  rw [integral_rpow (Or.inr ⟨hpne, hzero⟩)]
  have hexp : (alpha : Real) / 2 - 2 + 1 = q := by
    dsimp [q]
    ring
  rw [hexp]
  have hrewrite : (T ^ q - d ^ q) / q =
      (2 / (2 - (alpha : Real))) * (d ^ q - T ^ q) := by
    dsimp [q] at hqne ⊢
    field_simp [hden, hden', hqne]
    ring
  rw [hrewrite]
  have hcoef : 0 ≤ 2 / (2 - (alpha : Real)) := by
    exact div_nonneg (by norm_num) (sub_nonneg.mpr halpha_real.le)
  calc
    (2 / (2 - (alpha : Real))) * (d ^ q - T ^ q) ≤
        (2 / (2 - (alpha : Real))) * d ^ q := by
      exact mul_le_mul_of_nonneg_left
        (sub_le_self _ (Real.rpow_nonneg hT0.le q)) hcoef
    _ = (2 / (2 - (alpha : Real))) * d ^ ((alpha : Real) / 2 - 1) := by
      rfl

theorem mul_holderSecondTimeHeatScale_integral_le {alpha : NNReal}
    (halpha : alpha < 2) {d T : Real} (hd : 0 < d) (hT : d ≤ T) :
    d * (∫ t : Real in d..T, holderSecondTimeHeatScale alpha t) ≤
      (2 / (2 - (alpha : Real))) * d ^ ((alpha : Real) / 2) := by
  have h := mul_le_mul_of_nonneg_left
    (holderSecondTimeHeatScale_integral_le halpha hd hT) hd.le
  refine h.trans_eq ?_
  calc
    d * ((2 / (2 - (alpha : Real))) * d ^ ((alpha : Real) / 2 - 1)) =
        (2 / (2 - (alpha : Real))) *
          (d ^ (1 : Real) * d ^ ((alpha : Real) / 2 - 1)) := by
      rw [Real.rpow_one]
      ring_nf
    _ = (2 / (2 - (alpha : Real))) *
        d ^ (1 + ((alpha : Real) / 2 - 1)) := by
      rw [Real.rpow_add hd]
    _ = (2 / (2 - (alpha : Real))) * d ^ ((alpha : Real) / 2) := by
      congr 1
      ring_nf

omit [MeasurableSpace V] [BorelSpace V] in
theorem heatD2_time_add_sub_eq_integral_heatD2Dt
    {t d : Real} (ht : 0 < t) (hd : 0 ≤ d) (v w x : V) :
    heatD2 (t + d) v w x - heatD2 t v w x =
      ∫ r : Real in t..t + d, heatD2Dt r v w x := by
  have hpos : ∀ r ∈ uIcc t (t + d), 0 < r := by
    intro r hr
    rw [uIcc_of_le (le_add_of_nonneg_right hd)] at hr
    exact ht.trans_le hr.1
  have hderiv : IntervalIntegrable
      (fun r : Real ↦ heatD2Dt r v w x) volume t (t + d) := by
    apply ContinuousOn.intervalIntegrable
    intro r hr
    have hrpos := hpos r hr
    have hrne : r ≠ 0 := hrpos.ne'
    have hsne : heatScale r ≠ 0 := (heatScale_pos hrpos).ne'
    have hpne : heatScale r ^ Module.finrank Real V ≠ 0 := pow_ne_zero _ hsne
    have hr2ne : r ^ 2 ≠ 0 := pow_ne_zero _ hrne
    unfold heatD2Dt baseD2Dt baseD2 baseD3 baseHeat baseHeatMass heatScale
    fun_prop (disch := assumption)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r hr ↦ heatD2_time (hpos r hr) v w x) hderiv |>.symm

omit [MeasurableSpace V] [BorelSpace V] in
private theorem heatD2_time_add_diff_holder_point {alpha : NNReal}
    {t d : Real} (ht : 0 < t) (hd : 0 ≤ d) (v w x : V) :
    ‖heatD2 (t + d) v w x - heatD2 t v w x‖ *
        ‖x‖ ^ (alpha : Real) ≤
      ∫ r : Real in t..t + d,
        ‖heatD2Dt r v w x‖ * ‖x‖ ^ (alpha : Real) := by
  rw [heatD2_time_add_sub_eq_integral_heatD2Dt ht hd]
  calc
    ‖∫ r : Real in t..t + d, heatD2Dt r v w x‖ *
        ‖x‖ ^ (alpha : Real) ≤
      (∫ r : Real in t..t + d, ‖heatD2Dt r v w x‖) *
        ‖x‖ ^ (alpha : Real) := by
      gcongr
      exact intervalIntegral.norm_integral_le_integral_norm
        (le_add_of_nonneg_right hd)
    _ = ∫ r : Real in t..t + d,
        ‖heatD2Dt r v w x‖ * ‖x‖ ^ (alpha : Real) := by
      rw [intervalIntegral.integral_mul_const]

theorem heatD2_time_add_diff_holder {alpha : NNReal} (halpha : alpha ≤ 1)
    {t d : Real} (ht : 0 < t) (hd : 0 ≤ d) (v w : V) :
    (∫ x : V, ‖heatD2 (t + d) v w x - heatD2 t v w x‖ *
      ‖x‖ ^ (alpha : Real)) ≤
      d * ‖v‖ * ‖w‖ * holderSecondTimeHeatScale alpha t *
        heatC2DtHolder (V := V) alpha := by
  let μ : Measure Real := volume.restrict (Ioc t (t + d))
  let G : Real × V → Real := fun z ↦
    ‖heatD2Dt z.1 v w z.2‖ * ‖z.2‖ ^ (alpha : Real)
  let C : Real := ‖v‖ * ‖w‖ * holderSecondTimeHeatScale alpha t *
    heatC2DtHolder (V := V) alpha
  have htd : t ≤ t + d := le_add_of_nonneg_right hd
  have hq : (alpha : Real) / 2 - 2 ≤ 0 := by
    have ha : (alpha : Real) ≤ 1 := by exact_mod_cast halpha
    linarith
  have hslice_pos : ∀ r ∈ Icc t (t + d), 0 < r := by
    intro r hr
    exact ht.trans_le hr.1
  have hslice_int : ∀ r ∈ Icc t (t + d),
      Integrable (fun x : V ↦ G (r, x)) := by
    intro r hr
    have hrpos := hslice_pos r hr
    have hmajor : Integrable
        (fun x : V ↦ (‖v‖ * ‖w‖) * heatD2DtHolder alpha r x) :=
      (heatD2DtHolder_int (V := V) halpha hrpos).const_mul _
    refine hmajor.mono' ?_ ?_
    · apply Continuous.aestronglyMeasurable
      have hpow : Continuous (fun x : V ↦ ‖x‖ ^ (alpha : Real)) :=
        continuous_norm.rpow_const (fun _ ↦ Or.inr alpha.coe_nonneg)
      have hd2dt : Continuous (fun x : V ↦ heatD2Dt r v w x) := by
        unfold heatD2Dt baseD2Dt baseD2 baseD3 baseHeat baseHeatMass heatScale
        fun_prop
      exact hd2dt.norm.mul hpow
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg x) _))]
    exact heatD2Dt_holder_bound alpha hrpos v w x
  have hslice_le : ∀ r ∈ Icc t (t + d),
      (∫ x : V, G (r, x)) ≤ C := by
    intro r hr
    have hrpos := hslice_pos r hr
    have hscale : holderSecondTimeHeatScale alpha r ≤
        holderSecondTimeHeatScale alpha t := by
      unfold holderSecondTimeHeatScale
      exact Real.rpow_le_rpow_of_nonpos ht hr.1 hq
    calc
      (∫ x : V, G (r, x)) ≤
          ‖v‖ * ‖w‖ * holderSecondTimeHeatScale alpha r *
            heatC2DtHolder (V := V) alpha :=
        integral_holderD2Dt halpha hrpos v w
      _ ≤ ‖v‖ * ‖w‖ * holderSecondTimeHeatScale alpha t *
            heatC2DtHolder (V := V) alpha := by
        gcongr
        exact heatC2DtHolder_nonneg alpha
      _ = C := by rfl
  have hGmeas : AEStronglyMeasurable G (μ.prod (volume : Measure V)) := by
    apply Measurable.aestronglyMeasurable
    unfold G heatD2Dt baseD2Dt baseD2 baseD3 baseHeat baseHeatMass heatScale
    fun_prop
  have houter : Integrable (fun r : Real ↦ ∫ x : V, ‖G (r, x)‖) μ := by
    have hconst : IntegrableOn (fun _ : Real ↦ C) (Ioc t (t + d)) :=
      integrableOn_const measure_Ioc_lt_top.ne
    refine hconst.mono' hGmeas.norm.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr' : r ∈ Icc t (t + d) := ⟨hr.1.le, hr.2⟩
    have hnonneg : 0 ≤ ∫ x : V, ‖G (r, x)‖ :=
      integral_nonneg (fun _ ↦ norm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    have heq : (∫ x : V, ‖G (r, x)‖) = ∫ x : V, G (r, x) := by
      apply integral_congr_ae
      filter_upwards with x
      change |‖heatD2Dt r v w x‖ * ‖x‖ ^ (alpha : Real)| = _
      rw [abs_of_nonneg]
      exact mul_nonneg (norm_nonneg _)
        (Real.rpow_nonneg (norm_nonneg x) _)
    rw [heq]
    exact hslice_le r hr'
  have hGint : Integrable G (μ.prod (volume : Measure V)) := by
    exact (integrable_prod_iff hGmeas).2 ⟨by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact hslice_int r ⟨hr.1.le, hr.2⟩, houter⟩
  have hleft : Integrable (fun x : V ↦
      ‖heatD2 (t + d) v w x - heatD2 t v w x‖ *
        ‖x‖ ^ (alpha : Real)) := by
    have htargetmeas : AEStronglyMeasurable (fun x : V ↦
        ‖heatD2 (t + d) v w x - heatD2 t v w x‖ *
          ‖x‖ ^ (alpha : Real)) := by
      have hpow : Continuous (fun x : V ↦ ‖x‖ ^ (alpha : Real)) :=
        continuous_norm.rpow_const (fun _ ↦ Or.inr alpha.coe_nonneg)
      have hplus : Continuous (fun x : V ↦ heatD2 (t + d) v w x) := by
        unfold heatD2 baseD2 baseHeat baseHeatMass heatScale
        fun_prop
      have hnow : Continuous (fun x : V ↦ heatD2 t v w x) := by
        unfold heatD2 baseD2 baseHeat baseHeatMass heatScale
        fun_prop
      exact (hplus.sub hnow).norm.mul hpow |>.aestronglyMeasurable
    have hright := hGint.integral_prod_right
    refine hright.mono' htargetmeas ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg x) _))]
    change _ ≤ ∫ r : Real in Ioc t (t + d), G (r, x)
    rw [← intervalIntegral.integral_of_le htd]
    simpa only [G] using
      heatD2_time_add_diff_holder_point (alpha := alpha) ht hd v w x
  have hright := hGint.integral_prod_right
  calc
    (∫ x : V, ‖heatD2 (t + d) v w x - heatD2 t v w x‖ *
        ‖x‖ ^ (alpha : Real)) ≤
        ∫ x : V, ∫ r : Real, G (r, x) ∂μ := by
      exact integral_mono hleft hright (fun x ↦ by
        change _ ≤ ∫ r : Real in Ioc t (t + d), G (r, x)
        rw [← intervalIntegral.integral_of_le htd]
        simpa only [G] using
          heatD2_time_add_diff_holder_point (alpha := alpha) ht hd v w x)
    _ = ∫ r : Real, (∫ x : V, G (r, x)) ∂μ := by
      exact (integral_integral_swap (f := fun r x ↦ G (r, x)) hGint).symm
    _ ≤ ∫ _r : Real, C ∂μ := by
      apply integral_mono_ae hGint.integral_prod_left
        (by
          change IntegrableOn (fun _ : Real ↦ C) (Ioc t (t + d))
          exact integrableOn_const measure_Ioc_lt_top.ne)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact hslice_le r ⟨hr.1.le, hr.2⟩
    _ = d * C := by
      rw [MeasureTheory.integral_const]
      simp only [μ, measureReal_restrict_apply_univ,
        Real.volume_real_Ioc_of_le htd, add_sub_cancel_left, smul_eq_mul]
    _ = d * ‖v‖ * ‖w‖ * holderSecondTimeHeatScale alpha t *
        heatC2DtHolder (V := V) alpha := by
      unfold C
      ring

theorem heatD2_time_add_diff_holder_int {alpha : NNReal}
    (halpha : alpha ≤ 1) {t d : Real} (ht : 0 < t) (hd : 0 ≤ d)
    (v w : V) :
    Integrable (fun y : V ↦
      ‖heatD2 (t + d) v w y - heatD2 t v w y‖ *
        ‖y‖ ^ (alpha : Real)) := by
  have hweighted : ∀ {r : Real}, 0 < r → Integrable (fun y : V ↦
      ‖heatD2 r v w y‖ * ‖y‖ ^ (alpha : Real)) := by
    intro r hr
    have hmajor : Integrable
        (fun y : V ↦ (‖v‖ * ‖w‖) * heatD2Holder alpha r y) :=
      (heatD2Holder_int (V := V) halpha hr).const_mul _
    refine hmajor.mono' ?_ ?_
    · apply Continuous.aestronglyMeasurable
      have hpow : Continuous (fun y : V ↦ ‖y‖ ^ (alpha : Real)) :=
        continuous_norm.rpow_const (fun _ ↦ Or.inr alpha.coe_nonneg)
      have hd2 : Continuous (fun y : V ↦ heatD2 r v w y) := by
        unfold heatD2 baseD2 baseHeat baseHeatMass heatScale
        fun_prop
      exact hd2.norm.mul hpow
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg y) _))]
    exact heatD2_holder_bound alpha hr v w y
  have hplus := hweighted (ht.trans_le (le_add_of_nonneg_right hd))
  have hnow := hweighted ht
  refine (hplus.add hnow).mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    have hpow : Continuous (fun y : V ↦ ‖y‖ ^ (alpha : Real)) :=
      continuous_norm.rpow_const (fun _ ↦ Or.inr alpha.coe_nonneg)
    have hplusc : Continuous (fun y : V ↦ heatD2 (t + d) v w y) := by
      unfold heatD2 baseD2 baseHeat baseHeatMass heatScale
      fun_prop
    have hnowc : Continuous (fun y : V ↦ heatD2 t v w y) := by
      unfold heatD2 baseD2 baseHeat baseHeatMass heatScale
      fun_prop
    exact (hplusc.sub hnowc).norm.mul hpow
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg y) _))]
  calc
    ‖heatD2 (t + d) v w y - heatD2 t v w y‖ *
        ‖y‖ ^ (alpha : Real) ≤
      (‖heatD2 (t + d) v w y‖ + ‖heatD2 t v w y‖) *
        ‖y‖ ^ (alpha : Real) := by
      gcongr
      exact norm_sub_le _ _
    _ = ‖heatD2 (t + d) v w y‖ * ‖y‖ ^ (alpha : Real) +
        ‖heatD2 t v w y‖ * ‖y‖ ^ (alpha : Real) := by ring

end HeatEquation
