-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Parabolic/Euclidean/HeatPotential/TimeRealization.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Parabolic.Euclidean.HeatPotential.Schauder
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

@[expose] public section

-- Private declarations used in public declarations require the compatibility option below.

noncomputable section

open Filter MeasureTheory Real Set
open scoped Interval NNReal RealInnerProductSpace Topology

namespace HeatEquation

open CalabiYau.Schauder

variable {V F : Type*} [NormedAddCommGroup V]

section

variable [InnerProductSpace Real V] [FiniteDimensional Real V] [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

private def heatD2TimeLocalMajor (t : Real) (y : V) : Real :=
  ((heatScale (t / 2)) ^ Module.finrank Real V)⁻¹ *
    (heatScale (t / 2))⁻¹ * (heatScale (t / 2))⁻¹ *
      (baseHeatMass V)⁻¹ *
        ((2 : Real)⁻¹ *
          (1 + ‖(heatScale t)⁻¹ • y‖ ^ 2) *
            Real.exp (-(1 / 8 : Real) * ‖(heatScale t)⁻¹ • y‖ ^ 2))

private theorem heatD2TimeLocalMajor_int {t : Real} (ht : 0 < t) :
    Integrable (heatD2TimeLocalMajor (V := V) t) := by
  let g : V → Real := fun z =>
    (2 : Real)⁻¹ * (1 + ‖z‖ ^ 2) *
      Real.exp (-(1 / 8 : Real) * ‖z‖ ^ 2)
  have h0 := gaussMoment_int (V := V) 0
    (by norm_num : (0 : Real) < (1 / 8 : Real))
  have h2 := gaussMoment_int (V := V) 2
    (by norm_num : (0 : Real) < (1 / 8 : Real))
  have hg : Integrable g := by
    have heq : g = fun z : V =>
        (2 : Real)⁻¹ *
          (‖z‖ ^ 0 * Real.exp (-(1 / 8 : Real) * ‖z‖ ^ 2) +
            ‖z‖ ^ 2 * Real.exp (-(1 / 8 : Real) * ‖z‖ ^ 2)) := by
      funext z
      simp only [g, pow_zero, one_mul]
      ring
    rw [heq]
    exact (h0.add h2).const_mul _
  have hs := hg.comp_smul (inv_ne_zero (heatScale_pos ht).ne')
  refine (hs.const_mul
    (((heatScale (t / 2)) ^ Module.finrank Real V)⁻¹ *
      (heatScale (t / 2))⁻¹ * (heatScale (t / 2))⁻¹ *
        (baseHeatMass V)⁻¹)).congr (Filter.Eventually.of_forall ?_)
  intro y
  simp only [heatD2TimeLocalMajor, g]

end

section

variable [InnerProductSpace Real V] [NormedAddCommGroup F] [NormedSpace Real F]

private theorem heatD2Maj_le_timeLocalMajor {t q : Real} (ht : 0 < t)
    (hq0 : t / 2 < q) (hq1 : q < 2 * t) (y : V) :
    heatD2Maj q y ≤ heatD2TimeLocalMajor (V := V) t y := by
  have ht2 : 0 < t / 2 := by linarith
  have hq : 0 < q := ht2.trans hq0
  let rt := heatScale t
  let rh := heatScale (t / 2)
  let rq := heatScale q
  let a : V := rt⁻¹ • y
  let z : V := rq⁻¹ • y
  have hrt : 0 < rt := by simpa only [rt] using heatScale_pos ht
  have hrh : 0 < rh := by simpa only [rh] using heatScale_pos ht2
  have hrq : 0 < rq := by simpa only [rq] using heatScale_pos hq
  have hrtSq : rt ^ 2 = t := by
    simpa only [rt, heatScale] using Real.sq_sqrt ht.le
  have hrqSq : rq ^ 2 = q := by
    simpa only [rq, heatScale] using Real.sq_sqrt hq.le
  have hrh_le : rh ≤ rq := by
    unfold rh rq heatScale
    exact Real.sqrt_le_sqrt hq0.le
  have hfront :
      ((rq ^ Module.finrank Real V)⁻¹ * rq⁻¹ * rq⁻¹) ≤
        (rh ^ Module.finrank Real V)⁻¹ * rh⁻¹ * rh⁻¹ := by
    have hinv : rq⁻¹ ≤ rh⁻¹ := (inv_le_inv₀ hrq hrh).2 hrh_le
    have hpow : (rq ^ Module.finrank Real V)⁻¹ ≤
        (rh ^ Module.finrank Real V)⁻¹ := by
      rw [← inv_pow, ← inv_pow]
      exact pow_le_pow_left₀ (inv_nonneg.mpr hrq.le) hinv _
    gcongr
  have hqinv : q⁻¹ ≤ 2 * t⁻¹ := by
    have hraw : q⁻¹ < (t / 2)⁻¹ := by
      simpa only [one_div] using one_div_lt_one_div_of_lt ht2 hq0
    calc
      q⁻¹ ≤ (t / 2)⁻¹ := hraw.le
      _ = 2 * t⁻¹ := by field_simp [ht.ne']
  have htinv : (2 : Real)⁻¹ * t⁻¹ ≤ q⁻¹ := by
    have hraw : (2 * t)⁻¹ < q⁻¹ := by
      simpa only [one_div] using one_div_lt_one_div_of_lt hq hq1
    calc
      (2 : Real)⁻¹ * t⁻¹ = (2 * t)⁻¹ := by field_simp [ht.ne']
      _ ≤ q⁻¹ := hraw.le
  have hzEq : ‖z‖ ^ 2 = q⁻¹ * ‖y‖ ^ 2 := by
    unfold z
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hrq), mul_pow,
      inv_pow, hrqSq]
  have haEq : ‖a‖ ^ 2 = t⁻¹ * ‖y‖ ^ 2 := by
    unfold a
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hrt), mul_pow,
      inv_pow, hrtSq]
  have hzSq : ‖z‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 := by
    rw [hzEq, haEq]
    nlinarith [mul_le_mul_of_nonneg_right hqinv (sq_nonneg ‖y‖)]
  have haSq : ‖a‖ ^ 2 ≤ 2 * ‖z‖ ^ 2 := by
    rw [hzEq, haEq]
    nlinarith [mul_le_mul_of_nonneg_right htinv (sq_nonneg ‖y‖)]
  have hpoly : (4 : Real)⁻¹ * ‖z‖ ^ 2 + (2 : Real)⁻¹ ≤
      (2 : Real)⁻¹ * (1 + ‖a‖ ^ 2) := by
    nlinarith
  have hexpArg : -(1 / 4 : Real) * ‖z‖ ^ 2 ≤
      -(1 / 8 : Real) * ‖a‖ ^ 2 := by
    nlinarith
  have hexp : Real.exp (-(1 / 4 : Real) * ‖z‖ ^ 2) ≤
      Real.exp (-(1 / 8 : Real) * ‖a‖ ^ 2) :=
    Real.exp_le_exp.mpr hexpArg
  have hbase : baseD2Maj z ≤
      (baseHeatMass V)⁻¹ *
        ((2 : Real)⁻¹ * (1 + ‖a‖ ^ 2) *
          Real.exp (-(1 / 8 : Real) * ‖a‖ ^ 2)) := by
    have hmass : 0 ≤ (baseHeatMass V)⁻¹ :=
      inv_nonneg.mpr (baseHeatMass_pos (V := V)).le
    have hpolyNonneg : 0 ≤ (2 : Real)⁻¹ * (1 + ‖a‖ ^ 2) := by positivity
    unfold baseD2Maj baseHeat
    calc
      ((4 : Real)⁻¹ * ‖z‖ ^ 2 + (2 : Real)⁻¹) *
          ((baseHeatMass V)⁻¹ * Real.exp (-(4 : Real)⁻¹ * ‖z‖ ^ 2)) ≤
        ((2 : Real)⁻¹ * (1 + ‖a‖ ^ 2)) *
          ((baseHeatMass V)⁻¹ * Real.exp (-(4 : Real)⁻¹ * ‖z‖ ^ 2)) := by
        gcongr
      _ ≤ ((2 : Real)⁻¹ * (1 + ‖a‖ ^ 2)) *
          ((baseHeatMass V)⁻¹ *
            Real.exp (-(1 / 8 : Real) * ‖a‖ ^ 2)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (by simpa only [one_div] using hexp) hmass)
          hpolyNonneg
      _ = (baseHeatMass V)⁻¹ *
          ((2 : Real)⁻¹ * (1 + ‖a‖ ^ 2) *
            Real.exp (-(1 / 8 : Real) * ‖a‖ ^ 2)) := by ring
  have hfrontNonneg : 0 ≤
      (rq ^ Module.finrank Real V)⁻¹ * rq⁻¹ * rq⁻¹ := by positivity
  unfold heatD2Maj heatD2TimeLocalMajor
  change ((rq ^ Module.finrank Real V)⁻¹ * rq⁻¹ * rq⁻¹) * baseD2Maj z ≤ _
  calc
    ((rq ^ Module.finrank Real V)⁻¹ * rq⁻¹ * rq⁻¹) * baseD2Maj z ≤
        ((rq ^ Module.finrank Real V)⁻¹ * rq⁻¹ * rq⁻¹) *
          ((baseHeatMass V)⁻¹ *
            ((2 : Real)⁻¹ * (1 + ‖a‖ ^ 2) *
              Real.exp (-(1 / 8 : Real) * ‖a‖ ^ 2))) :=
      mul_le_mul_of_nonneg_left hbase hfrontNonneg
    _ ≤ ((rh ^ Module.finrank Real V)⁻¹ * rh⁻¹ * rh⁻¹) *
          ((baseHeatMass V)⁻¹ *
            ((2 : Real)⁻¹ * (1 + ‖a‖ ^ 2) *
              Real.exp (-(1 / 8 : Real) * ‖a‖ ^ 2))) := by
      exact mul_le_mul_of_nonneg_right hfront
        (mul_nonneg (inv_nonneg.mpr (baseHeatMass_pos (V := V)).le)
          (mul_nonneg
            (mul_nonneg (inv_nonneg.mpr (by norm_num)) (by positivity))
            (Real.exp_pos _).le))
    _ = ((heatScale (t / 2) ^ Module.finrank Real V)⁻¹ *
          (heatScale (t / 2))⁻¹ * (heatScale (t / 2))⁻¹ *
            (baseHeatMass V)⁻¹) *
        ((2 : Real)⁻¹ *
          (1 + ‖(heatScale t)⁻¹ • y‖ ^ 2) *
            Real.exp (-(1 / 8 : Real) * ‖(heatScale t)⁻¹ • y‖ ^ 2)) := by
      simp only [rt, rh, a]
      ring

private theorem heatD2TimeLocalMajor_nonneg {t : Real} (ht : 0 < t) (y : V) :
    0 ≤ heatD2TimeLocalMajor (V := V) t y := by
  have ht2 : 0 < t / 2 := by linarith
  unfold heatD2TimeLocalMajor
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht2).le _))
          (inv_nonneg.mpr (heatScale_pos ht2).le))
        (inv_nonneg.mpr (heatScale_pos ht2).le))
      (inv_nonneg.mpr (baseHeatMass_pos (V := V)).le))
    (mul_nonneg
      (mul_nonneg (inv_nonneg.mpr (by norm_num)) (by positivity))
      (Real.exp_pos _).le)

end

variable [InnerProductSpace Real V] [FiniteDimensional Real V] [NormedAddCommGroup F]
  [NormedSpace Real F] in
private theorem heatDt_norm_le_timeLocalMajor {t q : Real} (ht : 0 < t)
    (hq0 : t / 2 < q) (hq1 : q < 2 * t) (y : V) :
    ‖heatDt q y‖ ≤
      Module.finrank Real V * heatD2TimeLocalMajor (V := V) t y := by
  have hq : 0 < q := (by linarith : 0 < t / 2).trans hq0
  rw [heatDt_eq_trace hq]
  calc
    ‖∑ i : Fin (Module.finrank Real V),
        heatD2 q ((stdOrthonormalBasis Real V) i)
          ((stdOrthonormalBasis Real V) i) y‖ ≤
      ∑ i : Fin (Module.finrank Real V),
        ‖heatD2 q ((stdOrthonormalBasis Real V) i)
          ((stdOrthonormalBasis Real V) i) y‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (Module.finrank Real V),
        heatD2TimeLocalMajor (V := V) t y := by
      apply Finset.sum_le_sum
      intro i hi
      have hraw := heatD2_bound hq ((stdOrthonormalBasis Real V) i)
        ((stdOrthonormalBasis Real V) i) y
      rw [(stdOrthonormalBasis Real V).norm_eq_one i, one_mul] at hraw
      have hraw' : ‖heatD2 q ((stdOrthonormalBasis Real V) i)
          ((stdOrthonormalBasis Real V) i) y‖ ≤ heatD2Maj q y := by
        simpa only [one_mul] using hraw
      exact hraw'.trans (heatD2Maj_le_timeLocalMajor ht hq0 hq1 y)
    _ = Module.finrank Real V * heatD2TimeLocalMajor (V := V) t y := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]

variable [InnerProductSpace Real V] [FiniteDimensional Real V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace Real F] in
def heatLapSup (t : Real) (u : BoundedContinuousFunction V F) (x : V) : F :=
  ∑ i : Fin (Module.finrank Real V),
    heatD2Convolution t ((stdOrthonormalBasis Real V) i)
      ((stdOrthonormalBasis Real V) i) u x

variable [InnerProductSpace Real V] [FiniteDimensional Real V] [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F] in
theorem heatSup_time_eq_heatLapSup {t : Real} (ht : 0 < t)
    (u : BoundedContinuousFunction V F) (x : V) :
    HasDerivAt (fun q : Real => heatSup q u x) (heatLapSup t u x) t := by
  let F0 : Real → V → F := fun q y => heatKernel q y • u (x - y)
  let F1 : Real → V → F := fun q y => heatDt q y • u (x - y)
  let bound : V → Real := fun y =>
    Module.finrank Real V * ‖u‖ * heatD2TimeLocalMajor (V := V) t y
  have hs : Ioo (t / 2) (2 * t) ∈ 𝓝 t :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hmeas : ∀ᶠ q in 𝓝 t,
      AEStronglyMeasurable (F0 q) (volume : Measure V) := by
    apply Filter.Eventually.of_forall
    intro q
    apply Continuous.aestronglyMeasurable
    unfold F0 heatKernel baseHeat baseHeatMass heatScale
    fun_prop
  have hint : Integrable (F0 t) := by
    simpa only [F0] using supKernel_int (heatKernel_int (V := V) ht) u x
  have hderMeas : AEStronglyMeasurable (F1 t) (volume : Measure V) := by
    apply Continuous.aestronglyMeasurable
    unfold F1 heatDt baseHeat baseHeatMass heatScale
    fun_prop (disch := positivity)
  have hbound : ∀ᵐ y ∂(volume : Measure V), ∀ q ∈ Ioo (t / 2) (2 * t),
      ‖F1 q y‖ ≤ bound y := by
    apply Filter.Eventually.of_forall
    intro y q hq
    unfold F1 bound
    rw [norm_smul]
    calc
      ‖heatDt q y‖ * ‖u (x - y)‖ ≤
          (Module.finrank Real V * heatD2TimeLocalMajor (V := V) t y) * ‖u‖ :=
        mul_le_mul (heatDt_norm_le_timeLocalMajor ht hq.1 hq.2 y)
          (u.norm_coe_le_norm (x - y)) (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (heatD2TimeLocalMajor_nonneg ht y))
      _ = bound y := by ring
  have hboundInt : Integrable bound :=
    (heatD2TimeLocalMajor_int (V := V) ht).const_mul
      (Module.finrank Real V * ‖u‖)
  have hdiff : ∀ᵐ y ∂(volume : Measure V), ∀ q ∈ Ioo (t / 2) (2 * t),
      HasDerivAt (F0 · y) (F1 q y) q := by
    apply Filter.Eventually.of_forall
    intro y q hq
    unfold F0 F1
    exact (heatKernel_time (by linarith [ht, hq.1]) y).smul_const (u (x - y))
  have hraw := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F0) (F' := F1) (bound := bound) hs hmeas hint hderMeas
      hbound hboundInt hdiff
  have htrace : (∫ y : V, F1 t y) = heatLapSup t u x := by
    have hterm : ∀ i : Fin (Module.finrank Real V), Integrable (fun y : V =>
        heatD2 t ((stdOrthonormalBasis Real V) i)
          ((stdOrthonormalBasis Real V) i) y • u (x - y)) := by
      intro i
      exact supKernel_int (heatD2_int ht ((stdOrthonormalBasis Real V) i)
        ((stdOrthonormalBasis Real V) i)) u x
    unfold heatLapSup heatD2Convolution
    rw [← MeasureTheory.integral_finsetSum _ (fun i _ => hterm i)]
    apply integral_congr_ae
    filter_upwards with y
    unfold F1
    rw [heatDt_eq_trace ht, Finset.sum_smul]
  unfold heatSup supKernel
  rw [htrace] at hraw
  simpa only [F0] using hraw.2

section

variable [InnerProductSpace Real V] [FiniteDimensional Real V] [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

theorem heatLapSup_norm_le_of_holder {alpha K : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t)
    {u : BoundedContinuousFunction V F} (hu : HolderWith K alpha u) (x : V) :
    ‖heatLapSup t u x‖ ≤
      Module.finrank Real V * ((K : Real) * holderHeatScale alpha t *
        heatC2Holder (V := V) alpha) := by
  unfold heatLapSup
  calc
    ‖∑ i : Fin (Module.finrank Real V),
        heatD2Convolution t ((stdOrthonormalBasis Real V) i)
          ((stdOrthonormalBasis Real V) i) u x‖ ≤
      ∑ i : Fin (Module.finrank Real V),
        ‖heatD2Convolution t ((stdOrthonormalBasis Real V) i)
          ((stdOrthonormalBasis Real V) i) u x‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (Module.finrank Real V),
        ((K : Real) * holderHeatScale alpha t *
          heatC2Holder (V := V) alpha) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [heatD2Convolution_eq_cancel_of_holder halpha0 halpha1 ht hu]
      have hraw := heatD2Cancel_norm_of_holder halpha1 ht hu
        ((stdOrthonormalBasis Real V) i)
        ((stdOrthonormalBasis Real V) i) x
      simpa only [(stdOrthonormalBasis Real V).norm_eq_one i, one_mul] using hraw
    _ = Module.finrank Real V * ((K : Real) * holderHeatScale alpha t *
        heatC2Holder (V := V) alpha) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]

private theorem heatLapSup_aestronglyMeasurable
    (u : BoundedContinuousFunction V F) (x : V) {t : Real} (ht : 0 < t) :
    AEStronglyMeasurable (fun q : Real => heatLapSup q u x)
      (volume.restrict (uIoc (0 : Real) t)) := by
  have hder : AEStronglyMeasurable
      (deriv fun q : Real => heatSup q u x)
      (volume.restrict (uIoc (0 : Real) t)) :=
    (aestronglyMeasurable_deriv
      (fun q : Real => heatSup q u x) volume).restrict
  apply hder.congr
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with q hq
  rw [uIoc_of_le ht.le] at hq
  exact (heatSup_time_eq_heatLapSup hq.1 u x).deriv

theorem heatLapSup_int {alpha K : NNReal} (halpha0 : 0 < alpha)
    (halpha1 : alpha ≤ 1) {t : Real} (ht : 0 < t)
    {u : BoundedContinuousFunction V F} (hu : HolderWith K alpha u) (x : V) :
    IntervalIntegrable (fun q : Real => heatLapSup q u x) volume 0 t := by
  have hscale : IntervalIntegrable (holderHeatScale alpha) volume 0 t := by
    unfold holderHeatScale
    exact intervalIntegral.intervalIntegrable_rpow' (by
      have halphaReal : 0 < (alpha : Real) := by exact_mod_cast halpha0
      linarith)
  have hmajor := hscale.const_mul
    (Module.finrank Real V * ((K : Real) * heatC2Holder (V := V) alpha))
  apply hmajor.mono_fun'
    (heatLapSup_aestronglyMeasurable u x ht)
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with q hq
  rw [uIoc_of_le ht.le] at hq
  calc
    ‖heatLapSup q u x‖ ≤
        Module.finrank Real V * ((K : Real) * holderHeatScale alpha q *
          heatC2Holder (V := V) alpha) :=
      heatLapSup_norm_le_of_holder halpha0 halpha1 hq.1 hu x
    _ = Module.finrank Real V * ((K : Real) *
        heatC2Holder (V := V) alpha) * holderHeatScale alpha q := by ring

theorem heatSup_primitive_of_holder {alpha K : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t) (u : BoundedContinuousFunction V F)
    (hu : HolderWith K alpha u) (x : V) :
    (∫ q : Real in 0..t, heatLapSup q u x) = heatSup t u x - u x := by
  have hderiv : ∀ q ∈ Ioo (0 : Real) t,
      HasDerivAt (fun r : Real => heatSup r u x) (heatLapSup q u x) q := by
    intro q hq
    exact heatSup_time_eq_heatLapSup hq.1 u x
  have hzero := heatSup_zero_of_holder halpha0 halpha1 u hu x
  have htlim : Tendsto (fun q : Real => heatSup q u x) (𝓝[<] t)
      (𝓝 (heatSup t u x)) :=
    (heatSup_time_eq_heatLapSup ht u x).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto ht hderiv
    (heatLapSup_int halpha0 halpha1 ht hu x) hzero htlim

end

variable [InnerProductSpace Real V] [FiniteDimensional Real V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace Real F] in
def heatLapPotential (t : Real)
    (f : Real → BoundedContinuousFunction V F) (x : V) : F :=
  ∫ s : Real in 0..t, heatLapSup (t - s) (f s) x

variable [InnerProductSpace Real V] [FiniteDimensional Real V] [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F] in
theorem heatLapPotential_eq_heatLapDuhamel
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t)
    (f : Real → BoundedContinuousFunction V F)
    (hf : ∀ s ∈ Icc (0 : Real) t, HolderWith K alpha (f s))
    (hmeas2 : ∀ z : V, AEStronglyMeasurable
      (fun s : Real => heatSupHessian (t - s) (f s) z)
      (volume.restrict (uIoc (0 : Real) t)))
    (x : V) :
    heatLapPotential t f x = heatLapDuhamel t (fun s z => f s z) x := by
  have hterm : ∀ i : Fin (Module.finrank Real V), IntervalIntegrable
      (fun s : Real => heatD2Convolution (t - s)
        ((stdOrthonormalBasis Real V) i)
        ((stdOrthonormalBasis Real V) i) (f s) x) volume 0 t := by
    intro i
    exact heatD2Duhamel_int_of_holder halpha0 halpha1 ht (fun s z => f s z) hf
      ((stdOrthonormalBasis Real V) i)
      ((stdOrthonormalBasis Real V) i) x
      (heatD2Convolution_time_aestronglyMeasurable ht f hmeas2
        ((stdOrthonormalBasis Real V) i)
        ((stdOrthonormalBasis Real V) i) x)
  unfold heatLapPotential heatLapSup heatLapDuhamel heatD2Duhamel
  rw [intervalIntegral.integral_finsetSum (fun i _ => hterm i)]

variable [InnerProductSpace Real V] [FiniteDimensional Real V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace Real F] in
def heatLapTriangle
    (f : Real → BoundedContinuousFunction V F) (x : V) (z : Real × Real) : F :=
  if z.2 < z.1 then heatLapSup (z.1 - z.2) (f z.2) x else 0

variable [InnerProductSpace Real V] [FiniteDimensional Real V] [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F] in
private def heatLapTriangleIntegrand
    (f : Real → BoundedContinuousFunction V F) (x : V)
    (i : Fin (Module.finrank Real V)) (z : (Real × Real) × V) : F :=
  if z.1.2 < z.1.1 then
    heatD2 (z.1.1 - z.1.2) ((stdOrthonormalBasis Real V) i)
      ((stdOrthonormalBasis Real V) i) z.2 • f z.1.2 (x - z.2)
  else 0

section

variable [InnerProductSpace Real V] [FiniteDimensional Real V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace Real F]

private theorem heatLapTriangleIntegrand_aestronglyMeasurable
    {alpha Csource : NNReal} (halpha0 : 0 < alpha)
    {S t : Real} (htS : t ≤ S)
    (f : Real → BoundedContinuousFunction V F)
    (hsource : HolderWith Csource alpha
      ((parabolicCylinder (Ioc (0 : Real) S) Set.univ).domRestrict
        (fun p => f p.time p.space)))
    (x : V) (i : Fin (Module.finrank Real V)) :
    AEStronglyMeasurable (heatLapTriangleIntegrand f x i)
      (((volume.restrict (Ioc (0 : Real) t)).prod
          (volume.restrict (Ioc (0 : Real) t))).prod volume) := by
  let D : Set ((Real × Real) × V) :=
    {z | z.1.2 ∈ Ioc (0 : Real) S ∧ z.1.2 < z.1.1}
  let Q : Set (ParabolicPoint V) :=
    parabolicCylinder (Ioc (0 : Real) S) Set.univ
  let psi : D → Q := fun z =>
    ⟨parabolicPoint z.1.1.2 (x - z.1.2), ⟨z.2.1, Set.mem_univ _⟩⟩
  let g : ((Real × Real) × V) → F := fun z =>
    heatD2 (z.1.1 - z.1.2) ((stdOrthonormalBasis Real V) i)
      ((stdOrthonormalBasis Real V) i) z.2 • f z.1.2 (x - z.2)
  have hD : MeasurableSet D := by
    apply MeasurableSet.inter
    · exact measurableSet_Ioc.preimage (measurable_snd.comp measurable_fst)
    · exact measurableSet_lt (measurable_snd.comp measurable_fst)
        (measurable_fst.comp measurable_fst)
  have hpsi : Continuous psi := by
    unfold psi parabolicPoint
    fun_prop
  have hsourceD : Continuous (fun z : D => f z.1.1.2 (x - z.1.2)) := by
    exact ((hsource.continuous halpha0).comp hpsi).congr fun _ => rfl
  have hkernelD : Continuous (fun z : D =>
      heatD2 (z.1.1.1 - z.1.1.2) ((stdOrthonormalBasis Real V) i)
        ((stdOrthonormalBasis Real V) i) z.1.2) := by
    let ρ : D → Real := fun z => Real.sqrt (z.1.1.1 - z.1.1.2)
    have hq : Continuous (fun z : D => z.1.1.1 - z.1.1.2) := by fun_prop
    have hρ : Continuous ρ := by
      exact Real.continuous_sqrt.comp hq
    have hρne : ∀ z : D, ρ z ≠ 0 := by
      intro z
      exact (Real.sqrt_pos.2 (sub_pos.mpr z.2.2)).ne'
    have hρinv : Continuous (fun z : D => (ρ z)⁻¹) :=
      hρ.inv₀ hρne
    have hpowInv : Continuous
        (fun z : D => (ρ z ^ Module.finrank Real V)⁻¹) :=
      (hρ.pow _).inv₀ (fun z => pow_ne_zero _ (hρne z))
    have harg : Continuous (fun z : D => (ρ z)⁻¹ • z.1.2) :=
      hρinv.smul (continuous_snd.comp continuous_subtype_val)
    have hbase : Continuous (fun y : V =>
        baseD2 ((stdOrthonormalBasis Real V) i)
          ((stdOrthonormalBasis Real V) i) y) := by
      unfold baseD2 baseHeat
      fun_prop
    unfold heatD2 heatScale
    change Continuous (fun z : D =>
      (ρ z ^ Module.finrank Real V)⁻¹ * (ρ z)⁻¹ * (ρ z)⁻¹ *
        baseD2 ((stdOrthonormalBasis Real V) i)
          ((stdOrthonormalBasis Real V) i) ((ρ z)⁻¹ • z.1.2))
    exact (((hpowInv.mul hρinv).mul hρinv).mul (hbase.comp harg))
  have hg : ContinuousOn g D := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact hkernelD.smul hsourceD
  have hind : AEStronglyMeasurable (D.indicator g)
      (((volume : Measure Real).prod volume).prod volume) := by
    rw [aestronglyMeasurable_indicator_iff hD]
    exact hg.aestronglyMeasurable hD
  rw [Measure.prod_restrict, Measure.restrict_prod_eq_prod_univ]
  refine hind.restrict.congr ?_
  filter_upwards [ae_restrict_mem
    ((measurableSet_Ioc.prod measurableSet_Ioc).prod MeasurableSet.univ)] with z hz
  have hzs : z.1.2 ∈ Ioc (0 : Real) S :=
    ⟨hz.1.2.1, hz.1.2.2.trans htS⟩
  by_cases hsr : z.1.2 < z.1.1
  · have hzD : z ∈ D := ⟨hzs, hsr⟩
    rw [Set.indicator_of_mem hzD]
    simp only [heatLapTriangleIntegrand, if_pos hsr, g]
  · have hzD : z ∉ D := fun h => hsr h.2
    rw [Set.indicator_of_notMem hzD]
    simp only [heatLapTriangleIntegrand, if_neg hsr]

private theorem heatLapTriangle_aestronglyMeasurable_of_holder
    {alpha Csource : NNReal} (halpha0 : 0 < alpha)
    {S t : Real} (htS : t ≤ S)
    (f : Real → BoundedContinuousFunction V F)
    (hsource : HolderWith Csource alpha
      ((parabolicCylinder (Ioc (0 : Real) S) Set.univ).domRestrict
        (fun p => f p.time p.space)))
    (x : V) :
    AEStronglyMeasurable (heatLapTriangle f x)
      ((volume.restrict (Ioc (0 : Real) t)).prod
        (volume.restrict (Ioc (0 : Real) t))) := by
  let μ : Measure Real := volume.restrict (Ioc (0 : Real) t)
  have hterm : ∀ i : Fin (Module.finrank Real V),
      AEStronglyMeasurable
        (fun z : Real × Real => if z.2 < z.1 then
          heatD2Convolution (z.1 - z.2) ((stdOrthonormalBasis Real V) i)
            ((stdOrthonormalBasis Real V) i) (f z.2) x else 0) (μ.prod μ) := by
    intro i
    have hraw := (heatLapTriangleIntegrand_aestronglyMeasurable
      halpha0 htS f hsource x i).integral_prod_right'
    apply hraw.congr
    filter_upwards with z
    by_cases hsr : z.2 < z.1
    · simp only [heatLapTriangleIntegrand, if_pos hsr]
      rfl
    · simp only [heatLapTriangleIntegrand, if_neg hsr, integral_zero]
  have hsum : AEStronglyMeasurable
      (fun z : Real × Real =>
        ∑ i : Fin (Module.finrank Real V), if z.2 < z.1 then
          heatD2Convolution (z.1 - z.2) ((stdOrthonormalBasis Real V) i)
            ((stdOrthonormalBasis Real V) i) (f z.2) x else 0) (μ.prod μ) := by
    fun_prop
  apply hsum.congr
  filter_upwards with z
  by_cases hsr : z.2 < z.1
  · simp only [heatLapTriangle, heatLapSup, if_pos hsr]
  · simp only [heatLapTriangle, if_neg hsr, Finset.sum_const_zero]

end

variable [InnerProductSpace Real V] [FiniteDimensional Real V] [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F] in
private def heatLapTriangleMajor (alpha K : NNReal) (z : Real × Real) : Real :=
  if z.2 < z.1 then
    Module.finrank Real V * ((K : Real) * heatC2Holder (V := V) alpha) *
      holderHeatScale alpha (z.1 - z.2)
  else 0

section

variable [InnerProductSpace Real V] [FiniteDimensional Real V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

private theorem heatLapTriangleMajor_nonneg
    {alpha K : NNReal} (z : Real × Real) :
    0 ≤ heatLapTriangleMajor (V := V) alpha K z := by
  by_cases h : z.2 < z.1
  · simp only [heatLapTriangleMajor, if_pos h]
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (NNReal.coe_nonneg K)
          (heatC2Holder_nonneg (V := V) alpha)))
      (Real.rpow_nonneg (sub_pos.mpr h).le _)
  · simp only [heatLapTriangleMajor, if_neg h, le_refl]

private theorem heatLapTriangleMajor_aestronglyMeasurable
    {alpha K : NNReal} {t : Real} :
    AEStronglyMeasurable (heatLapTriangleMajor (V := V) alpha K)
      ((volume.restrict (Ioc (0 : Real) t)).prod
        (volume.restrict (Ioc (0 : Real) t))) := by
  let A : Set (Real × Real) := {z | z.2 < z.1}
  let g : Real × Real → Real := fun z =>
    Module.finrank Real V * ((K : Real) * heatC2Holder (V := V) alpha) *
      holderHeatScale alpha (z.1 - z.2)
  have hA : MeasurableSet A := by
    exact measurableSet_lt measurable_snd measurable_fst
  have hg : ContinuousOn g A := by
    unfold g holderHeatScale
    apply continuousOn_const.mul
    apply ContinuousOn.rpow_const
      (continuous_fst.sub continuous_snd).continuousOn
    intro z hz
    exact Or.inl (sub_ne_zero.mpr (ne_of_gt hz))
  have hind : AEStronglyMeasurable (A.indicator g)
      ((volume : Measure Real).prod volume) := by
    rw [aestronglyMeasurable_indicator_iff hA]
    exact hg.aestronglyMeasurable hA
  rw [Measure.prod_restrict]
  refine hind.restrict.congr ?_
  apply Filter.Eventually.of_forall
  intro z
  by_cases hz : z ∈ A
  · have hz' : z.2 < z.1 := by simpa only [A, Set.mem_ofPred_eq] using hz
    rw [Set.indicator_of_mem hz]
    simp only [heatLapTriangleMajor, if_pos hz', g]
  · have hz' : ¬ z.2 < z.1 := by simpa only [A, Set.mem_ofPred_eq] using hz
    rw [Set.indicator_of_notMem hz]
    simp only [heatLapTriangleMajor, if_neg hz']

private theorem integral_heatLapTriangleMajor_right
    {alpha K : NNReal} (halpha : 0 < alpha)
    {t r : Real} (hr : r ∈ Ioc (0 : Real) t) :
    (∫ s : Real, heatLapTriangleMajor (V := V) alpha K (r, s)
      ∂(volume.restrict (Ioc (0 : Real) t))) =
      Module.finrank Real V * ((K : Real) * heatC2Holder (V := V) alpha) *
        ((2 / (alpha : Real)) * r ^ ((alpha : Real) / 2)) := by
  have hsection :
      (∫ s : Real, heatLapTriangleMajor (V := V) alpha K (r, s)
        ∂(volume.restrict (Ioc (0 : Real) t))) =
        ∫ s : Real in 0..r,
          Module.finrank Real V * ((K : Real) * heatC2Holder (V := V) alpha) *
            holderHeatScale alpha (r - s) := by
    rw [intervalIntegral.integral_of_le hr.1.le]
    rw [← integral_indicator measurableSet_Ioc,
      ← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    have hne : ∀ᵐ s ∂(volume : Measure Real), s ≠ r := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hne] with s hsr0
    by_cases hs : s ∈ Ioc (0 : Real) t
    · by_cases hsr : s < r
      · have hsrMem : s ∈ Ioc (0 : Real) r := ⟨hs.1, hsr.le⟩
        simp [Set.indicator_of_mem hs, Set.indicator_of_mem hsrMem,
          heatLapTriangleMajor, hsr]
      · have hsrMem : s ∉ Ioc (0 : Real) r := fun h =>
          hsr (lt_of_le_of_ne h.2 hsr0)
        simp [Set.indicator, hs, hsrMem, heatLapTriangleMajor, hsr]
    · have hsrMem : s ∉ Ioc (0 : Real) r := by
        intro h
        exact hs ⟨h.1, h.2.trans hr.2⟩
      simp [Set.indicator, hs, hsrMem]
  rw [hsection, intervalIntegral.integral_const_mul,
    timeHolderHeatScale_int halpha]

private theorem heatLapTriangleMajor_integrable
    {alpha K : NNReal} (halpha : 0 < alpha)
    {t : Real} (ht : 0 < t) :
    Integrable (heatLapTriangleMajor (V := V) alpha K)
      ((volume.restrict (Ioc (0 : Real) t)).prod
        (volume.restrict (Ioc (0 : Real) t))) := by
  let μ : Measure Real := volume.restrict (Ioc (0 : Real) t)
  let A : Real :=
    Module.finrank Real V * ((K : Real) * heatC2Holder (V := V) alpha)
  have hmeas : AEStronglyMeasurable
      (heatLapTriangleMajor (V := V) alpha K) (μ.prod μ) := by
    simpa only [μ] using
      heatLapTriangleMajor_aestronglyMeasurable (V := V) (alpha := alpha)
        (K := K) (t := t)
  rw [integrable_prod_iff hmeas]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc,
      hmeas.prodMk_left] with r hr hrmeas
    have hraw : IntervalIntegrable
        (fun s : Real => A * holderHeatScale alpha (r - s)) volume 0 r :=
      (holderHeatScale_intble halpha).const_mul A
    have hOn : IntegrableOn
        (fun s : Real => A * holderHeatScale alpha (r - s))
        (Ioo (0 : Real) r) volume := by
      have hIoc : IntegrableOn
          (fun s : Real => A * holderHeatScale alpha (r - s))
          (Ioc (0 : Real) r) volume := by
        simpa only [intervalIntegrable_iff, uIoc_of_le hr.1.le] using hraw
      exact hIoc.mono_set Ioo_subset_Ioc_self
    have hglobal := hOn.integrable_indicator measurableSet_Ioo
    refine (hglobal.mono_measure Measure.restrict_le_self).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    by_cases hsr : s < r
    · have hmem : s ∈ Ioo (0 : Real) r := ⟨hs.1, hsr⟩
      simp [heatLapTriangleMajor, A, hsr, Set.indicator_of_mem hmem]
    · have hmem : s ∉ Ioo (0 : Real) r := fun h => hsr h.2
      simp [heatLapTriangleMajor, A, hsr, hmem]
  · have hrpowInt : IntervalIntegrable
        (fun r : Real => r ^ ((alpha : Real) / 2)) volume 0 t :=
      intervalIntegral.intervalIntegrable_rpow' (by
        have halphaReal : 0 < (alpha : Real) := by exact_mod_cast halpha
        linarith)
    have houter : Integrable
        (fun r : Real => A * ((2 / (alpha : Real)) *
          r ^ ((alpha : Real) / 2))) μ := by
      have hraw := hrpowInt.const_mul (A * (2 / (alpha : Real)))
      have hIoc : IntegrableOn
          (fun r : Real => A * ((2 / (alpha : Real)) *
            r ^ ((alpha : Real) / 2))) (Ioc (0 : Real) t) volume := by
        simpa only [intervalIntegrable_iff, uIoc_of_le ht.le,
          mul_assoc] using hraw
      change IntegrableOn
        (fun r : Real => A * ((2 / (alpha : Real)) *
          r ^ ((alpha : Real) / 2))) (Ioc (0 : Real) t) volume
      exact hIoc
    refine houter.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    calc
      A * ((2 / (alpha : Real)) * r ^ ((alpha : Real) / 2)) =
          ∫ s : Real, heatLapTriangleMajor (V := V) alpha K (r, s) ∂μ := by
        symm
        simpa only [μ, A] using
          integral_heatLapTriangleMajor_right (V := V) halpha hr
      _ = ∫ s : Real, ‖heatLapTriangleMajor (V := V) alpha K (r, s)‖ ∂μ := by
        apply integral_congr_ae
        filter_upwards with s
        rw [Real.norm_eq_abs,
          abs_of_nonneg (heatLapTriangleMajor_nonneg (V := V) (r, s))]

end

variable [InnerProductSpace Real V] [FiniteDimensional Real V] [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F] in
private theorem heatLapTriangle_integrable_of_aestronglyMeasurable
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t)
    (f : Real → BoundedContinuousFunction V F)
    (hf : ∀ s ∈ Icc (0 : Real) t, HolderWith K alpha (f s))
    (x : V)
    (hmeas : AEStronglyMeasurable (heatLapTriangle f x)
      ((volume.restrict (Ioc (0 : Real) t)).prod
        (volume.restrict (Ioc (0 : Real) t)))) :
    Integrable (heatLapTriangle f x)
      ((volume.restrict (Ioc (0 : Real) t)).prod
        (volume.restrict (Ioc (0 : Real) t))) := by
  apply (heatLapTriangleMajor_integrable (V := V) (K := K) halpha0 ht).mono' hmeas
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with z hz
  by_cases hsr : z.2 < z.1
  · have hraw := heatLapSup_norm_le_of_holder halpha0 halpha1
      (sub_pos.mpr hsr) (hf z.2 ⟨hz.2.1.le, hz.2.2⟩) x
    simpa only [heatLapTriangle, heatLapTriangleMajor, if_pos hsr] using
      hraw.trans_eq (by ring)
  · simp [heatLapTriangle, heatLapTriangleMajor, hsr]

variable [InnerProductSpace Real V] [FiniteDimensional Real V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace Real F] in
private theorem integral_heatLapTriangle_right
    {t r : Real} (hr : r ∈ Ioc (0 : Real) t)
    (f : Real → BoundedContinuousFunction V F) (x : V) :
    (∫ s : Real, heatLapTriangle f x (r, s)
      ∂(volume.restrict (Ioc (0 : Real) t))) = heatLapPotential r f x := by
  unfold heatLapPotential
  rw [intervalIntegral.integral_of_le hr.1.le]
  rw [← integral_indicator measurableSet_Ioc,
    ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  have hne : ∀ᵐ s ∂(volume : Measure Real), s ≠ r := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hne] with s hne
  by_cases hs : s ∈ Ioc (0 : Real) t
  · by_cases hsr : s < r
    · have hsrMem : s ∈ Ioc (0 : Real) r := ⟨hs.1, hsr.le⟩
      simp [Set.indicator_of_mem hs, Set.indicator_of_mem hsrMem,
        heatLapTriangle, hsr]
    · have hsrMem : s ∉ Ioc (0 : Real) r := fun h =>
        hsr (lt_of_le_of_ne h.2 hne)
      simp [Set.indicator, hs, hsrMem, heatLapTriangle, hsr]
  · have hsrMem : s ∉ Ioc (0 : Real) r := by
      intro h
      exact hs ⟨h.1, h.2.trans hr.2⟩
    simp [Set.indicator, hs, hsrMem]

section

variable [InnerProductSpace Real V] [FiniteDimensional Real V] [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

private theorem integral_heatLapTriangle_left
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t s : Real} (hs : s ∈ Ioo (0 : Real) t)
    (f : Real → BoundedContinuousFunction V F)
    (hf : ∀ r ∈ Icc (0 : Real) t, HolderWith K alpha (f r)) (x : V) :
    (∫ r : Real, heatLapTriangle f x (r, s)
      ∂(volume.restrict (Ioc (0 : Real) t))) =
      heatSup (t - s) (f s) x - f s x := by
  have hst : s ≤ t := hs.2.le
  have hsection :
      (∫ r : Real, heatLapTriangle f x (r, s)
        ∂(volume.restrict (Ioc (0 : Real) t))) =
        ∫ r : Real in s..t, heatLapSup (r - s) (f s) x := by
    rw [intervalIntegral.integral_of_le hst]
    rw [← integral_indicator measurableSet_Ioc,
      ← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards with r
    by_cases hr : r ∈ Ioc (0 : Real) t
    · by_cases hsr : s < r
      · have hrt : r ∈ Ioc s t := ⟨hsr, hr.2⟩
        simp [Set.indicator_of_mem hr, Set.indicator_of_mem hrt,
          heatLapTriangle, hsr]
      · have hrt : r ∉ Ioc s t := fun h => hsr h.1
        simp [Set.indicator, hr, hrt, heatLapTriangle, hsr]
    · have hrt : r ∉ Ioc s t := by
        intro h
        exact hr ⟨hs.1.trans h.1, h.2⟩
      simp [Set.indicator, hr, hrt]
  rw [hsection]
  change (∫ r : Real in s..t,
    (fun q : Real => heatLapSup q (f s) x) (r - s)) = _
  rw [intervalIntegral.integral_comp_sub_right
    (fun q : Real => heatLapSup q (f s) x) s]
  simp only [sub_self]
  exact heatSup_primitive_of_holder halpha0 halpha1 (sub_pos.mpr hs.2)
    (f s) (hf s ⟨hs.1.le, hs.2.le⟩) x

theorem heatDuhamel_eq_integral_add_heatLapPotential
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t)
    (f : Real → BoundedContinuousFunction V F)
    (hf : ∀ s ∈ Icc (0 : Real) t, HolderWith K alpha (f s))
    (x : V)
    (hftime : IntervalIntegrable (fun s : Real => f s x) volume 0 t)
    (htriangle : Integrable (heatLapTriangle f x)
      ((volume.restrict (Ioc (0 : Real) t)).prod
        (volume.restrict (Ioc (0 : Real) t)))) :
    heatDuhamel t f x =
      ∫ r : Real in 0..t, f r x + heatLapPotential r f x := by
  let μ : Measure Real := volume.restrict (Ioc (0 : Real) t)
  have hlapMu : Integrable (fun r : Real => heatLapPotential r f x) μ := by
    refine htriangle.integral_prod_left.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact integral_heatLapTriangle_right hr f x
  have hdiffMu : Integrable
      (fun s : Real => heatSup (t - s) (f s) x - f s x) μ := by
    refine htriangle.integral_prod_right.congr ?_
    have hne : ∀ᵐ s ∂(volume : Measure Real), s ≠ t := by
      simp [ae_iff, measure_singleton]
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (s := Ioc (0 : Real) t) hne] with s hs hst
    exact integral_heatLapTriangle_left halpha0 halpha1
      ⟨hs.1, lt_of_le_of_ne hs.2 hst⟩ f hf x
  have hlapInt : IntervalIntegrable
      (fun r : Real => heatLapPotential r f x) volume 0 t := by
    rw [intervalIntegrable_iff, uIoc_of_le ht.le]
    exact hlapMu
  have hdiffInt : IntervalIntegrable
      (fun s : Real => heatSup (t - s) (f s) x - f s x) volume 0 t := by
    rw [intervalIntegrable_iff, uIoc_of_le ht.le]
    exact hdiffMu
  have hlapEqMu :
      (∫ r : Real, heatLapPotential r f x ∂μ) =
        ∫ s : Real, heatSup (t - s) (f s) x - f s x ∂μ := by
    calc
      (∫ r : Real, heatLapPotential r f x ∂μ) =
          ∫ r : Real, (∫ s : Real, heatLapTriangle f x (r, s) ∂μ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        exact (integral_heatLapTriangle_right hr f x).symm
      _ = ∫ s : Real, (∫ r : Real, heatLapTriangle f x (r, s) ∂μ) ∂μ := by
        exact integral_integral_swap htriangle
      _ = ∫ s : Real, heatSup (t - s) (f s) x - f s x ∂μ := by
        apply integral_congr_ae
        have hne : ∀ᵐ s ∂(volume : Measure Real), s ≠ t := by
          simp [ae_iff, measure_singleton]
        filter_upwards [ae_restrict_mem measurableSet_Ioc,
          ae_restrict_of_ae (s := Ioc (0 : Real) t) hne] with s hs hst
        exact integral_heatLapTriangle_left halpha0 halpha1
          ⟨hs.1, lt_of_le_of_ne hs.2 hst⟩ f hf x
  have hlapEq :
      (∫ r : Real in 0..t, heatLapPotential r f x) =
        ∫ s : Real in 0..t, heatSup (t - s) (f s) x - f s x := by
    rw [intervalIntegral.integral_of_le ht.le,
      intervalIntegral.integral_of_le ht.le]
    exact hlapEqMu
  have hheatInt : IntervalIntegrable
      (fun s : Real => heatSup (t - s) (f s) x) volume 0 t := by
    have hadd := hdiffInt.add hftime
    have heq : (fun s : Real =>
        (heatSup (t - s) (f s) x - f s x) + f s x) =
        fun s : Real => heatSup (t - s) (f s) x := by
      funext s
      abel
    rw [heq] at hadd
    exact hadd
  unfold heatDuhamel
  calc
    (∫ s : Real in 0..t, heatSup (t - s) (f s) x) =
        (∫ s : Real in 0..t, f s x) +
          ∫ s : Real in 0..t, heatSup (t - s) (f s) x - f s x := by
      rw [intervalIntegral.integral_sub hheatInt hftime]
      abel
    _ = (∫ s : Real in 0..t, f s x) +
        ∫ r : Real in 0..t, heatLapPotential r f x := by rw [hlapEq]
    _ = ∫ r : Real in 0..t, f r x + heatLapPotential r f x :=
      (intervalIntegral.integral_add hftime hlapInt).symm

theorem heatDuhamelTimeDerivative_continuousAt
    {alpha K Csource : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {S t : Real} (ht : t ∈ Ioo (0 : Real) S)
    (f : Real → BoundedContinuousFunction V F)
    (hf : ∀ r ∈ Icc (0 : Real) S, HolderWith K alpha (f r))
    (hsource : HolderWith Csource alpha
      ((parabolicCylinder (Ioc (0 : Real) S) Set.univ).domRestrict
        (fun p => f p.time p.space)))
    (hmeas2 : ∀ q ∈ Ioc (0 : Real) S, ∀ z : V,
      AEStronglyMeasurable
        (fun s : Real => heatSupHessian (q - s) (f s) z)
        (volume.restrict (uIoc (0 : Real) q)))
    (x : V) :
    ContinuousAt
      (fun q : Real => heatDuhamelTimeDerivativeField (fun r z => f r z)
        (parabolicPoint q x)) t := by
  let Q : Set (ParabolicPoint V) :=
    parabolicCylinder (Ioc (0 : Real) S) Set.univ
  have hcand := heatDuhamelTimeDerivativeField_holderWith_restrict_of_holder
    halpha0 halpha1 (fun r z => f r z) hf hsource
      (fun q hq z i => heatD2Convolution_time_aestronglyMeasurable hq.1 f
        (hmeas2 q hq) ((stdOrthonormalBasis Real V) i)
        ((stdOrthonormalBasis Real V) i) z)
  have hcandCont : Continuous
      (Q.domRestrict (heatDuhamelTimeDerivativeField (fun r z => f r z))) :=
    hcand.continuous halpha0
  let phi : Ioc (0 : Real) S → Q := fun q =>
    ⟨parabolicPoint q.1 x, ⟨q.2, Set.mem_univ x⟩⟩
  have hphi : Continuous phi := by
    unfold phi parabolicPoint
    fun_prop
  have hcomp : Continuous (fun q : Ioc (0 : Real) S =>
      heatDuhamelTimeDerivativeField (fun r z => f r z)
        (parabolicPoint q.1 x)) := by
    exact (hcandCont.comp hphi).congr fun _ => rfl
  have hOn : ContinuousOn
      (fun q : Real => heatDuhamelTimeDerivativeField (fun r z => f r z)
        (parabolicPoint q x)) (Ioc (0 : Real) S) :=
    continuousOn_iff_continuous_domRestrict.mpr hcomp
  exact (hOn t ⟨ht.1, ht.2.le⟩).continuousAt (Ioc_mem_nhds ht.1 ht.2)

theorem heatDuhamel_time_of_integrable_triangle
    {alpha K Csource : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {S t : Real} (ht : t ∈ Ioo (0 : Real) S)
    (f : Real → BoundedContinuousFunction V F)
    (hf : ∀ r ∈ Icc (0 : Real) S, HolderWith K alpha (f r))
    (hsource : HolderWith Csource alpha
      ((parabolicCylinder (Ioc (0 : Real) S) Set.univ).domRestrict
        (fun p => f p.time p.space)))
    (hmeas2 : ∀ q ∈ Ioc (0 : Real) S, ∀ z : V,
      AEStronglyMeasurable
        (fun s : Real => heatSupHessian (q - s) (f s) z)
        (volume.restrict (uIoc (0 : Real) q)))
    (hftime : ∀ q ∈ Ioc (0 : Real) S, ∀ z : V,
      IntervalIntegrable (fun s : Real => f s z) volume 0 q)
    (htriangle : ∀ q ∈ Ioc (0 : Real) S, ∀ z : V,
      Integrable (heatLapTriangle f z)
        ((volume.restrict (Ioc (0 : Real) q)).prod
          (volume.restrict (Ioc (0 : Real) q))))
    (x : V) :
    HasDerivAt (fun q : Real => heatDuhamel q f x)
      (heatDuhamelTimeDerivativeField (fun r z => f r z)
        (parabolicPoint t x)) t := by
  let g : Real → F := fun q =>
    heatDuhamelTimeDerivativeField (fun r z => f r z) (parabolicPoint q x)
  have hg : ContinuousAt g t := by
    simpa only [g] using heatDuhamelTimeDerivative_continuousAt
      halpha0 halpha1 ht f hf hsource hmeas2 x
  have heq : ∀ q ∈ Ioc (0 : Real) S,
      heatDuhamel q f x = ∫ r : Real in 0..q, g r := by
    intro q hq
    have hfq : ∀ r ∈ Icc (0 : Real) q, HolderWith K alpha (f r) := by
      intro r hr
      exact hf r ⟨hr.1, hr.2.trans hq.2⟩
    rw [heatDuhamel_eq_integral_add_heatLapPotential halpha0 halpha1.le hq.1
      f hfq x (hftime q hq x) (htriangle q hq x)]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with r
    intro hr
    rw [uIoc_of_le hq.1.le] at hr
    have hrpos : 0 < r := hr.1
    have hrS : r ∈ Ioc (0 : Real) S := ⟨hrpos, hr.2.trans hq.2⟩
    rw [heatLapPotential_eq_heatLapDuhamel halpha0 halpha1.le hrpos f
      (fun s hs => hf s ⟨hs.1, hs.2.trans hrS.2⟩) (hmeas2 r hrS) x]
    rfl
  have hgInt : IntervalIntegrable g volume 0 t := by
    let μ : Measure Real := volume.restrict (Ioc (0 : Real) t)
    have htS : t ∈ Ioc (0 : Real) S := ⟨ht.1, ht.2.le⟩
    have hlapMu : Integrable (fun r : Real => heatLapPotential r f x) μ := by
      refine (htriangle t htS x).integral_prod_left.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact integral_heatLapTriangle_right hr f x
    have hlapInt : IntervalIntegrable
        (fun r : Real => heatLapPotential r f x) volume 0 t := by
      rw [intervalIntegrable_iff, uIoc_of_le ht.1.le]
      exact hlapMu
    have hsumInt := (hftime t htS x).add hlapInt
    refine hsumInt.congr ?_
    intro r hr
    rw [uIoc_of_le ht.1.le] at hr
    have hrS : r ∈ Ioc (0 : Real) S := ⟨hr.1, hr.2.trans ht.2.le⟩
    change f r x + heatLapPotential r f x = f r x + heatLapDuhamel r (fun s z => f s z) x
    rw [heatLapPotential_eq_heatLapDuhamel halpha0 halpha1.le hr.1 f
      (fun s hs => hf s ⟨hs.1, hs.2.trans hrS.2⟩) (hmeas2 r hrS) x]
  have hgMeas : StronglyMeasurableAtFilter g (nhds t) volume := by
    apply ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo
      (fun q hq => ?_) t ht
    simpa only [g] using heatDuhamelTimeDerivative_continuousAt
      halpha0 halpha1 hq f hf hsource hmeas2 x
  have hprim : HasDerivAt (fun q : Real => ∫ r : Real in 0..q, g r) (g t) t :=
    intervalIntegral.integral_hasDerivAt_right hgInt hgMeas hg
  apply hprim.congr_of_eventuallyEq
  filter_upwards [Ioc_mem_nhds ht.1 ht.2] with q hq
  exact heq q hq

theorem heatDuhamel_time_of_intervalIntegrable
    {alpha K Csource : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {S t : Real} (ht : t ∈ Ioo (0 : Real) S)
    (f : Real → BoundedContinuousFunction V F)
    (hf : ∀ r ∈ Icc (0 : Real) S, HolderWith K alpha (f r))
    (hsource : HolderWith Csource alpha
      ((parabolicCylinder (Ioc (0 : Real) S) Set.univ).domRestrict
        (fun p => f p.time p.space)))
    (hmeas2 : ∀ q ∈ Ioc (0 : Real) S, ∀ z : V,
      AEStronglyMeasurable
        (fun s : Real => heatSupHessian (q - s) (f s) z)
        (volume.restrict (uIoc (0 : Real) q)))
    (hftime : ∀ q ∈ Ioc (0 : Real) S, ∀ z : V,
      IntervalIntegrable (fun s : Real => f s z) volume 0 q)
    (x : V) :
    HasDerivAt (fun q : Real => heatDuhamel q f x)
      (heatDuhamelTimeDerivativeField (fun r z => f r z)
        (parabolicPoint t x)) t := by
  apply heatDuhamel_time_of_integrable_triangle halpha0 halpha1 ht f hf hsource
    hmeas2 hftime
  · intro q hq z
    exact heatLapTriangle_integrable_of_aestronglyMeasurable
      halpha0 halpha1.le hq.1 f
        (fun s hs => hf s ⟨hs.1, hs.2.trans hq.2⟩) z
        (heatLapTriangle_aestronglyMeasurable_of_holder
          halpha0 hq.2 f hsource z)

end

variable [NormedAddCommGroup F] in
private theorem heatSource_intervalIntegrable_of_holder
    {alpha Csource : NNReal} (halpha0 : 0 < alpha)
    {S t : Real} (ht : t ∈ Ioc (0 : Real) S)
    (f : Real → BoundedContinuousFunction V F)
    (hsource : HolderWith Csource alpha
      ((parabolicCylinder (Ioc (0 : Real) S) Set.univ).domRestrict
        (fun p => f p.time p.space)))
    (x : V) : IntervalIntegrable (fun r : Real => f r x) volume 0 t := by
  let Q : Set (ParabolicPoint V) :=
    parabolicCylinder (Ioc (0 : Real) S) Set.univ
  let phi : Ioc (0 : Real) S → Q := fun q =>
    ⟨parabolicPoint q.1 x, ⟨q.2, Set.mem_univ x⟩⟩
  have hphi : Continuous phi := by
    unfold phi parabolicPoint
    fun_prop
  have hcomp : Continuous (fun q : Ioc (0 : Real) S => f q.1 x) := by
    exact ((hsource.continuous halpha0).comp hphi).congr fun _ => rfl
  have hOn : ContinuousOn (fun r : Real => f r x) (Ioc (0 : Real) S) :=
    continuousOn_iff_continuous_domRestrict.mpr hcomp
  have hmeas : AEStronglyMeasurable (fun r : Real => f r x)
      (volume.restrict (Ioc (0 : Real) t)) :=
    (hOn.mono fun r hr => ⟨hr.1, hr.2.trans ht.2⟩).aestronglyMeasurable
      measurableSet_Ioc
  have hint : IntegrableOn (fun r : Real => f r x) (Ioc (0 : Real) t) volume := by
    apply IntegrableOn.of_bound measure_Ioc_lt_top hmeas
      (‖f t x‖ + (Csource : Real) * t ^ ((alpha : Real) / 2))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hdist := parabolicHolder_time_dist_le hsource
      (t := r) (s := t) (x := x)
      ⟨⟨hr.1, hr.2.trans ht.2⟩, Set.mem_univ x⟩
      ⟨ht, Set.mem_univ x⟩
    have habs : |r - t| ≤ t := by
      rw [abs_of_nonpos (sub_nonpos.mpr hr.2)]
      linarith [hr.1]
    have hpow : |r - t| ^ ((alpha : Real) / 2) ≤
        t ^ ((alpha : Real) / 2) :=
      Real.rpow_le_rpow (abs_nonneg _) habs (by positivity)
    calc
      ‖f r x‖ ≤ ‖f t x‖ + ‖f r x - f t x‖ :=
        norm_le_norm_add_norm_sub' _ _
      _ = ‖f t x‖ + dist (f r x) (f t x) := by rw [dist_eq_norm]
      _ ≤ ‖f t x‖ + (Csource : Real) *
          |r - t| ^ ((alpha : Real) / 2) := by
        simpa only [parabolicPoint_time, parabolicPoint_space] using
          add_le_add (le_refl ‖f t x‖) hdist
      _ ≤ ‖f t x‖ + (Csource : Real) *
          t ^ ((alpha : Real) / 2) := by
        exact add_le_add (le_refl ‖f t x‖)
          (mul_le_mul_of_nonneg_left hpow (NNReal.coe_nonneg Csource))
  simpa only [intervalIntegrable_iff, uIoc_of_le ht.1.le] using hint

section

variable [InnerProductSpace Real V] [FiniteDimensional Real V] [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

theorem heatDuhamel_time
    {alpha K Csource : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {S t : Real} (ht : t ∈ Ioo (0 : Real) S)
    (f : Real → BoundedContinuousFunction V F)
    (hf : ∀ r ∈ Icc (0 : Real) S, HolderWith K alpha (f r))
    (hsource : HolderWith Csource alpha
      ((parabolicCylinder (Ioc (0 : Real) S) Set.univ).domRestrict
        (fun p => f p.time p.space)))
    (hmeas2 : ∀ q ∈ Ioc (0 : Real) S, ∀ z : V,
      AEStronglyMeasurable
        (fun s : Real => heatSupHessian (q - s) (f s) z)
        (volume.restrict (uIoc (0 : Real) q)))
    (x : V) :
    HasDerivAt (fun q : Real => heatDuhamel q f x)
      (heatDuhamelTimeDerivativeField (fun r z => f r z)
        (parabolicPoint t x)) t := by
  apply heatDuhamel_time_of_intervalIntegrable halpha0 halpha1 ht f hf hsource
    hmeas2
  intro q hq z
  exact heatSource_intervalIntegrable_of_holder halpha0 hq f hsource z

theorem eParabolicC2HolderGaugeOn_heatDuhamel_le_of_lower_jets
    {alpha K B Csource C0 C1 : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {S T : Real} (hT : 0 ≤ T) (hTS : T < S)
    (f : Real → BoundedContinuousFunction V F)
    (hzero : ∀ p ∈ parabolicCylinder (Ioc (0 : Real) T) Set.univ,
      ‖parabolicSpatialJet 0 (fun t x => heatDuhamel t f x) p‖ ≤ C0)
    (hone : ∀ p ∈ parabolicCylinder (Ioc (0 : Real) T) Set.univ,
      ‖parabolicSpatialJet 1 (fun t x => heatDuhamel t f x) p‖ ≤ C1)
    (hbound : ∀ r ∈ Icc (0 : Real) S, ‖f r‖ ≤ B)
    (hf : ∀ r ∈ Icc (0 : Real) S, HolderWith K alpha (f r))
    (hsource : HolderWith Csource alpha
      ((parabolicCylinder (Ioc (0 : Real) S) Set.univ).domRestrict
        (fun p => f p.time p.space)))
    (hmeas0 : ∀ t ∈ Ioc (0 : Real) S, ∀ z : V,
      AEStronglyMeasurable
        (fun s : Real => heatSup (t - s) (f s) z)
        (volume.restrict (uIoc (0 : Real) t)))
    (hmeas1 : ∀ t ∈ Ioc (0 : Real) S, ∀ z : V,
      AEStronglyMeasurable
        (fun s : Real => heatSupGradient (t - s) (f s) z)
        (volume.restrict (uIoc (0 : Real) t)))
    (hmeas2 : ∀ t ∈ Ioc (0 : Real) S, ∀ z : V,
      AEStronglyMeasurable
        (fun s : Real => heatSupHessian (t - s) (f s) z)
        (volume.restrict (uIoc (0 : Real) t))) :
    eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Ioc (0 : Real) T) Set.univ)
      (fun t x => heatDuhamel t f x) ≤
      heatPotentialC2HolderGaugeConst (V := V)
        alpha K B Csource C0 C1 T := by
  apply eParabolicC2HolderGaugeOn_heatDuhamel_le_of_lower_jets_of_time_realization
    halpha0 halpha1 hT f hzero hone
  · intro r hr
    exact hbound r ⟨hr.1, hr.2.trans hTS.le⟩
  · intro r hr
    exact hf r ⟨hr.1, hr.2.trans hTS.le⟩
  · apply HolderWith.restrict_iff.mpr
    exact (HolderWith.restrict_iff.mp hsource).mono fun p hp =>
      ⟨⟨hp.1.1, hp.1.2.trans hTS.le⟩, hp.2⟩
  · intro p hp
    exact heatDuhamel_time halpha0 halpha1
      ⟨hp.1.1, lt_of_le_of_lt hp.1.2 hTS⟩ f hf hsource
        hmeas2 p.space
  · intro t ht z
    exact hmeas0 t ⟨ht.1, ht.2.trans hTS.le⟩ z
  · intro t ht z
    exact hmeas1 t ⟨ht.1, ht.2.trans hTS.le⟩ z
  · intro t ht z
    exact hmeas2 t ⟨ht.1, ht.2.trans hTS.le⟩ z

end

end HeatEquation

end
