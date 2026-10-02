-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Parabolic/Euclidean/HeatKernel/Schauder/SecondDerivative.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Parabolic.Euclidean.HeatKernel.Duhamel.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

-- and its private helpers occur in public declarations.

noncomputable section

open MeasureTheory Real Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace HeatEquation

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

def baseD2Holder (alpha : NNReal) (x : V) : Real :=
  ‖x‖ ^ (alpha : Real) * baseD2Maj x

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem baseD2Holder_nonneg (alpha : NNReal) (x : V) :
    0 ≤ baseD2Holder alpha x :=
  mul_nonneg (Real.rpow_nonneg (norm_nonneg x) _) (baseD2Maj_nonneg x)

theorem baseD2Holder_int {alpha : NNReal} (halpha : alpha ≤ 1) :
    Integrable (baseD2Holder alpha : V → Real) := by
  have hmajor : Integrable (fun x : V => (1 + ‖x‖) * baseD2Maj x) := by
    have hfirst : Integrable (fun x : V => ‖x‖ * baseD2Maj x) := by
      have h3 := (gaussMoment_int (V := V) 3
        (by positivity : (0 : Real) < (4 : Real)⁻¹)).const_mul
          ((4 : Real)⁻¹ * (baseHeatMass V)⁻¹)
      have h1 := (gaussMoment_int (V := V) 1
        (by positivity : (0 : Real) < (4 : Real)⁻¹)).const_mul
          ((2 : Real)⁻¹ * (baseHeatMass V)⁻¹)
      have heq : (fun x : V => ‖x‖ * baseD2Maj x) = fun x : V =>
          ((4 : Real)⁻¹ * (baseHeatMass V)⁻¹) *
              (‖x‖ ^ 3 * Real.exp (-(4 : Real)⁻¹ * ‖x‖ ^ 2)) +
            ((2 : Real)⁻¹ * (baseHeatMass V)⁻¹) *
              (‖x‖ ^ 1 * Real.exp (-(4 : Real)⁻¹ * ‖x‖ ^ 2)) := by
        funext x
        unfold baseD2Maj baseHeat
        ring
      rw [heq]
      exact h3.add h1
    have h := (baseD2Maj_int (V := V)).add hfirst
    have heq : (fun x : V => (1 + ‖x‖) * baseD2Maj x) =
        fun x : V => baseD2Maj x + ‖x‖ * baseD2Maj x := by
      funext x
      ring
    rw [heq]
    exact h
  refine hmajor.mono' ?_ ?_
  · have hpow : Continuous (fun x : V => ‖x‖ ^ (alpha : Real)) :=
      continuous_norm.rpow_const (fun _ => Or.inr alpha.coe_nonneg)
    have hmaj : Continuous (baseD2Maj : V → Real) := by
      unfold baseD2Maj baseHeat baseHeatMass
      fun_prop
    exact (hpow.mul hmaj).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (baseD2Holder_nonneg alpha x)]
  have hrpow : ‖x‖ ^ (alpha : Real) ≤ 1 + ‖x‖ := by
    by_cases hx : ‖x‖ ≤ 1
    · exact (Real.rpow_le_one (norm_nonneg x) hx alpha.coe_nonneg).trans
        (le_add_of_nonneg_right (norm_nonneg x))
    · have hx' : 1 ≤ ‖x‖ := le_of_not_ge hx
      exact (Real.rpow_le_self_of_one_le hx' (by exact_mod_cast halpha)).trans
        (le_add_of_nonneg_left zero_le_one)
  exact mul_le_mul_of_nonneg_right hrpow (baseD2Maj_nonneg x)

def heatC2Holder (alpha : NNReal) : Real :=
  ∫ x : V, baseD2Holder alpha x

omit [Nontrivial V] in
theorem heatC2Holder_nonneg (alpha : NNReal) : 0 ≤ heatC2Holder (V := V) alpha :=
  integral_nonneg (baseD2Holder_nonneg alpha)

def heatD2Holder (alpha : NNReal) (t : Real) (x : V) : Real :=
  ((heatScale t) ^ Module.finrank Real V)⁻¹ * t⁻¹ *
    (heatScale t) ^ (alpha : Real) *
      baseD2Holder alpha ((heatScale t)⁻¹ • x)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
omit [FiniteDimensional ℝ V] in
theorem heatD2Holder_eq (alpha : NNReal) {t : Real} (ht : 0 < t) (x : V) :
    heatD2Holder alpha t x = ‖x‖ ^ (alpha : Real) * heatD2Maj t x := by
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
  have hsquare : heatScale t ^ 2 = t := by
    simpa [heatScale] using Real.sq_sqrt ht.le
  have hscale : t⁻¹ = (heatScale t)⁻¹ * (heatScale t)⁻¹ := by
    field_simp [hr.ne', ht.ne']
    nlinarith [hsquare]
  unfold heatD2Holder heatD2Maj baseD2Holder
  rw [hrpow, hscale]
  ring

theorem heatD2Holder_int {alpha : NNReal} (halpha : alpha ≤ 1)
    {t : Real} (ht : 0 < t) :
    Integrable (heatD2Holder (V := V) alpha t) := by
  unfold heatD2Holder
  exact (baseD2Holder_int (V := V) halpha).comp_smul
    (inv_ne_zero (heatScale_pos ht).ne') |>.const_mul _

omit [Nontrivial V] in
theorem integral_heatD2Holder (alpha : NNReal) {t : Real} (ht : 0 < t) :
    ∫ x : V, heatD2Holder alpha t x =
      t⁻¹ * (heatScale t) ^ (alpha : Real) * heatC2Holder (V := V) alpha := by
  have hr : 0 < heatScale t := heatScale_pos ht
  unfold heatD2Holder heatC2Holder
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg
      (volume : Measure V) (baseD2Holder alpha) hr.le]
  simp only [smul_eq_mul]
  field_simp [hr.ne']

def holderHeatScale (alpha : NNReal) (t : Real) : Real :=
  t ^ ((alpha : Real) / 2 - 1)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem holderHeatScale_eq (alpha : NNReal) {t : Real} (ht : 0 < t) :
    t⁻¹ * (heatScale t) ^ (alpha : Real) = holderHeatScale alpha t := by
  unfold holderHeatScale heatScale
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one,
    ← Real.rpow_mul ht.le, ← Real.rpow_add ht]
  congr 1
  ring

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatD2_holder_bound (alpha : NNReal) {t : Real} (ht : 0 < t)
    (v w x : V) :
    ‖heatD2 t v w x‖ * ‖x‖ ^ (alpha : Real) ≤
      ‖v‖ * ‖w‖ * heatD2Holder alpha t x := by
  rw [heatD2Holder_eq alpha ht]
  calc
    ‖heatD2 t v w x‖ * ‖x‖ ^ (alpha : Real) ≤
        (‖v‖ * ‖w‖ * heatD2Maj t x) * ‖x‖ ^ (alpha : Real) :=
      mul_le_mul_of_nonneg_right (heatD2_bound ht v w x)
        (Real.rpow_nonneg (norm_nonneg x) _)
    _ = ‖v‖ * ‖w‖ * (‖x‖ ^ (alpha : Real) * heatD2Maj t x) := by
      ring

section Cancellation

variable {F : Type*}
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

omit [InnerProductSpace Real V] [FiniteDimensional Real V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedSpace Real F] [CompleteSpace F] in
private theorem holder_bound {alpha K : NNReal} {f : V → F}
    (hf : HolderWith K alpha f) (x y : V) :
    ‖f (x - y) - f x‖ ≤ (K : Real) * ‖y‖ ^ (alpha : Real) := by
  have hxy : dist (x - y) x = ‖y‖ := by
    rw [dist_eq_norm]
    have : (x - y) - x = -y := by abel
    rw [this, norm_neg]
  have h := hf.dist_le (x - y) x
  rw [dist_eq_norm, hxy] at h
  exact h

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] [CompleteSpace F] in
private theorem cancel_bound_of_holder {alpha K : NNReal} {t : Real} (ht : 0 < t)
    {f : V → F} (hf : HolderWith K alpha f) (v w x y : V) :
    ‖heatD2 t v w y • (f (x - y) - f x)‖ ≤
      (‖v‖ * ‖w‖ * (K : Real)) * heatD2Holder alpha t y := by
  calc
    ‖heatD2 t v w y • (f (x - y) - f x)‖ =
        ‖heatD2 t v w y‖ * ‖f (x - y) - f x‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖heatD2 t v w y‖ * ((K : Real) * ‖y‖ ^ (alpha : Real)) :=
      mul_le_mul_of_nonneg_left (holder_bound hf x y) (norm_nonneg _)
    _ ≤ (‖v‖ * ‖w‖ * heatD2Maj t y) *
        ((K : Real) * ‖y‖ ^ (alpha : Real)) := by
      gcongr
      exact heatD2_bound ht v w y
    _ = (‖v‖ * ‖w‖ * (K : Real)) * heatD2Holder alpha t y := by
      rw [heatD2Holder_eq alpha ht]
      ring

omit [CompleteSpace F] in
theorem heatD2Cancel_int_of_holder {alpha K : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t) {f : V → F} (hf : HolderWith K alpha f)
    (v w x : V) :
    Integrable (fun y : V => heatD2 t v w y • (f (x - y) - f x)) := by
  have hfcont : Continuous f := hf.continuous halpha0
  have hmajor : Integrable
      (fun y : V => (‖v‖ * ‖w‖ * (K : Real)) * heatD2Holder alpha t y) :=
    (heatD2Holder_int (V := V) halpha1 ht).const_mul _
  refine hmajor.mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    unfold heatD2 baseD2 baseHeat baseHeatMass heatScale
    fun_prop
  filter_upwards with y
  exact cancel_bound_of_holder ht hf v w x y

omit [CompleteSpace F] in
theorem heatD2Convolution_int_of_holder {alpha K : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t) {f : V → F} (hf : HolderWith K alpha f)
    (v w x : V) :
    Integrable (fun y : V => heatD2 t v w y • f (x - y)) := by
  have hcancel := heatD2Cancel_int_of_holder halpha0 halpha1 ht hf v w x
  have hconst := (heatD2_int ht v w).smul_const (f x)
  refine (hcancel.add hconst).congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [Pi.add_apply, smul_sub, sub_add_cancel]

theorem heatD2Convolution_eq_cancel_of_holder {alpha K : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t) {f : V → F} (hf : HolderWith K alpha f)
    (v w x : V) :
    heatD2Convolution t v w f x = heatD2Cancel t v w f x := by
  have hcancel := heatD2Cancel_int_of_holder halpha0 halpha1 ht hf v w x
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
theorem heatD2Cancel_norm_of_holder {alpha K : NNReal}
    (halpha : alpha ≤ 1) {t : Real} (ht : 0 < t)
    {f : V → F} (hf : HolderWith K alpha f) (v w x : V) :
    ‖heatD2Cancel t v w f x‖ ≤
      ‖v‖ * ‖w‖ * (K : Real) * holderHeatScale alpha t *
        heatC2Holder (V := V) alpha := by
  unfold heatD2Cancel
  calc
    ‖∫ y : V, heatD2 t v w y • (f (x - y) - f x)‖ ≤
        ∫ y : V, (‖v‖ * ‖w‖ * (K : Real)) * heatD2Holder alpha t y :=
      norm_integral_le_of_norm_le
        ((heatD2Holder_int (V := V) halpha ht).const_mul _)
        (Filter.Eventually.of_forall fun y => cancel_bound_of_holder ht hf v w x y)
    _ = (‖v‖ * ‖w‖ * (K : Real)) *
        (t⁻¹ * (heatScale t) ^ (alpha : Real) * heatC2Holder (V := V) alpha) := by
      rw [integral_const_mul, integral_heatD2Holder alpha ht]
    _ = ‖v‖ * ‖w‖ * (K : Real) * holderHeatScale alpha t *
        heatC2Holder (V := V) alpha := by
      rw [holderHeatScale_eq alpha ht]
      ring

end Cancellation

theorem holderHeatScale_intble {alpha : NNReal} (halpha : 0 < alpha)
    {t : Real} :
    IntervalIntegrable (fun s : Real => holderHeatScale alpha (t - s)) volume 0 t := by
  have hpow : IntervalIntegrable
      (fun u : Real => u ^ ((alpha : Real) / 2 - 1)) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by
      have : 0 < (alpha : Real) := by exact_mod_cast halpha
      linarith)
  have href := hpow.symm.comp_sub_left t
  simpa only [holderHeatScale, sub_self, sub_zero] using href

theorem timeHolderHeatScale_int {alpha : NNReal} (halpha : 0 < alpha)
    {t : Real} :
    ∫ s : Real in 0..t, holderHeatScale alpha (t - s) =
      (2 / (alpha : Real)) * t ^ ((alpha : Real) / 2) := by
  unfold holderHeatScale
  rw [intervalIntegral.integral_comp_sub_left
    (fun u : Real => u ^ ((alpha : Real) / 2 - 1)) t]
  simp only [sub_self, sub_zero]
  rw [integral_rpow (Or.inl (by
    have : 0 < (alpha : Real) := by exact_mod_cast halpha
    linarith))]
  have halpha_real : (alpha : Real) ≠ 0 := by exact_mod_cast halpha.ne'
  have hexp : (alpha : Real) / 2 - 1 + 1 = (alpha : Real) / 2 := by ring
  rw [hexp, Real.zero_rpow (by positivity)]
  field_simp
  ring

section Duhamel

variable {F : Type*}
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

def d2DuhamelHolderConst (alpha : NNReal) (v w : V) (K : NNReal) : Real :=
  ‖v‖ * ‖w‖ * (K : Real) * heatC2Holder (V := V) alpha

def d2DuhamelHolderMajor (alpha : NNReal) (v w : V) (K : NNReal)
    (t s : Real) : Real :=
  d2DuhamelHolderConst alpha v w K * holderHeatScale alpha (t - s)

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F] in
theorem d2DuhamelHolderMajor_intble {alpha : NNReal} (halpha : 0 < alpha)
    {t : Real} (v w : V) (K : NNReal) :
    IntervalIntegrable (d2DuhamelHolderMajor alpha v w K t) volume 0 t :=
  (holderHeatScale_intble halpha).const_mul (d2DuhamelHolderConst alpha v w K)

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F] in
theorem d2DuhamelHolderMajor_int {alpha : NNReal} (halpha : 0 < alpha)
    {t : Real} (v w : V) (K : NNReal) :
    ∫ s : Real in 0..t, d2DuhamelHolderMajor alpha v w K t s =
      d2DuhamelHolderConst alpha v w K *
        ((2 / (alpha : Real)) * t ^ ((alpha : Real) / 2)) := by
  unfold d2DuhamelHolderMajor
  rw [intervalIntegral.integral_const_mul, timeHolderHeatScale_int halpha]

theorem heatD2Duhamel_int_of_holder {alpha K : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t) (f : Real → V → F)
    (hf : ∀ s ∈ Set.Icc (0 : Real) t, HolderWith K alpha (f s))
    (v w x : V)
    (hmeas : AEStronglyMeasurable
      (fun s : Real => heatD2Convolution (t - s) v w (f s) x)
      (volume.restrict (Set.uIoc (0 : Real) t))) :
    IntervalIntegrable
      (fun s : Real => heatD2Convolution (t - s) v w (f s) x) volume 0 t := by
  apply (d2DuhamelHolderMajor_intble (V := V) halpha0 v w K).mono_fun' hmeas
  have hne : ∀ᵐ s ∂(volume : Measure Real), s ≠ t := by
    simp [ae_iff, measure_singleton]
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (s := Set.uIoc (0 : Real) t) hne] with s hs hst
  rw [Set.uIoc_of_le ht.le] at hs
  have hstlt : s < t := lt_of_le_of_ne hs.2 hst
  rw [heatD2Convolution_eq_cancel_of_holder halpha0 halpha1 (sub_pos.mpr hstlt)
    (hf s ⟨hs.1.le, hs.2⟩) v w x]
  refine (heatD2Cancel_norm_of_holder halpha1 (sub_pos.mpr hstlt)
    (hf s ⟨hs.1.le, hs.2⟩) v w x).trans_eq ?_
  unfold d2DuhamelHolderMajor d2DuhamelHolderConst
  ring

theorem heatD2Duhamel_norm_of_holder {alpha K : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t) (f : Real → V → F)
    (hf : ∀ s ∈ Set.Icc (0 : Real) t, HolderWith K alpha (f s))
    (v w x : V)
    (hmeas : AEStronglyMeasurable
      (fun s : Real => heatD2Convolution (t - s) v w (f s) x)
      (volume.restrict (Set.uIoc (0 : Real) t))) :
    ‖heatD2Duhamel t v w f x‖ ≤
      d2DuhamelHolderConst alpha v w K *
        ((2 / (alpha : Real)) * t ^ ((alpha : Real) / 2)) := by
  have hint := heatD2Duhamel_int_of_holder halpha0 halpha1 ht f hf v w x hmeas
  unfold heatD2Duhamel
  calc
    ‖∫ s : Real in 0..t, heatD2Convolution (t - s) v w (f s) x‖ ≤
        ∫ s : Real in 0..t, ‖heatD2Convolution (t - s) v w (f s) x‖ :=
      intervalIntegral.norm_integral_le_integral_norm ht.le
    _ ≤ ∫ s : Real in 0..t, d2DuhamelHolderMajor alpha v w K t s := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo ht.le hint.norm
        (d2DuhamelHolderMajor_intble (V := V) halpha0 v w K)
      intro s hs
      rw [heatD2Convolution_eq_cancel_of_holder halpha0 halpha1 (sub_pos.mpr hs.2)
        (hf s ⟨hs.1.le, hs.2.le⟩) v w x]
      refine (heatD2Cancel_norm_of_holder halpha1 (sub_pos.mpr hs.2)
        (hf s ⟨hs.1.le, hs.2.le⟩) v w x).trans_eq ?_
      unfold d2DuhamelHolderMajor d2DuhamelHolderConst
      ring
    _ = d2DuhamelHolderConst alpha v w K *
        ((2 / (alpha : Real)) * t ^ ((alpha : Real) / 2)) :=
      d2DuhamelHolderMajor_int (V := V) halpha0 v w K

end Duhamel

end HeatEquation
