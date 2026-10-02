-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Parabolic/Euclidean/HeatPotential/Schauder.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Parabolic.Euclidean.HeatKernel.Schauder.TimeDerivative
public import CalabiYau.Analysis.Parabolic.Euclidean.HeatPotential.Realization
public import CalabiYau.Analysis.Holder.Basic
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

-- and its private helpers occur in public declarations.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open MeasureTheory Real Set Filter
open scoped NNReal RealInnerProductSpace BigOperators

namespace HeatEquation

open CalabiYau.Schauder

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
omit [FiniteDimensional ℝ V] in
theorem heatD2_space_sub_eq_integral_heatD3 {t : Real} (h v w z : V) :
    heatD2 t v w (z - h) - heatD2 t v w z =
      ∫ s : Real in 0..1, -heatD3 t h v w (z + s • (-h)) := by
  let gamma : Real → V := fun s => z + s • (-h)
  have hgamma : ∀ s : Real, HasDerivAt gamma (-h) s := by
    intro s
    have hs : HasDerivAt (fun r : Real => r • (-h)) (-h) s := by
      simpa using (hasDerivAt_id s).smul_const (-h)
    simpa only [gamma] using hs.const_add z
  have hcomp : ∀ s : Real,
      HasDerivAt (fun r : Real => heatD2 t v w (gamma r))
        (-heatD3 t h v w (gamma s)) s := by
    intro s
    have h0 := (heatD2_hasFDeriv (t := t) v w (gamma s)).comp_hasDerivAt s (hgamma s)
    have hresult : HasDerivAt (fun r : Real => heatD2 t v w (gamma r))
        (-heatD3 t h v w (gamma s)) s :=
      (h0.congr_deriv (by
        simp [heatD3Map_apply, heatD3, baseD3]
        ring)).congr_of_eventuallyEq <|
          Filter.Eventually.of_forall fun _ => rfl
    exact hresult
  have hderiv : IntervalIntegrable
      (fun s : Real => -heatD3 t h v w (gamma s)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    unfold gamma heatD3 baseD3 baseHeat baseHeatMass heatScale
    fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hcomp s) hderiv
  have hgamma0 : gamma 0 = z := by simp [gamma]
  have hgamma1 : gamma 1 = z - h := by simp [gamma, sub_eq_add_neg]
  simpa only [hgamma1, hgamma0] using hftc.symm

section Convolution

variable {F : Type*}
  [NormedAddCommGroup F] [NormedSpace Real F]

omit [Nontrivial V] in
theorem heatD2Convolution_translate_kernel (t : Real) (h v w : V)
    (f : V → F) (x : V) :
    heatD2Convolution t v w f (x - h) =
      ∫ z : V, heatD2 t v w (z - h) • f (x - z) := by
  let g : V → F := fun z => heatD2 t v w (z - h) • f (x - z)
  have htranslate := MeasureTheory.integral_add_right_eq_self
    (μ := volume) g h
  unfold heatD2Convolution
  calc
    (∫ y : V, heatD2 t v w y • f (x - h - y)) =
        ∫ y : V, g (y + h) := by
      apply integral_congr_ae
      filter_upwards with y
      have hk : y + h - h = y := by abel
      have hfarg : x - h - y = x - (y + h) := by abel
      simp only [g, hk, hfarg]
    _ = ∫ z : V, g z := htranslate
    _ = ∫ z : V, heatD2 t v w (z - h) • f (x - z) := by rfl

variable [CompleteSpace F]

omit [CompleteSpace F] in
theorem heatD2Convolution_space_sub_eq_integral_kernel_diff_of_holder
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t) {f : V → F} (hf : HolderWith K alpha f)
    (h v w x : V) :
    heatD2Convolution t v w f (x - h) - heatD2Convolution t v w f x =
      ∫ z : V, (heatD2 t v w (z - h) - heatD2 t v w z) • f (x - z) := by
  have hzero := heatD2Convolution_int_of_holder halpha0 halpha1 ht hf v w x
  have hone0 := heatD2Convolution_int_of_holder halpha0 halpha1 ht hf v w (x - h)
  have hone : Integrable
      (fun z : V => heatD2 t v w (z - h) • f (x - z)) := by
    have htranslated := hone0.comp_add_right (-h)
    refine htranslated.congr (Filter.Eventually.of_forall fun z => ?_)
    have hk : z + -h = z - h := by abel
    have hfarg : x - h - (z - h) = x - z := by abel
    simp only [hk, hfarg]
  rw [heatD2Convolution_translate_kernel]
  unfold heatD2Convolution
  rw [← integral_sub hone hzero]
  apply integral_congr_ae
  filter_upwards with z
  rw [sub_smul]

omit [Nontrivial V] [CompleteSpace F] in
theorem integral_heatD3_path_eq_neg_heatD3Convolution
    (t : Real) (h v w : V) (f : V → F) (x : V) (s : Real) :
    (∫ z : V, (-heatD3 t h v w (z + s • (-h))) • f (x - z)) =
      -heatD3Convolution t h v w f (x - s • h) := by
  let g : V → F := fun z =>
    (-heatD3 t h v w (z + s • (-h))) • f (x - z)
  have htranslate := MeasureTheory.integral_add_right_eq_self
    (μ := volume) g (s • h)
  calc
    (∫ z : V, (-heatD3 t h v w (z + s • (-h))) • f (x - z)) =
        ∫ z : V, g z := by rfl
    _ = ∫ z : V, g (z + s • h) := htranslate.symm
    _ = ∫ z : V, -(heatD3 t h v w z • f (x - s • h - z)) := by
      apply integral_congr_ae
      filter_upwards with z
      have hk : z + s • h + s • (-h) = z := by
        rw [smul_neg]
        abel
      have hfarg : x - (z + s • h) = x - s • h - z := by abel
      simp only [g, hk, hfarg, neg_smul]
    _ = -heatD3Convolution t h v w f (x - s • h) := by
      rw [integral_neg]
      rfl

omit [InnerProductSpace Real V] [FiniteDimensional Real V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedSpace Real F] [CompleteSpace F] in
private theorem holder_shift_bound_heatPotential {alpha K : NNReal}
    {f : V → F} (hf : HolderWith K alpha f) (x y : V) :
    ‖f (x - y) - f x‖ ≤ (K : Real) * ‖y‖ ^ (alpha : Real) := by
  have hxy : dist (x - y) x = ‖y‖ := by
    rw [dist_eq_norm]
    have : (x - y) - x = -y := by abel
    rw [this, norm_neg]
  have h := hf.dist_le (x - y) x
  rw [dist_eq_norm, hxy] at h
  exact h

omit [CompleteSpace F] in
private theorem heatD3_path_integrable_of_holder {alpha K : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t) {f : V → F} (hf : HolderWith K alpha f)
    (h v w x : V) :
    Integrable
      (fun z : Real × V ↦
        (-heatD3 t h v w (z.2 + z.1 • (-h))) • f (x - z.2))
      ((volume.restrict (Ioc 0 1)).prod volume) := by
  let μ : Measure Real := volume.restrict (Ioc 0 1)
  let G : Real × V → F := fun z ↦
    (-heatD3 t h v w (z.2 + z.1 • (-h))) • f (x - z.2)
  let A : Real := ‖h‖ * ‖v‖ * ‖w‖ * (K : Real)
  let B : Real → Real := fun s ↦
    ‖h‖ * ‖v‖ * ‖w‖ * ‖f (x - s • h)‖
  let C : Real → Real := fun s ↦
    A * (∫ y : V, heatD3Holder alpha t y) +
      B s * (∫ y : V, heatD3Maj t y)
  have hfcont : Continuous f := hf.continuous halpha0
  have hGmeas : AEStronglyMeasurable G (μ.prod (volume : Measure V)) := by
    apply Continuous.aestronglyMeasurable
    unfold G heatD3 baseD3 baseHeat baseHeatMass heatScale
    fun_prop
  have hslice_int : ∀ s : Real, Integrable (fun y : V ↦ G (s, y)) := by
    intro s
    have hs :=
      (heatD3Convolution_int_of_holder halpha0 halpha1 ht hf h v w (x - s • h)).neg
        |>.comp_add_right (s • (-h))
    refine hs.congr (Eventually.of_forall fun y ↦ ?_)
    have hfarg : x - s • h - (y + s • (-h)) = x - y := by
      rw [smul_neg]
      abel
    simp only [G, hfarg, Pi.neg_apply, neg_smul]
  have hpoint : ∀ (s : Real) (y : V),
      ‖heatD3 t h v w y • f (x - s • h - y)‖ ≤
        A * heatD3Holder alpha t y + B s * heatD3Maj t y := by
    intro s y
    have hfvalue : ‖f (x - s • h - y)‖ ≤
        (K : Real) * ‖y‖ ^ (alpha : Real) + ‖f (x - s • h)‖ := by
      calc
        ‖f (x - s • h - y)‖ =
            ‖(f (x - s • h - y) - f (x - s • h)) +
              f (x - s • h)‖ := by rw [sub_add_cancel]
        _ ≤ ‖f (x - s • h - y) - f (x - s • h)‖ +
              ‖f (x - s • h)‖ := norm_add_le _ _
        _ ≤ (K : Real) * ‖y‖ ^ (alpha : Real) +
              ‖f (x - s • h)‖ := by
          gcongr
          exact holder_shift_bound_heatPotential hf (x - s • h) y
    rw [norm_smul]
    have hd3 := heatD3_bound ht h v w y
    have hd3holder := heatD3_holder_bound alpha ht h v w y
    calc
      ‖heatD3 t h v w y‖ * ‖f (x - s • h - y)‖ ≤
          ‖heatD3 t h v w y‖ *
            ((K : Real) * ‖y‖ ^ (alpha : Real) +
              ‖f (x - s • h)‖) := by
        gcongr
      _ = ((K : Real) *
            (‖heatD3 t h v w y‖ * ‖y‖ ^ (alpha : Real))) +
          ‖f (x - s • h)‖ * ‖heatD3 t h v w y‖ := by ring
      _ ≤ (K : Real) *
            (‖h‖ * ‖v‖ * ‖w‖ * heatD3Holder alpha t y) +
          ‖f (x - s • h)‖ *
            (‖h‖ * ‖v‖ * ‖w‖ * heatD3Maj t y) := by
        gcongr
      _ = A * heatD3Holder alpha t y + B s * heatD3Maj t y := by
        unfold A B
        ring
  have hslice_bound : ∀ s : Real,
      (∫ y : V, ‖G (s, y)‖) ≤ C s := by
    intro s
    let q : V → Real := fun y ↦
      ‖heatD3 t h v w y • f (x - s • h - y)‖
    have htranslate := MeasureTheory.integral_add_right_eq_self
      (μ := volume) q (s • (-h))
    have hleft_eq : (∫ y : V, ‖G (s, y)‖) = ∫ y : V, q y := by
      rw [← htranslate]
      apply integral_congr_ae
      filter_upwards with y
      have hfarg : x - s • h - (y + s • (-h)) = x - y := by
        rw [smul_neg]
        abel
      simp only [G, q, hfarg, norm_smul, Real.norm_eq_abs, abs_neg]
    have hmajor : Integrable (fun y : V ↦
        A * heatD3Holder alpha t y + B s * heatD3Maj t y) :=
      ((heatD3Holder_int (V := V) halpha1 ht).const_mul A).add
        ((heatD3Maj_int (V := V) ht).const_mul (B s))
    have hq : Integrable q := by
      have hs := heatD3Convolution_int_of_holder halpha0 halpha1 ht hf h v w
        (x - s • h)
      exact hs.norm
    rw [hleft_eq]
    calc
      (∫ y : V, q y) ≤
          ∫ y : V, A * heatD3Holder alpha t y + B s * heatD3Maj t y := by
        exact integral_mono hq hmajor (fun y ↦ hpoint s y)
      _ = C s := by
        have hfirst := (heatD3Holder_int (V := V) halpha1 ht).const_mul A
        have hsecond := (heatD3Maj_int (V := V) ht).const_mul (B s)
        unfold C
        rw [integral_add hfirst hsecond,
          integral_const_mul, integral_const_mul]
  have hCcont : Continuous C := by
    have hcenter : Continuous (fun s : Real ↦ f (x - s • h)) := by
      exact hfcont.comp (by fun_prop)
    unfold C B A
    exact continuous_const.add
      ((continuous_const.mul hcenter.norm).mul continuous_const)
  have hCint : Integrable C μ := by
    have hi := hCcont.intervalIntegrable (μ := volume)
      (a := (0 : Real)) (b := 1)
    change Integrable C (volume.restrict (Ioc (0 : Real) 1))
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (0 : Real) ≤ 1)).mp hi |>.integrable
  have hCnonneg : ∀ s : Real, 0 ≤ C s := by
    intro s
    have hholder : 0 ≤ ∫ y : V, heatD3Holder alpha t y :=
      integral_nonneg (heatD3Holder_nonneg alpha ht)
    have hmaj : 0 ≤ ∫ y : V, heatD3Maj t y :=
      integral_nonneg (heatD3Maj_nonneg ht)
    unfold C A B
    exact add_nonneg
      (mul_nonneg (by positivity) hholder)
      (mul_nonneg (by positivity) hmaj)
  have houter : Integrable (fun s : Real ↦ ∫ y : V, ‖G (s, y)‖) μ := by
    refine hCint.mono hGmeas.norm.integral_prod_right' ?_
    filter_upwards with s
    rw [Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg fun y ↦ norm_nonneg (G (s, y))),
      Real.norm_eq_abs, abs_of_nonneg (hCnonneg s)]
    exact hslice_bound s
  exact (integrable_prod_iff hGmeas).2
    ⟨Eventually.of_forall hslice_int, houter⟩

theorem heatD2Convolution_space_sub_eq_integral_heatD3Convolution_of_holder
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t) {f : V → F} (hf : HolderWith K alpha f)
    (h v w x : V) :
    heatD2Convolution t v w f (x - h) - heatD2Convolution t v w f x =
      ∫ s : Real in 0..1, -heatD3Convolution t h v w f (x - s • h) := by
  let μ : Measure Real := volume.restrict (Ioc 0 1)
  let G : Real × V → F := fun z ↦
    (-heatD3 t h v w (z.2 + z.1 • (-h))) • f (x - z.2)
  have hGint : Integrable G (μ.prod (volume : Measure V)) := by
    simpa only [G, μ] using
      heatD3_path_integrable_of_holder halpha0 halpha1 ht hf h v w x
  rw [heatD2Convolution_space_sub_eq_integral_kernel_diff_of_holder
    halpha0 halpha1 ht hf]
  calc
    (∫ z : V, (heatD2 t v w (z - h) - heatD2 t v w z) • f (x - z)) =
        ∫ z : V, (∫ s : Real in 0..1,
          -heatD3 t h v w (z + s • (-h))) • f (x - z) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [heatD2_space_sub_eq_integral_heatD3]
    _ = ∫ z : V, ∫ s : Real in 0..1,
        (-heatD3 t h v w (z + s • (-h))) • f (x - z) := by
      apply integral_congr_ae
      filter_upwards with z
      exact (intervalIntegral.integral_smul_const
        (fun s : Real ↦ -heatD3 t h v w (z + s • (-h))) (f (x - z))).symm
    _ = ∫ z : V, (∫ s : Real, G (s, z) ∂μ) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [intervalIntegral.integral_of_le (by norm_num)]
    _ = ∫ s : Real, (∫ z : V, G (s, z)) ∂μ := by
      have huncurry : Integrable
          (Function.uncurry (fun s : Real ↦ fun z : V ↦ G (s, z)))
          (μ.prod (volume : Measure V)) := by
        exact hGint.congr <| Filter.Eventually.of_forall fun _ => rfl
      have hswap :
          (∫ s : Real, (∫ z : V, G (s, z)) ∂μ) =
            ∫ z : V, (∫ s : Real, G (s, z) ∂μ) :=
        integral_integral_swap huncurry
      exact hswap.symm
    _ = ∫ s : Real in 0..1, -heatD3Convolution t h v w f (x - s • h) := by
      rw [intervalIntegral.integral_of_le (by norm_num)]
      apply integral_congr_ae
      filter_upwards with s
      simpa only [G] using integral_heatD3_path_eq_neg_heatD3Convolution t h v w f x s

omit [CompleteSpace F] in
theorem heatD3Convolution_path_intervalIntegrable_of_holder
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t) {f : V → F} (hf : HolderWith K alpha f)
    (h v w x : V) :
    IntervalIntegrable
      (fun s : Real ↦ heatD3Convolution t h v w f (x - s • h)) volume 0 1 := by
  let μ : Measure Real := volume.restrict (Ioc 0 1)
  let G : Real × V → F := fun z ↦
    (-heatD3 t h v w (z.2 + z.1 • (-h))) • f (x - z.2)
  have hGint : Integrable G (μ.prod (volume : Measure V)) := by
    simpa only [G, μ] using
      heatD3_path_integrable_of_holder halpha0 halpha1 ht hf h v w x
  have hneg : Integrable
      (fun s : Real ↦ -heatD3Convolution t h v w f (x - s • h)) μ := by
    refine hGint.integral_prod_left.congr (Eventually.of_forall fun s ↦ ?_)
    simpa only [G] using integral_heatD3_path_eq_neg_heatD3Convolution t h v w f x s
  have hconv : Integrable
      (fun s : Real ↦ heatD3Convolution t h v w f (x - s • h)) μ := by
    refine hneg.neg.congr (Eventually.of_forall fun s ↦ ?_)
    simp
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
    (by norm_num : (0 : Real) ≤ 1)]
  change Integrable _ (volume.restrict (Ioc (0 : Real) 1))
  exact hconv

theorem heatD2Convolution_space_sub_norm_le_of_holder
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t) {f : V → F} (hf : HolderWith K alpha f)
    (h v w x : V) :
    ‖heatD2Convolution t v w f (x - h) - heatD2Convolution t v w f x‖ ≤
      ‖h‖ * ‖v‖ * ‖w‖ * (K : Real) * holderThirdHeatScale alpha t *
        heatC3Holder (V := V) alpha := by
  let M : Real :=
    ‖h‖ * ‖v‖ * ‖w‖ * (K : Real) * holderThirdHeatScale alpha t *
      heatC3Holder (V := V) alpha
  have hpath :=
    heatD3Convolution_path_intervalIntegrable_of_holder halpha0 halpha1 ht hf h v w x
  have hconst : IntervalIntegrable (fun _ : Real ↦ M) volume 0 1 :=
    (continuous_const : Continuous (fun _ : Real ↦ M)).intervalIntegrable
      (μ := volume) 0 1
  rw [heatD2Convolution_space_sub_eq_integral_heatD3Convolution_of_holder
    halpha0 halpha1 ht hf]
  calc
    ‖∫ s : Real in 0..1, -heatD3Convolution t h v w f (x - s • h)‖ ≤
        ∫ s : Real in 0..1, ‖-heatD3Convolution t h v w f (x - s • h)‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ _s : Real in 0..1, M := by
      refine intervalIntegral.integral_mono (by norm_num) hpath.neg.norm hconst ?_
      intro s
      dsimp only
      rw [norm_neg]
      simpa only [M] using
        heatD3Convolution_norm_of_holder halpha0 halpha1 ht hf h v w (x - s • h)
    _ = M := by simp
    _ = ‖h‖ * ‖v‖ * ‖w‖ * (K : Real) * holderThirdHeatScale alpha t *
        heatC3Holder (V := V) alpha := by rfl

theorem heatD2Convolution_space_sub_norm_le_recent_of_holder
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t) {f : V → F} (hf : HolderWith K alpha f)
    (h v w x : V) :
    ‖heatD2Convolution t v w f (x - h) - heatD2Convolution t v w f x‖ ≤
      2 * (‖v‖ * ‖w‖ * (K : Real) * holderHeatScale alpha t *
        heatC2Holder (V := V) alpha) := by
  calc
    ‖heatD2Convolution t v w f (x - h) - heatD2Convolution t v w f x‖ ≤
        ‖heatD2Convolution t v w f (x - h)‖ +
          ‖heatD2Convolution t v w f x‖ := norm_sub_le _ _
    _ ≤ (‖v‖ * ‖w‖ * (K : Real) * holderHeatScale alpha t *
          heatC2Holder (V := V) alpha) +
        (‖v‖ * ‖w‖ * (K : Real) * holderHeatScale alpha t *
          heatC2Holder (V := V) alpha) := by
      exact add_le_add
        (by
          rw [heatD2Convolution_eq_cancel_of_holder halpha0 halpha1 ht hf]
          exact heatD2Cancel_norm_of_holder halpha1 ht hf v w (x - h))
        (by
          rw [heatD2Convolution_eq_cancel_of_holder halpha0 halpha1 ht hf]
          exact heatD2Cancel_norm_of_holder halpha1 ht hf v w x)
    _ = 2 * (‖v‖ * ‖w‖ * (K : Real) * holderHeatScale alpha t *
        heatC2Holder (V := V) alpha) := by ring

omit [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F] in
private theorem holderHeatScale_intervalIntegrable {alpha : NNReal}
    (halpha0 : 0 < alpha) (a b : Real) :
    IntervalIntegrable (holderHeatScale alpha) volume a b := by
  unfold holderHeatScale
  apply intervalIntegral.intervalIntegrable_rpow'
  have ha : 0 < (alpha : Real) := by exact_mod_cast halpha0
  linarith

omit [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F] in
private theorem holderHeatScale_terminal_interval_int {alpha : NNReal}
    (halpha0 : 0 < alpha) {a b : Real} :
    ∫ s : Real in a..b, holderHeatScale alpha (b - s) =
      (2 / (alpha : Real)) * (b - a) ^ ((alpha : Real) / 2) := by
  rw [intervalIntegral.integral_comp_sub_left]
  have h := timeHolderHeatScale_int (t := b - a) halpha0
  rw [intervalIntegral.integral_comp_sub_left] at h
  simpa only [sub_self, sub_zero] using h

omit [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F] in
private theorem holderHeatScale_add_le {alpha : NNReal}
    (halpha1 : alpha ≤ 1) {u d : Real} (hu : 0 < u) (hd : 0 ≤ d) :
    holderHeatScale alpha (u + d) ≤ holderHeatScale alpha u := by
  unfold holderHeatScale
  apply Real.rpow_le_rpow_of_nonpos hu (le_add_of_nonneg_right hd)
  have halpha_real : (alpha : Real) ≤ 1 := by exact_mod_cast halpha1
  linarith

omit [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F] in
private theorem holderThirdHeatScale_intervalIntegrable_of_pos
    {alpha : NNReal} {a b : Real} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (holderThirdHeatScale alpha) volume a b := by
  unfold holderThirdHeatScale
  apply ContinuousOn.intervalIntegrable
  intro y hy
  apply (Real.continuousAt_rpow_const y ((alpha : Real) / 2 - 3 / 2)
    (Or.inl ?_)).continuousWithinAt
  rw [uIcc_of_le hab] at hy
  exact (ha.trans_le hy.1).ne'

def d2DuhamelSpaceHolderConst (alpha : NNReal) (v w : V) (K : NNReal) : Real :=
  ‖v‖ * ‖w‖ * (K : Real) *
    ((4 / (alpha : Real)) * heatC2Holder (V := V) alpha +
      (2 / (1 - (alpha : Real))) * heatC3Holder (V := V) alpha)

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F] in
theorem d2DuhamelSpaceHolderConst_nonneg {alpha : NNReal} (halpha : alpha ≤ 1)
    (v w : V) (K : NNReal) :
    0 ≤ d2DuhamelSpaceHolderConst alpha v w K := by
  have halpha_real : (alpha : Real) ≤ 1 := by exact_mod_cast halpha
  unfold d2DuhamelSpaceHolderConst
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (norm_nonneg v) (norm_nonneg w)) K.coe_nonneg)
    (add_nonneg
      (mul_nonneg (div_nonneg (by norm_num) alpha.coe_nonneg)
        (heatC2Holder_nonneg (V := V) alpha))
      (mul_nonneg (div_nonneg (by norm_num) (sub_nonneg.mpr halpha_real))
        (heatC3Holder_nonneg (V := V) alpha)))

theorem heatD2Duhamel_space_sub_eq_integral {alpha K : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t) (f : Real → V → F)
    (hf : ∀ s ∈ Icc (0 : Real) t, HolderWith K alpha (f s))
    (h v w x : V)
    (hmeas0 : AEStronglyMeasurable
      (fun s : Real ↦ heatD2Convolution (t - s) v w (f s) x)
      (volume.restrict (uIoc (0 : Real) t)))
    (hmeas1 : AEStronglyMeasurable
      (fun s : Real ↦ heatD2Convolution (t - s) v w (f s) (x - h))
      (volume.restrict (uIoc (0 : Real) t))) :
    heatD2Duhamel t v w f (x - h) - heatD2Duhamel t v w f x =
      ∫ s : Real in 0..t,
        heatD2Convolution (t - s) v w (f s) (x - h) -
          heatD2Convolution (t - s) v w (f s) x := by
  have h0 := heatD2Duhamel_int_of_holder halpha0 halpha1 ht f hf v w x hmeas0
  have h1 :=
    heatD2Duhamel_int_of_holder halpha0 halpha1 ht f hf v w (x - h) hmeas1
  unfold heatD2Duhamel
  exact (intervalIntegral.integral_sub h1 h0).symm

theorem heatD2Duhamel_space_sub_norm_le_of_holder {alpha K : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {t : Real} (ht : 0 < t) (f : Real → V → F)
    (hf : ∀ s ∈ Icc (0 : Real) t, HolderWith K alpha (f s))
    (h v w x : V)
    (hmeas0 : AEStronglyMeasurable
      (fun s : Real ↦ heatD2Convolution (t - s) v w (f s) x)
      (volume.restrict (uIoc (0 : Real) t)))
    (hmeas1 : AEStronglyMeasurable
      (fun s : Real ↦ heatD2Convolution (t - s) v w (f s) (x - h))
      (volume.restrict (uIoc (0 : Real) t))) :
    ‖heatD2Duhamel t v w f (x - h) - heatD2Duhamel t v w f x‖ ≤
      d2DuhamelSpaceHolderConst alpha v w K * ‖h‖ ^ (alpha : Real) := by
  have halpha_le : alpha ≤ 1 := halpha1.le
  have h0 := heatD2Duhamel_int_of_holder halpha0 halpha_le ht f hf v w x hmeas0
  have h1 :=
    heatD2Duhamel_int_of_holder halpha0 halpha_le ht f hf v w (x - h) hmeas1
  let q : Real → F := fun s ↦
    heatD2Convolution (t - s) v w (f s) (x - h) -
      heatD2Convolution (t - s) v w (f s) x
  have hq : IntervalIntegrable q volume 0 t := h1.sub h0
  rw [heatD2Duhamel_space_sub_eq_integral halpha0 halpha_le ht f hf h v w x
    hmeas0 hmeas1]
  change ‖∫ s : Real in 0..t, q s‖ ≤ _
  by_cases hh0 : ‖h‖ = 0
  · have hh : h = 0 := norm_eq_zero.mp hh0
    subst h
    have halpha_ne : (alpha : Real) ≠ 0 := by exact_mod_cast halpha0.ne'
    have hpow0 : (0 : Real) ^ (alpha : Real) = 0 :=
      Real.zero_rpow halpha_ne
    simp [q, hpow0]
  have hr : 0 < ‖h‖ := lt_of_le_of_ne (norm_nonneg h) (Ne.symm hh0)
  let A2 : Real := 2 * (‖v‖ * ‖w‖ * (K : Real) *
    heatC2Holder (V := V) alpha)
  let A3 : Real := ‖v‖ * ‖w‖ * (K : Real) *
    heatC3Holder (V := V) alpha
  have hA2 : 0 ≤ A2 := by
    unfold A2
    exact mul_nonneg (by norm_num) <|
      mul_nonneg
        (mul_nonneg (mul_nonneg (norm_nonneg v) (norm_nonneg w)) K.coe_nonneg)
        (heatC2Holder_nonneg (V := V) alpha)
  have hA3 : 0 ≤ A3 := by
    unfold A3
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (norm_nonneg v) (norm_nonneg w)) K.coe_nonneg)
      (heatC3Holder_nonneg (V := V) alpha)
  by_cases hsplit : ‖h‖ ^ 2 ≤ t
  · let c : Real := t - ‖h‖ ^ 2
    have hc0 : 0 ≤ c := sub_nonneg.mpr hsplit
    have hct : c ≤ t := sub_le_self t (sq_nonneg ‖h‖)
    have hqe : IntervalIntegrable q volume 0 c := by
      apply hq.mono_set
      rw [uIcc_of_le hc0, uIcc_of_le ht.le]
      exact Icc_subset_Icc le_rfl hct
    have hqr : IntervalIntegrable q volume c t := by
      apply hq.mono_set
      rw [uIcc_of_le hct, uIcc_of_le ht.le]
      exact Icc_subset_Icc hc0 le_rfl
    have hscale2 : IntervalIntegrable
        (fun s : Real ↦ holderHeatScale alpha (t - s)) volume c t := by
      have hs :=
        (holderHeatScale_intervalIntegrable halpha0 0 (‖h‖ ^ 2)).comp_sub_left t
      simpa only [c, sub_zero, sub_sub_cancel] using hs.symm
    have hscale3 : IntervalIntegrable
        (fun s : Real ↦ holderThirdHeatScale alpha (t - s)) volume 0 c := by
      have hs :=
        (holderThirdHeatScale_intervalIntegrable_of_pos
          (sq_pos_of_pos hr) hsplit).comp_sub_left t
      simpa only [c, sub_self, sub_sub_cancel] using hs.symm
    have hearly :
        ‖∫ s : Real in 0..c, q s‖ ≤
          ∫ s : Real in 0..c,
            (‖h‖ * A3) * holderThirdHeatScale alpha (t - s) := by
      calc
        ‖∫ s : Real in 0..c, q s‖ ≤
            ∫ s : Real in 0..c, ‖q s‖ :=
          intervalIntegral.norm_integral_le_integral_norm hc0
        _ ≤ ∫ s : Real in 0..c,
            (‖h‖ * A3) * holderThirdHeatScale alpha (t - s) := by
          apply intervalIntegral.integral_mono_on_of_le_Ioo hc0 hqe.norm
            (hscale3.const_mul (‖h‖ * A3))
          intro s hs
          have hst : 0 < t - s := sub_pos.mpr (hs.2.trans_le hct)
          have hfs : HolderWith K alpha (f s) :=
            hf s ⟨hs.1.le, (hs.2.trans_le hct).le⟩
          change ‖heatD2Convolution (t - s) v w (f s) (x - h) -
              heatD2Convolution (t - s) v w (f s) x‖ ≤ _
          refine (heatD2Convolution_space_sub_norm_le_of_holder
            halpha0 halpha_le hst hfs h v w x).trans_eq ?_
          unfold A3
          ring
    have hrecent :
        ‖∫ s : Real in c..t, q s‖ ≤
          ∫ s : Real in c..t, A2 * holderHeatScale alpha (t - s) := by
      calc
        ‖∫ s : Real in c..t, q s‖ ≤
            ∫ s : Real in c..t, ‖q s‖ :=
          intervalIntegral.norm_integral_le_integral_norm hct
        _ ≤ ∫ s : Real in c..t, A2 * holderHeatScale alpha (t - s) := by
          apply intervalIntegral.integral_mono_on_of_le_Ioo hct hqr.norm
            (hscale2.const_mul A2)
          intro s hs
          have hst : 0 < t - s := sub_pos.mpr hs.2
          have hfs : HolderWith K alpha (f s) :=
            hf s ⟨hc0.trans_lt hs.1 |>.le, hs.2.le⟩
          change ‖heatD2Convolution (t - s) v w (f s) (x - h) -
              heatD2Convolution (t - s) v w (f s) x‖ ≤ _
          refine (heatD2Convolution_space_sub_norm_le_recent_of_holder
            halpha0 halpha_le hst hfs h v w x).trans_eq ?_
          unfold A2
          ring
    have hearly_scale :
        (∫ s : Real in 0..c,
          (‖h‖ * A3) * holderThirdHeatScale alpha (t - s)) ≤
        A3 * ((2 / (1 - (alpha : Real))) * ‖h‖ ^ (alpha : Real)) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_left]
      simp only [c, sub_zero, sub_sub_cancel]
      have hm := mul_holderThirdHeatScale_integral_le halpha1 hr hsplit
      calc
        (‖h‖ * A3) *
            ∫ y : Real in ‖h‖ ^ 2..t, holderThirdHeatScale alpha y =
            A3 * (‖h‖ *
              ∫ y : Real in ‖h‖ ^ 2..t, holderThirdHeatScale alpha y) := by ring
        _ ≤ A3 * ((2 / (1 - (alpha : Real))) *
            ‖h‖ ^ (alpha : Real)) := mul_le_mul_of_nonneg_left hm hA3
    have hrecent_scale :
        (∫ s : Real in c..t, A2 * holderHeatScale alpha (t - s)) =
        A2 * ((2 / (alpha : Real)) * ‖h‖ ^ (alpha : Real)) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_left]
      simp only [c, sub_self, sub_sub_cancel]
      rw [holderHeatScale_integral_sq halpha0 hr.le]
    have hadd := intervalIntegral.integral_add_adjacent_intervals hqe hqr
    calc
      ‖∫ s : Real in 0..t, q s‖ =
          ‖(∫ s : Real in 0..c, q s) + ∫ s : Real in c..t, q s‖ := by
        rw [hadd]
      _ ≤ ‖∫ s : Real in 0..c, q s‖ +
          ‖∫ s : Real in c..t, q s‖ := norm_add_le _ _
      _ ≤ (∫ s : Real in 0..c,
            (‖h‖ * A3) * holderThirdHeatScale alpha (t - s)) +
          ∫ s : Real in c..t, A2 * holderHeatScale alpha (t - s) :=
        add_le_add hearly hrecent
      _ ≤ A3 * ((2 / (1 - (alpha : Real))) * ‖h‖ ^ (alpha : Real)) +
          A2 * ((2 / (alpha : Real)) * ‖h‖ ^ (alpha : Real)) := by
        rw [hrecent_scale]
        gcongr
      _ = d2DuhamelSpaceHolderConst alpha v w K * ‖h‖ ^ (alpha : Real) := by
        unfold A2 A3 d2DuhamelSpaceHolderConst
        ring
  · have htr : t ≤ ‖h‖ ^ 2 := le_of_lt (lt_of_not_ge hsplit)
    have hscale : IntervalIntegrable
        (fun s : Real ↦ holderHeatScale alpha (t - s)) volume 0 t :=
      holderHeatScale_intble halpha0
    have hfull :
        ‖∫ s : Real in 0..t, q s‖ ≤
          ∫ s : Real in 0..t, A2 * holderHeatScale alpha (t - s) := by
      calc
        ‖∫ s : Real in 0..t, q s‖ ≤
            ∫ s : Real in 0..t, ‖q s‖ :=
          intervalIntegral.norm_integral_le_integral_norm ht.le
        _ ≤ ∫ s : Real in 0..t, A2 * holderHeatScale alpha (t - s) := by
          apply intervalIntegral.integral_mono_on_of_le_Ioo ht.le hq.norm
            (hscale.const_mul A2)
          intro s hs
          have hst : 0 < t - s := sub_pos.mpr hs.2
          have hfs : HolderWith K alpha (f s) := hf s ⟨hs.1.le, hs.2.le⟩
          change ‖heatD2Convolution (t - s) v w (f s) (x - h) -
              heatD2Convolution (t - s) v w (f s) x‖ ≤ _
          refine (heatD2Convolution_space_sub_norm_le_recent_of_holder
            halpha0 halpha_le hst hfs h v w x).trans_eq ?_
          unfold A2
          ring
    have hpow : t ^ ((alpha : Real) / 2) ≤ ‖h‖ ^ (alpha : Real) := by
      have hmono := Real.rpow_le_rpow ht.le htr
        (by positivity : 0 ≤ (alpha : Real) / 2)
      calc
        t ^ ((alpha : Real) / 2) ≤ (‖h‖ ^ 2) ^ ((alpha : Real) / 2) := hmono
        _ = ‖h‖ ^ (alpha : Real) := by
          rw [← Real.rpow_natCast]
          rw [← Real.rpow_mul hr.le]
          congr 1
          ring
    calc
      ‖∫ s : Real in 0..t, q s‖ ≤
          ∫ s : Real in 0..t, A2 * holderHeatScale alpha (t - s) := hfull
      _ = A2 * ((2 / (alpha : Real)) * t ^ ((alpha : Real) / 2)) := by
        rw [intervalIntegral.integral_const_mul,
          timeHolderHeatScale_int halpha0]
      _ ≤ A2 * ((2 / (alpha : Real)) * ‖h‖ ^ (alpha : Real)) := by
        gcongr
      _ ≤ d2DuhamelSpaceHolderConst alpha v w K * ‖h‖ ^ (alpha : Real) := by
        unfold A2 d2DuhamelSpaceHolderConst
        have hlate : 0 ≤ (2 / (1 - (alpha : Real))) *
            heatC3Holder (V := V) alpha := by
          exact mul_nonneg
            (div_nonneg (by norm_num)
              (sub_nonneg.mpr (by exact_mod_cast halpha1.le)))
            (heatC3Holder_nonneg (V := V) alpha)
        calc
          2 * (‖v‖ * ‖w‖ * (K : Real) * heatC2Holder alpha) *
              (2 / (alpha : Real) * ‖h‖ ^ (alpha : Real)) =
              (‖v‖ * ‖w‖ * (K : Real)) *
                ((4 / (alpha : Real)) * heatC2Holder alpha) *
                  ‖h‖ ^ (alpha : Real) := by ring
          _ ≤ (‖v‖ * ‖w‖ * (K : Real)) *
                ((4 / (alpha : Real)) * heatC2Holder alpha +
                  (2 / (1 - (alpha : Real))) * heatC3Holder alpha) *
                ‖h‖ ^ (alpha : Real) := by
            gcongr
            exact le_add_of_nonneg_right hlate

theorem heatD2Duhamel_norm_sub_le_of_holder {alpha K : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {t : Real} (ht : 0 < t) (f : Real → V → F)
    (hf : ∀ s ∈ Icc (0 : Real) t, HolderWith K alpha (f s))
    (v w x y : V)
    (hmeasx : AEStronglyMeasurable
      (fun s : Real ↦ heatD2Convolution (t - s) v w (f s) x)
      (volume.restrict (uIoc (0 : Real) t)))
    (hmeasy : AEStronglyMeasurable
      (fun s : Real ↦ heatD2Convolution (t - s) v w (f s) y)
      (volume.restrict (uIoc (0 : Real) t))) :
    ‖heatD2Duhamel t v w f y - heatD2Duhamel t v w f x‖ ≤
      d2DuhamelSpaceHolderConst alpha v w K * ‖y - x‖ ^ (alpha : Real) := by
  have h := heatD2Duhamel_space_sub_norm_le_of_holder
    halpha0 halpha1 ht f hf (x - y) v w x hmeasx (by
      simpa only [sub_sub_cancel] using hmeasy)
  simpa only [sub_sub_cancel, norm_sub_rev] using h

theorem heatD2Convolution_time_add_sub_eq_cancel_of_holder
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t d : Real} (ht : 0 < t) (hd : 0 ≤ d)
    {f : V → F} (hf : HolderWith K alpha f) (v w x : V) :
    heatD2Convolution (t + d) v w f x - heatD2Convolution t v w f x =
      ∫ y : V, (heatD2 (t + d) v w y - heatD2 t v w y) •
        (f (x - y) - f x) := by
  have htplus : 0 < t + d := ht.trans_le (le_add_of_nonneg_right hd)
  have hrawplus := heatD2Convolution_int_of_holder halpha0 halpha1 htplus hf v w x
  have hrawnow := heatD2Convolution_int_of_holder halpha0 halpha1 ht hf v w x
  have hker := (heatD2_int htplus v w).sub (heatD2_int ht v w)
  have hconst := hker.smul_const (f x)
  have hrawdiff := hrawplus.sub hrawnow
  have hcancel : Integrable (fun y : V ↦
      (heatD2 (t + d) v w y - heatD2 t v w y) •
        (f (x - y) - f x)) := by
    refine (hrawdiff.sub hconst).congr (Eventually.of_forall fun y ↦ ?_)
    simp only [Pi.sub_apply, sub_smul, smul_sub]
  unfold heatD2Convolution
  rw [← integral_sub hrawplus hrawnow]
  calc
    (∫ y : V, heatD2 (t + d) v w y • f (x - y) -
        heatD2 t v w y • f (x - y)) =
        ∫ y : V, (heatD2 (t + d) v w y - heatD2 t v w y) •
          (f (x - y) - f x) +
            (heatD2 (t + d) v w y - heatD2 t v w y) • f x := by
      apply integral_congr_ae
      filter_upwards with y
      simp only [sub_smul, smul_sub]
      module
    _ = (∫ y : V, (heatD2 (t + d) v w y - heatD2 t v w y) •
          (f (x - y) - f x)) +
        ∫ y : V, (heatD2 (t + d) v w y - heatD2 t v w y) • f x :=
      integral_add hcancel hconst
    _ = ∫ y : V, (heatD2 (t + d) v w y - heatD2 t v w y) •
        (f (x - y) - f x) := by
      rw [integral_smul_const, integral_sub (heatD2_int htplus v w)
        (heatD2_int ht v w), integral_heatD2_zero htplus,
        integral_heatD2_zero ht, sub_zero, zero_smul, add_zero]

theorem heatD2Convolution_time_add_sub_norm_le_of_holder
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t d : Real} (ht : 0 < t) (hd : 0 ≤ d)
    {f : V → F} (hf : HolderWith K alpha f) (v w x : V) :
    ‖heatD2Convolution (t + d) v w f x - heatD2Convolution t v w f x‖ ≤
      d * ‖v‖ * ‖w‖ * (K : Real) * holderSecondTimeHeatScale alpha t *
        heatC2DtHolder (V := V) alpha := by
  rw [heatD2Convolution_time_add_sub_eq_cancel_of_holder
    halpha0 halpha1 ht hd hf]
  have hmajor :=
    (heatD2_time_add_diff_holder_int halpha1 ht hd v w).const_mul (K : Real)
  calc
    ‖∫ y : V, (heatD2 (t + d) v w y - heatD2 t v w y) •
        (f (x - y) - f x)‖ ≤
      ∫ y : V, (K : Real) *
        (‖heatD2 (t + d) v w y - heatD2 t v w y‖ *
          ‖y‖ ^ (alpha : Real)) := by
      apply norm_integral_le_of_norm_le hmajor
      filter_upwards with y
      rw [norm_smul, Real.norm_eq_abs]
      have hshift := holder_shift_bound_heatPotential hf x y
      rw [← Real.norm_eq_abs]
      calc
        ‖heatD2 (t + d) v w y - heatD2 t v w y‖ *
            ‖f (x - y) - f x‖ ≤
          ‖heatD2 (t + d) v w y - heatD2 t v w y‖ *
            ((K : Real) * ‖y‖ ^ (alpha : Real)) := by gcongr
        _ = (K : Real) *
            (‖heatD2 (t + d) v w y - heatD2 t v w y‖ *
              ‖y‖ ^ (alpha : Real)) := by ring
    _ ≤ (K : Real) *
        (d * ‖v‖ * ‖w‖ * holderSecondTimeHeatScale alpha t *
          heatC2DtHolder (V := V) alpha) := by
      rw [integral_const_mul]
      gcongr
      exact heatD2_time_add_diff_holder halpha1 ht hd v w
    _ = d * ‖v‖ * ‖w‖ * (K : Real) * holderSecondTimeHeatScale alpha t *
        heatC2DtHolder (V := V) alpha := by ring

def d2DuhamelTimeHolderConst (alpha : NNReal) (v w : V) (K : NNReal) : Real :=
  ‖v‖ * ‖w‖ * (K : Real) *
    ((6 / (alpha : Real)) * heatC2Holder (V := V) alpha +
      (2 / (2 - (alpha : Real))) * heatC2DtHolder (V := V) alpha)

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F] in
theorem d2DuhamelTimeHolderConst_nonneg {alpha : NNReal} (halpha : alpha ≤ 1)
    (v w : V) (K : NNReal) :
    0 ≤ d2DuhamelTimeHolderConst alpha v w K := by
  have halpha_real : (alpha : Real) ≤ 1 := by exact_mod_cast halpha
  have hfirst : 0 ≤ (6 / (alpha : Real)) * heatC2Holder (V := V) alpha :=
    mul_nonneg (div_nonneg (by norm_num) alpha.coe_nonneg)
      (heatC2Holder_nonneg (V := V) alpha)
  have hsecond : 0 ≤ (2 / (2 - (alpha : Real))) *
      heatC2DtHolder (V := V) alpha :=
    mul_nonneg (div_nonneg (by norm_num) (by linarith))
      (heatC2DtHolder_nonneg (V := V) alpha)
  unfold d2DuhamelTimeHolderConst
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (norm_nonneg v) (norm_nonneg w)) K.coe_nonneg)
    (add_nonneg hfirst hsecond)

theorem heatD2Duhamel_time_add_sub_eq {alpha K : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {tau d : Real} (htau : 0 < tau) (hd : 0 ≤ d)
    (f : Real → V → F)
    (hf : ∀ s ∈ Icc (0 : Real) (tau + d), HolderWith K alpha (f s))
    (v w x : V)
    (hmeasplus : AEStronglyMeasurable
      (fun s : Real ↦ heatD2Convolution (tau + d - s) v w (f s) x)
      (volume.restrict (uIoc (0 : Real) (tau + d))))
    (hmeasnow : AEStronglyMeasurable
      (fun s : Real ↦ heatD2Convolution (tau - s) v w (f s) x)
      (volume.restrict (uIoc (0 : Real) tau))) :
    heatD2Duhamel (tau + d) v w f x - heatD2Duhamel tau v w f x =
      (∫ s : Real in 0..tau,
        heatD2Convolution ((tau - s) + d) v w (f s) x -
          heatD2Convolution (tau - s) v w (f s) x) +
      ∫ s : Real in tau..tau + d,
        heatD2Convolution (tau + d - s) v w (f s) x := by
  have htplus : 0 < tau + d := htau.trans_le (le_add_of_nonneg_right hd)
  have hplus := heatD2Duhamel_int_of_holder halpha0 halpha1 htplus f hf v w x hmeasplus
  have hfnow : ∀ s ∈ Icc (0 : Real) tau, HolderWith K alpha (f s) := by
    intro s hs
    exact hf s ⟨hs.1, hs.2.trans (le_add_of_nonneg_right hd)⟩
  have hnow := heatD2Duhamel_int_of_holder halpha0 halpha1 htau f hfnow v w x hmeasnow
  have hplusOld : IntervalIntegrable
      (fun s : Real ↦ heatD2Convolution (tau + d - s) v w (f s) x)
      volume 0 tau := by
    apply hplus.mono_set
    rw [uIcc_of_le htau.le, uIcc_of_le htplus.le]
    exact Icc_subset_Icc le_rfl (le_add_of_nonneg_right hd)
  have hplusNew : IntervalIntegrable
      (fun s : Real ↦ heatD2Convolution (tau + d - s) v w (f s) x)
      volume tau (tau + d) := by
    apply hplus.mono_set
    rw [uIcc_of_le (le_add_of_nonneg_right hd), uIcc_of_le htplus.le]
    exact Icc_subset_Icc htau.le le_rfl
  have hadd := intervalIntegral.integral_add_adjacent_intervals hplusOld hplusNew
  have holdsub := intervalIntegral.integral_sub hplusOld hnow
  unfold heatD2Duhamel
  calc
    (∫ s : Real in 0..tau + d, heatD2Convolution (tau + d - s) v w (f s) x) -
        ∫ s : Real in 0..tau, heatD2Convolution (tau - s) v w (f s) x =
      ((∫ s : Real in 0..tau, heatD2Convolution (tau + d - s) v w (f s) x) +
        ∫ s : Real in tau..tau + d,
          heatD2Convolution (tau + d - s) v w (f s) x) -
        ∫ s : Real in 0..tau, heatD2Convolution (tau - s) v w (f s) x := by
      rw [hadd]
    _ = (∫ s : Real in 0..tau,
        heatD2Convolution (tau + d - s) v w (f s) x -
          heatD2Convolution (tau - s) v w (f s) x) +
        ∫ s : Real in tau..tau + d,
          heatD2Convolution (tau + d - s) v w (f s) x := by
      rw [holdsub]
      abel
    _ = (∫ s : Real in 0..tau,
        heatD2Convolution ((tau - s) + d) v w (f s) x -
          heatD2Convolution (tau - s) v w (f s) x) +
        ∫ s : Real in tau..tau + d,
          heatD2Convolution (tau + d - s) v w (f s) x := by
      congr 2
      funext s
      congr 3
      ring

private theorem heatD2Duhamel_time_add_sub_norm_le_large
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {tau d : Real} (htau : 0 < tau) (htd : tau ≤ d)
    (f : Real → V → F)
    (hf : ∀ s ∈ Icc (0 : Real) (tau + d), HolderWith K alpha (f s))
    (v w x : V)
    (hmeasplus : AEStronglyMeasurable
      (fun s : Real ↦ heatD2Convolution (tau + d - s) v w (f s) x)
      (volume.restrict (uIoc (0 : Real) (tau + d))))
    (hmeasnow : AEStronglyMeasurable
      (fun s : Real ↦ heatD2Convolution (tau - s) v w (f s) x)
      (volume.restrict (uIoc (0 : Real) tau))) :
    ‖heatD2Duhamel (tau + d) v w f x - heatD2Duhamel tau v w f x‖ ≤
      d2DuhamelTimeHolderConst alpha v w K * d ^ ((alpha : Real) / 2) := by
  have hd : 0 < d := htau.trans_le htd
  have htplus : 0 < tau + d := htau.trans (lt_add_of_pos_right tau hd)
  have hfnow : ∀ s ∈ Icc (0 : Real) tau, HolderWith K alpha (f s) := by
    intro s hs
    exact hf s ⟨hs.1, hs.2.trans (le_add_of_nonneg_right hd.le)⟩
  have hplus := heatD2Duhamel_norm_of_holder
    halpha0 halpha1 htplus f hf v w x hmeasplus
  have hnow := heatD2Duhamel_norm_of_holder
    halpha0 halpha1 htau f hfnow v w x hmeasnow
  let p : Real := (alpha : Real) / 2
  have hp0 : 0 ≤ p := by
    dsimp [p]
    positivity
  have hp1 : p ≤ 1 := by
    have halpha_real : (alpha : Real) ≤ 1 := by exact_mod_cast halpha1
    dsimp [p]
    linarith
  have htauPow : tau ^ p ≤ d ^ p :=
    Real.rpow_le_rpow htau.le htd hp0
  have htplusPow : (tau + d) ^ p ≤ 2 * d ^ p := by
    calc
      (tau + d) ^ p ≤ (2 * d) ^ p := by
        apply Real.rpow_le_rpow htplus.le
        · linarith
        · exact hp0
      _ = 2 ^ p * d ^ p := Real.mul_rpow (by norm_num) hd.le
      _ ≤ 2 * d ^ p := by
        gcongr
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 2) hp1
  have hduh : 0 ≤ d2DuhamelHolderConst alpha v w K := by
    unfold d2DuhamelHolderConst
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (norm_nonneg v) (norm_nonneg w)) K.coe_nonneg)
      (heatC2Holder_nonneg (V := V) alpha)
  calc
    ‖heatD2Duhamel (tau + d) v w f x - heatD2Duhamel tau v w f x‖ ≤
        ‖heatD2Duhamel (tau + d) v w f x‖ + ‖heatD2Duhamel tau v w f x‖ :=
      norm_sub_le _ _
    _ ≤ d2DuhamelHolderConst alpha v w K *
          ((2 / (alpha : Real)) * (tau + d) ^ p) +
        d2DuhamelHolderConst alpha v w K *
          ((2 / (alpha : Real)) * tau ^ p) := add_le_add hplus hnow
    _ ≤ d2DuhamelHolderConst alpha v w K *
          ((2 / (alpha : Real)) * (2 * d ^ p)) +
        d2DuhamelHolderConst alpha v w K *
          ((2 / (alpha : Real)) * d ^ p) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left htplusPow (by positivity)) hduh)
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left htauPow (by positivity)) hduh)
    _ ≤ d2DuhamelTimeHolderConst alpha v w K * d ^ p := by
      unfold d2DuhamelHolderConst d2DuhamelTimeHolderConst
      have hlate : 0 ≤ (2 / (2 - (alpha : Real))) *
          heatC2DtHolder (V := V) alpha := by
        have halpha_real : (alpha : Real) ≤ 1 := by exact_mod_cast halpha1
        exact mul_nonneg (div_nonneg (by norm_num) (by linarith))
          (heatC2DtHolder_nonneg (V := V) alpha)
      have hbase : 0 ≤ ‖v‖ * ‖w‖ * (K : Real) := by positivity
      have hpow : 0 ≤ d ^ p := Real.rpow_nonneg hd.le p
      calc
        (‖v‖ * ‖w‖ * (K : Real) * heatC2Holder alpha) *
              (2 / (alpha : Real) * (2 * d ^ p)) +
            (‖v‖ * ‖w‖ * (K : Real) * heatC2Holder alpha) *
              (2 / (alpha : Real) * d ^ p) =
            (‖v‖ * ‖w‖ * (K : Real)) *
              ((6 / (alpha : Real)) * heatC2Holder alpha) * d ^ p := by ring
        _ ≤ (‖v‖ * ‖w‖ * (K : Real)) *
              ((6 / (alpha : Real)) * heatC2Holder alpha +
                (2 / (2 - (alpha : Real))) * heatC2DtHolder alpha) *
              d ^ p := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hlate) hbase) hpow

private theorem heatD2Duhamel_time_add_new_norm_le
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {tau d : Real} (htau : 0 ≤ tau) (hd : 0 < d) (f : Real → V → F)
    (hf : ∀ s ∈ Icc (0 : Real) (tau + d), HolderWith K alpha (f s))
    (v w x : V)
    (hnew : IntervalIntegrable
      (fun s : Real ↦ heatD2Convolution (tau + d - s) v w (f s) x)
      volume tau (tau + d)) :
    ‖∫ s : Real in tau..tau + d,
        heatD2Convolution (tau + d - s) v w (f s) x‖ ≤
      d2DuhamelHolderConst alpha v w K *
        ((2 / (alpha : Real)) * d ^ ((alpha : Real) / 2)) := by
  have hscale : IntervalIntegrable
      (fun s : Real ↦ holderHeatScale alpha (tau + d - s))
      volume tau (tau + d) := by
    have hs :=
      (holderHeatScale_intervalIntegrable halpha0 0 d).comp_sub_left (tau + d)
    simpa only [sub_zero, add_sub_cancel_right] using hs.symm
  calc
    ‖∫ s : Real in tau..tau + d,
        heatD2Convolution (tau + d - s) v w (f s) x‖ ≤
      ∫ s : Real in tau..tau + d,
        ‖heatD2Convolution (tau + d - s) v w (f s) x‖ :=
      intervalIntegral.norm_integral_le_integral_norm
        (le_add_of_nonneg_right hd.le)
    _ ≤ ∫ s : Real in tau..tau + d,
        d2DuhamelHolderConst alpha v w K *
          holderHeatScale alpha (tau + d - s) := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo
        (le_add_of_nonneg_right hd.le) hnew.norm
        (hscale.const_mul (d2DuhamelHolderConst alpha v w K))
      intro s hs
      have htime : 0 < tau + d - s := sub_pos.mpr hs.2
      rw [heatD2Convolution_eq_cancel_of_holder halpha0 halpha1 htime
        (hf s ⟨htau.trans hs.1.le, hs.2.le⟩) v w x]
      refine (heatD2Cancel_norm_of_holder halpha1 htime
        (hf s ⟨htau.trans hs.1.le, hs.2.le⟩) v w x).trans_eq ?_
      unfold d2DuhamelHolderConst
      ring
    _ = d2DuhamelHolderConst alpha v w K *
        ((2 / (alpha : Real)) * d ^ ((alpha : Real) / 2)) := by
      rw [intervalIntegral.integral_const_mul,
        holderHeatScale_terminal_interval_int halpha0, add_sub_cancel_left]

private theorem heatD2Duhamel_time_add_late_norm_le
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {tau d : Real} (hd : 0 < d) (hdt : d < tau)
    (f : Real → V → F)
    (hf : ∀ s ∈ Icc (0 : Real) (tau + d), HolderWith K alpha (f s))
    (v w x : V)
    (hq : IntervalIntegrable
      (fun s : Real ↦ heatD2Convolution ((tau - s) + d) v w (f s) x -
        heatD2Convolution (tau - s) v w (f s) x)
      volume 0 (tau - d)) :
    ‖∫ s : Real in 0..tau - d,
        heatD2Convolution ((tau - s) + d) v w (f s) x -
          heatD2Convolution (tau - s) v w (f s) x‖ ≤
      (‖v‖ * ‖w‖ * (K : Real) * heatC2DtHolder (V := V) alpha) *
        ((2 / (2 - (alpha : Real))) * d ^ ((alpha : Real) / 2)) := by
  let B : Real := ‖v‖ * ‖w‖ * (K : Real) * heatC2DtHolder (V := V) alpha
  have hB : 0 ≤ B := by
    unfold B
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (norm_nonneg v) (norm_nonneg w)) K.coe_nonneg)
      (heatC2DtHolder_nonneg (V := V) alpha)
  have hscale0 := holderSecondTimeHeatScale_intervalIntegrable
    (alpha := alpha) hd hdt.le
  have hscale : IntervalIntegrable
      (fun s : Real ↦ holderSecondTimeHeatScale alpha (tau - s))
      volume 0 (tau - d) := by
    have hs := hscale0.comp_sub_left tau
    simpa only [sub_self] using hs.symm
  have halpha2 : alpha < 2 := halpha1.trans_lt (by norm_num)
  calc
    ‖∫ s : Real in 0..tau - d,
        heatD2Convolution ((tau - s) + d) v w (f s) x -
          heatD2Convolution (tau - s) v w (f s) x‖ ≤
      ∫ s : Real in 0..tau - d,
        ‖heatD2Convolution ((tau - s) + d) v w (f s) x -
          heatD2Convolution (tau - s) v w (f s) x‖ :=
      intervalIntegral.norm_integral_le_integral_norm (sub_nonneg.mpr hdt.le)
    _ ≤ ∫ s : Real in 0..tau - d,
        (d * B) * holderSecondTimeHeatScale alpha (tau - s) := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo
        (sub_nonneg.mpr hdt.le) hq.norm (hscale.const_mul (d * B))
      intro s hs
      have htime : 0 < tau - s := by linarith [hs.2]
      have hfs : HolderWith K alpha (f s) :=
        hf s ⟨hs.1.le, by linarith [hs.2]⟩
      refine (heatD2Convolution_time_add_sub_norm_le_of_holder
        halpha0 halpha1 htime hd.le hfs v w x).trans_eq ?_
      unfold B
      ring_nf
    _ = B * (d *
        ∫ u : Real in d..tau, holderSecondTimeHeatScale alpha u) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_left]
      simp only [sub_sub_cancel]
      ring_nf
    _ ≤ B * ((2 / (2 - (alpha : Real))) *
        d ^ ((alpha : Real) / 2)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_holderSecondTimeHeatScale_integral_le halpha2 hd hdt.le) hB
    _ = (‖v‖ * ‖w‖ * (K : Real) * heatC2DtHolder alpha) *
        ((2 / (2 - (alpha : Real))) * d ^ ((alpha : Real) / 2)) := by
      rfl

private theorem heatD2Duhamel_time_add_near_norm_le
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {tau d : Real} (hd : 0 < d) (hdt : d < tau)
    (f : Real → V → F)
    (hf : ∀ s ∈ Icc (0 : Real) (tau + d), HolderWith K alpha (f s))
    (v w x : V)
    (hq : IntervalIntegrable
      (fun s : Real ↦ heatD2Convolution ((tau - s) + d) v w (f s) x -
        heatD2Convolution (tau - s) v w (f s) x)
      volume (tau - d) tau) :
    ‖∫ s : Real in tau - d..tau,
        heatD2Convolution ((tau - s) + d) v w (f s) x -
          heatD2Convolution (tau - s) v w (f s) x‖ ≤
      d2DuhamelHolderConst alpha v w K *
        ((4 / (alpha : Real)) * d ^ ((alpha : Real) / 2)) := by
  have hscale : IntervalIntegrable
      (fun s : Real ↦ holderHeatScale alpha (tau - s))
      volume (tau - d) tau := by
    have hs :=
      (holderHeatScale_intervalIntegrable halpha0 0 d).comp_sub_left tau
    simpa only [sub_zero] using hs.symm
  have hC : 0 ≤ d2DuhamelHolderConst alpha v w K := by
    unfold d2DuhamelHolderConst
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (norm_nonneg v) (norm_nonneg w)) K.coe_nonneg)
      (heatC2Holder_nonneg (V := V) alpha)
  calc
    ‖∫ s : Real in tau - d..tau,
        heatD2Convolution ((tau - s) + d) v w (f s) x -
          heatD2Convolution (tau - s) v w (f s) x‖ ≤
      ∫ s : Real in tau - d..tau,
        ‖heatD2Convolution ((tau - s) + d) v w (f s) x -
          heatD2Convolution (tau - s) v w (f s) x‖ :=
      intervalIntegral.norm_integral_le_integral_norm (sub_le_self tau hd.le)
    _ ≤ ∫ s : Real in tau - d..tau,
        (2 * d2DuhamelHolderConst alpha v w K) *
          holderHeatScale alpha (tau - s) := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo
        (sub_le_self tau hd.le) hq.norm
        (hscale.const_mul (2 * d2DuhamelHolderConst alpha v w K))
      intro s hs
      have htime : 0 < tau - s := sub_pos.mpr hs.2
      have htimeplus : 0 < (tau - s) + d :=
        htime.trans_le (le_add_of_nonneg_right hd.le)
      have hfs : HolderWith K alpha (f s) :=
        hf s ⟨by linarith [hs.1, hdt], by linarith [hs.2]⟩
      have hplus : ‖heatD2Convolution ((tau - s) + d) v w (f s) x‖ ≤
          d2DuhamelHolderConst alpha v w K *
            holderHeatScale alpha ((tau - s) + d) := by
        rw [heatD2Convolution_eq_cancel_of_holder
          halpha0 halpha1 htimeplus hfs v w x]
        refine (heatD2Cancel_norm_of_holder halpha1 htimeplus hfs v w x).trans_eq ?_
        unfold d2DuhamelHolderConst
        ring
      have hnow : ‖heatD2Convolution (tau - s) v w (f s) x‖ ≤
          d2DuhamelHolderConst alpha v w K * holderHeatScale alpha (tau - s) := by
        rw [heatD2Convolution_eq_cancel_of_holder halpha0 halpha1 htime hfs v w x]
        refine (heatD2Cancel_norm_of_holder halpha1 htime hfs v w x).trans_eq ?_
        unfold d2DuhamelHolderConst
        ring
      have hscaleAdd := holderHeatScale_add_le halpha1 htime hd.le
      calc
        ‖heatD2Convolution ((tau - s) + d) v w (f s) x -
            heatD2Convolution (tau - s) v w (f s) x‖ ≤
          ‖heatD2Convolution ((tau - s) + d) v w (f s) x‖ +
            ‖heatD2Convolution (tau - s) v w (f s) x‖ := norm_sub_le _ _
        _ ≤ d2DuhamelHolderConst alpha v w K *
              holderHeatScale alpha ((tau - s) + d) +
            d2DuhamelHolderConst alpha v w K *
              holderHeatScale alpha (tau - s) := add_le_add hplus hnow
        _ ≤ d2DuhamelHolderConst alpha v w K * holderHeatScale alpha (tau - s) +
            d2DuhamelHolderConst alpha v w K * holderHeatScale alpha (tau - s) := by
          gcongr
        _ = (2 * d2DuhamelHolderConst alpha v w K) *
            holderHeatScale alpha (tau - s) := by ring
    _ = d2DuhamelHolderConst alpha v w K *
        ((4 / (alpha : Real)) * d ^ ((alpha : Real) / 2)) := by
      rw [intervalIntegral.integral_const_mul,
        holderHeatScale_terminal_interval_int halpha0, sub_sub_cancel]
      ring

private theorem heatD2Duhamel_time_add_sub_norm_le_small
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {tau d : Real} (htau : 0 < tau) (hd : 0 < d) (hdt : d < tau)
    (f : Real → V → F)
    (hf : ∀ s ∈ Icc (0 : Real) (tau + d), HolderWith K alpha (f s))
    (v w x : V)
    (hmeasplus : AEStronglyMeasurable
      (fun s : Real ↦ heatD2Convolution (tau + d - s) v w (f s) x)
      (volume.restrict (uIoc (0 : Real) (tau + d))))
    (hmeasnow : AEStronglyMeasurable
      (fun s : Real ↦ heatD2Convolution (tau - s) v w (f s) x)
      (volume.restrict (uIoc (0 : Real) tau))) :
    ‖heatD2Duhamel (tau + d) v w f x - heatD2Duhamel tau v w f x‖ ≤
      d2DuhamelTimeHolderConst alpha v w K * d ^ ((alpha : Real) / 2) := by
  have htplus : 0 < tau + d := htau.trans (lt_add_of_pos_right tau hd)
  have hplus := heatD2Duhamel_int_of_holder
    halpha0 halpha1 htplus f hf v w x hmeasplus
  have hfnow : ∀ s ∈ Icc (0 : Real) tau, HolderWith K alpha (f s) := by
    intro s hs
    exact hf s ⟨hs.1, hs.2.trans (le_add_of_nonneg_right hd.le)⟩
  have hnow := heatD2Duhamel_int_of_holder
    halpha0 halpha1 htau f hfnow v w x hmeasnow
  have hplusOld : IntervalIntegrable
      (fun s : Real ↦ heatD2Convolution (tau + d - s) v w (f s) x)
      volume 0 tau := by
    apply hplus.mono_set
    rw [uIcc_of_le htau.le, uIcc_of_le htplus.le]
    exact Icc_subset_Icc le_rfl (le_add_of_nonneg_right hd.le)
  have hnew : IntervalIntegrable
      (fun s : Real ↦ heatD2Convolution (tau + d - s) v w (f s) x)
      volume tau (tau + d) := by
    apply hplus.mono_set
    rw [uIcc_of_le (le_add_of_nonneg_right hd.le), uIcc_of_le htplus.le]
    exact Icc_subset_Icc htau.le le_rfl
  have hq : IntervalIntegrable
      (fun s : Real ↦ heatD2Convolution ((tau - s) + d) v w (f s) x -
        heatD2Convolution (tau - s) v w (f s) x)
      volume 0 tau := by
    have hraw := hplusOld.sub hnow
    refine hraw.congr ?_
    intro s _
    ring_nf
  have hlate : IntervalIntegrable
      (fun s : Real ↦ heatD2Convolution ((tau - s) + d) v w (f s) x -
        heatD2Convolution (tau - s) v w (f s) x)
      volume 0 (tau - d) := by
    apply hq.mono_set
    rw [uIcc_of_le (sub_nonneg.mpr hdt.le), uIcc_of_le htau.le]
    exact Icc_subset_Icc le_rfl (sub_le_self tau hd.le)
  have hnear : IntervalIntegrable
      (fun s : Real ↦ heatD2Convolution ((tau - s) + d) v w (f s) x -
        heatD2Convolution (tau - s) v w (f s) x)
      volume (tau - d) tau := by
    apply hq.mono_set
    rw [uIcc_of_le (sub_le_self tau hd.le), uIcc_of_le htau.le]
    exact Icc_subset_Icc (sub_nonneg.mpr hdt.le) le_rfl
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hlate hnear
  have hlateBound := heatD2Duhamel_time_add_late_norm_le
    halpha0 halpha1 hd hdt f hf v w x hlate
  have hnearBound := heatD2Duhamel_time_add_near_norm_le
    halpha0 halpha1 hd hdt f hf v w x hnear
  have hnewBound := heatD2Duhamel_time_add_new_norm_le
    halpha0 halpha1 htau.le hd f hf v w x hnew
  rw [heatD2Duhamel_time_add_sub_eq halpha0 halpha1 htau hd.le
    f hf v w x hmeasplus hmeasnow, ← hsplit]
  calc
    ‖((∫ s : Real in 0..tau - d,
          heatD2Convolution (tau - s + d) v w (f s) x -
            heatD2Convolution (tau - s) v w (f s) x) +
        ∫ s : Real in tau - d..tau,
          heatD2Convolution (tau - s + d) v w (f s) x -
            heatD2Convolution (tau - s) v w (f s) x) +
      ∫ s : Real in tau..tau + d,
        heatD2Convolution (tau + d - s) v w (f s) x‖ ≤
      ‖∫ s : Real in 0..tau - d,
          heatD2Convolution (tau - s + d) v w (f s) x -
            heatD2Convolution (tau - s) v w (f s) x‖ +
        ‖∫ s : Real in tau - d..tau,
          heatD2Convolution (tau - s + d) v w (f s) x -
            heatD2Convolution (tau - s) v w (f s) x‖ +
        ‖∫ s : Real in tau..tau + d,
          heatD2Convolution (tau + d - s) v w (f s) x‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (‖v‖ * ‖w‖ * (K : Real) * heatC2DtHolder alpha) *
          ((2 / (2 - (alpha : Real))) * d ^ ((alpha : Real) / 2)) +
        d2DuhamelHolderConst alpha v w K *
          ((4 / (alpha : Real)) * d ^ ((alpha : Real) / 2)) +
        d2DuhamelHolderConst alpha v w K *
          ((2 / (alpha : Real)) * d ^ ((alpha : Real) / 2)) :=
      add_le_add (add_le_add hlateBound hnearBound) hnewBound
    _ = d2DuhamelTimeHolderConst alpha v w K * d ^ ((alpha : Real) / 2) := by
      unfold d2DuhamelHolderConst d2DuhamelTimeHolderConst
      ring

theorem heatD2Duhamel_time_add_sub_norm_le_of_holder
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {tau d : Real} (htau : 0 < tau) (hd : 0 ≤ d)
    (f : Real → V → F)
    (hf : ∀ s ∈ Icc (0 : Real) (tau + d), HolderWith K alpha (f s))
    (v w x : V)
    (hmeasplus : AEStronglyMeasurable
      (fun s : Real ↦ heatD2Convolution (tau + d - s) v w (f s) x)
      (volume.restrict (uIoc (0 : Real) (tau + d))))
    (hmeasnow : AEStronglyMeasurable
      (fun s : Real ↦ heatD2Convolution (tau - s) v w (f s) x)
      (volume.restrict (uIoc (0 : Real) tau))) :
    ‖heatD2Duhamel (tau + d) v w f x - heatD2Duhamel tau v w f x‖ ≤
      d2DuhamelTimeHolderConst alpha v w K * d ^ ((alpha : Real) / 2) := by
  by_cases hd0 : d = 0
  · subst d
    simp only [add_zero, sub_self, norm_zero]
    rw [Real.zero_rpow]
    · simp
    · positivity
  have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
  by_cases htd : tau ≤ d
  · exact heatD2Duhamel_time_add_sub_norm_le_large
      halpha0 halpha1 htau htd f hf v w x hmeasplus hmeasnow
  · exact heatD2Duhamel_time_add_sub_norm_le_small
      halpha0 halpha1 htau hdpos (lt_of_not_ge htd)
      f hf v w x hmeasplus hmeasnow

theorem heatD2Duhamel_time_norm_sub_le_of_holder
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {s t : Real} (hs : 0 < s) (ht : 0 < t)
    (f : Real → V → F)
    (hf : ∀ r ∈ Icc (0 : Real) (max s t), HolderWith K alpha (f r))
    (v w x : V)
    (hmeass : AEStronglyMeasurable
      (fun r : Real ↦ heatD2Convolution (s - r) v w (f r) x)
      (volume.restrict (uIoc (0 : Real) s)))
    (hmeast : AEStronglyMeasurable
      (fun r : Real ↦ heatD2Convolution (t - r) v w (f r) x)
      (volume.restrict (uIoc (0 : Real) t))) :
    ‖heatD2Duhamel t v w f x - heatD2Duhamel s v w f x‖ ≤
      d2DuhamelTimeHolderConst alpha v w K *
        |t - s| ^ ((alpha : Real) / 2) := by
  rcases le_total s t with hst | hts
  · have heq : s + (t - s) = t := by ring
    have hf' : ∀ r ∈ Icc (0 : Real) (s + (t - s)),
        HolderWith K alpha (f r) := by
      rw [heq]
      simpa only [max_eq_right hst] using hf
    have h := heatD2Duhamel_time_add_sub_norm_le_of_holder
      halpha0 halpha1 hs (sub_nonneg.mpr hst) f hf' v w x (by
        simpa only [heq] using hmeast) hmeass
    simpa only [heq, abs_of_nonneg (sub_nonneg.mpr hst)] using h
  · have heq : t + (s - t) = s := by ring
    have hf' : ∀ r ∈ Icc (0 : Real) (t + (s - t)),
        HolderWith K alpha (f r) := by
      rw [heq]
      simpa only [max_eq_left hts] using hf
    have h := heatD2Duhamel_time_add_sub_norm_le_of_holder
      halpha0 halpha1 ht (sub_nonneg.mpr hts) f hf' v w x (by
        simpa only [heq] using hmeass) hmeast
    simpa only [heq, norm_sub_rev,
      abs_of_nonpos (sub_nonpos.mpr hts), neg_sub] using h

def d2DuhamelParabolicHolderConst (alpha : NNReal) (v w : V) (K : NNReal) : Real :=
  d2DuhamelSpaceHolderConst alpha v w K + d2DuhamelTimeHolderConst alpha v w K

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F] in
theorem d2DuhamelParabolicHolderConst_nonneg {alpha : NNReal} (halpha : alpha ≤ 1)
    (v w : V) (K : NNReal) :
    0 ≤ d2DuhamelParabolicHolderConst alpha v w K := by
  exact add_nonneg (d2DuhamelSpaceHolderConst_nonneg (V := V) halpha v w K)
    (d2DuhamelTimeHolderConst_nonneg (V := V) halpha v w K)

theorem heatD2Duhamel_parabolic_norm_sub_le_of_holder
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {s t : Real} (hs : 0 < s) (ht : 0 < t)
    (f : Real → V → F)
    (hf : ∀ r ∈ Icc (0 : Real) (max s t), HolderWith K alpha (f r))
    (v w x y : V)
    (hmeastx : AEStronglyMeasurable
      (fun r : Real ↦ heatD2Convolution (t - r) v w (f r) x)
      (volume.restrict (uIoc (0 : Real) t)))
    (hmeasty : AEStronglyMeasurable
      (fun r : Real ↦ heatD2Convolution (t - r) v w (f r) y)
      (volume.restrict (uIoc (0 : Real) t)))
    (hmeassy : AEStronglyMeasurable
      (fun r : Real ↦ heatD2Convolution (s - r) v w (f r) y)
      (volume.restrict (uIoc (0 : Real) s))) :
    ‖heatD2Duhamel t v w f x - heatD2Duhamel s v w f y‖ ≤
      d2DuhamelParabolicHolderConst alpha v w K *
        (max (|t - s| ^ (1 / 2 : Real)) ‖x - y‖) ^ (alpha : Real) := by
  have halpha_le : alpha ≤ 1 := halpha1.le
  have hft : ∀ r ∈ Icc (0 : Real) t, HolderWith K alpha (f r) := by
    intro r hr
    exact hf r ⟨hr.1, hr.2.trans (le_max_right s t)⟩
  have hspace := heatD2Duhamel_norm_sub_le_of_holder
    halpha0 halpha1 ht f hft v w x y hmeastx hmeasty
  have htime := heatD2Duhamel_time_norm_sub_le_of_holder
    halpha0 halpha_le hs ht f hf v w y hmeassy hmeasty
  let D : Real := max (|t - s| ^ (1 / 2 : Real)) ‖x - y‖
  have hspaceD : ‖x - y‖ ^ (alpha : Real) ≤ D ^ (alpha : Real) := by
    apply Real.rpow_le_rpow (norm_nonneg _) (le_max_right _ _) alpha.coe_nonneg
  have htimeD : |t - s| ^ ((alpha : Real) / 2) ≤ D ^ (alpha : Real) := by
    have hhalf : |t - s| ^ (1 / 2 : Real) ≤ D := le_max_left _ _
    calc
      |t - s| ^ ((alpha : Real) / 2) =
          (|t - s| ^ (1 / 2 : Real)) ^ (alpha : Real) := by
        rw [← Real.rpow_mul (abs_nonneg _)]
        congr 1
        ring
      _ ≤ D ^ (alpha : Real) :=
        Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg _) _)
          hhalf alpha.coe_nonneg
  have hCs := d2DuhamelSpaceHolderConst_nonneg (V := V) halpha_le v w K
  have hCt := d2DuhamelTimeHolderConst_nonneg (V := V) halpha_le v w K
  calc
    ‖heatD2Duhamel t v w f x - heatD2Duhamel s v w f y‖ =
        ‖(heatD2Duhamel t v w f x - heatD2Duhamel t v w f y) +
          (heatD2Duhamel t v w f y - heatD2Duhamel s v w f y)‖ := by
      congr 1
      abel
    _ ≤ ‖heatD2Duhamel t v w f x - heatD2Duhamel t v w f y‖ +
          ‖heatD2Duhamel t v w f y - heatD2Duhamel s v w f y‖ := norm_add_le _ _
    _ ≤ d2DuhamelSpaceHolderConst alpha v w K * ‖x - y‖ ^ (alpha : Real) +
        d2DuhamelTimeHolderConst alpha v w K * |t - s| ^ ((alpha : Real) / 2) :=
      add_le_add (by simpa only [norm_sub_rev] using hspace) htime
    _ ≤ d2DuhamelSpaceHolderConst alpha v w K * D ^ (alpha : Real) +
        d2DuhamelTimeHolderConst alpha v w K * D ^ (alpha : Real) :=
      add_le_add (mul_le_mul_of_nonneg_left hspaceD hCs)
        (mul_le_mul_of_nonneg_left htimeD hCt)
    _ = d2DuhamelParabolicHolderConst alpha v w K * D ^ (alpha : Real) := by
      unfold d2DuhamelParabolicHolderConst
      ring

def heatD2DuhamelField (v w : V) (f : Real → V → F) : ParabolicPoint V → F :=
  fun p ↦ heatD2Duhamel p.time v w f p.space

theorem heatD2DuhamelField_holderOnWith_of_holder
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {T : Real} (f : Real → V → F)
    (hf : ∀ r ∈ Icc (0 : Real) T, HolderWith K alpha (f r))
    (v w : V)
    (hmeas : ∀ t ∈ Ioc (0 : Real) T, ∀ x : V,
      AEStronglyMeasurable
        (fun r : Real ↦ heatD2Convolution (t - r) v w (f r) x)
        (volume.restrict (uIoc (0 : Real) t))) :
    HolderOnWith (Real.toNNReal (d2DuhamelParabolicHolderConst alpha v w K)) alpha
      (heatD2DuhamelField v w f)
      (parabolicCylinder (Ioc (0 : Real) T) Set.univ) := by
  intro p hp q hq
  have hf' : ∀ r ∈ Icc (0 : Real) (max q.time p.time),
      HolderWith K alpha (f r) := by
    intro r hr
    exact hf r ⟨hr.1, hr.2.trans (max_le hq.1.2 hp.1.2)⟩
  have hreal := heatD2Duhamel_parabolic_norm_sub_le_of_holder
    halpha0 halpha1 hq.1.1 hp.1.1 f hf' v w p.space q.space
    (hmeas p.time hp.1 p.space) (hmeas p.time hp.1 q.space)
    (hmeas q.time hq.1 q.space)
  have hp_repr : parabolicPoint p.time p.space = p := by
    rcases p with ⟨⟨pt⟩, px⟩
    rfl
  have hq_repr : parabolicPoint q.time q.space = q := by
    rcases q with ⟨⟨qt⟩, qx⟩
    rfl
  have hdist : dist p q =
      max (|p.time - q.time| ^ (1 / 2 : Real)) ‖p.space - q.space‖ := by
    rw [← hp_repr, ← hq_repr, dist_parabolicPoint, dist_eq_norm]
    simp only [parabolicPoint_time, parabolicPoint_space]
  change edist (heatD2Duhamel p.time v w f p.space)
      (heatD2Duhamel q.time v w f q.space) ≤ _
  rw [edist_dist, edist_dist, hdist, ENNReal.ofNNReal_toNNReal,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) alpha.coe_nonneg,
    ← ENNReal.ofReal_mul
      (d2DuhamelParabolicHolderConst_nonneg (V := V) halpha1.le v w K)]
  simpa only [dist_eq_norm] using ENNReal.ofReal_le_ofReal hreal

theorem heatD2DuhamelField_holderWith_restrict_of_holder
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {T : Real} (f : Real → V → F)
    (hf : ∀ r ∈ Icc (0 : Real) T, HolderWith K alpha (f r))
    (v w : V)
    (hmeas : ∀ t ∈ Ioc (0 : Real) T, ∀ x : V,
      AEStronglyMeasurable
        (fun r : Real ↦ heatD2Convolution (t - r) v w (f r) x)
        (volume.restrict (uIoc (0 : Real) t))) :
    HolderWith (Real.toNNReal (d2DuhamelParabolicHolderConst alpha v w K)) alpha
      ((parabolicCylinder (Ioc (0 : Real) T) Set.univ).domRestrict
        (heatD2DuhamelField v w f)) :=
  (heatD2DuhamelField_holderOnWith_of_holder
    halpha0 halpha1 f hf v w hmeas).holderWith

def d2DuhamelJetHolderConst (alpha K : NNReal) : NNReal :=
  ∑ β : Fin 2 → Fin (Module.finrank Real V),
    Real.toNNReal (d2DuhamelParabolicHolderConst alpha
      ((stdOrthonormalBasis Real V) (β 0))
      ((stdOrthonormalBasis Real V) (β 1)) K)

def d2DuhamelJetNormConst (alpha K : NNReal) (T : Real) : NNReal :=
  ∑ β : Fin 2 → Fin (Module.finrank Real V),
    Real.toNNReal (d2DuhamelHolderConst alpha
      ((stdOrthonormalBasis Real V) (β 0))
      ((stdOrthonormalBasis Real V) (β 1)) K *
        ((2 / (alpha : Real)) * T ^ ((alpha : Real) / 2)))

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F] in
private theorem d2DuhamelJetNormConst_term_nonneg
    {alpha : NNReal} (halpha0 : 0 < alpha) (K : NNReal) {T : Real} (hT : 0 ≤ T)
    (β : Fin 2 → Fin (Module.finrank Real V)) :
    0 ≤ d2DuhamelHolderConst alpha
      ((stdOrthonormalBasis Real V) (β 0))
      ((stdOrthonormalBasis Real V) (β 1)) K *
        ((2 / (alpha : Real)) * T ^ ((alpha : Real) / 2)) := by
  have halphaReal : 0 < (alpha : Real) := by exact_mod_cast halpha0
  have hconst : 0 ≤ d2DuhamelHolderConst alpha
      ((stdOrthonormalBasis Real V) (β 0))
      ((stdOrthonormalBasis Real V) (β 1)) K := by
    unfold d2DuhamelHolderConst
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) K.coe_nonneg)
      (heatC2Holder_nonneg (V := V) alpha)
  exact mul_nonneg hconst
    (mul_nonneg (div_nonneg (by norm_num) halphaReal.le)
      (Real.rpow_nonneg hT _))

theorem parabolicSpatialJet_two_norm_le_of_heatD2Duhamel
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {T : Real} (hT : 0 ≤ T) (u f : Real → V → F)
    (hf : ∀ r ∈ Icc (0 : Real) T, HolderWith K alpha (f r))
    (hrealize : ∀ p ∈ parabolicCylinder (Ioc (0 : Real) T) Set.univ,
      ∀ m : Fin 2 → V,
        parabolicSpatialJet 2 u p m =
          heatD2Duhamel p.time (m 0) (m 1) f p.space)
    (hmeas : ∀ t ∈ Ioc (0 : Real) T, ∀ x : V,
      ∀ β : Fin 2 → Fin (Module.finrank Real V),
      AEStronglyMeasurable
        (fun r : Real ↦ heatD2Convolution (t - r)
          ((stdOrthonormalBasis Real V) (β 0))
          ((stdOrthonormalBasis Real V) (β 1)) (f r) x)
        (volume.restrict (uIoc (0 : Real) t)))
    (p : ParabolicPoint V)
    (hp : p ∈ parabolicCylinder (Ioc (0 : Real) T) Set.univ) :
    ‖parabolicSpatialJet 2 u p‖ ≤ d2DuhamelJetNormConst (V := V) alpha K T := by
  have hbasis := continuousMultilinearMap_norm_le_sum_stdOrthonormalBasis
    (parabolicSpatialJet 2 u p)
  calc
    ‖parabolicSpatialJet 2 u p‖ ≤
        ∑ β : Fin 2 → Fin (Module.finrank Real V),
          ‖parabolicSpatialJet 2 u p
            (fun i ↦ (stdOrthonormalBasis Real V) (β i))‖ := hbasis
    _ ≤ ∑ β : Fin 2 → Fin (Module.finrank Real V),
        d2DuhamelHolderConst alpha
          ((stdOrthonormalBasis Real V) (β 0))
          ((stdOrthonormalBasis Real V) (β 1)) K *
            ((2 / (alpha : Real)) * T ^ ((alpha : Real) / 2)) := by
      gcongr with β
      rw [hrealize p hp]
      have hslice : ∀ r ∈ Icc (0 : Real) p.time, HolderWith K alpha (f r) := by
        intro r hr
        exact hf r ⟨hr.1, hr.2.trans hp.1.2⟩
      have hraw := heatD2Duhamel_norm_of_holder halpha0 halpha1 hp.1.1 f hslice
        ((stdOrthonormalBasis Real V) (β 0))
        ((stdOrthonormalBasis Real V) (β 1)) p.space
        (hmeas p.time hp.1 p.space β)
      refine hraw.trans ?_
      have hcoef : 0 ≤ d2DuhamelHolderConst alpha
          ((stdOrthonormalBasis Real V) (β 0))
          ((stdOrthonormalBasis Real V) (β 1)) K := by
        unfold d2DuhamelHolderConst
        exact mul_nonneg
          (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) K.coe_nonneg)
          (heatC2Holder_nonneg (V := V) alpha)
      have hfactor : 0 ≤ 2 / (alpha : Real) := by
        exact div_nonneg (by norm_num) (by exact_mod_cast halpha0.le)
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hp.1.1.le hp.1.2 (by positivity)) hfactor) hcoef
    _ = d2DuhamelJetNormConst (V := V) alpha K T := by
      unfold d2DuhamelJetNormConst
      push_cast
      apply Finset.sum_congr rfl
      intro β _
      exact (Real.coe_toNNReal _
        (d2DuhamelJetNormConst_term_nonneg (V := V) halpha0 K hT β)).symm

theorem parabolicSpatialJet_two_holderWith_restrict_of_heatD2Duhamel
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {T : Real} (u f : Real → V → F)
    (hf : ∀ r ∈ Icc (0 : Real) T, HolderWith K alpha (f r))
    (hu : ∀ p ∈ parabolicCylinder (Ioc (0 : Real) T) Set.univ,
      ∀ m : Fin 2 → V,
        parabolicSpatialJet 2 u p m =
          heatD2Duhamel p.time (m 0) (m 1) f p.space)
    (hmeas : ∀ t ∈ Ioc (0 : Real) T, ∀ x : V,
      ∀ β : Fin 2 → Fin (Module.finrank Real V),
      AEStronglyMeasurable
        (fun r : Real ↦ heatD2Convolution (t - r)
          ((stdOrthonormalBasis Real V) (β 0))
          ((stdOrthonormalBasis Real V) (β 1)) (f r) x)
        (volume.restrict (uIoc (0 : Real) t))) :
    HolderWith (d2DuhamelJetHolderConst (V := V) alpha K) alpha
      ((parabolicCylinder (Ioc (0 : Real) T) Set.univ).domRestrict
        (parabolicSpatialJet 2 u)) := by
  apply holderWith_continuousMultilinearMap_of_stdOrthonormalBasis
    (C := fun β : Fin 2 → Fin (Module.finrank Real V) ↦
      Real.toNNReal (d2DuhamelParabolicHolderConst alpha
        ((stdOrthonormalBasis Real V) (β 0))
        ((stdOrthonormalBasis Real V) (β 1)) K))
  intro β
  have hdir := heatD2DuhamelField_holderWith_restrict_of_holder
    halpha0 halpha1 f hf
    ((stdOrthonormalBasis Real V) (β 0))
    ((stdOrthonormalBasis Real V) (β 1))
    (fun t ht x ↦ hmeas t ht x β)
  intro p q
  simp only [Set.domRestrict_apply]
  rw [hu p.1 p.2 (fun i ↦ (stdOrthonormalBasis Real V) (β i)),
    hu q.1 q.2 (fun i ↦ (stdOrthonormalBasis Real V) (β i))]
  simpa only [Set.domRestrict_apply, heatD2DuhamelField, edist_dist] using hdir p q

def heatLapDuhamel (t : Real) (f : Real → V → F) (x : V) : F :=
  ∑ i : Fin (Module.finrank Real V),
    heatD2Duhamel t ((stdOrthonormalBasis Real V) i)
      ((stdOrthonormalBasis Real V) i) f x

def lapDuhamelParabolicHolderConst (alpha K : NNReal) : Real :=
  ∑ i : Fin (Module.finrank Real V),
    d2DuhamelParabolicHolderConst alpha ((stdOrthonormalBasis Real V) i)
      ((stdOrthonormalBasis Real V) i) K

def lapDuhamelNormConst (alpha K : NNReal) (T : Real) : NNReal :=
  ∑ i : Fin (Module.finrank Real V),
    Real.toNNReal (d2DuhamelHolderConst alpha
      ((stdOrthonormalBasis Real V) i)
      ((stdOrthonormalBasis Real V) i) K *
        ((2 / (alpha : Real)) * T ^ ((alpha : Real) / 2)))

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F] in
private theorem lapDuhamelNormConst_term_nonneg
    {alpha : NNReal} (halpha0 : 0 < alpha) (K : NNReal) {T : Real} (hT : 0 ≤ T)
    (i : Fin (Module.finrank Real V)) :
    0 ≤ d2DuhamelHolderConst alpha
      ((stdOrthonormalBasis Real V) i)
      ((stdOrthonormalBasis Real V) i) K *
        ((2 / (alpha : Real)) * T ^ ((alpha : Real) / 2)) := by
  have halphaReal : 0 < (alpha : Real) := by exact_mod_cast halpha0
  have hconst : 0 ≤ d2DuhamelHolderConst alpha
      ((stdOrthonormalBasis Real V) i)
      ((stdOrthonormalBasis Real V) i) K := by
    unfold d2DuhamelHolderConst
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) K.coe_nonneg)
      (heatC2Holder_nonneg (V := V) alpha)
  exact mul_nonneg hconst
    (mul_nonneg (div_nonneg (by norm_num) halphaReal.le)
      (Real.rpow_nonneg hT _))

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F] in
theorem lapDuhamelParabolicHolderConst_nonneg {alpha : NNReal}
    (halpha : alpha ≤ 1) (K : NNReal) :
    0 ≤ lapDuhamelParabolicHolderConst (V := V) alpha K := by
  unfold lapDuhamelParabolicHolderConst
  exact Finset.sum_nonneg fun i _ ↦
    d2DuhamelParabolicHolderConst_nonneg halpha _ _ K

theorem heatLapDuhamel_norm_le_of_holder
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {T : Real} (hT : 0 ≤ T) (f : Real → V → F)
    (hf : ∀ r ∈ Icc (0 : Real) T, HolderWith K alpha (f r))
    (hmeas : ∀ t ∈ Ioc (0 : Real) T, ∀ x : V,
      ∀ i : Fin (Module.finrank Real V),
      AEStronglyMeasurable
        (fun r : Real ↦ heatD2Convolution (t - r)
          ((stdOrthonormalBasis Real V) i)
          ((stdOrthonormalBasis Real V) i) (f r) x)
        (volume.restrict (uIoc (0 : Real) t)))
    {t : Real} (ht : t ∈ Ioc (0 : Real) T) (x : V) :
    ‖heatLapDuhamel t f x‖ ≤ lapDuhamelNormConst (V := V) alpha K T := by
  unfold heatLapDuhamel
  calc
    ‖∑ i : Fin (Module.finrank Real V),
        heatD2Duhamel t ((stdOrthonormalBasis Real V) i)
          ((stdOrthonormalBasis Real V) i) f x‖ ≤
      ∑ i : Fin (Module.finrank Real V),
        ‖heatD2Duhamel t ((stdOrthonormalBasis Real V) i)
          ((stdOrthonormalBasis Real V) i) f x‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin (Module.finrank Real V),
        d2DuhamelHolderConst alpha
          ((stdOrthonormalBasis Real V) i)
          ((stdOrthonormalBasis Real V) i) K *
            ((2 / (alpha : Real)) * T ^ ((alpha : Real) / 2)) := by
      gcongr with i
      have hslice : ∀ r ∈ Icc (0 : Real) t, HolderWith K alpha (f r) := by
        intro r hr
        exact hf r ⟨hr.1, hr.2.trans ht.2⟩
      have hraw := heatD2Duhamel_norm_of_holder halpha0 halpha1 ht.1 f hslice
        ((stdOrthonormalBasis Real V) i) ((stdOrthonormalBasis Real V) i) x
        (hmeas t ht x i)
      refine hraw.trans ?_
      have hcoef : 0 ≤ d2DuhamelHolderConst alpha
          ((stdOrthonormalBasis Real V) i)
          ((stdOrthonormalBasis Real V) i) K := by
        unfold d2DuhamelHolderConst
        exact mul_nonneg
          (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) K.coe_nonneg)
          (heatC2Holder_nonneg (V := V) alpha)
      have hfactor : 0 ≤ 2 / (alpha : Real) := by
        exact div_nonneg (by norm_num) (by exact_mod_cast halpha0.le)
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow ht.1.le ht.2 (by positivity)) hfactor) hcoef
    _ = lapDuhamelNormConst (V := V) alpha K T := by
      unfold lapDuhamelNormConst
      push_cast
      apply Finset.sum_congr rfl
      intro i _
      exact (Real.coe_toNNReal _
        (lapDuhamelNormConst_term_nonneg (V := V) halpha0 K hT i)).symm

theorem heatLapDuhamel_parabolic_norm_sub_le_of_holder
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {s t : Real} (hs : 0 < s) (ht : 0 < t)
    (f : Real → V → F)
    (hf : ∀ r ∈ Icc (0 : Real) (max s t), HolderWith K alpha (f r))
    (x y : V)
    (hmeas : ∀ q ∈ ({s, t} : Set Real), ∀ z ∈ ({x, y} : Set V),
      ∀ i : Fin (Module.finrank Real V),
      AEStronglyMeasurable
        (fun r : Real ↦ heatD2Convolution (q - r) ((stdOrthonormalBasis Real V) i)
          ((stdOrthonormalBasis Real V) i) (f r) z)
        (volume.restrict (uIoc (0 : Real) q))) :
    ‖heatLapDuhamel t f x - heatLapDuhamel s f y‖ ≤
      lapDuhamelParabolicHolderConst (V := V) alpha K *
        (max (|t - s| ^ (1 / 2 : Real)) ‖x - y‖) ^ (alpha : Real) := by
  let D : Real := max (|t - s| ^ (1 / 2 : Real)) ‖x - y‖
  unfold heatLapDuhamel
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ i : Fin (Module.finrank Real V),
        (heatD2Duhamel t ((stdOrthonormalBasis Real V) i)
          ((stdOrthonormalBasis Real V) i) f x -
        heatD2Duhamel s ((stdOrthonormalBasis Real V) i)
          ((stdOrthonormalBasis Real V) i) f y)‖ ≤
      ∑ i : Fin (Module.finrank Real V),
        ‖heatD2Duhamel t ((stdOrthonormalBasis Real V) i)
          ((stdOrthonormalBasis Real V) i) f x -
        heatD2Duhamel s ((stdOrthonormalBasis Real V) i)
          ((stdOrthonormalBasis Real V) i) f y‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin (Module.finrank Real V),
        d2DuhamelParabolicHolderConst alpha ((stdOrthonormalBasis Real V) i)
          ((stdOrthonormalBasis Real V) i) K * D ^ (alpha : Real) := by
      gcongr with i
      exact heatD2Duhamel_parabolic_norm_sub_le_of_holder
        halpha0 halpha1 hs ht f hf _ _ x y
        (hmeas t (by simp) x (by simp) i)
        (hmeas t (by simp) y (by simp) i)
        (hmeas s (by simp) y (by simp) i)
    _ = lapDuhamelParabolicHolderConst (V := V) alpha K *
        D ^ (alpha : Real) := by
      unfold lapDuhamelParabolicHolderConst
      exact (Finset.sum_mul Finset.univ
        (fun i : Fin (Module.finrank Real V) ↦
          d2DuhamelParabolicHolderConst alpha ((stdOrthonormalBasis Real V) i)
            ((stdOrthonormalBasis Real V) i) K)
        (D ^ (alpha : Real))).symm

def heatLapDuhamelField (f : Real → V → F) : ParabolicPoint V → F :=
  fun p ↦ heatLapDuhamel p.time f p.space

theorem heatLapDuhamelField_holderOnWith_of_holder
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {T : Real} (f : Real → V → F)
    (hf : ∀ r ∈ Icc (0 : Real) T, HolderWith K alpha (f r))
    (hmeas : ∀ t ∈ Ioc (0 : Real) T, ∀ x : V,
      ∀ i : Fin (Module.finrank Real V),
      AEStronglyMeasurable
        (fun r : Real ↦ heatD2Convolution (t - r) ((stdOrthonormalBasis Real V) i)
          ((stdOrthonormalBasis Real V) i) (f r) x)
        (volume.restrict (uIoc (0 : Real) t))) :
    HolderOnWith (Real.toNNReal (lapDuhamelParabolicHolderConst (V := V) alpha K))
      alpha (heatLapDuhamelField f)
      (parabolicCylinder (Ioc (0 : Real) T) Set.univ) := by
  intro p hp q hq
  have hf' : ∀ r ∈ Icc (0 : Real) (max q.time p.time),
      HolderWith K alpha (f r) := by
    intro r hr
    exact hf r ⟨hr.1, hr.2.trans (max_le hq.1.2 hp.1.2)⟩
  have hreal := heatLapDuhamel_parabolic_norm_sub_le_of_holder
    halpha0 halpha1 hq.1.1 hp.1.1 f hf' p.space q.space
    (fun z hz a ha i ↦ hmeas z (by
      rcases hz with rfl | rfl
      · exact hq.1
      · exact hp.1) a i)
  have hp_repr : parabolicPoint p.time p.space = p := by
    rcases p with ⟨⟨pt⟩, px⟩
    rfl
  have hq_repr : parabolicPoint q.time q.space = q := by
    rcases q with ⟨⟨qt⟩, qx⟩
    rfl
  have hdist : dist p q =
      max (|p.time - q.time| ^ (1 / 2 : Real)) ‖p.space - q.space‖ := by
    rw [← hp_repr, ← hq_repr, dist_parabolicPoint, dist_eq_norm]
    simp only [parabolicPoint_time, parabolicPoint_space]
  change edist (heatLapDuhamel p.time f p.space) (heatLapDuhamel q.time f q.space) ≤ _
  rw [edist_dist, edist_dist, hdist, ENNReal.ofNNReal_toNNReal,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) alpha.coe_nonneg,
    ← ENNReal.ofReal_mul
      (lapDuhamelParabolicHolderConst_nonneg (V := V) halpha1.le K)]
  simpa only [dist_eq_norm] using ENNReal.ofReal_le_ofReal hreal

def heatDuhamelTimeDerivative (t : Real) (f : Real → V → F) (x : V) : F :=
  f t x + heatLapDuhamel t f x

def heatDuhamelTimeDerivativeField (f : Real → V → F) : ParabolicPoint V → F :=
  fun p ↦ heatDuhamelTimeDerivative p.time f p.space

theorem heatDuhamelTimeDerivativeField_holderWith_restrict_of_holder
    {alpha K C : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {T : Real} (f : Real → V → F)
    (hf : ∀ r ∈ Icc (0 : Real) T, HolderWith K alpha (f r))
    (hsource : HolderWith C alpha
      ((parabolicCylinder (Ioc (0 : Real) T) Set.univ).domRestrict
        (fun p ↦ f p.time p.space)))
    (hmeas : ∀ t ∈ Ioc (0 : Real) T, ∀ x : V,
      ∀ i : Fin (Module.finrank Real V),
      AEStronglyMeasurable
        (fun r : Real ↦ heatD2Convolution (t - r) ((stdOrthonormalBasis Real V) i)
          ((stdOrthonormalBasis Real V) i) (f r) x)
        (volume.restrict (uIoc (0 : Real) t))) :
    HolderWith (C + Real.toNNReal
      (lapDuhamelParabolicHolderConst (V := V) alpha K)) alpha
      ((parabolicCylinder (Ioc (0 : Real) T) Set.univ).domRestrict
        (heatDuhamelTimeDerivativeField f)) := by
  have hlap :=
    (heatLapDuhamelField_holderOnWith_of_holder halpha0 halpha1 f hf hmeas).holderWith
  intro p q
  simpa only [heatDuhamelTimeDerivativeField, heatDuhamelTimeDerivative,
    heatLapDuhamelField, Set.domRestrict_apply, Pi.add_apply, edist_dist] using
      (hsource.add hlap) p q

theorem parabolicTimeDerivative_norm_le_of_heatDuhamelTimeDerivative
    {alpha K B : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {T : Real} (hT : 0 ≤ T) (u f : Real → V → F)
    (hbound : ∀ r ∈ Icc (0 : Real) T, ∀ x : V, ‖f r x‖ ≤ B)
    (hf : ∀ r ∈ Icc (0 : Real) T, HolderWith K alpha (f r))
    (hrealize : ∀ p ∈ parabolicCylinder (Ioc (0 : Real) T) Set.univ,
      HasDerivAt (fun t : Real ↦ u t p.space)
        (heatDuhamelTimeDerivativeField f p) p.time)
    (hmeas : ∀ t ∈ Ioc (0 : Real) T, ∀ x : V,
      ∀ i : Fin (Module.finrank Real V),
      AEStronglyMeasurable
        (fun r : Real ↦ heatD2Convolution (t - r)
          ((stdOrthonormalBasis Real V) i)
          ((stdOrthonormalBasis Real V) i) (f r) x)
        (volume.restrict (uIoc (0 : Real) t)))
    (p : ParabolicPoint V)
    (hp : p ∈ parabolicCylinder (Ioc (0 : Real) T) Set.univ) :
    ‖parabolicTimeDerivative u p‖ ≤
      B + lapDuhamelNormConst (V := V) alpha K T := by
  have heq : parabolicTimeDerivative u p = heatDuhamelTimeDerivativeField f p := by
    unfold parabolicTimeDerivative
    rw [(hrealize p hp).hasFDerivAt.fderiv]
    simp
  rw [heq]
  unfold heatDuhamelTimeDerivativeField heatDuhamelTimeDerivative
  exact (norm_add_le _ _).trans
    (add_le_add (hbound p.time ⟨hp.1.1.le, hp.1.2⟩ p.space)
      (heatLapDuhamel_norm_le_of_holder halpha0 halpha1 hT f hf hmeas hp.1 p.space))

theorem parabolicTimeDerivative_holderWith_restrict_of_heatDuhamelTimeDerivative
    {alpha K C : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {T : Real} (u f : Real → V → F)
    (hf : ∀ r ∈ Icc (0 : Real) T, HolderWith K alpha (f r))
    (hsource : HolderWith C alpha
      ((parabolicCylinder (Ioc (0 : Real) T) Set.univ).domRestrict
        (fun p ↦ f p.time p.space)))
    (hu : ∀ p ∈ parabolicCylinder (Ioc (0 : Real) T) Set.univ,
      HasDerivAt (fun t : Real ↦ u t p.space)
        (heatDuhamelTimeDerivativeField f p) p.time)
    (hmeas : ∀ t ∈ Ioc (0 : Real) T, ∀ x : V,
      ∀ i : Fin (Module.finrank Real V),
      AEStronglyMeasurable
        (fun r : Real ↦ heatD2Convolution (t - r) ((stdOrthonormalBasis Real V) i)
          ((stdOrthonormalBasis Real V) i) (f r) x)
        (volume.restrict (uIoc (0 : Real) t))) :
    HolderWith (C + Real.toNNReal
      (lapDuhamelParabolicHolderConst (V := V) alpha K)) alpha
      ((parabolicCylinder (Ioc (0 : Real) T) Set.univ).domRestrict
        (parabolicTimeDerivative u)) := by
  have hcand := heatDuhamelTimeDerivativeField_holderWith_restrict_of_holder
    halpha0 halpha1 f hf hsource hmeas
  have heq :
      (parabolicCylinder (Ioc (0 : Real) T) Set.univ).domRestrict
          (parabolicTimeDerivative u) =
        (parabolicCylinder (Ioc (0 : Real) T) Set.univ).domRestrict
          (heatDuhamelTimeDerivativeField f) := by
    funext p
    unfold parabolicTimeDerivative
    change (fderiv Real (fun t : Real ↦ u t p.1.space) p.1.time) 1 =
      heatDuhamelTimeDerivativeField f p.1
    rw [(hu p p.2).hasFDerivAt.fderiv]
    simp
  rw [heq]
  exact hcand

theorem eParabolicC2HolderGaugeOn_le_of_heat_potential_jets
    {alpha K Csource : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {T : Real} (u f : Real → V → F)
    (Cspatial : Nat → NNReal) (Ctime : NNReal)
    (hspatial : ∀ j < 3,
      ∀ p ∈ parabolicCylinder (Ioc (0 : Real) T) Set.univ,
        ‖parabolicSpatialJet j u p‖ ≤ Cspatial j)
    (htime : ∀ p ∈ parabolicCylinder (Ioc (0 : Real) T) Set.univ,
      ‖parabolicTimeDerivative u p‖ ≤ Ctime)
    (hf : ∀ r ∈ Icc (0 : Real) T, HolderWith K alpha (f r))
    (hsource : HolderWith Csource alpha
      ((parabolicCylinder (Ioc (0 : Real) T) Set.univ).domRestrict
        (fun p ↦ f p.time p.space)))
    (hspaceRealize : ∀ p ∈ parabolicCylinder (Ioc (0 : Real) T) Set.univ,
      ∀ m : Fin 2 → V,
        parabolicSpatialJet 2 u p m =
          heatD2Duhamel p.time (m 0) (m 1) f p.space)
    (htimeRealize : ∀ p ∈ parabolicCylinder (Ioc (0 : Real) T) Set.univ,
      HasDerivAt (fun t : Real ↦ u t p.space)
        (heatDuhamelTimeDerivativeField f p) p.time)
    (hmeas : ∀ t ∈ Ioc (0 : Real) T, ∀ x : V,
      ∀ β : Fin 2 → Fin (Module.finrank Real V),
      AEStronglyMeasurable
        (fun r : Real ↦ heatD2Convolution (t - r)
          ((stdOrthonormalBasis Real V) (β 0))
          ((stdOrthonormalBasis Real V) (β 1)) (f r) x)
        (volume.restrict (uIoc (0 : Real) t))) :
    eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Ioc (0 : Real) T) Set.univ) u ≤
      (∑ j ∈ Finset.range 3, (Cspatial j : ENNReal)) + Ctime +
        d2DuhamelJetHolderConst (V := V) alpha K +
          (Csource + Real.toNNReal
            (lapDuhamelParabolicHolderConst (V := V) alpha K)) := by
  apply eParabolicC2HolderGaugeOn_le Cspatial Ctime
    (d2DuhamelJetHolderConst (V := V) alpha K)
    (Csource + Real.toNNReal
      (lapDuhamelParabolicHolderConst (V := V) alpha K)) hspatial htime
  · exact parabolicSpatialJet_two_holderWith_restrict_of_heatD2Duhamel
      halpha0 halpha1 u f hf hspaceRealize hmeas
  · exact parabolicTimeDerivative_holderWith_restrict_of_heatDuhamelTimeDerivative
      halpha0 halpha1 u f hf hsource htimeRealize (fun t ht x i => by
        simpa using hmeas t ht x (fun _ => i))

def heatPotentialC2HolderGaugeConst
    (alpha K B Csource C0 C1 : NNReal) (T : Real) : ENNReal :=
  C0 + C1 + d2DuhamelJetNormConst (V := V) alpha K T +
    (B + lapDuhamelNormConst (V := V) alpha K T) +
    d2DuhamelJetHolderConst (V := V) alpha K +
    (Csource + Real.toNNReal
      (lapDuhamelParabolicHolderConst (V := V) alpha K))

theorem eParabolicC2HolderGaugeOn_le_of_heat_potential_lower_jets
    {alpha K B Csource C0 C1 : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {T : Real} (hT : 0 ≤ T) (u f : Real → V → F)
    (hzero : ∀ p ∈ parabolicCylinder (Ioc (0 : Real) T) Set.univ,
      ‖parabolicSpatialJet 0 u p‖ ≤ C0)
    (hone : ∀ p ∈ parabolicCylinder (Ioc (0 : Real) T) Set.univ,
      ‖parabolicSpatialJet 1 u p‖ ≤ C1)
    (hbound : ∀ r ∈ Icc (0 : Real) T, ∀ x : V, ‖f r x‖ ≤ B)
    (hf : ∀ r ∈ Icc (0 : Real) T, HolderWith K alpha (f r))
    (hsource : HolderWith Csource alpha
      ((parabolicCylinder (Ioc (0 : Real) T) Set.univ).domRestrict
        (fun p ↦ f p.time p.space)))
    (hspaceRealize : ∀ p ∈ parabolicCylinder (Ioc (0 : Real) T) Set.univ,
      ∀ m : Fin 2 → V,
        parabolicSpatialJet 2 u p m =
          heatD2Duhamel p.time (m 0) (m 1) f p.space)
    (htimeRealize : ∀ p ∈ parabolicCylinder (Ioc (0 : Real) T) Set.univ,
      HasDerivAt (fun t : Real ↦ u t p.space)
        (heatDuhamelTimeDerivativeField f p) p.time)
    (hmeas : ∀ t ∈ Ioc (0 : Real) T, ∀ x : V,
      ∀ β : Fin 2 → Fin (Module.finrank Real V),
      AEStronglyMeasurable
        (fun r : Real ↦ heatD2Convolution (t - r)
          ((stdOrthonormalBasis Real V) (β 0))
          ((stdOrthonormalBasis Real V) (β 1)) (f r) x)
        (volume.restrict (uIoc (0 : Real) t))) :
    eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Ioc (0 : Real) T) Set.univ) u ≤
      heatPotentialC2HolderGaugeConst (V := V)
        alpha K B Csource C0 C1 T := by
  let Cspatial : Nat → NNReal := fun j =>
    match j with
    | 0 => C0
    | 1 => C1
    | _ => d2DuhamelJetNormConst (V := V) alpha K T
  have hspatial : ∀ j < 3,
      ∀ p ∈ parabolicCylinder (Ioc (0 : Real) T) Set.univ,
        ‖parabolicSpatialJet j u p‖ ≤ Cspatial j := by
    intro j hj p hp
    interval_cases j
    · exact hzero p hp
    · exact hone p hp
    · exact parabolicSpatialJet_two_norm_le_of_heatD2Duhamel
        halpha0 halpha1.le hT u f hf hspaceRealize hmeas p hp
  have htime : ∀ p ∈ parabolicCylinder (Ioc (0 : Real) T) Set.univ,
      ‖parabolicTimeDerivative u p‖ ≤
        B + lapDuhamelNormConst (V := V) alpha K T :=
    fun p hp => parabolicTimeDerivative_norm_le_of_heatDuhamelTimeDerivative
      halpha0 halpha1.le hT u f hbound hf htimeRealize
        (fun t ht x i => by simpa using hmeas t ht x (fun _ => i)) p hp
  have hraw := eParabolicC2HolderGaugeOn_le_of_heat_potential_jets
    halpha0 halpha1 u f Cspatial
    (B + lapDuhamelNormConst (V := V) alpha K T)
    hspatial htime hf hsource hspaceRealize htimeRealize hmeas
  unfold heatPotentialC2HolderGaugeConst
  convert hraw using 1
  norm_num [Cspatial, Finset.sum_range_succ]

theorem eParabolicC2HolderGaugeOn_heatDuhamel_le_of_lower_jets_of_time_realization
    {alpha K B Csource C0 C1 : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {T : Real} (hT : 0 ≤ T)
    (f : Real → BoundedContinuousFunction V F)
    (hzero : ∀ p ∈ parabolicCylinder (Ioc (0 : Real) T) Set.univ,
      ‖parabolicSpatialJet 0 (fun t x => heatDuhamel t f x) p‖ ≤ C0)
    (hone : ∀ p ∈ parabolicCylinder (Ioc (0 : Real) T) Set.univ,
      ‖parabolicSpatialJet 1 (fun t x => heatDuhamel t f x) p‖ ≤ C1)
    (hbound : ∀ r ∈ Icc (0 : Real) T, ‖f r‖ ≤ B)
    (hf : ∀ r ∈ Icc (0 : Real) T, HolderWith K alpha (f r))
    (hsource : HolderWith Csource alpha
      ((parabolicCylinder (Ioc (0 : Real) T) Set.univ).domRestrict
        (fun p => f p.time p.space)))
    (htimeRealize : ∀ p ∈ parabolicCylinder (Ioc (0 : Real) T) Set.univ,
      HasDerivAt (fun t : Real => heatDuhamel t f p.space)
        (heatDuhamelTimeDerivativeField (fun r x => f r x) p) p.time)
    (hmeas0 : ∀ t ∈ Ioc (0 : Real) T, ∀ z : V,
      AEStronglyMeasurable
        (fun s : Real => heatSup (t - s) (f s) z)
        (volume.restrict (uIoc (0 : Real) t)))
    (hmeas1 : ∀ t ∈ Ioc (0 : Real) T, ∀ z : V,
      AEStronglyMeasurable
        (fun s : Real => heatSupGradient (t - s) (f s) z)
        (volume.restrict (uIoc (0 : Real) t)))
    (hmeas2 : ∀ t ∈ Ioc (0 : Real) T, ∀ z : V,
      AEStronglyMeasurable
        (fun s : Real => heatSupHessian (t - s) (f s) z)
        (volume.restrict (uIoc (0 : Real) t))) :
    eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Ioc (0 : Real) T) Set.univ)
      (fun t x => heatDuhamel t f x) ≤
      heatPotentialC2HolderGaugeConst (V := V)
        alpha K B Csource C0 C1 T := by
  apply eParabolicC2HolderGaugeOn_le_of_heat_potential_lower_jets
    halpha0 halpha1 hT (fun t x => heatDuhamel t f x) (fun r x => f r x)
      hzero hone
  · intro r hr x
    exact (f r).norm_coe_le_norm x |>.trans (hbound r hr)
  · exact hf
  · exact hsource
  · intro p hp m
    exact heatDuhamel_parabolicSpatialJet_two halpha0 halpha1.le hp.1.1 f
      (fun s hs => hbound s ⟨hs.1, hs.2.trans hp.1.2⟩)
      (fun s hs => hf s ⟨hs.1, hs.2.trans hp.1.2⟩)
      (hmeas0 p.time hp.1) (hmeas1 p.time hp.1)
      (hmeas2 p.time hp.1) p.space m
  · exact htimeRealize
  · intro t ht x β
    exact heatD2Convolution_time_aestronglyMeasurable ht.1 f
      (hmeas2 t ht) ((stdOrthonormalBasis Real V) (β 0))
      ((stdOrthonormalBasis Real V) (β 1)) x

end Convolution

end HeatEquation
