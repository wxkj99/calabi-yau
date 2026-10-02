-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Parabolic/Euclidean/HeatPotential/Regularity.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Parabolic.Euclidean.HeatKernel.Approximation
public import CalabiYau.Analysis.Parabolic.Euclidean.HeatKernel.Derivatives.Cancellation
public import CalabiYau.Analysis.Parabolic.Euclidean.HeatKernel.Derivatives.Higher
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Convolution

@[expose] public section

-- and its private helpers occur in public declarations.

noncomputable section

open MeasureTheory Real Set Filter
open scoped RealInnerProductSpace Topology

namespace HeatEquation

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

def heatD2SmulRightMap (t : Real) (x : V) (f : F) :
    V →L[Real] (V →L[Real] F) :=
  ((ContinuousLinearMap.smulRightL Real V F).flip f).comp
    (heatD2CurriedMap t x)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] [CompleteSpace F] in
@[simp] theorem heatD2SmulRightMap_apply (t : Real) (x w v : V) (f : F) :
    heatD2SmulRightMap t x f w v = heatD2 t v w x • f := by
  simp [heatD2SmulRightMap]

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] [CompleteSpace F] in
theorem heatD1SmulRight_hasFDerivAt (t : Real) (x : V) (f : F) :
    HasFDerivAt (fun y : V => (heatD1Map t y).smulRight f)
      (heatD2SmulRightMap t x f) x := by
  have h := ((ContinuousLinearMap.smulRightL Real V F).flip f).hasFDerivAt.comp
    x (heatD1Map_hasFDeriv t x)
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] [CompleteSpace F] in
theorem heatD2SmulRightMap_norm_le {t : Real} (ht : 0 < t) (x : V) (f : F) :
    ‖heatD2SmulRightMap t x f‖ ≤ heatD2Maj t x * ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (heatD2SmulRightMap t x f)
    (mul_nonneg (heatD2Maj_nonneg ht x) (norm_nonneg f))
  intro w
  apply ContinuousLinearMap.opNorm_le_bound (heatD2SmulRightMap t x f w)
    (mul_nonneg
      (mul_nonneg (heatD2Maj_nonneg ht x) (norm_nonneg f))
      (norm_nonneg w))
  intro v
  rw [heatD2SmulRightMap_apply, norm_smul]
  calc
    ‖heatD2 t v w x‖ * ‖f‖ ≤
        (‖v‖ * ‖w‖ * heatD2Maj t x) * ‖f‖ :=
      mul_le_mul_of_nonneg_right (heatD2_bound ht v w x) (norm_nonneg f)
    _ = heatD2Maj t x * ‖f‖ * ‖w‖ * ‖v‖ := by ring

private def heatD1LocalMajor (t : Real) (x y : V) : Real :=
  ((heatScale t) ^ Module.finrank Real V)⁻¹ * (heatScale t)⁻¹ *
    (baseHeatMass V)⁻¹ * Real.exp (1 / 4 : Real) *
      ((1 + ‖(heatScale t)⁻¹ • (x - y)‖) *
        Real.exp (-(1 / 8 : Real) * ‖(heatScale t)⁻¹ • (x - y)‖ ^ 2))

private theorem heatD1LocalMajor_int {t : Real} (ht : 0 < t) (x : V) :
    Integrable (heatD1LocalMajor (V := V) t x) := by
  let g : V → Real := fun z =>
    (1 + ‖z‖) * Real.exp (-(1 / 8 : Real) * ‖z‖ ^ 2)
  have h0 := gaussMoment_int (V := V) 0
    (by norm_num : (0 : Real) < (1 / 8 : Real))
  have h1 := gaussMoment_int (V := V) 1
    (by norm_num : (0 : Real) < (1 / 8 : Real))
  have hg : Integrable g := by
    have heq : g = fun z : V =>
        ‖z‖ ^ 0 * Real.exp (-(1 / 8 : Real) * ‖z‖ ^ 2) +
          ‖z‖ ^ 1 * Real.exp (-(1 / 8 : Real) * ‖z‖ ^ 2) := by
      funext z
      simp only [g, pow_zero, one_mul, pow_one]
      ring
    rw [heq]
    exact h0.add h1
  have hs := (hg.comp_smul (inv_ne_zero (heatScale_pos ht).ne')).comp_sub_left x
  exact (hs.const_mul
    (((heatScale t) ^ Module.finrank Real V)⁻¹ * (heatScale t)⁻¹ *
      (baseHeatMass V)⁻¹ * Real.exp (1 / 4 : Real))).congr
        (Filter.Eventually.of_forall fun _ => rfl)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] [CompleteSpace F] in
omit [FiniteDimensional ℝ V] in
private theorem heatD1Maj_le_localMajor {t : Real} (ht : 0 < t)
    (x₀ y : V) {x : V} (hx : x ∈ Metric.ball x₀ (heatScale t)) :
    heatD1Maj t (x - y) ≤ heatD1LocalMajor (V := V) t x₀ y := by
  let r : Real := (heatScale t)⁻¹
  let a : V := r • (x₀ - y)
  let b : V := r • (x - x₀)
  let z : V := r • (x - y)
  have hr : 0 < r := inv_pos.mpr (heatScale_pos ht)
  have hz : z = a + b := by
    unfold z a b
    rw [← smul_add]
    congr 1
    abel
  have hb : ‖b‖ < 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    change (heatScale t)⁻¹ * ‖x - x₀‖ < 1
    rw [inv_mul_lt_one₀ (heatScale_pos ht)]
    simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hx
  have hz_le : ‖z‖ ≤ ‖a‖ + 1 := by
    rw [hz]
    calc
      ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
      _ ≤ ‖a‖ + 1 := by gcongr
  have ha_le : ‖a‖ ≤ ‖z‖ + 1 := by
    have ha : a = z - b := by rw [hz]; abel
    rw [ha]
    calc
      ‖z - b‖ ≤ ‖z‖ + ‖b‖ := norm_sub_le z b
      _ ≤ ‖z‖ + 1 := by gcongr
  have ha_sq : ‖a‖ ^ 2 ≤ 2 * ‖z‖ ^ 2 + 2 := by
    have hsq : ‖a‖ ^ 2 ≤ (‖z‖ + 1) ^ 2 := by
      exact sq_le_sq₀ (norm_nonneg a) (by positivity) |>.2 ha_le
    nlinarith [sq_nonneg (‖z‖ - 1)]
  have hexpArg : -(1 / 4 : Real) * ‖z‖ ^ 2 ≤
      1 / 4 - (1 / 8 : Real) * ‖a‖ ^ 2 := by
    nlinarith
  have hexp : Real.exp (-(1 / 4 : Real) * ‖z‖ ^ 2) ≤
      Real.exp (1 / 4 : Real) * Real.exp (-(1 / 8 : Real) * ‖a‖ ^ 2) := by
    calc
      Real.exp (-(1 / 4 : Real) * ‖z‖ ^ 2) ≤
          Real.exp (1 / 4 - (1 / 8 : Real) * ‖a‖ ^ 2) :=
        Real.exp_le_exp.mpr hexpArg
      _ = Real.exp (1 / 4 : Real) *
          Real.exp (-(1 / 8 : Real) * ‖a‖ ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hbase : baseD1Maj z ≤
      (baseHeatMass V)⁻¹ * Real.exp (1 / 4 : Real) *
        ((1 + ‖a‖) * Real.exp (-(1 / 8 : Real) * ‖a‖ ^ 2)) := by
    have hmass : 0 ≤ (baseHeatMass V)⁻¹ :=
      inv_nonneg.mpr (baseHeatMass_pos (V := V)).le
    have hexpZ : 0 ≤ Real.exp (-(4 : Real)⁻¹ * ‖z‖ ^ 2) :=
      (Real.exp_pos _).le
    have hleft : 0 ≤ (2 : Real)⁻¹ * (‖a‖ + 1) :=
      mul_nonneg (by positivity) (add_nonneg (norm_nonneg a) zero_le_one)
    let Q : Real := (baseHeatMass V)⁻¹ * (‖a‖ + 1) *
      (Real.exp (1 / 4 : Real) *
        Real.exp (-(1 / 8 : Real) * ‖a‖ ^ 2))
    have hQ : 0 ≤ Q := by
      unfold Q
      positivity
    unfold baseD1Maj baseHeat
    calc
      (2 : Real)⁻¹ * ‖z‖ *
          ((baseHeatMass V)⁻¹ * Real.exp (-(4 : Real)⁻¹ * ‖z‖ ^ 2)) ≤
        (2 : Real)⁻¹ * (‖a‖ + 1) *
          ((baseHeatMass V)⁻¹ * Real.exp (-(4 : Real)⁻¹ * ‖z‖ ^ 2)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hz_le (by positivity))
          (mul_nonneg hmass hexpZ)
      _ ≤ (2 : Real)⁻¹ * (‖a‖ + 1) *
          ((baseHeatMass V)⁻¹ *
            (Real.exp (1 / 4 : Real) *
              Real.exp (-(1 / 8 : Real) * ‖a‖ ^ 2))) := by
        have hexp' : Real.exp (-(4 : Real)⁻¹ * ‖z‖ ^ 2) ≤
            Real.exp (1 / 4 : Real) *
              Real.exp (-(1 / 8 : Real) * ‖a‖ ^ 2) := by
          simpa only [one_div] using hexp
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hexp' hmass) hleft
      _ = (2 : Real)⁻¹ * Q := by unfold Q; ring
      _ ≤ 1 * Q := mul_le_mul_of_nonneg_right (by norm_num) hQ
      _ = (baseHeatMass V)⁻¹ * Real.exp (1 / 4 : Real) *
          ((1 + ‖a‖) * Real.exp (-(1 / 8 : Real) * ‖a‖ ^ 2)) := by
        unfold Q
        ring
  have hfront : 0 ≤
      ((heatScale t) ^ Module.finrank Real V)⁻¹ * (heatScale t)⁻¹ :=
    mul_nonneg
      (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _))
      (inv_nonneg.mpr (heatScale_pos ht).le)
  unfold heatD1Maj heatD1LocalMajor
  change _ * baseD1Maj z ≤ _
  change _ ≤ _ * ((1 + ‖a‖) * _)
  simpa only [a, mul_assoc] using mul_le_mul_of_nonneg_left hbase hfront

private def heatD2LocalMajor (t : Real) (x y : V) : Real :=
  ((heatScale t) ^ Module.finrank Real V)⁻¹ * (heatScale t)⁻¹ *
    (heatScale t)⁻¹ * (baseHeatMass V)⁻¹ * Real.exp (1 / 4 : Real) *
      ((1 + ‖(heatScale t)⁻¹ • (x - y)‖ ^ 2) *
        Real.exp (-(1 / 8 : Real) * ‖(heatScale t)⁻¹ • (x - y)‖ ^ 2))

private theorem heatD2LocalMajor_int {t : Real} (ht : 0 < t) (x : V) :
    Integrable (heatD2LocalMajor (V := V) t x) := by
  let g : V → Real := fun z =>
    (1 + ‖z‖ ^ 2) * Real.exp (-(1 / 8 : Real) * ‖z‖ ^ 2)
  have h0 := gaussMoment_int (V := V) 0
    (by norm_num : (0 : Real) < (1 / 8 : Real))
  have h2 := gaussMoment_int (V := V) 2
    (by norm_num : (0 : Real) < (1 / 8 : Real))
  have hg : Integrable g := by
    have heq : g = fun z : V =>
        ‖z‖ ^ 0 * Real.exp (-(1 / 8 : Real) * ‖z‖ ^ 2) +
          ‖z‖ ^ 2 * Real.exp (-(1 / 8 : Real) * ‖z‖ ^ 2) := by
      funext z
      simp only [g, pow_zero, one_mul]
      ring
    rw [heq]
    exact h0.add h2
  have hs := (hg.comp_smul (inv_ne_zero (heatScale_pos ht).ne')).comp_sub_left x
  exact (hs.const_mul
    (((heatScale t) ^ Module.finrank Real V)⁻¹ * (heatScale t)⁻¹ *
      (heatScale t)⁻¹ * (baseHeatMass V)⁻¹ * Real.exp (1 / 4 : Real))).congr
        (Filter.Eventually.of_forall fun _ => rfl)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] [CompleteSpace F] in
omit [FiniteDimensional ℝ V] in
private theorem heatD2Maj_le_localMajor {t : Real} (ht : 0 < t)
    (x₀ y : V) {x : V} (hx : x ∈ Metric.ball x₀ (heatScale t)) :
    heatD2Maj t (x - y) ≤ heatD2LocalMajor (V := V) t x₀ y := by
  let r : Real := (heatScale t)⁻¹
  let a : V := r • (x₀ - y)
  let b : V := r • (x - x₀)
  let z : V := r • (x - y)
  have hr : 0 < r := inv_pos.mpr (heatScale_pos ht)
  have hz : z = a + b := by
    unfold z a b
    rw [← smul_add]
    congr 1
    abel
  have hb : ‖b‖ < 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    change (heatScale t)⁻¹ * ‖x - x₀‖ < 1
    rw [inv_mul_lt_one₀ (heatScale_pos ht)]
    simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hx
  have hz_le : ‖z‖ ≤ ‖a‖ + 1 := by
    rw [hz]
    calc
      ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
      _ ≤ ‖a‖ + 1 := by gcongr
  have ha_le : ‖a‖ ≤ ‖z‖ + 1 := by
    have ha : a = z - b := by rw [hz]; abel
    rw [ha]
    calc
      ‖z - b‖ ≤ ‖z‖ + ‖b‖ := norm_sub_le z b
      _ ≤ ‖z‖ + 1 := by gcongr
  have hz_sq : ‖z‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 := by
    have hsq : ‖z‖ ^ 2 ≤ (‖a‖ + 1) ^ 2 :=
      sq_le_sq₀ (norm_nonneg z) (by positivity) |>.2 hz_le
    nlinarith [sq_nonneg (‖a‖ - 1)]
  have ha_sq : ‖a‖ ^ 2 ≤ 2 * ‖z‖ ^ 2 + 2 := by
    have hsq : ‖a‖ ^ 2 ≤ (‖z‖ + 1) ^ 2 :=
      sq_le_sq₀ (norm_nonneg a) (by positivity) |>.2 ha_le
    nlinarith [sq_nonneg (‖z‖ - 1)]
  have hpoly : (1 / 4 : Real) * ‖z‖ ^ 2 + 1 / 2 ≤ 1 + ‖a‖ ^ 2 := by
    nlinarith
  have hexpArg : -(1 / 4 : Real) * ‖z‖ ^ 2 ≤
      1 / 4 - (1 / 8 : Real) * ‖a‖ ^ 2 := by
    nlinarith
  have hexp : Real.exp (-(1 / 4 : Real) * ‖z‖ ^ 2) ≤
      Real.exp (1 / 4 : Real) * Real.exp (-(1 / 8 : Real) * ‖a‖ ^ 2) := by
    calc
      Real.exp (-(1 / 4 : Real) * ‖z‖ ^ 2) ≤
          Real.exp (1 / 4 - (1 / 8 : Real) * ‖a‖ ^ 2) :=
        Real.exp_le_exp.mpr hexpArg
      _ = Real.exp (1 / 4 : Real) *
          Real.exp (-(1 / 8 : Real) * ‖a‖ ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hbase : baseD2Maj z ≤
      (baseHeatMass V)⁻¹ * Real.exp (1 / 4 : Real) *
        ((1 + ‖a‖ ^ 2) * Real.exp (-(1 / 8 : Real) * ‖a‖ ^ 2)) := by
    have hmass : 0 ≤ (baseHeatMass V)⁻¹ :=
      inv_nonneg.mpr (baseHeatMass_pos (V := V)).le
    have hexpZ : 0 ≤ Real.exp (-(4 : Real)⁻¹ * ‖z‖ ^ 2) :=
      (Real.exp_pos _).le
    have hpolyNonneg : 0 ≤ 1 + ‖a‖ ^ 2 := by positivity
    unfold baseD2Maj baseHeat
    calc
      ((4 : Real)⁻¹ * ‖z‖ ^ 2 + (2 : Real)⁻¹) *
          ((baseHeatMass V)⁻¹ * Real.exp (-(4 : Real)⁻¹ * ‖z‖ ^ 2)) ≤
        (1 + ‖a‖ ^ 2) *
          ((baseHeatMass V)⁻¹ * Real.exp (-(4 : Real)⁻¹ * ‖z‖ ^ 2)) := by
        exact mul_le_mul_of_nonneg_right
          (by simpa only [one_div] using hpoly)
          (mul_nonneg hmass hexpZ)
      _ ≤ (1 + ‖a‖ ^ 2) *
          ((baseHeatMass V)⁻¹ *
            (Real.exp (1 / 4 : Real) *
              Real.exp (-(1 / 8 : Real) * ‖a‖ ^ 2))) := by
        have hexp' : Real.exp (-(4 : Real)⁻¹ * ‖z‖ ^ 2) ≤
            Real.exp (1 / 4 : Real) *
              Real.exp (-(1 / 8 : Real) * ‖a‖ ^ 2) := by
          simpa only [one_div] using hexp
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hexp' hmass) hpolyNonneg
      _ = (baseHeatMass V)⁻¹ * Real.exp (1 / 4 : Real) *
          ((1 + ‖a‖ ^ 2) * Real.exp (-(1 / 8 : Real) * ‖a‖ ^ 2)) := by
        ring
  have hfront : 0 ≤
      ((heatScale t) ^ Module.finrank Real V)⁻¹ * (heatScale t)⁻¹ *
        (heatScale t)⁻¹ := by
    exact mul_nonneg
      (mul_nonneg
        (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _))
        (inv_nonneg.mpr (heatScale_pos ht).le))
      (inv_nonneg.mpr (heatScale_pos ht).le)
  unfold heatD2Maj heatD2LocalMajor
  change _ * baseD2Maj z ≤ _
  change _ ≤ _ * ((1 + ‖a‖ ^ 2) * _)
  simpa only [a, mul_assoc] using mul_le_mul_of_nonneg_left hbase hfront

def heatSupGradient (t : Real) (u : BoundedContinuousFunction V F) (x : V) :
    V →L[Real] F :=
  ∫ y : V, (heatD1Map t (x - y)).smulRight (u y)

omit [CompleteSpace F] in
theorem heatSup_hasFDerivAt {t : Real} (ht : 0 < t)
    (u : BoundedContinuousFunction V F) (x : V) :
    HasFDerivAt (fun z : V => heatSup t u z) (heatSupGradient t u x) x := by
  let G : V → V → F := fun z y => heatKernel t (z - y) • u y
  let DG : V → V → V →L[Real] F := fun z y =>
    (heatD1Map t (z - y)).smulRight (u y)
  let bound : V → Real := fun y => ‖u‖ * heatD1LocalMajor (V := V) t x y
  have hs : Metric.ball x (heatScale t) ∈ 𝓝 x :=
    Metric.ball_mem_nhds x (heatScale_pos ht)
  have hGmeas : ∀ᶠ z in 𝓝 x,
      AEStronglyMeasurable (G z) (volume : Measure V) := by
    apply Filter.Eventually.of_forall
    intro z
    apply Continuous.aestronglyMeasurable
    unfold G heatKernel baseHeat baseHeatMass heatScale
    fun_prop
  have hGint : Integrable (G x) := by
    refine (((heatKernel_int (V := V) ht).norm.comp_sub_left x).mul_const ‖u‖).mono' ?_ ?_
    · apply Continuous.aestronglyMeasurable
      unfold G heatKernel baseHeat baseHeatMass heatScale
      fun_prop
    filter_upwards with y
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (u.norm_coe_le_norm y)
      (norm_nonneg (heatKernel t (x - y)))
  have hDGmeas : AEStronglyMeasurable (DG x) (volume : Measure V) := by
    apply Continuous.aestronglyMeasurable
    unfold DG heatD1Map baseD1Map baseHeat baseHeatMass heatScale
    fun_prop
  have hbound : ∀ᵐ y ∂(volume : Measure V), ∀ z ∈ Metric.ball x (heatScale t),
      ‖DG z y‖ ≤ bound y := by
    apply Filter.Eventually.of_forall
    intro y z hz
    calc
      ‖DG z y‖ ≤ ‖heatD1Map t (z - y)‖ * ‖u y‖ := by
        unfold DG
        rw [ContinuousLinearMap.norm_smulRight_apply]
      _ ≤ heatD1Maj t (z - y) * ‖u‖ := by
        exact mul_le_mul (heatD1Map_norm_le ht (z - y))
          (u.norm_coe_le_norm y) (norm_nonneg _) (heatD1Maj_nonneg ht _)
      _ ≤ ‖u‖ * heatD1LocalMajor (V := V) t x y := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left
          (heatD1Maj_le_localMajor ht x y hz) (norm_nonneg u)
      _ = bound y := rfl
  have hboundInt : Integrable bound :=
    (heatD1LocalMajor_int (V := V) ht x).const_mul ‖u‖
  have hdiff : ∀ᵐ y ∂(volume : Measure V), ∀ z ∈ Metric.ball x (heatScale t),
      HasFDerivAt (G · y) (DG z y) z := by
    apply Filter.Eventually.of_forall
    intro y z hz
    have hsub : HasFDerivAt (fun q : V => q - y)
        (ContinuousLinearMap.id Real V) z :=
      (hasFDerivAt_id z).sub_const y
    unfold G DG
    simpa using ((heatKernel_hasFDeriv (z - y)).comp z hsub).smul_const (u y)
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := G) (F' := DG) (bound := bound) hs hGmeas hGint hDGmeas
      hbound hboundInt hdiff
  have hfun : (fun z : V => ∫ y : V, G z y) = fun z : V => heatSup t u z := by
    funext z
    unfold G heatSup supKernel
    rw [← MeasureTheory.convolution_lsmul_swap]
    rfl
  rw [hfun] at h
  simpa only [DG, heatSupGradient] using h

def heatSupHessian (t : Real) (u : BoundedContinuousFunction V F) (x : V) :
    V →L[Real] (V →L[Real] F) :=
  ∫ y : V, heatD2SmulRightMap t (x - y) (u y)

omit [CompleteSpace F] in
theorem heatSupGradient_hasFDerivAt {t : Real} (ht : 0 < t)
    (u : BoundedContinuousFunction V F) (x : V) :
    HasFDerivAt (heatSupGradient t u) (heatSupHessian t u x) x := by
  let G : V → V → V →L[Real] F := fun z y =>
    (heatD1Map t (z - y)).smulRight (u y)
  let DG : V → V → V →L[Real] (V →L[Real] F) := fun z y =>
    heatD2SmulRightMap t (z - y) (u y)
  let bound : V → Real := fun y => ‖u‖ * heatD2LocalMajor (V := V) t x y
  let : SecondCountableTopologyEither V (V →L[Real] (V →L[Real] F)) :=
    secondCountableTopologyEither_of_left V _
  have hs : Metric.ball x (heatScale t) ∈ 𝓝 x :=
    Metric.ball_mem_nhds x (heatScale_pos ht)
  have hGmeas : ∀ᶠ z in 𝓝 x,
      AEStronglyMeasurable (G z) (volume : Measure V) := by
    apply Filter.Eventually.of_forall
    intro z
    apply Continuous.aestronglyMeasurable
    unfold G heatD1Map baseD1Map baseHeat baseHeatMass heatScale
    fun_prop
  have hGint : Integrable (G x) := by
    refine (((heatD1Maj_int (V := V) ht).comp_sub_left x).const_mul ‖u‖).mono'
      ?_ ?_
    · apply Continuous.aestronglyMeasurable
      unfold G heatD1Map baseD1Map baseHeat baseHeatMass heatScale
      fun_prop
    filter_upwards with y
    calc
      ‖G x y‖ = ‖heatD1Map t (x - y)‖ * ‖u y‖ := by
        unfold G
        rw [ContinuousLinearMap.norm_smulRight_apply]
      _ ≤ heatD1Maj t (x - y) * ‖u‖ :=
        mul_le_mul (heatD1Map_norm_le ht (x - y))
          (u.norm_coe_le_norm y) (norm_nonneg _) (heatD1Maj_nonneg ht _)
      _ = ‖u‖ * heatD1Maj t (x - y) := by ring
  have hDGmeas : AEStronglyMeasurable (DG x) (volume : Measure V) := by
    apply Continuous.aestronglyMeasurable
    unfold DG heatD2SmulRightMap heatD2CurriedMap baseD2CurriedMap
      baseHeat baseHeatMass heatScale
    fun_prop
  have hbound : ∀ᵐ y ∂(volume : Measure V), ∀ z ∈ Metric.ball x (heatScale t),
      ‖DG z y‖ ≤ bound y := by
    apply Filter.Eventually.of_forall
    intro y z hz
    calc
      ‖DG z y‖ ≤ heatD2Maj t (z - y) * ‖u y‖ := by
        unfold DG
        exact heatD2SmulRightMap_norm_le ht (z - y) (u y)
      _ ≤ heatD2Maj t (z - y) * ‖u‖ := by
        exact mul_le_mul_of_nonneg_left (u.norm_coe_le_norm y)
          (heatD2Maj_nonneg ht _)
      _ ≤ ‖u‖ * heatD2LocalMajor (V := V) t x y := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left
          (heatD2Maj_le_localMajor ht x y hz) (norm_nonneg u)
      _ = bound y := rfl
  have hboundInt : Integrable bound :=
    (heatD2LocalMajor_int (V := V) ht x).const_mul ‖u‖
  have hdiff : ∀ᵐ y ∂(volume : Measure V), ∀ z ∈ Metric.ball x (heatScale t),
      HasFDerivAt (G · y) (DG z y) z := by
    apply Filter.Eventually.of_forall
    intro y z hz
    have hsub : HasFDerivAt (fun q : V => q - y)
        (ContinuousLinearMap.id Real V) z :=
      (hasFDerivAt_id z).sub_const y
    change HasFDerivAt (fun q : V => (heatD1Map t (q - y)).smulRight (u y))
      (heatD2SmulRightMap t (z - y) (u y)) z
    have hcomp := (heatD1SmulRight_hasFDerivAt t (z - y) (u y)).comp z hsub
    exact (hcomp.congr_fderiv (by ext; simp)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := G) (F' := DG) (bound := bound) hs hGmeas hGint hDGmeas
      hbound hboundInt hdiff
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)

omit [CompleteSpace F] in
theorem heatSup_iteratedFDeriv_two_apply {t : Real} (ht : 0 < t)
    (u : BoundedContinuousFunction V F) (x : V) (m : Fin 2 → V) :
    iteratedFDeriv Real 2 (fun z : V => heatSup t u z) x m =
      heatSupHessian t u x (m 0) (m 1) := by
  rw [iteratedFDeriv_two_apply]
  have hgrad : fderiv Real (fun z : V => heatSup t u z) = heatSupGradient t u := by
    funext z
    exact (heatSup_hasFDerivAt ht u z).fderiv
  rw [hgrad, (heatSupGradient_hasFDerivAt ht u x).fderiv]

omit [CompleteSpace F] in
theorem heatSupGradient_apply {t : Real} (ht : 0 < t)
    (u : BoundedContinuousFunction V F) (x v : V) :
    heatSupGradient t u x v = heatD1Sup t v u x := by
  have hInt : Integrable
      (fun y : V => (heatD1Map t (x - y)).smulRight (u y)) := by
    refine (((heatD1Maj_int (V := V) ht).comp_sub_left x).const_mul ‖u‖).mono'
      ?_ ?_
    · apply Continuous.aestronglyMeasurable
      unfold heatD1Map baseD1Map baseHeat baseHeatMass heatScale
      fun_prop
    filter_upwards with y
    rw [ContinuousLinearMap.norm_smulRight_apply]
    calc
      ‖heatD1Map t (x - y)‖ * ‖u y‖ ≤
          heatD1Maj t (x - y) * ‖u‖ :=
        mul_le_mul (heatD1Map_norm_le ht (x - y))
          (u.norm_coe_le_norm y) (norm_nonneg _) (heatD1Maj_nonneg ht _)
      _ = ‖u‖ * heatD1Maj t (x - y) := by ring
  unfold heatSupGradient heatD1Sup supKernel
  rw [ContinuousLinearMap.integral_apply hInt v]
  simp only [ContinuousLinearMap.smulRight_apply, heatD1Map_apply]
  change (∫ y : V, heatD1 t v (x - y) • u y) =
    ∫ y : V, heatD1 t v y • u (x - y)
  rw [← MeasureTheory.convolution_lsmul_swap]
  rfl

def heatD2ConvolutionMap (t : Real) (v : V)
    (u : BoundedContinuousFunction V F) (x : V) : V →L[Real] F :=
  ∫ y : V, (heatD2Map t v (x - y)).smulRight (u y)

omit [CompleteSpace F] in
@[simp] theorem heatD2ConvolutionMap_apply {t : Real} (ht : 0 < t) (v : V)
    (u : BoundedContinuousFunction V F) (x w : V) :
    heatD2ConvolutionMap t v u x w = heatD2Convolution t v w u x := by
  have hInt : Integrable
      (fun y : V => (heatD2Map t v (x - y)).smulRight (u y)) := by
    refine ((((heatD2Maj_int (V := V) ht).comp_sub_left x).const_mul ‖v‖).const_mul
      ‖u‖).mono' ?_ ?_
    · apply Continuous.aestronglyMeasurable
      unfold heatD2Map baseD2Map baseHeat baseHeatMass heatScale
      fun_prop
    filter_upwards with y
    rw [ContinuousLinearMap.norm_smulRight_apply]
    calc
      ‖heatD2Map t v (x - y)‖ * ‖u y‖ ≤
          (‖v‖ * heatD2Maj t (x - y)) * ‖u‖ :=
        mul_le_mul (heatD2Map_norm_le ht v (x - y))
          (u.norm_coe_le_norm y) (norm_nonneg _)
          (mul_nonneg (norm_nonneg v) (heatD2Maj_nonneg ht _))
      _ = ‖u‖ * (‖v‖ * heatD2Maj t (x - y)) := by ring
  unfold heatD2ConvolutionMap heatD2Convolution
  rw [ContinuousLinearMap.integral_apply hInt w]
  simp only [ContinuousLinearMap.smulRight_apply, heatD2Map_apply]
  change (∫ y : V, heatD2 t v w (x - y) • u y) =
    ∫ y : V, heatD2 t v w y • u (x - y)
  rw [← MeasureTheory.convolution_lsmul_swap]
  rfl

omit [CompleteSpace F] in
theorem heatD1Sup_hasFDerivAt {t : Real} (ht : 0 < t) (v : V)
    (u : BoundedContinuousFunction V F) (x : V) :
    HasFDerivAt (heatD1Sup t v u) (heatD2ConvolutionMap t v u x) x := by
  let G : V → V → F := fun z y => heatD1 t v (z - y) • u y
  let DG : V → V → V →L[Real] F := fun z y =>
    (heatD2Map t v (z - y)).smulRight (u y)
  let bound : V → Real := fun y =>
    ‖v‖ * ‖u‖ * heatD2LocalMajor (V := V) t x y
  have hs : Metric.ball x (heatScale t) ∈ 𝓝 x :=
    Metric.ball_mem_nhds x (heatScale_pos ht)
  have hGmeas : ∀ᶠ z in 𝓝 x,
      AEStronglyMeasurable (G z) (volume : Measure V) := by
    apply Filter.Eventually.of_forall
    intro z
    apply Continuous.aestronglyMeasurable
    unfold G heatD1 baseD1 baseHeat baseHeatMass heatScale
    fun_prop
  have hGint : Integrable (G x) := by
    refine (((heatD1_int (V := V) ht v).norm.comp_sub_left x).mul_const ‖u‖).mono'
      ?_ ?_
    · apply Continuous.aestronglyMeasurable
      unfold G heatD1 baseD1 baseHeat baseHeatMass heatScale
      fun_prop
    filter_upwards with y
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (u.norm_coe_le_norm y)
      (norm_nonneg (heatD1 t v (x - y)))
  have hDGmeas : AEStronglyMeasurable (DG x) (volume : Measure V) := by
    apply Continuous.aestronglyMeasurable
    unfold DG heatD2Map baseD2Map baseHeat baseHeatMass heatScale
    fun_prop
  have hbound : ∀ᵐ y ∂(volume : Measure V), ∀ z ∈ Metric.ball x (heatScale t),
      ‖DG z y‖ ≤ bound y := by
    apply Filter.Eventually.of_forall
    intro y z hz
    calc
      ‖DG z y‖ = ‖heatD2Map t v (z - y)‖ * ‖u y‖ := by
        unfold DG
        rw [ContinuousLinearMap.norm_smulRight_apply]
      _ ≤ (‖v‖ * heatD2Maj t (z - y)) * ‖u‖ :=
        mul_le_mul (heatD2Map_norm_le ht v (z - y))
          (u.norm_coe_le_norm y) (norm_nonneg _)
          (mul_nonneg (norm_nonneg v) (heatD2Maj_nonneg ht _))
      _ = ‖v‖ * ‖u‖ * heatD2Maj t (z - y) := by ring
      _ ≤ ‖v‖ * ‖u‖ * heatD2LocalMajor (V := V) t x y :=
        mul_le_mul_of_nonneg_left (heatD2Maj_le_localMajor ht x y hz)
          (mul_nonneg (norm_nonneg v) (norm_nonneg u))
      _ = bound y := rfl
  have hboundInt : Integrable bound :=
    (heatD2LocalMajor_int (V := V) ht x).const_mul (‖v‖ * ‖u‖)
  have hdiff : ∀ᵐ y ∂(volume : Measure V), ∀ z ∈ Metric.ball x (heatScale t),
      HasFDerivAt (G · y) (DG z y) z := by
    apply Filter.Eventually.of_forall
    intro y z hz
    have hsub : HasFDerivAt (fun q : V => q - y)
        (ContinuousLinearMap.id Real V) z :=
      (hasFDerivAt_id z).sub_const y
    unfold G DG
    simpa using ((heatD1_hasFDeriv v (z - y)).comp z hsub).smul_const (u y)
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := G) (F' := DG) (bound := bound) hs hGmeas hGint hDGmeas
      hbound hboundInt hdiff
  have hfun : (fun z : V => ∫ y : V, G z y) = heatD1Sup t v u := by
    funext z
    unfold G heatD1Sup supKernel
    rw [← MeasureTheory.convolution_lsmul_swap]
    rfl
  rw [hfun] at h
  simpa only [DG, heatD2ConvolutionMap] using h

omit [CompleteSpace F] in
theorem heatSupHessian_apply {t : Real} (ht : 0 < t)
    (u : BoundedContinuousFunction V F) (x w v : V) :
    heatSupHessian t u x w v = heatD2Convolution t v w u x := by
  let L : (V →L[Real] F) →L[Real] F :=
    (ContinuousLinearMap.apply Real F) v
  have heval := L.hasFDerivAt.comp x (heatSupGradient_hasFDerivAt ht u x)
  have hfun : (fun z : V => L (heatSupGradient t u z)) = heatD1Sup t v u := by
    funext z
    exact heatSupGradient_apply ht u z v
  have heval' : HasFDerivAt (heatD1Sup t v u)
      (L.comp (heatSupHessian t u x)) x := by
    rw [← hfun]
    exact heval.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)
  have hraw := heatD1Sup_hasFDerivAt ht v u x
  have hmaps := heval'.unique hraw
  have happly := congrArg (fun A : V →L[Real] F => A w) hmaps
  simpa only [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    heatD2ConvolutionMap_apply ht] using happly

omit [CompleteSpace F] in
theorem heatSupHessian_eval_eq_heatD2ConvolutionMap {t : Real} (ht : 0 < t)
    (u : BoundedContinuousFunction V F) (x v : V) :
    ((ContinuousLinearMap.apply Real F) v).comp (heatSupHessian t u x) =
      heatD2ConvolutionMap t v u x := by
  ext w
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    heatSupHessian_apply ht, heatD2ConvolutionMap_apply ht]

end HeatEquation

end
