-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Parabolic/Euclidean/HeatSemigroup/Schauder.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Parabolic.Euclidean.Duhamel.Frozen
public import CalabiYau.Analysis.Parabolic.Euclidean.HeatPotential.Estimate
public import CalabiYau.Mathlib.Analysis.Holder.Localization

@[expose] public section

-- Private declarations used in public declarations require the compatibility option below..

noncomputable section

open MeasureTheory Real Set Filter
open scoped NNReal RealInnerProductSpace

namespace HeatEquation

open CalabiYau.Schauder

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace Real F]

theorem heatD3Convolution_int_of_bounded {t : Real} (ht : 0 < t)
    (h v w : V) (u : BoundedContinuousFunction V F) (x : V) :
    Integrable (fun y : V => heatD3 t h v w y • u (x - y)) := by
  refine ((heatD3Maj_int (V := V) ht).const_mul
    (‖h‖ * ‖v‖ * ‖w‖ * ‖u‖)).mono' ?_ ?_
  · exact (Continuous.aestronglyMeasurable <| by
      unfold heatD3 baseD3 baseHeat baseHeatMass heatScale
      fun_prop)
  · filter_upwards with y
    rw [norm_smul]
    calc
      ‖heatD3 t h v w y‖ * ‖u (x - y)‖ ≤
          (‖h‖ * ‖v‖ * ‖w‖ * heatD3Maj t y) * ‖u‖ := by
        exact mul_le_mul (heatD3_bound ht h v w y)
          (u.norm_coe_le_norm (x - y)) (norm_nonneg _)
          (mul_nonneg
            (mul_nonneg (mul_nonneg (norm_nonneg h) (norm_nonneg v))
              (norm_nonneg w))
            (heatD3Maj_nonneg ht y))
      _ = (‖h‖ * ‖v‖ * ‖w‖ * ‖u‖) * heatD3Maj t y := by ring

theorem heatD3Convolution_norm_of_bounded {t : Real} (ht : 0 < t)
    (h v w : V) (u : BoundedContinuousFunction V F) (x : V) :
    ‖heatD3Convolution t h v w u x‖ ≤
      ‖h‖ * ‖v‖ * ‖w‖ * ‖u‖ * t⁻¹ * (heatScale t)⁻¹ * heatC3 V := by
  unfold heatD3Convolution
  calc
    ‖∫ y : V, heatD3 t h v w y • u (x - y)‖ ≤
        ∫ y : V, ‖heatD3 t h v w y‖ * ‖u‖ := by
      exact norm_integral_le_of_norm_le
        ((heatD3_int (V := V) ht h v w).norm.mul_const ‖u‖)
        (Filter.Eventually.of_forall fun y => by
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_left
            (u.norm_coe_le_norm (x - y)) (norm_nonneg _))
    _ = (∫ y : V, ‖heatD3 t h v w y‖) * ‖u‖ := by
      rw [integral_mul_const]
    _ ≤ (‖h‖ * ‖v‖ * ‖w‖ * t⁻¹ * (heatScale t)⁻¹ * heatC3 V) * ‖u‖ := by
      gcongr
      exact integral_norm_D3 ht h v w
    _ = ‖h‖ * ‖v‖ * ‖w‖ * ‖u‖ * t⁻¹ * (heatScale t)⁻¹ * heatC3 V := by
      ring

theorem heatD3_path_integrable_of_bounded {t : Real} (ht : 0 < t)
    (h v w : V) (u : BoundedContinuousFunction V F) (x : V) :
    Integrable
      (fun z : Real × V ↦
        (-heatD3 t h v w (z.2 + z.1 • (-h))) • u (x - z.2))
      ((volume.restrict (Ioc 0 1)).prod volume) := by
  let μ : Measure Real := volume.restrict (Ioc 0 1)
  let G : Real × V → F := fun z ↦
    (-heatD3 t h v w (z.2 + z.1 • (-h))) • u (x - z.2)
  let A : Real := ‖h‖ * ‖v‖ * ‖w‖ * ‖u‖
  let C : Real := A * (t⁻¹ * (heatScale t)⁻¹ * heatC3 V)
  have hGmeas : AEStronglyMeasurable G (μ.prod (volume : Measure V)) := by
    apply Continuous.aestronglyMeasurable
    unfold G heatD3 baseD3 baseHeat baseHeatMass heatScale
    fun_prop
  have hslice_int : ∀ s : Real, Integrable (fun y : V ↦ G (s, y)) := by
    intro s
    have hs := (heatD3Convolution_int_of_bounded ht h v w u (x - s • h)).neg
      |>.comp_add_right (s • (-h))
    refine hs.congr (Eventually.of_forall fun y ↦ ?_)
    have hfarg : x - s • h - (y + s • (-h)) = x - y := by
      rw [smul_neg]
      abel
    simp only [G, hfarg, Pi.neg_apply, neg_smul]
  have hslice_bound : ∀ s : Real, (∫ y : V, ‖G (s, y)‖) ≤ C := by
    intro s
    have hmajor : Integrable
        (fun y : V ↦ A * heatD3Maj t (y + s • (-h))) :=
      ((heatD3Maj_int (V := V) ht).comp_add_right (s • (-h))).const_mul A
    have hpoint : ∀ y : V,
        ‖G (s, y)‖ ≤ A * heatD3Maj t (y + s • (-h)) := by
      intro y
      rw [norm_smul]
      calc
        ‖-heatD3 t h v w (y + s • (-h))‖ * ‖u (x - y)‖ ≤
            (‖h‖ * ‖v‖ * ‖w‖ * heatD3Maj t (y + s • (-h))) * ‖u‖ := by
          rw [norm_neg]
          exact mul_le_mul (heatD3_bound ht h v w _)
            (u.norm_coe_le_norm (x - y)) (norm_nonneg _)
            (mul_nonneg
              (mul_nonneg (mul_nonneg (norm_nonneg h) (norm_nonneg v))
                (norm_nonneg w))
              (heatD3Maj_nonneg ht _))
        _ = A * heatD3Maj t (y + s • (-h)) := by
          unfold A
          ring
    calc
      (∫ y : V, ‖G (s, y)‖) ≤
          ∫ y : V, A * heatD3Maj t (y + s • (-h)) :=
        integral_mono (hslice_int s).norm hmajor hpoint
      _ = A * ∫ y : V, heatD3Maj t (y + s • (-h)) := by
        rw [integral_const_mul]
      _ = A * ∫ y : V, heatD3Maj t y := by
        rw [MeasureTheory.integral_add_right_eq_self]
      _ = C := by
        rw [integral_heatD3Maj ht]
  have hCnonneg : 0 ≤ C := by
    unfold C A
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (norm_nonneg h) (norm_nonneg v))
          (norm_nonneg w))
        (norm_nonneg u))
      (mul_nonneg
        (mul_nonneg (inv_nonneg.mpr ht.le)
          (inv_nonneg.mpr (heatScale_pos ht).le))
        (heatC3_nonneg (V := V)))
  have houter : Integrable (fun s : Real ↦ ∫ y : V, ‖G (s, y)‖) μ := by
    have hconst : Integrable (fun _ : Real ↦ C) μ := by
      change IntegrableOn (fun _ : Real ↦ C) (Ioc 0 1) volume
      exact integrableOn_const (C := C) measure_Ioc_lt_top.ne
    refine hconst.mono hGmeas.norm.integral_prod_right' ?_
    filter_upwards with s
    rw [Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg fun y ↦ norm_nonneg (G (s, y))),
      Real.norm_eq_abs, abs_of_nonneg hCnonneg]
    exact hslice_bound s
  exact (integrable_prod_iff hGmeas).2
    ⟨Eventually.of_forall hslice_int, houter⟩

theorem heatD2Convolution_space_sub_eq_integral_kernel_diff_of_bounded
    {t : Real} (ht : 0 < t) (h v w : V)
    (u : BoundedContinuousFunction V F) (x : V) :
    heatD2Convolution t v w u (x - h) - heatD2Convolution t v w u x =
      ∫ z : V, (heatD2 t v w (z - h) - heatD2 t v w z) • u (x - z) := by
  have hzero := supKernel_int (heatD2_int ht v w) u x
  have hone0 := supKernel_int (heatD2_int ht v w) u (x - h)
  change Integrable (fun z : V ↦ heatD2 t v w z • u (x - z)) at hzero
  change Integrable (fun z : V ↦ heatD2 t v w z • u (x - h - z)) at hone0
  have hone : Integrable
      (fun z : V ↦ heatD2 t v w (z - h) • u (x - z)) := by
    have htranslated := hone0.comp_add_right (-h)
    refine htranslated.congr (Filter.Eventually.of_forall fun z ↦ ?_)
    have hk : z + -h = z - h := by abel
    have hfarg : x - h - (z - h) = x - z := by abel
    simp only [hk, hfarg]
  rw [heatD2Convolution_translate_kernel]
  unfold heatD2Convolution
  rw [← integral_sub hone hzero]
  apply integral_congr_ae
  filter_upwards with z
  rw [sub_smul]

variable [CompleteSpace F] in
theorem heatD2Convolution_space_sub_eq_integral_heatD3Convolution_of_bounded
    {t : Real} (ht : 0 < t) (h v w : V)
    (u : BoundedContinuousFunction V F) (x : V) :
    heatD2Convolution t v w u (x - h) - heatD2Convolution t v w u x =
      ∫ s : Real in 0..1, -heatD3Convolution t h v w u (x - s • h) := by
  let μ : Measure Real := volume.restrict (Ioc 0 1)
  let G : Real × V → F := fun z ↦
    (-heatD3 t h v w (z.2 + z.1 • (-h))) • u (x - z.2)
  have hGint : Integrable G (μ.prod (volume : Measure V)) := by
    simpa only [G, μ] using heatD3_path_integrable_of_bounded ht h v w u x
  rw [heatD2Convolution_space_sub_eq_integral_kernel_diff_of_bounded ht]
  calc
    (∫ z : V, (heatD2 t v w (z - h) - heatD2 t v w z) • u (x - z)) =
        ∫ z : V, (∫ s : Real in 0..1,
          -heatD3 t h v w (z + s • (-h))) • u (x - z) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [heatD2_space_sub_eq_integral_heatD3]
    _ = ∫ z : V, ∫ s : Real in 0..1,
        (-heatD3 t h v w (z + s • (-h))) • u (x - z) := by
      apply integral_congr_ae
      filter_upwards with z
      exact (intervalIntegral.integral_smul_const
        (fun s : Real ↦ -heatD3 t h v w (z + s • (-h))) (u (x - z))).symm
    _ = ∫ z : V, (∫ s : Real, G (s, z) ∂μ) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [intervalIntegral.integral_of_le (by norm_num)]
    _ = ∫ s : Real, (∫ z : V, G (s, z)) ∂μ := by
      have huncurry : Integrable
          (Function.uncurry (fun s : Real ↦ fun z : V ↦ G (s, z)))
          (μ.prod (volume : Measure V)) := by
        change Integrable G (μ.prod (volume : Measure V))
        exact hGint
      have hswap :
          (∫ s : Real, (∫ z : V, G (s, z)) ∂μ) =
            ∫ z : V, (∫ s : Real, G (s, z) ∂μ) :=
        integral_integral_swap huncurry
      exact hswap.symm
    _ = ∫ s : Real in 0..1, -heatD3Convolution t h v w u (x - s • h) := by
      rw [intervalIntegral.integral_of_le (by norm_num)]
      apply integral_congr_ae
      filter_upwards with s
      simpa only [G] using integral_heatD3_path_eq_neg_heatD3Convolution t h v w u x s

theorem heatD3Convolution_path_intervalIntegrable_of_bounded
    {t : Real} (ht : 0 < t) (h v w : V)
    (u : BoundedContinuousFunction V F) (x : V) :
    IntervalIntegrable
      (fun s : Real ↦ heatD3Convolution t h v w u (x - s • h)) volume 0 1 := by
  let μ : Measure Real := volume.restrict (Ioc 0 1)
  let G : Real × V → F := fun z ↦
    (-heatD3 t h v w (z.2 + z.1 • (-h))) • u (x - z.2)
  have hGint : Integrable G (μ.prod (volume : Measure V)) := by
    simpa only [G, μ] using heatD3_path_integrable_of_bounded ht h v w u x
  have hneg : Integrable
      (fun s : Real ↦ -heatD3Convolution t h v w u (x - s • h)) μ := by
    refine hGint.integral_prod_left.congr (Eventually.of_forall fun s ↦ ?_)
    simpa only [G] using integral_heatD3_path_eq_neg_heatD3Convolution t h v w u x s
  have hconv : Integrable
      (fun s : Real ↦ heatD3Convolution t h v w u (x - s • h)) μ := by
    refine hneg.neg.congr (Eventually.of_forall fun s ↦ ?_)
    simp
  rw [intervalIntegrable_iff,
    uIoc_of_le (by norm_num : (0 : Real) ≤ 1)]
  change Integrable
    (fun s : Real ↦ heatD3Convolution t h v w u (x - s • h))
    (volume.restrict (Ioc 0 1)) at hconv
  exact hconv

variable [CompleteSpace F] in
theorem heatD2Convolution_space_sub_norm_le_of_bounded
    {t : Real} (ht : 0 < t) (h v w : V)
    (u : BoundedContinuousFunction V F) (x : V) :
    ‖heatD2Convolution t v w u (x - h) - heatD2Convolution t v w u x‖ ≤
      ‖h‖ * ‖v‖ * ‖w‖ * ‖u‖ * t⁻¹ * (heatScale t)⁻¹ * heatC3 V := by
  let M : Real :=
    ‖h‖ * ‖v‖ * ‖w‖ * ‖u‖ * t⁻¹ * (heatScale t)⁻¹ * heatC3 V
  have hpath := heatD3Convolution_path_intervalIntegrable_of_bounded ht h v w u x
  have hconst : IntervalIntegrable (fun _ : Real ↦ M) volume 0 1 :=
    (continuous_const : Continuous (fun _ : Real ↦ M)).intervalIntegrable
      (μ := volume) 0 1
  rw [heatD2Convolution_space_sub_eq_integral_heatD3Convolution_of_bounded ht]
  calc
    ‖∫ s : Real in 0..1, -heatD3Convolution t h v w u (x - s • h)‖ ≤
        ∫ s : Real in 0..1, ‖-heatD3Convolution t h v w u (x - s • h)‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ _s : Real in 0..1, M := by
      refine intervalIntegral.integral_mono (by norm_num) hpath.neg.norm hconst ?_
      intro s
      dsimp only
      rw [norm_neg]
      simpa only [M] using heatD3Convolution_norm_of_bounded ht h v w u (x - s • h)
    _ = M := by simp
    _ = ‖h‖ * ‖v‖ * ‖w‖ * ‖u‖ * t⁻¹ * (heatScale t)⁻¹ * heatC3 V := by
      rfl

def heatD2SupHolderConst (t : Real)
    (u : BoundedContinuousFunction V F) : NNReal :=
  max
    (2 * Real.toNNReal (t⁻¹ * heatC2 V * ‖u‖))
    (Real.toNNReal (‖u‖ * t⁻¹ * (heatScale t)⁻¹ * heatC3 V))

variable [CompleteSpace F] in
theorem heatD2Convolution_holder_of_norm_le_one
    {alpha : NNReal} (halpha : alpha ≤ 1)
    {t : Real} (ht : 0 < t) (v w : V)
    (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (u : BoundedContinuousFunction V F) :
    HolderWith (heatD2SupHolderConst (V := V) t u) alpha
      (fun x ↦ heatD2Convolution t v w u x) := by
  let B₀ : NNReal := Real.toNNReal (t⁻¹ * heatC2 V * ‖u‖)
  let B₁ : NNReal :=
    Real.toNNReal (‖u‖ * t⁻¹ * (heatScale t)⁻¹ * heatC3 V)
  have hnorm : ∀ x : V, ‖heatD2Convolution t v w u x‖ ≤ B₀ := by
    intro x
    have hraw := heatD2Sup_norm ht v w u x
    have hunit :
        (‖v‖ * ‖w‖ * t⁻¹ * heatC2 V) * ‖u‖ ≤
          t⁻¹ * heatC2 V * ‖u‖ := by
      have hvw : ‖v‖ * ‖w‖ ≤ 1 := by
        exact (mul_le_mul hv hw (norm_nonneg w) (by positivity)).trans_eq (one_mul 1)
      have hcoef : 0 ≤ t⁻¹ * heatC2 V * ‖u‖ := by
        exact mul_nonneg
          (mul_nonneg (inv_nonneg.mpr ht.le) (heatC2_nonneg (V := V)))
          (norm_nonneg u)
      calc
        (‖v‖ * ‖w‖ * t⁻¹ * heatC2 V) * ‖u‖ =
            (‖v‖ * ‖w‖) * (t⁻¹ * heatC2 V * ‖u‖) := by ring
        _ ≤ 1 * (t⁻¹ * heatC2 V * ‖u‖) :=
          mul_le_mul_of_nonneg_right hvw hcoef
        _ = t⁻¹ * heatC2 V * ‖u‖ := one_mul _
    have hraw' : ‖heatD2Convolution t v w u x‖ ≤
        t⁻¹ * heatC2 V * ‖u‖ := by
      simpa only [heatD2Convolution, heatD2Sup, supKernel] using hraw.trans hunit
    exact hraw'.trans (Real.le_coe_toNNReal _)
  have hzero : HolderWith (2 * B₀) 0
      (fun x ↦ heatD2Convolution t v w u x) :=
    holderWith_zero_of_norm_le hnorm
  have hlip : LipschitzWith B₁
      (fun x ↦ heatD2Convolution t v w u x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm]
    have hraw := heatD2Convolution_space_sub_norm_le_of_bounded ht (y - x) v w u y
    have hxy : y - (y - x) = x := by abel
    rw [hxy] at hraw
    have hunit :
        ‖y - x‖ * ‖v‖ * ‖w‖ * ‖u‖ * t⁻¹ *
            (heatScale t)⁻¹ * heatC3 V ≤
          (‖u‖ * t⁻¹ * (heatScale t)⁻¹ * heatC3 V) * ‖x - y‖ := by
      rw [norm_sub_rev]
      have hvw : ‖v‖ * ‖w‖ ≤ 1 := by
        exact (mul_le_mul hv hw (norm_nonneg w) (by positivity)).trans_eq (one_mul 1)
      have hcoef : 0 ≤
          ‖x - y‖ * ‖u‖ * t⁻¹ * (heatScale t)⁻¹ * heatC3 V := by
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (norm_nonneg _) (norm_nonneg u))
              (inv_nonneg.mpr ht.le))
            (inv_nonneg.mpr (heatScale_pos ht).le))
          (heatC3_nonneg (V := V))
      calc
        ‖x - y‖ * ‖v‖ * ‖w‖ * ‖u‖ * t⁻¹ *
            (heatScale t)⁻¹ * heatC3 V =
            (‖v‖ * ‖w‖) *
              (‖x - y‖ * ‖u‖ * t⁻¹ * (heatScale t)⁻¹ * heatC3 V) := by
          ring
        _ ≤ 1 * (‖x - y‖ * ‖u‖ * t⁻¹ *
            (heatScale t)⁻¹ * heatC3 V) :=
          mul_le_mul_of_nonneg_right hvw hcoef
        _ = (‖u‖ * t⁻¹ * (heatScale t)⁻¹ * heatC3 V) * ‖x - y‖ := by
          ring
    exact hraw.trans (hunit.trans (by
      unfold B₁
      gcongr
      exact Real.le_coe_toNNReal _))
  have hone : HolderWith B₁ 1
      (fun x ↦ heatD2Convolution t v w u x) := hlip.holderWith
  have hinterp := hzero.of_le_of_le hone bot_le halpha
  simpa only [heatD2SupHolderConst, B₀, B₁] using hinterp

def heatSupSpatialJetConst (t : Real)
    (u : BoundedContinuousFunction V F) : Nat → NNReal
  | 0 => ⟨‖u‖, norm_nonneg u⟩
  | 1 => Real.toNNReal ((heatScale t)⁻¹ * heatC1 V * ‖u‖)
  | _ => Real.toNNReal (t⁻¹ * heatC2 V * ‖u‖)

def heatSupHessianHolderConst (t : Real)
    (u : BoundedContinuousFunction V F) : NNReal :=
  ∑ _β : Fin 2 → Fin (Module.finrank Real V),
    heatD2SupHolderConst (V := V) t u

def heatSupHessianMapHolderConst (t : Real)
    (u : BoundedContinuousFunction V F) : NNReal :=
  ∑ _i : Fin (Module.finrank Real V),
    ∑ _j : Fin (Module.finrank Real V),
      heatD2SupHolderConst (V := V) t u

def heatSupSchauderConst (t : Real)
    (u : BoundedContinuousFunction V F) : NNReal :=
  (∑ j ∈ Finset.range 3, heatSupSpatialJetConst (V := V) t u j) +
    heatSupHessianHolderConst (V := V) t u

theorem heatSup_spatialJet_norm_le
    {t : Real} (ht : 0 < t) (u : BoundedContinuousFunction V F)
    {j : Nat} (hj : j ≤ 2) (x : V) :
    ‖iteratedFDeriv Real j (fun z : V ↦ heatSup t u z) x‖ ≤
      heatSupSpatialJetConst (V := V) t u j := by
  have hcases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  obtain rfl | rfl | rfl := hcases
  · rw [norm_iteratedFDeriv_zero]
    change ‖heatSup t u x‖ ≤ ‖u‖
    exact heatSup_contract ht u x
  · rw [norm_iteratedFDeriv_one, (heatSup_hasFDerivAt ht u x).fderiv]
    change ‖heatSupGradient t u x‖ ≤
      Real.toNNReal ((heatScale t)⁻¹ * heatC1 V * ‖u‖)
    have hnonneg : 0 ≤ (heatScale t)⁻¹ * heatC1 V * ‖u‖ :=
      mul_nonneg
        (mul_nonneg (inv_nonneg.mpr (heatScale_pos ht).le)
          (heatC1_nonneg (V := V)))
        (norm_nonneg u)
    rw [Real.coe_toNNReal _ hnonneg]
    refine ContinuousLinearMap.opNorm_le_bound (𝕜 := Real) (𝕜₂ := Real)
      (heatSupGradient t u x) ?_ ?_
    · exact hnonneg
    · intro v
      rw [heatSupGradient_apply ht]
      have hraw := heatD1Sup_norm ht v u x
      exact hraw.trans_eq (by ring)
  · refine ContinuousMultilinearMap.opNorm_le_bound ?_ ?_
    · change 0 ≤ Real.toNNReal (t⁻¹ * heatC2 V * ‖u‖)
      positivity
    · intro m
      rw [heatSup_iteratedFDeriv_two_apply ht, heatSupHessian_apply ht]
      have hraw := heatD2Sup_norm ht (m 1) (m 0) u x
      have hraw' : ‖heatD2Convolution t (m 1) (m 0) u x‖ ≤
          (‖m 1‖ * ‖m 0‖ * t⁻¹ * heatC2 V) * ‖u‖ := by
        simpa only [heatD2Convolution, heatD2Sup, supKernel] using hraw
      have hnonneg : 0 ≤ t⁻¹ * heatC2 V * ‖u‖ :=
        mul_nonneg
          (mul_nonneg (inv_nonneg.mpr ht.le) (heatC2_nonneg (V := V)))
          (norm_nonneg u)
      calc
        ‖heatD2Convolution t (m 1) (m 0) u x‖ ≤
            (‖m 1‖ * ‖m 0‖ * t⁻¹ * heatC2 V) * ‖u‖ := hraw'
        _ = (t⁻¹ * heatC2 V * ‖u‖) * ∏ i, ‖m i‖ := by
          rw [Fin.prod_univ_two]
          ring
        _ = (heatSupSpatialJetConst (V := V) t u 2 : Real) *
            ∏ i, ‖m i‖ := by
          change (t⁻¹ * heatC2 V * ‖u‖) * ∏ i, ‖m i‖ =
            (Real.toNNReal (t⁻¹ * heatC2 V * ‖u‖) : Real) * ∏ i, ‖m i‖
          rw [Real.coe_toNNReal _ hnonneg]
section

variable [CompleteSpace F]


theorem heatSup_iteratedFDeriv_two_holder
    {alpha : NNReal} (halpha : alpha ≤ 1)
    {t : Real} (ht : 0 < t) (u : BoundedContinuousFunction V F) :
    HolderWith (heatSupHessianHolderConst (V := V) t u) alpha
      (iteratedFDeriv Real 2 (fun z : V ↦ heatSup t u z)) := by
  apply holderWith_continuousMultilinearMap_of_stdOrthonormalBasis
    (C := fun _ ↦ heatD2SupHolderConst (V := V) t u)
  intro β
  have h := heatD2Convolution_holder_of_norm_le_one halpha ht
    ((stdOrthonormalBasis Real V) (β 1))
    ((stdOrthonormalBasis Real V) (β 0))
    (by simp) (by simp) u
  simpa only [heatSupHessianHolderConst,
    heatSup_iteratedFDeriv_two_apply ht, heatSupHessian_apply ht] using h

theorem heatSupHessian_holder
    {alpha : NNReal} (halpha : alpha ≤ 1)
    {t : Real} (ht : 0 < t) (u : BoundedContinuousFunction V F) :
    HolderWith (heatSupHessianMapHolderConst (V := V) t u) alpha
      (heatSupHessian t u) := by
  unfold heatSupHessianMapHolderConst
  apply holderWith_continuousLinearMap_two_of_stdOrthonormalBasis
    (A := heatSupHessian t u)
    (C := fun _ _ ↦ heatD2SupHolderConst (V := V) t u)
  intro i j
  have h := heatD2Convolution_holder_of_norm_le_one halpha ht
    ((stdOrthonormalBasis Real V) j)
    ((stdOrthonormalBasis Real V) i)
    (by simp) (by simp) u
  simpa only [heatSupHessian_apply ht] using h

theorem heatSup_contDiff_two
    {t : Real} (ht : 0 < t) (u : BoundedContinuousFunction V F) :
    ContDiff Real 2 (fun x : V ↦ heatSup t u x) := by
  have hhess : Continuous (heatSupHessian t u) :=
    (heatSupHessian_holder (alpha := 1) le_rfl ht u).continuous (by norm_num)
  have hgrad : ContDiff Real 1 (heatSupGradient t u) :=
    contDiff_one_iff_hasFDerivAt.mpr
      ⟨heatSupHessian t u, hhess, heatSupGradient_hasFDerivAt ht u⟩
  exact (contDiff_succ_iff_hasFDerivAt (n := 1)).mpr
    ⟨heatSupGradient t u, hgrad, heatSup_hasFDerivAt ht u⟩

theorem heatSup_schauder_estimate
    {alpha : NNReal} (halpha : alpha ≤ 1)
    {t : Real} (ht : 0 < t) (u : BoundedContinuousFunction V F) :
    eContDiffHolderGaugeOn 2 alpha Set.univ
      (fun x : V ↦ heatSup t u x) ≤
      heatSupSchauderConst (V := V) t u := by
  have h := eContDiffHolderGaugeOn_le
    (heatSupSpatialJetConst (V := V) t u)
    (heatSupHessianHolderConst (V := V) t u)
    (fun j hj x _ ↦ heatSup_spatialJet_norm_le ht u hj x)
    ((heatSup_iteratedFDeriv_two_holder halpha ht u).holderOnWith
      Set.univ).holderWith
  simpa only [heatSupSchauderConst, ENNReal.coe_add,
    ENNReal.ofNNReal_finsetSum] using h

end

end HeatEquation

end
