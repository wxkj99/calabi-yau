-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Parabolic/Euclidean/HeatPotential/Realization.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Parabolic.Euclidean.HeatKernel.Duhamel.LowerOrder
public import CalabiYau.Analysis.Parabolic.Euclidean.HeatKernel.Schauder.SecondDerivative
public import CalabiYau.Analysis.Parabolic.Euclidean.HeatPotential.Regularity
public import CalabiYau.Mathlib.Analysis.Holder.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

@[expose] public section

-- and its private helpers occur in public declarations.

noncomputable section

open MeasureTheory Real Set Filter
open scoped NNReal RealInnerProductSpace Topology

namespace HeatEquation

open CalabiYau.Schauder

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem heatSupGradient_norm_le {t : Real} (ht : 0 < t)
    (u : BoundedContinuousFunction V F) (x : V) :
    ‖heatSupGradient t u x‖ ≤
      (heatScale t)⁻¹ * heatC1 V * ‖u‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (heatSupGradient t u x)
    (mul_nonneg
      (mul_nonneg (inv_nonneg.mpr (heatScale_pos ht).le)
        (heatC1_nonneg (V := V)))
      (norm_nonneg u))
  intro v
  rw [heatSupGradient_apply ht]
  exact (heatD1Sup_norm ht v u x).trans_eq (by ring)

theorem heatSupHessian_norm_le_of_holder {alpha K : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t) {u : BoundedContinuousFunction V F}
    (hu : HolderWith K alpha u) (x : V) :
    ‖heatSupHessian t u x‖ ≤
      (K : Real) * holderHeatScale alpha t * heatC2Holder (V := V) alpha := by
  let C : Real :=
    (K : Real) * holderHeatScale alpha t * heatC2Holder (V := V) alpha
  have hC : 0 ≤ C := by
    unfold C
    exact mul_nonneg
      (mul_nonneg K.coe_nonneg (Real.rpow_nonneg (le_of_lt ht) _))
      (heatC2Holder_nonneg (V := V) alpha)
  apply ContinuousLinearMap.opNorm_le_bound (heatSupHessian t u x) hC
  intro w
  apply ContinuousLinearMap.opNorm_le_bound (heatSupHessian t u x w)
    (mul_nonneg hC (norm_nonneg w))
  intro v
  rw [heatSupHessian_apply ht,
    heatD2Convolution_eq_cancel_of_holder halpha0 halpha1 ht hu]
  exact (heatD2Cancel_norm_of_holder halpha1 ht hu v w x).trans_eq (by
    unfold C
    ring)

theorem heatD2ConvolutionMap_norm_le_of_holder {alpha K : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t) (v : V)
    {u : BoundedContinuousFunction V F} (hu : HolderWith K alpha u) (x : V) :
    ‖heatD2ConvolutionMap t v u x‖ ≤
      ‖v‖ * (K : Real) * holderHeatScale alpha t *
        heatC2Holder (V := V) alpha := by
  let C : Real :=
    ‖v‖ * (K : Real) * holderHeatScale alpha t * heatC2Holder (V := V) alpha
  have hC : 0 ≤ C := by
    unfold C
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (norm_nonneg v) K.coe_nonneg)
        (Real.rpow_nonneg (le_of_lt ht) _))
      (heatC2Holder_nonneg (V := V) alpha)
  apply ContinuousLinearMap.opNorm_le_bound (heatD2ConvolutionMap t v u x) hC
  intro w
  rw [heatD2ConvolutionMap_apply ht,
    heatD2Convolution_eq_cancel_of_holder halpha0 halpha1 ht hu]
  exact (heatD2Cancel_norm_of_holder halpha1 ht hu v w x).trans_eq (by
    unfold C
    ring)

def heatDuhamelGradientMap (t : Real)
    (f : Real → BoundedContinuousFunction V F) (x : V) : V →L[Real] F :=
  ∫ s : Real in 0..t, heatSupGradient (t - s) (f s) x

def heatDuhamelGradientMajor (B : NNReal) (t s : Real) : Real :=
  (B : Real) * heatC1 V * heatScale12 (t - s)

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F] in
theorem heatDuhamelGradientMajor_intble {t : Real} (B : NNReal) :
    IntervalIntegrable (heatDuhamelGradientMajor (V := V) B t) volume 0 t :=
  (scale12_intble).const_mul ((B : Real) * heatC1 V)

omit [CompleteSpace F] in
theorem heatDuhamel_hasFDerivAt {t : Real} (ht : 0 < t) {B : NNReal}
    (f : Real → BoundedContinuousFunction V F)
    (hf : ∀ s ∈ Icc (0 : Real) t, ‖f s‖ ≤ B)
    (hmeas0 : ∀ z : V, AEStronglyMeasurable
      (fun s : Real => heatSup (t - s) (f s) z)
      (volume.restrict (uIoc (0 : Real) t)))
    (hmeas1 : ∀ z : V, AEStronglyMeasurable
      (fun s : Real => heatSupGradient (t - s) (f s) z)
      (volume.restrict (uIoc (0 : Real) t)))
    (x : V) :
    HasFDerivAt (heatDuhamel t f) (heatDuhamelGradientMap t f x) x := by
  let G : V → Real → F := fun z s => heatSup (t - s) (f s) z
  let DG : V → Real → V →L[Real] F := fun z s =>
    heatSupGradient (t - s) (f s) z
  let bound : Real → Real := heatDuhamelGradientMajor (V := V) B t
  have hGmeas : ∀ᶠ z in 𝓝 x,
      AEStronglyMeasurable (G z) (volume.restrict (uIoc (0 : Real) t)) := by
    apply Filter.Eventually.of_forall
    exact hmeas0
  have hGint : IntervalIntegrable (G x) volume 0 t :=
    heatDuhamel_int ht f hf x (hmeas0 x)
  have hDGmeas : AEStronglyMeasurable (DG x)
      (volume.restrict (uIoc (0 : Real) t)) := hmeas1 x
  have hne : ∀ᵐ s ∂(volume : Measure Real), s ≠ t := by
    simp [ae_iff, measure_singleton]
  have hbound : ∀ᵐ s ∂(volume : Measure Real), s ∈ uIoc (0 : Real) t →
      ∀ z ∈ (Set.univ : Set V), ‖DG z s‖ ≤ bound s := by
    filter_upwards [hne] with s hst
    intro hs z hz
    rw [uIoc_of_le ht.le] at hs
    have hpos : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
    calc
      ‖DG z s‖ ≤ (heatScale (t - s))⁻¹ * heatC1 V * ‖f s‖ := by
        unfold DG
        exact heatSupGradient_norm_le hpos (f s) z
      _ ≤ (heatScale (t - s))⁻¹ * heatC1 V * (B : Real) := by
        exact mul_le_mul_of_nonneg_left (hf s ⟨hs.1.le, hs.2⟩)
          (mul_nonneg (inv_nonneg.mpr (heatScale_pos hpos).le)
            (heatC1_nonneg (V := V)))
      _ = bound s := by
        rw [← heatScale12_eq hpos]
        unfold bound heatDuhamelGradientMajor
        ring
  have hdiff : ∀ᵐ s ∂(volume : Measure Real), s ∈ uIoc (0 : Real) t →
      ∀ z ∈ (Set.univ : Set V), HasFDerivAt (G · s) (DG z s) z := by
    filter_upwards [hne] with s hst
    intro hs z hz
    rw [uIoc_of_le ht.le] at hs
    have hpos : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
    unfold G DG
    exact heatSup_hasFDerivAt hpos (f s) z
  have h := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := G) (F' := DG) (bound := bound) (s := (Set.univ : Set V))
      univ_mem hGmeas hGint hDGmeas hbound
      (heatDuhamelGradientMajor_intble (V := V) B) hdiff
  change HasFDerivAt
    (fun z : V => ∫ s : Real in 0..t, heatSup (t - s) (f s) z)
    (∫ s : Real in 0..t, heatSupGradient (t - s) (f s) x) x
  exact h

omit [CompleteSpace F] in
theorem heatDuhamelGradient_int {t : Real} (ht : 0 < t) {B : NNReal}
    (f : Real → BoundedContinuousFunction V F)
    (hf : ∀ s ∈ Icc (0 : Real) t, ‖f s‖ ≤ B) (x : V)
    (hmeas : AEStronglyMeasurable
      (fun s : Real => heatSupGradient (t - s) (f s) x)
      (volume.restrict (uIoc (0 : Real) t))) :
    IntervalIntegrable
      (fun s : Real => heatSupGradient (t - s) (f s) x) volume 0 t := by
  apply (heatDuhamelGradientMajor_intble (V := V) B).mono_fun' hmeas
  have hne : ∀ᵐ s ∂(volume : Measure Real), s ≠ t := by
    simp [ae_iff, measure_singleton]
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (s := uIoc (0 : Real) t) hne] with s hs hst
  rw [uIoc_of_le ht.le] at hs
  have hpos : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
  calc
    ‖heatSupGradient (t - s) (f s) x‖ ≤
        (heatScale (t - s))⁻¹ * heatC1 V * ‖f s‖ :=
      heatSupGradient_norm_le hpos (f s) x
    _ ≤ (heatScale (t - s))⁻¹ * heatC1 V * (B : Real) :=
      mul_le_mul_of_nonneg_left (hf s ⟨hs.1.le, hs.2⟩)
        (mul_nonneg (inv_nonneg.mpr (heatScale_pos hpos).le)
          (heatC1_nonneg (V := V)))
    _ = heatDuhamelGradientMajor (V := V) B t s := by
      rw [← heatScale12_eq hpos]
      unfold heatDuhamelGradientMajor
      ring

omit [CompleteSpace F] in
theorem heatDuhamelGradientMap_apply {t : Real} (ht : 0 < t) {B : NNReal}
    (f : Real → BoundedContinuousFunction V F)
    (hf : ∀ s ∈ Icc (0 : Real) t, ‖f s‖ ≤ B)
    (x : V)
    (hmeas : AEStronglyMeasurable
      (fun s : Real => heatSupGradient (t - s) (f s) x)
      (volume.restrict (uIoc (0 : Real) t)))
    (v : V) :
    heatDuhamelGradientMap t f x v = heatD1Duhamel t v f x := by
  have hInt := heatDuhamelGradient_int (V := V) ht f hf x hmeas
  unfold heatDuhamelGradientMap heatD1Duhamel
  rw [ContinuousLinearMap.intervalIntegral_apply hInt v]
  apply intervalIntegral.integral_congr_ae
  have hne : ∀ᵐ s ∂(volume : Measure Real), s ≠ t := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hne] with s hst
  intro hs
  rw [uIoc_of_le ht.le] at hs
  exact heatSupGradient_apply
    (sub_pos.mpr (lt_of_le_of_ne hs.2 hst)) (f s) x v

def heatDuhamelHessian (t : Real)
    (f : Real → BoundedContinuousFunction V F) (x : V) :
    V →L[Real] (V →L[Real] F) :=
  ∫ s : Real in 0..t, heatSupHessian (t - s) (f s) x

def heatDuhamelHessianMajor (alpha K : NNReal) (t s : Real) : Real :=
  (K : Real) * heatC2Holder (V := V) alpha * holderHeatScale alpha (t - s)

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F] in
theorem heatDuhamelHessianMajor_intble {alpha : NNReal} (halpha : 0 < alpha)
    {t : Real} (K : NNReal) :
    IntervalIntegrable (heatDuhamelHessianMajor (V := V) alpha K t) volume 0 t :=
  (holderHeatScale_intble halpha).const_mul
    ((K : Real) * heatC2Holder (V := V) alpha)

theorem heatDuhamelGradientMap_hasFDerivAt
    {alpha K B : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t)
    (f : Real → BoundedContinuousFunction V F)
    (hbound : ∀ s ∈ Icc (0 : Real) t, ‖f s‖ ≤ B)
    (hf : ∀ s ∈ Icc (0 : Real) t, HolderWith K alpha (f s))
    (hmeas1 : ∀ z : V, AEStronglyMeasurable
      (fun s : Real => heatSupGradient (t - s) (f s) z)
      (volume.restrict (uIoc (0 : Real) t)))
    (hmeas2 : ∀ z : V, AEStronglyMeasurable
      (fun s : Real => heatSupHessian (t - s) (f s) z)
      (volume.restrict (uIoc (0 : Real) t)))
    (x : V) :
    HasFDerivAt (heatDuhamelGradientMap t f) (heatDuhamelHessian t f x) x := by
  let G : V → Real → V →L[Real] F := fun z s =>
    heatSupGradient (t - s) (f s) z
  let DG : V → Real → V →L[Real] (V →L[Real] F) := fun z s =>
    heatSupHessian (t - s) (f s) z
  let bound : Real → Real := heatDuhamelHessianMajor (V := V) alpha K t
  have hGmeas : ∀ᶠ z in 𝓝 x,
      AEStronglyMeasurable (G z) (volume.restrict (uIoc (0 : Real) t)) := by
    apply Filter.Eventually.of_forall
    exact hmeas1
  have hGint : IntervalIntegrable (G x) volume 0 t :=
    heatDuhamelGradient_int ht f hbound x (hmeas1 x)
  have hDGmeas : AEStronglyMeasurable (DG x)
      (volume.restrict (uIoc (0 : Real) t)) := hmeas2 x
  have hne : ∀ᵐ s ∂(volume : Measure Real), s ≠ t := by
    simp [ae_iff, measure_singleton]
  have hmajor : ∀ᵐ s ∂(volume : Measure Real), s ∈ uIoc (0 : Real) t →
      ∀ z ∈ (Set.univ : Set V), ‖DG z s‖ ≤ bound s := by
    filter_upwards [hne] with s hst
    intro hs z hz
    rw [uIoc_of_le ht.le] at hs
    have hpos : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
    calc
      ‖DG z s‖ ≤ (K : Real) * holderHeatScale alpha (t - s) *
          heatC2Holder (V := V) alpha := by
        unfold DG
        exact heatSupHessian_norm_le_of_holder halpha0 halpha1 hpos
          (hf s ⟨hs.1.le, hs.2⟩) z
      _ = bound s := by
        unfold bound heatDuhamelHessianMajor
        ring
  have hdiff : ∀ᵐ s ∂(volume : Measure Real), s ∈ uIoc (0 : Real) t →
      ∀ z ∈ (Set.univ : Set V), HasFDerivAt (G · s) (DG z s) z := by
    filter_upwards [hne] with s hst
    intro hs z hz
    rw [uIoc_of_le ht.le] at hs
    have hpos : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
    unfold G DG
    exact heatSupGradient_hasFDerivAt hpos (f s) z
  have h := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := G) (F' := DG) (bound := bound) (s := (Set.univ : Set V))
      univ_mem hGmeas hGint hDGmeas hmajor
      (heatDuhamelHessianMajor_intble (V := V) halpha0 K) hdiff
  change HasFDerivAt
    (fun z : V => ∫ s : Real in 0..t, heatSupGradient (t - s) (f s) z)
    (∫ s : Real in 0..t, heatSupHessian (t - s) (f s) x) x
  exact h

def heatD2DuhamelMap (t : Real) (v : V)
    (f : Real → BoundedContinuousFunction V F) (x : V) : V →L[Real] F :=
  ∫ s : Real in 0..t, heatD2ConvolutionMap (t - s) v (f s) x

def heatD2DuhamelMapMajor (alpha K : NNReal) (v : V) (t s : Real) : Real :=
  ‖v‖ * (K : Real) * heatC2Holder (V := V) alpha *
    holderHeatScale alpha (t - s)

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F] in
theorem heatD2DuhamelMapMajor_intble {alpha : NNReal} (halpha : 0 < alpha)
    {t : Real} (K : NNReal) (v : V) :
    IntervalIntegrable (heatD2DuhamelMapMajor (V := V) alpha K v t) volume 0 t :=
  (holderHeatScale_intble halpha).const_mul
    (‖v‖ * (K : Real) * heatC2Holder (V := V) alpha)

theorem heatD2DuhamelMap_int
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t)
    (f : Real → BoundedContinuousFunction V F)
    (hf : ∀ s ∈ Icc (0 : Real) t, HolderWith K alpha (f s))
    (v x : V)
    (hmeas : AEStronglyMeasurable
      (fun s : Real => heatD2ConvolutionMap (t - s) v (f s) x)
      (volume.restrict (uIoc (0 : Real) t))) :
    IntervalIntegrable
      (fun s : Real => heatD2ConvolutionMap (t - s) v (f s) x) volume 0 t := by
  apply (heatD2DuhamelMapMajor_intble (V := V) halpha0 K v).mono_fun' hmeas
  have hne : ∀ᵐ s ∂(volume : Measure Real), s ≠ t := by
    simp [ae_iff, measure_singleton]
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (s := uIoc (0 : Real) t) hne] with s hs hst
  rw [uIoc_of_le ht.le] at hs
  have hpos : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
  calc
    ‖heatD2ConvolutionMap (t - s) v (f s) x‖ ≤
        ‖v‖ * (K : Real) * holderHeatScale alpha (t - s) *
          heatC2Holder (V := V) alpha :=
      heatD2ConvolutionMap_norm_le_of_holder halpha0 halpha1 hpos v
        (hf s ⟨hs.1.le, hs.2⟩) x
    _ = heatD2DuhamelMapMajor (V := V) alpha K v t s := by
      unfold heatD2DuhamelMapMajor
      ring

theorem heatD2DuhamelMap_apply
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t)
    (f : Real → BoundedContinuousFunction V F)
    (hf : ∀ s ∈ Icc (0 : Real) t, HolderWith K alpha (f s))
    (v x : V)
    (hmeas : AEStronglyMeasurable
      (fun s : Real => heatD2ConvolutionMap (t - s) v (f s) x)
      (volume.restrict (uIoc (0 : Real) t)))
    (w : V) :
    heatD2DuhamelMap t v f x w = heatD2Duhamel t v w (fun s => f s) x := by
  have hInt := heatD2DuhamelMap_int halpha0 halpha1 ht f hf v x hmeas
  unfold heatD2DuhamelMap heatD2Duhamel
  rw [ContinuousLinearMap.intervalIntegral_apply hInt w]
  apply intervalIntegral.integral_congr_ae
  have hne : ∀ᵐ s ∂(volume : Measure Real), s ≠ t := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hne] with s hst
  intro hs
  rw [uIoc_of_le ht.le] at hs
  exact heatD2ConvolutionMap_apply (sub_pos.mpr (lt_of_le_of_ne hs.2 hst)) v (f s) x w

theorem heatD1Duhamel_hasFDerivAt
    {alpha K B : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t)
    (f : Real → BoundedContinuousFunction V F)
    (hbound : ∀ s ∈ Icc (0 : Real) t, ‖f s‖ ≤ B)
    (hf : ∀ s ∈ Icc (0 : Real) t, HolderWith K alpha (f s))
    (v : V)
    (hmeas1 : ∀ z : V, AEStronglyMeasurable
      (fun s : Real => heatD1Sup (t - s) v (f s) z)
      (volume.restrict (uIoc (0 : Real) t)))
    (hmeas2 : ∀ z : V, AEStronglyMeasurable
      (fun s : Real => heatD2ConvolutionMap (t - s) v (f s) z)
      (volume.restrict (uIoc (0 : Real) t)))
    (x : V) :
    HasFDerivAt (heatD1Duhamel t v f) (heatD2DuhamelMap t v f x) x := by
  let G : V → Real → F := fun z s => heatD1Sup (t - s) v (f s) z
  let DG : V → Real → V →L[Real] F := fun z s =>
    heatD2ConvolutionMap (t - s) v (f s) z
  let bound : Real → Real := heatD2DuhamelMapMajor (V := V) alpha K v t
  have hGmeas : ∀ᶠ z in 𝓝 x,
      AEStronglyMeasurable (G z) (volume.restrict (uIoc (0 : Real) t)) := by
    apply Filter.Eventually.of_forall
    exact hmeas1
  have hGint : IntervalIntegrable (G x) volume 0 t :=
    heatD1Duhamel_int ht f hbound v x (hmeas1 x)
  have hDGmeas : AEStronglyMeasurable (DG x)
      (volume.restrict (uIoc (0 : Real) t)) := hmeas2 x
  have hne : ∀ᵐ s ∂(volume : Measure Real), s ≠ t := by
    simp [ae_iff, measure_singleton]
  have hmajor : ∀ᵐ s ∂(volume : Measure Real), s ∈ uIoc (0 : Real) t →
      ∀ z ∈ (Set.univ : Set V), ‖DG z s‖ ≤ bound s := by
    filter_upwards [hne] with s hst
    intro hs z hz
    rw [uIoc_of_le ht.le] at hs
    have hpos : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
    calc
      ‖DG z s‖ ≤ ‖v‖ * (K : Real) * holderHeatScale alpha (t - s) *
          heatC2Holder (V := V) alpha := by
        unfold DG
        exact heatD2ConvolutionMap_norm_le_of_holder halpha0 halpha1 hpos v
          (hf s ⟨hs.1.le, hs.2⟩) z
      _ = bound s := by
        unfold bound heatD2DuhamelMapMajor
        ring
  have hdiff : ∀ᵐ s ∂(volume : Measure Real), s ∈ uIoc (0 : Real) t →
      ∀ z ∈ (Set.univ : Set V), HasFDerivAt (G · s) (DG z s) z := by
    filter_upwards [hne] with s hst
    intro hs z hz
    rw [uIoc_of_le ht.le] at hs
    have hpos : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
    unfold G DG
    exact heatD1Sup_hasFDerivAt hpos v (f s) z
  have h := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := G) (F' := DG) (bound := bound) (s := (Set.univ : Set V))
      univ_mem hGmeas hGint hDGmeas hmajor
      (heatD2DuhamelMapMajor_intble (V := V) halpha0 K v) hdiff
  change HasFDerivAt
    (fun z : V => ∫ s : Real in 0..t, heatD1Sup (t - s) v (f s) z)
    (∫ s : Real in 0..t, heatD2ConvolutionMap (t - s) v (f s) x) x
  exact h

omit [CompleteSpace F] in
private theorem heatD1Sup_time_aestronglyMeasurable
    {t : Real} (ht : 0 < t)
    (f : Real → BoundedContinuousFunction V F)
    (hmeas : ∀ z : V, AEStronglyMeasurable
      (fun s : Real => heatSupGradient (t - s) (f s) z)
      (volume.restrict (uIoc (0 : Real) t)))
    (v z : V) :
    AEStronglyMeasurable
      (fun s : Real => heatD1Sup (t - s) v (f s) z)
      (volume.restrict (uIoc (0 : Real) t)) := by
  have hcomp := ((ContinuousLinearMap.apply Real F) v).continuous
    |>.comp_aestronglyMeasurable (hmeas z)
  apply hcomp.congr
  have hne : ∀ᵐ s ∂(volume : Measure Real), s ≠ t := by
    simp [ae_iff, measure_singleton]
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (s := uIoc (0 : Real) t) hne] with s hs hst
  rw [uIoc_of_le ht.le] at hs
  exact heatSupGradient_apply
    (sub_pos.mpr (lt_of_le_of_ne hs.2 hst)) (f s) z v

omit [CompleteSpace F] in
private theorem heatD2ConvolutionMap_time_aestronglyMeasurable
    {t : Real} (ht : 0 < t)
    (f : Real → BoundedContinuousFunction V F)
    (hmeas : ∀ z : V, AEStronglyMeasurable
      (fun s : Real => heatSupHessian (t - s) (f s) z)
      (volume.restrict (uIoc (0 : Real) t)))
    (v z : V) :
    AEStronglyMeasurable
      (fun s : Real => heatD2ConvolutionMap (t - s) v (f s) z)
      (volume.restrict (uIoc (0 : Real) t)) := by
  let L : (V →L[Real] (V →L[Real] F)) →L[Real] (V →L[Real] F) :=
    ContinuousLinearMap.compL Real V (V →L[Real] F) F
      ((ContinuousLinearMap.apply Real F) v)
  have hcomp := L.continuous.comp_aestronglyMeasurable (hmeas z)
  apply hcomp.congr
  have hne : ∀ᵐ s ∂(volume : Measure Real), s ≠ t := by
    simp [ae_iff, measure_singleton]
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (s := uIoc (0 : Real) t) hne] with s hs hst
  rw [uIoc_of_le ht.le] at hs
  unfold L
  rw [ContinuousLinearMap.compL_apply]
  exact heatSupHessian_eval_eq_heatD2ConvolutionMap
    (sub_pos.mpr (lt_of_le_of_ne hs.2 hst)) (f s) z v

omit [CompleteSpace F] in
theorem heatD2Convolution_time_aestronglyMeasurable
    {t : Real} (ht : 0 < t)
    (f : Real → BoundedContinuousFunction V F)
    (hmeas : ∀ z : V, AEStronglyMeasurable
      (fun s : Real => heatSupHessian (t - s) (f s) z)
      (volume.restrict (uIoc (0 : Real) t)))
    (v w z : V) :
    AEStronglyMeasurable
      (fun s : Real => heatD2Convolution (t - s) v w (f s) z)
      (volume.restrict (uIoc (0 : Real) t)) := by
  have hcomp := ((ContinuousLinearMap.apply Real F) w).continuous
    |>.comp_aestronglyMeasurable
      (heatD2ConvolutionMap_time_aestronglyMeasurable ht f hmeas v z)
  apply hcomp.congr
  have hne : ∀ᵐ s ∂(volume : Measure Real), s ≠ t := by
    simp [ae_iff, measure_singleton]
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (s := uIoc (0 : Real) t) hne] with s hs hst
  rw [uIoc_of_le ht.le] at hs
  exact heatD2ConvolutionMap_apply
    (sub_pos.mpr (lt_of_le_of_ne hs.2 hst)) v (f s) z w

theorem heatDuhamelHessian_apply
    {alpha K B : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t)
    (f : Real → BoundedContinuousFunction V F)
    (hbound : ∀ s ∈ Icc (0 : Real) t, ‖f s‖ ≤ B)
    (hf : ∀ s ∈ Icc (0 : Real) t, HolderWith K alpha (f s))
    (hmeas1 : ∀ z : V, AEStronglyMeasurable
      (fun s : Real => heatSupGradient (t - s) (f s) z)
      (volume.restrict (uIoc (0 : Real) t)))
    (hmeas2 : ∀ z : V, AEStronglyMeasurable
      (fun s : Real => heatSupHessian (t - s) (f s) z)
      (volume.restrict (uIoc (0 : Real) t)))
    (x w v : V) :
    heatDuhamelHessian t f x w v =
      heatD2Duhamel t v w (fun s => f s) x := by
  let L : (V →L[Real] F) →L[Real] F :=
    (ContinuousLinearMap.apply Real F) v
  have heval := L.hasFDerivAt.comp x
    (heatDuhamelGradientMap_hasFDerivAt halpha0 halpha1 ht f hbound hf
      hmeas1 hmeas2 x)
  have hfun : (fun z : V => L (heatDuhamelGradientMap t f z)) =
      heatD1Duhamel t v f := by
    funext z
    exact heatDuhamelGradientMap_apply ht f hbound z (hmeas1 z) v
  have heval' : HasFDerivAt (heatD1Duhamel t v f)
      (L.comp (heatDuhamelHessian t f x)) x := by
    rw [← hfun]
    exact heval.congr_of_eventuallyEq <|
      Filter.Eventually.of_forall fun _ => rfl
  have hraw := heatD1Duhamel_hasFDerivAt halpha0 halpha1 ht f hbound hf v
    (heatD1Sup_time_aestronglyMeasurable ht f hmeas1 v)
    (heatD2ConvolutionMap_time_aestronglyMeasurable ht f hmeas2 v) x
  have hmaps := heval'.unique hraw
  have happly := congrArg (fun A : V →L[Real] F => A w) hmaps
  simpa only [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    heatD2DuhamelMap_apply halpha0 halpha1 ht f hf v x
      (heatD2ConvolutionMap_time_aestronglyMeasurable ht f hmeas2 v x)] using happly

theorem heatDuhamel_iteratedFDeriv_two_apply
    {alpha K B : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t)
    (f : Real → BoundedContinuousFunction V F)
    (hbound : ∀ s ∈ Icc (0 : Real) t, ‖f s‖ ≤ B)
    (hf : ∀ s ∈ Icc (0 : Real) t, HolderWith K alpha (f s))
    (hmeas0 : ∀ z : V, AEStronglyMeasurable
      (fun s : Real => heatSup (t - s) (f s) z)
      (volume.restrict (uIoc (0 : Real) t)))
    (hmeas1 : ∀ z : V, AEStronglyMeasurable
      (fun s : Real => heatSupGradient (t - s) (f s) z)
      (volume.restrict (uIoc (0 : Real) t)))
    (hmeas2 : ∀ z : V, AEStronglyMeasurable
      (fun s : Real => heatSupHessian (t - s) (f s) z)
      (volume.restrict (uIoc (0 : Real) t)))
    (x : V) (m : Fin 2 → V) :
    iteratedFDeriv Real 2 (heatDuhamel t f) x m =
      heatD2Duhamel t (m 1) (m 0) (fun s => f s) x := by
  rw [iteratedFDeriv_two_apply]
  have hgrad : fderiv Real (heatDuhamel t f) = heatDuhamelGradientMap t f := by
    funext z
    exact (heatDuhamel_hasFDerivAt ht f hbound hmeas0 hmeas1 z).fderiv
  rw [hgrad,
    (heatDuhamelGradientMap_hasFDerivAt halpha0 halpha1 ht f hbound hf
      hmeas1 hmeas2 x).fderiv]
  exact heatDuhamelHessian_apply halpha0 halpha1 ht f hbound hf hmeas1 hmeas2
    x (m 0) (m 1)

theorem heatDuhamel_parabolicSpatialJet_two
    {alpha K B : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t)
    (f : Real → BoundedContinuousFunction V F)
    (hbound : ∀ s ∈ Icc (0 : Real) t, ‖f s‖ ≤ B)
    (hf : ∀ s ∈ Icc (0 : Real) t, HolderWith K alpha (f s))
    (hmeas0 : ∀ z : V, AEStronglyMeasurable
      (fun s : Real => heatSup (t - s) (f s) z)
      (volume.restrict (uIoc (0 : Real) t)))
    (hmeas1 : ∀ z : V, AEStronglyMeasurable
      (fun s : Real => heatSupGradient (t - s) (f s) z)
      (volume.restrict (uIoc (0 : Real) t)))
    (hmeas2 : ∀ z : V, AEStronglyMeasurable
      (fun s : Real => heatSupHessian (t - s) (f s) z)
      (volume.restrict (uIoc (0 : Real) t)))
    (x : V) (m : Fin 2 → V) :
    parabolicSpatialJet 2 (fun r : Real => heatDuhamel r f)
        (parabolicPoint t x) m =
      heatD2Duhamel t (m 0) (m 1) (fun s => f s) x := by
  unfold parabolicSpatialJet
  simp only [parabolicPoint_time, parabolicPoint_space]
  rw [heatDuhamel_iteratedFDeriv_two_apply halpha0 halpha1 ht f hbound hf
    hmeas0 hmeas1 hmeas2]
  exact heatD2Duhamel_comm t (m 1) (m 0) (fun s => f s) x

end HeatEquation

end
