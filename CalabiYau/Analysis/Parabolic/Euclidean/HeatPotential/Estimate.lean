-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Parabolic/Euclidean/HeatPotential/Estimate.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Parabolic.Euclidean.HeatPotential.Measurability

@[expose] public section

-- and its private helpers occur in public declarations.

noncomputable section

open MeasureTheory Real Set
open scoped Interval NNReal RealInnerProductSpace Topology

namespace HeatEquation

open CalabiYau.Schauder

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
  [MeasurableSpace V] [BorelSpace V]

variable [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F] in
def heatPotentialSchauderConst
    (alpha K B Csource : NNReal) (T : Real) : NNReal :=
  (heatPotentialC2HolderGaugeConst (V := V) alpha K B Csource
    (Real.toNNReal (T * (B : Real)))
    (Real.toNNReal (2 * (B : Real) * heatC1 V * Real.sqrt T)) T).toNNReal

variable [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F] in
def heatDuhamelConstSchauderConst
    (alpha K B : NNReal) (T : Real) : NNReal :=
  4 * heatPotentialSchauderConst (V := V) alpha K B K T

private theorem real_toNNReal_nnreal_mul (c : NNReal) (x : Real) :
    Real.toNNReal ((c : Real) * x) = c * Real.toNNReal x := by
  rw [Real.toNNReal_mul c.coe_nonneg, Real.toNNReal_coe]

private theorem d2DuhamelHolderConst_nnreal_mul
    (alpha : NNReal) (v w : V) (c K : NNReal) :
    d2DuhamelHolderConst alpha v w (c * K) =
      (c : Real) * d2DuhamelHolderConst alpha v w K := by
  simp [d2DuhamelHolderConst]
  ring

private theorem d2DuhamelSpaceHolderConst_nnreal_mul
    (alpha : NNReal) (v w : V) (c K : NNReal) :
    d2DuhamelSpaceHolderConst alpha v w (c * K) =
      (c : Real) * d2DuhamelSpaceHolderConst alpha v w K := by
  simp [d2DuhamelSpaceHolderConst]
  ring

private theorem d2DuhamelTimeHolderConst_nnreal_mul
    (alpha : NNReal) (v w : V) (c K : NNReal) :
    d2DuhamelTimeHolderConst alpha v w (c * K) =
      (c : Real) * d2DuhamelTimeHolderConst alpha v w K := by
  simp [d2DuhamelTimeHolderConst]
  ring

private theorem d2DuhamelParabolicHolderConst_nnreal_mul
    (alpha : NNReal) (v w : V) (c K : NNReal) :
    d2DuhamelParabolicHolderConst alpha v w (c * K) =
      (c : Real) * d2DuhamelParabolicHolderConst alpha v w K := by
  rw [d2DuhamelParabolicHolderConst, d2DuhamelParabolicHolderConst,
    d2DuhamelSpaceHolderConst_nnreal_mul, d2DuhamelTimeHolderConst_nnreal_mul]
  ring

private theorem d2DuhamelJetNormConst_nnreal_mul
    (alpha : NNReal) (c K : NNReal) (T : Real) :
    d2DuhamelJetNormConst (V := V) alpha (c * K) T =
      c * d2DuhamelJetNormConst (V := V) alpha K T := by
  rw [d2DuhamelJetNormConst, d2DuhamelJetNormConst, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro beta hbeta
  rw [d2DuhamelHolderConst_nnreal_mul]
  rw [show (c : Real) * d2DuhamelHolderConst alpha
      ((stdOrthonormalBasis Real V) (beta 0))
      ((stdOrthonormalBasis Real V) (beta 1)) K *
        ((2 / (alpha : Real)) * T ^ ((alpha : Real) / 2)) =
      (c : Real) * (d2DuhamelHolderConst alpha
        ((stdOrthonormalBasis Real V) (beta 0))
        ((stdOrthonormalBasis Real V) (beta 1)) K *
          ((2 / (alpha : Real)) * T ^ ((alpha : Real) / 2))) by ring]
  exact real_toNNReal_nnreal_mul c _

private theorem d2DuhamelJetHolderConst_nnreal_mul
    (alpha : NNReal) (c K : NNReal) :
    d2DuhamelJetHolderConst (V := V) alpha (c * K) =
      c * d2DuhamelJetHolderConst (V := V) alpha K := by
  rw [d2DuhamelJetHolderConst, d2DuhamelJetHolderConst, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro beta hbeta
  rw [d2DuhamelParabolicHolderConst_nnreal_mul,
    real_toNNReal_nnreal_mul]

private theorem lapDuhamelNormConst_nnreal_mul
    (alpha : NNReal) (c K : NNReal) (T : Real) :
    lapDuhamelNormConst (V := V) alpha (c * K) T =
      c * lapDuhamelNormConst (V := V) alpha K T := by
  rw [lapDuhamelNormConst, lapDuhamelNormConst, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [d2DuhamelHolderConst_nnreal_mul]
  rw [show (c : Real) * d2DuhamelHolderConst alpha
      ((stdOrthonormalBasis Real V) i)
      ((stdOrthonormalBasis Real V) i) K *
        ((2 / (alpha : Real)) * T ^ ((alpha : Real) / 2)) =
      (c : Real) * (d2DuhamelHolderConst alpha
        ((stdOrthonormalBasis Real V) i)
        ((stdOrthonormalBasis Real V) i) K *
          ((2 / (alpha : Real)) * T ^ ((alpha : Real) / 2))) by ring]
  exact real_toNNReal_nnreal_mul c _

private theorem lapDuhamelParabolicHolderConst_nnreal_mul
    (alpha : NNReal) (c K : NNReal) :
    lapDuhamelParabolicHolderConst (V := V) alpha (c * K) =
      (c : Real) * lapDuhamelParabolicHolderConst (V := V) alpha K := by
  rw [lapDuhamelParabolicHolderConst, lapDuhamelParabolicHolderConst,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact d2DuhamelParabolicHolderConst_nnreal_mul alpha _ _ c K

private theorem heatPotentialC2HolderGaugeConst_nnreal_mul
    (alpha : NNReal) (c K B Csource C0 C1 : NNReal) (T : Real) :
    heatPotentialC2HolderGaugeConst (V := V)
        alpha (c * K) (c * B) (c * Csource) (c * C0) (c * C1) T =
      c * heatPotentialC2HolderGaugeConst (V := V)
        alpha K B Csource C0 C1 T := by
  rw [heatPotentialC2HolderGaugeConst, heatPotentialC2HolderGaugeConst,
    d2DuhamelJetNormConst_nnreal_mul, lapDuhamelNormConst_nnreal_mul,
    d2DuhamelJetHolderConst_nnreal_mul,
    lapDuhamelParabolicHolderConst_nnreal_mul,
    real_toNNReal_nnreal_mul]
  push_cast
  ring

theorem heatPotentialSchauderConst_nnreal_mul
    (alpha : NNReal) (c K B Csource : NNReal) (T : Real) :
    heatPotentialSchauderConst (V := V)
        alpha (c * K) (c * B) (c * Csource) T =
      c * heatPotentialSchauderConst (V := V) alpha K B Csource T := by
  have hC0 : Real.toNNReal (T * ((c * B : NNReal) : Real)) =
      c * Real.toNNReal (T * (B : Real)) := by
    rw [show T * ((c * B : NNReal) : Real) =
      (c : Real) * (T * (B : Real)) by push_cast; ring,
      real_toNNReal_nnreal_mul]
  have hC1 : Real.toNNReal
      (2 * ((c * B : NNReal) : Real) * heatC1 V * Real.sqrt T) =
      c * Real.toNNReal
        (2 * (B : Real) * heatC1 V * Real.sqrt T) := by
    rw [show 2 * ((c * B : NNReal) : Real) * heatC1 V * Real.sqrt T =
      (c : Real) *
        (2 * (B : Real) * heatC1 V * Real.sqrt T) by push_cast; ring,
      real_toNNReal_nnreal_mul]
  unfold heatPotentialSchauderConst
  rw [hC0, hC1, heatPotentialC2HolderGaugeConst_nnreal_mul,
    ENNReal.toNNReal_mul, ENNReal.toNNReal_coe]

theorem heatDuhamelConstSchauderConst_nnreal_mul
    (alpha : NNReal) (c K B : NNReal) (T : Real) :
    heatDuhamelConstSchauderConst (V := V) alpha (c * K) (c * B) T =
      c * heatDuhamelConstSchauderConst (V := V) alpha K B T := by
  rw [heatDuhamelConstSchauderConst, heatDuhamelConstSchauderConst,
    heatPotentialSchauderConst_nnreal_mul]
  ring

private theorem d2DuhamelHolderConst_add
    (alpha : NNReal) (v w : V) (K₁ K₂ : NNReal) :
    d2DuhamelHolderConst alpha v w (K₁ + K₂) =
      d2DuhamelHolderConst alpha v w K₁ +
        d2DuhamelHolderConst alpha v w K₂ := by
  simp [d2DuhamelHolderConst]
  ring

private theorem d2DuhamelSpaceHolderConst_add
    (alpha : NNReal) (v w : V) (K₁ K₂ : NNReal) :
    d2DuhamelSpaceHolderConst alpha v w (K₁ + K₂) =
      d2DuhamelSpaceHolderConst alpha v w K₁ +
        d2DuhamelSpaceHolderConst alpha v w K₂ := by
  simp [d2DuhamelSpaceHolderConst]
  ring

private theorem d2DuhamelTimeHolderConst_add
    (alpha : NNReal) (v w : V) (K₁ K₂ : NNReal) :
    d2DuhamelTimeHolderConst alpha v w (K₁ + K₂) =
      d2DuhamelTimeHolderConst alpha v w K₁ +
        d2DuhamelTimeHolderConst alpha v w K₂ := by
  simp [d2DuhamelTimeHolderConst]
  ring

private theorem d2DuhamelParabolicHolderConst_add
    (alpha : NNReal) (v w : V) (K₁ K₂ : NNReal) :
    d2DuhamelParabolicHolderConst alpha v w (K₁ + K₂) =
      d2DuhamelParabolicHolderConst alpha v w K₁ +
        d2DuhamelParabolicHolderConst alpha v w K₂ := by
  rw [d2DuhamelParabolicHolderConst, d2DuhamelParabolicHolderConst,
    d2DuhamelParabolicHolderConst,
    d2DuhamelSpaceHolderConst_add, d2DuhamelTimeHolderConst_add]
  ring

private theorem d2DuhamelHolderConst_nonneg'
    (alpha : NNReal) (v w : V) (K : NNReal) :
    0 ≤ d2DuhamelHolderConst alpha v w K := by
  unfold d2DuhamelHolderConst
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (norm_nonneg v) (norm_nonneg w)) K.coe_nonneg)
    (heatC2Holder_nonneg (V := V) alpha)

private theorem d2DuhamelJetNormConst_add
    {alpha : NNReal} (K₁ K₂ : NNReal)
    {T : Real} (hT : 0 ≤ T) :
    d2DuhamelJetNormConst (V := V) alpha (K₁ + K₂) T =
      d2DuhamelJetNormConst (V := V) alpha K₁ T +
        d2DuhamelJetNormConst (V := V) alpha K₂ T := by
  rw [d2DuhamelJetNormConst, d2DuhamelJetNormConst, d2DuhamelJetNormConst,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro beta hbeta
  rw [d2DuhamelHolderConst_add]
  rw [show (d2DuhamelHolderConst alpha
        ((stdOrthonormalBasis Real V) (beta 0))
        ((stdOrthonormalBasis Real V) (beta 1)) K₁ +
      d2DuhamelHolderConst alpha
        ((stdOrthonormalBasis Real V) (beta 0))
        ((stdOrthonormalBasis Real V) (beta 1)) K₂) *
        ((2 / (alpha : Real)) * T ^ ((alpha : Real) / 2)) =
      d2DuhamelHolderConst alpha
          ((stdOrthonormalBasis Real V) (beta 0))
          ((stdOrthonormalBasis Real V) (beta 1)) K₁ *
          ((2 / (alpha : Real)) * T ^ ((alpha : Real) / 2)) +
        d2DuhamelHolderConst alpha
          ((stdOrthonormalBasis Real V) (beta 0))
          ((stdOrthonormalBasis Real V) (beta 1)) K₂ *
          ((2 / (alpha : Real)) * T ^ ((alpha : Real) / 2)) by ring,
    Real.toNNReal_add]
  · exact mul_nonneg (d2DuhamelHolderConst_nonneg' alpha _ _ K₁)
      (mul_nonneg (div_nonneg (by norm_num) alpha.coe_nonneg)
        (Real.rpow_nonneg hT _))
  · exact mul_nonneg (d2DuhamelHolderConst_nonneg' alpha _ _ K₂)
      (mul_nonneg (div_nonneg (by norm_num) alpha.coe_nonneg)
        (Real.rpow_nonneg hT _))

private theorem d2DuhamelJetHolderConst_add
    {alpha : NNReal} (halpha1 : alpha < 1) (K₁ K₂ : NNReal) :
    d2DuhamelJetHolderConst (V := V) alpha (K₁ + K₂) =
      d2DuhamelJetHolderConst (V := V) alpha K₁ +
        d2DuhamelJetHolderConst (V := V) alpha K₂ := by
  rw [d2DuhamelJetHolderConst, d2DuhamelJetHolderConst,
    d2DuhamelJetHolderConst, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro beta hbeta
  rw [d2DuhamelParabolicHolderConst_add, Real.toNNReal_add]
  · exact d2DuhamelParabolicHolderConst_nonneg halpha1.le _ _ K₁
  · exact d2DuhamelParabolicHolderConst_nonneg halpha1.le _ _ K₂

private theorem lapDuhamelNormConst_add
    {alpha : NNReal} (K₁ K₂ : NNReal)
    {T : Real} (hT : 0 ≤ T) :
    lapDuhamelNormConst (V := V) alpha (K₁ + K₂) T =
      lapDuhamelNormConst (V := V) alpha K₁ T +
        lapDuhamelNormConst (V := V) alpha K₂ T := by
  rw [lapDuhamelNormConst, lapDuhamelNormConst, lapDuhamelNormConst,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [d2DuhamelHolderConst_add]
  rw [show (d2DuhamelHolderConst alpha
        ((stdOrthonormalBasis Real V) i)
        ((stdOrthonormalBasis Real V) i) K₁ +
      d2DuhamelHolderConst alpha
        ((stdOrthonormalBasis Real V) i)
        ((stdOrthonormalBasis Real V) i) K₂) *
        ((2 / (alpha : Real)) * T ^ ((alpha : Real) / 2)) =
      d2DuhamelHolderConst alpha
          ((stdOrthonormalBasis Real V) i)
          ((stdOrthonormalBasis Real V) i) K₁ *
          ((2 / (alpha : Real)) * T ^ ((alpha : Real) / 2)) +
        d2DuhamelHolderConst alpha
          ((stdOrthonormalBasis Real V) i)
          ((stdOrthonormalBasis Real V) i) K₂ *
          ((2 / (alpha : Real)) * T ^ ((alpha : Real) / 2)) by ring,
    Real.toNNReal_add]
  · exact mul_nonneg (d2DuhamelHolderConst_nonneg' alpha _ _ K₁)
      (mul_nonneg (div_nonneg (by norm_num) alpha.coe_nonneg)
        (Real.rpow_nonneg hT _))
  · exact mul_nonneg (d2DuhamelHolderConst_nonneg' alpha _ _ K₂)
      (mul_nonneg (div_nonneg (by norm_num) alpha.coe_nonneg)
        (Real.rpow_nonneg hT _))

private theorem lapDuhamelParabolicHolderConst_add
    (alpha : NNReal) (K₁ K₂ : NNReal) :
    lapDuhamelParabolicHolderConst (V := V) alpha (K₁ + K₂) =
      lapDuhamelParabolicHolderConst (V := V) alpha K₁ +
        lapDuhamelParabolicHolderConst (V := V) alpha K₂ := by
  rw [lapDuhamelParabolicHolderConst, lapDuhamelParabolicHolderConst,
    lapDuhamelParabolicHolderConst, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact d2DuhamelParabolicHolderConst_add alpha _ _ K₁ K₂

private theorem lapDuhamelParabolicHolderConst_nonneg'
    {alpha : NNReal} (halpha1 : alpha < 1) (K : NNReal) :
    0 ≤ lapDuhamelParabolicHolderConst (V := V) alpha K := by
  unfold lapDuhamelParabolicHolderConst
  exact Finset.sum_nonneg fun i hi ↦
    d2DuhamelParabolicHolderConst_nonneg halpha1.le _ _ K

private theorem heatPotentialC2HolderGaugeConst_add
    {alpha : NNReal} (halpha1 : alpha < 1)
    (K₁ K₂ B₁ B₂ Csource₁ Csource₂ C0₁ C0₂ C1₁ C1₂ : NNReal)
    {T : Real} (hT : 0 ≤ T) :
    heatPotentialC2HolderGaugeConst (V := V) alpha
        (K₁ + K₂) (B₁ + B₂) (Csource₁ + Csource₂)
        (C0₁ + C0₂) (C1₁ + C1₂) T =
      heatPotentialC2HolderGaugeConst (V := V)
          alpha K₁ B₁ Csource₁ C0₁ C1₁ T +
        heatPotentialC2HolderGaugeConst (V := V)
          alpha K₂ B₂ Csource₂ C0₂ C1₂ T := by
  rw [heatPotentialC2HolderGaugeConst,
    heatPotentialC2HolderGaugeConst,
    heatPotentialC2HolderGaugeConst,
    d2DuhamelJetNormConst_add K₁ K₂ hT,
    lapDuhamelNormConst_add K₁ K₂ hT,
    d2DuhamelJetHolderConst_add halpha1 K₁ K₂,
    lapDuhamelParabolicHolderConst_add]
  rw [Real.toNNReal_add
    (lapDuhamelParabolicHolderConst_nonneg' halpha1 K₁)
    (lapDuhamelParabolicHolderConst_nonneg' halpha1 K₂)]
  push_cast
  ring

theorem heatPotentialSchauderConst_add
    {alpha : NNReal} (halpha1 : alpha < 1)
    (K₁ K₂ B₁ B₂ Csource₁ Csource₂ : NNReal)
    {T : Real} (hT : 0 ≤ T) :
    heatPotentialSchauderConst (V := V) alpha
        (K₁ + K₂) (B₁ + B₂) (Csource₁ + Csource₂) T =
      heatPotentialSchauderConst (V := V) alpha K₁ B₁ Csource₁ T +
        heatPotentialSchauderConst (V := V) alpha K₂ B₂ Csource₂ T := by
  have hC0 : Real.toNNReal (T * ((B₁ + B₂ : NNReal) : Real)) =
      Real.toNNReal (T * (B₁ : Real)) +
        Real.toNNReal (T * (B₂ : Real)) := by
    rw [show T * ((B₁ + B₂ : NNReal) : Real) =
      T * (B₁ : Real) + T * (B₂ : Real) by push_cast; ring,
      Real.toNNReal_add]
    · exact mul_nonneg hT B₁.coe_nonneg
    · exact mul_nonneg hT B₂.coe_nonneg
  have hC1 : Real.toNNReal
      (2 * ((B₁ + B₂ : NNReal) : Real) * heatC1 V * Real.sqrt T) =
      Real.toNNReal (2 * (B₁ : Real) * heatC1 V * Real.sqrt T) +
        Real.toNNReal
          (2 * (B₂ : Real) * heatC1 V * Real.sqrt T) := by
    rw [show 2 * ((B₁ + B₂ : NNReal) : Real) * heatC1 V * Real.sqrt T =
      2 * (B₁ : Real) * heatC1 V * Real.sqrt T +
        2 * (B₂ : Real) * heatC1 V * Real.sqrt T by push_cast; ring,
      Real.toNNReal_add]
    · exact mul_nonneg
        (mul_nonneg (mul_nonneg (by positivity) B₁.coe_nonneg)
          (heatC1_nonneg (V := V))) (Real.sqrt_nonneg T)
    · exact mul_nonneg
        (mul_nonneg (mul_nonneg (by positivity) B₂.coe_nonneg)
          (heatC1_nonneg (V := V))) (Real.sqrt_nonneg T)
  unfold heatPotentialSchauderConst
  rw [hC0, hC1, heatPotentialC2HolderGaugeConst_add halpha1
    K₁ K₂ B₁ B₂ Csource₁ Csource₂
    (Real.toNNReal (T * (B₁ : Real)))
    (Real.toNNReal (T * (B₂ : Real)))
    (Real.toNNReal
      (2 * (B₁ : Real) * heatC1 V * Real.sqrt T))
    (Real.toNNReal
      (2 * (B₂ : Real) * heatC1 V * Real.sqrt T)) hT,
    ENNReal.toNNReal_add]
  · simp [heatPotentialC2HolderGaugeConst]
  · simp [heatPotentialC2HolderGaugeConst]

theorem heatDuhamelConstSchauderConst_add
    {alpha : NNReal} (halpha1 : alpha < 1)
    (K₁ K₂ B₁ B₂ : NNReal) {T : Real} (hT : 0 ≤ T) :
    heatDuhamelConstSchauderConst (V := V) alpha
        (K₁ + K₂) (B₁ + B₂) T =
      heatDuhamelConstSchauderConst (V := V) alpha K₁ B₁ T +
        heatDuhamelConstSchauderConst (V := V) alpha K₂ B₂ T := by
  rw [heatDuhamelConstSchauderConst, heatDuhamelConstSchauderConst,
    heatDuhamelConstSchauderConst,
    heatPotentialSchauderConst_add halpha1 K₁ K₂ B₁ B₂ K₁ K₂ hT]
  ring

variable [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F] in
theorem coe_heatPotentialSchauderConst
    (alpha K B Csource : NNReal) (T : Real) :
    (heatPotentialSchauderConst (V := V) alpha K B Csource T : ENNReal) =
      heatPotentialC2HolderGaugeConst (V := V) alpha K B Csource
        (Real.toNNReal (T * (B : Real)))
        (Real.toNNReal (2 * (B : Real) * heatC1 V * Real.sqrt T)) T := by
  apply ENNReal.coe_toNNReal
  simp [heatPotentialC2HolderGaugeConst]

variable [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F] in
theorem heatDuhamelGradientMap_norm_le
    {t : Real} (ht : 0 < t) {B : NNReal}
    (f : Real → BoundedContinuousFunction V F)
    (hbound : ∀ s ∈ Icc (0 : Real) t, ‖f s‖ ≤ B)
    (x : V)
    (hmeas : AEStronglyMeasurable
      (fun s : Real => heatSupGradient (t - s) (f s) x)
      (volume.restrict (uIoc (0 : Real) t))) :
    ‖heatDuhamelGradientMap t f x‖ ≤
      2 * (B : Real) * heatC1 V * Real.sqrt t := by
  have hint := heatDuhamelGradient_int (V := V) ht f hbound x hmeas
  have hmajor := heatDuhamelGradientMajor_intble (V := V) (t := t) B
  unfold heatDuhamelGradientMap
  calc
    ‖∫ s : Real in 0..t, heatSupGradient (t - s) (f s) x‖ ≤
        ∫ s : Real in 0..t, ‖heatSupGradient (t - s) (f s) x‖ :=
      intervalIntegral.norm_integral_le_integral_norm ht.le
    _ ≤ ∫ s : Real in 0..t, heatDuhamelGradientMajor (V := V) B t s := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo ht.le hint.norm hmajor
      intro s hs
      have hpos : 0 < t - s := sub_pos.mpr hs.2
      calc
        ‖heatSupGradient (t - s) (f s) x‖ ≤
            (heatScale (t - s))⁻¹ * heatC1 V * ‖f s‖ :=
          heatSupGradient_norm_le hpos (f s) x
        _ ≤ (heatScale (t - s))⁻¹ * heatC1 V * (B : Real) :=
          mul_le_mul_of_nonneg_left (hbound s ⟨hs.1.le, hs.2.le⟩)
            (mul_nonneg (inv_nonneg.mpr (heatScale_pos hpos).le)
              (heatC1_nonneg (V := V)))
        _ = heatDuhamelGradientMajor (V := V) B t s := by
          rw [← heatScale12_eq hpos]
          unfold heatDuhamelGradientMajor
          ring
    _ = 2 * (B : Real) * heatC1 V * Real.sqrt t := by
      unfold heatDuhamelGradientMajor
      rw [intervalIntegral.integral_const_mul, timeScale12_int,
        Real.sqrt_eq_rpow]
      ring

variable [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F] in
theorem heatDuhamel_fderiv_norm_le
    {t : Real} (ht : 0 < t) {B : NNReal}
    (f : Real → BoundedContinuousFunction V F)
    (hbound : ∀ s ∈ Icc (0 : Real) t, ‖f s‖ ≤ B)
    (hmeas0 : ∀ z : V, AEStronglyMeasurable
      (fun s : Real => heatSup (t - s) (f s) z)
      (volume.restrict (uIoc (0 : Real) t)))
    (hmeas1 : ∀ z : V, AEStronglyMeasurable
      (fun s : Real => heatSupGradient (t - s) (f s) z)
      (volume.restrict (uIoc (0 : Real) t)))
    (x : V) :
    ‖fderiv Real (heatDuhamel t f) x‖ ≤
      2 * (B : Real) * heatC1 V * Real.sqrt t := by
  rw [(heatDuhamel_hasFDerivAt ht f hbound hmeas0 hmeas1 x).fderiv]
  exact heatDuhamelGradientMap_norm_le ht f hbound x (hmeas1 x)

variable [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F] in
theorem heatDuhamel_schauder_estimate
    {alpha K B Csource : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {S T : Real} (hT : 0 ≤ T) (hTS : T < S)
    (f : Real → BoundedContinuousFunction V F)
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
      heatPotentialSchauderConst (V := V) alpha K B Csource T := by
  rw [coe_heatPotentialSchauderConst]
  apply eParabolicC2HolderGaugeOn_heatDuhamel_le_of_lower_jets
    halpha0 halpha1 hT hTS f
  · intro p hp
    unfold parabolicSpatialJet
    rw [norm_iteratedFDeriv_zero]
    have hbound' : ∀ s ∈ Icc (0 : Real) p.time, ‖f s‖ ≤ B := by
      intro s hs
      exact hbound s ⟨hs.1, hs.2.trans (hp.1.2.trans hTS.le)⟩
    have hraw := heatDuhamel_norm hp.1.1 f hbound' p.space
      (hmeas0 p.time ⟨hp.1.1, hp.1.2.trans hTS.le⟩ p.space)
    have hTB : 0 ≤ T * (B : Real) := mul_nonneg hT B.coe_nonneg
    rw [Real.coe_toNNReal _ hTB]
    exact hraw.trans
      (mul_le_mul_of_nonneg_right hp.1.2 B.coe_nonneg)
  · intro p hp
    unfold parabolicSpatialJet
    rw [norm_iteratedFDeriv_one]
    have hbound' : ∀ s ∈ Icc (0 : Real) p.time, ‖f s‖ ≤ B := by
      intro s hs
      exact hbound s ⟨hs.1, hs.2.trans (hp.1.2.trans hTS.le)⟩
    have hraw := heatDuhamel_fderiv_norm_le hp.1.1 f hbound'
      (hmeas0 p.time ⟨hp.1.1, hp.1.2.trans hTS.le⟩)
      (hmeas1 p.time ⟨hp.1.1, hp.1.2.trans hTS.le⟩) p.space
    have hcoef : 0 ≤ 2 * (B : Real) * heatC1 V :=
      mul_nonneg (mul_nonneg (by positivity) B.coe_nonneg)
        (heatC1_nonneg (V := V))
    have hC : 0 ≤ 2 * (B : Real) * heatC1 V * Real.sqrt T :=
      mul_nonneg hcoef (Real.sqrt_nonneg T)
    rw [Real.coe_toNNReal _ hC]
    exact hraw.trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt hp.1.2) hcoef)
  · exact hbound
  · exact hf
  · exact hsource
  · exact hmeas0
  · exact hmeas1
  · exact hmeas2

variable [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F] in
theorem heatDuhamel_schauder_estimate_of_parabolic_holder
    {alpha K B : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {S T : Real} (hT : 0 ≤ T) (hTS : T < S)
    (f : Real → BoundedContinuousFunction V F)
    (hbound : ∀ r ∈ Icc (0 : Real) S, ‖f r‖ ≤ B)
    (hsource : HolderWith K alpha
      ((parabolicCylinder (Icc (0 : Real) S) Set.univ).domRestrict
        (fun p => f p.time p.space))) :
    eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Ioc (0 : Real) T) Set.univ)
      (fun t x => heatDuhamel t f x) ≤
      heatPotentialSchauderConst (V := V) alpha K B K T := by
  have hf : ∀ r ∈ Icc (0 : Real) S, HolderWith K alpha (f r) :=
    fun r hr => holderWith_slice_of_parabolicCylinder
      (f := fun s x => f s x) hsource hr
  have hsource' : HolderWith K alpha
      ((parabolicCylinder (Ioc (0 : Real) S) Set.univ).domRestrict
        (fun p => f p.time p.space)) := by
    rw [HolderWith.restrict_iff] at hsource ⊢
    exact hsource.mono fun p hp => ⟨⟨hp.1.1.le, hp.1.2⟩, hp.2⟩
  exact heatDuhamel_schauder_estimate halpha0 halpha1 hT hTS f hbound hf
    hsource'
    (fun t ht z =>
      heatSup_timeSource_aestronglyMeasurable_of_parabolic_holder
        halpha0 ht f hsource z)
    (fun t ht z =>
      heatSupGradient_timeSource_aestronglyMeasurable_of_parabolic_holder
        halpha0 ht f hsource z)
    (fun t ht z =>
      heatSupHessian_timeSource_aestronglyMeasurable_of_parabolic_holder
        halpha0 ht f hsource z)

variable [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F] in
theorem heatDuhamel_const_schauder_estimate
    {alpha K B : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {S T : Real} (hT : 0 < T) (hTS : T < S)
    (f : BoundedContinuousFunction V F)
    (hbound : ‖f‖ ≤ B) (hholder : HolderWith K alpha f) :
    eContDiffHolderGaugeOn 2 alpha Set.univ
      (heatDuhamel T (fun _ => f)) ≤
      heatDuhamelConstSchauderConst (V := V) alpha K B T := by
  have hpar := heatDuhamel_schauder_estimate_of_parabolic_holder
    halpha0 halpha1 hT.le hTS (fun _ => f)
    (fun _ _ => hbound)
    (holderWith_parabolic_const_time f hholder (Icc (0 : Real) S))
  have hslice := eContDiffHolderGaugeOn_slice_le
    (t := T) (J := Ioc (0 : Real) T) ⟨hT, le_rfl⟩ hpar
  unfold heatDuhamelConstSchauderConst
  convert hslice using 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    ENNReal.coe_mul, ENNReal.coe_ofNat]
  ring

end HeatEquation

end
