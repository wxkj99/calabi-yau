-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Parabolic/Euclidean/HeatKernel/Duhamel/LowerOrder.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Parabolic.Euclidean.HeatKernel.Duhamel.Basic
public import CalabiYau.Analysis.Parabolic.Euclidean.HeatKernel.Convolution.Supremum

@[expose] public section


noncomputable section

open MeasureTheory Real Set
open scoped NNReal RealInnerProductSpace

namespace HeatEquation

section ValuePotential

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

section

variable [MeasurableSpace V] [BorelSpace V] [Nontrivial V] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def d0DuhamelMajor (K : ℝ≥0) : ℝ := K

theorem d0DuhamelMajor_intble (t : ℝ) (K : ℝ≥0) :
    IntervalIntegrable (fun _ : ℝ => d0DuhamelMajor K) volume 0 t := by
  simpa only [d0DuhamelMajor] using
    (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => (K : ℝ)) volume 0 t)

theorem d0DuhamelMajor_int (t : ℝ) (K : ℝ≥0) :
    ∫ _ : ℝ in 0..t, d0DuhamelMajor K = t * (K : ℝ) := by
  simp only [d0DuhamelMajor, intervalIntegral.integral_const, sub_zero,
    smul_eq_mul]

def heatDuhamel (t : ℝ) (f : ℝ → BoundedContinuousFunction V F) (x : V) : F :=
  ∫ s : ℝ in 0..t, heatSup (t - s) (f s) x

end

section

variable [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem heatDuhamel_const_eq_integral_heatSup
    (t : Real) (f : BoundedContinuousFunction V F) (x : V) :
    heatDuhamel t (fun _ ↦ f) x =
      ∫ s : Real in 0..t, heatSup s f x := by
  unfold heatDuhamel
  rw [intervalIntegral.integral_comp_sub_left
    (fun s : Real ↦ heatSup s f x) t]
  simp

end

section

variable [MeasurableSpace V] [BorelSpace V] [Nontrivial V] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem heatDuhamel_int {t : ℝ} (ht : 0 < t) {K : ℝ≥0}
    (f : ℝ → BoundedContinuousFunction V F)
    (hf : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖f s‖ ≤ K) (x : V)
    (hmeas : AEStronglyMeasurable
      (fun s : ℝ => heatSup (t - s) (f s) x)
      (volume.restrict (Set.uIoc (0 : ℝ) t))) :
    IntervalIntegrable
      (fun s : ℝ => heatSup (t - s) (f s) x) volume 0 t := by
  apply (d0DuhamelMajor_intble t K).mono_fun' hmeas
  have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ t := by
    simp [ae_iff, measure_singleton]
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (s := Set.uIoc (0 : ℝ) t) hne] with s hs hst
  rw [Set.uIoc_of_le ht.le] at hs
  have hstlt : s < t := lt_of_le_of_ne hs.2 hst
  calc
    ‖heatSup (t - s) (f s) x‖ ≤ ‖f s‖ :=
      heatSup_contract (sub_pos.mpr hstlt) (f s) x
    _ ≤ K := hf s ⟨hs.1.le, hs.2⟩
    _ = d0DuhamelMajor K := by rfl

theorem heatDuhamel_norm {t : ℝ} (ht : 0 < t) {K : ℝ≥0}
    (f : ℝ → BoundedContinuousFunction V F)
    (hf : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖f s‖ ≤ K) (x : V)
    (hmeas : AEStronglyMeasurable
      (fun s : ℝ => heatSup (t - s) (f s) x)
      (volume.restrict (Set.uIoc (0 : ℝ) t))) :
    ‖heatDuhamel t f x‖ ≤ t * (K : ℝ) := by
  have hint := heatDuhamel_int ht f hf x hmeas
  unfold heatDuhamel
  calc
    ‖∫ s : ℝ in 0..t, heatSup (t - s) (f s) x‖ ≤
        ∫ s : ℝ in 0..t, ‖heatSup (t - s) (f s) x‖ :=
      intervalIntegral.norm_integral_le_integral_norm ht.le
    _ ≤ ∫ _ : ℝ in 0..t, d0DuhamelMajor K := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo ht.le hint.norm
        (d0DuhamelMajor_intble t K)
      intro s hs
      calc
        ‖heatSup (t - s) (f s) x‖ ≤ ‖f s‖ :=
          heatSup_contract (sub_pos.mpr hs.2) (f s) x
        _ ≤ K := hf s ⟨hs.1.le, hs.2.le⟩
        _ = d0DuhamelMajor K := by rfl
    _ = t * (K : ℝ) := d0DuhamelMajor_int t K

end

end ValuePotential

section GradientPotential

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

section

variable [MeasurableSpace V] [BorelSpace V] [Nontrivial V] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def d1DuhamelConst (v : V) (K : ℝ≥0) : ℝ :=
  ‖v‖ * (K : ℝ) * heatC1 V

def d1DuhamelMajor (v : V) (K : ℝ≥0) (t s : ℝ) : ℝ :=
  d1DuhamelConst v K * heatScale12 (t - s)

end

section

variable [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem d1DuhamelMajor_intble {t : ℝ} (v : V) (K : ℝ≥0) :
    IntervalIntegrable (d1DuhamelMajor v K t) volume 0 t := by
  exact (scale12_intble).const_mul (d1DuhamelConst v K)

end

section

variable [MeasurableSpace V] [BorelSpace V] [Nontrivial V] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def heatD1Duhamel (t : ℝ) (v : V)
    (f : ℝ → BoundedContinuousFunction V F) (x : V) : F :=
  ∫ s : ℝ in 0..t, heatD1Sup (t - s) v (f s) x

end

section

variable [MeasurableSpace V] [BorelSpace V] [Nontrivial V] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem heatD1Duhamel_int {t : ℝ} (ht : 0 < t) {K : ℝ≥0}
    (f : ℝ → BoundedContinuousFunction V F)
    (hf : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖f s‖ ≤ K)
    (v x : V)
    (hmeas : AEStronglyMeasurable
      (fun s : ℝ => heatD1Sup (t - s) v (f s) x)
      (volume.restrict (Set.uIoc (0 : ℝ) t))) :
    IntervalIntegrable
      (fun s : ℝ => heatD1Sup (t - s) v (f s) x) volume 0 t := by
  apply (d1DuhamelMajor_intble v K).mono_fun' hmeas
  have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ t := by
    simp [ae_iff, measure_singleton]
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (s := Set.uIoc (0 : ℝ) t) hne] with s hs hst
  rw [Set.uIoc_of_le ht.le] at hs
  have hstlt : s < t := lt_of_le_of_ne hs.2 hst
  have hpos : 0 < t - s := sub_pos.mpr hstlt
  have hcoef : 0 ≤ ‖v‖ * (heatScale (t - s))⁻¹ * heatC1 V := by
    exact mul_nonneg
      (mul_nonneg (norm_nonneg _) (inv_nonneg.mpr (heatScale_pos hpos).le))
      (heatC1_nonneg (V := V))
  calc
    ‖heatD1Sup (t - s) v (f s) x‖ ≤
        (‖v‖ * (heatScale (t - s))⁻¹ * heatC1 V) * ‖f s‖ :=
      heatD1Sup_norm hpos v (f s) x
    _ ≤ (‖v‖ * (heatScale (t - s))⁻¹ * heatC1 V) * (K : ℝ) :=
      mul_le_mul_of_nonneg_left (hf s ⟨hs.1.le, hs.2⟩) hcoef
    _ = d1DuhamelMajor v K t s := by
      rw [← heatScale12_eq hpos]
      unfold d1DuhamelMajor d1DuhamelConst
      ring

end

end GradientPotential

end HeatEquation
