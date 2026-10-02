-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Integration/L2/Basic.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Riemannian.Volume.Properties
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Topology.Algebra.Support

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal

namespace CalabiYau.L2

open CalabiYau.RiemannianVolume

theorem abs_integral_mul_le_eLpNorm_two
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤ (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
  have habs :
      ENNReal.ofReal |∫ x, f x * g x ∂μ| ≤ eLpNorm f 2 μ * eLpNorm g 2 μ := by
    calc
      ENNReal.ofReal |∫ x, f x * g x ∂μ| ≤ ∫⁻ x, ‖f x * g x‖ₑ ∂μ := by
        rw [← Real.norm_eq_abs, ofReal_norm]
        exact enorm_integral_le_lintegral_enorm _
      _ = eLpNorm (fun x => g x * f x) 1 μ := by
        rw [eLpNorm_one_eq_lintegral_enorm]
        refine lintegral_congr fun x => ?_
        simp [enorm_mul, mul_comm]
      _ ≤ eLpNorm g 2 μ * eLpNorm f 2 μ := by
        have hmul : (fun x => g x * f x) = (g : α → ℝ) • (f : α → ℝ) := by
          funext x
          simp [smul_eq_mul]
        rw [hmul]
        let _ : ENNReal.HolderTriple (2 : ℝ≥0∞) (2 : ℝ≥0∞) 1 := by
          constructor
          rw [show (1 : ℝ≥0∞)⁻¹ = 1 by simp, ENNReal.inv_two_add_inv_two]
        exact eLpNorm_smul_le_mul_eLpNorm
          hf.aestronglyMeasurable hg.aestronglyMeasurable
      _ = eLpNorm f 2 μ * eLpNorm g 2 μ := mul_comm _ _
  have hfinite : eLpNorm f 2 μ * eLpNorm g 2 μ ≠ (⊤ : ℝ≥0∞) :=
    ENNReal.mul_ne_top hf.eLpNorm_lt_top.ne hg.eLpNorm_lt_top.ne
  have hreal := ENNReal.toReal_mono hfinite habs
  rw [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul] at hreal
  exact hreal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem aestronglyMeasurable_of_continuous
    {F : Type*} [NormedAddCommGroup F] [SecondCountableTopology F]
    {f : M → F} (hf : Continuous f) (μ : MeasureTheory.Measure M) :
    MeasureTheory.AEStronglyMeasurable f μ :=
  hf.aestronglyMeasurable

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
theorem aestronglyMeasurable_of_contMDiff
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [SecondCountableTopology F]
    {f : M → F} (hf : ContMDiff I 𝓘(ℝ, F) ∞ f) (μ : MeasureTheory.Measure M) :
    MeasureTheory.AEStronglyMeasurable f μ :=
  aestronglyMeasurable_of_continuous (M := M) hf.continuous μ

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
theorem aestronglyMeasurable_of_contMDiff_of_nat
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [SecondCountableTopology F]
    {n : WithTop ℕ∞} {f : M → F} (hf : ContMDiff I 𝓘(ℝ, F) n f)
    (μ : MeasureTheory.Measure M) :
    MeasureTheory.AEStronglyMeasurable f μ :=
  aestronglyMeasurable_of_continuous (M := M) hf.continuous μ

theorem integrable_of_continuous_of_hasCompactSupport
    {F : Type*} [NormedAddCommGroup F]
    {μ : MeasureTheory.Measure M} [IsFiniteMeasureOnCompacts μ]
    {f : M → F} (hfc : Continuous f) (hfsup : HasCompactSupport f) :
    MeasureTheory.Integrable f μ :=
  hfc.integrable_of_hasCompactSupport hfsup

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
theorem integrable_of_contMDiff_of_hasCompactSupport
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : MeasureTheory.Measure M} [IsFiniteMeasureOnCompacts μ]
    {f : M → F} (hfc : ContMDiff I 𝓘(ℝ, F) ∞ f) (hfsup : HasCompactSupport f) :
    MeasureTheory.Integrable f μ :=
  integrable_of_continuous_of_hasCompactSupport hfc.continuous hfsup

theorem integrable_of_continuous_compactSpace
    [T2Space M] [CompactSpace M]
    {F : Type*} [NormedAddCommGroup F]
    (g : SmoothRiemannianMetric I M)
    {f : M → F} (hf : Continuous f) :
    MeasureTheory.Integrable f (riemannianVolumeMeasure (I := I) (M := M) g) :=
  haveI : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
theorem integrable_of_contMDiff_compactSpace
    [CompactSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : MeasureTheory.Measure M} [IsFiniteMeasureOnCompacts μ]
    {f : M → F} (hf : ContMDiff I 𝓘(ℝ, F) ∞ f) :
    MeasureTheory.Integrable f μ :=
  integrable_of_contMDiff_of_hasCompactSupport hf (HasCompactSupport.of_compactSpace f)

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
theorem lpNorm_two_sq_eq_integral_sq
    {μ : MeasureTheory.Measure M} {f : M → ℝ}
    (hf : MeasureTheory.AEStronglyMeasurable f μ) :
    MeasureTheory.lpNorm f 2 μ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
    (by norm_num) (by norm_num) hf]
  norm_num only [ENNReal.toReal_ofNat]
  have hnonneg : 0 ≤ ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ :=
    MeasureTheory.integral_nonneg (fun x => by positivity)
  rw [← Real.sqrt_eq_rpow]
  rw [sq, Real.mul_self_sqrt hnonneg]
  congr 1
  funext x
  rw [Real.norm_eq_abs]
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact sq_abs (f x)

theorem integral_add_of_riemannianVolume
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : MeasureTheory.Measure M}
    {f f' : M → F}
    (hf : MeasureTheory.Integrable f μ)
    (hf' : MeasureTheory.Integrable f' μ) :
    ∫ x, (f x + f' x) ∂μ = (∫ x, f x ∂μ) + (∫ x, f' x ∂μ) :=
  MeasureTheory.integral_add hf hf'

theorem integral_smul_of_riemannianVolume
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : MeasureTheory.Measure M}
    (c : ℝ) (f : M → F) :
    ∫ x, c • f x ∂μ = c • ∫ x, f x ∂μ :=
  MeasureTheory.integral_smul c f

theorem integral_sub_of_riemannianVolume
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : MeasureTheory.Measure M}
    {f f' : M → F}
    (hf : MeasureTheory.Integrable f μ)
    (hf' : MeasureTheory.Integrable f' μ) :
    ∫ x, (f x - f' x) ∂μ = (∫ x, f x ∂μ) - (∫ x, f' x ∂μ) :=
  MeasureTheory.integral_sub hf hf'

theorem integral_neg_of_riemannianVolume
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : MeasureTheory.Measure M} (f : M → F) :
    ∫ x, -f x ∂μ = -∫ x, f x ∂μ :=
  MeasureTheory.integral_neg f

theorem integral_zero_of_riemannianVolume
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : MeasureTheory.Measure M} :
    ∫ _ : M, (0 : F) ∂μ = 0 :=
  MeasureTheory.integral_zero M F

theorem integral_const_of_riemannianVolume
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {μ : MeasureTheory.Measure M} (c : F) :
    ∫ _ : M, c ∂μ = μ.real univ • c :=
  MeasureTheory.integral_const c

theorem integral_congr_ae_of_riemannianVolume
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : MeasureTheory.Measure M}
    {f f' : M → F}
    (h : f =ᵐ[μ] f') :
    ∫ x, f x ∂μ = ∫ x, f' x ∂μ :=
  MeasureTheory.integral_congr_ae h

theorem lintegral_add_left_of_riemannianVolume
    {μ : MeasureTheory.Measure M}
    {f : M → ℝ≥0∞} (hf : Measurable f) (f' : M → ℝ≥0∞) :
    ∫⁻ x, f x + f' x ∂μ = (∫⁻ x, f x ∂μ) + (∫⁻ x, f' x ∂μ) :=
  MeasureTheory.lintegral_add_left hf f'

theorem lintegral_const_mul_of_riemannianVolume
    {μ : MeasureTheory.Measure M}
    (r : ℝ≥0∞) {f : M → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, r * f x ∂μ = r * ∫⁻ x, f x ∂μ :=
  MeasureTheory.lintegral_const_mul r hf

end CalabiYau.L2
