-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/ChartBilinear/UniformDiffQuotBoundFromDomain/DataBounds.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.ChartBilinear.H1Compl

@[expose] public section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace CalabiYau
namespace Analysis
namespace Laplacian
namespace ChartBilinearH1Compl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.Laplacian.MetricExtension

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private lemma sq_eLpNorm_two_eq_ofReal_integral_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {v : α → ℝ}
    (hv : MemLp v 2 μ) :
    (eLpNorm v 2 μ) ^ 2 = ENNReal.ofReal (∫ x, v x ^ 2 ∂μ) := by
  classical
  have h_sq_lintegral :
      (eLpNorm v 2 μ) ^ 2 = ∫⁻ x, (‖v x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) hv.aestronglyMeasurable]
    have h2 : (2 : ℝ≥0∞).toReal = 2 := by show ENNReal.toReal 2 = 2; rfl
    rw [h2]
    have h_inner_eq : ∫⁻ x, (‖v x‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂μ =
        ∫⁻ x, (‖v x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards with x
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
    rw [h_inner_eq, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
    norm_num
  rw [h_sq_lintegral]
  have h_pt : ∀ x : α, (‖v x‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (v x ^ 2) := by
    intro x
    rw [← Real.enorm_eq_ofReal (sq_nonneg _)]
    rw [show v x ^ 2 = v x * v x from by ring, enorm_mul]
    rw [show (‖v x‖ₑ : ℝ≥0∞) ^ 2 = ‖v x‖ₑ * ‖v x‖ₑ from by ring]
  rw [lintegral_congr (fun x => h_pt x)]
  have h_sq_int : Integrable (fun x => v x ^ 2) μ := by
    have := hv.integrable_sq
    simpa [pow_two] using this
  have h_sq_nn : 0 ≤ᵐ[μ] fun x => v x ^ 2 :=
    Filter.Eventually.of_forall (fun x => sq_nonneg _)
  exact (ofReal_integral_eq_lintegral_ofReal h_sq_int h_sq_nn).symm

private lemma integral_sq_eq_eLpNorm_two_toReal_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {v : α → ℝ}
    (hv : MemLp v 2 μ) :
    ∫ x, v x ^ 2 ∂μ = (eLpNorm v 2 μ).toReal ^ 2 := by
  have h_sq := sq_eLpNorm_two_eq_ofReal_integral_sq (μ := μ) hv
  have h_int_nn : 0 ≤ ∫ x, v x ^ 2 ∂μ :=
    integral_nonneg (fun x => sq_nonneg _)
  have h_toReal :
      ((eLpNorm v 2 μ) ^ 2).toReal = (eLpNorm v 2 μ).toReal ^ 2 :=
    ENNReal.toReal_pow _ 2
  rw [h_sq] at h_toReal
  rw [ENNReal.toReal_ofReal h_int_nn] at h_toReal
  exact h_toReal

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma sq_cutoffPartial_le
    {χ : EuclN → ℝ} {u w : EuclN → ℝ}
    {M_χ M_dχ : ℝ} {l : Fin (Module.finrank ℝ E)}
    (hM_χ_bd : ∀ x : EuclN, |χ x| ≤ M_χ)
    (hM_dχ_bd : ∀ x : EuclN,
      |(fderiv ℝ χ x) (EuclideanSpace.single l 1)| ≤ M_dχ)
    (x : EuclN) :
    ((fderiv ℝ χ x) (EuclideanSpace.single l 1) * u x + χ x * w x) ^ 2 ≤
      2 * M_dχ ^ 2 * (u x) ^ 2 + 2 * M_χ ^ 2 * (w x) ^ 2 := by
  set a : ℝ := (fderiv ℝ χ x) (EuclideanSpace.single l 1) * u x with ha_def
  set b : ℝ := χ x * w x with hb_def
  have h_ab : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
    calc
      (a + b) ^ 2 ≤ (a + b) ^ 2 + (a - b) ^ 2 :=
        le_add_of_nonneg_right (sq_nonneg _)
      _ = 2 * a ^ 2 + 2 * b ^ 2 := by ring
  have h_a_sq : a ^ 2 ≤ M_dχ ^ 2 * (u x) ^ 2 := by
    rw [ha_def, mul_pow]
    have h_dχ_sq :
        ((fderiv ℝ χ x) (EuclideanSpace.single l 1)) ^ 2 ≤ M_dχ ^ 2 := by
      calc
        ((fderiv ℝ χ x) (EuclideanSpace.single l 1)) ^ 2 =
            |(fderiv ℝ χ x) (EuclideanSpace.single l 1)| ^ 2 := (sq_abs _).symm
        _ ≤ M_dχ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hM_dχ_bd x) 2
    exact mul_le_mul_of_nonneg_right h_dχ_sq (sq_nonneg _)
  have h_b_sq : b ^ 2 ≤ M_χ ^ 2 * (w x) ^ 2 := by
    rw [hb_def, mul_pow]
    have h_χ_sq : (χ x) ^ 2 ≤ M_χ ^ 2 := by
      calc
        (χ x) ^ 2 = |χ x| ^ 2 := (sq_abs _).symm
        _ ≤ M_χ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hM_χ_bd x) 2
    exact mul_le_mul_of_nonneg_right h_χ_sq (sq_nonneg _)
  calc (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := h_ab
    _ ≤ 2 * (M_dχ ^ 2 * (u x) ^ 2) + 2 * (M_χ ^ 2 * (w x) ^ 2) := by gcongr
    _ = 2 * M_dχ ^ 2 * (u x) ^ 2 + 2 * M_χ ^ 2 * (w x) ^ 2 := by ring

private lemma memLp_cutoff_mul
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {χ v : α → ℝ} {M_χ : ℝ} (hM_χ_nn : 0 ≤ M_χ)
    (hM_χ_bd : ∀ x : α, |χ x| ≤ M_χ)
    (hχ_aesm : AEStronglyMeasurable χ μ)
    (hv : MemLp v 2 μ) :
    MemLp (fun x => χ x * v x) 2 μ := by
  have h_pt_le : ∀ᵐ x ∂μ, ‖χ x * v x‖ ≤ ‖M_χ * v x‖ := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg hM_χ_nn]
    exact mul_le_mul_of_nonneg_right (hM_χ_bd x) (abs_nonneg _)
  exact MemLp.mono (hv.const_mul M_χ) (hχ_aesm.mul hv.aestronglyMeasurable) h_pt_le

theorem cutoff_energy_le_data_eLpNorm_sq
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    {χ : EuclN → ℝ} (hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ)
    {M_χ M_dχ : ℝ}
    (hM_χ_bd : ∀ x : EuclN, |χ x| ≤ M_χ)
    (hM_dχ_bd : ∀ (l : Fin (Module.finrank ℝ E)) (x : EuclN),
      |(fderiv ℝ χ x) (EuclideanSpace.single l 1)| ≤ M_dχ)
    {Ω' : Set EuclN}
    (hΩ'_closure_compact : IsCompact (closure Ω'))
    (hΩ'_closure_in : closure Ω' ⊆ chartTargetEuclid (I := I) (M := M) α)
    {fSource : EuclN → ℝ}
    (hfSource : MemLp fSource 2 ((volume : Measure EuclN).restrict (closure Ω')))
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α) :
    (∫ x in Ω', ∑ l : Fin (Module.finrank ℝ E),
        ((fderiv ℝ χ x) (EuclideanSpace.single l 1) * D.uChart x +
          χ x * D.weakPartial l x) ^ 2
      ∂(volume : Measure EuclN)) +
    (∫ x in Ω', (χ x * D.uChart x) ^ 2 ∂(volume : Measure EuclN)) +
    (∫ x in Ω', (χ x * fSource x) ^ 2 ∂(volume : Measure EuclN)) ≤
      (2 * ((Module.finrank ℝ E : ℝ) + 1) * (M_χ ^ 2 + M_dχ ^ 2 + 1)) *
        ((∑ l : Fin (Module.finrank ℝ E),
            (eLpNorm (D.weakPartial l) 2
              ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2) +
          (eLpNorm D.uChart 2
            ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2 +
          (eLpNorm fSource 2
            ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2) := by
  classical
  have hχ_cont : Continuous χ := hχ_smooth.continuous
  have hχ_fderiv_cont : Continuous (fderiv ℝ χ) :=
    hχ_smooth.continuous_fderiv (by decide : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)
  have hχ_partial_cont : ∀ l : Fin (Module.finrank ℝ E), Continuous
      (fun x => (fderiv ℝ χ x) (EuclideanSpace.single l 1)) := fun l =>
    hχ_fderiv_cont.clm_apply continuous_const
  have hχ_aesm : AEStronglyMeasurable χ
      ((volume : Measure EuclN).restrict (closure Ω')) :=
    hχ_cont.aestronglyMeasurable
  have hχ_partial_aesm : ∀ l : Fin (Module.finrank ℝ E), AEStronglyMeasurable
      (fun x => (fderiv ℝ χ x) (EuclideanSpace.single l 1))
      ((volume : Measure EuclN).restrict (closure Ω')) := fun l =>
    (hχ_partial_cont l).aestronglyMeasurable
  have hΩ'_closure_meas : MeasurableSet (closure Ω') := isClosed_closure.measurableSet
  have hu_l2 : MemLp D.uChart 2
      ((volume : Measure EuclN).restrict (closure Ω')) :=
    memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure (I := I) (M := M)
      D.u_chart_memLp_weighted hΩ'_closure_compact hΩ'_closure_meas hΩ'_closure_in
  have hf_l2 : MemLp fSource 2
      ((volume : Measure EuclN).restrict (closure Ω')) := hfSource
  have hwp_l2 : ∀ l : Fin (Module.finrank ℝ E), MemLp (D.weakPartial l) 2
      ((volume : Measure EuclN).restrict (closure Ω')) := fun l =>
    D.weak_partial_locally_memLp l (closure Ω') hΩ'_closure_compact hΩ'_closure_in
  have hM_χ_nn : 0 ≤ M_χ := le_trans (abs_nonneg _) (hM_χ_bd 0)
  have hM_dχ_nn : 0 ≤ M_dχ := by
    obtain ⟨l⟩ : Nonempty (Fin (Module.finrank ℝ E)) :=
      ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
    exact le_trans (abs_nonneg _) (hM_dχ_bd l 0)
  set Sw : ℝ := ∑ l : Fin (Module.finrank ℝ E),
      (eLpNorm (D.weakPartial l) 2
        ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2 with hSw_def
  set Su : ℝ := (eLpNorm D.uChart 2
      ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2 with hSu_def
  set Sf : ℝ := (eLpNorm fSource 2
      ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2 with hSf_def
  have hSw_nn : 0 ≤ Sw := by
    rw [hSw_def]; exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hSu_nn : 0 ≤ Su := by rw [hSu_def]; exact sq_nonneg _
  have hSf_nn : 0 ≤ Sf := by rw [hSf_def]; exact sq_nonneg _
  have hu_int_closure :
      ∫ x in closure Ω', (D.uChart x) ^ 2 ∂(volume : Measure EuclN) = Su := by
    rw [hSu_def]
    exact integral_sq_eq_eLpNorm_two_toReal_sq hu_l2
  have hf_int_closure :
      ∫ x in closure Ω', (fSource x) ^ 2 ∂(volume : Measure EuclN) = Sf := by
    rw [hSf_def]
    exact integral_sq_eq_eLpNorm_two_toReal_sq hf_l2
  have hwp_int_closure : ∀ l : Fin (Module.finrank ℝ E),
      ∫ x in closure Ω', (D.weakPartial l x) ^ 2 ∂(volume : Measure EuclN) =
        (eLpNorm (D.weakPartial l) 2
          ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2 := fun l =>
    integral_sq_eq_eLpNorm_two_toReal_sq (hwp_l2 l)
  have hug_l2 : MemLp (fun x => χ x * D.uChart x) 2
      ((volume : Measure EuclN).restrict (closure Ω')) :=
    memLp_cutoff_mul hM_χ_nn hM_χ_bd hχ_aesm hu_l2
  have hfg_l2 : MemLp (fun x => χ x * fSource x) 2
      ((volume : Measure EuclN).restrict (closure Ω')) :=
    memLp_cutoff_mul hM_χ_nn hM_χ_bd hχ_aesm hf_l2
  have hgg_l2 : ∀ l : Fin (Module.finrank ℝ E), MemLp (fun x =>
      (fderiv ℝ χ x) (EuclideanSpace.single l 1) * D.uChart x +
        χ x * D.weakPartial l x) 2
      ((volume : Measure EuclN).restrict (closure Ω')) := by
    intro l
    have h_term1 : MemLp (fun x =>
        (fderiv ℝ χ x) (EuclideanSpace.single l 1) * D.uChart x) 2
        ((volume : Measure EuclN).restrict (closure Ω')) :=
      memLp_cutoff_mul hM_dχ_nn (hM_dχ_bd l) (hχ_partial_aesm l) hu_l2
    have h_term2 : MemLp (fun x => χ x * D.weakPartial l x) 2
        ((volume : Measure EuclN).restrict (closure Ω')) :=
      memLp_cutoff_mul hM_χ_nn hM_χ_bd hχ_aesm (hwp_l2 l)
    exact h_term1.add h_term2
  have h_each_gg_int : ∀ l : Fin (Module.finrank ℝ E), IntegrableOn (fun x =>
      ((fderiv ℝ χ x) (EuclideanSpace.single l 1) * D.uChart x +
        χ x * D.weakPartial l x) ^ 2) (closure Ω') (volume : Measure EuclN) := by
    intro l
    have := (hgg_l2 l).integrable_sq
    simpa [IntegrableOn, pow_two] using this
  have h_principal_int : IntegrableOn (fun x =>
      ∑ l : Fin (Module.finrank ℝ E),
        ((fderiv ℝ χ x) (EuclideanSpace.single l 1) * D.uChart x +
          χ x * D.weakPartial l x) ^ 2) (closure Ω') (volume : Measure EuclN) := by
    have h_sum := integrable_finsetSum
      (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun l _ => (h_each_gg_int l).integrable)
    have h_eq : (fun x : EuclN => ∑ l : Fin (Module.finrank ℝ E),
        ((fderiv ℝ χ x) (EuclideanSpace.single l 1) * D.uChart x +
          χ x * D.weakPartial l x) ^ 2) =
        (fun x : EuclN => ∑ l ∈
          (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
          (fun y => ((fderiv ℝ χ y) (EuclideanSpace.single l 1) * D.uChart y +
            χ y * D.weakPartial l y) ^ 2) x) := by
      funext x; rfl
    rw [IntegrableOn, h_eq]; exact h_sum
  have h_ug_sq_int : IntegrableOn (fun x => (χ x * D.uChart x) ^ 2)
      (closure Ω') (volume : Measure EuclN) := by
    have := hug_l2.integrable_sq
    simpa [IntegrableOn, pow_two] using this
  have h_fg_sq_int : IntegrableOn (fun x => (χ x * fSource x) ^ 2)
      (closure Ω') (volume : Measure EuclN) := by
    have := hfg_l2.integrable_sq
    simpa [IntegrableOn, pow_two] using this
  have h_principal_mono :
      (∫ x in Ω', ∑ l : Fin (Module.finrank ℝ E),
        ((fderiv ℝ χ x) (EuclideanSpace.single l 1) * D.uChart x +
          χ x * D.weakPartial l x) ^ 2 ∂(volume : Measure EuclN)) ≤
      ∫ x in closure Ω', ∑ l : Fin (Module.finrank ℝ E),
        ((fderiv ℝ χ x) (EuclideanSpace.single l 1) * D.uChart x +
          χ x * D.weakPartial l x) ^ 2 ∂(volume : Measure EuclN) :=
    setIntegral_mono_set h_principal_int
      (Filter.Eventually.of_forall
        (fun x => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
      (Filter.Eventually.of_forall subset_closure)
  have h_ug_mono :
      (∫ x in Ω', (χ x * D.uChart x) ^ 2 ∂(volume : Measure EuclN)) ≤
      ∫ x in closure Ω', (χ x * D.uChart x) ^ 2 ∂(volume : Measure EuclN) :=
    setIntegral_mono_set h_ug_sq_int
      (Filter.Eventually.of_forall (fun x => sq_nonneg _))
      (Filter.Eventually.of_forall subset_closure)
  have h_fg_mono :
      (∫ x in Ω', (χ x * fSource x) ^ 2 ∂(volume : Measure EuclN)) ≤
      ∫ x in closure Ω', (χ x * fSource x) ^ 2 ∂(volume : Measure EuclN) :=
    setIntegral_mono_set h_fg_sq_int
      (Filter.Eventually.of_forall (fun x => sq_nonneg _))
      (Filter.Eventually.of_forall subset_closure)
  have h_pt_sum : ∀ x : EuclN,
      (∑ l : Fin (Module.finrank ℝ E),
        ((fderiv ℝ χ x) (EuclideanSpace.single l 1) * D.uChart x +
          χ x * D.weakPartial l x) ^ 2) ≤
      2 * (Module.finrank ℝ E : ℝ) * M_dχ ^ 2 * (D.uChart x) ^ 2 +
        2 * M_χ ^ 2 * (∑ l : Fin (Module.finrank ℝ E),
          (D.weakPartial l x) ^ 2) := by
    intro x
    calc (∑ l : Fin (Module.finrank ℝ E),
          ((fderiv ℝ χ x) (EuclideanSpace.single l 1) * D.uChart x +
            χ x * D.weakPartial l x) ^ 2)
        ≤ ∑ l : Fin (Module.finrank ℝ E),
            (2 * M_dχ ^ 2 * (D.uChart x) ^ 2 +
              2 * M_χ ^ 2 * (D.weakPartial l x) ^ 2) :=
          Finset.sum_le_sum (fun l _ =>
            sq_cutoffPartial_le hM_χ_bd (hM_dχ_bd l) x)
      _ = (∑ _l : Fin (Module.finrank ℝ E),
              2 * M_dχ ^ 2 * (D.uChart x) ^ 2) +
            ∑ l : Fin (Module.finrank ℝ E),
              2 * M_χ ^ 2 * (D.weakPartial l x) ^ 2 :=
          Finset.sum_add_distrib
      _ = (Module.finrank ℝ E : ℝ) * (2 * M_dχ ^ 2 * (D.uChart x) ^ 2) +
            2 * M_χ ^ 2 * (∑ l : Fin (Module.finrank ℝ E),
              (D.weakPartial l x) ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, ← Finset.mul_sum]
      _ = 2 * (Module.finrank ℝ E : ℝ) * M_dχ ^ 2 * (D.uChart x) ^ 2 +
            2 * M_χ ^ 2 * (∑ l : Fin (Module.finrank ℝ E),
              (D.weakPartial l x) ^ 2) := by ring
  have h_u_sq_int : IntegrableOn (fun x => (D.uChart x) ^ 2)
      (closure Ω') (volume : Measure EuclN) := by
    have := hu_l2.integrable_sq
    simpa [IntegrableOn, pow_two] using this
  have h_f_sq_int : IntegrableOn (fun x => (fSource x) ^ 2)
      (closure Ω') (volume : Measure EuclN) := by
    have := hf_l2.integrable_sq
    simpa [IntegrableOn, pow_two] using this
  have h_wp_sq_int : ∀ l : Fin (Module.finrank ℝ E),
      IntegrableOn (fun x => (D.weakPartial l x) ^ 2)
        (closure Ω') (volume : Measure EuclN) := by
    intro l
    have := (hwp_l2 l).integrable_sq
    simpa [IntegrableOn, pow_two] using this
  have h_wp_sum_sq_int : IntegrableOn
      (fun x => ∑ l : Fin (Module.finrank ℝ E), (D.weakPartial l x) ^ 2)
      (closure Ω') (volume : Measure EuclN) := by
    have h_sum := integrable_finsetSum
      (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun l _ => (h_wp_sq_int l).integrable)
    have h_eq : (fun x : EuclN => ∑ l : Fin (Module.finrank ℝ E),
        (D.weakPartial l x) ^ 2) =
        (fun x : EuclN => ∑ l ∈
          (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
          (fun y => (D.weakPartial l y) ^ 2) x) := by
      funext x; rfl
    rw [IntegrableOn, h_eq]; exact h_sum
  have h_rhs_int : IntegrableOn (fun x =>
      2 * (Module.finrank ℝ E : ℝ) * M_dχ ^ 2 * (D.uChart x) ^ 2 +
        2 * M_χ ^ 2 * (∑ l : Fin (Module.finrank ℝ E),
          (D.weakPartial l x) ^ 2))
      (closure Ω') (volume : Measure EuclN) :=
    Integrable.add
      (h_u_sq_int.integrable.const_mul (2 * (Module.finrank ℝ E : ℝ) * M_dχ ^ 2))
      (h_wp_sum_sq_int.integrable.const_mul (2 * M_χ ^ 2))
  have h_principal_closure_le :
      (∫ x in closure Ω', ∑ l : Fin (Module.finrank ℝ E),
        ((fderiv ℝ χ x) (EuclideanSpace.single l 1) * D.uChart x +
          χ x * D.weakPartial l x) ^ 2 ∂(volume : Measure EuclN)) ≤
      ∫ x in closure Ω',
        (2 * (Module.finrank ℝ E : ℝ) * M_dχ ^ 2 * (D.uChart x) ^ 2 +
          2 * M_χ ^ 2 * (∑ l : Fin (Module.finrank ℝ E),
            (D.weakPartial l x) ^ 2))
        ∂(volume : Measure EuclN) :=
    integral_mono_of_nonneg
      (Filter.Eventually.of_forall
        (fun x => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
      h_rhs_int.integrable
      (Filter.Eventually.of_forall h_pt_sum)
  have h_rhs_eval :
      (∫ x in closure Ω',
        (2 * (Module.finrank ℝ E : ℝ) * M_dχ ^ 2 * (D.uChart x) ^ 2 +
          2 * M_χ ^ 2 * (∑ l : Fin (Module.finrank ℝ E),
            (D.weakPartial l x) ^ 2))
        ∂(volume : Measure EuclN)) =
      2 * (Module.finrank ℝ E : ℝ) * M_dχ ^ 2 * Su + 2 * M_χ ^ 2 * Sw := by
    rw [integral_add (h_u_sq_int.integrable.const_mul _)
      (h_wp_sum_sq_int.integrable.const_mul _)]
    rw [integral_const_mul, integral_const_mul, hu_int_closure]
    have h_sum_swap :
        (∫ x in closure Ω', ∑ l : Fin (Module.finrank ℝ E),
          (D.weakPartial l x) ^ 2 ∂(volume : Measure EuclN)) =
        ∑ l : Fin (Module.finrank ℝ E), ∫ x in closure Ω',
          (D.weakPartial l x) ^ 2 ∂(volume : Measure EuclN) :=
      integral_finsetSum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun l _ => (h_wp_sq_int l).integrable)
    rw [h_sum_swap]
    have h_sum_eq : (∑ l : Fin (Module.finrank ℝ E), ∫ x in closure Ω',
        (D.weakPartial l x) ^ 2 ∂(volume : Measure EuclN)) = Sw := by
      rw [hSw_def]
      exact Finset.sum_congr rfl (fun l _ => hwp_int_closure l)
    rw [h_sum_eq]
  have h_principal_final :
      (∫ x in Ω', ∑ l : Fin (Module.finrank ℝ E),
        ((fderiv ℝ χ x) (EuclideanSpace.single l 1) * D.uChart x +
          χ x * D.weakPartial l x) ^ 2 ∂(volume : Measure EuclN)) ≤
      2 * (Module.finrank ℝ E : ℝ) * M_dχ ^ 2 * Su + 2 * M_χ ^ 2 * Sw :=
    le_trans h_principal_mono (le_trans h_principal_closure_le (le_of_eq h_rhs_eval))
  have h_χmul_pt : ∀ (v : EuclN → ℝ) (x : EuclN),
      (χ x * v x) ^ 2 ≤ M_χ ^ 2 * (v x) ^ 2 := by
    intro v x
    rw [mul_pow]
    have h_χ_sq : (χ x) ^ 2 ≤ M_χ ^ 2 := by
      calc
        (χ x) ^ 2 = |χ x| ^ 2 := (sq_abs _).symm
        _ ≤ M_χ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hM_χ_bd x) 2
    exact mul_le_mul_of_nonneg_right h_χ_sq (sq_nonneg _)
  have h_ug_closure_le :
      (∫ x in closure Ω', (χ x * D.uChart x) ^ 2 ∂(volume : Measure EuclN)) ≤
      M_χ ^ 2 * Su := by
    have h_int_le :
        (∫ x in closure Ω', (χ x * D.uChart x) ^ 2 ∂(volume : Measure EuclN)) ≤
        ∫ x in closure Ω', M_χ ^ 2 * (D.uChart x) ^ 2
          ∂(volume : Measure EuclN) :=
      integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun x => sq_nonneg _))
        (h_u_sq_int.integrable.const_mul (M_χ ^ 2))
        (Filter.Eventually.of_forall (fun x => h_χmul_pt D.uChart x))
    rwa [integral_const_mul, hu_int_closure] at h_int_le
  have h_fg_closure_le :
      (∫ x in closure Ω', (χ x * fSource x) ^ 2 ∂(volume : Measure EuclN)) ≤
      M_χ ^ 2 * Sf := by
    have h_int_le :
        (∫ x in closure Ω', (χ x * fSource x) ^ 2 ∂(volume : Measure EuclN)) ≤
        ∫ x in closure Ω', M_χ ^ 2 * (fSource x) ^ 2
          ∂(volume : Measure EuclN) :=
      integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun x => sq_nonneg _))
        (h_f_sq_int.integrable.const_mul (M_χ ^ 2))
        (Filter.Eventually.of_forall (fun x => h_χmul_pt fSource x))
    rwa [integral_const_mul, hf_int_closure] at h_int_le
  have h_ug_final :
      (∫ x in Ω', (χ x * D.uChart x) ^ 2 ∂(volume : Measure EuclN)) ≤
      M_χ ^ 2 * Su := le_trans h_ug_mono h_ug_closure_le
  have h_fg_final :
      (∫ x in Ω', (χ x * fSource x) ^ 2 ∂(volume : Measure EuclN)) ≤
      M_χ ^ 2 * Sf := le_trans h_fg_mono h_fg_closure_le
  have h_sum_bound :
      (∫ x in Ω', ∑ l : Fin (Module.finrank ℝ E),
          ((fderiv ℝ χ x) (EuclideanSpace.single l 1) * D.uChart x +
            χ x * D.weakPartial l x) ^ 2 ∂(volume : Measure EuclN)) +
      (∫ x in Ω', (χ x * D.uChart x) ^ 2 ∂(volume : Measure EuclN)) +
      (∫ x in Ω', (χ x * fSource x) ^ 2 ∂(volume : Measure EuclN)) ≤
      (2 * (Module.finrank ℝ E : ℝ) * M_dχ ^ 2 * Su + 2 * M_χ ^ 2 * Sw) +
        M_χ ^ 2 * Su + M_χ ^ 2 * Sf := by
    have := add_le_add (add_le_add h_principal_final h_ug_final) h_fg_final
    linarith [this]
  refine le_trans h_sum_bound ?_
  set Cχ : ℝ :=
    2 * ((Module.finrank ℝ E : ℝ) + 1) * (M_χ ^ 2 + M_dχ ^ 2 + 1) with hCχ_def
  have hn_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have h_coeff_w : 2 * M_χ ^ 2 ≤ Cχ := by
    rw [hCχ_def]
    have hrest : 0 ≤
        2 * (Module.finrank ℝ E : ℝ) * M_χ ^ 2 +
          2 * ((Module.finrank ℝ E : ℝ) + 1) * (M_dχ ^ 2 + 1) :=
      add_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hn_nn) (sq_nonneg _))
        (mul_nonneg
          (mul_nonneg (by norm_num) (add_nonneg hn_nn zero_le_one))
          (add_nonneg (sq_nonneg _) zero_le_one))
    calc
      2 * M_χ ^ 2 ≤ 2 * M_χ ^ 2 +
          (2 * (Module.finrank ℝ E : ℝ) * M_χ ^ 2 +
            2 * ((Module.finrank ℝ E : ℝ) + 1) * (M_dχ ^ 2 + 1)) :=
        le_add_of_nonneg_right hrest
      _ = 2 * ((Module.finrank ℝ E : ℝ) + 1) * (M_χ ^ 2 + M_dχ ^ 2 + 1) := by
        ring
  have h_coeff_u :
      2 * (Module.finrank ℝ E : ℝ) * M_dχ ^ 2 + M_χ ^ 2 ≤ Cχ := by
    rw [hCχ_def]
    have hrest : 0 ≤
        (2 * (Module.finrank ℝ E : ℝ) + 1) * M_χ ^ 2 +
          2 * M_dχ ^ 2 + 2 * (Module.finrank ℝ E : ℝ) + 2 :=
      add_nonneg
        (add_nonneg
          (add_nonneg
            (mul_nonneg (add_nonneg (mul_nonneg (by norm_num) hn_nn) zero_le_one)
              (sq_nonneg _))
            (mul_nonneg (by norm_num) (sq_nonneg _)))
          (mul_nonneg (by norm_num) hn_nn))
        (by norm_num)
    calc
      2 * (Module.finrank ℝ E : ℝ) * M_dχ ^ 2 + M_χ ^ 2 ≤
          2 * (Module.finrank ℝ E : ℝ) * M_dχ ^ 2 + M_χ ^ 2 +
            ((2 * (Module.finrank ℝ E : ℝ) + 1) * M_χ ^ 2 +
              2 * M_dχ ^ 2 + 2 * (Module.finrank ℝ E : ℝ) + 2) :=
        le_add_of_nonneg_right hrest
      _ = 2 * ((Module.finrank ℝ E : ℝ) + 1) * (M_χ ^ 2 + M_dχ ^ 2 + 1) := by
        ring
  have h_coeff_f : M_χ ^ 2 ≤ Cχ := by
    rw [hCχ_def]
    have hrest : 0 ≤
        (2 * (Module.finrank ℝ E : ℝ) + 1) * M_χ ^ 2 +
          2 * ((Module.finrank ℝ E : ℝ) + 1) * (M_dχ ^ 2 + 1) :=
      add_nonneg
        (mul_nonneg (add_nonneg (mul_nonneg (by norm_num) hn_nn) zero_le_one)
          (sq_nonneg _))
        (mul_nonneg
          (mul_nonneg (by norm_num) (add_nonneg hn_nn zero_le_one))
          (add_nonneg (sq_nonneg _) zero_le_one))
    calc
      M_χ ^ 2 ≤ M_χ ^ 2 +
          ((2 * (Module.finrank ℝ E : ℝ) + 1) * M_χ ^ 2 +
            2 * ((Module.finrank ℝ E : ℝ) + 1) * (M_dχ ^ 2 + 1)) :=
        le_add_of_nonneg_right hrest
      _ = 2 * ((Module.finrank ℝ E : ℝ) + 1) * (M_χ ^ 2 + M_dχ ^ 2 + 1) := by
        ring
  have h_final :
      (2 * (Module.finrank ℝ E : ℝ) * M_dχ ^ 2 * Su + 2 * M_χ ^ 2 * Sw) +
        M_χ ^ 2 * Su + M_χ ^ 2 * Sf ≤ Cχ * (Sw + Su + Sf) := by
    have h_w_term : 2 * M_χ ^ 2 * Sw ≤ Cχ * Sw :=
      mul_le_mul_of_nonneg_right h_coeff_w hSw_nn
    have h_u_term :
        2 * (Module.finrank ℝ E : ℝ) * M_dχ ^ 2 * Su + M_χ ^ 2 * Su ≤
          Cχ * Su := by
      have h_factored :
          2 * (Module.finrank ℝ E : ℝ) * M_dχ ^ 2 * Su + M_χ ^ 2 * Su =
            (2 * (Module.finrank ℝ E : ℝ) * M_dχ ^ 2 + M_χ ^ 2) * Su := by ring
      rw [h_factored]
      exact mul_le_mul_of_nonneg_right h_coeff_u hSu_nn
    have h_f_term : M_χ ^ 2 * Sf ≤ Cχ * Sf :=
      mul_le_mul_of_nonneg_right h_coeff_f hSf_nn
    have h_expand : Cχ * (Sw + Su + Sf) = Cχ * Sw + Cχ * Su + Cχ * Sf := by ring
    linarith [h_w_term, h_u_term, h_f_term, h_expand]
  calc (2 * (Module.finrank ℝ E : ℝ) * M_dχ ^ 2 * Su + 2 * M_χ ^ 2 * Sw) +
        M_χ ^ 2 * Su + M_χ ^ 2 * Sf
      ≤ Cχ * (Sw + Su + Sf) := h_final
    _ = (2 * ((Module.finrank ℝ E : ℝ) + 1) * (M_χ ^ 2 + M_dχ ^ 2 + 1)) *
          (Sw + Su + Sf) := by rw [hCχ_def]

end ChartBilinearH1Compl

end Laplacian
end Analysis
end CalabiYau
