-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Nirenberg/ChartBilinearDischarge/SubstitutionGradTendsto.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Nirenberg.ChartBilinearDischarge.SubstitutionSmoothApprox

@[expose] public section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal Pointwise

namespace CalabiYau
namespace Analysis
namespace Sobolev
namespace SubstitutionDischargeGradTendsto

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Laplacian.MetricExtension
open CalabiYau.Analysis.Laplacian.ChartLocalLaplacian
open CalabiYau.Laplacian.ChartMeasureEquiv
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open _root_.Sobolev.NirenbergTestFunction

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma fderiv_nirenbergTestFunction_apply
    {η u : EuclN → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (k j : Fin (Module.finrank ℝ E)) {h : ℝ} (hh : h ≠ 0) (x : EuclN) :
    (fderiv ℝ (nirenbergTestFunction (d := Module.finrank ℝ E) k h η u) x)
        (EuclideanSpace.single j 1) =
      Sobolev.diffQuot
        (d := Module.finrank ℝ E) k (-h)
        (fun y : EuclN =>
          2 * η y * ((fderiv ℝ η y) (EuclideanSpace.single j 1)) *
            Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h u y +
          (η y)^2 *
            Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h
              (fun z : EuclN =>
                (fderiv ℝ u z) (EuclideanSpace.single j 1)) y) x := by
  exact _root_.Sobolev.NirenbergTestFunction.fderiv_nirenbergTestFunction_apply
    (d := Module.finrank ℝ E) hη hu k j hh x

omit [NeZero (Module.finrank ℝ E)] in
private lemma diffQuot_chi_sub_one_uChart_vanishes
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {χ : EuclN → ℝ}
    {η : EuclN → ℝ}
    (k j : Fin (Module.finrank ℝ E))
    (h : ℝ)
    {K_0 : Set EuclN}
    (hχ_one : ∀ x ∈ Metric.cthickening |h| K_0, χ x = 1)
    (hη_support_in_K_0 : tsupport η ⊆ K_0) :
    (fun z =>
      2 * η z * ((fderiv ℝ η z) (EuclideanSpace.single j 1)) *
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          (fun y => (χ y - 1) * D.uChart y) z) =
    fun _ => (0 : ℝ) := by
  funext z
  by_cases hη_factor : 2 * η z * ((fderiv ℝ η z) (EuclideanSpace.single j 1)) = 0
  · rw [hη_factor, zero_mul]
  have hη_z_ne : η z ≠ 0 := by
    intro hz
    apply hη_factor
    rw [hz]; ring
  have hz_in_support : z ∈ tsupport η := subset_tsupport η hη_z_ne
  have hz_in_K0 : z ∈ K_0 := hη_support_in_K_0 hz_in_support
  have hz_in_cthick : z ∈ Metric.cthickening |h| K_0 :=
    Metric.self_subset_cthickening _ hz_in_K0
  have hz_shift_in_cthick : z + h • EuclideanSpace.single k 1 ∈
      Metric.cthickening |h| K_0 := by
    refine Metric.mem_cthickening_of_dist_le _ z |h| K_0 hz_in_K0 ?_
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
    simp [Real.norm_eq_abs]
  have hχz : χ z = 1 := hχ_one z hz_in_cthick
  have hχz_shift : χ (z + h • EuclideanSpace.single k 1) = 1 :=
    hχ_one _ hz_shift_in_cthick
  by_cases hh : h = 0
  · subst hh
    rw [Sobolev.diffQuot_zero_h]
    exact mul_zero _
  · rw [Sobolev.diffQuot_apply_of_ne
      (d := Module.finrank ℝ E) k hh _ z]
    have h1 : (χ z - 1) * D.uChart z = 0 := by rw [hχz]; ring
    have h2 : (χ (z + h • EuclideanSpace.single k 1) - 1) *
        D.uChart (z + h • EuclideanSpace.single k 1) = 0 := by
      rw [hχz_shift]; ring
    change 2 * η z * ((fderiv ℝ η z) (EuclideanSpace.single j 1)) *
        (((χ (z + h • EuclideanSpace.single k 1) - 1) *
          D.uChart (z + h • EuclideanSpace.single k 1) -
          (χ z - 1) * D.uChart z) / h) = 0
    rw [h1, h2, sub_zero, zero_div, mul_zero]

omit [NeZero (Module.finrank ℝ E)] in
private lemma diffQuot_dx_chi_uChart_vanishes
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {χ : EuclN → ℝ}
    {η : EuclN → ℝ}
    (k j : Fin (Module.finrank ℝ E))
    (h : ℝ)
    {K_0 : Set EuclN}
    (hχ_one : ∀ x ∈ Metric.cthickening |h| K_0, χ x = 1)
    (hχ_dx_zero : ∀ x ∈ Metric.cthickening |h| K_0, ∀ i,
      (fderiv ℝ χ x) (EuclideanSpace.single i 1) = 0)
    (hη_support_in_K_0 : tsupport η ⊆ K_0) :
    (fun z =>
      (η z)^2 *
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          (fun y =>
            (fderiv ℝ χ y) (EuclideanSpace.single j 1) * D.uChart y +
            (χ y - 1) * D.weakPartial j y) z) =
    fun _ => (0 : ℝ) := by
  funext z
  by_cases hη_sq_zero : (η z)^2 = 0
  · rw [hη_sq_zero, zero_mul]
  have hη_z_ne : η z ≠ 0 := by
    intro hz
    apply hη_sq_zero
    rw [hz]; ring
  have hz_in_support : z ∈ tsupport η := subset_tsupport η hη_z_ne
  have hz_in_K0 : z ∈ K_0 := hη_support_in_K_0 hz_in_support
  have hz_in_cthick : z ∈ Metric.cthickening |h| K_0 :=
    Metric.self_subset_cthickening _ hz_in_K0
  have hz_shift_in_cthick : z + h • EuclideanSpace.single k 1 ∈
      Metric.cthickening |h| K_0 := by
    refine Metric.mem_cthickening_of_dist_le _ z |h| K_0 hz_in_K0 ?_
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
    simp [Real.norm_eq_abs]
  have hχz : χ z = 1 := hχ_one z hz_in_cthick
  have hχz_shift : χ (z + h • EuclideanSpace.single k 1) = 1 :=
    hχ_one _ hz_shift_in_cthick
  have hdχz : (fderiv ℝ χ z) (EuclideanSpace.single j 1) = 0 :=
    hχ_dx_zero z hz_in_cthick j
  have hdχz_shift :
      (fderiv ℝ χ (z + h • EuclideanSpace.single k 1))
        (EuclideanSpace.single j 1) = 0 :=
    hχ_dx_zero _ hz_shift_in_cthick j
  by_cases hh : h = 0
  · subst hh
    rw [Sobolev.diffQuot_zero_h]
    exact mul_zero _
  · rw [Sobolev.diffQuot_apply_of_ne
      (d := Module.finrank ℝ E) k hh _ z]
    have h1 :
        (fderiv ℝ χ z) (EuclideanSpace.single j 1) * D.uChart z +
          (χ z - 1) * D.weakPartial j z = 0 := by
      rw [hdχz, hχz]; ring
    have h2 :
        (fderiv ℝ χ (z + h • EuclideanSpace.single k 1))
            (EuclideanSpace.single j 1) *
          D.uChart (z + h • EuclideanSpace.single k 1) +
          (χ (z + h • EuclideanSpace.single k 1) - 1) *
            D.weakPartial j (z + h • EuclideanSpace.single k 1) = 0 := by
      rw [hdχz_shift, hχz_shift]; ring
    change (η z)^2 *
        ((((fderiv ℝ χ (z + h • EuclideanSpace.single k 1))
              (EuclideanSpace.single j 1) *
            D.uChart (z + h • EuclideanSpace.single k 1) +
            (χ (z + h • EuclideanSpace.single k 1) - 1) *
              D.weakPartial j (z + h • EuclideanSpace.single k 1)) -
          ((fderiv ℝ χ z) (EuclideanSpace.single j 1) * D.uChart z +
            (χ z - 1) * D.weakPartial j z)) / h) = 0
    rw [h1, h2, sub_zero, zero_div, mul_zero]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma eLpNorm_translate_eq_local
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) (F : EuclN → ℝ) :
    eLpNorm (Sobolev.translate
      (d := Module.finrank ℝ E) k h F) 2 (volume : Measure EuclN) =
      eLpNorm F 2 (volume : Measure EuclN) := by
  set τ : EuclN ≃ₜ EuclN :=
    Homeomorph.addRight (h • EuclideanSpace.single k 1) with hτ_def
  have hMP : MeasurePreserving τ volume volume := by
    rw [show (τ : EuclN → EuclN) = fun x => x + h • EuclideanSpace.single k 1
      from rfl]
    exact measurePreserving_add_right volume _
  have hτ_emb : MeasurableEmbedding τ := τ.measurableEmbedding
  have h_eq :
      Sobolev.translate
        (d := Module.finrank ℝ E) k h F = F ∘ (τ : EuclN → EuclN) := rfl
  rw [h_eq]
  rw [show eLpNorm F 2 (volume : Measure EuclN) =
      eLpNorm F 2 (Measure.map τ volume) from by rw [hMP.map_eq]]
  exact (hτ_emb.eLpNorm_map_measure (g := F) (p := 2)).symm

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma eLpNorm_diffQuot_le_local
    (k : Fin (Module.finrank ℝ E)) {h : ℝ} (hh : h ≠ 0) {F : EuclN → ℝ}
    (hF_aesm : AEStronglyMeasurable F (volume : Measure EuclN)) :
    eLpNorm (Sobolev.diffQuot
      (d := Module.finrank ℝ E) k h F) 2 (volume : Measure EuclN) ≤
      (2 / ENNReal.ofReal |h|) * eLpNorm F 2 (volume : Measure EuclN) := by
  have h_dq_eq : Sobolev.diffQuot
      (d := Module.finrank ℝ E) k h F =
      fun x => h⁻¹ * (Sobolev.translate
        (d := Module.finrank ℝ E) k h F x - F x) := by
    funext x
    rw [Sobolev.diffQuot_apply_of_ne
      (d := Module.finrank ℝ E) k hh F x]
    change (F (x + h • EuclideanSpace.single k 1) - F x) / h =
      h⁻¹ * (F (x + h • EuclideanSpace.single k 1) - F x)
    field_simp
  rw [h_dq_eq]
  have h_eq_pi : (fun x => h⁻¹ * (Sobolev.translate
        (d := Module.finrank ℝ E) k h F x - F x)) =
      h⁻¹ • (Sobolev.translate
        (d := Module.finrank ℝ E) k h F - F) := by
    funext x
    simp [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [h_eq_pi]
  rw [eLpNorm_const_smul h⁻¹]
  have hτF_aesm : AEStronglyMeasurable
      (Sobolev.translate
        (d := Module.finrank ℝ E) k h F) (volume : Measure EuclN) := by
    have hMP : MeasurePreserving
        (fun x : EuclN => x + h • EuclideanSpace.single k 1) volume volume :=
      measurePreserving_add_right volume _
    exact hF_aesm.comp_measurePreserving hMP
  have h_minkowski :
      eLpNorm (Sobolev.translate
        (d := Module.finrank ℝ E) k h F - F) 2 (volume : Measure EuclN) ≤
        eLpNorm (Sobolev.translate
          (d := Module.finrank ℝ E) k h F) 2 (volume : Measure EuclN) +
          eLpNorm F 2 (volume : Measure EuclN) :=
    eLpNorm_sub_le hτF_aesm hF_aesm (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  rw [eLpNorm_translate_eq_local k h F] at h_minkowski
  have h_step : eLpNorm (Sobolev.translate
      (d := Module.finrank ℝ E) k h F - F) 2 (volume : Measure EuclN) ≤
      2 * eLpNorm F 2 (volume : Measure EuclN) := by
    rw [two_mul]; exact h_minkowski
  have h_inv_abs : |h⁻¹| = |h|⁻¹ := abs_inv _
  have habs_h_pos : 0 < |h| := abs_pos.mpr hh
  have h_ofReal_inv :
      ENNReal.ofReal |h⁻¹| = (ENNReal.ofReal |h|)⁻¹ := by
    rw [h_inv_abs]
    exact ENNReal.ofReal_inv_of_pos habs_h_pos
  have h_enorm_abs : (‖(h⁻¹ : ℝ)‖ₑ : ℝ≥0∞) = ENNReal.ofReal |h⁻¹| := by
    rw [Real.enorm_eq_ofReal_abs]
  rw [h_enorm_abs, h_ofReal_inv]
  calc (ENNReal.ofReal |h|)⁻¹ *
        eLpNorm (Sobolev.translate
          (d := Module.finrank ℝ E) k h F - F) 2 (volume : Measure EuclN)
      ≤ (ENNReal.ofReal |h|)⁻¹ *
          (2 * eLpNorm F 2 (volume : Measure EuclN)) := by gcongr
    _ = 2 / ENNReal.ofReal |h| * eLpNorm F 2 (volume : Measure EuclN) := by
        rw [← mul_assoc]
        congr 1
        rw [ENNReal.div_eq_inv_mul]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma eLpNorm_mul_bounded
    (M : ℝ) (hM_nn : 0 ≤ M) {f g : EuclN → ℝ}
    (hf_bound : ∀ x, |f x| ≤ M) :
    eLpNorm (fun x => f x * g x) 2 (volume : Measure EuclN) ≤
      ENNReal.ofReal M * eLpNorm g 2 (volume : Measure EuclN) := by
  classical
  have h2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2_ne_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have h2_toReal : ((2 : ℝ≥0∞)).toReal = 2 := by show ENNReal.toReal 2 = 2; rfl
  have h_pow_eq : ∀ a : ℝ≥0∞, a ^ (2 : ℝ) = a ^ (2 : ℕ) := by
    intro a
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
  have h_pt_enorm : ∀ x : EuclN,
      (‖f x * g x‖ₑ : ℝ≥0∞)^(2 : ℕ) ≤
        ENNReal.ofReal (M^2) * (‖g x‖ₑ : ℝ≥0∞)^(2 : ℕ) := by
    intro x
    have h_real : (f x * g x)^2 ≤ M^2 * (g x)^2 := by
      have h_abs_le : |f x| ≤ M := hf_bound x
      have h_sq_le : (f x)^2 ≤ M^2 := by
        rw [show (f x)^2 = |f x|^2 from by rw [sq_abs]]
        exact pow_le_pow_left₀ (abs_nonneg _) h_abs_le 2
      have h_g_sq_nn : 0 ≤ (g x)^2 := sq_nonneg _
      calc (f x * g x)^2
          = (f x)^2 * (g x)^2 := by ring
        _ ≤ M^2 * (g x)^2 := mul_le_mul_of_nonneg_right h_sq_le h_g_sq_nn
    have h_lhs_eq :
        (‖f x * g x‖ₑ : ℝ≥0∞)^(2 : ℕ) =
          ENNReal.ofReal ((f x * g x)^2) := by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2,
        sq_abs]
    have h_rhs_eq :
        (‖g x‖ₑ : ℝ≥0∞)^(2 : ℕ) =
          ENNReal.ofReal ((g x)^2) := by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2,
        sq_abs]
    rw [h_lhs_eq, h_rhs_eq]
    have hM2_nn : 0 ≤ M^2 := sq_nonneg _
    rw [show ENNReal.ofReal (M^2) * ENNReal.ofReal ((g x)^2) =
      ENNReal.ofReal (M^2 * (g x)^2) from
      (ENNReal.ofReal_mul hM2_nn).symm]
    exact ENNReal.ofReal_le_ofReal h_real
  have h_lint_le :
      ∫⁻ x : EuclN, (‖f x * g x‖ₑ : ℝ≥0∞)^(2 : ℕ)
          ∂(volume : Measure EuclN) ≤
        ENNReal.ofReal (M^2) *
          ∫⁻ x : EuclN, (‖g x‖ₑ : ℝ≥0∞)^(2 : ℕ) ∂(volume : Measure EuclN) := by
    calc ∫⁻ x : EuclN, (‖f x * g x‖ₑ : ℝ≥0∞)^(2 : ℕ)
        ≤ ∫⁻ x : EuclN, ENNReal.ofReal (M^2) *
            (‖g x‖ₑ : ℝ≥0∞)^(2 : ℕ) := by
          refine lintegral_mono_ae ?_
          filter_upwards with x using h_pt_enorm x
      _ = ENNReal.ofReal (M^2) *
            ∫⁻ x : EuclN, (‖g x‖ₑ : ℝ≥0∞)^(2 : ℕ) := by
          rw [lintegral_const_mul']
          exact ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h2_ne_zero h2_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal h2_ne_zero h2_ne_top, h2_toReal]
  have h_lhs_pow_eq :
      (∫⁻ x : EuclN, (‖f x * g x‖ₑ : ℝ≥0∞) ^ (2 : ℝ)
          ∂(volume : Measure EuclN)) =
        ∫⁻ x : EuclN, (‖f x * g x‖ₑ : ℝ≥0∞) ^ (2 : ℕ)
          ∂(volume : Measure EuclN) := by
    refine lintegral_congr_ae ?_
    filter_upwards with x using h_pow_eq _
  have h_rhs_pow_eq :
      (∫⁻ x : EuclN, (‖g x‖ₑ : ℝ≥0∞) ^ (2 : ℝ)
          ∂(volume : Measure EuclN)) =
        ∫⁻ x : EuclN, (‖g x‖ₑ : ℝ≥0∞) ^ (2 : ℕ)
          ∂(volume : Measure EuclN) := by
    refine lintegral_congr_ae ?_
    filter_upwards with x using h_pow_eq _
  rw [h_lhs_pow_eq, h_rhs_pow_eq]
  refine le_trans (ENNReal.rpow_le_rpow h_lint_le (by norm_num : (0 : ℝ) ≤ 1/2)) ?_
  have hM2_nn : 0 ≤ M^2 := sq_nonneg _
  have h_mul_rpow :
      (ENNReal.ofReal (M^2) *
          ∫⁻ x : EuclN, (‖g x‖ₑ : ℝ≥0∞) ^ (2 : ℕ)) ^ ((1 : ℝ) / 2) =
        (ENNReal.ofReal (M^2)) ^ ((1 : ℝ) / 2) *
          (∫⁻ x : EuclN, (‖g x‖ₑ : ℝ≥0∞) ^ (2 : ℕ)) ^ ((1 : ℝ) / 2) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1/2)]
  rw [h_mul_rpow]
  have h_sqrt_M2 :
      (ENNReal.ofReal (M^2)) ^ ((1 : ℝ) / 2) = ENNReal.ofReal M := by
    have h_M2_to_pow :
        ENNReal.ofReal (M^2) = (ENNReal.ofReal M) ^ (2 : ℕ) := by
      rw [ENNReal.ofReal_pow hM_nn 2]
    rw [h_M2_to_pow]
    rw [← ENNReal.rpow_natCast (ENNReal.ofReal M) 2,
      ← ENNReal.rpow_mul]
    have h_calc : ((2 : ℕ) : ℝ) * (1 / 2) = 1 := by norm_num
    rw [h_calc, ENNReal.rpow_one]
  rw [h_sqrt_M2]

omit [NeZero (Module.finrank ℝ E)] in
theorem nirenbergTestFunction_seq_grad_tendsto_eLpNorm
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {χ : EuclN → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχ_cs : HasCompactSupport χ)
    (hχ_support_in : tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {h : ℝ}
    (hχ_one : ∀ x ∈ Metric.cthickening |h| K_0, χ x = 1)
    (hχ_dx_zero : ∀ x ∈ Metric.cthickening |h| K_0, ∀ i,
      (fderiv ℝ χ x) (EuclideanSpace.single i 1) = 0)
    (hη_support_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    (hh : h ≠ 0)
    {uSeq : ℕ → EuclN → ℝ}
    (hu_seq_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (uSeq n))
    (hu_seq_cs : ∀ n, HasCompactSupport (uSeq n))
    (hu_seq_l2 : Tendsto (fun n =>
      eLpNorm (fun x => uSeq n x - χ x * D.uChart x) 2
        (volume : Measure EuclN)) atTop (𝓝 0))
    (hu_seq_grad_l2 : ∀ i,
      Tendsto (fun n => eLpNorm
        (fun x => (fderiv ℝ (uSeq n) x) (EuclideanSpace.single i 1) -
          ((fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.uChart x +
           χ x * D.weakPartial i x)) 2 (volume : Measure EuclN))
        atTop (𝓝 0))
    (j : Fin (Module.finrank ℝ E)) :
    Tendsto (fun n => eLpNorm
      (fun y =>
        (fderiv ℝ (nirenbergTestFunction (d := Module.finrank ℝ E)
          k h η (uSeq n)) y) (EuclideanSpace.single j 1) -
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k (-h)
          (fun z =>
            (η z)^2 *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weakPartial j) z +
            2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.uChart z) y) 2
      ((volume : Measure EuclN).restrict
        (Metric.cthickening |h| K_0))) atTop (𝓝 0) := by
  classical
  let _ := hu_seq_cs
  let _ := hK_0_compact
  set F_n : ℕ → EuclN → ℝ := fun n z =>
    2 * η z * ((fderiv ℝ η z) (EuclideanSpace.single j 1)) *
      Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (uSeq n) z +
    (η z)^2 *
      Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun z' => (fderiv ℝ (uSeq n) z') (EuclideanSpace.single j 1)) z
    with hF_n_def
  have h_fderiv_expansion : ∀ n y,
      (fderiv ℝ (nirenbergTestFunction (d := Module.finrank ℝ E)
        k h η (uSeq n)) y) (EuclideanSpace.single j 1) =
      Sobolev.diffQuot
        (d := Module.finrank ℝ E) k (-h) (F_n n) y := by
    intro n y
    exact fderiv_nirenbergTestFunction_apply (j := j) hη (hu_seq_smooth n)
      k hh y
  set B : EuclN → ℝ := fun z =>
    (η z)^2 *
      Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weakPartial j) z +
    2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
      Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.uChart z
    with hB_def
  have h_diff_eq : ∀ n y,
      ((fderiv ℝ (nirenbergTestFunction (d := Module.finrank ℝ E)
        k h η (uSeq n)) y) (EuclideanSpace.single j 1) -
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k (-h) B y) =
      Sobolev.diffQuot
        (d := Module.finrank ℝ E) k (-h) (F_n n - B) y := by
    intro n y
    rw [h_fderiv_expansion n y]
    rw [Sobolev.diffQuot_sub
      (d := Module.finrank ℝ E) k (-h)]
    rfl
  set TERM_A_n : ℕ → EuclN → ℝ := fun n z =>
    2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
      Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun y => uSeq n y - χ y * D.uChart y) z
    with hTerm_A_def
  set TERM_B_n : ℕ → EuclN → ℝ := fun n z =>
    (η z)^2 *
      Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun y =>
          (fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1) -
            ((fderiv ℝ χ y) (EuclideanSpace.single j 1) * D.uChart y +
              χ y * D.weakPartial j y)) z
    with hTerm_B_def
  have h_F_minus_B_eq : ∀ n,
      F_n n - B = TERM_A_n n + TERM_B_n n := by
    intro n
    funext z
    have hTerm_C_eq :=
      diffQuot_chi_sub_one_uChart_vanishes (I := I) (M := M) D
        (k := k) (j := j) (h := h)
        (K_0 := K_0) (η := η) (χ := χ) hχ_one hη_support_in_K_0
    have hTerm_D_eq :=
      diffQuot_dx_chi_uChart_vanishes (I := I) (M := M) D
        (k := k) (j := j) (h := h)
        (K_0 := K_0) (η := η) (χ := χ) hχ_one hχ_dx_zero hη_support_in_K_0
    have hTerm_C_z := congrFun hTerm_C_eq z
    have hTerm_D_z := congrFun hTerm_D_eq z
    have hsub_uchart :
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          (fun y => uSeq n y - χ y * D.uChart y) z =
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (uSeq n) z -
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          (fun y => χ y * D.uChart y) z := by
      have h_eq : (fun y => uSeq n y - χ y * D.uChart y) =
        (uSeq n) - (fun y => χ y * D.uChart y) := by
        funext y; rfl
      rw [h_eq, Sobolev.diffQuot_sub]
      rfl
    have hsub_grad :
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          (fun y =>
            (fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1) -
              ((fderiv ℝ χ y) (EuclideanSpace.single j 1) * D.uChart y +
                χ y * D.weakPartial j y)) z =
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          (fun z' => (fderiv ℝ (uSeq n) z') (EuclideanSpace.single j 1)) z -
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          (fun y =>
            (fderiv ℝ χ y) (EuclideanSpace.single j 1) * D.uChart y +
              χ y * D.weakPartial j y) z := by
      have h_eq : (fun y =>
          (fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1) -
            ((fderiv ℝ χ y) (EuclideanSpace.single j 1) * D.uChart y +
              χ y * D.weakPartial j y)) =
          (fun z' => (fderiv ℝ (uSeq n) z') (EuclideanSpace.single j 1)) -
          (fun y =>
            (fderiv ℝ χ y) (EuclideanSpace.single j 1) * D.uChart y +
              χ y * D.weakPartial j y) := by
        funext y; rfl
      rw [h_eq, Sobolev.diffQuot_sub]
      rfl
    have hsub_chi_uchart :
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          (fun y => (χ y - 1) * D.uChart y) z =
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          (fun y => χ y * D.uChart y) z -
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h D.uChart z := by
      have h_eq : (fun y => (χ y - 1) * D.uChart y) =
          (fun y => χ y * D.uChart y) - D.uChart := by
        funext y
        change (χ y - 1) * D.uChart y =
          (fun y => χ y * D.uChart y) y - D.uChart y
        ring
      rw [h_eq, Sobolev.diffQuot_sub]
      rfl
    have hsub_g_weak :
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          (fun y =>
            (fderiv ℝ χ y) (EuclideanSpace.single j 1) * D.uChart y +
              (χ y - 1) * D.weakPartial j y) z =
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          (fun y =>
            (fderiv ℝ χ y) (EuclideanSpace.single j 1) * D.uChart y +
              χ y * D.weakPartial j y) z -
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (D.weakPartial j) z := by
      have h_eq : (fun y =>
          (fderiv ℝ χ y) (EuclideanSpace.single j 1) * D.uChart y +
            (χ y - 1) * D.weakPartial j y) =
          (fun y =>
            (fderiv ℝ χ y) (EuclideanSpace.single j 1) * D.uChart y +
              χ y * D.weakPartial j y) - D.weakPartial j := by
        funext y
        change (fderiv ℝ χ y) (EuclideanSpace.single j 1) * D.uChart y +
            (χ y - 1) * D.weakPartial j y =
          ((fderiv ℝ χ y) (EuclideanSpace.single j 1) * D.uChart y +
            χ y * D.weakPartial j y) - D.weakPartial j y
        ring
      rw [h_eq, Sobolev.diffQuot_sub]
      rfl
    set α_z : ℝ := 2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1)
    set β_z : ℝ := (η z)^2
    set Du : ℝ := Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (uSeq n) z
    set Dχu : ℝ := Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun y => χ y * D.uChart y) z
    set Du0 : ℝ := Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.uChart z
    set DDu : ℝ := Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun z' => (fderiv ℝ (uSeq n) z') (EuclideanSpace.single j 1)) z
    set Dg : ℝ := Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun y =>
          (fderiv ℝ χ y) (EuclideanSpace.single j 1) * D.uChart y +
            χ y * D.weakPartial j y) z
    set Dwp : ℝ := Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weakPartial j) z
    have hDsub_uchart : Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun y => uSeq n y - χ y * D.uChart y) z = Du - Dχu := hsub_uchart
    have hDsub_grad : Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun y =>
          (fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1) -
            ((fderiv ℝ χ y) (EuclideanSpace.single j 1) * D.uChart y +
              χ y * D.weakPartial j y)) z = DDu - Dg := hsub_grad
    have hDsub_chi : Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun y => (χ y - 1) * D.uChart y) z = Dχu - Du0 := hsub_chi_uchart
    have hDsub_gw : Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun y =>
          (fderiv ℝ χ y) (EuclideanSpace.single j 1) * D.uChart y +
            (χ y - 1) * D.weakPartial j y) z = Dg - Dwp := hsub_g_weak
    have hC_simplified : α_z * (Dχu - Du0) = 0 := by
      have := hTerm_C_z
      rw [hDsub_chi] at this
      exact this
    have hD_simplified : β_z * (Dg - Dwp) = 0 := by
      have := hTerm_D_z
      rw [hDsub_gw] at this
      exact this
    change F_n n z - B z = TERM_A_n n z + TERM_B_n n z
    change (2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
          Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (uSeq n) z +
          (η z)^2 *
            Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h
              (fun z' => (fderiv ℝ (uSeq n) z') (EuclideanSpace.single j 1)) z) -
        ((η z)^2 *
            Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weakPartial j) z +
          2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
            Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h D.uChart z) =
      2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          (fun y => uSeq n y - χ y * D.uChart y) z +
      (η z)^2 *
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          (fun y =>
            (fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1) -
              ((fderiv ℝ χ y) (EuclideanSpace.single j 1) * D.uChart y +
                χ y * D.weakPartial j y)) z
    rw [hDsub_uchart, hDsub_grad]
    linarith
  have hη_cont : Continuous η := hη.continuous
  have hη_partial_cont : Continuous
      (fun y : EuclN => (fderiv ℝ η y) (EuclideanSpace.single j 1)) :=
    (hη.continuous_fderiv (by decide : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
      continuous_const
  obtain ⟨M_η, hM_η_nn, hM_η_bd⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |η x| ≤ M := by
    by_cases hSupport_empty : (tsupport η).Nonempty
    · obtain ⟨xMax, _hxMax_in, hxMax_max⟩ :=
        hη_support.exists_isMaxOn hSupport_empty hη_cont.abs.continuousOn
      refine ⟨|η xMax|, abs_nonneg _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport η
      · exact hxMax_max hx
      · have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport hx
        rw [hηx, abs_zero]; exact abs_nonneg _
    · refine ⟨0, le_refl _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport η
      · exact absurd ⟨x, hx⟩ hSupport_empty
      · have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport hx
        rw [hηx, abs_zero]
  have h_partial_η_support : HasCompactSupport
      (fun y : EuclN => (fderiv ℝ η y) (EuclideanSpace.single j 1)) :=
    hη_support.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1)
  obtain ⟨M_dη, hM_dη_nn, hM_dη_bd⟩ : ∃ M : ℝ, 0 ≤ M ∧
      ∀ x, |(fderiv ℝ η x) (EuclideanSpace.single j 1)| ≤ M := by
    by_cases hSupport_empty :
        (tsupport (fun y : EuclN => (fderiv ℝ η y) (EuclideanSpace.single j 1))).Nonempty
    · obtain ⟨xMax, _hxMax_in, hxMax_max⟩ :=
        h_partial_η_support.exists_isMaxOn hSupport_empty
          (hη_partial_cont.abs.continuousOn)
      refine ⟨|(fderiv ℝ η xMax) (EuclideanSpace.single j 1)|,
        abs_nonneg _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport
          (fun y : EuclN => (fderiv ℝ η y) (EuclideanSpace.single j 1))
      · exact hxMax_max hx
      · have hdηx :
            (fun y : EuclN => (fderiv ℝ η y) (EuclideanSpace.single j 1)) x = 0 :=
          image_eq_zero_of_notMem_tsupport
            (f := fun y : EuclN => (fderiv ℝ η y) (EuclideanSpace.single j 1)) hx
        rw [show (fderiv ℝ η x) (EuclideanSpace.single j 1) = 0 from hdηx,
          abs_zero]
        exact abs_nonneg _
    · refine ⟨0, le_refl _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport
          (fun y : EuclN => (fderiv ℝ η y) (EuclideanSpace.single j 1))
      · exact absurd ⟨x, hx⟩ hSupport_empty
      · have hdηx :
            (fun y : EuclN => (fderiv ℝ η y) (EuclideanSpace.single j 1)) x = 0 :=
          image_eq_zero_of_notMem_tsupport
            (f := fun y : EuclN => (fderiv ℝ η y) (EuclideanSpace.single j 1)) hx
        rw [show (fderiv ℝ η x) (EuclideanSpace.single j 1) = 0 from hdηx,
          abs_zero]
  have hM_2ηdη_nn : 0 ≤ 2 * M_η * M_dη := by positivity
  have hM_2ηdη_bd : ∀ x, |2 * η x * (fderiv ℝ η x) (EuclideanSpace.single j 1)|
      ≤ 2 * M_η * M_dη := by
    intro x
    rw [show 2 * η x * (fderiv ℝ η x) (EuclideanSpace.single j 1) =
      2 * (η x * (fderiv ℝ η x) (EuclideanSpace.single j 1)) from by ring]
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [show 2 * M_η * M_dη = 2 * (M_η * M_dη) from by ring]
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    rw [abs_mul]
    exact mul_le_mul (hM_η_bd x) (hM_dη_bd x) (abs_nonneg _) hM_η_nn
  have hM_η_sq_nn : 0 ≤ M_η^2 := sq_nonneg _
  have hM_η_sq_bd : ∀ x, |(η x)^2| ≤ M_η^2 := by
    intro x
    rw [show (η x)^2 = |η x|^2 from by rw [sq_abs], abs_pow]
    have h_abs_abs : |(|η x|)| = |η x| := abs_of_nonneg (abs_nonneg _)
    rw [h_abs_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hM_η_bd x) 2
  have h_χu_lp : MemLp (fun x => χ x * D.uChart x) 2
      (volume : Measure EuclN) :=
    SubstitutionDischargeSmoothApprox.cutoff_uChart_memLp_two_univ
      (I := I) (M := M) D hχ hχ_cs hχ_support_in
  have h_g_χu_lp : ∀ i,
      MemLp (fun x =>
        (fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.uChart x +
        χ x * D.weakPartial i x) 2 (volume : Measure EuclN) := fun i =>
    SubstitutionDischargeSmoothApprox.cutoff_uChart_partial_memLp_two_univ
      (I := I) (M := M) D hχ hχ_cs hχ_support_in i
  have h_diff_uchart_aesm : ∀ n,
      AEStronglyMeasurable
        (fun y => uSeq n y - χ y * D.uChart y)
        (volume : Measure EuclN) := by
    intro n
    have h_useq_aesm : AEStronglyMeasurable (uSeq n)
        (volume : Measure EuclN) :=
      (hu_seq_smooth n).continuous.aestronglyMeasurable
    have h_χu_aesm : AEStronglyMeasurable
        (fun x => χ x * D.uChart x) (volume : Measure EuclN) :=
      h_χu_lp.aestronglyMeasurable
    exact h_useq_aesm.sub h_χu_aesm
  have h_diff_grad_aesm : ∀ n,
      AEStronglyMeasurable
        (fun y =>
          (fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1) -
            ((fderiv ℝ χ y) (EuclideanSpace.single j 1) * D.uChart y +
              χ y * D.weakPartial j y))
        (volume : Measure EuclN) := by
    intro n
    have h_partial_useq_cont : Continuous
        (fun y : EuclN => (fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1)) :=
      ((hu_seq_smooth n).continuous_fderiv
        (by decide : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply continuous_const
    exact h_partial_useq_cont.aestronglyMeasurable.sub
      (h_g_χu_lp j).aestronglyMeasurable
  have h_A_aesm : ∀ n,
      AEStronglyMeasurable (TERM_A_n n) (volume : Measure EuclN) := by
    intro n
    rw [hTerm_A_def]
    have h_2ηdη_cont : Continuous
        (fun z : EuclN =>
          2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1)) :=
      (continuous_const.mul hη_cont).mul hη_partial_cont
    have h_dq_aesm := Sobolev.aestronglyMeasurable_diffQuot
      (d := Module.finrank ℝ E) k h (h_diff_uchart_aesm n)
    exact h_2ηdη_cont.aestronglyMeasurable.mul h_dq_aesm
  have h_B_aesm : ∀ n,
      AEStronglyMeasurable (TERM_B_n n) (volume : Measure EuclN) := by
    intro n
    rw [hTerm_B_def]
    have h_η_sq_cont : Continuous (fun z : EuclN => (η z)^2) := hη_cont.pow 2
    have h_dq_aesm :=
      Sobolev.aestronglyMeasurable_diffQuot
        (d := Module.finrank ℝ E) k h (h_diff_grad_aesm n)
    exact h_η_sq_cont.aestronglyMeasurable.mul h_dq_aesm
  have h_A_bound : ∀ n,
      eLpNorm (TERM_A_n n) 2 (volume : Measure EuclN) ≤
        ENNReal.ofReal (2 * M_η * M_dη) *
          ((2 / ENNReal.ofReal |h|) *
            eLpNorm (fun y => uSeq n y - χ y * D.uChart y) 2
              (volume : Measure EuclN)) := by
    intro n
    rw [hTerm_A_def]
    have h_step1 :
        eLpNorm (fun z =>
          2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
          Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h
            (fun y => uSeq n y - χ y * D.uChart y) z) 2
            (volume : Measure EuclN) ≤
        ENNReal.ofReal (2 * M_η * M_dη) *
          eLpNorm (Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h
            (fun y => uSeq n y - χ y * D.uChart y)) 2
            (volume : Measure EuclN) :=
      eLpNorm_mul_bounded (2 * M_η * M_dη) hM_2ηdη_nn hM_2ηdη_bd
    have h_step2 :
        eLpNorm (Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          (fun y => uSeq n y - χ y * D.uChart y)) 2
          (volume : Measure EuclN) ≤
        (2 / ENNReal.ofReal |h|) *
          eLpNorm (fun y => uSeq n y - χ y * D.uChart y) 2
            (volume : Measure EuclN) :=
      eLpNorm_diffQuot_le_local k hh (h_diff_uchart_aesm n)
    calc eLpNorm (fun z =>
        2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          (fun y => uSeq n y - χ y * D.uChart y) z) 2
            (volume : Measure EuclN)
        ≤ ENNReal.ofReal (2 * M_η * M_dη) *
          eLpNorm (Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h
            (fun y => uSeq n y - χ y * D.uChart y)) 2
            (volume : Measure EuclN) := h_step1
      _ ≤ ENNReal.ofReal (2 * M_η * M_dη) *
            ((2 / ENNReal.ofReal |h|) *
              eLpNorm (fun y => uSeq n y - χ y * D.uChart y) 2
                (volume : Measure EuclN)) := by gcongr
  have h_B_bound : ∀ n,
      eLpNorm (TERM_B_n n) 2 (volume : Measure EuclN) ≤
        ENNReal.ofReal (M_η^2) *
          ((2 / ENNReal.ofReal |h|) *
            eLpNorm (fun y =>
              (fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1) -
                ((fderiv ℝ χ y) (EuclideanSpace.single j 1) * D.uChart y +
                  χ y * D.weakPartial j y)) 2
              (volume : Measure EuclN)) := by
    intro n
    rw [hTerm_B_def]
    have h_step1 :
        eLpNorm (fun z =>
          (η z)^2 *
            Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h
              (fun y =>
                (fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1) -
                  ((fderiv ℝ χ y) (EuclideanSpace.single j 1) * D.uChart y +
                    χ y * D.weakPartial j y)) z) 2 (volume : Measure EuclN) ≤
        ENNReal.ofReal (M_η^2) *
          eLpNorm (Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h
            (fun y =>
              (fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1) -
                ((fderiv ℝ χ y) (EuclideanSpace.single j 1) * D.uChart y +
                  χ y * D.weakPartial j y))) 2 (volume : Measure EuclN) :=
      eLpNorm_mul_bounded (M_η^2) hM_η_sq_nn hM_η_sq_bd
    have h_step2 :
        eLpNorm (Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          (fun y =>
            (fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1) -
              ((fderiv ℝ χ y) (EuclideanSpace.single j 1) * D.uChart y +
                χ y * D.weakPartial j y))) 2 (volume : Measure EuclN) ≤
        (2 / ENNReal.ofReal |h|) *
          eLpNorm (fun y =>
            (fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1) -
              ((fderiv ℝ χ y) (EuclideanSpace.single j 1) * D.uChart y +
                χ y * D.weakPartial j y)) 2 (volume : Measure EuclN) :=
      eLpNorm_diffQuot_le_local k hh (h_diff_grad_aesm n)
    calc eLpNorm (fun z =>
        (η z)^2 *
          Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h
            (fun y =>
              (fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1) -
                ((fderiv ℝ χ y) (EuclideanSpace.single j 1) * D.uChart y +
                  χ y * D.weakPartial j y)) z) 2 (volume : Measure EuclN)
        ≤ ENNReal.ofReal (M_η^2) *
          eLpNorm (Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h
            (fun y =>
              (fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1) -
                ((fderiv ℝ χ y) (EuclideanSpace.single j 1) * D.uChart y +
                  χ y * D.weakPartial j y))) 2 (volume : Measure EuclN) :=
            h_step1
      _ ≤ ENNReal.ofReal (M_η^2) *
            ((2 / ENNReal.ofReal |h|) *
              eLpNorm (fun y =>
                (fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1) -
                  ((fderiv ℝ χ y) (EuclideanSpace.single j 1) * D.uChart y +
                    χ y * D.weakPartial j y)) 2
                (volume : Measure EuclN)) := by gcongr
  have h_F_minus_B_aesm : ∀ n,
      AEStronglyMeasurable (F_n n - B) (volume : Measure EuclN) := by
    intro n
    have h_eq := h_F_minus_B_eq n
    rw [h_eq]
    exact (h_A_aesm n).add (h_B_aesm n)
  have h_outer_bound : ∀ n,
      eLpNorm (Sobolev.diffQuot
        (d := Module.finrank ℝ E) k (-h) (F_n n - B)) 2
        (volume : Measure EuclN) ≤
      (2 / ENNReal.ofReal |h|) *
        eLpNorm (F_n n - B) 2 (volume : Measure EuclN) := by
    intro n
    have h_neg_h_ne : -h ≠ 0 := neg_ne_zero.mpr hh
    have habs_neg_h : |(-h)| = |h| := by rw [abs_neg]
    have := eLpNorm_diffQuot_le_local k h_neg_h_ne (h_F_minus_B_aesm n)
    rw [habs_neg_h] at this
    exact this
  have h_FB_bound : ∀ n,
      eLpNorm (F_n n - B) 2 (volume : Measure EuclN) ≤
      eLpNorm (TERM_A_n n) 2 (volume : Measure EuclN) +
      eLpNorm (TERM_B_n n) 2 (volume : Measure EuclN) := by
    intro n
    rw [h_F_minus_B_eq n]
    exact eLpNorm_add_le (h_A_aesm n) (h_B_aesm n)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have habs_h_pos : 0 < |h| := abs_pos.mpr hh
  have h_const_2η_ne_top : ENNReal.ofReal (2 * M_η * M_dη) *
      (2 / ENNReal.ofReal |h|) ≠ ⊤ := by
    refine ENNReal.mul_ne_top ?_ ?_
    · exact ENNReal.ofReal_ne_top
    · exact ENNReal.div_ne_top ENNReal.ofNat_ne_top
        (ENNReal.ofReal_pos.mpr habs_h_pos).ne'
  have h_const_η_sq_ne_top : ENNReal.ofReal (M_η^2) *
      (2 / ENNReal.ofReal |h|) ≠ ⊤ := by
    refine ENNReal.mul_ne_top ?_ ?_
    · exact ENNReal.ofReal_ne_top
    · exact ENNReal.div_ne_top ENNReal.ofNat_ne_top
        (ENNReal.ofReal_pos.mpr habs_h_pos).ne'
  have h_A_tendsto :
      Tendsto (fun n => eLpNorm (TERM_A_n n) 2 (volume : Measure EuclN))
        atTop (𝓝 0) := by
    have h_seq_tendsto :
        Tendsto (fun n =>
          ENNReal.ofReal (2 * M_η * M_dη) *
            ((2 / ENNReal.ofReal |h|) *
              eLpNorm (fun y => uSeq n y - χ y * D.uChart y) 2
                (volume : Measure EuclN))) atTop (𝓝 0) := by
      have h_eq_assoc : ∀ n,
          ENNReal.ofReal (2 * M_η * M_dη) *
            ((2 / ENNReal.ofReal |h|) *
              eLpNorm (fun y => uSeq n y - χ y * D.uChart y) 2
                (volume : Measure EuclN)) =
          (ENNReal.ofReal (2 * M_η * M_dη) * (2 / ENNReal.ofReal |h|)) *
            eLpNorm (fun y => uSeq n y - χ y * D.uChart y) 2
              (volume : Measure EuclN) := by
        intro n; ring
      simp only [h_eq_assoc]
      have h := ENNReal.Tendsto.const_mul (a :=
          ENNReal.ofReal (2 * M_η * M_dη) * (2 / ENNReal.ofReal |h|))
          hu_seq_l2 (Or.inr h_const_2η_ne_top)
      simpa using h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      h_seq_tendsto ?_ ?_
    · refine Filter.Eventually.of_forall (fun n => ?_)
      exact zero_le
    · refine Filter.Eventually.of_forall h_A_bound
  have h_B_tendsto :
      Tendsto (fun n => eLpNorm (TERM_B_n n) 2 (volume : Measure EuclN))
        atTop (𝓝 0) := by
    have h_seq_tendsto :
        Tendsto (fun n =>
          ENNReal.ofReal (M_η^2) *
            ((2 / ENNReal.ofReal |h|) *
              eLpNorm (fun y =>
                (fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1) -
                  ((fderiv ℝ χ y) (EuclideanSpace.single j 1) * D.uChart y +
                    χ y * D.weakPartial j y)) 2 (volume : Measure EuclN))) atTop
          (𝓝 0) := by
      have h_eq_assoc : ∀ n,
          ENNReal.ofReal (M_η^2) *
            ((2 / ENNReal.ofReal |h|) *
              eLpNorm (fun y =>
                (fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1) -
                  ((fderiv ℝ χ y) (EuclideanSpace.single j 1) * D.uChart y +
                    χ y * D.weakPartial j y)) 2 (volume : Measure EuclN)) =
          (ENNReal.ofReal (M_η^2) * (2 / ENNReal.ofReal |h|)) *
            eLpNorm (fun y =>
              (fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1) -
                ((fderiv ℝ χ y) (EuclideanSpace.single j 1) * D.uChart y +
                  χ y * D.weakPartial j y)) 2 (volume : Measure EuclN) := by
        intro n; ring
      simp only [h_eq_assoc]
      have h := ENNReal.Tendsto.const_mul (a :=
          ENNReal.ofReal (M_η^2) * (2 / ENNReal.ofReal |h|))
          (hu_seq_grad_l2 j) (Or.inr h_const_η_sq_ne_top)
      simpa using h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      h_seq_tendsto ?_ ?_
    · refine Filter.Eventually.of_forall (fun n => ?_)
      exact zero_le
    · refine Filter.Eventually.of_forall h_B_bound
  have h_AB_tendsto :
      Tendsto (fun n => eLpNorm (TERM_A_n n) 2 (volume : Measure EuclN) +
        eLpNorm (TERM_B_n n) 2 (volume : Measure EuclN)) atTop (𝓝 0) := by
    have := h_A_tendsto.add h_B_tendsto
    simpa using this
  have h_const_outer_ne_top : (2 / ENNReal.ofReal |h|) ≠ ⊤ :=
    ENNReal.div_ne_top ENNReal.ofNat_ne_top
      (ENNReal.ofReal_pos.mpr habs_h_pos).ne'
  have h_FB_seq_tendsto :
      Tendsto (fun n => (2 / ENNReal.ofReal |h|) *
        (eLpNorm (TERM_A_n n) 2 (volume : Measure EuclN) +
          eLpNorm (TERM_B_n n) 2 (volume : Measure EuclN))) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (a := (2 / ENNReal.ofReal |h|))
      h_AB_tendsto (Or.inr h_const_outer_ne_top)
    simpa using h
  have h_outer_tendsto :
      Tendsto (fun n => eLpNorm (Sobolev.diffQuot
        (d := Module.finrank ℝ E) k (-h) (F_n n - B)) 2
        (volume : Measure EuclN)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      h_FB_seq_tendsto ?_ ?_
    · refine Filter.Eventually.of_forall (fun n => ?_)
      exact zero_le
    · refine Filter.Eventually.of_forall (fun n => ?_)
      calc eLpNorm (Sobolev.diffQuot
            (d := Module.finrank ℝ E) k (-h) (F_n n - B)) 2
            (volume : Measure EuclN)
          ≤ (2 / ENNReal.ofReal |h|) *
              eLpNorm (F_n n - B) 2 (volume : Measure EuclN) :=
            h_outer_bound n
        _ ≤ (2 / ENNReal.ofReal |h|) *
              (eLpNorm (TERM_A_n n) 2 (volume : Measure EuclN) +
                eLpNorm (TERM_B_n n) 2 (volume : Measure EuclN)) := by
              gcongr
              exact h_FB_bound n
  have h_restrict_tendsto :
      Tendsto (fun n => eLpNorm (Sobolev.diffQuot
        (d := Module.finrank ℝ E) k (-h) (F_n n - B)) 2
        ((volume : Measure EuclN).restrict
          (Metric.cthickening |h| K_0))) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      h_outer_tendsto ?_ ?_
    · refine Filter.Eventually.of_forall (fun n => ?_)
      exact zero_le
    · refine Filter.Eventually.of_forall (fun n => ?_)
      exact MeasureTheory.eLpNorm_mono_measure
        (Sobolev.diffQuot
          (d := Module.finrank ℝ E) k (-h) (F_n n - B))
        Measure.restrict_le_self
  have h_goal_eq : ∀ n,
      (fun y =>
        (fderiv ℝ (nirenbergTestFunction (d := Module.finrank ℝ E)
          k h η (uSeq n)) y) (EuclideanSpace.single j 1) -
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k (-h)
          (fun z =>
            (η z)^2 *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weakPartial j) z +
            2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.uChart z) y) =
      Sobolev.diffQuot
        (d := Module.finrank ℝ E) k (-h) (F_n n - B) := by
    intro n
    funext y
    exact h_diff_eq n y
  rw [show (fun n => eLpNorm
        (fun y =>
          (fderiv ℝ (nirenbergTestFunction (d := Module.finrank ℝ E)
            k h η (uSeq n)) y) (EuclideanSpace.single j 1) -
          Sobolev.diffQuot
            (d := Module.finrank ℝ E) k (-h)
            (fun z =>
              (η z)^2 *
                Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h (D.weakPartial j) z +
              2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h D.uChart z) y) 2
        ((volume : Measure EuclN).restrict
          (Metric.cthickening |h| K_0))) =
      (fun n => eLpNorm
        (Sobolev.diffQuot
          (d := Module.finrank ℝ E) k (-h) (F_n n - B)) 2
        ((volume : Measure EuclN).restrict
          (Metric.cthickening |h| K_0))) from by
    funext n
    congr 1
    exact h_goal_eq n]
  exact h_restrict_tendsto

end SubstitutionDischargeGradTendsto
end Sobolev
end Analysis
end CalabiYau
