-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Nirenberg/ChartBilinearDischarge/SubstitutionIBP.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Nirenberg.ChartBilinearDischarge.SubstitutionIBPExpand
public import CalabiYau.Analysis.Elliptic.Operator.ChartLocalLaplacian
public import CalabiYau.Analysis.Elliptic.Regularity.ChartBilinear.H1Compl
public import CalabiYau.Analysis.Sobolev.Nirenberg.TestFunction.Basic
public import CalabiYau.Analysis.Sobolev.Nirenberg.TestFunction.TranslatedCutoffDiffQuot

@[expose] public section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal Pointwise

namespace CalabiYau
namespace Analysis
namespace Sobolev
namespace SubstitutionDischargeIBP

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
open Sobolev.NirenbergTestFunction
open Sobolev.SubstitutionDischargeSmoothApprox
open Sobolev.SubstitutionNonSmoothChartBilinear
open Sobolev.SubstitutionDischargeIBPExpand

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma exists_bound_of_contDiff_compactSupport
    {η : EuclN → ℝ} (hη_cont : Continuous η) (hη_cs : HasCompactSupport η) :
    ∃ M_η : ℝ, 0 ≤ M_η ∧ ∀ x, |η x| ≤ M_η := by
  classical
  by_cases hSupport_empty : (tsupport η).Nonempty
  · obtain ⟨xMax, _hxMax_in, hxMax_max⟩ :=
      hη_cs.exists_isMaxOn hSupport_empty hη_cont.abs.continuousOn
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

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma exists_bound_partial_eta
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_cs : HasCompactSupport η)
    (j : Fin (Module.finrank ℝ E)) :
    ∃ M_dη : ℝ, 0 ≤ M_dη ∧
      ∀ x, |(fderiv ℝ η x) (EuclideanSpace.single j 1)| ≤ M_dη := by
  classical
  have h_top_ne_zero : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by decide
  have h_partial_eta_cont : Continuous
      (fun z : EuclN => (fderiv ℝ η z) (EuclideanSpace.single j 1)) :=
    (hη.continuous_fderiv h_top_ne_zero).clm_apply continuous_const
  have h_partial_eta_cs : HasCompactSupport
      (fun z : EuclN => (fderiv ℝ η z) (EuclideanSpace.single j 1)) :=
    hη_cs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1)
  exact exists_bound_of_contDiff_compactSupport h_partial_eta_cont
    h_partial_eta_cs

omit [NeZero (Module.finrank ℝ E)] in
private lemma exists_bound_weightedInvGram
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, |weightedInvGramOnEuclid (I := I) g α i j y| ≤ C :=
  weightedInvGramOnEuclid_bounded_on_compact (I := I) (M := M) g α i j hK hK_in

omit [NeZero (Module.finrank ℝ E)] in
private lemma F_ij_memLp_restrict
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {h : ℝ}
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    (i : Fin (Module.finrank ℝ E)) (j : Fin (Module.finrank ℝ E)) :
    MemLp (fun y => weightedInvGramOnEuclid (I := I) g α i j y *
        D.weakPartial i y) 2
      ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)) := by
  classical
  have h_thick_compact : IsCompact (Metric.cthickening |h| K_0) :=
    cthickening_K_0_isCompact (E := E) hK_0_compact
  have h_thick_meas : MeasurableSet (Metric.cthickening |h| K_0) :=
    h_thick_compact.measurableSet
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    exists_bound_weightedInvGram (I := I) (M := M) g α i j h_thick_compact h_thick
  have hwp_lp : MemLp (D.weakPartial i) 2
      ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)) :=
    D.weak_partial_locally_memLp i (Metric.cthickening |h| K_0) h_thick_compact
      h_thick
  have h_weight_cont : ContinuousOn (weightedInvGramOnEuclid (I := I) g α i j)
      (chartTargetEuclid (I := I) (M := M) α) :=
    (weightedInvGramOnEuclid_contDiffOn (I := I) g α i j).continuousOn
  have h_weight_cont_thick : ContinuousOn
      (weightedInvGramOnEuclid (I := I) g α i j)
      (Metric.cthickening |h| K_0) :=
    h_weight_cont.mono h_thick
  have h_weight_aesm : AEStronglyMeasurable
      (weightedInvGramOnEuclid (I := I) g α i j)
      ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)) :=
    h_weight_cont_thick.aestronglyMeasurable_of_isCompact h_thick_compact
      h_thick_meas
  have h_pt_bound : ∀ᵐ y
      ∂((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)),
      ‖weightedInvGramOnEuclid (I := I) g α i j y * D.weakPartial i y‖ ≤
        ‖C * D.weakPartial i y‖ := by
    rw [ae_restrict_iff' h_thick_meas]
    refine Filter.Eventually.of_forall ?_
    intro y hy
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hC_nn]
    exact mul_le_mul_of_nonneg_right (hC_bd y hy) (abs_nonneg _)
  have h_prod_aesm : AEStronglyMeasurable
      (fun y => weightedInvGramOnEuclid (I := I) g α i j y * D.weakPartial i y)
      ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)) :=
    h_weight_aesm.mul hwp_lp.aestronglyMeasurable
  exact MemLp.mono (hwp_lp.const_mul C) h_prod_aesm h_pt_bound

private noncomputable def F_ij_extended
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {h : ℝ} (K_0 : Set EuclN)
    (i j : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  (Metric.cthickening |h| K_0).indicator
    (fun y => weightedInvGramOnEuclid (I := I) g α i j y *
      D.weakPartial i y)

omit [NeZero (Module.finrank ℝ E)] in
private lemma F_ij_extended_memLp
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {h : ℝ}
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    (i j : Fin (Module.finrank ℝ E)) :
    MemLp (F_ij_extended (I := I) (M := M) D (h := h) K_0 i j) 2
      (volume : Measure EuclN) := by
  classical
  unfold F_ij_extended
  have h_thick_compact : IsCompact (Metric.cthickening |h| K_0) :=
    cthickening_K_0_isCompact (E := E) hK_0_compact
  have h_thick_meas : MeasurableSet (Metric.cthickening |h| K_0) :=
    h_thick_compact.measurableSet
  exact (MeasureTheory.memLp_indicator_iff_restrict h_thick_meas).mpr
    (F_ij_memLp_restrict (I := I) (M := M) D hK_0_compact h_thick i j)

omit [NeZero (Module.finrank ℝ E)] in
private lemma u_chart_indicator_memLp
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {h : ℝ}
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    MemLp ((Metric.cthickening |h| K_0).indicator D.uChart) 2
      (volume : Measure EuclN) := by
  classical
  have h_thick_compact : IsCompact (Metric.cthickening |h| K_0) :=
    cthickening_K_0_isCompact (E := E) hK_0_compact
  have h_thick_meas : MeasurableSet (Metric.cthickening |h| K_0) :=
    h_thick_compact.measurableSet
  refine (MeasureTheory.memLp_indicator_iff_restrict h_thick_meas).mpr ?_
  exact memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure (I := I) (M := M)
    D.u_chart_memLp_weighted h_thick_compact h_thick_meas h_thick

omit [NeZero (Module.finrank ℝ E)] in
private lemma weak_partial_indicator_memLp
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {h : ℝ}
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    (j : Fin (Module.finrank ℝ E)) :
    MemLp ((Metric.cthickening |h| K_0).indicator (D.weakPartial j)) 2
      (volume : Measure EuclN) := by
  classical
  have h_thick_compact : IsCompact (Metric.cthickening |h| K_0) :=
    cthickening_K_0_isCompact (E := E) hK_0_compact
  have h_thick_meas : MeasurableSet (Metric.cthickening |h| K_0) :=
    h_thick_compact.measurableSet
  refine (MeasureTheory.memLp_indicator_iff_restrict h_thick_meas).mpr ?_
  exact D.weak_partial_locally_memLp j (Metric.cthickening |h| K_0)
    h_thick_compact h_thick

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma memLp_diffQuot_of_memLp
    {F : EuclN → ℝ} (hF_lp : MemLp F 2 (volume : Measure EuclN))
    (k : Fin (Module.finrank ℝ E)) {h : ℝ} (hh : h ≠ 0) :
    MemLp (Sobolev.diffQuot
      (d := Module.finrank ℝ E) k h F) 2 (volume : Measure EuclN) := by
  classical
  have hF_aesm : AEStronglyMeasurable F (volume : Measure EuclN) :=
    hF_lp.aestronglyMeasurable
  have hdq_aesm : AEStronglyMeasurable
      (Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h F) (volume : Measure EuclN) :=
    Sobolev.aestronglyMeasurable_diffQuot
      (d := Module.finrank ℝ E) k h hF_aesm
  refine ⟨hdq_aesm, ?_⟩
  have h_dq_eq : Sobolev.diffQuot
      (d := Module.finrank ℝ E) k h F =
      h⁻¹ • (Sobolev.translate
        (d := Module.finrank ℝ E) k h F - F) := by
    funext x
    rw [Sobolev.diffQuot_apply_of_ne
      (d := Module.finrank ℝ E) k hh F x]
    show (F (x + h • EuclideanSpace.single k 1) - F x) / h =
      (h⁻¹ • (Sobolev.translate
        (d := Module.finrank ℝ E) k h F - F)) x
    simp [Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      Sobolev.translate]
    field_simp
  rw [h_dq_eq]
  have hτF_lp : MemLp (Sobolev.translate
      (d := Module.finrank ℝ E) k h F) 2 (volume : Measure EuclN) :=
    Sobolev.memLp_translate
      (d := Module.finrank ℝ E) (p := 2) k h hF_lp
  have h_diff_lp : MemLp ((Sobolev.translate
      (d := Module.finrank ℝ E) k h F) - F) 2 (volume : Measure EuclN) :=
    hτF_lp.sub hF_lp
  exact (h_diff_lp.const_smul h⁻¹).eLpNorm_lt_top

private noncomputable def testFactor
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (η : EuclN → ℝ) (k : Fin (Module.finrank ℝ E)) (h : ℝ)
    (j : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun z => (η z)^2 *
    Sobolev.diffQuot
      (d := Module.finrank ℝ E) k h (D.weakPartial j) z +
    2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
      Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.uChart z

private noncomputable def testFactorExtended
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (η : EuclN → ℝ) (k : Fin (Module.finrank ℝ E)) (h : ℝ) (K_0 : Set EuclN)
    (j : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun z => (η z)^2 *
    Sobolev.diffQuot
      (d := Module.finrank ℝ E) k h
      ((Metric.cthickening |h| K_0).indicator (D.weakPartial j)) z +
    2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
      Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        ((Metric.cthickening |h| K_0).indicator D.uChart) z

omit [NeZero (Module.finrank ℝ E)] in
private lemma testFactorExtended_memLp_two
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (k : Fin (Module.finrank ℝ E))
    {h : ℝ} (hh : h ≠ 0)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    (j : Fin (Module.finrank ℝ E)) :
    MemLp (testFactorExtended (I := I) (M := M) D η k h K_0 j) 2
      (volume : Measure EuclN) := by
  classical
  have hη_cont : Continuous η := hη.continuous
  obtain ⟨M_η, hM_η_nn, hM_η_bd⟩ :=
    exists_bound_of_contDiff_compactSupport hη_cont hη_support
  obtain ⟨M_dη, hM_dη_nn, hM_dη_bd⟩ :=
    exists_bound_partial_eta hη hη_support j
  have h_top_ne_zero : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by decide
  have h_partial_eta_cont : Continuous
      (fun z : EuclN => (fderiv ℝ η z) (EuclideanSpace.single j 1)) :=
    (hη.continuous_fderiv h_top_ne_zero).clm_apply continuous_const
  have hu_ext_lp := u_chart_indicator_memLp (I := I) (M := M) D
    hK_0_compact h_thick
  have hwp_ext_lp := weak_partial_indicator_memLp (I := I) (M := M) D
    hK_0_compact h_thick j
  have hdq_u_ext_lp : MemLp
      (Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        ((Metric.cthickening |h| K_0).indicator D.uChart)) 2
      (volume : Measure EuclN) :=
    memLp_diffQuot_of_memLp hu_ext_lp k hh
  have hdq_wp_ext_lp : MemLp
      (Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        ((Metric.cthickening |h| K_0).indicator (D.weakPartial j))) 2
      (volume : Measure EuclN) :=
    memLp_diffQuot_of_memLp hwp_ext_lp k hh
  unfold testFactorExtended
  have ht1'_pt_bd : ∀ z, ‖(η z)^2 *
      Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        ((Metric.cthickening |h| K_0).indicator (D.weakPartial j)) z‖ ≤
      ‖M_η^2 *
      Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        ((Metric.cthickening |h| K_0).indicator (D.weakPartial j)) z‖ := by
    intro z
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ M_η^2)]
    have h_eta_sq : |(η z)^2| ≤ M_η^2 := by
      have h_abs : |η z| ≤ M_η := hM_η_bd z
      have h_nn : 0 ≤ |η z| := abs_nonneg _
      have h_eq : |(η z)^2| = (η z)^2 := abs_of_nonneg (sq_nonneg _)
      rw [h_eq]
      calc (η z)^2 = (|η z|)^2 := (sq_abs _).symm
        _ ≤ M_η^2 := by
          exact pow_le_pow_left₀ h_nn h_abs 2
    exact mul_le_mul_of_nonneg_right h_eta_sq (abs_nonneg _)
  have ht1'_aesm : AEStronglyMeasurable (fun z => (η z)^2 *
      Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        ((Metric.cthickening |h| K_0).indicator (D.weakPartial j)) z)
      (volume : Measure EuclN) :=
    (hη_cont.pow 2).aestronglyMeasurable.mul hdq_wp_ext_lp.aestronglyMeasurable
  have ht1'_lp : MemLp (fun z => (η z)^2 *
      Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        ((Metric.cthickening |h| K_0).indicator (D.weakPartial j)) z) 2
      (volume : Measure EuclN) :=
    MemLp.mono (hdq_wp_ext_lp.const_mul (M_η^2)) ht1'_aesm
      (Filter.Eventually.of_forall ht1'_pt_bd)
  have ht2'_pt_bd : ∀ z, ‖2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
      Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        ((Metric.cthickening |h| K_0).indicator D.uChart) z‖ ≤
      ‖(2 * M_η * M_dη) *
      Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        ((Metric.cthickening |h| K_0).indicator D.uChart) z‖ := by
    intro z
    have h_step : |2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1)| ≤
        2 * M_η * M_dη := by
      have h_factor : |2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1)| =
          2 * |η z| * |(fderiv ℝ η z) (EuclideanSpace.single j 1)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      rw [h_factor]
      have h1 : 2 * |η z| ≤ 2 * M_η := by
        have : |η z| ≤ M_η := hM_η_bd z
        linarith
      have h2 : (2 * |η z|) * |(fderiv ℝ η z) (EuclideanSpace.single j 1)| ≤
          (2 * M_η) * M_dη := by
        apply mul_le_mul h1 (hM_dη_bd z) (abs_nonneg _)
        linarith
      have h3 : 2 * M_η * M_dη = (2 * M_η) * M_dη := by ring
      rw [h3]
      exact h2
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    rw [show |2 * M_η * M_dη *
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          ((Metric.cthickening |h| K_0).indicator D.uChart) z| =
      (2 * M_η * M_dη) *
        |Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          ((Metric.cthickening |h| K_0).indicator D.uChart) z| from by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * M_η * M_dη)]]
    rw [show |2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          ((Metric.cthickening |h| K_0).indicator D.uChart) z| =
      |2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1)| *
        |Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          ((Metric.cthickening |h| K_0).indicator D.uChart) z| from by
      rw [abs_mul]]
    exact mul_le_mul_of_nonneg_right h_step (abs_nonneg _)
  have ht2'_aesm : AEStronglyMeasurable
      (fun z => 2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          ((Metric.cthickening |h| K_0).indicator D.uChart) z)
      (volume : Measure EuclN) := by
    have h1 : AEStronglyMeasurable
        (fun z : EuclN => 2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1))
        (volume : Measure EuclN) :=
      ((continuous_const.mul hη_cont).mul h_partial_eta_cont).aestronglyMeasurable
    exact h1.mul hdq_u_ext_lp.aestronglyMeasurable
  have ht2'_lp : MemLp
      (fun z => 2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          ((Metric.cthickening |h| K_0).indicator D.uChart) z) 2
      (volume : Measure EuclN) :=
    MemLp.mono (hdq_u_ext_lp.const_mul (2 * M_η * M_dη)) ht2'_aesm
      (Filter.Eventually.of_forall ht2'_pt_bd)
  exact ht1'_lp.add ht2'_lp

omit [NeZero (Module.finrank ℝ E)] in
private lemma testFactor_eq_testFactorExtended_on_tsupport
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN}
    {η : EuclN → ℝ} {h : ℝ}
    (hη_support_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    (j : Fin (Module.finrank ℝ E))
    {z : EuclN} (hz : z ∈ tsupport η) :
    testFactor (I := I) (M := M) D η k h j z =
      testFactorExtended (I := I) (M := M) D η k h K_0 j z := by
  classical
  have h_K_0_thick : K_0 ⊆ Metric.cthickening |h| K_0 :=
    Metric.self_subset_cthickening _
  have hz_K_0 : z ∈ K_0 := hη_support_in_K_0 hz
  have hz_thick : z ∈ Metric.cthickening |h| K_0 := h_K_0_thick hz_K_0
  have hz_shift : z + h • EuclideanSpace.single k 1 ∈ Metric.cthickening |h| K_0 := by
    refine Metric.mem_cthickening_of_dist_le _ _ |h| K_0 hz_K_0 ?_
    rw [dist_eq_norm]
    have hcalc : (z + h • EuclideanSpace.single k 1) - z =
        h • EuclideanSpace.single k 1 := by
      rw [add_sub_cancel_left]
    rw [hcalc, norm_smul]
    simp [Real.norm_eq_abs]
  have h_dq_wp : Sobolev.diffQuot
      (d := Module.finrank ℝ E) k h (D.weakPartial j) z =
    Sobolev.diffQuot
      (d := Module.finrank ℝ E) k h
      ((Metric.cthickening |h| K_0).indicator (D.weakPartial j)) z := by
    by_cases hh_eq : h = 0
    · rw [hh_eq]; simp [Sobolev.diffQuot]
    · rw [Sobolev.diffQuot_apply_of_ne
            (d := Module.finrank ℝ E) k hh_eq,
          Sobolev.diffQuot_apply_of_ne
            (d := Module.finrank ℝ E) k hh_eq]
      congr 1
      rw [Set.indicator_of_mem hz_shift, Set.indicator_of_mem hz_thick]
  have h_dq_u : Sobolev.diffQuot
      (d := Module.finrank ℝ E) k h D.uChart z =
    Sobolev.diffQuot
      (d := Module.finrank ℝ E) k h
      ((Metric.cthickening |h| K_0).indicator D.uChart) z := by
    by_cases hh_eq : h = 0
    · rw [hh_eq]; simp [Sobolev.diffQuot]
    · rw [Sobolev.diffQuot_apply_of_ne
            (d := Module.finrank ℝ E) k hh_eq,
          Sobolev.diffQuot_apply_of_ne
            (d := Module.finrank ℝ E) k hh_eq]
      congr 1
      rw [Set.indicator_of_mem hz_shift, Set.indicator_of_mem hz_thick]
  unfold testFactor testFactorExtended
  rw [h_dq_wp, h_dq_u]

omit [NeZero (Module.finrank ℝ E)] in
private lemma testFactor_eq_zero_outside_tsupport
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {η : EuclN → ℝ} (k : Fin (Module.finrank ℝ E)) (h : ℝ)
    (j : Fin (Module.finrank ℝ E))
    {z : EuclN} (hz : z ∉ tsupport η) :
    testFactor (I := I) (M := M) D η k h j z = 0 := by
  unfold testFactor
  have hηz : η z = 0 := image_eq_zero_of_notMem_tsupport hz
  rw [show (η z)^2 = 0 from by rw [hηz]; ring, zero_mul]
  rw [show 2 * η z = 0 from by rw [hηz]; ring]
  ring

omit [NeZero (Module.finrank ℝ E)] in
private lemma testFactorExtended_eq_zero_outside_tsupport
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {η : EuclN → ℝ} {h : ℝ} (k : Fin (Module.finrank ℝ E)) (K_0 : Set EuclN)
    (j : Fin (Module.finrank ℝ E))
    {z : EuclN} (hz : z ∉ tsupport η) :
    testFactorExtended (I := I) (M := M) D η k h K_0 j z = 0 := by
  unfold testFactorExtended
  have hηz : η z = 0 := image_eq_zero_of_notMem_tsupport hz
  rw [show (η z)^2 = 0 from by rw [hηz]; ring, zero_mul]
  rw [show 2 * η z = 0 from by rw [hηz]; ring]
  ring

omit [NeZero (Module.finrank ℝ E)] in
private lemma testFactor_eq_testFactorExtended
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN}
    {η : EuclN → ℝ}
    (hη_support_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E)) {h : ℝ}
    (j : Fin (Module.finrank ℝ E)) :
    testFactor (I := I) (M := M) D η k h j =
      testFactorExtended (I := I) (M := M) D η k h K_0 j := by
  funext z
  by_cases hz : z ∈ tsupport η
  · exact testFactor_eq_testFactorExtended_on_tsupport (I := I) (M := M) D
      hη_support_in_K_0 k j hz
  · rw [testFactor_eq_zero_outside_tsupport (I := I) (M := M) D k h j hz,
      testFactorExtended_eq_zero_outside_tsupport (I := I) (M := M) D k K_0 j hz]

omit [NeZero (Module.finrank ℝ E)] in
private lemma testFactor_memLp_two
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (hη_support_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {h : ℝ} (hh : h ≠ 0)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    (j : Fin (Module.finrank ℝ E)) :
    MemLp (testFactor (I := I) (M := M) D η k h j) 2
      (volume : Measure EuclN) := by
  rw [testFactor_eq_testFactorExtended (I := I) (M := M) D
    hη_support_in_K_0 k (h := h) j]
  exact testFactorExtended_memLp_two (I := I) (M := M) D hK_0_compact hη hη_support
    k hh h_thick j

omit [NeZero (Module.finrank ℝ E)] in
theorem chartBilinear_factor_integrable
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (hη_support_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {h : ℝ} (hh : h ≠ 0)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    (i j : Fin (Module.finrank ℝ E)) :
    Integrable (fun y =>
      weightedInvGramOnEuclid (I := I) g α i j y *
        D.weakPartial i y *
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k (-h)
          (fun z => (η z) ^ 2 *
            Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weakPartial j) z +
            2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.uChart z) y)
      ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)) := by
  classical
  have hF_lp : MemLp (fun y =>
      weightedInvGramOnEuclid (I := I) g α i j y * D.weakPartial i y) 2
      ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)) :=
    F_ij_memLp_restrict (I := I) (M := M) D hK_0_compact h_thick i j
  have h_test_lp_global :
      MemLp (testFactor (I := I) (M := M) D η k h j) 2
        (volume : Measure EuclN) :=
    testFactor_memLp_two (I := I) (M := M) D hK_0_compact hη hη_support
      hη_support_in_K_0 k hh h_thick j
  have hnh : (-h) ≠ 0 := neg_ne_zero.mpr hh
  have h_dq_test_lp_global :
      MemLp (Sobolev.diffQuot
        (d := Module.finrank ℝ E) k (-h)
        (testFactor (I := I) (M := M) D η k h j)) 2
        (volume : Measure EuclN) :=
    memLp_diffQuot_of_memLp h_test_lp_global k hnh
  have h_dq_test_lp_restrict :
      MemLp (Sobolev.diffQuot
        (d := Module.finrank ℝ E) k (-h)
        (testFactor (I := I) (M := M) D η k h j)) 2
        ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)) :=
    h_dq_test_lp_global.restrict _
  have h_int_prod : Integrable (fun y =>
      (fun y => weightedInvGramOnEuclid (I := I) g α i j y *
        D.weakPartial i y) y *
      Sobolev.diffQuot
        (d := Module.finrank ℝ E) k (-h)
        (testFactor (I := I) (M := M) D η k h j) y)
      ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)) := by
    let _ : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 := by
      constructor
      rw [show (1 : ℝ≥0∞)⁻¹ = 1 from inv_one]
      rw [ENNReal.inv_two_add_inv_two]
    have h := MemLp.integrable_mul (μ :=
      (volume : Measure EuclN).restrict (Metric.cthickening |h| K_0))
      (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) hF_lp h_dq_test_lp_restrict
    exact h.congr (Filter.Eventually.of_forall fun _ ↦ rfl)
  have h_assoc : (fun y =>
      weightedInvGramOnEuclid (I := I) g α i j y *
        D.weakPartial i y *
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k (-h)
          (fun z => (η z) ^ 2 *
            Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weakPartial j) z +
            2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.uChart z) y) =
      fun y =>
      (weightedInvGramOnEuclid (I := I) g α i j y * D.weakPartial i y) *
      Sobolev.diffQuot
        (d := Module.finrank ℝ E) k (-h)
        (testFactor (I := I) (M := M) D η k h j) y := by
    funext y
    rfl
  rw [h_assoc]
  exact h_int_prod

omit [NeZero (Module.finrank ℝ E)] in
theorem chartBilinear_factor_integrable_after
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (hη_support_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {h : ℝ} (hh : h ≠ 0)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    (i j : Fin (Module.finrank ℝ E)) :
    Integrable (fun y =>
      Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
          D.weakPartial i z) y *
      ((η y) ^ 2 *
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (D.weakPartial j) y +
        2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
          Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.uChart y))
      ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)) := by
  classical
  have hF_ext_lp : MemLp (F_ij_extended (I := I) (M := M) D (h := h) K_0 i j) 2
      (volume : Measure EuclN) :=
    F_ij_extended_memLp (I := I) (M := M) D hK_0_compact h_thick i j
  have h_dq_F_ext_lp : MemLp
      (Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (F_ij_extended (I := I) (M := M) D (h := h) K_0 i j)) 2
      (volume : Measure EuclN) :=
    memLp_diffQuot_of_memLp hF_ext_lp k hh
  have h_test_lp : MemLp (testFactor (I := I) (M := M) D η k h j) 2
      (volume : Measure EuclN) :=
    testFactor_memLp_two (I := I) (M := M) D hK_0_compact hη hη_support
      hη_support_in_K_0 k hh h_thick j
  have h_int_prod_global : Integrable (fun y =>
      Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (F_ij_extended (I := I) (M := M) D (h := h) K_0 i j) y *
      testFactor (I := I) (M := M) D η k h j y)
      (volume : Measure EuclN) :=
    Sobolev.integrable_mul_of_memLp_two
      (d := Module.finrank ℝ E) h_dq_F_ext_lp h_test_lp
  have h_int_prod_restrict : Integrable (fun y =>
      Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (F_ij_extended (I := I) (M := M) D (h := h) K_0 i j) y *
      testFactor (I := I) (M := M) D η k h j y)
      ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)) :=
    h_int_prod_global.restrict
  have h_pointwise_eq :
      ∀ᵐ y ∂((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)),
      Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (F_ij_extended (I := I) (M := M) D (h := h) K_0 i j) y *
      testFactor (I := I) (M := M) D η k h j y =
      Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
          D.weakPartial i z) y *
      ((η y) ^ 2 *
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (D.weakPartial j) y +
        2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
          Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.uChart y) := by
    refine Filter.Eventually.of_forall ?_
    intro y
    have h_test_eq : testFactor (I := I) (M := M) D η k h j y =
        (η y) ^ 2 *
          Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (D.weakPartial j) y +
          2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
            Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h D.uChart y := rfl
    by_cases hy : y ∈ tsupport η
    · have h_K_0_thick : K_0 ⊆ Metric.cthickening |h| K_0 :=
        Metric.self_subset_cthickening _
      have hy_K_0 : y ∈ K_0 := hη_support_in_K_0 hy
      have hy_thick : y ∈ Metric.cthickening |h| K_0 := h_K_0_thick hy_K_0
      have hy_shift : y + h • EuclideanSpace.single k 1 ∈ Metric.cthickening |h| K_0 := by
        refine Metric.mem_cthickening_of_dist_le _ _ |h| K_0 hy_K_0 ?_
        rw [dist_eq_norm]
        have hcalc : (y + h • EuclideanSpace.single k 1) - y =
            h • EuclideanSpace.single k 1 := by
          rw [add_sub_cancel_left]
        rw [hcalc, norm_smul]
        simp [Real.norm_eq_abs]
      have h_F_ext_eq : Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          (F_ij_extended (I := I) (M := M) D (h := h) K_0 i j) y =
          Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h
            (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
              D.weakPartial i z) y := by
        unfold F_ij_extended
        rw [Sobolev.diffQuot_apply_of_ne
              (d := Module.finrank ℝ E) k hh,
            Sobolev.diffQuot_apply_of_ne
              (d := Module.finrank ℝ E) k hh]
        congr 1
        congr 1
        · rw [Set.indicator_of_mem hy_shift]
        · rw [Set.indicator_of_mem hy_thick]
      rw [h_F_ext_eq, h_test_eq]
    · have h_test_zero : testFactor (I := I) (M := M) D η k h j y = 0 :=
        testFactor_eq_zero_outside_tsupport (I := I) (M := M) D k h j hy
      rw [h_test_zero]
      have hηy : η y = 0 := image_eq_zero_of_notMem_tsupport hy
      have h_rhs_test : (η y) ^ 2 *
          Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (D.weakPartial j) y +
            2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.uChart y = 0 := by
        rw [show (η y)^2 = 0 from by rw [hηy]; ring, zero_mul]
        rw [show 2 * η y = 0 from by rw [hηy]; ring]
        ring
      rw [h_rhs_test, mul_zero, mul_zero]
  exact h_int_prod_restrict.congr h_pointwise_eq

omit [NeZero (Module.finrank ℝ E)] in
private lemma diffQuot_testFactor_support_subset
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN}
    {η : EuclN → ℝ} (hη_support_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {h : ℝ}
    (j : Fin (Module.finrank ℝ E)) :
    Function.support (Sobolev.diffQuot
      (d := Module.finrank ℝ E) k (-h)
      (testFactor (I := I) (M := M) D η k h j)) ⊆
        Metric.cthickening |h| K_0 := by
  intro y hy
  rw [Function.mem_support] at hy
  by_cases hh_eq : h = 0
  · subst hh_eq
    have : Sobolev.diffQuot
        (d := Module.finrank ℝ E) k (-(0:ℝ))
        (testFactor (I := I) (M := M) D η k (0:ℝ) j) y = 0 := by
      simp [Sobolev.diffQuot]
    exact absurd this hy
  · rw [Sobolev.diffQuot_apply_of_ne
        (d := Module.finrank ℝ E) k (neg_ne_zero.mpr hh_eq)] at hy
    have h_num_ne : testFactor (I := I) (M := M) D η k h j
        (y + (-h) • EuclideanSpace.single k 1) -
        testFactor (I := I) (M := M) D η k h j y ≠ 0 := by
      intro hnum
      apply hy
      rw [hnum, zero_div]
    have h_or :
        testFactor (I := I) (M := M) D η k h j
          (y + (-h) • EuclideanSpace.single k 1) ≠ 0 ∨
        testFactor (I := I) (M := M) D η k h j y ≠ 0 := by
      by_contra h_neither
      have h1 : testFactor (I := I) (M := M) D η k h j
          (y + (-h) • EuclideanSpace.single k 1) = 0 := by
        by_contra hne
        exact h_neither (Or.inl hne)
      have h2 : testFactor (I := I) (M := M) D η k h j y = 0 := by
        by_contra hne
        exact h_neither (Or.inr hne)
      apply h_num_ne
      rw [h1, h2, sub_self]
    rcases h_or with h_shift | h_at
    · have h_in_support : y + (-h) • EuclideanSpace.single k 1 ∈ tsupport η := by
        by_contra hnot
        exact h_shift
          (testFactor_eq_zero_outside_tsupport (I := I) (M := M) D k h j hnot)
      have h_in_K_0 : y + (-h) • EuclideanSpace.single k 1 ∈ K_0 :=
        hη_support_in_K_0 h_in_support
      refine Metric.mem_cthickening_of_dist_le _ _ |h| K_0 h_in_K_0 ?_
      rw [dist_eq_norm]
      have hcalc : y - (y + (-h) • EuclideanSpace.single k 1) =
          h • EuclideanSpace.single k 1 := by
        rw [sub_add_eq_sub_sub, sub_self, zero_sub, ← neg_smul, neg_neg]
      rw [hcalc, norm_smul]
      simp [Real.norm_eq_abs]
    · have h_in_support : y ∈ tsupport η := by
        by_contra hnot
        exact h_at (testFactor_eq_zero_outside_tsupport (I := I) (M := M) D k h j hnot)
      exact Metric.self_subset_cthickening _ (hη_support_in_K_0 h_in_support)

omit [NeZero (Module.finrank ℝ E)] in
private lemma diffQuot_testFactor_eq_zero_outside_cthickening
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN}
    {η : EuclN → ℝ} (hη_support_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {h : ℝ}
    (j : Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∉ Metric.cthickening |h| K_0) :
    Sobolev.diffQuot
      (d := Module.finrank ℝ E) k (-h)
      (testFactor (I := I) (M := M) D η k h j) y = 0 := by
  by_contra hne
  exact hy (diffQuot_testFactor_support_subset (I := I) (M := M) D
    hη_support_in_K_0 k j hne)

omit [NeZero (Module.finrank ℝ E)] in
theorem chartBilinear_diffQuot_ibp_per_ij
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (hη_support_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {h : ℝ} (hh : h ≠ 0)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    (i j : Fin (Module.finrank ℝ E)) :
    ∫ y in Metric.cthickening |h| K_0,
      weightedInvGramOnEuclid (I := I) g α i j y *
        D.weakPartial i y *
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k (-h)
          (fun z => (η z) ^ 2 *
            Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weakPartial j) z +
            2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.uChart z) y
      ∂(volume : Measure EuclN) =
    - ∫ y in Metric.cthickening |h| K_0,
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
            D.weakPartial i z) y *
        ((η y) ^ 2 *
          Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (D.weakPartial j) y +
          2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
            Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h D.uChart y)
      ∂(volume : Measure EuclN) := by
  classical
  have h_thick_compact : IsCompact (Metric.cthickening |h| K_0) :=
    cthickening_K_0_isCompact (E := E) hK_0_compact
  have h_thick_meas : MeasurableSet (Metric.cthickening |h| K_0) :=
    h_thick_compact.measurableSet
  have hF_ext_lp : MemLp (F_ij_extended (I := I) (M := M) D (h := h) K_0 i j) 2
      (volume : Measure EuclN) :=
    F_ij_extended_memLp (I := I) (M := M) D hK_0_compact h_thick i j
  have h_test_lp : MemLp (testFactor (I := I) (M := M) D η k h j) 2
      (volume : Measure EuclN) :=
    testFactor_memLp_two (I := I) (M := M) D hK_0_compact hη hη_support
      hη_support_in_K_0 k hh h_thick j
  have h_global_ibp :
      ∫ y, Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (F_ij_extended (I := I) (M := M) D (h := h) K_0 i j) y *
      testFactor (I := I) (M := M) D η k h j y ∂(volume : Measure EuclN) =
      - ∫ y, F_ij_extended (I := I) (M := M) D (h := h) K_0 i j y *
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k (-h)
          (testFactor (I := I) (M := M) D η k h j) y ∂(volume : Measure EuclN) :=
    Sobolev.integral_diffQuot_mul_eq_neg_integral_mul_diffQuot
      (d := Module.finrank ℝ E) k hh hF_ext_lp h_test_lp
  have h_lhs_eq :
      ∫ y, Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h
        (F_ij_extended (I := I) (M := M) D (h := h) K_0 i j) y *
      testFactor (I := I) (M := M) D η k h j y ∂(volume : Measure EuclN) =
      ∫ y in Metric.cthickening |h| K_0,
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
            D.weakPartial i z) y *
        ((η y) ^ 2 *
          Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (D.weakPartial j) y +
          2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
            Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h D.uChart y)
      ∂(volume : Measure EuclN) := by
    have h_global_to_restricted :
        ∫ y, Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          (F_ij_extended (I := I) (M := M) D (h := h) K_0 i j) y *
        testFactor (I := I) (M := M) D η k h j y ∂(volume : Measure EuclN) =
        ∫ y in Metric.cthickening |h| K_0,
          Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h
            (F_ij_extended (I := I) (M := M) D (h := h) K_0 i j) y *
          testFactor (I := I) (M := M) D η k h j y
        ∂(volume : Measure EuclN) := by
      symm
      refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
      intro y hy_compl
      have hy_not_K_0 : y ∉ K_0 := fun h_in =>
        hy_compl (Metric.self_subset_cthickening _ h_in)
      have hy_not_tsupp : y ∉ tsupport η := fun h_in =>
        hy_not_K_0 (hη_support_in_K_0 h_in)
      have h_test_zero : testFactor (I := I) (M := M) D η k h j y = 0 :=
        testFactor_eq_zero_outside_tsupport (I := I) (M := M) D k h j hy_not_tsupp
      rw [h_test_zero, mul_zero]
    rw [h_global_to_restricted]
    refine integral_congr_ae ?_
    refine (ae_restrict_iff' h_thick_meas).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy
    by_cases hy_tsupp : y ∈ tsupport η
    · have hy_K_0 : y ∈ K_0 := hη_support_in_K_0 hy_tsupp
      have hy_thick : y ∈ Metric.cthickening |h| K_0 :=
        Metric.self_subset_cthickening _ hy_K_0
      have hy_shift : y + h • EuclideanSpace.single k 1 ∈ Metric.cthickening |h| K_0 := by
        refine Metric.mem_cthickening_of_dist_le _ _ |h| K_0 hy_K_0 ?_
        rw [dist_eq_norm]
        have hcalc : (y + h • EuclideanSpace.single k 1) - y =
            h • EuclideanSpace.single k 1 := by
          rw [add_sub_cancel_left]
        rw [hcalc, norm_smul]
        simp [Real.norm_eq_abs]
      have h_F_ext_eq : Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          (F_ij_extended (I := I) (M := M) D (h := h) K_0 i j) y =
          Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h
            (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
              D.weakPartial i z) y := by
        unfold F_ij_extended
        rw [Sobolev.diffQuot_apply_of_ne
              (d := Module.finrank ℝ E) k hh,
            Sobolev.diffQuot_apply_of_ne
              (d := Module.finrank ℝ E) k hh]
        congr 1
        congr 1
        · rw [Set.indicator_of_mem hy_shift]
        · rw [Set.indicator_of_mem hy_thick]
      change Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          (F_ij_extended (I := I) (M := M) D (h := h) K_0 i j) y *
        ((η y) ^ 2 *
          Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (D.weakPartial j) y +
          2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
            Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h D.uChart y) =
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
            D.weakPartial i z) y *
        ((η y) ^ 2 *
          Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (D.weakPartial j) y +
          2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
            Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h D.uChart y)
      rw [h_F_ext_eq]
    · have hηy : η y = 0 := image_eq_zero_of_notMem_tsupport hy_tsupp
      have h_test_explicit_zero : (η y) ^ 2 *
            Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weakPartial j) y +
            2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.uChart y = 0 := by
        rw [show (η y)^2 = 0 from by rw [hηy]; ring, zero_mul]
        rw [show 2 * η y = 0 from by rw [hηy]; ring]
        ring
      change Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          (F_ij_extended (I := I) (M := M) D (h := h) K_0 i j) y *
        ((η y) ^ 2 *
          Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (D.weakPartial j) y +
          2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
            Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h D.uChart y) =
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
            D.weakPartial i z) y *
        ((η y) ^ 2 *
          Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (D.weakPartial j) y +
          2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
            Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h D.uChart y)
      rw [h_test_explicit_zero, mul_zero, mul_zero]
  have h_rhs_eq :
      ∫ y, F_ij_extended (I := I) (M := M) D (h := h) K_0 i j y *
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k (-h)
          (testFactor (I := I) (M := M) D η k h j) y ∂(volume : Measure EuclN) =
      ∫ y in Metric.cthickening |h| K_0,
        weightedInvGramOnEuclid (I := I) g α i j y *
          D.weakPartial i y *
          Sobolev.diffQuot
            (d := Module.finrank ℝ E) k (-h)
            (fun z => (η z) ^ 2 *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weakPartial j) z +
              2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h D.uChart z) y
      ∂(volume : Measure EuclN) := by
    have h_global_to_restricted :
        ∫ y, F_ij_extended (I := I) (M := M) D (h := h) K_0 i j y *
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k (-h)
          (testFactor (I := I) (M := M) D η k h j) y ∂(volume : Measure EuclN) =
        ∫ y in Metric.cthickening |h| K_0,
          F_ij_extended (I := I) (M := M) D (h := h) K_0 i j y *
          Sobolev.diffQuot
            (d := Module.finrank ℝ E) k (-h)
            (testFactor (I := I) (M := M) D η k h j) y
        ∂(volume : Measure EuclN) := by
      symm
      refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
      intro y hy_compl
      unfold F_ij_extended
      rw [Set.indicator_of_notMem hy_compl, zero_mul]
    rw [h_global_to_restricted]
    refine integral_congr_ae ?_
    refine (ae_restrict_iff' h_thick_meas).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy_thick
    change F_ij_extended (I := I) (M := M) D (h := h) K_0 i j y *
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k (-h)
          (fun z => (η z) ^ 2 *
            Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weakPartial j) z +
            2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.uChart z) y =
      weightedInvGramOnEuclid (I := I) g α i j y * D.weakPartial i y *
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k (-h)
          (fun z => (η z) ^ 2 *
            Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weakPartial j) z +
            2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.uChart z) y
    unfold F_ij_extended
    rw [Set.indicator_of_mem hy_thick]
  rw [← h_rhs_eq, ← h_lhs_eq]
  linarith

omit [NeZero (Module.finrank ℝ E)] in
theorem variational_identity_after_ibp_of_compact_support
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (hη_support_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {h : ℝ} (hh : h ≠ 0)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    (h_expanded :
      (∫ y in Metric.cthickening |h| K_0,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weakPartial i y *
                Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k (-h)
                  (fun z => (η z) ^ 2 *
                    Sobolev.diffQuot
                      (d := Module.finrank ℝ E) k h (D.weakPartial j) z +
                    2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                      Sobolev.diffQuot
                        (d := Module.finrank ℝ E) k h D.uChart z) y)
          ∂(volume : Measure EuclN)) +
        (∫ y in Metric.cthickening |h| K_0,
          densityOnEuclid (I := I) g α y * D.uChart y *
            nirenbergTestFunction (d := Module.finrank ℝ E) k h η
              D.uChart y
          ∂(volume : Measure EuclN)) =
        ∫ y in Metric.cthickening |h| K_0,
          densityOnEuclid (I := I) g α y * D.fChart y *
            nirenbergTestFunction (d := Module.finrank ℝ E) k h η
              D.uChart y
          ∂(volume : Measure EuclN)) :
    -(∫ y in Metric.cthickening |h| K_0,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h
              (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
                D.weakPartial i z) y *
            ((η y) ^ 2 *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weakPartial j) y +
              2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
                Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h D.uChart y))
        ∂(volume : Measure EuclN)) +
      (∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.uChart y *
          nirenbergTestFunction (d := Module.finrank ℝ E) k h η D.uChart y
        ∂(volume : Measure EuclN)) =
      ∫ y in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α y * D.fChart y *
          nirenbergTestFunction (d := Module.finrank ℝ E) k h η D.uChart y
        ∂(volume : Measure EuclN) := by
  have h_ibp_per_ij : ∀ i j : Fin (Module.finrank ℝ E),
      ∫ y in Metric.cthickening |h| K_0,
        weightedInvGramOnEuclid (I := I) g α i j y *
          D.weakPartial i y *
          Sobolev.diffQuot
            (d := Module.finrank ℝ E) k (-h)
            (fun z => (η z) ^ 2 *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weakPartial j) z +
              2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h D.uChart z) y
        ∂(volume : Measure EuclN) =
      - ∫ y in Metric.cthickening |h| K_0,
          Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h
            (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
              D.weakPartial i z) y *
          ((η y) ^ 2 *
            Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weakPartial j) y +
            2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.uChart y)
        ∂(volume : Measure EuclN) := by
    intro i j
    exact chartBilinear_diffQuot_ibp_per_ij (I := I) (M := M) D
      hK_0_compact hη hη_support hη_support_in_K_0 k hh h_thick i j
  have h_principal_integrable : ∀ i j : Fin (Module.finrank ℝ E),
      Integrable (fun y =>
        weightedInvGramOnEuclid (I := I) g α i j y *
          D.weakPartial i y *
          Sobolev.diffQuot
            (d := Module.finrank ℝ E) k (-h)
            (fun z => (η z) ^ 2 *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weakPartial j) z +
              2 * η z * (fderiv ℝ η z) (EuclideanSpace.single j 1) *
                Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h D.uChart z) y)
        ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)) := by
    intro i j
    exact chartBilinear_factor_integrable (I := I) (M := M) D
      hK_0_compact hη hη_support hη_support_in_K_0 k hh h_thick i j
  have h_principal_integrable_after : ∀ i j : Fin (Module.finrank ℝ E),
      Integrable (fun y =>
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          (fun z => weightedInvGramOnEuclid (I := I) g α i j z *
            D.weakPartial i z) y *
        ((η y) ^ 2 *
          Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (D.weakPartial j) y +
          2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
            Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h D.uChart y))
        ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)) := by
    intro i j
    exact chartBilinear_factor_integrable_after (I := I) (M := M) D
      hK_0_compact hη hη_support hη_support_in_K_0 k hh h_thick i j
  exact variational_identity_after_ibp (I := I) (M := M) D
    k h_expanded h_ibp_per_ij h_principal_integrable h_principal_integrable_after

end SubstitutionDischargeIBP
end Sobolev
end Analysis
end CalabiYau
