-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/ChartBilinear/UniformDiffQuotBoundFromDomain/WeakPartialDerivativeBound.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Calculus.Cutoff.Compact
public import CalabiYau.Analysis.Elliptic.MetricExtension.DensityBounds
public import CalabiYau.Analysis.Elliptic.Regularity.ChartBilinear.UniformDiffQuotBoundFromDomain.DataBounds
public import CalabiYau.Analysis.Sobolev.Nirenberg.H2Regularity.UniformDifferenceQuotient
public import CalabiYau.Analysis.Sobolev.Nirenberg.SubstitutionIdentity.ChartBilinearVariationalIdentity
public import CalabiYau.Analysis.Sobolev.Nirenberg.SubstitutionIdentity.SubstitutionNonSmooth
public import CalabiYau.Analysis.Elliptic.Regularity.ChartBilinear.UniformDiffQuotBoundFromDomain.Coercivity
public import CalabiYau.Analysis.Elliptic.Regularity.ChartBilinear.UniformDiffQuotBoundFromDomain.Cutoff
public import CalabiYau.Analysis.Elliptic.Regularity.ChartBilinear.UniformDiffQuotBoundFromDomain.SolutionDifferenceQuotient
public import CalabiYau.Analysis.Elliptic.Regularity.ChartBilinear.UniformDiffQuotBoundFromDomain.TestFunction

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
open CalabiYau.DivergenceTheorem
open CalabiYau.Laplacian.MetricExtension
open CalabiYau.Analysis.Laplacian.ChartLocalLaplacian
open CalabiYau.Laplacian.ChartMeasureEquiv
open _root_.Sobolev
open Sobolev.NirenbergEuclidean
open Sobolev.NirenbergTestFunction
open Sobolev.SubstitutionDischargeSmoothApprox
open Sobolev.SubstitutionDischargeAssembly
open Sobolev.SubstitutionNonSmoothChartBilinear
open Sobolev.NirenbergSubstitutionNonSmooth
open Sobolev.NirenbergCrossBoundsNonSmooth

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private def extendedDensity
    (g : SmoothRiemannianMetric I M) (α : M) (χ : EuclN → ℝ) (y : EuclN) : ℝ :=
  χ y * densityOnEuclid (I := I) g α y + (1 - χ y) * 1

omit [NeZero (Module.finrank ℝ E)] in
private lemma extendedDensity_contDiff
    (g : SmoothRiemannianMetric I M) (α : M) [I.Boundaryless]
    {χ : EuclN → ℝ} (hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχ_support : tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ContDiff ℝ (⊤ : ℕ∞) (extendedDensity (I := I) g α χ) := by
  set f : EuclN → ℝ := extendedDensity (I := I) g α χ with hf_def
  set s : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hs_def
  set t : Set EuclN := (tsupport χ)ᶜ with ht_def
  have hs_open : IsOpen s := chartTargetEuclid_isOpen (I := I) (M := M) α
  have ht_open : IsOpen t := isClosed_tsupport _ |>.isOpen_compl
  have hcov : s ∪ t = Set.univ := by
    refine Set.eq_univ_of_forall ?_
    intro y
    by_cases hy : y ∈ tsupport χ
    · exact Or.inl (hχ_support hy)
    · exact Or.inr hy
  have hf_on_s : ContDiffOn ℝ (⊤ : ℕ∞) f s := by
    change ContDiffOn ℝ (⊤ : ℕ∞) (fun y =>
      χ y * densityOnEuclid (I := I) g α y + (1 - χ y) * 1) s
    refine ContDiffOn.add ?_ ?_
    · exact hχ_smooth.contDiffOn.mul (densityOnEuclid_contDiffOn (I := I) g α)
    · exact (contDiffOn_const.sub hχ_smooth.contDiffOn).mul contDiffOn_const
  have hf_on_t : ContDiffOn ℝ (⊤ : ℕ∞) f t := by
    have hf_eq_const : ∀ y ∈ t, f y = 1 := by
      intro y hy
      have hχ_zero : χ y = 0 := image_eq_zero_of_notMem_tsupport hy
      change extendedDensity (I := I) g α χ y = 1
      unfold extendedDensity
      rw [hχ_zero]; ring
    exact contDiffOn_const.congr (fun y hy => hf_eq_const y hy)
  exact contDiff_of_contDiffOn_union_of_isOpen hf_on_s hf_on_t hcov hs_open ht_open

omit [NeZero (Module.finrank ℝ E)] in
private lemma extendedDensity_eq_density_of_chi_one
    (g : SmoothRiemannianMetric I M) (α : M) {χ : EuclN → ℝ} {y : EuclN}
    (hχ_one : χ y = 1) :
    extendedDensity (I := I) g α χ y = densityOnEuclid (I := I) g α y := by
  unfold extendedDensity
  rw [hχ_one]; ring

private theorem exists_smooth_metric_extension_with_density
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN}
    (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ B : SmoothEllipticBilinearForm (Module.finrank ℝ E) (Set.univ : Set EuclN),
      (∀ y ∈ K, ∀ i j : Fin (Module.finrank ℝ E),
        B.a y i j = weightedInvGramOnEuclid (I := I) g α i j y) ∧
      (∀ y ∈ K, B.c y = densityOnEuclid (I := I) g α y) := by
  classical
  have hO : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  obtain ⟨δ, δ_pos, hδ_subset⟩ := hK.exists_cthickening_subset_open hO hK_target
  set Ω' : Set EuclN := Metric.thickening δ K with hΩ'_def
  set K' : Set EuclN := Metric.cthickening δ K with hK'_def
  have hΩ'_open : IsOpen Ω' := Metric.isOpen_thickening
  have hK'_compact : IsCompact K' := hK.cthickening (r := δ)
  have h_K_in_Ω' : K ⊆ Ω' := Metric.self_subset_thickening δ_pos K
  have h_Ω'_in_K' : Ω' ⊆ K' := Metric.thickening_subset_cthickening δ K
  have h_K'_in_chart : K' ⊆ chartTargetEuclid (I := I) (M := M) α := hδ_subset
  obtain ⟨χ, hχ_smooth, hχ_support, hχ_one_nhds, hχ_tsupp, hχ_range⟩ :=
    CalabiYau.exists_bump_compact
      (K := K) (U := Ω') hK hΩ'_open h_K_in_Ω'
  have hχ_one : ∀ x ∈ K, χ x = 1 := fun _ hx =>
    hχ_one_nhds.self_of_nhdsSet hx
  have hχ_tsupp_chart : tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α := by
    intro y hy
    have h1 : y ∈ Ω' := hχ_tsupp hy
    exact (h_Ω'_in_K'.trans h_K'_in_chart) h1
  have hχ_tsupp_compact : IsCompact (tsupport χ) := hχ_support
  obtain ⟨lamK0, hlamK0_pos, hlamK0_bound⟩ :=
    exists_uniform_lower_bound_on_compact (I := I) g α hχ_tsupp_compact hχ_tsupp_chart
  set lamK : ℝ := min 1 lamK0 with hlamK_def
  have hlamK_pos : 0 < lamK := lt_min one_pos hlamK0_pos
  have hlamK_le_one : lamK ≤ 1 := min_le_left _ _
  have hlamK_le_lamK0 : lamK ≤ lamK0 := min_le_right _ _
  have hlamK0_bound_for_lamK : ∀ y ∈ tsupport χ, ∀ ξ : EuclN,
      lamK * ‖ξ‖ ^ 2 ≤
        ⟪ξ, DeGiorgi.matMulE
          (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
            weightedInvGramOnEuclid (I := I) g α i j y)) ξ⟫_ℝ := by
    intro y hy ξ
    have h0 := hlamK0_bound y hy ξ
    have h_norm_sq_nn : 0 ≤ ‖ξ‖ ^ 2 := sq_nonneg _
    have h_le : lamK * ‖ξ‖ ^ 2 ≤ lamK0 * ‖ξ‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hlamK_le_lamK0 h_norm_sq_nn
    linarith
  let aFun : EuclN → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun y => Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
      extendedMatrix (I := I) g α χ i j y)
  have h_a_smooth : ∀ i j : Fin (Module.finrank ℝ E),
      ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclN => aFun y i j) := by
    intro i j
    change ContDiff ℝ (⊤ : ℕ∞) (extendedMatrix (I := I) g α χ i j)
    exact extendedMatrix_contDiff (I := I) g α
      (χ := χ) hχ_smooth hχ_tsupp_chart i j
  have h_a_symm : ∀ y i j, aFun y i j = aFun y j i := by
    intro y i j
    change extendedMatrix (I := I) g α χ i j y =
      extendedMatrix (I := I) g α χ j i y
    exact extendedMatrix_symm (I := I) g α
      (χ := χ) hχ_tsupp_chart i j y
  have h_a_coercive : ∀ y ∈ (Set.univ : Set EuclN), ∀ ξ : EuclN,
      lamK * ‖ξ‖ ^ 2 ≤ ⟪ξ, DeGiorgi.matMulE (aFun y) ξ⟫_ℝ := by
    intro y _ ξ
    change lamK * ‖ξ‖ ^ 2 ≤
      ⟪ξ, DeGiorgi.matMulE
        (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
          extendedMatrix (I := I) g α χ i j y)) ξ⟫_ℝ
    exact extendedMatrix_coercive (I := I) g α
      (χ := χ) hχ_range hχ_tsupp_chart hlamK_le_one
      hlamK0_bound_for_lamK y ξ
  let cFun : EuclN → ℝ := extendedDensity (I := I) g α χ
  have h_c_smooth : ContDiff ℝ (⊤ : ℕ∞) cFun :=
    extendedDensity_contDiff (I := I) g α hχ_smooth hχ_tsupp_chart
  let B : SmoothEllipticBilinearForm (Module.finrank ℝ E) (Set.univ : Set EuclN) :=
    { a := aFun
      c := cFun
      symm := h_a_symm
      smooth_a := h_a_smooth
      smooth_c := h_c_smooth
      lam := lamK
      capLam := max lamK 1
      ellipticity_pos := hlamK_pos
      ellipticity_le_upper := le_max_left _ _
      coercive := h_a_coercive }
  have h_agree_a : ∀ y ∈ K, ∀ i j : Fin (Module.finrank ℝ E),
      B.a y i j = weightedInvGramOnEuclid (I := I) g α i j y := by
    intro y hy i j
    change extendedMatrix (I := I) g α χ i j y =
      weightedInvGramOnEuclid (I := I) g α i j y
    have hχ_y : χ y = 1 := hχ_one y hy
    unfold extendedMatrix
    rw [hχ_y]; ring
  have h_agree_c : ∀ y ∈ K, B.c y = densityOnEuclid (I := I) g α y := by
    intro y hy
    change extendedDensity (I := I) g α χ y = densityOnEuclid (I := I) g α y
    exact extendedDensity_eq_density_of_chi_one (I := I) g α (hχ_one y hy)
  exact ⟨B, h_agree_a, h_agree_c⟩

theorem uniform_diffQuot_weakPartial_bound_quantitative
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_support : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (hN : 0 ≤ N) (h_fderiv_eta : ∀ x : EuclN, ‖fderiv ℝ η x‖ ≤ N)
    {Ω' Ω'' : Set EuclN} (hΩ' : IsOpen Ω')
    (hΩ'_chart : closure Ω' ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hΩ'_compact : IsCompact (closure Ω'))
    (hη_in_Ω' : tsupport η ⊆ Ω')
    {R₀ : ℝ} (hR₀_pos : 0 < R₀)
    (hh_support_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (hη_one_on_Ω'' : ∀ x ∈ Ω'', η x = 1)
    (hΩ''_meas : MeasurableSet Ω'') :
    ∃ C_geom : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ,
      (∀ i k, 0 ≤ C_geom i k) ∧
      ∀ (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
        ⦃i k : Fin (Module.finrank ℝ E)⦄ ⦃h : ℝ⦄,
        0 < |h| → |h| ≤ R₀ →
          eLpNorm
            (Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weakPartial i)) 2
            ((volume : Measure EuclN).restrict Ω'')
          ≤ ENNReal.ofReal (C_geom i k * Real.sqrt (
              (∑ l : Fin (Module.finrank ℝ E),
                (eLpNorm (D.weakPartial l) 2
                  ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2)
              + (eLpNorm D.uChart 2
                  ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2
              + (eLpNorm D.fChart 2
                  ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2)) := by
  classical
  have hη_tsupp_compact : IsCompact (tsupport η) := hη_support
  have h_cthickR0_compact : IsCompact (Metric.cthickening R₀ (tsupport η)) :=
    hη_tsupp_compact.cthickening
  have h_cthickR0_in_Ω' : Metric.cthickening R₀ (tsupport η) ⊆ Ω' := by
    have h := hh_support_in_Ω' (h := R₀) (by rw [abs_of_pos hR₀_pos])
    rw [abs_of_pos hR₀_pos] at h
    exact h
  have h_cthickR0_in_chart :
      Metric.cthickening R₀ (tsupport η) ⊆
        chartTargetEuclid (I := I) (M := M) α :=
    h_cthickR0_in_Ω'.trans (subset_closure.trans hΩ'_chart)
  obtain ⟨B, hB_a_match, hB_c_match⟩ :=
    exists_smooth_metric_extension_with_density (I := I) (M := M) g α
      h_cthickR0_compact h_cthickR0_in_chart
  have h_chart_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  obtain ⟨δ, hδ_pos, hδ_in_chart⟩ :=
    hΩ'_compact.exists_cthickening_subset_open h_chart_open hΩ'_chart
  set K_χ : Set EuclN := Metric.cthickening (δ / 2) (closure Ω') with hK_χ_def
  have hδ_half_pos : 0 < δ / 2 := by linarith
  have hδ_half_lt_δ : δ / 2 < δ := by linarith
  have hK_χ_compact : IsCompact K_χ := hΩ'_compact.cthickening
  have hK_χ_in_thick_δ : K_χ ⊆ Metric.thickening δ (closure Ω') := by
    intro x hx
    rw [hK_χ_def] at hx
    have h_inf : Metric.infEDist x (closure Ω') ≤ ENNReal.ofReal (δ / 2) :=
      Metric.mem_cthickening_iff.mp hx
    have h_ofReal_lt : ENNReal.ofReal (δ / 2) < ENNReal.ofReal δ :=
      ENNReal.ofReal_lt_ofReal_iff hδ_pos |>.mpr hδ_half_lt_δ
    have h_inf_lt : Metric.infEDist x (closure Ω') < ENNReal.ofReal δ :=
      lt_of_le_of_lt h_inf h_ofReal_lt
    exact Metric.mem_thickening_iff_infEDist_lt.mpr h_inf_lt
  have h_thick_δ_in_chart :
      Metric.thickening δ (closure Ω') ⊆ chartTargetEuclid (I := I) (M := M) α := by
    intro x hx
    exact hδ_in_chart (Metric.thickening_subset_cthickening _ _ hx)
  obtain ⟨χ, hχ_smooth, hχ_cs, hχ_one_nhds, hχ_tsupp, hχ_range⟩ :=
    CalabiYau.exists_bump_compact
      (K := K_χ)
      (U := Metric.thickening δ (closure Ω'))
      hK_χ_compact Metric.isOpen_thickening hK_χ_in_thick_δ
  have hχ_one : ∀ x ∈ K_χ, χ x = 1 := fun _ hx =>
    hχ_one_nhds.self_of_nhdsSet hx
  have hχ_tsupp_in_chart :
      tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α := by
    intro x hx
    exact h_thick_δ_in_chart (hχ_tsupp hx)
  have hχ_nn : ∀ x : EuclN, 0 ≤ χ x ∧ χ x ≤ 1 := by
    intro x
    have hx_range : χ x ∈ Set.range χ := Set.mem_range_self x
    exact ⟨(hχ_range hx_range).1, (hχ_range hx_range).2⟩
  have hχ_cont : Continuous χ := hχ_smooth.continuous
  obtain ⟨M_χ, hM_χ_nn, hM_χ_bd⟩ : ∃ M_χ : ℝ, 0 ≤ M_χ ∧ ∀ x, |χ x| ≤ M_χ := by
    by_cases hSupport_empty : (tsupport χ).Nonempty
    · obtain ⟨xMax, _, hxMax_max⟩ :=
        hχ_cs.exists_isMaxOn hSupport_empty hχ_cont.abs.continuousOn
      refine ⟨|χ xMax|, abs_nonneg _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport χ
      · exact hxMax_max hx
      · have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
        rw [hχx, abs_zero]; exact abs_nonneg _
    · refine ⟨0, le_refl _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport χ
      · exact absurd ⟨x, hx⟩ hSupport_empty
      · have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
        rw [hχx, abs_zero]
  have hχ_fderiv_cont : Continuous (fderiv ℝ χ) :=
    hχ_smooth.continuous_fderiv (by decide : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)
  have hχ_partial_cont : ∀ l : Fin (Module.finrank ℝ E), Continuous
      (fun x => (fderiv ℝ χ x) (EuclideanSpace.single l 1)) := fun l =>
    hχ_fderiv_cont.clm_apply continuous_const
  obtain ⟨M_dχ, hM_dχ_nn, hM_dχ_bd⟩ :
      ∃ M_dχ : ℝ, 0 ≤ M_dχ ∧ ∀ (l : Fin (Module.finrank ℝ E)) (x : EuclN),
        |(fderiv ℝ χ x) (EuclideanSpace.single l 1)| ≤ M_dχ := by
    have h_per_l : ∀ l : Fin (Module.finrank ℝ E),
        ∃ M : ℝ, 0 ≤ M ∧ ∀ x : EuclN,
          |(fderiv ℝ χ x) (EuclideanSpace.single l 1)| ≤ M := by
      intro l
      have h_cs_l : HasCompactSupport
          (fun x => (fderiv ℝ χ x) (EuclideanSpace.single l 1)) :=
        hχ_cs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single l 1)
      have h_cont_abs : Continuous
          (fun x => |(fderiv ℝ χ x) (EuclideanSpace.single l 1)|) :=
        (hχ_partial_cont l).abs
      by_cases hSupport_empty :
          (tsupport (fun x => (fderiv ℝ χ x) (EuclideanSpace.single l 1))).Nonempty
      · obtain ⟨xMax, _, hxMax_max⟩ :=
          h_cs_l.exists_isMaxOn hSupport_empty h_cont_abs.continuousOn
        refine ⟨|(fderiv ℝ χ xMax) (EuclideanSpace.single l 1)|,
          abs_nonneg _, fun x => ?_⟩
        by_cases hx : x ∈ tsupport
            (fun x => (fderiv ℝ χ x) (EuclideanSpace.single l 1))
        · exact hxMax_max hx
        · have hχx : (fderiv ℝ χ x) (EuclideanSpace.single l 1) = 0 :=
            image_eq_zero_of_notMem_tsupport
              (f := fun x => (fderiv ℝ χ x) (EuclideanSpace.single l 1)) hx
          rw [hχx, abs_zero]; exact abs_nonneg _
      · refine ⟨0, le_refl _, fun x => ?_⟩
        by_cases hx : x ∈ tsupport
            (fun x => (fderiv ℝ χ x) (EuclideanSpace.single l 1))
        · exact absurd ⟨x, hx⟩ hSupport_empty
        · have hχx : (fderiv ℝ χ x) (EuclideanSpace.single l 1) = 0 :=
            image_eq_zero_of_notMem_tsupport
              (f := fun x => (fderiv ℝ χ x) (EuclideanSpace.single l 1)) hx
          rw [hχx, abs_zero]
    choose Mfun hMfun_nn hMfun_bd using h_per_l
    set M_dχ : ℝ :=
      (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sup' Finset.univ_nonempty
        Mfun with hM_dχ_def
    have hM_dχ_nn : 0 ≤ M_dχ := by
      obtain ⟨l₀⟩ : Nonempty (Fin (Module.finrank ℝ E)) :=
        ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
      exact le_trans (hMfun_nn l₀)
        (Finset.le_sup' Mfun (Finset.mem_univ l₀))
    refine ⟨M_dχ, hM_dχ_nn, ?_⟩
    intro l x
    exact le_trans (hMfun_bd l x)
      (Finset.le_sup' Mfun (Finset.mem_univ l))
  set C_geom : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i k => Real.sqrt ((2 / B.lam) *
      nirenbergMasterYoungConstant B N hΩ'_compact k *
      (2 * ((Module.finrank ℝ E : ℝ) + 1) * (M_χ ^ 2 + M_dχ ^ 2 + 1)) *
      max 1 ((densityOnEuclidClosureSup (I := I) (M := M) g α Ω') ^ 2))
    with hC_geom_def
  refine ⟨C_geom, fun i k => Real.sqrt_nonneg _, ?_⟩
  intro D i k h hh_pos hh_le
  have h_diffQuot_u_bound :=
    integral_sq_diffQuot_uChart_le (I := I) (M := M) D hη_support
      hΩ'_chart hΩ'_compact hR₀_pos hh_support_in_Ω'
  have h_testFunction_sq_bound :=
    integral_sq_nirenbergTestFunction_le (I := I) (M := M) D hη hη_support hη_range
      hN h_fderiv_eta hΩ'_chart hR₀_pos hh_support_in_Ω'
  have h_coercivity :=
    weighted_diffQuot_weakPartial_energy_le (I := I) (M := M) D B hη hη_support
      hΩ'_chart hη_in_Ω' hR₀_pos hh_support_in_Ω'
      hB_a_match hB_c_match
  set u_g : EuclN → ℝ := fun x => χ x * D.uChart x with hu_g_def
  set g_g : Fin (Module.finrank ℝ E) → EuclN → ℝ := fun i x =>
    (fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.uChart x +
    χ x * D.weakPartial i x with hg_g_def
  set f_g : EuclN → ℝ :=
    fun x => χ x * (densityOnEuclid (I := I) g α x * D.fChart x) with hf_g_def
  have hu_g_l2 : MemLp u_g 2 (volume : Measure EuclN) :=
    cutoff_uChart_memLp_two_univ (I := I) (M := M) D hχ_smooth hχ_cs hχ_tsupp_in_chart
  have hg_g_l2 : ∀ i, MemLp (g_g i) 2 (volume : Measure EuclN) := fun i =>
    cutoff_uChart_partial_memLp_two_univ (I := I) (M := M) D
      hχ_smooth hχ_cs hχ_tsupp_in_chart i
  have hg_g_isWP : ∀ i, DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (g_g i) u_g Set.univ := fun i =>
    cutoff_uChart_hasWeakPartialDeriv_univ (I := I) (M := M) D
      hχ_smooth hχ_cs hχ_tsupp_in_chart i
  have hf_g_l2_global : MemLp f_g 2 (volume : Measure EuclN) := by
    classical
    have hχ_cont : Continuous χ := hχ_smooth.continuous
    obtain ⟨M_χ, hM_χ_nn, hM_χ_bd⟩ : ∃ M_χ : ℝ, 0 ≤ M_χ ∧ ∀ x, |χ x| ≤ M_χ := by
      by_cases hSupport_empty : (tsupport χ).Nonempty
      · obtain ⟨xMax, _, hxMax_max⟩ :=
          hχ_cs.exists_isMaxOn hSupport_empty hχ_cont.abs.continuousOn
        refine ⟨|χ xMax|, abs_nonneg _, ?_⟩
        intro x
        by_cases hx : x ∈ tsupport χ
        · exact hxMax_max hx
        · have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
          rw [hχx, abs_zero]; exact abs_nonneg _
      · refine ⟨0, le_refl _, ?_⟩
        intro x
        by_cases hx : x ∈ tsupport χ
        · exact absurd ⟨x, hx⟩ hSupport_empty
        · have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
          rw [hχx, abs_zero]
    have h_support_compact : IsCompact (tsupport χ) := hχ_cs
    have h_support_meas : MeasurableSet (tsupport χ) :=
      (isClosed_tsupport χ).measurableSet
    have h_density_contOn : ContinuousOn (densityOnEuclid (I := I) g α)
        (tsupport χ) :=
      ((densityOnEuclid_contDiffOn (I := I) g α).continuousOn).mono
        hχ_tsupp_in_chart
    obtain ⟨M_d, hM_d_nn, hM_d_bd⟩ :
        ∃ M_d : ℝ, 0 ≤ M_d ∧ ∀ x ∈ tsupport χ,
          |densityOnEuclid (I := I) g α x| ≤ M_d := by
      by_cases hSupport_empty : (tsupport χ).Nonempty
      · obtain ⟨xMax, _, hxMax_max⟩ :=
          h_support_compact.exists_isMaxOn hSupport_empty h_density_contOn.abs
        refine ⟨|densityOnEuclid (I := I) g α xMax|, abs_nonneg _, ?_⟩
        intro x hx; exact hxMax_max hx
      · refine ⟨0, le_refl _, ?_⟩
        intro x hx; exact absurd ⟨x, hx⟩ hSupport_empty
    have hf_l2_support : MemLp D.fChart 2
        ((volume : Measure EuclN).restrict (tsupport χ)) :=
      memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure (I := I) (M := M)
        D.f_chart_memLp_weighted h_support_compact h_support_meas hχ_tsupp_in_chart
    have h_f_aesm : AEStronglyMeasurable D.fChart
        ((volume : Measure EuclN).restrict (tsupport χ)) :=
      hf_l2_support.aestronglyMeasurable
    have h_density_aesm_support : AEStronglyMeasurable
        (densityOnEuclid (I := I) g α)
        ((volume : Measure EuclN).restrict (tsupport χ)) :=
      h_density_contOn.aestronglyMeasurable h_support_meas
    have h_prod_aesm : AEStronglyMeasurable f_g
        ((volume : Measure EuclN).restrict (tsupport χ)) := by
      refine (hχ_cont.aestronglyMeasurable.restrict).mul ?_
      exact h_density_aesm_support.mul h_f_aesm
    have h_pt_le : ∀ᵐ x ∂((volume : Measure EuclN).restrict (tsupport χ)),
        ‖f_g x‖ ≤ ‖(M_χ * M_d) * D.fChart x‖ := by
      refine ae_restrict_of_forall_mem h_support_meas ?_
      intro x hx
      change ‖χ x * (densityOnEuclid (I := I) g α x * D.fChart x)‖ ≤ _
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
      rw [show |M_χ * M_d| = M_χ * M_d from abs_of_nonneg (mul_nonneg hM_χ_nn hM_d_nn)]
      have h1 : |χ x| ≤ M_χ := hM_χ_bd x
      have h2 : |densityOnEuclid (I := I) g α x| ≤ M_d := hM_d_bd x hx
      have h3 : 0 ≤ |D.fChart x| := abs_nonneg _
      nlinarith [abs_nonneg (χ x), abs_nonneg (densityOnEuclid (I := I) g α x),
        mul_le_mul h1 h2 (abs_nonneg _) hM_χ_nn]
    have h_const_lp : MemLp (fun x => (M_χ * M_d) * D.fChart x) 2
        ((volume : Measure EuclN).restrict (tsupport χ)) :=
      hf_l2_support.const_mul (M_χ * M_d)
    have h_restrict_lp : MemLp f_g 2
        ((volume : Measure EuclN).restrict (tsupport χ)) :=
      MemLp.mono h_const_lp h_prod_aesm h_pt_le
    have h_indicator_eq : (tsupport χ).indicator f_g = f_g := by
      funext x
      by_cases hx : x ∈ tsupport χ
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx]
        have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
        have : f_g x = χ x * (densityOnEuclid (I := I) g α x * D.fChart x) := rfl
        rw [this, hχx, zero_mul]
    have h_indicator_lp :
        MemLp ((tsupport χ).indicator f_g) 2 (volume : Measure EuclN) :=
      (MeasureTheory.memLp_indicator_iff_restrict h_support_meas).mpr h_restrict_lp
    rw [h_indicator_eq] at h_indicator_lp
    exact h_indicator_lp
  have hf_g_l2_local : ∀ {Ω'_in : Set EuclN}, IsCompact (closure Ω'_in) →
      MemLp f_g 2 ((volume : Measure EuclN).restrict Ω'_in) := fun _ =>
    hf_g_l2_global.restrict _
  have h_closure_subset_thick_half_δ :
      closure Ω' ⊆ Metric.thickening (δ / 2) (closure Ω') :=
    Metric.self_subset_thickening hδ_half_pos _
  have h_thick_half_subset_K_χ :
      Metric.thickening (δ / 2) (closure Ω') ⊆ K_χ := by
    rw [hK_χ_def]
    exact Metric.thickening_subset_cthickening _ _
  have h_closure_subset_K_χ : closure Ω' ⊆ K_χ :=
    h_closure_subset_thick_half_δ.trans h_thick_half_subset_K_χ
  have hχ_one_on_closure : ∀ x ∈ closure Ω', χ x = 1 := fun x hx =>
    hχ_one x (h_closure_subset_K_χ hx)
  have h_thick_half_open : IsOpen (Metric.thickening (δ / 2) (closure Ω')) :=
    Metric.isOpen_thickening
  have h_fderiv_χ_zero_on_thick :
      ∀ x ∈ Metric.thickening (δ / 2) (closure Ω'),
        ∀ k : Fin (Module.finrank ℝ E),
          (fderiv ℝ χ x) (EuclideanSpace.single k 1) = 0 := by
    intro x hx k
    have hχ_eq_one_nhds : (fun y => χ y) =ᶠ[nhds x] (fun _ => (1 : ℝ)) := by
      refine Filter.eventually_of_mem (h_thick_half_open.mem_nhds hx) ?_
      intro y hy
      exact hχ_one y (h_thick_half_subset_K_χ hy)
    have h_fderiv_eq : fderiv ℝ χ x = fderiv ℝ (fun _ : EuclN => (1 : ℝ)) x :=
      Filter.EventuallyEq.fderiv_eq hχ_eq_one_nhds
    rw [h_fderiv_eq]; simp
  have hu_g_eq_on_closure : ∀ x ∈ closure Ω', u_g x = D.uChart x := by
    intro x hx
    have hχx : χ x = 1 := hχ_one_on_closure x hx
    change χ x * D.uChart x = D.uChart x
    rw [hχx, one_mul]
  have hg_g_eq_on_closure : ∀ x ∈ closure Ω',
      ∀ i : Fin (Module.finrank ℝ E), g_g i x = D.weakPartial i x := by
    intro x hx i
    have hχx : χ x = 1 := hχ_one_on_closure x hx
    have hx_in_thick : x ∈ Metric.thickening (δ / 2) (closure Ω') :=
      h_closure_subset_thick_half_δ hx
    have hdχx : (fderiv ℝ χ x) (EuclideanSpace.single i 1) = 0 :=
      h_fderiv_χ_zero_on_thick x hx_in_thick i
    change (fderiv ℝ χ x) (EuclideanSpace.single i 1) * D.uChart x +
      χ x * D.weakPartial i x = D.weakPartial i x
    rw [hdχx, hχx, zero_mul, one_mul, zero_add]
  have h_cthick_h_subset_closure : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ closure Ω' := fun {h} hh_le =>
    (hh_support_in_Ω' hh_le).trans subset_closure
  have h_tsupp_subset_closure : tsupport η ⊆ closure Ω' :=
    hη_in_Ω'.trans subset_closure
  have h_diffQuot_u_g_eq_on_tsupport :
      ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      ∀ (k : Fin (Module.finrank ℝ E)),
        ∀ x ∈ tsupport η,
          Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g x =
          Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.uChart x := by
    intro h hh hh_le k x hx
    have hx_in_closure : x ∈ closure Ω' := h_tsupp_subset_closure hx
    have h_shift_in_cthick : x + h • EuclideanSpace.single k 1 ∈
        Metric.cthickening |h| (tsupport η) := by
      refine Metric.mem_cthickening_of_dist_le _ _ |h| (tsupport η) hx ?_
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
      have hsing : ‖(EuclideanSpace.single k (1 : ℝ) : EuclN)‖ = 1 := by simp
      rw [hsing, mul_one, Real.norm_eq_abs]
    have h_shift_in_closure :
        x + h • EuclideanSpace.single k 1 ∈ closure Ω' :=
      h_cthick_h_subset_closure hh_le h_shift_in_cthick
    rw [Sobolev.diffQuot_apply_of_ne
        (d := Module.finrank ℝ E) k hh,
      Sobolev.diffQuot_apply_of_ne
        (d := Module.finrank ℝ E) k hh,
      hu_g_eq_on_closure x hx_in_closure,
      hu_g_eq_on_closure _ h_shift_in_closure]
  have h_diffQuot_g_g_eq_on_tsupport :
      ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      ∀ (k : Fin (Module.finrank ℝ E)) (i : Fin (Module.finrank ℝ E)),
        ∀ x ∈ tsupport η,
          Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (g_g i) x =
          Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (D.weakPartial i) x := by
    intro h hh hh_le k i x hx
    have hx_in_closure : x ∈ closure Ω' := h_tsupp_subset_closure hx
    have h_shift_in_cthick : x + h • EuclideanSpace.single k 1 ∈
        Metric.cthickening |h| (tsupport η) := by
      refine Metric.mem_cthickening_of_dist_le _ _ |h| (tsupport η) hx ?_
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
      have hsing : ‖(EuclideanSpace.single k (1 : ℝ) : EuclN)‖ = 1 := by simp
      rw [hsing, mul_one, Real.norm_eq_abs]
    have h_shift_in_closure :
        x + h • EuclideanSpace.single k 1 ∈ closure Ω' :=
      h_cthick_h_subset_closure hh_le h_shift_in_cthick
    rw [Sobolev.diffQuot_apply_of_ne
        (d := Module.finrank ℝ E) k hh,
      Sobolev.diffQuot_apply_of_ne
        (d := Module.finrank ℝ E) k hh,
      hg_g_eq_on_closure x hx_in_closure i,
      hg_g_eq_on_closure _ h_shift_in_closure i]
  have hΩ'_meas : MeasurableSet Ω' := hΩ'.measurableSet
  have h_tsupp_meas : MeasurableSet (tsupport η) :=
    (isClosed_tsupport η).measurableSet
  have h_FK :
      ∀ (k : Fin (Module.finrank ℝ E)),
      ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
        ∫ x in tsupport η,
            (Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h u_g x)^2
          ∂(volume : Measure EuclN) ≤
          ∫ x in Ω', ∑ l : Fin (Module.finrank ℝ E), ((g_g l) x) ^ 2
            ∂(volume : Measure EuclN) := by
    intro k h hh hh_le
    have h_LHS_eq :
        ∫ x in tsupport η,
            (Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h u_g x)^2
          ∂(volume : Measure EuclN) =
        ∫ x in tsupport η,
            (Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h D.uChart x)^2
          ∂(volume : Measure EuclN) := by
      refine setIntegral_congr_fun h_tsupp_meas ?_
      intro x hx
      have h_eq := h_diffQuot_u_g_eq_on_tsupport hh hh_le k x hx
      exact congrArg (· ^ 2) h_eq
    have hΩ'_subset_closure : Ω' ⊆ closure Ω' := subset_closure
    have h_RHS_eq :
        ∫ x in Ω', ∑ l : Fin (Module.finrank ℝ E), ((g_g l) x) ^ 2
          ∂(volume : Measure EuclN) =
        ∫ x in Ω', ∑ l : Fin (Module.finrank ℝ E), ((D.weakPartial l) x) ^ 2
          ∂(volume : Measure EuclN) := by
      refine setIntegral_congr_fun hΩ'_meas ?_
      intro x hx
      have hx_in_closure : x ∈ closure Ω' := hΩ'_subset_closure hx
      refine congrArg (fun s => s) ?_
      refine Finset.sum_congr rfl ?_
      intro l _
      rw [hg_g_eq_on_closure x hx_in_closure l]
    rw [h_LHS_eq, h_RHS_eq]
    exact h_diffQuot_u_bound k hh hh_le
  have h_nirenberg_eq :
      ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      ∀ (k : Fin (Module.finrank ℝ E)),
        ∀ x : EuclN,
          Sobolev.NirenbergTestFunction.nirenbergTestFunction
            (d := Module.finrank ℝ E) k h η u_g x =
          Sobolev.NirenbergTestFunction.nirenbergTestFunction
            (d := Module.finrank ℝ E) k h η D.uChart x := by
    intro h hh hh_le k x
    have hnh : (-h) ≠ 0 := neg_ne_zero.mpr hh
    have h_pt_inner : ∀ y : EuclN,
        (η y)^2 * Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h u_g y =
        (η y)^2 * Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h D.uChart y := by
      intro y
      by_cases hη_y : η y = 0
      · rw [hη_y]; ring
      · have hy_in_support : y ∈ tsupport η :=
          subset_tsupport η (Function.mem_support.mpr hη_y)
        rw [h_diffQuot_u_g_eq_on_tsupport hh hh_le k y hy_in_support]
    change Sobolev.diffQuot
        (d := Module.finrank ℝ E) k (-h)
        (fun y => (η y)^2 *
          Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h u_g y) x =
      Sobolev.diffQuot
        (d := Module.finrank ℝ E) k (-h)
        (fun y => (η y)^2 *
          Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.uChart y) x
    rw [Sobolev.diffQuot_apply_of_ne
        (d := Module.finrank ℝ E) k hnh,
      Sobolev.diffQuot_apply_of_ne
        (d := Module.finrank ℝ E) k hnh]
    rw [h_pt_inner (x + (-h) • EuclideanSpace.single k 1), h_pt_inner x]
  have h_v_test_sq :
      ∀ (k : Fin (Module.finrank ℝ E)),
      ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
        ∫ x, (Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u_g x)^2 ∂(volume : Measure EuclN) ≤
          8 * N^2 *
            ∫ x in tsupport η,
                (Sobolev.diffQuot k h u_g x)^2
              ∂(volume : Measure EuclN) +
          2 * ∫ x, (η x)^2 *
              (Sobolev.diffQuot k h (g_g k) x)^2
            ∂(volume : Measure EuclN) := by
    intro k h hh hh_le
    have h_LHS_eq :
        ∫ x, (Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u_g x)^2 ∂(volume : Measure EuclN) =
        ∫ x, (Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η D.uChart x)^2 ∂(volume : Measure EuclN) := by
      refine integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro x
      change (Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u_g x)^2 =
        (Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η D.uChart x)^2
      rw [h_nirenberg_eq hh hh_le k x]
    have h_RHS_1_eq :
        ∫ x in tsupport η,
            (Sobolev.diffQuot k h u_g x)^2
          ∂(volume : Measure EuclN) =
        ∫ x in tsupport η,
            (Sobolev.diffQuot k h D.uChart x)^2
          ∂(volume : Measure EuclN) := by
      refine setIntegral_congr_fun h_tsupp_meas ?_
      intro x hx
      exact congrArg (· ^ 2) (h_diffQuot_u_g_eq_on_tsupport hh hh_le k x hx)
    have h_RHS_2_eq :
        ∫ x, (η x)^2 *
            (Sobolev.diffQuot k h (g_g k) x)^2
          ∂(volume : Measure EuclN) =
        ∫ x, (η x)^2 *
            (Sobolev.diffQuot k h (D.weakPartial k) x)^2
          ∂(volume : Measure EuclN) := by
      refine integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro x
      change (η x)^2 *
          (Sobolev.diffQuot k h (g_g k) x)^2 =
        (η x)^2 *
          (Sobolev.diffQuot k h (D.weakPartial k) x)^2
      by_cases hη_x : η x = 0
      · rw [hη_x]; ring
      · have hx_in_support : x ∈ tsupport η :=
          subset_tsupport η (Function.mem_support.mpr hη_x)
        rw [h_diffQuot_g_g_eq_on_tsupport hh hh_le k k x hx_in_support]
    rw [h_LHS_eq, h_RHS_1_eq, h_RHS_2_eq]
    exact h_testFunction_sq_bound k hh hh_le
  have h_master :
      ∀ (k : Fin (Module.finrank ℝ E)),
      ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      B.lam * ∫ x, (η x)^2 *
          ∑ l : Fin (Module.finrank ℝ E),
            Sobolev.diffQuot k h (g_g l) x ^ 2
        ∂(volume : Measure EuclN) ≤
        |∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), ∫ x,
              2 * Sobolev.translate k h
                (fun y : EuclN => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              Sobolev.diffQuot k h (g_g i) x *
              Sobolev.diffQuot k h u_g x
            ∂(volume : Measure EuclN)| +
        |∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), ∫ x,
              Sobolev.diffQuot k h
                (fun y : EuclN => B.a y i j) x * (η x)^2 *
              ((g_g i) x) *
              Sobolev.diffQuot k h (g_g j) x
            ∂(volume : Measure EuclN)| +
        |∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), ∫ x,
              2 * Sobolev.diffQuot k h
                (fun y : EuclN => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              ((g_g i) x) *
              Sobolev.diffQuot k h u_g x
            ∂(volume : Measure EuclN)| +
        |∫ x in (Set.univ : Set EuclN), f_g x *
            Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u_g x| +
        |∫ x in (Set.univ : Set EuclN), B.c x * u_g x *
            Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u_g x ∂(volume : Measure EuclN)| := by
    intro k h hh hh_le
    have h_LHS_eq :
        ∫ x, (η x)^2 *
            ∑ l : Fin (Module.finrank ℝ E),
              Sobolev.diffQuot k h (g_g l) x ^ 2
          ∂(volume : Measure EuclN) =
        ∫ x, (η x)^2 *
            ∑ l : Fin (Module.finrank ℝ E),
              Sobolev.diffQuot k h (D.weakPartial l) x ^ 2
          ∂(volume : Measure EuclN) := by
      refine integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro x
      change (η x)^2 *
            ∑ l : Fin (Module.finrank ℝ E),
              Sobolev.diffQuot k h (g_g l) x ^ 2 =
        (η x)^2 *
            ∑ l : Fin (Module.finrank ℝ E),
              Sobolev.diffQuot k h (D.weakPartial l) x ^ 2
      by_cases hη_x : η x = 0
      · rw [hη_x]; ring
      · have hx_in_support : x ∈ tsupport η :=
          subset_tsupport η (Function.mem_support.mpr hη_x)
        congr 1
        refine Finset.sum_congr rfl ?_
        intro l _
        rw [h_diffQuot_g_g_eq_on_tsupport hh hh_le k l x hx_in_support]
    have h_A1_eq :
        ∀ i j : Fin (Module.finrank ℝ E),
        ∫ x, 2 * Sobolev.translate k h
                (fun y : EuclN => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              Sobolev.diffQuot k h (g_g i) x *
              Sobolev.diffQuot k h u_g x
            ∂(volume : Measure EuclN) =
        ∫ x, 2 * Sobolev.translate k h
                (fun y : EuclN => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              Sobolev.diffQuot k h (D.weakPartial i) x *
              Sobolev.diffQuot k h D.uChart x
            ∂(volume : Measure EuclN) := by
      intro i j
      refine integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro x
      change 2 * Sobolev.translate k h
                (fun y : EuclN => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              Sobolev.diffQuot k h (g_g i) x *
              Sobolev.diffQuot k h u_g x =
        2 * Sobolev.translate k h
                (fun y : EuclN => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              Sobolev.diffQuot k h (D.weakPartial i) x *
              Sobolev.diffQuot k h D.uChart x
      by_cases hη_x : η x = 0
      · rw [hη_x]; ring
      · have hx_in_support : x ∈ tsupport η :=
          subset_tsupport η (Function.mem_support.mpr hη_x)
        rw [h_diffQuot_g_g_eq_on_tsupport hh hh_le k i x hx_in_support,
            h_diffQuot_u_g_eq_on_tsupport hh hh_le k x hx_in_support]
    have h_A2_eq :
        ∀ i j : Fin (Module.finrank ℝ E),
        ∫ x, Sobolev.diffQuot k h
                (fun y : EuclN => B.a y i j) x * (η x)^2 *
              ((g_g i) x) *
              Sobolev.diffQuot k h (g_g j) x
            ∂(volume : Measure EuclN) =
        ∫ x, Sobolev.diffQuot k h
                (fun y : EuclN => B.a y i j) x * (η x)^2 *
              ((D.weakPartial i) x) *
              Sobolev.diffQuot k h (D.weakPartial j) x
            ∂(volume : Measure EuclN) := by
      intro i j
      refine integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro x
      change Sobolev.diffQuot k h
              (fun y : EuclN => B.a y i j) x * (η x)^2 *
            ((g_g i) x) *
            Sobolev.diffQuot k h (g_g j) x =
        Sobolev.diffQuot k h
              (fun y : EuclN => B.a y i j) x * (η x)^2 *
            ((D.weakPartial i) x) *
            Sobolev.diffQuot k h (D.weakPartial j) x
      by_cases hη_x : η x = 0
      · rw [hη_x]; ring
      · have hx_in_support : x ∈ tsupport η :=
          subset_tsupport η (Function.mem_support.mpr hη_x)
        have hx_in_closure : x ∈ closure Ω' := h_tsupp_subset_closure hx_in_support
        rw [hg_g_eq_on_closure x hx_in_closure i,
            h_diffQuot_g_g_eq_on_tsupport hh hh_le k j x hx_in_support]
    have h_A3_eq :
        ∀ i j : Fin (Module.finrank ℝ E),
        ∫ x, 2 * Sobolev.diffQuot k h
                (fun y : EuclN => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              ((g_g i) x) *
              Sobolev.diffQuot k h u_g x
            ∂(volume : Measure EuclN) =
        ∫ x, 2 * Sobolev.diffQuot k h
                (fun y : EuclN => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              ((D.weakPartial i) x) *
              Sobolev.diffQuot k h D.uChart x
            ∂(volume : Measure EuclN) := by
      intro i j
      refine integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro x
      change 2 * Sobolev.diffQuot k h
              (fun y : EuclN => B.a y i j) x * (η x) *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            ((g_g i) x) *
            Sobolev.diffQuot k h u_g x =
        2 * Sobolev.diffQuot k h
              (fun y : EuclN => B.a y i j) x * (η x) *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            ((D.weakPartial i) x) *
            Sobolev.diffQuot k h D.uChart x
      by_cases hη_x : η x = 0
      · rw [hη_x]; ring
      · have hx_in_support : x ∈ tsupport η :=
          subset_tsupport η (Function.mem_support.mpr hη_x)
        have hx_in_closure : x ∈ closure Ω' := h_tsupp_subset_closure hx_in_support
        rw [hg_g_eq_on_closure x hx_in_closure i,
            h_diffQuot_u_g_eq_on_tsupport hh hh_le k x hx_in_support]
    have h_f_term_eq :
        ∫ x in (Set.univ : Set EuclN), f_g x *
            Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u_g x =
        ∫ x in (Set.univ : Set EuclN),
            (densityOnEuclid (I := I) g α x * D.fChart x) *
            Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η D.uChart x := by
      refine setIntegral_congr_ae MeasurableSet.univ ?_
      refine Filter.Eventually.of_forall ?_
      intro x _
      have h_support_subset :
          Function.support
            (Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η D.uChart) ⊆
            Metric.cthickening |h| (tsupport η) := by
        intro y hy
        rw [Function.mem_support] at hy
        have hnh : (-h) ≠ 0 := neg_ne_zero.mpr hh
        change Sobolev.diffQuot
            (d := Module.finrank ℝ E) k (-h)
            (fun y₁ => (η y₁)^2 *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.uChart y₁) y ≠ 0 at hy
        rw [Sobolev.diffQuot_apply_of_ne
            (d := Module.finrank ℝ E) k hnh] at hy
        have h_num_ne :
            (η (y + (-h) • EuclideanSpace.single k 1))^2 *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.uChart
                  (y + (-h) • EuclideanSpace.single k 1) -
            (η y)^2 *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.uChart y ≠ 0 := by
          intro h_zero
          apply hy
          rw [h_zero, zero_div]
        by_cases hη_y : η y = 0
        · have h_first_zero : (η y)^2 *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.uChart y = 0 := by
            rw [hη_y]; ring
          rw [h_first_zero, sub_zero] at h_num_ne
          have h_eta_shift_ne : η (y + (-h) • EuclideanSpace.single k 1) ≠ 0 := by
            intro h_zero
            apply h_num_ne
            rw [show (η (y + (-h) • EuclideanSpace.single k 1))^2 = 0 from by
              rw [h_zero]; ring, zero_mul]
          have h_shift_in_support :
              y + (-h) • EuclideanSpace.single k 1 ∈ tsupport η :=
            subset_tsupport η (Function.mem_support.mpr h_eta_shift_ne)
          refine Metric.mem_cthickening_of_dist_le _ _ |h| (tsupport η)
            h_shift_in_support ?_
          rw [dist_eq_norm]
          have h_diff_eq : y - (y + (-h) • EuclideanSpace.single k 1) =
              h • EuclideanSpace.single k 1 := by
            rw [sub_add_eq_sub_sub, sub_self, zero_sub, neg_smul, neg_neg]
          rw [h_diff_eq, norm_smul]
          have hsing : ‖(EuclideanSpace.single k (1 : ℝ) : EuclN)‖ = 1 := by simp
          rw [hsing, mul_one, Real.norm_eq_abs]
        · exact Metric.self_subset_cthickening _
            (subset_tsupport η (Function.mem_support.mpr hη_y))
      have h_support_subset_u_g :
          Function.support
            (Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u_g) ⊆
            Metric.cthickening |h| (tsupport η) := by
        intro y hy
        rw [Function.mem_support] at hy
        have hnh : (-h) ≠ 0 := neg_ne_zero.mpr hh
        change Sobolev.diffQuot
            (d := Module.finrank ℝ E) k (-h)
            (fun y₁ => (η y₁)^2 *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h u_g y₁) y ≠ 0 at hy
        rw [Sobolev.diffQuot_apply_of_ne
            (d := Module.finrank ℝ E) k hnh] at hy
        have h_num_ne :
            (η (y + (-h) • EuclideanSpace.single k 1))^2 *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h u_g
                  (y + (-h) • EuclideanSpace.single k 1) -
            (η y)^2 *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h u_g y ≠ 0 := by
          intro h_zero
          apply hy
          rw [h_zero, zero_div]
        by_cases hη_y : η y = 0
        · have h_first_zero : (η y)^2 *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h u_g y = 0 := by
            rw [hη_y]; ring
          rw [h_first_zero, sub_zero] at h_num_ne
          have h_eta_shift_ne : η (y + (-h) • EuclideanSpace.single k 1) ≠ 0 := by
            intro h_zero
            apply h_num_ne
            rw [show (η (y + (-h) • EuclideanSpace.single k 1))^2 = 0 from by
              rw [h_zero]; ring, zero_mul]
          have h_shift_in_support :
              y + (-h) • EuclideanSpace.single k 1 ∈ tsupport η :=
            subset_tsupport η (Function.mem_support.mpr h_eta_shift_ne)
          refine Metric.mem_cthickening_of_dist_le _ _ |h| (tsupport η)
            h_shift_in_support ?_
          rw [dist_eq_norm]
          have h_diff_eq : y - (y + (-h) • EuclideanSpace.single k 1) =
              h • EuclideanSpace.single k 1 := by
            rw [sub_add_eq_sub_sub, sub_self, zero_sub, neg_smul, neg_neg]
          rw [h_diff_eq, norm_smul]
          have hsing : ‖(EuclideanSpace.single k (1 : ℝ) : EuclN)‖ = 1 := by simp
          rw [hsing, mul_one, Real.norm_eq_abs]
        · exact Metric.self_subset_cthickening _
            (subset_tsupport η (Function.mem_support.mpr hη_y))
      by_cases hx_in : x ∈ Metric.cthickening |h| (tsupport η)
      · have hx_in_closure : x ∈ closure Ω' :=
          h_cthick_h_subset_closure hh_le hx_in
        have hχx : χ x = 1 := hχ_one_on_closure x hx_in_closure
        have hf_g_eq : f_g x = densityOnEuclid (I := I) g α x * D.fChart x := by
          change χ x * (densityOnEuclid (I := I) g α x * D.fChart x) =
            densityOnEuclid (I := I) g α x * D.fChart x
          rw [hχx, one_mul]
        rw [hf_g_eq, h_nirenberg_eq hh hh_le k x]
      · have h_test_u_g_zero :
            Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u_g x = 0 := by
          by_contra h_ne
          exact hx_in (h_support_subset_u_g (Function.mem_support.mpr h_ne))
        have h_test_D_zero :
            Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η D.uChart x = 0 := by
          by_contra h_ne
          exact hx_in (h_support_subset (Function.mem_support.mpr h_ne))
        rw [h_test_u_g_zero, h_test_D_zero, mul_zero, mul_zero]
    have h_c_term_eq :
        ∫ x in (Set.univ : Set EuclN), B.c x * u_g x *
            Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u_g x ∂(volume : Measure EuclN) =
        ∫ x in (Set.univ : Set EuclN), B.c x * D.uChart x *
            Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η D.uChart x ∂(volume : Measure EuclN) := by
      refine setIntegral_congr_ae MeasurableSet.univ ?_
      refine Filter.Eventually.of_forall ?_
      intro x _
      have h_support_subset_D :
          Function.support
            (Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η D.uChart) ⊆
            Metric.cthickening |h| (tsupport η) := by
        intro y hy
        rw [Function.mem_support] at hy
        have hnh : (-h) ≠ 0 := neg_ne_zero.mpr hh
        change Sobolev.diffQuot
            (d := Module.finrank ℝ E) k (-h)
            (fun y₁ => (η y₁)^2 *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.uChart y₁) y ≠ 0 at hy
        rw [Sobolev.diffQuot_apply_of_ne
            (d := Module.finrank ℝ E) k hnh] at hy
        have h_num_ne :
            (η (y + (-h) • EuclideanSpace.single k 1))^2 *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.uChart
                  (y + (-h) • EuclideanSpace.single k 1) -
            (η y)^2 *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.uChart y ≠ 0 := by
          intro h_zero; apply hy; rw [h_zero, zero_div]
        by_cases hη_y : η y = 0
        · have h_first_zero : (η y)^2 *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.uChart y = 0 := by
            rw [hη_y]; ring
          rw [h_first_zero, sub_zero] at h_num_ne
          have h_eta_shift_ne : η (y + (-h) • EuclideanSpace.single k 1) ≠ 0 := by
            intro h_zero
            apply h_num_ne
            rw [show (η (y + (-h) • EuclideanSpace.single k 1))^2 = 0 from by
              rw [h_zero]; ring, zero_mul]
          have h_shift_in_support :
              y + (-h) • EuclideanSpace.single k 1 ∈ tsupport η :=
            subset_tsupport η (Function.mem_support.mpr h_eta_shift_ne)
          refine Metric.mem_cthickening_of_dist_le _ _ |h| (tsupport η)
            h_shift_in_support ?_
          rw [dist_eq_norm]
          have h_diff_eq : y - (y + (-h) • EuclideanSpace.single k 1) =
              h • EuclideanSpace.single k 1 := by
            rw [sub_add_eq_sub_sub, sub_self, zero_sub, neg_smul, neg_neg]
          rw [h_diff_eq, norm_smul]
          have hsing : ‖(EuclideanSpace.single k (1 : ℝ) : EuclN)‖ = 1 := by simp
          rw [hsing, mul_one, Real.norm_eq_abs]
        · exact Metric.self_subset_cthickening _
            (subset_tsupport η (Function.mem_support.mpr hη_y))
      have h_support_subset_u :
          Function.support
            (Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u_g) ⊆
            Metric.cthickening |h| (tsupport η) := by
        intro y hy
        rw [Function.mem_support] at hy
        have hnh : (-h) ≠ 0 := neg_ne_zero.mpr hh
        change Sobolev.diffQuot
            (d := Module.finrank ℝ E) k (-h)
            (fun y₁ => (η y₁)^2 *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h u_g y₁) y ≠ 0 at hy
        rw [Sobolev.diffQuot_apply_of_ne
            (d := Module.finrank ℝ E) k hnh] at hy
        have h_num_ne :
            (η (y + (-h) • EuclideanSpace.single k 1))^2 *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h u_g
                  (y + (-h) • EuclideanSpace.single k 1) -
            (η y)^2 *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h u_g y ≠ 0 := by
          intro h_zero; apply hy; rw [h_zero, zero_div]
        by_cases hη_y : η y = 0
        · have h_first_zero : (η y)^2 *
              Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h u_g y = 0 := by
            rw [hη_y]; ring
          rw [h_first_zero, sub_zero] at h_num_ne
          have h_eta_shift_ne : η (y + (-h) • EuclideanSpace.single k 1) ≠ 0 := by
            intro h_zero
            apply h_num_ne
            rw [show (η (y + (-h) • EuclideanSpace.single k 1))^2 = 0 from by
              rw [h_zero]; ring, zero_mul]
          have h_shift_in_support :
              y + (-h) • EuclideanSpace.single k 1 ∈ tsupport η :=
            subset_tsupport η (Function.mem_support.mpr h_eta_shift_ne)
          refine Metric.mem_cthickening_of_dist_le _ _ |h| (tsupport η)
            h_shift_in_support ?_
          rw [dist_eq_norm]
          have h_diff_eq : y - (y + (-h) • EuclideanSpace.single k 1) =
              h • EuclideanSpace.single k 1 := by
            rw [sub_add_eq_sub_sub, sub_self, zero_sub, neg_smul, neg_neg]
          rw [h_diff_eq, norm_smul]
          have hsing : ‖(EuclideanSpace.single k (1 : ℝ) : EuclN)‖ = 1 := by simp
          rw [hsing, mul_one, Real.norm_eq_abs]
        · exact Metric.self_subset_cthickening _
            (subset_tsupport η (Function.mem_support.mpr hη_y))
      by_cases hx_in : x ∈ Metric.cthickening |h| (tsupport η)
      · have hx_in_closure : x ∈ closure Ω' :=
          h_cthick_h_subset_closure hh_le hx_in
        have hu_eq : u_g x = D.uChart x := hu_g_eq_on_closure x hx_in_closure
        rw [hu_eq, h_nirenberg_eq hh hh_le k x]
      · have h_test_u_g_zero :
            Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η u_g x = 0 := by
          by_contra h_ne
          exact hx_in (h_support_subset_u (Function.mem_support.mpr h_ne))
        have h_test_D_zero :
            Sobolev.NirenbergTestFunction.nirenbergTestFunction
              k h η D.uChart x = 0 := by
          by_contra h_ne
          exact hx_in (h_support_subset_D (Function.mem_support.mpr h_ne))
        rw [h_test_u_g_zero, h_test_D_zero, mul_zero, mul_zero]
    rw [h_LHS_eq]
    have h_A1_sum_eq :
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), ∫ x,
              2 * Sobolev.translate k h
                (fun y : EuclN => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              Sobolev.diffQuot k h (g_g i) x *
              Sobolev.diffQuot k h u_g x
            ∂(volume : Measure EuclN) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), ∫ x,
              2 * Sobolev.translate k h
                (fun y : EuclN => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              Sobolev.diffQuot k h (D.weakPartial i) x *
              Sobolev.diffQuot k h D.uChart x
            ∂(volume : Measure EuclN) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      exact h_A1_eq i j
    have h_A2_sum_eq :
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), ∫ x,
              Sobolev.diffQuot k h
                (fun y : EuclN => B.a y i j) x * (η x)^2 *
              ((g_g i) x) *
              Sobolev.diffQuot k h (g_g j) x
            ∂(volume : Measure EuclN) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), ∫ x,
              Sobolev.diffQuot k h
                (fun y : EuclN => B.a y i j) x * (η x)^2 *
              ((D.weakPartial i) x) *
              Sobolev.diffQuot k h (D.weakPartial j) x
            ∂(volume : Measure EuclN) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      exact h_A2_eq i j
    have h_A3_sum_eq :
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), ∫ x,
              2 * Sobolev.diffQuot k h
                (fun y : EuclN => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              ((g_g i) x) *
              Sobolev.diffQuot k h u_g x
            ∂(volume : Measure EuclN) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), ∫ x,
              2 * Sobolev.diffQuot k h
                (fun y : EuclN => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              ((D.weakPartial i) x) *
              Sobolev.diffQuot k h D.uChart x
            ∂(volume : Measure EuclN) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      exact h_A3_eq i j
    rw [h_A1_sum_eq, h_A2_sum_eq, h_A3_sum_eq, h_f_term_eq, h_c_term_eq]
    exact h_coercivity k hh hh_le
  have h_g_g_quant :
      eLpNorm
        (Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (g_g i)) 2
        ((volume : Measure EuclN).restrict Ω'')
      ≤ ENNReal.ofReal (Real.sqrt ((2 / B.lam) *
          nirenbergMasterYoungConstant B N hΩ'_compact k *
          (∫ x in Ω', ∑ l : Fin (Module.finrank ℝ E), ((g_g l) x) ^ 2
              ∂(volume : Measure EuclN) +
            ∫ x in Ω', (u_g x)^2 ∂(volume : Measure EuclN) +
            ∫ x in Ω', (f_g x)^2 ∂(volume : Measure EuclN)))) :=
    uniform_diffQuot_bound_quantitative
      (d := Module.finrank ℝ E)
      B hu_g_l2 hf_g_l2_local hg_g_l2 hη hη_support hη_range hN
      h_fderiv_eta hΩ' hΩ'_compact
      hh_support_in_Ω' hη_one_on_Ω'' hΩ''_meas
      h_FK h_v_test_sq h_master hh_pos hh_le
  have hΩ'_closure_meas : MeasurableSet (closure Ω') :=
    isClosed_closure.measurableSet
  have hf_chart_l2_closure : MemLp D.fChart 2
      ((volume : Measure EuclN).restrict (closure Ω')) :=
    memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure (I := I) (M := M)
      D.f_chart_memLp_weighted hΩ'_compact hΩ'_closure_meas hΩ'_chart
  set fSource : EuclN → ℝ := fun x => densityOnEuclid (I := I) g α x * D.fChart x
    with hfSource_def
  have hfSource_l2_closure : MemLp fSource 2
      ((volume : Measure EuclN).restrict (closure Ω')) :=
    densityOnEuclid_mul_memLp (I := I) (M := M) (g := g) (α := α)
      hΩ'_compact hΩ'_chart hf_chart_l2_closure
  set Sw : ℝ := ∑ l : Fin (Module.finrank ℝ E),
      (eLpNorm (D.weakPartial l) 2
        ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2 with hSw_def
  set Su : ℝ := (eLpNorm D.uChart 2
      ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2 with hSu_def
  set Sf : ℝ := (eLpNorm D.fChart 2
      ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2 with hSf_def
  have hSw_nn : 0 ≤ Sw := by
    rw [hSw_def]; exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hSu_nn : 0 ≤ Su := by rw [hSu_def]; exact sq_nonneg _
  have hSf_nn : 0 ≤ Sf := by rw [hSf_def]; exact sq_nonneg _
  set G_total : ℝ :=
    (∫ x in Ω', ∑ l : Fin (Module.finrank ℝ E), ((g_g l) x) ^ 2
        ∂(volume : Measure EuclN) +
      ∫ x in Ω', (u_g x)^2 ∂(volume : Measure EuclN) +
      ∫ x in Ω', (f_g x)^2 ∂(volume : Measure EuclN)) with hG_total_def
  have hG_total_nn : 0 ≤ G_total := by
    rw [hG_total_def]
    refine add_nonneg (add_nonneg ?_ ?_) ?_
    · exact integral_nonneg (fun x => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    · exact integral_nonneg (fun x => sq_nonneg _)
    · exact integral_nonneg (fun x => sq_nonneg _)
  set Cχ : ℝ :=
    2 * ((Module.finrank ℝ E : ℝ) + 1) * (M_χ ^ 2 + M_dχ ^ 2 + 1) with hCχ_def
  have hCχ_nn : 0 ≤ Cχ := by
    rw [hCχ_def]
    have hn_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
    positivity
  have h_Sf'_le :
      (eLpNorm fSource 2
        ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2 ≤
        (densityOnEuclidClosureSup (I := I) (M := M) g α Ω') ^ 2 * Sf := by
    have h := eLpNorm_densityOnEuclid_mul_sq_le (I := I) (M := M)
      (g := g) (α := α) hΩ'_compact hΩ'_chart hf_chart_l2_closure
    rw [hfSource_def, hSf_def]
    exact h
  have h_gTotal_data : G_total ≤
      Cχ * (Sw + Su +
        (eLpNorm fSource 2
          ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2) := by
    have h := cutoff_energy_le_data_eLpNorm_sq (I := I) (M := M) (g := g) (α := α)
      hχ_smooth hM_χ_bd hM_dχ_bd hΩ'_compact hΩ'_chart hfSource_l2_closure D
    rw [hG_total_def, hCχ_def, hSw_def, hSu_def]
    simp only [hg_g_def, hu_g_def, hf_g_def, hfSource_def] at h ⊢
    convert h using 2
  set Mden2 : ℝ := max 1 ((densityOnEuclidClosureSup (I := I) (M := M) g α Ω') ^ 2)
    with hMden2_def
  have hMden2_one_le : (1 : ℝ) ≤ Mden2 := le_max_left _ _
  have hMden2_dens_le :
      (densityOnEuclidClosureSup (I := I) (M := M) g α Ω') ^ 2 ≤ Mden2 :=
    le_max_right _ _
  have hMden2_nn : 0 ≤ Mden2 := le_trans zero_le_one hMden2_one_le
  have h_gTotal_max : G_total ≤ Cχ * Mden2 * (Sw + Su + Sf) := by
    refine le_trans h_gTotal_data ?_
    have h_inner :
        Sw + Su +
          (eLpNorm fSource 2
            ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2 ≤
          Mden2 * (Sw + Su + Sf) := by
      have h_w : Sw ≤ Mden2 * Sw :=
        le_mul_of_one_le_left hSw_nn hMden2_one_le
      have h_u : Su ≤ Mden2 * Su :=
        le_mul_of_one_le_left hSu_nn hMden2_one_le
      have h_f :
          (eLpNorm fSource 2
            ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2 ≤
            Mden2 * Sf := by
        refine le_trans h_Sf'_le ?_
        exact mul_le_mul_of_nonneg_right hMden2_dens_le hSf_nn
      have h_expand : Mden2 * (Sw + Su + Sf) =
          Mden2 * Sw + Mden2 * Su + Mden2 * Sf := by ring
      linarith [h_w, h_u, h_f, h_expand]
    calc Cχ * (Sw + Su +
            (eLpNorm fSource 2
              ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2)
        ≤ Cχ * (Mden2 * (Sw + Su + Sf)) :=
          mul_le_mul_of_nonneg_left h_inner hCχ_nn
      _ = Cχ * Mden2 * (Sw + Su + Sf) := by ring
  have ellipticity_pos : 0 < B.lam := B.ellipticity_pos
  have h_two_lam_nn : (0 : ℝ) ≤ 2 / B.lam := by positivity
  have hC_young_nn : 0 ≤ nirenbergMasterYoungConstant B N hΩ'_compact k :=
    nirenbergMasterYoungConstant_nonneg B hN hΩ'_compact k
  have h_coeff_nn : 0 ≤ (2 / B.lam) *
      nirenbergMasterYoungConstant B N hΩ'_compact k * Cχ * Mden2 :=
    mul_nonneg (mul_nonneg (mul_nonneg h_two_lam_nn hC_young_nn) hCχ_nn) hMden2_nn
  have h_sqrt_arg_le :
      (2 / B.lam) * nirenbergMasterYoungConstant B N hΩ'_compact k * G_total ≤
        ((2 / B.lam) * nirenbergMasterYoungConstant B N hΩ'_compact k *
          Cχ * Mden2) * (Sw + Su + Sf) := by
    have h_pre_nn : 0 ≤ (2 / B.lam) *
        nirenbergMasterYoungConstant B N hΩ'_compact k :=
      mul_nonneg h_two_lam_nn hC_young_nn
    calc (2 / B.lam) * nirenbergMasterYoungConstant B N hΩ'_compact k * G_total
        ≤ (2 / B.lam) * nirenbergMasterYoungConstant B N hΩ'_compact k *
            (Cχ * Mden2 * (Sw + Su + Sf)) :=
          mul_le_mul_of_nonneg_left h_gTotal_max h_pre_nn
      _ = ((2 / B.lam) * nirenbergMasterYoungConstant B N hΩ'_compact k *
            Cχ * Mden2) * (Sw + Su + Sf) := by ring
  have hC_geom_eq : C_geom i k =
      Real.sqrt ((2 / B.lam) *
        nirenbergMasterYoungConstant B N hΩ'_compact k * Cχ * Mden2) := by
    simp only [hC_geom_def, hCχ_def, hMden2_def]
  have h_sqrt_le :
      Real.sqrt ((2 / B.lam) *
        nirenbergMasterYoungConstant B N hΩ'_compact k * G_total) ≤
        C_geom i k * Real.sqrt (Sw + Su + Sf) := by
    have h_mono := Real.sqrt_le_sqrt h_sqrt_arg_le
    have h_split :
        Real.sqrt (((2 / B.lam) *
          nirenbergMasterYoungConstant B N hΩ'_compact k * Cχ * Mden2) *
            (Sw + Su + Sf)) =
          C_geom i k * Real.sqrt (Sw + Su + Sf) := by
      rw [Real.sqrt_mul h_coeff_nn, hC_geom_eq]
    calc Real.sqrt ((2 / B.lam) *
            nirenbergMasterYoungConstant B N hΩ'_compact k * G_total)
        ≤ Real.sqrt (((2 / B.lam) *
            nirenbergMasterYoungConstant B N hΩ'_compact k * Cχ * Mden2) *
              (Sw + Su + Sf)) := h_mono
      _ = C_geom i k * Real.sqrt (Sw + Su + Sf) := h_split
  have h_g_g_bd :
      eLpNorm
        (Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (g_g i)) 2
        ((volume : Measure EuclN).restrict Ω'')
      ≤ ENNReal.ofReal (C_geom i k * Real.sqrt (Sw + Su + Sf)) := by
    refine le_trans h_g_g_quant ?_
    exact ENNReal.ofReal_le_ofReal h_sqrt_le
  have hh_ne : h ≠ 0 := abs_ne_zero.mp (ne_of_gt hh_pos)
  have hΩ''_subset_tsupp : Ω'' ⊆ tsupport η := by
    intro x hx
    have hη_x_eq_one : η x = 1 := hη_one_on_Ω'' x hx
    have hη_x_ne : η x ≠ 0 := by rw [hη_x_eq_one]; norm_num
    exact subset_tsupport η (Function.mem_support.mpr hη_x_ne)
  have h_eq_on_Ω'' : ∀ x ∈ Ω'',
      Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (g_g i) x =
      Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h (D.weakPartial i) x := by
    intro x hx
    exact h_diffQuot_g_g_eq_on_tsupport hh_ne hh_le k i x (hΩ''_subset_tsupp hx)
  have h_eLp_eq :
      eLpNorm
        (Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (D.weakPartial i)) 2
        ((volume : Measure EuclN).restrict Ω'') =
      eLpNorm
        (Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (g_g i)) 2
        ((volume : Measure EuclN).restrict Ω'') := by
    refine eLpNorm_congr_ae ?_
    refine (ae_restrict_iff' hΩ''_meas).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro x hx
    exact (h_eq_on_Ω'' x hx).symm
  rw [h_eLp_eq]
  rw [show (∑ l : Fin (Module.finrank ℝ E),
        (eLpNorm (D.weakPartial l) 2
          ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2)
      + (eLpNorm D.uChart 2
          ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2
      + (eLpNorm D.fChart 2
          ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2
      = Sw + Su + Sf from by rw [hSw_def, hSu_def, hSf_def]]
  exact h_g_g_bd

theorem uniform_diffQuot_weakPartial_bound
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_support : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (hN : 0 ≤ N) (h_fderiv_eta : ∀ x : EuclN, ‖fderiv ℝ η x‖ ≤ N)
    {Ω' Ω'' : Set EuclN} (hΩ' : IsOpen Ω')
    (hΩ'_chart : closure Ω' ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hΩ'_compact : IsCompact (closure Ω'))
    (hη_in_Ω' : tsupport η ⊆ Ω')
    {R₀ : ℝ} (hR₀_pos : 0 < R₀)
    (hh_support_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (hη_one_on_Ω'' : ∀ x ∈ Ω'', η x = 1)
    (hΩ''_meas : MeasurableSet Ω'') :
    ∃ MBound : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ,
      (∀ i k, 0 ≤ MBound i k) ∧
      (∀ (i k : Fin (Module.finrank ℝ E)) (h : ℝ),
        0 < |h| → |h| ≤ R₀ →
          eLpNorm
            (Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weakPartial i)) 2
            ((volume : Measure EuclN).restrict Ω'')
          ≤ ENNReal.ofReal (MBound i k)) := by
  classical
  obtain ⟨C_geom, hC_geom_nn, hC_geom⟩ :=
    uniform_diffQuot_weakPartial_bound_quantitative
      (I := I) (M := M) (E := E) (H := H) (g := g) (α := α)
      hη hη_support hη_range hN h_fderiv_eta hΩ' hΩ'_chart hΩ'_compact
      hη_in_Ω' hR₀_pos hh_support_in_Ω' hη_one_on_Ω'' hΩ''_meas
  refine ⟨fun i k => C_geom i k * Real.sqrt (
      (∑ l : Fin (Module.finrank ℝ E),
        (eLpNorm (D.weakPartial l) 2
          ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2)
      + (eLpNorm D.uChart 2
          ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2
      + (eLpNorm D.fChart 2
          ((volume : Measure EuclN).restrict (closure Ω'))).toReal ^ 2),
    fun i k => mul_nonneg (hC_geom_nn i k) (Real.sqrt_nonneg _),
    fun i k h hpos hle => hC_geom D hpos hle⟩

end ChartBilinearH1Compl

end Laplacian
end Analysis
end CalabiYau
