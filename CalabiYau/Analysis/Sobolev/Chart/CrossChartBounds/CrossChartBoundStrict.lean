-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Chart/CrossChartBounds/CrossChartBoundStrict.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Chart.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Group.NullSubmodule
public import Mathlib.Analysis.Normed.Group.Uniform
public import CalabiYau.Analysis.Sobolev.Chart.SmoothDensity.Defs
public import CalabiYau.Analysis.Sobolev.Chart.SmoothDensity.ChartSobolevDensity
public import CalabiYau.Analysis.Sobolev.Chart.ChartTransition.TransitionDiffeo
public import CalabiYau.Analysis.Sobolev.Chart.ChartTransition.ChartPullbackSmooth
public import CalabiYau.Analysis.Sobolev.Euclidean.Density
public import CalabiYau.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev
public import CalabiYau.Analysis.Sobolev.Euclidean.Multiplication.Multiply
public import CalabiYau.Analysis.Sobolev.Chart.RiemannianMeasureComparison
public import CalabiYau.Geometry.Riemannian.Volume.Basic
public import CalabiYau.Analysis.Sobolev.Tools.StrictStrongSupport
public import CalabiYau.Analysis.Sobolev.Approximation.Density.Smooth
public import CalabiYau.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuant

@[expose] public section

-- Private declarations used in public declarations require the compatibility option below.

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace Sobolev

namespace Euclidean

end Euclidean

namespace Chart

variable {E H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem chartTransition_smoothDiffeoBoundedAtOrder_strict
    [I.Boundaryless] (γ α : M)
    {K : Set M} (hK_compact : IsCompact K)
    (hK_γ : K ⊆ (chartAt H γ).source)
    (hK_α : K ⊆ (chartAt H α).source)
    (kmax : ℕ) :
    ∃ (Ω_γα Ω_αγ : Set EuclN) (_hΩ_γα : IsOpen Ω_γα) (_hΩ_αγ : IsOpen Ω_αγ)
      (_hΩ_γα_subset_target : Ω_γα ⊆ chartTargetEuclid (I := I) (M := M) γ)
      (_hΩ_αγ_subset_target : Ω_αγ ⊆ chartTargetEuclid (I := I) (M := M) α)
      (_hΩ_γα_subset_overlap : Ω_γα ⊆ chartOverlapEuclid (I := I) (M := M) γ α)
      (_hΩ_αγ_subset_overlap : Ω_αγ ⊆ chartOverlapEuclid (I := I) (M := M) α γ),
      ((toEuclidean : E ≃L[ℝ] _) ∘ extChartAt I γ) '' K ⊆ Ω_γα ∧
      ∃ (Φ : Sobolev.Euclidean.SmoothDiffeoBoundedAtOrder
          (Module.finrank ℝ E) Ω_γα Ω_αγ kmax),
        (∀ y ∈ Ω_γα,
          Φ.toFun y = chartTransitionEuclid (I := I) (M := M) γ α y) ∧
        (∀ y ∈ Ω_αγ,
          Φ.invFun y = chartTransitionEuclid (I := I) (M := M) α γ y) := by
  classical
  set K_E_γ : Set EuclN :=
    (fun x : M => (toEuclidean (E := E)) (extChartAt I γ x)) '' K with hKEγ_def
  set K_E_α : Set EuclN :=
    (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K with hKEα_def
  have hKEγ_compact : IsCompact K_E_γ :=
    kEuclid_compact (I := I) (M := M) γ hK_compact hK_γ
  have hKEγ_subset_overlap_γα : K_E_γ ⊆ chartOverlapEuclid (I := I) (M := M) γ α :=
    kEuclid_subset_overlap (I := I) (M := M) γ α hK_γ hK_α
  have hOverlap_γα_open : IsOpen (chartOverlapEuclid (I := I) (M := M) γ α) :=
    chartOverlapEuclid_isOpen (I := I) (M := M) γ α
  have hKEα_compact : IsCompact K_E_α :=
    kEuclid_compact (I := I) (M := M) α hK_compact hK_α
  have hKEα_subset_overlap_αγ : K_E_α ⊆ chartOverlapEuclid (I := I) (M := M) α γ :=
    kEuclid_subset_overlap (I := I) (M := M) α γ hK_α hK_γ
  have hOverlap_αγ_open : IsOpen (chartOverlapEuclid (I := I) (M := M) α γ) :=
    chartOverlapEuclid_isOpen (I := I) (M := M) α γ
  obtain ⟨δ_γ, η_γ, hδ_γ_pos, hδγ_subset, hη_γ_smooth, hη_γ_compact, _hη_γ_range,
      hη_γ_one, hη_γ_support⟩ :=
    Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      (d := Module.finrank ℝ E)
      hKEγ_compact hOverlap_γα_open hKEγ_subset_overlap_γα
  have hδ_γ_half_pos : 0 < δ_γ / 2 := by linarith
  set Ω_γα : Set EuclN := Metric.thickening (δ_γ / 2) K_E_γ with hΩγα_def
  have hΩγα_open : IsOpen Ω_γα := Metric.isOpen_thickening
  have hKEγ_subset_Ωγα : K_E_γ ⊆ Ω_γα := Metric.self_subset_thickening hδ_γ_half_pos K_E_γ
  have hΩγα_closure_subset_cthick_half :
      closure Ω_γα ⊆ Metric.cthickening (δ_γ / 2) K_E_γ :=
    Metric.closure_thickening_subset_cthickening (δ_γ / 2) K_E_γ
  have hcthick_half_subset_full :
      Metric.cthickening (δ_γ / 2) K_E_γ ⊆ Metric.cthickening δ_γ K_E_γ :=
    Metric.cthickening_mono (by linarith : δ_γ / 2 ≤ δ_γ) K_E_γ
  have hΩγα_closure_subset_cthick :
      closure Ω_γα ⊆ Metric.cthickening δ_γ K_E_γ :=
    hΩγα_closure_subset_cthick_half.trans hcthick_half_subset_full
  have hΩγα_closure_subset_overlap : closure Ω_γα ⊆ chartOverlapEuclid (I := I) (M := M) γ α :=
    hΩγα_closure_subset_cthick.trans hδγ_subset
  have hcthick_compact : IsCompact (Metric.cthickening (δ_γ / 2) K_E_γ) :=
    hKEγ_compact.cthickening
  have hΩγα_closure_compact : IsCompact (closure Ω_γα) :=
    hcthick_compact.of_isClosed_subset isClosed_closure hΩγα_closure_subset_cthick_half
  have hΩγα_subset_cthick : Ω_γα ⊆ Metric.cthickening δ_γ K_E_γ := by
    refine subset_trans (Metric.thickening_subset_cthickening (δ_γ / 2) K_E_γ) ?_
    exact hcthick_half_subset_full
  have hΩγα_subset_target : Ω_γα ⊆ chartTargetEuclid (I := I) (M := M) γ := by
    intro y hy
    have hy_overlap : y ∈ chartOverlapEuclid (I := I) (M := M) γ α := by
      have : y ∈ closure Ω_γα := subset_closure hy
      exact hΩγα_closure_subset_overlap this
    exact chartOverlapEuclid_subset_chartTarget (I := I) (M := M) γ α hy_overlap
  set c_γ : EuclN := chartCenterEuclid (I := I) (M := M) α with hcγ_def
  set T_γα : EuclN → EuclN :=
    chartTransitionExtended (I := I) (M := M) γ α η_γ c_γ with hTγα_def
  have hT_γα_smooth : ContDiff ℝ (⊤ : ℕ∞) T_γα :=
    chartTransitionExtended_contDiff (I := I) (M := M) γ α
      hη_γ_smooth hη_γ_support c_γ
  have hT_γα_eq_on_Ωγα : ∀ y ∈ Ω_γα,
      T_γα y = chartTransitionEuclid (I := I) (M := M) γ α y := by
    intro y hy
    have hy_cthick : y ∈ Metric.cthickening δ_γ K_E_γ := hΩγα_subset_cthick hy
    have hηy : η_γ y = 1 := hη_γ_one y hy_cthick
    exact chartTransitionExtended_eq_chartTransition_on_eta_eq_one
      (I := I) (M := M) γ α c_γ hηy
  set Ω_αγ : Set EuclN :=
    (chartTransitionEuclid (I := I) (M := M) γ α) '' Ω_γα with hΩαγ_def
  have hΩαγ_subset_overlap_αγ : Ω_αγ ⊆ chartOverlapEuclid (I := I) (M := M) α γ := by
    intro z hz
    rcases hz with ⟨y, hy_Ωγα, hyz⟩
    have hy_overlap : y ∈ chartOverlapEuclid (I := I) (M := M) γ α := by
      have : y ∈ closure Ω_γα := subset_closure hy_Ωγα
      exact hΩγα_closure_subset_overlap this
    rw [← hyz]
    exact chartTransitionEuclid_mapsTo_overlap (I := I) (M := M) γ α hy_overlap
  have hΩαγ_subset_target : Ω_αγ ⊆ chartTargetEuclid (I := I) (M := M) α := by
    refine hΩαγ_subset_overlap_αγ.trans ?_
    exact chartOverlapEuclid_subset_chartTarget (I := I) (M := M) α γ
  have hΩαγ_eq_preimage :
      Ω_αγ = (chartTransitionEuclid (I := I) (M := M) α γ ⁻¹' Ω_γα) ∩
              chartOverlapEuclid (I := I) (M := M) α γ := by
    ext z
    refine ⟨?_, ?_⟩
    · intro hz
      rcases hz with ⟨y, hy_Ωγα, hyz⟩
      have hy_overlap : y ∈ chartOverlapEuclid (I := I) (M := M) γ α := by
        have hy_cl : y ∈ closure Ω_γα := subset_closure hy_Ωγα
        exact hΩγα_closure_subset_overlap hy_cl
      have hz_overlap : z ∈ chartOverlapEuclid (I := I) (M := M) α γ := by
        rw [← hyz]
        exact chartTransitionEuclid_mapsTo_overlap (I := I) (M := M) γ α hy_overlap
      refine ⟨?_, hz_overlap⟩
      have h_inv : chartTransitionEuclid (I := I) (M := M) α γ z = y := by
        rw [← hyz]
        exact chartTransitionEuclid_left_inv (I := I) (M := M) γ α hy_overlap
      simp only [Set.mem_preimage, h_inv]
      exact hy_Ωγα
    · rintro ⟨hz_pre, hz_overlap⟩
      simp only [Set.mem_preimage] at hz_pre
      have h_T_αγ_z_overlap : chartTransitionEuclid (I := I) (M := M) α γ z ∈
          chartOverlapEuclid (I := I) (M := M) γ α := by
        have : chartTransitionEuclid (I := I) (M := M) α γ z ∈ closure Ω_γα :=
          subset_closure hz_pre
        exact hΩγα_closure_subset_overlap this
      have h_left_inv :
          chartTransitionEuclid (I := I) (M := M) γ α
            (chartTransitionEuclid (I := I) (M := M) α γ z) = z :=
        chartTransitionEuclid_left_inv (I := I) (M := M) α γ hz_overlap
      refine ⟨chartTransitionEuclid (I := I) (M := M) α γ z, hz_pre, h_left_inv⟩
  have hT_αγ_continuousOn :
      ContinuousOn (chartTransitionEuclid (I := I) (M := M) α γ)
        (chartOverlapEuclid (I := I) (M := M) α γ) :=
    (chartTransitionEuclid_contDiffOn_overlap (I := I) (M := M) α γ).continuousOn
  have hΩαγ_open : IsOpen Ω_αγ := by
    rw [hΩαγ_eq_preimage]
    rw [Set.inter_comm]
    exact hT_αγ_continuousOn.isOpen_inter_preimage hOverlap_αγ_open hΩγα_open
  set L_αγ : Set EuclN :=
    (chartTransitionEuclid (I := I) (M := M) γ α) '' (closure Ω_γα) with hLαγ_def
  have hL_αγ_compact : IsCompact L_αγ :=
    hΩγα_closure_compact.image_of_continuousOn
      ((chartTransitionEuclid_contDiffOn_overlap
          (I := I) (M := M) γ α).continuousOn.mono hΩγα_closure_subset_overlap)
  have hL_αγ_subset_overlap_αγ : L_αγ ⊆ chartOverlapEuclid (I := I) (M := M) α γ := by
    intro z hz
    rcases hz with ⟨y, hy_cl, hyz⟩
    rw [← hyz]
    exact chartTransitionEuclid_mapsTo_overlap (I := I) (M := M) γ α
      (hΩγα_closure_subset_overlap hy_cl)
  have hΩαγ_subset_Lαγ : Ω_αγ ⊆ L_αγ := by
    intro z hz
    rcases hz with ⟨y, hy_Ωγα, hyz⟩
    refine ⟨y, subset_closure hy_Ωγα, hyz⟩
  obtain ⟨δ_α, η_α, hδ_α_pos, hδα_subset, hη_α_smooth, hη_α_compact, _hη_α_range,
      hη_α_one, hη_α_support⟩ :=
    Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      (d := Module.finrank ℝ E)
      hL_αγ_compact hOverlap_αγ_open hL_αγ_subset_overlap_αγ
  have hL_αγ_subset_cthick_α : L_αγ ⊆ Metric.cthickening δ_α L_αγ :=
    Metric.self_subset_cthickening L_αγ
  have hΩαγ_subset_cthick_α : Ω_αγ ⊆ Metric.cthickening δ_α L_αγ :=
    hΩαγ_subset_Lαγ.trans hL_αγ_subset_cthick_α
  set c_α : EuclN := chartCenterEuclid (I := I) (M := M) γ with hcα_def
  set T_αγ : EuclN → EuclN :=
    chartTransitionExtended (I := I) (M := M) α γ η_α c_α with hTαγ_def
  have hT_αγ_smooth : ContDiff ℝ (⊤ : ℕ∞) T_αγ :=
    chartTransitionExtended_contDiff (I := I) (M := M) α γ
      hη_α_smooth hη_α_support c_α
  have hT_αγ_eq_on_Ωαγ : ∀ z ∈ Ω_αγ,
      T_αγ z = chartTransitionEuclid (I := I) (M := M) α γ z := by
    intro z hz
    have hz_cthick : z ∈ Metric.cthickening δ_α L_αγ := hΩαγ_subset_cthick_α hz
    have hηz : η_α z = 1 := hη_α_one z hz_cthick
    exact chartTransitionExtended_eq_chartTransition_on_eta_eq_one
      (I := I) (M := M) α γ c_α hηz
  have hBijOn_T_γα : Set.BijOn T_γα Ω_γα Ω_αγ := by
    refine ⟨?_, ?_, ?_⟩
    · intro y hy
      rw [hT_γα_eq_on_Ωγα y hy]
      exact ⟨y, hy, rfl⟩
    · intro y₁ hy₁ y₂ hy₂ heq
      rw [hT_γα_eq_on_Ωγα y₁ hy₁, hT_γα_eq_on_Ωγα y₂ hy₂] at heq
      have hy₁_overlap : y₁ ∈ chartOverlapEuclid (I := I) (M := M) γ α :=
        hΩγα_closure_subset_overlap (subset_closure hy₁)
      have hy₂_overlap : y₂ ∈ chartOverlapEuclid (I := I) (M := M) γ α :=
        hΩγα_closure_subset_overlap (subset_closure hy₂)
      exact chartTransitionEuclid_injOn_overlap (I := I) (M := M) γ α
        hy₁_overlap hy₂_overlap heq
    · intro z hz
      rcases hz with ⟨y, hy_Ωγα, hyz⟩
      refine ⟨y, hy_Ωγα, ?_⟩
      rw [hT_γα_eq_on_Ωγα y hy_Ωγα]; exact hyz
  have hBijOn_T_αγ : Set.BijOn T_αγ Ω_αγ Ω_γα := by
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      rw [hT_αγ_eq_on_Ωαγ z hz]
      rcases hz with ⟨y, hy_Ωγα, hyz⟩
      have hy_overlap : y ∈ chartOverlapEuclid (I := I) (M := M) γ α :=
        hΩγα_closure_subset_overlap (subset_closure hy_Ωγα)
      have h_inv : chartTransitionEuclid (I := I) (M := M) α γ z = y := by
        rw [← hyz]
        exact chartTransitionEuclid_left_inv (I := I) (M := M) γ α hy_overlap
      rw [h_inv]; exact hy_Ωγα
    · intro z₁ hz₁ z₂ hz₂ heq
      rw [hT_αγ_eq_on_Ωαγ z₁ hz₁, hT_αγ_eq_on_Ωαγ z₂ hz₂] at heq
      have hz₁_overlap : z₁ ∈ chartOverlapEuclid (I := I) (M := M) α γ :=
        hΩαγ_subset_overlap_αγ hz₁
      have hz₂_overlap : z₂ ∈ chartOverlapEuclid (I := I) (M := M) α γ :=
        hΩαγ_subset_overlap_αγ hz₂
      exact chartTransitionEuclid_injOn_overlap (I := I) (M := M) α γ
        hz₁_overlap hz₂_overlap heq
    · intro y hy_Ωγα
      have hy_overlap : y ∈ chartOverlapEuclid (I := I) (M := M) γ α :=
        hΩγα_closure_subset_overlap (subset_closure hy_Ωγα)
      refine ⟨chartTransitionEuclid (I := I) (M := M) γ α y, ?_, ?_⟩
      · exact ⟨y, hy_Ωγα, rfl⟩
      · have h_z_in_Ωαγ : chartTransitionEuclid (I := I) (M := M) γ α y ∈ Ω_αγ :=
          ⟨y, hy_Ωγα, rfl⟩
        rw [hT_αγ_eq_on_Ωαγ _ h_z_in_Ωαγ]
        exact chartTransitionEuclid_left_inv (I := I) (M := M) γ α hy_overlap
  have hLeft_inv : Set.LeftInvOn T_αγ T_γα Ω_γα := by
    intro y hy
    rw [hT_γα_eq_on_Ωγα y hy]
    have hy_overlap : y ∈ chartOverlapEuclid (I := I) (M := M) γ α :=
      hΩγα_closure_subset_overlap (subset_closure hy)
    have h_T_γα_y_in_Ωαγ : chartTransitionEuclid (I := I) (M := M) γ α y ∈ Ω_αγ :=
      ⟨y, hy, rfl⟩
    rw [hT_αγ_eq_on_Ωαγ _ h_T_γα_y_in_Ωαγ]
    exact chartTransitionEuclid_left_inv (I := I) (M := M) γ α hy_overlap
  have hRight_inv : Set.RightInvOn T_αγ T_γα Ω_αγ := by
    intro z hz
    have hz_orig : z ∈ Ω_αγ := hz
    rcases hz with ⟨y, hy_Ωγα, hyz⟩
    have hy_overlap : y ∈ chartOverlapEuclid (I := I) (M := M) γ α :=
      hΩγα_closure_subset_overlap (subset_closure hy_Ωγα)
    rw [hT_αγ_eq_on_Ωαγ _ hz_orig]
    have h_T_αγ_z_eq_y : chartTransitionEuclid (I := I) (M := M) α γ z = y := by
      rw [← hyz]
      exact chartTransitionEuclid_left_inv (I := I) (M := M) γ α hy_overlap
    rw [h_T_αγ_z_eq_y]
    rw [hT_γα_eq_on_Ωγα y hy_Ωγα]
    exact hyz
  obtain ⟨B_γ, hBγ_pos, hBγ_bound⟩ :=
    chartTransitionExtended_iter_deriv_bound (I := I) (M := M) γ α
      hη_γ_smooth hη_γ_compact hη_γ_support c_γ kmax
  obtain ⟨B_α, hBα_pos, hBα_bound⟩ :=
    chartTransitionExtended_iter_deriv_bound (I := I) (M := M) α γ
      hη_α_smooth hη_α_compact hη_α_support c_α kmax
  set B : ℝ := max B_γ B_α with hB_def
  have hB_pos : 0 < B := lt_of_lt_of_le hBγ_pos (le_max_left _ _)
  have hB_γ_bound : ∀ i, i ≤ kmax → ∀ x : EuclN,
      ‖iteratedFDeriv ℝ i T_γα x‖ ≤ B := fun i hi x =>
    (hBγ_bound i hi x).trans (le_max_left _ _)
  have hB_α_bound : ∀ i, i ≤ kmax → ∀ x : EuclN,
      ‖iteratedFDeriv ℝ i T_αγ x‖ ≤ B := fun i hi x =>
    (hBα_bound i hi x).trans (le_max_right _ _)
  by_cases hΩγα_empty : Ω_γα = ∅
  · have hKEγ_empty : K_E_γ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      have : y ∈ Ω_γα := hKEγ_subset_Ωγα hy
      rw [hΩγα_empty] at this
      exact Set.notMem_empty y this
    have hΩαγ_empty : Ω_αγ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      rcases hz with ⟨y, hy, _⟩
      rw [hΩγα_empty] at hy
      exact Set.notMem_empty y hy
    have hΩγα_subset_overlap : Ω_γα ⊆ chartOverlapEuclid (I := I) (M := M) γ α := by
      intro y hy
      have : y ∈ closure Ω_γα := subset_closure hy
      exact hΩγα_closure_subset_overlap this
    refine ⟨Ω_γα, Ω_αγ, hΩγα_open, hΩαγ_open, hΩγα_subset_target, hΩαγ_subset_target,
      hΩγα_subset_overlap, hΩαγ_subset_overlap_αγ, ?_, ?_⟩
    · intro y hy
      rcases hy with ⟨x, hxK, hxy⟩
      simp only [Function.comp_apply] at hxy
      have hxK_E_γ : (toEuclidean (E := E)) (extChartAt I γ x) ∈ K_E_γ := ⟨x, hxK, rfl⟩
      have : (toEuclidean (E := E)) (extChartAt I γ x) ∈ Ω_γα :=
        hKEγ_subset_Ωγα hxK_E_γ
      rw [hxy] at this
      exact this
    refine ⟨{
      toFun := T_γα,
      invFun := T_αγ,
      toFun_smooth := hT_γα_smooth,
      invFun_smooth := hT_αγ_smooth,
      bijOn := hBijOn_T_γα,
      invFun_bijOn := hBijOn_T_αγ,
      left_inv := hLeft_inv,
      right_inv := hRight_inv,
      derivBound := B,
      deriv_bound_pos := hB_pos,
      iter_deriv_bounded_at := hB_γ_bound,
      iter_deriv_invFun_bounded_at := hB_α_bound,
      jacobianLowerBound := 1,
      jacobian_lower_bound_pos := one_pos,
      jacobian_lower := ?_
    }, ?_, ?_⟩
    · intro x hx
      rw [hΩγα_empty] at hx
      exact (Set.notMem_empty x hx).elim
    · intro y hy
      change T_γα y = chartTransitionEuclid (I := I) (M := M) γ α y
      exact hT_γα_eq_on_Ωγα y hy
    · intro z hz
      change T_αγ z = chartTransitionEuclid (I := I) (M := M) α γ z
      exact hT_αγ_eq_on_Ωαγ z hz
  · have hΩγα_nonempty : Ω_γα.Nonempty := Set.nonempty_iff_ne_empty.mpr hΩγα_empty
    have hclosure_nonempty : (closure Ω_γα).Nonempty := hΩγα_nonempty.mono subset_closure
    have h_abs_det_pos_on_overlap : ∀ y ∈ chartOverlapEuclid (I := I) (M := M) γ α,
        0 < |(fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y).det| := by
      intro y hy
      have hT_γα_chart : DifferentiableAt ℝ
          (chartTransitionEuclid (I := I) (M := M) γ α) y := by
        have h_open : IsOpen (chartOverlapEuclid (I := I) (M := M) γ α) :=
          hOverlap_γα_open
        have h_smooth : ContDiffOn ℝ (⊤ : ℕ∞)
            (chartTransitionEuclid (I := I) (M := M) γ α)
            (chartOverlapEuclid (I := I) (M := M) γ α) :=
          chartTransitionEuclid_contDiffOn_overlap (I := I) (M := M) γ α
        have h_diffOn : DifferentiableOn ℝ
            (chartTransitionEuclid (I := I) (M := M) γ α)
            (chartOverlapEuclid (I := I) (M := M) γ α) :=
          h_smooth.differentiableOn (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)
        exact (h_diffOn y hy).differentiableAt (h_open.mem_nhds hy)
      have hT_αγ_at : DifferentiableAt ℝ
          (chartTransitionEuclid (I := I) (M := M) α γ)
          (chartTransitionEuclid (I := I) (M := M) γ α y) := by
        have hy_α : chartTransitionEuclid (I := I) (M := M) γ α y ∈
            chartOverlapEuclid (I := I) (M := M) α γ :=
          chartTransitionEuclid_mapsTo_overlap (I := I) (M := M) γ α hy
        have h_open : IsOpen (chartOverlapEuclid (I := I) (M := M) α γ) :=
          hOverlap_αγ_open
        have h_smooth : ContDiffOn ℝ (⊤ : ℕ∞)
            (chartTransitionEuclid (I := I) (M := M) α γ)
            (chartOverlapEuclid (I := I) (M := M) α γ) :=
          chartTransitionEuclid_contDiffOn_overlap (I := I) (M := M) α γ
        have h_diffOn : DifferentiableOn ℝ
            (chartTransitionEuclid (I := I) (M := M) α γ)
            (chartOverlapEuclid (I := I) (M := M) α γ) :=
          h_smooth.differentiableOn (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)
        exact (h_diffOn _ hy_α).differentiableAt (h_open.mem_nhds hy_α)
      have h_evt : (fun z => chartTransitionEuclid (I := I) (M := M) α γ
            (chartTransitionEuclid (I := I) (M := M) γ α z))
          =ᶠ[𝓝 y] (fun z : EuclN => z) := by
        refine Filter.eventually_of_mem (hOverlap_γα_open.mem_nhds hy) ?_
        intro z hz
        exact chartTransitionEuclid_left_inv (I := I) (M := M) γ α hz
      have h_fderiv_id :
          fderiv ℝ (fun z => chartTransitionEuclid (I := I) (M := M) α γ
              (chartTransitionEuclid (I := I) (M := M) γ α z)) y =
            ContinuousLinearMap.id ℝ EuclN := by
        rw [h_evt.fderiv_eq]; exact fderiv_fun_id
      have h_fderiv_comp :
          fderiv ℝ (fun z => chartTransitionEuclid (I := I) (M := M) α γ
              (chartTransitionEuclid (I := I) (M := M) γ α z)) y =
            (fderiv ℝ (chartTransitionEuclid (I := I) (M := M) α γ)
                (chartTransitionEuclid (I := I) (M := M) γ α y)).comp
              (fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y) :=
        fderiv_comp y hT_αγ_at hT_γα_chart
      have h_comp_eq :
          (fderiv ℝ (chartTransitionEuclid (I := I) (M := M) α γ)
              (chartTransitionEuclid (I := I) (M := M) γ α y)).comp
            (fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y) =
          ContinuousLinearMap.id ℝ EuclN := by
        rw [← h_fderiv_comp]; exact h_fderiv_id
      have h_det_eq :
          (fderiv ℝ (chartTransitionEuclid (I := I) (M := M) α γ)
              (chartTransitionEuclid (I := I) (M := M) γ α y)).det *
          (fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y).det = 1 := by
        have h_lin :
            ((fderiv ℝ (chartTransitionEuclid (I := I) (M := M) α γ)
                (chartTransitionEuclid (I := I) (M := M) γ α y)).comp
              (fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y) :
                EuclN →ₗ[ℝ] EuclN) =
            ((fderiv ℝ (chartTransitionEuclid (I := I) (M := M) α γ)
                (chartTransitionEuclid (I := I) (M := M) γ α y) :
                  EuclN →ₗ[ℝ] EuclN)).comp
              ((fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y) :
                  EuclN →ₗ[ℝ] EuclN) := rfl
        have h_det_id :
            ((ContinuousLinearMap.id ℝ EuclN) : EuclN →ₗ[ℝ] EuclN).det = 1 := by
          change LinearMap.det (LinearMap.id : EuclN →ₗ[ℝ] EuclN) = 1
          exact LinearMap.det_id
        have h_det_comp_lin :
            LinearMap.det
              (((fderiv ℝ (chartTransitionEuclid (I := I) (M := M) α γ)
                  (chartTransitionEuclid (I := I) (M := M) γ α y)) :
                    EuclN →ₗ[ℝ] EuclN).comp
                ((fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y) :
                    EuclN →ₗ[ℝ] EuclN)) =
              LinearMap.det
                ((fderiv ℝ (chartTransitionEuclid (I := I) (M := M) α γ)
                  (chartTransitionEuclid (I := I) (M := M) γ α y)) :
                    EuclN →ₗ[ℝ] EuclN) *
              LinearMap.det
                ((fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y) :
                    EuclN →ₗ[ℝ] EuclN) := LinearMap.det_comp _ _
        have hcomp_det :
            LinearMap.det
              (((fderiv ℝ (chartTransitionEuclid (I := I) (M := M) α γ)
                  (chartTransitionEuclid (I := I) (M := M) γ α y)).comp
                (fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y)) :
                  EuclN →ₗ[ℝ] EuclN) =
              LinearMap.det ((ContinuousLinearMap.id ℝ EuclN) : EuclN →ₗ[ℝ] EuclN) := by
          rw [h_comp_eq]
        rw [h_lin, h_det_comp_lin, h_det_id] at hcomp_det
        change (fderiv ℝ (chartTransitionEuclid (I := I) (M := M) α γ)
            (chartTransitionEuclid (I := I) (M := M) γ α y)).det *
            (fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y).det = 1
        exact hcomp_det
      have h_ne_zero : (fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y).det ≠ 0 := by
        intro h_zero
        rw [h_zero, mul_zero] at h_det_eq
        exact zero_ne_one h_det_eq
      exact abs_pos.mpr h_ne_zero
    have h_abs_det_continuousOn :
        ContinuousOn
          (fun y => |(fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y).det|)
          (closure Ω_γα) := by
      have h_smooth : ContDiffOn ℝ (⊤ : ℕ∞)
          (chartTransitionEuclid (I := I) (M := M) γ α)
          (chartOverlapEuclid (I := I) (M := M) γ α) :=
        chartTransitionEuclid_contDiffOn_overlap (I := I) (M := M) γ α
      have h_cont_fderiv : ContinuousOn
          (fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α))
          (chartOverlapEuclid (I := I) (M := M) γ α) :=
        h_smooth.continuousOn_fderiv_of_isOpen hOverlap_γα_open
          (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
      have h_cont_det : Continuous (fun A : EuclN →L[ℝ] EuclN => A.det) :=
        ContinuousLinearMap.continuous_det
      have h_cont_abs : Continuous (fun r : ℝ => |r|) := continuous_abs
      exact ((h_cont_abs.comp h_cont_det).continuousOn.comp h_cont_fderiv
        (Set.mapsTo_univ _ _)).mono hΩγα_closure_subset_overlap
    have h_abs_det_pos_on_closure : ∀ y ∈ closure Ω_γα,
        0 < |(fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y).det| := by
      intro y hy
      exact h_abs_det_pos_on_overlap y (hΩγα_closure_subset_overlap hy)
    obtain ⟨y₀, hy₀_cl, hy₀_min⟩ :=
      hΩγα_closure_compact.exists_isMinOn hclosure_nonempty h_abs_det_continuousOn
    set J : ℝ := |(fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y₀).det| with hJ_def
    have hJ_pos : 0 < J := h_abs_det_pos_on_closure y₀ hy₀_cl
    have hη_γ_eq_one_on_thick : ∀ y ∈ Metric.thickening δ_γ K_E_γ, η_γ y = 1 := by
      intro y hy
      have hy_cthick : y ∈ Metric.cthickening δ_γ K_E_γ :=
        Metric.thickening_subset_cthickening δ_γ K_E_γ hy
      exact hη_γ_one y hy_cthick
    have hΩγα_subset_thick_γ : Ω_γα ⊆ Metric.thickening δ_γ K_E_γ := by
      refine subset_trans ?_ (Metric.thickening_mono (by linarith : δ_γ / 2 ≤ δ_γ) K_E_γ)
      rfl
    have hT_γα_fderiv_eq : ∀ y ∈ Ω_γα,
        fderiv ℝ T_γα y = fderiv ℝ (chartTransitionEuclid (I := I) (M := M) γ α) y := by
      intro y hy
      have h_evt : T_γα =ᶠ[𝓝 y] (chartTransitionEuclid (I := I) (M := M) γ α) := by
        have h_open_thick : IsOpen (Metric.thickening δ_γ K_E_γ) := Metric.isOpen_thickening
        have hy_thick : y ∈ Metric.thickening δ_γ K_E_γ := hΩγα_subset_thick_γ hy
        refine Filter.eventually_of_mem (h_open_thick.mem_nhds hy_thick) ?_
        intro y' hy'
        have hηy' : η_γ y' = 1 := hη_γ_eq_one_on_thick y' hy'
        exact chartTransitionExtended_eq_chartTransition_on_eta_eq_one
          (I := I) (M := M) γ α c_γ hηy'
      exact h_evt.fderiv_eq
    have hJ_lower : ∀ y ∈ Ω_γα, J ≤ |(fderiv ℝ T_γα y).det| := by
      intro y hy
      rw [hT_γα_fderiv_eq y hy]
      exact hy₀_min (subset_closure hy)
    have hΩγα_subset_overlap : Ω_γα ⊆ chartOverlapEuclid (I := I) (M := M) γ α := by
      intro y hy
      have : y ∈ closure Ω_γα := subset_closure hy
      exact hΩγα_closure_subset_overlap this
    refine ⟨Ω_γα, Ω_αγ, hΩγα_open, hΩαγ_open, hΩγα_subset_target, hΩαγ_subset_target,
      hΩγα_subset_overlap, hΩαγ_subset_overlap_αγ, ?_, ?_⟩
    · intro y hy
      rcases hy with ⟨x, hxK, hxy⟩
      simp only [Function.comp_apply] at hxy
      have hxK_E_γ : (toEuclidean (E := E)) (extChartAt I γ x) ∈ K_E_γ := ⟨x, hxK, rfl⟩
      have : (toEuclidean (E := E)) (extChartAt I γ x) ∈ Ω_γα :=
        hKEγ_subset_Ωγα hxK_E_γ
      rw [hxy] at this
      exact this
    refine ⟨{
      toFun := T_γα,
      invFun := T_αγ,
      toFun_smooth := hT_γα_smooth,
      invFun_smooth := hT_αγ_smooth,
      bijOn := hBijOn_T_γα,
      invFun_bijOn := hBijOn_T_αγ,
      left_inv := hLeft_inv,
      right_inv := hRight_inv,
      derivBound := B,
      deriv_bound_pos := hB_pos,
      iter_deriv_bounded_at := hB_γ_bound,
      iter_deriv_invFun_bounded_at := hB_α_bound,
      jacobianLowerBound := J,
      jacobian_lower_bound_pos := hJ_pos,
      jacobian_lower := hJ_lower
    }, ?_, ?_⟩
    · intro y hy
      change T_γα y = chartTransitionEuclid (I := I) (M := M) γ α y
      exact hT_γα_eq_on_Ωγα y hy
    · intro z hz
      change T_αγ z = chartTransitionEuclid (I := I) (M := M) α γ z
      exact hT_αγ_eq_on_Ωαγ z hz

lemma chartPushed_chartPullback_zero_of_K_M_empty
    [T2Space M] [SigmaCompactSpace M]
    (γ α : M) {K_α : Set M}
    (hK_α_in_α : K_α ⊆ (chartAt H α).source)
    (hKM_empty : K_α ∩ tsupport
      ((CalabiYau.RiemannianVolume.chartAtlasPOU I M γ
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) = ∅)
    {χ : EuclN → ℝ}
    (hχ_support : tsupport χ ⊆
      (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_α) :
    chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) γ
        (chartPullback I α χ) =
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  funext y
  unfold chartPushed
  set z : M := (extChartAt I γ).symm ((toEuclidean (E := E)).symm y) with hz_def
  by_cases hρ_zero : (CalabiYau.RiemannianVolume.chartAtlasPOU I M γ
      : C^∞⟮I, M; ℝ⟯) z = 0
  · rw [hρ_zero]; ring
  · have hz_in_support_γ : z ∈ tsupport
        ((CalabiYau.RiemannianVolume.chartAtlasPOU I M γ
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
      have h_in : z ∈ Function.support
          ((CalabiYau.RiemannianVolume.chartAtlasPOU I M γ
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
        simp only [Function.mem_support, ne_eq]; exact hρ_zero
      exact subset_tsupport _ h_in
    by_cases hpb_zero : chartPullback I α χ z = 0
    · rw [hpb_zero]; ring
    · exfalso
      have hz_chartα : z ∈ (chartAt H α).source := by
        by_contra hcontra
        apply hpb_zero
        exact chartPullback_apply_of_notMem (I := I) (M := M) α χ hcontra
      rw [chartPullback_apply_of_mem (I := I) (M := M) α χ hz_chartα] at hpb_zero
      have h_arg_in_tsupp_χ : (toEuclidean (E := E)) (extChartAt I α z) ∈ tsupport χ := by
        have : (toEuclidean (E := E)) (extChartAt I α z) ∈ Function.support χ := by
          simp only [Function.mem_support, ne_eq]; exact hpb_zero
        exact subset_tsupport _ this
      have h_arg_in_image_K_α : (toEuclidean (E := E)) (extChartAt I α z) ∈
          (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_α :=
        hχ_support h_arg_in_tsupp_χ
      obtain ⟨x', hx'_in_K_α, hx'_eq⟩ := h_arg_in_image_K_α
      have hx'_chartα : x' ∈ (chartAt H α).source := hK_α_in_α hx'_in_K_α
      have h_eq_chart_α : extChartAt I α x' = extChartAt I α z := by
        have : (toEuclidean (E := E)) (extChartAt I α x') =
            (toEuclidean (E := E)) (extChartAt I α z) := hx'_eq
        exact (toEuclidean (E := E)).injective this
      have hz_eq_x' : z = x' := by
        have hz_extChart_source : z ∈ (extChartAt I α).source := by
          rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
            (I := I) (M := M)]
          exact hz_chartα
        have hx'_extChart_source : x' ∈ (extChartAt I α).source := by
          rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
            (I := I) (M := M)]
          exact hx'_chartα
        have h_inj := (extChartAt I α).injOn hx'_extChart_source hz_extChart_source
          h_eq_chart_α
        exact h_inj.symm
      have hz_in_K_α : z ∈ K_α := by rw [hz_eq_x']; exact hx'_in_K_α
      have hz_in_K_M : z ∈ K_α ∩ tsupport
          ((CalabiYau.RiemannianVolume.chartAtlasPOU I M γ
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) := ⟨hz_in_K_α, hz_in_support_γ⟩
      rw [hKM_empty] at hz_in_K_M
      exact Set.notMem_empty z hz_in_K_M

end Chart

end Sobolev
