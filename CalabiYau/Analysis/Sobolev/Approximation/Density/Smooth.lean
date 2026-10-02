-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Approximation/Density/Smooth.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Approximation.Density.Preliminaries
public import CalabiYau.Analysis.Sobolev.Chart.CrossChartBounds.CrossChartBound
public import CalabiYau.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuant

@[expose] public section

-- Private declarations used in public declarations require the compatibility option below.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace Sobolev
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

def chartImagePOUTsupport
    [T2Space M] [SigmaCompactSpace M] (α : M) : Set EuclN :=
  toEuclidean '' ((extChartAt I α) ''
    (tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ)))

lemma chartImagePOUTsupport_isCompact
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] (α : M) :
    IsCompact (chartImagePOUTsupport (I := I) (M := M) α) := by
  set Tα : Set M := tsupport
    ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hTα_def
  have hTα_compact : IsCompact Tα := (isClosed_tsupport _).isCompact
  have hTα_chart_source : Tα ⊆ (chartAt H α).source :=
    CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M α
  have hTα_ext_source : Tα ⊆ (extChartAt I α).source := by
    intro x hx
    rw [extChartAt_source]
    exact hTα_chart_source hx
  have hcont_ext : ContinuousOn (extChartAt I α) Tα :=
    (continuousOn_extChartAt α).mono hTα_ext_source
  have hImage_ext_compact : IsCompact ((extChartAt I α) '' Tα) :=
    hTα_compact.image_of_continuousOn hcont_ext
  exact hImage_ext_compact.image (toEuclidean (E := E)).continuous

lemma chartImagePOUTsupport_subset_target
    [T2Space M] [SigmaCompactSpace M] (α : M) :
    chartImagePOUTsupport (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  intro y hy
  unfold chartImagePOUTsupport at hy
  obtain ⟨z, ⟨x, hx_support, hxz⟩, hzy⟩ := hy
  have hx_chart : x ∈ (chartAt H α).source :=
    CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M α hx_support
  have hx_ext : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hx_chart
  have hz_target : z ∈ (extChartAt I α).target := by
    rw [← hxz]; exact (extChartAt I α).map_source hx_ext
  exact ⟨z, hz_target, hzy⟩

lemma chartPushed_eq_zero_off_chartImagePOUTsupport
    [T2Space M] [SigmaCompactSpace M] (α : M) (u : M → ℝ) {y : EuclN}
    (hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α)
    (hy_off : y ∉ chartImagePOUTsupport (I := I) (M := M) α) :
    chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u y = 0 :=
  chartPushed_support_subset_compact_in_target (I := I) (M := M) α u y
    hy_target hy_off

theorem exists_chartCutoff
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (α : M) :
    ∃ (δ : ℝ) (η : EuclN → ℝ),
      0 < δ ∧
      Metric.cthickening δ (chartImagePOUTsupport (I := I) (M := M) α) ⊆
        chartTargetEuclid (I := I) (M := M) α ∧
      ContDiff ℝ (⊤ : ℕ∞) η ∧
      HasCompactSupport η ∧
      Set.range η ⊆ Set.Icc (0 : ℝ) 1 ∧
      (∀ y ∈ Metric.cthickening δ
        (chartImagePOUTsupport (I := I) (M := M) α), η y = 1) ∧
      tsupport η ⊆ chartTargetEuclid (I := I) (M := M) α := by
  exact Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
    (d := Module.finrank ℝ E)
    (chartImagePOUTsupport_isCompact (I := I) (M := M) α)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (chartImagePOUTsupport_subset_target (I := I) (M := M) α)

omit [FiniteDimensional ℝ E] in
lemma norm_le_one_of_range_Icc
    {η : EuclN → ℝ}
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1) (x : EuclN) :
    ‖η x‖ ≤ 1 := by
  have hx : η x ∈ Set.Icc (0 : ℝ) 1 :=
    hη_range (Set.mem_range_self x)
  have h1 : 0 ≤ η x := hx.1
  have h2 : η x ≤ 1 := hx.2
  rw [Real.norm_of_nonneg h1]
  exact h2

omit [FiniteDimensional ℝ E] in
lemma exists_grad_bound_of_compactSupport_smooth
    {η : EuclN → ℝ}
    (hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : EuclN, ‖fderiv ℝ η x‖ ≤ C := by
  classical
  have h_ne_zero : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have h_cont_fderiv : Continuous (fun x : EuclN => fderiv ℝ η x) :=
    hη_smooth.continuous_fderiv h_ne_zero
  have h_cont_norm : Continuous (fun x : EuclN => ‖fderiv ℝ η x‖) :=
    h_cont_fderiv.norm
  have h_zero_off : ∀ x : EuclN, x ∉ tsupport η → fderiv ℝ η x = 0 := by
    intro x hx
    have h_mem : (tsupport η)ᶜ ∈ 𝓝 x :=
      (isClosed_tsupport η).isOpen_compl.mem_nhds hx
    have h_eq : (η =ᶠ[𝓝 x] fun _ => (0 : ℝ)) :=
      Filter.eventuallyEq_of_mem h_mem
        (fun y hy => image_eq_zero_of_notMem_tsupport hy)
    rw [Filter.EventuallyEq.fderiv_eq h_eq]
    simp
  set K : Set EuclN := tsupport η with hK_def
  have hK_compact : IsCompact K := hη_compact
  have h_bdd : ∃ C : ℝ, ∀ x ∈ K, ‖fderiv ℝ η x‖ ≤ C := by
    by_cases hKn : K.Nonempty
    · obtain ⟨x₀, _hx₀K, hx₀_max⟩ :=
        hK_compact.exists_isMaxOn hKn h_cont_norm.continuousOn
      exact ⟨‖fderiv ℝ η x₀‖, fun x hx => hx₀_max hx⟩
    · refine ⟨0, ?_⟩
      intro x hx
      exact (hKn ⟨x, hx⟩).elim
  obtain ⟨C₀, hC₀⟩ := h_bdd
  refine ⟨max C₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x
  by_cases hx : x ∈ K
  · exact (hC₀ x hx).trans (le_max_left _ _)
  · rw [h_zero_off x hx]
    simp only [norm_zero]
    exact le_trans zero_le_one (le_max_right _ _)

lemma chartCutoff_smul_chartPushed_eq_chartPushed
    [T2Space M] [SigmaCompactSpace M] (α : M) (u : M → ℝ)
    {δ : ℝ}
    {η : EuclN → ℝ}
    (hη_one : ∀ y ∈ Metric.cthickening δ
      (chartImagePOUTsupport (I := I) (M := M) α), η y = 1) :
    ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      η y * chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u y =
        chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u y := by
  intro y hy
  by_cases hyKα : y ∈ chartImagePOUTsupport (I := I) (M := M) α
  · have hy_cthick : y ∈ Metric.cthickening δ
        (chartImagePOUTsupport (I := I) (M := M) α) :=
      Metric.self_subset_cthickening _ hyKα
    have hηy : η y = 1 := hη_one y hy_cthick
    rw [hηy]; ring
  · have hf_zero : chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u y = 0 :=
      chartPushed_eq_zero_off_chartImagePOUTsupport (I := I) (M := M)
        α u hy hyKα
    rw [hf_zero]; ring

lemma chartCutoff_smul_chartPushed_memWkp
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {u : M → ℝ} (hu : MemWkpChart (I := I) (M := M) 1 p u) (α : M)
    {η : EuclN → ℝ}
    (hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η)
    {C : ℝ}
    (hη_bound_zero : ∀ x ∈ chartTargetEuclid (I := I) (M := M) α, ‖η x‖ ≤ C)
    (hη_bound_one : ∀ x ∈ chartTargetEuclid (I := I) (M := M) α,
      ‖fderiv ℝ η x‖ ≤ C) :
    Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 p
      (fun y => η y * chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have hu_α := hu α
  refine Sobolev.Euclidean.MemWkp.smul_smooth_bounded
    (d := Module.finrank ℝ E) 1 hp_one
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    hη_smooth (C := C) ?_ hu_α
  intro j hj x hx
  interval_cases j
  · rw [norm_iteratedFDeriv_zero]
    exact hη_bound_zero x hx
  · rw [norm_iteratedFDeriv_one]
    exact hη_bound_one x hx

theorem exists_smooth_strong_support_approx
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {u : M → ℝ} (hu : MemWkpChart (I := I) (M := M) 1 p u)
    (α : M) (ε_per : ℝ) (hε_per : 0 < ε_per) :
    ∃ (χ : EuclN → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) χ ∧
      HasCompactSupport χ ∧
      tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α ∧
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 p
        (fun y =>
          chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u y -
            χ y)
        (chartTargetEuclid (I := I) (M := M) α) ≤
        ENNReal.ofReal ε_per := by
  classical
  obtain ⟨δ, η, hδ_pos, _hδ_subset, hη_smooth, hη_compact, hη_range, hη_one,
    hη_support⟩ :=
    exists_chartCutoff (I := I) (M := M) α
  have hη_norm_one : ∀ x : EuclN, ‖η x‖ ≤ 1 :=
    norm_le_one_of_range_Icc hη_range
  obtain ⟨Cη, _hCη_pos, hCη_grad⟩ :=
    exists_grad_bound_of_compactSupport_smooth hη_smooth hη_compact
  set C : ℝ := max Cη 1 with hC_def
  have hη_norm_C : ∀ x ∈ chartTargetEuclid (I := I) (M := M) α, ‖η x‖ ≤ C :=
    fun x _ => (hη_norm_one x).trans (le_max_right _ _)
  have hη_grad_C : ∀ x ∈ chartTargetEuclid (I := I) (M := M) α,
      ‖fderiv ℝ η x‖ ≤ C := fun x _ => (hCη_grad x).trans (le_max_left _ _)
  set ρ_α := CalabiYau.RiemannianVolume.chartAtlasPOU I M with hρα_def
  set f_orig : EuclN → ℝ :=
    chartPushed (I := I) (M := M) ρ_α α u with hf_orig_def
  set f : EuclN → ℝ := fun y => η y * f_orig y with hf_def
  have hf_mem_W1p :
      Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 1 p f
        (chartTargetEuclid (I := I) (M := M) α) :=
    chartCutoff_smul_chartPushed_memWkp (I := I) (M := M) hp_one hu α
      hη_smooth hη_norm_C hη_grad_C
  have hf_support_subset : tsupport f ⊆ tsupport η :=
    tsupport_smul_subset_left η f_orig
  have hf_compact : HasCompactSupport f :=
    HasCompactSupport.intro hη_compact (fun y hy => by
      change η y * f_orig y = 0
      have hy_off : y ∉ tsupport η := hy
      rw [image_eq_zero_of_notMem_tsupport hy_off]
      ring)
  have hf_support_target : tsupport f ⊆ chartTargetEuclid (I := I) (M := M) α :=
    hf_support_subset.trans hη_support
  have hf_eq_forig_on_target : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      f y = f_orig y :=
    chartCutoff_smul_chartPushed_eq_chartPushed (I := I) (M := M) α u
      hη_one
  obtain ⟨χ, hχ_smooth, hχ_compact, hχ_support, hχ_close⟩ :=
    Sobolev.Euclidean.MemWkp.exists_smooth_compactSupport_approx
      (d := Module.finrank ℝ E)
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
      1 p hp_one hp_top
      hf_mem_W1p hf_compact hf_support_target
      ε_per hε_per
  refine ⟨χ, hχ_smooth, hχ_compact, hχ_support, ?_⟩
  have h_target_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  have h_diff_eq : (fun y => f_orig y - χ y) =ᵐ[volume.restrict
      (chartTargetEuclid (I := I) (M := M) α)] (fun y => f y - χ y) := by
    refine (ae_restrict_iff' h_target_meas).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy
    have h_eq := hf_eq_forig_on_target y hy
    change f_orig y - χ y = f y - χ y
    rw [h_eq]
  have h_norm_eq : Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) 1 p
      (fun y => f_orig y - χ y) (chartTargetEuclid (I := I) (M := M) α) =
    Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) 1 p
      (fun y => f y - χ y) (chartTargetEuclid (I := I) (M := M) α) :=
    Sobolev.Euclidean.wkpNorm_congr_ae
      (d := Module.finrank ℝ E) hp_one
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
      h_diff_eq
  change Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) 1 p
      (fun y => f_orig y - χ y) (chartTargetEuclid (I := I) (M := M) α) ≤
    ENNReal.ofReal ε_per
  rw [h_norm_eq]
  exact hχ_close

end Chart
end Sobolev
