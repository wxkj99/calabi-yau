-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Approximation/Density/HigherOrder.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Approximation.Density.FirstOrder
public import CalabiYau.Analysis.Sobolev.Chart.CrossChartBounds.CrossChartBoundStrictMemWkpHigherOrder
public import CalabiYau.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuantK

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace Sobolev
namespace Chart

variable {E H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private lemma chartCutoff_smul_chartPushed_memWkp_k
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (k : ℕ) {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {u : M → ℝ} (hu : MemWkpChart (I := I) (M := M) k p u) (α : M)
    {η : EuclN → ℝ}
    (hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η)
    {C : ℝ}
    (hη_bound : ∀ j ≤ k, ∀ x ∈ chartTargetEuclid (I := I) (M := M) α,
      ‖iteratedFDeriv ℝ j η x‖ ≤ C) :
    Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k p
      (fun y => η y * chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have hu_α := hu α
  exact Sobolev.Euclidean.MemWkp.smul_smooth_bounded
    (d := Module.finrank ℝ E) k hp_one
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    hη_smooth (C := C) hη_bound hu_α

private theorem exists_smooth_strong_support_approx_k
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (k : ℕ) {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {u : M → ℝ} (hu : MemWkpChart (I := I) (M := M) k p u)
    (α : M) (ε_per : ℝ) (hε_per : 0 < ε_per) :
    ∃ (χ : EuclN → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) χ ∧
      HasCompactSupport χ ∧
      tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α ∧
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p
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
  obtain ⟨C, hC_nn, hC_bound⟩ :=
    Sobolev.Euclidean.exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      hη_smooth hη_compact k
  set ρ_α := CalabiYau.RiemannianVolume.chartAtlasPOU I M with hρα_def
  set f_orig : EuclN → ℝ :=
    chartPushed (I := I) (M := M) ρ_α α u with hf_orig_def
  set f : EuclN → ℝ := fun y => η y * f_orig y with hf_def
  have hη_bound_global : ∀ j ≤ k, ∀ x ∈ chartTargetEuclid (I := I) (M := M) α,
      ‖iteratedFDeriv ℝ j η x‖ ≤ C := fun j hj x _ => hC_bound x j hj
  have hf_mem_Wkp :
      Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) k p f
        (chartTargetEuclid (I := I) (M := M) α) :=
    chartCutoff_smul_chartPushed_memWkp_k (I := I) (M := M) k hp_one hu α
      hη_smooth hη_bound_global
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
      k p hp_one hp_top
      hf_mem_Wkp hf_compact hf_support_target
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
      (d := Module.finrank ℝ E) k p
      (fun y => f_orig y - χ y) (chartTargetEuclid (I := I) (M := M) α) =
    Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) k p
      (fun y => f y - χ y) (chartTargetEuclid (I := I) (M := M) α) :=
    Sobolev.Euclidean.wkpNorm_congr_ae
      (d := Module.finrank ℝ E) hp_one
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
      h_diff_eq
  change Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) k p
      (fun y => f_orig y - χ y) (chartTargetEuclid (I := I) (M := M) α) ≤
    ENNReal.ofReal ε_per
  rw [h_norm_eq]
  exact hχ_close

private lemma tightenedChartPushed_memWkp_k
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (k : ℕ) {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {u : M → ℝ} (hu : MemWkpChart (I := I) (M := M) k p u) (α : M)
    {η_M : M → ℝ}
    (hη_M_smooth : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ η_M)
    (hη_M_compact : HasCompactSupport η_M)
    (hη_M_support_chart : tsupport η_M ⊆ (chartAt H α).source) :
    Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k p
      (tightenedChartPushed (I := I) (M := M) α η_M u)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set ηE : EuclN → ℝ := chartCutoffEuclidean (I := I) (M := M) α η_M with hηE_def
  have hηE_smooth : ContDiff ℝ (⊤ : ℕ∞) ηE :=
    contDiff_etaEuclid (I := I) (M := M) α η_M hη_M_smooth hη_M_compact hη_M_support_chart
  have hηE_compact : HasCompactSupport ηE :=
    hasCompactSupport_etaEuclid (I := I) (M := M) α η_M hη_M_compact hη_M_support_chart
  obtain ⟨C, hC_nn, hC_bound⟩ :=
    Sobolev.Euclidean.exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      hηE_smooth hηE_compact k
  have hC_target : ∀ j ≤ k, ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      ‖iteratedFDeriv ℝ j ηE y‖ ≤ C := fun j hj y _ => hC_bound y j hj
  exact chartCutoff_smul_chartPushed_memWkp_k (I := I) (M := M) k hp_one hu α
    hηE_smooth hC_target

private lemma wkpNorm_tightenedChartPushed_sub_eq_k
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (k : ℕ) {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    (α : M) {η_M : M → ℝ}
    (hη_one_on_tsupport :
      ∀ x ∈ tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ), η_M x = 1)
    (u : M → ℝ) (χ : EuclN → ℝ) :
    Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) k p
      (fun y => tightenedChartPushed (I := I) (M := M) α η_M u y - χ y)
      (chartTargetEuclid (I := I) (M := M) α) =
    Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) k p
      (fun y => chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u y - χ y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_target_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  have h_diff_eq : (fun y => tightenedChartPushed (I := I) (M := M) α η_M u y - χ y)
      =ᵐ[volume.restrict (chartTargetEuclid (I := I) (M := M) α)]
      (fun y => chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u y - χ y) := by
    refine (ae_restrict_iff' h_target_meas).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy
    have h_eq := tightenedChartPushed_eq_chartPushed_on_target (I := I) (M := M)
      α hη_one_on_tsupport u y hy
    simp [h_eq]
  exact Sobolev.Euclidean.wkpNorm_congr_ae
    (d := Module.finrank ℝ E) hp_one
    (chartTargetEuclid_isOpen (I := I) (M := M) α) h_diff_eq

private theorem MemWkp_of_cross_chart_pushforward_k
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (γ α : M) {K_α : Set M} (hK_compact : IsCompact K_α)
    (hK_α_in_α : K_α ⊆ (chartAt H α).source)
    (k : ℕ) {v : EuclN → ℝ} {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    (hv : Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) k p v
        (chartTargetEuclid (I := I) (M := M) α))
    (hv_support : tsupport v ⊆
      (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_α) :
    Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) k p
      (chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) γ
        (chartPullback I α v))
      (chartTargetEuclid (I := I) (M := M) γ) := by
  classical
  set ρ_γ_M : M → ℝ :=
    ((CalabiYau.RiemannianVolume.chartAtlasPOU I M γ
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hρ_γ_M_def
  have hρ_γ_M_smooth : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ ρ_γ_M :=
    (CalabiYau.RiemannianVolume.chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯).contMDiff
  have hρ_γ_M_support_in_chart : tsupport ρ_γ_M ⊆ (chartAt H γ).source :=
    CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M γ
  have hρ_γ_M_compact : HasCompactSupport ρ_γ_M :=
    (isClosed_tsupport _).isCompact
  set K_M : Set M := K_α ∩ tsupport ρ_γ_M with hKM_def
  have hKM_compact : IsCompact K_M :=
    hK_compact.inter_right (isClosed_tsupport _)
  have hKM_in_α : K_M ⊆ (chartAt H α).source := fun x hx => hK_α_in_α hx.1
  have hKM_in_γ : K_M ⊆ (chartAt H γ).source := fun x hx =>
    hρ_γ_M_support_in_chart hx.2
  obtain ⟨Ω_γα, Ω_αγ, hΩγα_open, hΩαγ_open, hΩγα_subset_target, hΩαγ_subset_target,
    hΩγα_subset_overlap, hΩαγ_subset_overlap, hKM_image_in_Ωγα, Φ,
    hΦ_eq_on_Ωγα, hΦ_inv_eq_on_Ωαγ⟩ :=
    chartTransition_smoothDiffeoBoundedAtOrder_strict (I := I) (M := M) γ α
      hKM_compact hKM_in_γ hKM_in_α k
  set K_E_γ : Set EuclN :=
    (fun x : M => (toEuclidean (E := E)) (extChartAt I γ x)) '' K_M with hKEγ_def
  set K_E_α : Set EuclN :=
    (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_M with hKEα_def
  have hKEγ_compact : IsCompact K_E_γ :=
    chartImage_isCompact_of_compact_in_source (I := I) (M := M) γ hKM_compact hKM_in_γ
  have hKEα_compact : IsCompact K_E_α :=
    chartImage_isCompact_of_compact_in_source (I := I) (M := M) α hKM_compact hKM_in_α
  have hKEγ_subset_target : K_E_γ ⊆ chartTargetEuclid (I := I) (M := M) γ := by
    intro y hy
    rcases hy with ⟨x, hxK, hxy⟩
    have hx_ext : x ∈ (extChartAt I γ).source := by rw [extChartAt_source]; exact hKM_in_γ hxK
    have h_target : extChartAt I γ x ∈ (extChartAt I γ).target :=
      (extChartAt I γ).map_source hx_ext
    rw [← hxy]; exact ⟨extChartAt I γ x, h_target, rfl⟩
  have hKEα_subset_target : K_E_α ⊆ chartTargetEuclid (I := I) (M := M) α := by
    intro y hy
    rcases hy with ⟨x, hxK, hxy⟩
    have hx_ext : x ∈ (extChartAt I α).source := by rw [extChartAt_source]; exact hKM_in_α hxK
    have h_target : extChartAt I α x ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source hx_ext
    rw [← hxy]; exact ⟨extChartAt I α x, h_target, rfl⟩
  have hΦ_eq_KM : ∀ x ∈ K_M, Φ.toFun ((toEuclidean (E := E)) (extChartAt I γ x)) =
      (toEuclidean (E := E)) (extChartAt I α x) := by
    intro x hxK
    set y := (toEuclidean (E := E)) (extChartAt I γ x) with hy_def
    have hy_in_KEγ : y ∈ K_E_γ := ⟨x, hxK, rfl⟩
    have hy_in_Ωγα : y ∈ Ω_γα := hKM_image_in_Ωγα hy_in_KEγ
    have h1 : Φ.toFun y = chartTransitionEuclid (I := I) (M := M) γ α y :=
      hΦ_eq_on_Ωγα y hy_in_Ωγα
    rw [h1]
    have hx_chart : x ∈ (chartAt H γ).source := hKM_in_γ hxK
    rw [hy_def]
    exact chartTransitionEuclid_eq_chartα_image (I := I) (M := M) γ α hx_chart
  have hKEα_eq_Φ_image : K_E_α = Φ.toFun '' K_E_γ := by
    ext z
    refine ⟨?_, ?_⟩
    · rintro ⟨x, hxK, hxz⟩
      refine ⟨(toEuclidean (E := E)) (extChartAt I γ x), ⟨x, hxK, rfl⟩, ?_⟩
      rw [hΦ_eq_KM x hxK]; simpa using hxz
    · rintro ⟨y, ⟨x, hxK, hxy⟩, hyz⟩
      refine ⟨x, hxK, ?_⟩
      rw [← hyz, ← hxy, hΦ_eq_KM x hxK]
  have hKEα_in_Ωαγ : K_E_α ⊆ Ω_αγ := by
    rw [hKEα_eq_Φ_image]
    intro z hz
    rcases hz with ⟨y, hy, hyz⟩
    have hy_in_Ωγα : y ∈ Ω_γα := hKM_image_in_Ωγα hy
    rw [← hyz]; exact Φ.bijOn.mapsTo hy_in_Ωγα
  set Uγ : Set EuclN := Ω_γα ∩ chartTargetEuclid (I := I) (M := M) γ with hUγ_def
  have hUγ_open : IsOpen Uγ :=
    hΩγα_open.inter (chartTargetEuclid_isOpen (I := I) (M := M) γ)
  have hKEγ_in_Uγ : K_E_γ ⊆ Uγ :=
    Set.subset_inter hKM_image_in_Ωγα hKEγ_subset_target
  obtain ⟨_δ_γ, η_γ_local, _hδ_γ_pos, _hδγ_subset, hη_γ_local_smooth, hη_γ_local_compact,
    hη_γ_local_range, hη_γ_local_one, hη_γ_local_support⟩ :=
    Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      (d := Module.finrank ℝ E) hKEγ_compact hUγ_open hKEγ_in_Uγ
  have hη_γ_local_support_Ωγα : tsupport η_γ_local ⊆ Ω_γα :=
    fun y hy => (hη_γ_local_support hy).1
  have hη_γ_local_support_target : tsupport η_γ_local ⊆ chartTargetEuclid (I := I) (M := M) γ :=
    fun y hy => (hη_γ_local_support hy).2
  set Uα : Set EuclN := Ω_αγ ∩ chartTargetEuclid (I := I) (M := M) α with hUα_def
  have hUα_open : IsOpen Uα :=
    hΩαγ_open.inter (chartTargetEuclid_isOpen (I := I) (M := M) α)
  have hKEα_in_Uα : K_E_α ⊆ Uα :=
    Set.subset_inter hKEα_in_Ωαγ hKEα_subset_target
  obtain ⟨_δ_α, η_α_local, _hδα_pos, _hδα_subset, hη_α_local_smooth, hη_α_local_compact,
    hη_α_local_range, hη_α_local_one, hη_α_local_support⟩ :=
    Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      (d := Module.finrank ℝ E) hKEα_compact hUα_open hKEα_in_Uα
  have hη_α_local_support_Ωαγ : tsupport η_α_local ⊆ Ω_αγ :=
    fun y hy => (hη_α_local_support hy).1
  set ργE : EuclN → ℝ := chartCutoffEuclidean (I := I) (M := M) γ ρ_γ_M with hργE_def
  have hργE_smooth : ContDiff ℝ (⊤ : ℕ∞) ργE :=
    contDiff_etaEuclid (I := I) (M := M) γ ρ_γ_M hρ_γ_M_smooth hρ_γ_M_compact
      hρ_γ_M_support_in_chart
  have hργE_compact : HasCompactSupport ργE :=
    hasCompactSupport_etaEuclid (I := I) (M := M) γ ρ_γ_M hρ_γ_M_compact
      hρ_γ_M_support_in_chart
  set η_combined : EuclN → ℝ := fun y => η_γ_local y * ργE y with hη_combined_def
  have hη_combined_smooth : ContDiff ℝ (⊤ : ℕ∞) η_combined :=
    hη_γ_local_smooth.mul hργE_smooth
  have hη_combined_compact : HasCompactSupport η_combined := by
    refine hη_γ_local_compact.of_isClosed_subset (isClosed_tsupport _) ?_
    refine closure_mono ?_
    intro y hy
    simp only [hη_combined_def, Function.mem_support, ne_eq] at hy
    have hη_ne : η_γ_local y ≠ 0 := by intro h0; apply hy; rw [h0]; ring
    exact Function.mem_support.mpr hη_ne
  have hη_combined_support_Ωγα : tsupport η_combined ⊆ Ω_γα := by
    refine Set.Subset.trans ?_ hη_γ_local_support_Ωγα
    refine closure_mono ?_
    intro y hy
    simp only [hη_combined_def, Function.mem_support, ne_eq] at hy
    have hη_ne : η_γ_local y ≠ 0 := by intro h0; apply hy; rw [h0]; ring
    exact Function.mem_support.mpr hη_ne
  obtain ⟨C_combined, hC_combined_nn, hC_combined_bound⟩ :=
    Sobolev.Euclidean.exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      hη_combined_smooth hη_combined_compact k
  obtain ⟨C_α, hC_α_nn, hC_α_bound⟩ :=
    Sobolev.Euclidean.exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      hη_α_local_smooth hη_α_local_compact k
  have hη_α_local_iter_bound :
      ∀ j ≤ k, ∀ x ∈ chartTargetEuclid (I := I) (M := M) α,
        ‖iteratedFDeriv ℝ j η_α_local x‖ ≤ C_α :=
    fun j hj x _ => hC_α_bound x j hj
  have hη_combined_iter_bound :
      ∀ j ≤ k, ∀ x ∈ Ω_γα, ‖iteratedFDeriv ℝ j η_combined x‖ ≤ C_combined :=
    fun j hj x _ => hC_combined_bound x j hj
  set χ_local : EuclN → ℝ := fun y => η_α_local y * v y with hχ_local_def
  have hχ_local_mem_target : Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k p χ_local (chartTargetEuclid (I := I) (M := M) α) := by
    have : (fun y => η_α_local y * v y) = χ_local := rfl
    rw [← this]
    exact Sobolev.Euclidean.MemWkp.smul_smooth_bounded
      (d := Module.finrank ℝ E) k hp_one (chartTargetEuclid_isOpen (I := I) (M := M) α)
      hη_α_local_smooth hη_α_local_iter_bound hv
  have hχ_local_support : tsupport χ_local ⊆ Ω_αγ := by
    refine Set.Subset.trans ?_ hη_α_local_support_Ωαγ
    refine closure_mono ?_
    intro y hy
    simp only [hχ_local_def, Function.mem_support, ne_eq] at hy
    have hη_ne : η_α_local y ≠ 0 := by intro h0; apply hy; rw [h0]; ring
    exact Function.mem_support.mpr hη_ne
  have hχ_local_compact : HasCompactSupport χ_local := by
    have h_sub_tsupp : tsupport χ_local ⊆ tsupport η_α_local := by
      refine closure_mono ?_
      intro y hy
      have hy' : χ_local y ≠ 0 := by simpa [Function.mem_support] using hy
      have hη_ne : η_α_local y ≠ 0 := by intro h0; apply hy'; simp [hχ_local_def, h0]
      simpa [Function.mem_support]
    exact hη_α_local_compact.of_isClosed_subset (isClosed_tsupport _) h_sub_tsupp
  obtain ⟨hχ_local_mem_Ωαγ, _⟩ :=
    Sobolev.Euclidean.wkpNorm_eq_of_tsupport_subset
      (d := Module.finrank ℝ E) k hp_one (chartTargetEuclid_isOpen (I := I) (M := M) α)
      hΩαγ_open hΩαγ_subset_target hχ_local_mem_target hχ_local_support
  have hχ_local_comp_mem : Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k p (fun y => χ_local (Φ.toFun y)) Ω_γα :=
    Sobolev.Euclidean.MemWkp.comp_smoothDiffeoBoundedAtOrder
      (d := Module.finrank ℝ E) k (le_refl k) hp_one hp_top hΩγα_open hΩαγ_open Φ
      hχ_local_mem_Ωαγ hχ_local_compact hχ_local_support
  set ψ : EuclN → ℝ := fun y => η_combined y * χ_local (Φ.toFun y) with hψ_def
  have hψ_mem_Ωγα : Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k p ψ Ω_γα :=
    Sobolev.Euclidean.MemWkp.smul_smooth_bounded
      (d := Module.finrank ℝ E) k hp_one hΩγα_open hη_combined_smooth
      hη_combined_iter_bound hχ_local_comp_mem
  have hψ_support_Ωγα : tsupport ψ ⊆ Ω_γα := by
    refine Set.Subset.trans ?_ hη_combined_support_Ωγα
    refine closure_mono ?_
    intro y hy
    simp only [hψ_def, Function.mem_support, ne_eq] at hy
    have hη_ne : η_combined y ≠ 0 := by intro h0; apply hy; rw [h0]; ring
    exact Function.mem_support.mpr hη_ne
  have hψ_compact : HasCompactSupport ψ :=
    hη_combined_compact.of_isClosed_subset (isClosed_tsupport _) (by
      refine closure_mono ?_
      intro y hy
      simp only [hψ_def, Function.mem_support, ne_eq] at hy
      have hη_ne : η_combined y ≠ 0 := by intro h0; apply hy; rw [h0]; ring
      exact Function.mem_support.mpr hη_ne)
  have hψ_mem_target : Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k p ψ (chartTargetEuclid (I := I) (M := M) γ) :=
    Sobolev.Euclidean.MemWkp.extend_zero
      (d := Module.finrank ℝ E) hp_one hΩγα_open
      (chartTargetEuclid_isOpen (I := I) (M := M) γ) hΩγα_subset_target
      hψ_mem_Ωγα hψ_support_Ωγα hψ_compact
  have h_ae_eq : (chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) γ
        (chartPullback I α v)) =ᵐ[volume.restrict
          (chartTargetEuclid (I := I) (M := M) γ)] ψ := by
    have h_target_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) γ) :=
      (chartTargetEuclid_isOpen (I := I) (M := M) γ).measurableSet
    refine (ae_restrict_iff' h_target_meas).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy_target
    set z : M := (extChartAt I γ).symm ((toEuclidean (E := E)).symm y) with hz_def
    have hsymm_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I γ).target := by
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy_target; exact hy_target
    have hz_source : z ∈ (extChartAt I γ).source :=
      (extChartAt I γ).map_target hsymm_target
    have hz_chartγ : z ∈ (chartAt H γ).source := by
      rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)] at hz_source; exact hz_source
    have h_pushed_eq : chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) γ
        (chartPullback I α v) y = ρ_γ_M z * chartPullback I α v z := rfl
    rw [h_pushed_eq, hψ_def, hχ_local_def]
    have hργE_y : ργE y = ρ_γ_M z := by
      rw [hργE_def]
      exact etaEuclid_apply_of_mem (I := I) (M := M) γ ρ_γ_M hy_target
    simp only [hη_combined_def, hργE_y]
    by_cases hρ_zero : ρ_γ_M z = 0
    · rw [hρ_zero]; simp
    · have hz_in_tsupp_ρ : z ∈ tsupport ρ_γ_M :=
        subset_tsupport _ (by simp [Function.mem_support, hρ_zero])
      by_cases hy_in_support_η_γ : y ∈ tsupport η_γ_local
      · have hy_in_Ωγα : y ∈ Ω_γα := hη_γ_local_support_Ωγα hy_in_support_η_γ
        have hz_chartα : z ∈ (chartAt H α).source := by
          have h_overlap_subset : Ω_γα ⊆ chartOverlapEuclid (I := I) (M := M) γ α :=
            hΩγα_subset_overlap
          have hy_overlap : y ∈ chartOverlapEuclid (I := I) (M := M) γ α :=
            h_overlap_subset hy_in_Ωγα
          unfold chartOverlapEuclid at hy_overlap
          rcases hy_overlap with ⟨a, ⟨w, ⟨hw_γ, hw_α⟩, hwa⟩, hay⟩
          have hy_eq : (toEuclidean (E := E)) (extChartAt I γ w) = y := by
            rw [← hay, ← hwa]
          have hz_eq_w : z = w := by
            have h_w_chart_γ : w ∈ (extChartAt I γ).source := by
              rw [extChartAt_source]; exact hw_γ
            have hy_symm : (toEuclidean (E := E)).symm y = extChartAt I γ w := by
              rw [← hy_eq, (toEuclidean (E := E)).symm_apply_apply]
            have hz_val : z = (extChartAt I γ).symm (extChartAt I γ w) := by
              rw [hz_def, hy_symm]
            rw [hz_val, (extChartAt I γ).left_inv h_w_chart_γ]
          rw [hz_eq_w]; exact hw_α
        have hΦy_eq : Φ.toFun y = chartTransitionEuclid (I := I) (M := M) γ α y :=
          hΦ_eq_on_Ωγα y hy_in_Ωγα
        have h_ext_γ_z : extChartAt I γ z = (toEuclidean (E := E)).symm y := by
          rw [hz_def]
          exact (extChartAt I γ).right_inv hsymm_target
        have hy_eq_w : y = (toEuclidean (E := E)) (extChartAt I γ z) := by
          calc
            y = (toEuclidean (E := E)) ((toEuclidean (E := E)).symm y) := by simp
            _ = (toEuclidean (E := E)) (extChartAt I γ z) := by rw [h_ext_γ_z]
        have hΦy_chartα : Φ.toFun y = (toEuclidean (E := E)) (extChartAt I α z) := by
          rw [hΦy_eq, hy_eq_w]
          exact chartTransitionEuclid_eq_chartα_image (I := I) (M := M) γ α hz_chartγ
        rw [hΦy_chartα]
        rw [chartPullback_apply_of_mem (I := I) (M := M) α v hz_chartα]
        by_cases hv_z : v ((toEuclidean (E := E)) (extChartAt I α z)) = 0
        · rw [hv_z, mul_zero, mul_zero, mul_zero]
        · have h_in_tsupp_v : (toEuclidean (E := E)) (extChartAt I α z) ∈ tsupport v :=
            subset_tsupport _ (by simpa using hv_z)
          have h_in_image_K_α : (toEuclidean (E := E)) (extChartAt I α z) ∈
              (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_α :=
            hv_support h_in_tsupp_v
          rcases h_in_image_K_α with ⟨x', hx'_K_α, hx'_eq⟩
          have hx'_chart : x' ∈ (chartAt H α).source := hK_α_in_α hx'_K_α
          have h_eq_chart : extChartAt I α x' = extChartAt I α z := by
            have h_eu : (toEuclidean (E := E)) (extChartAt I α x') =
                (toEuclidean (E := E)) (extChartAt I α z) := hx'_eq
            exact (toEuclidean (E := E)).injective h_eu
          have hz_in_α_ext : z ∈ (extChartAt I α).source := by
            rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
              (I := I) (M := M)]; exact hz_chartα
          have hx'_α_ext : x' ∈ (extChartAt I α).source := by
            rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
              (I := I) (M := M)]; exact hx'_chart
          have h_inj := (extChartAt I α).injOn hx'_α_ext hz_in_α_ext h_eq_chart
          have hz_in_K_α : z ∈ K_α := by rw [← h_inj]; exact hx'_K_α
          have hz_in_KM : z ∈ K_M := ⟨hz_in_K_α, hz_in_tsupp_ρ⟩
          have hy_in_KEγ : y ∈ K_E_γ := by
            refine ⟨z, hz_in_KM, ?_⟩
            change (toEuclidean (E := E)) (extChartAt I γ z) = y
            have h_z_chart : extChartAt I γ z = (toEuclidean (E := E)).symm y :=
              (extChartAt I γ).right_inv hsymm_target
            rw [h_z_chart]; exact (toEuclidean (E := E)).apply_symm_apply y
          have hη_γ_local_y_one : η_γ_local y = 1 :=
            hη_γ_local_one y (Metric.self_subset_cthickening K_E_γ hy_in_KEγ)
          have h_chartα_z_in_K_E_α :
              (toEuclidean (E := E)) (extChartAt I α z) ∈ K_E_α := ⟨z, hz_in_KM, rfl⟩
          have hη_α_local_eq_one : η_α_local ((toEuclidean (E := E)) (extChartAt I α z)) = 1 :=
            hη_α_local_one ((toEuclidean (E := E)) (extChartAt I α z))
              (Metric.self_subset_cthickening K_E_α h_chartα_z_in_K_E_α)
          rw [hη_γ_local_y_one, hη_α_local_eq_one]
          ring
      · have hη_γ_local_y_zero : η_γ_local y = 0 :=
          image_eq_zero_of_notMem_tsupport hy_in_support_η_γ
        have hz_not_Kα : z ∉ K_α := by
          intro hz_Kα
          apply hy_in_support_η_γ
          have hz_in_KM : z ∈ K_M := ⟨hz_Kα, hz_in_tsupp_ρ⟩
          have hy_in_KEγ : y ∈ K_E_γ := ⟨z, hz_in_KM, by
            have h_ext_γ_z : extChartAt I γ z = (toEuclidean (E := E)).symm y := by
              rw [hz_def]
              exact (extChartAt I γ).right_inv hsymm_target
            calc
              (toEuclidean (E := E)) (extChartAt I γ z)
                  = (toEuclidean (E := E)) ((toEuclidean (E := E)).symm y) := by rw [h_ext_γ_z]
              _ = y := by simp⟩
          have h_one : η_γ_local y = 1 :=
            hη_γ_local_one y (Metric.self_subset_cthickening K_E_γ hy_in_KEγ)
          have h_ne_zero : η_γ_local y ≠ 0 := by linarith
          exact subset_tsupport _ (by simpa [Function.mem_support] using h_ne_zero)
        have h_cp_zero : chartPullback I α v z = 0 := by
          by_cases hz_α_source : z ∈ (chartAt H α).source
          · rw [chartPullback_apply_of_mem (I := I) (M := M) α v hz_α_source]
            have h_outside : (toEuclidean (E := E)) (extChartAt I α z) ∉ tsupport v := by
              intro h
              have h_image : (toEuclidean (E := E)) (extChartAt I α z) ∈
                  (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_α :=
                hv_support h
              rcases h_image with ⟨x, hx_Kα, hx_eq⟩
              have h_toEucl_inj : Function.Injective (toEuclidean (E := E)) :=
                (toEuclidean (E := E)).injective
              have hx_source : x ∈ (extChartAt I α).source := by
                rw [extChartAt_source (I := I)]; exact hK_α_in_α hx_Kα
              have hz_ext_source : z ∈ (extChartAt I α).source := by
                rw [extChartAt_source (I := I)]; exact hz_α_source
              have h_ext_eq : extChartAt I α x = extChartAt I α z := h_toEucl_inj hx_eq
              have h_x_eq_z : x = z :=
                (extChartAt I α).injOn hx_source hz_ext_source h_ext_eq
              rw [h_x_eq_z] at hx_Kα
              exact hz_not_Kα hx_Kα
            exact image_eq_zero_of_notMem_tsupport h_outside
          · exact chartPullback_apply_of_notMem (I := I) (M := M) α v hz_α_source
        simp [hη_γ_local_y_zero, h_cp_zero]
  exact (Sobolev.Euclidean.MemWkp_congr_ae
    (d := Module.finrank ℝ E) hp_one
    (chartTargetEuclid_isOpen (I := I) (M := M) γ) h_ae_eq).mpr hψ_mem_target

theorem contMDiff_dense_in_WkpChart_k
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (k : ℕ) {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {u : M → ℝ} (hu : MemWkpChart (I := I) (M := M) k p u)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ v ∧
      wkpNormChart (I := I) (M := M) k p (fun x => u x - v x) ≤
        ENNReal.ofReal ε := by
  classical
  set S : Finset M :=
    CalabiYau.RiemannianVolume.chartAtlasPOUFinset (I := I) (M := M)
    with hS_def
  have h_per_chart : ∀ α : S,
      ∃ K_α : Set M, IsCompact K_α ∧ K_α ⊆ (chartAt H (α : M)).source ∧
        tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M
          (α : M) : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆ interior K_α ∧
        ∃ η_M : M → ℝ, ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ η_M ∧
          Set.range η_M ⊆ Set.Icc (0 : ℝ) 1 ∧
          (∀ x ∈ tsupport
            ((CalabiYau.RiemannianVolume.chartAtlasPOU I M (α : M)
              : C^∞⟮I, M; ℝ⟯) : M → ℝ), η_M x = 1) ∧
          tsupport η_M ⊆ K_α := by
    intro α
    obtain ⟨K_α, hK_compact, hK_chart, h_tsupp_in_int_K⟩ :=
      exists_compact_neighborhood_of_tsupport_pou (I := I) (M := M) (α : M)
    obtain ⟨η_M, hη_smooth, hη_range, _hη_support_eq, hη_one_M, hη_tsupp_K⟩ :=
      exists_manifold_cutoff_one_on_tsupport_pou (I := I) (M := M) (α : M)
        hK_compact h_tsupp_in_int_K
    exact ⟨K_α, hK_compact, hK_chart, h_tsupp_in_int_K,
      η_M, hη_smooth, hη_range, hη_one_M, hη_tsupp_K⟩
  let K_choose : S → Set M := fun α => (h_per_chart α).choose
  let K_α : S → Set M := K_choose
  have hK_compact : ∀ α : S, IsCompact (K_α α) := fun α =>
    (h_per_chart α).choose_spec.1
  have hK_chart : ∀ α : S, K_α α ⊆ (chartAt H (α : M)).source := fun α =>
    (h_per_chart α).choose_spec.2.1
  have hK_tsupp_in_int : ∀ α : S, tsupport
      ((CalabiYau.RiemannianVolume.chartAtlasPOU I M (α : M)
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆ interior (K_α α) := fun α =>
    (h_per_chart α).choose_spec.2.2.1
  let η_choose : S → (M → ℝ) := fun α => (h_per_chart α).choose_spec.2.2.2.choose
  let η_M : S → (M → ℝ) := η_choose
  have hη_smooth : ∀ α : S, ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ (η_M α) :=
    fun α => (h_per_chart α).choose_spec.2.2.2.choose_spec.1
  have hη_one_on_tsupport : ∀ α : S, ∀ x ∈ tsupport
      ((CalabiYau.RiemannianVolume.chartAtlasPOU I M (α : M)
        : C^∞⟮I, M; ℝ⟯) : M → ℝ), η_M α x = 1 := fun α =>
    (h_per_chart α).choose_spec.2.2.2.choose_spec.2.2.1
  have hη_tsupp_K : ∀ α : S, tsupport (η_M α) ⊆ K_α α := fun α =>
    (h_per_chart α).choose_spec.2.2.2.choose_spec.2.2.2
  have hη_M_support_chart : ∀ α : S, tsupport (η_M α) ⊆ (chartAt H (α : M)).source :=
    fun α => (hη_tsupp_K α).trans (hK_chart α)
  have hη_M_compact : ∀ α : S, HasCompactSupport (η_M α) := fun α =>
    (hK_compact α).of_isClosed_subset (isClosed_tsupport _) (hη_tsupp_K α)
  have h_per_pair : ∀ γ α : S, ∃ K : ℝ, 0 < K ∧
      ∀ {v : EuclN → ℝ},
        Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) k p v
            (chartTargetEuclid (I := I) (M := M) (α : M)) →
        tsupport v ⊆
          (fun x : M => (toEuclidean (E := E)) (extChartAt I (α : M) x)) '' K_α α →
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p
          (chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) (γ : M)
            (chartPullback I (α : M) v))
          (chartTargetEuclid (I := I) (M := M) (γ : M)) ≤
          ENNReal.ofReal K *
            Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := Module.finrank ℝ E) k p v
              (chartTargetEuclid (I := I) (M := M) (α : M)) := fun γ α =>
    cross_chart_bound_strict_strong_memWkp_k (I := I) (M := M) k hp_one hp_top
      (γ : M) (α : M) (hK_compact α) (hK_chart α)
  let K_pair : S → S → ℝ := fun γ α => (h_per_pair γ α).choose
  have hK_pair_pos : ∀ γ α : S, 0 < K_pair γ α := fun γ α =>
    (h_per_pair γ α).choose_spec.1
  have hK_pair_bound : ∀ γ α : S, ∀ {v : EuclN → ℝ},
      Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) k p v
          (chartTargetEuclid (I := I) (M := M) (α : M)) →
      tsupport v ⊆
        (fun x : M => (toEuclidean (E := E)) (extChartAt I (α : M) x)) '' K_α α →
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p
        (chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) (γ : M)
          (chartPullback I (α : M) v))
        (chartTargetEuclid (I := I) (M := M) (γ : M)) ≤
        ENNReal.ofReal (K_pair γ α) *
          Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) k p v
            (chartTargetEuclid (I := I) (M := M) (α : M)) := fun γ α =>
    (h_per_pair γ α).choose_spec.2
  set K_total : ℝ := (∑ γ : S, ∑ α : S, K_pair γ α) + 1 with hK_total_def
  have hK_total_pos : 0 < K_total := by
    rw [hK_total_def]
    have h_sum_nn : 0 ≤ ∑ γ : S, ∑ α : S, K_pair γ α := by
      refine Finset.sum_nonneg ?_
      intro γ _
      refine Finset.sum_nonneg ?_
      intro α _
      exact (hK_pair_pos γ α).le
    linarith
  set ε_per : ℝ := ε / K_total with hε_per_def
  have hε_per_pos : 0 < ε_per := div_pos hε hK_total_pos
  have hK_total_eps_le : K_total * ε_per ≤ ε := by
    rw [hε_per_def, mul_div_assoc']
    rw [div_le_iff₀ hK_total_pos]
    linarith [mul_comm K_total ε]
  have h_chi : ∀ α : S, ∃ χ : EuclN → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆
        (fun x : M => (toEuclidean (E := E)) (extChartAt I (α : M) x)) '' K_α α ∧
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p
        (fun y => chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) (α : M) u y - χ y)
        (chartTargetEuclid (I := I) (M := M) (α : M)) ≤
        ENNReal.ofReal ε_per := by
    intro α
    set ηE : EuclN → ℝ := chartCutoffEuclidean (I := I) (M := M) (α : M) (η_M α) with hηE_def
    have hηE_smooth : ContDiff ℝ (⊤ : ℕ∞) ηE :=
      contDiff_etaEuclid (I := I) (M := M) (α : M) (η_M α) (hη_smooth α)
        (hη_M_compact α) (hη_M_support_chart α)
    have hηE_compact : HasCompactSupport ηE :=
      hasCompactSupport_etaEuclid (I := I) (M := M) (α : M) (η_M α)
        (hη_M_compact α) (hη_M_support_chart α)
    have hηE_tsupp_in_image_K : tsupport ηE ⊆
        (fun x : M => (toEuclidean (E := E)) (extChartAt I (α : M) x)) '' K_α α := by
      refine subset_trans
        (tsupport_etaEuclid_subset_chartImage (I := I) (M := M) (α : M) (η_M α)
          (hη_M_compact α) (hη_M_support_chart α)) ?_
      exact Set.image_mono (hη_tsupp_K α)
    have hηE_one_on_pou_image :
        ∀ y ∈ (fun x : M => (toEuclidean (E := E)) (extChartAt I (α : M) x)) ''
          tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M (α : M)
            : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ηE y = 1 := fun y hy =>
      etaEuclid_eq_one_of_eta_eq_one (I := I) (M := M) (α : M) (η_M α)
        (hη_one_on_tsupport α) hy
    obtain ⟨C, hC_nn, hC_bound⟩ :=
      Sobolev.Euclidean.exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
        hηE_smooth hηE_compact k
    set Ωα : Set EuclN := chartTargetEuclid (I := I) (M := M) (α : M) with hΩα_def
    have hΩα_open : IsOpen Ωα := chartTargetEuclid_isOpen (I := I) (M := M) (α : M)
    have hηE_iter_bound : ∀ j ≤ k, ∀ y ∈ Ωα, ‖iteratedFDeriv ℝ j ηE y‖ ≤ C :=
      fun j hj y _ => hC_bound y j hj
    obtain ⟨K_leib, hK_leib_pos, hK_leib_bound⟩ :=
      Sobolev.Euclidean.wkpNorm_smul_smooth_bounded_le
        k hp_one hp_top hΩα_open hηE_smooth hC_nn hηE_iter_bound
    set ε_inner : ℝ := ε_per / (K_leib + 1) with hε_inner_def
    have hε_inner_pos : 0 < ε_inner := by
      apply div_pos hε_per_pos; linarith
    obtain ⟨ψ, hψ_smooth, hψ_compact, hψ_support, hψ_close⟩ :=
      exists_smooth_strong_support_approx_k (I := I) (M := M) k hp_one hp_top hu (α : M)
        ε_inner hε_inner_pos
    set χ : EuclN → ℝ := fun y => ηE y * ψ y with hχ_def
    have hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ := hηE_smooth.mul hψ_smooth
    have hχ_support_in : tsupport χ ⊆ tsupport ηE := by
      change tsupport (fun y => ηE y * ψ y) ⊆ tsupport ηE
      refine closure_mono ?_
      intro y hy
      simp only [Function.mem_support, ne_eq] at hy
      have hηE_ne : ηE y ≠ 0 := by intro h0; apply hy; rw [h0]; ring
      exact Function.mem_support.mpr hηE_ne
    have hχ_compact : HasCompactSupport χ :=
      hηE_compact.of_isClosed_subset (isClosed_tsupport _) hχ_support_in
    have hχ_support_image_K : tsupport χ ⊆
        (fun x : M => (toEuclidean (E := E)) (extChartAt I (α : M) x)) '' K_α α :=
      hχ_support_in.trans hηE_tsupp_in_image_K
    refine ⟨χ, hχ_smooth, hχ_compact, hχ_support_image_K, ?_⟩
    set f : EuclN → ℝ := chartPushed (I := I) (M := M)
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M) (α : M) u with hf_def
    have h_one_minus_ηE_f_zero : ∀ y ∈ Ωα, (1 - ηE y) * f y = 0 := by
      intro y hy
      by_cases hf_zero : f y = 0
      · rw [hf_zero]; ring
      · have hy_in_image : y ∈ chartImagePOUTsupport (I := I) (M := M) (α : M) := by
          by_contra hy_off
          apply hf_zero
          exact chartPushed_eq_zero_off_chartImagePOUTsupport (I := I) (M := M)
            (α : M) u hy hy_off
        have hy_in_image' :
            y ∈ (fun x : M => (toEuclidean (E := E)) (extChartAt I (α : M) x)) ''
              tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M (α : M)
                : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
          unfold chartImagePOUTsupport at hy_in_image
          rcases hy_in_image with ⟨z, ⟨x, hx_support, hxz⟩, hzy⟩
          exact ⟨x, hx_support, by rw [← hzy, ← hxz]⟩
        have hηEy : ηE y = 1 := hηE_one_on_pou_image y hy_in_image'
        rw [hηEy]; ring
    have h_decomp : ∀ y ∈ Ωα, f y - χ y = ηE y * (f y - ψ y) := by
      intro y hy
      have h0 : (1 - ηE y) * f y = 0 := h_one_minus_ηE_f_zero y hy
      change f y - ηE y * ψ y = ηE y * (f y - ψ y)
      have : f y - ηE y * ψ y = ηE y * (f y - ψ y) + (1 - ηE y) * f y := by ring
      rw [this, h0, add_zero]
    have h_target_meas : MeasurableSet Ωα := hΩα_open.measurableSet
    have h_diff_eq : (fun y => f y - χ y) =ᵐ[volume.restrict Ωα]
        (fun y => ηE y * (f y - ψ y)) := by
      refine (ae_restrict_iff' h_target_meas).mpr ?_
      refine Filter.Eventually.of_forall ?_
      intro y hy; exact h_decomp y hy
    have h_norm_eq :
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p (fun y => f y - χ y) Ωα =
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p (fun y => ηE y * (f y - ψ y)) Ωα :=
      Sobolev.Euclidean.wkpNorm_congr_ae
        (d := Module.finrank ℝ E) hp_one hΩα_open h_diff_eq
    have hf_mem :
        Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) k p f Ωα := hu (α : M)
    have hψ_mem :
        Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) k p ψ Ωα :=
      Sobolev.Euclidean.MemWkp_of_smooth_compactSupport
        (d := Module.finrank ℝ E) hΩα_open hψ_smooth hψ_compact hψ_support hp_one k
    have hfψ_mem :
        Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) k p (fun y => f y - ψ y) Ωα :=
      Sobolev.Euclidean.MemWkp.sub
        (d := Module.finrank ℝ E) hp_one hΩα_open hf_mem hψ_mem
    have h_leib_bound :
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p (fun y => ηE y * (f y - ψ y)) Ωα ≤
        ENNReal.ofReal K_leib *
          Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) k p (fun y => f y - ψ y) Ωα :=
      hK_leib_bound hfψ_mem
    rw [h_norm_eq]
    refine h_leib_bound.trans ?_
    have h_step : ENNReal.ofReal K_leib *
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p (fun y => f y - ψ y) Ωα ≤
        ENNReal.ofReal K_leib * ENNReal.ofReal ε_inner :=
      mul_le_mul_of_nonneg_left hψ_close (by simp : (0 : ℝ≥0∞) ≤ ENNReal.ofReal K_leib)
    refine h_step.trans ?_
    have hK_leib_nn : 0 ≤ K_leib := hK_leib_pos.le
    have hε_inner_nn : 0 ≤ ε_inner := hε_inner_pos.le
    rw [← ENNReal.ofReal_mul hK_leib_nn]
    apply ENNReal.ofReal_le_ofReal
    rw [hε_inner_def, mul_div_assoc']
    have hK1_pos : 0 < K_leib + 1 := by linarith
    rw [div_le_iff₀ hK1_pos]
    have : K_leib * ε_per ≤ (K_leib + 1) * ε_per := by
      refine mul_le_mul_of_nonneg_right ?_ hε_per_pos.le
      linarith
    linarith
  let χ : S → (EuclN → ℝ) := fun α => (h_chi α).choose
  have hχ_smooth : ∀ α : S, ContDiff ℝ (⊤ : ℕ∞) (χ α) := fun α =>
    (h_chi α).choose_spec.1
  have hχ_compact : ∀ α : S, HasCompactSupport (χ α) := fun α =>
    (h_chi α).choose_spec.2.1
  have hχ_support : ∀ α : S, tsupport (χ α) ⊆
      (fun x : M => (toEuclidean (E := E)) (extChartAt I (α : M) x)) '' K_α α :=
    fun α => (h_chi α).choose_spec.2.2.1
  have hχ_close : ∀ α : S,
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p
        (fun y => chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) (α : M) u y -
            χ α y)
        (chartTargetEuclid (I := I) (M := M) (α : M)) ≤
        ENNReal.ofReal ε_per := fun α => (h_chi α).choose_spec.2.2.2
  have hχ_support_target : ∀ α : S, tsupport (χ α) ⊆
      chartTargetEuclid (I := I) (M := M) (α : M) := by
    intro α
    refine (hχ_support α).trans ?_
    intro y hy
    rcases hy with ⟨x, hxK, hxy⟩
    have hx_chart : x ∈ (chartAt H (α : M)).source := hK_chart α hxK
    have hx_ext : x ∈ (extChartAt I (α : M)).source := by
      rw [extChartAt_source]; exact hx_chart
    have h_target : extChartAt I (α : M) x ∈ (extChartAt I (α : M)).target :=
      (extChartAt I (α : M)).map_source hx_ext
    rw [← hxy]
    exact ⟨extChartAt I (α : M) x, h_target, rfl⟩
  set v : M → ℝ := fun x =>
    ∑ α ∈ S.attach, chartPullback I (α : M) (χ α) x with hv_def
  have hv_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ v := by
    refine contMDiff_finsetSum_chartPullback (I := I) (M := M)
      (S := S.attach) (α := fun α : S => (α : M)) (ψ := fun α => χ α) ?_ ?_ ?_
    · intro α _; exact hχ_smooth α
    · intro α _; exact hχ_compact α
    · intro α _; exact hχ_support_target α
  refine ⟨v, hv_smooth, ?_⟩
  rw [wkpNormChart_eq_finset_sum (I := I) (M := M) k hp_one (fun x => u x - v x)]
  have h_per_gamma : ∀ (γ : M), (hγS : γ ∈ S) →
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p
        (chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) γ
          (fun x => u x - v x))
        (chartTargetEuclid (I := I) (M := M) γ) ≤
        ∑ α ∈ S.attach, ENNReal.ofReal (K_pair ⟨γ, hγS⟩ α) * ENNReal.ofReal ε_per := by
    intro γ hγS
    have h_u_decomp : (fun x : M => u x) =
        fun x =>
          ∑ α ∈ S.attach,
            chartPullback I (α : M)
              (chartPushed (I := I) (M := M)
                (CalabiYau.RiemannianVolume.chartAtlasPOU I M) (α : M) u) x := by
      have h_decomp := fun_eq_finset_sum_chartPullback_chartPushed
        (I := I) (M := M) u
      rw [h_decomp]
      funext x
      rw [show (∑ α ∈ S, chartPullback I α
            (chartPushed (I := I) (M := M)
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u) x) =
          (∑ α ∈ S.attach, chartPullback I (α : M)
            (chartPushed (I := I) (M := M)
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M) (α : M) u) x)
          from by rw [Finset.sum_attach S (fun α => chartPullback I α
            (chartPushed (I := I) (M := M)
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u) x)]]
    have h_uv_decomp : (fun x : M => u x - v x) =
        fun x =>
          ∑ α ∈ S.attach,
            chartPullback I (α : M)
              (fun y => chartPushed (I := I) (M := M)
                (CalabiYau.RiemannianVolume.chartAtlasPOU I M) (α : M) u y -
                χ α y) x := by
      funext x
      have h1 := congrFun h_u_decomp x
      change u x - v x = _
      rw [hv_def]
      simp only
      rw [h1]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro α _
      classical
      by_cases hxα : x ∈ (chartAt H (α : M)).source
      · rw [chartPullback_apply_of_mem (I := I) (M := M) (α : M) _ hxα]
        rw [chartPullback_apply_of_mem (I := I) (M := M) (α : M) _ hxα]
        rw [chartPullback_apply_of_mem (I := I) (M := M) (α : M) _ hxα]
      · rw [chartPullback_apply_of_notMem (I := I) (M := M) (α : M) _ hxα]
        rw [chartPullback_apply_of_notMem (I := I) (M := M) (α : M) _ hxα]
        rw [chartPullback_apply_of_notMem (I := I) (M := M) (α : M) _ hxα]
        ring
    have h_chartPushed_decomp : chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) γ
        (fun x => u x - v x) =
        fun y => ∑ α ∈ S.attach,
          chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) γ
            (chartPullback I (α : M)
              (fun z => chartPushed (I := I) (M := M)
                (CalabiYau.RiemannianVolume.chartAtlasPOU I M) (α : M) u z -
                χ α z)) y := by
      rw [h_uv_decomp]
      exact chartPushed_finset_sum
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) γ S.attach
        (fun α x => chartPullback I (α : M)
          (fun y => chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) (α : M) u y -
            χ α y) x)
    rw [h_chartPushed_decomp]
    have h_per_alpha : ∀ α ∈ S.attach,
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p
          (chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) γ
            (chartPullback I (α : M)
              (fun y => chartPushed (I := I) (M := M)
                (CalabiYau.RiemannianVolume.chartAtlasPOU I M) (α : M) u y -
                χ α y)))
          (chartTargetEuclid (I := I) (M := M) γ) ≤
          ENNReal.ofReal (K_pair ⟨γ, hγS⟩ α) * ENNReal.ofReal ε_per := by
      intro α _hα_mem
      set f_α : EuclN → ℝ :=
        tightenedChartPushed (I := I) (M := M) (α : M) (η_M α) u with hf_α_def
      have h_chartPullback_eq : chartPullback I (α : M)
          (fun y => chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) (α : M) u y -
            χ α y) =
          chartPullback I (α : M) (fun y => f_α y - χ α y) := by
        rw [chartPullback_sub, chartPullback_sub, hf_α_def,
          chartPullback_tightenedChartPushed_eq (I := I) (M := M)
            (α : M) (hη_one_on_tsupport α) u]
      rw [h_chartPullback_eq]
      have hf_α_mem : Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) k p f_α
          (chartTargetEuclid (I := I) (M := M) (α : M)) :=
        tightenedChartPushed_memWkp_k (I := I) (M := M) k hp_one hu (α : M)
          (hη_smooth α) (hη_M_compact α) (hη_M_support_chart α)
      have hχ_α_mem : Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) k p (χ α)
          (chartTargetEuclid (I := I) (M := M) (α : M)) :=
        Sobolev.Euclidean.MemWkp_of_smooth_compactSupport
          (d := Module.finrank ℝ E)
          (chartTargetEuclid_isOpen (I := I) (M := M) (α : M))
          (hχ_smooth α) (hχ_compact α) (hχ_support_target α) hp_one k
      have h_diff_mem : Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) k p (fun y => f_α y - χ α y)
          (chartTargetEuclid (I := I) (M := M) (α : M)) :=
        Sobolev.Euclidean.MemWkp.sub
          (d := Module.finrank ℝ E) hp_one
          (chartTargetEuclid_isOpen (I := I) (M := M) (α : M))
          hf_α_mem hχ_α_mem
      have h_diff_support : tsupport (fun y => f_α y - χ α y) ⊆
          (fun x : M => (toEuclidean (E := E)) (extChartAt I (α : M) x)) '' K_α α := by
        have h_support_sub : Function.support (fun y => f_α y - χ α y) ⊆
            Function.support f_α ∪ Function.support (χ α) := by
          intro y hy
          by_cases hyf : y ∈ Function.support f_α
          · exact Or.inl hyf
          · right
            change χ α y ≠ 0
            intro h0
            apply hy
            change f_α y - χ α y = 0
            have : f_α y = 0 := Function.notMem_support.mp hyf
            rw [this, h0, sub_self]
        have h_tsupp_sub : tsupport (fun y => f_α y - χ α y) ⊆
            tsupport f_α ∪ tsupport (χ α) := by
          unfold tsupport
          refine (closure_mono h_support_sub).trans ?_
          rw [closure_union]
        have hf_α_support : tsupport f_α ⊆
            (fun x : M => (toEuclidean (E := E)) (extChartAt I (α : M) x)) '' K_α α :=
          tsupport_tightenedChartPushed_subset (I := I) (M := M) (α : M)
            (hη_M_compact α) (hη_M_support_chart α) (hη_tsupp_K α) u
        exact h_tsupp_sub.trans (Set.union_subset hf_α_support (hχ_support α))
      have h_bd := hK_pair_bound ⟨γ, hγS⟩ α h_diff_mem h_diff_support
      have h_diff_close :
          Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) k p
            (fun y => f_α y - χ α y)
            (chartTargetEuclid (I := I) (M := M) (α : M)) ≤
          ENNReal.ofReal ε_per := by
        rw [hf_α_def]
        rw [wkpNorm_tightenedChartPushed_sub_eq_k (I := I) (M := M) k hp_one (α : M)
          (hη_one_on_tsupport α) u (χ α)]
        exact hχ_close α
      refine h_bd.trans ?_
      exact mul_le_mul_of_nonneg_left h_diff_close (zero_le)
    have h_summand_mem : ∀ α ∈ S.attach,
        Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) k p
          (chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) γ
            (chartPullback I (α : M)
              (fun y => chartPushed (I := I) (M := M)
                (CalabiYau.RiemannianVolume.chartAtlasPOU I M) (α : M) u y -
                χ α y)))
          (chartTargetEuclid (I := I) (M := M) γ) := by
      intro α _hα_mem
      set f_α : EuclN → ℝ :=
        tightenedChartPushed (I := I) (M := M) (α : M) (η_M α) u with hf_α_def'
      have hf_α_mem : Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) k p f_α
          (chartTargetEuclid (I := I) (M := M) (α : M)) :=
        tightenedChartPushed_memWkp_k (I := I) (M := M) k hp_one hu (α : M)
          (hη_smooth α) (hη_M_compact α) (hη_M_support_chart α)
      have hχ_α_mem : Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) k p (χ α)
          (chartTargetEuclid (I := I) (M := M) (α : M)) :=
        Sobolev.Euclidean.MemWkp_of_smooth_compactSupport
          (d := Module.finrank ℝ E)
          (chartTargetEuclid_isOpen (I := I) (M := M) (α : M))
          (hχ_smooth α) (hχ_compact α) (hχ_support_target α) hp_one k
      have h_diff_mem : Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) k p (fun y => f_α y - χ α y)
          (chartTargetEuclid (I := I) (M := M) (α : M)) :=
        Sobolev.Euclidean.MemWkp.sub
          (d := Module.finrank ℝ E) hp_one
          (chartTargetEuclid_isOpen (I := I) (M := M) (α : M))
          hf_α_mem hχ_α_mem
      have h_diff_support : tsupport (fun y => f_α y - χ α y) ⊆
          (fun x : M => (toEuclidean (E := E)) (extChartAt I (α : M) x)) '' K_α α := by
        have h_support_sub : Function.support (fun y => f_α y - χ α y) ⊆
            Function.support f_α ∪ Function.support (χ α) := by
          intro y hy
          by_cases hyf : y ∈ Function.support f_α
          · exact Or.inl hyf
          · right
            change χ α y ≠ 0
            intro h0
            apply hy
            change f_α y - χ α y = 0
            have : f_α y = 0 := Function.notMem_support.mp hyf
            rw [this, h0, sub_self]
        have h_tsupp_sub : tsupport (fun y => f_α y - χ α y) ⊆
            tsupport f_α ∪ tsupport (χ α) := by
          unfold tsupport
          refine (closure_mono h_support_sub).trans ?_
          rw [closure_union]
        have hf_α_support : tsupport f_α ⊆
            (fun x : M => (toEuclidean (E := E)) (extChartAt I (α : M) x)) '' K_α α :=
          tsupport_tightenedChartPushed_subset (I := I) (M := M) (α : M)
            (hη_M_compact α) (hη_M_support_chart α) (hη_tsupp_K α) u
        exact h_tsupp_sub.trans (Set.union_subset hf_α_support (hχ_support α))
      have h_mem_cross : Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) k p
          (chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) γ
            (chartPullback I (α : M) (fun y => f_α y - χ α y)))
          (chartTargetEuclid (I := I) (M := M) γ) :=
        MemWkp_of_cross_chart_pushforward_k (I := I) (M := M) γ (α : M)
          (hK_compact α) (hK_chart α) k hp_one hp_top h_diff_mem h_diff_support
      have h_eq : chartPullback I (α : M)
          (fun y => chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) (α : M) u y -
            χ α y) =
          chartPullback I (α : M) (fun y => f_α y - χ α y) := by
        rw [chartPullback_sub, chartPullback_sub, hf_α_def',
          chartPullback_tightenedChartPushed_eq (I := I) (M := M)
            (α : M) (hη_one_on_tsupport α) u]
      simpa [h_eq] using h_mem_cross
    set Ωγ := chartTargetEuclid (I := I) (M := M) γ with hΩγ_def
    have hΩγ_open : IsOpen Ωγ := chartTargetEuclid_isOpen (I := I) (M := M) γ
    have h_total_bound : Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p
        (fun y => ∑ α ∈ S.attach,
          chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) γ
            (chartPullback I (α : M)
              (fun z => chartPushed (I := I) (M := M)
                (CalabiYau.RiemannianVolume.chartAtlasPOU I M) (α : M) u z -
                χ α z)) y)
        Ωγ ≤
      ∑ α ∈ S.attach, ENNReal.ofReal (K_pair ⟨γ, hγS⟩ α) * ENNReal.ofReal ε_per := by
      set F : (↥S) → EuclN → ℝ := fun (α' : S) y =>
        chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) γ
          (chartPullback I (α' : M)
            (fun z => chartPushed (I := I) (M := M)
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M) (α' : M) u z -
              χ α' z)) y with hF_def
      have hF_mem : ∀ (α' : S) (h : α' ∈ S.attach),
          Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) k p (F α') Ωγ := by
        intro α' hα'
        simpa [hF_def] using h_summand_mem α' hα'
      induction S.attach using Finset.induction_on with
      | empty =>
          simp [Sobolev.Euclidean.wkpNorm_zero_fun_zero
            (d := Module.finrank ℝ E) hp_one hΩγ_open]
      | insert α T hαT ih =>
          have hsum_eq : (fun y => ∑ α' ∈ insert α T, F α' y) =
              (fun y => F α y + ∑ α' ∈ T, F α' y) := by
            ext y; simp [Finset.sum_insert hαT]
          rw [hsum_eq]
          have h_mem_α : Sobolev.Euclidean.MemWkp
              (d := Module.finrank ℝ E) k p (F α) Ωγ :=
            hF_mem α (Finset.mem_attach _ _)
          have h_mem_sum : Sobolev.Euclidean.MemWkp
              (d := Module.finrank ℝ E) k p (fun y => ∑ α' ∈ T, F α' y) Ωγ := by
            refine Finset.induction_on T ?_ ?_
            · exact Sobolev.Euclidean.MemWkp_zero_fun
                (d := Module.finrank ℝ E) hp_one hΩγ_open
            · intro β T' hβT' ih_sum
              have hsum_eq' : (fun y => ∑ β' ∈ insert β T', F β' y) =
                  (fun y => F β y + ∑ β' ∈ T', F β' y) := by
                ext y; simp [Finset.sum_insert hβT']
              rw [hsum_eq']
              exact Sobolev.Euclidean.MemWkp.add
                (d := Module.finrank ℝ E) hp_one hΩγ_open
                (hF_mem β (Finset.mem_attach _ _)) ih_sum
          refine (Sobolev.Euclidean.wkpNorm_add_le
            (d := Module.finrank ℝ E) hp_one hΩγ_open h_mem_α h_mem_sum).trans ?_
          rw [Finset.sum_insert hαT]
          refine add_le_add ?_ ?_
          · exact h_per_alpha α (Finset.mem_attach _ _)
          · exact ih
    exact h_total_bound
  let f : S → ENNReal := fun (γ : S) =>
    Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) k p
      (chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) γ.val
        (fun x => u x - v x))
      (chartTargetEuclid (I := I) (M := M) γ.val)
  have h_f_bound : ∀ (γ : S), f γ ≤ ∑ α : S, ENNReal.ofReal (K_pair γ α) * ENNReal.ofReal
    ε_per := by
    intro γ
    dsimp [f]
    simpa [Finset.sum_attach (s := CalabiYau.RiemannianVolume.chartAtlasPOUFinset), hS_def] using
      h_per_gamma γ.val γ.property
  rw [← Finset.sum_attach (s := S)]
  calc
    (∑ γ : S, f γ) ≤ (∑ γ : S, ∑ α : S, ENNReal.ofReal (K_pair γ α) * ENNReal.ofReal ε_per) :=
      Finset.sum_le_sum (fun γ _ => h_f_bound γ)
    _ ≤ ENNReal.ofReal ε := by
      calc
        (∑ γ : S, ∑ α : S, ENNReal.ofReal (K_pair γ α) * ENNReal.ofReal ε_per)
            = (∑ γ : S, ∑ α : S, ENNReal.ofReal (K_pair γ α * ε_per)) := by
          refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun α _ => ?_
          rw [ENNReal.ofReal_mul ((hK_pair_pos γ α).le)]
        _ = ENNReal.ofReal (∑ γ : S, ∑ α : S, (K_pair γ α * ε_per)) := by
          calc
            (∑ γ : S, ∑ α : S, ENNReal.ofReal (K_pair γ α * ε_per))
                = (∑ γ : S, ENNReal.ofReal (∑ α : S, (K_pair γ α * ε_per))) := by
              refine Finset.sum_congr rfl (fun γ _ => ?_)
              rw [ENNReal.ofReal_sum_of_nonneg (fun α hα =>
                mul_nonneg ((hK_pair_pos γ α).le) hε_per_pos.le)]
            _ = ENNReal.ofReal (∑ γ : S, ∑ α : S, (K_pair γ α * ε_per)) := by
              rw [ENNReal.ofReal_sum_of_nonneg (fun γ hγ =>
                Finset.sum_nonneg (fun α hα =>
                  mul_nonneg ((hK_pair_pos γ α).le) hε_per_pos.le))]
        _ = ENNReal.ofReal ((∑ γ : S, ∑ α : S, K_pair γ α) * ε_per) := by
          simp [Finset.sum_mul]
        _ = ENNReal.ofReal ((K_total - 1) * ε_per) := by
          rw [hK_total_def]; ring_nf
        _ ≤ ENNReal.ofReal (K_total * ε_per) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by
            have : 0 ≤ 1 := by norm_num
            linarith) hε_per_pos.le)
        _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hK_total_eps_le

end Chart
end Sobolev
