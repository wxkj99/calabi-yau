-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Tools/StrictStrongSupport.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Approximation.Density.Smooth

@[expose] public section


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace Sobolev
namespace Chart

variable {E H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

section

variable [IsManifold I ∞ M]

lemma exists_compact_neighborhood_of_tsupport_pou
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] (α : M) :
    ∃ K : Set M, IsCompact K ∧ K ⊆ (chartAt H α).source ∧
      tsupport
        ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆ interior K := by
  have : LocallyCompactSpace M :=
    CalabiYau.RiemannianVolume.locallyCompactSpace_of_chartedSpace
      E H I M
  have h_tsupp_compact : IsCompact
      (tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ)) := (isClosed_tsupport _).isCompact
  have h_tsupp_chart : tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU
      I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆ (chartAt H α).source :=
    CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M α
  obtain ⟨L, hL_compact, h_tsupp_in_int_L, hL_sub_chart⟩ :=
    exists_compact_between h_tsupp_compact (chartAt H α).open_source h_tsupp_chart
  exact ⟨L, hL_compact, hL_sub_chart, h_tsupp_in_int_L⟩

lemma exists_manifold_cutoff_one_on_tsupport_pou
    [T2Space M] [SigmaCompactSpace M] (α : M)
    {K : Set M} (hK_compact : IsCompact K)
    (h_tsupp_in_int_K : tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU
      I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆ interior K) :
    ∃ η : M → ℝ, ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ η ∧
      Set.range η ⊆ Set.Icc (0 : ℝ) 1 ∧
      Function.support η = interior K ∧
      (∀ x ∈ tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU
        I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ), η x = 1) ∧
      tsupport η ⊆ K := by
  classical
  set s : Set M := interior K with hs_def
  set t : Set M := tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU
    I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) with ht_def
  have hs_open : IsOpen s := isOpen_interior
  have ht_closed : IsClosed t := isClosed_tsupport _
  have htls : t ⊆ s := h_tsupp_in_int_K
  rcases exists_contMDiff_support_eq_eq_one_iff (I := I) (n := (⊤ : ℕ∞))
      hs_open ht_closed htls with
    ⟨η, hη_smooth, hη_range, hη_support, hη_one_iff⟩
  refine ⟨η, hη_smooth, hη_range, hη_support, ?_, ?_⟩
  · intro x hx
    exact (hη_one_iff x).mp hx
  · have h_closed_K : IsClosed K := hK_compact.isClosed
    change closure (Function.support η) ⊆ K
    rw [hη_support]
    exact (closure_mono interior_subset).trans h_closed_K.closure_subset

def chartCutoffEuclidean (α : M) (η_M : M → ℝ) : EuclN → ℝ := by
  classical
  exact fun y =>
    if y ∈ chartTargetEuclid (I := I) (M := M) α then
      η_M ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    else 0

end

lemma etaEuclid_apply_of_mem (α : M) (η_M : M → ℝ)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartCutoffEuclidean (I := I) (M := M) α η_M y =
      η_M ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  classical
  unfold chartCutoffEuclidean
  simp [hy]

lemma etaEuclid_apply_of_notMem (α : M) (η_M : M → ℝ)
    {y : EuclN} (hy : y ∉ chartTargetEuclid (I := I) (M := M) α) :
    chartCutoffEuclidean (I := I) (M := M) α η_M y = 0 := by
  classical
  unfold chartCutoffEuclidean
  simp [hy]

lemma chartImage_isCompact_of_compact_in_source (α : M)
    {S : Set M} (hS_compact : IsCompact S)
    (hS_chart : S ⊆ (chartAt H α).source) :
    IsCompact ((fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' S) := by
  have hcont_ext : ContinuousOn (extChartAt I α) S :=
    (continuousOn_extChartAt α).mono (by
      intro x hx
      rw [extChartAt_source]
      exact hS_chart hx)
  have h_image_ext : IsCompact ((extChartAt I α) '' S) :=
    hS_compact.image_of_continuousOn hcont_ext
  have h_image : IsCompact
      ((toEuclidean (E := E)) '' ((extChartAt I α) '' S)) :=
    h_image_ext.image (toEuclidean (E := E)).continuous
  have hset_eq :
      ((toEuclidean (E := E)) '' ((extChartAt I α) '' S)) =
        (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' S := by
    ext y
    simp only [Set.mem_image]
    constructor
    · rintro ⟨z, ⟨x, hxS, hxz⟩, hzy⟩
      exact ⟨x, hxS, by rw [← hzy, ← hxz]⟩
    · rintro ⟨x, hxS, hxy⟩
      exact ⟨extChartAt I α x, ⟨x, hxS, rfl⟩, hxy⟩
  rw [← hset_eq]; exact h_image

lemma chartImage_tsupport_subset_chartTargetEuclid (α : M) (η_M : M → ℝ)
    (h_tsupp_chart : tsupport η_M ⊆ (chartAt H α).source) :
    (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) ''
      tsupport η_M ⊆ chartTargetEuclid (I := I) (M := M) α := by
  intro y hy
  obtain ⟨x, hx_tsupp, hxy⟩ := hy
  have hx_chart : x ∈ (chartAt H α).source := h_tsupp_chart hx_tsupp
  have hx_ext : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hx_chart
  have h_target : extChartAt I α x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hx_ext
  rw [← hxy]
  exact ⟨extChartAt I α x, h_target, rfl⟩

lemma etaEuclid_zero_off_chartImage_tsupport (α : M) (η_M : M → ℝ)
    {y : EuclN}
    (hy_off : y ∉ (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) ''
      tsupport η_M) :
    chartCutoffEuclidean (I := I) (M := M) α η_M y = 0 := by
  classical
  by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [etaEuclid_apply_of_mem (I := I) (M := M) α η_M hy_target]
    set z : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hz_def
    by_contra hηne
    apply hy_off
    have hz_support : z ∈ Function.support η_M := by
      simp only [Function.mem_support, ne_eq]; exact hηne
    have hz_tsupp : z ∈ tsupport η_M := subset_tsupport _ hz_support
    have hsymm_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy_target
      exact hy_target
    have hy_eq : (toEuclidean (E := E)) (extChartAt I α z) = y := by
      have hz_eq : extChartAt I α z = (toEuclidean (E := E)).symm y :=
        (extChartAt I α).right_inv hsymm_target
      rw [hz_eq, (toEuclidean (E := E)).apply_symm_apply]
    exact ⟨z, hz_tsupp, hy_eq⟩
  · exact etaEuclid_apply_of_notMem (I := I) (M := M) α η_M hy_target

lemma tsupport_etaEuclid_subset_chartImage (α : M) (η_M : M → ℝ)
    (h_tsupp_compact : IsCompact (tsupport η_M))
    (h_tsupp_chart : tsupport η_M ⊆ (chartAt H α).source) :
    tsupport (chartCutoffEuclidean (I := I) (M := M) α η_M) ⊆
      (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) ''
        tsupport η_M := by
  classical
  have h_image_compact : IsCompact
      ((fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' tsupport η_M) :=
    chartImage_isCompact_of_compact_in_source (I := I) (M := M)
      α h_tsupp_compact h_tsupp_chart
  have h_image_closed : IsClosed _ := h_image_compact.isClosed
  have h_support_in : Function.support (chartCutoffEuclidean (I := I) (M := M) α η_M) ⊆
      (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) ''
        tsupport η_M := by
    intro y hy
    by_contra hy_off
    have h_zero := etaEuclid_zero_off_chartImage_tsupport (I := I) (M := M)
      α η_M hy_off
    simp only [Function.mem_support, ne_eq] at hy
    exact hy h_zero
  change closure (Function.support (chartCutoffEuclidean (I := I) (M := M) α η_M)) ⊆ _
  exact subset_trans (closure_mono h_support_in) h_image_closed.closure_subset

variable [IsManifold I ∞ M] in
lemma contDiff_etaEuclid [I.Boundaryless] (α : M) (η_M : M → ℝ)
    (hη_smooth : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ η_M)
    (hη_compact : HasCompactSupport η_M)
    (h_tsupp_chart : tsupport η_M ⊆ (chartAt H α).source) :
    ContDiff ℝ (⊤ : ℕ∞) (chartCutoffEuclidean (I := I) (M := M) α η_M) := by
  classical
  set f : EuclN → ℝ := chartCutoffEuclidean (I := I) (M := M) α η_M with hf_def
  set Sα : Set EuclN :=
    (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' tsupport η_M
    with hSα_def
  have hSα_compact : IsCompact Sα :=
    chartImage_isCompact_of_compact_in_source (I := I) (M := M)
      α hη_compact h_tsupp_chart
  have hSα_closed : IsClosed Sα := hSα_compact.isClosed
  have hSα_subset_target : Sα ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartImage_tsupport_subset_chartTargetEuclid (I := I) (M := M)
      α η_M h_tsupp_chart
  have h_f_zero_off_Sα : ∀ y, y ∉ Sα → f y = 0 := fun y hy =>
    etaEuclid_zero_off_chartImage_tsupport (I := I) (M := M) α η_M hy
  have h_cover : ∀ y : EuclN,
      y ∈ chartTargetEuclid (I := I) (M := M) α ∨ y ∈ Sαᶜ := by
    intro y
    by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
    · exact Or.inl hy
    · refine Or.inr ?_
      simp only [Set.mem_compl_iff]
      intro hy_Sα
      exact hy (hSα_subset_target hy_Sα)
  rw [contDiff_iff_contDiffAt]
  intro y
  rcases h_cover y with hy_target | hy_off_Sα
  · have h_open_target : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    have hy_nhds : chartTargetEuclid (I := I) (M := M) α ∈ 𝓝 y :=
      h_open_target.mem_nhds hy_target
    set g : EuclN → ℝ := fun y =>
      η_M ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) with hg_def
    have hf_eq_g_on_target : ∀ y' ∈ chartTargetEuclid (I := I) (M := M) α,
        f y' = g y' := fun y' hy' =>
      etaEuclid_apply_of_mem (I := I) (M := M) α η_M hy'
    have hf_eq_g_evt : f =ᶠ[𝓝 y] g :=
      Filter.eventually_of_mem hy_nhds (fun y' hy' => hf_eq_g_on_target y' hy')
    suffices hg_at : ContDiffAt ℝ ∞ g y from hg_at.congr_of_eventuallyEq hf_eq_g_evt
    set z : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hz_def
    have hsymm_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy_target
      exact hy_target
    have hz_source : z ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hsymm_target
    have hz_chart : z ∈ (chartAt H α).source := by
      rw [extChartAt_source] at hz_source; exact hz_source
    have hη_at : ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ∞ η_M z :=
      hη_smooth.contMDiffAt
    have hη_at_local :
        ContDiffWithinAt ℝ ∞
          (fun e : E => η_M ((extChartAt I α).symm e))
          (extChartAt I α).target ((toEuclidean (E := E)).symm y) := by
      have hη_at' : ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ∞ η_M z := hη_at
      have h_ext_inv_on : ContMDiffOn (modelWithCornersSelf ℝ E) I ∞
          (extChartAt I α).symm (extChartAt I α).target :=
        contMDiffOn_extChartAt_symm α
      have h_ext_inv : ContMDiffWithinAt
          (modelWithCornersSelf ℝ E) I ∞
          (extChartAt I α).symm
          (extChartAt I α).target ((toEuclidean (E := E)).symm y) :=
        h_ext_inv_on _ hsymm_target
      have h_sym_at :
          ContMDiffWithinAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ)
            ∞ (fun e : E => η_M ((extChartAt I α).symm e)) (extChartAt I α).target
            ((toEuclidean (E := E)).symm y) := by
        have h_eq : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) = z := rfl
        rw [show (fun e : E => η_M ((extChartAt I α).symm e)) =
            η_M ∘ (extChartAt I α).symm from rfl]
        refine ContMDiffWithinAt.comp (t := Set.univ)
          ((toEuclidean (E := E)).symm y) ?_ h_ext_inv ?_
        · have : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) = z := rfl
          rw [this]
          exact hη_at'.contMDiffWithinAt
        · exact Set.mapsTo_univ _ _
      rw [contMDiffWithinAt_iff_contDiffWithinAt] at h_sym_at
      exact h_sym_at
    have h_toEuclSymm_smooth : ContDiff ℝ (⊤ : ℕ∞)
        (fun y' : EuclN => (toEuclidean (E := E)).symm y') :=
      (toEuclidean (E := E)).symm.contDiff
    have h_target_ext_open : IsOpen (extChartAt I α).target :=
      isOpen_extChartAt_target (I := I) α
    have h_target_nhds : (extChartAt I α).target ∈ 𝓝
        ((toEuclidean (E := E)).symm y) :=
      h_target_ext_open.mem_nhds hsymm_target
    have h_outer_at :
        ContDiffAt ℝ ∞ (fun e : E => η_M ((extChartAt I α).symm e))
          ((toEuclidean (E := E)).symm y) :=
      hη_at_local.contDiffAt h_target_nhds
    exact h_outer_at.comp y h_toEuclSymm_smooth.contDiffAt
  · have h_Sα_compl_open : IsOpen (Sα : Set EuclN)ᶜ := hSα_closed.isOpen_compl
    have hy_nhds : (Sα : Set EuclN)ᶜ ∈ 𝓝 y :=
      h_Sα_compl_open.mem_nhds hy_off_Sα
    have hf_zero_evt : f =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) :=
      Filter.eventually_of_mem hy_nhds (fun y' hy' =>
        h_f_zero_off_Sα y' hy')
    exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ => (0 : ℝ)) y).congr_of_eventuallyEq
      hf_zero_evt

lemma etaEuclid_range_Icc (α : M) (η_M : M → ℝ)
    (hη_range : Set.range η_M ⊆ Set.Icc (0 : ℝ) 1) :
    Set.range (chartCutoffEuclidean (I := I) (M := M) α η_M) ⊆ Set.Icc (0 : ℝ) 1 := by
  classical
  rintro v ⟨y, hy⟩
  by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [etaEuclid_apply_of_mem (I := I) (M := M) α η_M hy_target] at hy
    rw [← hy]
    exact hη_range (Set.mem_range_self _)
  · rw [etaEuclid_apply_of_notMem (I := I) (M := M) α η_M hy_target] at hy
    rw [← hy]
    exact ⟨le_refl _, zero_le_one⟩

variable [IsManifold I ∞ M] in
lemma etaEuclid_eq_one_of_eta_eq_one
    [T2Space M] [SigmaCompactSpace M] (α : M) (η_M : M → ℝ)
    (hη_one : ∀ x ∈ tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU
      I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ), η_M x = 1)
    {y : EuclN}
    (hy : y ∈ (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) ''
      tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :
    chartCutoffEuclidean (I := I) (M := M) α η_M y = 1 := by
  classical
  obtain ⟨x, hx_support, hxy⟩ := hy
  have hx_chart : x ∈ (chartAt H α).source :=
    CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M α hx_support
  have hx_ext : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hx_chart
  have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α := by
    rw [← hxy]
    exact ⟨extChartAt I α x, (extChartAt I α).map_source hx_ext, rfl⟩
  rw [etaEuclid_apply_of_mem (I := I) (M := M) α η_M hy_target]
  set z : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hz_def
  have hsymm_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy_target
    exact hy_target
  have hz_source : z ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hsymm_target
  have hz_eq_x : z = x := by
    have h_chart : extChartAt I α z = (toEuclidean (E := E)).symm y :=
      (extChartAt I α).right_inv hsymm_target
    have h_x_chart : extChartAt I α x = (toEuclidean (E := E)).symm y := by
      have : (toEuclidean (E := E)) (extChartAt I α x) = y := hxy
      have := congr_arg ((toEuclidean (E := E)).symm) this
      rw [(toEuclidean (E := E)).symm_apply_apply] at this
      exact this
    have h_eq : extChartAt I α z = extChartAt I α x := h_chart.trans h_x_chart.symm
    exact (extChartAt I α).injOn hz_source hx_ext h_eq
  rw [hz_eq_x]
  exact hη_one x hx_support

lemma hasCompactSupport_etaEuclid (α : M) (η_M : M → ℝ)
    (hη_compact : HasCompactSupport η_M)
    (h_tsupp_chart : tsupport η_M ⊆ (chartAt H α).source) :
    HasCompactSupport (chartCutoffEuclidean (I := I) (M := M) α η_M) := by
  have h_tsupp_compact_image : IsCompact
      ((fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' tsupport η_M) :=
    chartImage_isCompact_of_compact_in_source (I := I) (M := M) α
      hη_compact h_tsupp_chart
  have hf_support_in : tsupport (chartCutoffEuclidean (I := I) (M := M) α η_M) ⊆
      (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' tsupport η_M :=
    tsupport_etaEuclid_subset_chartImage (I := I) (M := M) α η_M
      hη_compact h_tsupp_chart
  refine HasCompactSupport.intro' (K := _) h_tsupp_compact_image
    h_tsupp_compact_image.isClosed ?_
  intro y hy_off
  have : y ∉ tsupport (chartCutoffEuclidean (I := I) (M := M) α η_M) :=
    fun h => hy_off (hf_support_in h)
  exact image_eq_zero_of_notMem_tsupport this

section

variable [IsManifold I ∞ M]

lemma exists_grad_bound_etaEuclid [I.Boundaryless] (α : M) (η_M : M → ℝ)
    (hη_smooth : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ η_M)
    (hη_compact : HasCompactSupport η_M)
    (h_tsupp_chart : tsupport η_M ⊆ (chartAt H α).source) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : EuclN, ‖fderiv ℝ (chartCutoffEuclidean (I := I) (M := M) α η_M) x‖ ≤
      C := by
  set f : EuclN → ℝ := chartCutoffEuclidean (I := I) (M := M) α η_M
  have hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f :=
    contDiff_etaEuclid (I := I) (M := M) α η_M hη_smooth hη_compact h_tsupp_chart
  have hf_compact : HasCompactSupport f :=
    hasCompactSupport_etaEuclid (I := I) (M := M) α η_M hη_compact h_tsupp_chart
  exact exists_grad_bound_of_compactSupport_smooth hf_smooth hf_compact

theorem exists_strict_strong_support_approx
    [I.Boundaryless] [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    (α : M) :
    ∃ K_α : Set M, IsCompact K_α ∧ K_α ⊆ (chartAt H α).source ∧
      tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆ interior K_α ∧
      ∀ {u : M → ℝ}, MemWkpChart (I := I) (M := M) 1 p u →
        ∀ ε_per > 0,
          ∃ χ : EuclN → ℝ,
            ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
            tsupport χ ⊆
              (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_α ∧
            Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := Module.finrank ℝ E) 1 p
              (fun y => chartPushed (I := I) (M := M)
                  (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u y - χ y)
              (chartTargetEuclid (I := I) (M := M) α) ≤
              ENNReal.ofReal ε_per := by
  classical
  obtain ⟨K_α, hK_compact, hK_chart, h_tsupp_in_int_K⟩ :=
    exists_compact_neighborhood_of_tsupport_pou (I := I) (M := M) α
  obtain ⟨η_M, hη_smooth_M, hη_range_M, hη_support_eq, hη_one_M, hη_tsupp_chart_K⟩ :=
    exists_manifold_cutoff_one_on_tsupport_pou (I := I) (M := M) α hK_compact
      h_tsupp_in_int_K
  have hη_tsupp_chart_α : tsupport η_M ⊆ (chartAt H α).source :=
    hη_tsupp_chart_K.trans hK_chart
  have hη_compact_M : HasCompactSupport η_M :=
    hK_compact.of_isClosed_subset (isClosed_tsupport _) hη_tsupp_chart_K
  set ηE : EuclN → ℝ := chartCutoffEuclidean (I := I) (M := M) α η_M with hηE_def
  have hηE_smooth : ContDiff ℝ (⊤ : ℕ∞) ηE :=
    contDiff_etaEuclid (I := I) (M := M) α η_M hη_smooth_M hη_compact_M hη_tsupp_chart_α
  have hηE_compact : HasCompactSupport ηE :=
    hasCompactSupport_etaEuclid (I := I) (M := M) α η_M hη_compact_M hη_tsupp_chart_α
  have hηE_range : Set.range ηE ⊆ Set.Icc (0 : ℝ) 1 :=
    etaEuclid_range_Icc (I := I) (M := M) α η_M hη_range_M
  have hηE_norm_one : ∀ y : EuclN, ‖ηE y‖ ≤ 1 :=
    norm_le_one_of_range_Icc hηE_range
  have hηE_tsupp_in_image_K : tsupport ηE ⊆
      (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_α := by
    refine subset_trans
      (tsupport_etaEuclid_subset_chartImage (I := I) (M := M) α η_M
        hη_compact_M hη_tsupp_chart_α) ?_
    exact Set.image_mono hη_tsupp_chart_K
  have hηE_one_on_pou_image :
      ∀ y ∈ (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) ''
        tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ),
      ηE y = 1 := fun y hy =>
    etaEuclid_eq_one_of_eta_eq_one (I := I) (M := M) α η_M hη_one_M hy
  obtain ⟨Cη, _hCη_pos, hCη_grad⟩ :=
    exists_grad_bound_etaEuclid (I := I) (M := M) α η_M
      hη_smooth_M hη_compact_M hη_tsupp_chart_α
  set C : ℝ := max Cη 1 with hC_def
  have hC_one : ∀ y : EuclN, ‖ηE y‖ ≤ C :=
    fun y => (hηE_norm_one y).trans (le_max_right _ _)
  have hC_grad : ∀ y : EuclN, ‖fderiv ℝ ηE y‖ ≤ C :=
    fun y => (hCη_grad y).trans (le_max_left _ _)
  set Ωα : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩα_def
  have hΩα_open : IsOpen Ωα := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hC_one_on_Ωα : ∀ y ∈ Ωα, ‖ηE y‖ ≤ C := fun y _ => hC_one y
  have hC_grad_on_Ωα : ∀ y ∈ Ωα, ‖fderiv ℝ ηE y‖ ≤ C := fun y _ => hC_grad y
  have hC_nonneg : 0 ≤ C := le_trans zero_le_one (le_max_right _ _)
  have hηE_iter_bound :
      ∀ j ≤ 1, ∀ y ∈ Ωα, ‖iteratedFDeriv ℝ j ηE y‖ ≤ C := by
    intro j hj y hy
    interval_cases j
    · rw [norm_iteratedFDeriv_zero]; exact hC_one_on_Ωα y hy
    · rw [norm_iteratedFDeriv_one]; exact hC_grad_on_Ωα y hy
  obtain ⟨K_leib, hK_leib_pos, hK_leib_bound⟩ :=
    Sobolev.Euclidean.wkpNorm_smul_smooth_bounded_le_one
      1 (le_refl _) (d := Module.finrank ℝ E) hp_one hΩα_open hηE_smooth
      hC_nonneg hηE_iter_bound
  refine ⟨K_α, hK_compact, hK_chart, h_tsupp_in_int_K, ?_⟩
  intro u hu ε_per hε_per
  classical
  set ε_inner : ℝ := ε_per / (K_leib + 1) with hε_inner_def
  have hε_inner_pos : 0 < ε_inner := by
    apply div_pos hε_per
    linarith
  obtain ⟨ψ, hψ_smooth, hψ_compact, hψ_support, hψ_close⟩ :=
    exists_smooth_strong_support_approx (I := I) (M := M) hp_one hp_top hu α ε_inner
      hε_inner_pos
  set χ : EuclN → ℝ := fun y => ηE y * ψ y with hχ_def
  have hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ := hηE_smooth.mul hψ_smooth
  have hχ_support_in : tsupport χ ⊆ tsupport ηE := by
    change tsupport (fun y => ηE y * ψ y) ⊆ tsupport ηE
    refine closure_mono ?_
    intro y hy
    simp only [Function.mem_support, ne_eq] at hy
    have hηE_ne : ηE y ≠ 0 := by
      intro h0
      apply hy
      rw [h0]; ring
    exact Function.mem_support.mpr hηE_ne
  have hχ_compact : HasCompactSupport χ :=
    hηE_compact.of_isClosed_subset (isClosed_tsupport _) hχ_support_in
  have hχ_support_image_K : tsupport χ ⊆
      (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_α :=
    hχ_support_in.trans hηE_tsupp_in_image_K
  refine ⟨χ, hχ_smooth, hχ_compact, hχ_support_image_K, ?_⟩
  set f : EuclN → ℝ := chartPushed (I := I) (M := M)
    (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u with hf_def
  have h_one_minus_ηE_f_zero : ∀ y ∈ Ωα, (1 - ηE y) * f y = 0 := by
    intro y hy
    by_cases hf_zero : f y = 0
    · rw [hf_zero]; ring
    · have hy_in_image : y ∈ chartImagePOUTsupport (I := I) (M := M) α := by
        by_contra hy_off
        apply hf_zero
        exact chartPushed_eq_zero_off_chartImagePOUTsupport (I := I) (M := M)
          α u hy hy_off
      have hy_in_image' :
          y ∈ (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) ''
            tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
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
    intro y hy
    exact h_decomp y hy
  have h_norm_eq :
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 p (fun y => f y - χ y) Ωα =
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 p (fun y => ηE y * (f y - ψ y)) Ωα :=
    Sobolev.Euclidean.wkpNorm_congr_ae
      (d := Module.finrank ℝ E) hp_one hΩα_open h_diff_eq
  have hf_mem :
      Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 1 p f Ωα := hu α
  have hψ_mem :
      Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 1 p ψ Ωα :=
    Sobolev.Euclidean.MemWkp_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hΩα_open hψ_smooth hψ_compact hψ_support hp_one 1
  have hfψ_mem :
      Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 1 p (fun y => f y - ψ y) Ωα :=
    Sobolev.Euclidean.MemWkp.sub
      (d := Module.finrank ℝ E) hp_one hΩα_open hf_mem hψ_mem
  have h_leib_bound :
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 p (fun y => ηE y * (f y - ψ y)) Ωα ≤
      ENNReal.ofReal K_leib *
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 p (fun y => f y - ψ y) Ωα :=
    hK_leib_bound hfψ_mem
  rw [h_norm_eq]
  refine h_leib_bound.trans ?_
  have h_step : ENNReal.ofReal K_leib *
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 p (fun y => f y - ψ y) Ωα ≤
      ENNReal.ofReal K_leib * ENNReal.ofReal ε_inner := by
    exact mul_le_mul_of_nonneg_left hψ_close (by simp : (0 : ℝ≥0∞) ≤ ENNReal.ofReal K_leib)
  refine h_step.trans ?_
  have hK_leib_nn : 0 ≤ K_leib := hK_leib_pos.le
  have hε_inner_nn : 0 ≤ ε_inner := hε_inner_pos.le
  rw [← ENNReal.ofReal_mul hK_leib_nn]
  apply ENNReal.ofReal_le_ofReal
  rw [hε_inner_def]
  rw [mul_div_assoc']
  have hK1_pos : 0 < K_leib + 1 := by linarith
  rw [div_le_iff₀ hK1_pos]
  have : K_leib * ε_per ≤ (K_leib + 1) * ε_per := by
    refine mul_le_mul_of_nonneg_right ?_ hε_per.le
    linarith
  linarith

end

end Chart
end Sobolev
