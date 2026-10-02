-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Chart/CrossChartBounds/CrossChartBoundStrictMemWkpHigherOrder.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Euclidean.SupportAndDomain.CrossChartBoundStrictMemWkp
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

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem crossChartJointK
    [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (k : ℕ) {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    (γ α : M) {K_α : Set M} (hK_compact : IsCompact K_α)
    (hK_α_in_α : K_α ⊆ (chartAt H α).source) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ},
        Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) k p v
            (chartTargetEuclid (I := I) (M := M) α) →
        tsupport v ⊆
          (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_α →
        Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) k p
            (chartPushed (I := I) (M := M)
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M) γ
              (chartPullback I α v))
            (chartTargetEuclid (I := I) (M := M) γ) ∧
          Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) k p
            (chartPushed (I := I) (M := M)
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M) γ
              (chartPullback I α v))
            (chartTargetEuclid (I := I) (M := M) γ) ≤
          ENNReal.ofReal K *
            Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := Module.finrank ℝ E) k p v
              (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set K_M : Set M := K_α ∩ tsupport
    ((CalabiYau.RiemannianVolume.chartAtlasPOU I M γ
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hKM_def
  have hKM_compact : IsCompact K_M :=
    hK_compact.inter_right (isClosed_tsupport _)
  have hKM_in_α : K_M ⊆ (chartAt H α).source := fun x hx => hK_α_in_α hx.1
  have hKM_in_γ : K_M ⊆ (chartAt H γ).source := fun x hx =>
    CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M γ hx.2
  by_cases hKM_empty : K_M = ∅
  · refine ⟨1, one_pos, ?_⟩
    intro v _hv_mem hv_support
    have h_pushed_zero := chartPushed_chartPullback_zero_of_K_M_empty
      (I := I) (M := M) γ α hK_α_in_α hKM_empty hv_support
    rw [h_pushed_zero]
    refine ⟨Sobolev.Euclidean.MemWkp_zero_fun
      (d := Module.finrank ℝ E) hp_one
      (chartTargetEuclid_isOpen (I := I) (M := M) γ), ?_⟩
    rw [Sobolev.Euclidean.wkpNorm_zero_fun_zero
      (d := Module.finrank ℝ E) hp_one
      (chartTargetEuclid_isOpen (I := I) (M := M) γ)]
    exact zero_le
  obtain ⟨Ω_γα, Ω_αγ, hΩγα_open, hΩαγ_open, hΩγα_subset_target, hΩαγ_subset_target,
    hΩγα_subset_overlap, _hΩαγ_subset_overlap, hKM_image_in_Ωγα, Φ,
    hΦ_eq_on_Ωγα, _hΦ_inv_eq_on_Ωαγ⟩ :=
    chartTransition_smoothDiffeoBoundedAtOrder_strict (I := I) (M := M)
      γ α hKM_compact hKM_in_γ hKM_in_α k
  set K_E_γ : Set EuclN :=
    (fun x : M => (toEuclidean (E := E)) (extChartAt I γ x)) '' K_M
    with hKEγ_def
  set K_E_α : Set EuclN :=
    (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_M
    with hKEα_def
  have hKEγ_compact : IsCompact K_E_γ :=
    chartImage_isCompact_of_compact_in_source (I := I) (M := M) γ hKM_compact hKM_in_γ
  have hKEα_compact : IsCompact K_E_α :=
    chartImage_isCompact_of_compact_in_source (I := I) (M := M) α hKM_compact hKM_in_α
  have hKEγ_subset_target : K_E_γ ⊆ chartTargetEuclid (I := I) (M := M) γ := by
    intro y hy
    rcases hy with ⟨x, hxK, hxy⟩
    have hx_chart : x ∈ (chartAt H γ).source := hKM_in_γ hxK
    have hx_ext : x ∈ (extChartAt I γ).source := by rw [extChartAt_source]; exact hx_chart
    have h_target : extChartAt I γ x ∈ (extChartAt I γ).target :=
      (extChartAt I γ).map_source hx_ext
    rw [← hxy]; exact ⟨extChartAt I γ x, h_target, rfl⟩
  have hKEα_subset_target : K_E_α ⊆ chartTargetEuclid (I := I) (M := M) α := by
    intro y hy
    rcases hy with ⟨x, hxK, hxy⟩
    have hx_chart : x ∈ (chartAt H α).source := hKM_in_α hxK
    have hx_ext : x ∈ (extChartAt I α).source := by rw [extChartAt_source]; exact hx_chart
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
      refine ⟨(toEuclidean (E := E)) (extChartAt I γ x), ?_, ?_⟩
      · exact ⟨x, hxK, rfl⟩
      · have := hΦ_eq_KM x hxK
        rw [this]; exact hxz
    · rintro ⟨y, hy, hyz⟩
      rcases hy with ⟨x, hxK, hxy⟩
      refine ⟨x, hxK, ?_⟩
      have := hΦ_eq_KM x hxK
      rw [← hyz, ← hxy, this]
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
  obtain ⟨δ_γ, η_γ_local, _hδ_γ_pos, _hδγ_subset, hη_γ_local_smooth, hη_γ_local_compact,
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
  obtain ⟨_δ_α, η_α_local, _hδ_α_pos, _hδα_subset, hη_α_local_smooth, hη_α_local_compact,
    hη_α_local_range, hη_α_local_one, hη_α_local_support⟩ :=
    Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      (d := Module.finrank ℝ E) hKEα_compact hUα_open hKEα_in_Uα
  have hη_α_local_support_Ωαγ : tsupport η_α_local ⊆ Ω_αγ :=
    fun y hy => (hη_α_local_support hy).1
  have hη_α_local_support_target : tsupport η_α_local ⊆ chartTargetEuclid (I := I) (M := M) α :=
    fun y hy => (hη_α_local_support hy).2
  set ρ_γ_M : M → ℝ :=
    ((CalabiYau.RiemannianVolume.chartAtlasPOU I M γ
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hρ_γ_M_def
  have hρ_γ_M_smooth : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ ρ_γ_M :=
    (CalabiYau.RiemannianVolume.chartAtlasPOU I M γ
      : C^∞⟮I, M; ℝ⟯).contMDiff
  have hρ_γ_M_support_in_chart : tsupport ρ_γ_M ⊆ (chartAt H γ).source :=
    CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M γ
  have hρ_γ_M_compact : HasCompactSupport ρ_γ_M :=
    (isClosed_tsupport _).isCompact
  have hρ_γ_M_range : Set.range ρ_γ_M ⊆ Set.Icc (0 : ℝ) 1 := by
    rintro _ ⟨x, rfl⟩
    refine ⟨(CalabiYau.RiemannianVolume.chartAtlasPOU I M).nonneg γ x,
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M).le_one γ x⟩
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
    _root_.Sobolev.Euclidean.exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      hη_combined_smooth hη_combined_compact k
  obtain ⟨C_α, hC_α_nn, hC_α_bound⟩ :=
    _root_.Sobolev.Euclidean.exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      hη_α_local_smooth hη_α_local_compact k
  set Ωγ_target : Set EuclN := chartTargetEuclid (I := I) (M := M) γ with hΩγ_target_def
  set Ωα_target : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩα_target_def
  have hΩγ_target_open : IsOpen Ωγ_target := chartTargetEuclid_isOpen (I := I) (M := M) γ
  have hΩα_target_open : IsOpen Ωα_target := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hη_combined_iter_bound :
      ∀ j ≤ k, ∀ y ∈ Ω_γα, ‖iteratedFDeriv ℝ j η_combined y‖ ≤ C_combined := by
    intro j hj y _; exact hC_combined_bound y j hj
  obtain ⟨K_leib, hK_leib_pos, hK_leib_bound⟩ :=
    Sobolev.Euclidean.wkpNorm_smul_smooth_bounded_le
      k hp_one hΩγα_open hη_combined_smooth hC_combined_nn
      hη_combined_iter_bound
  have hη_α_local_iter_bound :
      ∀ j ≤ k, ∀ y ∈ Ωα_target, ‖iteratedFDeriv ℝ j η_α_local y‖ ≤ C_α := by
    intro j hj y _; exact hC_α_bound y j hj
  obtain ⟨K_leib_α, hK_leib_α_pos, hK_leib_α_bound⟩ :=
    Sobolev.Euclidean.wkpNorm_smul_smooth_bounded_le
      k hp_one hΩα_target_open hη_α_local_smooth hC_α_nn
      hη_α_local_iter_bound
  set K_chain : ℝ := Φ.wkpCompositionConstant k p with hK_chain_def
  have hK_chain_pos : 0 < K_chain := by
    have hp_zero : p ≠ 0 := by
      intro hpz; rw [hpz] at hp_one; exact absurd hp_one (by norm_num)
    have hq_pos : 0 < p.toReal := ENNReal.toReal_pos hp_zero hp_top
    have hjLB_pos : 0 < Φ.jacobianLowerBound := Φ.jacobian_lower_bound_pos
    have hjLB_inv_pos : 0 < 1 / Φ.jacobianLowerBound := by positivity
    have hKchg_pos : 0 < (1 / Φ.jacobianLowerBound) ^ (1 / p.toReal) :=
      Real.rpow_pos_of_pos hjLB_inv_pos _
    rw [hK_chain_def]
    unfold Sobolev.Euclidean.SmoothDiffeoBoundedAtOrder.wkpCompositionConstant
    have h_zero_in : (0 : ℕ) ∈ Finset.range (k + 1) :=
      Finset.mem_range.mpr (Nat.zero_lt_succ _)
    have h_at_zero : (Fintype.card (Fin 0 → Fin (Module.finrank ℝ E)) : ℝ) = 1 := by
      have h_card : Fintype.card (Fin 0 → Fin (Module.finrank ℝ E)) = 1 := by
        rw [Fintype.card_fun]; simp
      exact_mod_cast h_card
    have h_card_pos : 0 < (Finset.range (k + 1)).sum
        (fun j => (Fintype.card (Fin j → Fin (Module.finrank ℝ E)) : ℝ)) := by
      have h_le := Finset.single_le_sum (s := Finset.range (k + 1))
        (f := fun j => (Fintype.card (Fin j → Fin (Module.finrank ℝ E)) : ℝ))
        (fun j _ => by positivity) h_zero_in
      rw [h_at_zero] at h_le
      linarith
    have h_kfact_D_pos : 0 < (k.factorial : ℝ) * Φ.derivBoundMaxOne ^ k := by
      refine mul_pos ?_ ?_
      · exact_mod_cast Nat.factorial_pos k
      · exact pow_pos Φ.derivBoundMaxOne_pos k
    have h_k1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.zero_lt_succ k
    positivity
  set K : ℝ := K_leib * K_chain * K_leib_α with hK_def
  have hK_pos : 0 < K := mul_pos (mul_pos hK_leib_pos hK_chain_pos) hK_leib_α_pos
  refine ⟨K, hK_pos, ?_⟩
  intro v hv_mem hv_support
  set χ_local : EuclN → ℝ := fun y => η_α_local y * v y with hχ_local_def
  have hχ_local_support_in_η_α : tsupport χ_local ⊆ tsupport η_α_local := by
    refine closure_mono ?_
    intro y hy
    simp only [Function.mem_support, ne_eq] at hy
    have h_η_ne : η_α_local y ≠ 0 := by
      intro h0; apply hy; change η_α_local y * v y = 0; rw [h0]; ring
    exact Function.mem_support.mpr h_η_ne
  have hχ_local_support_in_Ωαγ : tsupport χ_local ⊆ Ω_αγ :=
    hχ_local_support_in_η_α.trans hη_α_local_support_Ωαγ
  have hχ_local_support_in_Ωα_target : tsupport χ_local ⊆ Ωα_target :=
    hχ_local_support_in_η_α.trans hη_α_local_support_target
  have hχ_local_compact : HasCompactSupport χ_local :=
    hη_α_local_compact.of_isClosed_subset (isClosed_tsupport _) hχ_local_support_in_η_α
  have hχ_local_mem_Ωα_target : Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k p χ_local Ωα_target := by
    have h_bound : ∀ j ≤ k, ∀ x ∈ Ωα_target,
        ‖iteratedFDeriv ℝ j η_α_local x‖ ≤ C_α := hη_α_local_iter_bound
    exact Sobolev.Euclidean.MemWkp.smul_smooth_bounded
      (d := Module.finrank ℝ E) k hp_one hΩα_target_open hη_α_local_smooth h_bound hv_mem
  have hχ_local_pair_target_Ωαγ :=
    Sobolev.Euclidean.wkpNorm_eq_of_tsupport_subset
      (d := Module.finrank ℝ E) k hp_one hΩα_target_open hΩαγ_open
      hΩαγ_subset_target hχ_local_mem_Ωα_target hχ_local_support_in_Ωαγ
  have hχ_local_mem_Ωαγ : Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k p χ_local Ω_αγ := hχ_local_pair_target_Ωαγ.1
  have hχ_local_norm_target_eq_Ωαγ :
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p χ_local Ωα_target =
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p χ_local Ω_αγ := hχ_local_pair_target_Ωαγ.2
  set ψ_total : EuclN → ℝ := fun y => η_combined y * χ_local (Φ.toFun y) with hψ_total_def
  have hψ_total_support_in_η_combined : tsupport ψ_total ⊆ tsupport η_combined := by
    refine closure_mono ?_
    intro y hy
    simp only [Function.mem_support, ne_eq] at hy
    have h_η_ne : η_combined y ≠ 0 := by
      intro h0; apply hy; change η_combined y * χ_local (Φ.toFun y) = 0; rw [h0]; ring
    exact Function.mem_support.mpr h_η_ne
  have hψ_total_support_Ωγα : tsupport ψ_total ⊆ Ω_γα :=
    hψ_total_support_in_η_combined.trans hη_combined_support_Ωγα
  have hψ_total_compact : HasCompactSupport ψ_total :=
    hη_combined_compact.of_isClosed_subset (isClosed_tsupport _)
      hψ_total_support_in_η_combined
  have h_pointwise_eq : ∀ y ∈ Ωγ_target,
      chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) γ
          (chartPullback I α v) y = ψ_total y := by
    intro y hy_target
    set z : M := (extChartAt I γ).symm ((toEuclidean (E := E)).symm y) with hz_def
    have hsymm_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I γ).target := by
      have := hy_target
      rw [hΩγ_target_def, chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at this
      exact this
    have hz_source : z ∈ (extChartAt I γ).source :=
      (extChartAt I γ).map_target hsymm_target
    have hz_chartγ : z ∈ (chartAt H γ).source := by
      rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)] at hz_source
      exact hz_source
    have h_pushed_eq : chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) γ
        (chartPullback I α v) y =
        ρ_γ_M z * chartPullback I α v z := by
      unfold chartPushed
      rfl
    rw [h_pushed_eq]
    have hργE_y : ργE y = ρ_γ_M z := by
      rw [hργE_def]
      exact etaEuclid_apply_of_mem (I := I) (M := M) γ ρ_γ_M hy_target
    have hψ_total_y : ψ_total y = η_γ_local y * ργE y * χ_local (Φ.toFun y) := rfl
    rw [hψ_total_y]
    by_cases h_y_in_support_η_γ : y ∈ tsupport η_γ_local
    · have hy_in_Ωγα : y ∈ Ω_γα := hη_γ_local_support_Ωγα h_y_in_support_η_γ
      by_cases hρ_zero : ρ_γ_M z = 0
      · rw [hρ_zero, hργE_y, hρ_zero]; ring
      · have hz_in_tsupp_ρ : z ∈ tsupport ρ_γ_M := by
          have h_in : z ∈ Function.support ρ_γ_M := by
            simp only [Function.mem_support, ne_eq]; exact hρ_zero
          exact subset_tsupport _ h_in
        by_cases hz_in_α : z ∈ (chartAt H α).source
        · rw [chartPullback_apply_of_mem (I := I) (M := M) α v hz_in_α]
          by_cases hz_in_Kα : z ∈ K_α
          · have hz_in_KM : z ∈ K_M := ⟨hz_in_Kα, hz_in_tsupp_ρ⟩
            have hy_in_KEγ : y ∈ K_E_γ := by
              refine ⟨z, hz_in_KM, ?_⟩
              change (toEuclidean (E := E)) (extChartAt I γ z) = y
              have h_z_chart : extChartAt I γ z = (toEuclidean (E := E)).symm y :=
                (extChartAt I γ).right_inv hsymm_target
              rw [h_z_chart]
              exact (toEuclidean (E := E)).apply_symm_apply y
            have hη_γ_local_y : η_γ_local y = 1 := by
              apply hη_γ_local_one
              exact Metric.self_subset_cthickening K_E_γ hy_in_KEγ
            have hΦ_y : Φ.toFun y = (toEuclidean (E := E)) (extChartAt I α z) := by
              have h := hΦ_eq_KM z hz_in_KM
              have h_z_chart : extChartAt I γ z = (toEuclidean (E := E)).symm y :=
                (extChartAt I γ).right_inv hsymm_target
              have hy_eq : (toEuclidean (E := E)) (extChartAt I γ z) = y := by
                rw [h_z_chart]
                exact (toEuclidean (E := E)).apply_symm_apply y
              rw [← hy_eq]
              exact h
            rw [hΦ_y]
            have h_Φy_in_KEα : (toEuclidean (E := E)) (extChartAt I α z) ∈ K_E_α :=
              ⟨z, hz_in_KM, rfl⟩
            have hη_α_local_Φy : η_α_local ((toEuclidean (E := E)) (extChartAt I α z)) = 1 := by
              apply hη_α_local_one
              exact Metric.self_subset_cthickening K_E_α h_Φy_in_KEα
            have hχ_local_Φy : χ_local ((toEuclidean (E := E)) (extChartAt I α z)) =
                v ((toEuclidean (E := E)) (extChartAt I α z)) := by
              change η_α_local _ * v _ = v _
              rw [hη_α_local_Φy]; ring
            rw [hχ_local_Φy, hη_γ_local_y, hργE_y]
            ring
          · have hvα_z_eq : (toEuclidean (E := E)) (extChartAt I α z) ∉ tsupport v := by
              intro hin
              have := hv_support hin
              rcases this with ⟨x', hx'_K, hx'_eq⟩
              have hx'_chart : x' ∈ (chartAt H α).source := hK_α_in_α hx'_K
              have h_eq_chart_α : extChartAt I α x' = extChartAt I α z := by
                have h_eu : (toEuclidean (E := E)) (extChartAt I α x') =
                    (toEuclidean (E := E)) (extChartAt I α z) := hx'_eq
                exact (toEuclidean (E := E)).injective h_eu
              have hz_in_α_ext : z ∈ (extChartAt I α).source := by
                rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
                  (I := I) (M := M)]
                exact hz_in_α
              have hx'_α_ext : x' ∈ (extChartAt I α).source := by
                rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
                  (I := I) (M := M)]
                exact hx'_chart
              have h_inj := (extChartAt I α).injOn hx'_α_ext hz_in_α_ext h_eq_chart_α
              have : z ∈ K_α := by rw [← h_inj]; exact hx'_K
              exact hz_in_Kα this
            have hv_z : v ((toEuclidean (E := E)) (extChartAt I α z)) = 0 :=
              image_eq_zero_of_notMem_tsupport hvα_z_eq
            have hΦ_y : Φ.toFun y = (toEuclidean (E := E)) (extChartAt I α z) := by
              rw [hΦ_eq_on_Ωγα y hy_in_Ωγα]
              have h_z_chart : extChartAt I γ z = (toEuclidean (E := E)).symm y :=
                (extChartAt I γ).right_inv hsymm_target
              have hy_eq : (toEuclidean (E := E)) (extChartAt I γ z) = y := by
                rw [h_z_chart]
                exact (toEuclidean (E := E)).apply_symm_apply y
              rw [← hy_eq]
              exact chartTransitionEuclid_eq_chartα_image (I := I) (M := M) γ α hz_chartγ
            have hχ_local_zero : χ_local ((toEuclidean (E := E)) (extChartAt I α z)) = 0 := by
              change η_α_local _ * v _ = 0
              rw [hv_z]; ring
            rw [hΦ_y, hχ_local_zero, hv_z]; ring
        · rw [chartPullback_apply_of_notMem (I := I) (M := M) α v hz_in_α]
          exfalso
          have hy_in_overlap : y ∈ chartOverlapEuclid (I := I) (M := M) γ α :=
            hΩγα_subset_overlap hy_in_Ωγα
          unfold chartOverlapEuclid at hy_in_overlap
          rcases hy_in_overlap with ⟨z', ⟨w, hw_inter, hwz'⟩, hz'y⟩
          have hy_eq : (toEuclidean (E := E)) (extChartAt I γ w) = y := by
            rw [← hz'y, ← hwz']
          have h_w_chart_γ : w ∈ (extChartAt I γ).source := by
            rw [extChartAt_source]; exact hw_inter.1
          have h_z_eq_w : z = w := by
            have h_y_eq_chart : (toEuclidean (E := E)).symm y = extChartAt I γ w := by
              rw [← hy_eq, (toEuclidean (E := E)).symm_apply_apply]
            change (extChartAt I γ).symm ((toEuclidean (E := E)).symm y) = w
            rw [h_y_eq_chart]
            exact (extChartAt I γ).left_inv h_w_chart_γ
          rw [h_z_eq_w] at hz_in_α
          exact hz_in_α hw_inter.2
    · have h_zero : η_γ_local y = 0 := image_eq_zero_of_notMem_tsupport h_y_in_support_η_γ
      rw [h_zero]; simp only [zero_mul]
      by_cases hρ_zero : ρ_γ_M z = 0
      · rw [hρ_zero]; ring
      · have hz_in_tsupp_ρ : z ∈ tsupport ρ_γ_M := by
          have h_in : z ∈ Function.support ρ_γ_M := by
            simp only [Function.mem_support, ne_eq]; exact hρ_zero
          exact subset_tsupport _ h_in
        by_cases hpb_zero : chartPullback I α v z = 0
        · rw [hpb_zero]; ring
        · exfalso
          have hz_chartα : z ∈ (chartAt H α).source := by
            by_contra hcontra
            apply hpb_zero
            exact chartPullback_apply_of_notMem (I := I) (M := M) α v hcontra
          rw [chartPullback_apply_of_mem (I := I) (M := M) α v hz_chartα] at hpb_zero
          have h_arg_in_tsupp_v : (toEuclidean (E := E)) (extChartAt I α z) ∈ tsupport v := by
            have : (toEuclidean (E := E)) (extChartAt I α z) ∈ Function.support v := by
              simp only [Function.mem_support, ne_eq]; exact hpb_zero
            exact subset_tsupport _ this
          have h_arg_in_image_K_α : (toEuclidean (E := E)) (extChartAt I α z) ∈
              (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_α :=
            hv_support h_arg_in_tsupp_v
          obtain ⟨x', hx'_K_α, hx'_eq⟩ := h_arg_in_image_K_α
          have hx'_chart : x' ∈ (chartAt H α).source := hK_α_in_α hx'_K_α
          have h_eq_chart : extChartAt I α x' = extChartAt I α z := by
            have h_eu : (toEuclidean (E := E)) (extChartAt I α x') =
                (toEuclidean (E := E)) (extChartAt I α z) := hx'_eq
            exact (toEuclidean (E := E)).injective h_eu
          have hx'_α_ext : x' ∈ (extChartAt I α).source := by
            rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
              (I := I) (M := M)]; exact hx'_chart
          have hz_α_ext : z ∈ (extChartAt I α).source := by
            rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
              (I := I) (M := M)]; exact hz_chartα
          have h_inj := (extChartAt I α).injOn hx'_α_ext hz_α_ext h_eq_chart
          have hz_in_K_α : z ∈ K_α := by rw [← h_inj]; exact hx'_K_α
          have hz_in_K_M : z ∈ K_M := ⟨hz_in_K_α, hz_in_tsupp_ρ⟩
          have hy_in_KEγ : y ∈ K_E_γ := by
            refine ⟨z, hz_in_K_M, ?_⟩
            change (toEuclidean (E := E)) (extChartAt I γ z) = y
            have h_z_chart : extChartAt I γ z = (toEuclidean (E := E)).symm y :=
              (extChartAt I γ).right_inv hsymm_target
            rw [h_z_chart]
            exact (toEuclidean (E := E)).apply_symm_apply y
          have hy_in_cthick : y ∈ Metric.cthickening δ_γ K_E_γ :=
            Metric.self_subset_cthickening K_E_γ hy_in_KEγ
          have h_η_y_one : η_γ_local y = 1 := hη_γ_local_one y hy_in_cthick
          have h_ne_zero : η_γ_local y ≠ 0 := by linarith
          have hy_in_support : y ∈ Function.support η_γ_local := by
            simp only [Function.mem_support, ne_eq, h_ne_zero, not_false_eq_true]
          exact h_y_in_support_η_γ (subset_tsupport _ hy_in_support)
  have h_ae_eq : (chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) γ
        (chartPullback I α v)) =ᵐ[volume.restrict Ωγ_target] ψ_total := by
    refine (ae_restrict_iff' hΩγ_target_open.measurableSet).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy; exact h_pointwise_eq y hy
  have h_χ_local_comp_mem :
      Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) k p (fun y => χ_local (Φ.toFun y)) Ω_γα :=
    Sobolev.Euclidean.MemWkp.comp_smoothDiffeoBoundedAtOrder
      (d := Module.finrank ℝ E) k (le_refl k) hp_one hp_top hΩγα_open hΩαγ_open Φ
      hχ_local_mem_Ωαγ hχ_local_compact hχ_local_support_in_Ωαγ
  have hψ_total_mem_Ωγα :
      Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) k p ψ_total Ω_γα := by
    have h_bound : ∀ j ≤ k, ∀ x ∈ Ω_γα, ‖iteratedFDeriv ℝ j η_combined x‖ ≤ C_combined :=
      hη_combined_iter_bound
    exact Sobolev.Euclidean.MemWkp.smul_smooth_bounded
      (d := Module.finrank ℝ E) k hp_one hΩγα_open hη_combined_smooth h_bound
      h_χ_local_comp_mem
  have hψ_total_mem_target :
      Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) k p ψ_total Ωγ_target :=
    Sobolev.Euclidean.MemWkp.extend_zero
      (d := Module.finrank ℝ E) hp_one hΩγα_open hΩγ_target_open
      hΩγα_subset_target hψ_total_mem_Ωγα hψ_total_support_Ωγα hψ_total_compact
  have h_pushed_mem :
      Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) k p
        (chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) γ
          (chartPullback I α v)) Ωγ_target :=
    (Sobolev.Euclidean.MemWkp_congr_ae
      (d := Module.finrank ℝ E) hp_one hΩγ_target_open h_ae_eq).mpr
        hψ_total_mem_target
  refine ⟨h_pushed_mem, ?_⟩
  rw [Sobolev.Euclidean.wkpNorm_congr_ae
        (d := Module.finrank ℝ E) hp_one hΩγ_target_open h_ae_eq]
  have h_bridge_γ :
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p ψ_total Ωγ_target ≤
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p ψ_total Ω_γα :=
    Sobolev.Euclidean.wkpNorm_le_of_tsupport_subset_mem_small
      (d := Module.finrank ℝ E) k hp_one hΩγ_target_open hΩγα_open
      hΩγα_subset_target hψ_total_mem_Ωγα hψ_total_support_Ωγα
  refine h_bridge_γ.trans ?_
  have h_leib_step : Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) k p ψ_total Ω_γα ≤
      ENNReal.ofReal K_leib *
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p (fun y => χ_local (Φ.toFun y)) Ω_γα :=
    hK_leib_bound h_χ_local_comp_mem
  refine h_leib_step.trans ?_
  have h_chain_step :
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p (fun y => χ_local (Φ.toFun y)) Ω_γα ≤
      ENNReal.ofReal K_chain *
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p χ_local Ω_αγ :=
    Sobolev.Euclidean.SmoothDiffeoBoundedAtOrder.wkpNorm_comp_le
      hp_one hp_top hΩγα_open hΩαγ_open Φ k (le_refl k)
      hχ_local_mem_Ωαγ hχ_local_compact hχ_local_support_in_Ωαγ
  have h_chain_step_target :
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p (fun y => χ_local (Φ.toFun y)) Ω_γα ≤
      ENNReal.ofReal K_chain *
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p χ_local Ωα_target := by
    refine h_chain_step.trans ?_
    rw [hχ_local_norm_target_eq_Ωαγ]
  have h_leib_α_step : Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) k p χ_local Ωα_target ≤
      ENNReal.ofReal K_leib_α *
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p v Ωα_target := by
    have h_eq : χ_local = (fun y => η_α_local y * v y) := rfl
    rw [h_eq]
    exact hK_leib_α_bound hv_mem
  have h_chain_combined : Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) k p (fun y => χ_local (Φ.toFun y)) Ω_γα ≤
      ENNReal.ofReal K_chain *
        (ENNReal.ofReal K_leib_α *
          Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) k p v Ωα_target) := by
    refine h_chain_step_target.trans ?_
    exact mul_le_mul_of_nonneg_left h_leib_α_step (zero_le)
  refine (mul_le_mul_of_nonneg_left h_chain_combined (zero_le)).trans ?_
  have h_K_eq : ENNReal.ofReal K_leib *
      (ENNReal.ofReal K_chain * (ENNReal.ofReal K_leib_α *
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p v Ωα_target)) =
      ENNReal.ofReal K *
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p v Ωα_target := by
    rw [hK_def]
    rw [ENNReal.ofReal_mul (mul_pos hK_leib_pos hK_chain_pos).le]
    rw [ENNReal.ofReal_mul hK_leib_pos.le]
    ring
  exact h_K_eq ▸ le_refl _

theorem cross_chart_bound_strict_strong_memWkp_k
    [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (k : ℕ) {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    (γ α : M) {K_α : Set M} (hK_compact : IsCompact K_α)
    (hK_α_in_α : K_α ⊆ (chartAt H α).source) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ},
        Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) k p v
            (chartTargetEuclid (I := I) (M := M) α) →
        tsupport v ⊆
          (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_α →
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p
          (chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) γ
            (chartPullback I α v))
          (chartTargetEuclid (I := I) (M := M) γ) ≤
        ENNReal.ofReal K *
          Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) k p v
            (chartTargetEuclid (I := I) (M := M) α) := by
  obtain ⟨K, hK, hjoint⟩ := crossChartJointK (I := I) (M := M)
    k hp_one hp_top γ α hK_compact hK_α_in_α
  refine ⟨K, hK, ?_⟩
  intro v hv hv_support
  exact (hjoint hv hv_support).2

end Chart
end Sobolev
