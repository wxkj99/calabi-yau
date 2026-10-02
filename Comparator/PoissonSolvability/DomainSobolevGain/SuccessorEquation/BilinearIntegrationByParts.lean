module

public import Comparator.PoissonSolvability.DomainSobolevGain.SuccessorEquation.MixedIntegrationByParts

/-!
# Principal, mass and forcing integration by parts for the successor equation

Proof-preserving extraction from the checked successor weak-equation assembly.
Source: DifferentialGeometry `7a48598d35109aa99d1cc678e2724c213cdf4ff3`,
`Iterated/VariationalIdentity/InductiveSuccessor.lean:251-577`.
The forcing is the actual `SuccessorSource` definition; no copied forcing definition is used.
-/

public section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace CalabiYau.PoissonDomainRegularity.SuccessorEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.Analysis.Laplacian
open CalabiYau.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open Sobolev.Euclidean
open CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl
open CalabiYau.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.DifferentiatedCrossTermIBP

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
theorem ibp_density_fChartEffectivePrev
    (g : SmoothRiemannianMetric I M) (α : M)
    {fChartEffectivePrev : EuclN → ℝ}
    (h_fChartEffectivePrev_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 fChartEffectivePrev
        (chartTargetEuclid (I := I) (M := M) α))
    (l : Fin (Module.finrank ℝ E))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * fChartEffectivePrev y *
        (fderiv ℝ ψ y) (EuclideanSpace.single l 1)
      ∂(volume : Measure EuclN))
    = -((∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fderiv ℝ (densityOnEuclid (I := I) g α) y)
              (EuclideanSpace.single l 1) *
            fChartEffectivePrev y * ψ y
          ∂(volume : Measure EuclN))
      + (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 l fChartEffectivePrev
              (chartTargetEuclid (I := I) (M := M) α) y *
            ψ y
          ∂(volume : Measure EuclN))) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set v : EuclN → ℝ := fChartEffectivePrev with hv_def
  set w : Fin (Module.finrank ℝ E) → EuclN → ℝ := fun j =>
    chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 j v Ω with hw_def
  have h_v_memLp : MemLp v 2 ((volume : Measure EuclN).restrict Ω) :=
    h_fChartEffectivePrev_memW1p.1
  have hv_localMemLp : ∀ K' : Set EuclN, IsCompact K' → K' ⊆ Ω →
      MemLp v 2 ((volume : Measure EuclN).restrict K') := by
    intro K' hK'_compact hK'_in
    have hK'_meas : MeasurableSet K' := hK'_compact.isClosed.measurableSet
    have h_eq : ((volume : Measure EuclN).restrict Ω).restrict K' =
        (volume : Measure EuclN).restrict K' := by
      rw [Measure.restrict_restrict hK'_meas]
      congr 1
      exact Set.inter_eq_self_of_subset_left hK'_in
    rw [← h_eq]
    exact h_v_memLp.restrict K'
  have hw_global : ∀ j : Fin (Module.finrank ℝ E),
      MemLp (w j) 2 ((volume : Measure EuclN).restrict Ω) := fun j =>
    chosenWeakPartialOrZero_memLp_of_mem h_fChartEffectivePrev_memW1p j
  have hw_localMemLp : ∀ (j : Fin (Module.finrank ℝ E)) (K' : Set EuclN),
      IsCompact K' → K' ⊆ Ω →
      MemLp (w j) 2 ((volume : Measure EuclN).restrict K') := by
    intro j K' hK'_compact hK'_in
    have hK'_meas : MeasurableSet K' := hK'_compact.isClosed.measurableSet
    have h_eq : ((volume : Measure EuclN).restrict Ω).restrict K' =
        (volume : Measure EuclN).restrict K' := by
      rw [Measure.restrict_restrict hK'_meas]
      congr 1
      exact Set.inter_eq_self_of_subset_left hK'_in
    rw [← h_eq]
    exact (hw_global j).restrict K'
  have hw_isWeakPartial : ∀ j : Fin (Module.finrank ℝ E),
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) j (w j) v Ω :=
    fun j => chosenWeakPartialOrZero_isWeakPartial_of_mem h_fChartEffectivePrev_memW1p j
  have h_dens_chart : ContDiffOn ℝ (⊤ : ℕ∞)
      (densityOnEuclid (I := I) g α) Ω :=
    densityOnEuclid_contDiffOn (I := I) g α
  set K : Set EuclN := tsupport ψ with hK_def
  have hK_compact : IsCompact K := hψ_cs
  have hK_in : K ⊆ Ω := hψ_support
  obtain ⟨δ, dExt, hδ_pos, hδ_subset, hdExt_smooth, hdExt_eq⟩ :=
    exists_smooth_global_extension (I := I) (M := M)
      (φ := densityOnEuclid (I := I) g α) α h_dens_chart hK_compact hK_in
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have h_thick : Metric.cthickening δ K ⊆ Ω := hδ_subset
  have hK_in_thick : K ⊆ Metric.cthickening δ K := Metric.self_subset_cthickening _
  have h_fderiv_ψ_zero : ∀ x ∉ K, fderiv ℝ ψ x = 0 := by
    intro x hx
    have h_compl_open : IsOpen (Kᶜ) := (isClosed_tsupport _).isOpen_compl
    have hx_in_compl : x ∈ Kᶜ := hx
    have hψ_zero_neighborhood : ∀ᶠ y in 𝓝 x, ψ y = 0 := by
      filter_upwards [h_compl_open.mem_nhds hx_in_compl] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    have hψ_const_zero : fderiv ℝ ψ x = fderiv ℝ (fun _ : EuclN => (0 : ℝ)) x := by
      apply Filter.EventuallyEq.fderiv_eq
      filter_upwards [hψ_zero_neighborhood] with y hy
      rw [hy]
    rw [hψ_const_zero]; simp
  have h_ibp_ext :=
    integral_smul_weak_partial_eq (d := Module.finrank ℝ E) (Ω := Ω) hΩ_open
      (φ := dExt) hdExt_smooth (v := v) (w := w)
      hv_localMemLp hw_localMemLp hw_isWeakPartial l
      (ψ := ψ) hψ_smooth hψ_cs hψ_support
  have hLHS_eq :
      ∫ y in Ω, dExt y * v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l 1) ∂(volume : Measure EuclN) =
      ∫ y in Ω, densityOnEuclid (I := I) g α y * v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l 1) ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y hy => ?_)
    by_cases hy_K : y ∈ K
    · rw [hdExt_eq y (hK_in_thick hy_K)]
    · rw [h_fderiv_ψ_zero y hy_K]
      simp
  have h_fderiv_dExt_eq_dens : ∀ y ∈ K, ∀ j' : Fin (Module.finrank ℝ E),
      (fderiv ℝ dExt y) (EuclideanSpace.single j' 1) =
      (fderiv ℝ (densityOnEuclid (I := I) g α) y) (EuclideanSpace.single j' 1) := by
    intro y hy_K j'
    have hy_thick_open : y ∈ Metric.thickening δ K := by
      rw [Metric.mem_thickening_iff]
      refine ⟨y, hy_K, ?_⟩
      simp [hδ_pos]
    have h_thick_open : IsOpen (Metric.thickening δ K) := Metric.isOpen_thickening
    have h_neighborhood : Metric.thickening δ K ∈ 𝓝 y := h_thick_open.mem_nhds hy_thick_open
    have h_thick_sub : Metric.thickening δ K ⊆ Metric.cthickening δ K :=
      Metric.thickening_subset_cthickening _ _
    have h_eq_neighborhood : dExt =ᶠ[𝓝 y] densityOnEuclid (I := I) g α := by
      filter_upwards [h_neighborhood] with z hz
      exact hdExt_eq z (h_thick_sub hz)
    have h_fderiv_eq : fderiv ℝ dExt y = fderiv ℝ (densityOnEuclid (I := I) g α) y :=
      Filter.EventuallyEq.fderiv_eq h_eq_neighborhood
    rw [h_fderiv_eq]
  have hLeib1_eq :
      ∫ y in Ω, (fderiv ℝ dExt y) (EuclideanSpace.single l 1) * v y * ψ y
        ∂(volume : Measure EuclN) =
      ∫ y in Ω, (fderiv ℝ (densityOnEuclid (I := I) g α) y)
          (EuclideanSpace.single l 1) * v y * ψ y
        ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y hy => ?_)
    by_cases hy_K : y ∈ K
    · rw [h_fderiv_dExt_eq_dens y hy_K l]
    · have hψy : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy_K
      rw [hψy]; ring
  have hLeib2_eq :
      ∫ y in Ω, dExt y * w l y * ψ y ∂(volume : Measure EuclN) =
      ∫ y in Ω, densityOnEuclid (I := I) g α y * w l y * ψ y
        ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y hy => ?_)
    by_cases hy_K : y ∈ K
    · rw [hdExt_eq y (hK_in_thick hy_K)]
    · have hψy : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy_K
      rw [hψy]; ring
  rw [← hLHS_eq, ← hLeib1_eq, ← hLeib2_eq]
  exact h_ibp_ext

lemma snoc_cons_eq_cons_snoc {β : Type*} {m : ℕ}
    (i : β) (dirs : Fin m → β) (l : β) :
    @Fin.snoc m.succ (fun _ => β) (Fin.cons i dirs) l =
      Fin.cons i (Fin.snoc dirs l) :=
  (Fin.cons_snoc_eq_snoc_cons (β := β) i dirs l).symm

omit [NeZero (Module.finrank ℝ E)] in
theorem ibp_principal_pair
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g} (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (h_chart_H_m_plus_2 :
      MemWkp (d := Module.finrank ℝ E) (m + 2) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α))
    (l : Fin (Module.finrank ℝ E))
    (i j : Fin (Module.finrank ℝ E))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
        weightedInvGramOnEuclid (I := I) g α i j y *
          chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
            (m + 1) (Fin.cons i dirs) y *
          (fderiv ℝ (fun z : EuclN =>
            (fderiv ℝ ψ z) (EuclideanSpace.single l 1)) y)
              (EuclideanSpace.single j 1)
        ∂(volume : Measure EuclN))
    = -((∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fderiv ℝ (weightedInvGramOnEuclid (I := I) g α i j) y)
              (EuclideanSpace.single l 1) *
            chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
              (m + 1) (Fin.cons i dirs) y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
          ∂(volume : Measure EuclN))
      + (∫ y in chartTargetEuclid (I := I) (M := M) α,
          weightedInvGramOnEuclid (I := I) g α i j y *
            chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
              (m + 2) (Fin.cons i (Fin.snoc dirs l)) y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
          ∂(volume : Measure EuclN))) := by
  classical
  set ψ_j : EuclN → ℝ := fun y => (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
    with hψ_j_def
  have hψ_j_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ_j :=
    contDiff_fderiv_apply_single (ψ := ψ) hψ_smooth j
  have hψ_j_cs : HasCompactSupport ψ_j :=
    hasCompactSupport_fderiv_apply_single (ψ := ψ) hψ_cs j
  have hψ_j_support : tsupport ψ_j ⊆ chartTargetEuclid (I := I) (M := M) α :=
    (tsupport_fderiv_apply_single_subset ψ j).trans hψ_support
  have h_schwarz : ∀ y : EuclN,
      (fderiv ℝ (fun z : EuclN =>
        (fderiv ℝ ψ z) (EuclideanSpace.single l 1)) y)
          (EuclideanSpace.single j 1) =
      (fderiv ℝ ψ_j y) (EuclideanSpace.single l 1) := by
    intro y
    change (fderiv ℝ
        (fun z : EuclN => (fderiv ℝ ψ z) (EuclideanSpace.single l 1)) y)
          (EuclideanSpace.single j 1) =
      (fderiv ℝ
        (fun z : EuclN => (fderiv ℝ ψ z) (EuclideanSpace.single j 1)) y)
          (EuclideanSpace.single l 1)
    exact fderiv_apply_single_swap (ψ := ψ) hψ_smooth y j l
  have h_lhs_schwarz :
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
          weightedInvGramOnEuclid (I := I) g α i j y *
            chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
              (m + 1) (Fin.cons i dirs) y *
            (fderiv ℝ (fun z : EuclN =>
              (fderiv ℝ ψ z) (EuclideanSpace.single l 1)) y)
                (EuclideanSpace.single j 1)
          ∂(volume : Measure EuclN)) =
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
          weightedInvGramOnEuclid (I := I) g α i j y *
            chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
              (m + 1) (Fin.cons i dirs) y *
            (fderiv ℝ ψ_j y) (EuclideanSpace.single l 1)
          ∂(volume : Measure EuclN)) := by
    refine setIntegral_congr_fun
      (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
      (fun y _ => ?_)
    rw [h_schwarz y]
  rw [h_lhs_schwarz]
  have h_ibp := per_pair_ibp_chosenMthMixed
    (I := I) (M := M) g α (m + 1) (Fin.cons i dirs)
    h_chart_H_m_plus_2
    (weightedInvGramOnEuclid_contDiffOn (I := I) g α i j)
    hψ_j_smooth hψ_j_cs hψ_j_support l
  have h_snoc_cons :
      Fin.snoc (α := fun _ => Fin (Module.finrank ℝ E)) (Fin.cons i dirs) l =
        Fin.cons i (Fin.snoc dirs l) :=
    snoc_cons_eq_cons_snoc (β := Fin (Module.finrank ℝ E)) i dirs l
  rw [h_snoc_cons] at h_ibp
  exact h_ibp

omit [NeZero (Module.finrank ℝ E)] in
theorem ibp_mass
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g} (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (h_chart_H_m_plus_1 :
      MemWkp (d := Module.finrank ℝ E) (m + 1) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α))
    (l : Fin (Module.finrank ℝ E))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m dirs y *
          (fderiv ℝ ψ y) (EuclideanSpace.single l 1)
        ∂(volume : Measure EuclN))
    = -((∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fderiv ℝ (densityOnEuclid (I := I) g α) y)
              (EuclideanSpace.single l 1) *
            chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m dirs y *
            ψ y
          ∂(volume : Measure EuclN))
      + (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
              (m + 1) (Fin.snoc dirs l) y *
            ψ y
          ∂(volume : Measure EuclN))) :=
  per_pair_ibp_chosenMthMixed (I := I) (M := M) g α m dirs
    h_chart_H_m_plus_1
    (densityOnEuclid_contDiffOn (I := I) g α)
    hψ_smooth hψ_cs hψ_support l

omit [NeZero (Module.finrank ℝ E)] in
theorem ibp_inner_j
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g} (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (h_chart_H_m_plus_2 :
      MemWkp (d := Module.finrank ℝ E) (m + 2) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α))
    (l : Fin (Module.finrank ℝ E))
    (i j : Fin (Module.finrank ℝ E))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
        weightedInvGramDerivOnEuclid (I := I) g α i j l y *
          chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
            (m + 1) (Fin.cons i dirs) y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
        ∂(volume : Measure EuclN))
    = -((∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
              (EuclideanSpace.single j 1) *
            chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
              (m + 1) (Fin.cons i dirs) y *
            ψ y
          ∂(volume : Measure EuclN))
      + (∫ y in chartTargetEuclid (I := I) (M := M) α,
          weightedInvGramDerivOnEuclid (I := I) g α i j l y *
            chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
              (m + 2) (Fin.cons i (Fin.snoc dirs j)) y *
            ψ y
          ∂(volume : Measure EuclN))) := by
  classical
  have h_ibp := per_pair_ibp_chosenMthMixed
    (I := I) (M := M) g α (m + 1) (Fin.cons i dirs)
    h_chart_H_m_plus_2
    (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α i j l)
    hψ_smooth hψ_cs hψ_support j
  have h_snoc_cons :
      Fin.snoc (α := fun _ => Fin (Module.finrank ℝ E)) (Fin.cons i dirs) j =
        Fin.cons i (Fin.snoc dirs j) :=
    snoc_cons_eq_cons_snoc (β := Fin (Module.finrank ℝ E)) i dirs j
  rw [h_snoc_cons] at h_ibp
  exact h_ibp

end CalabiYau.PoissonDomainRegularity.SuccessorEquation
