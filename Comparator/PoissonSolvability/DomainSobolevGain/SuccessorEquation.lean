module

public import Comparator.PoissonSolvability.DomainSobolevGain.SuccessorSource
import Comparator.PoissonSolvability.DomainSobolevGain.SuccessorEquation.MixedIntegrationByParts
import Comparator.PoissonSolvability.DomainSobolevGain.SuccessorEquation.Support
import Comparator.PoissonSolvability.DomainSobolevGain.SuccessorEquation.BilinearIntegrationByParts
import Comparator.PoissonSolvability.DomainSobolevGain.SuccessorEquation.Integrability

/-!
# Weak equation for a successor directional sequence

Adapted from DifferentialGeometry at `7a48598d35109aa99d1cc678e2724c213cdf4ff3`,
`Iterated/VariationalIdentity/InductiveSuccessor.lean`, lines 643–1180.
The two analytic leaves are the forcing L² bound and this weak identity.
-/

@[expose] public section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace CalabiYau.PoissonDomainRegularity

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
open SuccessorEquation

/-- Differentiate the existing weak equation with the required forcing and solution regularity.
All commutation of selected weak partials in this proof must be almost everywhere. -/
theorem successorChart_variational_identity
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g} (m : ℕ)
    (D : IteratedDiffChartBilinearData (I := I) (M := M) g α u_h m)
    (l : Fin (Module.finrank ℝ E))
    (h_chart_H_m_plus_1 :
      Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) (m + 1) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α))
    (h_chart_H_m_plus_2 :
      Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) (m + 2) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α))
    (h_forcing_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      D.diffChartForcing (chartTargetEuclid (I := I) (M := M) α))
    (h_forcing_ae_zero :
      D.diffChartForcing =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ))) :
    ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
                (m + 1 + 1) (Fin.cons i (Fin.snoc D.directions l)) y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN)) +
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
            (m + 1) (Fin.snoc D.directions l) y * ψ y
        ∂(volume : Measure EuclN)) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          successorChartForcing g α u_h m D.directions D.diffChartForcing l y * ψ y
        ∂(volume : Measure EuclN) := by
  classical
  intro ψ hψ_smooth hψ_cs hψ_support
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  set Kα : Set EuclN := chartImagePOUTsupport (I := I) (M := M) α with hKα_def
  have hKα_compact : IsCompact Kα :=
    chartImagePOUTsupport_isCompact (I := I) (M := M) α
  have hKα_meas : MeasurableSet Kα := hKα_compact.isClosed.measurableSet
  have hKα_in : Kα ⊆ Ω := chartImagePOUTsupport_subset_target (I := I) (M := M) α
  have hΩ_diff_Kα_open : IsOpen (Ω \ Kα) := hΩ_open.sdiff hKα_compact.isClosed
  have hΩ_diff_Kα_meas : MeasurableSet (Ω \ Kα) := hΩ_diff_Kα_open.measurableSet
  set ψ_l : EuclN → ℝ := fun y =>
    (fderiv ℝ ψ y) (EuclideanSpace.single l 1) with hψ_l_def
  have hψ_l_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ_l :=
    contDiff_fderiv_apply_single (ψ := ψ) hψ_smooth l
  have hψ_l_cs : HasCompactSupport ψ_l :=
    hasCompactSupport_fderiv_apply_single (ψ := ψ) hψ_cs l
  have hψ_l_support : tsupport ψ_l ⊆ Ω :=
    (tsupport_fderiv_apply_single_subset ψ l).trans hψ_support
  have h_level_m :=
    D.m_diff_variational_identity ψ_l hψ_l_smooth hψ_l_cs hψ_l_support
  set A_pair : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j =>
      ∫ y in Ω,
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
            (EuclideanSpace.single j 1) *
          chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
            (m + 1) (Fin.cons i D.directions) y *
          ψ y
        ∂(volume : Measure EuclN) with hA_pair_def
  set B_pair : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j =>
      ∫ y in Ω,
        weightedInvGramDerivOnEuclid (I := I) g α i j l y *
          chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
            (m + 2) (Fin.cons i (Fin.snoc D.directions j)) y *
          ψ y
        ∂(volume : Measure EuclN) with hB_pair_def
  set PR_pair : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j =>
      ∫ y in Ω,
        weightedInvGramOnEuclid (I := I) g α i j y *
          chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
            (m + 2) (Fin.cons i (Fin.snoc D.directions l)) y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
        ∂(volume : Measure EuclN) with hPR_pair_def
  set INT_LHS_m_pair : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j =>
      ∫ y in Ω,
        weightedInvGramOnEuclid (I := I) g α i j y *
          chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
            (m + 1) (Fin.cons i D.directions) y *
          (fderiv ℝ ψ_l y) (EuclideanSpace.single j 1)
        ∂(volume : Measure EuclN) with hINT_LHS_m_pair_def
  have h_principal_pair : ∀ i j : Fin (Module.finrank ℝ E),
      INT_LHS_m_pair i j = A_pair i j + B_pair i j - PR_pair i j := by
    intro i j
    have h_pp := ibp_principal_pair (I := I) (M := M) g α m D.directions
      h_chart_H_m_plus_2 l i j hψ_smooth hψ_cs hψ_support
    have h_inner := ibp_inner_j (I := I) (M := M) g α m D.directions
      h_chart_H_m_plus_2 l i j hψ_smooth hψ_cs hψ_support
    have h_pp' : INT_LHS_m_pair i j =
        -((∫ y in Ω,
            weightedInvGramDerivOnEuclid (I := I) g α i j l y *
              chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
                (m + 1) (Fin.cons i D.directions) y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
            ∂(volume : Measure EuclN))
          + PR_pair i j) := h_pp
    rw [h_pp', h_inner]
    ring
  set K : Set EuclN := tsupport ψ with hK_def
  have hK_compact : IsCompact K := hψ_cs
  have hK_meas : MeasurableSet K := (isClosed_tsupport ψ).measurableSet
  have hK_in : K ⊆ Ω := hψ_support
  have h_aij_cont : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn (weightedInvGramOnEuclid (I := I) g α i j) Ω :=
    fun i j => (weightedInvGramOnEuclid_contDiffOn (I := I) g α i j).continuousOn
  have h_daij_cont : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn (weightedInvGramDerivOnEuclid (I := I) g α i j l) Ω :=
    fun i j =>
      (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α i j l).continuousOn
  have h_dens_cont : ContinuousOn (densityOnEuclid (I := I) g α) Ω :=
    densityOnEuclid_continuousOn (I := I) g α
  have h_dens_deriv_cont : ContinuousOn
      (densityDerivOnEuclid (I := I) g α l) Ω :=
    (densityDerivOnEuclid_contDiffOn (I := I) g α l).continuousOn
  have h_aij_fderiv_cont : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn (fun y : EuclN =>
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
          (EuclideanSpace.single j 1)) Ω := by
    intro i j
    have h_diffOn :
        ContDiffOn ℝ (⊤ : ℕ∞) (weightedInvGramDerivOnEuclid (I := I) g α i j l) Ω :=
      weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α i j l
    have h_fderiv_diff :
        ContDiffOn ℝ (⊤ : ℕ∞)
          (fun y => fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y) Ω :=
      ((contDiffOn_infty_iff_fderiv_of_isOpen hΩ_open).1 h_diffOn).2
    have h_eval : ContDiff ℝ (⊤ : ℕ∞)
        (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single j 1)) :=
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ))).contDiff
    exact (h_eval.contDiffOn.comp h_fderiv_diff (mapsTo_univ _ _)).continuousOn
  have h_dens_fderiv_cont : ContinuousOn (fun y : EuclN =>
        (fderiv ℝ (densityOnEuclid (I := I) g α) y)
          (EuclideanSpace.single l 1)) Ω := by
    change ContinuousOn (densityDerivOnEuclid (I := I) g α l) Ω
    exact h_dens_deriv_cont
  have hψ_cont : Continuous ψ := hψ_smooth.continuous
  have hψ_support_K : tsupport ψ ⊆ K := le_refl _
  have hψ_partial_cont : ∀ j : Fin (Module.finrank ℝ E),
      Continuous (fun y : EuclN => (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) :=
    fun j => (hψ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψ_partial_support : ∀ j : Fin (Module.finrank ℝ E),
      tsupport (fun y : EuclN => (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) ⊆ K :=
    fun j => tsupport_fderiv_apply_single_subset ψ j
  have hψ_l_partial_cont : ∀ j : Fin (Module.finrank ℝ E),
      Continuous (fun y : EuclN => (fderiv ℝ ψ_l y) (EuclideanSpace.single j 1)) :=
    fun j => (hψ_l_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψ_l_partial_support : ∀ j : Fin (Module.finrank ℝ E),
      tsupport (fun y : EuclN => (fderiv ℝ ψ_l y) (EuclideanSpace.single j 1)) ⊆ K :=
    fun j =>
      (tsupport_fderiv_apply_single_subset ψ_l j).trans
        (tsupport_fderiv_apply_single_subset ψ l)
  have hvolK_finite : (volume : Measure EuclN) K < (⊤ : ℝ≥0∞) :=
    hK_compact.measure_lt_top
  have hvolK_finite' : (volume.restrict K : Measure EuclN) Set.univ < (⊤ : ℝ≥0∞) := by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact hvolK_finite
  have : IsFiniteMeasure ((volume : Measure EuclN).restrict K) := ⟨hvolK_finite'⟩
  have h_M_m_int : IntegrableOn
      (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m
        D.directions) K (volume : Measure EuclN) := by
    have h_parent_m : MemWkp (d := Module.finrank ℝ E) m 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α) :=
      h_chart_H_m_plus_1.le_succ
    exact (chosenMthMixedPartialChartPushedU_locally_memLp
      (I := I) (M := M) g α u_h m h_parent_m D.directions
      hK_compact hK_in).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h_M_m1_int : ∀ idx : Fin (m + 1) → Fin (Module.finrank ℝ E),
      IntegrableOn
        (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h (m + 1) idx)
        K (volume : Measure EuclN) :=
    fun idx =>
      (chosenMthMixedPartialChartPushedU_locally_memLp (I := I) (M := M) g α u_h
        (m + 1) h_chart_H_m_plus_1 idx
        hK_compact hK_in).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h_M_m2_int : ∀ idx : Fin (m + 2) → Fin (Module.finrank ℝ E),
      IntegrableOn
        (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h (m + 2) idx)
        K (volume : Measure EuclN) :=
    fun idx =>
      (chosenMthMixedPartialChartPushedU_locally_memLp (I := I) (M := M) g α u_h
        (m + 2) h_chart_H_m_plus_2 idx
        hK_compact hK_in).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h_fChartEffective_int : IntegrableOn D.diffChartForcing K (volume : Measure EuclN) := by
    have h_global : MemLp D.diffChartForcing 2
        ((volume : Measure EuclN).restrict Ω) := h_forcing_memW1p.1
    have h_eq : ((volume : Measure EuclN).restrict Ω).restrict K =
        (volume : Measure EuclN).restrict K := by
      rw [Measure.restrict_restrict hK_meas]; congr 1
      exact Set.inter_eq_self_of_subset_left hK_in
    have h_K : MemLp D.diffChartForcing 2 ((volume : Measure EuclN).restrict K) := by
      rw [← h_eq]; exact h_global.restrict K
    exact h_K.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h_fChartEffective_wp_int : IntegrableOn
      (chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 l D.diffChartForcing Ω)
      K (volume : Measure EuclN) := by
    have h_global := chosenWeakPartialOrZero_memLp_of_mem h_forcing_memW1p l
    have h_eq : ((volume : Measure EuclN).restrict Ω).restrict K =
        (volume : Measure EuclN).restrict K := by
      rw [Measure.restrict_restrict hK_meas]; congr 1
      exact Set.inter_eq_self_of_subset_left hK_in
    have h_K : MemLp (chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 l
        D.diffChartForcing Ω) 2
        ((volume : Measure EuclN).restrict K) := by
      rw [← h_eq]; exact h_global.restrict K
    exact h_K.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h_int_LHS_m_pair : ∀ i j : Fin (Module.finrank ℝ E),
      Integrable (fun y => weightedInvGramOnEuclid (I := I) g α i j y *
          chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
            (m + 1) (Fin.cons i D.directions) y *
          (fderiv ℝ ψ_l y) (EuclideanSpace.single j 1))
        ((volume : Measure EuclN).restrict Ω) := fun i j =>
    integrable_triple_helper (α := α) hK_compact hK_meas hK_in
      (h_aij_cont i j) (h_M_m1_int (Fin.cons i D.directions))
      (hψ_l_partial_cont j) (hψ_l_partial_support j)
  have h_int_A_pair : ∀ i j,
      Integrable (fun y =>
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
          (EuclideanSpace.single j 1) *
        chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
          (m + 1) (Fin.cons i D.directions) y * ψ y)
        ((volume : Measure EuclN).restrict Ω) := fun i j =>
    integrable_triple_helper (α := α) hK_compact hK_meas hK_in
      (h_aij_fderiv_cont i j)
      (h_M_m1_int (Fin.cons i D.directions)) hψ_cont hψ_support_K
  have h_int_B_pair : ∀ i j,
      Integrable (fun y =>
        weightedInvGramDerivOnEuclid (I := I) g α i j l y *
        chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
          (m + 2) (Fin.cons i (Fin.snoc D.directions j)) y * ψ y)
        ((volume : Measure EuclN).restrict Ω) := fun i j =>
    integrable_triple_helper (α := α) hK_compact hK_meas hK_in
      (h_daij_cont i j)
      (h_M_m2_int (Fin.cons i (Fin.snoc D.directions j))) hψ_cont hψ_support_K
  have h_int_PR_pair : ∀ i j,
      Integrable (fun y =>
        weightedInvGramOnEuclid (I := I) g α i j y *
        chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
          (m + 2) (Fin.cons i (Fin.snoc D.directions l)) y *
        (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ((volume : Measure EuclN).restrict Ω) := fun i j =>
    integrable_triple_helper (α := α) hK_compact hK_meas hK_in
      (h_aij_cont i j)
      (h_M_m2_int (Fin.cons i (Fin.snoc D.directions l)))
      (hψ_partial_cont j) (hψ_partial_support j)
  set INT_LHS_principal_m_l : ℝ :=
    ∫ y in Ω,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
              (m + 1) (Fin.cons i D.directions) y *
            (fderiv ℝ ψ_l y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN) with hINT_LHS_principal_m_l_def
  set INT_LHS_mass_m_l : ℝ :=
    ∫ y in Ω,
      densityOnEuclid (I := I) g α y *
        chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m
          D.directions y * ψ_l y
      ∂(volume : Measure EuclN) with hINT_LHS_mass_m_l_def
  set INT_RHS_m_l : ℝ :=
    ∫ y in Ω,
      densityOnEuclid (I := I) g α y * D.diffChartForcing y * ψ_l y
      ∂(volume : Measure EuclN) with hINT_RHS_m_l_def
  have h_level_m' :
      INT_LHS_principal_m_l + INT_LHS_mass_m_l = INT_RHS_m_l := h_level_m
  have h_swap_LHS_principal :
      INT_LHS_principal_m_l = ∑ i, ∑ j, INT_LHS_m_pair i j := by
    change (∫ y in Ω,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
                (m + 1) (Fin.cons i D.directions) y *
              (fderiv ℝ ψ_l y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN)) = _
    rw [integral_finsetSum _ (fun i _ =>
      (integrable_finsetSum _ (fun j _ => h_int_LHS_m_pair i j)))]
    refine Finset.sum_congr rfl ?_; intro i _
    rw [integral_finsetSum _ (fun j _ => h_int_LHS_m_pair i j)]
  have h_sum_principal :
      ∑ i, ∑ j, INT_LHS_m_pair i j =
      (∑ i, ∑ j, A_pair i j) + (∑ i, ∑ j, B_pair i j) - (∑ i, ∑ j, PR_pair i j) := by
    calc ∑ i, ∑ j, INT_LHS_m_pair i j
        = ∑ i, ∑ j, (A_pair i j + B_pair i j - PR_pair i j) := by
          refine Finset.sum_congr rfl ?_; intro i _
          refine Finset.sum_congr rfl ?_; intro j _
          exact h_principal_pair i j
      _ = ∑ i, ∑ j, (A_pair i j + (B_pair i j + (-(PR_pair i j)))) := by
          refine Finset.sum_congr rfl ?_; intro i _
          refine Finset.sum_congr rfl ?_; intro j _
          ring
      _ = ∑ i, (∑ j, A_pair i j) + ∑ i, (∑ j, (B_pair i j + (-(PR_pair i j)))) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_; intro i _
          exact Finset.sum_add_distrib
      _ = (∑ i, ∑ j, A_pair i j) +
          ((∑ i, ∑ j, B_pair i j) + ∑ i, ∑ j, -(PR_pair i j)) := by
          congr 1
          rw [show (fun i => ∑ j, (B_pair i j + (-(PR_pair i j)))) =
              (fun i => (∑ j, B_pair i j) + (∑ j, -(PR_pair i j))) by
            funext i; exact Finset.sum_add_distrib]
          exact Finset.sum_add_distrib
      _ = (∑ i, ∑ j, A_pair i j) + (∑ i, ∑ j, B_pair i j) -
          (∑ i, ∑ j, PR_pair i j) := by
          simp_rw [Finset.sum_neg_distrib (s :=
            (Finset.univ : Finset (Fin (Module.finrank ℝ E))))]
          ring
  have h_dens_fderiv_eq : ∀ y : EuclN,
      (fderiv ℝ (densityOnEuclid (I := I) g α) y) (EuclideanSpace.single l 1) =
        densityDerivOnEuclid (I := I) g α l y := fun _ => rfl
  set N_C : ℝ :=
    ∫ y in Ω, densityDerivOnEuclid (I := I) g α l y *
      chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m
        D.directions y * ψ y
      ∂(volume : Measure EuclN) with hN_C_def
  set N_mass_new : ℝ :=
    ∫ y in Ω,
      densityOnEuclid (I := I) g α y *
      chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
        (m + 1) (Fin.snoc D.directions l) y * ψ y
      ∂(volume : Measure EuclN) with hN_mass_new_def
  have h_mass_ibp : INT_LHS_mass_m_l = -(N_C + N_mass_new) := by
    have hb := ibp_mass (I := I) (M := M) g α m D.directions
      h_chart_H_m_plus_1 l hψ_smooth hψ_cs hψ_support
    change (∫ y in Ω,
        densityOnEuclid (I := I) g α y *
          chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m
            D.directions y * ψ_l y
        ∂(volume : Measure EuclN)) = _
    rw [hb]
    rfl
  set N_D : ℝ :=
    ∫ y in Ω, densityDerivOnEuclid (I := I) g α l y *
      D.diffChartForcing y * ψ y
      ∂(volume : Measure EuclN) with hN_D_def
  set N_E : ℝ :=
    ∫ y in Ω, densityOnEuclid (I := I) g α y *
      chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 l D.diffChartForcing Ω y * ψ y
      ∂(volume : Measure EuclN) with hN_E_def
  have h_rhs_ibp : INT_RHS_m_l = -(N_D + N_E) := by
    have hb := ibp_density_fChartEffectivePrev (I := I) (M := M) g α
      h_forcing_memW1p l hψ_smooth hψ_cs hψ_support
    change (∫ y in Ω,
        densityOnEuclid (I := I) g α y * D.diffChartForcing y * ψ_l y
        ∂(volume : Measure EuclN)) = _
    rw [hb]
    rfl
  have h_combine : (∑ i, ∑ j, PR_pair i j) + N_mass_new =
      (∑ i, ∑ j, A_pair i j) + (∑ i, ∑ j, B_pair i j) +
        (-N_C) + N_D + N_E := by
    have h := h_level_m'
    rw [h_swap_LHS_principal, h_sum_principal, h_mass_ibp, h_rhs_ibp] at h
    linarith
  set I_step_RHS : ℝ :=
    ∫ y in Ω,
      densityOnEuclid (I := I) g α y *
        successorChartForcing (I := I) (M := M) g α u_h m D.directions
          D.diffChartForcing l y * ψ y
      ∂(volume : Measure EuclN) with hI_step_RHS_def
  set LHS_principal_new : ℝ :=
    ∫ y in Ω,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
              (m + 2) (Fin.cons i (Fin.snoc D.directions l)) y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN) with hLHS_principal_new_def
  have h_LHS_principal_new_eq : LHS_principal_new = ∑ i, ∑ j, PR_pair i j := by
    change (∫ y in Ω,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
                (m + 2) (Fin.cons i (Fin.snoc D.directions l)) y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN)) = _
    rw [integral_finsetSum _ (fun i _ =>
      (integrable_finsetSum _ (fun j _ => h_int_PR_pair i j)))]
    refine Finset.sum_congr rfl ?_; intro i _
    rw [integral_finsetSum _ (fun j _ => h_int_PR_pair i j)]
  have h_M_m_ae :
      chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m D.directions
        =ᵐ[(volume : Measure EuclN).restrict (Ω \ Kα)]
        (fun _ : EuclN => (0 : ℝ)) :=
    chosenMthMixedPartialChartPushedU_ae_zero_off_chartImagePOUTsupport
      (I := I) (M := M) g α u_h m h_chart_H_m_plus_1.le_succ D.directions
  have h_M_m1_ae : ∀ idx : Fin (m + 1) → Fin (Module.finrank ℝ E),
      chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h (m + 1) idx
        =ᵐ[(volume : Measure EuclN).restrict (Ω \ Kα)]
        (fun _ : EuclN => (0 : ℝ)) := fun idx =>
    chosenMthMixedPartialChartPushedU_ae_zero_off_chartImagePOUTsupport
      (I := I) (M := M) g α u_h (m + 1) h_chart_H_m_plus_1 idx
  have h_M_m2_ae : ∀ idx : Fin (m + 2) → Fin (Module.finrank ℝ E),
      chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h (m + 2) idx
        =ᵐ[(volume : Measure EuclN).restrict (Ω \ Kα)]
        (fun _ : EuclN => (0 : ℝ)) := fun idx =>
    chosenMthMixedPartialChartPushedU_ae_zero_off_chartImagePOUTsupport
      (I := I) (M := M) g α u_h (m + 2) h_chart_H_m_plus_2 idx
  have h_fChartEffective_wp_ae :
      chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 l D.diffChartForcing Ω
        =ᵐ[(volume : Measure EuclN).restrict (Ω \ Kα)]
        (fun _ : EuclN => (0 : ℝ)) := by
    exact
      chosenWeakPartialOrZero_ae_zero_on_open_subset_of_ae_zero
        (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        hΩ_open hΩ_diff_Kα_open (fun _ hy => hy.1)
        h_forcing_memW1p h_forcing_ae_zero l
  have h_numer_ae_zero :
      ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ Kα)),
        successorChartForcingNumerator (I := I) (M := M) g α u_h m D.directions
          D.diffChartForcing l y = 0 := by
    have h_M_m1_each : ∀ i : Fin (Module.finrank ℝ E),
        ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ Kα)),
          chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h (m + 1)
            (Fin.cons i D.directions) y = 0 :=
      fun i => h_M_m1_ae (Fin.cons i D.directions)
    have h_M_m2_j_each : ∀ i j : Fin (Module.finrank ℝ E),
        ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ Kα)),
          chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h (m + 2)
            (Fin.cons i (Fin.snoc D.directions j)) y = 0 :=
      fun i j => h_M_m2_ae (Fin.cons i (Fin.snoc D.directions j))
    have h_M_m1_all : ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ Kα)),
        ∀ i : Fin (Module.finrank ℝ E),
          chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h (m + 1)
            (Fin.cons i D.directions) y = 0 := by
      rw [ae_all_iff]; exact h_M_m1_each
    have h_M_m2_j_all : ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ Kα)),
        ∀ i j : Fin (Module.finrank ℝ E),
          chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h (m + 2)
            (Fin.cons i (Fin.snoc D.directions j)) y = 0 := by
      rw [ae_all_iff]; intro i; rw [ae_all_iff]; exact h_M_m2_j_each i
    filter_upwards [h_M_m_ae, h_M_m1_all, h_M_m2_j_all,
      h_forcing_ae_zero, h_fChartEffective_wp_ae] with y h_M_m_y h_M_m1_y
      h_M_m2_j_y h_fE_y h_fE_wp_y
    unfold successorChartForcingNumerator
    have h_A_zero :
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
                (EuclideanSpace.single j 1) *
              chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h (m + 1)
                (Fin.cons i D.directions) y) = 0 := by
      refine Finset.sum_eq_zero ?_; intro i _
      refine Finset.sum_eq_zero ?_; intro _ _
      rw [h_M_m1_y i]; ring
    have h_B_zero :
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramDerivOnEuclid (I := I) g α i j l y *
              chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h (m + 2)
                (Fin.cons i (Fin.snoc D.directions j)) y) = 0 := by
      refine Finset.sum_eq_zero ?_; intro i _
      refine Finset.sum_eq_zero ?_; intro j _
      rw [h_M_m2_j_y i j]; ring
    rw [h_A_zero, h_B_zero, h_M_m_y, h_fE_y, h_fE_wp_y]
    ring
  have h_step_RHS_eq_indicator :
      I_step_RHS =
      ∫ y in Ω,
        Set.indicator Kα
          (fun z => successorChartForcingNumerator (I := I) (M := M) g α u_h m
            D.directions D.diffChartForcing l z) y * ψ y
        ∂(volume : Measure EuclN) := by
    change (∫ y in Ω,
        densityOnEuclid (I := I) g α y *
          successorChartForcing (I := I) (M := M) g α u_h m D.directions
            D.diffChartForcing l y * ψ y
        ∂(volume : Measure EuclN)) = _
    refine setIntegral_congr_fun hΩ_meas (fun y hy => ?_)
    have h_pt := density_mul_successorChartForcing_eq_indicator_numerator
      (I := I) (M := M) g α u_h m D.directions D.diffChartForcing l y hy
    rw [show densityOnEuclid (I := I) g α y *
        successorChartForcing (I := I) (M := M) g α u_h m D.directions
          D.diffChartForcing l y * ψ y =
        (densityOnEuclid (I := I) g α y *
          successorChartForcing (I := I) (M := M) g α u_h m D.directions
            D.diffChartForcing l y) * ψ y from rfl]
    rw [h_pt]
  have h_indicator_eq_numerator :
      ∫ y in Ω,
        Set.indicator Kα
          (fun z => successorChartForcingNumerator (I := I) (M := M) g α u_h m
            D.directions D.diffChartForcing l z) y * ψ y
        ∂(volume : Measure EuclN) =
      ∫ y in Ω,
        successorChartForcingNumerator (I := I) (M := M) g α u_h m D.directions
          D.diffChartForcing l y * ψ y
        ∂(volume : Measure EuclN) := by
    refine MeasureTheory.integral_congr_ae ?_
    refine (ae_restrict_iff' hΩ_meas).mpr ?_
    have h_off : ∀ᵐ y ∂(volume : Measure EuclN),
        y ∈ Ω \ Kα →
        successorChartForcingNumerator (I := I) (M := M) g α u_h m D.directions
          D.diffChartForcing l y = 0 := by
      rw [← ae_restrict_iff' hΩ_diff_Kα_meas]
      exact h_numer_ae_zero
    filter_upwards [h_off] with y hy hy_Ω
    by_cases hy_Kα : y ∈ Kα
    · rw [Set.indicator_of_mem hy_Kα]
    · rw [Set.indicator_of_notMem hy_Kα]
      have hy_diff : y ∈ Ω \ Kα := ⟨hy_Ω, hy_Kα⟩
      rw [hy hy_diff]
  have h_step_RHS_eq_num : I_step_RHS =
      ∫ y in Ω,
        successorChartForcingNumerator (I := I) (M := M) g α u_h m D.directions
          D.diffChartForcing l y * ψ y
        ∂(volume : Measure EuclN) := by
    rw [h_step_RHS_eq_indicator]; exact h_indicator_eq_numerator
  have h_int_C : Integrable (fun y =>
      densityDerivOnEuclid (I := I) g α l y *
        chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m
          D.directions y * ψ y)
      ((volume : Measure EuclN).restrict Ω) :=
    integrable_triple_helper (α := α) hK_compact hK_meas hK_in
      h_dens_deriv_cont h_M_m_int hψ_cont hψ_support_K
  have h_int_D : Integrable (fun y =>
      densityDerivOnEuclid (I := I) g α l y * D.diffChartForcing y * ψ y)
      ((volume : Measure EuclN).restrict Ω) :=
    integrable_triple_helper (α := α) hK_compact hK_meas hK_in
      h_dens_deriv_cont h_fChartEffective_int hψ_cont hψ_support_K
  have h_int_E : Integrable (fun y =>
      densityOnEuclid (I := I) g α y *
      chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 l D.diffChartForcing Ω y * ψ y)
      ((volume : Measure EuclN).restrict Ω) :=
    integrable_triple_helper (α := α) hK_compact hK_meas hK_in
      h_dens_cont h_fChartEffective_wp_int hψ_cont hψ_support_K
  have h_numer_decomp :
      (∫ y in Ω,
        successorChartForcingNumerator (I := I) (M := M) g α u_h m D.directions
          D.diffChartForcing l y * ψ y
        ∂(volume : Measure EuclN)) =
      (∑ i, ∑ j, A_pair i j) + (∑ i, ∑ j, B_pair i j) - N_C + N_D + N_E := by
    set f_A : EuclN → ℝ := fun y => ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
          (EuclideanSpace.single j 1) *
        chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
          (m + 1) (Fin.cons i D.directions) y * ψ y with hf_A_def
    set f_B : EuclN → ℝ := fun y => ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        weightedInvGramDerivOnEuclid (I := I) g α i j l y *
        chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
          (m + 2) (Fin.cons i (Fin.snoc D.directions j)) y * ψ y with hf_B_def
    set f_C : EuclN → ℝ := fun y =>
      - (densityDerivOnEuclid (I := I) g α l y *
        chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m
          D.directions y * ψ y) with hf_C_def
    set f_D : EuclN → ℝ := fun y =>
      densityDerivOnEuclid (I := I) g α l y *
        D.diffChartForcing y * ψ y with hf_D_def
    set f_E : EuclN → ℝ := fun y =>
      densityOnEuclid (I := I) g α y *
        chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 l D.diffChartForcing Ω y *
        ψ y with hf_E_def
    have h_integrand_eq : ∀ y : EuclN,
        successorChartForcingNumerator (I := I) (M := M) g α u_h m D.directions
          D.diffChartForcing l y * ψ y =
        f_A y + f_B y + f_C y + f_D y + f_E y := by
      intro y
      unfold successorChartForcingNumerator
      rw [add_mul, add_mul, sub_mul, add_mul,
        successor_sum_sum_mul, successor_sum_sum_mul]
      ring
    rw [setIntegral_congr_fun hΩ_meas (fun y _ => h_integrand_eq y)]
    have hint_A : Integrable f_A ((volume : Measure EuclN).restrict Ω) :=
      integrable_finsetSum _ (fun i _ =>
        integrable_finsetSum _ (fun j _ => h_int_A_pair i j))
    have hint_B : Integrable f_B ((volume : Measure EuclN).restrict Ω) :=
      integrable_finsetSum _ (fun i _ =>
        integrable_finsetSum _ (fun j _ => h_int_B_pair i j))
    have hint_C : Integrable f_C ((volume : Measure EuclN).restrict Ω) :=
      h_int_C.neg
    have hint_D : Integrable f_D ((volume : Measure EuclN).restrict Ω) :=
      h_int_D
    have hint_E : Integrable f_E ((volume : Measure EuclN).restrict Ω) :=
      h_int_E
    have h_sum_AB : Integrable (fun y => f_A y + f_B y)
        ((volume : Measure EuclN).restrict Ω) := hint_A.add hint_B
    have h_sum_ABC : Integrable (fun y => f_A y + f_B y + f_C y)
        ((volume : Measure EuclN).restrict Ω) := h_sum_AB.add hint_C
    have h_sum_ABCD : Integrable (fun y => f_A y + f_B y + f_C y + f_D y)
        ((volume : Measure EuclN).restrict Ω) := h_sum_ABC.add hint_D
    rw [MeasureTheory.integral_add h_sum_ABCD hint_E]
    rw [MeasureTheory.integral_add h_sum_ABC hint_D]
    rw [MeasureTheory.integral_add h_sum_AB hint_C]
    rw [MeasureTheory.integral_add hint_A hint_B]
    have h_int_f_A : (∫ y in Ω, f_A y ∂(volume : Measure EuclN)) =
        ∑ i, ∑ j, A_pair i j := by
      change (∫ y in Ω,
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
                (EuclideanSpace.single j 1) *
              chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
                (m + 1) (Fin.cons i D.directions) y * ψ y
          ∂(volume : Measure EuclN)) = _
      rw [integral_finsetSum _ (fun i _ =>
        (integrable_finsetSum _ (fun j _ => h_int_A_pair i j)))]
      refine Finset.sum_congr rfl ?_; intro i _
      rw [integral_finsetSum _ (fun j _ => h_int_A_pair i j)]
    have h_int_f_B : (∫ y in Ω, f_B y ∂(volume : Measure EuclN)) =
        ∑ i, ∑ j, B_pair i j := by
      change (∫ y in Ω,
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α i j l y *
              chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
                (m + 2) (Fin.cons i (Fin.snoc D.directions j)) y * ψ y
          ∂(volume : Measure EuclN)) = _
      rw [integral_finsetSum _ (fun i _ =>
        (integrable_finsetSum _ (fun j _ => h_int_B_pair i j)))]
      refine Finset.sum_congr rfl ?_; intro i _
      rw [integral_finsetSum _ (fun j _ => h_int_B_pair i j)]
    have h_int_f_C : (∫ y in Ω, f_C y ∂(volume : Measure EuclN)) = -N_C := by
      change (∫ y in Ω,
          - (densityDerivOnEuclid (I := I) g α l y *
            chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m
              D.directions y * ψ y)
          ∂(volume : Measure EuclN)) = _
      rw [MeasureTheory.integral_neg]
    have h_int_f_D : (∫ y in Ω, f_D y ∂(volume : Measure EuclN)) = N_D := rfl
    have h_int_f_E : (∫ y in Ω, f_E y ∂(volume : Measure EuclN)) = N_E := rfl
    rw [h_int_f_A, h_int_f_B, h_int_f_C, h_int_f_D, h_int_f_E]
    ring
  change LHS_principal_new + N_mass_new = I_step_RHS
  rw [h_LHS_principal_new_eq, h_step_RHS_eq_num, h_numer_decomp]
  linarith

end CalabiYau.PoissonDomainRegularity
