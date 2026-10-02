module

public import Comparator.PoissonSolvability.DomainSobolevGain.SuccessorSource
public import Comparator.PoissonSolvability.DomainSobolevGain.MixedPartialRegularity
public import CalabiYau.Analysis.Elliptic.Regularity.DiffChart.Differentiated.CrossTermIBP

/-!
# Integration by parts for selected mixed chart partials and smooth tests

Proof-preserving extraction from the checked successor weak-equation assembly.
Source: DifferentialGeometry `7a48598d35109aa99d1cc678e2724c213cdf4ff3`,
`Iterated/VariationalIdentity/InductiveSuccessor.lean:44-249; SuccessorSource.lean:65-249`.
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

omit [NeZero (Module.finrank ℝ E)] in
theorem per_pair_ibp_chosenMthMixed
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g} (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (h_chart_regularity : MemWkp (d := Module.finrank ℝ E) (m + 1) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α))
    {φ : EuclN → ℝ}
    (hφ_chart : ContDiffOn ℝ (⊤ : ℕ∞) φ
      (chartTargetEuclid (I := I) (M := M) α))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (l : Fin (Module.finrank ℝ E)) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      φ y * chosenMthMixedPartialChartPushedU g α u_h m dirs y *
        (fderiv ℝ ψ y) (EuclideanSpace.single l 1) ∂(volume : Measure EuclN)) =
    -((∫ y in chartTargetEuclid (I := I) (M := M) α,
        (fderiv ℝ φ y) (EuclideanSpace.single l 1) *
          chosenMthMixedPartialChartPushedU g α u_h m dirs y * ψ y
        ∂(volume : Measure EuclN)) +
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        φ y * chosenMthMixedPartialChartPushedU g α u_h (m + 1)
          (Fin.snoc dirs l) y * ψ y ∂(volume : Measure EuclN))) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set v : EuclN → ℝ := chosenMthMixedPartialChartPushedU g α u_h m dirs with hv_def
  set w : Fin (Module.finrank ℝ E) → EuclN → ℝ := fun j =>
    chosenMthMixedPartialChartPushedU g α u_h (m + 1) (Fin.snoc dirs j) with hw_def
  have h_v_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 v Ω :=
    chosenMthMixedPartialChartPushedU_memW1p_two g α u_h m h_chart_regularity dirs
  have h_w_eq : ∀ j : Fin (Module.finrank ℝ E),
      w j = chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 j v Ω := by
    intro j
    simp only [hw_def, chosenMthMixedPartialChartPushedU,
      Fin.snoc_last, Fin.init_snoc]
    rfl
  have hw_isWeakPartial : ∀ j : Fin (Module.finrank ℝ E),
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) j (w j) v Ω := by
    intro j
    rw [h_w_eq j]
    exact chosenWeakPartialOrZero_isWeakPartial_of_mem h_v_memW1p j
  have hv_global_memLp : MemLp v 2 ((volume : Measure EuclN).restrict Ω) :=
    h_v_memW1p.1
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
    exact hv_global_memLp.restrict K'
  have hw_global_memLp : ∀ j : Fin (Module.finrank ℝ E),
      MemLp (w j) 2 ((volume : Measure EuclN).restrict Ω) := by
    intro j
    rw [h_w_eq j]
    exact chosenWeakPartialOrZero_memLp_of_mem h_v_memW1p j
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
    exact (hw_global_memLp j).restrict K'
  set K : Set EuclN := tsupport ψ with hK_def
  have hK_compact : IsCompact K := hψ_cs
  have hK_in : K ⊆ Ω := hψ_support
  obtain ⟨δ, φExt, hδ_pos, hδ_subset, hφExt_smooth, hφExt_eq⟩ :=
    exists_smooth_global_extension
      (I := I) (M := M) (φ := φ) α hφ_chart hK_compact hK_in
  have h_ibp_ext :=
    CalabiYau.Analysis.Sobolev.Euclidean.integral_smul_weak_partial_eq
      (d := Module.finrank ℝ E) (Ω := Ω) hΩ_open
      (φ := φExt) hφExt_smooth (v := v) (w := w)
      hv_localMemLp hw_localMemLp hw_isWeakPartial l
      (ψ := ψ) hψ_smooth hψ_cs hψ_support
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have hK_in_thickening : K ⊆ Metric.cthickening δ K := Metric.self_subset_cthickening _
  have h_fderiv_zero_outside_K : ∀ x ∉ K, fderiv ℝ ψ x = 0 := by
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
    rw [hψ_const_zero]
    simp
  have hLHS_eq :
      ∫ y in Ω, φExt y * v y * (fderiv ℝ ψ y) (EuclideanSpace.single l 1)
        ∂(volume : Measure EuclN) =
      ∫ y in Ω, φ y * v y * (fderiv ℝ ψ y) (EuclideanSpace.single l 1)
        ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y hy => ?_)
    by_cases hy_K : y ∈ K
    · rw [hφExt_eq y (hK_in_thickening hy_K)]
    · rw [h_fderiv_zero_outside_K y hy_K]
      simp
  have h_fderiv_φExt_eq_φ_on_K : ∀ y ∈ K, ∀ j' : Fin (Module.finrank ℝ E),
      (fderiv ℝ φExt y) (EuclideanSpace.single j' 1) =
      (fderiv ℝ φ y) (EuclideanSpace.single j' 1) := by
    intro y hy_K j'
    have hy_thick_open : y ∈ Metric.thickening δ K := by
      rw [Metric.mem_thickening_iff]
      refine ⟨y, hy_K, ?_⟩
      simp [hδ_pos]
    have h_thick_open : IsOpen (Metric.thickening δ K) := Metric.isOpen_thickening
    have h_neighborhood : Metric.thickening δ K ∈ 𝓝 y :=
      h_thick_open.mem_nhds hy_thick_open
    have h_thick_sub : Metric.thickening δ K ⊆ Metric.cthickening δ K :=
      Metric.thickening_subset_cthickening _ _
    have h_eq_neighborhood : φExt =ᶠ[𝓝 y] φ := by
      filter_upwards [h_neighborhood] with z hz
      exact hφExt_eq z (h_thick_sub hz)
    rw [Filter.EventuallyEq.fderiv_eq h_eq_neighborhood]
  have hLeibniz1_eq :
      ∫ y in Ω, (fderiv ℝ φExt y) (EuclideanSpace.single l 1) * v y * ψ y
        ∂(volume : Measure EuclN) =
      ∫ y in Ω, (fderiv ℝ φ y) (EuclideanSpace.single l 1) * v y * ψ y
        ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y hy => ?_)
    by_cases hy_K : y ∈ K
    · rw [h_fderiv_φExt_eq_φ_on_K y hy_K l]
    · have hψy : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy_K
      rw [hψy]
      ring
  have hLeibniz2_eq :
      ∫ y in Ω, φExt y * w l y * ψ y ∂(volume : Measure EuclN) =
      ∫ y in Ω, φ y * w l y * ψ y ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y hy => ?_)
    by_cases hy_K : y ∈ K
    · rw [hφExt_eq y (hK_in_thickening hy_K)]
    · have hψy : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy_K
      rw [hψy]
      ring
  rw [← hLHS_eq, ← hLeibniz1_eq, ← hLeibniz2_eq]
  exact h_ibp_ext

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma contDiff_fderiv_apply_single
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (l : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclN =>
      (fderiv ℝ ψ y) (EuclideanSpace.single l 1)) := by
  have h_fderiv : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclN => fderiv ℝ ψ y) :=
    (contDiff_infty_iff_fderiv.1 hψ).2
  have h_eval : ContDiff ℝ (⊤ : ℕ∞)
      (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single l 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single l (1 : ℝ))).contDiff
  exact h_eval.comp h_fderiv

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma hasCompactSupport_fderiv_apply_single
    {ψ : EuclN → ℝ} (hψ_cs : HasCompactSupport ψ)
    (l : Fin (Module.finrank ℝ E)) :
    HasCompactSupport (fun y : EuclN =>
      (fderiv ℝ ψ y) (EuclideanSpace.single l 1)) :=
  hψ_cs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single l 1)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma tsupport_fderiv_apply_single_subset
    (ψ : EuclN → ℝ) (l : Fin (Module.finrank ℝ E)) :
    tsupport (fun y : EuclN => (fderiv ℝ ψ y) (EuclideanSpace.single l 1)) ⊆
      tsupport ψ :=
  tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single l 1)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma fderiv_apply_single_swap
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (y : EuclN)
    (j l : Fin (Module.finrank ℝ E)) :
    (fderiv ℝ
      (fun z : EuclN => (fderiv ℝ ψ z) (EuclideanSpace.single l 1)) y)
        (EuclideanSpace.single j 1) =
    (fderiv ℝ
      (fun z : EuclN => (fderiv ℝ ψ z) (EuclideanSpace.single j 1)) y)
        (EuclideanSpace.single l 1) := by
  classical
  have h_diff_fderiv : Differentiable ℝ (fderiv ℝ ψ) :=
    ((contDiff_infty_iff_fderiv.1 hψ).2).differentiable (by simp)
  have h_flip_eq : ∀ k : Fin (Module.finrank ℝ E),
      fderiv ℝ
        (fun z : EuclN => (fderiv ℝ ψ z) (EuclideanSpace.single k 1)) y =
        (fderiv ℝ (fderiv ℝ ψ) y).flip (EuclideanSpace.single k 1) := by
    intro k
    have h_const_diff :
        DifferentiableAt ℝ
          (fun _ : EuclN => (EuclideanSpace.single k (1 : ℝ))) y :=
      differentiableAt_const _
    have h_step :=
      fderiv_clm_apply (𝕜 := ℝ)
        (c := fderiv ℝ ψ) (u := fun _ : EuclN => EuclideanSpace.single k (1 : ℝ))
        (x := y) (h_diff_fderiv y) h_const_diff
    have h_const_fderiv :
        fderiv ℝ (fun _ : EuclN => EuclideanSpace.single k (1 : ℝ)) y = 0 :=
      fderiv_const_apply (EuclideanSpace.single k (1 : ℝ))
    rw [h_step, h_const_fderiv]; simp
  rw [h_flip_eq l, h_flip_eq j]
  have h_symm : IsSymmSndFDerivAt ℝ ψ y := by
    have h_ge : minSmoothness ℝ 2 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
      rw [minSmoothness_of_isRCLikeNormedField]; decide
    exact hψ.contDiffAt.isSymmSndFDerivAt (𝕜 := ℝ) h_ge
  change ((fderiv ℝ (fderiv ℝ ψ) y).flip (EuclideanSpace.single l 1))
        (EuclideanSpace.single j 1) =
      ((fderiv ℝ (fderiv ℝ ψ) y).flip (EuclideanSpace.single j 1))
        (EuclideanSpace.single l 1)
  rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_apply]
  exact h_symm (EuclideanSpace.single j 1) (EuclideanSpace.single l 1)

end CalabiYau.PoissonDomainRegularity.SuccessorEquation
