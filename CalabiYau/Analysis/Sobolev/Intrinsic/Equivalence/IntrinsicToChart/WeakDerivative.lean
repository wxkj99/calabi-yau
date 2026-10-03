-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Intrinsic/Equivalence/IntrinsicToChart/WeakDerivative.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Intrinsic.Equivalence.NormEquivalence
public import CalabiYau.Analysis.Sobolev.Manifold.Measure.UniformChartComparison

@[expose] public section


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace Sobolev
namespace EquivalenceReverse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open Sobolev.Chart

local notation "EuclN_E" =>
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

lemma chartSmoothExt_eq_chartPushed_pou_on_target
    [T2Space M] [SigmaCompactSpace M] (α : M) (u : M → ℝ)
    {y : EuclN_E}
    (hy : y ∈ Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α) :
    Sobolev.Chart.chartSmoothExt
        (I := I) (M := M) α
        (fun x : M => ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * u x) y =
      Sobolev.Chart.chartPushed
        (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u y := by
  classical
  have hsymm_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [Sobolev.Chart.chartTargetEuclid_eq_preimage_symm
      (I := I) (M := M)] at hy
    exact hy
  unfold Sobolev.Chart.chartPushed
  change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
        ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          u ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
      else (0 : ℝ)) =
    ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
      u ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
  rw [ite_eq_left hsymm_target]

lemma chartSmoothExt_eq_chartPushed_pou_ae
    [T2Space M] [SigmaCompactSpace M] (α : M) (u : M → ℝ) :
    Sobolev.Chart.chartSmoothExt
        (I := I) (M := M) α
        (fun x : M => ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * u x) =ᵐ[
        (volume : Measure EuclN_E).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)]
      Sobolev.Chart.chartPushed
        (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u := by
  filter_upwards [self_mem_ae_restrict
    (Sobolev.Chart.chartTargetEuclid_measurableSet
      (I := I) (M := M) α)] with y hy
  exact chartSmoothExt_eq_chartPushed_pou_on_target (I := I) (M := M) α u hy

lemma contDiff_chartSmoothExt_pou_mul_local_reverse
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    ContDiff ℝ ∞
      (Sobolev.Chart.chartSmoothExt
        (I := I) (M := M) α
        (fun y : M => ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) y * u y)) := by
  classical
  set ρ : C^∞⟮I, M; ℝ⟯ :=
    CalabiYau.RiemannianVolume.chartAtlasPOU I M α
  set f : M → ℝ := fun y : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) y * u y
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := ρ.contMDiff.mul hu
  have hf_support_chart : tsupport f ⊆ (chartAt H α).source := by
    have h1 : tsupport f ⊆ tsupport
        ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
      have h_eq : f = (fun y : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) y • u y) := by
        funext y; rfl
      rw [h_eq]
      exact tsupport_smul_subset_left
        (f := fun y : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) y) (g := u)
    exact h1.trans
      (CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M α)
  have hf_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
  rw [contDiff_iff_contDiffAt]
  intro y
  set form : EuclN_E → ℝ := fun z =>
    f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
  have h_target_open :=
    Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) (α := α)
  have h_form_contDiffOn : ContDiffOn ℝ ∞ form
      (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
    have hscalar : ContDiffOn ℝ ∞
        (CalabiYau.DivergenceTheorem.scalarOnE
          (I := I) α f) (extChartAt I α).target :=
      CalabiYau.DivergenceTheorem.scalarOnE_contDiffOn
        (I := I) α hf_smooth
    have htoEuc_symm_smooth : ContDiff ℝ ∞ ((toEuclidean (E := E)).symm) :=
      ContinuousLinearEquiv.contDiff _
    have hmaps : Set.MapsTo ((toEuclidean (E := E)).symm)
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)
        (extChartAt I α).target := by
      intro y' hy'
      obtain ⟨z, hz_target, rfl⟩ := hy'
      have h_eq : (toEuclidean (E := E)).symm
          ((toEuclidean (E := E) : E ≃L[ℝ] EuclN_E) z) = z :=
        (toEuclidean (E := E)).symm_apply_apply z
      rw [h_eq]
      exact hz_target
    have h_eq_form : form = (CalabiYau.DivergenceTheorem.scalarOnE
        (I := I) α f) ∘ (fun z : EuclN_E => (toEuclidean (E := E)).symm z) := by
      funext z; rfl
    rw [h_eq_form]
    exact hscalar.comp htoEuc_symm_smooth.contDiffOn hmaps
  by_cases hy_target : y ∈
      Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α
  · have h_at : ContDiffAt ℝ ∞ form y :=
      (h_form_contDiffOn.contDiffWithinAt hy_target).contDiffAt
        (h_target_open.mem_nhds hy_target)
    apply h_at.congr_of_eventuallyEq
    filter_upwards [h_target_open.mem_nhds hy_target] with z hz
    obtain ⟨w, hw_target, hw_eq⟩ := hz
    have hsymm_eq : (toEuclidean (E := E)).symm z = w := by
      rw [← hw_eq]
      exact (toEuclidean (E := E)).symm_apply_apply w
    have htarget_at_z : (toEuclidean (E := E)).symm z ∈ (extChartAt I α).target := by
      rw [hsymm_eq]; exact hw_target
    change Sobolev.Chart.chartSmoothExt
        (I := I) (M := M) α f z =
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
    change (if (toEuclidean (E := E)).symm z ∈ (extChartAt I α).target then
        f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
      else (0 : ℝ)) =
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
    rw [ite_eq_left htarget_at_z]
  · set K : Set EuclN_E := (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f))
    have hK_compact : IsCompact K := by
      have h_extChart_cont : ContinuousOn (extChartAt I α) (tsupport f) :=
        (continuousOn_extChartAt α).mono (by
          intro x hx
          rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
            (I := I) (M := M)]
          exact hf_support_chart hx)
      have h1 : IsCompact ((extChartAt I α) '' (tsupport f)) :=
        hf_compact.image_of_continuousOn h_extChart_cont
      exact h1.image (toEuclidean (E := E)).continuous
    have hK_subset : K ⊆
        Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α := by
      rintro y' ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      have hxsource : x ∈ (extChartAt I α).source := by
        rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
          (I := I) (M := M)]
        exact hf_support_chart hx
      exact ⟨extChartAt I α x, (extChartAt I α).map_source hxsource, rfl⟩
    have hy_off_K : y ∉ K := fun hy_in => hy_target (hK_subset hy_in)
    have hK_compl_open : IsOpen Kᶜ := hK_compact.isClosed.isOpen_compl
    apply ContDiffAt.congr_of_eventuallyEq (f := fun _ : EuclN_E => (0 : ℝ)) contDiffAt_const
    filter_upwards [hK_compl_open.mem_nhds hy_off_K] with z hz
    classical
    by_cases hz_target : (toEuclidean (E := E)).symm z ∈ (extChartAt I α).target
    · have hsymm_source : (extChartAt I α).symm
          ((toEuclidean (E := E)).symm z) ∈ (extChartAt I α).source :=
        (extChartAt I α).map_target hz_target
      have hxsupp : (extChartAt I α).symm ((toEuclidean (E := E)).symm z) ∉ tsupport f := by
        intro hin
        apply hz
        refine ⟨(toEuclidean (E := E)).symm z, ?_, ?_⟩
        · refine ⟨(extChartAt I α).symm ((toEuclidean (E := E)).symm z), hin, ?_⟩
          exact (extChartAt I α).right_inv hz_target
        · exact (toEuclidean (E := E)).apply_symm_apply z
      have hf_zero : f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) = 0 :=
        image_eq_zero_of_notMem_tsupport hxsupp
      change (if (toEuclidean (E := E)).symm z ∈ (extChartAt I α).target then
                f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
              else (0 : ℝ)) = 0
      rw [ite_eq_left hz_target, hf_zero]
    · change (if (toEuclidean (E := E)).symm z ∈ (extChartAt I α).target then
                f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
              else (0 : ℝ)) = 0
      rw [ite_eq_right hz_target]

lemma chosenWeakPartial_chartPushed_ae_eq_fderiv
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (α : M) {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (i : Fin (Module.finrank ℝ E)) :
    Sobolev.Euclidean.chosenWeakPartialOrZero
        (d := Module.finrank ℝ E) p i
        (Sobolev.Chart.chartPushed
          (I := I) (M := M) (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
        (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)
      =ᵐ[(volume : Measure EuclN_E).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)]
      (fun y : EuclN_E => fderiv ℝ
        (Sobolev.Chart.chartSmoothExt
          (I := I) (M := M) α
          (fun z : M => ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z)) y
          (EuclideanSpace.single i (1 : ℝ))) := by
  classical
  set ρ : C^∞⟮I, M; ℝ⟯ :=
    CalabiYau.RiemannianVolume.chartAtlasPOU I M α
  set ψ : EuclN_E → ℝ := Sobolev.Chart.chartSmoothExt
    (I := I) (M := M) α
    (fun z : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z)
  set f : M → ℝ := fun z : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := ρ.contMDiff.mul hu
  have hf_support_chart : tsupport f ⊆ (chartAt H α).source := by
    have h1 : tsupport f ⊆ tsupport ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
      have h_eq : f = (fun z : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) z • u z) := by
        funext z; rfl
      rw [h_eq]
      exact tsupport_smul_subset_left
        (f := fun z : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) z) (g := u)
    exact h1.trans
      (CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M α)
  have hf_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
  have hψ_smooth : ContDiff ℝ ∞ ψ :=
    contDiff_chartSmoothExt_pou_mul_local_reverse (I := I) (M := M) α hu
  have hψ_support : tsupport ψ ⊆
      Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α := by
    set K_eucl : Set EuclN_E := (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f))
    have hK_compact : IsCompact K_eucl := by
      have h_extChart_cont : ContinuousOn (extChartAt I α) (tsupport f) :=
        (continuousOn_extChartAt α).mono (by
          intro x hx
          rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
            (I := I) (M := M)]
          exact hf_support_chart hx)
      have h1 : IsCompact ((extChartAt I α) '' (tsupport f)) :=
        hf_compact.image_of_continuousOn h_extChart_cont
      exact h1.image (toEuclidean (E := E)).continuous
    have hK_subset : K_eucl ⊆
        Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α := by
      rintro y' ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      have hxsource : x ∈ (extChartAt I α).source := by
        rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
          (I := I) (M := M)]
        exact hf_support_chart hx
      exact ⟨extChartAt I α x, (extChartAt I α).map_source hxsource, rfl⟩
    have h_sub_image : tsupport ψ ⊆ K_eucl := by
      apply closure_minimal _ hK_compact.isClosed
      intro y hy
      by_contra hy_off
      apply hy
      classical
      by_cases hz_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target
      · have hxsupp : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∉ tsupport f := by
          intro hin
          apply hy_off
          refine ⟨(toEuclidean (E := E)).symm y, ?_, ?_⟩
          · refine ⟨(extChartAt I α).symm ((toEuclidean (E := E)).symm y), hin, ?_⟩
            exact (extChartAt I α).right_inv hz_target
          · exact (toEuclidean (E := E)).apply_symm_apply y
        have hf_zero : f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) = 0 :=
          image_eq_zero_of_notMem_tsupport hxsupp
        change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
                  f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
                else (0 : ℝ)) = 0
        rw [ite_eq_left hz_target, hf_zero]
      · change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
                  f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
                else (0 : ℝ)) = 0
        rw [ite_eq_right hz_target]
    exact h_sub_image.trans hK_subset
  have hψ_compact_support : HasCompactSupport ψ := by
    set K_eucl : Set EuclN_E := (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f))
    have hK_compact : IsCompact K_eucl := by
      have h_extChart_cont : ContinuousOn (extChartAt I α) (tsupport f) :=
        (continuousOn_extChartAt α).mono (by
          intro x hx
          rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
            (I := I) (M := M)]
          exact hf_support_chart hx)
      have h1 : IsCompact ((extChartAt I α) '' (tsupport f)) :=
        hf_compact.image_of_continuousOn h_extChart_cont
      exact h1.image (toEuclidean (E := E)).continuous
    have h_sub_image : tsupport ψ ⊆ K_eucl := by
      apply closure_minimal _ hK_compact.isClosed
      intro y hy
      by_contra hy_off
      apply hy
      classical
      by_cases hz_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target
      · have hxsupp : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∉ tsupport f := by
          intro hin
          apply hy_off
          refine ⟨(toEuclidean (E := E)).symm y, ?_, ?_⟩
          · refine ⟨(extChartAt I α).symm ((toEuclidean (E := E)).symm y), hin, ?_⟩
            exact (extChartAt I α).right_inv hz_target
          · exact (toEuclidean (E := E)).apply_symm_apply y
        have hf_zero : f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) = 0 :=
          image_eq_zero_of_notMem_tsupport hxsupp
        change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
                  f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
                else (0 : ℝ)) = 0
        rw [ite_eq_left hz_target, hf_zero]
      · change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
                  f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
                else (0 : ℝ)) = 0
        rw [ite_eq_right hz_target]
    exact hK_compact.of_isClosed_subset (isClosed_tsupport _) h_sub_image
  have hψ_mem_W1p : Sobolev.Euclidean.MemW1p (d := Module.finrank ℝ E) p ψ
      (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
    have h := Sobolev.Euclidean.MemWkp_of_smooth_compactSupport
      (d := Module.finrank ℝ E)
      (Sobolev.Chart.chartTargetEuclid_isOpen
        (I := I) (M := M) α)
      hψ_smooth hψ_compact_support hψ_support hp_one 1
    exact (Sobolev.Euclidean.MemWkp.one_iff_memW1p).mp h
  have h_ae_chartPushed : Sobolev.Chart.chartPushed
      (I := I) (M := M) (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u
      =ᵐ[(volume : Measure EuclN_E).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)]
      ψ := (chartSmoothExt_eq_chartPushed_pou_ae (I := I) (M := M) α u).symm
  have h_classical_isWeak :
      Sobolev.Euclidean.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
        (fun y : EuclN_E => fderiv ℝ ψ y (EuclideanSpace.single i 1)) ψ
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) :=
    Sobolev.Euclidean.HasWeakPartialDeriv.of_contDiff
      (Ω := Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α)
      (i := i) (f := ψ)
      (hψ_smooth.of_le (by norm_cast))
  have h_chosen_isWeak :
      Sobolev.Euclidean.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
        (Sobolev.Euclidean.chosenWeakPartialOrZero
          (d := Module.finrank ℝ E) p i ψ
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)) ψ
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) :=
    Sobolev.Euclidean.chosenWeakPartialOrZero_isWeakPartial_of_mem
      hψ_mem_W1p i
  have h_classical_local : LocallyIntegrable
      (fun y : EuclN_E => fderiv ℝ ψ y (EuclideanSpace.single i (1 : ℝ)))
      ((volume : Measure EuclN_E).restrict
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)) := by
    have h_cont : Continuous
        (fun y : EuclN_E => fderiv ℝ ψ y (EuclideanSpace.single i (1 : ℝ))) :=
      (hψ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
    exact h_cont.locallyIntegrable.mono_measure Measure.restrict_le_self
  have h_chosen_local : LocallyIntegrable
      (Sobolev.Euclidean.chosenWeakPartialOrZero
        (d := Module.finrank ℝ E) p i ψ
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α))
      ((volume : Measure EuclN_E).restrict
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)) :=
    (Sobolev.Euclidean.chosenWeakPartialOrZero_memLp_of_mem
      hψ_mem_W1p i).locallyIntegrable hp_one
  have h_chosen_psi_ae :
      (Sobolev.Euclidean.chosenWeakPartialOrZero
        (d := Module.finrank ℝ E) p i ψ
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α))
        =ᵐ[(volume : Measure EuclN_E).restrict
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)]
        (fun y : EuclN_E => fderiv ℝ ψ y (EuclideanSpace.single i (1 : ℝ))) :=
    Sobolev.Euclidean.HasWeakPartialDeriv.ae_eq
      (Ω := Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α)
      (Sobolev.Chart.chartTargetEuclid_isOpen
        (I := I) (M := M) α)
      h_chosen_isWeak h_classical_isWeak
      h_chosen_local h_classical_local
  have h_chartPushed_mem_W1p : Sobolev.Euclidean.MemW1p (d := Module.finrank ℝ E) p
      (Sobolev.Chart.chartPushed
        (I := I) (M := M) (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
      (Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
    have h := Sobolev.Euclidean.MemWkp.one_iff_memW1p
      (d := Module.finrank ℝ E) (p := p)
      (u := Sobolev.Chart.chartPushed
        (I := I) (M := M) (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
      (Ω := Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α)
    refine h.mp ?_
    have h_psi_mem : Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 1 p ψ
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) :=
      (Sobolev.Euclidean.MemWkp.one_iff_memW1p).mpr hψ_mem_W1p
    exact (Sobolev.Euclidean.MemWkp_congr_ae
      (d := Module.finrank ℝ E) hp_one
      (Sobolev.Chart.chartTargetEuclid_isOpen
        (I := I) (M := M) α) h_ae_chartPushed).mpr h_psi_mem
  have h_chosen_chartPushed_isWeak :
      Sobolev.Euclidean.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
        (Sobolev.Euclidean.chosenWeakPartialOrZero
          (d := Module.finrank ℝ E) p i
          (Sobolev.Chart.chartPushed
            (I := I) (M := M) (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α))
        (Sobolev.Chart.chartPushed
          (I := I) (M := M) (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) :=
    Sobolev.Euclidean.chosenWeakPartialOrZero_isWeakPartial_of_mem
      h_chartPushed_mem_W1p i
  have h_chosen_chartPushed_isWeak_psi :
      Sobolev.Euclidean.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
        (Sobolev.Euclidean.chosenWeakPartialOrZero
          (d := Module.finrank ℝ E) p i
          (Sobolev.Chart.chartPushed
            (I := I) (M := M) (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
          (Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α))
        ψ
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) := by
    intro φ hφ_smooth hφ_compact hφ_support
    have h_lhs := h_chosen_chartPushed_isWeak φ hφ_smooth hφ_compact hφ_support
    rw [show (∫ x in Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α,
            ψ x * (fderiv ℝ φ x) (EuclideanSpace.single i 1)) =
          ∫ x in Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α,
            Sobolev.Chart.chartPushed
              (I := I) (M := M)
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u x *
              (fderiv ℝ φ x) (EuclideanSpace.single i 1) from ?_]
    · exact h_lhs
    · refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [h_ae_chartPushed] with x hx
      rw [hx]
  have h_chosen_chartPushed_local : LocallyIntegrable
      (Sobolev.Euclidean.chosenWeakPartialOrZero
        (d := Module.finrank ℝ E) p i
        (Sobolev.Chart.chartPushed
          (I := I) (M := M) (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α))
      ((volume : Measure EuclN_E).restrict
        (Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)) :=
    (Sobolev.Euclidean.chosenWeakPartialOrZero_memLp_of_mem
      h_chartPushed_mem_W1p i).locallyIntegrable hp_one
  exact Sobolev.Euclidean.HasWeakPartialDeriv.ae_eq
    (Ω := Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α)
    (Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α)
    h_chosen_chartPushed_isWeak_psi h_classical_isWeak
    h_chosen_chartPushed_local h_classical_local

end EquivalenceReverse
end Sobolev
