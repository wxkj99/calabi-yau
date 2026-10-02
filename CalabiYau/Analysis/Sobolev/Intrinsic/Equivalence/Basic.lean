-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Intrinsic/Equivalence/Basic.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Chart.Defs
public import CalabiYau.Analysis.Sobolev.Intrinsic.Defs
public import CalabiYau.Geometry.Riemannian.Volume.Chart.MeasureComparison
public import CalabiYau.Geometry.Riemannian.Operator.DirectionalDerivative
public import CalabiYau.Geometry.Riemannian.Volume.Properties
public import CalabiYau.Geometry.Riemannian.Volume.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace Sobolev
namespace Equivalence

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

private abbrev EuclN (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private def chartPushedExt (α : M) (f : M → ℝ) : EuclN E → ℝ := by
  classical
  exact fun y =>
    if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    else 0

omit [IsManifold I ∞ M] in
private lemma chartPushedExt_apply_of_mem_target
    (α : M) (f : M → ℝ) {y : EuclN E}
    (hy : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target) :
    chartPushedExt (I := I) (M := M) α f y =
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  classical
  change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    else 0) = f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
  rw [if_pos hy]

omit [IsManifold I ∞ M] in
private lemma chartPushedExt_apply_of_notMem_target
    (α : M) (f : M → ℝ) {y : EuclN E}
    (hy : (toEuclidean (E := E)).symm y ∉ (extChartAt I α).target) :
    chartPushedExt (I := I) (M := M) α f y = 0 := by
  classical
  change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    else 0) = 0
  rw [if_neg hy]

omit [IsManifold I ∞ M] in
private lemma chartPushedExt_apply_of_mem_chartTargetEuclid
    (α : M) (f : M → ℝ) {y : EuclN E}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushedExt (I := I) (M := M) α f y =
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  classical
  apply chartPushedExt_apply_of_mem_target
  rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
  exact hy

omit [IsManifold I ∞ M] in
private lemma chartPushedExt_apply_of_notMem_chartTargetEuclid
    (α : M) (f : M → ℝ) {y : EuclN E}
    (hy : y ∉ chartTargetEuclid (I := I) (M := M) α) :
    chartPushedExt (I := I) (M := M) α f y = 0 := by
  classical
  apply chartPushedExt_apply_of_notMem_target
  rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
  exact hy

omit [IsManifold I ∞ M] in
private lemma chartPushedExt_eq_chartPushed_on_target
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (α : M) (u : M → ℝ) {y : EuclN E}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushedExt (I := I) (M := M) α
        (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) y =
      chartPushed (I := I) (M := M) ρ α u y := by
  classical
  rw [chartPushedExt_apply_of_mem_chartTargetEuclid (I := I) (M := M) α _ hy]
  unfold chartPushed
  rfl

omit [IsManifold I ∞ M] in
private lemma image_toEuclidean_chart_tsupport_isCompact
    [CompactSpace M] {f : M → ℝ} {α : M}
    (hf_support : tsupport f ⊆ (chartAt H α).source) :
    IsCompact ((toEuclidean (E := E)) ''
      ((extChartAt I α) '' (tsupport f))) := by
  have hKE := image_extChartAt_tsupport_compact_subset_target
    (I := I) (M := M) (u := f) (α := α) hf_support
  exact hKE.1.image (toEuclidean (E := E)).continuous

omit [IsManifold I ∞ M] in
private lemma image_toEuclidean_chart_tsupport_subset_chartTargetEuclid
    {f : M → ℝ} {α : M}
    (hf_support : tsupport f ⊆ (chartAt H α).source) :
    (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport f)) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
  image_toEuclidean_extChartAt_tsupport_subset_chartTargetEuclid
    (I := I) (M := M) (u := f) (α := α) hf_support

omit [IsManifold I ∞ M] in
private lemma chartPushedExt_eq_zero_off_image_tsupport
    (α : M) {f : M → ℝ}
    (_hf_support : tsupport f ⊆ (chartAt H α).source) {y : EuclN E}
    (hy_off : y ∉ (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport f))) :
    chartPushedExt (I := I) (M := M) α f y = 0 := by
  classical
  by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
  · obtain ⟨z, hz_target, hzy⟩ := hy_target
    have hy_target' : y ∈ chartTargetEuclid (I := I) (M := M) α := ⟨z, hz_target, hzy⟩
    have hsymm_source : (extChartAt I α).symm z ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hz_target
    have hy_symm : (toEuclidean (E := E)).symm y = z := by
      rw [← hzy]; exact (toEuclidean (E := E)).symm_apply_apply z
    rw [chartPushedExt_apply_of_mem_chartTargetEuclid (I := I) (M := M) α f hy_target',
      hy_symm]
    by_contra hne
    apply hy_off
    have hsymm_in_support : (extChartAt I α).symm z ∈ tsupport f :=
      subset_tsupport _ (Function.mem_support.mpr hne)
    have hz_eq : (extChartAt I α) ((extChartAt I α).symm z) = z :=
      (extChartAt I α).right_inv hz_target
    refine ⟨z, ⟨(extChartAt I α).symm z, hsymm_in_support, hz_eq⟩, hzy⟩
  · exact chartPushedExt_apply_of_notMem_chartTargetEuclid (I := I) (M := M) α f hy_target

omit [IsManifold I ∞ M] in
private lemma hasCompactSupport_chartPushedExt
    [CompactSpace M] (α : M) {f : M → ℝ}
    (hf_support : tsupport f ⊆ (chartAt H α).source) :
    HasCompactSupport (chartPushedExt (I := I) (M := M) α f) := by
  classical
  set K : Set (EuclN E) :=
    (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f)) with hK_def
  have hK_compact : IsCompact K :=
    image_toEuclidean_chart_tsupport_isCompact
      (I := I) (M := M) (f := f) (α := α) hf_support
  apply HasCompactSupport.of_support_subset_isCompact hK_compact
  intro y hy_support
  by_contra hyK
  apply hy_support
  exact chartPushedExt_eq_zero_off_image_tsupport
    (I := I) (M := M) α (f := f) hf_support hyK

private lemma contDiffOn_chartPushedExt_formula
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContDiffOn ℝ ∞
        (fun y : EuclN E =>
          f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hscalar : ContDiffOn ℝ ∞
      (fun y : E => f ((extChartAt I α).symm y))
      (extChartAt I α).target := by
    have h := scalarOnE_contDiffOn (I := I) α hf
    exact h
  have htoEuc_symm_smooth : ContDiff ℝ ∞ ((toEuclidean (E := E)).symm) :=
    ContinuousLinearEquiv.contDiff _
  have hmaps : Set.MapsTo ((toEuclidean (E := E)).symm)
      (chartTargetEuclid (I := I) (M := M) α) (extChartAt I α).target := by
    intro y hy
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have hcomp := hscalar.comp htoEuc_symm_smooth.contDiffOn hmaps
  exact hcomp

private lemma contDiffAt_chartPushedExt_of_mem_target
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    [I.Boundaryless] {y : EuclN E}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    ContDiffAt ℝ ∞ (chartPushedExt (I := I) (M := M) α f) y := by
  classical
  have hOpen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hContDiffOn := contDiffOn_chartPushedExt_formula (I := I) (M := M) α hf
  have hContDiffAt_formula : ContDiffAt ℝ ∞
      (fun y : EuclN E => f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) y := by
    have hwithin : ContDiffWithinAt ℝ ∞
        (fun y : EuclN E => f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (chartTargetEuclid (I := I) (M := M) α) y := hContDiffOn y hy
    exact hwithin.contDiffAt (hOpen.mem_nhds hy)
  apply hContDiffAt_formula.congr_of_eventuallyEq
  filter_upwards [hOpen.mem_nhds hy] with z hz
  rw [chartPushedExt_apply_of_mem_chartTargetEuclid (I := I) (M := M) α f hz]

omit [IsManifold I ∞ M] in
private lemma contDiffAt_chartPushedExt_of_notMem_image_tsupport_compact
    (α : M) {f : M → ℝ}
    (hf_support : tsupport f ⊆ (chartAt H α).source)
    (hf_compact : IsCompact (tsupport f)) {y : EuclN E}
    (hy_off : y ∉ (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport f))) :
    ContDiffAt ℝ ∞ (chartPushedExt (I := I) (M := M) α f) y := by
  classical
  set K : Set (EuclN E) :=
    (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f)) with hK_def
  have hK_compact : IsCompact K := by
    have hsub : tsupport f ⊆ (extChartAt I α).source := by
      intro x hx
      rw [extChartAt_source_eq_chartAt_source (I := I) (M := M)]
      exact hf_support hx
    have hcont : ContinuousOn (extChartAt I α) (tsupport f) :=
      (continuousOn_extChartAt α).mono hsub
    have h1 : IsCompact ((extChartAt I α) '' (tsupport f)) :=
      hf_compact.image_of_continuousOn hcont
    exact h1.image (toEuclidean (E := E)).continuous
  have hK_closed : IsClosed K := hK_compact.isClosed
  have hK_compl_open : IsOpen Kᶜ := hK_closed.isOpen_compl
  have hy_compl : y ∈ Kᶜ := hy_off
  apply ContDiffAt.congr_of_eventuallyEq (f := fun _ : EuclN E => (0 : ℝ)) contDiffAt_const
  filter_upwards [hK_compl_open.mem_nhds hy_compl] with z hz
  exact chartPushedExt_eq_zero_off_image_tsupport
    (I := I) (M := M) α (f := f) hf_support hz

private lemma contDiff_chartPushedExt
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    [I.Boundaryless]
    (hf_support : tsupport f ⊆ (chartAt H α).source)
    (hf_compact : IsCompact (tsupport f)) :
    ContDiff ℝ ∞ (chartPushedExt (I := I) (M := M) α f) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
  · exact contDiffAt_chartPushedExt_of_mem_target (I := I) (M := M) α hf hy_target
  · have hy_off : y ∉ (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport f)) := by
      intro hy_in
      apply hy_target
      exact image_toEuclidean_chart_tsupport_subset_chartTargetEuclid
        (I := I) (M := M) (f := f) (α := α) hf_support hy_in
    exact contDiffAt_chartPushedExt_of_notMem_image_tsupport_compact
      (I := I) (M := M) α (f := f) hf_support hf_compact hy_off

omit [IsManifold I ∞ M] in
private lemma chartTargetEuclid_isOpen' [I.Boundaryless] (α : M) :
    IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
  chartTargetEuclid_isOpen (I := I) (M := M) α

private lemma memLp_chartPushedExt
    [CompactSpace M] [I.Boundaryless]
    (α : M) (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (hρ : ρ.IsSubordinate (fun β : M => (chartAt H β).source))
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (p : ℝ≥0∞) :
    MemLp (chartPushedExt (I := I) (M := M) α
        (fun x => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x))
      p (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set f : M → ℝ := fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x with hf_def
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f :=
    ((ρ α : C^∞⟮I, M; ℝ⟯).contMDiff).mul hu
  have hf_support : tsupport f ⊆ (chartAt H α).source := by
    have h1 : tsupport f ⊆ tsupport ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
      apply tsupport_mul_subset_left
    exact h1.trans (hρ α)
  have hf_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
  have hsmooth : ContDiff ℝ ∞ (chartPushedExt (I := I) (M := M) α f) :=
    contDiff_chartPushedExt (I := I) (M := M) α hf_smooth hf_support hf_compact
  have hcs : HasCompactSupport (chartPushedExt (I := I) (M := M) α f) :=
    hasCompactSupport_chartPushedExt (I := I) (M := M) α hf_support
  have hmemLp_global : MemLp (chartPushedExt (I := I) (M := M) α f) p volume :=
    hsmooth.continuous.memLp_of_hasCompactSupport hcs
  exact hmemLp_global.restrict _

private lemma fderiv_chartPushedExt_memLp
    [CompactSpace M] [I.Boundaryless]
    (α : M) (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (hρ : ρ.IsSubordinate (fun β : M => (chartAt H β).source))
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (p : ℝ≥0∞)
    (i : Fin (Module.finrank ℝ E)) :
    MemLp (fun x : EuclN E =>
        (fderiv ℝ (chartPushedExt (I := I) (M := M) α
          (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x)) x)
          (EuclideanSpace.single i 1))
      p (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set f : M → ℝ := fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x with hf_def
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f :=
    ((ρ α : C^∞⟮I, M; ℝ⟯).contMDiff).mul hu
  have hf_support : tsupport f ⊆ (chartAt H α).source := by
    have h1 : tsupport f ⊆ tsupport ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
      apply tsupport_mul_subset_left
    exact h1.trans (hρ α)
  have hf_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
  have hsmooth : ContDiff ℝ ∞ (chartPushedExt (I := I) (M := M) α f) :=
    contDiff_chartPushedExt (I := I) (M := M) α hf_smooth hf_support hf_compact
  have hcs : HasCompactSupport (chartPushedExt (I := I) (M := M) α f) :=
    hasCompactSupport_chartPushedExt (I := I) (M := M) α hf_support
  have hderiv_smooth : ContDiff ℝ ∞
      (fun x => (fderiv ℝ (chartPushedExt (I := I) (M := M) α f) x)
        (EuclideanSpace.single i 1)) :=
    (hsmooth.fderiv_right (m := (⊤ : ℕ∞)) (by norm_cast)).clm_apply contDiff_const
  have hderiv_cs : HasCompactSupport
      (fun x => (fderiv ℝ (chartPushedExt (I := I) (M := M) α f) x)
        (EuclideanSpace.single i 1)) :=
    hcs.fderiv_apply (𝕜 := ℝ) _
  have hmemLp_global : MemLp _ p volume :=
    hderiv_smooth.continuous.memLp_of_hasCompactSupport hderiv_cs
  exact hmemLp_global.restrict _

private lemma memW1p_chartPushedExt
    [CompactSpace M] [I.Boundaryless]
    (α : M) (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (hρ : ρ.IsSubordinate (fun β : M => (chartAt H β).source))
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) {p : ℝ≥0∞} (_hp : 1 ≤ p) :
    DeGiorgi.MemW1p p (chartPushedExt (I := I) (M := M) α
        (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set f : M → ℝ := fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x with hf_def
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f :=
    ((ρ α : C^∞⟮I, M; ℝ⟯).contMDiff).mul hu
  have hf_support : tsupport f ⊆ (chartAt H α).source := by
    have h1 : tsupport f ⊆ tsupport ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
      apply tsupport_mul_subset_left
    exact h1.trans (hρ α)
  have hf_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
  have hsmooth : ContDiff ℝ ∞ (chartPushedExt (I := I) (M := M) α f) :=
    contDiff_chartPushedExt (I := I) (M := M) α hf_smooth hf_support hf_compact
  refine ⟨?_, ?_⟩
  · exact memLp_chartPushedExt (I := I) (M := M) α ρ hρ hu p
  · intro i
    refine ⟨fun x : EuclN E =>
      (fderiv ℝ (chartPushedExt (I := I) (M := M) α f) x)
        (EuclideanSpace.single i 1), ?_, ?_⟩
    · exact fderiv_chartPushedExt_memLp (I := I) (M := M) α ρ hρ hu p i
    · exact DeGiorgi.HasWeakPartialDeriv.of_contDiff
        (chartTargetEuclid_isOpen' (I := I) (M := M) α)
        (hsmooth.of_le (by norm_cast))

private theorem memW1p_chartPushed_of_contMDiff
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    DeGiorgi.MemW1p p
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set ρ := chartAtlasPOU I M with hρ_def
  have hρ_sub : ρ.IsSubordinate (fun β : M => (chartAt H β).source) :=
    chartAtlasPOU_isSubordinate I M
  have hExt_memW1p : DeGiorgi.MemW1p p
      (chartPushedExt (I := I) (M := M) α
        (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x))
      (chartTargetEuclid (I := I) (M := M) α) :=
    memW1p_chartPushedExt (I := I) (M := M) α ρ hρ_sub hu hp
  have hae_eq : chartPushedExt (I := I) (M := M) α
      (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) =ᵐ[volume.restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      chartPushed (I := I) (M := M) ρ α u := by
    refine
      (MeasureTheory.ae_restrict_iff' (chartTargetEuclid_measurableSet
        (I := I) (M := M) α)).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy
    exact chartPushedExt_eq_chartPushed_on_target
      (I := I) (M := M) ρ α u hy
  exact (Sobolev.Euclidean.MemW1p_congr_ae
    (chartTargetEuclid_isOpen' (I := I) (M := M) α) hae_eq).mp hExt_memW1p

theorem MemWkpChart_of_contMDiff
    [CompactSpace M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M]
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    MemWkpChart (I := I) (M := M) 1 p u := by
  intro α
  rw [show (1 : ℕ) = 0 + 1 from rfl,
    Sobolev.Euclidean.MemWkp_succ]
  refine ⟨?_, ?_⟩
  · exact memW1p_chartPushed_of_contMDiff (I := I) (M := M) α hu hp
  · intro i
    have hMW1p : DeGiorgi.MemW1p p
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u)
        (chartTargetEuclid (I := I) (M := M) α) :=
      memW1p_chartPushed_of_contMDiff (I := I) (M := M) α hu hp
    rw [Sobolev.Euclidean.MemWkp_zero]
    exact Sobolev.Euclidean.chosenWeakPartialOrZero_memLp_of_mem
      (d := Module.finrank ℝ E) hMW1p i

end Equivalence
end Sobolev
