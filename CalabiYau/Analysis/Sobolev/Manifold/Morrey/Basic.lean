-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Manifold/Morrey/Basic.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Euclidean.Embedding.Morrey.Basic
public import CalabiYau.Analysis.Sobolev.Intrinsic.Equivalence.Basic
public import CalabiYau.Analysis.Sobolev.Manifold.Embedding.Basic
public import CalabiYau.Analysis.Sobolev.Manifold.Embedding.Subcritical
public import CalabiYau.Geometry.Riemannian.Volume.Chart.MeasureComparison
public import CalabiYau.Analysis.Sobolev.Manifold.Measure.UniformChartComparison
public import CalabiYau.Analysis.Sobolev.Approximation.Density.FirstOrder
public import CalabiYau.Analysis.Sobolev.Manifold.Rellich.Compactness
public import CalabiYau.Geometry.Riemannian.Volume.Family.Basic
public import CalabiYau.Geometry.Riemannian.Volume.Basic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

def chartSmoothExt (α : M) (f : M → ℝ) : EuclN → ℝ := by
  classical
  exact fun y =>
    if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    else 0

omit [IsManifold I ∞ M] in
private lemma chartSmoothExt_apply_of_mem_target
    (α : M) (f : M → ℝ) {y : EuclN}
    (hy : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target) :
    chartSmoothExt (I := I) (M := M) α f y =
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  classical
  change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    else 0) = f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
  rw [if_pos hy]

omit [IsManifold I ∞ M] in
private lemma chartSmoothExt_apply_of_notMem_target
    (α : M) (f : M → ℝ) {y : EuclN}
    (hy : (toEuclidean (E := E)).symm y ∉ (extChartAt I α).target) :
    chartSmoothExt (I := I) (M := M) α f y = 0 := by
  classical
  change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    else 0) = 0
  rw [if_neg hy]

omit [IsManifold I ∞ M] in
private lemma chartSmoothExt_apply_of_mem_chartTargetEuclid
    (α : M) (f : M → ℝ) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartSmoothExt (I := I) (M := M) α f y =
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  classical
  apply chartSmoothExt_apply_of_mem_target
  rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
  exact hy

omit [IsManifold I ∞ M] in
private lemma chartSmoothExt_apply_of_notMem_chartTargetEuclid
    (α : M) (f : M → ℝ) {y : EuclN}
    (hy : y ∉ chartTargetEuclid (I := I) (M := M) α) :
    chartSmoothExt (I := I) (M := M) α f y = 0 := by
  classical
  apply chartSmoothExt_apply_of_notMem_target
  rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
  exact hy

omit [IsManifold I ∞ M] in
private lemma chartSmoothExt_eq_chartPushed_on_target
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (α : M) (u : M → ℝ) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartSmoothExt (I := I) (M := M) α
        (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) y =
      chartPushed (I := I) (M := M) ρ α u y := by
  classical
  rw [chartSmoothExt_apply_of_mem_chartTargetEuclid (I := I) (M := M) α _ hy]
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
private lemma chartSmoothExt_eq_zero_off_image_tsupport
    (α : M) {f : M → ℝ}
    (_hf_support : tsupport f ⊆ (chartAt H α).source) {y : EuclN}
    (hy_off : y ∉ (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport f))) :
    chartSmoothExt (I := I) (M := M) α f y = 0 := by
  classical
  by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
  · obtain ⟨z, hz_target, hzy⟩ := hy_target
    have hy_target' : y ∈ chartTargetEuclid (I := I) (M := M) α := ⟨z, hz_target, hzy⟩
    have hy_symm : (toEuclidean (E := E)).symm y = z := by
      rw [← hzy]; exact (toEuclidean (E := E)).symm_apply_apply z
    rw [chartSmoothExt_apply_of_mem_chartTargetEuclid (I := I) (M := M) α f hy_target',
      hy_symm]
    by_contra hne
    apply hy_off
    have hsymm_in_support : (extChartAt I α).symm z ∈ tsupport f :=
      subset_tsupport _ (Function.mem_support.mpr hne)
    have hz_eq : (extChartAt I α) ((extChartAt I α).symm z) = z :=
      (extChartAt I α).right_inv hz_target
    refine ⟨z, ⟨(extChartAt I α).symm z, hsymm_in_support, hz_eq⟩, hzy⟩
  · exact chartSmoothExt_apply_of_notMem_chartTargetEuclid (I := I) (M := M) α f hy_target

omit [IsManifold I ∞ M] in
private lemma hasCompactSupport_chartSmoothExt
    [CompactSpace M] (α : M) {f : M → ℝ}
    (hf_support : tsupport f ⊆ (chartAt H α).source) :
    HasCompactSupport (chartSmoothExt (I := I) (M := M) α f) := by
  classical
  set K : Set EuclN :=
    (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f)) with hK_def
  have hK_compact : IsCompact K :=
    image_toEuclidean_chart_tsupport_isCompact
      (I := I) (M := M) (f := f) (α := α) hf_support
  apply HasCompactSupport.of_support_subset_isCompact hK_compact
  intro y hy_support
  by_contra hyK
  apply hy_support
  exact chartSmoothExt_eq_zero_off_image_tsupport
    (I := I) (M := M) α (f := f) hf_support hyK

omit [IsManifold I ∞ M] in
private lemma tsupport_chartSmoothExt_subset
    [CompactSpace M] (α : M) {f : M → ℝ}
    (hf_support : tsupport f ⊆ (chartAt H α).source) :
    tsupport (chartSmoothExt (I := I) (M := M) α f) ⊆
      (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f)) := by
  classical
  set K : Set EuclN :=
    (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f)) with hK_def
  have hK_compact : IsCompact K :=
    image_toEuclidean_chart_tsupport_isCompact
      (I := I) (M := M) (f := f) (α := α) hf_support
  have hK_closed : IsClosed K := hK_compact.isClosed
  have h_support_sub : Function.support (chartSmoothExt (I := I) (M := M) α f) ⊆ K := by
    intro y hy
    by_contra hyK
    apply hy
    exact chartSmoothExt_eq_zero_off_image_tsupport
      (I := I) (M := M) α (f := f) hf_support hyK
  rw [tsupport]
  exact hK_closed.closure_subset_iff.mpr h_support_sub

private lemma contDiffOn_chartSmoothExt_formula
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContDiffOn ℝ ∞
        (fun y : EuclN =>
          f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hscalar : ContDiffOn ℝ ∞
      (fun y : E => f ((extChartAt I α).symm y))
      (extChartAt I α).target := by
    exact CalabiYau.DivergenceTheorem.scalarOnE_contDiffOn (I := I) α hf
  have htoEuc_symm_smooth : ContDiff ℝ ∞ ((toEuclidean (E := E)).symm) :=
    ContinuousLinearEquiv.contDiff _
  have hmaps : Set.MapsTo ((toEuclidean (E := E)).symm)
      (chartTargetEuclid (I := I) (M := M) α) (extChartAt I α).target := by
    intro y hy
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  exact hscalar.comp htoEuc_symm_smooth.contDiffOn hmaps

private lemma contDiffAt_chartSmoothExt_of_mem_target
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    [I.Boundaryless] {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    ContDiffAt ℝ ∞ (chartSmoothExt (I := I) (M := M) α f) y := by
  classical
  have hOpen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hContDiffOn := contDiffOn_chartSmoothExt_formula (I := I) (M := M) α hf
  have hContDiffAt_formula : ContDiffAt ℝ ∞
      (fun y : EuclN => f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) y := by
    have hwithin : ContDiffWithinAt ℝ ∞
        (fun y : EuclN => f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (chartTargetEuclid (I := I) (M := M) α) y := hContDiffOn y hy
    exact hwithin.contDiffAt (hOpen.mem_nhds hy)
  apply hContDiffAt_formula.congr_of_eventuallyEq
  filter_upwards [hOpen.mem_nhds hy] with z hz
  rw [chartSmoothExt_apply_of_mem_chartTargetEuclid (I := I) (M := M) α f hz]

omit [IsManifold I ∞ M] in
private lemma contDiffAt_chartSmoothExt_of_notMem_image_tsupport
    (α : M) {f : M → ℝ}
    (hf_support : tsupport f ⊆ (chartAt H α).source)
    (hf_compact : IsCompact (tsupport f)) {y : EuclN}
    (hy_off : y ∉ (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport f))) :
    ContDiffAt ℝ ∞ (chartSmoothExt (I := I) (M := M) α f) y := by
  classical
  set K : Set EuclN :=
    (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f)) with hK_def
  have hK_compact : IsCompact K := by
    have hsub : tsupport f ⊆ (extChartAt I α).source := by
      intro x hx
      rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)]
      exact hf_support hx
    have hcont : ContinuousOn (extChartAt I α) (tsupport f) :=
      (continuousOn_extChartAt α).mono hsub
    have h1 : IsCompact ((extChartAt I α) '' (tsupport f)) :=
      hf_compact.image_of_continuousOn hcont
    exact h1.image (toEuclidean (E := E)).continuous
  have hK_closed : IsClosed K := hK_compact.isClosed
  have hK_compl_open : IsOpen Kᶜ := hK_closed.isOpen_compl
  have hy_compl : y ∈ Kᶜ := hy_off
  apply ContDiffAt.congr_of_eventuallyEq (f := fun _ : EuclN => (0 : ℝ)) contDiffAt_const
  filter_upwards [hK_compl_open.mem_nhds hy_compl] with z hz
  exact chartSmoothExt_eq_zero_off_image_tsupport
    (I := I) (M := M) α (f := f) hf_support hz

private lemma contDiff_chartSmoothExt
    (α : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    [I.Boundaryless]
    (hf_support : tsupport f ⊆ (chartAt H α).source)
    (hf_compact : IsCompact (tsupport f)) :
    ContDiff ℝ ∞ (chartSmoothExt (I := I) (M := M) α f) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
  · exact contDiffAt_chartSmoothExt_of_mem_target (I := I) (M := M) α hf hy_target
  · have hy_off : y ∉ (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport f)) := by
      intro hy_in
      apply hy_target
      exact image_toEuclidean_chart_tsupport_subset_chartTargetEuclid
        (I := I) (M := M) (f := f) (α := α) hf_support hy_in
    exact contDiffAt_chartSmoothExt_of_notMem_image_tsupport
      (I := I) (M := M) α (f := f) hf_support hf_compact hy_off

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private lemma tsupport_pou_mul_subset_chart_source
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (hρ : ρ.IsSubordinate (fun β : M => (chartAt H β).source))
    (α : M) (u : M → ℝ) :
    tsupport (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) ⊆
      (chartAt H α).source := by
  have h1 : tsupport (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) ⊆
      tsupport ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
    have h_eq : (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) =
        (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x • u x) := by funext x; rfl
    rw [h_eq]
    exact tsupport_smul_subset_left
      (f := fun x : M => ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) (g := u)
  exact h1.trans (hρ α)

lemma contDiff_chartSmoothExt_pou_mul
    [CompactSpace M] [I.Boundaryless]
    (α : M) (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (hρ : ρ.IsSubordinate (fun β : M => (chartAt H β).source))
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    ContDiff ℝ ∞ (chartSmoothExt (I := I) (M := M) α
      (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x)) := by
  set f : M → ℝ := fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x with hf_def
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f :=
    ((ρ α : C^∞⟮I, M; ℝ⟯).contMDiff).mul hu
  have hf_support : tsupport f ⊆ (chartAt H α).source :=
    tsupport_pou_mul_subset_chart_source (I := I) (M := M) ρ hρ α u
  have hf_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
  exact contDiff_chartSmoothExt (I := I) (M := M) α hf_smooth hf_support hf_compact

omit [IsManifold I ∞ M] in
lemma hasCompactSupport_chartSmoothExt_pou_mul
    [CompactSpace M] (α : M) (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (hρ : ρ.IsSubordinate (fun β : M => (chartAt H β).source)) (u : M → ℝ) :
    HasCompactSupport (chartSmoothExt (I := I) (M := M) α
      (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x)) := by
  set f : M → ℝ := fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x with hf_def
  have hf_support : tsupport f ⊆ (chartAt H α).source :=
    tsupport_pou_mul_subset_chart_source (I := I) (M := M) ρ hρ α u
  exact hasCompactSupport_chartSmoothExt (I := I) (M := M) α hf_support

omit [IsManifold I ∞ M] in
private lemma tsupport_chartSmoothExt_pou_mul_subset_chart_image
    [CompactSpace M] (α : M) (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (hρ : ρ.IsSubordinate (fun β : M => (chartAt H β).source)) (u : M → ℝ) :
    tsupport (chartSmoothExt (I := I) (M := M) α
      (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x)) ⊆
      (toEuclidean (E := E)) ''
        ((extChartAt I α) ''
          (tsupport ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ))) := by
  have hsupp_pou_mul : tsupport (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) ⊆
      (chartAt H α).source :=
    tsupport_pou_mul_subset_chart_source (I := I) (M := M) ρ hρ α u
  have hsubset_tsupport : tsupport (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) ⊆
      tsupport ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
    have h_eq : (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) =
        (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x • u x) := by funext x; rfl
    rw [h_eq]
    exact tsupport_smul_subset_left
      (f := fun x : M => ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) (g := u)
  have hstep := tsupport_chartSmoothExt_subset (I := I) (M := M) α (f :=
    fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) hsupp_pou_mul
  refine hstep.trans ?_
  intro y ⟨z, ⟨x, hx_support, hxz⟩, hzy⟩
  refine ⟨z, ⟨x, hsubset_tsupport hx_support, hxz⟩, hzy⟩

variable [T2Space M] [CompactSpace M] [I.Boundaryless]

def chartCarrier (α : M) : Set EuclN :=
  (toEuclidean (E := E)) ''
    ((extChartAt I α) ''
      (tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ)))

omit [I.Boundaryless] in
lemma chartCarrier_isCompact (α : M) :
    IsCompact (chartCarrier (I := I) (M := M) α) := by
  unfold chartCarrier
  set Tα : Set M := tsupport
    ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hTα_def
  have hTα_compact : IsCompact Tα := (isClosed_tsupport _).isCompact
  have hTα_chart_source : Tα ⊆ (chartAt H α).source :=
    CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M α
  have hTα_ext_source : Tα ⊆ (extChartAt I α).source := by
    intro x hx
    rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
      (I := I) (M := M)]
    exact hTα_chart_source hx
  have hcont_ext : ContinuousOn (extChartAt I α) Tα :=
    (continuousOn_extChartAt α).mono hTα_ext_source
  have hImage_ext_compact : IsCompact ((extChartAt I α) '' Tα) :=
    hTα_compact.image_of_continuousOn hcont_ext
  exact hImage_ext_compact.image (toEuclidean (E := E)).continuous

omit [I.Boundaryless] in
lemma chartCarrier_subset_chartTargetEuclid (α : M) :
    chartCarrier (I := I) (M := M) α ⊆ chartTargetEuclid (I := I) (M := M) α := by
  unfold chartCarrier
  set Tα : Set M := tsupport
    ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hTα_def
  have hTα_chart_source : Tα ⊆ (chartAt H α).source :=
    CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M α
  have hTα_ext_source : Tα ⊆ (extChartAt I α).source := by
    intro x hx
    rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
      (I := I) (M := M)]
    exact hTα_chart_source hx
  rintro y ⟨z, ⟨x, hx_support, hxz⟩, hzy⟩
  refine ⟨z, ?_, hzy⟩
  rw [← hxz]
  exact (extChartAt I α).map_source (hTα_ext_source hx_support)

noncomputable def chartRadius (α : M) : ℝ :=
  (((chartCarrier_isCompact (I := I) (M := M) α).isBounded.subset_ball_lt
      0 (0 : EuclN)).choose) * 2 + 1

omit [I.Boundaryless] in
lemma chartRadius_pos (α : M) : 0 < chartRadius (I := I) (M := M) α := by
  unfold chartRadius
  have h := ((chartCarrier_isCompact (I := I) (M := M) α).isBounded.subset_ball_lt
    0 (0 : EuclN)).choose_spec
  linarith [h.1]

omit [I.Boundaryless] in
lemma chartCarrier_subset_half_ball (α : M) :
    chartCarrier (I := I) (M := M) α ⊆
      Metric.ball (0 : EuclN) (chartRadius (I := I) (M := M) α / 2) := by
  unfold chartRadius
  have h := ((chartCarrier_isCompact (I := I) (M := M) α).isBounded.subset_ball_lt
    0 (0 : EuclN)).choose_spec
  have h1 : 0 < (((chartCarrier_isCompact (I := I) (M := M) α).isBounded.subset_ball_lt
      0 (0 : EuclN)).choose) := h.1
  have h2 : chartCarrier (I := I) (M := M) α ⊆
      Metric.ball (0 : EuclN)
        (((chartCarrier_isCompact (I := I) (M := M) α).isBounded.subset_ball_lt
          0 (0 : EuclN)).choose) := h.2
  refine h2.trans ?_
  intro y hy
  rw [Metric.mem_ball] at hy ⊢
  have h_ineq : (((chartCarrier_isCompact (I := I) (M := M) α).isBounded.subset_ball_lt
      0 (0 : EuclN)).choose) ≤
      (((chartCarrier_isCompact (I := I) (M := M) α).isBounded.subset_ball_lt
        0 (0 : EuclN)).choose * 2 + 1) / 2 := by
    linarith
  linarith

omit [I.Boundaryless] in
lemma chartCarrier_subset_radius_ball (α : M) :
    chartCarrier (I := I) (M := M) α ⊆
      Metric.ball (0 : EuclN) (chartRadius (I := I) (M := M) α) := by
  refine (chartCarrier_subset_half_ball (I := I) (M := M) α).trans ?_
  intro y hy
  rw [Metric.mem_ball] at hy ⊢
  have h := chartRadius_pos (I := I) (M := M) α
  linarith

omit [I.Boundaryless] in
lemma tsupport_chartSmoothExt_pou_mul_subset_chartCarrier
    (α : M) (u : M → ℝ) :
    tsupport (chartSmoothExt (I := I) (M := M) α
      (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x)) ⊆
      chartCarrier (I := I) (M := M) α := by
  unfold chartCarrier
  exact tsupport_chartSmoothExt_pou_mul_subset_chart_image
    (I := I) (M := M) α (CalabiYau.RiemannianVolume.chartAtlasPOU I M)
    (CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M) u

omit [I.Boundaryless] in
private lemma chartSmoothExt_pou_mul_eq_zero_off_half_ball
    (α : M) (u : M → ℝ) {y : EuclN}
    (hy : y ∉ Metric.ball (0 : EuclN) (chartRadius (I := I) (M := M) α / 2)) :
    chartSmoothExt (I := I) (M := M) α
      (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x) y = 0 := by
  by_contra hne
  apply hy
  have h_in_support : y ∈ Function.support (chartSmoothExt (I := I) (M := M) α
      (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x)) := Function.mem_support.mpr hne
  have h_in_tsupport := subset_tsupport _ h_in_support
  exact chartCarrier_subset_half_ball (I := I) (M := M) α
    (tsupport_chartSmoothExt_pou_mul_subset_chartCarrier (I := I) (M := M) α u
      h_in_tsupport)

private lemma chartSmoothExt_morrey_sup_uniform
    (α : M) {p : ℝ} (hp : (Module.finrank ℝ E : ℝ) < p)
    [NeZero (Module.finrank ℝ E)] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
        ∀ y : EuclN, ‖chartSmoothExt (I := I) (M := M) α
          (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x) y‖ ≤ C *
          ((eLpNorm (chartSmoothExt (I := I) (M := M) α
              (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
                : C^∞⟮I, M; ℝ⟯) x * u x)) (ENNReal.ofReal p)
              (volume.restrict (Metric.ball (0 : EuclN) (chartRadius (I := I) (M := M) α)))).toReal
                +
           (eLpNorm (fun z => ‖fderiv ℝ (chartSmoothExt (I := I) (M := M) α
              (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
                : C^∞⟮I, M; ℝ⟯) x * u x)) z‖) (ENNReal.ofReal p)
             (volume.restrict (Metric.ball (0 : EuclN)
               (chartRadius (I := I) (M := M) α)))).toReal) := by
  classical
  have hR_pos : 0 < chartRadius (I := I) (M := M) α := chartRadius_pos (I := I) (M := M) α
  obtain ⟨C, hC_nn, hbound⟩ :=
    Sobolev.EuclideanMorrey.smooth_morrey_sup_bound_uniform
      (d := Module.finrank ℝ E) hp
      (x₀ := (0 : EuclN)) (R := chartRadius (I := I) (M := M) α) hR_pos
  refine ⟨C, hC_nn, ?_⟩
  intro u hu y
  set f : EuclN → ℝ := chartSmoothExt (I := I) (M := M) α
    (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) x * u x) with hf_def
  have hf_smooth : ContDiff ℝ ∞ f := by
    rw [hf_def]
    exact contDiff_chartSmoothExt_pou_mul (I := I) (M := M) α
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M)
      (CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M) hu
  have hf_smooth_top : ContDiff ℝ (⊤ : ℕ∞) f := by
    have : ContDiff ℝ ∞ f := hf_smooth
    exact this
  by_cases hy_half : y ∈ Metric.ball (0 : EuclN) (chartRadius (I := I) (M := M) α / 2)
  · exact hbound hf_smooth_top y hy_half
  · have hf_y_zero : f y = 0 :=
      chartSmoothExt_pou_mul_eq_zero_off_half_ball (I := I) (M := M) α u hy_half
    rw [hf_y_zero, norm_zero]
    have h_nn1 : 0 ≤ (eLpNorm f (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuclN) (chartRadius (I := I) (M := M) α)))).toReal :=
      ENNReal.toReal_nonneg
    have h_nn2 : 0 ≤ (eLpNorm (fun z => ‖fderiv ℝ f z‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuclN) (chartRadius (I := I) (M := M) α)))).toReal :=
      ENNReal.toReal_nonneg
    have h_RHS_nn : 0 ≤ C *
        ((eLpNorm f (ENNReal.ofReal p)
            (volume.restrict (Metric.ball (0 : EuclN) (chartRadius (I := I) (M := M) α)))).toReal +
         (eLpNorm (fun z => ‖fderiv ℝ f z‖) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball (0 : EuclN)
              (chartRadius (I := I) (M := M) α)))).toReal) := by
      apply mul_nonneg hC_nn
      linarith
    exact h_RHS_nn

omit [IsManifold I ∞ M] [T2Space M] [CompactSpace M] [I.Boundaryless] in
private lemma chartSmoothExt_eq_zero_off_target
    (α : M) (f : M → ℝ) {y : EuclN}
    (hy : y ∉ chartTargetEuclid (I := I) (M := M) α) :
    chartSmoothExt (I := I) (M := M) α f y = 0 :=
  chartSmoothExt_apply_of_notMem_chartTargetEuclid (I := I) (M := M) α f hy

omit [FiniteDimensional ℝ E] in
private lemma fderiv_eq_zero_off_tsupport_subset_closed
    {h : EuclN → ℝ} {K : Set EuclN} (hK_closed : IsClosed K)
    (hh_support : tsupport h ⊆ K) {y : EuclN} (hy : y ∉ K) :
    fderiv ℝ h y = 0 := by
  have hy_off_tsupp : y ∉ tsupport h := fun hyt => hy (hh_support hyt)
  have h_compl : Kᶜ ∈ 𝓝 y := hK_closed.isOpen_compl.mem_nhds hy
  have hh_zero_eventually : h =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := by
    refine Filter.eventuallyEq_of_mem h_compl ?_
    intro z hz
    have hz_off_tsupp : z ∉ tsupport h := fun hzt => hz (hh_support hzt)
    exact image_eq_zero_of_notMem_tsupport hz_off_tsupp
  rw [Filter.EventuallyEq.fderiv_eq hh_zero_eventually]
  simp

omit [IsManifold I ∞ M] [T2Space M] [CompactSpace M] [I.Boundaryless] in
private lemma eLpNorm_chartSmoothExt_eq_restrict_target
    (α : M) (f : M → ℝ) (q : ℝ≥0∞) :
    eLpNorm (chartSmoothExt (I := I) (M := M) α f) q volume =
      eLpNorm (chartSmoothExt (I := I) (M := M) α f) q
        (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set h : EuclN → ℝ := chartSmoothExt (I := I) (M := M) α f with hh_def
  have hΩ_meas : MeasurableSet Ω :=
    chartTargetEuclid_measurableSet (I := I) (M := M) α
  have h_eq : h = Ω.indicator h := by
    funext y
    by_cases hy : y ∈ Ω
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      exact chartSmoothExt_eq_zero_off_target (I := I) (M := M) α f hy
  calc eLpNorm h q volume
      = eLpNorm (Ω.indicator h) q volume := by rw [← h_eq]
    _ = eLpNorm h q (volume.restrict Ω) :=
        eLpNorm_indicator_eq_eLpNorm_restrict hΩ_meas

omit [I.Boundaryless] in
private lemma eLpNorm_norm_fderiv_chartSmoothExt_pou_mul_eq_restrict_target
    (α : M) (u : M → ℝ) (q : ℝ≥0∞) :
    eLpNorm (fun z => ‖fderiv ℝ (chartSmoothExt (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x)) z‖) q volume =
      eLpNorm (fun z => ‖fderiv ℝ (chartSmoothExt (I := I) (M := M) α
          (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x)) z‖) q
        (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set h : EuclN → ℝ := chartSmoothExt (I := I) (M := M) α
    (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) x * u x) with hh_def
  set K : Set EuclN := chartCarrier (I := I) (M := M) α with hK_def
  have hK_closed : IsClosed K := (chartCarrier_isCompact (I := I) (M := M) α).isClosed
  have hK_support : tsupport h ⊆ K :=
    tsupport_chartSmoothExt_pou_mul_subset_chartCarrier (I := I) (M := M) α u
  have hK_subset_Ω : K ⊆ Ω :=
    chartCarrier_subset_chartTargetEuclid (I := I) (M := M) α
  have hΩ_meas : MeasurableSet Ω :=
    chartTargetEuclid_measurableSet (I := I) (M := M) α
  set fnNorm : EuclN → ℝ := fun z => ‖fderiv ℝ h z‖ with hfnNorm_def
  have h_eq : fnNorm = Ω.indicator fnNorm := by
    funext y
    by_cases hy : y ∈ Ω
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      have hyK : y ∉ K := fun h2 => hy (hK_subset_Ω h2)
      have h_fderiv_zero : fderiv ℝ h y = 0 :=
        fderiv_eq_zero_off_tsupport_subset_closed hK_closed hK_support hyK
      change ‖fderiv ℝ h y‖ = 0
      rw [h_fderiv_zero, norm_zero]
  calc eLpNorm fnNorm q volume
      = eLpNorm (Ω.indicator fnNorm) q volume := by rw [← h_eq]
    _ = eLpNorm fnNorm q (volume.restrict Ω) :=
        eLpNorm_indicator_eq_eLpNorm_restrict hΩ_meas

omit [I.Boundaryless] in
private lemma eLpNorm_chartSmoothExt_pou_mul_restrict_ball_eq_restrict_target
    (α : M) (u : M → ℝ) (q : ℝ≥0∞) :
    eLpNorm (chartSmoothExt (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x)) q
      (volume.restrict (Metric.ball (0 : EuclN) (chartRadius (I := I) (M := M) α))) =
      eLpNorm (chartSmoothExt (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x)) q
        (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set h : EuclN → ℝ := chartSmoothExt (I := I) (M := M) α
    (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) x * u x) with hh_def
  set K : Set EuclN := chartCarrier (I := I) (M := M) α with hK_def
  set BR : Set EuclN := Metric.ball (0 : EuclN) (chartRadius (I := I) (M := M) α)
    with hBR_def
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hK_closed : IsClosed K := (chartCarrier_isCompact (I := I) (M := M) α).isClosed
  have hK_support : tsupport h ⊆ K :=
    tsupport_chartSmoothExt_pou_mul_subset_chartCarrier (I := I) (M := M) α u
  have hK_BR : K ⊆ BR :=
    chartCarrier_subset_radius_ball (I := I) (M := M) α
  have hK_Ω : K ⊆ Ω :=
    chartCarrier_subset_chartTargetEuclid (I := I) (M := M) α
  have hBR_meas : MeasurableSet BR := measurableSet_ball
  have hΩ_meas : MeasurableSet Ω :=
    chartTargetEuclid_measurableSet (I := I) (M := M) α
  have h_eq_BR : h = BR.indicator h := by
    funext y
    by_cases hy : y ∈ BR
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      have hyK : y ∉ K := fun h2 => hy (hK_BR h2)
      have hy_off_tsupp : y ∉ tsupport h := fun hyt => hyK (hK_support hyt)
      exact image_eq_zero_of_notMem_tsupport hy_off_tsupp
  have h_eq_Ω : h = Ω.indicator h := by
    funext y
    by_cases hy : y ∈ Ω
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      exact chartSmoothExt_eq_zero_off_target (I := I) (M := M) α _ hy
  calc eLpNorm h q (volume.restrict BR)
      = eLpNorm (BR.indicator h) q volume :=
        (eLpNorm_indicator_eq_eLpNorm_restrict hBR_meas).symm
    _ = eLpNorm h q volume := by rw [← h_eq_BR]
    _ = eLpNorm (Ω.indicator h) q volume := by rw [← h_eq_Ω]
    _ = eLpNorm h q (volume.restrict Ω) :=
        eLpNorm_indicator_eq_eLpNorm_restrict hΩ_meas

omit [I.Boundaryless] in
private lemma eLpNorm_norm_fderiv_chartSmoothExt_pou_mul_restrict_ball_eq_restrict_target
    (α : M) (u : M → ℝ) (q : ℝ≥0∞) :
    eLpNorm (fun z : EuclN => ‖fderiv ℝ (chartSmoothExt (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x)) z‖) q
      (volume.restrict (Metric.ball (0 : EuclN) (chartRadius (I := I) (M := M) α))) =
      eLpNorm (fun z : EuclN => ‖fderiv ℝ (chartSmoothExt (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x)) z‖) q
        (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set h : EuclN → ℝ := chartSmoothExt (I := I) (M := M) α
    (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) x * u x) with hh_def
  set K : Set EuclN := chartCarrier (I := I) (M := M) α with hK_def
  set BR : Set EuclN := Metric.ball (0 : EuclN) (chartRadius (I := I) (M := M) α)
    with hBR_def
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hK_closed : IsClosed K := (chartCarrier_isCompact (I := I) (M := M) α).isClosed
  have hK_support : tsupport h ⊆ K :=
    tsupport_chartSmoothExt_pou_mul_subset_chartCarrier (I := I) (M := M) α u
  have hK_BR : K ⊆ BR :=
    chartCarrier_subset_radius_ball (I := I) (M := M) α
  have hK_Ω : K ⊆ Ω :=
    chartCarrier_subset_chartTargetEuclid (I := I) (M := M) α
  have hBR_meas : MeasurableSet BR := measurableSet_ball
  have hΩ_meas : MeasurableSet Ω :=
    chartTargetEuclid_measurableSet (I := I) (M := M) α
  set fnNorm : EuclN → ℝ := fun z => ‖fderiv ℝ h z‖ with hfnNorm_def
  have h_eq_BR : fnNorm = BR.indicator fnNorm := by
    funext y
    by_cases hy : y ∈ BR
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      have hyK : y ∉ K := fun h2 => hy (hK_BR h2)
      have h_fderiv_zero : fderiv ℝ h y = 0 :=
        fderiv_eq_zero_off_tsupport_subset_closed hK_closed hK_support hyK
      change ‖fderiv ℝ h y‖ = 0
      rw [h_fderiv_zero, norm_zero]
  have h_eq_Ω : fnNorm = Ω.indicator fnNorm := by
    funext y
    by_cases hy : y ∈ Ω
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      have hyK : y ∉ K := fun h2 => hy (hK_Ω h2)
      have h_fderiv_zero : fderiv ℝ h y = 0 :=
        fderiv_eq_zero_off_tsupport_subset_closed hK_closed hK_support hyK
      change ‖fderiv ℝ h y‖ = 0
      rw [h_fderiv_zero, norm_zero]
  calc eLpNorm fnNorm q (volume.restrict BR)
      = eLpNorm (BR.indicator fnNorm) q volume :=
        (eLpNorm_indicator_eq_eLpNorm_restrict hBR_meas).symm
    _ = eLpNorm fnNorm q volume := by rw [← h_eq_BR]
    _ = eLpNorm (Ω.indicator fnNorm) q volume := by rw [← h_eq_Ω]
    _ = eLpNorm fnNorm q (volume.restrict Ω) :=
        eLpNorm_indicator_eq_eLpNorm_restrict hΩ_meas

omit [I.Boundaryless] in
lemma chartSmoothExt_ae_eq_chartPushed
    (α : M) (u : M → ℝ) :
    chartSmoothExt (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x) =ᵐ[volume.restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u := by
  refine (MeasureTheory.ae_restrict_iff' (chartTargetEuclid_measurableSet
    (I := I) (M := M) α)).mpr ?_
  refine Filter.Eventually.of_forall ?_
  intro y hy
  exact chartSmoothExt_eq_chartPushed_on_target
    (I := I) (M := M) (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u hy

omit [I.Boundaryless] in
private lemma eLpNorm_chartSmoothExt_target_eq_eLpNorm_chartPushed_target
    (α : M) (u : M → ℝ) (q : ℝ≥0∞) :
    eLpNorm (chartSmoothExt (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x)) q
      (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) =
      eLpNorm (chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u) q
        (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) :=
  eLpNorm_congr_ae (chartSmoothExt_ae_eq_chartPushed (I := I) (M := M) α u)

omit [I.Boundaryless] in
private lemma eLpNorm_chartSmoothExt_ball_le_wkpNormChart
    (α : M) (u : M → ℝ) (q : ℝ≥0∞) :
    eLpNorm (chartSmoothExt (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x)) q
      (volume.restrict (Metric.ball (0 : EuclN) (chartRadius (I := I) (M := M) α))) ≤
      wkpNormChart (I := I) (M := M) 1 q u := by
  classical
  rw [eLpNorm_chartSmoothExt_pou_mul_restrict_ball_eq_restrict_target
    (I := I) (M := M) α u q]
  rw [eLpNorm_chartSmoothExt_target_eq_eLpNorm_chartPushed_target
    (I := I) (M := M) α u q]
  exact eLpNorm_chartPushed_p_le_wkpNorm_one (I := I) (M := M) (p := q) u α

omit [FiniteDimensional ℝ E] in
private lemma euclN_norm_le_sum_components_norms (w : EuclN) :
    ‖w‖ ≤ ∑ i : Fin (Module.finrank ℝ E), ‖w i‖ := by
  classical
  have h_w_sum :
      w = ∑ i : Fin (Module.finrank ℝ E), EuclideanSpace.single i (w i) := by
    ext j
    simp [Finset.sum_apply]
  conv_lhs => rw [h_w_sum]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  simp

omit [FiniteDimensional ℝ E] in
private lemma norm_fderiv_eq_norm_partials_local
    {ψ : EuclN → ℝ} (y : EuclN) :
    ‖fderiv ℝ ψ y‖ =
      ‖(WithLp.toLp 2
        (fun i : Fin (Module.finrank ℝ E) =>
          (fderiv ℝ ψ y) (EuclideanSpace.single i 1)) : EuclN)‖ := by
  classical
  set v : EuclN :=
    (InnerProductSpace.toDual ℝ EuclN).symm (fderiv ℝ ψ y) with hv_def
  have hv_map : (InnerProductSpace.toDual ℝ EuclN) v = fderiv ℝ ψ y := by simp [v]
  have h_fderiv_norm_eq_v : ‖fderiv ℝ ψ y‖ = ‖v‖ := by simp [v]
  have h_v_eq_components : v =
      WithLp.toLp 2
        (fun i : Fin (Module.finrank ℝ E) =>
          (fderiv ℝ ψ y) (EuclideanSpace.single i 1)) := by
    ext i
    calc
      v i = inner ℝ v (EuclideanSpace.single i (1 : ℝ)) := by
        simpa using
          (EuclideanSpace.inner_single_right (i := i) (a := (1 : ℝ)) v).symm
      _ = ((InnerProductSpace.toDual ℝ EuclN) v) (EuclideanSpace.single i (1 : ℝ)) := by
        rw [InnerProductSpace.toDual_apply_apply]
      _ = (fderiv ℝ ψ y) (EuclideanSpace.single i (1 : ℝ)) := by rw [hv_map]
      _ = (WithLp.toLp 2
            (fun j : Fin (Module.finrank ℝ E) =>
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))) i := by simp
  rw [h_fderiv_norm_eq_v, h_v_eq_components]

omit [FiniteDimensional ℝ E] in
private lemma norm_fderiv_le_sum_partials_local
    (ψ : EuclN → ℝ) (y : EuclN) :
    ‖fderiv ℝ ψ y‖ ≤
      ∑ i : Fin (Module.finrank ℝ E), ‖(fderiv ℝ ψ y) (EuclideanSpace.single i 1)‖ := by
  rw [norm_fderiv_eq_norm_partials_local (ψ := ψ) y]
  refine (euclN_norm_le_sum_components_norms _).trans ?_
  apply le_of_eq
  refine Finset.sum_congr rfl ?_
  intro i _
  simp

omit [FiniteDimensional ℝ E] in
private lemma eLpNorm_norm_fderiv_le_sum_eLpNorm_partials
    {q : ℝ≥0∞} (hq_one : 1 ≤ q) {μ : Measure EuclN}
    {f : EuclN → ℝ} (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f) :
    eLpNorm (fun z : EuclN => ‖fderiv ℝ f z‖) q μ ≤
      ∑ i : Fin (Module.finrank ℝ E),
        eLpNorm (fun z : EuclN => (fderiv ℝ f z) (EuclideanSpace.single i 1)) q μ := by
  classical
  have h_aesm_comp : ∀ i : Fin (Module.finrank ℝ E),
      AEStronglyMeasurable
        (fun z : EuclN => (fderiv ℝ f z) (EuclideanSpace.single i 1)) μ := by
    intro i
    have h_cont : Continuous
        (fun z : EuclN => (fderiv ℝ f z) (EuclideanSpace.single i 1)) :=
      ((hf_smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
    exact h_cont.aestronglyMeasurable
  have h_pt : ∀ z : EuclN,
      ‖fderiv ℝ f z‖ ≤ ∑ i : Fin (Module.finrank ℝ E),
        ‖(fderiv ℝ f z) (EuclideanSpace.single i 1)‖ :=
    fun z => norm_fderiv_le_sum_partials_local f z
  have h_step1 : eLpNorm (fun z : EuclN => ‖fderiv ℝ f z‖) q μ ≤
      eLpNorm (fun z : EuclN =>
        ∑ i : Fin (Module.finrank ℝ E),
          ‖(fderiv ℝ f z) (EuclideanSpace.single i 1)‖) q μ := by
    apply eLpNorm_mono_real
    intro z
    have hh := h_pt z
    have h_norm : ‖‖fderiv ℝ f z‖‖ = ‖fderiv ℝ f z‖ :=
      Real.norm_of_nonneg (norm_nonneg _)
    rw [h_norm]
    exact hh
  refine h_step1.trans ?_
  have h_sum_le := eLpNorm_sum_le (μ := μ) (p := q)
    (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
    (f := fun i => fun z : EuclN => ‖(fderiv ℝ f z) (EuclideanSpace.single i 1)‖)
    (fun i _ => (h_aesm_comp i).norm) hq_one
  have h_lhs_eq :
      (fun z : EuclN =>
        ∑ i : Fin (Module.finrank ℝ E),
          ‖(fderiv ℝ f z) (EuclideanSpace.single i 1)‖) =
        ∑ i : Fin (Module.finrank ℝ E),
          fun z : EuclN => ‖(fderiv ℝ f z) (EuclideanSpace.single i 1)‖ := by
    funext z
    simp [Finset.sum_apply]
  rw [h_lhs_eq]
  refine h_sum_le.trans ?_
  apply Finset.sum_le_sum
  intro i _
  rw [eLpNorm_norm]

omit [FiniteDimensional ℝ E] in
private lemma classical_partial_ae_eq_chosenWeakPartial_local
    {q : ℝ≥0∞} (hq_one : 1 ≤ q) {Ω : Set EuclN} (hΩ_open : IsOpen Ω)
    {f : EuclN → ℝ} (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_compact : HasCompactSupport f) (hf_support : tsupport f ⊆ Ω)
    (i : Fin (Module.finrank ℝ E)) :
    (fun z : EuclN => (fderiv ℝ f z) (EuclideanSpace.single i 1))
      =ᵐ[volume.restrict Ω]
      Sobolev.Euclidean.chosenWeakPartialOrZero q i f Ω := by
  classical
  have hf_mem : Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 q f Ω :=
    Sobolev.Euclidean.MemWkp_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hΩ_open hf_smooth hf_compact hf_support hq_one 1
  have hf_W1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) q f Ω :=
    Sobolev.Euclidean.MemWkp.one_iff_memW1p.mp hf_mem
  have h_classical_isWeak :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
        (fun z : EuclN => (fderiv ℝ f z) (EuclideanSpace.single i 1)) f Ω :=
    DeGiorgi.HasWeakPartialDeriv.of_contDiff (Ω := Ω) (i := i) (f := f)
      hΩ_open (hf_smooth.of_le (by norm_cast))
  have h_chosen_isWeak :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
        (Sobolev.Euclidean.chosenWeakPartialOrZero q i f Ω) f Ω :=
    Sobolev.Euclidean.chosenWeakPartialOrZero_isWeakPartial_of_mem
      hf_W1p i
  have h_classical_local : LocallyIntegrable
      (fun z : EuclN => (fderiv ℝ f z) (EuclideanSpace.single i 1))
      (volume.restrict Ω) := by
    have h_cont : Continuous
        (fun z : EuclN => (fderiv ℝ f z) (EuclideanSpace.single i 1)) :=
      ((hf_smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
    exact h_cont.locallyIntegrable.mono_measure Measure.restrict_le_self
  have h_chosen_local : LocallyIntegrable
      (Sobolev.Euclidean.chosenWeakPartialOrZero q i f Ω)
      (volume.restrict Ω) :=
    (Sobolev.Euclidean.chosenWeakPartialOrZero_memLp_of_mem
      hf_W1p i).locallyIntegrable hq_one
  exact DeGiorgi.HasWeakPartialDeriv.ae_eq (Ω := Ω) hΩ_open
    h_classical_isWeak h_chosen_isWeak h_classical_local h_chosen_local

omit [FiniteDimensional ℝ E] in
private lemma eLpNorm_norm_fderiv_le_d_mul_wkpNorm
    [NeZero (Module.finrank ℝ E)]
    {q : ℝ≥0∞} (hq_one : 1 ≤ q) {Ω : Set EuclN} (hΩ_open : IsOpen Ω)
    {f : EuclN → ℝ} (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf_compact : HasCompactSupport f) (hf_support : tsupport f ⊆ Ω) :
    eLpNorm (fun z : EuclN => ‖fderiv ℝ f z‖) q (volume.restrict Ω) ≤
      ((Module.finrank ℝ E : ℕ) : ℝ≥0∞) *
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 q f Ω := by
  classical
  have h_grad_le := eLpNorm_norm_fderiv_le_sum_eLpNorm_partials
    (q := q) hq_one (μ := volume.restrict Ω) hf_smooth
  refine h_grad_le.trans ?_
  have h_each_eq : ∀ i : Fin (Module.finrank ℝ E),
      eLpNorm (fun z : EuclN => (fderiv ℝ f z) (EuclideanSpace.single i 1)) q
        (volume.restrict Ω) =
      eLpNorm
        (Sobolev.Euclidean.chosenWeakPartialOrZero q i f Ω)
        q (volume.restrict Ω) := fun i =>
    eLpNorm_congr_ae (classical_partial_ae_eq_chosenWeakPartial_local
      hq_one hΩ_open hf_smooth hf_compact hf_support i)
  have h_step1 :
      ∑ i : Fin (Module.finrank ℝ E),
        eLpNorm (fun z : EuclN => (fderiv ℝ f z) (EuclideanSpace.single i 1)) q
          (volume.restrict Ω)
        = ∑ i : Fin (Module.finrank ℝ E),
          eLpNorm
            (Sobolev.Euclidean.chosenWeakPartialOrZero q i f Ω)
            q (volume.restrict Ω) :=
    Finset.sum_congr rfl (fun i _ => h_each_eq i)
  rw [h_step1]
  have hWkpEq :
      Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 q f Ω =
        ∑ j ∈ Finset.range 2,
          ∑ β : Fin j → Fin (Module.finrank ℝ E),
            eLpNorm
              (Sobolev.Euclidean.iterWeakPartial
                (d := Module.finrank ℝ E) q j β f Ω)
              q (volume.restrict Ω) :=
    Sobolev.Euclidean.wkpNorm_eq_sum 1 q f Ω
  have h_j1_term :
      (∑ β : Fin 1 → Fin (Module.finrank ℝ E),
          eLpNorm
            (Sobolev.Euclidean.iterWeakPartial
              (d := Module.finrank ℝ E) q 1 β f Ω) q (volume.restrict Ω)) =
        ∑ i : Fin (Module.finrank ℝ E),
          eLpNorm
            (Sobolev.Euclidean.chosenWeakPartialOrZero q i f Ω)
            q (volume.restrict Ω) := by
    have h_unfold : ∀ β : Fin 1 → Fin (Module.finrank ℝ E),
        eLpNorm
          (Sobolev.Euclidean.iterWeakPartial
            (d := Module.finrank ℝ E) q 1 β f Ω) q (volume.restrict Ω) =
          eLpNorm
            (Sobolev.Euclidean.chosenWeakPartialOrZero q (β 0) f Ω)
            q (volume.restrict Ω) := by
      intro β
      have hit :
          Sobolev.Euclidean.iterWeakPartial
              (d := Module.finrank ℝ E) q 1 β f Ω =
            Sobolev.Euclidean.chosenWeakPartialOrZero q (β 0) f Ω := by
        rw [Sobolev.Euclidean.iterWeakPartial_succ]
        simp [Sobolev.Euclidean.iterWeakPartial_zero]
      rw [hit]
    rw [Finset.sum_congr rfl (fun β _ => h_unfold β)]
    let e : (Fin 1 → Fin (Module.finrank ℝ E)) ≃ Fin (Module.finrank ℝ E) :=
      { toFun := fun β => β 0
        invFun := fun i _ => i
        left_inv := fun β => by
          funext j
          have hj : j = 0 := Subsingleton.elim _ _
          rw [hj]
        right_inv := fun _ => rfl }
    exact Fintype.sum_equiv e
      (fun β =>
        eLpNorm
          (Sobolev.Euclidean.chosenWeakPartialOrZero q (β 0) f Ω)
          q (volume.restrict Ω))
      (fun i =>
        eLpNorm
          (Sobolev.Euclidean.chosenWeakPartialOrZero q i f Ω)
          q (volume.restrict Ω))
      (fun _ => rfl)
  have h_le_wkp :
      (∑ i : Fin (Module.finrank ℝ E),
          eLpNorm
            (Sobolev.Euclidean.chosenWeakPartialOrZero q i f Ω)
            q (volume.restrict Ω)) ≤
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 q f Ω := by
    rw [hWkpEq, Finset.sum_range_succ, Finset.sum_range_one, ← h_j1_term]
    refine le_add_of_nonneg_left ?_
    exact zero_le
  refine h_le_wkp.trans ?_
  have hd_pos : 0 < Module.finrank ℝ E := NeZero.pos _
  have hd_one_le : (1 : ℝ≥0∞) ≤ ((Module.finrank ℝ E : ℕ) : ℝ≥0∞) := by
    exact_mod_cast hd_pos
  conv_lhs => rw [show Sobolev.Euclidean.iteratedWeakSobolevNorm
    (d := Module.finrank ℝ E) 1 q f Ω = 1 *
    Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) 1 q f Ω from
    (one_mul _).symm]
  gcongr

private lemma eLpNorm_norm_fderiv_chartSmoothExt_target_le_wkpNormChart
    [NeZero (Module.finrank ℝ E)]
    (α : M) {q : ℝ≥0∞} (hq_one : 1 ≤ q) {u : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    eLpNorm (fun z : EuclN => ‖fderiv ℝ (chartSmoothExt (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x)) z‖) q
      (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) ≤
      ((Module.finrank ℝ E : ℕ) : ℝ≥0∞) *
        Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 q
          (chartSmoothExt (I := I) (M := M) α
            (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) x * u x))
          (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set f : EuclN → ℝ := chartSmoothExt (I := I) (M := M) α
    (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) x * u x) with hf_def
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hf_smooth : ContDiff ℝ ∞ f := by
    rw [hf_def]
    exact contDiff_chartSmoothExt_pou_mul (I := I) (M := M) α
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M)
      (CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M) hu
  have hf_smooth_top : ContDiff ℝ (⊤ : ℕ∞) f := hf_smooth
  have hf_compact : HasCompactSupport f := by
    rw [hf_def]
    exact hasCompactSupport_chartSmoothExt_pou_mul (I := I) (M := M) α
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M)
      (CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M) u
  have hf_support : tsupport f ⊆ Ω := by
    rw [hf_def, hΩ_def]
    have h1 : tsupport (chartSmoothExt (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x)) ⊆ chartCarrier (I := I) (M := M) α :=
      tsupport_chartSmoothExt_pou_mul_subset_chartCarrier (I := I) (M := M) α u
    exact h1.trans (chartCarrier_subset_chartTargetEuclid (I := I) (M := M) α)
  exact eLpNorm_norm_fderiv_le_d_mul_wkpNorm hq_one hΩ_open hf_smooth_top hf_compact hf_support

private lemma wkpNorm_chartSmoothExt_target_eq_wkpNorm_chartPushed_target
    {q : ℝ≥0∞} (hq_one : 1 ≤ q) (α : M) (u : M → ℝ) :
    Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 q
        (chartSmoothExt (I := I) (M := M) α
          (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x))
        (chartTargetEuclid (I := I) (M := M) α) =
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 q
        (chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
        (chartTargetEuclid (I := I) (M := M) α) :=
  Sobolev.Euclidean.wkpNorm_congr_ae
    (d := Module.finrank ℝ E) hq_one
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (chartSmoothExt_ae_eq_chartPushed (I := I) (M := M) α u)

omit [I.Boundaryless] in
private lemma wkpNorm_chartPushed_target_le_wkpNormChart
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {q : ℝ≥0∞} (α : M) (u : M → ℝ) :
    Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 q
        (chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
        (chartTargetEuclid (I := I) (M := M) α) ≤
      wkpNormChart (I := I) (M := M) 1 q u := by
  classical
  let _ := g
  unfold wkpNormChart
  exact ENNReal.le_tsum α

private lemma eLpNorm_norm_fderiv_chartSmoothExt_ball_le_wkpNormChart
    [NeZero (Module.finrank ℝ E)]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    (α : M) {q : ℝ≥0∞} (hq_one : 1 ≤ q) {u : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    eLpNorm (fun z : EuclN => ‖fderiv ℝ (chartSmoothExt (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x)) z‖) q
      (volume.restrict (Metric.ball (0 : EuclN) (chartRadius (I := I) (M := M) α))) ≤
      ((Module.finrank ℝ E : ℕ) : ℝ≥0∞) *
        wkpNormChart (I := I) (M := M) 1 q u := by
  classical
  rw [eLpNorm_norm_fderiv_chartSmoothExt_pou_mul_restrict_ball_eq_restrict_target
    (I := I) (M := M) α u q]
  refine (eLpNorm_norm_fderiv_chartSmoothExt_target_le_wkpNormChart
    (I := I) (M := M) α hq_one hu).trans ?_
  rw [wkpNorm_chartSmoothExt_target_eq_wkpNorm_chartPushed_target
    (I := I) (M := M) hq_one α u]
  gcongr
  exact wkpNorm_chartPushed_target_le_wkpNormChart (I := I) (M := M) g α u

private lemma per_chart_smooth_sup_bound
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {p : ℝ} (hp : (Module.finrank ℝ E : ℝ) < p)
    [NeZero (Module.finrank ℝ E)] (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
        ∀ y : EuclN, ‖chartSmoothExt (I := I) (M := M) α
          (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x) y‖ ≤ C *
          (wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p) u).toReal := by
  classical
  have hp_pos : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg _) hp
  have hp_one : 1 ≤ p := by
    have hd_pos : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by
      exact_mod_cast NeZero.pos (Module.finrank ℝ E)
    have hd_one_le : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
      have : 1 ≤ Module.finrank ℝ E := NeZero.one_le
      exact_mod_cast this
    linarith
  have hp_enn_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal hp_one
  obtain ⟨Cmorrey, hCmorrey_nn, hbound⟩ :=
    chartSmoothExt_morrey_sup_uniform (I := I) (M := M) α hp
  set d : ℕ := Module.finrank ℝ E
  refine ⟨Cmorrey * (1 + (d : ℝ)), ?_, ?_⟩
  · have hd_nn : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
    positivity
  · intro u hu y
    have hbound_y := hbound hu y
    set f : EuclN → ℝ := chartSmoothExt (I := I) (M := M) α
      (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x) with hf_def
    have hLp_bd := eLpNorm_chartSmoothExt_ball_le_wkpNormChart
      (I := I) (M := M) α u (ENNReal.ofReal p)
    have hgrad_bd := eLpNorm_norm_fderiv_chartSmoothExt_ball_le_wkpNormChart
      (I := I) (M := M) g α hp_enn_one hu
    have hwkp_lt_top : wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p) u < ⊤ :=
      wkpNormChart_lt_top_of_memWkpChart (I := I) (M := M) hp_enn_one
        (Sobolev.Equivalence.MemWkpChart_of_contMDiff
          (I := I) (M := M) hp_enn_one hu)
    have hwkp_ne_top : wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p) u ≠ ⊤ :=
      hwkp_lt_top.ne
    set N : ℝ := (wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p) u).toReal with hN_def
    have hN_nn : 0 ≤ N := ENNReal.toReal_nonneg
    have hLp_real : (eLpNorm f (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuclN) (chartRadius (I := I) (M := M) α)))).toReal
        ≤ N := by
      apply ENNReal.toReal_mono hwkp_ne_top
      exact hLp_bd
    have hgrad_real : (eLpNorm (fun z : EuclN => ‖fderiv ℝ f z‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuclN) (chartRadius (I := I) (M := M) α)))).toReal
        ≤ (d : ℝ) * N := by
      have h_ne_top : ((d : ℕ) : ℝ≥0∞) *
          wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p) u ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hwkp_ne_top
      have h_le := ENNReal.toReal_mono h_ne_top hgrad_bd
      rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h_le
    have h_combined : (eLpNorm f (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuclN) (chartRadius (I := I) (M := M) α)))).toReal +
      (eLpNorm (fun z : EuclN => ‖fderiv ℝ f z‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuclN) (chartRadius (I := I) (M := M) α)))).toReal ≤
      N + (d : ℝ) * N := by
      linarith
    have h_final : Cmorrey * ((eLpNorm f (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuclN) (chartRadius (I := I) (M := M) α)))).toReal +
      (eLpNorm (fun z : EuclN => ‖fderiv ℝ f z‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuclN) (chartRadius (I := I) (M := M) α)))).toReal) ≤
      Cmorrey * (1 + (d : ℝ)) * N := by
      have h1 : Cmorrey * (N + (d : ℝ) * N) = Cmorrey * (1 + (d : ℝ)) * N := by ring
      calc Cmorrey * ((eLpNorm f (ENNReal.ofReal p)
          (volume.restrict (Metric.ball (0 : EuclN) (chartRadius (I := I) (M := M) α)))).toReal +
        (eLpNorm (fun z : EuclN => ‖fderiv ℝ f z‖) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball (0 : EuclN) (chartRadius (I := I) (M := M) α)))).toReal)
          ≤ Cmorrey * (N + (d : ℝ) * N) :=
            mul_le_mul_of_nonneg_left h_combined hCmorrey_nn
        _ = Cmorrey * (1 + (d : ℝ)) * N := h1
    rw [hf_def] at h_final
    exact le_trans hbound_y h_final

omit [I.Boundaryless] in
private lemma chartSmoothExt_pou_mul_apply_at_chart_image
    (α : M) (u : M → ℝ) {x : M} (hx : x ∈ (chartAt H α).source) :
    chartSmoothExt (I := I) (M := M) α
        (fun y : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) y * u y)
        ((toEuclidean : E ≃L[ℝ] EuclN) (extChartAt I α x)) =
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x := by
  classical
  have hx_target : extChartAt I α x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source (by
      rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)]
      exact hx)
  have h_symm_eq : (toEuclidean (E := E)).symm
      ((toEuclidean : E ≃L[ℝ] EuclN) (extChartAt I α x)) = extChartAt I α x :=
    (toEuclidean (E := E)).symm_apply_apply _
  have hsub : (toEuclidean (E := E)).symm
      ((toEuclidean : E ≃L[ℝ] EuclN) (extChartAt I α x)) ∈ (extChartAt I α).target := by
    rw [h_symm_eq]; exact hx_target
  rw [chartSmoothExt_apply_of_mem_target (I := I) (M := M) α _ hsub]
  rw [h_symm_eq]
  rw [(extChartAt I α).left_inv (by
    rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
      (I := I) (M := M)]
    exact hx)]

omit [I.Boundaryless] in
private lemma norm_pou_mul_le_norm_chartSmoothExt_at_some_point
    (α : M) (u : M → ℝ) (x : M) {Cmod : ℝ}
    (hbound : ∀ y : EuclN, ‖chartSmoothExt (I := I) (M := M) α
      (fun z : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) z * u z) y‖ ≤ Cmod) (hCmod : 0 ≤ Cmod) :
    ‖(CalabiYau.RiemannianVolume.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) x * u x‖ ≤ Cmod := by
  classical
  by_cases hx : x ∈ (chartAt H α).source
  · have h_eq := chartSmoothExt_pou_mul_apply_at_chart_image (I := I) (M := M) α u hx
    rw [← h_eq]
    exact hbound _
  · have hρ_zero : (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x = 0 := by
      have hsubord :
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M).IsSubordinate
            (fun α : M => (chartAt H α).source) :=
        CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M
      have h_support := hsubord α
      by_contra hne
      apply hx
      apply h_support
      apply subset_tsupport
      exact Function.mem_support.mpr hne
    rw [hρ_zero, zero_mul, norm_zero]
    exact hCmod

private noncomputable def perChartMorreyConst
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {p : ℝ} (hp : (Module.finrank ℝ E : ℝ) < p)
    [NeZero (Module.finrank ℝ E)] (α : M) : ℝ :=
  Classical.choose (per_chart_smooth_sup_bound (I := I) (M := M) g hp α)

private lemma perChartMorreyConst_nn
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {p : ℝ} (hp : (Module.finrank ℝ E : ℝ) < p)
    [NeZero (Module.finrank ℝ E)] (α : M) :
    0 ≤ perChartMorreyConst (I := I) (M := M) g hp α :=
  (Classical.choose_spec
    (per_chart_smooth_sup_bound (I := I) (M := M) g hp α)).1

private lemma perChartMorreyConst_bound
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {p : ℝ} (hp : (Module.finrank ℝ E : ℝ) < p)
    [NeZero (Module.finrank ℝ E)] (α : M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (y : EuclN) :
    ‖chartSmoothExt (I := I) (M := M) α
        (fun z : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) z * u z) y‖ ≤
      perChartMorreyConst (I := I) (M := M) g hp α *
        (wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p) u).toReal :=
  (Classical.choose_spec
    (per_chart_smooth_sup_bound (I := I) (M := M) g hp α)).2 hu y

theorem smooth_manifold_morrey_sup_bound_uniform
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {p : ℝ} (hp : (Module.finrank ℝ E : ℝ) < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
        ∀ x : M, ‖u x‖ ≤ C *
          (wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p) u).toReal := by
  classical
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  let : MeasurableSpace M := borel M
  have : BorelSpace M := ⟨rfl⟩
  set S : Finset M :=
    CalabiYau.RiemannianVolume.chartAtlasPOUFinset (I := I) (M := M)
    with hS_def
  refine ⟨∑ α ∈ S, perChartMorreyConst (I := I) (M := M) g hp α, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun α _ =>
      perChartMorreyConst_nn (I := I) (M := M) g hp α)
  intro u hu x
  have h_decomp : u x = ∑ α ∈ S,
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M α : M → ℝ) x * u x := by
    have hsum : ∑ α ∈ S,
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M α : M → ℝ) x = 1 :=
      Sobolev.Chart.chartAtlasPOU_finset_sum_eq_one
        (I := I) (M := M) x
    rw [← Finset.sum_mul, hsum, one_mul]
  rw [h_decomp]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro α _
  have hC_α_nn : 0 ≤ perChartMorreyConst (I := I) (M := M) g hp α :=
    perChartMorreyConst_nn (I := I) (M := M) g hp α
  have hCN_nn : 0 ≤ perChartMorreyConst (I := I) (M := M) g hp α *
      (wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p) u).toReal :=
    mul_nonneg hC_α_nn ENNReal.toReal_nonneg
  refine norm_pou_mul_le_norm_chartSmoothExt_at_some_point
    (I := I) (M := M) α u x ?_ hCN_nn
  intro y
  exact perChartMorreyConst_bound (I := I) (M := M) g hp α hu y

omit [I.Boundaryless] in
private lemma eLpNorm_riemannianMeasure_le_const_mul_wkpNormChart
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, Measurable u →
        eLpNorm u p
            (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M)) ≤
          ENNReal.ofReal C * wkpNormChart (I := I) (M := M) 1 p u := by
  classical
  set S : Finset M :=
    CalabiYau.RiemannianVolume.chartAtlasPOUFinset (I := I) (M := M)
    with hS_def
  set ρ := CalabiYau.RiemannianVolume.chartAtlasPOU I M with hρ_def
  have h_bridge_α : ∀ α : M, ∃ C_α : ℝ, 0 < C_α ∧
      ∀ {u : M → ℝ}, Measurable u → tsupport u ⊆ tsupport (ρ α : M → ℝ) →
        eLpNorm u p
            (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g ρ)
          ≤ ENNReal.ofReal C_α *
              eLpNorm (chartPushedRaw I α u) p
                ((volume : Measure EuclN).restrict
                  (chartTargetEuclid (I := I) (M := M) α)) := by
    intro α
    set Kα : Set M := tsupport (ρ α : M → ℝ) with hKα_def
    have hKα_compact : IsCompact Kα := (isClosed_tsupport _).isCompact
    have hKα_sub : Kα ⊆ (chartAt H α).source :=
      CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M α
    obtain ⟨C_α, hC_α_pos, hbound⟩ :=
      eLpNorm_riemannianMeasure_le_const_mul_eLpNorm_chartPushedRaw_uniform_of_subset
        (I := I) (M := M) g α hKα_compact hKα_sub hp_one hp_top
    exact ⟨C_α, hC_α_pos, hbound⟩
  set Cα : M → ℝ := fun α => Classical.choose (h_bridge_α α) with hCα_def
  have hCα_pos : ∀ α : M, 0 < Cα α := fun α => (Classical.choose_spec (h_bridge_α α)).1
  have hCα_bound : ∀ α : M, ∀ {u : M → ℝ}, Measurable u →
      tsupport u ⊆ tsupport (ρ α : M → ℝ) →
      eLpNorm u p
          (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g ρ)
        ≤ ENNReal.ofReal (Cα α) *
            eLpNorm (chartPushedRaw I α u) p
              ((volume : Measure EuclN).restrict
                (chartTargetEuclid (I := I) (M := M) α)) := fun α =>
    (Classical.choose_spec (h_bridge_α α)).2
  refine ⟨∑ α ∈ S, Cα α, Finset.sum_nonneg (fun α _ => (hCα_pos α).le), ?_⟩
  intro u hu_meas
  have h_eLpNorm_eq :
      eLpNorm u p (CalabiYau.RiemannianVolume.riemannianMeasure
          (I := I) g ρ) =
        eLpNorm (∑ α ∈ S, fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) p
          (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g ρ) := by
    refine eLpNorm_congr_ae ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Finset.sum_apply]
    change u x = ∑ α ∈ S, (ρ α : M → ℝ) x * u x
    have hsum : ∑ α ∈ S, (ρ α : M → ℝ) x = 1 :=
      Sobolev.Chart.chartAtlasPOU_finset_sum_eq_one
        (I := I) (M := M) x
    rw [← Finset.sum_mul, hsum, one_mul]
  rw [h_eLpNorm_eq]
  have h_aesm : ∀ α ∈ S,
      AEStronglyMeasurable (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x)
        (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g ρ) := by
    intro α _
    have hcont : Continuous (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x) :=
      (ρ α).contMDiff.continuous
    exact (hcont.measurable.mul hu_meas).aestronglyMeasurable
  refine (eLpNorm_sum_le h_aesm hp_one).trans ?_
  have h_per_α : ∀ α ∈ S,
      eLpNorm (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) p
        (CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g ρ) ≤
      ENNReal.ofReal (Cα α) * wkpNormChart (I := I) (M := M) 1 p u := by
    intro α _
    have h_support : tsupport (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) ⊆
        tsupport (ρ α : M → ℝ) := by
      have h_eq : (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) =
          (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x • u x) := by funext x; rfl
      rw [h_eq]
      exact tsupport_smul_subset_left
        (f := fun x : M => ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) (g := u)
    have h_meas : Measurable (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) :=
      (ρ α).contMDiff.continuous.measurable.mul hu_meas
    have h_bridge := hCα_bound α h_meas h_support
    refine h_bridge.trans ?_
    have h_ae := chartPushed_eq_chartPushedRaw_pou_ae (I := I) (M := M) ρ α u
    have h_eLpNorm_eq :
        eLpNorm (chartPushedRaw I α (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x)) p
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) =
          eLpNorm (chartPushed (I := I) (M := M) ρ α u) p
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) :=
      eLpNorm_congr_ae h_ae.symm
    rw [h_eLpNorm_eq]
    have h1 := eLpNorm_chartPushed_p_le_wkpNorm_one (I := I) (M := M) (p := p) u α
    gcongr
  refine (Finset.sum_le_sum h_per_α).trans ?_
  rw [← Finset.sum_mul]
  gcongr
  rw [show (∑ α ∈ S, ENNReal.ofReal (Cα α)) = ENNReal.ofReal (∑ α ∈ S, Cα α) from ?_]
  refine (ENNReal.ofReal_sum_of_nonneg (fun α _ => (hCα_pos α).le)).symm

theorem morrey_C0_embedding_of_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {p : ℝ} (hp : (Module.finrank ℝ E : ℝ) < p)
    {u : M → ℝ} (hu_meas : Measurable u)
    (hu : MemWkpChart (I := I) (M := M) 1 (ENNReal.ofReal p) u) :
    ∃ (ũ : M → ℝ) (C : ℝ),
      Continuous ũ ∧ 0 ≤ C ∧
      (∀ᵐ x ∂(CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M)),
        ũ x = u x) ∧
      (∀ x : M, ‖ũ x‖ ≤ C *
        (wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p) u).toReal) := by
  classical
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  let : MeasurableSpace M := borel M
  have : BorelSpace M := ⟨rfl⟩
  have hp_pos : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg _) hp
  have hp_one : 1 ≤ p := by
    have hd_one_le : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
      have : 1 ≤ Module.finrank ℝ E := NeZero.one_le
      exact_mod_cast this
    linarith
  have hp_enn_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal hp_one
  have hp_enn_top : ENNReal.ofReal p ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have hp_enn_ne_zero : ENNReal.ofReal p ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hp_pos
  obtain ⟨Cmorrey, hCmorrey_nn, hMorrey_bd⟩ :=
    smooth_manifold_morrey_sup_bound_uniform (I := I) (M := M) g hp
  have h_pick : ∀ n : ℕ, ∃ v : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ v ∧
      wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p) (fun x => u x - v x) ≤
        ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
    intro n
    have h_eps_pos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by
      apply div_pos one_pos
      exact_mod_cast Nat.succ_pos n
    exact contMDiff_dense_in_WkpChart (I := I) (M := M) hp_enn_one hp_enn_top hu h_eps_pos
  set v : ℕ → M → ℝ := fun n => (h_pick n).choose with hv_def
  have hv_smooth : ∀ n, ContMDiff I 𝓘(ℝ, ℝ) ∞ (v n) := fun n => (h_pick n).choose_spec.1
  have hv_close : ∀ n,
      wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p) (fun x => u x - v n x) ≤
        ENNReal.ofReal (1 / (n + 1 : ℝ)) := fun n => (h_pick n).choose_spec.2
  have hv_mem : ∀ n, MemWkpChart (I := I) (M := M) 1 (ENNReal.ofReal p) (v n) := fun n =>
    Sobolev.Equivalence.MemWkpChart_of_contMDiff
      (I := I) (M := M) hp_enn_one (hv_smooth n)
  have h_diff_smooth : ∀ n m, ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => v n x - v m x) :=
    fun n m => (hv_smooth n).sub (hv_smooth m)
  have h_pair_sup : ∀ n m (x : M), ‖v n x - v m x‖ ≤
      Cmorrey * (wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p)
        (fun y => v n y - v m y)).toReal := by
    intro n m x
    exact hMorrey_bd (h_diff_smooth n m) x
  have h_wkp_diff_bound : ∀ n m,
      wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p)
          (fun x => v n x - v m x) ≤
        ENNReal.ofReal (1 / (n + 1 : ℝ)) + ENNReal.ofReal (1 / (m + 1 : ℝ)) := by
    intro n m
    have h_decomp : (fun x : M => v n x - v m x) =
        fun x : M => (u x - v m x) + (-(u x - v n x)) := by
      funext x; ring
    rw [h_decomp]
    have h_diff_n_mem : MemWkpChart (I := I) (M := M) 1 (ENNReal.ofReal p)
        (fun x => -(u x - v n x)) :=
      MemWkpChart_neg (I := I) (M := M) hp_enn_one
        (MemWkpChart_sub (I := I) (M := M) hp_enn_one hu (hv_mem n))
    have h_diff_m_mem : MemWkpChart (I := I) (M := M) 1 (ENNReal.ofReal p)
        (fun x => u x - v m x) :=
      MemWkpChart_sub (I := I) (M := M) hp_enn_one hu (hv_mem m)
    have h_tri := wkpNormChart_add_le (I := I) (M := M) hp_enn_one h_diff_m_mem h_diff_n_mem
    refine h_tri.trans ?_
    have h_neg_eq :
        wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p)
          (fun x => -(u x - v n x)) =
        wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p) (fun x => u x - v n x) := by
      have h := wkpNormChart_const_smul (I := I) (M := M) hp_enn_one (-1)
        (MemWkpChart_sub (I := I) (M := M) hp_enn_one hu (hv_mem n))
      have h_eq : (fun x : M => -1 * (u x - v n x)) = (fun x => -(u x - v n x)) := by
        funext x; ring
      rw [h_eq] at h
      rw [h]
      simp
    rw [h_neg_eq]
    rw [add_comm]
    exact add_le_add (hv_close n) (hv_close m)
  have h_decay_to_zero : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (n + 1 : ℝ)))
      atTop (nhds 0) := by
    have hReal : Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (nhds 0) := by
      have h1 : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop := by
        have h2 : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
          tendsto_natCast_atTop_atTop
        exact h2.atTop_add tendsto_const_nhds
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).div_atTop h1
    simpa [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hReal
  have h_pair_real : ∀ n m (x : M), ‖v n x - v m x‖ ≤
      Cmorrey * ((1 / (n + 1 : ℝ)) + (1 / (m + 1 : ℝ))) := by
    intro n m x
    refine (h_pair_sup n m x).trans ?_
    apply mul_le_mul_of_nonneg_left _ hCmorrey_nn
    have h_bd := h_wkp_diff_bound n m
    have h_ne_top : ENNReal.ofReal (1 / (n + 1 : ℝ)) +
        ENNReal.ofReal (1 / (m + 1 : ℝ)) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
    have h_le := ENNReal.toReal_mono h_ne_top h_bd
    have h_sum_eq : (ENNReal.ofReal (1 / (n + 1 : ℝ)) +
        ENNReal.ofReal (1 / (m + 1 : ℝ))).toReal = 1 / (n + 1 : ℝ) + 1 / (m + 1 : ℝ) := by
      rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]
      rw [ENNReal.toReal_ofReal (by positivity)]
      rw [ENNReal.toReal_ofReal (by positivity)]
    rw [h_sum_eq] at h_le
    exact h_le
  have h_uniform_cauchy : UniformCauchySeqOn v atTop Set.univ := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    by_cases hCm_zero : Cmorrey = 0
    · refine ⟨0, ?_⟩
      intro n _ m _ x _
      have := h_pair_real n m x
      rw [hCm_zero, zero_mul] at this
      have hpos : 0 < ε := hε
      have hineq : dist (v n x) (v m x) = ‖v n x - v m x‖ := by
        rw [dist_eq_norm]
      rw [hineq]
      linarith
    · have hCm_pos : 0 < Cmorrey := lt_of_le_of_ne hCmorrey_nn (Ne.symm hCm_zero)
      have hε' : 0 < ε / (2 * Cmorrey) := by positivity
      obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, (1 / (n + 1 : ℝ)) < ε / (2 * Cmorrey) := by
        have hReal : Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (nhds 0) := by
          have h1 : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop := by
            have h2 : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
              tendsto_natCast_atTop_atTop
            exact h2.atTop_add tendsto_const_nhds
          simpa using (tendsto_const_nhds (x := (1 : ℝ))).div_atTop h1
        rw [Metric.tendsto_atTop] at hReal
        obtain ⟨N, hN⟩ := hReal _ hε'
        refine ⟨N, ?_⟩
        intro n hn
        have h := hN n hn
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h
        exact h
      refine ⟨N, ?_⟩
      intro n hn m hm x _
      have h_n_lt : (1 / (n + 1 : ℝ)) < ε / (2 * Cmorrey) := hN n hn
      have h_m_lt : (1 / (m + 1 : ℝ)) < ε / (2 * Cmorrey) := hN m hm
      have h_sum_lt : (1 / (n + 1 : ℝ)) + (1 / (m + 1 : ℝ)) < ε / Cmorrey := by
        have : ε / Cmorrey = ε / (2 * Cmorrey) + ε / (2 * Cmorrey) := by
          field_simp; ring
        rw [this]
        linarith
      have h_dist : dist (v n x) (v m x) = ‖v n x - v m x‖ := by rw [dist_eq_norm]
      rw [h_dist]
      have h_bd := h_pair_real n m x
      have h_step : Cmorrey * ((1 / (n + 1 : ℝ)) + (1 / (m + 1 : ℝ))) < Cmorrey * (ε / Cmorrey) :=
        mul_lt_mul_of_pos_left h_sum_lt hCm_pos
      have h_simp : Cmorrey * (ε / Cmorrey) = ε := by
        field_simp
      linarith
  have h_pw_cauchy : ∀ x : M, CauchySeq (fun n => v n x) := by
    intro x
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have h_uc := h_uniform_cauchy
    rw [Metric.uniformCauchySeqOn_iff] at h_uc
    obtain ⟨N, hN⟩ := h_uc ε hε
    refine ⟨N, ?_⟩
    intro n hn m hm
    exact hN n hn m hm x (Set.mem_univ _)
  have h_pw_limit : ∀ x : M, ∃ y : ℝ, Tendsto (fun n => v n x) atTop (nhds y) :=
    fun x => cauchySeq_tendsto_of_complete (h_pw_cauchy x)
  set ũ : M → ℝ := fun x => Classical.choose (h_pw_limit x) with hũ_def
  have hũ_tendsto : ∀ x : M, Tendsto (fun n => v n x) atTop (nhds (ũ x)) :=
    fun x => Classical.choose_spec (h_pw_limit x)
  have h_uniform_tendsto : TendstoUniformlyOn v ũ atTop Set.univ :=
    h_uniform_cauchy.tendstoUniformlyOn_of_tendsto (fun x _ => hũ_tendsto x)
  have h_uniform_tendsto' : TendstoUniformly v ũ atTop := by
    rw [show (TendstoUniformly v ũ atTop) ↔ TendstoUniformlyOn v ũ atTop Set.univ from
      tendstoUniformlyOn_univ.symm]
    exact h_uniform_tendsto
  have hũ_cont : Continuous ũ := by
    refine h_uniform_tendsto'.continuous ?_
    exact Filter.Eventually.frequently (Filter.Eventually.of_forall
      (fun n => (hv_smooth n).continuous))
  set μ_g : Measure M :=
    CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M) with hμ_g_def
  have hμ_g_finite : IsFiniteMeasure μ_g := by
    rw [hμ_g_def]
    exact CalabiYau.RiemannianVolume.riemannianMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g _
      (CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M)
  obtain ⟨Cbridge, hCbridge_nn, hbridge⟩ :=
    eLpNorm_riemannianMeasure_le_const_mul_wkpNormChart (I := I) (M := M) g hp_enn_one hp_enn_top
  have h_meas_diff : ∀ n : ℕ, Measurable (fun x : M => u x - v n x) := by
    intro n
    exact hu_meas.sub (hv_smooth n).continuous.measurable
  have h_v_to_u_Lp : Tendsto (fun n => eLpNorm (fun x => u x - v n x) (ENNReal.ofReal p) μ_g)
      atTop (nhds 0) := by
    have h_C_decay : Tendsto (fun n : ℕ => ENNReal.ofReal Cbridge *
        ENNReal.ofReal (1 / (n + 1 : ℝ))) atTop (nhds 0) := by
      have h1 : Tendsto (fun n : ℕ => ENNReal.ofReal Cbridge * ENNReal.ofReal (1 / (n + 1 : ℝ)))
          atTop (nhds (ENNReal.ofReal Cbridge * 0)) := by
        refine ENNReal.Tendsto.const_mul h_decay_to_zero ?_
        exact Or.inr ENNReal.ofReal_ne_top
      simpa using h1
    have h_total_le : ∀ n,
        eLpNorm (fun x : M => u x - v n x) (ENNReal.ofReal p) μ_g ≤
          ENNReal.ofReal Cbridge * ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
      intro n
      refine (hbridge (h_meas_diff n)).trans ?_
      gcongr
      exact hv_close n
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_C_decay
      (Filter.Eventually.of_forall (fun _ => zero_le))
      (Filter.Eventually.of_forall h_total_le)
  have hu_aesm : AEStronglyMeasurable u μ_g := hu_meas.aestronglyMeasurable
  have hv_aesm : ∀ n, AEStronglyMeasurable (v n) μ_g :=
    fun n => (hv_smooth n).continuous.aestronglyMeasurable
  have h_tim : TendstoInMeasure μ_g v atTop u := by
    refine tendstoInMeasure_of_tendsto_eLpNorm hp_enn_ne_zero hv_aesm hu_aesm ?_
    have h_neg_eq : ∀ n,
        eLpNorm (fun x : M => v n x - u x) (ENNReal.ofReal p) μ_g =
          eLpNorm (fun x : M => u x - v n x) (ENNReal.ofReal p) μ_g := by
      intro n
      have h_eq : (fun x : M => v n x - u x) = (fun x : M => -(u x - v n x)) := by
        funext x; ring
      rw [h_eq]
      have h_neg_apply : (fun x : M => -(u x - v n x)) = -(fun x : M => u x - v n x) := by
        funext x; rfl
      rw [h_neg_apply, eLpNorm_neg]
    refine (Filter.tendsto_congr h_neg_eq).mpr h_v_to_u_Lp
  obtain ⟨φ, hφ_mono, hφ_ae⟩ := h_tim.exists_seq_tendsto_ae
  have h_subseq_to_ũ : ∀ x : M, Tendsto (fun n => v (φ n) x) atTop (nhds (ũ x)) :=
    fun x => (hũ_tendsto x).comp hφ_mono.tendsto_atTop
  have h_ae_eq : ∀ᵐ x ∂μ_g, ũ x = u x := by
    filter_upwards [hφ_ae] with x hx
    exact tendsto_nhds_unique (h_subseq_to_ũ x) hx
  have hwkp_u_ne_top : wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p) u ≠ ⊤ :=
    (wkpNormChart_lt_top_of_memWkpChart (I := I) (M := M) hp_enn_one hu).ne
  set Nu : ℝ := (wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p) u).toReal with hNu_def
  have hNu_nn : 0 ≤ Nu := ENNReal.toReal_nonneg
  have h_wkp_vn_bound : ∀ n,
      wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p) (v n) ≤
        wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p) u +
          ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
    intro n
    have h_decomp : v n = fun x => u x + (v n x - u x) := by funext x; ring
    have h_diff_n_mem : MemWkpChart (I := I) (M := M) 1 (ENNReal.ofReal p)
        (fun x => v n x - u x) := by
      have hneg : MemWkpChart (I := I) (M := M) 1 (ENNReal.ofReal p)
          (fun x => -(u x - v n x)) :=
        MemWkpChart_neg (I := I) (M := M) hp_enn_one
          (MemWkpChart_sub (I := I) (M := M) hp_enn_one hu (hv_mem n))
      have h_eq : (fun x : M => -(u x - v n x)) = (fun x : M => v n x - u x) := by
        funext x; ring
      rw [h_eq] at hneg
      exact hneg
    rw [h_decomp]
    have h_tri := wkpNormChart_add_le (I := I) (M := M) hp_enn_one hu h_diff_n_mem
    refine h_tri.trans ?_
    have h_neg_eq : wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p)
        (fun x => v n x - u x) =
          wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p)
            (fun x => u x - v n x) := by
      have h := wkpNormChart_const_smul (I := I) (M := M) hp_enn_one (-1)
        (MemWkpChart_sub (I := I) (M := M) hp_enn_one hu (hv_mem n))
      have h_eq1 : (fun x : M => -1 * (u x - v n x)) = (fun x => -(u x - v n x)) := by
        funext x; ring
      have h_eq2 : (fun x : M => -(u x - v n x)) = (fun x => v n x - u x) := by
        funext x; ring
      rw [h_eq1] at h
      have h_smul := h
      rw [h_eq2] at h_smul
      have h' := wkpNormChart_const_smul (I := I) (M := M) hp_enn_one (-1) hu
      have h_eq3 : (fun x : M => -1 * u x) = -u := by funext x; rw [neg_one_mul]; rfl
      rw [h_smul]; simp
    rw [h_neg_eq]
    gcongr
    exact hv_close n
  have h_wkp_vn_real : ∀ n,
      (wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p) (v n)).toReal ≤
        Nu + 1 / (n + 1 : ℝ) := by
    intro n
    have h_bd := h_wkp_vn_bound n
    have h_ne_top : wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p) u +
        ENNReal.ofReal (1 / (n + 1 : ℝ)) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨hwkp_u_ne_top, ENNReal.ofReal_ne_top⟩
    have h_le := ENNReal.toReal_mono h_ne_top h_bd
    rw [ENNReal.toReal_add hwkp_u_ne_top ENNReal.ofReal_ne_top] at h_le
    rw [ENNReal.toReal_ofReal (by positivity)] at h_le
    rw [hNu_def]
    exact h_le
  refine ⟨ũ, Cmorrey, hũ_cont, hCmorrey_nn, h_ae_eq, ?_⟩
  intro x
  have h_v_bound : ∀ n, ‖v n x‖ ≤ Cmorrey * (Nu + 1 / (n + 1 : ℝ)) := by
    intro n
    have h := hMorrey_bd (hv_smooth n) x
    refine h.trans ?_
    apply mul_le_mul_of_nonneg_left _ hCmorrey_nn
    exact h_wkp_vn_real n
  have h_norm_tendsto : Tendsto (fun n => ‖v n x‖) atTop (nhds (‖ũ x‖)) :=
    (continuous_norm.tendsto _).comp (hũ_tendsto x)
  have h_rhs_tendsto : Tendsto (fun n : ℕ => Cmorrey * (Nu + 1 / (n + 1 : ℝ)))
      atTop (nhds (Cmorrey * Nu)) := by
    have h1 : Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (nhds 0) := by
      have h2 : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop := by
        have h3 : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
          tendsto_natCast_atTop_atTop
        exact h3.atTop_add tendsto_const_nhds
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).div_atTop h2
    have h2 : Tendsto (fun n : ℕ => Nu + 1 / (n + 1 : ℝ)) atTop (nhds (Nu + 0)) :=
      tendsto_const_nhds.add h1
    have h3 : Tendsto (fun n : ℕ => Cmorrey * (Nu + 1 / (n + 1 : ℝ)))
        atTop (nhds (Cmorrey * (Nu + 0))) :=
      tendsto_const_nhds.mul h2
    simpa using h3
  exact le_of_tendsto_of_tendsto' h_norm_tendsto h_rhs_tendsto h_v_bound

private lemma chartSmoothExt_holder_uniform_half_ball
    (g : CalabiYau.SmoothRiemannianMetric I M)
    (α : M) {p : ℝ} (hp : (Module.finrank ℝ E : ℝ) < p)
    [NeZero (Module.finrank ℝ E)] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
        ∀ y₁ y₂ : EuclN,
          y₁ ∈ Metric.ball (0 : EuclN) (chartRadius (I := I) (M := M) α / 2) →
          y₂ ∈ Metric.ball (0 : EuclN) (chartRadius (I := I) (M := M) α / 2) →
          ‖chartSmoothExt (I := I) (M := M) α
              (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
                : C^∞⟮I, M; ℝ⟯) x * u x) y₁ -
            chartSmoothExt (I := I) (M := M) α
              (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
                : C^∞⟮I, M; ℝ⟯) x * u x) y₂‖ ≤
            C * ‖y₁ - y₂‖ ^ (1 - (Module.finrank ℝ E : ℝ) / p) *
              (wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p) u).toReal := by
  classical
  have hd_pos : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast NeZero.pos (Module.finrank ℝ E)
  have hd_one_le : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
    have : 1 ≤ Module.finrank ℝ E := NeZero.one_le
    exact_mod_cast this
  have hp_pos : 0 < p := lt_of_le_of_lt hd_pos.le hp
  have hp_one : 1 ≤ p := by linarith
  have hp_enn_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal hp_one
  set R : ℝ := chartRadius (I := I) (M := M) α with hR_def
  have hR_pos : 0 < R := chartRadius_pos (I := I) (M := M) α
  obtain ⟨C₀, hC₀_nn, hbound⟩ :=
    Sobolev.EuclideanMorrey.smooth_morrey_pair_bound_uniform
      (d := Module.finrank ℝ E) hp
      (x₀ := (0 : EuclN)) (R := R) hR_pos
  set d : ℕ := Module.finrank ℝ E with hd_def
  refine ⟨C₀ * (d : ℝ), mul_nonneg hC₀_nn (Nat.cast_nonneg _), ?_⟩
  intro u hu y₁ y₂ hy₁ hy₂
  set f : EuclN → ℝ := chartSmoothExt (I := I) (M := M) α
    (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) x * u x) with hf_def
  have hf_smooth_top : ContDiff ℝ (⊤ : ℕ∞) f := by
    rw [hf_def]
    exact contDiff_chartSmoothExt_pou_mul (I := I) (M := M) α
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M)
      (CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M) hu
  have h_pair := hbound (u := f) hf_smooth_top hy₁ hy₂
  have h_grad_bd := eLpNorm_norm_fderiv_chartSmoothExt_ball_le_wkpNormChart
    (I := I) (M := M) g α (q := ENNReal.ofReal p) hp_enn_one hu
  have hwkp_lt_top : wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p) u < ⊤ :=
    wkpNormChart_lt_top_of_memWkpChart (I := I) (M := M) hp_enn_one
      (Sobolev.Equivalence.MemWkpChart_of_contMDiff
        (I := I) (M := M) hp_enn_one hu)
  have hwkp_ne_top : wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p) u ≠ ⊤ :=
    hwkp_lt_top.ne
  set N : ℝ := (wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p) u).toReal with hN_def
  have hN_nn : 0 ≤ N := ENNReal.toReal_nonneg
  have h_d_wkp_ne_top : ((d : ℕ) : ℝ≥0∞) *
      wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p) u ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hwkp_ne_top
  have h_grad_real :
      (eLpNorm (fun z : EuclN => ‖fderiv ℝ f z‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : EuclN) R))).toReal ≤
        (d : ℝ) * N := by
    have h_le := ENNReal.toReal_mono h_d_wkp_ne_top h_grad_bd
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h_le
    exact h_le
  have h_dist_eq : dist y₁ y₂ = ‖y₁ - y₂‖ := dist_eq_norm y₁ y₂
  have h_dist_pow_nn : 0 ≤ dist y₁ y₂ ^ (1 - (d : ℝ) / p) :=
    Real.rpow_nonneg dist_nonneg _
  calc ‖f y₁ - f y₂‖
      ≤ C₀ * dist y₁ y₂ ^ (1 - (d : ℝ) / p) *
          (eLpNorm (fun z : EuclN => ‖fderiv ℝ f z‖) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball (0 : EuclN) R))).toReal := h_pair
    _ ≤ C₀ * dist y₁ y₂ ^ (1 - (d : ℝ) / p) * ((d : ℝ) * N) := by
        apply mul_le_mul_of_nonneg_left h_grad_real
        exact mul_nonneg hC₀_nn h_dist_pow_nn
    _ = C₀ * (d : ℝ) * ‖y₁ - y₂‖ ^ (1 - (d : ℝ) / p) * N := by
        rw [h_dist_eq]; ring

omit [I.Boundaryless] in
private lemma toEuclidean_extChartAt_mem_half_ball_of_mem_tsupport_pou
    (α : M) {x : M}
    (hx : x ∈ tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :
    (toEuclidean (E := E)) (extChartAt I α x) ∈
      Metric.ball (0 : EuclN) (chartRadius (I := I) (M := M) α / 2) := by
  classical
  have h_ext_in : extChartAt I α x ∈ (extChartAt I α) ''
      (tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ)) := ⟨x, hx, rfl⟩
  have h_toEuc_in : (toEuclidean (E := E)) (extChartAt I α x) ∈
      chartCarrier (I := I) (M := M) α :=
    ⟨extChartAt I α x, h_ext_in, rfl⟩
  exact chartCarrier_subset_half_ball (I := I) (M := M) α h_toEuc_in

private lemma pou_mul_holder_chart_uniform_tsupport
    (g : CalabiYau.SmoothRiemannianMetric I M)
    (α : M) {p : ℝ} (hp : (Module.finrank ℝ E : ℝ) < p)
    [NeZero (Module.finrank ℝ E)] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
        ∀ x ∈ tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ y ∈ tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ),
          ‖(CalabiYau.RiemannianVolume.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) x * u x -
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) y * u y‖ ≤
            C * ‖(toEuclidean (E := E)) (extChartAt I α x) -
                (toEuclidean (E := E)) (extChartAt I α y)‖ ^
                (1 - (Module.finrank ℝ E : ℝ) / p) *
              (wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p) u).toReal := by
  classical
  obtain ⟨C, hC_nn, hbound⟩ :=
    chartSmoothExt_holder_uniform_half_ball (I := I) (M := M) g α hp
  refine ⟨C, hC_nn, ?_⟩
  intro u hu x hx y hy
  have h_subord :
      tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆ (chartAt H α).source :=
    CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M α
  have hx_source : x ∈ (chartAt H α).source := h_subord hx
  have hy_source : y ∈ (chartAt H α).source := h_subord hy
  set y₁ : EuclN := (toEuclidean (E := E)) (extChartAt I α x) with hy₁_def
  set y₂ : EuclN := (toEuclidean (E := E)) (extChartAt I α y) with hy₂_def
  have hy₁_R2 : y₁ ∈ Metric.ball (0 : EuclN)
      (chartRadius (I := I) (M := M) α / 2) :=
    toEuclidean_extChartAt_mem_half_ball_of_mem_tsupport_pou (I := I) (M := M) α hx
  have hy₂_R2 : y₂ ∈ Metric.ball (0 : EuclN)
      (chartRadius (I := I) (M := M) α / 2) :=
    toEuclidean_extChartAt_mem_half_ball_of_mem_tsupport_pou (I := I) (M := M) α hy
  have h_pair := hbound hu y₁ y₂ hy₁_R2 hy₂_R2
  have h_eq_x :
      chartSmoothExt (I := I) (M := M) α
          (fun z : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) z * u z) y₁ =
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x := by
    rw [hy₁_def]
    exact chartSmoothExt_pou_mul_apply_at_chart_image (I := I) (M := M) α u hx_source
  have h_eq_y :
      chartSmoothExt (I := I) (M := M) α
          (fun z : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) z * u z) y₂ =
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) y * u y := by
    rw [hy₂_def]
    exact chartSmoothExt_pou_mul_apply_at_chart_image (I := I) (M := M) α u hy_source
  rw [h_eq_x, h_eq_y] at h_pair
  exact h_pair

end Chart
end Sobolev
