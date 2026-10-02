-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/H1Compl/GradientLipschitz.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.H1Compl.ChartGradient
public import CalabiYau.Analysis.Sobolev.Intrinsic.Equivalence.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Analysis.Calculus.ContDiff.Basic

@[expose] public section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace CalabiYau
namespace Analysis
namespace Laplacian
namespace H1ComplGradientLipschitz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Laplacian.MetricExtension
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.H1ComplGradientChartBridge
open CalabiYau.Analysis.Laplacian.H1ComplToLpChartBridge

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))


variable [T2Space M] [CompactSpace M] in
noncomputable def smoothChartExt (g : SmoothRiemannianMetric I M) (α : M)
    (v : SmoothScalar g) : EuclN → ℝ := by
  classical
  exact fun y =>
    if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
        v.toFun ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    else 0

section

variable [T2Space M] [CompactSpace M]

lemma smoothChartExt_apply_of_mem_target
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) {y : EuclN}
    (hy : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target) :
    smoothChartExt (I := I) (M := M) g α v y =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
        v.toFun ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  classical
  change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
        v.toFun ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    else 0) = _
  rw [if_pos hy]

lemma smoothChartExt_apply_of_notMem_target
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) {y : EuclN}
    (hy : (toEuclidean (E := E)).symm y ∉ (extChartAt I α).target) :
    smoothChartExt (I := I) (M := M) g α v y = 0 := by
  classical
  change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
        v.toFun ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    else 0) = 0
  rw [if_neg hy]

private lemma smoothChartExt_eq_chartPushed_on_target
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) {y : EuclN}
    (hy : y ∈ Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α) :
    smoothChartExt (I := I) (M := M) g α v y =
      Sobolev.Chart.chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α v.toFun y := by
  classical
  have h_toE_symm_in : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rcases hy with ⟨z, hz_target, hzy⟩
    have h_eq : (toEuclidean (E := E)).symm y = z := by
      rw [← hzy]; exact (toEuclidean (E := E)).symm_apply_apply z
    rw [h_eq]; exact hz_target
  rw [smoothChartExt_apply_of_mem_target (I := I) (M := M) g α v h_toE_symm_in]
  unfold Sobolev.Chart.chartPushed
  rfl

private lemma smoothChartExt_smooth
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ fun x : M =>
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x * v.toFun x :=
  ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff).mul v.smooth

private lemma smoothChartExt_support_in_chartSource
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    tsupport (fun x : M =>
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x * v.toFun x) ⊆
      (chartAt H α).source := by
  have h1 : tsupport (fun x : M =>
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x * v.toFun x) ⊆
      tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
    apply tsupport_mul_subset_left
  exact h1.trans
    ((CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M) α)

private lemma contDiffOn_extFormula
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    ContDiffOn ℝ ∞
        (fun y : EuclN =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            v.toFun ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set f : M → ℝ := fun x : M =>
    (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x * v.toFun x with hf_def
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f :=
    smoothChartExt_smooth (I := I) (M := M) g α v
  have hscalar : ContDiffOn ℝ ∞
      (fun y : E => f ((extChartAt I α).symm y))
      (extChartAt I α).target := scalarOnE_contDiffOn (I := I) α hf_smooth
  have htoEuc_symm_smooth : ContDiff ℝ ∞ ((toEuclidean (E := E)).symm) :=
    ContinuousLinearEquiv.contDiff _
  have hmaps : Set.MapsTo ((toEuclidean (E := E)).symm)
      (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)
      (extChartAt I α).target := by
    intro y hy
    rcases hy with ⟨z, hz_target, hzy⟩
    have h_eq : (toEuclidean (E := E)).symm y = z := by
      rw [← hzy]; exact (toEuclidean (E := E)).symm_apply_apply z
    rw [h_eq]; exact hz_target
  exact hscalar.comp htoEuc_symm_smooth.contDiffOn hmaps

end

variable [I.Boundaryless] [T2Space M] [CompactSpace M] in
private lemma smoothChartExt_contDiffAt_of_mem_target
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) {y : EuclN}
    (hy : y ∈ Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α) :
    ContDiffAt ℝ ∞ (smoothChartExt (I := I) (M := M) g α v) y := by
  classical
  have hOpen : IsOpen (Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α) :=
    Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α
  have hContDiffOn := contDiffOn_extFormula (I := I) (M := M) g α v
  have hContDiffAt_formula : ContDiffAt ℝ ∞
      (fun y : EuclN =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          v.toFun ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) y := by
    have hwithin : ContDiffWithinAt ℝ ∞
        (fun y : EuclN =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            v.toFun ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)
        y := hContDiffOn y hy
    exact hwithin.contDiffAt (hOpen.mem_nhds hy)
  apply hContDiffAt_formula.congr_of_eventuallyEq
  filter_upwards [hOpen.mem_nhds hy] with z hz
  have h_toE_symm_in : (toEuclidean (E := E)).symm z ∈ (extChartAt I α).target := by
    rcases hz with ⟨w, hw_target, hwz⟩
    have h_eq : (toEuclidean (E := E)).symm z = w := by
      rw [← hwz]; exact (toEuclidean (E := E)).symm_apply_apply w
    rw [h_eq]; exact hw_target
  rw [smoothChartExt_apply_of_mem_target (I := I) (M := M) g α v h_toE_symm_in]

section

variable [T2Space M] [CompactSpace M]

private lemma image_toE_chart_support_isCompact
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    IsCompact ((toEuclidean (E := E)) ''
      ((extChartAt I α) '' (tsupport
        (fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x * v.toFun x)))) := by
  set f : M → ℝ := fun x : M =>
    (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x * v.toFun x with hf_def
  have hf_support : tsupport f ⊆ (chartAt H α).source :=
    smoothChartExt_support_in_chartSource (I := I) (M := M) g α v
  have hf_compact : IsCompact (tsupport f) := (isClosed_tsupport _).isCompact
  have hsub : tsupport f ⊆ (extChartAt I α).source := by
    intro x hx
    rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source (I := I)]
    exact hf_support hx
  have hcont : ContinuousOn (extChartAt I α) (tsupport f) :=
    (continuousOn_extChartAt α).mono hsub
  have h1 : IsCompact ((extChartAt I α) '' (tsupport f)) :=
    hf_compact.image_of_continuousOn hcont
  exact h1.image (toEuclidean (E := E)).continuous

private lemma image_toE_chart_support_subset_chartTarget
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport
          (fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x * v.toFun x))) ⊆
      Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α := by
  intro y hy
  rcases hy with ⟨z, ⟨x, hx_support, hxz⟩, hzy⟩
  have hf_support : tsupport (fun x : M =>
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x * v.toFun x) ⊆
        (chartAt H α).source :=
    smoothChartExt_support_in_chartSource (I := I) (M := M) g α v
  have hx_source : x ∈ (extChartAt I α).source := by
    rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source (I := I)]
    exact hf_support hx_support
  have hz_target : z ∈ (extChartAt I α).target := by
    rw [← hxz]; exact (extChartAt I α).map_source hx_source
  exact ⟨z, hz_target, hzy⟩

private lemma smoothChartExt_contDiffAt_of_notMem
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) {y : EuclN}
    (hy_off : y ∉ (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport
          (fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x * v.toFun x)))) :
    ContDiffAt ℝ ∞ (smoothChartExt (I := I) (M := M) g α v) y := by
  classical
  set K : Set EuclN := (toEuclidean (E := E)) ''
      ((extChartAt I α) '' (tsupport
        (fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x * v.toFun x)))
    with hK_def
  have hK_compact : IsCompact K := image_toE_chart_support_isCompact (I := I) (M := M) g α v
  have hK_closed : IsClosed K := hK_compact.isClosed
  have hK_compl_open : IsOpen Kᶜ := hK_closed.isOpen_compl
  have hy_compl : y ∈ Kᶜ := hy_off
  apply ContDiffAt.congr_of_eventuallyEq (f := fun _ : EuclN => (0 : ℝ)) contDiffAt_const
  filter_upwards [hK_compl_open.mem_nhds hy_compl] with z hz
  by_cases hz_target : z ∈ Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α
  · obtain ⟨w, hw_target, hwz⟩ := hz_target
    have h_eq : (toEuclidean (E := E)).symm z = w := by
      rw [← hwz]; exact (toEuclidean (E := E)).symm_apply_apply w
    have hsmooth_eq := smoothChartExt_apply_of_mem_target
      (I := I) (M := M) g α v (h_eq ▸ hw_target)
    by_contra hne
    apply hne
    rw [hsmooth_eq]
    by_contra hne_f
    apply hz
    have hne_f' : (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) ((extChartAt I α).symm w) *
        v.toFun ((extChartAt I α).symm w) ≠ 0 := by
      intro hzero
      apply hne_f
      rw [h_eq]; exact hzero
    have h_in_tsupp : (extChartAt I α).symm w ∈ tsupport
        (fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x * v.toFun x) := by
      apply subset_tsupport
      exact hne_f'
    have hext_right : (extChartAt I α) ((extChartAt I α).symm w) = w :=
      (extChartAt I α).right_inv hw_target
    exact ⟨w, ⟨(extChartAt I α).symm w, h_in_tsupp, hext_right⟩, hwz⟩
  · have h_notMem : (toEuclidean (E := E)).symm z ∉ (extChartAt I α).target := by
      intro h_in
      apply hz_target
      refine ⟨(toEuclidean (E := E)).symm z, h_in, ?_⟩
      simp
    exact smoothChartExt_apply_of_notMem_target (I := I) (M := M) g α v h_notMem

end

variable [I.Boundaryless] [T2Space M] [CompactSpace M] in
theorem smoothChartExt_contDiff
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    ContDiff ℝ ∞ (smoothChartExt (I := I) (M := M) g α v) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy_target : y ∈ Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α
  · exact smoothChartExt_contDiffAt_of_mem_target (I := I) (M := M) g α v hy_target
  · have hy_off : y ∉ (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport
          (fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x * v.toFun x))) := fun h_in =>
      hy_target (image_toE_chart_support_subset_chartTarget (I := I) (M := M) g α v h_in)
    exact smoothChartExt_contDiffAt_of_notMem (I := I) (M := M) g α v hy_off

section

variable [T2Space M] [CompactSpace M]

theorem smoothChartExt_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    HasCompactSupport (smoothChartExt (I := I) (M := M) g α v) := by
  classical
  have hK_compact : IsCompact ((toEuclidean (E := E)) ''
      ((extChartAt I α) '' (tsupport
        (fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x * v.toFun x)))) :=
    image_toE_chart_support_isCompact (I := I) (M := M) g α v
  apply HasCompactSupport.of_support_subset_isCompact hK_compact
  intro y hy_support
  by_contra hyK
  apply hy_support
  by_cases hy_target : y ∈ Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α
  · obtain ⟨w, hw_target, hwy⟩ := hy_target
    have h_eq : (toEuclidean (E := E)).symm y = w := by
      rw [← hwy]; exact (toEuclidean (E := E)).symm_apply_apply w
    have hsmooth_eq := smoothChartExt_apply_of_mem_target
      (I := I) (M := M) g α v (h_eq ▸ hw_target)
    by_contra hne
    apply hne
    rw [hsmooth_eq]
    by_contra hne_f
    apply hyK
    have hne_f' : (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) ((extChartAt I α).symm w) *
        v.toFun ((extChartAt I α).symm w) ≠ 0 := by
      intro hzero
      apply hne_f
      rw [h_eq]; exact hzero
    have h_in_tsupp : (extChartAt I α).symm w ∈ tsupport
        (fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x * v.toFun x) := by
      apply subset_tsupport
      exact hne_f'
    have hext_right : (extChartAt I α) ((extChartAt I α).symm w) = w :=
      (extChartAt I α).right_inv hw_target
    exact ⟨w, ⟨(extChartAt I α).symm w, h_in_tsupp, hext_right⟩, hwy⟩
  · have h_notMem : (toEuclidean (E := E)).symm y ∉ (extChartAt I α).target := by
      intro h_in
      apply hy_target
      refine ⟨(toEuclidean (E := E)).symm y, h_in, ?_⟩
      simp
    exact smoothChartExt_apply_of_notMem_target (I := I) (M := M) g α v h_notMem

private lemma smoothChartExt_add_apply
    (g : SmoothRiemannianMetric I M) (α : M) (v w : SmoothScalar g) (y : EuclN) :
    smoothChartExt (I := I) (M := M) g α (v + w) y =
      smoothChartExt (I := I) (M := M) g α v y +
        smoothChartExt (I := I) (M := M) g α w y := by
  classical
  by_cases hy : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target
  · rw [smoothChartExt_apply_of_mem_target (I := I) (M := M) g α (v + w) hy]
    rw [smoothChartExt_apply_of_mem_target (I := I) (M := M) g α v hy]
    rw [smoothChartExt_apply_of_mem_target (I := I) (M := M) g α w hy]
    rw [SmoothScalar.toFun_add_apply]
    ring
  · rw [smoothChartExt_apply_of_notMem_target (I := I) (M := M) g α (v + w) hy]
    rw [smoothChartExt_apply_of_notMem_target (I := I) (M := M) g α v hy]
    rw [smoothChartExt_apply_of_notMem_target (I := I) (M := M) g α w hy]
    ring

private lemma smoothChartExt_smul_apply
    (g : SmoothRiemannianMetric I M) (α : M) (c : ℝ) (v : SmoothScalar g) (y : EuclN) :
    smoothChartExt (I := I) (M := M) g α (c • v) y =
      c * smoothChartExt (I := I) (M := M) g α v y := by
  classical
  by_cases hy : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target
  · rw [smoothChartExt_apply_of_mem_target (I := I) (M := M) g α (c • v) hy]
    rw [smoothChartExt_apply_of_mem_target (I := I) (M := M) g α v hy]
    rw [SmoothScalar.toFun_smul_apply]
    ring
  · rw [smoothChartExt_apply_of_notMem_target (I := I) (M := M) g α (c • v) hy]
    rw [smoothChartExt_apply_of_notMem_target (I := I) (M := M) g α v hy]
    ring

private lemma smoothChartExt_add
    (g : SmoothRiemannianMetric I M) (α : M) (v w : SmoothScalar g) :
    smoothChartExt (I := I) (M := M) g α (v + w) =
      smoothChartExt (I := I) (M := M) g α v + smoothChartExt (I := I) (M := M) g α w := by
  funext y
  exact smoothChartExt_add_apply (I := I) (M := M) g α v w y

private lemma smoothChartExt_smul
    (g : SmoothRiemannianMetric I M) (α : M) (c : ℝ) (v : SmoothScalar g) :
    smoothChartExt (I := I) (M := M) g α (c • v) =
      c • smoothChartExt (I := I) (M := M) g α v := by
  funext y
  rw [Pi.smul_apply, smul_eq_mul]
  exact smoothChartExt_smul_apply (I := I) (M := M) g α c v y

end

variable [T2Space M] [CompactSpace M] in
noncomputable def smoothChartExtPartial
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (v : SmoothScalar g) : EuclN → ℝ := fun y =>
  (fderiv ℝ (smoothChartExt (I := I) (M := M) g α v) y) (EuclideanSpace.single j 1)

variable [I.Boundaryless] [T2Space M] [CompactSpace M] in
theorem smoothChartExtPartial_contDiff
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (v : SmoothScalar g) :
    ContDiff ℝ ∞ (smoothChartExtPartial (I := I) (M := M) g α j v) := by
  unfold smoothChartExtPartial
  exact ((smoothChartExt_contDiff (I := I) (M := M) g α v).fderiv_right
    (m := (⊤ : ℕ∞)) (by norm_cast)).clm_apply contDiff_const

variable [T2Space M] [CompactSpace M] in
theorem smoothChartExtPartial_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (v : SmoothScalar g) :
    HasCompactSupport (smoothChartExtPartial (I := I) (M := M) g α j v) := by
  unfold smoothChartExtPartial
  exact (smoothChartExt_hasCompactSupport (I := I) (M := M) g α v).fderiv_apply (𝕜 := ℝ) _

section

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

theorem smoothChartExtPartial_continuous
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (v : SmoothScalar g) :
    Continuous (smoothChartExtPartial (I := I) (M := M) g α j v) :=
  (smoothChartExtPartial_contDiff (I := I) (M := M) g α j v).continuous

theorem smoothChartExtPartial_add
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (v w : SmoothScalar g) :
    smoothChartExtPartial (I := I) (M := M) g α j (v + w) =
      smoothChartExtPartial (I := I) (M := M) g α j v +
        smoothChartExtPartial (I := I) (M := M) g α j w := by
  funext y
  change (fderiv ℝ (smoothChartExt (I := I) (M := M) g α (v + w)) y) (EuclideanSpace.single j 1) =
    (fderiv ℝ (smoothChartExt (I := I) (M := M) g α v) y) (EuclideanSpace.single j 1) +
      (fderiv ℝ (smoothChartExt (I := I) (M := M) g α w) y) (EuclideanSpace.single j 1)
  have h1 : DifferentiableAt ℝ (smoothChartExt (I := I) (M := M) g α v) y :=
    (smoothChartExt_contDiff (I := I) (M := M) g α v).differentiable (by norm_cast) y
  have h2 : DifferentiableAt ℝ (smoothChartExt (I := I) (M := M) g α w) y :=
    (smoothChartExt_contDiff (I := I) (M := M) g α w).differentiable (by norm_cast) y
  have h_fderiv_eq : fderiv ℝ (smoothChartExt (I := I) (M := M) g α (v + w)) y =
      fderiv ℝ (smoothChartExt (I := I) (M := M) g α v) y +
        fderiv ℝ (smoothChartExt (I := I) (M := M) g α w) y := by
    rw [smoothChartExt_add (I := I) (M := M) g α v w]
    exact fderiv_fun_add h1 h2
  rw [h_fderiv_eq, add_apply]

theorem smoothChartExtPartial_smul
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (c : ℝ) (v : SmoothScalar g) :
    smoothChartExtPartial (I := I) (M := M) g α j (c • v) =
      c • smoothChartExtPartial (I := I) (M := M) g α j v := by
  funext y
  change (fderiv ℝ (smoothChartExt (I := I) (M := M) g α (c • v)) y) (EuclideanSpace.single j 1) =
    c • (fderiv ℝ (smoothChartExt (I := I) (M := M) g α v) y) (EuclideanSpace.single j 1)
  have h : DifferentiableAt ℝ (smoothChartExt (I := I) (M := M) g α v) y :=
    (smoothChartExt_contDiff (I := I) (M := M) g α v).differentiable (by norm_cast) y
  have h_fderiv_eq : fderiv ℝ (smoothChartExt (I := I) (M := M) g α (c • v)) y =
      c • fderiv ℝ (smoothChartExt (I := I) (M := M) g α v) y := by
    rw [smoothChartExt_smul (I := I) (M := M) g α c v]
    exact fderiv_const_smul h c
  rw [h_fderiv_eq, smul_apply]

private lemma chartPushed_eventuallyEq_smoothChartExt
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) {y : EuclN}
    (hy : y ∈ Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :
    Sobolev.Chart.chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α v.toFun =ᶠ[𝓝 y]
      smoothChartExt (I := I) (M := M) g α v := by
  classical
  have hOpen : IsOpen (Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α) :=
    Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α
  filter_upwards [hOpen.mem_nhds hy] with z hz
  exact (smoothChartExt_eq_chartPushed_on_target (I := I) (M := M) g α v hz).symm

theorem chartPushedPartial_eq_smoothChartExtPartial_on_target
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (v : SmoothScalar g) {y : EuclN}
    (hy : y ∈ Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :
    CalabiYau.Analysis.Laplacian.H1ComplGradientChartBridge.chartPushedPartial
        (I := I) (M := M) g α j v y =
      smoothChartExtPartial (I := I) (M := M) g α j v y := by
  unfold CalabiYau.Analysis.Laplacian.H1ComplGradientChartBridge.chartPushedPartial
  unfold smoothChartExtPartial
  congr 1
  exact Filter.EventuallyEq.fderiv_eq
    (chartPushed_eventuallyEq_smoothChartExt (I := I) (M := M) g α v hy)

theorem chartPushedPartial_aeEq_smoothChartExtPartial
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (v : SmoothScalar g) :
    CalabiYau.Analysis.Laplacian.H1ComplGradientChartBridge.chartPushedPartial
        (I := I) (M := M) g α j v =ᵐ[
          (chartPulledWeightedMeasure (I := I) g α).restrict
            (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)]
      smoothChartExtPartial (I := I) (M := M) g α j v := by
  refine (MeasureTheory.ae_restrict_iff'
    (Sobolev.Chart.chartTargetEuclid_measurableSet
      (I := I) (M := M) α)).mpr ?_
  refine Filter.Eventually.of_forall (fun y hy => ?_)
  exact chartPushedPartial_eq_smoothChartExtPartial_on_target
    (I := I) (M := M) g α j v hy

theorem smoothChartExtPartial_memLp_chartWeighted_restrict
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (v : SmoothScalar g) :
    MemLp (smoothChartExtPartial (I := I) (M := M) g α j v) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_cont : Continuous (smoothChartExtPartial (I := I) (M := M) g α j v) :=
    smoothChartExtPartial_continuous (I := I) (M := M) g α j v
  have h_cs : HasCompactSupport (smoothChartExtPartial (I := I) (M := M) g α j v) :=
    smoothChartExtPartial_hasCompactSupport (I := I) (M := M) g α j v
  obtain ⟨M_partial, hM_partial_nn, hM_partial_bd⟩ : ∃ N : ℝ, 0 ≤ N ∧
      ∀ y : EuclN, |smoothChartExtPartial (I := I) (M := M) g α j v y| ≤ N := by
    rcases h_cont.bounded_above_of_compact_support h_cs with ⟨N, hN⟩
    refine ⟨max N 0, le_max_right _ _, fun y => ?_⟩
    exact (hN y).trans (le_max_left _ _)
  refine ⟨h_cont.aestronglyMeasurable, ?_⟩
  set K_partial := tsupport (smoothChartExtPartial (I := I) (M := M) g α j v)
  have hK_compact : IsCompact K_partial := h_cs
  have h_zero_off : ∀ y, y ∉ K_partial →
      smoothChartExtPartial (I := I) (M := M) g α j v y = 0 := by
    intro y hy
    by_contra hne
    exact hy (subset_tsupport _ hne)
  have hK_partial_in_chartTarget : K_partial ⊆
      Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α := by
    have h_fderiv_support : tsupport (smoothChartExtPartial (I := I) (M := M) g α j v) ⊆
        tsupport (smoothChartExt (I := I) (M := M) g α v) :=
      tsupport_fderiv_apply_subset (𝕜 := ℝ) (EuclideanSpace.single j 1)
    set K_image : Set EuclN := (toEuclidean (E := E)) ''
        ((extChartAt I α) '' (tsupport
          (fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x * v.toFun x)))
      with hK_image_def
    have hK_image_compact : IsCompact K_image :=
      image_toE_chart_support_isCompact (I := I) (M := M) g α v
    have hK_image_in : K_image ⊆ Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α :=
      image_toE_chart_support_subset_chartTarget (I := I) (M := M) g α v
    have h_support_in_K_image : Function.support (smoothChartExt (I := I) (M := M) g α v) ⊆
        K_image := by
      intro y hy_support
      by_contra hyK
      apply hy_support
      by_cases hy_target : y ∈ Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α
      · obtain ⟨w, hw_target, hwy⟩ := hy_target
        have h_eq : (toEuclidean (E := E)).symm y = w := by
          rw [← hwy]; exact (toEuclidean (E := E)).symm_apply_apply w
        have hsmooth_eq := smoothChartExt_apply_of_mem_target
          (I := I) (M := M) g α v (h_eq ▸ hw_target)
        by_contra hne
        apply hne
        rw [hsmooth_eq]
        by_contra hne_f
        apply hyK
        have hne_f' : (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) ((extChartAt I α).symm w) *
            v.toFun ((extChartAt I α).symm w) ≠ 0 := by
          intro hzero
          apply hne_f
          rw [h_eq]
          exact hzero
        have h_in_tsupp : (extChartAt I α).symm w ∈ tsupport
            (fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x * v.toFun x) := by
          apply subset_tsupport
          exact hne_f'
        have hext_right : (extChartAt I α) ((extChartAt I α).symm w) = w :=
          (extChartAt I α).right_inv hw_target
        exact ⟨w, ⟨(extChartAt I α).symm w, h_in_tsupp, hext_right⟩, hwy⟩
      · have h_notMem : (toEuclidean (E := E)).symm y ∉ (extChartAt I α).target := by
          intro h_in
          apply hy_target
          refine ⟨(toEuclidean (E := E)).symm y, h_in, ?_⟩
          simp
        exact smoothChartExt_apply_of_notMem_target (I := I) (M := M) g α v h_notMem
    have h_smoothExt_support_in_chartTarget :
        tsupport (smoothChartExt (I := I) (M := M) g α v) ⊆
          Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α := by
      have h_tsupp_in_K : tsupport (smoothChartExt (I := I) (M := M) g α v) ⊆ K_image :=
        closure_minimal h_support_in_K_image hK_image_compact.isClosed
      exact h_tsupp_in_K.trans hK_image_in
    exact h_fderiv_support.trans h_smoothExt_support_in_chartTarget
  have h_dens_contOn :
      ContinuousOn (densityOnEuclid (I := I) g α) K_partial :=
    (densityOnEuclid_continuousOn (I := I) g α).mono hK_partial_in_chartTarget
  obtain ⟨M_density, hM_density_pos, hM_density_bd⟩ : ∃ M_d : ℝ, 0 < M_d ∧
      ∀ y ∈ K_partial, densityOnEuclid (I := I) g α y ≤ M_d := by
    by_cases hKne : K_partial.Nonempty
    · obtain ⟨y₀, hy₀_mem, hy₀_max⟩ :=
        hK_compact.exists_isMaxOn hKne h_dens_contOn
      have h_pos : 0 < densityOnEuclid (I := I) g α y₀ :=
        densityOnEuclid_pos (I := I) g α (hK_partial_in_chartTarget hy₀_mem)
      refine ⟨densityOnEuclid (I := I) g α y₀, h_pos, fun y hy => hy₀_max hy⟩
    · refine ⟨1, by norm_num, ?_⟩
      intro y hy
      rw [Set.not_nonempty_iff_eq_empty] at hKne
      rw [hKne] at hy
      exact absurd hy (Set.notMem_empty y)
  have h_vol_K_lt_top : (volume : Measure EuclN) K_partial < ⊤ :=
    hK_compact.measure_lt_top
  have h_cpw_K_lt_top : (chartPulledWeightedMeasure (I := I) g α) K_partial < ⊤ := by
    unfold chartPulledWeightedMeasure
    rw [withDensity_apply _ hK_compact.measurableSet]
    have h_int_bd : (∫⁻ y in K_partial, ENNReal.ofReal (densityOnEuclid (I := I) g α y)
        ∂(volume : Measure EuclN)) ≤
        ENNReal.ofReal M_density * (volume : Measure EuclN) K_partial := by
      calc (∫⁻ y in K_partial, ENNReal.ofReal (densityOnEuclid (I := I) g α y)
          ∂(volume : Measure EuclN))
          ≤ ∫⁻ _y in K_partial, ENNReal.ofReal M_density ∂(volume : Measure EuclN) := by
            refine MeasureTheory.setLIntegral_mono_ae' hK_compact.measurableSet ?_
            refine Filter.Eventually.of_forall (fun y hy => ?_)
            exact ENNReal.ofReal_le_ofReal (hM_density_bd y hy)
        _ = ENNReal.ofReal M_density * (volume : Measure EuclN) K_partial := by
            rw [MeasureTheory.setLIntegral_const]
    exact lt_of_le_of_lt h_int_bd
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h_vol_K_lt_top)
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  have h_two : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h_two]
  refine ENNReal.rpow_lt_top_of_nonneg (by positivity) ?_
  have h_lint_bd : ∫⁻ y, ‖smoothChartExtPartial (I := I) (M := M) g α j v y‖ₑ ^ (2 : ℝ)
      ∂((chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal (M_partial^2) *
          (chartPulledWeightedMeasure (I := I) g α) K_partial := by
    have h_ptbd : ∀ y, ‖smoothChartExtPartial (I := I) (M := M) g α j v y‖ₑ ^ (2 : ℝ)
        ≤ ENNReal.ofReal (M_partial^2) * Set.indicator K_partial (fun _ => (1 : ℝ≥0∞)) y := by
      intro y
      by_cases hy : y ∈ K_partial
      · rw [Set.indicator_of_mem hy, mul_one]
        have h1 : ‖smoothChartExtPartial (I := I) (M := M) g α j v y‖ₑ ≤
            ENNReal.ofReal M_partial := by
          rw [Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal (hM_partial_bd y)
        calc ‖smoothChartExtPartial (I := I) (M := M) g α j v y‖ₑ ^ (2 : ℝ)
            ≤ (ENNReal.ofReal M_partial) ^ (2 : ℝ) := by
              exact ENNReal.rpow_le_rpow h1 (by norm_num)
          _ = ENNReal.ofReal (M_partial^2) := by
              rw [show (M_partial^2 : ℝ) = M_partial * M_partial from sq M_partial]
              rw [ENNReal.ofReal_mul hM_partial_nn]
              rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num,
                  ENNReal.rpow_natCast, sq]
      · have h_f_zero : smoothChartExtPartial (I := I) (M := M) g α j v y = 0 := h_zero_off y hy
        rw [h_f_zero, enorm_zero]
        rw [Set.indicator_of_notMem hy, mul_zero]
        rw [ENNReal.zero_rpow_of_pos (by norm_num)]
    calc ∫⁻ y, ‖smoothChartExtPartial (I := I) (M := M) g α j v y‖ₑ ^ (2 : ℝ)
            ∂((chartPulledWeightedMeasure (I := I) g α).restrict
                (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α))
          ≤ ∫⁻ y, ENNReal.ofReal (M_partial^2) * Set.indicator K_partial (fun _ => (1 : ℝ≥0∞)) y
              ∂((chartPulledWeightedMeasure (I := I) g α).restrict
                  (Sobolev.Chart.chartTargetEuclid
                    (I := I) (M := M) α)) := by
            refine MeasureTheory.lintegral_mono_ae ?_
            exact Filter.Eventually.of_forall h_ptbd
        _ = ENNReal.ofReal (M_partial^2) *
              ∫⁻ y, Set.indicator K_partial (fun _ => (1 : ℝ≥0∞)) y
                ∂((chartPulledWeightedMeasure (I := I) g α).restrict
                    (Sobolev.Chart.chartTargetEuclid
                      (I := I) (M := M) α)) := by
            rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ = ENNReal.ofReal (M_partial^2) *
              ((chartPulledWeightedMeasure (I := I) g α).restrict
                  (Sobolev.Chart.chartTargetEuclid
                    (I := I) (M := M) α)) K_partial := by
            congr 1
            rw [MeasureTheory.lintegral_indicator_const hK_compact.measurableSet]
            rw [one_mul]
        _ ≤ ENNReal.ofReal (M_partial^2) *
              (chartPulledWeightedMeasure (I := I) g α) K_partial := by
            have h_restrict_le : ((chartPulledWeightedMeasure (I := I) g α).restrict
                  (Sobolev.Chart.chartTargetEuclid
                    (I := I) (M := M) α)) K_partial ≤
                (chartPulledWeightedMeasure (I := I) g α) K_partial :=
              MeasureTheory.Measure.restrict_apply_le _ _
            gcongr
  have h_lint_lt_top : ∫⁻ y, ‖smoothChartExtPartial (I := I) (M := M) g α j v y‖ₑ ^ (2 : ℝ)
      ∂((chartPulledWeightedMeasure (I := I) g α).restrict
          (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α))
      < ⊤ :=
    lt_of_le_of_lt h_lint_bd
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h_cpw_K_lt_top)
  exact h_lint_lt_top.ne

theorem chartPushedPartial_memLp
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (v : SmoothScalar g) :
    MemLp (CalabiYau.Analysis.Laplacian.H1ComplGradientChartBridge.chartPushedPartial
        (I := I) (M := M) g α j v) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)) := by
  have h_aeEq := chartPushedPartial_aeEq_smoothChartExtPartial
    (I := I) (M := M) g α j v
  have h_smoothMemLp := smoothChartExtPartial_memLp_chartWeighted_restrict
    (I := I) (M := M) g α j v
  exact h_smoothMemLp.ae_eq h_aeEq.symm

end

end H1ComplGradientLipschitz
end Laplacian
end Analysis
end CalabiYau

end
