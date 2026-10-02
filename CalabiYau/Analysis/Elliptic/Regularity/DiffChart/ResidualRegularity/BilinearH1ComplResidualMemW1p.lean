-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/DiffChart/ResidualRegularity/BilinearH1ComplResidualMemW1p.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplResidualChain
public import CalabiYau.Analysis.Elliptic.Regularity.FChartResidual.LpDecomposition
public import CalabiYau.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplFromDomainPow
public import CalabiYau.Analysis.Sobolev.Chart.SmoothDensity.SmoothMul
public import CalabiYau.Analysis.Sobolev.Manifold.Rellich.Compactness

@[expose] public section
open CalabiYau.Riemannian

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace CalabiYau
namespace Analysis
namespace Laplacian
namespace DiffChartBilinearH1ComplResidualMemW1p

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.LaplacianDomainChartData
open CalabiYau.Laplacian.LaplacianDomainSmoothMul
open CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl
open CalabiYau.Analysis.Sobolev.Chart
open _root_.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private def smoothExt (α : M) (f : M → ℝ) : EuclN → ℝ := by
  classical
  exact fun y =>
    if y ∈ chartTargetEuclid (I := I) (M := M) α then
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    else 0

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma smoothExt_apply_of_mem
    (α : M) (f : M → ℝ) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    smoothExt (I := I) (M := M) α f y =
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  classical
  unfold smoothExt; simp [hy]

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma smoothExt_apply_of_notMem
    (α : M) (f : M → ℝ) {y : EuclN}
    (hy : y ∉ chartTargetEuclid (I := I) (M := M) α) :
    smoothExt (I := I) (M := M) α f y = 0 := by
  classical
  unfold smoothExt; simp [hy]

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma smoothExt_eq_chartPushedRaw (α : M) (f : M → ℝ) :
    smoothExt (I := I) (M := M) α f =
      chartPushedRaw (I := I) (M := M) α f := by
  funext y
  classical
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [smoothExt_apply_of_mem (I := I) (M := M) α f hy]
    rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α f hy]
  · rw [smoothExt_apply_of_notMem (I := I) (M := M) α f hy]
    rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α f hy]

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma chartPushedRaw_smooth_eq_zero_off_image_tsupport
    {α : M} {f : M → ℝ}
    {y : EuclN}
    (hy : y ∉ (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f))) :
    chartPushedRaw (I := I) (M := M) α f y = 0 := by
  classical
  by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
  · exact _root_.Sobolev.Chart.chartPushedRaw_eq_zero_off_image_tsupport
      (I := I) (M := M) (u := f) α hy_target hy
  · exact chartPushedRaw_apply_of_notMem (I := I) (M := M) α f hy_target

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma chartPushedRaw_smooth_hasCompactSupport
    {α : M} {f : M → ℝ}
    (hf_support : tsupport f ⊆ (chartAt H α).source) :
    HasCompactSupport (chartPushedRaw (I := I) (M := M) α f) := by
  classical
  set K : Set EuclN :=
    (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f)) with hK_def
  have hK_compact : IsCompact K := by
    refine IsCompact.image ?_ (toEuclidean (E := E)).continuous
    have h_tsupp_compact : IsCompact (tsupport f) :=
      (isClosed_tsupport _).isCompact
    have h_cont : ContinuousOn (extChartAt I α) (tsupport f) := by
      apply (continuousOn_extChartAt (I := I) α).mono
      intro x hx
      have hsrc : x ∈ (chartAt H α).source := hf_support hx
      rw [← CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)] at hsrc
      exact hsrc
    exact h_tsupp_compact.image_of_continuousOn h_cont
  apply HasCompactSupport.of_support_subset_isCompact hK_compact
  intro y hy_support
  by_contra hyK
  apply hy_support
  exact chartPushedRaw_smooth_eq_zero_off_image_tsupport
    (I := I) (M := M) (f := f) (α := α) hyK

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
private lemma chartPushedRaw_smooth_continuous
    {α : M} {f : M → ℝ}
    (hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_support : tsupport f ⊆ (chartAt H α).source) :
    Continuous (chartPushedRaw (I := I) (M := M) α f) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set K : Set EuclN :=
    (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f)) with hK_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hK_compact : IsCompact K := by
    refine IsCompact.image ?_ (toEuclidean (E := E)).continuous
    have h_tsupp_compact : IsCompact (tsupport f) :=
      (isClosed_tsupport _).isCompact
    have h_cont : ContinuousOn (extChartAt I α) (tsupport f) := by
      apply (continuousOn_extChartAt (I := I) α).mono
      intro x hx
      have hsrc : x ∈ (chartAt H α).source := hf_support hx
      rw [← CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)] at hsrc
      exact hsrc
    exact h_tsupp_compact.image_of_continuousOn h_cont
  have hK_in_Ω : K ⊆ Ω := by
    intro y hy
    rcases hy with ⟨z, hz, hzy⟩
    rcases hz with ⟨x, hx_support, hxz⟩
    have hxsrc : x ∈ (chartAt H α).source := hf_support hx_support
    rw [hΩ_def, chartTargetEuclid]
    refine ⟨z, ?_, hzy⟩
    rw [← hxz]
    have : x ∈ (extChartAt I α).source := by
      rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)]
      exact hxsrc
    exact (extChartAt I α).map_source this
  have hKc_open : IsOpen (Kᶜ : Set EuclN) := hK_compact.isClosed.isOpen_compl
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy_Ω : y ∈ Ω
  · have hΩ_nhds : Ω ∈ 𝓝 y := hΩ_open.mem_nhds hy_Ω
    have h_eq_on_Ω : ∀ z ∈ Ω, chartPushedRaw (I := I) (M := M) α f z =
        f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) := by
      intro z hz
      exact chartPushedRaw_apply_of_mem (I := I) (M := M) α f hz
    have h_smooth_cont : ContinuousOn
        (fun z : EuclN => f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)))
        Ω := by
      have hscalar : ContDiffOn ℝ ∞
          (fun z : E => f ((extChartAt I α).symm z))
          (extChartAt I α).target :=
        CalabiYau.DivergenceTheorem.scalarOnE_contDiffOn
          (I := I) α hf_smooth
      have htoEuc_cont : Continuous ((toEuclidean (E := E)).symm) :=
        (toEuclidean (E := E)).symm.continuous
      have hmaps : Set.MapsTo ((toEuclidean (E := E)).symm) Ω (extChartAt I α).target := by
        intro z hz
        rw [hΩ_def, chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hz
        exact hz
      have hcont_scalar := hscalar.continuousOn
      exact hcont_scalar.comp htoEuc_cont.continuousOn hmaps
    refine ContinuousAt.congr (f := fun z =>
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))) ?_ ?_
    · exact (h_smooth_cont y hy_Ω).continuousAt hΩ_nhds
    · filter_upwards [hΩ_nhds] with z hz using (h_eq_on_Ω z hz).symm
  · have hy_Kc : y ∈ (Kᶜ : Set EuclN) := by
      intro hy_K
      exact hy_Ω (hK_in_Ω hy_K)
    have hKc_nhds : (Kᶜ : Set EuclN) ∈ 𝓝 y := hKc_open.mem_nhds hy_Kc
    have h_eq_zero_on_Kc : ∀ z ∈ (Kᶜ : Set EuclN),
        chartPushedRaw (I := I) (M := M) α f z = 0 := by
      intro z hz
      exact chartPushedRaw_smooth_eq_zero_off_image_tsupport
        (I := I) (M := M) (f := f) (α := α) hz
    refine ContinuousAt.congr (f := fun _ : EuclN => (0 : ℝ)) ?_ ?_
    · exact continuousAt_const
    · filter_upwards [hKc_nhds] with z hz using (h_eq_zero_on_Kc z hz).symm

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
private lemma chartPushedRaw_smooth_memLp
    {α : M} {f : M → ℝ}
    (hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_support : tsupport f ⊆ (chartAt H α).source)
    (p : ℝ≥0∞) :
    MemLp (chartPushedRaw (I := I) (M := M) α f) p
      ((volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have hcont : Continuous (chartPushedRaw (I := I) (M := M) α f) :=
    chartPushedRaw_smooth_continuous (I := I) (M := M)
      (f := f) (α := α) hf_smooth hf_support
  have hcompact : HasCompactSupport (chartPushedRaw (I := I) (M := M) α f) :=
    chartPushedRaw_smooth_hasCompactSupport
      (I := I) (M := M) (f := f) (α := α) hf_support
  have hmemLp_full : MemLp (chartPushedRaw (I := I) (M := M) α f) p
      (volume : Measure EuclN) :=
    hcont.memLp_of_hasCompactSupport (μ := volume) hcompact
  exact hmemLp_full.restrict _

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
theorem memW1p_chartPushedRaw_of_contMDiff_tsupport
    {α : M} {f : M → ℝ}
    (hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_support : tsupport f ⊆ (chartAt H α).source)
    (p : ℝ≥0∞) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) p
      (chartPushedRaw (I := I) (M := M) α f)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  refine ⟨?_, ?_⟩
  · exact chartPushedRaw_smooth_memLp (I := I) (M := M)
      (f := f) (α := α) hf_smooth hf_support p
  · intro i
    set Λ : EuclN → ℝ := chartPushedRaw (I := I) (M := M) α f with hΛ_def
    set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
    set K : Set EuclN :=
      (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f)) with hK_def
    have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
    have hK_compact : IsCompact K := by
      refine IsCompact.image ?_ (toEuclidean (E := E)).continuous
      have h_tsupp_compact : IsCompact (tsupport f) :=
        (isClosed_tsupport _).isCompact
      have h_cont : ContinuousOn (extChartAt I α) (tsupport f) := by
        apply (continuousOn_extChartAt (I := I) α).mono
        intro x hx
        have hsrc : x ∈ (chartAt H α).source := hf_support hx
        rw [← CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
          (I := I) (M := M)] at hsrc
        exact hsrc
      exact h_tsupp_compact.image_of_continuousOn h_cont
    have hKc_open : IsOpen (Kᶜ : Set EuclN) := hK_compact.isClosed.isOpen_compl
    have hK_in_Ω : K ⊆ Ω := by
      intro y hy
      rcases hy with ⟨z, hz, hzy⟩
      rcases hz with ⟨x, hx_support, hxz⟩
      have hxsrc : x ∈ (chartAt H α).source := hf_support hx_support
      rw [hΩ_def, chartTargetEuclid]
      refine ⟨z, ?_, hzy⟩
      rw [← hxz]
      have : x ∈ (extChartAt I α).source := by
        rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
          (I := I) (M := M)]
        exact hxsrc
      exact (extChartAt I α).map_source this
    have hΛ_smooth : ContDiff ℝ ∞ Λ := by
      rw [contDiff_iff_contDiffAt]
      intro y
      by_cases hy_Ω : y ∈ Ω
      · have hΩ_nhds : Ω ∈ 𝓝 y := hΩ_open.mem_nhds hy_Ω
        have h_eq_on_Ω : ∀ z ∈ Ω, Λ z =
            f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) := by
          intro z hz
          exact chartPushedRaw_apply_of_mem (I := I) (M := M) α f hz
        have h_smooth_form : ContDiffOn ℝ ∞
            (fun z : EuclN => f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)))
            Ω := by
          have hscalar : ContDiffOn ℝ ∞
              (fun z : E => f ((extChartAt I α).symm z))
              (extChartAt I α).target :=
            CalabiYau.DivergenceTheorem.scalarOnE_contDiffOn
              (I := I) α hf_smooth
          have htoEuc_smooth : ContDiff ℝ ∞ ((toEuclidean (E := E)).symm) :=
            ContinuousLinearEquiv.contDiff _
          have hmaps : Set.MapsTo ((toEuclidean (E := E)).symm) Ω (extChartAt I α).target := by
            intro z hz
            rw [hΩ_def, chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hz
            exact hz
          exact hscalar.comp htoEuc_smooth.contDiffOn hmaps
        have h_smooth_at : ContDiffAt ℝ ∞
            (fun z : EuclN => f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))) y := by
          exact (h_smooth_form y hy_Ω).contDiffAt (hΩ_open.mem_nhds hy_Ω)
        apply h_smooth_at.congr_of_eventuallyEq
        filter_upwards [hΩ_nhds] with z hz using h_eq_on_Ω z hz
      · have hy_Kc : y ∈ (Kᶜ : Set EuclN) := fun hy_K => hy_Ω (hK_in_Ω hy_K)
        have hKc_nhds : (Kᶜ : Set EuclN) ∈ 𝓝 y := hKc_open.mem_nhds hy_Kc
        refine ContDiffAt.congr_of_eventuallyEq (f := fun _ : EuclN => (0 : ℝ))
          contDiffAt_const ?_
        filter_upwards [hKc_nhds] with z hz
        exact chartPushedRaw_smooth_eq_zero_off_image_tsupport
          (I := I) (M := M) (f := f) (α := α) hz
    have hΛ_compact : HasCompactSupport Λ :=
      chartPushedRaw_smooth_hasCompactSupport
        (I := I) (M := M) (f := f) (α := α) hf_support
    have hΛ_smooth_top : ContDiff ℝ (⊤ : ℕ∞) Λ := hΛ_smooth
    have hΛ_smooth_C1 : ContDiff ℝ 1 Λ := hΛ_smooth.of_le (by norm_cast)
    have hw_univ : DeGiorgi.MemW1pWitness (d := Module.finrank ℝ E) p Λ Set.univ :=
      DeGiorgi.MemW1pWitness.ofContDiffHasCompactSupport (p := p) hΛ_smooth_top hΛ_compact
    have hw_chart : DeGiorgi.MemW1pWitness (d := Module.finrank ℝ E) p Λ
        (chartTargetEuclid (I := I) (M := M) α) :=
      hw_univ.restrict (chartTargetEuclid_isOpen (I := I) (M := M) α)
        (Set.subset_univ _)
    refine ⟨fun x => hw_chart.weakGrad x i,
      hw_chart.weakGrad_component_memLp i, hw_chart.isWeakGrad i⟩

noncomputable def fHLeibnizResidualSmoothRep
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) : M → ℝ :=
  fun x : M =>
    -((2 : ℝ) * g.inner x (gradFun (I := I) g
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x)
      (gradFun (I := I) g v.toFun x)) -
    (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x * v.toFun x

omit [NeZero (Module.finrank ℝ E)] in
lemma fHLeibnizResidualSmoothRep_contMDiff
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fHLeibnizResidualSmoothRep (I := I) (M := M) g α v) := by
  classical
  unfold fHLeibnizResidualSmoothRep
  have h_inner : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g.inner x (gradFun (I := I) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x)
        (gradFun (I := I) g v.toFun x)) := by
    have hα_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff
    let rhoMap : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯ :=
      ⟨(chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯), hα_smooth⟩
    let vMap : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯ := ⟨v.toFun, v.smooth⟩
    have h := CalabiYau.Riemannian.contMDiff_g_inner_of_smooth_sections
      (I := I) (M := M) g
      (CalabiYau.Riemannian.gradG (I := I) g rhoMap)
      (CalabiYau.Riemannian.gradG (I := I) g vMap)
    refine h.congr (fun x => ?_)
    rw [CalabiYau.Riemannian.grad_g_apply,
      CalabiYau.Riemannian.grad_g_apply]
    congr 1
  have h_piece1 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => -((2 : ℝ) * g.inner x (gradFun (I := I) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x)
        (gradFun (I := I) g v.toFun x))) := by
    have h_two : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => (2 : ℝ)) := contMDiff_const
    have h_mul : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => (2 : ℝ) * g.inner x (gradFun (I := I) g
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x)
          (gradFun (I := I) g v.toFun x)) := h_two.mul h_inner
    exact h_mul.neg
  have h_piece2 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x * v.toFun x) :=
    (laplacianOfChartPOU (I := I) (M := M) g α).contMDiff.mul v.smooth
  exact h_piece1.sub h_piece2

omit [NeZero (Module.finrank ℝ E)] in
lemma fHLeibnizResidualSmoothRep_tsupport_subset
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    tsupport (fHLeibnizResidualSmoothRep (I := I) (M := M) g α v) ⊆
      (chartAt H α).source := by
  classical
  have h_support_subset : Function.support
      (fHLeibnizResidualSmoothRep (I := I) (M := M) g α v) ⊆
      tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
    intro x hx_support
    by_contra hx_off
    apply hx_support
    have h_open : IsOpen
        (tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))ᶜ :=
      (isClosed_tsupport _).isOpen_compl
    have h_ev : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) =ᶠ[𝓝 x]
        (fun _ : M => (0 : ℝ)) := by
      filter_upwards [h_open.mem_nhds hx_off] with y hy
      by_contra hne
      exact hy (subset_tsupport _ hne)
    have h_grad_zero : gradFun (I := I) g
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0 :=
      gradFun_eq_zero_of_eventuallyEq_zero (I := I) g h_ev
    have h_lap_zero : (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x = 0 := by
      rw [laplacianOfChartPOU_apply]
      rw [Δ_g_def]
      have h_grad_ev : ∀ᶠ y in 𝓝 x,
          (CalabiYau.Riemannian.gradG (I := I) g
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) y =
          (0 : TangentSpace I y) := by
        filter_upwards [h_open.mem_nhds hx_off] with y hy
        have h_y_ev : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) =ᶠ[𝓝 y]
            (fun _ : M => (0 : ℝ)) := by
          filter_upwards [h_open.mem_nhds hy] with z hz
          by_contra hne
          exact hz (subset_tsupport _ hne)
        have h_g := gradFun_eq_zero_of_eventuallyEq_zero (I := I) g h_y_ev
        rw [CalabiYau.Riemannian.grad_g_apply]
        exact h_g
      exact CalabiYau.DivergenceTheorem.divergence_g_zero_of_eventuallyEq_zero
        (I := I) g _ h_grad_ev
    change fHLeibnizResidualSmoothRep (I := I) (M := M) g α v x = 0
    unfold fHLeibnizResidualSmoothRep
    rw [h_grad_zero, h_lap_zero]
    simp
  have h_tsupp_subset : tsupport
      (fHLeibnizResidualSmoothRep (I := I) (M := M) g α v) ⊆
      tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
    closure_minimal h_support_subset (isClosed_tsupport _)
  exact h_tsupp_subset.trans
    (CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M α)

omit [NeZero (Module.finrank ℝ E)] in
theorem memW1p_chartPushedRaw_fHLeibnizResidualSmoothRep
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (chartPushedRaw (I := I) (M := M) α
        (fHLeibnizResidualSmoothRep (I := I) (M := M) g α v))
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_smooth := fHLeibnizResidualSmoothRep_contMDiff (I := I) (M := M) g α v
  have h_support := fHLeibnizResidualSmoothRep_tsupport_subset (I := I) (M := M) g α v
  exact memW1p_chartPushedRaw_of_contMDiff_tsupport
    (I := I) (M := M) (f := fHLeibnizResidualSmoothRep (I := I) (M := M) g α v)
    (α := α) h_smooth h_support 2

omit [NeZero (Module.finrank ℝ E)] in
theorem fHLeibnizResidualLp_smoothToH1Compl_coeFn_ae
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    ((CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
        (I := I) (M := M) g α
        (smoothToH1Compl (I := I) (M := M) g v) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      fHLeibnizResidualSmoothRep (I := I) (M := M) g α v := by
  classical
  set ρα : C^∞⟮I, M; ℝ⟯ := chartAtlasPOU I M α
  set Δρα : C^∞⟮I, M; ℝ⟯ := laplacianOfChartPOU (I := I) (M := M) g α
  have h_gradInnerCLM_smooth :
      gradInnerCLM (I := I) (M := M) g ρα
          (smoothToH1Compl (I := I) (M := M) g v) =
        gradInnerSmooth (I := I) (M := M) g ρα v :=
    gradInnerCLM_smoothToH1Compl (I := I) (M := M) g ρα v
  have h_H1ComplToLp_smooth :
      H1ComplToLp (I := I) (M := M) g
          (smoothToH1Compl (I := I) (M := M) g v) =
        smoothToLp (I := I) (M := M) g v :=
    H1ComplToLp_smoothToH1Compl (I := I) (M := M) g v
  have h_lp_eq :
      CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
          (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g v) =
        -((2 : ℝ) • gradInnerSmooth (I := I) (M := M) g ρα v) -
          smoothMulLp (I := I) (M := M) g Δρα
            (smoothToLp (I := I) (M := M) g v) := by
    unfold CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
    rw [h_gradInnerCLM_smooth, h_H1ComplToLp_smooth]
  rw [h_lp_eq]
  have h_grad_coeFn := gradInnerSmooth_coeFn (I := I) (M := M) g ρα v
  have h_smoothMul_coeFn :=
    smoothMulLp_apply_coeFn (I := I) (M := M) g Δρα
      (smoothToLp (I := I) (M := M) g v)
  have h_smoothToLp_coeFn :
      (smoothToLp (I := I) (M := M) g v :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g] v.toFun :=
    MemLp.coeFn_toLp v.memLp_two
  have h_sub_coe :
      (((-((2 : ℝ) • gradInnerSmooth (I := I) (M := M) g ρα v) -
          smoothMulLp (I := I) (M := M) g Δρα
            (smoothToLp (I := I) (M := M) g v)) :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g]
        fun x : M =>
          ((-((2 : ℝ) • gradInnerSmooth (I := I) (M := M) g ρα v) :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x -
          ((smoothMulLp (I := I) (M := M) g Δρα
              (smoothToLp (I := I) (M := M) g v) :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x :=
    MeasureTheory.Lp.coeFn_sub _ _
  have h_neg_coe :
      ((-((2 : ℝ) • gradInnerSmooth (I := I) (M := M) g ρα v) :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g]
        fun x : M => -(((((2 : ℝ) • gradInnerSmooth (I := I) (M := M) g ρα v) :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) x :=
    MeasureTheory.Lp.coeFn_neg _
  have h_smul_coe :
      ((((2 : ℝ) • gradInnerSmooth (I := I) (M := M) g ρα v) :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g]
        (2 : ℝ) • ((gradInnerSmooth (I := I) (M := M) g ρα v :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
    MeasureTheory.Lp.coeFn_smul _ _
  filter_upwards [h_sub_coe, h_neg_coe, h_smul_coe, h_grad_coeFn,
    h_smoothMul_coeFn, h_smoothToLp_coeFn] with x hx_sub hx_neg hx_smul hx_grad
    hx_smoothMul hx_smoothToLp
  rw [hx_sub]
  rw [hx_neg]
  rw [hx_smul]
  rw [hx_smoothMul]
  rw [hx_smoothToLp]
  unfold fHLeibnizResidualSmoothRep
  simp only [Pi.smul_apply, smul_eq_mul, hx_grad]
  ring

omit [NeZero (Module.finrank ℝ E)] in
theorem memW1p_fChartResidual_smoothToH1Compl
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
        (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g v))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_lp_ae := fHLeibnizResidualLp_smoothToH1Compl_coeFn_ae
    (I := I) (M := M) g α v
  have h_fChart_ae := chartPushedRawLpFromLp_coeFn
    (I := I) (M := M) g α
    (CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
      (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g v))
  have h_lp_meas : Measurable
      ((CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
          (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g v) :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
    exact (Lp.stronglyMeasurable _).measurable
  have h_rep_meas : Measurable
      (fHLeibnizResidualSmoothRep (I := I) (M := M) g α v) := by
    have h := fHLeibnizResidualSmoothRep_contMDiff (I := I) (M := M) g α v
    exact h.continuous.measurable
  have h_chartPushed_lp_ae :=
    CalabiYau.Analysis.Laplacian.LaplacianDomainChartData.chartPushedRaw_aeEq_of_aeEq
      (I := I) (M := M) g α h_lp_meas h_rep_meas h_lp_ae
  have h_fChart_smooth_ae :
      CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
          (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g v) =ᵐ[
          (chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)]
        chartPushedRaw (I := I) (M := M) α
          (fHLeibnizResidualSmoothRep (I := I) (M := M) g α v) := by
    unfold CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
    exact h_fChart_ae.trans h_chartPushed_lp_ae
  have h_vol_abs_weighted : (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α) ≪
      (chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α) := by
    intro A hA
    have h_chartTarget_meas : MeasurableSet
        (chartTargetEuclid (I := I) (M := M) α) :=
      (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
    unfold chartPulledWeightedMeasure at hA
    rw [show ((volume : Measure EuclN).withDensity
        (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))).restrict
        (chartTargetEuclid (I := I) (M := M) α) =
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)).withDensity
          (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
      from MeasureTheory.restrict_withDensity h_chartTarget_meas _] at hA
    rw [MeasureTheory.withDensity_apply_eq_zero'
      (μ := (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α))
      (f := fun y : EuclN => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
      (ENNReal.measurable_ofReal.comp_aemeasurable
        ((densityOnEuclid_continuousOn (I := I) g α).aemeasurable h_chartTarget_meas))]
      at hA
    rw [Measure.restrict_apply' h_chartTarget_meas]
    rw [Measure.restrict_apply' h_chartTarget_meas] at hA
    refine MeasureTheory.measure_mono_null ?_ hA
    intro y ⟨hy_A, hy_chart⟩
    refine ⟨⟨?_, hy_A⟩, hy_chart⟩
    have h_pos : 0 < densityOnEuclid (I := I) g α y :=
      densityOnEuclid_pos (I := I) g α hy_chart
    exact (ENNReal.ofReal_pos.mpr h_pos).ne'
  have h_fChart_smooth_ae_vol :
      CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
          (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g v) =ᵐ[
          (volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)]
        chartPushedRaw (I := I) (M := M) α
          (fHLeibnizResidualSmoothRep (I := I) (M := M) g α v) :=
    h_vol_abs_weighted.ae_le h_fChart_smooth_ae
  have h_smooth_w1p :=
    memW1p_chartPushedRaw_fHLeibnizResidualSmoothRep (I := I) (M := M) g α v
  exact (_root_.Sobolev.Euclidean.MemW1p_congr_ae
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    h_fChart_smooth_ae_vol.symm).mp h_smooth_w1p

end DiffChartBilinearH1ComplResidualMemW1p
end Laplacian
end Analysis
end CalabiYau

end
