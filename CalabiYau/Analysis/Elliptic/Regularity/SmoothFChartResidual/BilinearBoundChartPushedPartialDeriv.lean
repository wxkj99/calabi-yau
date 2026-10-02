-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/SmoothFChartResidual/BilinearBoundChartPushedPartialDeriv.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplResidual
public import CalabiYau.Analysis.Elliptic.Regularity.GradInner.CLM.ChartFormula
public import CalabiYau.Analysis.Sobolev.Chart.SmoothDensity.StrictCutoffPushforwardBound
public import CalabiYau.Analysis.Sobolev.Chart.SmoothDensity.SmoothMul
public import CalabiYau.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuantK
public import CalabiYau.Analysis.Sobolev.Manifold.Morrey.HigherOrder
public import CalabiYau.Analysis.Sobolev.Manifold.Embedding.Iterated

@[expose] public section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace CalabiYau
namespace Analysis
namespace Laplacian
namespace SmoothFChartResidualBilinearBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.LaplacianDomainChartData
open CalabiYau.Analysis.Laplacian.DiffChartBilinearH1ComplResidual
open CalabiYau.Analysis.Laplacian.GradInnerCLMChartFormula
open CalabiYau.Analysis.Sobolev.Chart
open _root_.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))


section ChartDirectionPartialBound

variable [IsManifold I ∞ M] in
variable [CompactSpace M] [I.Boundaryless] in
private def euclSupport (α : M) (u : M → ℝ) : Set EuclN :=
  (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport u))

variable [CompactSpace M] in
private lemma euclSupport_isCompact {α : M} {u : M → ℝ}
    (hu_support : tsupport u ⊆ (chartAt H α).source) :
    IsCompact (euclSupport (I := I) (M := M) α u) := by
  classical
  refine IsCompact.image ?_ (toEuclidean (E := E)).continuous
  have h_tsupp_compact : IsCompact (tsupport u) := (isClosed_tsupport _).isCompact
  have h_cont_on : ContinuousOn (extChartAt I α) (tsupport u) := by
    refine (continuousOn_extChartAt (I := I) α).mono ?_
    intro x hx
    have hsrc : x ∈ (chartAt H α).source := hu_support hx
    rw [← extChartAt_source_eq_chartAt_source (I := I) (M := M)] at hsrc
    exact hsrc
  exact h_tsupp_compact.image_of_continuousOn h_cont_on

private lemma euclSupport_subset_chartTargetEuclid {α : M} {u : M → ℝ}
    (hu_support : tsupport u ⊆ (chartAt H α).source) :
    euclSupport (I := I) (M := M) α u ⊆ chartTargetEuclid (I := I) (M := M) α := by
  intro y hy
  rcases hy with ⟨z, ⟨x, hx_support, hxz⟩, hzy⟩
  have hxsrc : x ∈ (chartAt H α).source := hu_support hx_support
  have hx_ext : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I) (M := M)]; exact hxsrc
  have hz_target : z ∈ (extChartAt I α).target := by
    rw [← hxz]; exact (extChartAt I α).map_source hx_ext
  exact ⟨z, hz_target, hzy⟩

private lemma chartPushedRaw_eq_zero_off_euclSupport {α : M} {u : M → ℝ}
    {y : EuclN} (hy : y ∉ euclSupport (I := I) (M := M) α u) :
    chartPushedRaw (I := I) (M := M) α u y = 0 := by
  classical
  by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
  · exact _root_.Sobolev.Chart.chartPushedRaw_eq_zero_off_image_tsupport
      (I := I) (M := M) (u := u) α hy_target hy
  · exact chartPushedRaw_apply_of_notMem (I := I) (M := M) α u hy_target

section

variable [CompactSpace M]

lemma chartPushedRaw_smooth_hasCompactSupport_local
    {α : M} {u : M → ℝ} (hu_support : tsupport u ⊆ (chartAt H α).source) :
    HasCompactSupport (chartPushedRaw (I := I) (M := M) α u) := by
  classical
  apply HasCompactSupport.of_support_subset_isCompact
    (euclSupport_isCompact (I := I) (M := M) (α := α) (u := u) hu_support)
  intro y hy_support
  by_contra hy_off
  exact hy_support
    (chartPushedRaw_eq_zero_off_euclSupport (I := I) (M := M)
      (α := α) (u := u) hy_off)

lemma tsupport_chartPushedRaw_subset_chartTargetEuclid
    {α : M} {u : M → ℝ} (hu_support : tsupport u ⊆ (chartAt H α).source) :
    tsupport (chartPushedRaw (I := I) (M := M) α u) ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  have h_support_sub : Function.support (chartPushedRaw (I := I) (M := M) α u) ⊆
      euclSupport (I := I) (M := M) α u := by
    intro y hy
    by_contra hy_off
    exact hy
      (chartPushedRaw_eq_zero_off_euclSupport (I := I) (M := M)
        (α := α) (u := u) hy_off)
  have h_cl : tsupport (chartPushedRaw (I := I) (M := M) α u) ⊆
      euclSupport (I := I) (M := M) α u :=
    closure_minimal h_support_sub
      (euclSupport_isCompact (I := I) (M := M) (α := α) (u := u)
        hu_support).isClosed
  exact h_cl.trans
    (euclSupport_subset_chartTargetEuclid (I := I) (M := M)
      (α := α) (u := u) hu_support)

end

variable [IsManifold I ∞ M] in
variable [CompactSpace M] [I.Boundaryless] in
lemma chartPushedRaw_contDiff
    {α : M} {u : M → ℝ}
    (hu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (hu_support : tsupport u ⊆ (chartAt H α).source) :
    ContDiff ℝ ∞ (chartPushedRaw (I := I) (M := M) α u) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set K : Set EuclN := euclSupport (I := I) (M := M) α u with hK_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hK_compact : IsCompact K :=
    euclSupport_isCompact (I := I) (M := M) (α := α) (u := u) hu_support
  have hKc_open : IsOpen (Kᶜ : Set EuclN) := hK_compact.isClosed.isOpen_compl
  have hK_in_Ω : K ⊆ Ω :=
    euclSupport_subset_chartTargetEuclid (I := I) (M := M)
      (α := α) (u := u) hu_support
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy_Ω : y ∈ Ω
  · have hΩ_nhds : Ω ∈ 𝓝 y := hΩ_open.mem_nhds hy_Ω
    have h_eq_on_Ω : ∀ z ∈ Ω, chartPushedRaw (I := I) (M := M) α u z =
        u ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) := fun z hz =>
      chartPushedRaw_apply_of_mem (I := I) (M := M) α u hz
    have h_smooth_form : ContDiffOn ℝ ∞
        (fun z : EuclN => u ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))) Ω := by
      have hscalar : ContDiffOn ℝ ∞ (scalarOnE (I := I) α u)
          (extChartAt I α).target :=
        CalabiYau.DivergenceTheorem.scalarOnE_contDiffOn
          (I := I) α hu_smooth
      have htoEuc_smooth : ContDiff ℝ ∞ ((toEuclidean (E := E)).symm) :=
        ContinuousLinearEquiv.contDiff _
      have hmaps : Set.MapsTo ((toEuclidean (E := E)).symm) Ω
          (extChartAt I α).target := by
        intro z hz
        rw [hΩ_def, chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hz
        exact hz
      exact hscalar.comp htoEuc_smooth.contDiffOn hmaps
    have h_smooth_at : ContDiffAt ℝ ∞
        (fun z : EuclN => u ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))) y :=
      (h_smooth_form y hy_Ω).contDiffAt hΩ_nhds
    apply h_smooth_at.congr_of_eventuallyEq
    filter_upwards [hΩ_nhds] with z hz using h_eq_on_Ω z hz
  · have hy_Kc : y ∈ (Kᶜ : Set EuclN) := fun hy_K => hy_Ω (hK_in_Ω hy_K)
    have hKc_nhds : (Kᶜ : Set EuclN) ∈ 𝓝 y := hKc_open.mem_nhds hy_Kc
    refine ContDiffAt.congr_of_eventuallyEq (f := fun _ : EuclN => (0 : ℝ))
      contDiffAt_const ?_
    filter_upwards [hKc_nhds] with z hz
    exact chartPushedRaw_eq_zero_off_euclSupport (I := I) (M := M)
      (α := α) (u := u) hz

variable [IsManifold I ∞ M] in
variable [I.Boundaryless] in
private lemma partialDerivOnEuclid_eq_fderiv_chartPushedRaw_apply_single
    {α : M} (i : Fin (Module.finrank ℝ E))
    {u : M → ℝ}
    (hu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (_hu_support : tsupport u ⊆ (chartAt H α).source)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    partialDerivOnEuclid (I := I) (M := M) α i u y =
      fderiv ℝ (chartPushedRaw (I := I) (M := M) α u) y
        (EuclideanSpace.single i (1 : ℝ)) := by
  classical
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hΩ_nhds : chartTargetEuclid (I := I) (M := M) α ∈ 𝓝 y :=
    hΩ_open.mem_nhds hy
  have hsymm_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy; exact hy
  have h_target_open : IsOpen (extChartAt I α).target :=
    isOpen_extChartAt_target (I := I) α
  have h_target_nhds : (extChartAt I α).target ∈ 𝓝
      ((toEuclidean (E := E)).symm y) :=
    h_target_open.mem_nhds hsymm_target
  have h_eqf : (chartPushedRaw (I := I) (M := M) α u) =ᶠ[𝓝 y]
      (fun z : EuclN => scalarOnE (I := I) α u ((toEuclidean (E := E)).symm z)) := by
    filter_upwards [hΩ_nhds] with z hz
    rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α u hz]
    rfl
  have h_scalar_contDiffOn : ContDiffOn ℝ ∞ (scalarOnE (I := I) α u)
      (extChartAt I α).target :=
    CalabiYau.DivergenceTheorem.scalarOnE_contDiffOn
      (I := I) α hu_smooth
  have h_scalar_diffAt : DifferentiableAt ℝ (scalarOnE (I := I) α u)
      ((toEuclidean (E := E)).symm y) := by
    have h_at : ContDiffAt ℝ ∞ (scalarOnE (I := I) α u)
        ((toEuclidean (E := E)).symm y) :=
      (h_scalar_contDiffOn.contDiffWithinAt hsymm_target).contDiffAt h_target_nhds
    exact h_at.differentiableAt (by simp)
  have h_TE_symm_diffAt : DifferentiableAt ℝ
      (fun z : EuclN => (toEuclidean (E := E)).symm z) y :=
    ((toEuclidean (E := E)).symm).differentiable.differentiableAt
  have h_comp_fderiv :
      fderiv ℝ (fun z : EuclN => scalarOnE (I := I) α u
          ((toEuclidean (E := E)).symm z)) y =
        (fderiv ℝ (scalarOnE (I := I) α u)
          ((toEuclidean (E := E)).symm y)).comp
          (fderiv ℝ (fun z : EuclN => (toEuclidean (E := E)).symm z) y) :=
    fderiv_comp y h_scalar_diffAt h_TE_symm_diffAt
  have h_TE_symm_fderiv :
      fderiv ℝ (fun z : EuclN => (toEuclidean (E := E)).symm z) y =
        ((toEuclidean (E := E)).symm : EuclN →L[ℝ] E) :=
    ((toEuclidean (E := E)).symm).fderiv
  have h_fderiv_chartPushedRaw :
      fderiv ℝ (chartPushedRaw (I := I) (M := M) α u) y =
        (fderiv ℝ (scalarOnE (I := I) α u)
          ((toEuclidean (E := E)).symm y)).comp
          ((toEuclidean (E := E)).symm : EuclN →L[ℝ] E) := by
    rw [h_eqf.fderiv_eq, h_comp_fderiv, h_TE_symm_fderiv]
  rw [h_fderiv_chartPushedRaw]
  have h_basis : (toEuclidean (E := E)).symm (EuclideanSpace.single i (1 : ℝ))
      = CalabiYau.Tensor.Coordinates.chartModelBasis E i := by
    rw [CalabiYau.Tensor.Coordinates.chartModelBasis_apply]
  change CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (scalarOnE (I := I) α u)
      ((toEuclidean (E := E)).symm y) =
    (fderiv ℝ (scalarOnE (I := I) α u)
        ((toEuclidean (E := E)).symm y))
      ((toEuclidean (E := E)).symm (EuclideanSpace.single i (1 : ℝ)))
  rw [h_basis]
  rfl

section

variable [IsManifold I ∞ M]
variable [CompactSpace M] [I.Boundaryless]

lemma partialDerivOnEuclid_ae_eq_chosenWeakPartial
    {α : M} (i : Fin (Module.finrank ℝ E))
    {u : M → ℝ} (hu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (hu_support : tsupport u ⊆ (chartAt H α).source)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) :
    partialDerivOnEuclid (I := I) (M := M) α i u
      =ᵐ[volume.restrict (chartTargetEuclid (I := I) (M := M) α)]
      _root_.Sobolev.Euclidean.chosenWeakPartialOrZero
        (d := Module.finrank ℝ E) p i
        (chartPushedRaw (I := I) (M := M) α u)
        (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  set Λ : EuclN → ℝ := chartPushedRaw (I := I) (M := M) α u with hΛ_def
  have hΛ_smooth : ContDiff ℝ ∞ Λ :=
    chartPushedRaw_contDiff (I := I) (M := M)
      (α := α) (u := u) hu_smooth hu_support
  have hΛ_smoothTop : ContDiff ℝ (⊤ : ℕ∞) Λ := hΛ_smooth
  have hΛ_compact : HasCompactSupport Λ :=
    chartPushedRaw_smooth_hasCompactSupport_local (I := I) (M := M)
      (α := α) (u := u) hu_support
  have hΛ_tsupp_in_Ω : tsupport Λ ⊆ Ω :=
    tsupport_chartPushedRaw_subset_chartTargetEuclid (I := I) (M := M)
      (α := α) (u := u) hu_support
  have hΛ_W1 : _root_.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 p Λ Ω :=
    _root_.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hΩ_open hΛ_smoothTop hΛ_compact
      hΛ_tsupp_in_Ω hp_one 1
  have hΛ_W1p : Sobolev.Euclidean.MemW1p (d := Module.finrank ℝ E) p Λ Ω :=
    _root_.Sobolev.Euclidean.MemWkp.one_iff_memW1p.mp
      hΛ_W1
  have h_chosen_ae :=
    _root_.Sobolev.Euclidean.chosenWeakPartial_smooth_ae_eq
      (d := Module.finrank ℝ E) hp_one hΩ_open hΛ_smoothTop hΛ_W1p i
  have h_pointwise : ∀ y ∈ Ω,
      partialDerivOnEuclid (I := I) (M := M) α i u y =
        (fderiv ℝ Λ y) (EuclideanSpace.single i (1 : ℝ)) := fun y hy =>
    partialDerivOnEuclid_eq_fderiv_chartPushedRaw_apply_single
      (I := I) (M := M) (α := α) (i := i)
      (u := u) hu_smooth hu_support hy
  have h_pointwise_ae : partialDerivOnEuclid (I := I) (M := M) α i u
      =ᵐ[volume.restrict Ω]
      (fun y => (fderiv ℝ Λ y) (EuclideanSpace.single i (1 : ℝ))) := by
    refine (ae_restrict_iff' hΩ_open.measurableSet).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy
    exact h_pointwise y hy
  exact h_pointwise_ae.trans h_chosen_ae.symm

theorem wkpNorm_partialDerivOnEuclid_le_wkpNorm_chartPushedRaw_succ
    (α : M) (i : Fin (Module.finrank ℝ E))
    (k : ℕ) {p : ℝ≥0∞} (hp_one : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {u : M → ℝ},
      ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
      tsupport u ⊆ (chartAt H α).source →
      _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p
        (partialDerivOnEuclid (I := I) (M := M) α i u)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal C *
        _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) (k+1) p
          (chartPushedRaw (I := I) (M := M) α u)
          (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  refine ⟨(1 : ℝ), by norm_num, ?_⟩
  intro u hu_smooth hu_support
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_ae := partialDerivOnEuclid_ae_eq_chosenWeakPartial (I := I) (M := M)
    (α := α) (i := i) (u := u) hu_smooth hu_support (p := p) hp_one
  rw [_root_.Sobolev.Euclidean.wkpNorm_congr_ae
        (d := Module.finrank ℝ E) hp_one hΩ_open h_ae]
  have h_bound :=
    _root_.Sobolev.Euclidean.wkpNorm_chosenWeakPartial_le_wkpNorm_succ
      (d := Module.finrank ℝ E) k (p := p) (Ω := Ω)
      (chartPushedRaw (I := I) (M := M) α u) i
  have h_one : ENNReal.ofReal (1 : ℝ) = (1 : ℝ≥0∞) := by
    simp
  rw [h_one, one_mul]
  exact h_bound

end

end ChartDirectionPartialBound

end SmoothFChartResidualBilinearBound
end Laplacian
end Analysis
end CalabiYau

end
