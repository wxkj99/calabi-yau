-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Integration/DivergenceTheorem/Local/IntegrationByParts.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Local.Formula
public import CalabiYau.Geometry.Riemannian.Operator.DirectionalDerivative
public import CalabiYau.Geometry.Riemannian.Volume.Family.Basic
public import CalabiYau.Mathlib.Geometry.Manifold.PartitionOfUnity.CompactSupport
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.Algebra.Support

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace CalabiYau.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type*} [TopologicalSpace M]

open CalabiYau.RiemannianVolume

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Module.Finite ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in
private def chartImageOfTsupport (α : M) (φ : M → ℝ) : Set E :=
  (extChartAt I α) '' tsupport φ

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
private lemma chartImageOfTsupport_isCompact
    (α : M) {φ : M → ℝ}
    (hφ_compactSupport : HasCompactSupport φ)
    (hφ_support : tsupport φ ⊆ (chartAt H α).source) :
    IsCompact (chartImageOfTsupport (I := I) α φ) := by
  unfold chartImageOfTsupport
  have hcontOn : ContinuousOn (extChartAt I α) (tsupport φ) := by
    refine (continuousOn_extChartAt (I := I) α).mono ?_
    intro x hx
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hφ_support hx
  exact (hφ_compactSupport : IsCompact (tsupport φ)).image_of_continuousOn hcontOn

private lemma chartImageOfTsupport_subset_target
    (α : M) {φ : M → ℝ}
    (hφ_support : tsupport φ ⊆ (chartAt H α).source) :
    chartImageOfTsupport (I := I) α φ ⊆ (extChartAt I α).target := by
  intro y hy
  rcases hy with ⟨x, hxsupp, hxy⟩
  have hxsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hφ_support hxsupp
  have : (extChartAt I α) x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hxsrc
  rwa [hxy] at this

private lemma chartImageOfTsupport_isClosed
    (α : M) {φ : M → ℝ}
    (hφ_compactSupport : HasCompactSupport φ)
    (hφ_support : tsupport φ ⊆ (chartAt H α).source) :
    IsClosed (chartImageOfTsupport (I := I) α φ) :=
  (chartImageOfTsupport_isCompact (I := I) α hφ_compactSupport hφ_support).isClosed

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Module.Finite ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
private def vwIntegrandOnE
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y => (extChartAt I α).target.indicator
    (fun z => chartCoeffOnE (I := I) α X i z * chartDensityOnE (I := I) g α z) y

private lemma vwIntegrandOnE_apply_of_mem
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    vwIntegrandOnE (I := I) g α X i y =
      chartCoeffOnE (I := I) α X i y * chartDensityOnE (I := I) g α y :=
  Set.indicator_of_mem hy _

private lemma vwIntegrandOnE_apply_of_notMem
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∉ (extChartAt I α).target) :
    vwIntegrandOnE (I := I) g α X i y = 0 :=
  Set.indicator_of_notMem hy _

private lemma vwIntegrandOnE_contDiffOn_target
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (vwIntegrandOnE (I := I) g α X i) (extChartAt I α).target := by
  have hsmooth : ContDiffOn ℝ ∞
      (fun y : E => chartCoeffOnE (I := I) α X i y * chartDensityOnE (I := I) g α y)
      (extChartAt I α).target :=
    chartCoeffOnE_mul_chartDensityOnE_contDiffOn (I := I) g α X i
  refine hsmooth.congr ?_
  intro y hy
  rw [vwIntegrandOnE_apply_of_mem (I := I) g α X i hy]

private abbrev phiOnE (α : M) (φ : M → ℝ) : E → ℝ :=
  chartPullZero (I := I) α φ

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
private lemma phiOnE_apply_of_mem (α : M) (φ : M → ℝ) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    phiOnE (I := I) α φ y = φ ((extChartAt I α).symm y) :=
  Set.indicator_of_mem hy _

private lemma phiOnE_apply_of_notMem (α : M) (φ : M → ℝ) {y : E}
    (hy : y ∉ (extChartAt I α).target) :
    phiOnE (I := I) α φ y = 0 :=
  Set.indicator_of_notMem hy _

private lemma phiOnE_eq_scalarOnE_on_target
    (α : M) (φ : M → ℝ) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    phiOnE (I := I) α φ y = scalarOnE (I := I) α φ y := by
  rw [phiOnE_apply_of_mem (I := I) α φ hy]
  rfl

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in
private lemma phiOnE_contDiffOn_target
    (α : M) {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ) :
    ContDiffOn ℝ ∞ (phiOnE (I := I) α φ) (extChartAt I α).target := by
  have hsmooth : ContDiffOn ℝ ∞
      (scalarOnE (I := I) α φ) (extChartAt I α).target :=
    scalarOnE_contDiffOn (I := I) α hφ
  refine hsmooth.congr ?_
  intro y hy
  exact phiOnE_eq_scalarOnE_on_target (I := I) α φ hy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in
private lemma contDiff_of_smooth_on_open_zero_outside
    {U : Set E} (hU : IsOpen U) {K : Set E} (hK : IsClosed K)
    (hKU : K ⊆ U) {f : E → ℝ}
    (hf_smooth : ContDiffOn ℝ ∞ f U)
    (hf_zero : ∀ y, y ∉ K → f y = 0) :
    ContDiff ℝ ∞ f := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ U
  · exact (hf_smooth.contDiffWithinAt hy).contDiffAt (hU.mem_nhds hy)
  · have hyK : y ∉ K := fun h => hy (hKU h)
    have hKc_open : IsOpen Kᶜ := hK.isOpen_compl
    have hf_zero_on : Kᶜ ∈ 𝓝 y := hKc_open.mem_nhds hyK
    have hzero_at : ContDiffAt ℝ ∞ (fun _ : E => (0 : ℝ)) y :=
      (contDiff_const).contDiffAt
    refine hzero_at.congr_of_eventuallyEq ?_
    filter_upwards [hf_zero_on] with z hz
    exact hf_zero z hz

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
private lemma phiOnE_support_subset_chartImage
    (α : M) (φ : M → ℝ) :
    Function.support (phiOnE (I := I) α φ) ⊆ chartImageOfTsupport (I := I) α φ := by
  intro y hy
  rw [Function.mem_support] at hy
  by_cases hyT : y ∈ (extChartAt I α).target
  · rw [phiOnE_apply_of_mem (I := I) α φ hyT] at hy
    refine ⟨(extChartAt I α).symm y, ?_, ?_⟩
    · exact subset_tsupport _ hy
    · exact (extChartAt I α).right_inv hyT
  · rw [phiOnE_apply_of_notMem (I := I) α φ hyT] at hy
    exact (hy rfl).elim

private lemma phiOnE_tsupport_subset_chartImage
    (α : M) {φ : M → ℝ}
    (hφ_compactSupport : HasCompactSupport φ)
    (hφ_support : tsupport φ ⊆ (chartAt H α).source) :
    tsupport (phiOnE (I := I) α φ) ⊆ chartImageOfTsupport (I := I) α φ := by
  refine closure_minimal (phiOnE_support_subset_chartImage (I := I) α φ) ?_
  exact chartImageOfTsupport_isClosed (I := I) α hφ_compactSupport hφ_support

private lemma phiOnE_hasCompactSupport
    (α : M) {φ : M → ℝ}
    (hφ_compactSupport : HasCompactSupport φ)
    (hφ_support : tsupport φ ⊆ (chartAt H α).source) :
    HasCompactSupport (phiOnE (I := I) α φ) := by
  refine HasCompactSupport.intro
    (chartImageOfTsupport_isCompact (I := I) α hφ_compactSupport hφ_support) ?_
  intro y hy
  by_cases hyT : y ∈ (extChartAt I α).target
  · rw [phiOnE_apply_of_mem (I := I) α φ hyT]
    by_contra hne
    have : (extChartAt I α).symm y ∈ tsupport φ := subset_tsupport _ hne
    have : y ∈ chartImageOfTsupport (I := I) α φ :=
      ⟨(extChartAt I α).symm y, this, (extChartAt I α).right_inv hyT⟩
    exact hy this
  · exact phiOnE_apply_of_notMem (I := I) α φ hyT

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in
private lemma phiOnE_contDiff [I.Boundaryless]
    (α : M) {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
    (hφ_compactSupport : HasCompactSupport φ)
    (hφ_support : tsupport φ ⊆ (chartAt H α).source) :
    ContDiff ℝ ∞ (phiOnE (I := I) α φ) := by
  refine contDiff_of_smooth_on_open_zero_outside (U := (extChartAt I α).target)
    (isOpen_extChartAt_target (I := I) α)
    (K := chartImageOfTsupport (I := I) α φ)
    (chartImageOfTsupport_isClosed (I := I) α hφ_compactSupport hφ_support)
    (chartImageOfTsupport_subset_target (I := I) α hφ_support) ?_ ?_
  · exact phiOnE_contDiffOn_target (I := I) α hφ
  · intro y hy
    by_cases hyT : y ∈ (extChartAt I α).target
    · rw [phiOnE_apply_of_mem (I := I) α φ hyT]
      by_contra hne
      have : (extChartAt I α).symm y ∈ tsupport φ := subset_tsupport _ hne
      have : y ∈ chartImageOfTsupport (I := I) α φ :=
        ⟨(extChartAt I α).symm y, this, (extChartAt I α).right_inv hyT⟩
      exact hy this
    · exact phiOnE_apply_of_notMem (I := I) α φ hyT

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Module.Finite ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in
private lemma vwIntegrandOnE_differentiableOn_target [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) :
    ∀ y ∈ (extChartAt I α).target,
      DifferentiableAt ℝ (vwIntegrandOnE (I := I) g α X i) y := by
  intro y hy
  have hOpen := isOpen_extChartAt_target (I := I) α
  have h_at : ContDiffWithinAt ℝ ∞
      (vwIntegrandOnE (I := I) g α X i) (extChartAt I α).target y :=
    vwIntegrandOnE_contDiffOn_target (I := I) g α X i y hy
  exact ((h_at.contDiffAt (hOpen.mem_nhds hy)).differentiableAt (by simp))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] in
private lemma fderiv_phiOnE_eq_fderiv_scalarOnE [I.Boundaryless]
    (α : M) (φ : M → ℝ)
    {y : E} (hy : y ∈ (extChartAt I α).target) :
    fderiv ℝ (phiOnE (I := I) α φ) y =
      fderiv ℝ (scalarOnE (I := I) α φ) y := by
  have hOpen : IsOpen (extChartAt I α).target := isOpen_extChartAt_target (I := I) α
  have h_eq : phiOnE (I := I) α φ =ᶠ[𝓝 y] scalarOnE (I := I) α φ := by
    filter_upwards [hOpen.mem_nhds hy] with z hz
    exact phiOnE_eq_scalarOnE_on_target (I := I) α φ hz
  exact Filter.EventuallyEq.fderiv_eq h_eq

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Module.Finite ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in
private theorem ibp_per_index [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
    (hφ_compactSupport : HasCompactSupport φ)
    (hφ_support : tsupport φ ⊆ (chartAt H α).source)
    (i : Fin (Module.finrank ℝ E)) :
    ∫ y, vwIntegrandOnE (I := I) g α X i y *
        fderiv ℝ (phiOnE (I := I) α φ) y ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i)
        ∂(modelHaar (E := E)) =
      -∫ y, fderiv ℝ (vwIntegrandOnE (I := I) g α X i) y
            ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) *
          phiOnE (I := I) α φ y
        ∂(modelHaar (E := E)) := by
  have hphi_smooth : ContDiff ℝ ∞ (phiOnE (I := I) α φ) :=
    phiOnE_contDiff (I := I) α hφ hφ_compactSupport hφ_support
  have hphi_compactSupport : HasCompactSupport (phiOnE (I := I) α φ) :=
    phiOnE_hasCompactSupport (I := I) α hφ_compactSupport hφ_support
  have hvw_diff_on_target := vwIntegrandOnE_differentiableOn_target (I := I) g α X i
  have hphi_tsupp_in_target : tsupport (phiOnE (I := I) α φ) ⊆
      (extChartAt I α).target := by
    refine (phiOnE_tsupport_subset_chartImage (I := I) α hφ_compactSupport hφ_support).trans ?_
    exact chartImageOfTsupport_subset_target (I := I) α hφ_support
  have hvw_diff_tsupp_phi : ∀ y ∈ tsupport (phiOnE (I := I) α φ),
      DifferentiableAt ℝ (vwIntegrandOnE (I := I) g α X i) y :=
    fun y hy => hvw_diff_on_target y (hphi_tsupp_in_target hy)
  have hphi_diff : ∀ y, DifferentiableAt ℝ (phiOnE (I := I) α φ) y :=
    fun y => hphi_smooth.differentiable (by simp) |>.differentiableAt
  have hphi_diff_tsupp_vw : ∀ y ∈ tsupport (vwIntegrandOnE (I := I) g α X i),
      DifferentiableAt ℝ (phiOnE (I := I) α φ) y :=
    fun y _ => hphi_diff y
  have hvw_cont : ContinuousOn (vwIntegrandOnE (I := I) g α X i)
      (extChartAt I α).target :=
    (vwIntegrandOnE_contDiffOn_target (I := I) g α X i).continuousOn
  have hphi_cont : Continuous (phiOnE (I := I) α φ) := hphi_smooth.continuous
  have hvw_cont_on_tsupp : ContinuousOn (vwIntegrandOnE (I := I) g α X i)
      (tsupport (phiOnE (I := I) α φ)) :=
    hvw_cont.mono hphi_tsupp_in_target
  have : IsFiniteMeasureOnCompacts (modelHaar (E := E)) := by infer_instance
  have hI1_smooth : ContDiff ℝ ∞
      (fun y => vwIntegrandOnE (I := I) g α X i y * phiOnE (I := I) α φ y) := by
    refine contDiff_of_smooth_on_open_zero_outside (U := (extChartAt I α).target)
      (isOpen_extChartAt_target (I := I) α)
      (K := chartImageOfTsupport (I := I) α φ)
      (chartImageOfTsupport_isClosed (I := I) α hφ_compactSupport hφ_support)
      (chartImageOfTsupport_subset_target (I := I) α hφ_support) ?_ ?_
    · exact (vwIntegrandOnE_contDiffOn_target (I := I) g α X i).mul
        ((phiOnE_contDiff (I := I) α hφ hφ_compactSupport hφ_support).contDiffOn)
    · intro y hy
      have hphi_zero : phiOnE (I := I) α φ y = 0 := by
        by_cases hyT : y ∈ (extChartAt I α).target
        · rw [phiOnE_apply_of_mem (I := I) α φ hyT]
          by_contra hne
          have : (extChartAt I α).symm y ∈ tsupport φ := subset_tsupport _ hne
          exact hy ⟨(extChartAt I α).symm y, this, (extChartAt I α).right_inv hyT⟩
        · exact phiOnE_apply_of_notMem (I := I) α φ hyT
      rw [hphi_zero, mul_zero]
  have hI1_compactSupport : HasCompactSupport
      (fun y => vwIntegrandOnE (I := I) g α X i y * phiOnE (I := I) α φ y) :=
    hphi_compactSupport.mul_left
  have hfg_int : Integrable
      (fun y => vwIntegrandOnE (I := I) g α X i y * phiOnE (I := I) α φ y)
      (modelHaar (E := E)) :=
    hI1_smooth.continuous.integrable_of_hasCompactSupport hI1_compactSupport
  have hI2_smooth : ContDiff ℝ ∞
      (fun y => fderiv ℝ (vwIntegrandOnE (I := I) g α X i) y
            ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) * phiOnE (I := I) α φ y) := by
    refine contDiff_of_smooth_on_open_zero_outside (U := (extChartAt I α).target)
      (isOpen_extChartAt_target (I := I) α)
      (K := chartImageOfTsupport (I := I) α φ)
      (chartImageOfTsupport_isClosed (I := I) α hφ_compactSupport hφ_support)
      (chartImageOfTsupport_subset_target (I := I) α hφ_support) ?_ ?_
    · have hvw_fderiv : ContDiffOn ℝ ∞
          (fderiv ℝ (vwIntegrandOnE (I := I) g α X i))
          (extChartAt I α).target :=
        (vwIntegrandOnE_contDiffOn_target (I := I) g α X i).fderiv_of_isOpen
          (isOpen_extChartAt_target (I := I) α) (by rw [ENat.coe_top_add_one])
      have hbasis_const : ContDiffOn ℝ ∞ (fun _ : E => (CalabiYau.Tensor.Coordinates.chartModelBasis E) i)
          (extChartAt I α).target := contDiffOn_const
      have hpartial : ContDiffOn ℝ ∞
          (fun y => fderiv ℝ (vwIntegrandOnE (I := I) g α X i) y
              ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i)) (extChartAt I α).target :=
        hvw_fderiv.clm_apply hbasis_const
      exact hpartial.mul ((phiOnE_contDiff (I := I) α hφ hφ_compactSupport hφ_support).contDiffOn)
    · intro y hy
      have hphi_zero : phiOnE (I := I) α φ y = 0 := by
        by_cases hyT : y ∈ (extChartAt I α).target
        · rw [phiOnE_apply_of_mem (I := I) α φ hyT]
          by_contra hne
          have : (extChartAt I α).symm y ∈ tsupport φ := subset_tsupport _ hne
          exact hy ⟨(extChartAt I α).symm y, this, (extChartAt I α).right_inv hyT⟩
        · exact phiOnE_apply_of_notMem (I := I) α φ hyT
      rw [hphi_zero, mul_zero]
  have hI2_compactSupport : HasCompactSupport
      (fun y => fderiv ℝ (vwIntegrandOnE (I := I) g α X i) y
            ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) * phiOnE (I := I) α φ y) :=
    hphi_compactSupport.mul_left
  have hf'g_int : Integrable
      (fun y => fderiv ℝ (vwIntegrandOnE (I := I) g α X i) y
            ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) * phiOnE (I := I) α φ y)
      (modelHaar (E := E)) :=
    hI2_smooth.continuous.integrable_of_hasCompactSupport hI2_compactSupport
  have hI3_smooth : ContDiff ℝ ∞
      (fun y => vwIntegrandOnE (I := I) g α X i y *
          fderiv ℝ (phiOnE (I := I) α φ) y ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i)) := by
    refine contDiff_of_smooth_on_open_zero_outside (U := (extChartAt I α).target)
      (isOpen_extChartAt_target (I := I) α)
      (K := chartImageOfTsupport (I := I) α φ)
      (chartImageOfTsupport_isClosed (I := I) α hφ_compactSupport hφ_support)
      (chartImageOfTsupport_subset_target (I := I) α hφ_support) ?_ ?_
    · have hphi_smooth_total : ContDiff ℝ ∞ (phiOnE (I := I) α φ) := hphi_smooth
      have hphi_fderiv_total : ContDiff ℝ ∞ (fderiv ℝ (phiOnE (I := I) α φ)) := by
        have := hphi_smooth_total.fderiv_right (m := ∞) (by rw [ENat.coe_top_add_one])
        exact this
      have hphi_fderiv : ContDiffOn ℝ ∞ (fderiv ℝ (phiOnE (I := I) α φ))
          (extChartAt I α).target := hphi_fderiv_total.contDiffOn
      have hbasis_const : ContDiffOn ℝ ∞ (fun _ : E => (CalabiYau.Tensor.Coordinates.chartModelBasis E) i)
          (extChartAt I α).target := contDiffOn_const
      have hpartial : ContDiffOn ℝ ∞
          (fun y => fderiv ℝ (phiOnE (I := I) α φ) y ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i))
          (extChartAt I α).target :=
        hphi_fderiv.clm_apply hbasis_const
      exact (vwIntegrandOnE_contDiffOn_target (I := I) g α X i).mul hpartial
    · intro y hy
      have hKc_open : IsOpen (chartImageOfTsupport (I := I) α φ)ᶜ :=
        (chartImageOfTsupport_isClosed (I := I) α hφ_compactSupport hφ_support).isOpen_compl
      have hphi_zero_on_nhd : phiOnE (I := I) α φ =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
        filter_upwards [hKc_open.mem_nhds hy] with z hz
        by_cases hzT : z ∈ (extChartAt I α).target
        · rw [phiOnE_apply_of_mem (I := I) α φ hzT]
          by_contra hne
          have : (extChartAt I α).symm z ∈ tsupport φ := subset_tsupport _ hne
          exact hz ⟨(extChartAt I α).symm z, this, (extChartAt I α).right_inv hzT⟩
        · exact phiOnE_apply_of_notMem (I := I) α φ hzT
      have hfderiv_zero : fderiv ℝ (phiOnE (I := I) α φ) y =
          fderiv ℝ (fun _ : E => (0 : ℝ)) y :=
        hphi_zero_on_nhd.fderiv_eq
      rw [hfderiv_zero]
      have hfderiv_const_zero : fderiv ℝ (fun _ : E => (0 : ℝ)) y = 0 := by
        rw [show (fun _ : E => (0 : ℝ)) = Function.const E (0 : ℝ) from rfl]
        rw [fderiv_const]
        rfl
      rw [hfderiv_const_zero]
      simp
  have hI3_compactSupport : HasCompactSupport
      (fun y => vwIntegrandOnE (I := I) g α X i y *
          fderiv ℝ (phiOnE (I := I) α φ) y ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i)) := by
    refine HasCompactSupport.intro
      (chartImageOfTsupport_isCompact (I := I) α hφ_compactSupport hφ_support) ?_
    intro y hy
    have hKc_open : IsOpen (chartImageOfTsupport (I := I) α φ)ᶜ :=
      (chartImageOfTsupport_isClosed (I := I) α hφ_compactSupport hφ_support).isOpen_compl
    have hphi_zero_on_nhd : phiOnE (I := I) α φ =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
      filter_upwards [hKc_open.mem_nhds hy] with z hz
      by_cases hzT : z ∈ (extChartAt I α).target
      · rw [phiOnE_apply_of_mem (I := I) α φ hzT]
        by_contra hne
        have : (extChartAt I α).symm z ∈ tsupport φ := subset_tsupport _ hne
        exact hz ⟨(extChartAt I α).symm z, this, (extChartAt I α).right_inv hzT⟩
      · exact phiOnE_apply_of_notMem (I := I) α φ hzT
    have hfderiv_zero : fderiv ℝ (phiOnE (I := I) α φ) y =
        fderiv ℝ (fun _ : E => (0 : ℝ)) y :=
      hphi_zero_on_nhd.fderiv_eq
    rw [hfderiv_zero]
    have hfderiv_const_zero : fderiv ℝ (fun _ : E => (0 : ℝ)) y = 0 := by
      rw [show (fun _ : E => (0 : ℝ)) = Function.const E (0 : ℝ) from rfl]
      rw [fderiv_const]
      rfl
    rw [hfderiv_const_zero]
    simp
  have hfg'_int : Integrable
      (fun y => vwIntegrandOnE (I := I) g α X i y *
          fderiv ℝ (phiOnE (I := I) α φ) y ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i))
      (modelHaar (E := E)) :=
    hI3_smooth.continuous.integrable_of_hasCompactSupport hI3_compactSupport
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hf'g_int hfg'_int hfg_int
    hvw_diff_tsupp_phi hphi_diff_tsupp_vw

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Module.Finite ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in
private lemma partialDeriv_vwIntegrandOnE_eq_on_target [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y =
      CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i
        (fun z : E => chartCoeffOnE (I := I) α X i z * chartDensityOnE (I := I) g α z) y := by
  unfold CalabiYau.Tensor.Coordinates.partialDeriv
  have hOpen : IsOpen (extChartAt I α).target := isOpen_extChartAt_target (I := I) α
  have h_eq : vwIntegrandOnE (I := I) g α X i =ᶠ[𝓝 y]
      (fun z : E => chartCoeffOnE (I := I) α X i z * chartDensityOnE (I := I) g α z) := by
    filter_upwards [hOpen.mem_nhds hy] with z hz
    exact vwIntegrandOnE_apply_of_mem (I := I) g α X i hz
  rw [h_eq.fderiv_eq]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Module.Finite ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] in
private lemma partialDeriv_phiOnE_eq_on_target [I.Boundaryless]
    (α : M) (φ : M → ℝ) (i : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (phiOnE (I := I) α φ) y =
      CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (scalarOnE (I := I) α φ) y := by
  unfold CalabiYau.Tensor.Coordinates.partialDeriv
  rw [fderiv_phiOnE_eq_fderiv_scalarOnE (I := I) α φ hy]

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Module.Finite ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
private lemma localDivergence_mul_chartDensity_chart_target_apply [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    chartDensity (I := I) g α ((extChartAt I α).symm y) *
      localDivergence (I := I) g α X ((extChartAt I α).symm y) =
      ∑ i : Fin (Module.finrank ℝ E),
        CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y := by
  classical
  have hsymm : (extChartAt I α) ((extChartAt I α).symm y) = y :=
    (extChartAt I α).right_inv hy
  have hsymmsrc : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hy
  have hsymmbase : (extChartAt I α).symm y ∈
      (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsymmsrc
    exact hsymmsrc
  have hρ_pos : 0 < chartDensity (I := I) g α ((extChartAt I α).symm y) :=
    chartDensity_pos (I := I) g α hsymmbase
  rw [localDivergence_def]
  field_simp
  rw [hsymm]
  refine Finset.sum_congr rfl ?_
  intro i _
  exact (partialDeriv_vwIntegrandOnE_eq_on_target (I := I) g α X i hy).symm

private lemma tangentSectionAction_chart_target_apply [I.Boundaryless]
    (α : M) (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
    {y : E} (hy : y ∈ (extChartAt I α).target) :
    tangentSectionAction (I := I) X φ ((extChartAt I α).symm y) =
      ∑ i : Fin (Module.finrank ℝ E),
        chartCoeff (I := I) α X i ((extChartAt I α).symm y) *
          CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (scalarOnE (I := I) α φ) y := by
  classical
  have hsymmsrc : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hy
  have hsymmchart : (extChartAt I α).symm y ∈ (chartAt H α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsymmsrc
    exact hsymmsrc
  have htsa := tangentSectionAction_chartLocal_of_boundaryless (I := I) α X hφ hsymmchart
  rw [htsa]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [(extChartAt I α).right_inv hy]

lemma localDivergence_continuousOn_baseSet [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContinuousOn (localDivergence (I := I) g α X) (chartAt H α).source := by
  have hsmooth : ContMDiffOn I 𝓘(ℝ) ∞ (localDivergence (I := I) g α X)
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) :=
    localDivergence_contMDiffOn (I := I) g α X
  have hdomain_eq : (extChartAt I α).source ∩
      (extChartAt I α) ⁻¹' interior (extChartAt I α).target = (chartAt H α).source := by
    ext x
    constructor
    · intro hx
      have h1 : x ∈ (extChartAt I α).source := hx.1
      rw [extChartAt_source_eq_chartAt_source (I := I)] at h1
      exact h1
    · intro hx
      refine ⟨?_, ?_⟩
      · rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
      · rw [(isOpen_extChartAt_target (I := I) α).interior_eq]
        have : x ∈ (extChartAt I α).source := by
          rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
        exact (extChartAt I α).map_source this
  rw [← hdomain_eq]
  exact hsmooth.continuousOn

lemma localDivergence_mul_phi_measurable [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {φ : M → ℝ} (hφ_cont : Continuous φ)
    (hφ_support : tsupport φ ⊆ (chartAt H α).source) :
    Measurable (fun x => localDivergence (I := I) g α X x * φ x) := by
  set s : Set M := (chartAt H α).source
  have hs_open : IsOpen s := (chartAt H α).open_source
  have hs_meas : MeasurableSet s := hs_open.measurableSet
  have hldiv_cont_s : ContinuousOn (localDivergence (I := I) g α X) s :=
    localDivergence_continuousOn_baseSet (I := I) g α X
  have hφ_cont_s : ContinuousOn φ s := hφ_cont.continuousOn
  have hprod_cont_s : ContinuousOn
      (fun x => localDivergence (I := I) g α X x * φ x) s :=
    hldiv_cont_s.mul hφ_cont_s
  have h_zero_off : ∀ x ∉ s, localDivergence (I := I) g α X x * φ x = 0 := by
    intro x hx
    have hxsupp : x ∉ tsupport φ := fun h => hx (hφ_support h)
    have : φ x = 0 := by
      by_contra hne
      exact hxsupp (subset_tsupport _ hne)
    rw [this, mul_zero]
  classical
  have hzero_cont : ContinuousOn (fun _ : M => (0 : ℝ)) sᶜ := continuousOn_const
  have hpiecewise_meas : Measurable (s.piecewise
      (fun x => localDivergence (I := I) g α X x * φ x)
      (fun _ : M => (0 : ℝ))) :=
    hprod_cont_s.measurable_piecewise hzero_cont hs_meas
  have h_eq : (fun x => localDivergence (I := I) g α X x * φ x) =
      s.piecewise (fun x => localDivergence (I := I) g α X x * φ x)
        (fun _ : M => (0 : ℝ)) := by
    funext x
    by_cases hx : x ∈ s
    · rw [Set.piecewise_eq_of_mem _ _ _ hx]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hx, h_zero_off x hx]
  rw [h_eq]
  exact hpiecewise_meas

private lemma lhs_chart_target [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {φ : M → ℝ} (hφ_cont : Continuous φ)
    (hφ_support : tsupport φ ⊆ (chartAt H α).source) :
    ∫ x, localDivergence (I := I) g α X x * φ x ∂(chartLocalMeasure (I := I) g α) =
      ∫ y in (extChartAt I α).target,
        (∑ i : Fin (Module.finrank ℝ E),
          CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y) *
            phiOnE (I := I) α φ y
        ∂(modelHaar (E := E)) := by
  classical
  set h : M → ℝ := fun x => localDivergence (I := I) g α X x * φ x with hh_def
  have hh_meas : Measurable h :=
    localDivergence_mul_phi_measurable (I := I) g α X hφ_cont hφ_support
  rw [integral_chartLocalMeasure (I := I) g α h hh_meas]
  refine setIntegral_congr_fun (measurableSet_extChartAt_target (I := I) α) ?_
  intro y hy
  have hρ_localDiv :=
    localDivergence_mul_chartDensity_chart_target_apply (I := I) g α X hy
  change chartDensity (I := I) g α ((extChartAt I α).symm y) *
        (localDivergence (I := I) g α X ((extChartAt I α).symm y)
          * φ ((extChartAt I α).symm y)) = _
  rw [show chartDensity (I := I) g α ((extChartAt I α).symm y) *
          (localDivergence (I := I) g α X ((extChartAt I α).symm y) *
            φ ((extChartAt I α).symm y)) =
        (chartDensity (I := I) g α ((extChartAt I α).symm y) *
          localDivergence (I := I) g α X ((extChartAt I α).symm y)) *
            φ ((extChartAt I α).symm y) from by ring]
  rw [hρ_localDiv]
  rw [← phiOnE_apply_of_mem (I := I) α φ hy]

private lemma rhs_chart_target [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ) :
    ∫ x, tangentSectionAction (I := I) X φ x ∂(chartLocalMeasure (I := I) g α) =
      ∫ y in (extChartAt I α).target,
        chartDensityOnE (I := I) g α y *
          (∑ i : Fin (Module.finrank ℝ E),
            chartCoeffOnE (I := I) α X i y *
              CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (scalarOnE (I := I) α φ) y)
        ∂(modelHaar (E := E)) := by
  classical
  have htsa_cont : Continuous (tangentSectionAction (I := I) X φ) :=
    (tangentSectionAction_contMDiff (I := I) X hφ).continuous
  rw [integral_chartLocalMeasure (I := I) g α (tangentSectionAction (I := I) X φ)
      htsa_cont.measurable]
  refine setIntegral_congr_fun (measurableSet_extChartAt_target (I := I) α) ?_
  intro y hy
  have htsa_eq := tangentSectionAction_chart_target_apply (I := I) α X hφ hy
  change chartDensity (I := I) g α ((extChartAt I α).symm y) *
      tangentSectionAction (I := I) X φ ((extChartAt I α).symm y) = _
  rw [htsa_eq]
  rfl

private lemma summand_int [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
    (hφ_compactSupport : HasCompactSupport φ)
    (hφ_support : tsupport φ ⊆ (chartAt H α).source)
    (i : Fin (Module.finrank ℝ E)) :
    Integrable (fun y =>
      CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y *
        phiOnE (I := I) α φ y) (modelHaar (E := E)) := by
  have hphi_smooth : ContDiff ℝ ∞ (phiOnE (I := I) α φ) :=
    phiOnE_contDiff (I := I) α hφ hφ_compactSupport hφ_support
  have hphi_compactSupport : HasCompactSupport (phiOnE (I := I) α φ) :=
    phiOnE_hasCompactSupport (I := I) α hφ_compactSupport hφ_support
  have hI_smooth : ContDiff ℝ ∞
      (fun y => CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y *
        phiOnE (I := I) α φ y) := by
    refine contDiff_of_smooth_on_open_zero_outside (U := (extChartAt I α).target)
      (isOpen_extChartAt_target (I := I) α)
      (K := chartImageOfTsupport (I := I) α φ)
      (chartImageOfTsupport_isClosed (I := I) α hφ_compactSupport hφ_support)
      (chartImageOfTsupport_subset_target (I := I) α hφ_support) ?_ ?_
    · have hvw_fderiv : ContDiffOn ℝ ∞
          (fderiv ℝ (vwIntegrandOnE (I := I) g α X i))
          (extChartAt I α).target :=
        (vwIntegrandOnE_contDiffOn_target (I := I) g α X i).fderiv_of_isOpen
          (isOpen_extChartAt_target (I := I) α) (by rw [ENat.coe_top_add_one])
      have hbasis_const : ContDiffOn ℝ ∞ (fun _ : E => (CalabiYau.Tensor.Coordinates.chartModelBasis E) i)
          (extChartAt I α).target := contDiffOn_const
      have hpartial : ContDiffOn ℝ ∞
          (CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i))
          (extChartAt I α).target := hvw_fderiv.clm_apply hbasis_const
      exact hpartial.mul hphi_smooth.contDiffOn
    · intro y hy
      have hphi_zero : phiOnE (I := I) α φ y = 0 := by
        by_cases hyT : y ∈ (extChartAt I α).target
        · rw [phiOnE_apply_of_mem (I := I) α φ hyT]
          by_contra hne
          have : (extChartAt I α).symm y ∈ tsupport φ := subset_tsupport _ hne
          exact hy ⟨(extChartAt I α).symm y, this, (extChartAt I α).right_inv hyT⟩
        · exact phiOnE_apply_of_notMem (I := I) α φ hyT
      rw [hphi_zero, mul_zero]
  have hI_compactSupport : HasCompactSupport
      (fun y => CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y *
          phiOnE (I := I) α φ y) :=
    hphi_compactSupport.mul_left
  exact hI_smooth.continuous.integrable_of_hasCompactSupport hI_compactSupport

private lemma summand_int' [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
    (hφ_compactSupport : HasCompactSupport φ)
    (hφ_support : tsupport φ ⊆ (chartAt H α).source)
    (i : Fin (Module.finrank ℝ E)) :
    Integrable (fun y =>
      vwIntegrandOnE (I := I) g α X i y *
        CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (phiOnE (I := I) α φ) y) (modelHaar (E := E)) := by
  have hphi_smooth : ContDiff ℝ ∞ (phiOnE (I := I) α φ) :=
    phiOnE_contDiff (I := I) α hφ hφ_compactSupport hφ_support
  have hI_smooth : ContDiff ℝ ∞
      (fun y => vwIntegrandOnE (I := I) g α X i y *
          CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (phiOnE (I := I) α φ) y) := by
    refine contDiff_of_smooth_on_open_zero_outside (U := (extChartAt I α).target)
      (isOpen_extChartAt_target (I := I) α)
      (K := chartImageOfTsupport (I := I) α φ)
      (chartImageOfTsupport_isClosed (I := I) α hφ_compactSupport hφ_support)
      (chartImageOfTsupport_subset_target (I := I) α hφ_support) ?_ ?_
    · have hphi_fderiv : ContDiffOn ℝ ∞ (fderiv ℝ (phiOnE (I := I) α φ))
          (extChartAt I α).target :=
        (hphi_smooth.fderiv_right (m := ∞) (by rw [ENat.coe_top_add_one])).contDiffOn
      have hbasis_const : ContDiffOn ℝ ∞ (fun _ : E => (CalabiYau.Tensor.Coordinates.chartModelBasis E) i)
          (extChartAt I α).target := contDiffOn_const
      have hpartial : ContDiffOn ℝ ∞
          (CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (phiOnE (I := I) α φ))
          (extChartAt I α).target := hphi_fderiv.clm_apply hbasis_const
      exact (vwIntegrandOnE_contDiffOn_target (I := I) g α X i).mul hpartial
    · intro y hy
      have hKc_open : IsOpen (chartImageOfTsupport (I := I) α φ)ᶜ :=
        (chartImageOfTsupport_isClosed (I := I) α hφ_compactSupport hφ_support).isOpen_compl
      have hphi_zero_on_nhd : phiOnE (I := I) α φ =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
        filter_upwards [hKc_open.mem_nhds hy] with z hz
        by_cases hzT : z ∈ (extChartAt I α).target
        · rw [phiOnE_apply_of_mem (I := I) α φ hzT]
          by_contra hne
          have : (extChartAt I α).symm z ∈ tsupport φ := subset_tsupport _ hne
          exact hz ⟨(extChartAt I α).symm z, this, (extChartAt I α).right_inv hzT⟩
        · exact phiOnE_apply_of_notMem (I := I) α φ hzT
      have hpartial_zero : CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (phiOnE (I := I) α φ) y = 0 := by
        unfold CalabiYau.Tensor.Coordinates.partialDeriv
        have hfderiv_eq : fderiv ℝ (phiOnE (I := I) α φ) y =
            fderiv ℝ (fun _ : E => (0 : ℝ)) y :=
          hphi_zero_on_nhd.fderiv_eq
        rw [hfderiv_eq]
        rw [show (fun _ : E => (0 : ℝ)) = Function.const E (0 : ℝ) from rfl, fderiv_const]
        rfl
      rw [hpartial_zero, mul_zero]
  have hI_compactSupport : HasCompactSupport
      (fun y => vwIntegrandOnE (I := I) g α X i y *
          CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (phiOnE (I := I) α φ) y) := by
    refine HasCompactSupport.intro
      (chartImageOfTsupport_isCompact (I := I) α hφ_compactSupport hφ_support) ?_
    intro y hy
    have hKc_open : IsOpen (chartImageOfTsupport (I := I) α φ)ᶜ :=
      (chartImageOfTsupport_isClosed (I := I) α hφ_compactSupport hφ_support).isOpen_compl
    have hphi_zero_on_nhd : phiOnE (I := I) α φ =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
      filter_upwards [hKc_open.mem_nhds hy] with z hz
      by_cases hzT : z ∈ (extChartAt I α).target
      · rw [phiOnE_apply_of_mem (I := I) α φ hzT]
        by_contra hne
        have : (extChartAt I α).symm z ∈ tsupport φ := subset_tsupport _ hne
        exact hz ⟨(extChartAt I α).symm z, this, (extChartAt I α).right_inv hzT⟩
      · exact phiOnE_apply_of_notMem (I := I) α φ hzT
    have hpartial_zero : CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (phiOnE (I := I) α φ) y = 0 := by
      unfold CalabiYau.Tensor.Coordinates.partialDeriv
      have hfderiv_eq : fderiv ℝ (phiOnE (I := I) α φ) y =
          fderiv ℝ (fun _ : E => (0 : ℝ)) y :=
        hphi_zero_on_nhd.fderiv_eq
      rw [hfderiv_eq]
      rw [show (fun _ : E => (0 : ℝ)) = Function.const E (0 : ℝ) from rfl, fderiv_const]
      rfl
    rw [hpartial_zero, mul_zero]
  exact hI_smooth.continuous.integrable_of_hasCompactSupport hI_compactSupport

theorem chart_local_ibp [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
    (hφ_compactSupport : HasCompactSupport φ)
    (hφ_support : tsupport φ ⊆ (chartAt H α).source) :
    ∫ x, localDivergence (I := I) g α X x * φ x ∂(chartLocalMeasure (I := I) g α) =
      -∫ x, tangentSectionAction (I := I) X φ x ∂(chartLocalMeasure (I := I) g α) := by
  classical
  rw [lhs_chart_target (I := I) g α X hφ.continuous hφ_support]
  rw [rhs_chart_target (I := I) g α X hφ]
  have hLHS_to_E :
      ∫ y in (extChartAt I α).target,
        (∑ i : Fin (Module.finrank ℝ E),
          CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y) *
            phiOnE (I := I) α φ y
        ∂(modelHaar (E := E)) =
      ∫ y, (∑ i : Fin (Module.finrank ℝ E),
          CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y) *
            phiOnE (I := I) α φ y
        ∂(modelHaar (E := E)) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero (μ := modelHaar (E := E))
      (s := (extChartAt I α).target)
      (f := fun y => (∑ i : Fin (Module.finrank ℝ E),
          CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y) *
            phiOnE (I := I) α φ y) ?_
    intro y hy
    have hphi_zero : phiOnE (I := I) α φ y = 0 :=
      phiOnE_apply_of_notMem (I := I) α φ hy
    simp only [hphi_zero, mul_zero]
  rw [hLHS_to_E]
  have h_sum_int :
      ∫ y, (∑ i : Fin (Module.finrank ℝ E),
          CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y) *
            phiOnE (I := I) α φ y
        ∂(modelHaar (E := E)) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∫ y, CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y *
            phiOnE (I := I) α φ y
        ∂(modelHaar (E := E)) := by
    rw [show (fun y => (∑ i : Fin (Module.finrank ℝ E),
            CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y) *
              phiOnE (I := I) α φ y)
          = (fun y => ∑ i : Fin (Module.finrank ℝ E),
              CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y *
              phiOnE (I := I) α φ y) from
      by funext y; rw [Finset.sum_mul]]
    rw [integral_finsetSum]
    intro i _
    exact summand_int (I := I) g α X hφ hφ_compactSupport hφ_support i
  rw [h_sum_int]
  have h_each : ∀ i : Fin (Module.finrank ℝ E),
      ∫ y, CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (vwIntegrandOnE (I := I) g α X i) y *
          phiOnE (I := I) α φ y
        ∂(modelHaar (E := E))
      = -∫ y, vwIntegrandOnE (I := I) g α X i y *
            CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (phiOnE (I := I) α φ) y
          ∂(modelHaar (E := E)) := by
    intro i
    have h_ibp := ibp_per_index (I := I) g α X hφ hφ_compactSupport hφ_support i
    change ∫ y, fderiv ℝ (vwIntegrandOnE (I := I) g α X i) y ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i)
        * phiOnE (I := I) α φ y
      ∂(modelHaar (E := E))
      = -∫ y, vwIntegrandOnE (I := I) g α X i y *
          fderiv ℝ (phiOnE (I := I) α φ) y ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i)
        ∂(modelHaar (E := E))
    linarith [h_ibp]
  rw [Finset.sum_congr rfl (fun i _ => h_each i)]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
          -∫ y, vwIntegrandOnE (I := I) g α X i y *
              CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (phiOnE (I := I) α φ) y
            ∂(modelHaar (E := E))) =
        - ∑ i : Fin (Module.finrank ℝ E),
          ∫ y, vwIntegrandOnE (I := I) g α X i y *
              CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (phiOnE (I := I) α φ) y
            ∂(modelHaar (E := E)) from by
      rw [← Finset.sum_neg_distrib]]
  have h_sum_back :
      ∑ i : Fin (Module.finrank ℝ E),
        ∫ y, vwIntegrandOnE (I := I) g α X i y *
            CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (phiOnE (I := I) α φ) y
          ∂(modelHaar (E := E)) =
      ∫ y, (∑ i : Fin (Module.finrank ℝ E),
          vwIntegrandOnE (I := I) g α X i y *
            CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (phiOnE (I := I) α φ) y)
        ∂(modelHaar (E := E)) := by
    rw [← integral_finsetSum]
    intro i _
    exact summand_int' (I := I) g α X hφ hφ_compactSupport hφ_support i
  rw [h_sum_back]
  have hE_to_target :
      ∫ y, (∑ i : Fin (Module.finrank ℝ E),
          vwIntegrandOnE (I := I) g α X i y *
            CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (phiOnE (I := I) α φ) y)
        ∂(modelHaar (E := E)) =
      ∫ y in (extChartAt I α).target,
        (∑ i : Fin (Module.finrank ℝ E),
          vwIntegrandOnE (I := I) g α X i y *
            CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (phiOnE (I := I) α φ) y)
        ∂(modelHaar (E := E)) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (μ := modelHaar (E := E))
      (s := (extChartAt I α).target)
      (f := fun y => ∑ i : Fin (Module.finrank ℝ E),
          vwIntegrandOnE (I := I) g α X i y *
            CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (phiOnE (I := I) α φ) y) ?_]
    intro y hy
    refine Finset.sum_eq_zero ?_
    intro i _
    rw [vwIntegrandOnE_apply_of_notMem (I := I) g α X i hy, zero_mul]
  rw [hE_to_target]
  refine congrArg Neg.neg ?_
  refine setIntegral_congr_fun (measurableSet_extChartAt_target (I := I) α) ?_
  intro y hy
  change (∑ i : Fin (Module.finrank ℝ E),
      vwIntegrandOnE (I := I) g α X i y *
          CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (phiOnE (I := I) α φ) y) =
      chartDensityOnE (I := I) g α y *
        ∑ i : Fin (Module.finrank ℝ E),
          chartCoeffOnE (I := I) α X i y *
            CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (scalarOnE (I := I) α φ) y
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [vwIntegrandOnE_apply_of_mem (I := I) g α X i hy]
  rw [partialDeriv_phiOnE_eq_on_target (I := I) α φ i hy]
  ring

end

end CalabiYau.DivergenceTheorem
