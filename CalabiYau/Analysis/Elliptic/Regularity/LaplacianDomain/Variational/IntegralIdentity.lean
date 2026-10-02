-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/LaplacianDomain/Variational/IntegralIdentity.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.LaplacianDomain.Variational.Identity
public import CalabiYau.Analysis.Elliptic.Regularity.ChartPushed.WeakPartialOnVolume
public import CalabiYau.Analysis.Elliptic.Regularity.H1Compl.WeakPartialLimit
public import CalabiYau.Analysis.Elliptic.Regularity.H1Compl.ChartLp
public import CalabiYau.Analysis.Elliptic.Regularity.H1Compl.GradientH1LipschitzBound
public import CalabiYau.Analysis.Elliptic.Regularity.LaplacianDomain.Variational.SmoothApproximation

@[expose] public section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace CalabiYau
namespace Analysis
namespace Laplacian
namespace LaplacianDomainVariationalIdentityIntegralForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Laplacian.MetricExtension
  hiding chartTargetEuclid
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.ChartBilinearH1ComplFromDom
open CalabiYau.Analysis.Laplacian.ChartPulledIntegralContinuity
open CalabiYau.Analysis.Laplacian.ChartPushedWeakPartialOnVolume
open CalabiYau.Analysis.Laplacian.LaplacianDomainVariationalLimit
open CalabiYau.Analysis.Laplacian.LaplacianDomainVariationalLimitGeneral
open CalabiYau.Analysis.Laplacian.LaplacianDomainVariationalIdentity
open CalabiYau.Analysis.Laplacian.H1ComplWeakPartialLimit
open CalabiYau.Analysis.Laplacian.H1ComplGradientChartBridge
open CalabiYau.Analysis.Laplacian.H1ComplGradientLipschitz
open CalabiYau.Analysis.Laplacian.H1ComplGradientLipschitzBound
open CalabiYau.Analysis.Laplacian.H1ComplGradientH1LipschitzBound
open CalabiYau.Analysis.Laplacian.H1ComplToLpChartBridge
open Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))


private lemma chartPulledWeightedMeasure_lt_top_of_compact_subset
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (chartPulledWeightedMeasure (I := I) g α) K < ⊤ := by
  classical
  by_cases hKne : K.Nonempty
  · have h_dens_contOn : ContinuousOn (densityOnEuclid (I := I) g α) K :=
      (densityOnEuclid_continuousOn (I := I) g α).mono hK_in
    obtain ⟨y₀, hy₀_mem, hy₀_max⟩ :=
      hK_compact.exists_isMaxOn hKne h_dens_contOn
    set M_d : ℝ := densityOnEuclid (I := I) g α y₀ with hM_d_def
    have hM_d_bd : ∀ y ∈ K, densityOnEuclid (I := I) g α y ≤ M_d := fun y hy =>
      hy₀_max hy
    unfold chartPulledWeightedMeasure
    rw [withDensity_apply _ hK_compact.measurableSet]
    have h_int_bd :
        (∫⁻ y in K, ENNReal.ofReal (densityOnEuclid (I := I) g α y)
          ∂(volume : Measure EuclN)) ≤
          ENNReal.ofReal M_d * (volume : Measure EuclN) K := by
      calc (∫⁻ y in K, ENNReal.ofReal (densityOnEuclid (I := I) g α y)
            ∂(volume : Measure EuclN))
          ≤ ∫⁻ _y in K, ENNReal.ofReal M_d ∂(volume : Measure EuclN) := by
            refine MeasureTheory.setLIntegral_mono_ae' hK_compact.measurableSet ?_
            refine Filter.Eventually.of_forall (fun y hy => ?_)
            exact ENNReal.ofReal_le_ofReal (hM_d_bd y hy)
        _ = ENNReal.ofReal M_d * (volume : Measure EuclN) K := by
            rw [MeasureTheory.setLIntegral_const]
    refine lt_of_le_of_lt h_int_bd ?_
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK_compact.measure_lt_top
  · rw [Set.not_nonempty_iff_eq_empty] at hKne
    rw [hKne, measure_empty]
    exact ENNReal.zero_lt_top

private lemma chartPulledWeightedMeasure_restrict_lt_top_of_compact_subset
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ((chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α)) K < ⊤ := by
  rw [Measure.restrict_apply hK_compact.measurableSet]
  refine lt_of_le_of_lt
    (measure_mono (Set.inter_subset_left)) ?_
  exact chartPulledWeightedMeasure_lt_top_of_compact_subset
    (I := I) (M := M) g α hK_compact hK_in

lemma continuous_compactSupport_memLp_chartPulledWeighted_restrict
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : EuclN → ℝ} (hf_cont : Continuous f) (hf_cs : HasCompactSupport f)
    (hf_support : tsupport f ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp f 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  obtain ⟨C, hC_bd⟩ : ∃ C : ℝ, ∀ y : EuclN, ‖f y‖ ≤ C :=
    hf_cont.bounded_above_of_compact_support hf_cs
  have h_aestrong : AEStronglyMeasurable f
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    hf_cont.aestronglyMeasurable.mono_measure Measure.restrict_le_self
  have h_top : MemLp f ⊤
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    memLp_top_of_bound h_aestrong C (Filter.Eventually.of_forall hC_bd)
  have h_zero_off : ∀ y, y ∉ tsupport f → f y = 0 :=
    fun y hy => image_eq_zero_of_notMem_tsupport hy
  have h_support_finite : ((chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α)) (tsupport f) ≠ ⊤ :=
    (chartPulledWeightedMeasure_restrict_lt_top_of_compact_subset
      (I := I) (M := M) g α hf_cs hf_support).ne
  refine h_top.mono_exponent_of_measure_support_ne_top h_zero_off h_support_finite ?_
  exact le_top

variable [NeZero (Module.finrank ℝ E)] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]
  [T2Space M] [CompactSpace M] in
private def principalMultiplier
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) (ψ : EuclN → ℝ) : EuclN → ℝ :=
  fun y =>
    ∑ j : Fin (Module.finrank ℝ E),
      invGramOnEuclid (I := I) g α i j y *
        (fderiv ℝ ψ y) (EuclideanSpace.single j 1)

private lemma principalMultiplier_eq_zero_off_tsupport
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) {ψ : EuclN → ℝ}
    {y : EuclN} (hy : y ∉ tsupport ψ) :
    principalMultiplier (I := I) (M := M) g α i ψ y = 0 := by
  classical
  unfold principalMultiplier
  have h_fder_zero : ∀ j : Fin (Module.finrank ℝ E),
      (fderiv ℝ ψ y) (EuclideanSpace.single j 1) = 0 := by
    intro j
    have h_compl_open : IsOpen ((tsupport ψ)ᶜ) :=
      (isClosed_tsupport _).isOpen_compl
    have h_ev : ψ =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
      filter_upwards [h_compl_open.mem_nhds hy] with z hz
      exact image_eq_zero_of_notMem_tsupport hz
    have h_fder_eq : fderiv ℝ ψ y = fderiv ℝ (fun _ : EuclN => (0 : ℝ)) y :=
      Filter.EventuallyEq.fderiv_eq h_ev
    rw [h_fder_eq]
    have h_const_zero : (fun _ : EuclN => (0 : ℝ)) =
        (Function.const EuclN (0 : ℝ)) := rfl
    rw [h_const_zero, fderiv_const]
    rfl
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [h_fder_zero, mul_zero]

private lemma principalMultiplier_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) {ψ : EuclN → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContinuousOn (principalMultiplier (I := I) (M := M) g α i ψ)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  unfold principalMultiplier
  refine continuousOn_finsetSum _ fun j _ => ?_
  have h_inv : ContinuousOn (invGramOnEuclid (I := I) g α i j)
      (chartTargetEuclid (I := I) (M := M) α) :=
    (invGramOnEuclid_contDiffOn (I := I) g α i j).continuousOn
  have hψ1 : ContDiff ℝ (1 : ℕ∞) ψ := hψ.of_le (by
      have h1 : (1 : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
      exact_mod_cast h1)
  have h_fder : Continuous (fun y : EuclN =>
      (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) :=
    (hψ1.continuous_fderiv (by norm_cast)).clm_apply continuous_const
  exact h_inv.mul h_fder.continuousOn

variable [I.Boundaryless] in
private lemma principalMultiplier_continuous
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) {ψ : EuclN → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Continuous (principalMultiplier (I := I) (M := M) g α i ψ) := by
  classical
  refine continuous_iff_continuousAt.mpr fun y => ?_
  by_cases hy : y ∈ tsupport ψ
  · have hy_T : y ∈ chartTargetEuclid (I := I) (M := M) α := hψ_support hy
    have hOpen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α
    exact (principalMultiplier_continuousOn (I := I) (M := M) g α i hψ).continuousAt
      (hOpen.mem_nhds hy_T)
  · have h_compl_open : IsOpen ((tsupport ψ)ᶜ) :=
      (isClosed_tsupport _).isOpen_compl
    have h_ev : (principalMultiplier (I := I) (M := M) g α i ψ) =ᶠ[𝓝 y]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [h_compl_open.mem_nhds hy] with z hz
      exact principalMultiplier_eq_zero_off_tsupport (I := I) (M := M) g α i hz
    refine ContinuousAt.congr ?_ h_ev.symm
    exact continuousAt_const

private lemma principalMultiplier_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) {ψ : EuclN → ℝ}
    (hψ_cs : HasCompactSupport ψ) :
    HasCompactSupport (principalMultiplier (I := I) (M := M) g α i ψ) := by
  classical
  refine HasCompactSupport.intro (hψ_cs : IsCompact (tsupport ψ)) (fun y hy => ?_)
  exact principalMultiplier_eq_zero_off_tsupport (I := I) (M := M) g α i hy

private lemma principalMultiplier_tsupport_subset
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) {ψ : EuclN → ℝ}
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    tsupport (principalMultiplier (I := I) (M := M) g α i ψ) ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  refine subset_trans ?_ hψ_support
  refine (closure_minimal ?_ (isClosed_tsupport _))
  intro y hy
  rw [Function.mem_support] at hy
  by_contra hyψ
  exact hy (principalMultiplier_eq_zero_off_tsupport (I := I) (M := M) g α i hyψ)

variable [NeZero (Module.finrank ℝ E)] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]
  [T2Space M] [CompactSpace M] in
private noncomputable def principalMultiplierLp
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) {ψ : EuclN → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α)) :=
  (continuous_compactSupport_memLp_chartPulledWeighted_restrict
    (I := I) (M := M) g α
    (principalMultiplier_continuous (I := I) (M := M) g α i hψ hψ_support)
    (principalMultiplier_hasCompactSupport (I := I) (M := M) g α i hψ_cs)
    (principalMultiplier_tsupport_subset (I := I) (M := M) g α i hψ_support)).toLp _

variable [I.Boundaryless] in
private lemma principalMultiplierLp_coeFn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) {ψ : EuclN → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ((principalMultiplierLp (I := I) (M := M) g α i hψ hψ_cs hψ_support :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      principalMultiplier (I := I) (M := M) g α i ψ := by
  unfold principalMultiplierLp
  exact MemLp.coeFn_toLp _

variable [NeZero (Module.finrank ℝ E)] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]
  [T2Space M] [CompactSpace M] in
private noncomputable def massMultiplierLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α)) :=
  (continuous_compactSupport_memLp_chartPulledWeighted_restrict
    (I := I) (M := M) g α hψ.continuous hψ_cs hψ_support).toLp _

private lemma massMultiplierLp_coeFn
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ((massMultiplierLp (I := I) (M := M) g α hψ hψ_cs hψ_support :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      ψ := by
  unfold massMultiplierLp
  exact MemLp.coeFn_toLp _

variable [I.Boundaryless] in
private lemma densityOnEuclid_aemeasurable_restrict_chartTarget
    (g : SmoothRiemannianMetric I M) (α : M) :
    AEMeasurable (fun y : EuclN => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
  exact (densityOnEuclid_continuousOn (I := I) g α).aemeasurable
    (Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet

private lemma densityOnEuclid_lt_top_ae_restrict_chartTarget
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      ENNReal.ofReal (densityOnEuclid (I := I) g α y) < ⊤ :=
  Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)

variable [I.Boundaryless] in
lemma setIntegral_chartPulledWeighted_eq_setIntegral_density_mul_volume
    (g : SmoothRiemannianMetric I M) (α : M) (f : EuclN → ℝ) :
    ∫ y in chartTargetEuclid (I := I) (M := M) α, f y
        ∂(chartPulledWeightedMeasure (I := I) g α) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y * f y ∂(volume : Measure EuclN) := by
  classical
  have h_target_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  unfold chartPulledWeightedMeasure
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀
      (densityOnEuclid_aemeasurable_restrict_chartTarget (I := I) (M := M) g α)
      (densityOnEuclid_lt_top_ae_restrict_chartTarget (I := I) (M := M) g α)
      f h_target_meas]
  refine MeasureTheory.setIntegral_congr_fun h_target_meas (fun y hy => ?_)
  have hy_pos : 0 < densityOnEuclid (I := I) g α y :=
    densityOnEuclid_pos (I := I) g α hy
  have : (ENNReal.ofReal (densityOnEuclid (I := I) g α y)).toReal =
      densityOnEuclid (I := I) g α y :=
    ENNReal.toReal_ofReal hy_pos.le
  rw [show (ENNReal.ofReal (densityOnEuclid (I := I) g α y)).toReal • f y =
      (ENNReal.ofReal (densityOnEuclid (I := I) g α y)).toReal * f y from rfl]
  rw [this]
section

variable [I.Boundaryless] [T2Space M] [CompactSpace M]


private lemma smooth_lhs_principal_per_i_integral_eq_weighted
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) {ψ : EuclN → ℝ}
    (_hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (v : SmoothScalar g) :
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            chartPushedPartial (I := I) (M := M) g α i v y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN) =
      ∫ y, principalMultiplier (I := I) (M := M) g α i ψ y *
          chartPushedPartial (I := I) (M := M) g α i v y
        ∂((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_meas_chartTarget : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  have h_pointwise : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      (∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            chartPushedPartial (I := I) (M := M) g α i v y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) =
        densityOnEuclid (I := I) g α y *
          (principalMultiplier (I := I) (M := M) g α i ψ y *
            chartPushedPartial (I := I) (M := M) g α i v y) := by
    intro y _hy
    unfold principalMultiplier
    have h_w : ∀ j : Fin (Module.finrank ℝ E),
        weightedInvGramOnEuclid (I := I) g α i j y =
          densityOnEuclid (I := I) g α y * invGramOnEuclid (I := I) g α i j y :=
      fun j => rfl
    have h_each : ∀ j : Fin (Module.finrank ℝ E),
        weightedInvGramOnEuclid (I := I) g α i j y *
            chartPushedPartial (I := I) (M := M) g α i v y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1) =
          densityOnEuclid (I := I) g α y *
            (invGramOnEuclid (I := I) g α i j y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) *
            chartPushedPartial (I := I) (M := M) g α i v y := by
      intro j
      rw [h_w j]
      ring
    rw [Finset.sum_congr rfl (fun j _ => h_each j)]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  rw [MeasureTheory.setIntegral_congr_fun h_meas_chartTarget h_pointwise]
  rw [← setIntegral_chartPulledWeighted_eq_setIntegral_density_mul_volume
    (I := I) (M := M) g α
    (fun y => principalMultiplier (I := I) (M := M) g α i ψ y *
      chartPushedPartial (I := I) (M := M) g α i v y)]

private lemma smooth_lhs_principal_per_i_eq_inner
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) {ψ : EuclN → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (v : SmoothScalar g) :
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            chartPushedPartial (I := I) (M := M) g α i v y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN) =
      ⟪principalMultiplierLp (I := I) (M := M) g α i hψ hψ_cs hψ_support,
        chartPushedPartialLp (I := I) (M := M) g α i v
          (chartPushedPartial_memLp (I := I) (M := M) g α i v)⟫_ℝ := by
  classical
  rw [smooth_lhs_principal_per_i_integral_eq_weighted (I := I) (M := M) g α i hψ v]
  rw [L2.inner_def (𝕜 := ℝ)]
  refine MeasureTheory.integral_congr_ae ?_
  have h_P := principalMultiplierLp_coeFn (I := I) (M := M) g α i hψ hψ_cs hψ_support
  have h_C : ((chartPushedPartialLp (I := I) (M := M) g α i v
        (chartPushedPartial_memLp (I := I) (M := M) g α i v) :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      chartPushedPartial (I := I) (M := M) g α i v := by
    unfold chartPushedPartialLp
    exact MemLp.coeFn_toLp _
  filter_upwards [h_P, h_C] with y h_Py h_Cy
  rw [show @inner ℝ _ _
      (((principalMultiplierLp (I := I) (M := M) g α i hψ hψ_cs hψ_support :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y)
      (((chartPushedPartialLp (I := I) (M := M) g α i v
          (chartPushedPartial_memLp (I := I) (M := M) g α i v) :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) =
      (((chartPushedPartialLp (I := I) (M := M) g α i v
          (chartPushedPartial_memLp (I := I) (M := M) g α i v) :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) *
      (((principalMultiplierLp (I := I) (M := M) g α i hψ hψ_cs hψ_support :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) from rfl]
  rw [h_Py, h_Cy]
  ring

noncomputable def chartPushedLpFromLp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α)) :=
  (chartPushed_memLp_chartPulledWeightedMeasure_restrict_of_memLp
    (I := I) (M := M) g α
    (Lp.stronglyMeasurable u).measurable
    (Lp.memLp u)).toLp _

lemma chartPushedLpFromLp_coeFn
    (g : SmoothRiemannianMetric I M) (α : M)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ((chartPushedLpFromLp (I := I) (M := M) g α u :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α (u : M → ℝ) := by
  unfold chartPushedLpFromLp
  exact MemLp.coeFn_toLp _

lemma chartPushedLpFromLp_tendsto
    (g : SmoothRiemannianMetric I M) (α : M)
    {u : ℕ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    {u_lim : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (h_tendsto : Tendsto u atTop (𝓝 u_lim)) :
    Tendsto (fun n => chartPushedLpFromLp (I := I) (M := M) g α (u n))
      atTop (𝓝 (chartPushedLpFromLp (I := I) (M := M) g α u_lim)) := by
  classical
  have h_norm_tendsto :
      Tendsto (fun n => ‖u n - u_lim‖) atTop (𝓝 0) := by
    have h_sub : Tendsto (fun n => u n - u_lim) atTop (𝓝 0) := by
      have := h_tendsto.sub (tendsto_const_nhds (x := u_lim))
      simpa using this
    change Tendsto
      ((fun a : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) => ‖a‖) ∘
        fun n => u n - u_lim) atTop (nhds 0)
    simpa only [norm_zero] using
      (continuous_norm.tendsto (0 :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))).comp h_sub
  have h_eLpNorm_eq : ∀ n,
      eLpNorm (((u n - u_lim) : Lp ℝ 2 _) : M → ℝ) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) =
      ENNReal.ofReal ‖u n - u_lim‖ := by
    intro n
    rw [Lp.norm_def]
    rw [ENNReal.ofReal_toReal
      ((Lp.memLp (u n - u_lim)).eLpNorm_lt_top.ne)]
  have h_eLpNorm_tendsto :
      Tendsto (fun n => eLpNorm (((u n - u_lim) : Lp ℝ 2 _) : M → ℝ) 2
        (riemannianVolumeMeasure (I := I) (M := M) g)) atTop (𝓝 0) := by
    have h_funeq : (fun n =>
        eLpNorm (((u n - u_lim) : Lp ℝ 2 _) : M → ℝ) 2
          (riemannianVolumeMeasure (I := I) (M := M) g)) =
        (fun n => ENNReal.ofReal ‖u n - u_lim‖) := funext h_eLpNorm_eq
    rw [h_funeq]
    have h_comp := (ENNReal.continuous_ofReal.tendsto 0).comp h_norm_tendsto
    simp only [Function.comp_def, ENNReal.ofReal_zero] at h_comp
    exact h_comp
  have h_aeEq : ∀ n, (((u n - u_lim) : Lp ℝ 2 _) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x => ((u n : Lp ℝ 2 _) : M → ℝ) x -
        ((u_lim : Lp ℝ 2 _) : M → ℝ) x) := by
    intro n
    have := MeasureTheory.Lp.coeFn_sub (u n) u_lim
    filter_upwards [this] with x hx
    exact hx
  have h_diff_tendsto :
      Tendsto (fun n => eLpNorm
        (fun x => ((u n : Lp ℝ 2 _) : M → ℝ) x - ((u_lim : Lp ℝ 2 _) : M → ℝ) x) 2
        (riemannianVolumeMeasure (I := I) (M := M) g)) atTop (𝓝 0) := by
    have h_funeq : (fun n => eLpNorm
        (fun x => ((u n : Lp ℝ 2 _) : M → ℝ) x - ((u_lim : Lp ℝ 2 _) : M → ℝ) x) 2
        (riemannianVolumeMeasure (I := I) (M := M) g)) =
      (fun n => eLpNorm (((u n - u_lim) : Lp ℝ 2 _) : M → ℝ) 2
        (riemannianVolumeMeasure (I := I) (M := M) g)) := by
      funext n
      exact MeasureTheory.eLpNorm_congr_ae (h_aeEq n).symm
    rw [h_funeq]
    exact h_eLpNorm_tendsto
  have hu_meas : ∀ n, Measurable ((u n : Lp ℝ 2 _) : M → ℝ) := fun n =>
    (Lp.stronglyMeasurable (u n)).measurable
  have hu_lim_meas : Measurable ((u_lim : Lp ℝ 2 _) : M → ℝ) :=
    (Lp.stronglyMeasurable u_lim).measurable
  have h_chartPushed_eLp_tendsto :=
    chartPushed_tendsto_chartPulledWeightedMeasure (I := I) (M := M) g α
      hu_meas hu_lim_meas h_diff_tendsto
  rw [tendsto_iff_dist_tendsto_zero]
  have h_dist_eq : ∀ n,
      dist (chartPushedLpFromLp (I := I) (M := M) g α (u n))
          (chartPushedLpFromLp (I := I) (M := M) g α u_lim) =
        ENNReal.toReal (eLpNorm (fun y =>
          Sobolev.Chart.chartPushed (I := I) (M := M)
            (chartAtlasPOU I M) α ((u n : Lp ℝ 2 _) : M → ℝ) y -
          Sobolev.Chart.chartPushed (I := I) (M := M)
            (chartAtlasPOU I M) α ((u_lim : Lp ℝ 2 _) : M → ℝ) y) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) := by
    intro n
    rw [dist_eq_norm, Lp.norm_def]
    have h_sub_aeEq := MeasureTheory.Lp.coeFn_sub
      (chartPushedLpFromLp (I := I) (M := M) g α (u n))
      (chartPushedLpFromLp (I := I) (M := M) g α u_lim)
    have h_coe_n := chartPushedLpFromLp_coeFn (I := I) (M := M) g α (u n)
    have h_coe_lim := chartPushedLpFromLp_coeFn (I := I) (M := M) g α u_lim
    have h_diff_ae : (((chartPushedLpFromLp (I := I) (M := M) g α (u n) -
            chartPushedLpFromLp (I := I) (M := M) g α u_lim) :
            Lp ℝ 2 _) : EuclN → ℝ) =ᵐ[
          (chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)]
        (fun y =>
          Sobolev.Chart.chartPushed (I := I) (M := M)
            (chartAtlasPOU I M) α ((u n : Lp ℝ 2 _) : M → ℝ) y -
          Sobolev.Chart.chartPushed (I := I) (M := M)
            (chartAtlasPOU I M) α ((u_lim : Lp ℝ 2 _) : M → ℝ) y) := by
      filter_upwards [h_sub_aeEq, h_coe_n, h_coe_lim] with y hy_sub hy_n hy_lim
      rw [hy_sub, Pi.sub_apply, hy_n, hy_lim]
    rw [MeasureTheory.eLpNorm_congr_ae h_diff_ae]
  rw [show (fun n =>
      dist (chartPushedLpFromLp (I := I) (M := M) g α (u n))
        (chartPushedLpFromLp (I := I) (M := M) g α u_lim)) =
    (fun n => ENNReal.toReal (eLpNorm (fun y =>
        Sobolev.Chart.chartPushed (I := I) (M := M)
          (chartAtlasPOU I M) α ((u n : Lp ℝ 2 _) : M → ℝ) y -
        Sobolev.Chart.chartPushed (I := I) (M := M)
          (chartAtlasPOU I M) α ((u_lim : Lp ℝ 2 _) : M → ℝ) y) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)))) from funext h_dist_eq]
  have h_toReal_tendsto :
      Tendsto (fun n => ENNReal.toReal (eLpNorm (fun y =>
        Sobolev.Chart.chartPushed (I := I) (M := M)
          (chartAtlasPOU I M) α ((u n : Lp ℝ 2 _) : M → ℝ) y -
        Sobolev.Chart.chartPushed (I := I) (M := M)
          (chartAtlasPOU I M) α ((u_lim : Lp ℝ 2 _) : M → ℝ) y) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)))) atTop (𝓝 0) := by
    have h_comp := (ENNReal.tendsto_toReal (by norm_num : (0 : ℝ≥0∞) ≠ ⊤)).comp
      h_chartPushed_eLp_tendsto
    change Tendsto (ENNReal.toReal ∘ fun n => eLpNorm (fun y =>
      Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α ((u n : Lp ℝ 2 _) : M → ℝ) y -
      Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α ((u_lim : Lp ℝ 2 _) : M → ℝ) y) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))) atTop (nhds 0)
    exact h_comp
  exact h_toReal_tendsto

private lemma smooth_lhs_mass_integral_eq_weighted
    (g : SmoothRiemannianMetric I M) (α : M)
    (v : SmoothScalar g) (ψ : EuclN → ℝ) :
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          Sobolev.Chart.chartPushed (I := I) (M := M)
            (chartAtlasPOU I M) α v.toFun y * ψ y
        ∂(volume : Measure EuclN) =
      ∫ y,
        Sobolev.Chart.chartPushed (I := I) (M := M)
          (chartAtlasPOU I M) α v.toFun y * ψ y
        ∂((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_meas_chartTarget : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  rw [show ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          Sobolev.Chart.chartPushed (I := I) (M := M)
            (chartAtlasPOU I M) α v.toFun y * ψ y
        ∂(volume : Measure EuclN) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (Sobolev.Chart.chartPushed (I := I) (M := M)
            (chartAtlasPOU I M) α v.toFun y * ψ y)
        ∂(volume : Measure EuclN) from by
      refine MeasureTheory.setIntegral_congr_fun h_meas_chartTarget (fun y _hy => ?_)
      ring]
  rw [← setIntegral_chartPulledWeighted_eq_setIntegral_density_mul_volume
    (I := I) (M := M) g α
    (fun y =>
      Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α v.toFun y * ψ y)]

private lemma chartPushedLpFromLp_smoothToLp_aeEq
    (g : SmoothRiemannianMetric I M) (α : M)
    (v : SmoothScalar g) :
    ((chartPushedLpFromLp (I := I) (M := M) g α
        (smoothToLp (I := I) (M := M) g v) :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α v.toFun := by
  classical
  have h_lp_coeFn := chartPushedLpFromLp_coeFn (I := I) (M := M) g α
    (smoothToLp (I := I) (M := M) g v)
  have h_smooth_coe : ((smoothToLp (I := I) (M := M) g v :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g] v.toFun :=
    MemLp.coeFn_toLp v.memLp_two
  refine h_lp_coeFn.trans ?_
  have h_meas_lp_coe : Measurable
      ((smoothToLp (I := I) (M := M) g v : Lp ℝ 2 _) : M → ℝ) :=
    (Lp.stronglyMeasurable _).measurable
  have h_meas_v : Measurable v.toFun := v.smooth.continuous.measurable
  have h_zero_μg : eLpNorm
        (fun x : M => ((smoothToLp (I := I) (M := M) g v :
              Lp ℝ 2 _) : M → ℝ) x - v.toFun x) 2
          (riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
    refine (MeasureTheory.eLpNorm_eq_zero_iff
      (h_meas_lp_coe.sub h_meas_v).aestronglyMeasurable
      (by norm_num : (2 : ℝ≥0∞) ≠ 0)).mpr ?_
    filter_upwards [h_smooth_coe] with x hx
    change ((smoothToLp (I := I) (M := M) g v : Lp ℝ 2 _) : M → ℝ) x - v.toFun x = 0
    rw [hx, sub_self]
  obtain ⟨C, _hC_pos, hC_bnd⟩ :=
    eLpNorm_chartPushed_chartPulledWeightedMeasure_restrict_le (I := I) (M := M) g α
      (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  have h_sub_meas : Measurable
      (fun x : M => ((smoothToLp (I := I) (M := M) g v :
            Lp ℝ 2 _) : M → ℝ) x - v.toFun x) :=
    h_meas_lp_coe.sub h_meas_v
  have h_diff_bound := hC_bnd h_sub_meas
  have h_chart_diff :
        Sobolev.Chart.chartPushed (I := I) (M := M)
          (chartAtlasPOU I M) α
          (fun x : M => ((smoothToLp (I := I) (M := M) g v :
                Lp ℝ 2 _) : M → ℝ) x - v.toFun x) =
        (fun y =>
          Sobolev.Chart.chartPushed (I := I) (M := M)
            (chartAtlasPOU I M) α (((smoothToLp (I := I) (M := M) g v :
                Lp ℝ 2 _) : M → ℝ)) y -
          Sobolev.Chart.chartPushed (I := I) (M := M)
            (chartAtlasPOU I M) α v.toFun y) := by
    funext y
    unfold Sobolev.Chart.chartPushed
    ring
  rw [h_chart_diff] at h_diff_bound
  rw [h_zero_μg, mul_zero] at h_diff_bound
  have h_chart_eLpNorm_zero : eLpNorm
      (fun y =>
        Sobolev.Chart.chartPushed (I := I) (M := M)
          (chartAtlasPOU I M) α (((smoothToLp (I := I) (M := M) g v :
              Lp ℝ 2 _) : M → ℝ)) y -
        Sobolev.Chart.chartPushed (I := I) (M := M)
          (chartAtlasPOU I M) α v.toFun y) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) = 0 :=
    le_antisymm h_diff_bound (zero_le)
  have h_aestrong : AEStronglyMeasurable (fun y =>
      Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α (((smoothToLp (I := I) (M := M) g v :
          Lp ℝ 2 _) : M → ℝ)) y -
      Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α v.toFun y)
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    refine AEStronglyMeasurable.sub ?_ ?_
    · exact (chartPushed_memLp_chartPulledWeightedMeasure_restrict_of_memLp
        (I := I) (M := M) g α h_meas_lp_coe (Lp.memLp _)).1
    · exact (chartPushed_memLp_chartPulledWeightedMeasure_restrict_of_memLp
        (I := I) (M := M) g α h_meas_v v.memLp_two).1
  have h_aeEq_zero := (MeasureTheory.eLpNorm_eq_zero_iff h_aestrong
    (by norm_num : (2 : ℝ≥0∞) ≠ 0)).mp h_chart_eLpNorm_zero
  filter_upwards [h_aeEq_zero] with y hy
  have hy' : Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α (((smoothToLp (I := I) (M := M) g v :
          Lp ℝ 2 _) : M → ℝ)) y -
      Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α v.toFun y = 0 := hy
  linarith

private lemma smooth_lhs_mass_eq_inner
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (v : SmoothScalar g) :
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          Sobolev.Chart.chartPushed (I := I) (M := M)
            (chartAtlasPOU I M) α v.toFun y * ψ y
        ∂(volume : Measure EuclN) =
      ⟪massMultiplierLp (I := I) (M := M) g α hψ hψ_cs hψ_support,
        chartPushedLpFromLp (I := I) (M := M) g α
          (smoothToLp (I := I) (M := M) g v)⟫_ℝ := by
  classical
  rw [smooth_lhs_mass_integral_eq_weighted (I := I) (M := M) g α v ψ]
  rw [L2.inner_def (𝕜 := ℝ)]
  refine MeasureTheory.integral_congr_ae ?_
  have h_ψ := massMultiplierLp_coeFn (I := I) (M := M) g α hψ hψ_cs hψ_support
  have h_C := chartPushedLpFromLp_smoothToLp_aeEq (I := I) (M := M) g α v
  filter_upwards [h_ψ, h_C] with y h_ψy h_Cy
  rw [show @inner ℝ _ _
      (((massMultiplierLp (I := I) (M := M) g α hψ hψ_cs hψ_support :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y)
      (((chartPushedLpFromLp (I := I) (M := M) g α
          (smoothToLp (I := I) (M := M) g v) :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) =
      (((chartPushedLpFromLp (I := I) (M := M) g α
          (smoothToLp (I := I) (M := M) g v) :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) *
      (((massMultiplierLp (I := I) (M := M) g α hψ hψ_cs hψ_support :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) from rfl]
  rw [h_ψy, h_Cy]

private lemma smooth_lhs_principal_per_i_tendsto
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) {ψ : EuclN → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    {u_h : H1Compl g}
    {v : ℕ → SmoothScalar g}
    (h_tendsto : Tendsto (fun n => smoothToH1Compl (I := I) (M := M) g (v n))
      atTop (𝓝 u_h)) :
    Tendsto (fun n =>
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chartPushedPartial (I := I) (M := M) g α i (v n) y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) atTop
      (𝓝 ⟪principalMultiplierLp (I := I) (M := M) g α i hψ hψ_cs hψ_support,
        chartPushedWeakPartialLp (I := I) (M := M) g α i
          (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α i) u_h⟫_ℝ) := by
  classical
  have h_per_n : ∀ n,
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chartPushedPartial (I := I) (M := M) g α i (v n) y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN) =
        ⟪principalMultiplierLp (I := I) (M := M) g α i hψ hψ_cs hψ_support,
          chartPushedPartialLp (I := I) (M := M) g α i (v n)
            (chartPushedPartial_memLp (I := I) (M := M) g α i (v n))⟫_ℝ := fun n =>
    smooth_lhs_principal_per_i_eq_inner (I := I) (M := M) g α i hψ hψ_cs hψ_support (v n)
  have h_smooth_case_eq : ∀ n,
      chartPushedPartialLp (I := I) (M := M) g α i (v n)
          (chartPushedPartial_memLp (I := I) (M := M) g α i (v n)) =
        chartPushedWeakPartialLp (I := I) (M := M) g α i
          (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α i)
          (smoothToH1Compl (I := I) (M := M) g (v n)) :=
    fun n => (chartPushedWeakPartialLp_smoothToH1Compl
      (I := I) (M := M) g α i
      (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α i) (v n)).symm
  have h_cwpL_tendsto : Tendsto (fun n => chartPushedWeakPartialLp
        (I := I) (M := M) g α i
        (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α i)
        (smoothToH1Compl (I := I) (M := M) g (v n))) atTop
      (𝓝 (chartPushedWeakPartialLp (I := I) (M := M) g α i
        (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α i) u_h)) :=
    ((chartPushedWeakPartialLp_continuous
      (I := I) (M := M) g α i _).tendsto _).comp h_tendsto
  have h_inner_tendsto : Tendsto (fun n =>
        ⟪principalMultiplierLp (I := I) (M := M) g α i hψ hψ_cs hψ_support,
          chartPushedWeakPartialLp (I := I) (M := M) g α i
            (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α i)
            (smoothToH1Compl (I := I) (M := M) g (v n))⟫_ℝ) atTop
      (𝓝 ⟪principalMultiplierLp (I := I) (M := M) g α i hψ hψ_cs hψ_support,
        chartPushedWeakPartialLp (I := I) (M := M) g α i
          (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α i) u_h⟫_ℝ) :=
    Filter.Tendsto.inner tendsto_const_nhds h_cwpL_tendsto
  rw [show (fun n =>
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chartPushedPartial (I := I) (M := M) g α i (v n) y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) =
    (fun n =>
      ⟪principalMultiplierLp (I := I) (M := M) g α i hψ hψ_cs hψ_support,
        chartPushedWeakPartialLp (I := I) (M := M) g α i
          (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α i)
          (smoothToH1Compl (I := I) (M := M) g (v n))⟫_ℝ) from by
    funext n
    rw [h_per_n n, h_smooth_case_eq n]]
  exact h_inner_tendsto

private lemma smooth_lhs_mass_tendsto
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    {u_h : H1Compl g}
    {v : ℕ → SmoothScalar g}
    (h_tendsto : Tendsto (fun n => smoothToH1Compl (I := I) (M := M) g (v n))
      atTop (𝓝 u_h)) :
    Tendsto (fun n =>
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            Sobolev.Chart.chartPushed (I := I) (M := M)
              (chartAtlasPOU I M) α (v n).toFun y * ψ y
          ∂(volume : Measure EuclN)) atTop
      (𝓝 ⟪massMultiplierLp (I := I) (M := M) g α hψ hψ_cs hψ_support,
        chartPushedLpFromLp (I := I) (M := M) g α
          (h1ComplToLp (I := I) (M := M) g u_h)⟫_ℝ) := by
  classical
  have h_per_n : ∀ n,
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            Sobolev.Chart.chartPushed (I := I) (M := M)
              (chartAtlasPOU I M) α (v n).toFun y * ψ y
          ∂(volume : Measure EuclN) =
        ⟪massMultiplierLp (I := I) (M := M) g α hψ hψ_cs hψ_support,
          chartPushedLpFromLp (I := I) (M := M) g α
            (smoothToLp (I := I) (M := M) g (v n))⟫_ℝ := fun n =>
    smooth_lhs_mass_eq_inner (I := I) (M := M) g α hψ hψ_cs hψ_support (v n)
  have h_lp_tendsto : Tendsto (fun n => smoothToLp (I := I) (M := M) g (v n))
      atTop (𝓝 (h1ComplToLp (I := I) (M := M) g u_h)) :=
    smoothToLp_tendsto_H1ComplToLp_of_h1_tendsto (I := I) (M := M) g h_tendsto
  have h_cPL_tendsto :
      Tendsto (fun n => chartPushedLpFromLp (I := I) (M := M) g α
          (smoothToLp (I := I) (M := M) g (v n))) atTop
        (𝓝 (chartPushedLpFromLp (I := I) (M := M) g α
          (h1ComplToLp (I := I) (M := M) g u_h))) :=
    chartPushedLpFromLp_tendsto (I := I) (M := M) g α h_lp_tendsto
  have h_inner_tendsto : Tendsto (fun n =>
        ⟪massMultiplierLp (I := I) (M := M) g α hψ hψ_cs hψ_support,
          chartPushedLpFromLp (I := I) (M := M) g α
            (smoothToLp (I := I) (M := M) g (v n))⟫_ℝ) atTop
      (𝓝 ⟪massMultiplierLp (I := I) (M := M) g α hψ hψ_cs hψ_support,
        chartPushedLpFromLp (I := I) (M := M) g α
          (h1ComplToLp (I := I) (M := M) g u_h)⟫_ℝ) :=
    Filter.Tendsto.inner tendsto_const_nhds h_cPL_tendsto
  rw [show (fun n =>
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            Sobolev.Chart.chartPushed (I := I) (M := M)
              (chartAtlasPOU I M) α (v n).toFun y * ψ y
          ∂(volume : Measure EuclN)) =
    (fun n =>
      ⟪massMultiplierLp (I := I) (M := M) g α hψ hψ_cs hψ_support,
        chartPushedLpFromLp (I := I) (M := M) g α
          (smoothToLp (I := I) (M := M) g (v n))⟫_ℝ) from
    funext h_per_n]
  exact h_inner_tendsto

private lemma general_lhs_mass_eq_inner
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (u_h : H1Compl g) :
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          Sobolev.Chart.chartPushed (I := I) (M := M)
            (chartAtlasPOU I M) α
            (((h1ComplToLp (I := I) (M := M) g u_h) :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) y * ψ y
        ∂(volume : Measure EuclN) =
      ⟪massMultiplierLp (I := I) (M := M) g α hψ hψ_cs hψ_support,
        chartPushedLpFromLp (I := I) (M := M) g α
          (h1ComplToLp (I := I) (M := M) g u_h)⟫_ℝ := by
  classical
  have h_meas_chartTarget : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  rw [show ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          Sobolev.Chart.chartPushed (I := I) (M := M)
            (chartAtlasPOU I M) α
            (((h1ComplToLp (I := I) (M := M) g u_h) :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) y * ψ y
        ∂(volume : Measure EuclN) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (Sobolev.Chart.chartPushed (I := I) (M := M)
            (chartAtlasPOU I M) α
            (((h1ComplToLp (I := I) (M := M) g u_h) :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) y * ψ y)
        ∂(volume : Measure EuclN) from by
      refine MeasureTheory.setIntegral_congr_fun h_meas_chartTarget (fun y _hy => ?_)
      ring]
  rw [← setIntegral_chartPulledWeighted_eq_setIntegral_density_mul_volume
    (I := I) (M := M) g α
    (fun y =>
      Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α
        (((h1ComplToLp (I := I) (M := M) g u_h) :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) y * ψ y)]
  rw [L2.inner_def (𝕜 := ℝ)]
  refine MeasureTheory.integral_congr_ae ?_
  have h_ψ := massMultiplierLp_coeFn (I := I) (M := M) g α hψ hψ_cs hψ_support
  have h_C := chartPushedLpFromLp_coeFn (I := I) (M := M) g α
    (h1ComplToLp (I := I) (M := M) g u_h)
  filter_upwards [h_ψ, h_C] with y h_ψy h_Cy
  rw [show @inner ℝ _ _
      (((massMultiplierLp (I := I) (M := M) g α hψ hψ_cs hψ_support :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y)
      (((chartPushedLpFromLp (I := I) (M := M) g α
          (h1ComplToLp (I := I) (M := M) g u_h) :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) =
      (((chartPushedLpFromLp (I := I) (M := M) g α
          (h1ComplToLp (I := I) (M := M) g u_h) :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) *
      (((massMultiplierLp (I := I) (M := M) g α hψ hψ_cs hψ_support :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) from rfl]
  rw [h_ψy, h_Cy]

private lemma general_lhs_principal_full_integrand_pointwise
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ}
    (u_h : H1Compl g)
    {y : EuclN} (_hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        weightedInvGramOnEuclid (I := I) g α i j y *
          ((chartPushedWeakPartialLp (I := I) (M := M) g α i
            (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α i) u_h :
            Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) =
      densityOnEuclid (I := I) g α y *
        (∑ i : Fin (Module.finrank ℝ E),
          principalMultiplier (I := I) (M := M) g α i ψ y *
            ((chartPushedWeakPartialLp (I := I) (M := M) g α i
              (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α i) u_h :
              Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) := by
  classical
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold principalMultiplier
  have h_each : ∀ j : Fin (Module.finrank ℝ E),
      weightedInvGramOnEuclid (I := I) g α i j y *
        ((chartPushedWeakPartialLp (I := I) (M := M) g α i
          (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α i) u_h :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y *
        (fderiv ℝ ψ y) (EuclideanSpace.single j 1) =
      densityOnEuclid (I := I) g α y *
        (invGramOnEuclid (I := I) g α i j y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) *
        ((chartPushedWeakPartialLp (I := I) (M := M) g α i
          (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α i) u_h :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y := by
    intro j
    have h_w : weightedInvGramOnEuclid (I := I) g α i j y =
        densityOnEuclid (I := I) g α y * invGramOnEuclid (I := I) g α i j y := rfl
    rw [h_w]
    ring
  rw [Finset.sum_congr rfl (fun j _ => h_each j)]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  ring

private lemma general_lhs_principal_eq_sum_inner
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (u_h : H1Compl g) :
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            ((chartPushedWeakPartialLp (I := I) (M := M) g α i
              (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α i) u_h :
              Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN) =
      ∑ i : Fin (Module.finrank ℝ E),
        ⟪principalMultiplierLp (I := I) (M := M) g α i hψ hψ_cs hψ_support,
          chartPushedWeakPartialLp (I := I) (M := M) g α i
            (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α i) u_h⟫_ℝ := by
  classical
  set μ := (chartPulledWeightedMeasure (I := I) g α).restrict
    (chartTargetEuclid (I := I) (M := M) α)
  have h_meas_chartTarget : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  rw [MeasureTheory.setIntegral_congr_fun h_meas_chartTarget
    (fun y hy => general_lhs_principal_full_integrand_pointwise (I := I) (M := M) g α u_h hy)]
  rw [← setIntegral_chartPulledWeighted_eq_setIntegral_density_mul_volume
    (I := I) (M := M) g α
    (fun y => ∑ i : Fin (Module.finrank ℝ E),
      principalMultiplier (I := I) (M := M) g α i ψ y *
        ((chartPushedWeakPartialLp (I := I) (M := M) g α i
          (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α i) u_h :
          Lp ℝ 2 _) : EuclN → ℝ) y)]
  have h_per_i_integrable : ∀ i : Fin (Module.finrank ℝ E),
      Integrable (fun y =>
        principalMultiplier (I := I) (M := M) g α i ψ y *
          ((chartPushedWeakPartialLp (I := I) (M := M) g α i
            (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α i) u_h :
            Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) μ := by
    intro i
    have h_P : MemLp (principalMultiplier (I := I) (M := M) g α i ψ) 2 μ :=
      continuous_compactSupport_memLp_chartPulledWeighted_restrict
        (I := I) (M := M) g α
        (principalMultiplier_continuous (I := I) (M := M) g α i hψ hψ_support)
        (principalMultiplier_hasCompactSupport (I := I) (M := M) g α i hψ_cs)
        (principalMultiplier_tsupport_subset (I := I) (M := M) g α i hψ_support)
    have h_C : MemLp (((chartPushedWeakPartialLp (I := I) (M := M) g α i
        (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α i) u_h :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ)) 2 μ :=
      Lp.memLp _
    exact MemLp.integrable_mul h_P h_C
  rw [MeasureTheory.integral_finsetSum _ (fun i _ => h_per_i_integrable i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [L2.inner_def (𝕜 := ℝ)]
  refine MeasureTheory.integral_congr_ae ?_
  have h_P := principalMultiplierLp_coeFn (I := I) (M := M) g α i hψ hψ_cs hψ_support
  filter_upwards [h_P] with y h_Py
  rw [show @inner ℝ _ _
      (((principalMultiplierLp (I := I) (M := M) g α i hψ hψ_cs hψ_support :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y)
      (((chartPushedWeakPartialLp (I := I) (M := M) g α i
          (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α i) u_h :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) =
      (((chartPushedWeakPartialLp (I := I) (M := M) g α i
          (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α i) u_h :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) *
      (((principalMultiplierLp (I := I) (M := M) g α i hψ hψ_cs hψ_support :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) from rfl]
  rw [h_Py]
  ring

private lemma rhs_smooth_tendsto_chartPulledIntegralCLM_fHLeibniz
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {v : ℕ → SmoothScalar g}
    (h_v_tendsto :
      Tendsto (fun n => smoothToH1Compl (I := I) (M := M) g (v n))
        atTop (𝓝 u_h)) :
    Tendsto (fun n =>
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            ((pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical.toFun)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
            ψ y ∂(volume : Measure EuclN))
      atTop (𝓝 (chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
        (leibnizCompensatedSource (I := I) (M := M) g α u_h hu_h))) := by
  classical
  have h_eq_smooth : ∀ n,
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            ((pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical.toFun)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
            ψ y ∂(volume : Measure EuclN) =
        chartPulledIntegralCLM (I := I) (M := M) g α
          (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
          (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
          (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
          (smoothToLp (I := I) (M := M) g
            (pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical) := by
    intro n
    rw [chartPulledIntegralCLM_smoothToLp (I := I) (M := M) g α _ _ _
      (pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical]
    refine MeasureTheory.setIntegral_congr_fun
      (Sobolev.Chart.chartTargetEuclid_isOpen
        (I := I) (M := M) α).measurableSet (fun y _ => ?_)
    ring
  have h_eq_fHLeibniz_smooth : ∀ n,
      smoothToLp (I := I) (M := M) g
          (pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical =
        leibnizCompensatedSource (I := I) (M := M) g α
          (smoothToH1Compl (I := I) (M := M) g (v n))
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) (v n)) :=
    fun n => smoothToLp_pouScalar_oneSubLap_eq_fHLeibniz (I := I) (M := M) g α (v n)
  have h_fHLeibniz_eq : ∀ n,
      chartPulledIntegralCLM (I := I) (M := M) g α
          (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
          (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
          (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
          (smoothToLp (I := I) (M := M) g
            (pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical) =
        chartPulledIntegralCLM (I := I) (M := M) g α
            (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
            (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
            (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
            (smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
              (smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical)) -
          (2 : ℝ) *
            chartPulledIntegralCLM (I := I) (M := M) g α
              (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
              (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
              (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
              (gradInnerSmooth (I := I) (M := M) g
                (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) (v n)) -
          chartPulledIntegralCLM (I := I) (M := M) g α
            (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
            (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
            (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
            (smoothMulLp (I := I) (M := M) g
              (laplacianOfChartPOU (I := I) (M := M) g α)
              (smoothToLp (I := I) (M := M) g (v n))) := by
    intro n
    rw [h_eq_fHLeibniz_smooth n, fHLeibniz_smoothToH1Compl]
    simp only [ContinuousLinearMap.map_sub, ContinuousLinearMap.map_smul,
      smul_eq_mul]
  have h_lim_1 := chartPulledIntegralCLM_smoothMulLp_oneSubLap_tendsto
    (I := I) (M := M) g α hψ hψ_cs hψ_support hu_h h_v_tendsto
  have h_lim_2 := chartPulledIntegralCLM_gradInnerSmooth_tendsto
    (I := I) (M := M) g α hψ hψ_cs hψ_support h_v_tendsto
  have h_lim_3 := chartPulledIntegralCLM_smoothMulLp_tendsto
    (I := I) (M := M) g α hψ hψ_cs hψ_support h_v_tendsto
  have h_sum_lim : Tendsto (fun n =>
        chartPulledIntegralCLM (I := I) (M := M) g α
            (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
            (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
            (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
            (smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
              (smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical)) -
          (2 : ℝ) *
            chartPulledIntegralCLM (I := I) (M := M) g α
              (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
              (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
              (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
              (gradInnerSmooth (I := I) (M := M) g
                (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) (v n)) -
          chartPulledIntegralCLM (I := I) (M := M) g α
            (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
            (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
            (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
            (smoothMulLp (I := I) (M := M) g
              (laplacianOfChartPOU (I := I) (M := M) g α)
              (smoothToLp (I := I) (M := M) g (v n)))) atTop
      (𝓝 (chartPulledIntegralCLM (I := I) (M := M) g α
            (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
            (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
            (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
            (smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
              (h1ComplToLp (I := I) (M := M) g u_h -
                laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩)) -
          (2 : ℝ) *
            chartPulledIntegralCLM (I := I) (M := M) g α
              (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
              (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
              (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
              (gradInnerCLM (I := I) (M := M) g
                (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h) -
          chartPulledIntegralCLM (I := I) (M := M) g α
            (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
            (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
            (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
            (smoothMulLp (I := I) (M := M) g
              (laplacianOfChartPOU (I := I) (M := M) g α)
              (h1ComplToLp (I := I) (M := M) g u_h)))) := by
    refine (h_lim_1.sub ?_).sub h_lim_3
    exact (tendsto_const_nhds.mul h_lim_2 : Tendsto _ _ _)
  have h_target_eq :
      chartPulledIntegralCLM (I := I) (M := M) g α
            (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
            (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
            (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
            (smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
              (h1ComplToLp (I := I) (M := M) g u_h -
                laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩)) -
          (2 : ℝ) *
            chartPulledIntegralCLM (I := I) (M := M) g α
              (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
              (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
              (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
              (gradInnerCLM (I := I) (M := M) g
                (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h) -
          chartPulledIntegralCLM (I := I) (M := M) g α
            (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
            (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
            (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
            (smoothMulLp (I := I) (M := M) g
              (laplacianOfChartPOU (I := I) (M := M) g α)
              (h1ComplToLp (I := I) (M := M) g u_h)) =
        chartPulledIntegralCLM (I := I) (M := M) g α
          (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
          (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
          (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
          (leibnizCompensatedSource (I := I) (M := M) g α u_h hu_h) :=
    laplacianDomain_variational_identity_clm_form
      (I := I) (M := M) g α hu_h hψ hψ_cs hψ_support
  rw [show (fun n =>
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          ((pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical.toFun)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          ψ y ∂(volume : Measure EuclN)) =
    (fun n =>
      chartPulledIntegralCLM (I := I) (M := M) g α
            (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
            (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
            (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
            (smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
              (smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical)) -
          (2 : ℝ) *
            chartPulledIntegralCLM (I := I) (M := M) g α
              (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
              (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
              (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
              (gradInnerSmooth (I := I) (M := M) g
                (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) (v n)) -
          chartPulledIntegralCLM (I := I) (M := M) g α
            (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
            (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
            (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
            (smoothMulLp (I := I) (M := M) g
              (laplacianOfChartPOU (I := I) (M := M) g α)
              (smoothToLp (I := I) (M := M) g (v n)))) from by
    funext n; rw [h_eq_smooth n, h_fHLeibniz_eq n]]
  rw [← h_target_eq]
  exact h_sum_lim

end

variable [NeZero (Module.finrank ℝ E)] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]
  [T2Space M] [CompactSpace M] in
theorem laplacianDomain_variational_identity
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        weightedInvGramOnEuclid (I := I) g α i j y *
          ((chartPushedWeakPartialLp (I := I) (M := M) g α i
            (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α i) u_h :
            Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y *
        Sobolev.Chart.chartPushed (I := I) (M := M)
          (chartAtlasPOU I M) α
          (((h1ComplToLp (I := I) (M := M) g u_h) :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) y * ψ y
      ∂(volume : Measure EuclN)) =
    chartPulledIntegralCLM (I := I) (M := M) g α
      (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
      (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
      (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
      (leibnizCompensatedSource (I := I) (M := M) g α u_h hu_h) := by
  classical
  obtain ⟨v, h_v_tendsto⟩ :=
    exists_smooth_approx_seq (I := I) (M := M) g u_h
  have h_smooth_case : ∀ n,
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            chartPushedPartial (I := I) (M := M) g α i (v n) y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN)) +
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          Sobolev.Chart.chartPushed (I := I) (M := M)
            (chartAtlasPOU I M) α (v n).toFun y * ψ y
        ∂(volume : Measure EuclN)) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          ((pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical.toFun)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          ψ y ∂(volume : Measure EuclN) := fun n =>
    laplacianDomain_variational_identity_smooth_case (I := I) (M := M) g α (v n)
      hψ hψ_cs hψ_support
  have h_per_i_tendsto : ∀ i : Fin (Module.finrank ℝ E),
      Tendsto (fun n =>
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chartPushedPartial (I := I) (M := M) g α i (v n) y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) atTop
      (𝓝 ⟪principalMultiplierLp (I := I) (M := M) g α i hψ hψ_cs hψ_support,
        chartPushedWeakPartialLp (I := I) (M := M) g α i
          (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α i) u_h⟫_ℝ) :=
    fun i => smooth_lhs_principal_per_i_tendsto (I := I) (M := M) g α i hψ hψ_cs hψ_support h_v_tendsto
  have h_swap_n : ∀ n,
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chartPushedPartial (I := I) (M := M) g α i (v n) y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∫ y in chartTargetEuclid (I := I) (M := M) α,
            (∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                chartPushedPartial (I := I) (M := M) g α i (v n) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
            ∂(volume : Measure EuclN) := by
    intro n
    set μ := (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α)
    have h_per_i_eq : ∀ i : Fin (Module.finrank ℝ E),
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chartPushedPartial (I := I) (M := M) g α i (v n) y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN) =
          ∫ y, principalMultiplier (I := I) (M := M) g α i ψ y *
              chartPushedPartial (I := I) (M := M) g α i (v n) y ∂μ := fun i =>
      smooth_lhs_principal_per_i_integral_eq_weighted (I := I) (M := M) g α i hψ (v n)
    have h_full_eq :
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
            (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                chartPushedPartial (I := I) (M := M) g α i (v n) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
            ∂(volume : Measure EuclN) =
          ∫ y, ∑ i : Fin (Module.finrank ℝ E),
            principalMultiplier (I := I) (M := M) g α i ψ y *
              chartPushedPartial (I := I) (M := M) g α i (v n) y ∂μ := by
      have h_meas_chartTarget : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
        (Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
      have h_pointwise : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chartPushedPartial (I := I) (M := M) g α i (v n) y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) =
          densityOnEuclid (I := I) g α y *
            (∑ i : Fin (Module.finrank ℝ E),
              principalMultiplier (I := I) (M := M) g α i ψ y *
                chartPushedPartial (I := I) (M := M) g α i (v n) y) := by
        intro y _hy
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        unfold principalMultiplier
        have h_each : ∀ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chartPushedPartial (I := I) (M := M) g α i (v n) y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1) =
            densityOnEuclid (I := I) g α y *
              (invGramOnEuclid (I := I) g α i j y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) *
              chartPushedPartial (I := I) (M := M) g α i (v n) y := by
          intro j
          show weightedInvGramOnEuclid (I := I) g α i j y *
              chartPushedPartial (I := I) (M := M) g α i (v n) y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1) = _
          rw [show weightedInvGramOnEuclid (I := I) g α i j y =
              densityOnEuclid (I := I) g α y * invGramOnEuclid (I := I) g α i j y from rfl]
          ring
        rw [Finset.sum_congr rfl (fun j _ => h_each j)]
        rw [← Finset.sum_mul, ← Finset.mul_sum]
        ring
      rw [MeasureTheory.setIntegral_congr_fun h_meas_chartTarget h_pointwise]
      change ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (∑ i : Fin (Module.finrank ℝ E),
              principalMultiplier (I := I) (M := M) g α i ψ y *
                chartPushedPartial (I := I) (M := M) g α i (v n) y)
          ∂(volume : Measure EuclN) = _
      rw [← setIntegral_chartPulledWeighted_eq_setIntegral_density_mul_volume
        (I := I) (M := M) g α
        (fun y => ∑ i : Fin (Module.finrank ℝ E),
          principalMultiplier (I := I) (M := M) g α i ψ y *
            chartPushedPartial (I := I) (M := M) g α i (v n) y)]
    have h_per_i_memLp_P : ∀ i : Fin (Module.finrank ℝ E),
        MemLp (principalMultiplier (I := I) (M := M) g α i ψ) 2 μ :=
      fun i => continuous_compactSupport_memLp_chartPulledWeighted_restrict
        (I := I) (M := M) g α
        (principalMultiplier_continuous (I := I) (M := M) g α i hψ hψ_support)
        (principalMultiplier_hasCompactSupport (I := I) (M := M) g α i hψ_cs)
        (principalMultiplier_tsupport_subset (I := I) (M := M) g α i hψ_support)
    have h_per_i_memLp_C : ∀ i : Fin (Module.finrank ℝ E),
        MemLp (chartPushedPartial (I := I) (M := M) g α i (v n)) 2 μ :=
      fun i => chartPushedPartial_memLp (I := I) (M := M) g α i (v n)
    have h_per_i_integrable : ∀ i : Fin (Module.finrank ℝ E),
        Integrable (fun y =>
          principalMultiplier (I := I) (M := M) g α i ψ y *
            chartPushedPartial (I := I) (M := M) g α i (v n) y) μ := by
      intro i
      have h_P := h_per_i_memLp_P i
      have h_C := h_per_i_memLp_C i
      exact MemLp.integrable_mul h_P h_C
    rw [h_full_eq]
    rw [MeasureTheory.integral_finsetSum _ (fun i _ => h_per_i_integrable i)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact (h_per_i_eq i).symm
  have h_lhs_principal_tendsto : Tendsto (fun n =>
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            chartPushedPartial (I := I) (M := M) g α i (v n) y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN)) atTop
    (𝓝 (∑ i : Fin (Module.finrank ℝ E),
      ⟪principalMultiplierLp (I := I) (M := M) g α i hψ hψ_cs hψ_support,
        chartPushedWeakPartialLp (I := I) (M := M) g α i
          (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α i) u_h⟫_ℝ)) := by
    rw [show (fun n =>
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chartPushedPartial (I := I) (M := M) g α i (v n) y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) =
      (fun n => ∑ i : Fin (Module.finrank ℝ E),
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chartPushedPartial (I := I) (M := M) g α i (v n) y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) from funext h_swap_n]
    exact tendsto_finsetSum _ (fun i _ => h_per_i_tendsto i)
  have h_lhs_mass_tendsto :=
    smooth_lhs_mass_tendsto (I := I) (M := M) g α hψ hψ_cs hψ_support h_v_tendsto
  have h_rhs_tendsto := rhs_smooth_tendsto_chartPulledIntegralCLM_fHLeibniz
    (I := I) (M := M) g α hψ hψ_cs hψ_support hu_h h_v_tendsto
  have h_lhs_sum_tendsto := h_lhs_principal_tendsto.add h_lhs_mass_tendsto
  have h_smooth_eq_fun : (fun n =>
      ((∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            chartPushedPartial (I := I) (M := M) g α i (v n) y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN)) +
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          Sobolev.Chart.chartPushed (I := I) (M := M)
            (chartAtlasPOU I M) α (v n).toFun y * ψ y
        ∂(volume : Measure EuclN)))) =
    fun n =>
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          ((pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical.toFun)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          ψ y ∂(volume : Measure EuclN) := funext h_smooth_case
  have h_LHS_eq_RHS_lim : (∑ i : Fin (Module.finrank ℝ E),
        ⟪principalMultiplierLp (I := I) (M := M) g α i hψ hψ_cs hψ_support,
          chartPushedWeakPartialLp (I := I) (M := M) g α i
            (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α i) u_h⟫_ℝ) +
      ⟪massMultiplierLp (I := I) (M := M) g α hψ hψ_cs hψ_support,
        chartPushedLpFromLp (I := I) (M := M) g α
          (h1ComplToLp (I := I) (M := M) g u_h)⟫_ℝ =
    chartPulledIntegralCLM (I := I) (M := M) g α
      (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_support)
      (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
      (densityPsi_support (I := I) (M := M) (g := g) (α := α) hψ_support)
      (leibnizCompensatedSource (I := I) (M := M) g α u_h hu_h) := by
    have h_seq_eq : (fun n =>
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chartPushedPartial (I := I) (M := M) g α i (v n) y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            Sobolev.Chart.chartPushed (I := I) (M := M)
              (chartAtlasPOU I M) α (v n).toFun y * ψ y
          ∂(volume : Measure EuclN))) =
      (fun n =>
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            ((pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical.toFun)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
            ψ y ∂(volume : Measure EuclN)) := h_smooth_eq_fun
    have h_lhs_lim : Tendsto (fun n =>
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chartPushedPartial (I := I) (M := M) g α i (v n) y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            Sobolev.Chart.chartPushed (I := I) (M := M)
              (chartAtlasPOU I M) α (v n).toFun y * ψ y
          ∂(volume : Measure EuclN))) atTop
      (𝓝 ((∑ i : Fin (Module.finrank ℝ E),
          ⟪principalMultiplierLp (I := I) (M := M) g α i hψ hψ_cs hψ_support,
            chartPushedWeakPartialLp (I := I) (M := M) g α i
              (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α i) u_h⟫_ℝ) +
        ⟪massMultiplierLp (I := I) (M := M) g α hψ hψ_cs hψ_support,
          chartPushedLpFromLp (I := I) (M := M) g α
            (h1ComplToLp (I := I) (M := M) g u_h)⟫_ℝ)) := h_lhs_sum_tendsto
    rw [h_seq_eq] at h_lhs_lim
    exact tendsto_nhds_unique h_lhs_lim h_rhs_tendsto
  rw [general_lhs_principal_eq_sum_inner (I := I) (M := M) g α hψ hψ_cs hψ_support u_h,
    general_lhs_mass_eq_inner (I := I) (M := M) g α hψ hψ_cs hψ_support u_h]
  exact h_LHS_eq_RHS_lim

end LaplacianDomainVariationalIdentityIntegralForm
end Laplacian
end Analysis
end CalabiYau

end
