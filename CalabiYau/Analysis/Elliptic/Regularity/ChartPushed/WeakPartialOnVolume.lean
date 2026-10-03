-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/ChartPushed/WeakPartialOnVolume.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.H1Compl.GradientH1LipschitzBound
public import CalabiYau.Analysis.Sobolev.Euclidean.WeakDerivative.Closedness
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

@[expose] public section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace CalabiYau
namespace Analysis
namespace Laplacian
namespace ChartPushedWeakPartialOnVolume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Laplacian.MetricExtension
  hiding chartTargetEuclid
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.H1ComplGradientChartBridge
open CalabiYau.Analysis.Laplacian.H1ComplGradientLipschitz
open CalabiYau.Analysis.Laplacian.H1ComplGradientLipschitzBound
open CalabiYau.Analysis.Laplacian.H1ComplGradientH1LipschitzBound
open CalabiYau.Analysis.Laplacian.H1ComplToLpChartBridge
open CalabiYau.Analysis.Laplacian.H1ComplWeakPartialLimit
open Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))


variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless] [T2Space M] [CompactSpace M] in
private noncomputable def extChartAtSymmExt (α : M) : E → M := by
  classical
  exact (extChartAt I α).target.piecewise
    (fun y : E => (extChartAt I α).symm y)
    (fun _ : E => α)

private lemma extChartAtSymmExt_eq_on_target (α : M) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    extChartAtSymmExt (I := I) (M := M) α y = (extChartAt I α).symm y := by
  classical
  change (extChartAt I α).target.piecewise
    (fun y : E => (extChartAt I α).symm y)
    (fun _ : E => α) y = _
  rw [Set.piecewise_eq_of_mem _ _ _ hy]

private lemma extChartAtSymmExt_measurable (α : M) :
    Measurable (extChartAtSymmExt (I := I) (M := M) α) := by
  classical
  unfold extChartAtSymmExt
  exact ContinuousOn.measurable_piecewise
    (continuousOn_extChartAt_symm (I := I) α)
    continuousOn_const
    (CalabiYau.RiemannianVolume.measurableSet_extChartAt_target
      (I := I) (M := M) α)

variable [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in
private lemma exists_density_inf_pos_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ c : ℝ, 0 < c ∧ ∀ y ∈ K, c ≤ densityOnEuclid (I := I) g α y := by
  classical
  by_cases hKne : K.Nonempty
  · have h_dens_contOn : ContinuousOn (densityOnEuclid (I := I) g α) K :=
      (densityOnEuclid_continuousOn (I := I) g α).mono hK_in
    obtain ⟨y₀, hy₀_mem, hy₀_min⟩ :=
      hK_compact.exists_isMinOn hKne h_dens_contOn
    have h_pos : 0 < densityOnEuclid (I := I) g α y₀ :=
      densityOnEuclid_pos (I := I) g α (hK_in hy₀_mem)
    refine ⟨densityOnEuclid (I := I) g α y₀, h_pos, fun y hy => hy₀_min hy⟩
  · refine ⟨1, by norm_num, ?_⟩
    intro y hy
    rw [Set.not_nonempty_iff_eq_empty] at hKne
    rw [hKne] at hy
    exact absurd hy (Set.notMem_empty y)

variable [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in
private lemma volume_restrict_le_smul_chartPulledWeightedMeasure_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ c : ℝ, 0 < c ∧
      (volume : Measure EuclN).restrict K ≤
        ENNReal.ofReal (c⁻¹) •
          (chartPulledWeightedMeasure (I := I) g α).restrict K := by
  classical
  obtain ⟨c, hc_pos, hc_le⟩ :=
    exists_density_inf_pos_on_compact (I := I) (M := M) g α hK_compact hK_in
  refine ⟨c, hc_pos, ?_⟩
  have hK_meas : MeasurableSet K := hK_compact.measurableSet
  refine Measure.le_iff.2 ?_
  intro A hA
  rw [Measure.smul_apply, Measure.restrict_apply hA, Measure.restrict_apply hA]
  unfold chartPulledWeightedMeasure
  rw [withDensity_apply _ (hA.inter hK_meas)]
  have hc_ne_zero : c ≠ 0 := ne_of_gt hc_pos
  have h_lower :
      ENNReal.ofReal c * (volume : Measure EuclN) (A ∩ K) ≤
        ∫⁻ y in A ∩ K, ENNReal.ofReal (densityOnEuclid (I := I) g α y)
          ∂(volume : Measure EuclN) := by
    have h_const :
        ENNReal.ofReal c * (volume : Measure EuclN) (A ∩ K) =
          ∫⁻ _y in A ∩ K, ENNReal.ofReal c ∂(volume : Measure EuclN) := by
      rw [MeasureTheory.setLIntegral_const]
    rw [h_const]
    refine MeasureTheory.setLIntegral_mono_ae' (hA.inter hK_meas) ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    exact ENNReal.ofReal_le_ofReal (hc_le y hy.2)
  have h_inv_pos : 0 < c⁻¹ := inv_pos.mpr hc_pos
  have h_inv_mul_eq : ENNReal.ofReal (c⁻¹) * ENNReal.ofReal c = 1 := by
    rw [← ENNReal.ofReal_mul (le_of_lt h_inv_pos),
        inv_mul_cancel₀ hc_ne_zero, ENNReal.ofReal_one]
  calc (volume : Measure EuclN) (A ∩ K)
      = 1 * (volume : Measure EuclN) (A ∩ K) := (one_mul _).symm
    _ = (ENNReal.ofReal (c⁻¹) * ENNReal.ofReal c) *
          (volume : Measure EuclN) (A ∩ K) := by rw [h_inv_mul_eq]
    _ = ENNReal.ofReal (c⁻¹) *
          (ENNReal.ofReal c * (volume : Measure EuclN) (A ∩ K)) := by
        rw [mul_assoc]
    _ ≤ ENNReal.ofReal (c⁻¹) *
          ∫⁻ y in A ∩ K, ENNReal.ofReal (densityOnEuclid (I := I) g α y)
            ∂(volume : Measure EuclN) := by gcongr

variable [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in
theorem eLpNorm_volume_restrict_le_eLpNorm_chartPulledWeighted_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : EuclN → ℝ),
      eLpNorm f 2 ((volume : Measure EuclN).restrict K) ≤
        ENNReal.ofReal C *
          eLpNorm f 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  obtain ⟨c, hc_pos, h_vol_le⟩ :=
    volume_restrict_le_smul_chartPulledWeightedMeasure_on_compact
      (I := I) (M := M) g α hK_compact hK_in
  refine ⟨Real.sqrt (c⁻¹), Real.sqrt_pos.mpr (inv_pos.mpr hc_pos), ?_⟩
  intro f
  have h_step1 :
      eLpNorm f 2 ((volume : Measure EuclN).restrict K) ≤
        eLpNorm f 2 (ENNReal.ofReal (c⁻¹) •
          (chartPulledWeightedMeasure (I := I) g α).restrict K) :=
    eLpNorm_mono_measure f h_vol_le
  have h_smul_eq :
      eLpNorm f 2 (ENNReal.ofReal (c⁻¹) •
          (chartPulledWeightedMeasure (I := I) g α).restrict K) =
        ENNReal.ofReal (c⁻¹) ^ ((1 : ℝ) / 2) •
          eLpNorm f 2 ((chartPulledWeightedMeasure (I := I) g α).restrict K) := by
    have h_toReal : ((1 / 2 : ℝ≥0∞).toReal : ℝ) = (1 : ℝ) / 2 := by
      rw [show (1 / 2 : ℝ≥0∞) = (1 : ℝ≥0∞) / 2 from rfl]
      simp
    rw [eLpNorm_smul_measure_of_ne_zero_of_ne_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
    rw [h_toReal]
  rw [h_smul_eq] at h_step1
  have hK_in_open :
      (chartPulledWeightedMeasure (I := I) g α).restrict K ≤
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α) :=
    Measure.restrict_mono hK_in (le_refl _)
  have h_mono_target :
      eLpNorm f 2 ((chartPulledWeightedMeasure (I := I) g α).restrict K) ≤
        eLpNorm f 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
    eLpNorm_mono_measure f hK_in_open
  have h_pow_eq : ENNReal.ofReal (c⁻¹) ^ ((1 : ℝ) / 2) =
      ENNReal.ofReal (Real.sqrt (c⁻¹)) := by
    rw [Real.sqrt_eq_rpow]
    rw [← ENNReal.ofReal_rpow_of_nonneg (le_of_lt (inv_pos.mpr hc_pos))
      (by positivity)]
  refine h_step1.trans ?_
  rw [h_pow_eq, smul_eq_mul]
  exact mul_le_mul' (le_refl _) h_mono_target

variable [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] in
private lemma memLp_of_chartPulledWeighted_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    {f : EuclN → ℝ}
    (hf_memLp : MemLp f 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))) :
    MemLp f 2 ((volume : Measure EuclN).restrict K) := by
  obtain ⟨C, _hC_pos, hC_bd⟩ :=
    eLpNorm_volume_restrict_le_eLpNorm_chartPulledWeighted_compact
      (I := I) (M := M) g α hK_compact hK_in
  refine memLp_iff.mpr ?_
  refine lt_of_le_of_lt (hC_bd f) ?_
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf_memLp.eLpNorm_lt_top

variable [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]
  [T2Space M] [CompactSpace M] in
theorem chartPushedWeakPartialLp_locally_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (u_h : H1Compl g)
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (((chartPushedWeakPartialLp (I := I) (M := M) g α j
      (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α j) u_h
     ) : EuclN → ℝ))
      2 ((volume : Measure EuclN).restrict K) := by
  classical
  have hf_memLp_weighted := MeasureTheory.Lp.memLp
    (chartPushedWeakPartialLp (I := I) (M := M) g α j
      (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α j) u_h)
  exact memLp_of_chartPulledWeighted_on_compact (I := I) (M := M) g α
    hK_compact hK_in hf_memLp_weighted

variable [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]
  [T2Space M] [CompactSpace M] in
private lemma exists_smoothApprox_seq
    (g : SmoothRiemannianMetric I M) (u_h : H1Compl g) :
    ∃ v : ℕ → SmoothScalar g,
      Tendsto (fun n => smoothToH1Compl (I := I) (M := M) g (v n))
        atTop (𝓝 u_h) := by
  classical
  have h_dense : DenseRange (smoothToH1Compl (I := I) (M := M) g) := by
    unfold smoothToH1Compl
    rw [show (UniformSpace.Completion.toComplL : SmoothScalar g → H1Compl g) =
        ((↑) : SmoothScalar g → UniformSpace.Completion (SmoothScalar g)) from
        UniformSpace.Completion.coe_toComplL]
    exact UniformSpace.Completion.denseRange_coe
  have h_in_closure : u_h ∈ closure
      (Set.range (smoothToH1Compl (I := I) (M := M) g)) := by
    rw [h_dense.closure_range]
    trivial
  rw [mem_closure_iff_seq_limit] at h_in_closure
  obtain ⟨xs, hxs_in_range, hxs_tendsto⟩ := h_in_closure
  choose v hv using fun n => hxs_in_range n
  refine ⟨v, ?_⟩
  have h_eq : (fun n => smoothToH1Compl (I := I) (M := M) g (v n)) = xs := by
    funext n; exact hv n
  rw [h_eq]
  exact hxs_tendsto

variable [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]
  [T2Space M] [CompactSpace M] in
private lemma chartPushed_lp_tendsto_of_smoothApprox
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl g} {v : ℕ → SmoothScalar g}
    (h_tendsto : Tendsto (fun n =>
      smoothToH1Compl (I := I) (M := M) g (v n)) atTop (𝓝 u_h)) :
    Tendsto (fun n => eLpNorm
      (fun y =>
        chartPushed (I := I) (M := M) (chartAtlasPOU I M) α (v n).toFun y -
          chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
            (((h1ComplToLp (I := I) (M := M) g u_h)) : M → ℝ) y) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))) atTop (𝓝 0) := by
  classical
  have h_lp_tendsto : Tendsto (fun n =>
      smoothToLp (I := I) (M := M) g (v n)) atTop
      (𝓝 (h1ComplToLp (I := I) (M := M) g u_h)) := by
    have h_compose : Tendsto (fun n => h1ComplToLp (I := I) (M := M) g
        (smoothToH1Compl (I := I) (M := M) g (v n))) atTop
        (𝓝 (h1ComplToLp (I := I) (M := M) g u_h)) :=
      ((h1ComplToLp (I := I) (M := M) g).continuous.tendsto _).comp h_tendsto
    have h_eq : (fun n => h1ComplToLp (I := I) (M := M) g
        (smoothToH1Compl (I := I) (M := M) g (v n))) =
        (fun n => smoothToLp (I := I) (M := M) g (v n)) := by
      funext n
      exact h1ComplToLp_smoothToH1Compl (I := I) (M := M) g (v n)
    rw [← h_eq]; exact h_compose
  have h_norm_tendsto : Tendsto (fun n =>
        ‖smoothToLp (I := I) (M := M) g (v n) -
          h1ComplToLp (I := I) (M := M) g u_h‖) atTop (𝓝 0) := by
    have h_sub : Tendsto (fun n => smoothToLp (I := I) (M := M) g (v n) -
        h1ComplToLp (I := I) (M := M) g u_h) atTop (𝓝 0) := by
      have := h_lp_tendsto.sub
        (tendsto_const_nhds (x := h1ComplToLp (I := I) (M := M) g u_h))
      simpa using this
    have hnorm := (continuous_norm.tendsto (0 :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))).comp h_sub
    rw [norm_zero] at hnorm
    exact hnorm.congr' (Filter.Eventually.of_forall fun _ ↦ rfl)
  have h_lp_eLpNorm_tendsto :
      Tendsto (fun n => eLpNorm
        (((smoothToLp (I := I) (M := M) g (v n) -
            h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)) 2
        (riemannianVolumeMeasure (I := I) (M := M) g)) atTop (𝓝 0) := by
    have h_eLpNorm_eq : ∀ n,
        eLpNorm (((smoothToLp (I := I) (M := M) g (v n) -
            h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)) 2
          (riemannianVolumeMeasure (I := I) (M := M) g) =
          ENNReal.ofReal ‖smoothToLp (I := I) (M := M) g (v n) -
            h1ComplToLp (I := I) (M := M) g u_h‖ := by
      intro n
      rw [Lp.norm_def]
      have h_sub_aeEq := MeasureTheory.Lp.coeFn_sub
        (smoothToLp (I := I) (M := M) g (v n))
        (h1ComplToLp (I := I) (M := M) g u_h)
      have h_eLp_congr := MeasureTheory.eLpNorm_congr_ae h_sub_aeEq (p := 2)
      rw [← h_eLp_congr]
      rw [ENNReal.ofReal_toReal
        ((Lp.memLp (smoothToLp (I := I) (M := M) g (v n) -
          h1ComplToLp (I := I) (M := M) g u_h)).eLpNorm_lt_top.ne)]
    have h_ofReal_tendsto :
        Tendsto (fun n => ENNReal.ofReal ‖smoothToLp (I := I) (M := M) g (v n) -
            h1ComplToLp (I := I) (M := M) g u_h‖) atTop (𝓝 0) := by
      have h_comp := (ENNReal.continuous_ofReal.tendsto 0).comp h_norm_tendsto
      simp only [Function.comp_def, ENNReal.ofReal_zero] at h_comp
      exact h_comp
    have h_funeq : (fun n => eLpNorm
        (((smoothToLp (I := I) (M := M) g (v n) -
            h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)) 2
          (riemannianVolumeMeasure (I := I) (M := M) g)) =
        (fun n => ENNReal.ofReal ‖smoothToLp (I := I) (M := M) g (v n) -
            h1ComplToLp (I := I) (M := M) g u_h‖) := funext h_eLpNorm_eq
    rw [h_funeq]; exact h_ofReal_tendsto
  set u_lim : M → ℝ := ((h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)
    with hu_lim_def
  have hu_lim_meas : Measurable u_lim := (Lp.stronglyMeasurable _).measurable
  have hu_meas : ∀ n, Measurable (v n).toFun := fun n =>
    (v n).smooth.continuous.measurable
  have h_aeEq_diff : ∀ n,
      (((smoothToLp (I := I) (M := M) g (v n) -
          h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      fun x => (v n).toFun x - u_lim x := by
    intro n
    have h_sub_coeFn := MeasureTheory.Lp.coeFn_sub
      (smoothToLp (I := I) (M := M) g (v n))
      (h1ComplToLp (I := I) (M := M) g u_h)
    have h_smooth_coeFn : ((smoothToLp (I := I) (M := M) g (v n)) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g] (v n).toFun :=
      MeasureTheory.MemLp.coeFn_toLp (v n).memLp_two
    have h_step1 : (fun x => ((smoothToLp (I := I) (M := M) g (v n)) : M → ℝ) x -
        ((h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ) x) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
        fun x => (v n).toFun x - u_lim x := by
      filter_upwards [h_smooth_coeFn] with x hx
      show ((smoothToLp (I := I) (M := M) g (v n)) : M → ℝ) x -
        ((h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ) x =
        (v n).toFun x - u_lim x
      rw [hx]
    have h_pi_form : (((smoothToLp (I := I) (M := M) g (v n) -
            h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
        fun x => ((smoothToLp (I := I) (M := M) g (v n)) : M → ℝ) x -
          ((h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ) x := by
      filter_upwards [h_sub_coeFn] with x hx
      rfl
    exact h_pi_form.trans h_step1
  have h_diff_tendsto :
      Tendsto (fun n => eLpNorm (fun x => (v n).toFun x - u_lim x) 2
        (riemannianVolumeMeasure (I := I) (M := M) g)) atTop (𝓝 0) := by
    have h_funeq : (fun n => eLpNorm
        (((smoothToLp (I := I) (M := M) g (v n) -
            h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)) 2
          (riemannianVolumeMeasure (I := I) (M := M) g)) =
        (fun n => eLpNorm (fun x => (v n).toFun x - u_lim x) 2
          (riemannianVolumeMeasure (I := I) (M := M) g)) := by
      funext n
      exact MeasureTheory.eLpNorm_congr_ae (h_aeEq_diff n)
    rw [← h_funeq]; exact h_lp_eLpNorm_tendsto
  exact chartPushed_tendsto_chartPulledWeightedMeasure (I := I) (M := M) g α
    hu_meas hu_lim_meas h_diff_tendsto

variable [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]
  [T2Space M] [CompactSpace M] in
private lemma chartPushedWeakPartial_lp_tendsto_of_smoothApprox
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    {u_h : H1Compl g} {v : ℕ → SmoothScalar g}
    (h_tendsto : Tendsto (fun n =>
      smoothToH1Compl (I := I) (M := M) g (v n)) atTop (𝓝 u_h)) :
    Tendsto (fun n => eLpNorm
      (fun y =>
        chartPushedPartial (I := I) (M := M) g α j (v n) y -
          ((chartPushedWeakPartialLp (I := I) (M := M) g α j
            (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α j)
            u_h) : EuclN → ℝ) y) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))) atTop (𝓝 0) := by
  classical
  have h_cwpL_tendsto : Tendsto (fun n => chartPushedWeakPartialLp
        (I := I) (M := M) g α j
        (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α j)
        (smoothToH1Compl (I := I) (M := M) g (v n))) atTop
      (𝓝 (chartPushedWeakPartialLp (I := I) (M := M) g α j
        (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α j) u_h)) := by
    have h_cont :
        Continuous (chartPushedWeakPartialLp (I := I) (M := M) g α j
          (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α j)) :=
      chartPushedWeakPartialLp_continuous (I := I) (M := M) g α j _
    exact (h_cont.tendsto _).comp h_tendsto
  have h_smoothCase : ∀ n, chartPushedWeakPartialLp (I := I) (M := M) g α j
        (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α j)
        (smoothToH1Compl (I := I) (M := M) g (v n)) =
        chartPushedPartialLp (I := I) (M := M) g α j (v n)
          (chartPushedPartial_memLp (I := I) (M := M) g α j (v n)) := fun n =>
    chartPushedWeakPartialLp_smoothToH1Compl (I := I) (M := M) g α j _ (v n)
  rw [show (fun n => chartPushedWeakPartialLp (I := I) (M := M) g α j
        (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α j)
        (smoothToH1Compl (I := I) (M := M) g (v n))) =
      (fun n => chartPushedPartialLp (I := I) (M := M) g α j (v n)
        (chartPushedPartial_memLp (I := I) (M := M) g α j (v n))) from
      funext h_smoothCase] at h_cwpL_tendsto
  have h_norm_tendsto :
      Tendsto (fun n => ‖chartPushedPartialLp (I := I) (M := M) g α j (v n)
          (chartPushedPartial_memLp (I := I) (M := M) g α j (v n)) -
        chartPushedWeakPartialLp (I := I) (M := M) g α j
          (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α j) u_h‖)
      atTop (𝓝 0) := by
    have h_sub : Tendsto (fun n => chartPushedPartialLp
          (I := I) (M := M) g α j (v n)
          (chartPushedPartial_memLp (I := I) (M := M) g α j (v n)) -
        chartPushedWeakPartialLp (I := I) (M := M) g α j
          (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α j) u_h)
        atTop (𝓝 0) := by
      have := h_cwpL_tendsto.sub
        (tendsto_const_nhds (x := chartPushedWeakPartialLp
          (I := I) (M := M) g α j
          (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α j) u_h))
      simpa using this
    have hnorm := (continuous_norm.tendsto (0 :
      Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)))).comp h_sub
    rw [norm_zero] at hnorm
    exact hnorm.congr' (Filter.Eventually.of_forall fun _ ↦ rfl)
  have h_eLpNorm_eq : ∀ n,
      eLpNorm (((chartPushedPartialLp (I := I) (M := M) g α j (v n)
            (chartPushedPartial_memLp (I := I) (M := M) g α j (v n)) -
          chartPushedWeakPartialLp (I := I) (M := M) g α j
            (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α j) u_h
         ) : EuclN → ℝ)) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) =
      ENNReal.ofReal ‖chartPushedPartialLp (I := I) (M := M) g α j (v n)
          (chartPushedPartial_memLp (I := I) (M := M) g α j (v n)) -
        chartPushedWeakPartialLp (I := I) (M := M) g α j
          (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α j) u_h‖ := by
    intro n
    rw [Lp.norm_def]
    have h_sub_aeEq := MeasureTheory.Lp.coeFn_sub
      (chartPushedPartialLp (I := I) (M := M) g α j (v n)
        (chartPushedPartial_memLp (I := I) (M := M) g α j (v n)))
      (chartPushedWeakPartialLp (I := I) (M := M) g α j
        (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α j) u_h)
    have h_eLp_congr := MeasureTheory.eLpNorm_congr_ae h_sub_aeEq (p := 2)
    rw [← h_eLp_congr]
    rw [ENNReal.ofReal_toReal
      ((Lp.memLp (chartPushedPartialLp (I := I) (M := M) g α j (v n)
        (chartPushedPartial_memLp (I := I) (M := M) g α j (v n)) -
        chartPushedWeakPartialLp (I := I) (M := M) g α j
          (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α j)
          u_h)).eLpNorm_lt_top.ne)]
  have h_lp_eLpNorm_tendsto :
      Tendsto (fun n =>
        eLpNorm (((chartPushedPartialLp (I := I) (M := M) g α j (v n)
            (chartPushedPartial_memLp (I := I) (M := M) g α j (v n)) -
          chartPushedWeakPartialLp (I := I) (M := M) g α j
            (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α j) u_h
         ) : EuclN → ℝ)) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) atTop (𝓝 0) := by
    have h_comp := (ENNReal.continuous_ofReal.tendsto 0).comp h_norm_tendsto
    simp only [Function.comp_def, ENNReal.ofReal_zero] at h_comp
    have h_funeq : (fun n =>
        eLpNorm (((chartPushedPartialLp (I := I) (M := M) g α j (v n)
            (chartPushedPartial_memLp (I := I) (M := M) g α j (v n)) -
          chartPushedWeakPartialLp (I := I) (M := M) g α j
            (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α j) u_h
         ) : EuclN → ℝ)) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) =
        (fun n => ENNReal.ofReal ‖chartPushedPartialLp (I := I) (M := M) g α j (v n)
            (chartPushedPartial_memLp (I := I) (M := M) g α j (v n)) -
          chartPushedWeakPartialLp (I := I) (M := M) g α j
            (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α j) u_h‖) :=
      funext h_eLpNorm_eq
    rw [h_funeq]; exact h_comp
  have h_aeEq_diff : ∀ n,
      (((chartPushedPartialLp (I := I) (M := M) g α j (v n)
            (chartPushedPartial_memLp (I := I) (M := M) g α j (v n)) -
          chartPushedWeakPartialLp (I := I) (M := M) g α j
            (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α j) u_h
       ) : EuclN → ℝ)) =ᵐ[
          (chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)]
        fun y => chartPushedPartial (I := I) (M := M) g α j (v n) y -
          ((chartPushedWeakPartialLp (I := I) (M := M) g α j
              (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α j) u_h
           ) : EuclN → ℝ) y := by
    intro n
    have h_sub_coeFn := MeasureTheory.Lp.coeFn_sub
      (chartPushedPartialLp (I := I) (M := M) g α j (v n)
        (chartPushedPartial_memLp (I := I) (M := M) g α j (v n)))
      (chartPushedWeakPartialLp (I := I) (M := M) g α j
        (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α j) u_h)
    have h_partialLp_coeFn :
        (((chartPushedPartialLp (I := I) (M := M) g α j (v n)
            (chartPushedPartial_memLp (I := I) (M := M) g α j (v n))
         ) : EuclN → ℝ)) =ᵐ[
            (chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α)]
          chartPushedPartial (I := I) (M := M) g α j (v n) := by
      unfold chartPushedPartialLp
      exact MeasureTheory.MemLp.coeFn_toLp _
    have h_step1 : (fun y => ((chartPushedPartialLp (I := I) (M := M) g α j (v n)
            (chartPushedPartial_memLp (I := I) (M := M) g α j (v n))
           ) : EuclN → ℝ) y -
          ((chartPushedWeakPartialLp (I := I) (M := M) g α j
              (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α j) u_h
           ) : EuclN → ℝ) y) =ᵐ[
          (chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)]
        fun y => chartPushedPartial (I := I) (M := M) g α j (v n) y -
          ((chartPushedWeakPartialLp (I := I) (M := M) g α j
              (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α j) u_h
           ) : EuclN → ℝ) y := by
      filter_upwards [h_partialLp_coeFn] with y hy
      show ((chartPushedPartialLp (I := I) (M := M) g α j (v n)
            (chartPushedPartial_memLp (I := I) (M := M) g α j (v n))
           ) : EuclN → ℝ) y -
          ((chartPushedWeakPartialLp (I := I) (M := M) g α j
              (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α j) u_h
           ) : EuclN → ℝ) y =
        chartPushedPartial (I := I) (M := M) g α j (v n) y -
          ((chartPushedWeakPartialLp (I := I) (M := M) g α j
              (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α j) u_h
           ) : EuclN → ℝ) y
      rw [hy]
    have h_pi_form : (((chartPushedPartialLp (I := I) (M := M) g α j (v n)
            (chartPushedPartial_memLp (I := I) (M := M) g α j (v n)) -
          chartPushedWeakPartialLp (I := I) (M := M) g α j
            (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α j) u_h
         ) : EuclN → ℝ)) =ᵐ[
          (chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)]
        fun y => ((chartPushedPartialLp (I := I) (M := M) g α j (v n)
              (chartPushedPartial_memLp (I := I) (M := M) g α j (v n))
           ) : EuclN → ℝ) y -
          ((chartPushedWeakPartialLp (I := I) (M := M) g α j
              (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α j) u_h
           ) : EuclN → ℝ) y := by
      filter_upwards [h_sub_coeFn] with y hy
      rfl
    exact h_pi_form.trans h_step1
  have h_eLpNorm_funeq : ∀ n,
      eLpNorm (((chartPushedPartialLp (I := I) (M := M) g α j (v n)
            (chartPushedPartial_memLp (I := I) (M := M) g α j (v n)) -
          chartPushedWeakPartialLp (I := I) (M := M) g α j
            (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α j) u_h
         ) : EuclN → ℝ)) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) =
      eLpNorm
        (fun y => chartPushedPartial (I := I) (M := M) g α j (v n) y -
          ((chartPushedWeakPartialLp (I := I) (M := M) g α j
              (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α j) u_h
           ) : EuclN → ℝ) y) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := fun n =>
    MeasureTheory.eLpNorm_congr_ae (h_aeEq_diff n)
  have h_funeq2 : (fun n =>
        eLpNorm (((chartPushedPartialLp (I := I) (M := M) g α j (v n)
            (chartPushedPartial_memLp (I := I) (M := M) g α j (v n)) -
          chartPushedWeakPartialLp (I := I) (M := M) g α j
            (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α j) u_h
         ) : EuclN → ℝ)) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) =
      (fun n => eLpNorm
        (fun y => chartPushedPartial (I := I) (M := M) g α j (v n) y -
          ((chartPushedWeakPartialLp (I := I) (M := M) g α j
              (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α j) u_h
           ) : EuclN → ℝ) y) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) :=
    funext h_eLpNorm_funeq
  rw [← h_funeq2]; exact h_lp_eLpNorm_tendsto

variable [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M] in
private lemma chartPushed_eqOn_chartTarget_smoothChartExt
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    Set.EqOn (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α v.toFun)
      (smoothChartExt (I := I) (M := M) g α v)
      (chartTargetEuclid (I := I) (M := M) α) := by
  intro y hy
  classical
  have h_toE_symm_in : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rcases hy with ⟨w, hw_target, hwy⟩
    have h_eq : (toEuclidean (E := E)).symm y = w := by
      rw [← hwy]; exact (toEuclidean (E := E)).symm_apply_apply w
    rw [h_eq]; exact hw_target
  rw [smoothChartExt_apply_of_mem_target (I := I) (M := M) g α v h_toE_symm_in]
  unfold chartPushed
  rfl

variable [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]
  [T2Space M] [CompactSpace M] in
private lemma hasWeakPartialDeriv_chartPushedPartial_smooth
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (v : SmoothScalar g)
    {Ω : Set EuclN} (hΩ_open : IsOpen Ω)
    (hΩ_in : Ω ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Sobolev.Euclidean.HasWeakPartialDeriv (d := Module.finrank ℝ E) j
      (chartPushedPartial (I := I) (M := M) g α j v)
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α v.toFun) Ω := by
  classical
  intro φ hφ_smooth hφ_support hφ_sub
  have h_chartTarget_eqOn := chartPushed_eqOn_chartTarget_smoothChartExt (I := I) (M := M) g α v
  have h_eq_on : Set.EqOn (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α v.toFun)
      (smoothChartExt (I := I) (M := M) g α v) Ω :=
    h_chartTarget_eqOn.mono hΩ_in
  have h_partial_eq_on : Set.EqOn (chartPushedPartial (I := I) (M := M) g α j v)
      (smoothChartExtPartial (I := I) (M := M) g α j v) Ω := by
    intro y hy
    exact chartPushedPartial_eq_smoothChartExtPartial_on_target
      (I := I) (M := M) g α j v (hΩ_in hy)
  have h_smooth_contDiff : ContDiff ℝ ∞ (smoothChartExt (I := I) (M := M) g α v) :=
    smoothChartExt_contDiff (I := I) (M := M) g α v
  have h_smooth_C1 : ContDiff ℝ 1 (smoothChartExt (I := I) (M := M) g α v) :=
    h_smooth_contDiff.of_le (by norm_cast)
  have h_weak_smooth :
      Sobolev.Euclidean.HasWeakPartialDeriv (d := Module.finrank ℝ E) j
        (fun y => (fderiv ℝ (smoothChartExt (I := I) (M := M) g α v) y)
          (EuclideanSpace.single j 1))
        (smoothChartExt (I := I) (M := M) g α v) Ω :=
    Sobolev.Euclidean.HasWeakPartialDeriv.of_contDiff h_smooth_C1
  have h_identity := h_weak_smooth φ hφ_smooth hφ_support hφ_sub
  have h_LHS_eq :
      ∫ x in Ω, chartPushed (I := I) (M := M) (chartAtlasPOU I M) α v.toFun x *
          (fderiv ℝ φ x) (EuclideanSpace.single j 1) =
        ∫ x in Ω, smoothChartExt (I := I) (M := M) g α v x *
          (fderiv ℝ φ x) (EuclideanSpace.single j 1) := by
    apply setIntegral_congr_fun hΩ_open.measurableSet
    intro x hx
    simp only
    rw [h_eq_on hx]
  have h_RHS_eq :
      ∫ x in Ω, chartPushedPartial (I := I) (M := M) g α j v x * φ x =
        ∫ x in Ω, smoothChartExtPartial (I := I) (M := M) g α j v x * φ x := by
    apply setIntegral_congr_fun hΩ_open.measurableSet
    intro x hx
    simp only
    rw [h_partial_eq_on hx]
  change ∫ x in Ω, chartPushed (I := I) (M := M) (chartAtlasPOU I M) α v.toFun x *
        (fderiv ℝ φ x) (EuclideanSpace.single j 1) =
      -∫ x in Ω, chartPushedPartial (I := I) (M := M) g α j v x * φ x
  rw [h_LHS_eq, h_RHS_eq]
  unfold smoothChartExtPartial
  exact h_identity

variable [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]
  [T2Space M] [CompactSpace M] in
theorem hasWeakPartialDeriv_chartPushedWeakPartialLp_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (u_h : H1Compl g)
    {Ω : Set EuclN} (hΩ_open : IsOpen Ω)
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hΩ_in_K : Ω ⊆ K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Sobolev.Euclidean.HasWeakPartialDeriv (d := Module.finrank ℝ E) j
      (((chartPushedWeakPartialLp (I := I) (M := M) g α j
        (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α j) u_h
       ) : EuclN → ℝ))
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)) Ω := by
  classical
  obtain ⟨v, h_tendsto⟩ :=
    exists_smoothApprox_seq (I := I) (M := M) g u_h
  obtain ⟨C_vol, _hC_vol_pos, hC_vol_bd⟩ :=
    eLpNorm_volume_restrict_le_eLpNorm_chartPulledWeighted_compact
      (I := I) (M := M) g α hK_compact hK_in
  have h_vol_Ω_le_K : (volume : Measure EuclN).restrict Ω ≤
      (volume : Measure EuclN).restrict K :=
    Measure.restrict_mono hΩ_in_K (le_refl _)
  have hC_vol_Ω : ∀ (f : EuclN → ℝ),
      eLpNorm f 2 ((volume : Measure EuclN).restrict Ω) ≤
        ENNReal.ofReal C_vol *
          eLpNorm f 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := fun f =>
    (eLpNorm_mono_measure f h_vol_Ω_le_K).trans (hC_vol_bd f)
  have h_func_tendsto :=
    chartPushed_lp_tendsto_of_smoothApprox (I := I) (M := M) g α h_tendsto
  have h_partial_tendsto :=
    chartPushedWeakPartial_lp_tendsto_of_smoothApprox
      (I := I) (M := M) g α j h_tendsto
  have h_func_tendsto_vol :
      Tendsto (fun n => eLpNorm
        (fun y =>
          chartPushed (I := I) (M := M) (chartAtlasPOU I M) α (v n).toFun y -
            chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
              ((h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ) y) 2
        ((volume : Measure EuclN).restrict Ω))
      atTop (𝓝 0) := by
    have h_const_mul_tendsto :
        Tendsto (fun n => ENNReal.ofReal C_vol *
          eLpNorm
            (fun y =>
              chartPushed (I := I) (M := M) (chartAtlasPOU I M) α (v n).toFun y -
                chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
                  ((h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ) y) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))) atTop (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C_vol)
        (b := 0) h_func_tendsto
        (Or.inr ENNReal.ofReal_ne_top)
      simpa using h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds h_const_mul_tendsto
      (fun _ => zero_le) (fun n => hC_vol_Ω _)
  have h_partial_tendsto_vol :
      Tendsto (fun n => eLpNorm
        (fun y =>
          chartPushedPartial (I := I) (M := M) g α j (v n) y -
            ((chartPushedWeakPartialLp (I := I) (M := M) g α j
              (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α j)
              u_h) : EuclN → ℝ) y) 2
        ((volume : Measure EuclN).restrict Ω))
      atTop (𝓝 0) := by
    have h_const_mul_tendsto :
        Tendsto (fun n => ENNReal.ofReal C_vol *
          eLpNorm
            (fun y =>
              chartPushedPartial (I := I) (M := M) g α j (v n) y -
                ((chartPushedWeakPartialLp (I := I) (M := M) g α j
                  (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α j)
                  u_h) : EuclN → ℝ) y) 2
              ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α))) atTop (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C_vol)
        (b := 0) h_partial_tendsto
        (Or.inr ENNReal.ofReal_ne_top)
      simpa using h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds h_const_mul_tendsto
      (fun _ => zero_le) (fun n => hC_vol_Ω _)
  set u_n_chart : ℕ → EuclN → ℝ := fun n =>
    chartPushed (I := I) (M := M) (chartAtlasPOU I M) α (v n).toFun
    with hu_n_chart_def
  set u_lim_chart : EuclN → ℝ :=
    chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
      ((h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)
    with hu_lim_chart_def
  set g_n_chart : ℕ → EuclN → ℝ :=
    fun n => chartPushedPartial (I := I) (M := M) g α j (v n)
    with hg_n_chart_def
  set g_lim_chart : EuclN → ℝ :=
    ((chartPushedWeakPartialLp (I := I) (M := M) g α j
      (chartPushedPartialLipschitzCanonical (I := I) (M := M) g α j) u_h
     ) : EuclN → ℝ)
    with hg_lim_chart_def
  have hu_n_aestrong_w : ∀ n,
      AEStronglyMeasurable (u_n_chart n)
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
    intro n
    refine (chartPushed_memLp_chartPulledWeightedMeasure_restrict_of_memLp
      (I := I) (M := M) g α (v n).smooth.continuous.measurable
      (v n).memLp_two).aestronglyMeasurable
  have hu_lim_aestrong_w :
      AEStronglyMeasurable u_lim_chart
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
    refine (chartPushed_memLp_chartPulledWeightedMeasure_restrict_of_memLp
      (I := I) (M := M) g α ((Lp.stronglyMeasurable _).measurable)
      (Lp.memLp _)).aestronglyMeasurable
  have hu_n_memLp_w : ∀ n,
      MemLp (u_n_chart n) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := fun n =>
    chartPushed_memLp_chartPulledWeightedMeasure_restrict_of_memLp
      (I := I) (M := M) g α (v n).smooth.continuous.measurable
      (v n).memLp_two
  have hu_lim_memLp_w :
      MemLp u_lim_chart 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
    chartPushed_memLp_chartPulledWeightedMeasure_restrict_of_memLp
      (I := I) (M := M) g α ((Lp.stronglyMeasurable _).measurable) (Lp.memLp _)
  have hg_n_memLp_w : ∀ n,
      MemLp (g_n_chart n) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := fun n =>
    chartPushedPartial_memLp (I := I) (M := M) g α j (v n)
  have hg_lim_memLp_w :
      MemLp g_lim_chart 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
    MeasureTheory.Lp.memLp _
  have hu_n_aestrong : ∀ n,
      AEStronglyMeasurable (u_n_chart n) ((volume : Measure EuclN).restrict Ω) := by
    intro n
    have h_w : AEStronglyMeasurable (u_n_chart n)
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := (hu_n_memLp_w n).aestronglyMeasurable
    set ψ : EuclN → ℝ := fun y =>
        ((chartAtlasPOU I M α : M → ℝ)
          (extChartAtSymmExt (I := I) (M := M) α ((toEuclidean (E := E)).symm y))) *
        (v n).toFun (extChartAtSymmExt (I := I) (M := M) α ((toEuclidean (E := E)).symm y))
      with hψ_def
    have hψ_meas : Measurable ψ := by
      refine Measurable.mul ?_ ?_
      · exact ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff.continuous.measurable).comp
          ((extChartAtSymmExt_measurable (I := I) (M := M) α).comp
            (toEuclidean (E := E)).symm.continuous.measurable)
      · exact ((v n).smooth.continuous.measurable).comp
          ((extChartAtSymmExt_measurable (I := I) (M := M) α).comp
            (toEuclidean (E := E)).symm.continuous.measurable)
    have h_ψ_eq : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
        ψ y = u_n_chart n y := by
      intro y hy
      have h_toE_symm_in : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
        rcases hy with ⟨w, hw_target, hwy⟩
        have h_eq : (toEuclidean (E := E)).symm y = w := by
          rw [← hwy]; exact (toEuclidean (E := E)).symm_apply_apply w
        rw [h_eq]; exact hw_target
      change ((chartAtlasPOU I M α : M → ℝ)
          (extChartAtSymmExt (I := I) (M := M) α ((toEuclidean (E := E)).symm y))) *
        (v n).toFun (extChartAtSymmExt (I := I) (M := M) α ((toEuclidean (E := E)).symm y)) =
        u_n_chart n y
      rw [extChartAtSymmExt_eq_on_target (I := I) (M := M) α h_toE_symm_in]
      rfl
    have h_aeEq : u_n_chart n =ᵐ[(volume : Measure EuclN).restrict Ω] ψ := by
      refine (MeasureTheory.ae_restrict_iff' hΩ_open.measurableSet).mpr ?_
      refine Filter.Eventually.of_forall (fun y hy => ?_)
      exact (h_ψ_eq y (hK_in (hΩ_in_K hy))).symm
    exact hψ_meas.aestronglyMeasurable.congr h_aeEq.symm
  have hu_lim_aestrong :
      AEStronglyMeasurable u_lim_chart ((volume : Measure EuclN).restrict Ω) := by
    set u_lim_M : M → ℝ := ((h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)
      with hu_lim_M_def
    have hu_lim_M_meas : Measurable u_lim_M :=
      (Lp.stronglyMeasurable _).measurable
    set ψ : EuclN → ℝ := fun y =>
        ((chartAtlasPOU I M α : M → ℝ)
          (extChartAtSymmExt (I := I) (M := M) α ((toEuclidean (E := E)).symm y))) *
        u_lim_M (extChartAtSymmExt (I := I) (M := M) α ((toEuclidean (E := E)).symm y))
      with hψ_def
    have hψ_meas : Measurable ψ := by
      refine Measurable.mul ?_ ?_
      · exact ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff.continuous.measurable).comp
          ((extChartAtSymmExt_measurable (I := I) (M := M) α).comp
            (toEuclidean (E := E)).symm.continuous.measurable)
      · exact hu_lim_M_meas.comp
          ((extChartAtSymmExt_measurable (I := I) (M := M) α).comp
            (toEuclidean (E := E)).symm.continuous.measurable)
    have h_ψ_eq : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
        ψ y = u_lim_chart y := by
      intro y hy
      have h_toE_symm_in : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
        rcases hy with ⟨w, hw_target, hwy⟩
        have h_eq : (toEuclidean (E := E)).symm y = w := by
          rw [← hwy]; exact (toEuclidean (E := E)).symm_apply_apply w
        rw [h_eq]; exact hw_target
      change ((chartAtlasPOU I M α : M → ℝ)
          (extChartAtSymmExt (I := I) (M := M) α ((toEuclidean (E := E)).symm y))) *
        u_lim_M (extChartAtSymmExt (I := I) (M := M) α ((toEuclidean (E := E)).symm y)) =
        u_lim_chart y
      rw [extChartAtSymmExt_eq_on_target (I := I) (M := M) α h_toE_symm_in]
      rfl
    have h_aeEq : u_lim_chart =ᵐ[(volume : Measure EuclN).restrict Ω] ψ := by
      refine (MeasureTheory.ae_restrict_iff' hΩ_open.measurableSet).mpr ?_
      refine Filter.Eventually.of_forall (fun y hy => ?_)
      exact (h_ψ_eq y (hK_in (hΩ_in_K hy))).symm
    exact hψ_meas.aestronglyMeasurable.congr h_aeEq.symm
  have hg_n_aestrong : ∀ n,
      AEStronglyMeasurable (g_n_chart n) ((volume : Measure EuclN).restrict Ω) := by
    intro n
    have h_smooth_strong : StronglyMeasurable
        (smoothChartExtPartial (I := I) (M := M) g α j (v n)) :=
      (smoothChartExtPartial_continuous (I := I) (M := M) g α j (v n)).stronglyMeasurable
    have h_aeEq : g_n_chart n =ᵐ[(volume : Measure EuclN).restrict Ω]
        smoothChartExtPartial (I := I) (M := M) g α j (v n) := by
      refine (MeasureTheory.ae_restrict_iff' hΩ_open.measurableSet).mpr ?_
      refine Filter.Eventually.of_forall (fun y hy => ?_)
      exact chartPushedPartial_eq_smoothChartExtPartial_on_target
        (I := I) (M := M) g α j (v n) (hΩ_in_K hy |> hK_in)
    exact h_smooth_strong.aestronglyMeasurable.congr h_aeEq.symm
  have hg_lim_aestrong :
      AEStronglyMeasurable g_lim_chart ((volume : Measure EuclN).restrict Ω) :=
    (Lp.stronglyMeasurable _).aestronglyMeasurable
  have hu_n_memLp : ∀ n, MemLp (u_n_chart n) 2 ((volume : Measure EuclN).restrict Ω) := by
    intro n
    refine memLp_iff.mpr ?_
    refine lt_of_le_of_lt (hC_vol_Ω _) ?_
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hu_n_memLp_w n).eLpNorm_lt_top
  have hu_lim_memLp : MemLp u_lim_chart 2 ((volume : Measure EuclN).restrict Ω) := by
    refine memLp_iff.mpr ?_
    refine lt_of_le_of_lt (hC_vol_Ω _) ?_
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu_lim_memLp_w.eLpNorm_lt_top
  have hg_n_memLp : ∀ n, MemLp (g_n_chart n) 2 ((volume : Measure EuclN).restrict Ω) := by
    intro n
    refine memLp_iff.mpr ?_
    refine lt_of_le_of_lt (hC_vol_Ω _) ?_
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hg_n_memLp_w n).eLpNorm_lt_top
  have hg_lim_memLp : MemLp g_lim_chart 2 ((volume : Measure EuclN).restrict Ω) := by
    refine memLp_iff.mpr ?_
    refine lt_of_le_of_lt (hC_vol_Ω _) ?_
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg_lim_memLp_w.eLpNorm_lt_top
  have h_weak_n : ∀ n,
      Sobolev.Euclidean.HasWeakPartialDeriv (d := Module.finrank ℝ E) j
        (g_n_chart n) (u_n_chart n) Ω := by
    intro n
    change Sobolev.Euclidean.HasWeakPartialDeriv (d := Module.finrank ℝ E) j
      (chartPushedPartial (I := I) (M := M) g α j (v n))
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α (v n).toFun) Ω
    refine hasWeakPartialDeriv_chartPushedPartial_smooth
      (I := I) (M := M) g α j (v n) hΩ_open ?_
    exact hΩ_in_K.trans hK_in
  exact Sobolev.Euclidean.hasWeakPartialDeriv_of_tendsto_eLpNorm
    (d := Module.finrank ℝ E)
    (p := 2) (by norm_num) j
    (u_n := u_n_chart) (g_n := g_n_chart)
    (u := u_lim_chart) (g := g_lim_chart)
    hu_n_memLp hg_n_memLp hu_lim_memLp hg_lim_memLp h_weak_n
    h_func_tendsto_vol h_partial_tendsto_vol

end ChartPushedWeakPartialOnVolume
end Laplacian
end Analysis
end CalabiYau

end
