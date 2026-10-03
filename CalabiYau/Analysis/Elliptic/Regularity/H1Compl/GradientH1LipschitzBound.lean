-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/H1Compl/GradientH1LipschitzBound.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.H1Compl.GradientLipschitzBound
public import CalabiYau.Analysis.Elliptic.Regularity.H1Compl.WeakPartialLimit
public import CalabiYau.Analysis.Sobolev.Intrinsic.Equivalence.IntrinsicToChart.ComponentNormBound
public import CalabiYau.Analysis.Sobolev.Chart.RiemannianMeasureComparison
public import CalabiYau.Analysis.Sobolev.Manifold.Measure.UniformChartComparison
public import CalabiYau.Geometry.Riemannian.Operator.Gradient.NormSquared
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic

@[expose] public section
open CalabiYau.Riemannian

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace CalabiYau
namespace Analysis
namespace Laplacian
namespace H1ComplGradientH1LipschitzBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Laplacian.MetricExtension
  hiding chartTargetEuclid
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.H1ComplGradientChartBridge
open CalabiYau.Analysis.Laplacian.H1ComplGradientLipschitz
open CalabiYau.Analysis.Laplacian.H1ComplGradientLipschitzBound
open CalabiYau.Analysis.Laplacian.H1ComplToLpChartBridge
open CalabiYau.Analysis.Laplacian.H1ComplWeakPartialLimit
open Sobolev.Chart
open Sobolev.EquivalenceReverse

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartPushedPartial_eq_fderiv_chartSmoothExt
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (v : SmoothScalar g) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushedPartial (I := I) (M := M) g α j v y =
      (fderiv ℝ (chartSmoothExt (I := I) (M := M) α
        (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * v.toFun x)) y)
        (EuclideanSpace.single j 1) := by
  classical
  unfold chartPushedPartial
  congr 1
  have hOpen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [hOpen.mem_nhds hy] with z hz
  classical
  rcases hz with ⟨w, hw_target, hwz⟩
  have h_eq : (toEuclidean (E := E)).symm z = w := by
    rw [← hwz]; exact (toEuclidean (E := E)).symm_apply_apply w
  have h_chartPushed : chartPushed (I := I) (M := M) (chartAtlasPOU I M) α v.toFun z =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) *
        v.toFun ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) := by
    unfold chartPushed
    rfl
  rw [h_chartPushed]
  have h_chartSmoothExt : chartSmoothExt (I := I) (M := M) α
      (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * v.toFun x) z =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) *
        v.toFun ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) := by
    have h_eq_z : (toEuclidean (E := E)).symm z ∈ (extChartAt I α).target := by
      rw [h_eq]; exact hw_target
    change (if (toEuclidean (E := E)).symm z ∈ (extChartAt I α).target then
        (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * v.toFun x)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
      else 0) = _
    rw [ite_eq_left h_eq_z]
  rw [h_chartSmoothExt]

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartPushedPartial_aeEq_fderiv_chartSmoothExt
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (v : SmoothScalar g) :
    chartPushedPartial (I := I) (M := M) g α j v =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      (fun y : EuclN => (fderiv ℝ (chartSmoothExt (I := I) (M := M) α
        (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * v.toFun x)) y)
        (EuclideanSpace.single j 1)) := by
  refine (MeasureTheory.ae_restrict_iff'
    (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
  refine Filter.Eventually.of_forall (fun y hy => ?_)
  exact chartPushedPartial_eq_fderiv_chartSmoothExt (I := I) (M := M) g α j v hy

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma chartPulledWeightedMeasure_le_smul_volume_on_kPouCompact
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∃ M_d : ℝ, 0 ≤ M_d ∧
      (chartPulledWeightedMeasure (I := I) g α).restrict
          (kPouCompact (I := I) (M := M) α) ≤
        ENNReal.ofReal M_d •
          (volume : Measure EuclN).restrict (kPouCompact (I := I) (M := M) α) := by
  classical
  obtain ⟨M_d, hM_d_pos, hM_d_bd⟩ :=
    exists_density_sup_on_kPouCompact (I := I) (M := M) g α
  refine ⟨M_d, hM_d_pos.le, ?_⟩
  have hK_meas : MeasurableSet (kPouCompact (I := I) (M := M) α) :=
    (kPouCompact_isCompact (I := I) (M := M) α).measurableSet
  refine Measure.le_iff.2 ?_
  intro A hA
  rw [Measure.smul_apply, Measure.restrict_apply hA, Measure.restrict_apply hA]
  unfold chartPulledWeightedMeasure
  rw [withDensity_apply _ (hA.inter hK_meas)]
  calc ∫⁻ y in A ∩ kPouCompact (I := I) (M := M) α,
          ENNReal.ofReal (densityOnEuclid (I := I) g α y) ∂(volume : Measure EuclN)
      ≤ ∫⁻ _y in A ∩ kPouCompact (I := I) (M := M) α,
          ENNReal.ofReal M_d ∂(volume : Measure EuclN) := by
        refine MeasureTheory.setLIntegral_mono_ae' (hA.inter hK_meas) ?_
        refine Filter.Eventually.of_forall (fun y hy => ?_)
        exact ENNReal.ofReal_le_ofReal (hM_d_bd y hy.2)
    _ = ENNReal.ofReal M_d * (volume : Measure EuclN)
          (A ∩ kPouCompact (I := I) (M := M) α) := by
        rw [MeasureTheory.setLIntegral_const]
    _ = ENNReal.ofReal M_d • (volume : Measure EuclN)
          (A ∩ kPouCompact (I := I) (M := M) α) := by rw [smul_eq_mul]

private noncomputable def chartPulledWeightedConst
    (g : SmoothRiemannianMetric I M) (α : M) : ℝ :=
  Real.sqrt (chartPulledWeightedMeasure_le_smul_volume_on_kPouCompact (I := I) (M := M) g α).choose

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma chartPulledWeightedConst_nonneg
    (g : SmoothRiemannianMetric I M) (α : M) :
    0 ≤ chartPulledWeightedConst (I := I) (M := M) g α := Real.sqrt_nonneg _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma eLpNorm_chartPulledWeighted_le_eLpNorm_volume_of_support_in_kPou
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : EuclN → ℝ} (hf_support : Function.support f ⊆ kPouCompact (I := I) (M := M) α) :
    eLpNorm f 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)) ≤
      ENNReal.ofReal (chartPulledWeightedConst (I := I) (M := M) g α) *
        eLpNorm f 2
          ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set M_d_unsqrt : ℝ :=
    (chartPulledWeightedMeasure_le_smul_volume_on_kPouCompact (I := I) (M := M) g α).choose
    with hM_d_unsqrt_def
  have hM_d_nn : 0 ≤ M_d_unsqrt :=
    (chartPulledWeightedMeasure_le_smul_volume_on_kPouCompact (I := I) (M := M) g α).choose_spec.1
  have hM_d_le :
      (chartPulledWeightedMeasure (I := I) g α).restrict
          (kPouCompact (I := I) (M := M) α) ≤
        ENNReal.ofReal M_d_unsqrt •
          (volume : Measure EuclN).restrict (kPouCompact (I := I) (M := M) α) :=
    (chartPulledWeightedMeasure_le_smul_volume_on_kPouCompact (I := I) (M := M) g α).choose_spec.2
  change eLpNorm f 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)) ≤
      ENNReal.ofReal (Real.sqrt M_d_unsqrt) *
        eLpNorm f 2
          ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α))
  have hK_sub_ChTE : kPouCompact (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    kPouCompact_subset_chartTargetEuclid (I := I) (M := M) α
  have h_support_in_ChTE : Function.support f ⊆ chartTargetEuclid (I := I) (M := M) α :=
    hf_support.trans hK_sub_ChTE
  have h_LHS_eq : eLpNorm f 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) =
      eLpNorm f 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (kPouCompact (I := I) (M := M) α)) := by
    rw [show eLpNorm f 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) =
        eLpNorm f 2 (chartPulledWeightedMeasure (I := I) g α) from
        by
          rw [← eLpNorm_indicator_eq_eLpNorm_restrict
            (chartTargetEuclid_measurableSet (I := I) (M := M) α),
            Set.indicator_eq_self.mpr h_support_in_ChTE]]
    rw [show eLpNorm f 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (kPouCompact (I := I) (M := M) α)) =
        eLpNorm f 2 (chartPulledWeightedMeasure (I := I) g α) from
        by
          rw [← eLpNorm_indicator_eq_eLpNorm_restrict
            (kPouCompact_isCompact (I := I) (M := M) α).measurableSet,
            Set.indicator_eq_self.mpr hf_support]]
  have h_RHS_eq : eLpNorm f 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) =
      eLpNorm f 2
        ((volume : Measure EuclN).restrict
          (kPouCompact (I := I) (M := M) α)) := by
    rw [show eLpNorm f 2
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) =
        eLpNorm f 2 (volume : Measure EuclN) from
        by
          rw [← eLpNorm_indicator_eq_eLpNorm_restrict
            (chartTargetEuclid_measurableSet (I := I) (M := M) α),
            Set.indicator_eq_self.mpr h_support_in_ChTE]]
    rw [show eLpNorm f 2
        ((volume : Measure EuclN).restrict
          (kPouCompact (I := I) (M := M) α)) =
        eLpNorm f 2 (volume : Measure EuclN) from
        by
          rw [← eLpNorm_indicator_eq_eLpNorm_restrict
            (kPouCompact_isCompact (I := I) (M := M) α).measurableSet,
            Set.indicator_eq_self.mpr hf_support]]
  rw [h_LHS_eq, h_RHS_eq]
  have h_mono : eLpNorm f 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (kPouCompact (I := I) (M := M) α)) ≤
      eLpNorm f 2
        (ENNReal.ofReal M_d_unsqrt •
          (volume : Measure EuclN).restrict
            (kPouCompact (I := I) (M := M) α)) :=
    eLpNorm_mono_measure f hM_d_le
  refine h_mono.trans ?_
  rw [eLpNorm_smul_measure_of_ne_zero_of_ne_top
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  have h_toReal : ((1 / 2 : ℝ≥0∞).toReal : ℝ) = (1 : ℝ) / 2 := by
    rw [show (1 / 2 : ℝ≥0∞) = (1 : ℝ≥0∞) / 2 from rfl]
    simp
  rw [h_toReal]
  have h_pow_eq : ENNReal.ofReal M_d_unsqrt ^ ((1 : ℝ) / 2) =
      ENNReal.ofReal (Real.sqrt M_d_unsqrt) := by
    rw [Real.sqrt_eq_rpow]
    rw [← ENNReal.ofReal_rpow_of_nonneg hM_d_nn (by positivity)]
  rw [h_pow_eq, smul_eq_mul]

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
private lemma lintegral_enorm_v_toFun_sq_eq
    {g : SmoothRiemannianMetric I M} (v : SmoothScalar g) :
    ∫⁻ x, ‖v.toFun x‖ₑ ^ (2 : ℝ)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ENNReal.ofReal
        (∫ x, v.toFun x * v.toFun x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  classical
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun x => mul_self_nonneg _))
    (v.continuous_mul v).aestronglyMeasurable]
  rw [ENNReal.ofReal_toReal]
  · refine MeasureTheory.lintegral_congr ?_
    intro x
    have h1 : ‖v.toFun x‖ₑ ^ (2 : ℝ) = (‖v.toFun x‖ₑ)^(2 : ℕ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num]
      rw [ENNReal.rpow_natCast]
    rw [h1]
    rw [Real.enorm_eq_ofReal_abs]
    rw [show ((ENNReal.ofReal |v.toFun x|)^2 : ℝ≥0∞) =
        ENNReal.ofReal |v.toFun x| * ENNReal.ofReal |v.toFun x| from sq _]
    rw [← ENNReal.ofReal_mul (abs_nonneg _)]
    congr 1
    rw [← abs_mul, abs_mul_self]
  · exact (v.integrable_mul v).lintegral_lt_top.ne

omit [NeZero (Module.finrank ℝ E)] in
private lemma eLpNorm_v_toFun_le_norm
    {g : SmoothRiemannianMetric I M} (v : SmoothScalar g) :
    eLpNorm v.toFun 2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
      ENNReal.ofReal ‖v‖ := by
  classical
  have h_inner_self : @inner ℝ _ _ v v = smoothScalarH1Inner (I := I) (M := M) v v := rfl
  have h_norm_sq : ‖v‖^2 = smoothScalarH1Inner (I := I) (M := M) v v := by
    rw [@norm_sq_eq_re_inner ℝ]
    change @inner ℝ _ _ v v = _
    rw [h_inner_self]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) v.smooth.continuous.aestronglyMeasurable]
  have h_two_toReal : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h_two_toReal]
  rw [lintegral_enorm_v_toFun_sq_eq (I := I) (M := M) v]
  have h_int_nn : 0 ≤ ∫ x, v.toFun x * v.toFun x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) := v.integral_mul_self_nonneg
  rw [show ENNReal.ofReal (∫ x, v.toFun x * v.toFun x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ^ ((1 : ℝ) / 2) =
      ENNReal.ofReal (Real.sqrt
        (∫ x, v.toFun x * v.toFun x ∂(riemannianVolumeMeasure (I := I) (M := M) g))) from by
    rw [Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg h_int_nn (by positivity)]]
  refine ENNReal.ofReal_le_ofReal ?_
  have h_sqrt_sq_le : ∫ x, v.toFun x * v.toFun x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤ ‖v‖^2 := by
    rw [h_norm_sq]
    unfold smoothScalarH1Inner
    have h_grad_nn := v.integral_inner_grad_self_nonneg
    linarith
  have h_norm_nn : 0 ≤ ‖v‖ := norm_nonneg _
  rw [show ‖v‖ = Real.sqrt (‖v‖^2) from (Real.sqrt_sq h_norm_nn).symm]
  exact Real.sqrt_le_sqrt h_sqrt_sq_le

omit [NeZero (Module.finrank ℝ E)] in
private lemma lintegral_enorm_sqrt_grad_v_sq_eq
    {g : SmoothRiemannianMetric I M} (v : SmoothScalar g) :
    ∫⁻ x, ‖Real.sqrt (g.inner x (gradFun (I := I) g v.toFun x) (gradFun (I := I) g v.toFun x))‖ₑ
        ^ (2 : ℝ)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ENNReal.ofReal
        (∫ x, g.inner x ((gradG (I := I) g ⟨v.toFun, v.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((gradG (I := I) g ⟨v.toFun, v.smooth⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  classical
  have h_inner_nn : ∀ x, 0 ≤ g.inner x (gradFun (I := I) g v.toFun x)
      (gradFun (I := I) g v.toFun x) := by
    intro x
    exact SmoothRiemannianMetric_inner_self_nonneg g x _
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun x => SmoothRiemannianMetric_inner_self_nonneg g x _))
    (v.continuous_inner_grad v).aestronglyMeasurable]
  rw [ENNReal.ofReal_toReal]
  · refine MeasureTheory.lintegral_congr ?_
    intro x
    have h_grad_eq : ((gradG (I := I) g ⟨v.toFun, v.smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) = gradFun (I := I) g v.toFun x := by
      exact grad_g_apply (I := I) g ⟨v.toFun, v.smooth⟩ x
    rw [h_grad_eq]
    have h1 : ‖Real.sqrt (g.inner x (gradFun (I := I) g v.toFun x)
        (gradFun (I := I) g v.toFun x))‖ₑ ^ (2 : ℝ) =
        (‖Real.sqrt (g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x))‖ₑ)^(2 : ℕ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num]
      rw [ENNReal.rpow_natCast]
    rw [h1]
    rw [Real.enorm_eq_ofReal_abs]
    have h_sqrt_nn : 0 ≤ Real.sqrt (g.inner x (gradFun (I := I) g v.toFun x)
        (gradFun (I := I) g v.toFun x)) := Real.sqrt_nonneg _
    rw [abs_of_nonneg h_sqrt_nn]
    rw [show ((ENNReal.ofReal
        (Real.sqrt (g.inner x (gradFun (I := I) g v.toFun x)
          (gradFun (I := I) g v.toFun x))))^(2 : ℕ) : ℝ≥0∞) =
        ENNReal.ofReal
          (Real.sqrt (g.inner x (gradFun (I := I) g v.toFun x)
            (gradFun (I := I) g v.toFun x))) *
          ENNReal.ofReal
            (Real.sqrt (g.inner x (gradFun (I := I) g v.toFun x)
              (gradFun (I := I) g v.toFun x))) from sq _]
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    congr 1
    rw [Real.mul_self_sqrt (h_inner_nn x)]
  · exact (v.integrable_inner_grad v).lintegral_lt_top.ne

omit [NeZero (Module.finrank ℝ E)] in
private lemma eLpNorm_sqrt_grad_v_le_norm
    {g : SmoothRiemannianMetric I M} (v : SmoothScalar g) :
    eLpNorm (fun x : M => Real.sqrt (g.inner x
        (gradFun (I := I) g v.toFun x) (gradFun (I := I) g v.toFun x))) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) ≤
      ENNReal.ofReal ‖v‖ := by
  classical
  have h_inner_self : @inner ℝ _ _ v v = smoothScalarH1Inner (I := I) (M := M) v v := rfl
  have h_norm_sq : ‖v‖^2 = smoothScalarH1Inner (I := I) (M := M) v v := by
    rw [@norm_sq_eq_re_inner ℝ]
    change @inner ℝ _ _ v v = _
    rw [h_inner_self]
  have h_grad_meas : AEStronglyMeasurable (fun x : M => Real.sqrt (g.inner x
      (gradFun (I := I) g v.toFun x) (gradFun (I := I) g v.toFun x)))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have h_cont : Continuous (fun x : M => Real.sqrt (g.inner x
        (gradFun (I := I) g v.toFun x) (gradFun (I := I) g v.toFun x))) :=
      (v.continuous_inner_grad v).sqrt
    exact h_cont.aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) h_grad_meas]
  have h_two_toReal : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h_two_toReal]
  rw [lintegral_enorm_sqrt_grad_v_sq_eq (I := I) (M := M) v]
  have h_int_nn : 0 ≤ ∫ x, g.inner x ((gradG (I := I) g ⟨v.toFun, v.smooth⟩ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g ⟨v.toFun, v.smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    v.integral_inner_grad_self_nonneg
  rw [show ENNReal.ofReal (∫ x, g.inner x _ _ ∂_) ^ ((1 : ℝ) / 2) =
      ENNReal.ofReal (Real.sqrt (∫ x, g.inner x ((gradG (I := I) g ⟨v.toFun, v.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((gradG (I := I) g ⟨v.toFun, v.smooth⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g))) from by
    rw [Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg h_int_nn (by positivity)]]
  refine ENNReal.ofReal_le_ofReal ?_
  have h_sqrt_sq_le : ∫ x, g.inner x ((gradG (I := I) g ⟨v.toFun, v.smooth⟩ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g ⟨v.toFun, v.smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤ ‖v‖^2 := by
    rw [h_norm_sq]
    unfold smoothScalarH1Inner
    have h_v_nn := v.integral_mul_self_nonneg
    linarith
  have h_norm_nn : 0 ≤ ‖v‖ := norm_nonneg _
  rw [show ‖v‖ = Real.sqrt (‖v‖^2) from (Real.sqrt_sq h_norm_nn).symm]
  exact Real.sqrt_le_sqrt h_sqrt_sq_le

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushedPartial_h1_lipschitz
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : SmoothScalar g),
      eLpNorm (chartPushedPartial (I := I) (M := M) g α j v) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal C * (‖v‖₊ : ℝ≥0∞) := by
  classical
  obtain ⟨C_grad, hC_grad_nn, hC_grad_bd⟩ :=
    eLpNorm_fderiv_chartSmoothExt_apply_le_const_mul (I := I) (M := M) g α
      (p := (2 : ℝ≥0∞)) (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  set M_sqrt : ℝ := chartPulledWeightedConst (I := I) (M := M) g α with hM_sqrt_def
  have hM_sqrt_nn : 0 ≤ M_sqrt :=
    chartPulledWeightedConst_nonneg (I := I) (M := M) g α
  set C : ℝ := M_sqrt * 2 * C_grad with hC_def
  have hC_nn : 0 ≤ C := by
    apply mul_nonneg
    · exact mul_nonneg hM_sqrt_nn (by norm_num)
    · exact hC_grad_nn
  refine ⟨C, hC_nn, ?_⟩
  intro v
  have h_aeEq := chartPushedPartial_aeEq_fderiv_chartSmoothExt
    (I := I) (M := M) g α j v
  rw [eLpNorm_congr_ae h_aeEq]
  have h_support : Function.support (fun y : EuclN => (fderiv ℝ
        (chartSmoothExt (I := I) (M := M) α
          (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * v.toFun x)) y)
        (EuclideanSpace.single j 1)) ⊆ kPouCompact (I := I) (M := M) α := by
    intro y hy
    have hy_ne : (fderiv ℝ
        (chartSmoothExt (I := I) (M := M) α
          (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * v.toFun x)) y)
        (EuclideanSpace.single j 1) ≠ 0 := hy
    have h_funeq : chartSmoothExt (I := I) (M := M) α
        (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * v.toFun x) =
        smoothChartExt (I := I) (M := M) g α v := by
      funext z
      classical
      by_cases hz : (toEuclidean (E := E)).symm z ∈ (extChartAt I α).target
      · change (if (toEuclidean (E := E)).symm z ∈ (extChartAt I α).target then
            (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * v.toFun x)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
          else 0) = _
        rw [ite_eq_left hz]
        rw [smoothChartExt_apply_of_mem_target (I := I) (M := M) g α v hz]
      · change (if (toEuclidean (E := E)).symm z ∈ (extChartAt I α).target then
            (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * v.toFun x)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
          else 0) = _
        rw [ite_eq_right hz]
        rw [smoothChartExt_apply_of_notMem_target (I := I) (M := M) g α v hz]
    rw [h_funeq] at hy_ne
    change (smoothChartExtPartial (I := I) (M := M) g α j v y) ≠ 0 at hy_ne
    exact smoothChartExtPartial_tsupport_subset_kPouCompact (I := I) (M := M) g α j v
      (subset_tsupport _ hy_ne)
  have h_density_le := eLpNorm_chartPulledWeighted_le_eLpNorm_volume_of_support_in_kPou
    (I := I) (M := M) g α (f := fun y : EuclN => (fderiv ℝ
      (chartSmoothExt (I := I) (M := M) α
        (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * v.toFun x)) y)
      (EuclideanSpace.single j 1)) h_support
  refine h_density_le.trans ?_
  have h_grad_bd := hC_grad_bd v.smooth j
  have h_v_le := eLpNorm_v_toFun_le_norm (I := I) (M := M) v
  have h_grad_le := eLpNorm_sqrt_grad_v_le_norm (I := I) (M := M) v
  have h_sum_le :
      eLpNorm v.toFun 2 (riemannianVolumeMeasure (I := I) (M := M) g) +
        eLpNorm (fun x : M => Real.sqrt
          (g.inner x (gradFun (I := I) g v.toFun x) (gradFun (I := I) g v.toFun x))) 2
            (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal ‖v‖ + ENNReal.ofReal ‖v‖ := add_le_add h_v_le h_grad_le
  have h_norm_nn : (0 : ℝ) ≤ ‖v‖ := norm_nonneg _
  have h_two_norm : ENNReal.ofReal ‖v‖ + ENNReal.ofReal ‖v‖ = 2 * ENNReal.ofReal ‖v‖ := by
    rw [two_mul]
  calc ENNReal.ofReal M_sqrt *
        eLpNorm (fun y : EuclN => (fderiv ℝ
            (chartSmoothExt (I := I) (M := M) α
              (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * v.toFun x)) y)
            (EuclideanSpace.single j 1)) 2
          ((volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal M_sqrt *
          (ENNReal.ofReal C_grad *
            (eLpNorm v.toFun 2 (riemannianVolumeMeasure (I := I) (M := M) g) +
              eLpNorm (fun x : M => Real.sqrt
                (g.inner x (gradFun (I := I) g v.toFun x) (gradFun (I := I) g v.toFun x))) 2
                (riemannianVolumeMeasure (I := I) (M := M) g))) := by
        gcongr
    _ ≤ ENNReal.ofReal M_sqrt *
          (ENNReal.ofReal C_grad * (ENNReal.ofReal ‖v‖ + ENNReal.ofReal ‖v‖)) := by
        gcongr
    _ = ENNReal.ofReal M_sqrt *
          (ENNReal.ofReal C_grad * (2 * ENNReal.ofReal ‖v‖)) := by rw [h_two_norm]
    _ = ENNReal.ofReal (M_sqrt * 2 * C_grad) * ENNReal.ofReal ‖v‖ := by
        rw [show (M_sqrt * 2 * C_grad : ℝ) = M_sqrt * (C_grad * 2) from by ring]
        rw [ENNReal.ofReal_mul hM_sqrt_nn]
        rw [ENNReal.ofReal_mul hC_grad_nn]
        rw [show (ENNReal.ofReal 2 : ℝ≥0∞) = 2 from by
          rw [show (2 : ℝ≥0∞) = ((2 : ℕ) : ℝ≥0∞) from by norm_cast]
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num]
          rw [ENNReal.ofReal_natCast]]
        ring
    _ = ENNReal.ofReal C * (‖v‖₊ : ℝ≥0∞) := by
        rw [hC_def]
        congr 1
        rw [show ((‖v‖₊ : ℝ≥0∞) : ℝ≥0∞) = ENNReal.ofReal ‖v‖ from by
          rw [ENNReal.ofReal, Real.toNNReal_of_nonneg h_norm_nn]
          rfl]

noncomputable def chartPushedPartialLipschitzCanonical
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E)) :
    ChartPushedPartialLipschitz (I := I) (M := M) g α j :=
  let h := chartPushedPartial_h1_lipschitz (I := I) (M := M) g α j
  { C := h.choose
    C_nonneg := h.choose_spec.1
    bound := by
      classical
      intro v
      rw [norm_chartPushedPartialLpLin (I := I) (M := M) g α j v]
      have h_bd := h.choose_spec.2 v
      have h_nn := h.choose_spec.1
      have h_norm_nn : (0 : ℝ) ≤ ‖v‖ := norm_nonneg _
      have h_lhs_finite : eLpNorm (chartPushedPartial (I := I) (M := M) g α j v) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)) ≠ ⊤ :=
        (chartPushedPartial_memLp (I := I) (M := M) g α j v).eLpNorm_lt_top.ne
      have h_rhs_eq : ENNReal.ofReal h.choose * (‖v‖₊ : ℝ≥0∞) =
          ENNReal.ofReal (h.choose * ‖v‖) := by
        rw [show ((‖v‖₊ : ℝ≥0∞) : ℝ≥0∞) = ENNReal.ofReal ‖v‖ from by
          rw [ENNReal.ofReal, Real.toNNReal_of_nonneg h_norm_nn]
          rfl]
        rw [← ENNReal.ofReal_mul h_nn]
      rw [h_rhs_eq] at h_bd
      have h_toReal := (ENNReal.toReal_le_toReal h_lhs_finite ENNReal.ofReal_ne_top).mpr h_bd
      rwa [ENNReal.toReal_ofReal (mul_nonneg h_nn h_norm_nn)] at h_toReal }

end H1ComplGradientH1LipschitzBound
end Laplacian
end Analysis
end CalabiYau

end
