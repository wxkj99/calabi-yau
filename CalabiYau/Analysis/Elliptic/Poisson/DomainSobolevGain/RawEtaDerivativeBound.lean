module

public import CalabiYau.Analysis.Elliptic.Regularity.SmoothFChartResidual.BilinearBound

/-!
# Quantitative raw derivative control for the auxiliary chart cutoff

This estimate is needed before passing smooth raw eta derivatives to an H1
limit. Qualitative raw chart Sobolev transport does not give this norm bound.
The target chart's POU weight is not assumed positive on the eta support.
-/

@[expose] public section

noncomputable section
open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace CalabiYau.PoissonDomainRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
open CalabiYau.RiemannianVolume CalabiYau.Analysis.Laplacian
open CalabiYau.Analysis.Sobolev.Chart
open CalabiYau.Analysis.Laplacian.GradInnerCLMChartFormula
open CalabiYau.Analysis.Laplacian.SmoothFChartResidualBilinearBound
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

section QuantitativeHelpers
open CalabiYau.Riemannian
open _root_.Sobolev.Chart
set_option maxHeartbeats 800000

-- Local copies of the private scalar-energy estimates from GradientH1LipschitzBound.
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
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
private theorem chart_sobolev_one_two_le_h1
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : SmoothScalar g,
      wkpNormChart (I := I) (M := M) 1 2 s.toFun ≤
        ENNReal.ofReal C * ENNReal.ofReal ‖s‖ := by
  obtain ⟨A, hA, hAb⟩ :=
    _root_.Sobolev.EquivalenceReverse.wkpNormChart_le_const_mul_intrinsicLpComponents_smooth_uniform
      (I := I) (M := M) g (p := 2) (by norm_num) (by norm_num)
  refine ⟨A * 2, mul_nonneg hA (by norm_num), ?_⟩
  intro s
  calc
    wkpNormChart (I := I) (M := M) 1 2 s.toFun ≤
        ENNReal.ofReal A *
          (eLpNorm s.toFun 2 (riemannianVolumeMeasure (I := I) (M := M) g) +
           eLpNorm (fun x => Real.sqrt (g.inner x
             (gradFun (I := I) g s.toFun x) (gradFun (I := I) g s.toFun x)))
             2 (riemannianVolumeMeasure (I := I) (M := M) g)) := hAb s.smooth
    _ ≤ ENNReal.ofReal A * (ENNReal.ofReal ‖s‖ + ENNReal.ofReal ‖s‖) := by
      gcongr
      · exact eLpNorm_v_toFun_le_norm s
      · exact eLpNorm_sqrt_grad_v_le_norm s
    _ = ENNReal.ofReal (A * 2) * ENNReal.ofReal ‖s‖ := by
      rw [ENNReal.ofReal_mul hA]
      norm_num
      ring

private theorem actual_eta_raw_sobolev_one_two_le_h1
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : SmoothScalar g,
      _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm 1 2
        (chartPushedRaw I α (etaTimesV (I := I) (M := M) α s.toFun))
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal C * ENNReal.ofReal ‖s‖ := by
  obtain ⟨A, hA, hAb⟩ := wkpNorm_chartPushedRaw_strictCutoff_mul_le
    (I := I) (M := M) g α 1 (p := 2) (by norm_num) (by norm_num)
  obtain ⟨B, hB, hBb⟩ := chart_sobolev_one_two_le_h1 (I := I) (M := M) g
  refine ⟨A * B, mul_nonneg hA.le hB, ?_⟩
  intro s
  have hs : MemWkpChart (I := I) (M := M) 1 2 s.toFun :=
    memWkpChart_of_contMDiff_k (I := I) (M := M) (by norm_num) 1 s.smooth
  calc
    _ ≤ ENNReal.ofReal A * wkpNormChart (I := I) (M := M) 1 2 s.toFun := hAb hs
    _ ≤ ENNReal.ofReal A * (ENNReal.ofReal B * ENNReal.ofReal ‖s‖) := by
      gcongr
      exact hBb s
    _ = ENNReal.ofReal (A * B) * ENNReal.ofReal ‖s‖ := by
      rw [ENNReal.ofReal_mul hA.le]
      ring

private theorem actual_eta_raw_partial_le_h1
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : SmoothScalar g,
      eLpNorm (partialDerivOnEuclid (I := I) (M := M) α j
        (etaTimesV (I := I) (M := M) α s.toFun)) 2
        ((volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)) ≤
      ENNReal.ofReal C * ENNReal.ofReal ‖s‖ := by
  obtain ⟨A, hA, hAb⟩ := wkpNorm_partialDerivOnEuclid_le_wkpNorm_chartPushedRaw_succ
    (I := I) (M := M) α j 0 (p := 2) (by norm_num)
  obtain ⟨B, hB, hBb⟩ := actual_eta_raw_sobolev_one_two_le_h1 (I := I) (M := M) g α
  refine ⟨A * B, mul_nonneg hA.le hB, ?_⟩
  intro s
  have h := hAb (etaTimesV_smooth (I := I) (M := M) α s.smooth)
    (tsupport_etaTimesV_subset (I := I) (M := M) α s.toFun)
  rw [_root_.Sobolev.Euclidean.wkpNorm_zero] at h
  exact h.trans (by
    calc
      _ ≤ ENNReal.ofReal A * (ENNReal.ofReal B * ENNReal.ofReal ‖s‖) := by
        gcongr
        exact hBb s
      _ = ENNReal.ofReal (A * B) * ENNReal.ofReal ‖s‖ := by
        rw [ENNReal.ofReal_mul hA.le]
        ring)

private theorem actual_eta_raw_partial_le_h1_on_subset
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Ω : Set EuclN),
      Ω ⊆ chartTargetEuclid (I := I) (M := M) α → ∀ s : SmoothScalar g,
      eLpNorm (partialDerivOnEuclid (I := I) (M := M) α j
        (etaTimesV (I := I) (M := M) α s.toFun)) 2
        ((volume : Measure EuclN).restrict Ω) ≤
      ENNReal.ofReal C * ENNReal.ofReal ‖s‖ := by
  obtain ⟨C, hC, hCb⟩ := actual_eta_raw_partial_le_h1 (I := I) (M := M) g α j
  refine ⟨C, hC, ?_⟩
  intro Ω hΩ s
  exact (eLpNorm_mono_measure _ (Measure.restrict_mono hΩ le_rfl)).trans (hCb s)


end QuantitativeHelpers

/-- A uniform quantitative L2 estimate, without a raw derivative map premise. -/
theorem raw_eta_partial_eLpNorm_le_H1
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (Ω : Set EuclN)
    (hΩt : closure Ω ⊆ _root_.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : SmoothScalar g,
      eLpNorm (partialDerivOnEuclid (I := I) (M := M) α j
        (etaTimesV (I := I) (M := M) α s.toFun)) 2
        ((volume : Measure EuclN).restrict Ω) ≤
      ENNReal.ofReal (C * ‖smoothToH1Compl (I := I) (M := M) g s‖) := by
  obtain ⟨C, hC, hCb⟩ := actual_eta_raw_partial_le_h1_on_subset
    (I := I) (M := M) g α j
  refine ⟨C, hC, ?_⟩
  intro s
  have h := hCb Ω (subset_closure.trans hΩt) s
  simpa only [smoothToH1Compl_apply, UniformSpace.Completion.norm_coe,
    ENNReal.ofReal_mul hC] using h

/-- The same constant controls smooth differences in the H1 completion norm.
This is the input to the raw derivative Cauchy argument, not limit identification. -/
theorem raw_eta_partial_difference_eLpNorm_le_H1
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (Ω : Set EuclN)
    (hΩt : closure Ω ⊆ _root_.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s t : SmoothScalar g,
      eLpNorm (partialDerivOnEuclid (I := I) (M := M) α j
        (etaTimesV (I := I) (M := M) α (s - t).toFun)) 2
        ((volume : Measure EuclN).restrict Ω) ≤
      ENNReal.ofReal (C * ‖smoothToH1Compl (I := I) (M := M) g s -
        smoothToH1Compl (I := I) (M := M) g t‖) := by
  obtain ⟨C, hC, hbound⟩ := raw_eta_partial_eLpNorm_le_H1 g α j Ω hΩt
  refine ⟨C, hC, ?_⟩
  intro s t
  simpa only [map_sub] using hbound (s - t)

end CalabiYau.PoissonDomainRegularity
