module

public import CalabiYau.Analysis.Elliptic.Regularity.SmoothFChartResidual.BilinearBound

/-!
# Cauchy property of the smooth base forcing residuals

Port target: DifferentialGeometry at `7a48598d35109aa99d1cc678e2724c213cdf4ff3`,
`Analysis/Elliptic/Regularity/Iterated/BaseFChart/PolymorphicRegularity.lean`,
`smoothApproxSeqWkpM_wkpNormChart_diff_le` and
`smoothApproxSeq_smoothFChartResidual_wkpNorm_cauchy_wkpM` (lines 120–240), stated for any
sequence of smooth approximants at rate `1/(n+1)` and any uniform residual bound. The order-one
template is `SmoothApproxSeq/Cauchy.lean`; residual linearity is `smoothFChartResidual_ae_sub`.
-/

@[expose] public section

noncomputable section
open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace CalabiYau.PoissonDomainRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
open CalabiYau.RiemannianVolume CalabiYau.Analysis.Laplacian Sobolev.Chart Sobolev.Euclidean
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.LaplacianDomainChartData
open CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.DiffChartBilinearH1ComplResidual
open CalabiYau.Analysis.Laplacian.SmoothFChartResidualBilinearBound
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))


variable [FiniteDimensional ℝ E]
    [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private noncomputable def residualSmoothScalarSub
    {g : SmoothRiemannianMetric I M}
    (v₁ v₂ : SmoothScalar g) : SmoothScalar g :=
  { toFun := fun x => v₁.toFun x - v₂.toFun x
    smooth := v₁.smooth.sub v₂.smooth }

private lemma residualSmoothScalarSub_toFun
    {g : SmoothRiemannianMetric I M}
    (v₁ v₂ : SmoothScalar g) :
    (residualSmoothScalarSub v₁ v₂).toFun = fun x => v₁.toFun x - v₂.toFun x := rfl

private lemma residualSmoothScalarEqSub
    {g : SmoothRiemannianMetric I M}
    (v₁ v₂ vdiff : SmoothScalar g)
    (hdiff : vdiff.toFun = fun x => v₁.toFun x - v₂.toFun x) :
    vdiff = v₁ - v₂ := by
  apply SmoothScalar.ext
  rw [hdiff]
  rfl

variable [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [I.Boundaryless] [T2Space M] in
private lemma residualSmoothToH1ComplEqSub
    (g : SmoothRiemannianMetric I M) (v₁ v₂ vdiff : SmoothScalar g)
    (hdiff : vdiff.toFun = fun x => v₁.toFun x - v₂.toFun x) :
    smoothToH1Compl (I := I) (M := M) g vdiff =
      smoothToH1Compl (I := I) (M := M) g v₁ -
        smoothToH1Compl (I := I) (M := M) g v₂ := by
  rw [residualSmoothScalarEqSub v₁ v₂ vdiff hdiff]
  exact map_sub (smoothToH1Compl (I := I) (M := M) g) v₁ v₂

variable [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma residualLeibnizResidualSub
    (g : SmoothRiemannianMetric I M) (α : M)
    (u₁ u₂ : H1Compl (I := I) (M := M) g) :
    CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
        (I := I) (M := M) g α (u₁ - u₂) =
      CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
          (I := I) (M := M) g α u₁ -
        CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
          (I := I) (M := M) g α u₂ := by
  classical
  unfold CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
  set ρα : C^∞⟮I, M; ℝ⟯ := chartAtlasPOU I M α with hρα_def
  set Δρα : C^∞⟮I, M; ℝ⟯ := laplacianOfChartPOU (I := I) (M := M) g α with hΔρα_def
  have hgrad : gradInnerCLM (I := I) (M := M) g ρα (u₁ - u₂) =
      gradInnerCLM (I := I) (M := M) g ρα u₁ - gradInnerCLM (I := I) (M := M) g ρα u₂ :=
    map_sub (gradInnerCLM (I := I) (M := M) g ρα) u₁ u₂
  have hcompl : h1ComplToLp (I := I) (M := M) g (u₁ - u₂) =
      h1ComplToLp (I := I) (M := M) g u₁ - h1ComplToLp (I := I) (M := M) g u₂ :=
    map_sub (h1ComplToLp (I := I) (M := M) g) u₁ u₂
  have hlap : smoothMulLp (I := I) (M := M) g Δρα
      (h1ComplToLp (I := I) (M := M) g (u₁ - u₂)) =
      smoothMulLp (I := I) (M := M) g Δρα (h1ComplToLp (I := I) (M := M) g u₁) -
        smoothMulLp (I := I) (M := M) g Δρα (h1ComplToLp (I := I) (M := M) g u₂) := by
    rw [hcompl]
    exact map_sub (smoothMulLp (I := I) (M := M) g Δρα) _ _
  rw [hgrad, hlap, smul_sub, neg_sub]
  abel

variable [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] in
private lemma residualVolumeAbsolutelyContinuous
    (g : SmoothRiemannianMetric I M) (α : M) :
    (volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α) ≪
      (chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α) := by
  intro A hA
  have hT : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  unfold chartPulledWeightedMeasure at hA
  rw [show ((volume : Measure EuclN).withDensity
        (fun y => ENNReal.ofReal (CalabiYau.Laplacian.MetricExtension.densityOnEuclid
          (I := I) g α y))).restrict (chartTargetEuclid (I := I) (M := M) α) =
      ((volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)).withDensity
        (fun y => ENNReal.ofReal (CalabiYau.Laplacian.MetricExtension.densityOnEuclid
          (I := I) g α y))
    from MeasureTheory.restrict_withDensity hT _] at hA
  rw [MeasureTheory.withDensity_apply_eq_zero'
    (μ := (volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α))
    (f := fun y : EuclN => ENNReal.ofReal
      (CalabiYau.Laplacian.MetricExtension.densityOnEuclid (I := I) g α y))
    (ENNReal.measurable_ofReal.comp_aemeasurable
      ((CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl.densityOnEuclid_continuousOn
        (I := I) g α).aemeasurable hT))] at hA
  rw [Measure.restrict_apply' hT]
  rw [Measure.restrict_apply' hT] at hA
  refine MeasureTheory.measure_mono_null ?_ hA
  intro y ⟨hyA, hyT⟩
  refine ⟨⟨?_, hyA⟩, hyT⟩
  have hpos : 0 < CalabiYau.Laplacian.MetricExtension.densityOnEuclid (I := I) g α y :=
    CalabiYau.Laplacian.MetricExtension.densityOnEuclid_pos (I := I) g α hyT
  exact (ENNReal.ofReal_pos.mpr hpos).ne'

variable [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem residualSmoothFChartResidualAeSub
    (g : SmoothRiemannianMetric I M) (α : M)
    (v₁ v₂ vdiff : SmoothScalar g)
    (hdiff : vdiff.toFun = fun x => v₁.toFun x - v₂.toFun x) :
    smoothFChartResidual (I := I) (M := M) g α vdiff =ᵐ[
        (volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)]
      fun y => smoothFChartResidual (I := I) (M := M) g α v₁ y -
        smoothFChartResidual (I := I) (M := M) g α v₂ y := by
  classical
  have hsmoothToH1 := residualSmoothToH1ComplEqSub (I := I) (M := M)
    g v₁ v₂ vdiff hdiff
  have hresidual :
      CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
          (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g vdiff) =
        CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g v₁) -
          CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g v₂) := by
    rw [hsmoothToH1]
    exact residualLeibnizResidualSub (I := I) (M := M) g α _ _
  have hpush :
      chartPushedRawLpFromLp (I := I) (M := M) g α
          (CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g vdiff)) =
        chartPushedRawLpFromLp (I := I) (M := M) g α
          (CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
              (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g v₁) -
            CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
              (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g v₂)) := by
    rw [hresidual]
  have hcoe := CalabiYau.Analysis.Laplacian.GradInnerCLMLeibniz.chartPushedRawLpFromLp_coeFn_sub
      (I := I) (M := M) g α
      (CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
        (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g v₁))
      (CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
        (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g v₂))
  have hweighted :
      ((chartPushedRawLpFromLp (I := I) (M := M) g α
          (CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g vdiff)) :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      fun y =>
        ((chartPushedRawLpFromLp (I := I) (M := M) g α
            (CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
              (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g v₁)) :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y -
        ((chartPushedRawLpFromLp (I := I) (M := M) g α
            (CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
              (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g v₂)) :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y := by
    rw [hpush]
    exact hcoe
  have habs := residualVolumeAbsolutelyContinuous (I := I) (M := M) g α
  unfold smoothFChartResidual
    CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
  exact habs.ae_le hweighted

variable [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
/-- If the smooth `v n` approximate `u` in chart `H^(m+1)` at rate `1/(n+1)` and the residual is
bounded by `C` times the chart `H^(m+1)` norm, the residuals of `v n` are Cauchy in `H^m`. -/
theorem smoothFChartResidual_wkpNorm_cauchy_of_approx
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ)
    {u : M → ℝ} (hu : MemWkpChart (I := I) (M := M) (m + 1) 2 u)
    {C : ℝ} (hC : ∀ v : SmoothScalar g,
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) m 2
        (smoothFChartResidual (I := I) (M := M) g α v)
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal C * wkpNormChart (I := I) (M := M) (m + 1) 2 v.toFun)
    (v : ℕ → SmoothScalar g)
    (hv : ∀ n, wkpNormChart (I := I) (M := M) (m + 1) 2 (fun x => u x - (v n).toFun x) ≤
      ENNReal.ofReal (1 / ((n : ℝ) + 1))) :
    ∀ ε > 0, ∃ N, ∀ a b, N ≤ a → N ≤ b →
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) m 2
        (fun y => smoothFChartResidual (I := I) (M := M) g α (v a) y -
          smoothFChartResidual (I := I) (M := M) g α (v b) y)
        (chartTargetEuclid (I := I) (M := M) α) ≤ ENNReal.ofReal ε := by
  classical
  intro ε hε
  by_cases hCpos : 0 < C
  · have hεCpos : 0 < ε / (2 * C) := by positivity
    obtain ⟨N0, hN0real⟩ := exists_nat_gt (1 / (ε / (2 * C)) - 1)
    have hN1pos : (0 : ℝ) < (N0 : ℝ) + 1 := by
      have hpos : 0 < 1 / (ε / (2 * C)) := by positivity
      linarith
    have hN0inv : (1 : ℝ) / ((N0 : ℝ) + 1) ≤ ε / (2 * C) := by
      rw [div_le_iff₀ hN1pos]
      have h1 : (1 : ℝ) = (ε / (2 * C)) * (1 / (ε / (2 * C))) := by
        rw [mul_one_div, div_self hεCpos.ne']
      rw [h1]
      apply mul_le_mul_of_nonneg_left _ hεCpos.le
      linarith
    refine ⟨N0, ?_⟩
    intro a b ha hb
    set va : SmoothScalar g := v a
    set vb : SmoothScalar g := v b
    set vdiff : SmoothScalar g := residualSmoothScalarSub va vb
    have hvdiff_toFun : vdiff.toFun = fun x => va.toFun x - vb.toFun x :=
      residualSmoothScalarSub_toFun va vb
    have h_ae_sub := residualSmoothFChartResidualAeSub (I := I) (M := M) g α va vb vdiff hvdiff_toFun
    have h_wkp_eq :
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) m 2
          (fun y => smoothFChartResidual (I := I) (M := M) g α va y -
            smoothFChartResidual (I := I) (M := M) g α vb y)
          (chartTargetEuclid (I := I) (M := M) α) =
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) m 2
          (smoothFChartResidual (I := I) (M := M) g α vdiff)
          (chartTargetEuclid (I := I) (M := M) α) := by
      refine wkpNorm_congr_ae (d := Module.finrank ℝ E) (by norm_num)
        (chartTargetEuclid_isOpen (I := I) (M := M) α) ?_
      exact h_ae_sub.symm
    rw [h_wkp_eq]
    have h_chartdiff : wkpNormChart (I := I) (M := M) (m + 1) 2 vdiff.toFun ≤
        ENNReal.ofReal (1 / ((a : ℝ) + 1)) + ENNReal.ofReal (1 / ((b : ℝ) + 1)) := by
      rw [hvdiff_toFun]
      have hdecomp : (fun x : M => va.toFun x - vb.toFun x) =
          (fun x => (u x - vb.toFun x) - (u x - va.toFun x)) := by
        funext x; ring
      rw [hdecomp]
      have hp : (1 : ℝ≥0∞) ≤ 2 := by norm_num
      have hva : MemWkpChart (I := I) (M := M) (m + 1) 2 va.toFun :=
        CalabiYau.Analysis.Sobolev.Chart.memWkpChart_of_contMDiff_k (I := I) (M := M) hp (m + 1) va.smooth
      have hvb : MemWkpChart (I := I) (M := M) (m + 1) 2 vb.toFun :=
        CalabiYau.Analysis.Sobolev.Chart.memWkpChart_of_contMDiff_k (I := I) (M := M) hp (m + 1) vb.smooth
      have huva : MemWkpChart (I := I) (M := M) (m + 1) 2 (fun x => u x - va.toFun x) :=
        _root_.Sobolev.Chart.MemWkpChart_sub (I := I) (M := M) hp hu hva
      have huvb : MemWkpChart (I := I) (M := M) (m + 1) 2 (fun x => u x - vb.toFun x) :=
        _root_.Sobolev.Chart.MemWkpChart_sub (I := I) (M := M) hp hu hvb
      have hsplit : (fun x : M => (u x - vb.toFun x) - (u x - va.toFun x)) =
          (fun x => (u x - vb.toFun x) + (-1 : ℝ) * (u x - va.toFun x)) := by
        funext x; ring
      rw [hsplit]
      have hnegMem : MemWkpChart (I := I) (M := M) (m + 1) 2
          (fun x => (-1 : ℝ) * (u x - va.toFun x)) := by
        have heq : (fun x : M => (-1 : ℝ) * (u x - va.toFun x)) =
            (fun x => -(u x - va.toFun x)) := by funext x; ring
        rw [heq]
        exact _root_.Sobolev.Chart.MemWkpChart_neg (I := I) (M := M) hp huva
      have hnegNorm : wkpNormChart (I := I) (M := M) (m + 1) 2
          (fun x => (-1 : ℝ) * (u x - va.toFun x)) =
          wkpNormChart (I := I) (M := M) (m + 1) 2 (fun x => u x - va.toFun x) := by
        rw [_root_.Sobolev.Chart.wkpNormChart_const_smul
          (I := I) (M := M) hp (-1 : ℝ) huva]
        simp [enorm]
      have hadd := _root_.Sobolev.Chart.wkpNormChart_add_le (I := I) (M := M)
        (k := m + 1) (p := 2) hp huvb hnegMem
      rw [hnegNorm] at hadd
      have hbound : wkpNormChart (I := I) (M := M) (m + 1) 2 (fun x => u x - vb.toFun x) +
          wkpNormChart (I := I) (M := M) (m + 1) 2 (fun x => u x - va.toFun x) ≤
          ENNReal.ofReal (1 / ((b : ℝ) + 1)) + ENNReal.ofReal (1 / ((a : ℝ) + 1)) :=
        add_le_add (hv b) (hv a)
      exact hadd.trans (le_of_le_of_eq hbound (by rw [add_comm]))
    have h_step : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) m 2
          (smoothFChartResidual (I := I) (M := M) g α vdiff)
          (chartTargetEuclid (I := I) (M := M) α) ≤
        ENNReal.ofReal C * (ENNReal.ofReal (1 / ((a : ℝ) + 1)) +
          ENNReal.ofReal (1 / ((b : ℝ) + 1))) := by
      exact (hC vdiff).trans (mul_le_mul_of_nonneg_left h_chartdiff zero_le)
    refine h_step.trans ?_
    have hNa : (N0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    have hNb : (N0 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    have ha1 : (0 : ℝ) < (a : ℝ) + 1 := by linarith
    have hb1 : (0 : ℝ) < (b : ℝ) + 1 := by linarith
    have haInv : (1 : ℝ) / ((a : ℝ) + 1) ≤ (1 : ℝ) / ((N0 : ℝ) + 1) :=
      div_le_div_of_nonneg_left zero_le_one hN1pos (by linarith)
    have hbInv : (1 : ℝ) / ((b : ℝ) + 1) ≤ (1 : ℝ) / ((N0 : ℝ) + 1) :=
      div_le_div_of_nonneg_left zero_le_one hN1pos (by linarith)
    have hsum : ENNReal.ofReal (1 / ((a : ℝ) + 1)) + ENNReal.ofReal (1 / ((b : ℝ) + 1)) ≤
        ENNReal.ofReal (1 / ((N0 : ℝ) + 1)) + ENNReal.ofReal (1 / ((N0 : ℝ) + 1)) :=
      add_le_add (ENNReal.ofReal_le_ofReal haInv) (ENNReal.ofReal_le_ofReal hbInv)
    have hmul := mul_le_mul_of_nonneg_left hsum
      (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal C from bot_le)
    have hNinvNN : (0 : ℝ) ≤ 1 / ((N0 : ℝ) + 1) := by positivity
    rw [show ENNReal.ofReal (1 / ((N0 : ℝ) + 1)) + ENNReal.ofReal (1 / ((N0 : ℝ) + 1)) =
      ENNReal.ofReal (2 * (1 / ((N0 : ℝ) + 1))) by
        rw [show 2 * (1 / ((N0 : ℝ) + 1)) = (1 / ((N0 : ℝ) + 1)) + (1 / ((N0 : ℝ) + 1)) by ring,
          ENNReal.ofReal_add hNinvNN hNinvNN]] at hmul
    rw [← ENNReal.ofReal_mul hCpos.le] at hmul
    refine hmul.trans ?_
    apply ENNReal.ofReal_le_ofReal
    calc C * (2 * (1 / ((N0 : ℝ) + 1))) ≤ C * (2 * (ε / (2 * C))) := by
          apply mul_le_mul_of_nonneg_left _ hCpos.le
          exact mul_le_mul_of_nonneg_left hN0inv (by norm_num)
      _ = ε := by field_simp
  · have hCnonpos : C ≤ 0 := le_of_not_gt hCpos
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε - 1)
    have hN1pos : (0 : ℝ) < (N : ℝ) + 1 := by
      have hpos : 0 < 1 / ε := by positivity
      linarith
    have hNinv : (1 : ℝ) / ((N : ℝ) + 1) ≤ ε := by
      rw [div_le_iff₀ hN1pos]
      have h1 : (1 : ℝ) = ε * (1 / ε) := by rw [mul_one_div, div_self hε.ne']
      rw [h1]
      exact mul_le_mul_of_nonneg_left (by linarith) hε.le
    refine ⟨N, ?_⟩
    intro a b ha hb
    set va : SmoothScalar g := v a
    set vb : SmoothScalar g := v b
    set vdiff : SmoothScalar g := residualSmoothScalarSub va vb
    have hvdiff_toFun : vdiff.toFun = fun x => va.toFun x - vb.toFun x :=
      residualSmoothScalarSub_toFun va vb
    have hae := residualSmoothFChartResidualAeSub (I := I) (M := M) g α va vb vdiff hvdiff_toFun
    rw [wkpNorm_congr_ae (d := Module.finrank ℝ E) (by norm_num)
      (chartTargetEuclid_isOpen (I := I) (M := M) α) hae.symm]
    have hzero := hC vdiff
    have hzero' : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) m 2
        (smoothFChartResidual (I := I) (M := M) g α vdiff)
        (chartTargetEuclid (I := I) (M := M) α) ≤ 0 := by
      simpa [ENNReal.ofReal_eq_zero.mpr hCnonpos] using hzero
    have hnonneg : 0 ≤ iteratedWeakSobolevNorm (d := Module.finrank ℝ E) m 2
        (smoothFChartResidual (I := I) (M := M) g α vdiff)
        (chartTargetEuclid (I := I) (M := M) α) := bot_le
    have heq : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) m 2
        (smoothFChartResidual (I := I) (M := M) g α vdiff)
        (chartTargetEuclid (I := I) (M := M) α) = 0 := le_antisymm hzero' hnonneg
    rw [heq]
    positivity

end CalabiYau.PoissonDomainRegularity
