module

public import CalabiYau.Analysis.Elliptic.Regularity.SmoothFChartResidual.BilinearBound

/-!
# Sobolev bound for the Laplacian piece of the base forcing residual

Port target: DifferentialGeometry at `7a48598d35109aa99d1cc678e2724c213cdf4ff3`,
`Analysis/Elliptic/Regularity/Iterated/BaseFChart/BilinearRegularity.lean`,
`wkpNorm_chartPushedRaw_lapPiece_le` (lines 608–722),
general order `m` (the repository already has the order-one case privately in
`SmoothFChartResidual/BilinearBound.lean`). Used by `fChartResidual_memWkp_of_memWkpChart`.
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
open CalabiYau.RiemannianVolume CalabiYau.Analysis.Laplacian Sobolev.Chart Sobolev.Euclidean
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.LaplacianDomainChartData
open CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.DiffChartBilinearH1ComplResidual
open CalabiYau.Analysis.Laplacian.SmoothFChartResidualBilinearBound
open _root_.CalabiYau.Analysis.Sobolev.Chart
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma memWkp_chartPushedRaw_etaTimesV
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ) (v : SmoothScalar g) :
    MemWkp (d := Module.finrank ℝ E) m 2
      (chartPushedRaw (I := I) (M := M) α
        (etaTimesV (I := I) (M := M) α v.toFun))
      (chartTargetEuclid (I := I) (M := M) α) := by
  have hηv_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (etaTimesV (I := I) (M := M) α v.toFun) :=
    etaTimesV_smooth (I := I) (M := M) α v.smooth
  have hηv_support : tsupport (etaTimesV (I := I) (M := M) α v.toFun) ⊆
      (chartAt H α).source :=
    tsupport_etaTimesV_subset (I := I) (M := M) α v.toFun
  have hCP_smooth : ContDiff ℝ ∞
      (chartPushedRaw (I := I) (M := M) α
        (etaTimesV (I := I) (M := M) α v.toFun)) :=
    chartPushedRaw_contDiff (I := I) (M := M) hηv_smooth hηv_support
  have hCP_compact : HasCompactSupport
      (chartPushedRaw (I := I) (M := M) α
        (etaTimesV (I := I) (M := M) α v.toFun)) :=
    chartPushedRaw_smooth_hasCompactSupport_local (I := I) (M := M) hηv_support
  have hCP_tsupp : tsupport (chartPushedRaw (I := I) (M := M) α
        (etaTimesV (I := I) (M := M) α v.toFun)) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    tsupport_chartPushedRaw_subset_chartTargetEuclid (I := I) (M := M) hηv_support
  exact _root_.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport
    (d := Module.finrank ℝ E)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    hCP_smooth hCP_compact hCP_tsupp (by norm_num : (1 : ℝ≥0∞) ≤ 2) m

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [I.Boundaryless] in
private lemma wkpNormChart_le_of_le
    (j k : ℕ) (hjk : j ≤ k) (p : ℝ≥0∞) (u : M → ℝ) :
    wkpNormChart (I := I) (M := M) j p u ≤ wkpNormChart (I := I) (M := M) k p u := by
  classical
  unfold wkpNormChart
  refine ENNReal.tsum_le_tsum (fun α => ?_)
  exact CalabiYau.Analysis.Sobolev.Chart.EuclideanIterated.wkpNorm_mono_order
    (d := Module.finrank ℝ E) (j := j) (k := k) hjk

set_option maxHeartbeats 1000000 in
private lemma wkpNorm_chartPushedRaw_etaTimesV_le_self
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SmoothScalar g,
      _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2
        (chartPushedRaw (I := I) (M := M) α
          (etaTimesV (I := I) (M := M) α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal C * wkpNormChart (I := I) (M := M) m 2 v.toFun := by
  classical
  obtain ⟨C, hC_pos, hC_bound⟩ :=
    _root_.Sobolev.Chart.wkpNorm_chartPushedRaw_strictCutoff_mul_le
      (I := I) (M := M) g α m (p := 2) (by norm_num) (by norm_num)
  refine ⟨C, hC_pos, ?_⟩
  intro v
  have h_v_MemWkpChart : MemWkpChart (I := I) (M := M) m 2 v.toFun :=
    memWkpChart_of_contMDiff_k (I := I) (M := M) (by norm_num) m v.smooth
  have h_funext : etaTimesV (I := I) (M := M) α v.toFun =
      fun x : M => chartStrictCutoff (I := I) (M := M) α x * v.toFun x := by
    funext x; rfl
  rw [h_funext]
  exact hC_bound h_v_MemWkpChart

/-- For smooth `v`, the raw chart push of the Laplacian piece `(Δρ_α)(η_α v)`
of the residual is in `H^m` on the chart target, with `H^m` norm bounded by a uniform constant
times the chart `H^(m+1)` norm of `v`. -/
theorem chartPushedRaw_lapPiece_memWkp_and_le
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SmoothScalar g,
      MemWkp (d := Module.finrank ℝ E) m 2
        (chartPushedRaw (I := I) (M := M) α (lapPiece (I := I) (M := M) g α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α) ∧
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) m 2
        (chartPushedRaw (I := I) (M := M) α (lapPiece (I := I) (M := M) g α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal C * wkpNormChart (I := I) (M := M) (m + 1) 2 v.toFun := by
  classical
  obtain ⟨b, hb_smooth, _, hb_one_on_tsupp, hb_support⟩ :=
    exists_chart_cutoff_M (I := I) (M := M) α
  set bΔρα : M → ℝ := fun x : M =>
    b x * (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x with hbΔρα_def
  have hbΔρα_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ bΔρα :=
    hb_smooth.mul (laplacianOfChartPOU (I := I) (M := M) g α).contMDiff
  have hbΔρα_support : tsupport bΔρα ⊆ (chartAt H α).source := by
    have h_eq : bΔρα = (fun x : M => b x •
        (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x) := by
      funext x; rfl
    rw [h_eq]
    exact (tsupport_smul_subset_left (f := b)
      (g := ((laplacianOfChartPOU (I := I) (M := M) g α : C^∞⟮I, M; ℝ⟯) : M → ℝ))).trans
      hb_support
  obtain ⟨CΛ, hCΛ_nn, hCΛ_bound⟩ :=
    _root_.CalabiYau.Analysis.Sobolev.Chart.smoothExtensionScalar_iteratedFDeriv_bound
      (I := I) (M := M) α hbΔρα_smooth hbΔρα_support m
  set Λ : EuclN → ℝ := smoothExtensionScalar (I := I) (M := M) α bΔρα with hΛ_def
  have hΛ_smooth : ContDiff ℝ (⊤ : ℕ∞) Λ :=
    contDiff_smoothExtensionScalar (I := I) (M := M) α hbΔρα_smooth hbΔρα_support
  have hΛ_bound : ∀ j ≤ m, ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      ‖iteratedFDeriv ℝ j Λ y‖ ≤ CΛ := fun j hj y _ => hCΛ_bound j hj y
  obtain ⟨K, hK_pos, hK_bound⟩ :=
    _root_.Sobolev.Euclidean.wkpNorm_smul_smooth_bounded_le
      (d := Module.finrank ℝ E) m (p := 2) (by norm_num)
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
      hΛ_smooth hCΛ_nn hΛ_bound
  obtain ⟨C_strict, hC_strict_pos, hC_strict_bound⟩ :=
    wkpNorm_chartPushedRaw_etaTimesV_le_self (I := I) (M := M) g α m
  set Cfinal : ℝ := K * C_strict with hCfinal_def
  have h_Cfinal_pos : 0 < Cfinal := mul_pos hK_pos hC_strict_pos
  refine ⟨Cfinal, h_Cfinal_pos, ?_⟩
  intro v
  have h_factor : (fun y : EuclN => chartPushedRaw (I := I) (M := M) α
        (lapPiece (I := I) (M := M) g α v.toFun) y) =ᵐ[
        volume.restrict (chartTargetEuclid (I := I) (M := M) α)]
      fun y : EuclN => Λ y * chartPushedRaw (I := I) (M := M) α
        (etaTimesV (I := I) (M := M) α v.toFun) y := by
    refine (MeasureTheory.ae_restrict_iff'
      (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet).mpr ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    exact chartPushedRaw_lapPiece_factor (I := I) (M := M) g α v.toFun
      hb_one_on_tsupp hy
  have hH_Wm2 : MemWkp (d := Module.finrank ℝ E) m 2
      (chartPushedRaw (I := I) (M := M) α
        (etaTimesV (I := I) (M := M) α v.toFun))
      (chartTargetEuclid (I := I) (M := M) α) :=
    memWkp_chartPushedRaw_etaTimesV (I := I) (M := M) g α m v
  have h_product_mem : MemWkp (d := Module.finrank ℝ E) m 2
      (fun y : EuclN => Λ y * chartPushedRaw (I := I) (M := M) α
        (etaTimesV (I := I) (M := M) α v.toFun) y)
      (chartTargetEuclid (I := I) (M := M) α) :=
    _root_.Sobolev.Euclidean.MemWkp.smul_smooth_bounded
      (d := Module.finrank ℝ E) m (by norm_num)
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
      hΛ_smooth hΛ_bound hH_Wm2
  have h_lap_mem : MemWkp (d := Module.finrank ℝ E) m 2
      (chartPushedRaw (I := I) (M := M) α
        (lapPiece (I := I) (M := M) g α v.toFun))
      (chartTargetEuclid (I := I) (M := M) α) :=
    (_root_.Sobolev.Euclidean.MemWkp_congr_ae
      (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (chartTargetEuclid_isOpen (I := I) (M := M) α) h_factor).mpr h_product_mem
  have h_norm_eq :
      _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2
        (chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α) =
      _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2
        (fun y : EuclN => Λ y * chartPushedRaw (I := I) (M := M) α
          (etaTimesV (I := I) (M := M) α v.toFun) y)
        (chartTargetEuclid (I := I) (M := M) α) :=
    _root_.Sobolev.Euclidean.wkpNorm_congr_ae
      (d := Module.finrank ℝ E) (by norm_num)
      (chartTargetEuclid_isOpen (I := I) (M := M) α) h_factor
  rw [h_norm_eq]
  have h_mono : wkpNormChart (I := I) (M := M) m 2 v.toFun ≤
      wkpNormChart (I := I) (M := M) (m + 1) 2 v.toFun :=
    wkpNormChart_le_of_le (I := I) (M := M) m (m + 1)
      (Nat.le_succ _) 2 v.toFun
  refine ⟨h_lap_mem, ?_⟩
  calc _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2
        (fun y => Λ y * chartPushedRaw (I := I) (M := M) α
          (etaTimesV (I := I) (M := M) α v.toFun) y)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal K *
          _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) m 2
            (chartPushedRaw (I := I) (M := M) α
              (etaTimesV (I := I) (M := M) α v.toFun))
            (chartTargetEuclid (I := I) (M := M) α) := hK_bound hH_Wm2
    _ ≤ ENNReal.ofReal K *
            (ENNReal.ofReal C_strict * wkpNormChart (I := I) (M := M) m 2 v.toFun) :=
          mul_le_mul_of_nonneg_left (hC_strict_bound v) (zero_le)
    _ ≤ ENNReal.ofReal K *
            (ENNReal.ofReal C_strict * wkpNormChart (I := I) (M := M) (m + 1) 2 v.toFun) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h_mono (zero_le)) (zero_le)
    _ = ENNReal.ofReal (K * C_strict) *
            wkpNormChart (I := I) (M := M) (m + 1) 2 v.toFun := by
          rw [← mul_assoc, ENNReal.ofReal_mul hK_pos.le]
    _ = ENNReal.ofReal Cfinal *
            wkpNormChart (I := I) (M := M) (m + 1) 2 v.toFun := by
          rw [hCfinal_def]

end CalabiYau.PoissonDomainRegularity
