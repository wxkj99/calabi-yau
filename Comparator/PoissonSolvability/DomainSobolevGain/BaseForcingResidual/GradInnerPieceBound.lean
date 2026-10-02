module

public import CalabiYau.Analysis.Elliptic.Regularity.SmoothFChartResidual.BilinearBound

/-!
# Sobolev bound for the gradient piece of the base forcing residual

Port target: DifferentialGeometry at `7a48598d35109aa99d1cc678e2724c213cdf4ff3`,
`Analysis/Elliptic/Regularity/Iterated/BaseFChart/BilinearRegularity.lean`,
`wkpNorm_chartPushedRaw_gradInnerPiece_le` (lines 52–280 helpers, 281–607),
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
open CalabiYau.Analysis.Laplacian.GradInnerCLMChartFormula
open CalabiYau.Analysis.Sobolev.Chart
open _root_.Sobolev.Euclidean
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma memWkp_chartPushedRaw_etaTimesV_succ
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ) (v : SmoothScalar g) :
    _root_.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 1) 2
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
    hCP_smooth hCP_compact hCP_tsupp (by norm_num : (1 : ℝ≥0∞) ≤ 2) (m + 1)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma memWkp_chartPushedRaw_etaTimesV
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ) (v : SmoothScalar g) :
    _root_.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) m 2
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

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma memWkp_partialDerivOnEuclid_etaTimesV
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ) (v : SmoothScalar g)
    (i : Fin (Module.finrank ℝ E)) :
    _root_.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) m 2
      (partialDerivOnEuclid (I := I) (M := M) α i
        (etaTimesV (I := I) (M := M) α v.toFun))
      (chartTargetEuclid (I := I) (M := M) α) := by
  have hηv_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (etaTimesV (I := I) (M := M) α v.toFun) :=
    etaTimesV_smooth (I := I) (M := M) α v.smooth
  have hηv_support : tsupport (etaTimesV (I := I) (M := M) α v.toFun) ⊆
      (chartAt H α).source :=
    tsupport_etaTimesV_subset (I := I) (M := M) α v.toFun
  have h_chartPushed_succ := memWkp_chartPushedRaw_etaTimesV_succ
    (I := I) (M := M) g α m v
  have h_chosen_mem :
      _root_.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) m 2
        (_root_.Sobolev.Euclidean.chosenWeakPartialOrZero
          (d := Module.finrank ℝ E) 2 i
          (chartPushedRaw (I := I) (M := M) α
            (etaTimesV (I := I) (M := M) α v.toFun))
          (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) :=
    _root_.Sobolev.Euclidean.MemWkp.chosenWeakPartial_mem
      h_chartPushed_succ i
  have h_ae := partialDerivOnEuclid_ae_eq_chosenWeakPartial
    (I := I) (M := M) (α := α) (i := i) hηv_smooth hηv_support
    (p := (2 : ℝ≥0∞)) (by norm_num)
  exact (_root_.Sobolev.Euclidean.MemWkp_congr_ae
    (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (chartTargetEuclid_isOpen (I := I) (M := M) α) h_ae).mpr h_chosen_mem

private lemma wkpNorm_chartPushedRaw_etaTimesV_le_succ
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SmoothScalar g,
      _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) (m + 1) 2
        (chartPushedRaw (I := I) (M := M) α
          (etaTimesV (I := I) (M := M) α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal C * wkpNormChart (I := I) (M := M) (m + 1) 2
        (fun x : M => v.toFun x) := by
  classical
  obtain ⟨C, hC_pos, hC_bound⟩ :=
    _root_.Sobolev.Chart.wkpNorm_chartPushedRaw_strictCutoff_mul_le
      (I := I) (M := M) g α (m + 1) (p := 2) (by norm_num) (by norm_num)
  refine ⟨C, hC_pos, ?_⟩
  intro v
  have h_v_MemWkpChart : MemWkpChart (I := I) (M := M) (m + 1) 2 v.toFun :=
    _root_.CalabiYau.Analysis.Sobolev.Chart.memWkpChart_of_contMDiff_k (I := I) (M := M) (by norm_num) (m + 1) v.smooth
  have h_funext : etaTimesV (I := I) (M := M) α v.toFun =
      fun x : M => chartStrictCutoff (I := I) (M := M) α x * v.toFun x := by
    funext x; rfl
  rw [h_funext]
  exact hC_bound h_v_MemWkpChart

private lemma wkpNorm_chartPushedRaw_etaTimesV_le_self
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SmoothScalar g,
      _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2
        (chartPushedRaw (I := I) (M := M) α
          (etaTimesV (I := I) (M := M) α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal C * wkpNormChart (I := I) (M := M) m 2
        (fun x : M => v.toFun x) := by
  classical
  obtain ⟨C, hC_pos, hC_bound⟩ :=
    _root_.Sobolev.Chart.wkpNorm_chartPushedRaw_strictCutoff_mul_le
      (I := I) (M := M) g α m (p := 2) (by norm_num) (by norm_num)
  refine ⟨C, hC_pos, ?_⟩
  intro v
  have h_v_MemWkpChart : MemWkpChart (I := I) (M := M) m 2 v.toFun :=
    _root_.CalabiYau.Analysis.Sobolev.Chart.memWkpChart_of_contMDiff_k (I := I) (M := M) (by norm_num) m v.smooth
  have h_funext : etaTimesV (I := I) (M := M) α v.toFun =
      fun x : M => chartStrictCutoff (I := I) (M := M) α x * v.toFun x := by
    funext x; rfl
  rw [h_funext]
  exact hC_bound h_v_MemWkpChart

private lemma wkpNorm_partialDerivOnEuclid_etaTimesV_le_m
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SmoothScalar g,
      ∀ i : Fin (Module.finrank ℝ E),
        _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) m 2
          (partialDerivOnEuclid (I := I) (M := M) α i
            (etaTimesV (I := I) (M := M) α v.toFun))
          (chartTargetEuclid (I := I) (M := M) α) ≤
        ENNReal.ofReal C * wkpNormChart (I := I) (M := M) (m + 1) 2
          (fun x : M => v.toFun x) := by
  classical
  have h_per_i_partial : ∀ i : Fin (Module.finrank ℝ E), ∃ C_p : ℝ, 0 < C_p ∧
      ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u → tsupport u ⊆ (chartAt H α).source →
        _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) m 2
          (partialDerivOnEuclid (I := I) (M := M) α i u)
          (chartTargetEuclid (I := I) (M := M) α) ≤
        ENNReal.ofReal C_p *
          _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) (m + 1) 2
            (chartPushedRaw (I := I) (M := M) α u)
            (chartTargetEuclid (I := I) (M := M) α) := fun i =>
    wkpNorm_partialDerivOnEuclid_le_wkpNorm_chartPushedRaw_succ
      (I := I) (M := M) α i m (p := 2) (by norm_num)
  let Cp : Fin (Module.finrank ℝ E) → ℝ := fun i => (h_per_i_partial i).choose
  have hCp_pos : ∀ i, 0 < Cp i := fun i => (h_per_i_partial i).choose_spec.1
  have hCp_bound : ∀ i : Fin (Module.finrank ℝ E),
      ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u → tsupport u ⊆ (chartAt H α).source →
        _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) m 2
          (partialDerivOnEuclid (I := I) (M := M) α i u)
          (chartTargetEuclid (I := I) (M := M) α) ≤
        ENNReal.ofReal (Cp i) *
          _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) (m + 1) 2
            (chartPushedRaw (I := I) (M := M) α u)
            (chartTargetEuclid (I := I) (M := M) α) := fun i =>
    (h_per_i_partial i).choose_spec.2
  obtain ⟨C_strict, hC_strict_pos, hC_strict_bound⟩ :=
    wkpNorm_chartPushedRaw_etaTimesV_le_succ (I := I) (M := M) g α m
  have h_fin_pos : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero (NeZero.ne _)
  have h_nonempty : Nonempty (Fin (Module.finrank ℝ E)) := ⟨⟨0, h_fin_pos⟩⟩
  set Cmax : ℝ := Finset.univ.sup' (Finset.univ_nonempty (α := Fin _)) Cp
  have hCmax_ge : ∀ i, Cp i ≤ Cmax := fun i => Finset.le_sup' Cp (Finset.mem_univ i)
  have hCmax_pos : 0 < Cmax :=
    lt_of_lt_of_le (hCp_pos h_nonempty.some) (hCmax_ge h_nonempty.some)
  set C_total : ℝ := Cmax * C_strict with hC_total_def
  have hC_total_pos : 0 < C_total := mul_pos hCmax_pos hC_strict_pos
  refine ⟨C_total, hC_total_pos, ?_⟩
  intro v i
  have hηv_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (etaTimesV (I := I) (M := M) α v.toFun) :=
    etaTimesV_smooth (I := I) (M := M) α v.smooth
  have hηv_support : tsupport (etaTimesV (I := I) (M := M) α v.toFun) ⊆
      (chartAt H α).source :=
    tsupport_etaTimesV_subset (I := I) (M := M) α v.toFun
  have h_partial_bound := hCp_bound i hηv_smooth hηv_support
  have h_strict_bound := hC_strict_bound v
  calc _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2
        (partialDerivOnEuclid (I := I) (M := M) α i
          (etaTimesV (I := I) (M := M) α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal (Cp i) *
          _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) (m + 1) 2
            (chartPushedRaw (I := I) (M := M) α
              (etaTimesV (I := I) (M := M) α v.toFun))
            (chartTargetEuclid (I := I) (M := M) α) := h_partial_bound
    _ ≤ ENNReal.ofReal (Cp i) *
            (ENNReal.ofReal C_strict * wkpNormChart (I := I) (M := M) (m + 1) 2 v.toFun) :=
            mul_le_mul_of_nonneg_left h_strict_bound (zero_le)
    _ = ENNReal.ofReal (Cp i * C_strict) *
            wkpNormChart (I := I) (M := M) (m + 1) 2 v.toFun := by
            rw [← mul_assoc, ENNReal.ofReal_mul (hCp_pos i).le]
    _ ≤ ENNReal.ofReal C_total *
            wkpNormChart (I := I) (M := M) (m + 1) 2 v.toFun := by
            refine mul_le_mul_of_nonneg_right ?_ (zero_le)
            refine ENNReal.ofReal_le_ofReal ?_
            rw [hC_total_def]
            exact mul_le_mul_of_nonneg_right (hCmax_ge i) hC_strict_pos.le

private lemma wkpNorm_chartPushedRaw_gradInnerPiece_le
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SmoothScalar g,
      _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2
        (chartPushedRaw (I := I) (M := M) α
          (gradInnerPiece (I := I) (M := M) g α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal C * wkpNormChart (I := I) (M := M) (m + 1) 2
        (fun x : M => v.toFun x) := by
  classical
  have h_per_i_smul : ∀ i : Fin (Module.finrank ℝ E), ∃ K : ℝ, 0 < K ∧
      ∀ {u : EuclN → ℝ},
        _root_.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) m 2 u
          (chartTargetEuclid (I := I) (M := M) α) →
        _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) m 2
          (fun y => Λgrad (I := I) (M := M) g α i y * u y)
          (chartTargetEuclid (I := I) (M := M) α) ≤
        ENNReal.ofReal K *
          _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) m 2 u
            (chartTargetEuclid (I := I) (M := M) α) := by
    intro i
    obtain ⟨C_Λ, hC_Λ_nn, hC_Λ_bound⟩ :=
      _root_.CalabiYau.Analysis.Sobolev.Chart.smoothExtensionScalar_iteratedFDeriv_bound
        (I := I) (M := M) α
        (gradInnerCoefI_M_smooth (I := I) (M := M) g α i)
        (tsupport_gradInnerCoefI_M_subset (I := I) (M := M) g α i) m
    exact _root_.Sobolev.Euclidean.wkpNorm_smul_smooth_bounded_le
      (d := Module.finrank ℝ E) m (p := 2) (by norm_num) (by norm_num)
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
      (Λgrad_contDiff (I := I) (M := M) g α i)
      hC_Λ_nn (fun j hj y _ => hC_Λ_bound j hj y)
  let K : Fin (Module.finrank ℝ E) → ℝ := fun i => (h_per_i_smul i).choose
  have hK_pos : ∀ i, 0 < K i := fun i => (h_per_i_smul i).choose_spec.1
  have hK_bound : ∀ i : Fin (Module.finrank ℝ E),
      ∀ {u : EuclN → ℝ},
        _root_.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) m 2 u
          (chartTargetEuclid (I := I) (M := M) α) →
        _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) m 2
          (fun y => Λgrad (I := I) (M := M) g α i y * u y)
          (chartTargetEuclid (I := I) (M := M) α) ≤
        ENNReal.ofReal (K i) *
          _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) m 2 u
            (chartTargetEuclid (I := I) (M := M) α) := fun i =>
    (h_per_i_smul i).choose_spec.2
  obtain ⟨C_partial, hC_partial_pos, hC_partial_bound⟩ :=
    wkpNorm_partialDerivOnEuclid_etaTimesV_le_m (I := I) (M := M) g α m
  set sumK : ℝ := ∑ i : Fin (Module.finrank ℝ E), K i with hsumK_def
  have hsumK_nn : 0 ≤ sumK :=
    Finset.sum_nonneg (fun i _ => (hK_pos i).le)
  set Cfinal : ℝ := 2 * (sumK * C_partial) + 1 with hCfinal_def
  have h_Cfinal_pos : 0 < Cfinal := by
    rw [hCfinal_def]; linarith [mul_nonneg hsumK_nn hC_partial_pos.le]
  refine ⟨Cfinal, h_Cfinal_pos, ?_⟩
  intro v
  have h_pointwise : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      chartPushedRaw (I := I) (M := M) α
          (gradInnerPiece (I := I) (M := M) g α v.toFun) y =
        (2 : ℝ) * ∑ i : Fin (Module.finrank ℝ E),
          Λgrad (I := I) (M := M) g α i y *
            partialDerivOnEuclid (I := I) (M := M) α i
              (etaTimesV (I := I) (M := M) α v.toFun) y := fun y hy =>
    chartPushedRaw_gradInnerPiece_eq_sum (I := I) (M := M) g α v hy
  have h_ae : (chartPushedRaw (I := I) (M := M) α
        (gradInnerPiece (I := I) (M := M) g α v.toFun)) =ᵐ[
        volume.restrict (chartTargetEuclid (I := I) (M := M) α)]
      fun y => (2 : ℝ) * ∑ i : Fin (Module.finrank ℝ E),
        Λgrad (I := I) (M := M) g α i y *
          partialDerivOnEuclid (I := I) (M := M) α i
            (etaTimesV (I := I) (M := M) α v.toFun) y := by
    refine (MeasureTheory.ae_restrict_iff'
      (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy; exact h_pointwise y hy
  rw [_root_.Sobolev.Euclidean.wkpNorm_congr_ae
        (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        (chartTargetEuclid_isOpen (I := I) (M := M) α) h_ae]
  have h_partial_mem : ∀ i : Fin (Module.finrank ℝ E),
      _root_.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) m 2
        (partialDerivOnEuclid (I := I) (M := M) α i
          (etaTimesV (I := I) (M := M) α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α) := fun i =>
    memWkp_partialDerivOnEuclid_etaTimesV (I := I) (M := M) g α m v i
  have h_summand_mem : ∀ i : Fin (Module.finrank ℝ E),
      _root_.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) m 2
        (fun y : EuclN => Λgrad (I := I) (M := M) g α i y *
          partialDerivOnEuclid (I := I) (M := M) α i
            (etaTimesV (I := I) (M := M) α v.toFun) y)
        (chartTargetEuclid (I := I) (M := M) α) := by
    intro i
    obtain ⟨C_Λ, hC_Λ_nn, hC_Λ_bound⟩ :=
      _root_.CalabiYau.Analysis.Sobolev.Chart.smoothExtensionScalar_iteratedFDeriv_bound
        (I := I) (M := M) α
        (gradInnerCoefI_M_smooth (I := I) (M := M) g α i)
        (tsupport_gradInnerCoefI_M_subset (I := I) (M := M) g α i) m
    exact _root_.Sobolev.Euclidean.MemWkp.smul_smooth_bounded
      (d := Module.finrank ℝ E) m (p := 2) (by norm_num)
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
      (Λgrad_contDiff (I := I) (M := M) g α i)
      (fun j hj y _ => hC_Λ_bound j hj y)
      (h_partial_mem i)
  have h_sum_mem_gen : ∀ (S : Finset (Fin (Module.finrank ℝ E))),
      (∀ ε ∈ S, _root_.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) m 2
        (fun y : EuclN => Λgrad (I := I) (M := M) g α ε y *
          partialDerivOnEuclid (I := I) (M := M) α ε
            (etaTimesV (I := I) (M := M) α v.toFun) y)
        (chartTargetEuclid (I := I) (M := M) α)) →
      _root_.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) m 2
        (fun y : EuclN => ∑ ε ∈ S,
          Λgrad (I := I) (M := M) g α ε y *
            partialDerivOnEuclid (I := I) (M := M) α ε
              (etaTimesV (I := I) (M := M) α v.toFun) y)
        (chartTargetEuclid (I := I) (M := M) α) := by
    intro S
    induction S using Finset.induction with
    | empty =>
        intro _
        simp only [Finset.sum_empty]
        exact _root_.Sobolev.Euclidean.MemWkp_zero_fun
          (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
          (chartTargetEuclid_isOpen (I := I) (M := M) α)
    | insert δ S' hδ ih2 =>
        intro hf
        have hf_δ := hf δ (Finset.mem_insert_self δ S')
        have hf_S' : ∀ ε ∈ S', _ := fun ε hε =>
          hf ε (Finset.mem_insert_of_mem hε)
        have hsum := ih2 hf_S'
        have h_eq : (fun y : EuclN => ∑ ε ∈ insert δ S',
            Λgrad (I := I) (M := M) g α ε y *
              partialDerivOnEuclid (I := I) (M := M) α ε
                (etaTimesV (I := I) (M := M) α v.toFun) y) =
            fun y : EuclN =>
              (Λgrad (I := I) (M := M) g α δ y *
                partialDerivOnEuclid (I := I) (M := M) α δ
                  (etaTimesV (I := I) (M := M) α v.toFun) y) +
              ∑ ε ∈ S', Λgrad (I := I) (M := M) g α ε y *
                partialDerivOnEuclid (I := I) (M := M) α ε
                  (etaTimesV (I := I) (M := M) α v.toFun) y := by
          funext y; exact Finset.sum_insert hδ
        rw [h_eq]
        exact _root_.Sobolev.Euclidean.MemWkp.add
          (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
          (chartTargetEuclid_isOpen (I := I) (M := M) α) hf_δ hsum
  have h_sum_mem :
      _root_.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) m 2
        (fun y : EuclN => ∑ i : Fin (Module.finrank ℝ E),
          Λgrad (I := I) (M := M) g α i y *
            partialDerivOnEuclid (I := I) (M := M) α i
              (etaTimesV (I := I) (M := M) α v.toFun) y)
        (chartTargetEuclid (I := I) (M := M) α) :=
    h_sum_mem_gen Finset.univ (fun i _ => h_summand_mem i)
  have h_const2 :
      _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2
        (fun y => (2 : ℝ) * ∑ i : Fin (Module.finrank ℝ E),
          Λgrad (I := I) (M := M) g α i y *
            partialDerivOnEuclid (I := I) (M := M) α i
              (etaTimesV (I := I) (M := M) α v.toFun) y)
        (chartTargetEuclid (I := I) (M := M) α) =
      ‖(2 : ℝ)‖ₑ *
        _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) m 2
          (fun y : EuclN => ∑ i : Fin (Module.finrank ℝ E),
            Λgrad (I := I) (M := M) g α i y *
              partialDerivOnEuclid (I := I) (M := M) α i
                (etaTimesV (I := I) (M := M) α v.toFun) y)
          (chartTargetEuclid (I := I) (M := M) α) :=
    _root_.Sobolev.Euclidean.wkpNorm_const_smul
      (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (chartTargetEuclid_isOpen (I := I) (M := M) α) h_sum_mem (2 : ℝ)
  rw [h_const2]
  have h_triangle :
      _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2
        (fun y : EuclN => ∑ i : Fin (Module.finrank ℝ E),
          Λgrad (I := I) (M := M) g α i y *
            partialDerivOnEuclid (I := I) (M := M) α i
              (etaTimesV (I := I) (M := M) α v.toFun) y)
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ∑ i : Fin (Module.finrank ℝ E),
        _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) m 2
          (fun y : EuclN => Λgrad (I := I) (M := M) g α i y *
            partialDerivOnEuclid (I := I) (M := M) α i
              (etaTimesV (I := I) (M := M) α v.toFun) y)
          (chartTargetEuclid (I := I) (M := M) α) := by
    have h_gen : ∀ (T : Finset (Fin (Module.finrank ℝ E))),
        (∀ i ∈ T, _root_.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) m 2
          (fun y : EuclN => Λgrad (I := I) (M := M) g α i y *
            partialDerivOnEuclid (I := I) (M := M) α i
              (etaTimesV (I := I) (M := M) α v.toFun) y)
          (chartTargetEuclid (I := I) (M := M) α)) →
        _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) m 2
          (fun y : EuclN => ∑ i ∈ T,
            Λgrad (I := I) (M := M) g α i y *
              partialDerivOnEuclid (I := I) (M := M) α i
                (etaTimesV (I := I) (M := M) α v.toFun) y)
          (chartTargetEuclid (I := I) (M := M) α) ≤
        ∑ i ∈ T,
          _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) m 2
            (fun y : EuclN => Λgrad (I := I) (M := M) g α i y *
              partialDerivOnEuclid (I := I) (M := M) α i
                (etaTimesV (I := I) (M := M) α v.toFun) y)
            (chartTargetEuclid (I := I) (M := M) α) := by
      intro T
      induction T using Finset.induction with
      | empty =>
          intro _
          simp only [Finset.sum_empty]
          rw [_root_.Sobolev.Euclidean.wkpNorm_zero_fun_zero
            (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
            (chartTargetEuclid_isOpen (I := I) (M := M) α)]
      | insert γ T hγ ih =>
          intro hf_mem
          have hf_γ_mem := hf_mem γ (Finset.mem_insert_self γ T)
          have hf_T_mem : ∀ ε ∈ T,
              _root_.Sobolev.Euclidean.MemWkp
                (d := Module.finrank ℝ E) m 2
                (fun y : EuclN => Λgrad (I := I) (M := M) g α ε y *
                  partialDerivOnEuclid (I := I) (M := M) α ε
                    (etaTimesV (I := I) (M := M) α v.toFun) y)
                (chartTargetEuclid (I := I) (M := M) α) := fun ε hε =>
            hf_mem ε (Finset.mem_insert_of_mem hε)
          have h_sumT_mem : _root_.Sobolev.Euclidean.MemWkp
              (d := Module.finrank ℝ E) m 2
              (fun y : EuclN => ∑ ε ∈ T,
                Λgrad (I := I) (M := M) g α ε y *
                  partialDerivOnEuclid (I := I) (M := M) α ε
                    (etaTimesV (I := I) (M := M) α v.toFun) y)
              (chartTargetEuclid (I := I) (M := M) α) := h_sum_mem_gen T hf_T_mem
          have h_eq : (fun y : EuclN => ∑ ε ∈ insert γ T,
              Λgrad (I := I) (M := M) g α ε y *
                partialDerivOnEuclid (I := I) (M := M) α ε
                  (etaTimesV (I := I) (M := M) α v.toFun) y) =
              fun y : EuclN =>
                (Λgrad (I := I) (M := M) g α γ y *
                  partialDerivOnEuclid (I := I) (M := M) α γ
                    (etaTimesV (I := I) (M := M) α v.toFun) y) +
                ∑ ε ∈ T, Λgrad (I := I) (M := M) g α ε y *
                  partialDerivOnEuclid (I := I) (M := M) α ε
                    (etaTimesV (I := I) (M := M) α v.toFun) y := by
            funext y; exact Finset.sum_insert hγ
          rw [h_eq, Finset.sum_insert hγ]
          have h_triangle_step :=
            _root_.Sobolev.Euclidean.wkpNorm_add_le
              (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
              (chartTargetEuclid_isOpen (I := I) (M := M) α) hf_γ_mem h_sumT_mem
          have h_ih := ih hf_T_mem
          refine h_triangle_step.trans ?_
          exact add_le_add le_rfl h_ih
    exact h_gen Finset.univ (fun i _ => h_summand_mem i)
  have h_two_norm : ‖(2 : ℝ)‖ₑ = ENNReal.ofReal 2 := by
    rw [Real.enorm_eq_ofReal (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h_two_norm]
  refine le_trans (mul_le_mul_of_nonneg_left h_triangle (zero_le)) ?_
  have h_each_bound : ∀ i : Fin (Module.finrank ℝ E),
      _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2
        (fun y : EuclN => Λgrad (I := I) (M := M) g α i y *
          partialDerivOnEuclid (I := I) (M := M) α i
            (etaTimesV (I := I) (M := M) α v.toFun) y)
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal (K i * C_partial) *
        wkpNormChart (I := I) (M := M) (m + 1) 2 v.toFun := by
    intro i
    have h_step1 := hK_bound i (h_partial_mem i)
    have h_step2 := hC_partial_bound v i
    calc _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) m 2
          (fun y => Λgrad (I := I) (M := M) g α i y *
            partialDerivOnEuclid (I := I) (M := M) α i
              (etaTimesV (I := I) (M := M) α v.toFun) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (K i) *
            _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := Module.finrank ℝ E) m 2
              (partialDerivOnEuclid (I := I) (M := M) α i
                (etaTimesV (I := I) (M := M) α v.toFun))
              (chartTargetEuclid (I := I) (M := M) α) := h_step1
      _ ≤ ENNReal.ofReal (K i) *
              (ENNReal.ofReal C_partial * wkpNormChart (I := I) (M := M) (m + 1) 2 v.toFun) :=
            mul_le_mul_of_nonneg_left h_step2 (zero_le)
      _ = ENNReal.ofReal (K i * C_partial) *
              wkpNormChart (I := I) (M := M) (m + 1) 2 v.toFun := by
            rw [← mul_assoc, ENNReal.ofReal_mul (hK_pos i).le]
  have h_sum_bound : ∑ i : Fin (Module.finrank ℝ E),
      _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2
        (fun y : EuclN => Λgrad (I := I) (M := M) g α i y *
          partialDerivOnEuclid (I := I) (M := M) α i
            (etaTimesV (I := I) (M := M) α v.toFun) y)
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ∑ i : Fin (Module.finrank ℝ E),
        ENNReal.ofReal (K i * C_partial) *
          wkpNormChart (I := I) (M := M) (m + 1) 2 v.toFun :=
    Finset.sum_le_sum (fun i _ => h_each_bound i)
  refine le_trans (mul_le_mul_of_nonneg_left h_sum_bound (zero_le)) ?_
  rw [← Finset.sum_mul]
  rw [show ∑ i : Fin (Module.finrank ℝ E), ENNReal.ofReal (K i * C_partial) =
      ENNReal.ofReal (∑ i : Fin (Module.finrank ℝ E), K i * C_partial) from by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro i _
        exact mul_nonneg (hK_pos i).le hC_partial_pos.le]
  rw [show ∑ i : Fin (Module.finrank ℝ E), K i * C_partial = sumK * C_partial from by
        rw [hsumK_def, Finset.sum_mul]]
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (zero_le)
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hCfinal_def]; linarith [mul_nonneg hsumK_nn hC_partial_pos.le]

/-- For smooth `v`, the raw chart push of the gradient piece `2⟨∇ρ_α, ∇(η_α v)⟩`
of the residual is in `H^m` on the chart target, with `H^m` norm bounded by a uniform constant
times the chart `H^(m+1)` norm of `v`. -/
theorem chartPushedRaw_gradInnerPiece_memWkp_and_le
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SmoothScalar g,
      MemWkp (d := Module.finrank ℝ E) m 2
        (chartPushedRaw (I := I) (M := M) α (gradInnerPiece (I := I) (M := M) g α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α) ∧
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) m 2
        (chartPushedRaw (I := I) (M := M) α (gradInnerPiece (I := I) (M := M) g α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal C * wkpNormChart (I := I) (M := M) (m + 1) 2 v.toFun := by
  classical
  obtain ⟨C, hC_pos, hC_bound⟩ :=
    wkpNorm_chartPushedRaw_gradInnerPiece_le (I := I) (M := M) g α m
  refine ⟨C, hC_pos, ?_⟩
  intro v
  have h_smooth := gradInnerPiece_smooth (I := I) (M := M) g α v
  have h_support := tsupport_gradInnerPiece_subset_source
    (I := I) (M := M) g α v.toFun
  have hCP_smooth : ContDiff ℝ ∞
      (chartPushedRaw (I := I) (M := M) α
        (gradInnerPiece (I := I) (M := M) g α v.toFun)) :=
    chartPushedRaw_contDiff (I := I) h_smooth h_support
  have hCP_compact : HasCompactSupport
      (chartPushedRaw (I := I) (M := M) α
        (gradInnerPiece (I := I) (M := M) g α v.toFun)) :=
    chartPushedRaw_smooth_hasCompactSupport_local (I := I) h_support
  have hCP_tsupp : tsupport (chartPushedRaw (I := I) (M := M) α
        (gradInnerPiece (I := I) (M := M) g α v.toFun)) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    tsupport_chartPushedRaw_subset_chartTargetEuclid (I := I) h_support
  have h_mem := _root_.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport
    (d := Module.finrank ℝ E)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    hCP_smooth hCP_compact hCP_tsupp (by norm_num : (1 : ℝ≥0∞) ≤ 2) m
  exact ⟨h_mem, hC_bound v⟩

end CalabiYau.PoissonDomainRegularity
