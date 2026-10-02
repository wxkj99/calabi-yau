module

public import Comparator.PoissonSolvability.DomainSobolevGain.BaseForcingResidual.GradInnerPieceBound
public import Comparator.PoissonSolvability.DomainSobolevGain.BaseForcingResidual.LapPieceBound

/-!
# Sobolev bound for the smooth base forcing residual

Port target: DifferentialGeometry at `7a48598d35109aa99d1cc678e2724c213cdf4ff3`,
`Analysis/Elliptic/Regularity/Iterated/BaseFChart/BilinearRegularity.lean`,
`wkpNorm_smoothFChartResidual_le_wkpNormChart_wkpM` (lines 723–890) and
`smoothFChartResidual_memWkp_m` (lines 891–996): the residual of smooth `v` agrees a.e. on the
chart target with `-(gradient piece) - (Laplacian piece)`
(`smoothFChartResidual_ae_eq_chartPushedRaw_smoothRep`, `chartPushedRaw_smoothRep_eq`), so both
statements follow from the two piece bounds.
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
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- For smooth `v`, the base forcing residual is in `H^m` on the chart target, with `H^m` norm
bounded by a uniform constant times the chart `H^(m+1)` norm of `v`. -/
theorem smoothFChartResidual_memWkp_and_le
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SmoothScalar g,
      MemWkp (d := Module.finrank ℝ E) m 2
        (smoothFChartResidual (I := I) (M := M) g α v)
        (chartTargetEuclid (I := I) (M := M) α) ∧
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) m 2
        (smoothFChartResidual (I := I) (M := M) g α v)
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal C * wkpNormChart (I := I) (M := M) (m + 1) 2 v.toFun := by
  classical
  obtain ⟨C_grad, hC_grad_pos, hC_grad⟩ :=
    chartPushedRaw_gradInnerPiece_memWkp_and_le (I := I) (M := M) g α m
  obtain ⟨C_lap, hC_lap_pos, hC_lap⟩ :=
    chartPushedRaw_lapPiece_memWkp_and_le (I := I) (M := M) g α m
  refine ⟨C_grad + C_lap, by linarith, ?_⟩
  intro v
  have h_ae := smoothFChartResidual_ae_eq_chartPushedRaw_smoothRep
    (I := I) (M := M) g α v
  have h_ae_pieces :
      smoothFChartResidual (I := I) (M := M) g α v =ᵐ[
        (volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)]
      (fun y => (-1 : ℝ) * chartPushedRaw (I := I) (M := M) α
          (gradInnerPiece (I := I) (M := M) g α v.toFun) y +
        (-1 : ℝ) * chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun) y) := by
    filter_upwards [h_ae] with y hy
    rw [hy, chartPushedRaw_smoothRep_eq (I := I) (M := M) g α v y]
    ring
  have h_grad := (hC_grad v).1
  have h_lap := (hC_lap v).1
  have hP_neg_grad :=
    _root_.Sobolev.Euclidean.MemWkp.const_smul
      (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (chartTargetEuclid_isOpen (I := I) (M := M) α) h_grad (-1 : ℝ)
  have hP_neg_lap :=
    _root_.Sobolev.Euclidean.MemWkp.const_smul
      (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (chartTargetEuclid_isOpen (I := I) (M := M) α) h_lap (-1 : ℝ)
  have h_sum_mem := _root_.Sobolev.Euclidean.MemWkp.add
    (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (chartTargetEuclid_isOpen (I := I) (M := M) α) hP_neg_grad hP_neg_lap
  have h_res_mem :=
    (_root_.Sobolev.Euclidean.MemWkp_congr_ae
      (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (chartTargetEuclid_isOpen (I := I) (M := M) α) h_ae_pieces).mpr h_sum_mem
  have h_tri := _root_.Sobolev.Euclidean.wkpNorm_add_le
    (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (chartTargetEuclid_isOpen (I := I) (M := M) α) hP_neg_grad hP_neg_lap
  have h_neg_norm_grad :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) m 2
        (fun y => (-1 : ℝ) * chartPushedRaw (I := I) (M := M) α
          (gradInnerPiece (I := I) (M := M) g α v.toFun) y)
        (chartTargetEuclid (I := I) (M := M) α) =
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) m 2
        (chartPushedRaw (I := I) (M := M) α
          (gradInnerPiece (I := I) (M := M) g α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α) := by
    rw [_root_.Sobolev.Euclidean.wkpNorm_const_smul
      (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (chartTargetEuclid_isOpen (I := I) (M := M) α) h_grad (-1 : ℝ)]
    have hnorm : ‖(-1 : ℝ)‖ₑ = 1 := by
      rw [Real.enorm_eq_ofReal_abs]
      simp
    rw [hnorm, one_mul]
  have h_neg_norm_lap :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) m 2
        (fun y => (-1 : ℝ) * chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun) y)
        (chartTargetEuclid (I := I) (M := M) α) =
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) m 2
        (chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α) := by
    rw [_root_.Sobolev.Euclidean.wkpNorm_const_smul
      (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (chartTargetEuclid_isOpen (I := I) (M := M) α) h_lap (-1 : ℝ)]
    have hnorm : ‖(-1 : ℝ)‖ₑ = 1 := by
      rw [Real.enorm_eq_ofReal_abs]
      simp
    rw [hnorm, one_mul]
  have h_norm_eq := _root_.Sobolev.Euclidean.wkpNorm_congr_ae
    (d := Module.finrank ℝ E) (k := m) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (chartTargetEuclid_isOpen (I := I) (M := M) α) h_ae_pieces
  refine ⟨h_res_mem, ?_⟩
  calc
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) m 2
        (smoothFChartResidual (I := I) (M := M) g α v)
        (chartTargetEuclid (I := I) (M := M) α) =
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) m 2
        (fun y => (-1 : ℝ) * chartPushedRaw (I := I) (M := M) α
          (gradInnerPiece (I := I) (M := M) g α v.toFun) y +
          (-1 : ℝ) * chartPushedRaw (I := I) (M := M) α
            (lapPiece (I := I) (M := M) g α v.toFun) y)
        (chartTargetEuclid (I := I) (M := M) α) := h_norm_eq
    _ ≤ iteratedWeakSobolevNorm (d := Module.finrank ℝ E) m 2
          (fun y => (-1 : ℝ) * chartPushedRaw (I := I) (M := M) α
            (gradInnerPiece (I := I) (M := M) g α v.toFun) y)
          (chartTargetEuclid (I := I) (M := M) α) +
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) m 2
          (fun y => (-1 : ℝ) * chartPushedRaw (I := I) (M := M) α
            (lapPiece (I := I) (M := M) g α v.toFun) y)
          (chartTargetEuclid (I := I) (M := M) α) := h_tri
    _ = iteratedWeakSobolevNorm (d := Module.finrank ℝ E) m 2
          (chartPushedRaw (I := I) (M := M) α
            (gradInnerPiece (I := I) (M := M) g α v.toFun))
          (chartTargetEuclid (I := I) (M := M) α) +
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) m 2
          (chartPushedRaw (I := I) (M := M) α
            (lapPiece (I := I) (M := M) g α v.toFun))
          (chartTargetEuclid (I := I) (M := M) α) := by
            rw [h_neg_norm_grad, h_neg_norm_lap]
    _ ≤ ENNReal.ofReal C_grad * wkpNormChart (I := I) (M := M) (m + 1) 2 v.toFun +
        ENNReal.ofReal C_lap * wkpNormChart (I := I) (M := M) (m + 1) 2 v.toFun :=
          add_le_add (hC_grad v).2 (hC_lap v).2
    _ = ENNReal.ofReal (C_grad + C_lap) *
        wkpNormChart (I := I) (M := M) (m + 1) 2 v.toFun := by
          calc
            _ = (ENNReal.ofReal C_grad + ENNReal.ofReal C_lap) *
                wkpNormChart (I := I) (M := M) (m + 1) 2 v.toFun := by rw [add_mul]
            _ = _ := by rw [ENNReal.ofReal_add hC_grad_pos.le hC_lap_pos.le]

end CalabiYau.PoissonDomainRegularity
