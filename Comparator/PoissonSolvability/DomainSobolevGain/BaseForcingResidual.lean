module

public import CalabiYau.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplFromDomainPow
public import Comparator.PoissonSolvability.DomainSobolevGain.BaseForcingResidual.ResidualBound
public import Comparator.PoissonSolvability.DomainSobolevGain.BaseForcingResidual.ResidualCauchy
public import Comparator.PoissonSolvability.DomainSobolevGain.BaseForcingResidual.LimitIdentification
public import CalabiYau.Analysis.Sobolev.Approximation.Density.HigherOrder
public import CalabiYau.Analysis.Sobolev.Euclidean.Completeness.IteratedSobolevBanach

/-!
# Sobolev regularity of the Leibniz residual of the base chart forcing

Port target: DifferentialGeometry at `7a48598d35109aa99d1cc678e2724c213cdf4ff3`,
`Analysis/Elliptic/Regularity/Iterated/BaseFChart/PolymorphicRegularity.lean`,
`fChartResidual_memWkp_m` (lines 1020–1037), with its inputs in
`BaseFChart/BilinearRegularity.lean`: smooth approximation, the residual `W^{m,2}`
bound and Cauchy identification. Only chart regularity of `u` is used; no domain power.

Proof: approximate `u` in chart `H^(m+1)` by smooth `v n` at rate `1/(n+1)`
(`contMDiff_dense_in_WkpChart_k`); their residuals are in `H^m` with a uniform bound
(`smoothFChartResidual_memWkp_and_le`), hence Cauchy (`smoothFChartResidual_wkpNorm_cauchy_of_approx`);
the `H^m` limit exists (`MemWkp.exists_limit_of_wkpNorm_cauchy`) and is a.e. the residual of `u_h`
(`smoothFChartResidual_limit_eq_fChartResidual_of_approx`).
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
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- The residual `-2⟨∇ρ_α, ∇u⟩ - (Δρ_α) u`, pushed raw to chart `α`, is in `H^m`
whenever `u` is chart `H^(m+1)`. -/
theorem fChartResidual_memWkp_of_memWkpChart
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu : MemWkpChart (I := I) (M := M) (m + 1) 2
      ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)) :
    MemWkp (d := Module.finrank ℝ E) m 2 (fChartResidual (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set u : M → ℝ := ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ) with hu_def
  have hex : ∀ n : ℕ, ∃ v : SmoothScalar g,
      wkpNormChart (I := I) (M := M) (m + 1) 2 (fun x => u x - v.toFun x) ≤
        ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    intro n
    obtain ⟨w, hw_smooth, hw_le⟩ :=
      _root_.Sobolev.Chart.contMDiff_dense_in_WkpChart_k (I := I) (M := M) (m + 1)
        (p := 2) (by norm_num) (by norm_num) hu
        (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))
    exact ⟨⟨w, hw_smooth⟩, hw_le⟩
  choose v hv using hex
  obtain ⟨C, -, hC⟩ := smoothFChartResidual_memWkp_and_le (I := I) (M := M) g α m
  have h_cauchy := smoothFChartResidual_wkpNorm_cauchy_of_approx (I := I) (M := M) g α m
    hu (fun w => (hC w).2) v hv
  obtain ⟨F, hF, hF_lim⟩ :=
    _root_.Sobolev.Euclidean.MemWkp.exists_limit_of_wkpNorm_cauchy
      (chartTargetEuclid_isOpen (I := I) (M := M) α) m 2 (by norm_num)
      (u := fun n => smoothFChartResidual (I := I) (M := M) g α (v n))
      (fun n => (hC (v n)).1) h_cauchy
  have h_id := smoothFChartResidual_limit_eq_fChartResidual_of_approx (I := I) (M := M)
    g α m hu v hv F hF hF_lim
  exact (_root_.Sobolev.Euclidean.MemWkp_congr_ae (by norm_num)
    (chartTargetEuclid_isOpen (I := I) (M := M) α) h_id).mp hF

end CalabiYau.PoissonDomainRegularity
