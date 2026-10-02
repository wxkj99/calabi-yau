module

public import Comparator.PoissonSolvability.DomainSobolevGain.SuccessorEquation

/-!
# Data for one differentiated chart step

Following differential-geometry, the construction in
`Iterated/VariationalIdentity/InductiveSuccessor.lean`.
The forcing L² bound and weak equation are supplied by separate lemmas.
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

open CalabiYau.RiemannianVolume
open CalabiYau.Analysis.Laplacian
open Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- A faithful single successor, with all analytic hypotheses exposed. -/
def IteratedDiffChartBilinearData.successor
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g} (m : ℕ)
    (D : IteratedDiffChartBilinearData (I := I) (M := M) g α u_h m)
    (l : Fin (Module.finrank ℝ E))
    (h_chart_H_m_plus_1 :
      Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) (m + 1) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α))
    (h_chart_H_m_plus_2 :
      Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) (m + 2) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α))
    (h_forcing_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      D.diffChartForcing (chartTargetEuclid (I := I) (M := M) α))
    (h_forcing_ae_zero :
      D.diffChartForcing =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ))) :
    IteratedDiffChartBilinearData (I := I) (M := M) g α u_h (m + 1) :=
  IteratedDiffChartBilinearData.mkFromHypotheses
    (Fin.snoc D.directions l)
    (successorChartForcing g α u_h m D.directions D.diffChartForcing l)
    (successorChartForcing_memLp h_chart_H_m_plus_1 h_chart_H_m_plus_2
      D.fChartEffective_memLp_weighted)
    (successorChart_variational_identity g α m D l
      h_chart_H_m_plus_1 h_chart_H_m_plus_2 h_forcing_memW1p h_forcing_ae_zero)

end CalabiYau.PoissonDomainRegularity
