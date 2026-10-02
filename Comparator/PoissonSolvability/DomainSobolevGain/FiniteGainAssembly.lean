module

public import Comparator.PoissonSolvability.DomainSobolevGain.BaseData
public import Comparator.PoissonSolvability.DomainSobolevGain.SuccessorData
public import Comparator.PoissonSolvability.DomainSobolevGain.FiniteForcingRegularity

/-!
# Ordinary-domain finite differentiated-data assembly

The initial compensated forcing estimate remains explicit. The successor
constructor and descending forcing regularity are the existing frozen providers.
This module does not assert the final Sobolev gain or discharge eta weak-gradient
identification.
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
open CalabiYau.RiemannianVolume CalabiYau.Analysis.Laplacian Sobolev.Chart
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.LaplacianDomainChartData
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- Every direction sequence has actual differentiated data. The initial forcing
estimate and support remain explicit; no target solution regularity is used. -/
theorem ordinaryDomain_all_direction_data_of_initial_forcing
    (g : SmoothRiemannianMetric I M) (α : M)
    (u : laplacianDomain (I := I) (M := M) g) (r : ℕ)
    (hu : MemWkpChart (I := I) (M := M) (r + 1) 2
      (H1ComplToLp g (u : H1Compl g) : M → ℝ))
    (h_initial : Sobolev.Euclidean.MemWkp r 2
      (chartBilinearH1ComplDataOfLaplacianDomain g α u.property).fChart
      (chartTargetEuclid (I := I) (M := M) α))
    (h_support : (chartBilinearH1ComplDataOfLaplacianDomain g α u.property).fChart
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ chartImagePOUTsupport (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ))) :
    ∀ j, j ≤ r → ∀ dirs : Fin j → Fin (Module.finrank ℝ E),
      ∃ D : IteratedDiffChartBilinearData g α (u : H1Compl g) j,
        D.directions = dirs ∧ D.diffChartForcing =
          iteratedChartForcing g α (u : H1Compl g)
            (chartBilinearH1ComplDataOfLaplacianDomain g α u.property).fChart j dirs := by
  classical
  have hforcing := iteratedChartForcing_memWkp_and_support g α (u : H1Compl g)
    (chartBilinearH1ComplDataOfLaplacianDomain g α u.property).fChart r
    h_initial h_support (hu α)
  intro j
  induction j with
  | zero =>
    intro _ dirs
    let htwo := (laplacianDomain_memWkpChart_two (I := I) (M := M) g u.property).1
    refine ⟨IteratedDiffChartBilinearData.ofBase_of_chartH2 g α u.property htwo, ?_, ?_⟩
    · exact Subsingleton.elim _ _
    · rfl
  | succ j ih =>
    intro hj dirs
    obtain ⟨D, hdirs, hF⟩ := ih (by omega) (Fin.init dirs)
    have hprev := hforcing j (by omega) (Fin.init dirs)
    have hW1 : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 D.diffChartForcing
        (chartTargetEuclid (I := I) (M := M) α) := by
      rw [hF]
      exact (hprev.1.le_of_le (k := 1) (by omega)).memW1p
    have hzero : D.diffChartForcing =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ chartImagePOUTsupport (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)) := by
      rw [hF]
      exact hprev.2
    let Dnext := IteratedDiffChartBilinearData.successor g α j D (dirs (Fin.last j))
      ((hu α).le_of_le (by omega)) ((hu α).le_of_le (by omega)) hW1 hzero
    refine ⟨Dnext, ?_, ?_⟩
    · change Fin.snoc D.directions (dirs (Fin.last j)) = dirs
      rw [hdirs, Fin.snoc_init_self]
    · change successorChartForcing g α (u : H1Compl g) j D.directions D.diffChartForcing
        (dirs (Fin.last j)) = _
      rw [hdirs, hF]
      rfl

end CalabiYau.PoissonDomainRegularity
