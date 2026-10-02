module

public import CalabiYau.Analysis.Elliptic.Poisson.DomainSobolevGain.DifferentiatedData
public import CalabiYau.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev

/-!
# Sobolev regularity of chosen mixed chart partials

Adapted from DifferentialGeometry at `7a48598d35109aa99d1cc678e2724c213cdf4ff3`,
`Analysis/Elliptic/Regularity/Iterated/NirenbergInterior/MixedPartials.lean`,
lines 144–258. Each chosen weak derivative loses one Sobolev order. This uses
only the last-index recursion; it asserts no commutation of chosen representatives.
-/

@[expose] public section
noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace CalabiYau.PoissonDomainRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume CalabiYau.Analysis.Laplacian Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem chosenMthMixedPartialChartPushedU_memWkp_of_chartPushed_memWkp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ) :
    ∀ (k : ℕ),
      Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) (k + m) 2
        (Sobolev.Chart.chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α) →
      ∀ (idx : Fin m → Fin (Module.finrank ℝ E)),
        Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) k 2
          (chosenMthMixedPartialChartPushedU g α u_h m idx)
          (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α) := by
  induction m with
  | zero =>
      intro k h_parent _idx
      simpa [chosenMthMixedPartialChartPushedU] using h_parent
  | succ m ih =>
      intro k h_parent idx
      have h_parent' : Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E)
          ((k + 1) + m) 2
          (Sobolev.Chart.chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
            ((h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
          (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α) := by
        simpa only [Nat.add_assoc, Nat.add_comm 1 m] using h_parent
      exact (ih (k + 1) h_parent' (Fin.init idx)).chosenWeakPartial_mem
        (idx (Fin.last m))

theorem chosenMthMixedPartialChartPushedU_memLp_two
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ)
    (h_parent : Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) m 2
      (Sobolev.Chart.chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α))
    (idx : Fin m → Fin (Module.finrank ℝ E)) :
    MemLp (chosenMthMixedPartialChartPushedU g α u_h m idx) 2
      ((volume : Measure EuclN).restrict
        (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)) := by
  exact chosenMthMixedPartialChartPushedU_memWkp_of_chartPushed_memWkp
    g α u_h m 0 (by simpa only [Nat.zero_add] using h_parent) idx

theorem chosenMthMixedPartialChartPushedU_memW1p_two
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ)
    (h_parent : Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) (m + 1) 2
      (Sobolev.Chart.chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α))
    (idx : Fin m → Fin (Module.finrank ℝ E)) :
    Sobolev.Euclidean.MemW1p (d := Module.finrank ℝ E) 2
      (chosenMthMixedPartialChartPushedU g α u_h m idx)
      (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α) := by
  apply Sobolev.Euclidean.MemWkp.one_iff_memW1p.mp
  exact chosenMthMixedPartialChartPushedU_memWkp_of_chartPushed_memWkp
    g α u_h m 1 (by simpa only [Nat.add_comm 1 m] using h_parent) idx

end CalabiYau.PoissonDomainRegularity
