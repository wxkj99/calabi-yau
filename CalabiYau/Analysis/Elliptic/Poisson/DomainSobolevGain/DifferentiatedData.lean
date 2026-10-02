module

public import CalabiYau.Analysis.Elliptic.Regularity.LaplacianDomain.Chart.VariationalData
public import CalabiYau.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.ChosenFirstPartialW1p

/-!
# Differentiated chart data for finite elliptic bootstrap

Adapted from DifferentialGeometry at `7a48598d35109aa99d1cc678e2724c213cdf4ff3`:
`Iterated/NirenbergInterior/MixedPartials.lean`, lines 47–60, and
`Iterated/VariationalIdentity/DifferentiatedData.lean`, lines 57–118.

The recursion appends the differentiated direction. The `Fin.cons` appearing in
its weak-equation data instead indexes the gradient component; no commutation
of mixed weak partials is asserted by this infrastructure.
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
open CalabiYau.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.LaplacianDomainChartData
open Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

noncomputable def chosenMthMixedPartialChartPushedU
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) :
    ∀ (m : ℕ), (Fin m → Fin (Module.finrank ℝ E)) → EuclN → ℝ
  | 0, _ =>
      Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)
  | m + 1, idx =>
      Sobolev.Euclidean.chosenWeakPartialOrZero
        (d := Module.finrank ℝ E) 2 (idx (Fin.last m))
        (chosenMthMixedPartialChartPushedU g α u_h m (Fin.init idx))
        (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)

structure IteratedDiffChartBilinearData
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ) where
  directions : Fin m → Fin (Module.finrank ℝ E)
  diffChartForcing : EuclN → ℝ
  fChartEffective_memLp_weighted :
    MemLp diffChartForcing 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))
  m_diff_variational_identity :
    ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
                (m + 1) (Fin.cons i directions) y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN)) +
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
            m directions y * ψ y
        ∂(volume : Measure EuclN)) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y * diffChartForcing y * ψ y
        ∂(volume : Measure EuclN)

def IteratedDiffChartBilinearData.mkFromHypotheses
    {g : SmoothRiemannianMetric I M} {α : M}
    {u_h : H1Compl (I := I) (M := M) g} {m : ℕ}
    (directions : Fin m → Fin (Module.finrank ℝ E))
    (diffChartForcing : EuclN → ℝ)
    (fChartEffective_memLp_weighted :
      MemLp diffChartForcing 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)))
    (m_diff_variational_identity :
      ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
                  (m + 1) (Fin.cons i directions) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
              m directions y * ψ y
          ∂(volume : Measure EuclN)) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y * diffChartForcing y * ψ y
          ∂(volume : Measure EuclN)) :
    IteratedDiffChartBilinearData (I := I) (M := M) g α u_h m :=
  { directions := directions
    diffChartForcing := diffChartForcing
    fChartEffective_memLp_weighted := fChartEffective_memLp_weighted
    m_diff_variational_identity := m_diff_variational_identity }

namespace IteratedDiffChartBilinearData

variable {g : SmoothRiemannianMetric I M} {α : M}
  {u_h : H1Compl (I := I) (M := M) g} {m : ℕ}

end IteratedDiffChartBilinearData
end CalabiYau.PoissonDomainRegularity
