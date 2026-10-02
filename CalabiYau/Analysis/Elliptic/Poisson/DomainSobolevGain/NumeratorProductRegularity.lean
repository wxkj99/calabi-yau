module

public import CalabiYau.Analysis.Elliptic.Poisson.DomainSobolevGain.SuccessorSource
public import CalabiYau.Analysis.Elliptic.Poisson.DomainSobolevGain.NumeratorProductRegularity.SolutionProducts
public import CalabiYau.Analysis.Elliptic.Poisson.DomainSobolevGain.NumeratorProductRegularity.PreviousProducts

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

open CalabiYau.RiemannianVolume CalabiYau.Analysis.Laplacian
open CalabiYau.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl
open Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
/-- The five exact product layers of the successor numerator have finite chart Sobolev order. -/
theorem successorChartForcingNumerator_product_layers_memWkp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m K : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (previousForcing : EuclN → ℝ) (l : Fin (Module.finrank ℝ E))
    (h_previous_memWkp : Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (K + 1) 2 previousForcing
      (chartTargetEuclid (I := I) (M := M) α))
    (h_previous_ae_zero :
      previousForcing =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)))
    (h_chart_H_u : Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 2 + K) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α)) :
    Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
              (EuclideanSpace.single j 1) *
            chosenMthMixedPartialChartPushedU (I := I) (M := M)
              g α u_h (m + 1) (Fin.cons i dirs) y)
      (chartTargetEuclid (I := I) (M := M) α) ∧
    Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α i j l y *
            chosenMthMixedPartialChartPushedU (I := I) (M := M)
              g α u_h (m + 2) (Fin.cons i (Fin.snoc dirs j)) y)
      (chartTargetEuclid (I := I) (M := M) α) ∧
    Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => densityDerivOnEuclid (I := I) g α l y *
        chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m dirs y)
      (chartTargetEuclid (I := I) (M := M) α) ∧
    Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => densityDerivOnEuclid (I := I) g α l y * previousForcing y)
      (chartTargetEuclid (I := I) (M := M) α) ∧
    Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => densityOnEuclid (I := I) g α y *
        Sobolev.Euclidean.chosenWeakPartialOrZero
          (d := Module.finrank ℝ E) 2 l previousForcing
          (chartTargetEuclid (I := I) (M := M) α) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  obtain ⟨hA, hB, hC⟩ := CalabiYau.PoissonDomainRegularity.NumeratorSolutionProducts.solution_numerator_product_layers_memWkp
    g α u_h m K dirs l h_chart_H_u
  obtain ⟨hD, hE⟩ := PreviousForcingProductsUnique.previous_forcing_products_memWkp
    g α K previousForcing l h_previous_memWkp h_previous_ae_zero
  exact ⟨hA, hB, hC, hD, hE⟩

end CalabiYau.PoissonDomainRegularity
