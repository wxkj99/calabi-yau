module
public import CalabiYau.Analysis.Elliptic.Poisson.DomainSobolevGain.NumeratorProductRegularity.SupportMultiplier

@[expose] public section
noncomputable section
namespace CalabiYau.PoissonDomainRegularity.NumeratorSolutionProducts
open MeasureTheory Set Filter Topology Sobolev.Euclidean
open scoped ENNReal ContDiff
open Bundle Manifold Function
open scoped Manifold BigOperators
open Sobolev.Chart CalabiYau.RiemannianVolume CalabiYau.Analysis.Laplacian
open CalabiYau.PoissonDomainRegularity CalabiYau.PoissonDomainRegularity.NumeratorMixedRegularity CalabiYau.Laplacian.MetricExtension
open CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
local notation "Ω" => Sobolev.Chart.chartTargetEuclid (I := I) (M := M)

lemma solution_numerator_product_layers_memWkp
    (g : SmoothRiemannianMetric I M) (α : M) (u_h : H1Compl g) (m K : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E)) (l : Fin (Module.finrank ℝ E))
    (h : MemWkp (m + 2 + K) 2
      (chartPushed (chartAtlasPOU I M) α ((h1ComplToLp g u_h) : M → ℝ)) (Ω α)) :
    MemWkp K 2 (fun y => ∑ i, ∑ j,
      (fderiv ℝ (weightedInvGramDerivOnEuclid g α i j l) y)
        (EuclideanSpace.single j 1) *
      chosenMthMixedPartialChartPushedU g α u_h (m + 1) (Fin.cons i dirs) y) (Ω α) ∧
    MemWkp K 2 (fun y => ∑ i, ∑ j,
      weightedInvGramDerivOnEuclid g α i j l y *
      chosenMthMixedPartialChartPushedU g α u_h (m + 2) (Fin.cons i (Fin.snoc dirs j)) y)
      (Ω α) ∧
    MemWkp K 2 (fun y => densityDerivOnEuclid g α l y *
      chosenMthMixedPartialChartPushedU g α u_h m dirs y) (Ω α) := by
  classical
  have hA : ∀ i j, MemWkp K 2
      (fun y => (fderiv ℝ (weightedInvGramDerivOnEuclid g α i j l) y)
        (EuclideanSpace.single j 1) *
        chosenMthMixedPartialChartPushedU g α u_h (m + 1) (Fin.cons i dirs) y) (Ω α) := by
    intro i j
    have hd := weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α i j l
    have hfd := ((contDiffOn_infty_iff_fderiv_of_isOpen
      (Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α)).1 hd).2
    have heval : ContDiff ℝ (⊤ : ℕ∞)
        (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single j 1)) :=
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ))).contDiff
    exact coef_mul_selectedMixed_memWkp g α u_h (m + 1) K (Fin.cons i dirs)
      (heval.contDiffOn.comp hfd (mapsTo_univ _ _)) (h.le_of_le (by omega))
  have hB : ∀ i j, MemWkp K 2
      (fun y => weightedInvGramDerivOnEuclid g α i j l y *
        chosenMthMixedPartialChartPushedU g α u_h (m + 2) (Fin.cons i (Fin.snoc dirs j)) y)
      (Ω α) := by
    intro i j
    exact coef_mul_selectedMixed_memWkp g α u_h (m + 2) K (Fin.cons i (Fin.snoc dirs j))
      (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α i j l) h
  have hC : MemWkp K 2 (fun y => densityDerivOnEuclid g α l y *
      chosenMthMixedPartialChartPushedU g α u_h m dirs y) (Ω α) :=
    coef_mul_selectedMixed_memWkp g α u_h m K dirs
      (densityDerivOnEuclid_contDiffOn (I := I) g α l) (h.le_of_le (by omega))
  refine ⟨?_, ?_, hC⟩
  · exact memWkp_finset_sum Finset.univ (fun i _ =>
      memWkp_finset_sum Finset.univ (fun j _ => hA i j))
  · exact memWkp_finset_sum Finset.univ (fun i _ =>
      memWkp_finset_sum Finset.univ (fun j _ => hB i j))

#print axioms solution_numerator_product_layers_memWkp
end CalabiYau.PoissonDomainRegularity.NumeratorSolutionProducts
