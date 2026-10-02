module

public import CalabiYau.Geometry.Kahler.Poisson
public import CalabiYau.Analysis.Elliptic.Regularity.LaplacianDomain.L2
public import CalabiYau.Analysis.Sobolev.Manifold.Embedding.IteratedSmooth

/-!
# Global smooth representative of an L² class

The all-orders chart Sobolev embedding assembles a smooth representative.
The conclusion is equality in L², as required by the variational Poisson solver.
No equation or choice of normalization is asserted here.
-/

@[expose] public section

open scoped Manifold ContDiff
open MeasureTheory CalabiYau.Analysis.Laplacian

namespace CalabiYau

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M]
  [NeZero (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))]

omit [MeasurableSpace M] [BorelSpace M] in
/-- All finite even chart Sobolev orders give a smooth representative of the same L² class. -/
theorem poisson_exists_smoothScalar_of_all_even_orders
    (g : SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) M)
    (u : Lp ℝ 2 (RiemannianVolume.riemannianVolumeMeasure
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g))
    (h_all : ∀ k : ℕ, Sobolev.Chart.MemWkpChart
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) (2 * k) 2 (u : M → ℝ)) :
    ∃ q : SmoothScalar g,
      smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g q = u := by
  obtain ⟨v, hv, hae⟩ :=
    Sobolev.Chart.sobolev_smooth_representative_of_memWkpChart_forall
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
      (Lp.stronglyMeasurable u).measurable h_all
  refine ⟨⟨v, hv⟩, ?_⟩
  apply Lp.ext
  exact (MemLp.coeFn_toLp (SmoothScalar.memLp_two
    (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) (g := g) ⟨v, hv⟩)).trans hae

end CalabiYau
