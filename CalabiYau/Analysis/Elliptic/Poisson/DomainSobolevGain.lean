module

public import CalabiYau.Analysis.Elliptic.Poisson.DomainSourceRegularity
public import CalabiYau.Analysis.Elliptic.Poisson.DomainSobolevGain.SobolevSuccessor

/-!
# One derivative of elliptic bootstrap

Gilbarg--Trudinger, Chapter 8, proof of Theorem 8.10: differentiate the weak
uniformly elliptic divergence equation, apply the interior H² argument to the
resulting derivatives, and localize on compactly contained chart neighborhoods.
The given order `k + 1` handles coefficient commutators. The source is the
resolvent preimage `(1 - ΔG)u`, so this statement requires no smooth source.
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
/-- The single differentiation step, with the source and current solution orders explicit. -/
theorem poisson_domain_memWkpChart_succ
    (g : SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) M)
    (u_h : laplacianDomain (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g)
    (k : ℕ)
    (hu : Sobolev.Chart.MemWkpChart
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) (k + 1) 2
      (h1ComplToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
        (u_h : H1Compl (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g) : M → ℝ))
    (hsource : Sobolev.Chart.MemWkpChart
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) k 2
      (laplacianDomain.preimage
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g u_h : M → ℝ)) :
    Sobolev.Chart.MemWkpChart
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) (k + 2) 2
      (h1ComplToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
        (u_h : H1Compl (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g) : M → ℝ) := by
  cases k with
  | zero =>
      simpa using (laplacianDomain_memWkpChart_two
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g u_h.property).1
  | succ k =>
      intro α
      exact CalabiYau.PoissonDomainRegularity.chartPushed_memWkp_succ_of_preimage
        g α u_h (k + 1) hu hsource

end CalabiYau
