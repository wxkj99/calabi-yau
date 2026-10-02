module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.BochnerIdentity.OrderedJets
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.BochnerIdentity.PairLocalization
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.BochnerIdentity.MetricPairLeibniz
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.BochnerIdentity.PairHessian

/-!
# Assembly of localization and the two tensor-pairing jets

Székelyhidi, §3.3, proof of Lemma 3.9, printed pp. 44–45, (3.14).
The inverse entry is [q,p]; curvature begins with -partialZ_p(partialBar_q g).
The pairing is linear on the left and conjugate-linear on the right.
This computation uses only the stated
No off-target smoothness is assumed.
-/

@[expose] public section

open scoped Manifold ContDiff BigOperators ComplexOrder

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

theorem calabiEnergy_laplacian_eq_ordered_pair (ω₀ : KahlerForm n M)
    {φ : M → ℝ} (hφ : ω₀.IsPotential φ) (x : M) :
    (ω₀.perturb φ hφ).laplacian (calabiEnergy ω₀ φ) x =
      c3BochnerDerivativeSquares ω₀ φ x +
        (c3Pair (c3PerturbedMetricInChart ω₀ φ x)
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x)
          (c3OppositeConnectionTensorLaplacian ω₀ φ x
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x))
          (c3ConnectionDifferenceInChart ω₀ φ x
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x))).re +
        c3BochnerConnectionTerm ω₀ φ x := by
  rw [calabiEnergy_laplacian_eq_chart_pair_hessian ω₀ hφ x]
  exact c3ChartPairHessianLaplacian_eq_ordered_pair_of_leibniz ω₀ hφ x
    (c3MetricPairLeibnizOn_perturbed ω₀ hφ x)

end KahlerForm
