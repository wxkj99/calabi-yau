module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.BochnerTensors
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.BochnerIdentity.PairDifferentiation
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.BochnerIdentity.RicciCommutator

@[expose] public section

open scoped Manifold ContDiff BigOperators

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

omit [T2Space M] [CompactSpace M] in
private theorem c3Bochner_of_ordered_pair_and_commutator (ω₀ : KahlerForm n M) {φ : M → ℝ}
    (hφ : ω₀.IsPotential φ) (x : M)
    (hWeighted :
      (ω₀.perturb φ hφ).laplacian (calabiEnergy ω₀ φ) x =
        c3BochnerDerivativeSquares ω₀ φ x +
          (c3Pair (c3PerturbedMetricInChart ω₀ φ x)
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x)
            (c3OppositeConnectionTensorLaplacian ω₀ φ x
              (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x))
            (connectionDifferenceInChart ω₀ φ x
              (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x))).re +
          (c3Pair (c3PerturbedMetricInChart ω₀ φ x)
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x)
            (c3ConnectionTensorLaplacian ω₀ φ x
              (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x))
            (connectionDifferenceInChart ω₀ φ x
              (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x))).re)
    (hComm :
      c3OppositeConnectionTensorLaplacian ω₀ φ x
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) =
        fun i j k ↦
          c3ConnectionTensorLaplacian ω₀ φ x
              (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) i j k +
            c3RicciTensorAction (c3PerturbedMetricInChart ω₀ φ x)
              (connectionDifferenceInChart ω₀ φ x
                (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x))
              (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) i j k) :
    (ω₀.perturb φ hφ).laplacian (calabiEnergy ω₀ φ) x =
      c3BochnerDerivativeSquares ω₀ φ x +
        2 * c3BochnerConnectionTerm ω₀ φ x +
        c3BochnerRicciActionTerm ω₀ φ x := by
  rw [hWeighted, hComm, c3Pair_add_left]
  simp only [Complex.add_re]
  simp [c3BochnerConnectionTerm, c3BochnerRicciActionTerm]
  ring

theorem calabiEnergy_laplacian_eq_bochner (ω₀ : KahlerForm n M)
    {φ : M → ℝ} (hφ : ω₀.IsPotential φ) (x : M) :
    (ω₀.perturb φ hφ).laplacian (calabiEnergy ω₀ φ) x =
      c3BochnerDerivativeSquares ω₀ φ x + 2 * c3BochnerConnectionTerm ω₀ φ x +
        c3BochnerRicciActionTerm ω₀ φ x := by
  exact c3Bochner_of_ordered_pair_and_commutator ω₀ hφ x
    (calabiEnergy_laplacian_eq_ordered_pair ω₀ hφ x)
    (c3ConnectionTensorLaplacian_commutator ω₀ hφ x)

end KahlerForm
