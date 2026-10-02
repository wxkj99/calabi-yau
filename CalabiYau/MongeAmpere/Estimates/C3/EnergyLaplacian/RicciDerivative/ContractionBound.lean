module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.Basic
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.ContractionBound.UniformEstimate

/-!
# Algebraic pairing bound for the differentiated Ricci remainder

Székelyhidi, §3.3, proof of Lemma 3.9, p. 45: two-sided metric comparison
and bounded reference-frame tensor components turn a linear-plus-quadratic
connection-difference error into C*(sqrt(E)+E). No MA equation or Holder
bridge is hidden here: their concrete reference-frame bounds are premises.
-/

public section

open scoped Manifold ContDiff BigOperators ComplexOrder MatrixOrder
open ContinuousAlternatingMap
open Matrix

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

omit [T2Space M] [CompactSpace M] in
/-- Finite-dimensional contraction only: fixed and forcing tensor jets have
explicit finite bounds; the actual potential provides positivity and E=|T|². -/
theorem exists_uniform_c3RicciDerivativeError_bound (ω₀ : KahlerForm n M)
    (S : Set ((M → ℝ) × (M → ℝ))) (hS : ∀ p ∈ S, ω₀.IsPotential p.2)
    (hMetric : ∃ B : ℝ, 0 < B ∧ ∀ p ∈ S, ∀ x,
      relTrace (ω₀ x) (ω₀ x + mddbar n p.2 x) ≤ B ∧
      relTrace (ω₀ x + mddbar n p.2 x) (ω₀ x) ≤ B)
    (R H : ℝ) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hRicci : ∀ x P, IsReferenceOrthonormalFrame ω₀ x P →
      ReferenceRicciFrameBound ω₀ x
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) P R)
    (hForcing : ∀ p ∈ S, ∀ x P, IsReferenceOrthonormalFrame ω₀ x P →
      ForcingFrameBound ω₀ p.1 x
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) P H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ S, ∀ x,
      |c3RicciDerivativeError ω₀ p.1 p.2 x| ≤
        C * (calabiEnergy ω₀ p.2 x + Real.sqrt (calabiEnergy ω₀ p.2 x)) := by
  exact (c3_exists_uniform_ricci_derivative_error_bound ω₀ S hS hMetric R H hR hH hRicci hForcing)

end KahlerForm
