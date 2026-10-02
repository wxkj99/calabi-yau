module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.BochnerTensors
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciActionBound.UniformEndomorphismBound
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciActionBound.TensorContraction

/-!
# Uniform Ricci commutator contraction for a general Monge–Ampère family

Székelyhidi, §3.3, proof of Lemma 3.9, printed p. 45, the Ricci commutator
and (3.15). Instead of the Einstein specialization (3.11), use
`Ric(ωφ) = Ric(ω₀) - i∂∂̄G`. The fixed reference Ricci tensor and uniform
second derivatives of `G`, together with two-sided metric comparison,
control this quadratic action on the connection-difference tensor.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

open scoped ComplexOrder MatrixOrder

omit [T2Space M] in
/-- Only the quadratic Ricci action is estimated; this is not a bound on
all of `Δ E`. The forcing family is general, not restricted to Einstein metrics. -/
theorem exists_uniform_c3BochnerRicciAction_bound (ω₀ : KahlerForm n M)
    (S : Set ((M → ℝ) × (M → ℝ)))
    (hS : ∀ p ∈ S, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ p.1 ∧
      ω₀.SolvesMongeAmpere p.1 p.2)
    (hG : HolderBoundedInCharts (EuclideanSpace ℂ (Fin n)) 3 0 (Prod.fst '' S))
    (hMetric : ∃ B : ℝ, 0 < B ∧ ∀ p ∈ S, ∀ x,
      relTrace (ω₀ x) (ω₀ x + mddbar n p.2 x) ≤ B ∧
      relTrace (ω₀ x + mddbar n p.2 x) (ω₀ x) ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ S, ∀ x,
      |c3BochnerRicciActionTerm ω₀ p.2 x| ≤ C * calabiEnergy ω₀ p.2 x := by
  classical
  let : PartialOrder ℂ := Complex.partialOrder
  obtain ⟨R, hR, hframe⟩ :=
    exists_uniform_c3RicciEndomorphism_frame_bound ω₀ S hS hG hMetric
  refine ⟨3 * (n : ℝ) * R, mul_nonneg (mul_nonneg (by norm_num)
    (Nat.cast_nonneg n)) hR, ?_⟩
  intro p hp x
  let z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x
  let g := c3PerturbedMetricInChart ω₀ p.2 x
  let T := connectionDifferenceInChart ω₀ p.2 x z
  obtain ⟨P, hP, hA⟩ := hframe p hp x
  have hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target :=
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).map_source
      (mem_extChartAt_source x)
  have hg : (g z).PosDef := by
    have hpos := (ω₀.perturb p.2 (hS p hp).2.1).posDef_metricInChart x hz
    rw [ω₀.metricInChart_perturb (hS p hp).2.1 x hz] at hpos
    exact hpos
  have hbound := c3RicciTensorAction_pair_bound_of_unitary_frame g z T P R
    hP hR hA
  simpa only [c3BochnerRicciActionTerm, calabiEnergy, calabiEnergyInChart,
    c3Pair, c3PerturbedMetricInChart, RCLike.re_eq_complex_re, z, g, T] using hbound

end KahlerForm
