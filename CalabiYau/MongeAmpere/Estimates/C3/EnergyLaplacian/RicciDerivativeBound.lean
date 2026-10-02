module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.BochnerTensors
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.ComponentIdentity
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.ConnectionChange
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.ForcingBound
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.ReferenceRicciBound
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.ContractionBound

/-!
# Differentiated Ricci error for a general Monge–Ampère family

Székelyhidi, §3.3, proof of Lemma 3.9, printed p. 45, the estimate of
`∇k Ricⁱⱼ` after the Bianchi calculation. For the present general equation,
differentiate `Ric(ωφ) = Ric(ω₀) - i∂∂̄G`, rather than using (3.11).
The ordinary derivative is controlled by `C³` forcing and fixed reference
Ricci derivatives. Replacing `∇₀` by `∇φ` produces a term linear in `T`.
Pairing with `T` gives `C (E + sqrt E)`, not a constant independent of `E`.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

omit [T2Space M] in
/-- Uniform control of the differentiated-Ricci contraction alone. This
retains the connection correction and requires third, not just second, derivatives of `G`. -/
theorem exists_uniform_c3BochnerRicciDerivative_bound (ω₀ : KahlerForm n M)
    (S : Set ((M → ℝ) × (M → ℝ)))
    (hS : ∀ p ∈ S, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ p.1 ∧
      ω₀.SolvesMongeAmpere p.1 p.2)
    (hG : HolderBoundedInCharts (EuclideanSpace ℂ (Fin n)) 3 0 (Prod.fst '' S))
    (hMetric : ∃ B : ℝ, 0 < B ∧ ∀ p ∈ S, ∀ x,
      relTrace (ω₀ x) (ω₀ x + mddbar n p.2 x) ≤ B ∧
      relTrace (ω₀ x + mddbar n p.2 x) (ω₀ x) ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ S, ∀ x,
      |c3BochnerRicciDerivativeTerm ω₀ p.2 x| ≤
        C * (calabiEnergy ω₀ p.2 x + Real.sqrt (calabiEnergy ω₀ p.2 x)) := by
  have hSmooth : ∀ G ∈ Prod.fst '' S,
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G := by
    rintro G ⟨p, hp, rfl⟩
    exact (hS p hp).1
  obtain ⟨H, hH, hforcing⟩ := exists_uniform_c3ForcingFrameBound ω₀ (Prod.fst '' S) hSmooth hG
  obtain ⟨K, hK, hcurv⟩ := ω₀.exists_uniform_reference_curvature_component_bound
  obtain ⟨A, hA, hderiv⟩ := ω₀.exists_uniform_c3ReferenceCurvatureCovariantDerivative_bound
  have hricci := referenceRicciFrameBound_of_curvature ω₀ K A hK hA hcurv hderiv
  obtain ⟨C, hC, hbound⟩ := exists_uniform_c3RicciDerivativeError_bound ω₀ S
    (fun p hp ↦ (hS p hp).2.1) hMetric ((n : ℝ) * (K + A)) H (by positivity) hH hricci
    (fun p hp ↦ hforcing p.1 ⟨p, hp, rfl⟩)
  refine ⟨C, hC, ?_⟩
  intro p hp x
  rw [c3BochnerRicciDerivativeTerm_eq_error ω₀ (hS p hp).1 x
    (fun z hz j l ↦ c3RicciInChart_perturb_eq_of_solvesMongeAmpere ω₀
      (hS p hp).1 (hS p hp).2 x hz j l)]
  exact hbound p hp x

end KahlerForm
