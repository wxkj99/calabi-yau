module

public import CalabiYau.MongeAmpere.Continuity.Openness.HolderSpaces
public import CalabiYau.MongeAmpere.Continuity.Openness.C2Approximation
public import CalabiYau.MongeAmpere.Continuity.Openness.C2MassNormalization.DensityConvergence
public import CalabiYau.MongeAmpere.Continuity.Openness.C2MassNormalization.IntegralLimit

/-!
# Monge–Ampère mass for `C²` potentials

The volume of a Kähler form in the class of `ω₀` is unchanged by a `C²` potential.  This finite
regularity version is needed before the Schauder bootstrap: the IFT branch is only `C²`, so the
normalization step cannot appeal to the existing smooth-potential integral theorem.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology
open Set MeasureTheory Filter

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M]

omit [ConnectedSpace M] in
/-- The Monge–Ampère density of a positive `C²` potential has the same total mass as the
background Kähler form, given an explicit smooth positive approximation in chartwise `C²`. -/
theorem integral_mongeAmpere_of_isC2Potential (ω₀ : KahlerForm n M) {φ : M → ℝ}
    (hφ : ω₀.IsC2Potential φ)
    (A : SmoothC2PotentialApproximationData ω₀ φ hφ) :
    ∫ x, ω₀.mongeAmpere φ x ∂ω₀.volume = ω₀.volume.real univ := by
  have hdensity := A.uniform_mongeAmpere_converges ω₀ hφ
  have hintegrable : ∀ j, Integrable (ω₀.mongeAmpere (A.approx j)) ω₀.volume := by
    intro j
    have hcont : Continuous (ω₀.mongeAmpere (A.approx j)) :=
      (ω₀.contMDiff_mongeAmpere (A.smooth j)).continuous
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hlimit := integral_tendsto_of_uniform_convergence ω₀.volume
    (fun j x => ω₀.mongeAmpere (A.approx j) x) (ω₀.mongeAmpere φ)
    hintegrable (hdensity.1.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) hdensity.2
  have hmass (j : ℕ) :
      ∫ x, ω₀.mongeAmpere (A.approx j) x ∂ω₀.volume = ω₀.volume.real univ :=
    integral_mongeAmpere (A.potential j)
  have hlimit_const :
      Tendsto (fun _ : ℕ => ω₀.volume.real univ) atTop
        (nhds (∫ x, ω₀.mongeAmpere φ x ∂ω₀.volume)) := by
    exact hlimit.congr' (Filter.Eventually.of_forall hmass)
  exact tendsto_nhds_unique hlimit_const tendsto_const_nhds

end KahlerForm
