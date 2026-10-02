module

public import CalabiYau.MongeAmpere.Estimates.C3.TraceLaplacian.Refined.NormalFrameRelativeTraceHessian
public import CalabiYau.MongeAmpere.Estimates.C3.TraceLaplacian.Refined.NormalFramePotentialHessian

/-!
# Both complex scalar Laplacians under a normal-frame change

The relative trace and the Monge–Ampère right-hand side are scalars. Their
complex mixed Hessians transform with the first holomorphic and conjugate
first antiholomorphic Jacobian slots; contraction against the corresponding
inverse metric cancels both Jacobians. These identities turn intrinsic
Laplacians into precisely the two scalar terms of the normal trace identity.

Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §3.3,
Lemma 3.10, pp. 45–46; Yau (1978), §3.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- Transport the perturbed Laplacian of the relative trace and the reference
Laplacian of `G` along the *same* local holomorphic normal frame. The latter
uses `G : M → ℝ` explicitly smooth; a `1/2` appears in each Wirtinger
operator, so neither identity includes an extra real-Laplacian factor. -/
theorem c3RefinedTrace_normalFrame_scalarHessians
    (ω₀ : KahlerForm n M) (G φ : M → ℝ)
    (hG : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G)
    (hsol : ω₀.SolvesMongeAmpere G φ) (x : M)
    (frame : C3RefinedTraceNormalCoordinateFrame ω₀ φ x) :
    let g := c3RefinedTracePulledReferenceMetric ω₀ x frame.coord
    let h := c3RefinedTracePulledPerturbedMetric ω₀ φ x frame.coord
    let H := c3RefinedTracePulledPotential G x frame.coord
    (ω₀.perturb φ hsol.1).laplacian
        (fun y ↦ relTrace (ω₀ y) (ω₀ y + mddbar n φ y)) x =
      RCLike.re (((h frame.center)⁻¹ * Matrix.of (fun p q ↦
        c3PartialZ (fun w ↦ c3RefinedTracePartialBar
          (fun v ↦ c3RefinedTraceRelativeMatrixTrace g h v) w q) frame.center p)).trace) ∧
    ω₀.laplacian G x =
      ∑ p : Fin n, RCLike.re
        (c3PartialZ (fun w ↦ c3RefinedTracePartialBar H w p) frame.center p) := by
  exact ⟨c3RefinedTrace_normalFrame_relativeTraceHessian ω₀ G φ hsol x frame,
    c3RefinedTrace_normalFrame_potentialHessian ω₀ G φ hG hsol x frame⟩

end KahlerForm
