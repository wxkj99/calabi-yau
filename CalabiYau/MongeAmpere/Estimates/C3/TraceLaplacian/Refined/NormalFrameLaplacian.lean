module

public import CalabiYau.MongeAmpere.Estimates.C3.TraceLaplacian.Refined.NormalFrameEquation
public import CalabiYau.MongeAmpere.Estimates.C3.TraceLaplacian.Refined.NormalFrameOrderedTrace
public import CalabiYau.MongeAmpere.Estimates.C3.TraceLaplacian.Refined.NormalFrameScalarHessian

/-!
# Transport traces and complex Laplacians to a normal frame

The relative trace is a scalar, and its complex Laplacian is the contracted
mixed Hessian. Both ordered traces, the perturbed Laplacian of the relative
trace, and the reference Laplacian of the right-hand-side potential agree with
their expressions after a local holomorphic change of coordinates. This does
not assert a normal chart exists or estimate any third derivative or curvature.

Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §3.3,
Lemma 3.10, pp. 45–46; Yau (1978), §3, normal-coordinate scalar transport.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- The scalar identities required to apply the local trace inequality in a
normal chart. The mixed potential Hessian carries the complex normalization
`∂∂̄ = (Δreal)/4` in one flat complex dimension, and the ordered inverse
matrix entries are retained on both sides of the trace identities. -/
theorem c3RefinedTrace_normalFrame_trace_and_laplacian
    (ω₀ : KahlerForm n M) (G φ : M → ℝ)
    (hG : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G)
    (hsol : ω₀.SolvesMongeAmpere G φ) (x : M)
    (frame : C3RefinedTraceNormalCoordinateFrame ω₀ φ x) :
    let g := c3RefinedTracePulledReferenceMetric ω₀ x frame.coord
    let h := c3RefinedTracePulledPerturbedMetric ω₀ φ x frame.coord
    let H := c3RefinedTracePulledPotential G x frame.coord
    relTrace (ω₀ x) (ω₀ x + mddbar n φ x) =
      RCLike.re (((g frame.center)⁻¹ * h frame.center).trace) ∧
    relTrace (ω₀ x + mddbar n φ x) (ω₀ x) =
      RCLike.re (((h frame.center)⁻¹ * g frame.center).trace) ∧
    (ω₀.perturb φ hsol.1).laplacian
        (fun y ↦ relTrace (ω₀ y) (ω₀ y + mddbar n φ y)) x =
      RCLike.re (((h frame.center)⁻¹ * Matrix.of (fun p q ↦
        c3PartialZ (fun w ↦ c3RefinedTracePartialBar
          (fun v ↦ c3RefinedTraceRelativeMatrixTrace g h v) w q) frame.center p)).trace) ∧
    ω₀.laplacian G x =
      ∑ p : Fin n, RCLike.re
        (c3PartialZ (fun w ↦ c3RefinedTracePartialBar H w p) frame.center p) := by
  obtain ⟨hForward, hReverse⟩ := c3RefinedTrace_normalFrame_orderedTraces ω₀ G φ hsol x frame
  obtain ⟨hTraceLap, hPotentialLap⟩ :=
    c3RefinedTrace_normalFrame_scalarHessians ω₀ G φ hG hsol x frame
  exact ⟨hForward, hReverse, hTraceLap, hPotentialLap⟩

end KahlerForm
