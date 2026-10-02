module

public import CalabiYau.MongeAmpere.Estimates.C3.TraceLaplacian.Refined.NormalFrameLaplacian
public import CalabiYau.MongeAmpere.Estimates.C3.TraceLaplacian.Refined.NormalFrameConnectionEnergy
public import CalabiYau.MongeAmpere.Estimates.C3.TraceLaplacian.Refined.NormalFrameCurvature

/-!
# Transport energy and reference curvature to a normal frame

The difference of the holomorphic connections is tensorial, despite the
individual Christoffel symbols being coordinate dependent. Its squared norm
therefore becomes the diagonal three-inverse-eigenvalue expression in normal
coordinates. The shared K curvature chart law similarly identifies the
intrinsic signed curvature contraction with its diagonal normal-frame sum.
Neither identity asserts a uniform bound.

Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §3.3,
(3.13) and Lemma 3.10, pp. 45–46; Yau (1978), §3.
-/

@[expose] public section

open scoped BigOperators Manifold ContDiff NNReal
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- The two tensorial invariances needed to replace the normal-frame positive
term and signed curvature error by the intrinsic expressions. The curvature
coefficient remains `λⱼ / λₚ - 1`; reversing either index would be incorrect. -/
theorem c3RefinedTrace_normalFrame_energy_and_curvature
    (ω₀ : KahlerForm n M) (G φ : M → ℝ)
    (hsol : ω₀.SolvesMongeAmpere G φ) (x : M)
    (frame : C3RefinedTraceNormalCoordinateFrame ω₀ φ x) :
    let g := c3RefinedTracePulledReferenceMetric ω₀ x frame.coord
    let h := c3RefinedTracePulledPerturbedMetric ω₀ φ x frame.coord
    calabiEnergy ω₀ φ x =
      ∑ p : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        ‖wirtingerDerivInChart (fun w ↦ h w j k) frame.center p‖ ^ (2 : ℕ) /
          (frame.eigenvalue p * frame.eigenvalue j * frame.eigenvalue k) ∧
    c3RefinedTraceReferenceCurvatureSignedError ω₀ φ x =
      ∑ p : Fin n, ∑ j : Fin n,
        (frame.eigenvalue j / frame.eigenvalue p - 1) *
          RCLike.re (c3RefinedTraceReferenceCurvatureInChart g frame.center p p j j) := by
  exact ⟨c3RefinedTrace_normalFrame_connectionEnergy ω₀ G φ hsol x frame,
    c3RefinedTrace_normalFrame_referenceCurvature ω₀ φ x frame⟩

end KahlerForm
