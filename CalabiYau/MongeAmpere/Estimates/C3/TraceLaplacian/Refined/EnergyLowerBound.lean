module

public import CalabiYau.MongeAmpere.Estimates.C3.TraceLaplacian.Refined.NormalTraceIdentity
public import CalabiYau.MongeAmpere.Estimates.C3.TraceLaplacian.Refined.DiagonalMetricBounds
public import CalabiYau.MongeAmpere.Estimates.C3.TraceLaplacian.Refined.NormalFrameEnergy

/-!
# Intrinsic energy term in the refined relative-trace inequality

The refined Aubin–Yau computation, *before bounding its two signed errors*,
provides a positive multiple of the connection-difference energy in the
Laplacian of the relative trace. The signed errors are exactly the intrinsic
reference Laplacian of `G` and the reference-curvature contraction, not an
unspecified remainder. Uniform estimates for these two expressions are separate
children; in particular, this theorem is not the parent's uniform XL bound.

Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §3.3,
Lemma 3.10, pp. 45–46; Yau (1978), §3. Both Wirtinger derivatives carry `1/2`.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- Pointwise positive-energy trace inequality with its *unbounded* signed
potential and reference-curvature terms left visible. A normal-coordinate
calculation uses `c3_normalTraceHessian_lower_of_two_traces`; chart invariance
transports its trace Hessian and Calabi energy to the intrinsic expressions.
Neither error is silently assumed bounded by a constant. -/
theorem c3RefinedTrace_relTrace_laplacian_energy_with_signed_errors
    (ω₀ : KahlerForm n M) (G φ : M → ℝ)
    (hG : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G)
    (hsol : ω₀.SolvesMongeAmpere G φ) (x : M) (B : ℝ) (hB : 0 < B)
    (hForward : relTrace (ω₀ x) (ω₀ x + mddbar n φ x) ≤ B)
    (hReverse : relTrace (ω₀ x + mddbar n φ x) (ω₀ x) ≤ B) :
    B⁻¹ * calabiEnergy ω₀ φ x + ω₀.laplacian G x +
      c3RefinedTraceReferenceCurvatureSignedError ω₀ φ x ≤
        (ω₀.perturb φ hsol.1).laplacian
          (fun y ↦ relTrace (ω₀ y) (ω₀ y + mddbar n φ y)) x := by
  classical
  obtain ⟨frame⟩ := exists_c3RefinedTrace_normalCoordinateFrame ω₀ G φ hsol x
  let g := c3RefinedTracePulledReferenceMetric ω₀ x frame.coord
  let h := c3RefinedTracePulledPerturbedMetric ω₀ φ x frame.coord
  let H := c3RefinedTracePulledPotential G x frame.coord
  obtain ⟨hg, hh, hH, hLocal, hKahler⟩ :=
    c3RefinedTrace_normalFrame_equation_and_kahler ω₀ G φ hG hsol x frame
  obtain ⟨hForwardEq, hReverseEq, hLapEq, hPotentialEq⟩ :=
    c3RefinedTrace_normalFrame_trace_and_laplacian ω₀ G φ hG hsol x frame
  obtain ⟨hEnergyEq, hCurvatureEq⟩ :=
    c3RefinedTrace_normalFrame_energy_and_curvature ω₀ G φ hsol x frame
  have hbForward : RCLike.re (((g frame.center)⁻¹ * h frame.center).trace) ≤ B :=
    hForwardEq ▸ hForward
  have hbReverse : RCLike.re (((h frame.center)⁻¹ * g frame.center).trace) ≤ B :=
    hReverseEq ▸ hReverse
  have hEigen := c3RefinedTrace_diagonal_eigenvalue_bounds_of_matrix_traces g h frame.center
    frame.eigenvalue hB frame.reference_normal frame.perturbed_diagonal
    frame.eigenvalue_pos hbForward hbReverse
  have hPositive := c3RefinedTrace_diagonalEnergy_lower_of_metric_lower frame.eigenvalue
    (fun p j k ↦ wirtingerDerivInChart (fun w ↦ h w j k) frame.center p)
    (inv_pos.mpr hB) (fun i ↦ (hEigen i).1)
  have hIdentity := c3RefinedTrace_normalTraceHessian_identity g h H frame.center
    frame.eigenvalue hg hh hH frame.reference_normal frame.reference_first
    frame.perturbed_diagonal frame.eigenvalue_pos hLocal hKahler
  have hLocalBound :
      B⁻¹ * (∑ p : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        ‖wirtingerDerivInChart (fun w ↦ h w j k) frame.center p‖ ^ (2 : ℕ) /
          (frame.eigenvalue p * frame.eigenvalue j * frame.eigenvalue k)) +
      (∑ p : Fin n, RCLike.re
        (wirtingerDerivInChart (fun w ↦ c3RefinedTracePartialBar H w p) frame.center p)) +
      (∑ p : Fin n, ∑ j : Fin n,
        (frame.eigenvalue j / frame.eigenvalue p - 1) *
          RCLike.re (c3RefinedTraceReferenceCurvatureInChart g frame.center p p j j)) ≤
      RCLike.re (((h frame.center)⁻¹ * Matrix.of (fun p q ↦
        wirtingerDerivInChart (fun w ↦ c3RefinedTracePartialBar
          (fun v ↦ c3RefinedTraceRelativeMatrixTrace g h v) w q) frame.center p)).trace) := by
    rw [hIdentity]
    linarith only [hPositive]
  rw [hEnergyEq, hPotentialEq, hCurvatureEq, hLapEq]
  exact hLocalBound

end KahlerForm
