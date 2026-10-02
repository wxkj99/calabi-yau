module

public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.ComplexSmoothBall

/-!
# Restrict the smooth Schauder estimate to an interior ball

This is the positive-dimensional ball estimate used in the finite-cover proof of
`interiorSchauderBaseRegularity`. The analytic freezing, interpolation and real-coordinate
steps are the public results following `ComplexSmoothBall`, not a private provider assumption.

The buffered outer radius is `(R + S) / 2`: its closed ball lies in the original open
ball of radius `S`. This bridge uses no boundary regularity or all-domain approximation.
- conforming interior estimate: Gilbarg–Trudinger, second edition, Theorem 6.2, §6.1;
- analytic implementation: Constantin, *Schauder Estimates*, Theorem 3, equation (9),
  pp. 7–9, as documented in the imported results.
-/

@[expose] public section

open Set Matrix
open scoped NNReal ContDiff Topology

namespace CalabiYau.Schauder

/-- Exact open-ball restriction of the public smooth complex-ball estimate. The constant
is chosen before the coefficient, solution and source/value bounds. -/
theorem smoothInteriorSchauderBallEstimate (n : ℕ) (hn : 0 < n) :
    ∀ (α : ℝ≥0), 0 < α → α < 1 →
      ∀ (lam K : ℝ≥0), 0 < lam →
        ∀ c : EuclideanSpace ℂ (Fin n), ∀ R S : ℝ, 0 < R → R < S →
          ∃ C : ℝ≥0, ∀ (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
            (u : EuclideanSpace ℂ (Fin n) → ℝ),
            (∀ j l, ContDiffOn ℝ ∞ (fun z ↦ A z j l) (Metric.ball c S)) →
            ContDiffOn ℝ ∞ u (Metric.ball c S) →
            IsUniformlyEllipticOn A lam (Metric.ball c S) →
            (∀ j l, HolderBoundOn 0 α K (Metric.ball c S) fun z ↦ A z j l) →
            ∀ K₀ K₁ : ℝ≥0,
              ContDiffOn ℝ 0 (complexEllipticOp A u) (Metric.ball c S) →
              HolderBoundOn 0 α K₁ (Metric.ball c S) (complexEllipticOp A u) →
              (∀ z ∈ Metric.ball c S, |u z| ≤ K₀) →
              HolderBoundOn 2 α (C * (K₁ + K₀))
                (Metric.closedBall c (R / 2)) u := by
  intro α hα₀ hα₁ lam K hlam c R S hR hRS
  obtain ⟨C, hC⟩ := smoothComplexBallInteriorEstimate hn
    α lam K hα₀ hα₁ hlam (R / 2) ((R + S) / 2) (by linarith) (by linarith)
  refine ⟨C, ?_⟩
  intro A u hA hu hEll hAH K₀ K₁ _hL₀ hLH hBound
  apply hC Metric.isOpen_ball ?_ hA hu hEll hAH hLH hBound
  intro z hz
  apply Metric.mem_ball.mpr
  have hz' := Metric.mem_closedBall.mp hz
  linarith

end CalabiYau.Schauder
