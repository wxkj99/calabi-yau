module

public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.ComplexSmoothBall.RealBallEstimate
public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.ComplexSmoothBall.CoordinateData
public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.ComplexSmoothBall.CoordinateBound

/-!
# Smooth complex-ball interior Schauder estimate

Source: Gilbarg–Trudinger, §6.1, Theorem 6.2, freezing/interpolation proof;
Constantin, Schauder Estimates, pp. 6–9. The estimates follow Constantin, *Schauder Estimates*, pp. 6–9.
-/

@[expose] public section

open Set Matrix
open scoped NNReal ContDiff Topology

namespace CalabiYau.Schauder

/-- Exact proposed complex-ball helper, with all estimates independent of derivative norms. -/
theorem smoothComplexBallInteriorEstimate {n : ℕ} (hn : 0 < n)
    (α lam K : ℝ≥0) (hα₀ : 0 < α) (hα₁ : α < 1) (hlam : 0 < lam)
    (ρ R : ℝ) (hρ : 0 ≤ ρ) (hρR : ρ < R) :
    ∃ C : ℝ≥0, ∀ {U : Set (EuclideanSpace ℂ (Fin n))}
      {c : EuclideanSpace ℂ (Fin n)}
      {A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
      {u : EuclideanSpace ℂ (Fin n) → ℝ} {K₀ K₁ : ℝ≥0},
      IsOpen U → Metric.closedBall c R ⊆ U →
      (∀ i j, ContDiffOn ℝ ∞ (fun z => A z i j) U) → ContDiffOn ℝ ∞ u U →
      IsUniformlyEllipticOn A lam U →
      (∀ i j, HolderBoundOn 0 α K U (fun z => A z i j)) →
      HolderBoundOn 0 α K₁ U (complexEllipticOp A u) →
      (∀ z ∈ U, |u z| ≤ K₀) →
      HolderBoundOn 2 α (C * (K₁ + K₀)) (Metric.closedBall c ρ) u := by
  obtain ⟨C, hC⟩ := smoothRealBallInteriorEstimate hn α (lam/4) K hα₀ hα₁
    (by positivity) ρ R hρ hρR
  refine ⟨C, ?_⟩
  intro U c A u K₀ K₁ hU hRU hA hu hEll hAH hLH hBound
  have hRealU : IsOpen (complexToRealCoordinateEquiv.symm ⁻¹' U) :=
    hU.preimage complexToRealCoordinateEquiv.symm.continuous
  have hRealBall : Metric.closedBall (complexToRealCoordinateEquiv c) R ⊆
      complexToRealCoordinateEquiv.symm ⁻¹' U := by
    intro y hy
    apply hRU
    rw [Metric.mem_closedBall] at hy ⊢
    simpa only [← complexToRealCoordinateEquiv.symm.dist_map,
      complexToRealCoordinateEquiv.symm_apply_apply] using hy
  exact holderBoundOn_two_of_realCoordinateGauge (hC hRealU hRealBall
    (complex_realSmoothBallData hlam hU hA hu hEll hAH hLH hBound))

end CalabiYau.Schauder
