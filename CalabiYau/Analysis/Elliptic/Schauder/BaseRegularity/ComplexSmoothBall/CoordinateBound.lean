module

public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.ComplexSmoothBall.Basic
public import CalabiYau.Analysis.Elliptic.Schauder.RealCoordinateEquiv.Ellipticity
public import CalabiYau.Analysis.Elliptic.Schauder.CoordinateHolderGauge

/-!
# Real-coordinate gauge to complex Hölder bound

Source: Gilbarg–Trudinger, §6.1, Theorem 6.2, freezing/interpolation proof;
Constantin, Schauder Estimates, pp. 6–9. The estimates follow Constantin, *Schauder Estimates*, pp. 6–9.
-/

@[expose] public section

open Set Matrix
open scoped NNReal ContDiff Topology

namespace CalabiYau.Schauder

/-- Transport the real-coordinate gauge to the complex model with the same constant.
The existing coordinate map is a real linear isometry, so multilinear jet precomposition
preserves norm and the closed balls correspond exactly. This is not invariance under an
arbitrary non-unitary coordinate change, and contains no elliptic estimate. -/
theorem holderBoundOn_two_of_realCoordinateGauge :
    ∀ {n : ℕ} {α B : ℝ≥0} {c : EuclideanSpace ℂ (Fin n)} {ρ : ℝ}
  {u : EuclideanSpace ℂ (Fin n) → ℝ},
  eContDiffHolderGaugeOn 2 α (Metric.closedBall (complexToRealCoordinateEquiv c) ρ)
    (fun y => u (complexToRealCoordinateEquiv.symm y)) ≤ B →
  HolderBoundOn 2 α B (Metric.closedBall c ρ) u := by
  intro n α B c ρ u h
  apply (holderBoundOn_coordinate_iff (e := complexToRealCoordinateEquiv)
    (Metric.closedBall c ρ) u).mpr
  rw [complexToRealCoordinateEquiv.image_closedBall]
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    exact spatialJet_norm_le h hj hx
  · exact HolderWith.restrict_iff.mp (topSpatialJet_holderWith_restrict h)

end CalabiYau.Schauder
