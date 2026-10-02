module

public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.SourceInterpolation.Basic
public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.SourceInterpolationProofs.ProductFormula

/-!
# Canonical cutoff-source product formula

Source: Constantin, Schauder Estimates, equation (9), p. 7, and localization
p. 8. Both cross terms remain separate; no coefficient symmetry is assumed.
-/

@[expose] public section

open Matrix
open scoped NNReal ContDiff Topology

namespace CalabiYau.Schauder

/-- The jet's canonical value identity fixes its differentiated product. -/
theorem realBallCutoffSource_formula
    {n : ℕ} {α : ℝ≥0} {x : RealBallModel n} {δ : ℝ}
    {a : RealBallModel n → Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ}
    {u : RealBallModel n → ℝ} (hδ : 0 < δ)
    (coeff : RealBallCoefficientExtension a x δ) (jet : RealBallCutoffJet α x δ u)
    (hsmooth : ContDiffOn ℝ 2 u (Metric.ball x (2 * δ))) :
    ∀ y ∈ Metric.ball x δ,
      variableMatrixLap coeff.coefficient jet.second y =
        ballCutoff x (δ / 2) δ y * realBallSource a u y +
          realBallCutoffCommutator coeff u y := by
  have hproduct :=
    SourceInterpolationProofs.realBallCutoffJet_variableMatrixLap_formula_on_ball
      hδ coeff jet (fun z hz => hsmooth.contDiffAt (Metric.isOpen_ball.mem_nhds hz))
  intro y hy
  rw [hproduct y hy]
  unfold realBallCutoffCommutator
  simp_rw [← coeff.agrees _ _ y hy]

end CalabiYau.Schauder
