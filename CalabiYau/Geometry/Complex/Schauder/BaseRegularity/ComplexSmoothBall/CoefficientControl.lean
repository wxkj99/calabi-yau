module

public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.ComplexSmoothBall.Basic

/-!
# Local coefficient Hölder and oscillation bounds

Source: Gilbarg–Trudinger, §6.1, Theorem 6.2, freezing/interpolation proof;
Constantin, Schauder Estimates, pp. 6–9. The estimates follow Constantin, *Schauder Estimates*, pp. 6–9.
-/

@[expose] public section

open Set Matrix
open scoped NNReal ContDiff Topology

namespace CalabiYau.Schauder

private theorem holderOnWith_zero_of_holderBoundOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α C : ℝ≥0} {U : Set E} {f : E → ℝ}
    (hf : HolderBoundOn 0 α C U f) : HolderOnWith C α f U := by
  let L := continuousMultilinearCurryFin0 ℝ E ℝ
  intro x hx y hy
  have h := hf.2 x hx y hy
  rw [iteratedFDeriv_zero_eq_comp] at h
  change edist (L.symm (f x)) (L.symm (f y)) ≤ _ at h
  rw [L.symm.edist_map] at h
  exact h

/-- The exact localization contract consumed by the real-ball estimate. -/
theorem realBallCoefficientExtension_control :
    ∀ {n : ℕ} {α K : ℝ≥0}
  {U : Set (RealBallModel n)}
  {a : RealBallModel n → Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ}
  {x : RealBallModel n} {δ : ℝ},
  0 < α → 0 < δ → Metric.closedBall x δ ⊆ U →
  (∀ i j, HolderBoundOn 0 α K U (fun y => a y i j)) →
  ∀ coeff : RealBallCoefficientExtension a x δ,
    (∀ i j, HolderWith K α ((Metric.ball x δ).domRestrict
      (coeff.coefficient i j : RealBallModel n → ℝ))) ∧
    (∀ i j y, y ∈ Metric.ball x δ →
      ‖coeff.coefficient i j x - coeff.coefficient i j y‖ ≤
        (K * Real.toNNReal δ ^ (α : ℝ) : ℝ)) := by
  intro n α K U a x δ hα hδ hclosed hcoeff coeff
  constructor
  · intro i j
    have hball : Metric.ball x δ ⊆ U :=
      Metric.ball_subset_closedBall.trans hclosed
    have hlocal : HolderOnWith K α (fun y : RealBallModel n => a y i j)
        (Metric.ball x δ) :=
      (holderOnWith_zero_of_holderBoundOn (hcoeff i j)).mono hball
    have heq : ∀ y ∈ Metric.ball x δ,
        a y i j = coeff.coefficient i j y := by
      intro y hy
      exact (coeff.agrees i j y hy).symm
    have hlocal' : HolderOnWith K α
        (coeff.coefficient i j : RealBallModel n → ℝ) (Metric.ball x δ) := by
      intro y hy z hz
      rw [← heq y hy, ← heq z hz]
      exact hlocal y hy z hz
    exact HolderWith.restrict_iff.mpr hlocal'
  · intro i j y hy
    let f : RealBallModel n → ℝ := coeff.coefficient i j
    have hball : Metric.ball x δ ⊆ U :=
      Metric.ball_subset_closedBall.trans hclosed
    have hlocal : HolderOnWith K α (fun z : RealBallModel n => a z i j)
        (Metric.ball x δ) :=
      (holderOnWith_zero_of_holderBoundOn (hcoeff i j)).mono hball
    have heq : ∀ z ∈ Metric.ball x δ, a z i j = f z := by
      intro z hz
      exact (coeff.agrees i j z hz).symm
    have hlocal' : HolderOnWith K α f (Metric.ball x δ) := by
      intro z hz w hw
      rw [← heq z hz, ← heq w hw]
      exact hlocal z hz w hw
    have hwith : HolderWith K α ((Metric.ball x δ).domRestrict f) :=
      HolderWith.restrict_iff.mpr hlocal'
    have hos := norm_sub_le_holderBallOscillationConst_of_mem_ball hδ hwith hy
    simpa [f, holderBallOscillationConst] using hos

end CalabiYau.Schauder
