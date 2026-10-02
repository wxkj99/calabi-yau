module

public import CalabiYau.MongeAmpere.Continuity.Openness.C2MassNormalization
public import CalabiYau.MongeAmpere.Continuity.Openness.ResidualNormalization.LittleHolderResidual

/-!
# Monge–Ampère mass forces a centered residual constant to vanish

A zero of the centered residual makes the uncentered logarithmic residual constant.  Finite-C²
mass invariance and the normalized continuity-path mass then force the constant to be zero.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology
open Set MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- A zero of the centered residual in its positive ball satisfies the exact finite-regularity
Monge–Ampère equation along the continuity path. -/
@[deprecated "unused hypotheses `hα₀` and `hα₁`; will be removed" (since := "2026-10-02")]
theorem centeredResidual_zero_implies_path_equation (ω₀ : KahlerForm n M) (F : M → ℝ)
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F)
    (t : ℝ) (φ : M → ℝ)
    (hsol : ω₀.SolvesMongeAmpere (fun x ↦ t * F x + ω₀.pathConstant F t) φ)
    (α : ℝ≥0) (hα₀ : 0 < α) (hα₁ : α < 1)
    [P : ContinuityHolderPair (ω₀.perturb φ hsol.1) α]
    (D : CenteredPathResidualCarrierData ω₀ F hF t φ hsol α)
    (u : P.C2) (δ : ℝ) (hu : ‖u‖ < D.radius)
    (hzero : D.residual (u, δ) = 0) :
    ω₀.SolvesMongeAmpereC2
      (fun x ↦ (t + δ) * F x + ω₀.pathConstant F (t + δ))
      (φ + P.evalC2 u) := by
  have hφu : ω₀.IsC2Potential (φ + P.evalC2 u) := D.radius_potential_sum u hu
  refine ⟨hφu, ?_⟩
  intro x
  by_cases hM : Nonempty M
  · letI : Nonempty M := hM
    let q := uncenteredContinuityPathResidual ω₀ F t φ hsol (P.evalC2 u) δ
    let ω₁ := ω₀.perturb φ hsol.1
    let c : ℝ := (∫ y, q y ∂ω₁.volume) / ω₁.volume.real Set.univ
    have hq : ∀ y, q y = c := by
      intro y
      have hevalzero : P.evalC0 (D.residual (u, δ)) y = 0 := by
        rw [hzero]
        simp
      have hcenter : centeredContinuityPathResidual ω₀ F t φ hsol
          (P.evalC2 u) δ y = 0 := by
        rw [← D.eval_residual u δ hu y]
        exact hevalzero
      change q y - c = 0 at hcenter
      dsimp [c] at hcenter
      linarith
    have hratio : ∀ y, ω₀.mongeAmpere (φ + P.evalC2 u) y /
        ω₀.mongeAmpere φ y = Real.exp
          (δ * F y + (ω₀.pathConstant F (t + δ) - ω₀.pathConstant F t) + c) := by
      intro y
      have hlog : Real.log (ω₀.mongeAmpere (φ + P.evalC2 u) y /
          ω₀.mongeAmpere φ y) -
        (δ * F y + (ω₀.pathConstant F (t + δ) - ω₀.pathConstant F t)) = c := by
        exact hq y
      have hposNew : 0 < ω₀.mongeAmpere (φ + P.evalC2 u) y := by
        change 0 < ContinuousAlternatingMap.relDet (ω₀ y) (ω₀ y + mddbar n (φ + P.evalC2 u) y)
        exact ContinuousAlternatingMap.relDet_pos (ω₀.isPositive y) (hφu.2 y)
      have hpos := div_pos hposNew (ω₀.mongeAmpere_pos hsol.1 y)
      have hlog' : Real.log (ω₀.mongeAmpere (φ + P.evalC2 u) y /
          ω₀.mongeAmpere φ y) =
          δ * F y + (ω₀.pathConstant F (t + δ) - ω₀.pathConstant F t) + c := by
        linarith
      calc
        _ = Real.exp (Real.log (ω₀.mongeAmpere (φ + P.evalC2 u) y /
            ω₀.mongeAmpere φ y)) := (Real.exp_log hpos).symm
        _ = _ := by rw [hlog']
    have hpoint : ∀ y, ω₀.mongeAmpere (φ + P.evalC2 u) y =
        Real.exp c * Real.exp ((t + δ) * F y + ω₀.pathConstant F (t + δ)) := by
      intro y
      have hbase := hsol.2 y
      have hmul := hratio y
      rw [div_eq_iff (ne_of_gt (ω₀.mongeAmpere_pos hsol.1 y))] at hmul
      rw [hmul, hbase]
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      rw [add_comm t δ]
      ring
    have hmass := integral_mongeAmpere_of_isC2Potential ω₀ hφu
      (Classical.choice (exists_smoothC2Potential_approximation ω₀ hφu))
    have hpath := ω₀.integral_exp_path hF (t + δ)
    have hvol : 0 < ω₀.volume.real Set.univ := by
      have hint : Integrable (fun _ : M ↦ Real.exp (0 : ℝ)) ω₀.volume := by
        simpa using (integrable_const (1 : ℝ) :
          Integrable (fun _ : M ↦ (1 : ℝ)) ω₀.volume)
      simpa using integral_exp_pos (μ := ω₀.volume)
        (f := fun _ : M ↦ (0 : ℝ)) hint
    have hc : Real.exp c = 1 := by
      have hi : ∫ y, ω₀.mongeAmpere (φ + P.evalC2 u) y ∂ω₀.volume =
          Real.exp c * ∫ y, Real.exp ((t + δ) * F y + ω₀.pathConstant F (t + δ))
            ∂ω₀.volume := by
        calc
          _ = ∫ y, Real.exp c * Real.exp
              ((t + δ) * F y + ω₀.pathConstant F (t + δ)) ∂ω₀.volume := by
                apply integral_congr_ae
                filter_upwards [] with y
                exact hpoint y
          _ = _ := by rw [MeasureTheory.integral_const_mul]
      rw [hmass, hpath] at hi
      nlinarith [Real.exp_pos c]
    have hc0 : c = 0 := by
      have := congrArg Real.log hc
      simpa using this
    simpa [hc0] using hpoint x
  · have hempty : IsEmpty M := not_nonempty_iff.mp hM
    exact (hempty.false x).elim

end KahlerForm
