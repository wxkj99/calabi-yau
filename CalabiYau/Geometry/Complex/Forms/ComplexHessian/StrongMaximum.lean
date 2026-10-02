module

public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.Harmonic.Analytic
import CalabiYau.Geometry.Complex.Forms.ComplexHessian.ComplexLineHarmonic

/-!
# Strong maximum principle for pluriharmonic functions

The one-variable harmonic maximum principle is applied to complex lines through the maximum point.
The resulting local constancy statement is used in the compact connected manifold theorem for
`i∂∂̄`-closed functions.
-/

@[expose] public section

open Complex InnerProductSpace Set

variable {n : ℕ}

/-- If every sufficiently short complex-line restriction through `z` is harmonic and `f` has a
maximum at `z` on a coordinate ball, then `f` is constant on a smaller ball. -/
@[deprecated "unused hypothesis `hr`; will be removed" (since := "2026-10-02")]
theorem eqOn_ball_of_harmonicOnNhd_complexLine
    {f : EuclideanSpace ℂ (Fin n) → ℝ} {z : EuclideanSpace ℂ (Fin n)} {r : ℝ}
    (hr : 0 < r)
    (hmax : IsMaxOn f (Metric.ball z r) z)
    (hline : ∀ v : EuclideanSpace ℂ (Fin n), ‖v‖ < r / 2 →
      InnerProductSpace.HarmonicOnNhd (fun t : ℂ ↦ f (z + t • v)) (Metric.ball (0 : ℂ) 2)) :
    EqOn f (Function.const (EuclideanSpace ℂ (Fin n)) (f z)) (Metric.ball z (r / 2)) := by
  have _hr := hr
  have hsegment (v : EuclideanSpace ℂ (Fin n)) (hv : ‖v‖ < r / 2) :
      f (z + v) = f z := by
    let g : ℂ → ℝ := fun t ↦ f (z + t • v)
    have hmaps : MapsTo (fun t : ℂ ↦ z + t • v) (Metric.ball (0 : ℂ) 2)
        (Metric.ball z r) := by
      intro t ht
      have ht' : ‖t‖ < 2 := by
        simpa [Metric.mem_ball, dist_eq_norm] using ht
      have hbound : ‖t‖ * ‖v‖ < r := by
        calc
          ‖t‖ * ‖v‖ ≤ 2 * ‖v‖ :=
            mul_le_mul_of_nonneg_right (le_of_lt ht') (norm_nonneg v)
          _ < 2 * (r / 2) := mul_lt_mul_of_pos_left hv (by norm_num)
          _ = r := by ring
      rw [Metric.mem_ball, dist_eq_norm, show (z + t • v) - z = t • v by abel]
      simpa [norm_smul] using hbound
    obtain ⟨F, hF, hRe⟩ :=
      (hline v hv).exists_analyticOnNhd_ball_re_eq
    have hFdiff : DifferentiableOn ℂ F (Metric.ball (0 : ℂ) 2) := by
      intro t ht
      exact (hF t ht).differentiableAt.differentiableWithinAt
    have hexpDiff : DifferentiableOn ℂ (fun t : ℂ ↦ Complex.exp (F t))
        (Metric.ball (0 : ℂ) 2) := by
      intro t ht
      exact (differentiable_exp.differentiableAt.comp t (hF t ht).differentiableAt).differentiableWithinAt
    have hzero : (0 : ℂ) ∈ Metric.ball 0 2 := by
      exact Metric.mem_ball.mpr (by norm_num [dist_eq_norm])
    have hmaxExp : IsMaxOn (norm ∘ fun t : ℂ ↦ Complex.exp (F t))
        (Metric.ball (0 : ℂ) 2) 0 := by
      intro t ht
      have hReT := hRe ht
      have hRe0 := hRe hzero
      change (F t).re = g t at hReT
      change (F 0).re = g 0 at hRe0
      have hgt : g t ≤ g 0 := by simpa [g] using hmax (hmaps ht)
      calc
        ‖Complex.exp (F t)‖ = Real.exp ((F t).re) := by rw [Complex.norm_exp]
        _ = Real.exp (g t) := by rw [hReT]
        _ ≤ Real.exp (g 0) := Real.exp_le_exp.mpr hgt
        _ = ‖Complex.exp (F 0)‖ := by rw [Complex.norm_exp, ← hRe0]
    have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
      (convex_ball (0 : ℂ) 2).isPreconnected Metric.isOpen_ball hexpDiff hzero hmaxExp
    have hone : (1 : ℂ) ∈ Metric.ball 0 2 := by
      norm_num [Metric.mem_ball, dist_eq_norm]
    have hExpEq : Complex.exp (F 1) = Complex.exp (F 0) := by
      simpa using hconst hone
    have hReEq : (F 1).re = (F 0).re := by
      apply Real.exp_injective
      simpa only [Complex.norm_exp] using congrArg norm hExpEq
    have hReOne : (F 1).re = g 1 := by simpa [g] using hRe hone
    have hReZero : (F 0).re = g 0 := by simpa [g] using hRe hzero
    have hlineEq : g 1 = g 0 := by
      rw [← hReOne, ← hReZero]
      exact hReEq
    simpa [g] using hlineEq
  intro x hx
  have hx' : dist x z < r / 2 := by
    simpa [Metric.mem_ball] using hx
  have hv : ‖x - z‖ < r / 2 := by simpa [dist_eq_norm] using hx'
  simpa using hsegment (x - z) hv
