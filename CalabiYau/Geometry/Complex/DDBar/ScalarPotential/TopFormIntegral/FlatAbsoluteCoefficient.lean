module

public import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.TopFormIntegral.Basic
public import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.TraceWedge.CoordinateBasis

import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.TraceWedge.ExteriorPair
import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.TraceWedge.DiagonalCounting
import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.TopFormIntegral.FlatLastPairCoefficient

/-!
# Absolute coefficient of the flat Kähler power

Wells, *Differential Analysis on Complex Manifolds*, third edition (2008),
V §1, equations (1.5) and (1.9)–(1.12), pp. 157–158, uses
`Ω = (i/2) ∑ dzⱼ ∧ dbarzⱼ = ∑ dxⱼ ∧ dyⱼ` and proves
`Ωⁿ = n! dx₁ ∧ dy₁ ∧ ⋯ ∧ dxₙ ∧ dyₙ`.

The project's `omegaFlat` is twice this coordinate expression:
`eta j = 2 dxⱼ ∧ dyⱼ` and `omegaFlat = ∑ j, eta j`.
Thus its raw top power has coefficient `n! * 2^n`, not `n!`.
The wedge is the ordinary exterior product, and `wedgePow` does not
include division by a factorial. `topFormCoeff` uses the interleaved
positive frame `(e₀, Ie₀, …, eₙ₋₁, Ieₙ₋₁)`.

In dimension zero the wedge power is the scalar unit, so its coefficient
is one even though the flat two-form is the empty sum. In dimensions
one and two the raw coefficients are respectively `+2` and `+8`.
No determinant, relative-trace, nonvanishing or geometric hypothesis
is imposed on this fixed standard-coordinate evaluation.
-/

public section

namespace ContinuousAlternatingMap

/-- The unnormalized flat top power has absolute coefficient `n! * 2^n`
in the positive interleaved real frame, including the degree-zero unit. -/
theorem omegaFlat_topFormCoeff (n : ℕ) :
    topFormCoeff (wedgePow (omegaFlat (n := n)) n) =
      (n.factorial : ℝ) * 2 ^ n := by
  have omegaFlat_topFormCoeff_succ_recurrence (k : ℕ) :
      topFormCoeff (wedgePow (omegaFlat (n := k + 1)) (k + 1)) =
        ((k + 1 : ℕ) : ℝ) * 2 *
          topFormCoeff (wedgePow (omegaFlat (n := k)) k) := by
    by_cases hk : k = 0
    · subst k
      have hpow : wedgePow (omegaFlat (n := 1)) 1 = flatLastPairTop 0 := by
        have hflat : omegaFlat (n := 1) = eta (Fin.last 0) := by
          simp [omegaFlat]
        conv_lhs => rw [hflat]
        rfl
      calc
        topFormCoeff (wedgePow (omegaFlat (n := 1)) 1) =
            topFormCoeff (flatLastPairTop 0) := congrArg topFormCoeff hpow
        _ = 2 * topFormCoeff (wedgePow (omegaFlat (n := 0)) 0) := by
          rw [topFormCoeff_flatLastPairTop]
        _ = ((0 + 1 : ℕ) : ℝ) * 2 *
            topFormCoeff (wedgePow (omegaFlat (n := 0)) 0) := by
          norm_num
    · have hkpos : 0 < k := by omega
      let d : Fin (k + 1) → ℝ := fun i => if i = Fin.last k then 1 else 0
      have halphaD : (eta (Fin.last k)).coeffMatrix =
          Matrix.diagonal (fun i : Fin (k + 1) => (d i : ℂ)) := by
        rw [eta_coeffMatrix]
        congr 1
        funext i
        by_cases hi : i = Fin.last k <;> simp [d, hi]
      have hcount := diagonal_trace_wedge_counting
        (n := k + 1) (by omega) (fun j => eta_wedge_self_zero j)
        (fun i j => eta_wedge_comm i j)
        (omegaFlat (n := k + 1)) (eta (Fin.last k))
        omegaFlat_isOneOne (eta_isOneOne (Fin.last k))
        omegaFlat_coeffMatrix d halphaD
      have htrace : (omegaFlat (n := k + 1)).relTrace (eta (Fin.last k)) = 1 := by
        rw [relTrace, omegaFlat_coeffMatrix, eta_coeffMatrix]
        simp [Matrix.trace_diagonal, Finset.sum_ite_eq', Finset.mem_univ]
      have hcount' :
          wedgePow (omegaFlat (n := k + 1)) (k + 1) =
            ((k + 1 : ℕ) : ℝ) • flatLastPairTop k := by
        calc
          wedgePow (omegaFlat (n := k + 1)) (k + 1) =
              1 • wedgePow (omegaFlat (n := k + 1)) (k + 1) := by simp
          _ = ((omegaFlat (n := k + 1)).relTrace (eta (Fin.last k))) •
                wedgePow (omegaFlat (n := k + 1)) (k + 1) :=
            (congrArg (fun c : ℝ => c • wedgePow (omegaFlat (n := k + 1)) (k + 1))
              htrace).symm
          _ = ((k + 1 : ℕ) : ℝ) •
                mixedWedgeOfPos (by omega) (eta (Fin.last k))
                  (omegaFlat (n := k + 1)) := hcount
          _ = ((k + 1 : ℕ) : ℝ) • flatLastPairTop k :=
            congrArg (fun β => ((k + 1 : ℕ) : ℝ) • β)
              (omegaFlat_mixedWedge_lastPair k)
      have hcoeff := congrArg topFormCoeff hcount'
      have hcoeff' :
          topFormCoeff (wedgePow (omegaFlat (n := k + 1)) (k + 1)) =
            ((k + 1 : ℕ) : ℝ) * topFormCoeff (flatLastPairTop k) := by
        change topFormCoeff (wedgePow (omegaFlat (n := k + 1)) (k + 1)) =
          ((k + 1 : ℕ) : ℝ) * topFormCoeff (flatLastPairTop k) at hcoeff
        exact hcoeff
      rw [topFormCoeff_flatLastPairTop] at hcoeff'
      calc
        topFormCoeff (wedgePow (omegaFlat (n := k + 1)) (k + 1)) =
            ((k + 1 : ℕ) : ℝ) * (2 *
              topFormCoeff (wedgePow (omegaFlat (n := k)) k)) := hcoeff'
        _ = _ := by ring
  induction n with
  | zero =>
      simp [topFormCoeff, wedgePow]
  | succ n ih =>
      rw [omegaFlat_topFormCoeff_succ_recurrence n, ih, Nat.factorial_succ]
      push_cast
      ring

end ContinuousAlternatingMap
