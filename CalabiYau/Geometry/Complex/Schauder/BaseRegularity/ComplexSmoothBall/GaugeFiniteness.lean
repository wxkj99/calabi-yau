module

public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.ComplexSmoothBall.Basic

/-!
# Finiteness of the smooth closed-ball gauge

Source: Gilbarg–Trudinger, §6.1, Theorem 6.2, freezing/interpolation proof;
Constantin, Schauder Estimates, pp. 6–9. The estimates follow Constantin, *Schauder Estimates*, pp. 6–9.
-/

@[expose] public section

open Set Matrix
open scoped NNReal ContDiff Topology

namespace CalabiYau.Schauder

/-- Compactness bounds every jet, while smoothness on the open neighborhood makes the second
jet locally Lipschitz. Thus its Hölder seminorm is finite on the outer closed ball.
This result precedes every conversion of a gauge to `NNReal` in the consumer; without it,
`ENNReal.toNNReal` could silently turn an infinite gauge into zero.
Dimension zero and an empty closed ball are included. -/
theorem smooth_realBallGauge_ne_top :
    ∀ {n : ℕ} {α : ℝ≥0} {U : Set (RealBallModel n)}
  {c : RealBallModel n} {R : ℝ} {u : RealBallModel n → ℝ},
  α < 1 → IsOpen U → Metric.closedBall c R ⊆ U → ContDiffOn ℝ ∞ u U →
  eContDiffHolderGaugeOn 2 α (Metric.closedBall c R) u ≠ ⊤ := by
  intro n α U c R u hα hU hball hu
  let S : Set (RealBallModel n) := Metric.closedBall c R
  have hcompact : IsCompact S := by
    dsimp [S]
    exact isCompact_closedBall c R
  have hconvex : Convex ℝ S := by
    dsimp [S]
    exact convex_closedBall c R
  have hjet2 : ContDiffOn ℝ 1 (iteratedFDeriv ℝ 2 u) S := by
    intro x hx
    have hxU : x ∈ U := hball hx
    have hux : ContDiffAt ℝ ∞ u x := (hu x hxU).contDiffAt (hU.mem_nhds hxU)
    have hj : ContDiffAt ℝ 1 (iteratedFDeriv ℝ 2 u) x := by
      have hi : (1 + 2 : ℕ∞ω) ≤ ∞ := by
        change (↑(↑(1 + 2 : ℕ) : ℕ∞) : ℕ∞ω) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω)
        exact WithTop.coe_le_coe.mpr le_top
      exact hux.iteratedFDeriv_right hi
    exact hj.contDiffWithinAt
  obtain ⟨L, hL⟩ := hjet2.exists_lipschitzOnWith (by norm_num)
    hconvex hcompact
  have hjet2cont : ContinuousOn (iteratedFDeriv ℝ 2 u) S := hjet2.continuousOn
  obtain ⟨B, hB⟩ := hcompact.exists_bound_of_continuousOn hjet2cont
  let Bnn : ℝ≥0 := ⟨max B 0, le_max_right B 0⟩
  have hBnn : ∀ x ∈ S, ‖iteratedFDeriv ℝ 2 u x‖ ≤ Bnn := by
    intro x hx
    have h := hB x hx
    exact_mod_cast h.trans (le_max_left B 0)
  have hholder := holderWith_restrict_of_norm_le_of_lipschitzOnWith
      (s := S) (f := iteratedFDeriv ℝ 2 u) (M := Bnn) (L := L)
      (epsilon := 1) (alpha := α) (by norm_num) (by exact_mod_cast (le_of_lt hα))
      hBnn hL
  have hholderfinite : eHolderSeminormOn α S (iteratedFDeriv ℝ 2 u) ≠ ⊤ := by
    have hh := hholder.eHolderNorm_le
    unfold eHolderSeminormOn
    exact ne_top_of_le_ne_top ENNReal.coe_ne_top hh
  have hsupfinite : ∀ j ∈ Finset.range 3,
      eSupNormOn S (iteratedFDeriv ℝ j u) ≠ ⊤ := by
    intro j hj
    have hjcont : ContinuousOn (iteratedFDeriv ℝ j u) S := by
      intro x hx
      have hxU : x ∈ U := hball hx
      have hux : ContDiffAt ℝ ∞ u x := (hu x hxU).contDiffAt (hU.mem_nhds hxU)
      exact (hux.continuousAt_iteratedFDeriv
        (by exact_mod_cast (le_top : (j : ℕ∞) ≤ (⊤ : ℕ∞)))).continuousWithinAt
    obtain ⟨Bj, hBj⟩ := hcompact.exists_bound_of_continuousOn hjcont
    let Bjn : ℝ≥0 := ⟨max Bj 0, le_max_right Bj 0⟩
    have hBjn : ∀ x ∈ S, ‖iteratedFDeriv ℝ j u x‖ ≤ Bjn := by
      intro x hx
      have h := hBj x hx
      exact_mod_cast h.trans (le_max_left Bj 0)
    have hle : eSupNormOn S (iteratedFDeriv ℝ j u) ≤ Bjn := by
      rw [eSupNormOn_le]
      intro x hx
      rw [ENNReal.ofReal_le_coe]
      exact hBjn x hx
    exact ne_top_of_le_ne_top ENNReal.coe_ne_top hle
  change eContDiffHolderGaugeOn 2 α S u ≠ ⊤
  unfold eContDiffHolderGaugeOn
  have hsum : (∑ j ∈ Finset.range (2 + 1),
      eSupNormOn S (iteratedFDeriv ℝ j u)) ≠ ⊤ := by
    apply ENNReal.sum_ne_top.mpr
    intro j hj
    have hj' : j ∈ Finset.range 3 := by simpa using hj
    exact hsupfinite j hj'
  exact ENNReal.add_ne_top.mpr ⟨hsum, hholderfinite⟩

end CalabiYau.Schauder
