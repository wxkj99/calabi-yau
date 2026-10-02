module

public import CalabiYau.Geometry.Complex.Schauder.BaseRegularity.ComplexSmoothBall.Basic

/-!
# Bounded real coefficient extensions

Source: Gilbarg–Trudinger, §6.1, Theorem 6.2, freezing/interpolation proof;
Constantin, Schauder Estimates, pp. 6–9. The estimates follow Constantin, *Schauder Estimates*, pp. 6–9.
-/

@[expose] public section

open Set Matrix
open scoped NNReal ContDiff Topology

namespace CalabiYau.Schauder

/-- Extend the real coefficients to bounded continuous functions, agreeing on the patch.
The closed-ball inclusion provides a collar for the extension cutoff.
No global ellipticity or global Hölder estimate is requested: the Hessian is supported on
this patch, and the extracted freezing theorem uses support-restricted coefficient control. -/
theorem exists_realBallCoefficientExtension :
    ∀ {n : ℕ}
  {a : RealBallModel n → Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ}
  {U : Set (RealBallModel n)} {x : RealBallModel n} {δ : ℝ},
  IsOpen U → 0 < δ → Metric.closedBall x δ ⊆ U →
  (∀ i j, ContDiffOn ℝ ∞ (fun y => a y i j) U) →
  Nonempty (RealBallCoefficientExtension a x δ) := by
  intro n a U x δ hU hδ hδU ha
  let K : Set (RealBallModel n) := Metric.closedBall x δ
  have hKcomp : IsCompact K := by
    exact isCompact_closedBall x δ
  have hxK : x ∈ K := by
    simp [K, Metric.mem_closedBall, dist_self, le_of_lt hδ]
  obtain ⟨ε, hε, hεU⟩ :=
    hKcomp.exists_cthickening_subset_open hU (by simpa [K] using hδU)
  let θ : RealBallModel n → ℝ := fun y => max 0 (1 - Metric.infDist y K / ε)
  have hθcont : Continuous θ := by
    exact continuous_const.max
      (continuous_const.sub ((Metric.continuous_infDist_pt K).div_const ε))
  have hθone : ∀ y ∈ K, θ y = 1 := by
    intro y hy
    simp [θ, Metric.infDist_zero_of_mem hy]
  have hθsupport : tsupport θ ⊆ Metric.cthickening ε K := by
    apply closure_minimal
    · intro y hy
      by_contra hyct
      have hyDist : ε ≤ Metric.infDist y K := by
        by_contra hnot
        apply hyct
        have hlt : Metric.infDist y K < ε := lt_of_not_ge hnot
        rw [Metric.mem_cthickening_iff]
        exact (ENNReal.le_ofReal_iff_toReal_le
          (Metric.infEDist_ne_top ⟨x, hxK⟩) hε.le).2 hlt.le
      have hratio : 1 - Metric.infDist y K / ε ≤ 0 := by
        rw [sub_nonpos]
        exact (one_le_div hε).2 hyDist
      have hzero : θ y = 0 := by
        simp [θ, max_eq_left hratio]
      exact hy (by simpa [Function.mem_support] using hzero)
    · exact Metric.isClosed_cthickening
  have hKεcomp : IsCompact (Metric.cthickening ε K) := by
    exact hKcomp.cthickening
  let f : (Fin n × Fin 2) → (Fin n × Fin 2) → RealBallModel n → ℝ :=
    fun i j y => θ y * a y i j
  have hfsupport (i j : Fin n × Fin 2) :
      tsupport (f i j) ⊆ Metric.cthickening ε K := by
    apply closure_minimal
    · intro y hy
      have hθy : θ y ≠ 0 := by
        intro hz
        exact hy (by simp [f, hz])
      have hyθ : y ∈ Function.support θ := by
        simpa [Function.mem_support] using hθy
      exact hθsupport (subset_tsupport θ hyθ)
    · exact Metric.isClosed_cthickening
  have hfcontOn (i j : Fin n × Fin 2) : ContinuousOn (f i j) U := by
    exact hθcont.continuousOn.mul (ha i j).continuousOn
  have hfcont (i j : Fin n × Fin 2) : Continuous (f i j) := by
    apply (hfcontOn i j).continuous_of_tsupport_subset hU
    exact (hfsupport i j).trans hεU
  have hfcs (i j : Fin n × Fin 2) : HasCompactSupport (f i j) :=
    HasCompactSupport.of_support_subset_isCompact hKεcomp
      (fun y hy => hfsupport i j (subset_tsupport (f i j) hy))
  let c : (Fin n × Fin 2) → (Fin n × Fin 2) →
      BoundedContinuousFunction (RealBallModel n) ℝ :=
    fun i j => BoundedContinuousFunction.ofNormedAddCommGroup (f i j) (hfcont i j)
      (Classical.choose ((hfcont i j).bounded_above_of_compact_support (hfcs i j)))
      (Classical.choose_spec ((hfcont i j).bounded_above_of_compact_support (hfcs i j)))
  refine ⟨⟨c, ?_⟩⟩
  intro i j y hy
  have hyK : y ∈ K := by
    exact (Metric.mem_ball.mp hy).le
  have hθy : θ y = 1 := hθone y hyK
  change f i j y = a y i j
  simp [f, hθy]

end CalabiYau.Schauder
