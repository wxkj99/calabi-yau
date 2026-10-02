module

public import CalabiYau.MongeAmpere.Operator
public import CalabiYau.Mathlib.Geometry.Manifold.Holder
import CalabiYau.Geometry.Complex.Forms.Positive

/-!
# Metric equivalence for Calabi's third-order estimate

The Monge–Ampère equation bounds the determinant ratio above and below when `G` is bounded.
The upper trace bound then bounds every relative eigenvalue away from zero, yielding an upper
bound on the reverse trace. See Székelyhidi, §3.2, Lemma 3.8, p. 43, combined with the
positive-eigenvalue inequalities in the Aubin–Yau estimate.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] in
/-- A uniform upper bound on `tr_{ω₀} ωφ` and `G` in `C³` gives a uniform upper bound on
`tr_{ωφ} ω₀`. The constant is positive also in dimension zero. -/
private theorem c3_exists_uniform_abs_G (S : Set ((M → ℝ) × (M → ℝ)))
    (hG : HolderBoundedInCharts (EuclideanSpace ℂ (Fin n)) 3 0 (Prod.fst '' S)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p ∈ S, ∀ x, |p.1 x| ≤ K := by
  classical
  by_cases hM : IsEmpty M
  · exact ⟨0, le_rfl, fun p hp x => (hM.false x).elim⟩
  · let : Nonempty M := not_isEmpty_iff.mp hM
    let I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
    let E := EuclideanSpace ℂ (Fin n)
    let : LocallyCompactSpace M := inferInstance
    let : FiniteDimensional ℝ E := FiniteDimensional.of_locallyCompact_manifold M I
    let e (x : M) := extChartAt I x
    let c (x : M) : E := e x x
    have hr (x : M) : ∃ r : ℝ, 0 < r ∧ Metric.ball (c x) r ⊆ (e x).target := by
      exact Metric.isOpen_iff.mp (isOpen_extChartAt_target (I := I) x)
        (c x) (mem_extChartAt_target (I := I) x)
    let r (x : M) : ℝ := Classical.choose (hr x)
    have hrpos (x : M) : 0 < r x := (Classical.choose_spec (hr x)).1
    have hrball (x : M) : Metric.ball (c x) (r x) ⊆ (e x).target :=
      (Classical.choose_spec (hr x)).2
    let V (x : M) : Set M := (chartAt E x).source ∩ (e x) ⁻¹' Metric.ball (c x) (r x / 2)
    have hVopen (x : M) : IsOpen (V x) := by
      exact isOpen_extChartAt_preimage (I := I) x Metric.isOpen_ball
    have hVcover : ∀ y : M, ∃ x : M, y ∈ V x := by
      intro y
      refine ⟨y, ?_⟩
      constructor
      · simp
      · change e y y ∈ Metric.ball (c y) (r y / 2)
        rw [Metric.mem_ball]
        simp [c, dist_self, hrpos]
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover V hVopen (by
      intro y hy
      obtain ⟨x, hx⟩ := hVcover y
      exact Set.mem_iUnion.2 ⟨x, hx⟩)
    let piece (x : M) : Set E := Metric.closedBall (c x) (r x / 2)
    have hpieceCompact (x : M) : IsCompact (piece x) := isCompact_closedBall _ _
    have hpieceTarget (x : M) : piece x ⊆ (e x).target := by
      intro z hz
      apply hrball x
      rw [Metric.mem_ball]
      have hz' : dist (z : E) (c x) ≤ r x / 2 := by
        simpa [piece, Metric.mem_closedBall] using hz
      have hz'' : dist (c x) z ≤ r x / 2 := by
        calc
          dist (c x) z = dist z (c x) := dist_comm _ _
          _ ≤ r x / 2 := hz'
      linarith [hrpos x]
    let B (x : M) : ℝ≥0 := Classical.choose (hG x (piece x) (hpieceCompact x) (hpieceTarget x))
    have hB (x : M) (p : (M → ℝ) × (M → ℝ)) (hp : p ∈ S)
        (z : E) (hz : z ∈ piece x) :
        HolderBoundOn 3 0 (B x) (piece x) (p.1 ∘ (e x).symm) := by
      have hp' : p.1 ∈ Prod.fst '' S := ⟨p, hp, rfl⟩
      exact Classical.choose_spec (hG x (piece x) (hpieceCompact x) (hpieceTarget x)) p.1 hp'
    let K : ℝ := ∑ x ∈ t, (B x : ℝ)
    have hK : 0 ≤ K := by
      dsimp [K]
      positivity
    refine ⟨K, hK, ?_⟩
    intro p hp y
    obtain ⟨x, hxt, hyV⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
    have hzsource : y ∈ (e x).source := by
      have hsource : (e x).source = (chartAt E x).source := extChartAt_source (I := I) x
      rw [hsource]
      exact hyV.1
    have hzball : e x y ∈ Metric.ball (c x) (r x / 2) := hyV.2
    have hzpiece : e x y ∈ piece x := Metric.ball_subset_closedBall hzball
    have hval := (hB x p hp (e x y) hzpiece).1 0 (by norm_num) (e x y) hzpiece
    have hpoint : (p.1 ∘ (e x).symm) (e x y) = p.1 y := by
      exact congrArg p.1 ((e x).left_inv hzsource)
    have hlocal : |p.1 y| ≤ (B x : ℝ) := by
      have hval' : |(p.1 ∘ (e x).symm) (e x y)| ≤ (B x : ℝ) := by simpa using hval
      rw [hpoint] at hval'
      exact hval'
    have hsum : (B x : ℝ) ≤ K := by
      dsimp [K]
      exact Finset.single_le_sum (fun i hi => (B i).coe_nonneg) hxt
    exact hlocal.trans hsum

/-- A uniform upper bound on `tr_{ω₀} ωφ` and `G` in `C³` gives a uniform upper bound on
`tr_{ωφ} ω₀`. The constant is positive also in dimension zero. -/
theorem exists_uniform_relTrace_equivalence (ω₀ : KahlerForm n M)
    (S : Set ((M → ℝ) × (M → ℝ)))
    (hS : ∀ p ∈ S, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ p.1 ∧
      ω₀.SolvesMongeAmpere p.1 p.2)
    (hG : HolderBoundedInCharts (EuclideanSpace ℂ (Fin n)) 3 0 (Prod.fst '' S))
    {Λ : ℝ} (hΛ : ∀ p ∈ S, ∀ x,
      relTrace (ω₀ x) (ω₀ x + mddbar n p.2 x) ≤ Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ S, ∀ x,
      relTrace (ω₀ x) (ω₀ x + mddbar n p.2 x) ≤ C ∧
      relTrace (ω₀ x + mddbar n p.2 x) (ω₀ x) ≤ C := by
  by_cases hM : IsEmpty M
  · refine ⟨1, by norm_num, ?_⟩
    intro p hp x
    exact (hM.false x).elim
  · by_cases hSempty : S = ∅
    · refine ⟨1, by norm_num, ?_⟩
      intro p hp x
      simp [hSempty] at hp
    · by_cases hn : n = 0
      · subst n
        refine ⟨1, by norm_num, ?_⟩
        intro p hp x
        constructor <;> simp [ContinuousAlternatingMap.relTrace, Matrix.trace]
      · let : NeZero n := ⟨hn⟩
        obtain ⟨K, hK, hGbound⟩ := c3_exists_uniform_abs_G S hG
        have hSnonempty : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hSempty
        have hΛpos : 0 < Λ := by
          obtain ⟨p, hp⟩ := hSnonempty
          obtain ⟨x⟩ := not_isEmpty_iff.mp hM
          exact (relTrace_pos (ω₀.isPositive x)
            (((hS p hp).2.1).2 x)).trans_le (hΛ p hp x)
        let C : ℝ := max Λ (Λ ^ (n - 1) * Real.exp K)
        have hC : 0 < C := by
          dsimp [C]
          exact lt_of_lt_of_le hΛpos (le_max_left _ _)
        refine ⟨C, hC, ?_⟩
        intro p hp x
        let omegaPoint : _ := ω₀ x
        let alphaPoint : _ := ω₀ x + mddbar n p.2 x
        have hω : omegaPoint.IsPositive := ω₀.isPositive x
        have hα : alphaPoint.IsPositive := by
          dsimp [alphaPoint]
          exact ((hS p hp).2.1).2 x
        have htrace : relTrace omegaPoint alphaPoint ≤ Λ := by
          simpa [omegaPoint, alphaPoint] using hΛ p hp x
        have hdet : relDet omegaPoint alphaPoint = Real.exp (p.1 x) := by
          simpa [KahlerForm.mongeAmpere, omegaPoint, alphaPoint] using (hS p hp).2.2 x
        have hG_lower : -K ≤ p.1 x := (abs_le.mp (hGbound p hp x)).1
        have hGupper_neg : -p.1 x ≤ K := by simpa using neg_le_neg hG_lower
        have hinv : (relDet omegaPoint alphaPoint)⁻¹ ≤ Real.exp K := by
          rw [hdet, ← Real.exp_neg]
          exact Real.exp_le_exp.mpr hGupper_neg
        have htrace_rev := relTrace_le_relTrace_pow_div_relDet hω hα
        have hpower : relTrace omegaPoint alphaPoint ^ (n - 1) ≤ Λ ^ (n - 1) :=
          pow_le_pow_left₀ (relTrace_nonneg hω hα.isNonneg) htrace _
        have hrev : relTrace alphaPoint omegaPoint ≤ Λ ^ (n - 1) * Real.exp K := by
          calc
            relTrace alphaPoint omegaPoint ≤ relTrace omegaPoint alphaPoint ^ (n - 1) /
                relDet omegaPoint alphaPoint := htrace_rev
            _ = relTrace omegaPoint alphaPoint ^ (n - 1) *
                (relDet omegaPoint alphaPoint)⁻¹ := by rw [div_eq_mul_inv]
            _ ≤ Λ ^ (n - 1) * Real.exp K :=
              mul_le_mul hpower hinv (inv_nonneg.mpr (relDet_pos hω hα).le)
                (pow_nonneg hΛpos.le _)
        constructor
        · dsimp [C]
          exact htrace.trans (le_max_left _ _)
        · dsimp [C]
          exact hrev.trans (le_max_right _ _)

end KahlerForm
