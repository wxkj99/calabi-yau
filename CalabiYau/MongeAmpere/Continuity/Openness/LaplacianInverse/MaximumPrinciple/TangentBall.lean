module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Order.LocalExtr

/-!
# A ball tangent to an attained maximum set

This is the geometric step in Gilbarg–Trudinger, §3.2, proof of Theorem 3.5.
It has no differential-operator hypotheses. The closed ball remains inside the ambient open
set, and only the open ball must be in the strict sublevel set.

In dimension zero, a preconnected domain containing the maximum point is a singleton,
so the nonconstancy hypothesis is impossible rather than requiring a dimension restriction.
-/

@[expose] public section

open Set

/-- Nonconstancy below an attained maximum on an open connected domain yields an interior
ball tangent to the maximum set. The dimension-zero case needs no separate premise. -/
theorem exists_ball_tangent_to_maximum_set {n : ℕ}
    {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U)
    (hconn : IsPreconnected U) {u : EuclideanSpace ℂ (Fin n) → ℝ}
    (hu : ContinuousOn u U) {x : EuclideanSpace ℂ (Fin n)} (hx : x ∈ U)
    (hmax : ∀ y ∈ U, u y ≤ u x) (hne : ¬ ∀ y ∈ U, u y = u x) :
    ∃ (c : EuclideanSpace ℂ (Fin n)) (R : ℝ) (z : EuclideanSpace ℂ (Fin n)),
      0 < R ∧ Metric.closedBall c R ⊆ U ∧ z ∈ Metric.sphere c R ∧
      u z = u x ∧ ∀ y ∈ Metric.ball c R, u y < u x := by
  classical
  let F : Set U := {y | u y.1 = u x}
  have hxF : (⟨x, hx⟩ : U) ∈ F := rfl
  have hcont : Continuous (fun y : U => u y.1) :=
    continuousOn_iff_continuous_domRestrict.mp hu
  have hFclosed : IsClosed F := by
    exact isClosed_singleton.preimage hcont
  have hFproper : ¬ (univ : Set U) ⊆ F := by
    intro hsub
    apply hne
    intro y hy
    have hyF : (⟨y, hy⟩ : U) ∈ F := hsub (mem_univ _)
    exact hyF
  have hFnotOpen : ¬ IsOpen F := by
    intro hFopen
    have hsub : (univ : Set U) ⊆ F :=
      (Subtype.preconnectedSpace hconn).isPreconnected_univ.subset_isClopen
        ⟨hFclosed, hFopen⟩ ⟨⟨x, hx⟩, mem_univ _, hxF⟩
    exact hFproper hsub
  have hex :
      ∃ a : U, a ∈ F ∧ ∀ ρ : ℝ, 0 < ρ → ¬ Metric.ball a ρ ⊆ F := by
    by_contra h
    apply hFnotOpen
    rw [Metric.isOpen_iff]
    intro a ha
    by_contra hloc
    exact h ⟨a, ha, fun ρ hρ hsub => hloc ⟨ρ, hρ, hsub⟩⟩
  obtain ⟨a, haF, haN⟩ := hex
  obtain ⟨r, hr, hballU⟩ := Metric.isOpen_iff.mp hU a.1 a.2
  have hball_not_subset : ∀ ρ : ℝ, 0 < ρ → ¬ Metric.ball a ρ ⊆ F := haN
  have hexnot := hball_not_subset (r / 4) (by linarith)
  obtain ⟨c0, hc0ball, hc0F⟩ := Set.not_subset.mp hexnot
  let c : EuclideanSpace ℂ (Fin n) := c0.1
  let B : Set (EuclideanSpace ℂ (Fin n)) := Metric.closedBall a.1 (r / 2)
  have hBU : B ⊆ U := by
    exact (Metric.closedBall_subset_ball (by linarith : r / 2 < r)).trans hballU
  let K : Set (EuclideanSpace ℂ (Fin n)) := B ∩ u ⁻¹' {u x}
  have hcontB : ContinuousOn u B := hu.mono hBU
  have hBclosed : IsClosed B := by
    change IsClosed {y | dist y a.1 ≤ r / 2}
    exact isClosed_le (by fun_prop) continuous_const
  have hKclosed : IsClosed K := by
    exact hcontB.preimage_isClosed_of_isClosed hBclosed isClosed_singleton
  have hKcompact : IsCompact K := by
    exact (isCompact_closedBall a.1 (r / 2)).of_isClosed_subset hKclosed fun y hy => hy.1
  have haK : a.1 ∈ K := by
    refine ⟨?_, ?_⟩
    · simp [B]
      positivity
    · exact haF
  have hc0B : c ∈ B := by
    apply Metric.mem_closedBall.mpr
    have hc0dist : dist c a.1 < r / 4 := by
      simpa only [Metric.mem_ball, Subtype.dist_eq, c] using hc0ball
    change dist c a.1 ≤ r / 2
    rw [dist_comm]
    have hc0dist' : dist a.1 c < r / 4 := by simpa [dist_comm] using hc0dist
    linarith
  let f : EuclideanSpace ℂ (Fin n) → ℝ := fun y => dist c y
  have hf : ContinuousOn f K := by
    exact (continuous_const.dist continuous_id).continuousOn
  obtain ⟨z, hzK, hzmin⟩ := hKcompact.exists_isMinOn ⟨a.1, haK⟩ hf
  let R : ℝ := dist c z
  have hRpos : 0 < R := by
    by_contra h
    have hzero : R = 0 := le_antisymm (le_of_not_gt h) (by positivity)
    have hcz : dist c z = 0 := by simpa [R] using hzero
    have hcz' : c = z := dist_eq_zero.mp hcz
    apply hc0F
    change u c0 = u x
    change c0.1 = z at hcz'
    rw [hcz']
    exact hzK.2
  have hRle : R ≤ dist c a.1 := by
    dsimp [R, f] at hzmin ⊢
    exact hzmin haK
  have hc0dist : dist c a.1 < r / 4 := by
    simpa only [Metric.mem_ball, Subtype.dist_eq, c] using hc0ball
  have hclosedU : Metric.closedBall c R ⊆ U := by
    intro y hy
    apply hballU
    rw [Metric.mem_ball]
    have hyca : dist y c ≤ R := Metric.mem_closedBall.mp hy
    calc
      dist y a.1 ≤ dist y c + dist c a.1 := dist_triangle y c a.1
      _ ≤ R + dist c a.1 := add_le_add_left hyca (dist c a.1)
      _ ≤ dist c a.1 + dist c a.1 := add_le_add_left hRle (dist c a.1)
      _ < r := by linarith
  have hzSphere : z ∈ Metric.sphere c R := by
    simp [R, dist_comm, dist_eq_norm]
  have hstrict : ∀ y ∈ Metric.ball c R, u y < u x := by
    intro y hy
    have hyU : y ∈ U := hclosedU (Metric.ball_subset_closedBall hy)
    have hle := hmax y hyU
    by_contra hnot
    have heq : u y = u x := le_antisymm hle (le_of_not_gt hnot)
    have hyK : y ∈ K := by
      refine ⟨?_, heq⟩
      apply Metric.mem_closedBall.mpr
      rw [Metric.mem_ball] at hy
      have hyB : dist y a.1 < r / 2 := by
        calc
          dist y a.1 ≤ dist y c + dist c a.1 := dist_triangle y c a.1
          _ < R + dist c a.1 := add_lt_add_left hy (dist c a.1)
          _ ≤ dist c a.1 + dist c a.1 := add_le_add_left hRle (dist c a.1)
          _ < r / 2 := by linarith
      exact le_of_lt hyB
    have hmin := hzmin hyK
    dsimp [R, f] at hmin
    have hylt : dist c y < R := by
      rw [Metric.mem_ball] at hy
      simpa [dist_comm] using hy
    exact (not_lt_of_ge hmin) hylt
  refine ⟨c, R, z, hRpos, hclosedU, hzSphere, ?_, hstrict⟩
  exact hzK.2
