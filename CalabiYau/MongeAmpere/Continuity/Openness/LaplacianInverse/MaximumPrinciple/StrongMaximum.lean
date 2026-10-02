module

public import CalabiYau.Mathlib.Topology.MetricSpace.TangentBall
public import CalabiYau.MongeAmpere.Continuity.Openness.LaplacianInverse.MaximumPrinciple.Barrier
public import CalabiYau.MongeAmpere.Continuity.Openness.LaplacianInverse.MaximumPrinciple.BoundaryContact
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# C² strong maximum principle for the complex elliptic principal part

Specialization of Gilbarg–Trudinger, §3.2, Theorem 3.5, from the geometric tangent-ball
step, the exponential barrier estimate, and annular boundary comparison. The sign is `Lu ≥ 0`.
There are no first-order or zeroth-order terms and no positive-dimension premise.
-/

@[expose] public section

open scoped ContDiff Topology NNReal
open Set

/-- A C² subsolution of a bounded uniformly Hermitian elliptic principal part on an open
connected domain is constant if it attains its maximum inside. -/
theorem eqOn_of_complexEllipticOp_nonneg_of_isMaxOn {n : ℕ}
    (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U) (hconn : IsPreconnected U)
    {u : EuclideanSpace ℂ (Fin n) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    {lam K : ℝ≥0} (hlam : 0 < lam) (hEll : IsUniformlyEllipticOn A lam U)
    (hbound : ∀ y ∈ U, ∀ j k, ‖A y j k‖ ≤ (K : ℝ))
    (hLu : ∀ y ∈ U, 0 ≤ complexEllipticOp A u y)
    {x : EuclideanSpace ℂ (Fin n)} (hx : x ∈ U) (hmax : IsMaxOn u U x) :
    ∀ y ∈ U, u y = u x := by
  by_contra hne
  obtain ⟨c, R, z, hR, hball, hz, hzx, hstrict⟩ :=
    exists_ball_tangent_to_maximum_set hU hconn hu.continuousOn hx hmax hne
  have hballU : Metric.ball c R ⊆ U := fun y hy => hball (Metric.ball_subset_closedBall hy)
  have hEllBall : IsUniformlyEllipticOn A lam (Metric.ball c R) :=
    fun y hy => hEll y (hballU hy)
  obtain ⟨a, ha, hv, hvzero, hLv, hvderiv⟩ :=
    exists_complexEllipticOp_exponential_barrier A hR hlam hEllBall
      (fun y hy => hbound y (hballU hy))
  have hpos := complexEllipticOp_boundary_contact_deriv_pos A hU hu hv hR hball hz
    hEllBall (fun y hy => hLu y (hballU hy))
    (fun y hy => by rw [hzx]; exact hmax (hball hy))
    (fun y hy => by rw [hzx]; exact hstrict y hy)
    hvzero hLv (hvderiv z hz)
  have hzU : z ∈ U := hball (Metric.sphere_subset_closedBall hz)
  have hlocal : IsLocalMax u z := by
    filter_upwards [hU.mem_nhds hzU] with y hy
    rw [hzx]
    exact hmax hy
  rw [hlocal.fderiv_eq_zero] at hpos
  simp at hpos
