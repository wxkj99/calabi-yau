-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Geometry/Metric/PointwiseInner/Bounds.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Riemannian.Metric.Basic
public import CalabiYau.Geometry.Manifold.Tensor.RSTensor.Defs

@[expose] public section

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff ENNReal NNReal Matrix BigOperators

namespace CalabiYau.Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

lemma metric_inner_cauchy_schwarz_sq
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    (g.inner x v w) ^ 2 ≤ g.inner x v v * g.inner x w w := by
  classical
  set a := g.inner x v v
  set b := g.inner x w w
  set c := g.inner x v w
  have ha_nn : 0 ≤ a := by
    rcases eq_or_ne v 0 with hv0 | hv0
    · have heq : a = 0 := by change g.inner x v v = 0; rw [hv0]; simp
      rw [heq]
    · exact (g.pos x v hv0).le
  have hb_nn : 0 ≤ b := by
    rcases eq_or_ne w 0 with hw0 | hw0
    · have heq : b = 0 := by change g.inner x w w = 0; rw [hw0]; simp
      rw [heq]
    · exact (g.pos x w hw0).le
  have hquad : ∀ t : ℝ, 0 ≤ t * t * a + 2 * t * c + b := by
    intro t
    have hpos : 0 ≤ g.inner x (t • v + w) (t • v + w) := by
      rcases eq_or_ne (t • v + w) 0 with hz | hnz
      · have heqz : g.inner x (t • v + w) (t • v + w) = 0 := by rw [hz]; simp
        rw [heqz]
      · exact (g.pos x _ hnz).le
    have h_expand : g.inner x (t • v + w) (t • v + w) =
        t * t * a + 2 * t * c + b := by
      have h1 : g.inner x (t • v + w) (t • v + w) =
          g.inner x (t • v) (t • v + w) + g.inner x w (t • v + w) := by
        rw [map_add (g.inner x), add_apply]
      have h2 : g.inner x (t • v) (t • v + w) =
          g.inner x (t • v) (t • v) + g.inner x (t • v) w :=
        map_add (g.inner x (t • v)) (t • v) w
      have h3 : g.inner x w (t • v + w) =
          g.inner x w (t • v) + g.inner x w w :=
        map_add (g.inner x w) (t • v) w
      have h4 : g.inner x (t • v) (t • v) = t * (t * a) := by
        rw [map_smul (g.inner x), smul_apply,
          map_smul (g.inner x v), smul_eq_mul, smul_eq_mul]
      have h5 : g.inner x (t • v) w = t * c := by
        rw [map_smul (g.inner x), smul_apply, smul_eq_mul]
      have h6 : g.inner x w (t • v) = t * c := by
        rw [map_smul (g.inner x w), smul_eq_mul, g.symm x w v]
      rw [h1, h2, h3, h4, h5, h6]
      ring
    rw [h_expand] at hpos
    exact hpos
  rcases lt_or_eq_of_le ha_nn with ha_pos | ha_zero
  · have hroot := hquad (-c / a)
    have hsimp : -c / a * (-c / a) * a + 2 * (-c / a) * c + b = b - c^2 / a := by
      field_simp
      ring
    rw [hsimp] at hroot
    have hcsa : c ^ 2 / a ≤ b := by linarith
    have h1 : c ^ 2 = a * (c ^ 2 / a) := by field_simp
    rw [h1]
    exact mul_le_mul_of_nonneg_left hcsa ha_nn
  · have ha_eq : a = 0 := ha_zero.symm
    have hv_zero : v = 0 := by
      by_contra hne
      exact (lt_irrefl (0 : ℝ)) (ha_eq ▸ g.pos x v hne)
    have hc_eq : c = 0 := by
      change g.inner x v w = 0
      rw [hv_zero]; simp
    rw [hc_eq, ha_eq]
    simp

lemma abs_metric_inner_le_sqrt_metric_quadratic
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    |g.inner x v w| ≤ Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) := by
  have ha_nn : 0 ≤ g.inner x v v := metric_inner_self_nonneg (I := I) (M := M) g x v
  have hb_nn : 0 ≤ g.inner x w w := metric_inner_self_nonneg (I := I) (M := M) g x w
  have hCS_sq := metric_inner_cauchy_schwarz_sq (I := I) (M := M) g x v w
  have h_abs_sq : |g.inner x v w| ^ 2 ≤ g.inner x v v * g.inner x w w := by
    rw [sq_abs]; exact hCS_sq
  have hsqrt_mul : Real.sqrt (g.inner x v v * g.inner x w w) =
      Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) :=
    Real.sqrt_mul ha_nn _
  have h_abs_nn : 0 ≤ |g.inner x v w| := abs_nonneg _
  have h_le_sqrt : |g.inner x v w| ≤ Real.sqrt (g.inner x v v * g.inner x w w) := by
    rw [show |g.inner x v w| = Real.sqrt (|g.inner x v w| ^ 2) from
      (Real.sqrt_sq h_abs_nn).symm]
    exact Real.sqrt_le_sqrt h_abs_sq
  rw [hsqrt_mul] at h_le_sqrt
  exact h_le_sqrt

end CalabiYau.Laplacian

end
