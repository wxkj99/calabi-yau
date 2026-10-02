-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/FiniteDimensional/Coercivity.lean
-- Locally modified.
module
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Separation.Regular

@[expose] public section


open Set

section

variable {Z F : Type*} [TopologicalSpace Z]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : Z → F →L[ℝ] F →L[ℝ] ℝ} {K : Set Z}

theorem ContinuousOn.exists_uniform_bilin_quadratic_lower_bound
    (hB : ContinuousOn (fun p : Z × F => B p.1 p.2 p.2) (K ×ˢ (univ : Set F)))
    (hK : IsCompact K) (hpos : ∀ x ∈ K, ∀ v : F, v ≠ 0 → 0 < B x v v) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ v : F, c * ‖v‖ ^ 2 ≤ B x v v := by
  have hcpt := hK.prod (isCompact_sphere (0 : F) 1)
  have hc : ContinuousOn (fun p : Z × F => B p.1 p.2 p.2)
      (K ×ˢ Metric.sphere (0 : F) 1) :=
    hB.mono (prod_mono Subset.rfl (subset_univ _))
  have hp : ∀ p ∈ K ×ˢ Metric.sphere (0 : F) 1, 0 < B p.1 p.2 p.2 := by
    intro p hp
    apply hpos p.1 hp.1 p.2
    intro hzero
    have hn := hp.2
    rw [hzero, Metric.mem_sphere, dist_self] at hn
    exact zero_ne_one hn
  obtain ⟨c, hcpos, hcbound⟩ := hcpt.exists_forall_le' hc hp
  refine ⟨c, hcpos, ?_⟩
  intro x hx v
  by_cases hv : v = 0
  · subst v
    simp
  · have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hu : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : F) 1 := by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv,
        Real.norm_eq_abs, abs_norm, inv_mul_cancel₀ hvnorm]
    have hbound := hcbound (x, ‖v‖⁻¹ • v) ⟨hx, hu⟩
    calc
      c * ‖v‖ ^ 2 ≤ B x (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hbound (sq_nonneg ‖v‖)
      _ = B x v v := by
        simp only [map_smul, smul_apply, smul_eq_mul]
        field_simp

end

section

variable {Z E : Type*} [TopologicalSpace Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

end
