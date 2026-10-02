module

public import Mathlib.Data.Real.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Positive lower bounds on compact sets

A continuous positive real-valued function on a nonempty compact set has a uniform positive lower
bound, by attainment of its minimum.
-/

@[expose] public section

namespace PositiveLowerBound

/-- A continuous strictly positive function on a nonempty compact set has a positive uniform
lower bound. This is used for the reference metric determinant on a buffered chart domain. -/
theorem exists_pos_lower_bound_of_continuousOn_of_forall_pos
    {E : Type*} [TopologicalSpace E] {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    {f : E → ℝ} (hf : ContinuousOn f K) (hpos : ∀ z ∈ K, 0 < f z) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K, δ ≤ f z := by
  obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn hne hf
  refine ⟨f z, hpos z hz, ?_⟩
  intro y hy
  exact (isMinOn_iff.mp hmin) y hy

end PositiveLowerBound

end
