module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.Topology.Order.Compact

/-!
# Normalizations preserved by a uniform limit

The compactness argument of GT, Lemma 6.36, p. 136, preserves the integral on a finite
measure space and an attained absolute value. The latter is not a supremum normalization:
no pointwise bound `|u_j| ≤ 1` is assumed or concluded.
-/

set_option autoImplicit false

@[expose] public section

open Filter MeasureTheory
open scoped Topology

/-- Finite measure permits passage of the mean through uniform convergence. On a compact
space, witnesses with `|u_j x_j|=1` give a point with `|f x|=1`, using the closed compact
image of `|f|`. This does not require extracting a subsequence of the points themselves. -/
theorem integral_zero_and_exists_abs_eq_one_of_uniform_limit
    {M : Type*} [TopologicalSpace M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M]
    (μ : Measure M) [IsFiniteMeasure μ]
    (u : ℕ → M → ℝ) (f : M → ℝ)
    (hu : ∀ j, Continuous (u j)) (hf : Continuous f)
    (hconv : TendstoUniformly u f atTop)
    (hmean : ∀ j, ∫ x, u j x ∂μ = 0)
    (hnorm : ∀ j, ∃ x, |u j x| = 1) :
    (∫ x, f x ∂μ = 0) ∧ ∃ x, |f x| = 1 := by
  constructor
  · have hUi : ∀ j, Integrable (u j) μ := by
      intro j
      let Uj : C(M, ℝ) := ⟨u j, hu j⟩
      refine Integrable.of_bound Uj.continuous.aestronglyMeasurable ‖Uj‖ ?_
      filter_upwards [] with x
      exact Uj.norm_coe_le_norm x
    have hFi : Integrable f μ := by
      let F : C(M, ℝ) := ⟨f, hf⟩
      refine Integrable.of_bound F.continuous.aestronglyMeasurable ‖F‖ ?_
      filter_upwards [] with x
      exact F.norm_coe_le_norm x
    have hInt : Tendsto (fun j => ∫ x, u j x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      let δ : ℝ := ε / (μ.real Set.univ + 1)
      have hδ : 0 < δ := by
        dsimp [δ]
        positivity
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
        (Metric.tendstoUniformly_iff.mp hconv δ hδ)
      refine ⟨N, ?_⟩
      intro j hjN
      have hj : ∀ x, dist (f x) (u j x) < δ := hN j hjN
      have hbound : ∀ᵐ x ∂μ, ‖u j x - f x‖ ≤ δ := by
        filter_upwards [] with x
        have hx := hj x
        rw [Real.dist_eq] at hx
        rw [Real.norm_eq_abs, abs_sub_comm]
        exact hx.le
      have hle := norm_integral_le_of_norm_le_const hbound
      have hdist : dist (∫ x, u j x ∂μ) (∫ x, f x ∂μ) ≤ δ * μ.real Set.univ := by
        rw [Real.dist_eq, ← integral_sub (hUi j) hFi]
        exact hle
      refine hdist.trans_lt ?_
      have hmass : 0 ≤ μ.real Set.univ := measureReal_nonneg
      change ε / (μ.real Set.univ + 1) * μ.real Set.univ < ε
      rw [div_mul_eq_mul_div]
      apply (div_lt_iff₀ (by linarith : 0 < μ.real Set.univ + 1)).2
      nlinarith [mul_pos hε (by linarith : 0 < μ.real Set.univ + 1)]
    have hzero : Tendsto (fun j => ∫ x, u j x ∂μ) atTop (𝓝 0) := by
      simp [hmean]
    exact tendsto_nhds_unique hInt hzero
  · let g : M → ℝ := fun x => |f x|
    have hg : Continuous g := continuous_abs.comp hf
    have hcompact : IsCompact (Set.range g) := isCompact_range hg
    have hclosure : (1 : ℝ) ∈ closure (Set.range g) := by
      apply (Metric.mem_closure_iff).2
      intro ε hε
      have hev := (Metric.tendstoUniformly_iff.mp hconv) ε hε
      obtain ⟨j, hj⟩ := hev.exists
      obtain ⟨x, hx⟩ := hnorm j
      refine ⟨g x, ⟨x, rfl⟩, ?_⟩
      change dist 1 (|f x|) < ε
      rw [dist_comm, Real.dist_eq]
      calc
        abs (abs (f x) - 1) = abs (abs (f x) - abs (u j x)) := by rw [hx]
        _ ≤ abs (f x - u j x) := by
          simpa only [Real.norm_eq_abs] using norm_abs_sub_abs (f x) (u j x)
        _ = dist (f x) (u j x) := (Real.dist_eq _ _).symm
        _ < ε := hj x
    have hmem : (1 : ℝ) ∈ Set.range g := hcompact.isClosed.closure_subset hclosure
    obtain ⟨x, hx⟩ := hmem
    exact ⟨x, by simpa [g] using hx⟩
