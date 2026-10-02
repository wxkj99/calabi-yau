module

public import CalabiYau.MongeAmpere.Continuity.Openness.C2Approximation.Smoothing.CompactSupport

/-!
# Uniform convergence of the full two-jet

Hirsch, *Differential Topology*, §2, Theorems 2.3–2.4, pp. 46–50:
all continuous derivatives of a compactly supported C² function are uniformly
continuous. Applying the same normalized shrinking bump to each of these
continuous jets proves uniform C² convergence. This step uses a genuine
compact-support hypothesis; local continuity on a noncompact domain alone
would not imply uniform convergence over the entire space.
-/

@[expose] public section

open scoped ContDiff Convolution Topology NNReal
open MeasureTheory MeasureTheory.Measure

/-- The normalized shrinking kernels uniformly approximate all real Fréchet
jets through order two, provided that differentiation through convolution has
already been identified. Works for any finite-dimensional norm on `E`;
there is no silent isometric identification with Euclidean coordinate space. -/
theorem euclideanC2Convolution_uniform_twoJet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [IsAddHaarMeasure (volume : Measure E)]
    {f : E → ℝ} {U : Set E}
    (A : EuclideanC2ConvolutionData E f U) (hf : ContDiff ℝ 2 f)
    (hcompact : HasCompactSupport f)
    (hjets : ∀ j r, r ≤ 2 → ∀ x,
      iteratedFDeriv ℝ r (A.approximation j) x =
        ∫ y, ((A.kernel j).normed (volume : Measure E) y) •
          iteratedFDeriv ℝ r f (x - y) ∂(volume : Measure E)) :
    ∀ ε : ℝ≥0, 0 < ε → ∃ N, ∀ j, N ≤ j → ∀ r ≤ 2, ∀ x,
      ‖iteratedFDeriv ℝ r (A.approximation j - f) x‖ ≤ ε := by
  classical
  intro ε hε
  have hεR : 0 < (ε : ℝ) := by exact_mod_cast hε
  have hper (r : ℕ) (hr : r ≤ 2) :
      ∃ N : ℕ, ∀ j ≥ N, ∀ x : E,
        ‖iteratedFDeriv ℝ r (A.approximation j - f) x‖ ≤ ε := by
    let g : E → (E [×r]→L[ℝ] ℝ) := fun x => iteratedFDeriv ℝ r f x
    have hgcont : Continuous g := hf.continuous_iteratedFDeriv (by exact_mod_cast hr)
    have hgsupp : HasCompactSupport g := hcompact.iteratedFDeriv r
    have hguniform : UniformContinuous g :=
      hgcont.uniformContinuous_of_tendsto_cocompact hgsupp.is_zero_at_infty
    obtain ⟨δ, hδ, hgδ⟩ := (Metric.uniformContinuous_iff.mp hguniform) (ε : ℝ) hεR
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ j ≥ N, (A.kernel j).rOut < δ := by
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp A.radius_tendsto) δ hδ
      refine ⟨N, ?_⟩
      intro j hj
      simpa [Real.dist_eq, abs_of_nonneg (le_of_lt (A.kernel j).rOut_pos)] using hN j hj
    refine ⟨N, ?_⟩
    intro j hj x
    have hlocal : ∀ y ∈ Metric.ball x (A.kernel j).rOut,
        dist (g y) (g x) ≤ (ε : ℝ) := by
      intro y hy
      exact le_of_lt (hgδ (lt_trans (Metric.mem_ball.mp hy) (hN j hj)))
    have hbound := (A.kernel j).dist_normed_convolution_le
      (μ := (volume : Measure E)) (g := g) hgcont.aestronglyMeasurable hlocal
    have hconv : (((A.kernel j).normed (volume : Measure E)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x =
        ∫ y, ((A.kernel j).normed (volume : Measure E) y) • g (x - y) ∂(volume : Measure E) :=
      convolution_lsmul
    have happroxC2 : ContDiffAt ℝ r (A.approximation j) x :=
      (A.smooth j).contDiffAt.of_le (by exact_mod_cast (le_top : r ≤ (⊤ : ℕ∞)))
    have hfC2 : ContDiffAt ℝ r f x := hf.contDiffAt.of_le (by exact_mod_cast hr)
    rw [iteratedFDeriv_sub_apply happroxC2 hfC2, hjets j r hr x]
    change ‖(∫ y, ((A.kernel j).normed (volume : Measure E) y) • g (x - y) ∂(volume : Measure E)) - g x‖ ≤ (ε : ℝ)
    rw [dist_eq_norm, hconv] at hbound
    exact hbound
  obtain ⟨N₀, hN₀⟩ := hper 0 (by omega)
  obtain ⟨N₁, hN₁⟩ := hper 1 (by omega)
  obtain ⟨N₂, hN₂⟩ := hper 2 (by omega)
  refine ⟨max N₀ (max N₁ N₂), ?_⟩
  intro j hj r hr x
  interval_cases r
  · exact hN₀ j ((le_max_left _ _).trans hj) x
  · exact hN₁ j ((le_max_of_le_right (le_max_left _ _)).trans hj) x
  · exact hN₂ j ((le_max_of_le_right (le_max_right _ _)).trans hj) x
