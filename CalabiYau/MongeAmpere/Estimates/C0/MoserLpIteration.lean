module

public import CalabiYau.Analysis.MoserIteration.Iteration
public import CalabiYau.Geometry.Kahler.Volume
public import CalabiYau.Geometry.Kahler.Sobolev
public import CalabiYau.MongeAmpere.Estimates.C0.Softplus

public section

open scoped Manifold ContDiff ENNReal
open MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M]
  [ConnectedSpace M]

@[expose] noncomputable def c0MomentExponent (κ : ℝ) (k : ℕ) : ENNReal :=
  ENNReal.ofReal (2 * κ ^ k)

@[expose] noncomputable def c0MomentFactor (n : ℕ) (κ C_S : ℝ) (k : ℕ) : ENNReal :=
  ENNReal.ofReal
    ((max C_S 1 * (1 + (n : ℝ) * (2 * κ ^ k) / 4)) ^ ((2 * κ ^ k)⁻¹))

omit [ConnectedSpace M] in
/-- Convert an eLpNorm recurrence with a finite product into an essential-supremum estimate.

Continuity on compact `M` supplies the initial finite moment. -/
theorem c0_eLpNormEssSup_bound_of_recurrence
    (ω₀ : KahlerForm n M) {f : M → ℝ}
    (hf : AEStronglyMeasurable f ω₀.volume) (hcont : Continuous f)
    (hnonneg : ∀ x, 0 ≤ f x)
    {p factor : ℕ → ENNReal} {B : ENNReal}
    (hp0 : ∀ k, p k ≠ 0) (hpTop : ∀ k, p k ≠ ⊤)
    (hpTendsto : Filter.Tendsto (fun k => (p k).toReal) Filter.atTop Filter.atTop)
    (hrec : ∀ k, eLpNorm f (p (k + 1)) ω₀.volume ≤
      factor k * eLpNorm f (p k) ω₀.volume)
    (hprod : ∀ N, (∏ k ∈ Finset.range N, factor k) ≤ B) :
    eLpNormEssSup f ω₀.volume ≤ B * eLpNorm f (p 0) ω₀.volume ∧
      eLpNorm f (p 0) ω₀.volume < ⊤ := by
  have hess := MeasureTheory.eLpNormEssSup_le_of_eLpNorm_recurrence
    hf hp0 hpTop hpTendsto hrec hprod
  obtain ⟨C, hC⟩ := (isCompact_range hcont).bddAbove
  have hbound : ∀ x, ‖f x‖ ≤ max C 0 := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg x)]
    exact (hC (Set.mem_range_self x)).trans (le_max_left _ _)
  have hmem : MemLp f (p 0) ω₀.volume :=
    MemLp.of_bound hf (max C 0) (Filter.Eventually.of_forall hbound)
  exact ⟨hess, hmem.eLpNorm_lt_top⟩

omit [ConnectedSpace M] in
theorem c0_centered_softplus_essSup_bound_of_product
    (ω₀ : KahlerForm n M) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u)
    {κ C_S : ℝ} {B : ENNReal} (hκ : 1 < κ)
    (hprod : ∀ N,
      (∏ k ∈ Finset.range N, c0MomentFactor n κ C_S k) ≤ B)
    (hf : AEStronglyMeasurable (c0CenteredSoftplus u) ω₀.volume)
    (hrec : ∀ k,
      eLpNorm (c0CenteredSoftplus u) (c0MomentExponent κ (k + 1)) ω₀.volume ≤
        c0MomentFactor n κ C_S k *
          eLpNorm (c0CenteredSoftplus u) (c0MomentExponent κ k) ω₀.volume) :
    eLpNormEssSup (c0CenteredSoftplus u) ω₀.volume ≤
        B *
          eLpNorm (c0CenteredSoftplus u) (c0MomentExponent κ 0) ω₀.volume ∧
      eLpNorm (c0CenteredSoftplus u) (c0MomentExponent κ 0) ω₀.volume < ⊤ := by
  have hq (k : ℕ) : 0 < 2 * κ ^ k :=
    mul_pos (by norm_num) (pow_pos (lt_trans zero_lt_one hκ) k)
  have hp0 : ∀ k, c0MomentExponent κ k ≠ 0 :=
    fun k => ENNReal.ofReal_ne_zero_iff.mpr (hq k)
  have hpTop : ∀ k, c0MomentExponent κ k ≠ ⊤ :=
    fun _ => (ENNReal.ofReal_lt_top).ne
  have hpEq : (fun k => (c0MomentExponent κ k).toReal) = fun k => 2 * κ ^ k := by
    funext k
    change (ENNReal.ofReal (2 * κ ^ k)).toReal = 2 * κ ^ k
    exact ENNReal.toReal_ofReal (hq k).le
  have hpTendsto : Filter.Tendsto (fun k => (c0MomentExponent κ k).toReal)
      Filter.atTop Filter.atTop := by
    rw [hpEq]
    exact Filter.Tendsto.const_mul_atTop (by norm_num : 0 < (2 : ℝ))
      (tendsto_pow_atTop_atTop_of_one_lt hκ)
  exact c0_eLpNormEssSup_bound_of_recurrence ω₀ hf
    (continuous_c0Softplus.comp hu.continuous)
    (fun x => c0Softplus_nonneg (u x)) hp0 hpTop hpTendsto hrec hprod

end KahlerForm
