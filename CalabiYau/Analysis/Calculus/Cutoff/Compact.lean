-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Calculus/Cutoff/Compact.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Calculus.Cutoff.Basic
public import Mathlib.Geometry.Manifold.Metrizable

@[expose] public section

set_option autoImplicit false

namespace CalabiYau

open Filter Set
open scoped ContDiff Manifold Topology

theorem exists_bump_compact
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K U : Set E}
    (hK : IsCompact K)
    (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ χ : E → ℝ,
      ContDiff ℝ ∞ χ ∧
      HasCompactSupport χ ∧
      χ =ᶠ[𝓝ˢ K] 1 ∧
      tsupport χ ⊆ U ∧
      Set.range χ ⊆ Set.Icc 0 1 := by
  have : NormalSpace E := inferInstance
  have : LocallyCompactSpace E := inferInstance
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨χM, hχone, hχzero, hχrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior
      (I := 𝓘(ℝ, E)) (M := E) (n := (⊤ : ℕ∞)) hK.isClosed hKL
  let χ : E → ℝ := χM
  refine ⟨χ, ?_, ?_, ?_, ?_, Set.range_subset_iff.mpr hχrange⟩
  · exact contMDiff_iff_contDiff.mp
      (χM.contMDiff.of_le (by exact_mod_cast le_top))
  · refine HasCompactSupport.intro hL ?_
    intro x hx
    exact hχzero x hx
  · exact hχone
  · change closure (Function.support χ) ⊆ U
    exact (closure_minimal
      (fun x hx => by
        by_contra hxL
        exact hx (hχzero x hxL))
      hL.isClosed).trans hLU

theorem exists_bump_compact_with_fderiv_bound
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K U : Set E}
    (hK : IsCompact K)
    (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ χ : E → ℝ,
      ContDiff ℝ ∞ χ ∧
      HasCompactSupport χ ∧
      χ =ᶠ[nhdsSet K] 1 ∧
      tsupport χ ⊆ U ∧
      Set.range χ ⊆ Set.Icc 0 1 ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, ‖fderiv ℝ χ x‖ ≤ C := by
  obtain ⟨χ, hχ_smooth, hχ_compact, hχ_one, hχ_support, hχ_range⟩ :=
    exists_bump_compact hK hU hKU
  refine ⟨χ, hχ_smooth, hχ_compact, hχ_one, hχ_support, hχ_range, ?_⟩
  have h_fderiv_cont : Continuous (fderiv ℝ χ) :=
    hχ_smooth.continuous_fderiv (by simp)
  have h_norm_cont : Continuous (fun x : E => ‖fderiv ℝ χ x‖) := h_fderiv_cont.norm
  have h_fderiv_compact : HasCompactSupport (fderiv ℝ χ) := hχ_compact.fderiv ℝ
  have h_norm_compact : HasCompactSupport (fun x : E => ‖fderiv ℝ χ x‖) := by
    apply h_fderiv_compact.comp_left
    simp
  obtain ⟨C₀, hC₀⟩ := h_norm_cont.bddAbove_range_of_hasCompactSupport h_norm_compact
  refine ⟨max C₀ 0, le_max_right _ _, fun x => ?_⟩
  exact (hC₀ ⟨x, rfl⟩).trans (le_max_left _ _)

end CalabiYau
