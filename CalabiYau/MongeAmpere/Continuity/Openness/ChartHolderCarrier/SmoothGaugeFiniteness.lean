module

public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderCarrier.Basic

@[expose] public section

open scoped Manifold ContDiff NNReal ENNReal Topology

namespace KahlerForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
/-- Smooth functions have finite finite-chart Hölder gauge on a compact chart cover when
`0 < α < 1`. -/
@[deprecated "unused hypothesis `hα₀`; will be removed" (since := "2026-10-02")]
theorem smoothChartHolderGauge_finite
    (cover : CompactChartCover E M) (k : ℕ) (α : ℝ≥0)
    (hα₀ : 0 < α) (hα₁ : α < 1)
    (f : SmoothChartHolderCore cover k α) :
    HasFiniteChartHolderGauge cover k α f.smoothMap := by
  classical
  have hα : α ≤ 1 := by
    exact_mod_cast le_of_lt hα₁
  have hcharts : HolderBoundedInCharts E k α
      ({(f.smoothMap : M → ℝ)} : Set (M → ℝ)) :=
    HolderBoundedInCharts.singleton f.smoothMap.contMDiff hα
  change (⨆ i : cover.ι,
    CalabiYau.Schauder.eContDiffHolderGaugeOn k α (cover.piece i)
      (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm)) < ⊤
  apply lt_top_iff_ne_top.mpr
  apply iSup_ne_top
  intro i
  obtain ⟨C, hC⟩ := hcharts (cover.base i) (cover.piece i)
    (cover.isCompact_piece i) (cover.piece_in_target i)
  have hbound := hC f.smoothMap (Set.mem_singleton _)
  have hholder : HolderWith C α
      ((cover.piece i).domRestrict
        (iteratedFDeriv ℝ k
          (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm))) := by
    simpa [Function.comp_def] using hbound.2.holderWith
  have hle := CalabiYau.Schauder.eContDiffHolderGaugeOn_le
    (fun _ : ℕ => C) C hbound.1 hholder
  have hsum : (∑ j ∈ Finset.range (k + 1), (C : ℝ≥0∞)) ≠ ⊤ := by
    apply ENNReal.sum_ne_top.mpr
    intro j hj
    exact ENNReal.coe_ne_top
  have htotal : (∑ j ∈ Finset.range (k + 1), (C : ℝ≥0∞)) + C ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hsum, ENNReal.coe_ne_top⟩
  exact ne_top_of_le_ne_top htotal hle

end KahlerForm
