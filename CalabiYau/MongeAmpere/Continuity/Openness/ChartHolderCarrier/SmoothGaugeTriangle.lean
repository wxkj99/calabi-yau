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
/-- The finite-chart Hölder gauge is subadditive on the fixed smooth core. -/
theorem smoothChartHolderGauge_add_le
    (cover : CompactChartCover E M) (k : ℕ) (α : ℝ≥0)
    (f g : SmoothChartHolderCore cover k α) :
    smoothChartHolderGauge cover k α (f + g) ≤
      smoothChartHolderGauge cover k α f + smoothChartHolderGauge cover k α g := by
  classical
  unfold smoothChartHolderGauge finiteChartHolderGauge
  apply iSup_le
  intro i
  let chart : E → M := (extChartAt 𝓘(ℝ, E) (cover.base i)).symm
  have hfcoord : ∀ x ∈ cover.piece i,
      ContDiffAt ℝ k (f.smoothMap ∘ chart) x := by
    have hOn : ContDiffOn ℝ ∞ (f.smoothMap ∘ chart)
        (extChartAt 𝓘(ℝ, E) (cover.base i)).target := by
      apply ContMDiffOn.contDiffOn
      simpa [chart] using f.smoothMap.contMDiff.comp_contMDiffOn
        (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, E)) (cover.base i))
    intro x hx
    have hxTarget : x ∈ (extChartAt 𝓘(ℝ, E) (cover.base i)).target :=
      cover.piece_in_target i hx
    have hxnhds : (extChartAt 𝓘(ℝ, E) (cover.base i)).target ∈ 𝓝 x :=
      (isOpen_extChartAt_target (I := 𝓘(ℝ, E)) (cover.base i)).mem_nhds hxTarget
    exact (hOn.contDiffAt hxnhds).of_le
      (WithTop.coe_le_coe.2 (show (k : ℕ∞) ≤ ⊤ from le_top))
  have hgcoord : ∀ x ∈ cover.piece i,
      ContDiffAt ℝ k (g.smoothMap ∘ chart) x := by
    have hOn : ContDiffOn ℝ ∞ (g.smoothMap ∘ chart)
        (extChartAt 𝓘(ℝ, E) (cover.base i)).target := by
      apply ContMDiffOn.contDiffOn
      simpa [chart] using g.smoothMap.contMDiff.comp_contMDiffOn
        (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, E)) (cover.base i))
    intro x hx
    have hxTarget : x ∈ (extChartAt 𝓘(ℝ, E) (cover.base i)).target :=
      cover.piece_in_target i hx
    have hxnhds : (extChartAt 𝓘(ℝ, E) (cover.base i)).target ∈ 𝓝 x :=
      (isOpen_extChartAt_target (I := 𝓘(ℝ, E)) (cover.base i)).mem_nhds hxTarget
    exact (hOn.contDiffAt hxnhds).of_le
      (WithTop.coe_le_coe.2 (show (k : ℕ∞) ≤ ⊤ from le_top))
  have hlocal := CalabiYau.Schauder.eContDiffHolderGaugeOn_add_le k α (cover.piece i)
    (f.smoothMap ∘ chart) (g.smoothMap ∘ chart) hfcoord hgcoord
  have hsum : (f + g : SmoothChartHolderCore cover k α).smoothMap =
      f.smoothMap + g.smoothMap := rfl
  have hchart_add : (f.smoothMap + g.smoothMap) ∘ chart =
      (f.smoothMap ∘ chart) + (g.smoothMap ∘ chart) := by
    ext z
    rfl
  calc
    CalabiYau.Schauder.eContDiffHolderGaugeOn k α (cover.piece i)
        (((f + g : SmoothChartHolderCore cover k α).smoothMap) ∘ chart) ≤
        CalabiYau.Schauder.eContDiffHolderGaugeOn k α (cover.piece i)
          (f.smoothMap ∘ chart) +
        CalabiYau.Schauder.eContDiffHolderGaugeOn k α (cover.piece i)
          (g.smoothMap ∘ chart) := by
      rw [hsum, hchart_add]
      exact hlocal
    _ ≤ (⨆ j, CalabiYau.Schauder.eContDiffHolderGaugeOn k α (cover.piece j)
          (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base j)).symm)) +
        (⨆ j, CalabiYau.Schauder.eContDiffHolderGaugeOn k α (cover.piece j)
          (g.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base j)).symm)) :=
      add_le_add
        (by
          simpa [chart] using
            (le_iSup (fun j => CalabiYau.Schauder.eContDiffHolderGaugeOn k α
              (cover.piece j)
              (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base j)).symm)) i))
        (by
          simpa [chart] using
            (le_iSup (fun j => CalabiYau.Schauder.eContDiffHolderGaugeOn k α
              (cover.piece j)
              (g.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base j)).symm)) i))

end KahlerForm
