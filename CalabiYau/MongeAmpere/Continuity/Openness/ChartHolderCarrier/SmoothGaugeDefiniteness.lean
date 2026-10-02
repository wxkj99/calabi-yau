module

public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderCarrier.Basic

@[expose] public section

open scoped Manifold ContDiff NNReal ENNReal Topology

namespace KahlerForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The chart gauge separates smooth core functions; the chart interiors cover `M`, including in
flat complex dimension one and in the empty-manifold edge case. -/
theorem smoothChartHolderGauge_eq_zero_iff
    (cover : CompactChartCover E M) (k : ℕ) (α : ℝ≥0)
    (f : SmoothChartHolderCore cover k α) :
    smoothChartHolderGauge cover k α f = 0 ↔ f = 0 := by
  constructor
  · intro hg
    apply (smoothChartHolderCoreEquivSmoothMap cover k α).injective
    ext x
    rcases cover.interior_covers x with ⟨i, ⟨z, hz, hzx⟩⟩
    have hzpiece : z ∈ cover.piece i := interior_subset hz
    have hjet := CalabiYau.Schauder.spatialJet_le_eContDiffHolderGaugeOn k α
      (cover.piece i)
      (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm)
      (j := 0) (Nat.zero_le k) z hzpiece
    have hpiece : CalabiYau.Schauder.eContDiffHolderGaugeOn k α (cover.piece i)
        (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) ≤
        smoothChartHolderGauge cover k α f := by
      change CalabiYau.Schauder.eContDiffHolderGaugeOn k α (cover.piece i)
          (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) ≤
        ⨆ j, CalabiYau.Schauder.eContDiffHolderGaugeOn k α (cover.piece j)
          (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base j)).symm)
      exact le_iSup
        (fun j : cover.ι => CalabiYau.Schauder.eContDiffHolderGaugeOn k α
          (cover.piece j)
          (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base j)).symm)) i
    have hpoint : ENNReal.ofReal ‖f.smoothMap x‖ ≤ smoothChartHolderGauge cover k α f := by
      calc
        ENNReal.ofReal ‖f.smoothMap x‖ =
            ENNReal.ofReal ‖iteratedFDeriv ℝ 0
              (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z‖ := by
          rw [← hzx]
          simp only [norm_iteratedFDeriv_zero, Function.comp_apply]
        _ ≤ CalabiYau.Schauder.eContDiffHolderGaugeOn k α (cover.piece i)
            (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) := hjet
        _ ≤ smoothChartHolderGauge cover k α f := hpiece
    have hzero : ENNReal.ofReal ‖f.smoothMap x‖ = 0 := by
      rw [hg] at hpoint
      exact le_antisymm hpoint bot_le
    have hnorm : ‖f.smoothMap x‖ = 0 := by simpa using hzero
    exact norm_eq_zero.mp hnorm
  · intro hf
    subst f
    have hzero : (0 : SmoothChartHolderCore cover k α).smoothMap = 0 := by
      change (smoothChartHolderCoreEquivSmoothMap cover k α)
        ((smoothChartHolderCoreEquivSmoothMap cover k α).symm 0) = 0
      exact (smoothChartHolderCoreEquivSmoothMap cover k α).apply_symm_apply 0
    change (⨆ i, CalabiYau.Schauder.eContDiffHolderGaugeOn k α (cover.piece i)
      ((0 : SmoothChartHolderCore cover k α).smoothMap ∘
        (extChartAt 𝓘(ℝ, E) (cover.base i)).symm)) = 0
    apply le_antisymm
    · apply iSup_le
      intro i
      have hcoord : ((0 : SmoothChartHolderCore cover k α).smoothMap ∘
          (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) = (0 : E → ℝ) := by
        funext z
        change (0 : SmoothChartHolderCore cover k α).smoothMap
          ((extChartAt 𝓘(ℝ, E) (cover.base i)).symm z) = 0
        rw [hzero]
        rfl
      rw [hcoord]
      simp [CalabiYau.Schauder.eContDiffHolderGaugeOn,
        CalabiYau.Schauder.eSupNormOn,
        CalabiYau.Schauder.eHolderSeminormOn]
      change eHolderNorm α (0 : cover.piece i → E [×k]→L[ℝ] ℝ) = 0
      exact eHolderNorm_zero (cover.piece i) α
    · exact bot_le

end KahlerForm
