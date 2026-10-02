module

public import CalabiYau.Analysis.Holder.Basic
public import CalabiYau.MongeAmpere.Continuity.Openness.CompactChartCover
public import CalabiYau.Geometry.Complex.Holder

/-!
# Finite-chart Hölder gauge

This file gives a concrete finite-chart gauge for scalar functions on a compact charted space.
The chart pieces are compact subsets of the corresponding extended-chart targets, and their
interiors cover the space. The gauge is the supremum over these finitely many charts of the sum of
the sup norms of all jets through order `k` and the Hölder seminorm of the top jet.

The gauge is the starting point for constructing the little-Hölder carriers used by the
continuity-method openness argument. The Banach completion and its evaluation theorem are developed separately.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal ENNReal Topology

namespace KahlerForm

attribute [instance] CompactChartCover.fintype_ι

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- The finite-chart `C^{k,α}` gauge: the maximum over the cover of the sup norms of jets through
order `k` and the `α`-Hölder seminorm of the order-`k` jet. Values are in `ℝ≥0∞` so unbounded
functions are represented by `⊤`. -/
noncomputable def finiteChartHolderGauge (cover : CompactChartCover E M)
    (k : ℕ) (α : ℝ≥0) (f : M → ℝ) : ℝ≥0∞ :=
  ⨆ i, CalabiYau.Schauder.eContDiffHolderGaugeOn k α (cover.piece i)
    (f ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm)

/-- Finiteness of the concrete finite-chart gauge. -/
def HasFiniteChartHolderGauge (cover : CompactChartCover E M)
    (k : ℕ) (α : ℝ≥0) (f : M → ℝ) : Prop :=
  finiteChartHolderGauge cover k α f < ⊤

/-- The chartwise boundedness condition represented by `finiteChartHolderGauge`. -/
def HolderBoundedOnChartCover (cover : CompactChartCover E M)
    (k : ℕ) (α : ℝ≥0) (f : M → ℝ) : Prop :=
  ∃ C : ℝ≥0, ∀ i,
    HolderBoundOn k α C (cover.piece i)
      (f ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm)

/-- A finite-chart gauge is finite exactly when its coordinate expressions have a common
`C^{k,α}` bound on all pieces of the chosen finite cover. -/
theorem finiteChartHolderGauge_lt_top_iff (cover : CompactChartCover E M)
    (k : ℕ) (α : ℝ≥0) (f : M → ℝ) :
    HasFiniteChartHolderGauge cover k α f ↔
      HolderBoundedOnChartCover cover k α f := by
  constructor
  · intro h
    let C : ℝ≥0 := (finiteChartHolderGauge cover k α f).toNNReal
    refine ⟨C, ?_⟩
    intro i
    have hi : CalabiYau.Schauder.eContDiffHolderGaugeOn k α (cover.piece i)
        (f ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) ≤ (C : ℝ≥0∞) := by
      calc
        _ ≤ finiteChartHolderGauge cover k α f := le_iSup _ i
        _ = C := (ENNReal.coe_toNNReal (ne_of_lt h)).symm
    exact ⟨(fun j hj z hz ↦ CalabiYau.Schauder.spatialJet_norm_le hi hj hz),
      HolderWith.restrict_iff.mp (CalabiYau.Schauder.topSpatialJet_holderWith_restrict hi)⟩
  · rintro ⟨C, hC⟩
    have hbound : finiteChartHolderGauge cover k α f ≤
        (∑ _j ∈ Finset.range (k + 1), (C : ℝ≥0∞)) + C := by
      unfold finiteChartHolderGauge
      apply iSup_le
      intro i
      exact CalabiYau.Schauder.eContDiffHolderGaugeOn_le (fun _ ↦ C) C
        (hC i).1 (HolderWith.restrict_iff.mpr (hC i).2)
    exact lt_of_le_of_lt hbound (by
      simpa using ENNReal.mul_lt_top (by simp : (k : ℝ≥0∞) + 1 < ⊤)
        (by simp : (C : ℝ≥0∞) < ⊤))

end KahlerForm
