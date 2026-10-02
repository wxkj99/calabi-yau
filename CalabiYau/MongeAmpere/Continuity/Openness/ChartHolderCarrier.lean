module

public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderCarrier.Basic
public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderCarrier.SmoothGaugeFiniteness
public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderCarrier.SmoothGaugeDefiniteness
public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderCarrier.SmoothGaugeTriangle
public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderCarrier.SmoothGaugeScalar

/-!
# Normed structure on the smooth finite-chart Hölder core

Assemble the finiteness, definiteness, triangle, and scalar laws to obtain the
concrete gauge normed space.
-/

@[expose] public section

noncomputable section

open scoped Manifold ContDiff NNReal ENNReal Topology

namespace KahlerForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Existence of the gauge normed structure on the actual smooth-function core. The finite-gauge
field, norm formula, and operation-coherence fields rule out infinite gauges and twisted algebra
structures. -/
theorem exists_smoothChartHolderNormedData
    (cover : CompactChartCover E M) (k : ℕ) (α : ℝ≥0)
    (hα₀ : 0 < α) (hα₁ : α < 1) :
    Nonempty (SmoothChartHolderNormedData cover k α) := by
  have hfinite : ∀ f : SmoothChartHolderCore cover k α,
      HasFiniteChartHolderGauge cover k α f.smoothMap :=
    fun f => smoothChartHolderGauge_finite cover k α hα₀ hα₁ f
  have hcore : NormedSpace.Core ℝ (SmoothChartHolderCore cover k α) := by
    refine {
      norm_nonneg := ?_
      norm_smul := ?_
      norm_triangle := ?_
      norm_eq_zero_iff := ?_
    }
    · intro f
      change 0 ≤ (smoothChartHolderGauge cover k α f).toReal
      exact ENNReal.toReal_nonneg
    · intro c f
      change (smoothChartHolderGauge cover k α (c • f)).toReal =
        ‖c‖ * (smoothChartHolderGauge cover k α f).toReal
      rw [smoothChartHolderGauge_smul, ENNReal.toReal_mul]
      rfl
    · intro f g
      change (smoothChartHolderGauge cover k α (f + g)).toReal ≤
        (smoothChartHolderGauge cover k α f).toReal +
          (smoothChartHolderGauge cover k α g).toReal
      have hf : smoothChartHolderGauge cover k α f < ⊤ := by
        exact hfinite f
      have hg : smoothChartHolderGauge cover k α g < ⊤ := by
        exact hfinite g
      have hfne : smoothChartHolderGauge cover k α f ≠ ⊤ := ne_of_lt hf
      have hgne : smoothChartHolderGauge cover k α g ≠ ⊤ := ne_of_lt hg
      have hsumne : smoothChartHolderGauge cover k α f +
          smoothChartHolderGauge cover k α g ≠ ⊤ :=
        ENNReal.add_ne_top.mpr ⟨hfne, hgne⟩
      exact (ENNReal.toReal_mono hsumne
        (smoothChartHolderGauge_add_le cover k α f g)).trans_eq
        (ENNReal.toReal_add hfne hgne)
    · intro f
      change (smoothChartHolderGauge cover k α f).toReal = 0 ↔ f = 0
      constructor
      · intro h
        have hGauge : smoothChartHolderGauge cover k α f = 0 :=
          (ENNReal.toReal_eq_zero_iff _).mp h |>.resolve_right (ne_of_lt (hfinite f))
        exact (smoothChartHolderGauge_eq_zero_iff cover k α f).mp hGauge
      · intro hf
        subst f
        have hzero : smoothChartHolderGauge cover k α
            (0 : SmoothChartHolderCore cover k α) = 0 := by
          simpa using smoothChartHolderGauge_smul cover k α (0 : ℝ)
            (0 : SmoothChartHolderCore cover k α)
        exact congrArg ENNReal.toReal hzero
  exact ⟨{ finiteGauge := hfinite, normedCore := hcore }⟩

end KahlerForm
