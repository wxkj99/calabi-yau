module

public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderEvaluation
public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderC2Regularity.CompletedChartJets.Identity
public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderC2Regularity.CompletedChartJets.NormBound
public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderC2Regularity.CompletedChartJets.TopJetHolderBound
public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderMeanZero.C2GaugeClosability

/-!
# Faithfulness of order-two little-Hölder evaluation

Continuous evaluation observes values, while the order-two completion also retains its first and
second chart derivatives. Faithfulness therefore depends on closability of those derivative limits,
not an estimate of the full gauge by the sup norm.
-/

@[expose] public section

noncomputable section

open scoped Manifold ContDiff NNReal ENNReal Topology

namespace KahlerForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]

/-- Evaluation faithfully represents the order-two little-Hölder completion on a compact,
finite-dimensional manifold. The proof identifies the limiting chart derivatives on chart interiors
with derivatives of the evaluated limit, as in Gilbarg–Trudinger, §4.1, pp. 51–53, and Lunardi,
Proposition 0.2.1, pp. 4–5. The statement includes `α = 0`, and in particular the flat
one-dimensional chart. -/
theorem smoothChartHolderContinuousMapExtension_C2_injective
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover 2 α) :
    Function.Injective (smoothChartHolderContinuousMapExtension cover 2 α N) := by
  classical
  let : NormedAddCommGroup (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedAddCommGroup cover 2 α N
  let : NormedSpace ℝ (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedSpace cover 2 α N
  intro u v huv
  let F := smoothChartHolderContinuousMapExtension cover 2 α N
  have hker : F (u - v) = 0 := by
    dsimp [F]
    rw [map_sub, huv, sub_self]
  have happrox : ∀ n : ℕ, ∃ f : SmoothChartHolderCore cover 2 α,
      dist (f : LittleHolder cover 2 α N) (u - v) < (1 : ℝ) / (n + 1) := by
    intro n
    have hr : 0 < (1 : ℝ) / (n + 1) := by positivity
    obtain ⟨f, hfball⟩ :=
      UniformSpace.Completion.denseRange_coe.mem_nhds
        (Metric.ball_mem_nhds (u - v) hr)
    refine ⟨f, ?_⟩
    simpa [Metric.mem_ball] using hfball
  let f : ℕ → SmoothChartHolderCore cover 2 α := fun n => Classical.choose (happrox n)
  have hfapprox (n : ℕ) :
      dist (f n : LittleHolder cover 2 α N) (u - v) < (1 : ℝ) / (n + 1) :=
    Classical.choose_spec (happrox n)
  have hf_tendsto :
      Filter.Tendsto (fun n => (f n : LittleHolder cover 2 α N)) Filter.atTop
        (𝓝 (u - v)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨Nε, hNε⟩ := exists_nat_gt ε⁻¹
    refine ⟨Nε, ?_⟩
    intro n hn
    calc
      dist (f n : LittleHolder cover 2 α N) (u - v) < (1 : ℝ) / (n + 1) :=
        hfapprox n
      _ ≤ (1 : ℝ) / (Nε + 1) := by
        gcongr
      _ < ε := by
        apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (Nε : ℝ) + 1)).2
        have hmul := mul_lt_mul_of_pos_right hNε hε
        rw [inv_mul_cancel₀ (ne_of_gt hε)] at hmul
        nlinarith
  have hf_cauchy :
      CauchySeq (fun n => (f n : LittleHolder cover 2 α N)) := hf_tendsto.cauchySeq
  have hEval :
      Filter.Tendsto
        (fun n => smoothChartHolderContinuousMapLinearMap cover 2 α (f n))
        Filter.atTop (𝓝 0) := by
    have hcont : Filter.Tendsto (fun n => F (f n : LittleHolder cover 2 α N))
        Filter.atTop (𝓝 (F (u - v))) := by
      exact (F.continuous.tendsto (u - v)).comp hf_tendsto
    rw [hker] at hcont
    simpa only [F, smoothChartHolderContinuousMapExtension_coe] using hcont
  have hnormCore := smoothChartHolderCoreCauchySeq_tendsto_zero_of_uniformEvaluation_tendsto_zero
    cover α N f hf_cauchy hEval
  have hnormCompletion :
      Filter.Tendsto (fun n => ‖(f n : LittleHolder cover 2 α N)‖)
        Filter.atTop (𝓝 ‖u - v‖) := by
    exact (continuous_norm.tendsto (u - v)).comp hf_tendsto
  have hnormCompletionZero :
      Filter.Tendsto (fun n => ‖(f n : LittleHolder cover 2 α N)‖)
        Filter.atTop (𝓝 0) := by
    simpa using hnormCore
  have hnorm : ‖u - v‖ = 0 := by
    exact (tendsto_nhds_unique hnormCompletionZero hnormCompletion).symm
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

end KahlerForm
