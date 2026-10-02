module

public import CalabiYau.MongeAmpere.Continuity.Openness.LaplacianInverse.GlobalSchauder.LocalEstimate

/-!
# Uniform order-two bound for a normalized sequence

The local order-two Schauder estimate bounds every finite-chart order-two gauge once the input
functions are pointwise bounded by one and their finite order-zero Laplacian gauges tend to zero.
A convergent real sequence is bounded, including its finite initial segment.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology
open MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
/-- Local Schauder plus bounded input gives one finite bound for the entire normalized sequence.
The vanishing-gauge premise is needed to bound even the initial order-zero gauges. -/
theorem exists_uniform_normalized_laplacian_C2_gauge_bound
    (ω₁ : KahlerForm n M) (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (α : ℝ≥0) (hLocal : HasFiniteChartLocalLaplacianHolderEstimate ω₁ cover α)
    (u : ℕ → M → ℝ)
    (huSmooth : ∀ j, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (u j))
    (huBound : ∀ j x, |u j x| ≤ 1)
    (huFinite : ∀ j, finiteChartHolderGauge cover 0 α (ω₁.laplacian (u j)) < ⊤)
    (huSmall : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ j, N ≤ j →
      (finiteChartHolderGauge cover 0 α (ω₁.laplacian (u j))).toReal < ε) :
    ∃ B : ℝ≥0, ∀ j,
      finiteChartHolderGauge cover 2 α (u j) < ⊤ ∧
      (finiteChartHolderGauge cover 2 α (u j)).toReal ≤ (B : ℝ) := by
  classical
  let q : ℕ → ℝ := fun j =>
    (finiteChartHolderGauge cover 0 α (ω₁.laplacian (u j))).toReal
  have hq_nonneg (j : ℕ) : 0 ≤ q j := by
    dsimp [q]
    exact ENNReal.toReal_nonneg
  obtain ⟨N, hN⟩ := huSmall 1 (by norm_num)
  let Bprefix : ℝ := ∑ k ∈ Finset.range N, max 0 (q k)
  have hBprefix_nonneg : 0 ≤ Bprefix := by
    dsimp [Bprefix]
    positivity
  have hq_le_prefix_or_tail (j : ℕ) : q j ≤ Bprefix + 1 := by
    by_cases hj : j < N
    · have hmem : j ∈ Finset.range N := Finset.mem_range.mpr hj
      have hsum : max 0 (q j) ≤
          ∑ k ∈ Finset.range N, max 0 (q k) :=
        Finset.single_le_sum (fun k hk => le_max_left 0 (q k)) hmem
      dsimp [Bprefix]
      calc
        q j ≤ max 0 (q j) := le_max_right 0 (q j)
        _ ≤ ∑ k ∈ Finset.range N, max 0 (q k) := hsum
        _ ≤ (∑ k ∈ Finset.range N, max 0 (q k)) + 1 := by linarith
    · have hNj : N ≤ j := Nat.le_of_not_gt hj
      have hsmall := hN j hNj
      dsimp [q] at hsmall ⊢
      linarith [hBprefix_nonneg]
  let B₀ : ℝ≥0 := ⟨Bprefix + 1, by linarith [hBprefix_nonneg]⟩
  have hq_le (j : ℕ) : q j ≤ (B₀ : ℝ) := by
    change q j ≤ Bprefix + 1
    exact hq_le_prefix_or_tail j
  obtain ⟨C, hC⟩ := hLocal
  let B : ℝ≥0 := C * (B₀ + 1)
  refine ⟨B, ?_⟩
  intro j
  have _ : finiteChartHolderGauge cover 0 α (ω₁.laplacian (u j)) < ⊤ := huFinite j
  have hEst := hC (u j) (huSmooth j) 1 (by
    intro x
    exact huBound j x)
  obtain ⟨hGauge₂, _hLapGauge, hEstimate⟩ := hEst
  refine ⟨hGauge₂, ?_⟩
  have hqadd : q j + 1 ≤ (B₀ : ℝ) + 1 := by linarith [hq_le j]
  have hmul := mul_le_mul_of_nonneg_left hqadd (show 0 ≤ (C : ℝ) by positivity)
  change (finiteChartHolderGauge cover 2 α (u j)).toReal ≤ (B : ℝ)
  calc
    (finiteChartHolderGauge cover 2 α (u j)).toReal ≤
        (C : ℝ) * ((finiteChartHolderGauge cover 0 α (ω₁.laplacian (u j))).toReal + 1) := by
      simpa using hEstimate
    _ ≤ (C : ℝ) * ((B₀ : ℝ) + 1) := by
      simpa [q] using hmul
    _ = (B : ℝ) := by simp [B]

end KahlerForm
