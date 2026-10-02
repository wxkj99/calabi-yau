module
public import Comparator.PoissonSolvability.DomainSobolevGain.DifferentiatedData
public import CalabiYau.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev

/-!
# Reconstruction from chosen mixed chart derivatives

Adapted from DifferentialGeometry at `7a48598d35109aa99d1cc678e2724c213cdf4ff3`,
`Iterated/Bootstrap/ChartHm.lean` lines 144–245 and 263–309.
The recursive Sobolev bookkeeping appends the last direction; no commutation is used.
-/

@[expose] public section

noncomputable section
open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators RealInnerProductSpace ENNReal

namespace CalabiYau.PoissonDomainRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.Analysis.Laplacian
open CalabiYau.Laplacian.MetricExtension hiding chartTargetEuclid chartTargetEuclid_isOpen
open Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

 private theorem reconstruction_zero
    (g : SmoothRiemannianMetric I M) (α : M) (u_h : H1Compl (I := I) (M := M) g)
    (idx : Fin 0 → Fin (Module.finrank ℝ E)) :
    chosenMthMixedPartialChartPushedU g α u_h 0 idx =
      Sobolev.Chart.chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ) := rfl

private theorem reconstruction_succ
    (g : SmoothRiemannianMetric I M) (α : M) (u_h : H1Compl (I := I) (M := M) g)
    (m : ℕ) (idx : Fin (m + 1) → Fin (Module.finrank ℝ E)) :
    chosenMthMixedPartialChartPushedU g α u_h (m + 1) idx =
      Sobolev.Euclidean.chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2
        (idx (Fin.last m)) (chosenMthMixedPartialChartPushedU g α u_h m (Fin.init idx))
        (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α) := rfl

private theorem reconstruction_mixed_memWkp
    (g : SmoothRiemannianMetric I M) (α : M) (u_h : H1Compl (I := I) (M := M) g)
    (m : ℕ) :
    ∀ (k : ℕ), Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) (k + m) 2
      (Sobolev.Chart.chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α) →
      ∀ (idx : Fin m → Fin (Module.finrank ℝ E)),
      Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) k 2
        (chosenMthMixedPartialChartPushedU g α u_h m idx)
        (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α) := by
  induction m with
  | zero =>
      intro k h_parent idx
      simpa [reconstruction_zero] using h_parent
  | succ m ih =>
      intro k h_parent idx
      have h_parent' : Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) ((k + 1) + m) 2
          (Sobolev.Chart.chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
            ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
          (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α) := by
        simpa only [Nat.add_assoc, Nat.add_comm 1 m] using h_parent
      have h_inner := ih (k + 1) h_parent' (Fin.init idx)
      rw [reconstruction_succ]
      exact h_inner.chosenWeakPartial_mem (idx (Fin.last m))

private theorem chosenMthMixed_memWkp_of_chartH_at_all_multi_indices
    (g : SmoothRiemannianMetric I M) (α : M) (u_h : H1Compl (I := I) (M := M) g)
    (n_succ m : ℕ) (dirs : Fin m → Fin (Module.finrank ℝ E))
    (h_w1p_m : ∀ idx : Fin m → Fin (Module.finrank ℝ E),
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (chosenMthMixedPartialChartPushedU g α u_h m idx)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_memWkp_succ : ∀ idx : Fin (m + 1) → Fin (Module.finrank ℝ E),
      Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) (n_succ + 1) 2
        (chosenMthMixedPartialChartPushedU g α u_h (m + 1) idx)
        (chartTargetEuclid (I := I) (M := M) α)) :
    Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) (n_succ + 2) 2
      (chosenMthMixedPartialChartPushedU g α u_h m dirs)
      (chartTargetEuclid (I := I) (M := M) α) := by
  refine ⟨h_w1p_m dirs, ?_⟩
  intro i
  have h_next := h_memWkp_succ (Fin.snoc dirs i)
  simpa only [reconstruction_succ, Fin.snoc_last, Fin.init_snoc] using h_next

theorem chartPushed_memWkp_m_plus_two_of_mthMixed_chart_H_two
    (g : SmoothRiemannianMetric I M) (α : M) (u_h : H1Compl (I := I) (M := M) g) (m : ℕ)
    (h_intermediate_w1p : ∀ j : ℕ, j ≤ m → ∀ idx : Fin j → Fin (Module.finrank ℝ E),
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (chosenMthMixedPartialChartPushedU g α u_h j idx)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_top_memWkp_two : ∀ idx : Fin m → Fin (Module.finrank ℝ E),
      Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) 2 2
        (chosenMthMixedPartialChartPushedU g α u_h m idx)
        (chartTargetEuclid (I := I) (M := M) α)) :
    Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) (m + 2) 2
      (Sobolev.Chart.chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) := by
  suffices h : ∀ s j : ℕ, s + j = m → ∀ dirs : Fin j → Fin (Module.finrank ℝ E),
      Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) (s + 2) 2
        (chosenMthMixedPartialChartPushedU g α u_h j dirs)
        (chartTargetEuclid (I := I) (M := M) α) by
    have h_apply := h m 0 (by omega) Fin.elim0
    simpa [reconstruction_zero] using h_apply
  intro s
  induction s with
  | zero =>
      intro j hj dirs
      have hj_eq : j = m := by omega
      subst hj_eq
      exact h_top_memWkp_two dirs
  | succ s ih =>
      intro j hj dirs
      have hj_le_m : j ≤ m := by omega
      have hj_succ_in_m : s + (j + 1) = m := by omega
      have h_next : ∀ idx : Fin (j + 1) → Fin (Module.finrank ℝ E),
          Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) (s + 2) 2
            (chosenMthMixedPartialChartPushedU g α u_h (j + 1) idx)
            (chartTargetEuclid (I := I) (M := M) α) :=
        fun idx => ih (j + 1) hj_succ_in_m idx
      exact chosenMthMixed_memWkp_of_chartH_at_all_multi_indices
        g α u_h (s + 1) j dirs (h_intermediate_w1p j hj_le_m) h_next

theorem chartPushed_memWkp_m_plus_two_step
    (g : SmoothRiemannianMetric I M) (α : M) (u_h : H1Compl (I := I) (M := M) g) (m : ℕ)
    (h_chart_H_m_plus_1 : Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) (m + 1) 2
      (Sobolev.Chart.chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α))
    (h_top_memWkp_two : ∀ idx : Fin m → Fin (Module.finrank ℝ E),
      Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) 2 2
        (chosenMthMixedPartialChartPushedU g α u_h m idx)
        (chartTargetEuclid (I := I) (M := M) α)) :
    Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) (m + 2) 2
      (Sobolev.Chart.chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) := by
  apply chartPushed_memWkp_m_plus_two_of_mthMixed_chart_H_two g α u_h m ?_ h_top_memWkp_two
  intro j hj idx
  have h_parent : Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) (1 + j) 2
      (Sobolev.Chart.chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) :=
    h_chart_H_m_plus_1.le_of_le (by omega)
  exact (reconstruction_mixed_memWkp
    g α u_h j 1 h_parent idx).memW1p

end CalabiYau.PoissonDomainRegularity
