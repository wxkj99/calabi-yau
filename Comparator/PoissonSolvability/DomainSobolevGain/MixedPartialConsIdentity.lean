module

public import Comparator.PoissonSolvability.DomainSobolevGain.DifferentiatedData
public import Comparator.PoissonSolvability.DomainSobolevGain.WeakSchwarz

/-!
# Prepending a direction to a chosen mixed chart partial

`chosenMthMixedPartialChartPushedU` appends directions. Under chart `H^(m+1)`, putting the
new direction first agrees a.e. with differentiating the `m`-th chosen partial: weak
partial derivatives commute.

Port target: DifferentialGeometry at `7a48598d35109aa99d1cc678e2724c213cdf4ff3`,
`Iterated/NirenbergInterior/InteriorH2RelaxedHyp.lean`,
`chosenMthMixedPartialChartPushedU_cons_eq_chosenWeakPartial_chosenMthMixed_ae_weak`
(lines 50–210). `chosenWeakPartialOrZero_swap_ae_of_memWkp_two` (`WeakSchwarz`) is the
local commutation input.
-/

@[expose] public section

noncomputable section
open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace CalabiYau.PoissonDomainRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
open CalabiYau.RiemannianVolume CalabiYau.Analysis.Laplacian Sobolev.Chart Sobolev.Euclidean
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.LaplacianDomainChartData
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
private theorem chosenMthMixedPartialChartPushedU_memWkp_of_chartPushed_memWkp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ) :
    ∀ (k : ℕ), MemWkp (d := Module.finrank ℝ E) (k + m) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) →
      ∀ (idx : Fin m → Fin (Module.finrank ℝ E)),
        MemWkp (d := Module.finrank ℝ E) k 2
          (chosenMthMixedPartialChartPushedU g α u_h m idx)
          (chartTargetEuclid (I := I) (M := M) α) := by
  induction m with
  | zero =>
      intro k h_parent idx
      simpa [chosenMthMixedPartialChartPushedU] using h_parent
  | succ m ih =>
      intro k h_parent idx
      have h_parent' : MemWkp (d := Module.finrank ℝ E) ((k + 1) + m) 2
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
            ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
          (chartTargetEuclid (I := I) (M := M) α) := by
        simpa only [Nat.add_assoc, Nat.add_comm 1 m] using h_parent
      exact (ih (k + 1) h_parent' (Fin.init idx)).chosenWeakPartial_mem
        (idx (Fin.last m))

private theorem fin_initial_cons_aux {α : Type*} {m : ℕ}
    (x : α) (p : Fin (m + 1) → α) :
    Fin.init (Fin.cons x p : Fin (m + 2) → α) = Fin.cons x (Fin.init p) := by
  funext j
  induction j using Fin.cases with
  | zero =>
      have h1 : (Fin.init (Fin.cons x p : Fin (m + 2) → α)) 0 = x := by
        simp [Fin.init]
      have h2 : (Fin.cons x (Fin.init p) : Fin (m + 1) → α) 0 = x := by simp
      rw [h1, h2]
  | succ k =>
      have h1 : (Fin.init (Fin.cons x p : Fin (m + 2) → α)) (Fin.succ k) =
          p k.castSucc := by simp [Fin.init, Fin.cons_succ]
      have h2 : (Fin.cons x (Fin.init p) : Fin (m + 1) → α) (Fin.succ k) =
          p k.castSucc := by simp [Fin.init, Fin.cons_succ]
      rw [h1, h2]

omit [NeZero (Module.finrank ℝ E)] in
private theorem chosenMthMixedPartialChartPushedU_succ
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ)
    (idx : Fin (m + 1) → Fin (Module.finrank ℝ E)) :
    chosenMthMixedPartialChartPushedU g α u_h (m + 1) idx =
      chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 (idx (Fin.last m))
        (chosenMthMixedPartialChartPushedU g α u_h m (Fin.init idx))
        (chartTargetEuclid (I := I) (M := M) α) := rfl

/-- Prepending direction `i` to an `m`-th chosen mixed partial is a.e. the chosen `i`-th
weak partial of that `m`-th partial. -/
theorem chosenMthMixedPartialChartPushedU_cons_ae_eq
    (g : SmoothRiemannianMetric I M) (α : M) (u_h : H1Compl (I := I) (M := M) g)
    (m : ℕ) (dirs : Fin m → Fin (Module.finrank ℝ E)) (i : Fin (Module.finrank ℝ E))
    (h_parent : MemWkp (d := Module.finrank ℝ E) (m + 1) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α)) :
    chosenMthMixedPartialChartPushedU g α u_h (m + 1) (Fin.cons i dirs) =ᵐ[
      (volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)]
    chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 i
      (chosenMthMixedPartialChartPushedU g α u_h m dirs)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  revert dirs i h_parent
  induction m with
  | zero =>
      intro dirs i h_parent
      have h_eq : chosenMthMixedPartialChartPushedU g α u_h 1 (Fin.cons i dirs) =
          chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 i
            (chosenMthMixedPartialChartPushedU g α u_h 0 dirs)
            (chartTargetEuclid (I := I) (M := M) α) := by
        rw [chosenMthMixedPartialChartPushedU_succ]
        have h_last : (Fin.cons i dirs : Fin 1 → _) (Fin.last 0) = i := rfl
        have h_initial : Fin.init (Fin.cons i dirs : Fin 1 → _) = dirs := by
          funext k
          exact k.elim0
        rw [h_last, h_initial]
      exact Filter.EventuallyEq.of_eq h_eq
  | succ m ih =>
      intro dirs i h_parent
      set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
      have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
      have h_last :
          (Fin.cons i dirs : Fin (m + 2) → Fin (Module.finrank ℝ E)) (Fin.last (m + 1)) =
            dirs (Fin.last m) := by simp
      have h_initial : Fin.init (Fin.cons i dirs : Fin (m + 2) →
          Fin (Module.finrank ℝ E)) = Fin.cons i (Fin.init dirs) :=
        fin_initial_cons_aux i dirs
      have h_lhs_unfold :
          chosenMthMixedPartialChartPushedU g α u_h (m + 2) (Fin.cons i dirs) =
            chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2
              (dirs (Fin.last m))
              (chosenMthMixedPartialChartPushedU g α u_h (m + 1)
                (Fin.cons i (Fin.init dirs))) Ω := by
        rw [chosenMthMixedPartialChartPushedU_succ, h_last, h_initial]
      have h_dirs_unfold :
          chosenMthMixedPartialChartPushedU g α u_h (m + 1) dirs =
            chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2
              (dirs (Fin.last m))
              (chosenMthMixedPartialChartPushedU g α u_h m (Fin.init dirs)) Ω := by
        rw [chosenMthMixedPartialChartPushedU_succ]
      have h_parent_for_ih : MemWkp (d := Module.finrank ℝ E) (m + 1) 2
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
            ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
          (chartTargetEuclid (I := I) (M := M) α) :=
        MemWkp.le_of_le (by omega) h_parent
      have h_ih := ih (Fin.init dirs) i h_parent_for_ih
      have h_propagate :
          chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 (dirs (Fin.last m))
              (chosenMthMixedPartialChartPushedU g α u_h (m + 1)
                (Fin.cons i (Fin.init dirs))) Ω =ᵐ[(volume : Measure EuclN).restrict Ω]
          chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 (dirs (Fin.last m))
              (chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 i
                (chosenMthMixedPartialChartPushedU g α u_h m (Fin.init dirs)) Ω) Ω :=
        chosenWeakPartialOrZero_ae_congr (d := Module.finrank ℝ E)
          (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ih (dirs (Fin.last m))
      have h_inner_memWkp_2_2 : MemWkp (d := Module.finrank ℝ E) 2 2
          (chosenMthMixedPartialChartPushedU g α u_h m (Fin.init dirs)) Ω := by
        have h_2_m : (2 : ℕ) + m = m + 2 := by omega
        have h_parent_2_m : MemWkp (d := Module.finrank ℝ E) (2 + m) 2
            (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
              ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)) Ω := by
          rw [h_2_m]
          exact h_parent
        exact chosenMthMixedPartialChartPushedU_memWkp_of_chartPushed_memWkp
          g α u_h m 2 h_parent_2_m (Fin.init dirs)
      have h_swap :=
        CalabiYau.PoissonDomainRegularity.WeakSchwarz.chosenWeakPartialOrZero_swap_ae_of_memWkp_two
          hΩ_open h_inner_memWkp_2_2 i (dirs (Fin.last m))
      have h_final :
          chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 i
              (chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2
                (dirs (Fin.last m))
                (chosenMthMixedPartialChartPushedU g α u_h m (Fin.init dirs)) Ω) Ω =
            chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 i
              (chosenMthMixedPartialChartPushedU g α u_h (m + 1) dirs) Ω := by
        rw [← h_dirs_unfold]
      calc chosenMthMixedPartialChartPushedU g α u_h (m + 2) (Fin.cons i dirs)
          = chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2
              (dirs (Fin.last m))
              (chosenMthMixedPartialChartPushedU g α u_h (m + 1)
                (Fin.cons i (Fin.init dirs))) Ω := h_lhs_unfold
        _ =ᵐ[(volume : Measure EuclN).restrict Ω]
            chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2
              (dirs (Fin.last m))
              (chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 i
                (chosenMthMixedPartialChartPushedU g α u_h m (Fin.init dirs)) Ω) Ω := h_propagate
        _ =ᵐ[(volume : Measure EuclN).restrict Ω]
            chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 i
              (chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2
                (dirs (Fin.last m))
                (chosenMthMixedPartialChartPushedU g α u_h m (Fin.init dirs)) Ω) Ω := h_swap
        _ = chosenWeakPartialOrZero (d := Module.finrank ℝ E) 2 i
              (chosenMthMixedPartialChartPushedU g α u_h (m + 1) dirs) Ω := h_final

end CalabiYau.PoissonDomainRegularity
