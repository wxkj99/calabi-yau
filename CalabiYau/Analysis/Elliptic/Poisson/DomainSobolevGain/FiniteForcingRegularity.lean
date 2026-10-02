module

public import CalabiYau.Analysis.Elliptic.Poisson.DomainSobolevGain.ForcingSobolevSuccessor

/-!
# Descending forcing regularity along every finite direction sequence

The result descends forcing regularity along each finite direction sequence
from the initial forcing regularity and support assumptions. These hypotheses
come from finite-order regularity of the resolvent preimage.
-/

@[expose] public section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace CalabiYau.PoissonDomainRegularity

private theorem all_direction_sequences_of_base_and_snoc
    {ι : Type*} (r : ℕ) (P : (j : ℕ) → ℕ → (Fin j → ι) → Prop)
    (hbase : ∀ dirs : Fin 0 → ι, P 0 r dirs)
    (hstep : ∀ j, j < r → ∀ (dirs : Fin j → ι) (i : ι),
      P j (r - j) dirs → P (j + 1) (r - (j + 1)) (Fin.snoc dirs i)) :
    ∀ j, j ≤ r → ∀ dirs : Fin j → ι, P j (r - j) dirs := by
  intro j
  induction j with
  | zero =>
    intro _ dirs
    simpa only [Nat.sub_zero] using hbase dirs
  | succ j ih =>
    intro hj dirs
    have h := hstep j (Nat.lt_of_succ_le hj) (Fin.init dirs) (dirs (Fin.last j))
      (ih (Nat.le_of_succ_le hj) (Fin.init dirs))
    simpa only [Fin.snoc_init_self] using h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.Analysis.Laplacian
open Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- Raw forcing recursion in the same last-after-prefix order as the chosen mixed partials. -/
def iteratedChartForcing
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (initialForcing : EuclN → ℝ) :
    ∀ j : ℕ, (Fin j → Fin (Module.finrank ℝ E)) → EuclN → ℝ
  | 0, _ => initialForcing
  | j + 1, dirs => successorChartForcing g α u_h j (Fin.init dirs)
      (iteratedChartForcing g α u_h initialForcing j (Fin.init dirs)) (dirs (Fin.last j))

omit [NeZero (Module.finrank ℝ E)] in
/-- Fixed terminal order: the forcing at stage `j` has order `r - j`.
Only the current solution order `r + 1` is used, never the desired `r + 2`. -/
theorem iteratedChartForcing_memWkp_and_support
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (initialForcing : EuclN → ℝ) (r : ℕ)
    (h_initial_memWkp : Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) r 2 initialForcing
      (chartTargetEuclid (I := I) (M := M) α))
    (h_initial_ae_zero :
      initialForcing =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)))
    (h_current_solution : Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (r + 1) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α)) :
    ∀ j, j ≤ r → ∀ dirs : Fin j → Fin (Module.finrank ℝ E),
      Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) (r - j) 2
        (iteratedChartForcing g α u_h initialForcing j dirs)
        (chartTargetEuclid (I := I) (M := M) α) ∧
      iteratedChartForcing g α u_h initialForcing j dirs
        =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartImagePOUTsupport (I := I) (M := M) α)]
          (fun _ : EuclN => (0 : ℝ)) := by
  refine all_direction_sequences_of_base_and_snoc r
    (fun j k dirs =>
      Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) k 2
        (iteratedChartForcing g α u_h initialForcing j dirs)
        (chartTargetEuclid (I := I) (M := M) α) ∧
      iteratedChartForcing g α u_h initialForcing j dirs
        =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartImagePOUTsupport (I := I) (M := M) α)]
          (fun _ : EuclN => (0 : ℝ))) ?_ ?_
  · intro dirs
    exact ⟨h_initial_memWkp, h_initial_ae_zero⟩
  · intro j hj dirs l hprev
    have h_order : r - j = (r - (j + 1)) + 1 := by omega
    have h_solution_order : j + 2 + (r - (j + 1)) = r + 1 := by omega
    have h_prev := hprev.1
    rw [h_order] at h_prev
    have h_solution : Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E)
        (j + 2 + (r - (j + 1))) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α) := by
      simpa only [h_solution_order] using h_current_solution
    constructor
    · simpa only [iteratedChartForcing, Fin.init_snoc, Fin.snoc_last] using
        successorChartForcing_memWkp g α u_h j (r - (j + 1)) dirs
          (iteratedChartForcing g α u_h initialForcing j dirs) l h_prev hprev.2 h_solution
    · simpa only [iteratedChartForcing, Fin.init_snoc, Fin.snoc_last] using
        successorChartForcing_ae_zero_off_support g α u_h j dirs
          (iteratedChartForcing g α u_h initialForcing j dirs) l

end CalabiYau.PoissonDomainRegularity
