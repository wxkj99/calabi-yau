module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceCurvatureDerivative.Basic
public import CalabiYau.MongeAmpere.Estimates.C3.CalabiEnergy.Basic
public import CalabiYau.Geometry.Kahler.Curvature.Chart.Basic
import Mathlib.Topology.Compactness.Compact

/-!
# Finite-cover bound for the centered reference curvature derivative

Only local bounds on open neighborhoods enter the compactness argument.
No continuity of the moving centered chart or selected frame is assumed.
Source: Székelyhidi, §3.3, proof of Lemma 3.9, printed pp. 44–45.
-/

public section

open scoped Manifold ContDiff

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [CompactSpace M]

/-- A finite subcover gives one finite nonnegative bound for every centered
reference-normalized frame. Empty manifolds and zero complex dimension are allowed. -/
theorem exists_uniform_c3_curvature_derivative_bound_of_local
    (ω₀ : KahlerForm n M)
    (hlocal : ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ U, ∀ (P : Matrix (Fin n) (Fin n) ℂ),
        P.transpose * ω₀.metricInChart y
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y) * P.map star = 1 →
          ∀ s p q j k : Fin n,
            ‖c3FiveSlotFrameContraction P
              (c3CovariantFourTensorZJet
                (c3ChristoffelInChart (ω₀.metricInChart y)
                  (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y))
                (chartCurvature (ω₀.metricInChart y)
                  (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y))
                (fun a b c d e => chartPartialZComplex
                  (fun w => chartCurvature (ω₀.metricInChart y) w b c d e)
                  (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y) a))
              s p q j k‖ ≤ B) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : M, ∀ (P : Matrix (Fin n) (Fin n) ℂ),
      P.transpose * ω₀.metricInChart x
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) * P.map star = 1 →
        ∀ s p q j k : Fin n,
          ‖c3FiveSlotFrameContraction P
            (c3CovariantFourTensorZJet
              (c3ChristoffelInChart (ω₀.metricInChart x)
                (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x))
              (chartCurvature (ω₀.metricInChart x)
                (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x))
              (fun a b c d e => chartPartialZComplex
                (fun w => chartCurvature (ω₀.metricInChart x) w b c d e)
                (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) a))
            s p q j k‖ ≤ B := by
  classical
  choose U hU hx hbound using hlocal
  choose B hB hestimate using hbound
  have hcover : (Set.univ : Set M) ⊆ ⋃ x : M, U x := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hx x⟩
  obtain ⟨t, ht⟩ := (isCompact_univ : IsCompact (Set.univ : Set M)).elim_finite_subcover
    U hU hcover
  refine ⟨∑ x ∈ t, B x, Finset.sum_nonneg (fun x _ => hB x), ?_⟩
  intro x P hP s p q j k
  obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact (hestimate y x hxy P hP s p q j k).trans
    (Finset.single_le_sum (fun z _ => hB z) hyt)

end KahlerForm
