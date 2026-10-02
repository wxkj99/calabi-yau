module

public import Comparator.PoissonSolvability.DomainSobolevGain.NumeratorProductRegularity

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

open CalabiYau.RiemannianVolume CalabiYau.Analysis.Laplacian
open Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- Finite-order regularity of the actual numerator, before division by density. -/
theorem successorChartForcingNumerator_memWkp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m K : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (previousForcing : EuclN → ℝ) (l : Fin (Module.finrank ℝ E))
    (h_previous_memWkp : Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (K + 1) 2 previousForcing
      (chartTargetEuclid (I := I) (M := M) α))
    (h_previous_ae_zero :
      previousForcing =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)))
    (h_chart_H_u : Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 2 + K) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α)) :
    Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) K 2
      (successorChartForcingNumerator g α u_h m dirs previousForcing l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    successorChartForcingNumerator_product_layers_memWkp
      g α u_h m K dirs previousForcing l
      h_previous_memWkp h_previous_ae_zero h_chart_H_u
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hAB := Sobolev.Euclidean.MemWkp.add
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open hA hB
  have hABC := Sobolev.Euclidean.MemWkp.sub
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open hAB hC
  have hABCD := Sobolev.Euclidean.MemWkp.add
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open hABC hD
  have hABCDE := Sobolev.Euclidean.MemWkp.add
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open hABCD hE
  exact hABCDE

end CalabiYau.PoissonDomainRegularity
