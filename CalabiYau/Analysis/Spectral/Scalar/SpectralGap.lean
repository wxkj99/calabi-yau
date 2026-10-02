-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Spectral/Scalar/SpectralGap.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Spectral.Scalar.Enumeration

@[expose] public section

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace CalabiYau.Laplacian

open CalabiYau.Analysis.Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

theorem exists_pos_le_nonzeroLaplacianEigenvalueSet
    (g : SmoothRiemannianMetric I M) :
    ∃ c : ℝ, 0 < c ∧
      ∀ lam ∈ nonzeroLaplacianEigenvalueSet (I := I) (M := M) g, c ≤ lam := by
  by_cases hne : (nonzeroLaplacianEigenvalueSet (I := I) (M := M) g).Nonempty
  · by_cases hinf : (nonzeroLaplacianEigenvalueSet (I := I) (M := M) g).Infinite
    · refine ⟨laplacianEigenvalueAscending (I := I) (M := M) g 0, ?_, ?_⟩
      · exact nonzeroLaplacianEigenvalueSet_pos (I := I) (M := M) g
          (laplacianEigenvalueAscending_mem_of_infinite (I := I) (M := M) g hinf 0)
      · intro lam hlam
        rw [laplacianEigenvalueAscending_zero_eq_sInf (I := I) (M := M) g hne]
        exact csInf_le
          ⟨0, fun x hx => (nonzeroLaplacianEigenvalueSet_pos (I := I) (M := M) g hx).le⟩ hlam
    · have hfin : (nonzeroLaplacianEigenvalueSet (I := I) (M := M) g).Finite := by
        simpa using hinf
      have hfinne : hfin.toFinset.Nonempty := by
        rwa [Set.Finite.toFinset_nonempty]
      refine ⟨hfin.toFinset.min' hfinne, ?_, ?_⟩
      · have hmem : hfin.toFinset.min' hfinne ∈
            nonzeroLaplacianEigenvalueSet (I := I) (M := M) g := by
          rw [← Set.Finite.mem_toFinset]
          exact Finset.min'_mem _ _
        exact nonzeroLaplacianEigenvalueSet_pos (I := I) (M := M) g hmem
      · intro lam hlam
        exact Finset.min'_le _ _ (by rwa [Set.Finite.mem_toFinset])
  · exact ⟨1, one_pos, fun lam hlam => absurd ⟨lam, hlam⟩ hne⟩

end CalabiYau.Laplacian

end
