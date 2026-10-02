module

public import CalabiYau.MongeAmpere.Continuity.Openness.SmoothBootstrap.SchauderFirstGain
public import CalabiYau.MongeAmpere.Continuity.Openness.SmoothBootstrap.SchauderInductionStep

/-!
# Assemble the regularity induction

The first nonzero-quotient Schauder step upgrades `C²` to `C³`.  Thereafter the higher-order
induction applies to derivatives which are already `C²`.  The finite-order tower gives smoothness;
the original positivity and Monge–Ampère equation are retained.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- Uniform difference-quotient Schauder estimates give the first `C²` to `C³` gain, and the
higher-order induction then gives smoothness. -/
theorem solvesMongeAmpereC2_smooth_of_differenceQuotientSchauderData
    (hSch : InteriorSchauderEstimate n)
    (ω₀ : KahlerForm n M) (α : ℝ≥0) (hα₀ : 0 < α) (hα₁ : α < 1)
    {G φ : M → ℝ}
    (hG : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G)
    (hφ : ω₀.SolvesMongeAmpereC2 G φ)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (hφGauge : HasFiniteChartHolderGauge cover 2 α φ)
    (hEquation : HasChartLogDetEquation ω₀ G φ)
    (hDifferenceQuotients : HasDifferenceQuotientSchauderData ω₀ G φ α) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ φ := by
  have hThree := solvesMongeAmpereC2_contMDiff_three_of_differenceQuotientSchauderData
    hSch ω₀ α hα₀ hα₁ hG hφ cover hφGauge hEquation hDifferenceQuotients
  have hfinite : ∀ k : ℕ,
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) k φ := by
    intro k
    induction k with
    | zero =>
        exact hφ.1.1.of_le (by norm_num)
    | succ k ih =>
        by_cases hk0 : k = 0
        · subst k
          exact hφ.1.1.of_le (by norm_num)
        by_cases hk1 : k = 1
        · subst k
          exact hφ.1.1
        by_cases hk2 : k = 2
        · subst k
          exact hThree
        have hk3 : 3 ≤ k := by omega
        have hnext := solvesMongeAmpereC2_contMDiff_succ_of_contMDiff
          hSch ω₀ hG hφ hEquation hk3 ih
        exact hnext.of_le (by
          exact_mod_cast (show k + 1 ≤ k + 1 by omega))
  exact contMDiff_infty.2 hfinite

end KahlerForm
