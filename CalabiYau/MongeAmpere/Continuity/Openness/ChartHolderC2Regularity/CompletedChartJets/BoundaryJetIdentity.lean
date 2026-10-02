module

public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderEvaluation
public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderJets
import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderC2Regularity.CompletedChartJets.TransitionJetCompatibility

/-!
# Completed chart jets on every compact-piece point

Uniform convergence of the smooth-core chart jets gives the identity on all of a compact chart
piece. At points not in the interior of that piece, use a different chart whose interior contains
the corresponding manifold point, then compare coordinate jets across the smooth chart transition.
-/

@[expose] public section

noncomputable section

open scoped Manifold ContDiff NNReal Topology

namespace KahlerForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]

/-- Every chart-coordinate derivative through order two of the completed evaluation equals its
canonical completed chart jet at every point of a compact chart piece, including points outside the
piece's interior. The boundary case uses another member of the cover whose interior contains the
corresponding manifold point and the smooth transition between the two charts. -/
theorem smoothChartHolderCompletedBoundaryJetIdentity
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover 2 α)
    (u : LittleHolder cover 2 α N)
    (j : ℕ) (hj : j ≤ 2) (i : cover.ι) (z : E)
    (hz : z ∈ cover.piece i) :
    iteratedFDeriv ℝ j
      ((smoothChartHolderContinuousMapExtension cover 2 α N u : M → ℝ) ∘
        (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z =
      smoothChartHolderJetCanonicalExtension cover 2 α N j hj u i ⟨z, hz⟩ := by
  let : NormedAddCommGroup (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedAddCommGroup cover 2 α N
  let : NormedSpace ℝ (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedSpace cover 2 α N
  cases j with
  | zero =>
      have hj0 : 0 ≤ 2 := by omega
      let p := extChartAt 𝓘(ℝ, E) (cover.base i)
      let A : LittleHolder cover 2 α N → E [×0]→L[ℝ] ℝ := fun v =>
        (continuousMultilinearCurryFin0 ℝ E ℝ).symm
          (smoothChartHolderContinuousMapExtension cover 2 α N v (p.symm z))
      let B : LittleHolder cover 2 α N → E [×0]→L[ℝ] ℝ := fun v =>
        smoothChartHolderJetCanonicalExtension cover 2 α N 0 hj0 v i ⟨z, hz⟩
      have hA : Continuous A := by
        fun_prop
      have hB : Continuous B := by
        fun_prop
      have hclosed : IsClosed {v : LittleHolder cover 2 α N | A v = B v} :=
        isClosed_eq hA hB
      have hcore : ∀ f : SmoothChartHolderCore cover 2 α, A f = B f := by
        intro f
        simp [A, B, p, smoothChartHolderContinuousMapExtension_coe,
          smoothChartHolderJetCanonicalExtension_coe, smoothChartHolderJetData,
          iteratedFDeriv_zero_eq_comp]; rfl
      have hEq : A u = B u :=
        UniformSpace.Completion.induction_on u hclosed hcore
      simpa only [A, B, iteratedFDeriv_zero_eq_comp, Function.comp_apply] using hEq
  | succ j =>
      let x := (extChartAt 𝓘(ℝ, E) (cover.base i)).symm z
      obtain ⟨k, q, hq, hqpoint⟩ := cover.interior_covers x
      have hoverlap :
          (extChartAt 𝓘(ℝ, E) (cover.base i)).symm z =
            (extChartAt 𝓘(ℝ, E) (cover.base k)).symm q := by
        simpa [x] using hqpoint.symm
      have hcompat := smoothChartHolderCompletedTransitionJetCompatibility
        cover α N u i k z q hz hq hoverlap
      rcases hcompat with ⟨hactual1, hcanonical1, hactual2, hcanonical2⟩
      cases j with
      | zero =>
          change iteratedFDeriv ℝ 1
              ((smoothChartHolderContinuousMapExtension cover 2 α N u : M → ℝ) ∘
                (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z =
            smoothChartHolderJetCanonicalExtension cover 2 α N 1 (by omega) u i
              ⟨z, hz⟩
          ext m
          exact (hactual1 m).trans (hcanonical1 m).symm
      | succ j =>
          cases j with
          | zero =>
              change iteratedFDeriv ℝ 2
                  ((smoothChartHolderContinuousMapExtension cover 2 α N u : M → ℝ) ∘
                    (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z =
                smoothChartHolderJetCanonicalExtension cover 2 α N 2 le_rfl u i
                  ⟨z, hz⟩
              ext m
              exact (hactual2 m).trans (hcanonical2 m).symm
          | succ j => omega

end KahlerForm
