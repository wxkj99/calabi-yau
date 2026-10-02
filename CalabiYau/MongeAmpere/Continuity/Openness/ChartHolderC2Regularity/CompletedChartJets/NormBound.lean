module

public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderJets

/-!
# Completed coordinate-jet norm bound

The canonical chart-jet extension is continuous with operator norm at most one in the finite-chart
gauge, so each pointwise completed jet is bounded by the completion norm.
-/

@[expose] public section

noncomputable section

open scoped Manifold ContDiff NNReal Topology

namespace KahlerForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]

/-- The canonical completed chart jet is pointwise bounded by the little-Hölder norm, for every
exponent when the normed data is supplied. -/
theorem smoothChartHolderCompletedJetNormBound
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover 2 α)
    (u : LittleHolder cover 2 α N)
    (j : ℕ) (hj : j ≤ 2) (i) (z : E)
    (hz : z ∈ interior (cover.piece i)) :
    ‖smoothChartHolderJetCanonicalExtension cover 2 α N j hj u i
      ⟨z, interior_subset hz⟩‖ ≤ ‖u‖ := by
  letI : NormedAddCommGroup (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedAddCommGroup cover 2 α N
  letI : NormedSpace ℝ (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedSpace cover 2 α N
  let T := smoothChartHolderJetCanonicalContinuousLinearMap cover 2 α N j hj
  let K := T.fromCompletion
  have hT : ‖T‖ ≤ 1 := by
    dsimp [T, smoothChartHolderJetCanonicalContinuousLinearMap]
    let h := exists_smoothChartHolderJetLinearMap cover 2 α N j hj
    let J := Classical.choose h
    have hJ : ∀ f, ‖J f‖ ≤ (smoothChartHolderGauge cover 2 α f).toReal :=
      Classical.choose_spec h |>.1
    change ‖smoothChartHolderJetContinuousLinearMap cover 2 α N j J hJ‖ ≤ 1
    dsimp [smoothChartHolderJetContinuousLinearMap]
    letI : NormedAddCommGroup (SmoothChartHolderCore cover 2 α) :=
      smoothChartHolderCoreNormedAddCommGroup cover 2 α N
    letI : NormedSpace ℝ (SmoothChartHolderCore cover 2 α) :=
      smoothChartHolderCoreNormedSpace cover 2 α N
    exact LinearMap.mkContinuous_norm_le J zero_le_one (fun f => by
      calc
        ‖J f‖ ≤ (smoothChartHolderGauge cover 2 α f).toReal := hJ f
        _ = ‖f‖ := (smoothChartHolderCore_norm_eq_gauge cover 2 α N f).symm
        _ = 1 * ‖f‖ := by ring)
  have hK : ∀ v : LittleHolder cover 2 α N, ‖K v‖ ≤ ‖v‖ := by
    intro v
    change ‖T.fromCompletion v‖ ≤ ‖v‖
    refine UniformSpace.Completion.induction_on v
      (isClosed_le (by fun_prop) (by fun_prop)) ?_
    intro f
    simpa only [ContinuousLinearMap.fromCompletion_apply_coe,
      UniformSpace.Completion.norm_coe, one_mul] using T.le_of_opNorm_le hT f
  change ‖K u i ⟨z, interior_subset hz⟩‖ ≤ ‖u‖
  calc
    ‖K u i ⟨z, interior_subset hz⟩‖ ≤ ‖K u i‖ :=
      (K u i).norm_coe_le_norm ⟨z, interior_subset hz⟩
    _ ≤ ‖K u‖ := norm_le_pi_norm (K u) i
    _ ≤ ‖u‖ := hK u

end KahlerForm
