module

public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderJets

/-!
# Hölder control of completed chart jets

The finite-chart gauge bounds the sup norms of all jets and the Holder seminorm of the top jet on
each entire compact chart piece. Cauchy convergence and density pass both controls to the completion
without losing the norm constant, for every exponent including zero.
-/

@[expose] public section

noncomputable section

open scoped Manifold ContDiff NNReal ENNReal Topology

namespace KahlerForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]

omit [CompactSpace M] in
omit [FiniteDimensional ℝ E] in
/-- On a fixed compact chart piece, every completed jet through order two is bounded by the
completion norm, and the completed order-two jet retains the full Holder seminorm with that same
constant. The statement is conditional on the supplied normed data and includes α = 0. -/
theorem smoothChartHolderCompletedJetHolderWith
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover 2 α)
    (u : LittleHolder cover 2 α N) (i : cover.ι) :
    (∀ (j : ℕ) (hj : j ≤ 2) (z : cover.piece i),
      ‖smoothChartHolderJetCanonicalExtension cover 2 α N j hj u i z‖ ≤ ‖u‖) ∧
    HolderWith ‖u‖₊ α
      (fun z : cover.piece i =>
        smoothChartHolderJetCanonicalExtension cover 2 α N 2 le_rfl u i z) := by
  let : NormedAddCommGroup (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedAddCommGroup cover 2 α N
  let : NormedSpace ℝ (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedSpace cover 2 α N
  let T := smoothChartHolderJetCanonicalContinuousLinearMap cover 2 α N 2 le_rfl
  let K := T.fromCompletion
  have hT : ‖T‖ ≤ 1 := by
    dsimp [T, smoothChartHolderJetCanonicalContinuousLinearMap]
    let h := exists_smoothChartHolderJetLinearMap cover 2 α N 2 le_rfl
    let J := Classical.choose h
    have hJ : ∀ f, ‖J f‖ ≤ (smoothChartHolderGauge cover 2 α f).toReal :=
      Classical.choose_spec h |>.1
    change ‖smoothChartHolderJetContinuousLinearMap cover 2 α N 2 J hJ‖ ≤ 1
    dsimp [smoothChartHolderJetContinuousLinearMap]
    let : NormedAddCommGroup (SmoothChartHolderCore cover 2 α) :=
      smoothChartHolderCoreNormedAddCommGroup cover 2 α N
    let : NormedSpace ℝ (SmoothChartHolderCore cover 2 α) :=
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
  have hcoreHolder (f : SmoothChartHolderCore cover 2 α) :
      HolderWith ‖(f : LittleHolder cover 2 α N)‖₊ α
        (fun z : cover.piece i => K (f : LittleHolder cover 2 α N) i z) := by
    have hfinite : smoothChartHolderGauge cover 2 α f ≠ ⊤ :=
      (N.finiteGauge f).ne_top
    have hpiece' :
        CalabiYau.Schauder.eContDiffHolderGaugeOn 2 α (cover.piece i)
          (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) ≤
          smoothChartHolderGauge cover 2 α f := by
      change CalabiYau.Schauder.eContDiffHolderGaugeOn 2 α (cover.piece i)
          (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) ≤
        (⨆ q : cover.ι,
          CalabiYau.Schauder.eContDiffHolderGaugeOn 2 α (cover.piece q)
            (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base q)).symm))
      exact le_iSup
        (fun q : cover.ι =>
          CalabiYau.Schauder.eContDiffHolderGaugeOn 2 α (cover.piece q)
            (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base q)).symm)) i
    have hpiece :
        CalabiYau.Schauder.eContDiffHolderGaugeOn 2 α (cover.piece i)
          (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) ≤
          (smoothChartHolderGauge cover 2 α f).toNNReal :=
      hpiece'.trans ((ENNReal.coe_toNNReal hfinite).symm.le)
    have hholder := CalabiYau.Schauder.topSpatialJet_holderWith_restrict hpiece
    have hholder' : HolderWith (smoothChartHolderGauge cover 2 α f).toNNReal α
        (fun z : cover.piece i =>
          iteratedFDeriv ℝ 2
            (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z) :=
      (HolderWith.restrict_iff.mp hholder).holderWith
    have hnorm : (smoothChartHolderGauge cover 2 α f).toNNReal =
        ‖(f : LittleHolder cover 2 α N)‖₊ := by
      apply NNReal.coe_injective
      rw [ENNReal.coe_toNNReal_eq_toReal, coe_nnnorm,
        UniformSpace.Completion.norm_coe]
      exact (smoothChartHolderCore_norm_eq_gauge cover 2 α N f).symm
    rw [← hnorm]
    have hcoe : K (f : LittleHolder cover 2 α N) = T f := by
      simp [K]
    have hTfun : (fun z : cover.piece i => T f i z) =
        (fun z : cover.piece i =>
          iteratedFDeriv ℝ 2
            (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z) := by
      funext z
      change smoothChartHolderJetCanonicalContinuousLinearMap cover 2 α N
        2 le_rfl f i z = _
      rw [smoothChartHolderJetCanonicalContinuousLinearMap_apply]
      rfl
    simpa only [hcoe, hTfun] using hholder'
  have hEval (z : cover.piece i) :
      Continuous (fun v : LittleHolder cover 2 α N => K v i z) := by
    fun_prop
  have hNorm : Continuous (fun v : LittleHolder cover 2 α N =>
      (‖v‖₊ : ℝ≥0∞)) := by
    fun_prop
  have hHolderClosed : IsClosed {v : LittleHolder cover 2 α N |
      HolderWith ‖v‖₊ α (fun z : cover.piece i => K v i z)} := by
    have hEq : {v : LittleHolder cover 2 α N |
        HolderWith ‖v‖₊ α (fun z : cover.piece i => K v i z)} =
        ⋂ p : cover.piece i × cover.piece i,
          {v : LittleHolder cover 2 α N |
            edist (K v i p.1) (K v i p.2) ≤
              (‖v‖₊ : ℝ≥0∞) * edist p.1 p.2 ^ (α : ℝ)} := by
      ext v
      simp only [Set.mem_ofPred_eq, HolderWith, Set.mem_iInter, Prod.forall]
    rw [hEq]
    apply isClosed_iInter
    intro p
    apply isClosed_le
    · exact continuous_edist.comp ((hEval p.1).prodMk (hEval p.2))
    · have hconst : edist p.1 p.2 ^ (α : ℝ) ≠ (⊤ : ℝ≥0∞) := by
        rw [edist_dist]
        exact (ENNReal.rpow_lt_top_of_nonneg α.coe_nonneg ENNReal.ofReal_ne_top).ne
      exact (ENNReal.continuous_mul_const hconst).comp hNorm
  have hholder : HolderWith ‖u‖₊ α (fun z : cover.piece i => K u i z) :=
    UniformSpace.Completion.induction_on u hHolderClosed hcoreHolder
  have hjet : ∀ (j : ℕ) (hj : j ≤ 2) (z : cover.piece i),
      ‖smoothChartHolderJetCanonicalExtension cover 2 α N j hj u i z‖ ≤ ‖u‖ := by
    intro j hj z
    let Tj := smoothChartHolderJetCanonicalContinuousLinearMap cover 2 α N j hj
    let Kj := Tj.fromCompletion
    have hTj : ‖Tj‖ ≤ 1 := by
      dsimp [Tj, smoothChartHolderJetCanonicalContinuousLinearMap]
      let h := exists_smoothChartHolderJetLinearMap cover 2 α N j hj
      let J := Classical.choose h
      have hJ : ∀ f, ‖J f‖ ≤ (smoothChartHolderGauge cover 2 α f).toReal :=
        Classical.choose_spec h |>.1
      change ‖smoothChartHolderJetContinuousLinearMap cover 2 α N j J hJ‖ ≤ 1
      dsimp [smoothChartHolderJetContinuousLinearMap]
      exact LinearMap.mkContinuous_norm_le J zero_le_one (fun f => by
        calc
          ‖J f‖ ≤ (smoothChartHolderGauge cover 2 α f).toReal := hJ f
          _ = ‖f‖ := (smoothChartHolderCore_norm_eq_gauge cover 2 α N f).symm
          _ = 1 * ‖f‖ := by ring)
    have hKj : ‖Kj u‖ ≤ ‖u‖ := by
      change ‖Tj.fromCompletion u‖ ≤ ‖u‖
      refine UniformSpace.Completion.induction_on u
        (isClosed_le (by fun_prop) (by fun_prop)) ?_
      intro f
      simpa only [ContinuousLinearMap.fromCompletion_apply_coe,
        UniformSpace.Completion.norm_coe, one_mul] using Tj.le_of_opNorm_le hTj f
    change ‖Kj u i z‖ ≤ ‖u‖
    calc
      ‖Kj u i z‖ ≤ ‖Kj u i‖ := (Kj u i).norm_coe_le_norm z
      _ ≤ ‖Kj u‖ := norm_le_pi_norm (Kj u) i
      _ ≤ ‖u‖ := hKj
  refine ⟨hjet, ?_⟩
  simpa only [K, T, smoothChartHolderJetCanonicalExtension] using hholder

end KahlerForm
