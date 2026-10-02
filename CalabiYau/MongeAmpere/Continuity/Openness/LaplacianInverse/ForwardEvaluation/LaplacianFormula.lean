module

public import CalabiYau.MongeAmpere.Continuity.Openness.LaplacianInverse.ForwardEvaluation.SmoothCoreExtension
public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderC2Regularity.CompletedChartJets.Identity
public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderC2Regularity.CompletedChartJets.NormBound

/-!
# Pass the Kähler Laplacian formula through completion

The core extension identifies the completed forward map with the pointwise Kähler Laplacian
on the dense smooth mean-zero core. Extend this identity to every `P.C2` element using the
completed second-jet identity and norm bound supplied by the explicitly imported lower-level C2
regularity interfaces. The low-level statements are used here without restating them.

The flat complex-dimension-one check uses `Δω=(1/4)ΔR`: on `cos (2πx)` the formula is
`Δω cos (2πx)=-π² cos (2πx)`. The completion limit must retain the same sign and factor.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology

namespace KahlerForm

open Filter CalabiYau.Schauder

section CompletedRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]

omit [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] in
private theorem exists_smoothChartHolderCore_seq_tendsto
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover 2 α)
    (u : LittleHolder cover 2 α N) :
    ∃ fseq : ℕ → SmoothChartHolderCore cover 2 α,
      Filter.Tendsto (fun n => (fseq n : LittleHolder cover 2 α N))
        Filter.atTop (𝓝 u) := by
  let : NormedAddCommGroup (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedAddCommGroup cover 2 α N
  let : NormedSpace ℝ (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedSpace cover 2 α N
  have hmem : u ∈ closure (Set.range
      (fun f : SmoothChartHolderCore cover 2 α =>
        (f : LittleHolder cover 2 α N))) := UniformSpace.Completion.denseRange_coe u
  have hex (n : ℕ) : ∃ f : SmoothChartHolderCore cover 2 α,
      dist (f : LittleHolder cover 2 α N) u < (1 : ℝ) / (n + 1) := by
    have hn : 0 < (1 : ℝ) / (n + 1) := by positivity
    have hball := (Metric.mem_closure_iff.mp hmem) ((1 : ℝ) / (n + 1)) hn
    rcases hball with ⟨y, hy, hdist⟩
    rcases hy with ⟨f, rfl⟩
    exact ⟨f, by simpa [dist_comm] using hdist⟩
  let fseq : ℕ → SmoothChartHolderCore cover 2 α := fun n => Classical.choose (hex n)
  have hdist (n : ℕ) : dist (fseq n : LittleHolder cover 2 α N) u <
      (1 : ℝ) / (n + 1) := Classical.choose_spec (hex n)
  have hsmall : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) Filter.atTop
      (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine ⟨fseq, ?_⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hsmall.eventually (gt_mem_nhds hε)] with n hn
  exact (hdist n).trans hn

private theorem local_completed_C2_regularity
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover 2 α)
    (u : LittleHolder cover 2 α N) (x : M)
    (hJet : ∀ (j : ℕ) (hj : j ≤ 2) (i) (z : E)
      (hz : z ∈ interior (cover.piece i)),
      iteratedFDeriv ℝ j
        ((smoothChartHolderContinuousMapExtension cover 2 α N u : M → ℝ) ∘
          (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z =
        smoothChartHolderJetCanonicalExtension cover 2 α N j hj u i
          ⟨z, interior_subset hz⟩)
    (_hJetNorm : ∀ (j : ℕ) (hj : j ≤ 2) (i) (z : E)
      (hz : z ∈ interior (cover.piece i)),
      ‖smoothChartHolderJetCanonicalExtension cover 2 α N j hj u i
        ⟨z, interior_subset hz⟩‖ ≤ ‖u‖) :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) 2
      (smoothChartHolderContinuousMapExtension cover 2 α N u) x := by
  classical
  let : NormedAddCommGroup (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedAddCommGroup cover 2 α N
  let : NormedSpace ℝ (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedSpace cover 2 α N
  obtain ⟨fseq, hfseq⟩ :=
    exists_smoothChartHolderCore_seq_tendsto cover α N u
  obtain ⟨i, z, hz, hx⟩ := cover.interior_covers x
  let e := extChartAt 𝓘(ℝ, E) (cover.base i)
  let U : Set E := interior (cover.piece i)
  let F : E → ℝ := fun y =>
    (smoothChartHolderContinuousMapExtension cover 2 α N u : M → ℝ) (e.symm y)
  let fseq' : ℕ → E → ℝ := fun n =>
    (fseq n).smoothMap ∘ e.symm
  let Fzero : E → E [×0]→L[ℝ] ℝ := iteratedFDeriv ℝ 0 F
  let c0 : (E [×0]→L[ℝ] ℝ) ≃L[ℝ] ℝ :=
    (continuousMultilinearCurryFin0 ℝ E ℝ).toContinuousLinearEquiv
  let c1 := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 1 => E) ℝ
  let c2 := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => E) ℝ
  let Uopen : IsOpen U := isOpen_interior
  have hjetConv (j : ℕ) (hj : j ≤ 2) :
      Filter.Tendsto
        (fun n => smoothChartHolderJetCanonicalExtension cover 2 α N j hj
          (fseq n : LittleHolder cover 2 α N))
        Filter.atTop (𝓝 (smoothChartHolderJetCanonicalExtension cover 2 α N j hj u)) := by
    exact (smoothChartHolderJetCanonicalExtension cover 2 α N j hj).continuous.continuousAt.tendsto
      |>.comp hfseq
  have hjetUniform (j : ℕ) (hj : j ≤ 2) :
      TendstoUniformlyOn
        (fun n y => iteratedFDeriv ℝ j (fseq' n) y)
        (iteratedFDeriv ℝ j F) Filter.atTop U := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [(hjetConv j hj).eventually (Metric.ball_mem_nhds _ hε)] with n hn y hy
    have hyPiece : y ∈ cover.piece i := interior_subset hy
    have hcore (w : ℕ) :
        smoothChartHolderJetCanonicalExtension cover 2 α N j hj
          (fseq w : LittleHolder cover 2 α N) i ⟨y, hyPiece⟩ =
          iteratedFDeriv ℝ j (fseq' w) y := by
      rw [smoothChartHolderJetCanonicalExtension_coe]
      simp [fseq', e, smoothChartHolderJetData]
    have hlimit :
        smoothChartHolderJetCanonicalExtension cover 2 α N j hj u i ⟨y, hyPiece⟩ =
          iteratedFDeriv ℝ j F y := by
      change _ = iteratedFDeriv ℝ j
        ((smoothChartHolderContinuousMapExtension cover 2 α N u : M → ℝ) ∘ e.symm) y
      exact (hJet j hj i y hy).symm
    let Jn := smoothChartHolderJetCanonicalExtension cover 2 α N j hj
      (fseq n : LittleHolder cover 2 α N)
    let Ju := smoothChartHolderJetCanonicalExtension cover 2 α N j hj u
    have hn' : dist Jn Ju < ε := by
      simpa [Jn, Ju] using hn
    have hdist : ‖Jn - Ju‖ < ε := by
      simpa [dist_eq_norm] using hn'
    have hpoint : ‖(Ju i - Jn i) ⟨y, hyPiece⟩‖ ≤ ‖Ju i - Jn i‖ :=
      (Ju i - Jn i).norm_coe_le_norm ⟨y, hyPiece⟩
    calc
      dist (iteratedFDeriv ℝ j F y) (iteratedFDeriv ℝ j (fseq' n) y) =
          dist (Ju i ⟨y, hyPiece⟩) (Jn i ⟨y, hyPiece⟩) := by
        rw [← hlimit, ← hcore n]
      _ = ‖(Ju i - Jn i) ⟨y, hyPiece⟩‖ := by
        rw [dist_eq_norm, ContinuousMap.sub_apply]
      _ ≤ ‖Ju i - Jn i‖ := hpoint
      _ ≤ ‖Ju - Jn‖ := by
        change ‖(Ju - Jn) i‖ ≤ ‖Ju - Jn‖
        exact norm_le_pi_norm (Ju - Jn) i
      _ = ‖Jn - Ju‖ := norm_sub_rev _ _
      _ < ε := hdist
  have hjetLocally (j : ℕ) (hj : j ≤ 2) :
      TendstoLocallyUniformlyOn
        (fun n y => iteratedFDeriv ℝ j (fseq' n) y)
        (iteratedFDeriv ℝ j F) Filter.atTop U :=
    (hjetUniform j hj).tendstoLocallyUniformlyOn
  have hfnSmooth : ∀ n, ContDiffOn ℝ ∞ (fseq' n) e.target := by
    intro n
    have h := (contMDiff_iff.mp (fseq n).smoothMap.contMDiff).2 (cover.base i) 0
    simpa [fseq', e, extChartAt, chartAt_self_eq] using h
  have hfnZero : ∀ n, ContDiffOn ℝ ∞ (iteratedFDeriv ℝ 0 (fseq' n)) e.target := by
    intro n
    exact (c0.symm.contDiff.comp_contDiffOn (hfnSmooth n)).congr fun y => by
      simp [iteratedFDeriv_zero_eq_comp, fseq', e, c0]
  have hfg : ∀ y ∈ U,
      Filter.Tendsto (fun n => iteratedFDeriv ℝ 0 (fseq' n) y)
        Filter.atTop (𝓝 (Fzero y)) := by
    intro y hy
    exact (hjetUniform 0 (by omega)).tendsto_at hy
  have hc1 : LipschitzWith 1 c1 := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    rw [c1.dist_map]
    simp
  have hc2 : LipschitzWith 1 c2 := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    rw [c2.dist_map]
    simp
  have hconv1 : TendstoLocallyUniformlyOn
      (fun n y => c1 (iteratedFDeriv ℝ 1 (fseq' n) y))
      (fun y => c1 (iteratedFDeriv ℝ 1 F y)) Filter.atTop U :=
    hc1.uniformContinuous.comp_tendstoLocallyUniformlyOn
      (hjetLocally 1 (by omega))
  have hconv2 : TendstoLocallyUniformlyOn
      (fun n y => c2 (iteratedFDeriv ℝ 2 (fseq' n) y))
      (fun y => c2 (iteratedFDeriv ℝ 2 F y)) Filter.atTop U :=
    hc2.uniformContinuous.comp_tendstoLocallyUniformlyOn
      (hjetLocally 2 (by omega))
  have hfirstZero : ∀ y ∈ U,
      HasFDerivAt Fzero (c1 (iteratedFDeriv ℝ 1 F y)) y := by
    intro y hy
    refine hasFDerivAt_of_tendstoLocallyUniformlyOn Uopen hconv1 ?_ hfg hy
    intro n w hw
    have hAt := (hfnZero n).contDiffAt
      ((isOpen_extChartAt_target (cover.base i)).mem_nhds
        (cover.piece_in_target i (interior_subset hw)))
    have hklt : (↑(0 : ℕ) : ℕ∞ω) < ∞ := by simp
    have hhas := (hAt.differentiableAt (by simp)).hasFDerivAt
    have hfd := congrFun (fderiv_iteratedFDeriv (𝕜 := ℝ)
      (f := fseq' n) (n := 0)) w
    rw [hfd] at hhas
    exact hhas
  have hsecond : ∀ y ∈ U,
      HasFDerivAt (iteratedFDeriv ℝ 1 F) (c2 (iteratedFDeriv ℝ 2 F y)) y := by
    intro y hy
    exact hasFDerivAt_of_tendstoLocallyUniformlyOn
      (f := fun n => iteratedFDeriv ℝ 1 (fseq' n))
      (g := iteratedFDeriv ℝ 1 F)
      (f' := fun n y => c2 (iteratedFDeriv ℝ 2 (fseq' n) y))
      (g' := fun y => c2 (iteratedFDeriv ℝ 2 F y))
      Uopen hconv2
      (fun n w hw => by
      have hAt := (hfnSmooth n).contDiffAt
        ((isOpen_extChartAt_target (cover.base i)).mem_nhds
          (cover.piece_in_target i (interior_subset hw)))
      have hklt : (↑(1 : ℕ) : ℕ∞ω) < ∞ := by
        exact_mod_cast (show (1 : ℕ∞) < ⊤ from WithTop.coe_lt_top 1)
      have hhas := hAt.differentiableAt_iteratedFDeriv hklt |>.hasFDerivAt
      have hfd := congrFun (fderiv_iteratedFDeriv (𝕜 := ℝ)
        (f := fseq' n) (n := 1)) w
      rw [hfd] at hhas
      exact hhas)
      (fun w hw => (hjetLocally 1 (by omega)).tendsto_at hw) hy
  let Gzero : E → E →L[ℝ] (E [×0]→L[ℝ] ℝ) := fun y =>
    c1 (iteratedFDeriv ℝ 1 F y)
  let c1L : (E [×1]→L[ℝ] ℝ) →L[ℝ] E →L[ℝ] (E [×0]→L[ℝ] ℝ) :=
    c1.toContinuousLinearEquiv.toContinuousLinearMap
  let Hzero : E → E →L[ℝ] (E →L[ℝ] (E [×0]→L[ℝ] ℝ)) := fun y =>
    c1L.comp (c2 (iteratedFDeriv ℝ 2 F y))
  have hGzero : ∀ y ∈ U, HasFDerivAt Gzero (Hzero y) y := by
    intro y hy
    have hclm : HasFDerivAt (c1L : (E [×1]→L[ℝ] ℝ) → E →L[ℝ] (E [×0]→L[ℝ] ℝ))
        c1L (iteratedFDeriv ℝ 1 F y) := c1L.hasFDerivAt
    exact hclm.comp y (hsecond y hy)
  have hHzero : ContinuousOn Hzero U := by
    rw [continuousOn_iff_continuous_domRestrict]
    let J2 := smoothChartHolderJetCanonicalExtension cover 2 α N 2 (by omega) u i
    let inc : U → cover.piece i := fun y => ⟨y.1, interior_subset y.2⟩
    have hinc : Continuous inc := by
      apply continuous_induced_rng.mpr
      exact continuous_subtype_val
    have hjet : Continuous (fun y : U => c2 (J2 (inc y))) :=
      (c2.continuous.comp J2.continuous).comp hinc
    let compOp := ContinuousLinearMap.compL ℝ E (E [×1]→L[ℝ] ℝ)
      (E →L[ℝ] (E [×0]→L[ℝ] ℝ)) c1L
    have hcont : Continuous (fun y : U => compOp (c2 (J2 (inc y)))) :=
      compOp.continuous.comp hjet
    change Continuous (fun y : U => Hzero y.1)
    apply hcont.congr
    intro y
    change c1L.comp (c2 (J2 (inc y))) =
      c1L.comp (c2 (iteratedFDeriv ℝ 2 F y.1))
    have hEq := hJet 2 (by omega) i y.1 y.2
    rw [← hEq]
    change c1L.comp (c2 (iteratedFDeriv ℝ 2
      ((smoothChartHolderContinuousMapExtension cover 2 α N u : M → ℝ) ∘ e.symm) y.1)) =
      c1L.comp (c2 (iteratedFDeriv ℝ 2
        ((smoothChartHolderContinuousMapExtension cover 2 α N u : M → ℝ) ∘ e.symm) y.1))
    rfl
  have hGzeroContDiff : ContDiffOn ℝ (0 + 1) Gzero U := by
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
      (𝕜 := ℝ) (n := 0) (s := U) Uopen.uniqueDiffOn).2
    constructor
    · intro hω
      cases hω
    · refine ⟨Hzero, (contDiffOn_zero).2 hHzero, ?_⟩
      intro y hy
      exact (hGzero y hy).hasFDerivWithinAt
  have hFzeroContDiff : ContDiffOn ℝ (1 + 1) Fzero U := by
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
      (𝕜 := ℝ) (n := 1) (s := U) Uopen.uniqueDiffOn).2
    constructor
    · intro hω
      cases hω
    · refine ⟨Gzero, hGzeroContDiff, ?_⟩
      intro y hy
      exact (hfirstZero y hy).hasFDerivWithinAt
  have hFcontDiff : ContDiffOn ℝ 2 F U := by
    have hc0 : ContDiff ℝ 2 (c0 : (E [×0]→L[ℝ] ℝ) → ℝ) := by fun_prop
    have hcomp := hc0.comp_contDiffOn hFzeroContDiff
    apply hcomp.congr
    intro y hy
    simp [Fzero, F, iteratedFDeriv_zero_eq_comp, c0]
  have hzF : ContDiffAt ℝ 2 F z :=
    hFcontDiff.contDiffAt (Uopen.mem_nhds hz)
  have hzTarget : z ∈ e.target := cover.piece_in_target i (interior_subset hz)
  have hsource : e.symm z ∈ e.source := e.symm.map_source hzTarget
  have hxSource : x ∈ (chartAt E (cover.base i)).source := by
    rw [← hx, ← extChartAt_source (I := 𝓘(ℝ, E)) (x := cover.base i)]
    exact hsource
  have hcoord : (extChartAt 𝓘(ℝ, E) (cover.base i)) x = z := by
    rw [← hx]
    exact e.right_inv hzTarget
  rw [contMDiffAt_iff_source_of_mem_source (I := 𝓘(ℝ, E))
    (I' := 𝓘(ℝ, ℝ)) (x := cover.base i) (x' := x) hxSource]
  rw [hcoord]
  rw [contMDiffWithinAt_iff_contDiffWithinAt]
  simpa [F, e, extChartAt, chartAt_self_eq, Set.range, Function.comp_def,
    Function.comp_apply] using hzF.contDiffWithinAt

end CompletedRegularity

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M]

private theorem completed_evalC2_contMDiff_two [Nonempty M]
    (ω₁ : KahlerForm n M) (α : ℝ≥0) [P : ContinuityHolderPair ω₁ α]
    (u : P.C2) : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2
      (P.evalC2 u) := by
  let cover := P.finiteChartCover
  let N := P.normedDataC2
  let v : LittleHolder cover 2 α N := u
  have hJet (j : ℕ) (hj : j ≤ 2) (i) (z : EuclideanSpace ℂ (Fin n))
      (hz : z ∈ interior (cover.piece i)) :
      iteratedFDeriv ℝ j
        ((smoothChartHolderContinuousMapExtension cover 2 α N v : M → ℝ) ∘
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) z =
        smoothChartHolderJetCanonicalExtension cover 2 α N j hj v i
          ⟨z, interior_subset hz⟩ := by
    exact smoothChartHolderCompletedJetIdentity cover α N v j hj i z hz
  have hJetNorm (j : ℕ) (hj : j ≤ 2) (i) (z : EuclideanSpace ℂ (Fin n))
      (hz : z ∈ interior (cover.piece i)) :
      ‖smoothChartHolderJetCanonicalExtension cover 2 α N j hj v i
        ⟨z, interior_subset hz⟩‖ ≤ ‖v‖ := by
    exact smoothChartHolderCompletedJetNormBound cover α N v j hj i z hz
  have hregular (x : M) := local_completed_C2_regularity cover α N v x hJet hJetNorm
  have heval : (P.evalC2 u : M → ℝ) =
      smoothChartHolderContinuousMapExtension cover 2 α N v := by
    funext x
    rfl
  rw [heval]
  intro x
  exact hregular x

open Complex ContinuousAlternatingMap

/-- A bounded forward map that agrees with the Laplacian on the smooth mean-zero core agrees with
the pointwise Laplacian of completed evaluation. The proof consumes the C2Regularity completed-jet
identity and norm bound; it does not reprove either low-level statement. -/
theorem completed_forward_laplacian_formula [Nonempty M]
    (ω₁ : KahlerForm n M) (α : ℝ≥0)
    [P : ContinuityHolderPair ω₁ α]
    (A : P.C2 →L[ℝ] P.C0)
    (hCore : IsSmoothMeanZeroForwardExtension P A)
    (hvol : 0 < ω₁.volume.real Set.univ) :
    ∀ u, P.evalC0 (A u) = ω₁.laplacian (P.evalC2 u) := by
  classical
  let cover := P.finiteChartCover
  let N := P.normedDataC2
  let N₀ := P.normedDataC0
  let hessianFromJet
      (T : (EuclideanSpace ℂ (Fin n) [×2]→L[ℝ] ℝ)) : Matrix (Fin n) (Fin n) ℂ :=
    fun j k =>
      (((T ![EuclideanSpace.single j (1 : ℂ), EuclideanSpace.single k (1 : ℂ)] : ℝ) : ℂ) +
        (T ![Complex.I • EuclideanSpace.single j (1 : ℂ),
          Complex.I • EuclideanSpace.single k (1 : ℂ)] : ℝ) +
        Complex.I * (((T ![EuclideanSpace.single j (1 : ℂ),
          Complex.I • EuclideanSpace.single k (1 : ℂ)] : ℝ) : ℂ) -
          ((T ![Complex.I • EuclideanSpace.single j (1 : ℂ),
            EuclideanSpace.single k (1 : ℂ)] : ℝ) : ℂ))) / 4
  let laplacianJetContract (Ginv : Matrix (Fin n) (Fin n) ℂ)
      (T : EuclideanSpace ℂ (Fin n) [×2]→L[ℝ] ℝ) : ℝ :=
    RCLike.re (Ginv * hessianFromJet T).trace
  have hIsOneOne (φ : M → ℝ)
      (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 φ) :
      (mddbar n φ).IsOneOne := by
    intro x
    let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
    have hz : e x ∈ e.target := mem_extChartAt_target x
    have hsymm : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
        𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 2 e.symm (e x) := by
      exact ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x).contMDiffAt
        ((isOpen_extChartAt_target x).mem_nhds hz)).of_le
          (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
    have hφM : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2
        (φ ∘ e.symm) (e x) := (hφ x).comp_of_eq hsymm (e.left_inv (mem_extChartAt_source x))
    have hφC : ContDiffAt ℝ 2 (φ ∘ e.symm) (e x) :=
      (contMDiffAt_iff_contDiffAt).mp hφM
    change (ddbar (φ ∘ e.symm) (e x)).IsOneOne
    exact isOneOne_ddbar hφC
  have hLaplacianChart (f : M → ℝ)
      (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 f) (x : M)
      {y : M} (hy : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source) :
      ω₁.laplacian f y = RCLike.re
        ((ω₁.metricInChart x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y))⁻¹ *
          complexHessian (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)).trace := by
    let ψ := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
    let z := ψ y
    have hy' : y ∈ ψ.source := by simpa [ψ, ← extChartAt_source] using hy
    have hz : z ∈ ψ.target := ψ.map_source hy'
    have hzpoint : ψ.symm z = y := ψ.left_inv hy'
    have hychart : y ∈
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).source := by simp
    have hyC : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source := by
      simpa [extChartAt_real_eq, ← extChartAt_source] using hy
    have hyCy : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source := by simp
    have hOverlap : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source ∩
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).source := ⟨hy', hychart⟩
    let A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n) := {
      toLinearEquiv := {
        toFun := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y
        invFun := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y x y
        left_inv := by
          intro v
          have htriple : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source ∩
            (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source ∩
              (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source := by
            exact ⟨⟨hyC, hyCy⟩, hyC⟩
          have hc := tangentCoordChange_comp (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
            (w := x) (x := y) (y := x) (z := y) (v := v) htriple
          calc
            _ = tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x x y v := hc
            _ = v := tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
              (x := x) (z := y) hyC
        right_inv := by
          intro v
          have htriple : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source ∩
              (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source ∩
              (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source := by
            exact ⟨⟨hyCy, hyC⟩, hyCy⟩
          have hc := tangentCoordChange_comp (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
            (w := y) (x := x) (y := y) (z := y) (v := v) htriple
          calc
            _ = tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y y y v := hc
            _ = v := tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
              (x := y) (z := y) (by simp)
        map_add' := by intro u v; exact (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y).map_add u v
        map_smul' := by intro c v; exact (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y).map_smul c v
      }
      continuous_toFun := (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y).continuous
      continuous_invFun := (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y x y).continuous
    }
    have hA : fderiv ℝ
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y ∘
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z =
        (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ := by
      have hdef : tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y =
          fderiv ℝ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y ∘
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z := by
        rw [tangentCoordChange_def]
        simp [z, ψ]
      calc
        _ = tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y := hdef.symm
        _ = (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y).restrictScalars ℝ :=
          tangentCoordChange_real_eq hOverlap
        _ = _ := rfl
    have hrep (β : FormField (EuclideanSpace ℂ (Fin n)) M 2) :
        β.chartRep x z = (β y).compContinuousLinearMap
          ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ) := by
      rw [FormField.chartRep_eq_chartRep_comp (x := x) (x' := y) (z := z) hz]
      · rw [hzpoint, FormField.chartRep_self, hA]
      · have heq : (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z = y := by
          simpa [ψ] using hzpoint
        rw [heq]
        exact hychart
    have htrace := ContinuousAlternatingMap.relTrace_compContinuousLinearMap
      (ω₁.isOneOne y) (hIsOneOne f hf y) A
    have hddbar := chartRep_mddbar_of_contMDiff_two hf x hz
    calc
      ω₁.laplacian f y = relTrace (ω₁ y) (mddbar n f y) := rfl
      _ = relTrace ((ω₁ y).compContinuousLinearMap
            ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ))
          ((mddbar n f y).compContinuousLinearMap
            ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)) :=
        htrace.symm
      _ = RCLike.re
          ((ω₁.metricInChart x z)⁻¹ * complexHessian (f ∘ ψ.symm) z).trace := by
        rw [← hrep ω₁.toFormField, ← hrep (mddbar n f), hddbar]
        rfl

  let core2 := smoothMeanZeroChartHolderCore ω₁ cover 2 α N
  let : NormedAddCommGroup (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedAddCommGroup cover 2 α N
  let : NormedSpace ℝ (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedSpace cover 2 α N
  have hTcore₂ (f : SmoothChartHolderCore cover 2 α) :
      littleHolderMeanFunctional ω₁ cover 2 α N (f : LittleHolder cover 2 α N) =
        continuousVolumeIntegralCLM ω₁ (smoothChartHolderContinuousMapLinearMap cover 2 α f) := by
    simp [littleHolderMeanFunctional, smoothChartHolderContinuousMapExtension_coe,
      smoothChartHolderContinuousMapLinearMap]
  let e₂ (f : core2) : P.C2 :=
    ⟨(f : SmoothChartHolderCore cover 2 α), by
      change littleHolderMeanFunctional ω₁ cover 2 α N
        ((f : SmoothChartHolderCore cover 2 α) : LittleHolder cover 2 α N) = 0
      rw [hTcore₂]
      change ((continuousVolumeIntegralCLM ω₁).comp
        (smoothChartHolderContinuousMapCLM cover 2 α N)).toLinearMap f = 0
      exact f.property⟩
  have hEvalEmbed (f : core2) : P.evalC2 (e₂ f) =
      (f : SmoothChartHolderCore cover 2 α).smoothMap := by
    funext x
    simp [ContinuityHolderPair.evalC2, e₂, littleHolderMeanZeroEvaluationCLM,
      smoothChartHolderContinuousMapExtension_coe,
      smoothChartHolderContinuousMapLinearMap]
  have hEvalInj : Function.Injective P.evalC2 := by
    intro u v huv
    apply littleHolderMeanZeroEvaluationC2CLM_injective ω₁ cover α N
    apply ContinuousMap.ext
    intro x
    exact congrFun huv x
  have hDense₂ : DenseRange e₂ := by
    rw [denseRange_iff_closure_range]
    apply Set.eq_univ_iff_forall.2
    intro u
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hu : (u : LittleHolder cover 2 α N) ∈ closure (Set.range fun f : core2 =>
        ((f : SmoothChartHolderCore cover 2 α) : LittleHolder cover 2 α N)) := by
      rw [closure_smoothMeanZeroChartHolderCore_coe ω₁ cover 2 α N hvol]
      exact u.property
    obtain ⟨v, hv, hdist⟩ := Metric.mem_closure_iff.mp hu ε hε
    rcases hv with ⟨f, rfl⟩
    refine ⟨e₂ f, ⟨f, rfl⟩, ?_⟩
    simpa [e₂, Subtype.dist_eq] using hdist
  intro u
  funext x
  obtain ⟨i, z, hz, hx⟩ := cover.interior_covers x
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)
  have hzTarget : z ∈ e.target := cover.piece_in_target i (interior_subset hz)
  have hy : e.symm z ∈ (chartAt (EuclideanSpace ℂ (Fin n)) (cover.base i)).source := by
    simpa [e, ← extChartAt_source] using e.map_target hzTarget
  let y := e.symm z
  let p : cover.piece i := ⟨z, interior_subset hz⟩
  let jetCLM : P.C2 →L[ℝ] (EuclideanSpace ℂ (Fin n) [×2]→L[ℝ] ℝ) :=
    ((ContinuousMap.evalCLM (R := ℝ) p).comp
      (ContinuousLinearMap.proj i)).comp
      ((smoothChartHolderJetCanonicalExtension cover 2 α N 2 (Nat.le_refl 2)).comp
        (littleHolderMeanZeroSubmodule ω₁ cover 2 α N).subtypeL)
  have hJetCLM (v : P.C2) : jetCLM v =
      smoothChartHolderJetCanonicalExtension cover 2 α N 2 (Nat.le_refl 2)
        (v : LittleHolder cover 2 α N) i p := by
    simp [jetCLM, p]
  have hJetNorm (v : P.C2) : ‖jetCLM v‖ ≤ ‖v‖ := by
    rw [hJetCLM]
    exact smoothChartHolderCompletedJetNormBound cover α N v 2 (Nat.le_refl 2) i z hz
  have hJetLip : LipschitzWith 1 jetCLM := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    calc
      dist (jetCLM v) (jetCLM w) = ‖jetCLM (v - w)‖ := by
        rw [dist_eq_norm, ← map_sub]
      _ ≤ ‖v - w‖ := hJetNorm _
      _ = (1 : ℝ≥0) * dist v w := by simp [dist_eq_norm]
  let Ginv := (ω₁.metricInChart (cover.base i) z)⁻¹
  let contract : (EuclideanSpace ℂ (Fin n) [×2]→L[ℝ] ℝ) → ℝ :=
    laplacianJetContract Ginv
  have hContract : Continuous contract := by
    change Continuous (fun T => RCLike.re (Ginv * hessianFromJet T).trace)
    dsimp [hessianFromJet]
    fun_prop
  let rhs (v : P.C2) : ℝ := contract (jetCLM v)
  have hRhsCont : Continuous rhs := hContract.comp hJetLip.continuous
  have hLapFormula (v : P.C2) : ω₁.laplacian (P.evalC2 v) y = rhs v := by
    have hReg := completed_evalC2_contMDiff_two ω₁ α v
    have hLap := hLaplacianChart (P.evalC2 v) hReg
      (cover.base i) (y := y) hy
    rw [e.right_inv hzTarget] at hLap
    rw [hLap]
    have hCoord : ContDiffAt ℝ 2 ((P.evalC2 v) ∘ e.symm) z := by
      have hRegOn : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2
          (P.evalC2 v) Set.univ := contMDiffOn_univ.mpr hReg
      have hSymmOn : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
          𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 2 e.symm e.target :=
        (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
          (cover.base i)).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
      have hComp := hRegOn.comp hSymmOn (by intro w hw; simp)
      exact (hComp.contDiffOn.contDiffAt
        ((isOpen_extChartAt_target (cover.base i)).mem_nhds hzTarget))
    have hJet := smoothChartHolderCompletedJetIdentity cover α N
      (v : LittleHolder cover 2 α N) 2 (Nat.le_refl 2) i z hz
    have hEvalFn : P.evalC2 v =
        smoothChartHolderContinuousMapExtension cover 2 α N (v : LittleHolder cover 2 α N) := by
      funext w
      rfl
    have hComplex : complexHessian ((P.evalC2 v) ∘ e.symm) z =
        hessianFromJet (jetCLM v) := by
      ext j k
      have hD (a b : EuclideanSpace ℂ (Fin n)) :
          fderiv ℝ (fderiv ℝ ((P.evalC2 v) ∘ e.symm)) z a b =
            iteratedFDeriv ℝ 2 ((P.evalC2 v) ∘ e.symm) z ![a, b] := by
        simpa using (iteratedFDeriv_two_apply ((P.evalC2 v) ∘ e.symm) z ![a, b]).symm
      rw [complexHessian_apply hCoord j k]
      rw [hD _ _, hD _ _, hD _ _, hD _ _]
      rw [hEvalFn, hJet, hJetCLM]
    rw [hComplex]
  let eval0 : P.C0 →L[ℝ] ℝ :=
    (ContinuousMap.evalCLM (R := ℝ) y).comp
      (littleHolderMeanZeroEvaluationCLM ω₁ cover 0 α N₀)
  have hEval0 (v : P.C0) : eval0 v = P.evalC0 v y := rfl
  let lhs (v : P.C2) : ℝ := eval0 (A v)
  have hLhsCont : Continuous lhs := eval0.continuous.comp A.continuous
  have hCoreEq (f : core2) : lhs (e₂ f) = rhs (e₂ f) := by
    rcases hCore f with ⟨v, hv, g, hg, hgv⟩
    have hEq : P.evalC2 v = P.evalC2 (e₂ f) := by rw [hv, hEvalEmbed]
    have hve : v = e₂ f := hEvalInj hEq
    calc
      lhs (e₂ f) = P.evalC0 (A v) y := by simp [lhs, hEval0, ← hve]
      _ = (g : SmoothChartHolderCore cover 0 α).smoothMap y := by exact congrFun hgv y
      _ = ω₁.laplacian (P.evalC2 (e₂ f)) y := by
        rw [hEvalEmbed]
        exact congrFun hg y
      _ = rhs (e₂ f) := hLapFormula (e₂ f)
  have hEq : lhs u = rhs u := by
    refine hDense₂.induction ?_ (isClosed_eq hLhsCont hRhsCont) u
    rintro _ ⟨f, rfl⟩
    exact hCoreEq f
  calc
    P.evalC0 (A u) x = lhs u := by rw [← hx]; rfl
    _ = rhs u := hEq
    _ = ω₁.laplacian (P.evalC2 u) x := by
      rw [← hx]
      exact (hLapFormula u).symm

end KahlerForm
