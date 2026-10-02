module

public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderEvaluation
public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderC2Regularity.CompletedChartJets

import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# Pointwise C² regularity from chart-jet convergence

This is the local analytic step in the regularity of an evaluation map on a little-Hölder
completion. On a chart piece whose interior contains the point, a Cauchy sequence in the
finite-chart order-two gauge has uniformly Cauchy coordinate jets of orders zero, one, and two.
The local uniform-derivative limit theorem, applied in a smaller coordinate neighborhood, identifies
the limits of the first and second jets as derivatives of the C⁰ evaluation extension.
-/

@[expose] public section

noncomputable section

open scoped Manifold ContDiff NNReal Topology

namespace KahlerForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] in
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

omit [FiniteDimensional ℝ E] in
/-- Pointwise C² regularity of the continuous evaluation extension. The finite-chart gauge controls
all coordinate jets through order two uniformly on a chart piece; convergence of those jets and the
line-segment fundamental theorem of calculus identify the limiting jets with derivatives of the
extended evaluation in a neighborhood of the point. -/
theorem smoothChartHolderContinuousMapExtension_contMDiffAt_orderTwo
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover 2 α)
    (u : LittleHolder cover 2 α N) (x : M)
    (hJet : ∀ (j : ℕ) (hj : j ≤ 2) (i) (z : E)
      (hz : z ∈ interior (cover.piece i)),
      iteratedFDeriv ℝ j
        ((smoothChartHolderContinuousMapExtension cover 2 α N u : M → ℝ) ∘
          (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z =
        smoothChartHolderJetCanonicalExtension cover 2 α N j hj u i
          ⟨z, interior_subset hz⟩) :
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

omit [FiniteDimensional ℝ E] in
/-- Global order-two regularity follows from the completed chart-jet identity and bound. This
all-exponent regularity is conditional on the supplied normed data and makes no claim that such data exist
for every exponent. -/
theorem smoothChartHolderContinuousMapExtension_contMDiff_orderTwo_of_completedJets
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover 2 α)
    (u : LittleHolder cover 2 α N)
    (hJet : ∀ (j : ℕ) (hj : j ≤ 2) (i) (z : E)
      (hz : z ∈ interior (cover.piece i)),
      iteratedFDeriv ℝ j
        ((smoothChartHolderContinuousMapExtension cover 2 α N u : M → ℝ) ∘
          (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z =
        smoothChartHolderJetCanonicalExtension cover 2 α N j hj u i
          ⟨z, interior_subset hz⟩) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) 2
      (smoothChartHolderContinuousMapExtension cover 2 α N u) := by
  intro x
  exact smoothChartHolderContinuousMapExtension_contMDiffAt_orderTwo
    cover α N u x hJet

end KahlerForm
