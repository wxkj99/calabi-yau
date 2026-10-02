module

public import CalabiYau.MongeAmpere.Continuity.Openness.ResidualDerivative.LogDetRemainder.ChartTaylorData
import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderC2Regularity.CompletedChartJets

open scoped Manifold ContDiff NNReal Topology ComplexOrder Matrix.Norms.Frobenius
open MeasureTheory Set

public section

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
  letI : NormedAddCommGroup (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedAddCommGroup cover 2 α N
  letI : NormedSpace ℝ (SmoothChartHolderCore cover 2 α) :=
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

/-- Pointwise C² regularity of the continuous evaluation extension. The finite-chart gauge controls
all coordinate jets through order two uniformly on a chart piece; convergence of those jets and the
line-segment fundamental theorem of calculus identify the limiting jets with derivatives of the
extended evaluation in a neighborhood of the point. -/
private theorem compactControl_smoothChartHolderContinuousMapExtension_contMDiffAt_orderTwo
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
  letI : NormedAddCommGroup (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedAddCommGroup cover 2 α N
  letI : NormedSpace ℝ (SmoothChartHolderCore cover 2 α) :=
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

/-- Global order-two regularity follows from the completed chart-jet identity and bound. This
all-exponent regularity is conditional on the supplied normed data and makes no claim that such data exist
for every exponent. -/
private theorem compactControl_smoothChartHolderContinuousMapExtension_contMDiff_orderTwo_of_completedJets
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover 2 α)
    (u : LittleHolder cover 2 α N)
    (hJet : ∀ (j : ℕ) (hj : j ≤ 2) (i) (z : E)
      (hz : z ∈ interior (cover.piece i)),
      iteratedFDeriv ℝ j
        ((smoothChartHolderContinuousMapExtension cover 2 α N u : M → ℝ) ∘
          (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z =
        smoothChartHolderJetCanonicalExtension cover 2 α N j hj u i
          ⟨z, interior_subset hz⟩)
    (hJetNorm : ∀ (j : ℕ) (hj : j ≤ 2) (i) (z : E)
      (hz : z ∈ interior (cover.piece i)),
      ‖smoothChartHolderJetCanonicalExtension cover 2 α N j hj u i
        ⟨z, interior_subset hz⟩‖ ≤ ‖u‖) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) 2
      (smoothChartHolderContinuousMapExtension cover 2 α N u) := by
  intro x
  exact compactControl_smoothChartHolderContinuousMapExtension_contMDiffAt_orderTwo
    cover α N u x hJet hJetNorm

end KahlerForm

namespace Matrix

private theorem exists_small_hermitian_radius_control {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (hA : A.PosDef) :
    ∃ r : ℝ, 0 < r ∧ ∀ H : Matrix ι ι ℂ, ‖H‖ < r → H.IsHermitian →
      (A + H).PosDef := by
  classical
  by_cases hn : Nonempty ι
  · let : NormedAddCommGroup (Matrix ι ι ℂ) := Matrix.normedAddCommGroup
    let q : (ι → ℂ) → ℝ := fun x => RCLike.re (star x ⬝ᵥ (A *ᵥ x))
    have hq : Continuous q := by
      dsimp [q]
      fun_prop
    let S : Set (ι → ℂ) := Metric.sphere 0 1
    have hS : IsCompact S := isCompact_sphere 0 1
    have hSne : S.Nonempty := by
      obtain ⟨i⟩ := hn
      refine ⟨Pi.single i 1, ?_⟩
      simp [S, Pi.norm_single]
    obtain ⟨x, hxS, hxMin⟩ := hS.exists_isMinOn hSne hq.continuousOn
    have hxpos : 0 < q x := by
      have hd := hA.dotProduct_mulVec_pos (Metric.ne_of_mem_sphere hxS one_ne_zero)
      simpa [q] using (RCLike.pos_iff.mp hd).1
    have hq_lower : ∀ y ∈ S, q x ≤ q y := hxMin
    have hqH_bound (H : Matrix ι ι ℂ) (y : ι → ℂ) (hy : y ∈ S) :
        |RCLike.re (star y ⬝ᵥ (H *ᵥ y))| ≤ (Fintype.card ι : ℝ)^2 * ‖H‖ := by
      have hy_norm : ‖y‖ = 1 := by simpa [S, dist_eq_norm] using hy
      have hyi (i : ι) : ‖y i‖ ≤ 1 := by
        rw [← hy_norm]
        exact norm_le_pi_norm y i
      have hentry (i j : ι) : ‖H i j‖ ≤ ‖H‖ := by
        have hsumNat : ‖H i j‖ ^ 2 ≤ ∑ a, ∑ b, ‖H a b‖ ^ 2 := by
          calc
            ‖H i j‖ ^ 2 ≤ ∑ b, ‖H i b‖ ^ 2 :=
              Finset.single_le_sum (fun b _ => sq_nonneg ‖H i b‖) (Finset.mem_univ j)
            _ ≤ ∑ a, ∑ b, ‖H a b‖ ^ 2 :=
              Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg ‖H a b‖)
                (Finset.mem_univ i)
        have hpow := Real.rpow_le_rpow (sq_nonneg (‖H i j‖)) hsumNat
          (by norm_num : 0 ≤ (1 / 2 : ℝ))
        have hleft : (‖H i j‖ ^ 2) ^ (1 / 2 : ℝ) = ‖H i j‖ := by
          rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
        calc
          ‖H i j‖ = (‖H i j‖ ^ 2) ^ (1 / 2 : ℝ) := hleft.symm
          _ ≤ (∑ a, ∑ b, ‖H a b‖ ^ 2) ^ (1 / 2 : ℝ) := hpow
          _ = ‖H‖ := by
            rw [Matrix.frobenius_norm_def]
            congr 1
            simp only [Real.rpow_two, pow_two]
      have hterm (i j : ι) : ‖star (y i) * H i j * y j‖ ≤ ‖H‖ := by
        calc
          ‖star (y i) * H i j * y j‖ = ‖y i‖ * ‖H i j‖ * ‖y j‖ := by simp [mul_assoc]
          _ ≤ 1 * ‖H‖ * 1 := by
            calc
              (‖y i‖ * ‖H i j‖) * ‖y j‖ ≤ (1 * ‖H‖) * ‖y j‖ := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul (hyi i) (hentry i j) (norm_nonneg _) (by norm_num))
                  (norm_nonneg _)
              _ ≤ (1 * ‖H‖) * 1 := mul_le_mul_of_nonneg_left (hyi j) (by positivity)
          _ = ‖H‖ := by ring
      have hexpand : star y ⬝ᵥ (H *ᵥ y) = ∑ i, ∑ j, star (y i) * H i j * y j := by
        simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
      rw [hexpand]
      calc
        |RCLike.re (∑ i, ∑ j, star (y i) * H i j * y j)| ≤
            ‖∑ i, ∑ j, star (y i) * H i j * y j‖ := RCLike.abs_re_le_norm _
        _ ≤ ∑ i, ‖∑ j, star (y i) * H i j * y j‖ := norm_sum_le _ _
        _ ≤ ∑ i, ∑ j, ‖star (y i) * H i j * y j‖ := by
          apply Finset.sum_le_sum
          intro i hi
          exact norm_sum_le _ _
        _ ≤ ∑ i, ∑ j, ‖H‖ := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro j hj
          exact hterm i j
        _ = (Fintype.card ι : ℝ)^2 * ‖H‖ := by simp [pow_two, mul_assoc]
    let C : ℝ := (Fintype.card ι : ℝ)^2
    have hC : 0 < C := by
      dsimp [C]
      have : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr hn
      positivity
    let r : ℝ := q x / (2 * C)
    have hr : 0 < r := by
      dsimp [r]
      exact div_pos hxpos (by positivity)
    have hN : ∀ᶠ H : Matrix ι ι ℂ in 𝓝 (0 : Matrix ι ι ℂ),
        H.IsHermitian → (A + H).PosDef := by
      filter_upwards [Metric.ball_mem_nhds (0 : Matrix ι ι ℂ) hr] with H hH
      intro hHerm
      have hnorm : ‖H‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hH
      have hsmall : C * ‖H‖ < q x / 2 := by
        dsimp [r] at hnorm
        calc
          C * ‖H‖ < C * (q x / (2 * C)) := mul_lt_mul_of_pos_left hnorm hC
          _ = q x / 2 := by field_simp
      have hqpos (y : ι → ℂ) (hy : y ∈ S) :
          0 < q y + RCLike.re (star y ⬝ᵥ (H *ᵥ y)) := by
        have hbound := hqH_bound H y hy
        have hlow := hq_lower y hy
        have hneg := neg_abs_le (RCLike.re (star y ⬝ᵥ (H *ᵥ y)))
        dsimp [C] at hsmall
        linarith
      apply PosDef.of_dotProduct_mulVec_pos (hA.1.add hHerm)
      intro v hv
      have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
      let y : ι → ℂ := (‖v‖⁻¹ : ℝ) • v
      have hyS : y ∈ S := by
        simp [S, y, norm_smul,
          inv_mul_cancel₀ hvnorm.ne']
      have hreal : 0 < RCLike.re (star y ⬝ᵥ ((A + H) *ᵥ y)) := by
        have heq : RCLike.re (star y ⬝ᵥ ((A + H) *ᵥ y)) =
            q y + RCLike.re (star y ⬝ᵥ (H *ᵥ y)) := by
          dsimp [q]
          rw [add_mulVec, dotProduct_add]
          simp
        rw [heq]
        exact hqpos y hyS
      have hv_eq : v = (‖v‖ : ℝ) • y := by
        dsimp [y]
        rw [smul_smul, mul_inv_cancel₀ hvnorm.ne', one_smul]
      have hscale : star v ⬝ᵥ ((A + H) *ᵥ v) =
          (‖v‖ ^ 2 : ℂ) * (star y ⬝ᵥ ((A + H) *ᵥ y)) := by
        conv_lhs => rw [hv_eq]
        simp [dotProduct, mulVec, Finset.mul_sum, RCLike.real_smul_eq_coe_mul]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [hscale]
      apply mul_pos
      · exact_mod_cast sq_pos_of_pos hvnorm
      · exact (RCLike.pos_iff.mpr ⟨hreal, (hA.1.add hHerm).im_star_dotProduct_mulVec_self y⟩)
    obtain ⟨r', hr', hball⟩ := Metric.mem_nhds_iff.mp hN
    refine ⟨r', hr', ?_⟩
    intro H hHnorm hHerm
    have hmem : H ∈ Metric.ball (0 : Matrix ι ι ℂ) r' := by
      rwa [Metric.mem_ball, dist_zero_right]
    exact hball hmem hHerm
  · have : IsEmpty ι := not_nonempty_iff.mp hn
    exact ⟨1, by norm_num, fun H _ hHerm => by
      have hzero : H = 0 := Subsingleton.elim _ _
      simpa [hzero] using hA⟩

private theorem exists_compact_uniform_hermitian_perturbation_posdef_control
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι] (A : X → Matrix ι ι ℂ)
    (hAcont : Continuous A) (hApos : ∀ x, (A x).PosDef) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : X, ∀ H : Matrix ι ι ℂ,
      H.IsHermitian → ‖H‖ < ε → (A x + H).PosDef := by
  classical
  by_cases hX : IsEmpty X
  · refine ⟨1, by norm_num, ?_⟩
    intro x
    exact (hX.false x).elim
  · let r : X → ℝ := fun x => Classical.choose
      (exists_small_hermitian_radius_control (A x) (hApos x))
    have hrpos (x : X) : 0 < r x :=
      (Classical.choose_spec
        (exists_small_hermitian_radius_control (A x) (hApos x))).1
    have hrule (x : X) : ∀ H : Matrix ι ι ℂ, ‖H‖ < r x → H.IsHermitian →
        (A x + H).PosDef :=
      (Classical.choose_spec
        (exists_small_hermitian_radius_control (A x) (hApos x))).2
    let U : X → Set X := fun x => A ⁻¹' Metric.ball (A x) (r x / 2)
    have hUopen (x : X) : IsOpen (U x) := Metric.isOpen_ball.preimage hAcont
    have hUcover : (Set.univ : Set X) ⊆ ⋃ x : X, U x := by
      intro y hy
      refine Set.mem_iUnion.2 ⟨y, ?_⟩
      change A y ∈ Metric.ball (A y) (r y / 2)
      rw [Metric.mem_ball, dist_self]
      exact half_pos (hrpos y)
    obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hUopen hUcover
    have hsne : s.Nonempty := by
      have hXne : Nonempty X := not_isEmpty_iff.mp hX
      obtain ⟨x⟩ := hXne
      have hx := hs (Set.mem_univ x)
      rcases Set.mem_iUnion.mp hx with ⟨y, hy⟩
      rcases Set.mem_iUnion.mp hy with ⟨hyS, hyx⟩
      exact ⟨y, by simpa using hyS⟩
    let R : Finset ℝ := s.image (fun x => r x / 2)
    have hRne : R.Nonempty := Finset.image_nonempty.mpr hsne
    let ε : ℝ := R.min' hRne
    have hε : 0 < ε := by
      change 0 < R.min' hRne
      rw [Finset.lt_min'_iff]
      intro q hq
      rcases Finset.mem_image.mp hq with ⟨x, hx, rfl⟩
      exact half_pos (hrpos x)
    refine ⟨ε, hε, ?_⟩
    intro x H hHerm hH
    have hxcover := hs (Set.mem_univ x)
    rcases Set.mem_iUnion.mp hxcover with ⟨a, hxa⟩
    rcases Set.mem_iUnion.mp hxa with ⟨haS, hxa⟩
    have haS' : a ∈ s := by simpa using haS
    have hAxclose : dist (A x) (A a) < r a / 2 := by
      simpa [U] using hxa
    have hRadMin : ε ≤ r a / 2 := by
      change R.min' hRne ≤ r a / 2
      exact Finset.min'_le R (r a / 2) (Finset.mem_image.mpr ⟨a, haS', rfl⟩)
    have hAherm : (A x - A a).IsHermitian :=
      (hApos x).isHermitian.sub (hApos a).isHermitian
    have hpertHerm : (A x - A a + H).IsHermitian := hAherm.add hHerm
    have hpertNorm : ‖A x - A a + H‖ < r a := by
      calc
        ‖A x - A a + H‖ ≤ ‖A x - A a‖ + ‖H‖ := norm_add_le _ _
        _ < r a / 2 + ε := add_lt_add (by simpa [dist_eq_norm] using hAxclose) hH
        _ ≤ r a / 2 + r a / 2 := by nlinarith [hRadMin]
        _ = r a := by ring
    have hpos := hrule a (A x - A a + H) hpertNorm hpertHerm
    have hEq : A a + (A x - A a + H) = A x + H := by abel
    rw [← hEq]
    exact hpos

private theorem inverseNormSmallAdd_control {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A X : Matrix ι ι ℂ) (M : ℝ)
    (hA : A.PosDef) (hAX : (A + X).PosDef)
    (hAinv : ‖A⁻¹‖ ≤ M) (hsmall : M * ‖X‖ ≤ 1 / 2) :
    ‖(A + X)⁻¹‖ ≤ 2 * M := by
  let V := (A + X)⁻¹
  have hAunit : IsUnit A.det := (ne_of_gt hA.det_pos).isUnit
  have hAXunit : IsUnit (A + X).det := (ne_of_gt hAX.det_pos).isUnit
  have hAinvA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hAunit
  have hAXAXinv : (A + X) * V = 1 := by
    dsimp [V]
    exact Matrix.mul_nonsing_inv (A + X) hAXunit
  have hident : (1 + A⁻¹ * X) * V = A⁻¹ := by
    calc
      (1 + A⁻¹ * X) * V = (A⁻¹ * A + A⁻¹ * X) * V := by rw [hAinvA]
      _ = A⁻¹ * (A + X) * V := by rw [Matrix.mul_add]
      _ = A⁻¹ := by rw [Matrix.mul_assoc, hAXAXinv]; simp
  have hsum : V + A⁻¹ * X * V = A⁻¹ := by
    simpa only [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc] using hident
  have hsub : V = A⁻¹ - A⁻¹ * X * V := by
    calc
      V = (V + A⁻¹ * X * V) - A⁻¹ * X * V := by module
      _ = A⁻¹ - A⁻¹ * X * V := by rw [hsum]
  have hmul : ‖A⁻¹ * X * V‖ ≤ ‖A⁻¹‖ * ‖X‖ * ‖V‖ := by
    calc
      _ ≤ ‖A⁻¹ * X‖ * ‖V‖ := Matrix.frobenius_norm_mul _ _
      _ ≤ (‖A⁻¹‖ * ‖X‖) * ‖V‖ := by
        gcongr
        exact Matrix.frobenius_norm_mul _ _
  have hmulM : ‖A⁻¹ * X * V‖ ≤ M * ‖X‖ * ‖V‖ := by
    calc
      ‖A⁻¹ * X * V‖ ≤ ‖A⁻¹‖ * ‖X‖ * ‖V‖ := hmul
      _ ≤ M * ‖X‖ * ‖V‖ := by gcongr
  have hV : ‖V‖ ≤ M + (M * ‖X‖) * ‖V‖ := by
    calc
      ‖V‖ = ‖A⁻¹ - A⁻¹ * X * V‖ := congrArg norm hsub
      _ ≤ ‖A⁻¹‖ + ‖A⁻¹ * X * V‖ := norm_sub_le _ _
      _ ≤ M + (M * ‖X‖) * ‖V‖ := by nlinarith [hAinv, hmulM]
  have hM : 0 ≤ M := le_trans (norm_nonneg _) hAinv
  have hVnonneg : 0 ≤ ‖V‖ := norm_nonneg _
  nlinarith

private theorem exists_compact_uniform_hermitian_perturbation_resolvent_control
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : X → Matrix ι ι ℂ) (hAcont : Continuous A)
    (hApos : ∀ x, (A x).PosDef) :
    ∃ ε M : ℝ, 0 < ε ∧ 0 < M ∧
      ∀ x : X, ∀ H : Matrix ι ι ℂ, H.IsHermitian → ‖H‖ < ε →
        (A x + H).PosDef ∧ ‖(A x + H)⁻¹‖ ≤ M := by
  obtain ⟨εpos, hεpos, hpos⟩ :=
    exists_compact_uniform_hermitian_perturbation_posdef_control A hAcont hApos
  open scoped Matrix.Norms.Elementwise in
    have hInvCont : Continuous (fun x : X => (A x)⁻¹) := by
      rw [continuous_iff_continuousAt]
      intro x
      exact ((Matrix.contDiffAt_inv ((hApos x).det_pos.ne').isUnit).continuousAt).comp
        hAcont.continuousAt
  have hnormCont : Continuous (fun x : X => ‖(A x)⁻¹‖) :=
    continuous_norm.comp hInvCont
  obtain ⟨B, hB₀, hB⟩ :=
    (isCompact_univ.bddAbove_image hnormCont.continuousOn).exists_ge 0
  let M₀ : ℝ := B + 1
  have hM₀ : 0 < M₀ := by dsimp [M₀]; linarith
  have hAinv (x : X) : ‖(A x)⁻¹‖ ≤ M₀ := by
    have h := hB _ ⟨x, Set.mem_univ x, rfl⟩
    dsimp [M₀]
    linarith
  let ε : ℝ := min εpos (1 / (2 * M₀))
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min hεpos (one_div_pos.mpr (mul_pos (by norm_num) hM₀))
  refine ⟨ε, 2 * M₀, hε, by positivity, ?_⟩
  intro x H hHerm hH
  have hHlt : ‖H‖ < εpos :=
    (lt_min_iff.mp (by simpa [ε] using hH)).1
  have hHsmall : ‖H‖ < 1 / (2 * M₀) :=
    (lt_min_iff.mp (by simpa [ε] using hH)).2
  have hAX := hpos x H hHerm hHlt
  have hsmall : M₀ * ‖H‖ ≤ 1 / 2 := by
    have h := mul_lt_mul_of_pos_left hHsmall hM₀
    have hEq : M₀ * (1 / (2 * M₀)) = 1 / 2 := by field_simp
    rw [hEq] at h
    exact le_of_lt h
  refine ⟨hAX, ?_⟩
  exact inverseNormSmallAdd_control (A x) H M₀ (hApos x) hAX (hAinv x) hsmall

end Matrix

namespace KahlerForm

private theorem holderBoundOn_of_contDiffOn_compact
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {U K : Set E} {f : E → F} {α : ℝ≥0}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U) (hα : α ≤ 1) :
    ∃ C : ℝ≥0, HolderBoundOn 0 α C K f := by
  classical
  have hNormCont : ContinuousOn (fun x => ‖f x‖) K :=
    (hf.continuousOn.mono hKU).norm
  obtain ⟨B, hB₀, hB⟩ := (hK.bddAbove_image hNormCont).exists_ge 0
  let C : ℝ≥0 := ⟨B, hB₀⟩
  have hBound (x : E) (hx : x ∈ K) : ‖f x‖ ≤ (C : ℝ) := by
    exact_mod_cast hB (‖f x‖) ⟨x, hx, rfl⟩
  have hLoc : LocallyLipschitzOn K f := by
    intro x hx
    have hxU : x ∈ U := hKU hx
    have hfx : ContDiffAt ℝ 1 f x :=
      (hf.contDiffAt (hU.mem_nhds hxU)).of_le (by simp)
    obtain ⟨L, t, ht, hLip⟩ := hfx.exists_lipschitzOnWith
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp ht
    refine ⟨L, Metric.ball x δ ∩ K,
      Metric.mem_nhdsWithin_iff.mpr ⟨δ, hδ, ?_⟩, ?_⟩
    · exact fun y hy => ⟨hy.1, hy.2⟩
    · apply hLip.mono
      intro y hy
      exact hball hy.1
  obtain ⟨L, hLip⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK hLoc
  have hdiamTop : Metric.ediam K ≠ ⊤ := hK.isBounded.ediam_ne_top
  let D : ℝ≥0 := (Metric.ediam K).toNNReal
  have hdist (x : E) (hx : x ∈ K) (y : E) (hy : y ∈ K) :
      edist x y ≤ (D : ENNReal) := by
    have heq : (D : ENNReal) = Metric.ediam K := ENNReal.coe_toNNReal hdiamTop
    rw [heq]
    exact Metric.edist_le_ediam_of_mem hx hy
  have hHolderF := hLip.holderOnWith.of_le hdist hα
  let Cα : ℝ≥0 := L * D ^ ((1 : ℝ) - (α : ℝ))
  let Ctot : ℝ≥0 := max (2 * C) Cα
  let JI : F ≃ₗᵢ[ℝ] (E [×0]→L[ℝ] F) :=
    (continuousMultilinearCurryFin0 ℝ E F).symm
  let J : F →L[ℝ] (E [×0]→L[ℝ] F) := JI.toContinuousLinearMap
  have hJlip : LipschitzWith 1 J := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    calc
      dist (J x) (J y) = dist x y := by
        rw [dist_eq_norm, dist_eq_norm, ← map_sub]
        exact JI.norm_map _
      _ ≤ 1 * dist x y := by simp
  have hJ : HolderWith 1 1 J := hJlip.holderWith
  have hHolderJet : HolderOnWith Cα α (iteratedFDeriv ℝ 0 f) K := by
    have hcomp : HolderOnWith (1 * Cα ^ (1 : ℝ)) (1 * α) (J ∘ f) K :=
      (hJ.holderOnWith Set.univ).comp hHolderF (by intro x hx; exact Set.mem_univ _)
    have hcomp' : HolderOnWith Cα α (J ∘ f) K := by
      simpa [NNReal.rpow_one, one_mul] using hcomp
    have heq : iteratedFDeriv ℝ 0 f = J ∘ f := by
      simpa [J] using (iteratedFDeriv_zero_eq_comp (𝕜 := ℝ) (f := f))
    rw [heq]
    exact hcomp'
  refine ⟨Ctot, ?_⟩
  constructor
  · intro j hj x hx
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    rw [norm_iteratedFDeriv_zero]
    exact (hBound x hx).trans (by
      calc
        (C : ℝ) = 1 * C := by ring
        _ ≤ (2 * C : ℝ) := by gcongr; norm_num
        _ ≤ (Ctot : ℝ) := by exact_mod_cast (le_max_left (2 * C) Cα))
  · exact hHolderJet.mono_const (le_max_right _ _)

private theorem holderBoundOn_zero_from_holderOnWith
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set E}
    {α C : ℝ≥0} {f : E → F}
    (hf : HolderOnWith C α f K) (hBound : ∀ x ∈ K, ‖f x‖ ≤ C) :
    HolderBoundOn 0 α C K f := by
  let L := continuousMultilinearCurryFin0 ℝ E F
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    simpa [norm_iteratedFDeriv_zero] using hBound x hx
  · intro x hx y hy
    rw [iteratedFDeriv_zero_eq_comp]
    change edist (L.symm (f x)) (L.symm (f y)) ≤ _
    rw [L.symm.edist_map]
    exact hf x hx y hy

private theorem frobenius_norm_le_of_entry_bound {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hA : ∀ i j, ‖A i j‖ ≤ B) :
    ‖A‖ ≤ Real.sqrt (Fintype.card (ι × ι) : ℝ) * B := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  simp only [Real.rpow_two, pow_two]
  calc
    Real.sqrt (∑ i, ∑ j, ‖A i j‖ * ‖A i j‖) ≤
        Real.sqrt ((Fintype.card ι : ℝ) * (Fintype.card ι : ℝ) * (B * B)) := by
      apply Real.sqrt_le_sqrt
      calc
        (∑ i, ∑ j, ‖A i j‖ * ‖A i j‖) ≤
            ∑ i, ∑ j, B * B := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro j hj
          exact mul_le_mul (hA i j) (hA i j) (norm_nonneg _) hB
        _ = (Fintype.card ι : ℝ) * (Fintype.card ι : ℝ) * (B * B) := by
          simp [mul_assoc]
    _ = Real.sqrt (Fintype.card (ι × ι) : ℝ) * B := by
      rw [Fintype.card_prod, Nat.cast_mul, Real.sqrt_mul (by positivity),
        Real.sqrt_mul (by positivity), Real.sqrt_mul_self hB]

private theorem holderOnWith_frobenius_of_entrywise {E : Type*} [PseudoMetricSpace E]
    {ι : Type*} [Fintype ι] {α C : ℝ≥0} {K : Set E}
    {A : E → Matrix ι ι ℂ}
    (hA : ∀ i j, HolderOnWith C α (fun x ↦ A x i j) K) :
    HolderOnWith ((Real.sqrt (Fintype.card (ι × ι) : ℝ) * (C : ℝ)).toNNReal) α A K := by
  intro x hx y hy
  rw [edist_dist]
  have hentry (i j : ι) : ‖A x i j - A y i j‖ ≤
      (C : ℝ) * dist x y ^ (α : ℝ) := by
    have h := (hA i j).edist_le hx hy
    rw [edist_dist, edist_dist,
      ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) α.coe_nonneg,
      ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)] at h
    have h' : dist (A x i j) (A y i j) ≤
        (C : ℝ) * dist x y ^ (α : ℝ) :=
      (ENNReal.ofReal_le_ofReal_iff
        (p := dist (A x i j) (A y i j))
        (q := (C : ℝ) * dist x y ^ (α : ℝ)) (by positivity)).mp h
    rw [dist_eq_norm] at h'
    simpa only [norm_sub_rev] using h'
  have hmat := frobenius_norm_le_of_entry_bound (A x - A y)
    ((C : ℝ) * dist x y ^ (α : ℝ)) (by positivity) (by
      intro i j
      simpa only [Matrix.sub_apply] using hentry i j)
  have hnorm : dist (A x) (A y) ≤
      (Real.sqrt (Fintype.card (ι × ι) : ℝ) * (C : ℝ)) * dist x y ^ (α : ℝ) := by
    rw [dist_eq_norm]
    calc
      ‖A x - A y‖ ≤ Real.sqrt (Fintype.card (ι × ι) : ℝ) *
          ((C : ℝ) * dist x y ^ (α : ℝ)) := hmat
      _ = (Real.sqrt (Fintype.card (ι × ι) : ℝ) * (C : ℝ)) *
          dist x y ^ (α : ℝ) := by ring
  calc
    ENNReal.ofReal (dist (A x) (A y)) ≤
        ENNReal.ofReal ((Real.sqrt (Fintype.card (ι × ι) : ℝ) * (C : ℝ)) *
          dist x y ^ (α : ℝ)) := ENNReal.ofReal_le_ofReal hnorm
    _ = ((((Real.sqrt (Fintype.card (ι × ι) : ℝ) * (C : ℝ)).toNNReal :
          ℝ≥0) : ENNReal) * edist x y ^ (α : ℝ)) := by
      rw [ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) α.coe_nonneg,
        ← edist_dist, ENNReal.ofReal_eq_coe_nnreal (by positivity)]
      apply congrArg (fun c : ℝ≥0 => (c : ENNReal) * edist x y ^ (α : ℝ))
      apply NNReal.eq
      rw [Real.coe_toNNReal _ (mul_nonneg (Real.sqrt_nonneg _)
        (NNReal.coe_nonneg C))]
      rfl

private theorem holderOnWith_zero_of_holderBoundOn
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α C : ℝ≥0} {U : Set E} {f : E → F}
    (hf : HolderBoundOn 0 α C U f) : HolderOnWith C α f U := by
  let L := continuousMultilinearCurryFin0 ℝ E F
  intro x hx y hy
  have h := hf.2 x hx y hy
  rw [iteratedFDeriv_zero_eq_comp] at h
  change edist (L.symm (f x)) (L.symm (f y)) ≤ _ at h
  rw [L.symm.edist_map] at h
  exact h

variable {n : ℕ}

private theorem hessian_entry_holderOnWith_of_orderTwoBound
    {α C : ℝ≥0} {K : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → ℝ}
    (hf : HolderBoundOn 2 α C K f)
    (hSmooth : ∀ z ∈ K, ContDiffAt ℝ 2 f z) (i j : Fin n) :
    HolderOnWith C α (fun z ↦ complexHessian f z i j) K := by
  let u : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single i 1
  let v : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j 1
  let iu := Complex.I • u
  let iv := Complex.I • v
  let D := iteratedFDeriv ℝ 2 f
  have hu : ‖u‖ = 1 := by simp [u]
  have hv : ‖v‖ = 1 := by simp [v]
  have hiu : ‖iu‖ = 1 := by simp [iu, hu, norm_smul, Complex.norm_I]
  have hiv : ‖iv‖ = 1 := by simp [iv, hv, norm_smul, Complex.norm_I]
  have hform (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ K) :
      complexHessian f z i j =
        ((D z ![u, v] : ℂ) + D z ![iu, iv] +
          Complex.I * (D z ![u, iv] - D z ![iu, v])) / 4 := by
    rw [complexHessian_apply (hSmooth z hz) i j]
    rw [show fderiv ℝ (fderiv ℝ f) z u v = D z ![u, v] by
          simpa [D] using (iteratedFDeriv_two_apply f z ![u, v]).symm,
      show fderiv ℝ (fderiv ℝ f) z iu iv = D z ![iu, iv] by
          simpa [D] using (iteratedFDeriv_two_apply f z ![iu, iv]).symm,
      show fderiv ℝ (fderiv ℝ f) z u iv = D z ![u, iv] by
          simpa [D] using (iteratedFDeriv_two_apply f z ![u, iv]).symm,
      show fderiv ℝ (fderiv ℝ f) z iu v = D z ![iu, v] by
          simpa [D] using (iteratedFDeriv_two_apply f z ![iu, v]).symm]
  have hD (x : EuclideanSpace ℂ (Fin n)) (hx : x ∈ K)
      (y : EuclideanSpace ℂ (Fin n)) (hy : y ∈ K) :
      ‖D x - D y‖ ≤ (C : ℝ) * dist x y ^ (α : ℝ) := by
    have h := hf.2.dist_le hx hy
    simpa only [dist_eq_norm] using h
  have hEval (T : (EuclideanSpace ℂ (Fin n) [×2]→L[ℝ] ℝ))
      (w : Fin 2 → EuclideanSpace ℂ (Fin n)) (hw : ∀ k, ‖w k‖ = 1) :
      ‖T w‖ ≤ ‖T‖ := by
    calc
      ‖T w‖ ≤ ‖T‖ * ∏ k, ‖w k‖ := ContinuousMultilinearMap.le_opNorm T w
      _ = ‖T‖ := by simp [hw]
  have huvv (w : Fin 2 → EuclideanSpace ℂ (Fin n))
      (w0 : ‖w 0‖ = 1) (w1 : ‖w 1‖ = 1) : ∀ k, ‖w k‖ = 1 := by
    intro k
    fin_cases k
    · exact w0
    · exact w1
  have hdiff (x : EuclideanSpace ℂ (Fin n)) (hx : x ∈ K)
      (y : EuclideanSpace ℂ (Fin n)) (hy : y ∈ K) :
      complexHessian f x i j - complexHessian f y i j =
        (((D x - D y) ![u, v] : ℂ) + (D x - D y) ![iu, iv] +
          Complex.I * ((D x - D y) ![u, iv] - (D x - D y) ![iu, v])) / 4 := by
    rw [hform x hx, hform y hy]
    simp only [sub_apply]
    field_simp
    push_cast
    ring
  intro x hx y hy
  rw [edist_dist]
  have hnum :
      ‖(((D x - D y) ![u, v] : ℝ) : ℂ) + (D x - D y) ![iu, iv] +
        Complex.I * ((D x - D y) ![u, iv] - (D x - D y) ![iu, v])‖ ≤
      4 * ‖D x - D y‖ := by
    have h1 := hEval (D x - D y) ![u, v] (huvv _ hu hv)
    have h2 := hEval (D x - D y) ![iu, iv] (huvv _ hiu hiv)
    have h3 := hEval (D x - D y) ![u, iv] (huvv _ hu hiv)
    have h4 := hEval (D x - D y) ![iu, v] (huvv _ hiu hv)
    let a : ℝ := (D x) ![u, v]
    let b : ℝ := (D x) ![iu, iv]
    let c : ℝ := (D x) ![u, iv]
    let d : ℝ := (D x) ![iu, v]
    let a' : ℝ := (D y) ![u, v]
    let b' : ℝ := (D y) ![iu, iv]
    let c' : ℝ := (D y) ![u, iv]
    let d' : ℝ := (D y) ![iu, v]
    have h1C : ‖Complex.ofReal a - Complex.ofReal a'‖ ≤ ‖D x - D y‖ := by
      rw [← Complex.ofReal_sub, Complex.norm_real]
      simpa [a, a', sub_apply] using h1
    have h2C : ‖Complex.ofReal b - Complex.ofReal b'‖ ≤ ‖D x - D y‖ := by
      rw [← Complex.ofReal_sub, Complex.norm_real]
      simpa [b, b', sub_apply] using h2
    have h3C : ‖Complex.ofReal c - Complex.ofReal c'‖ ≤ ‖D x - D y‖ := by
      rw [← Complex.ofReal_sub, Complex.norm_real]
      simpa [c, c', sub_apply] using h3
    have h4C : ‖Complex.ofReal d - Complex.ofReal d'‖ ≤ ‖D x - D y‖ := by
      rw [← Complex.ofReal_sub, Complex.norm_real]
      simpa [d, d', sub_apply] using h4
    have hrest : ‖Complex.I * ((Complex.ofReal c - Complex.ofReal c') -
        (Complex.ofReal d - Complex.ofReal d'))‖ ≤
        ‖D x - D y‖ + ‖D x - D y‖ := by
      rw [norm_mul, Complex.norm_I]
      simpa only [one_mul] using (norm_sub_le _ _).trans (add_le_add h3C h4C)
    have htri : ‖Complex.ofReal (a - a') + Complex.ofReal (b - b') +
        Complex.I * ((Complex.ofReal c - Complex.ofReal c') -
          (Complex.ofReal d - Complex.ofReal d'))‖ ≤
        ‖Complex.ofReal (a - a')‖ + ‖Complex.ofReal (b - b')‖ +
          ‖D x - D y‖ + ‖D x - D y‖ := by
      calc
        _ ≤ ‖Complex.ofReal (a - a')‖ + ‖Complex.ofReal (b - b')‖ +
            ‖Complex.I * ((Complex.ofReal c - Complex.ofReal c') -
              (Complex.ofReal d - Complex.ofReal d'))‖ := by
          calc
            _ ≤ ‖Complex.ofReal (a - a') + Complex.ofReal (b - b')‖ +
                ‖Complex.I * ((Complex.ofReal c - Complex.ofReal c') -
                  (Complex.ofReal d - Complex.ofReal d'))‖ := norm_add_le _ _
            _ ≤ _ := by exact add_le_add (norm_add_le _ _) le_rfl
        _ ≤ _ := by
          have h := add_le_add_left hrest
            (‖Complex.ofReal (a - a')‖ + ‖Complex.ofReal (b - b')‖)
          nlinarith
    calc
      _ = ‖Complex.ofReal (a - a') + Complex.ofReal (b - b') +
          Complex.I * ((Complex.ofReal c - Complex.ofReal c') -
            (Complex.ofReal d - Complex.ofReal d'))‖ := by
        simp [a, b, c, d, a', b', c', d', Complex.ofReal_sub,
          sub_apply]
      _ ≤ ‖D x - D y‖ + ‖D x - D y‖ +
          (‖D x - D y‖ + ‖D x - D y‖) := by
        have h1R : ‖Complex.ofReal (a - a')‖ ≤ ‖D x - D y‖ := by
          simpa [Complex.norm_real] using h1C
        have h2R : ‖Complex.ofReal (b - b')‖ ≤ ‖D x - D y‖ := by
          simpa [Complex.norm_real] using h2C
        have hrest' := hrest
        nlinarith [htri, h1R, h2R, hrest']
      _ = 4 * ‖D x - D y‖ := by ring
  calc
    ENNReal.ofReal (dist (complexHessian f x i j) (complexHessian f y i j)) =
        ENNReal.ofReal ‖complexHessian f x i j - complexHessian f y i j‖ := by
          rw [dist_eq_norm]
    _ ≤ ENNReal.ofReal (‖D x - D y‖) := by
      apply ENNReal.ofReal_le_ofReal
      rw [hdiff x hx y hy, norm_div, Complex.norm_ofNat]
      have hden : (0 : ℝ) < 4 := by norm_num
      calc
        ‖(((D x - D y) ![u, v] : ℝ) : ℂ) + (D x - D y) ![iu, iv] +
            Complex.I * ((D x - D y) ![u, iv] - (D x - D y) ![iu, v])‖ / 4 ≤
            (4 * ‖D x - D y‖) / 4 := div_le_div_of_nonneg_right hnum (by positivity)
        _ = ‖D x - D y‖ := by norm_num
    _ ≤ ENNReal.ofReal ((C : ℝ) * dist x y ^ (α : ℝ)) :=
      ENNReal.ofReal_le_ofReal (hD x hx y hy)
    _ = (C : ENNReal) * edist x y ^ (α : ℝ) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      rw [← ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) α.coe_nonneg, ← edist_dist]
      rw [ENNReal.ofReal_coe_nnreal]

private theorem hessian_entry_norm_le_of_orderTwoBound
    {α C : ℝ≥0} {K : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → ℝ}
    (hf : HolderBoundOn 2 α C K f)
    (hSmooth : ∀ z ∈ K, ContDiffAt ℝ 2 f z) (i j : Fin n)
    {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ K) :
    ‖complexHessian f z i j‖ ≤ (C : ℝ) := by
  let u : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single i 1
  let v : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j 1
  let iu := Complex.I • u
  let iv := Complex.I • v
  let D := iteratedFDeriv ℝ 2 f
  have hu : ‖u‖ = 1 := by simp [u]
  have hv : ‖v‖ = 1 := by simp [v]
  have hiu : ‖iu‖ = 1 := by simp [iu, hu, norm_smul, Complex.norm_I]
  have hiv : ‖iv‖ = 1 := by simp [iv, hv, norm_smul, Complex.norm_I]
  have hform : complexHessian f z i j =
      ((D z ![u, v] : ℂ) + D z ![iu, iv] +
        Complex.I * (D z ![u, iv] - D z ![iu, v])) / 4 := by
    rw [complexHessian_apply (hSmooth z hz) i j]
    rw [show fderiv ℝ (fderiv ℝ f) z u v = D z ![u, v] by
          simpa [D] using (iteratedFDeriv_two_apply f z ![u, v]).symm,
      show fderiv ℝ (fderiv ℝ f) z iu iv = D z ![iu, iv] by
          simpa [D] using (iteratedFDeriv_two_apply f z ![iu, iv]).symm,
      show fderiv ℝ (fderiv ℝ f) z u iv = D z ![u, iv] by
          simpa [D] using (iteratedFDeriv_two_apply f z ![u, iv]).symm,
      show fderiv ℝ (fderiv ℝ f) z iu v = D z ![iu, v] by
          simpa [D] using (iteratedFDeriv_two_apply f z ![iu, v]).symm]
  have hEval (w : Fin 2 → EuclideanSpace ℂ (Fin n))
      (hw0 : ‖w 0‖ = 1) (hw1 : ‖w 1‖ = 1) : ‖D z w‖ ≤ ‖D z‖ := by
    calc
      ‖D z w‖ ≤ ‖D z‖ * ∏ k, ‖w k‖ := ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖D z‖ := by simp [hw0, hw1]
  have hD : ‖D z‖ ≤ (C : ℝ) := hf.1 2 le_rfl z hz
  have h1 : ‖((D z ![u, v] : ℝ) : ℂ)‖ ≤ (C : ℝ) := by
    simpa [Complex.norm_real] using (hEval ![u, v] hu hv).trans hD
  have h2 : ‖((D z ![iu, iv] : ℝ) : ℂ)‖ ≤ (C : ℝ) := by
    simpa [Complex.norm_real] using (hEval ![iu, iv] hiu hiv).trans hD
  have h3 : ‖((D z ![u, iv] : ℝ) : ℂ)‖ ≤ (C : ℝ) := by
    simpa [Complex.norm_real] using (hEval ![u, iv] hu hiv).trans hD
  have h4 : ‖((D z ![iu, v] : ℝ) : ℂ)‖ ≤ (C : ℝ) := by
    simpa [Complex.norm_real] using (hEval ![iu, v] hiu hv).trans hD
  have hCross : ‖Complex.I * ((D z ![u, iv] : ℂ) - D z ![iu, v])‖ ≤
      (C : ℝ) + C := by
    rw [norm_mul, Complex.norm_I, one_mul]
    exact (norm_sub_le _ _).trans (add_le_add h3 h4)
  have hNumerator : ‖(D z ![u, v] : ℂ) + D z ![iu, iv] +
      Complex.I * (D z ![u, iv] - D z ![iu, v])‖ ≤
      (C : ℝ) + C + ((C : ℝ) + C) := by
    calc
      _ ≤ ‖(D z ![u, v] : ℂ)‖ + ‖(D z ![iu, iv] : ℂ)‖ +
          ‖Complex.I * (D z ![u, iv] - D z ![iu, v])‖ := by
        calc
          _ ≤ ‖(D z ![u, v] : ℂ) + D z ![iu, iv]‖ +
              ‖Complex.I * (D z ![u, iv] - D z ![iu, v])‖ := norm_add_le _ _
          _ ≤ _ := by exact add_le_add (norm_add_le _ _) le_rfl
      _ ≤ (C : ℝ) + C + ((C : ℝ) + C) := add_le_add (add_le_add h1 h2) hCross
  rw [hform, norm_div, Complex.norm_ofNat]
  calc
    ‖(D z ![u, v] : ℂ) + D z ![iu, iv] +
        Complex.I * (D z ![u, iv] - D z ![iu, v])‖ / 4 ≤
        ((C : ℝ) + C + ((C : ℝ) + C)) / 4 :=
      div_le_div_of_nonneg_right hNumerator (by norm_num)
    _ = C := by ring

private theorem hessian_matrix_holderBoundOn_zero_of_orderTwoBound
    {α C : ℝ≥0} {K : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → ℝ}
    (hf : HolderBoundOn 2 α C K f)
    (hSmooth : ∀ z ∈ K, ContDiffAt ℝ 2 f z) :
    @HolderBoundOn (EuclideanSpace ℂ (Fin n)) _ _ (Matrix (Fin n) (Fin n) ℂ)
      Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace 0 α
      ((Real.sqrt (Fintype.card (Fin n × Fin n) : ℝ) * (C : ℝ)).toNNReal) K
      (fun z ↦ (fun i j ↦ complexHessian f z i j : Matrix (Fin n) (Fin n) ℂ)) := by
  let H : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun z i j ↦ complexHessian f z i j
  change @HolderBoundOn (EuclideanSpace ℂ (Fin n)) _ _ (Matrix (Fin n) (Fin n) ℂ)
    Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace 0 α
    ((Real.sqrt (Fintype.card (Fin n × Fin n) : ℝ) * (C : ℝ)).toNNReal) K H
  apply holderBoundOn_zero_from_holderOnWith
    (holderOnWith_frobenius_of_entrywise (fun i j ↦
      hessian_entry_holderOnWith_of_orderTwoBound hf hSmooth i j))
  intro z hz
  change ‖H z‖ ≤ _
  calc
    ‖H z‖ ≤ Real.sqrt (Fintype.card (Fin n × Fin n) : ℝ) * (C : ℝ) :=
      frobenius_norm_le_of_entry_bound (H z) (C : ℝ) (NNReal.coe_nonneg C) (by
        intro i j
        exact hessian_entry_norm_le_of_orderTwoBound hf hSmooth i j hz)
    _ = ((Real.sqrt (Fintype.card (Fin n × Fin n) : ℝ) * (C : ℝ)).toNNReal : ℝ) :=
      (Real.coe_toNNReal _ (mul_nonneg (Real.sqrt_nonneg _) (NNReal.coe_nonneg C))).symm
private theorem hessian_entry_holderBoundOn_zero_of_orderTwoBound
    {α C : ℝ≥0} {K : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → ℝ}
    (hf : HolderBoundOn 2 α C K f)
    (hSmooth : ∀ z ∈ K, ContDiffAt ℝ 2 f z) (i j : Fin n) :
    HolderBoundOn 0 α C K (fun z ↦ complexHessian f z i j) := by
  apply holderBoundOn_zero_from_holderOnWith
    (hessian_entry_holderOnWith_of_orderTwoBound hf hSmooth i j)
  intro z hz
  exact hessian_entry_norm_le_of_orderTwoBound hf hSmooth i j hz

private theorem exists_actual_metric_chart_base_holder
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M]
    (ω₁ : KahlerForm n M) (α : ℝ≥0) (hα₁ : α < 1)
    [P : ContinuityHolderPair ω₁ α] :
    ∃ C : ℝ≥0, ∀ i,
      HolderBoundOn 0 α C (P.finiteChartCover.piece i)
        (fun z => ω₁.metricInChart (P.finiteChartCover.base i) z) := by
  classical
  let cover := P.finiteChartCover
  have hEntryLocal (i : cover.ι) (j k : Fin n) :
      ∃ C : ℝ≥0, HolderBoundOn 0 α C (cover.piece i)
        (fun z => ω₁.metricInChart (cover.base i) z j k) :=
    holderBoundOn_of_contDiffOn_compact
      (isOpen_extChartAt_target (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (cover.base i))
      (cover.isCompact_piece i) (cover.piece_in_target i)
      (ω₁.contDiffOn_metricInChart (cover.base i) j k) (le_of_lt hα₁)
  let c (p : cover.ι × Fin n × Fin n) : ℝ≥0 :=
    Classical.choose (hEntryLocal p.1 p.2.1 p.2.2)
  let C : ℝ≥0 := Finset.univ.sup c
  have hEntryBound (i : cover.ι) (j k : Fin n) :
      HolderBoundOn 0 α C (cover.piece i)
        (fun z => ω₁.metricInChart (cover.base i) z j k) := by
    have hle : c (i, j, k) ≤ C := Finset.le_sup (Finset.mem_univ (i, j, k))
    exact (Classical.choose_spec (hEntryLocal i j k)).mono_const hle
  let Cmatrix : ℝ≥0 :=
    (Real.sqrt (Fintype.card (Fin n × Fin n) : ℝ) * (C : ℝ)).toNNReal
  have hCmatrix : (Cmatrix : ℝ) =
      Real.sqrt (Fintype.card (Fin n × Fin n) : ℝ) * (C : ℝ) :=
    Real.coe_toNNReal _ (mul_nonneg (Real.sqrt_nonneg _) (NNReal.coe_nonneg C))
  refine ⟨Cmatrix, ?_⟩
  intro i
  have hEntryHolder (j k : Fin n) :
      HolderOnWith C α (fun z => ω₁.metricInChart (cover.base i) z j k)
        (cover.piece i) :=
    holderOnWith_zero_of_holderBoundOn (hEntryBound i j k)
  have hHolder : HolderOnWith Cmatrix α
      (fun z => ω₁.metricInChart (cover.base i) z) (cover.piece i) :=
    holderOnWith_frobenius_of_entrywise hEntryHolder
  apply holderBoundOn_zero_from_holderOnWith hHolder
  intro z hz
  have hEntryNorm (j k : Fin n) :
      ‖ω₁.metricInChart (cover.base i) z j k‖ ≤ (C : ℝ) := by
    simpa [norm_iteratedFDeriv_zero] using
      (hEntryBound i j k).1 0 (by omega) z hz
  calc
    ‖ω₁.metricInChart (cover.base i) z‖ ≤
        Real.sqrt (Fintype.card (Fin n × Fin n) : ℝ) * (C : ℝ) :=
      frobenius_norm_le_of_entry_bound _ (C : ℝ) (NNReal.coe_nonneg C) hEntryNorm
    _ = (Cmatrix : ℝ) := hCmatrix.symm

private theorem posDef_affine_segment_control {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (s : ℝ) (hA : A.PosDef) (hB : B.PosDef)
    (hs : s ∈ Icc (0 : ℝ) 1) : ((1 - s) • A + s • B).PosDef := by
  by_cases hs0 : s = 0
  · simpa [hs0] using hA
  · by_cases hs1 : s = 1
    · simpa [hs1] using hB
    · have hleft : 0 < 1 - s :=
        lt_of_le_of_ne (sub_nonneg.mpr hs.2) (by intro h; apply hs1; linarith)
      have hright : 0 < s :=
        lt_of_le_of_ne hs.1 (by intro h; apply hs0; linarith)
      exact (hA.smul hleft).add (hB.smul hright)

private theorem compact_actual_chart_metric_control
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M]
    (ω₁ : KahlerForm n M) {α : ℝ≥0} [P : ContinuityHolderPair ω₁ α] :
    ∃ ε N : ℝ, 0 < ε ∧ 0 < N ∧
      ∀ i x y, x ∈ P.finiteChartCover.piece i → y ∈ P.finiteChartCover.piece i →
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ J : Matrix (Fin n) (Fin n) ℂ,
          J.IsHermitian → ‖J‖ < ε →
          (((1 - s) • ω₁.metricInChart (P.finiteChartCover.base i) x +
              s • ω₁.metricInChart (P.finiteChartCover.base i) y + J).PosDef ∧
            ‖((1 - s) • ω₁.metricInChart (P.finiteChartCover.base i) x +
              s • ω₁.metricInChart (P.finiteChartCover.base i) y + J)⁻¹‖ ≤ N) := by
  classical
  let cover := P.finiteChartCover
  let Piece (i : cover.ι) := {z : EuclideanSpace ℂ (Fin n) // z ∈ cover.piece i}
  let Segment := {s : ℝ // s ∈ Icc (0 : ℝ) 1}
  let X := Σ i : cover.ι, Piece i × (Piece i × Segment)
  let : ∀ i, CompactSpace (Piece i) := fun i =>
    isCompact_iff_compactSpace.mp (cover.isCompact_piece i)
  let : CompactSpace Segment := isCompact_iff_compactSpace.mp isCompact_Icc
  let : CompactSpace X := by dsimp [X, Piece, Segment]; infer_instance
  let A : X → Matrix (Fin n) (Fin n) ℂ := fun q =>
    (1 - q.2.2.2.val) • ω₁.metricInChart (cover.base q.1) q.2.1.val +
      q.2.2.2.val • ω₁.metricInChart (cover.base q.1) q.2.2.1.val
  have hentryCont (i : cover.ι) (j k : Fin n) :
      Continuous (fun z : Piece i => ω₁.metricInChart (cover.base i) z.1 j k) := by
    rw [continuous_iff_continuousAt]
    intro z
    have hz : z.1 ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).target :=
      cover.piece_in_target i z.2
    exact (((ω₁.contDiffOn_metricInChart (cover.base i) j k).contDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
        (x := cover.base i)).mem_nhds hz)).continuousAt).comp
          continuous_subtype_val.continuousAt
  have hmetricCont (i : cover.ι) :
      Continuous (fun z : Piece i => ω₁.metricInChart (cover.base i) z.1) := by
    exact continuous_pi (fun j => continuous_pi (fun k => hentryCont i j k))
  have hAcont : Continuous A := by
    apply continuous_sigma
    intro i
    let sfun : Continuous (fun p : Piece i × (Piece i × Segment) => (p.2.2 : ℝ)) :=
      continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
    let hleft : Continuous (fun p : Piece i × (Piece i × Segment) =>
        ω₁.metricInChart (cover.base i) p.1) := hmetricCont i |>.comp continuous_fst
    let hright : Continuous (fun p : Piece i × (Piece i × Segment) =>
        ω₁.metricInChart (cover.base i) p.2.1) :=
      hmetricCont i |>.comp (continuous_fst.comp continuous_snd)
    have h₁ : Continuous (fun p : Piece i × (Piece i × Segment) =>
        (1 - (p.2.2 : ℝ)) • ω₁.metricInChart (cover.base i) p.1) :=
      (continuous_const.sub sfun).smul hleft
    have h₂ : Continuous (fun p : Piece i × (Piece i × Segment) =>
        (p.2.2 : ℝ) • ω₁.metricInChart (cover.base i) p.2.1) := sfun.smul hright
    exact h₁.add h₂
  have hApos (q : X) : (A q).PosDef := by
    dsimp [A]
    apply posDef_affine_segment_control
    · exact ω₁.posDef_metricInChart (cover.base q.1)
        (cover.piece_in_target q.1 q.2.1.property)
    · exact ω₁.posDef_metricInChart (cover.base q.1)
        (cover.piece_in_target q.1 q.2.2.1.property)
    · exact q.2.2.2.property
  obtain ⟨ε, N, hε, hN, hctrl⟩ :=
    Matrix.exists_compact_uniform_hermitian_perturbation_resolvent_control A hAcont hApos
  refine ⟨ε, N, hε, hN, ?_⟩
  intro i x y hx hy s hs J hJ hJnorm
  let q : X := ⟨i, ⟨x, hx⟩, ⟨⟨y, hy⟩, ⟨s, hs⟩⟩⟩
  have h := hctrl q J hJ hJnorm
  simpa [A, q, cover, Piece, Segment] using h

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]

omit [ConnectedSpace M] in
private theorem evalC2_contMDiff_two
    (ω₁ : KahlerForm n M) (α : ℝ≥0) [P : ContinuityHolderPair ω₁ α]
    (u : P.C2) : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 (P.evalC2 u) := by
  have heq : P.evalC2 u = smoothChartHolderContinuousMapExtension P.finiteChartCover 2 α
      P.normedDataC2 (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2) := by
    funext x
    rfl
  rw [heq]
  exact compactControl_smoothChartHolderContinuousMapExtension_contMDiff_orderTwo_of_completedJets
    P.finiteChartCover α P.normedDataC2
    (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2)
    (fun j hj i z hz => smoothChartHolderContinuousMapExtension_completedJet_eq
      P.finiteChartCover α P.normedDataC2
      (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2) j hj i z hz)
    (fun j hj i z hz => smoothChartHolderContinuousMapExtension_completedJet_norm_le
      P.finiteChartCover α P.normedDataC2
      (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2) j hj i z hz)

omit [ConnectedSpace M] in
private theorem evalC2_chart_contDiffAt_two
    (ω₁ : KahlerForm n M) (α : ℝ≥0) [P : ContinuityHolderPair ω₁ α]
    (u : P.C2) (i : P.finiteChartCover.ι) {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      (P.finiteChartCover.base i)).target) :
    ContDiffAt ℝ 2
      ((P.evalC2 u) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
        (P.finiteChartCover.base i)).symm) z := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (P.finiteChartCover.base i)
  have hsmoothTop : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ e.symm z :=
    (contMDiffOn_extChartAt_symm
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (P.finiteChartCover.base i)).contMDiffAt
        ((isOpen_extChartAt_target (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
          (P.finiteChartCover.base i)).mem_nhds hz)
  have hsmooth : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 2 e.symm z := by
    exact hsmoothTop.of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  exact (contMDiffAt_iff_contDiffAt).mp
    ((evalC2_contMDiff_two ω₁ α u (e.symm z)).comp_of_eq hsmooth rfl)

private theorem chartTaylorH_sub
    (ω₁ : KahlerForm n M) (α : ℝ≥0) [P : ContinuityHolderPair ω₁ α]
    (u v : P.C2) (i : P.finiteChartCover.ι) (z : EuclideanSpace ℂ (Fin n))
    (hz : z ∈ P.finiteChartCover.piece i) :
    chartTaylorH P (u - v) i z = chartTaylorH P u i z - chartTaylorH P v i z := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (P.finiteChartCover.base i)
  let fu := (P.evalC2 u) ∘ e.symm
  let fv := (P.evalC2 v) ∘ e.symm
  let fuv := (P.evalC2 (u - v)) ∘ e.symm
  have heval : P.evalC2 (u - v) = P.evalC2 u - P.evalC2 v := by
    exact map_sub P.evalC2 u v
  have hfuv : fuv = fu - fv := by
    funext x
    change P.evalC2 (u - v) (e.symm x) =
      P.evalC2 u (e.symm x) - P.evalC2 v (e.symm x)
    rw [heval]
    rfl
  have hfu : ContDiffAt ℝ 2 fu z :=
    evalC2_chart_contDiffAt_two ω₁ α u i (P.finiteChartCover.piece_in_target i hz)
  have hfv : ContDiffAt ℝ 2 fv z :=
    evalC2_chart_contDiffAt_two ω₁ α v i (P.finiteChartCover.piece_in_target i hz)
  have hfuvSmooth : ContDiffAt ℝ 2 fuv z := by
    rw [hfuv]
    exact hfu.sub hfv
  have hjet : iteratedFDeriv ℝ 2 fuv z =
      iteratedFDeriv ℝ 2 fu z - iteratedFDeriv ℝ 2 fv z := by
    rw [hfuv]
    exact iteratedFDeriv_sub_apply hfu hfv
  have hsecond (a b : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fderiv ℝ fuv) z a b =
        fderiv ℝ (fderiv ℝ fu) z a b - fderiv ℝ (fderiv ℝ fv) z a b := by
    have hduv : fderiv ℝ (fderiv ℝ fuv) z a b =
        iteratedFDeriv ℝ 2 fuv z ![a, b] := by
      simpa using (iteratedFDeriv_two_apply fuv z ![a, b]).symm
    have hdu : fderiv ℝ (fderiv ℝ fu) z a b =
        iteratedFDeriv ℝ 2 fu z ![a, b] := by
      simpa using (iteratedFDeriv_two_apply fu z ![a, b]).symm
    have hdv : fderiv ℝ (fderiv ℝ fv) z a b =
        iteratedFDeriv ℝ 2 fv z ![a, b] := by
      simpa using (iteratedFDeriv_two_apply fv z ![a, b]).symm
    calc
      fderiv ℝ (fderiv ℝ fuv) z a b = iteratedFDeriv ℝ 2 fuv z ![a, b] := hduv
      _ = iteratedFDeriv ℝ 2 fu z ![a, b] - iteratedFDeriv ℝ 2 fv z ![a, b] := by
        rw [hjet]
        simp
      _ = fderiv ℝ (fderiv ℝ fu) z a b - fderiv ℝ (fderiv ℝ fv) z a b := by
        rw [hdu, hdv]
  change complexHessian fuv z = complexHessian fu z - complexHessian fv z
  ext j k
  rw [complexHessian_apply hfuvSmooth j k]
  rw [Matrix.sub_apply]
  rw [complexHessian_apply hfu j k, complexHessian_apply hfv j k]
  rw [hsecond (EuclideanSpace.single j 1) (EuclideanSpace.single k 1),
    hsecond (Complex.I • EuclideanSpace.single j 1) (Complex.I • EuclideanSpace.single k 1),
    hsecond (EuclideanSpace.single j 1) (Complex.I • EuclideanSpace.single k 1),
    hsecond (Complex.I • EuclideanSpace.single j 1) (EuclideanSpace.single k 1)]
  push_cast
  ring

private theorem chartTaylorH_hermitian
    (ω₁ : KahlerForm n M) (α : ℝ≥0) [P : ContinuityHolderPair ω₁ α]
    (u : P.C2) (i : P.finiteChartCover.ι) (z : EuclideanSpace ℂ (Fin n))
    (hz : z ∈ P.finiteChartCover.piece i) :
    (chartTaylorH P u i z).IsHermitian := by
  let f := (P.evalC2 u) ∘
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (P.finiteChartCover.base i)).symm
  have hf : ContDiffAt ℝ 2 f z :=
    evalC2_chart_contDiffAt_two ω₁ α u i
      (P.finiteChartCover.piece_in_target i hz)
  change (ddbar f z).coeffMatrix.IsHermitian
  exact (isOneOne_ddbar hf).isHermitian_coeffMatrix

private theorem real_toNNReal_mul_coe (r : ℝ) (hr : 0 ≤ r) (c : ℝ≥0) :
    (r * (c : ℝ)).toNNReal = r.toNNReal * c := by
  apply NNReal.eq
  simp only [NNReal.coe_mul]
  rw [Real.coe_toNNReal _ (mul_nonneg hr (NNReal.coe_nonneg c))]
  rw [Real.coe_toNNReal _ hr]

private theorem exists_actualChartTaylorControl_of_commonCone
    (ω₁ : KahlerForm n M) (α : ℝ≥0) (hα₁ : α < 1)
    [P : ContinuityHolderPair ω₁ α]
    (hjet : ∀ (u : P.C2) i,
      HolderBoundOn 2 α ‖u‖₊ (P.finiteChartCover.piece i)
        ((P.evalC2 u) ∘
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
            (P.finiteChartCover.base i)).symm))
    (ε N : ℝ) (hε : 0 < ε) (hN : 0 < N)
    (hcone : ∀ i x y, x ∈ P.finiteChartCover.piece i →
      y ∈ P.finiteChartCover.piece i → ∀ s ∈ Icc (0 : ℝ) 1,
        ∀ J : Matrix (Fin n) (Fin n) ℂ, J.IsHermitian → ‖J‖ < ε →
          (((1 - s) • ω₁.metricInChart (P.finiteChartCover.base i) x +
              s • ω₁.metricInChart (P.finiteChartCover.base i) y + J).PosDef ∧
            ‖((1 - s) • ω₁.metricInChart (P.finiteChartCover.base i) x +
              s • ω₁.metricInChart (P.finiteChartCover.base i) y + J)⁻¹‖ ≤ N)) :
    Nonempty (ChartTaylorControl α P.finiteChartCover.piece
      (fun i z ↦ ω₁.metricInChart (P.finiteChartCover.base i) z)
      (chartTaylorH P)) := by
  obtain ⟨baseConstant, hBaseHolder⟩ :=
    exists_actual_metric_chart_base_holder ω₁ α hα₁
  let jetConstant : ℝ≥0 :=
    (Real.sqrt (Fintype.card (Fin n × Fin n) : ℝ)).toNNReal
  have hJetHolder (u : P.C2) (i : P.finiteChartCover.ι) :
      HolderBoundOn 0 α (jetConstant * ‖u‖₊) (P.finiteChartCover.piece i)
        (fun z => chartTaylorH P u i z) := by
    let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      (P.finiteChartCover.base i)
    let f := (P.evalC2 u) ∘ e.symm
    have hSmooth (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ P.finiteChartCover.piece i) :
        ContDiffAt ℝ 2 f z :=
      evalC2_chart_contDiffAt_two ω₁ α u i
        (P.finiteChartCover.piece_in_target i hz)
    have hMatrix := hessian_matrix_holderBoundOn_zero_of_orderTwoBound
      (hjet u i) hSmooth
    have hScale :
        (Real.sqrt (Fintype.card (Fin n × Fin n) : ℝ) * (‖u‖₊ : ℝ)).toNNReal =
          jetConstant * ‖u‖₊ :=
      real_toNNReal_mul_coe (Real.sqrt (Fintype.card (Fin n × Fin n) : ℝ))
        (Real.sqrt_nonneg _) ‖u‖₊
    rw [hScale] at hMatrix
    exact hMatrix
  have hNcoe : (N.toNNReal : ℝ) = N :=
    Real.coe_toNNReal N (le_of_lt hN)
  refine ⟨{
    baseConstant := baseConstant
    jetConstant := jetConstant
    epsilon := ε
    epsilon_pos := hε
    inverseBound := N.toNNReal
    inverseBound_pos := by
      exact_mod_cast (show 0 < (N.toNNReal : ℝ) by rw [hNcoe]; exact hN)
    baseHolder := hBaseHolder
    jetHolder := hJetHolder
    jet_sub := by
      intro u v i z hz
      exact chartTaylorH_sub ω₁ α u v i z hz
    jet_hermitian := by
      intro u i z hz
      exact chartTaylorH_hermitian ω₁ α u i z hz
    smallHermitian := by
      intro i x y hx hy s hs J hJ hJnorm
      rcases hcone i x y hx hy s hs J hJ hJnorm with ⟨hp, hinv⟩
      refine ⟨hp, ?_⟩
      rw [hNcoe]
      exact hinv
  }⟩

/-- A single strictly positive Hermitian neighborhood and finite inverse bound,
with the order-two bounds transported to the actual evaluated Hessian matrices. -/
theorem exists_actualChartTaylorControl
    (ω₁ : KahlerForm n M) (α : ℝ≥0) (hα₁ : α < 1)
    [P : ContinuityHolderPair ω₁ α]
    (hjet : ∀ (u : P.C2) i,
      HolderBoundOn 2 α ‖u‖₊ (P.finiteChartCover.piece i)
        ((P.evalC2 u) ∘
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
            (P.finiteChartCover.base i)).symm)) :
    Nonempty (ChartTaylorControl α P.finiteChartCover.piece
      (fun i z ↦ ω₁.metricInChart (P.finiteChartCover.base i) z)
      (chartTaylorH P)) := by
  obtain ⟨ε, N, hε, hN, hcone⟩ :=
    compact_actual_chart_metric_control (α := α) ω₁
  exact exists_actualChartTaylorControl_of_commonCone
    ω₁ α hα₁ hjet ε N hε hN hcone

end KahlerForm
