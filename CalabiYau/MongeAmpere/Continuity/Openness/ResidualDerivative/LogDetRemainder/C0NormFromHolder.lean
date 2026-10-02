module

public import CalabiYau.MongeAmpere.Continuity.Openness.HolderSpaces

/-!
# C⁰ completion norm from its chartwise Hölder representative

The order-zero mean-zero carrier is a completion in the finite-chart C^{0,α} gauge. Faithful
continuous evaluation lets one recover its completed chart data from the represented function.
-/

@[expose] public section

noncomputable section

open scoped Manifold ContDiff NNReal Topology

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]

omit [ConnectedSpace M] in
/-- A faithfully evaluated mean-zero C⁰ completion element with a chartwise `HolderBoundOn` bound
has completion norm bounded by twice the order-zero chart-gauge constant. -/
@[deprecated "unused hypothesis `hEval`; will be removed" (since := "2026-10-02")]
theorem meanZeroC0_norm_le_of_chartHolderBound
    (ω₁ : KahlerForm n M) (α : ℝ≥0)
    [P : ContinuityHolderPair ω₁ α]
    (v : P.C0) (hEval : Function.Injective P.evalC0)
    (K : ℝ≥0)
    (hK : ∀ i, HolderBoundOn 0 α K (P.finiteChartCover.piece i)
      (P.evalC0 v ∘
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
          (P.finiteChartCover.base i)).symm) ) :
    ‖v‖ ≤ 2 * (K : ℝ) := by
  classical
  let cover := P.finiteChartCover
  let N := P.normedDataC0
  let F := smoothChartHolderContinuousMapExtension cover 0 α N
  let core := SmoothChartHolderCore cover 0 α
  let completion := LittleHolder cover 0 α N
  let vcomp : completion := v
  let f : M → ℝ := P.evalC0 v
  let : NormedAddCommGroup core := smoothChartHolderCoreNormedAddCommGroup cover 0 α N
  let : NormedSpace ℝ core := smoothChartHolderCoreNormedSpace cover 0 α N
  have hdense (m : ℕ) : ∃ a : core,
      dist vcomp (a : completion) < 1 / ((m : ℝ) + 1) := by
    have hcl := (Metric.mem_closure_iff.mp (UniformSpace.Completion.denseRange_coe vcomp))
      (1 / ((m : ℝ) + 1)) (by positivity)
    rcases hcl with ⟨a, ha, hdist⟩
    rcases ha with ⟨a, rfl⟩
    exact ⟨a, hdist⟩
  choose u hu using hdense
  have hseq : Filter.Tendsto (fun m => (u m : completion)) Filter.atTop (𝓝 vcomp) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    obtain ⟨Nε, hNε⟩ := exists_nat_gt (1 / ε)
    refine ⟨Nε, ?_⟩
    intro m hm
    have hfrac : 1 / ((m : ℝ) + 1) < ε := by
      have hlt : (1 / ε) < (m : ℝ) + 1 := by
        have hm' : (Nε : ℝ) ≤ m := by exact_mod_cast hm
        have hNε' : (1 / ε) < (Nε : ℝ) := by exact_mod_cast hNε
        linarith
      rw [div_lt_iff₀ (by positivity)]
      have hmul : (1 : ℝ) < ((m : ℝ) + 1) * ε :=
        (div_lt_iff₀ hε).mp hlt
      nlinarith
    exact (dist_comm _ _).trans_lt (hu m) |>.trans hfrac
  have hCauchy : CauchySeq u :=
    (UniformSpace.Completion.isUniformInducing_coe core).cauchy_map_iff.mp hseq.cauchySeq
  have hFseq : Filter.Tendsto (fun m => F (u m : completion)) Filter.atTop (𝓝 (F v)) :=
    (F.continuous.tendsto vcomp).comp hseq
  have hevalClose (δ : ℝ) (hδ : 0 < δ) :
      ∀ᶠ m in Filter.atTop, ‖F (u m : completion) - F v‖ < δ := by
    have hzero : Filter.Tendsto (fun m => F (u m : completion) - F vcomp) Filter.atTop
        (𝓝 (0 : C(M, ℝ))) := by
      have h := hFseq.sub_const (F vcomp)
      simpa [vcomp] using h
    have hnormzero : Filter.Tendsto (fun m => ‖F (u m : completion) - F vcomp‖)
        Filter.atTop (𝓝 0) := by
      change Filter.Tendsto ((fun g : C(M, ℝ) => ‖g‖) ∘
        (fun m => F (u m : completion) - F vcomp)) Filter.atTop (𝓝 0)
      simpa only [norm_zero] using
        (continuous_norm.tendsto (0 : C(M, ℝ))).comp hzero
    have hsmall := hnormzero.eventually (Metric.ball_mem_nhds 0 hδ)
    filter_upwards [hsmall] with m hm
    exact by simpa [Metric.mem_ball, Real.dist_eq] using hm
  have hFpoint (m : ℕ) (x : M) :
      (F (u m : completion)) x = (u m).smoothMap x := by
    dsimp [F, completion, core, N, cover]
    rw [smoothChartHolderContinuousMapExtension_coe]
    rfl
  have hpoint (x : M) : Filter.Tendsto (fun m => (u m).smoothMap x)
      Filter.atTop (𝓝 (f x)) := by
    have heval := ((ContinuousMap.evalCLM (R := ℝ) x).continuous.tendsto (F vcomp)).comp hFseq
    have heval' : Filter.Tendsto (fun m => (F (u m : completion)) x)
        Filter.atTop (𝓝 ((F v) x)) := by
      change Filter.Tendsto ((fun g : C(M, ℝ) => g x) ∘
        (fun m => F (u m : completion))) Filter.atTop (𝓝 ((F vcomp) x))
      exact heval
    have heq (m : ℕ) : (F (u m : completion)) x = (u m).smoothMap x := hFpoint m x
    have hv : (F vcomp) x = f x := by rfl
    rw [hv] at heval'
    exact heval'.congr' (Filter.Eventually.of_forall heq)
  have hcoreBound (δ : ℝ≥0) (hδ : 0 < δ) :
      ∀ᶠ m in Filter.atTop, ‖(u m : completion)‖ ≤ 2 * ((K : ℝ) + (δ : ℝ)) := by
    obtain ⟨Nδ, hNδ⟩ := Metric.cauchySeq_iff.mp hCauchy (δ : ℝ) (by exact_mod_cast hδ)
    have hclose := hevalClose (δ : ℝ) (by exact_mod_cast hδ)
    obtain ⟨Nclose, hNclose⟩ := Filter.eventually_atTop.1 hclose
    have hnear (m : ℕ) (hm : Nclose ≤ m) :
        ‖F (u m : completion) - F v‖ < δ := hNclose m hm
    have hholder (i : cover.ι) (m : ℕ) (hm : Nδ ≤ m) :
        HolderOnWith δ α (fun z =>
          iteratedFDeriv ℝ 0 ((u m).smoothMap ∘
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) z -
          iteratedFDeriv ℝ 0 (f ∘
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) z)
          (cover.piece i) := by
      let chart := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm
      let L := (continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℂ (Fin n)) ℝ).symm
      let jet (a : core) : EuclideanSpace ℂ (Fin n) →
          EuclideanSpace ℂ (Fin n) [×0]→L[ℝ] ℝ :=
        iteratedFDeriv ℝ 0 (a.smoothMap ∘ chart)
      have hsub (q : ℕ) : jet (u m - u q) = jet (u m) - jet (u q) := by
        funext z
        change L ((u m).smoothMap (chart z) - (u q).smoothMap (chart z)) = _
        exact L.map_sub _ _
      have hseminorm (q : ℕ) (hq : Nδ ≤ q) :
          CalabiYau.Schauder.eHolderSeminormOn α (cover.piece i)
            (jet (u m) - jet (u q)) ≤ (δ : ENNReal) := by
        calc
          CalabiYau.Schauder.eHolderSeminormOn α (cover.piece i) (jet (u m) - jet (u q)) =
              CalabiYau.Schauder.eHolderSeminormOn α (cover.piece i) (jet (u m - u q)) := by
                rw [← hsub q]
          _ ≤ CalabiYau.Schauder.eContDiffHolderGaugeOn 0 α (cover.piece i)
              ((u m - u q).smoothMap ∘ chart) := by
                unfold CalabiYau.Schauder.eContDiffHolderGaugeOn
                  CalabiYau.Schauder.eHolderSeminormOn
                simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
                exact le_add_left le_rfl
          _ ≤ smoothChartHolderGauge cover 0 α (u m - u q) :=
              le_iSup (fun j => CalabiYau.Schauder.eContDiffHolderGaugeOn 0 α
                (cover.piece j) ((u m - u q).smoothMap ∘
                  (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base j)).symm)) i
          _ = ENNReal.ofReal ‖u m - u q‖ := by
              have hfinite := N.finiteGauge (u m - u q)
              calc
                smoothChartHolderGauge cover 0 α (u m - u q) =
                    ENNReal.ofReal (smoothChartHolderGauge cover 0 α (u m - u q)).toReal :=
                  (ENNReal.ofReal_toReal (ne_of_lt hfinite)).symm
                _ = ENNReal.ofReal ‖u m - u q‖ := by
                  rw [← smoothChartHolderCore_norm_eq_gauge cover 0 α N]
          _ ≤ (δ : ENNReal) := by
              rw [← ENNReal.ofReal_coe_nnreal]
              apply ENNReal.ofReal_le_ofReal
              have hdist := hNδ m hm q hq
              simpa [dist_eq_norm] using hdist.le
      have hdiff (q : ℕ) (hq : Nδ ≤ q) : HolderOnWith δ α
          (fun z => jet (u m) z - jet (u q) z) (cover.piece i) :=
        HolderWith.restrict_iff.mp
          (CalabiYau.Schauder.holderWith_restrict_of_eHolderSeminormOn_le (hseminorm q hq))
      have hEventually : ∀ᶠ q in Filter.atTop, HolderOnWith δ α
          (fun z => jet (u m) z - jet (u q) z) (cover.piece i) := by
        filter_upwards [Filter.eventually_ge_atTop Nδ] with q hq
        exact hdiff q hq
      have hlim (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ cover.piece i) :
          Filter.Tendsto (fun q => jet (u m) z - jet (u q) z) Filter.atTop
            (𝓝 (iteratedFDeriv ℝ 0 ((u m).smoothMap ∘ chart) z -
              iteratedFDeriv ℝ 0 (f ∘ chart) z)) := by
        have Lcont := (continuousMultilinearCurryFin0 ℝ
          (EuclideanSpace ℂ (Fin n)) ℝ).symm.continuous
        have hjet : Filter.Tendsto (fun q => jet (u q) z) Filter.atTop
            (𝓝 (iteratedFDeriv ℝ 0 (f ∘ chart) z)) := by
          have hjet' := Lcont.continuousAt.tendsto.comp (hpoint (chart z))
          convert hjet' using 1
          · funext q
            simp [jet, iteratedFDeriv_zero_eq_comp]
          · simp [iteratedFDeriv_zero_eq_comp]
        exact tendsto_const_nhds.sub hjet
      have hclosed := CalabiYau.Schauder.holderOnWith_of_tendsto hEventually hlim
      simpa [jet, chart, Function.comp_def] using hclosed
    have hlocal (m : ℕ) (hm₁ : Nδ ≤ m) (hm₂ : Nclose ≤ m) (i : cover.ι) :
        HolderBoundOn 0 α (K + δ) (cover.piece i)
          ((u m).smoothMap ∘
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) := by
      let chart := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm
      have hpointwise (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ cover.piece i) :
          ‖iteratedFDeriv ℝ 0 ((u m).smoothMap ∘ chart) z‖ ≤ (K + δ : ℝ≥0) := by
        have hFclose := hnear m hm₂
        have hFv : ‖(F v) (chart z)‖ ≤ K := by
          have hb := (hK i).1 0 le_rfl z hz
          have heq : iteratedFDeriv ℝ 0 (f ∘ chart) z =
              (continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℂ (Fin n)) ℝ).symm (f (chart z)) := by
            simp [iteratedFDeriv_zero_eq_comp]
          have hbound : ‖f (chart z)‖ ≤ K := by
            simpa [f, chart, iteratedFDeriv_zero_eq_comp] using hb
          change ‖(F vcomp) (chart z)‖ ≤ K
          have hvalue : (F vcomp) (chart z) = f (chart z) := rfl
          rw [hvalue]
          exact hbound
        have hdiff := ContinuousMap.norm_coe_le_norm
          (F (u m : completion) - F v) (chart z)
        have hsum : (F (u m : completion)) (chart z) =
            (F (u m : completion) - F v) (chart z) + (F v) (chart z) := by
          simp
        have hval : ‖(u m).smoothMap (chart z)‖ ≤ (K : ℝ) + δ := by
          calc
            ‖(u m).smoothMap (chart z)‖ = ‖(F (u m : completion)) (chart z)‖ := by
              rw [← hFpoint m (chart z)]
            _ ≤ ‖(F (u m : completion) - F v) (chart z)‖ + ‖(F v) (chart z)‖ := by
              simpa only [hsum] using
                (norm_add_le ((F (u m : completion) - F v) (chart z)) ((F v) (chart z)))
            _ ≤ ‖F (u m : completion) - F v‖ + K := add_le_add hdiff hFv
            _ ≤ (K : ℝ) + δ := by linarith [hFclose.le]
        calc
          ‖iteratedFDeriv ℝ 0 ((u m).smoothMap ∘ chart) z‖ =
              ‖(u m).smoothMap (chart z)‖ := by simp
          _ ≤ (K + δ : ℝ≥0) := by exact_mod_cast hval
      have hholderSub := hholder i m hm₁
      have hlimitHolder : HolderWith K α
          ((cover.piece i).domRestrict
            (fun z => iteratedFDeriv ℝ 0 (f ∘ chart) z)) := by
        have hh := (hK i).2.holderWith
        simpa [f, chart, Function.comp_def] using hh
      have hremHolder : HolderWith δ α
          ((cover.piece i).domRestrict (fun z =>
            iteratedFDeriv ℝ 0 ((u m).smoothMap ∘ chart) z -
              iteratedFDeriv ℝ 0 (f ∘ chart) z)) :=
        hholderSub.holderWith
      have hsumHolder := hlimitHolder.add hremHolder
      refine ⟨?_, ?_⟩
      · intro j hj z hz
        have hj0 : j = 0 := by omega
        subst j
        have hb := hpointwise z hz
        exact_mod_cast hb
      · have hsumOn : HolderOnWith (K + δ) α
            (fun z => iteratedFDeriv ℝ 0 (f ∘ chart) z +
              (iteratedFDeriv ℝ 0 ((u m).smoothMap ∘ chart) z -
                iteratedFDeriv ℝ 0 (f ∘ chart) z)) (cover.piece i) :=
          HolderWith.restrict_iff.mp hsumHolder
        have hEq : (fun z => iteratedFDeriv ℝ 0 (f ∘ chart) z +
            (iteratedFDeriv ℝ 0 ((u m).smoothMap ∘ chart) z -
              iteratedFDeriv ℝ 0 (f ∘ chart) z)) =
            iteratedFDeriv ℝ 0 ((u m).smoothMap ∘ chart) := by
          funext z
          abel
        rw [hEq] at hsumOn
        simpa [chart, Function.comp_def] using hsumOn
    have hboundEventually : ∀ᶠ m in Filter.atTop, ‖(u m : completion)‖ ≤
        2 * ((K : ℝ) + (δ : ℝ)) := by
      filter_upwards [Filter.eventually_ge_atTop (max Nδ Nclose)] with m hm
      have hm₁ : Nδ ≤ m := le_trans (le_max_left _ _) hm
      have hm₂ : Nclose ≤ m := le_trans (le_max_right _ _) hm
      have hgaugeChart (i : cover.ι) :
          CalabiYau.Schauder.eContDiffHolderGaugeOn 0 α (cover.piece i)
            ((u m).smoothMap ∘
              (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) ≤
            (ENNReal.ofNNReal (2 * (K + δ))) := by
        have hb := hlocal m hm₁ hm₂ i
        have hle := CalabiYau.Schauder.eContDiffHolderGaugeOn_le (fun _ => K + δ)
          (K + δ) hb.1 hb.2.holderWith
        simpa [two_mul, Finset.sum_range_succ] using hle
      have hgauge : smoothChartHolderGauge cover 0 α (u m) ≤
          ENNReal.ofNNReal (2 * (K + δ)) := by
        apply iSup_le
        intro i
        exact hgaugeChart i
      have hcoreNorm : ‖u m‖ ≤ 2 * ((K : ℝ) + (δ : ℝ)) := by
        rw [smoothChartHolderCore_norm_eq_gauge cover 0 α N]
        calc
          (smoothChartHolderGauge cover 0 α (u m)).toReal ≤
              (ENNReal.ofNNReal (2 * (K + δ))).toReal :=
            ENNReal.toReal_mono ENNReal.coe_ne_top hgauge
          _ = 2 * ((K : ℝ) + (δ : ℝ)) := by
            rw [ENNReal.coe_toReal]
            exact_mod_cast (show (2 * (K + δ) : ℝ≥0) =
              2 * ((K : ℝ) + (δ : ℝ)) by norm_num [NNReal.coe_add, NNReal.coe_mul])
      simpa only [UniformSpace.Completion.norm_coe] using hcoreNorm
    exact hboundEventually
  have hnormseq : Filter.Tendsto (fun m => ‖(u m : completion)‖) Filter.atTop (𝓝 ‖vcomp‖) :=
    (continuous_norm.tendsto vcomp).comp hseq
  have hsmall (ε : ℝ) (hε : 0 < ε) : ‖v‖ ≤ 2 * ((K : ℝ) + ε) := by
    let εnn : ℝ≥0 := Real.toNNReal ε
    have hεnn : 0 < εnn := Real.toNNReal_pos.mpr hε
    have hevent := hcoreBound εnn hεnn
    have hle := le_of_tendsto hnormseq hevent
    have hcoe : (εnn : ℝ) = ε := Real.coe_toNNReal ε hε.le
    have hvnorm : ‖vcomp‖ = ‖v‖ := rfl
    rw [hvnorm, hcoe] at hle
    exact hle
  have hlim : ∀ ε : ℝ, 0 < ε → ‖v‖ ≤ 2 * ((K : ℝ) + ε) := hsmall
  have hresult : ‖v‖ ≤ 2 * (K : ℝ) := by
    by_contra hnot
    have hpos : 0 < ‖v‖ - 2 * (K : ℝ) := by linarith
    have hquarter : 0 < (‖v‖ - 2 * (K : ℝ)) / 4 := by positivity
    have hb := hlim ((‖v‖ - 2 * (K : ℝ)) / 4) hquarter
    nlinarith
  exact hresult

end KahlerForm
