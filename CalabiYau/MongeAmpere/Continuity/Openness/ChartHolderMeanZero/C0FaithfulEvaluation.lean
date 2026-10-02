module

public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderEvaluation

/-!
# Faithfulness of order-zero little-Hölder evaluation

Order-zero evaluation is faithful because the completion retains both uniform values and their
Hölder seminorm. If the limiting values vanish, closability of that seminorm forces the full
order-zero gauge to vanish.
-/

@[expose] public section

noncomputable section

open scoped Manifold ContDiff NNReal ENNReal Topology
open CalabiYau.Schauder Filter

namespace KahlerForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]

/-- Evaluation faithfully represents the order-zero little-Hölder completion on a compact,
finite-dimensional manifold. The statement includes `α = 0`, and in particular the flat
one-dimensional chart. -/
theorem smoothChartHolderContinuousMapExtension_C0_injective
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover 0 α) :
    Function.Injective (smoothChartHolderContinuousMapExtension cover 0 α N) := by
  classical
  let : NormedAddCommGroup (SmoothChartHolderCore cover 0 α) :=
    smoothChartHolderCoreNormedAddCommGroup cover 0 α N
  let : NormedSpace ℝ (SmoothChartHolderCore cover 0 α) :=
    smoothChartHolderCoreNormedSpace cover 0 α N
  intro x y hxy
  let F := smoothChartHolderContinuousMapExtension cover 0 α N
  let z := x - y
  have hz : F z = 0 := by
    change F (x - y) = 0
    rw [map_sub, hxy, sub_self]
  have hdense (n : ℕ) : ∃ a : SmoothChartHolderCore cover 0 α,
      dist z (a : LittleHolder cover 0 α N) < 1 / ((n : ℝ) + 1) := by
    have hcl := (Metric.mem_closure_iff.mp
      (UniformSpace.Completion.denseRange_coe z))
      (1 / ((n : ℝ) + 1)) (by positivity)
    rcases hcl with ⟨v, hv, hdist⟩
    rcases hv with ⟨a, rfl⟩
    exact ⟨a, hdist⟩
  choose u hu using hdense
  have hseq : Tendsto (fun n => (u n : LittleHolder cover 0 α N)) atTop (𝓝 z) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    obtain ⟨Nε, hNε⟩ := exists_nat_gt (1 / ε)
    refine ⟨Nε, ?_⟩
    intro n hn
    have hfrac : 1 / ((n : ℝ) + 1) < ε := by
      have hlt : (1 / ε) < (n : ℝ) + 1 := by
        have hn' : (Nε : ℝ) ≤ n := by exact_mod_cast hn
        have hNε' : (1 / ε) < (Nε : ℝ) := by exact_mod_cast hNε
        linarith
      rw [div_lt_iff₀ (by positivity)]
      have hmul : (1 : ℝ) < ((n : ℝ) + 1) * ε :=
        (div_lt_iff₀ hε).mp hlt
      nlinarith
    exact (dist_comm _ _).trans_lt (hu n) |>.trans hfrac
  have hCauchy : CauchySeq u :=
    (UniformSpace.Completion.isUniformInducing_coe
      (SmoothChartHolderCore cover 0 α)).cauchy_map_iff.mp
      hseq.cauchySeq
  have hFseq : Tendsto (fun n => F (u n : LittleHolder cover 0 α N)) atTop (𝓝 0) := by
    rw [← hz]
    exact (F.continuous.tendsto z).comp hseq
  have hpoint (p : M) : Tendsto (fun n => (u n).smoothMap p) atTop (𝓝 0) := by
    have hev := ((ContinuousMap.evalCLM (R := ℝ) p).continuous.tendsto
      (0 : C(M, ℝ))).comp hFseq
    have hev' : Tendsto (fun n => (F (u n : LittleHolder cover 0 α N)) p)
        atTop (𝓝 0) := by
      change Tendsto ((fun f : C(M, ℝ) => f p) ∘
        (fun n => F (u n : LittleHolder cover 0 α N))) atTop (𝓝 0)
      exact hev
    have heq (n : ℕ) : (F (u n : LittleHolder cover 0 α N)) p = (u n).smoothMap p := by
      dsimp [F]
      rw [smoothChartHolderContinuousMapExtension_coe]
      rfl
    exact hev'.congr' (Filter.Eventually.of_forall fun n => heq n)
  have hnormF : Tendsto (fun n => ‖F (u n : LittleHolder cover 0 α N)‖) atTop (𝓝 0) := by
    simpa using hFseq.norm
  have hholder (i : cover.ι) (δ : ℝ≥0) (hδ : 0 < δ) :
      ∀ᶠ n in atTop, eHolderSeminormOn α (cover.piece i)
        (iteratedFDeriv ℝ 0 ((u n).smoothMap ∘
          (extChartAt 𝓘(ℝ, E) (cover.base i)).symm)) ≤ δ := by
    have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
    obtain ⟨Nδ, hNδ⟩ := Metric.cauchySeq_iff.mp hCauchy (δ : ℝ) hδR
    let chart := (extChartAt 𝓘(ℝ, E) (cover.base i)).symm
    let L := (continuousMultilinearCurryFin0 ℝ E ℝ).symm
    let jet (f : SmoothChartHolderCore cover 0 α) :
        E → E [×0]→L[ℝ] ℝ := iteratedFDeriv ℝ 0 (f.smoothMap ∘ chart)
    have hlim : ∀ zc ∈ cover.piece i, Tendsto (fun m => jet (u m) zc)
        atTop (𝓝 0) := by
      intro zc hzc
      have heval := hpoint (chart zc)
      have hjet := (L.continuous.tendsto (0 : ℝ)).comp heval
      have hjet' : Tendsto (fun m => L ((u m).smoothMap (chart zc))) atTop (𝓝 0) := by
        change Tendsto (L ∘ (fun m => (u m).smoothMap (chart zc))) atTop (𝓝 0)
        exact hjet
      have heq : (fun m => jet (u m) zc) =
          (fun m => L ((u m).smoothMap (chart zc))) := by
        funext m
        simp [jet, chart, L, iteratedFDeriv_zero_eq_comp]
      rw [heq]
      exact hjet'
    have hseminorm (n : ℕ) (hn : Nδ ≤ n) :
        eHolderSeminormOn α (cover.piece i) (jet (u n)) ≤ δ := by
      have hHolderDiff (m : ℕ) (hm : Nδ ≤ m) :
          HolderOnWith δ α (jet (u n) - jet (u m)) (cover.piece i) := by
        have hjetSub : jet (u n) - jet (u m) = jet (u n - u m) := by
          funext zc
          change L ((u n).smoothMap (chart zc)) - L ((u m).smoothMap (chart zc)) =
            L ((u n).smoothMap (chart zc) - (u m).smoothMap (chart zc))
          exact (L).map_sub _ _
        have hbound : eHolderSeminormOn α (cover.piece i)
            (jet (u n) - jet (u m)) ≤ (δ : ENNReal) := by
          calc
            eHolderSeminormOn α (cover.piece i) (jet (u n) - jet (u m)) =
                eHolderSeminormOn α (cover.piece i) (jet (u n - u m)) := by rw [hjetSub]
            _ ≤ CalabiYau.Schauder.eContDiffHolderGaugeOn 0 α (cover.piece i)
                (((u n - u m).smoothMap ∘ chart)) := by
                  unfold jet eHolderSeminormOn
                  unfold eContDiffHolderGaugeOn
                  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
                  exact le_add_left le_rfl
            _ ≤ smoothChartHolderGauge cover 0 α (u n - u m) :=
              le_iSup (fun j => CalabiYau.Schauder.eContDiffHolderGaugeOn 0 α
                (cover.piece j) ((u n - u m).smoothMap ∘
                  (extChartAt 𝓘(ℝ, E) (cover.base j)).symm)) i
            _ = ENNReal.ofReal ‖u n - u m‖ := by
              have hfinite := N.finiteGauge (u n - u m)
              calc
                smoothChartHolderGauge cover 0 α (u n - u m) =
                    ENNReal.ofReal (smoothChartHolderGauge cover 0 α (u n - u m)).toReal :=
                      (ENNReal.ofReal_toReal (ne_of_lt hfinite)).symm
                _ = ENNReal.ofReal ‖u n - u m‖ := by
                  rw [← smoothChartHolderCore_norm_eq_gauge cover 0 α N (u n - u m)]
            _ ≤ (δ : ENNReal) := by
              rw [← ENNReal.ofReal_coe_nnreal]
              apply ENNReal.ofReal_le_ofReal
              have hdist := hNδ n hn m hm
              simpa [dist_eq_norm] using hdist.le
        exact HolderWith.restrict_iff.mp
          (holderWith_restrict_of_eHolderSeminormOn_le hbound)
      have hEventually : ∀ᶠ m in atTop, HolderOnWith δ α
          (jet (u n) - jet (u m)) (cover.piece i) := by
        filter_upwards [eventually_ge_atTop Nδ] with m hm
        exact hHolderDiff m hm
      have hlimit := holderOnWith_of_tendsto hEventually (by
        intro zc hzc
        simpa using (tendsto_const_nhds.sub (hlim zc hzc)))
      have hrestr : HolderWith δ α ((cover.piece i).domRestrict (jet (u n))) :=
        HolderWith.restrict_iff.mpr hlimit
      simpa [eHolderSeminormOn] using hrestr.eHolderNorm_le
    filter_upwards [eventually_ge_atTop Nδ] with n hn
    exact hseminorm n hn
  have hnorm_tendsto : Tendsto (fun n => ‖(u n : LittleHolder cover 0 α N)‖) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    let δ : ℝ≥0 := ⟨ε / 3, by linarith⟩
    have hδ : 0 < δ := by exact_mod_cast (show 0 < ε / 3 by linarith)
    obtain ⟨Nδ, hNδ⟩ := Metric.cauchySeq_iff.mp hCauchy (δ : ℝ) (by exact_mod_cast hδ)
    have hout : ∀ᶠ n in atTop, ‖F (u n : LittleHolder cover 0 α N)‖ < δ := by
      have hball := hnormF.eventually (Metric.ball_mem_nhds (0 : ℝ) (by exact_mod_cast hδ))
      filter_upwards [hball] with n hn
      simpa [Metric.mem_ball, Real.dist_eq] using hn
    have hhold : ∀ᶠ n in atTop, ∀ i : cover.ι,
        eHolderSeminormOn α (cover.piece i)
          (iteratedFDeriv ℝ 0 ((u n).smoothMap ∘
            (extChartAt 𝓘(ℝ, E) (cover.base i)).symm)) ≤ δ :=
      Filter.eventually_all.2 (fun i => hholder i δ hδ)
    obtain ⟨Nout, houtN⟩ := eventually_atTop.1 hout
    obtain ⟨Nhold, hholdN⟩ := eventually_atTop.1 hhold
    let Nall := max Nδ (max Nout Nhold)
    refine ⟨Nall, ?_⟩
    intro n hn
    have hnδ : Nδ ≤ n := le_trans (le_max_left _ _) hn
    have hnout : Nout ≤ n :=
      le_trans (le_trans (le_max_left Nout Nhold) (le_max_right Nδ (max Nout Nhold))) hn
    have hnhold : Nhold ≤ n :=
      le_trans (le_trans (le_max_right Nout Nhold) (le_max_right Nδ (max Nout Nhold))) hn
    have hFn := houtN n hnout
    have hHn := hholdN n hnhold
    have hlocal (i : cover.ι) :
        CalabiYau.Schauder.eContDiffHolderGaugeOn 0 α (cover.piece i)
          ((u n).smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) ≤
          ENNReal.ofReal (2 * δ) := by
      unfold CalabiYau.Schauder.eContDiffHolderGaugeOn
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      have hsup : eSupNormOn (cover.piece i)
          (iteratedFDeriv ℝ 0 ((u n).smoothMap ∘
            (extChartAt 𝓘(ℝ, E) (cover.base i)).symm)) ≤ (δ : ENNReal) := by
        apply eSupNormOn_le.mpr
        intro zc hzc
        rw [← ENNReal.ofReal_coe_nnreal]
        apply ENNReal.ofReal_le_ofReal
        calc
          ‖iteratedFDeriv ℝ 0 ((u n).smoothMap ∘
              (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) zc‖ =
              ‖(u n).smoothMap ((extChartAt 𝓘(ℝ, E) (cover.base i)).symm zc)‖ := by
                simp
          _ ≤ ‖F (u n : LittleHolder cover 0 α N)‖ := by
            have heq : (F (u n : LittleHolder cover 0 α N))
                ((extChartAt 𝓘(ℝ, E) (cover.base i)).symm zc) =
                (u n).smoothMap ((extChartAt 𝓘(ℝ, E) (cover.base i)).symm zc) := by
              dsimp [F]
              rw [smoothChartHolderContinuousMapExtension_coe]
              rfl
            rw [← heq]
            exact (F (u n : LittleHolder cover 0 α N)).norm_coe_le_norm _
          _ ≤ δ := hFn.le
      have hseminorm := hHn i
      calc
        _ = eSupNormOn (cover.piece i)
              (iteratedFDeriv ℝ 0 ((u n).smoothMap ∘
                (extChartAt 𝓘(ℝ, E) (cover.base i)).symm)) +
            eHolderSeminormOn α (cover.piece i)
              (iteratedFDeriv ℝ 0 ((u n).smoothMap ∘
                (extChartAt 𝓘(ℝ, E) (cover.base i)).symm)) := by rfl
        _ ≤ (δ : ENNReal) + δ := add_le_add hsup hseminorm
        _ = ENNReal.ofReal (2 * δ) := by
          rw [show (2 : ℝ) * (δ : ℝ) = (δ : ℝ) + (δ : ℝ) by ring,
            ENNReal.ofReal_add (by positivity) (by positivity)]
          simp
    have hgauge : smoothChartHolderGauge cover 0 α (u n) ≤ ENNReal.ofReal (2 * δ) := by
      apply iSup_le
      intro i
      exact hlocal i
    have hnorm : ‖u n‖ ≤ 2 * δ := by
      rw [smoothChartHolderCore_norm_eq_gauge cover 0 α N]
      calc
        (smoothChartHolderGauge cover 0 α (u n)).toReal ≤
            (ENNReal.ofReal (2 * δ)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hgauge
        _ = 2 * δ := by simp
    have hbound : ‖(u n : LittleHolder cover 0 α N)‖ < ε := by
      rw [UniformSpace.Completion.norm_coe]
      have hδlt : (2 : ℝ) * (δ : ℝ) < ε := by
        change 2 * (ε / 3) < ε
        linarith
      exact lt_of_le_of_lt hnorm hδlt
    simpa [dist_eq_norm] using hbound
  have hxzero : z = 0 := by
    have hnormz : ‖z‖ = 0 := by
      have hnormz' : Tendsto (fun _ : ℕ => ‖z‖) atTop (𝓝 ‖z‖) := tendsto_const_nhds
      have hnormseq : Tendsto (fun n => ‖(u n : LittleHolder cover 0 α N)‖)
          atTop (𝓝 ‖z‖) := (continuous_norm.tendsto z).comp hseq
      have hnormeq : ‖z‖ = 0 := tendsto_nhds_unique hnormseq hnorm_tendsto
      exact hnormeq
    exact norm_eq_zero.mp hnormz
  exact sub_eq_zero.mp (by simpa [z] using hxzero)

end KahlerForm
