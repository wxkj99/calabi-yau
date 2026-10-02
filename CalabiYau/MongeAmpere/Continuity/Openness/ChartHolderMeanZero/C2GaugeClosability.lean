module

public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderEvaluation
public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderC2Regularity.CompletedChartJets.Identity
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Closability of the order-two chart Hölder gauge

A Cauchy sequence in the full finite-chart `C^{2,α}` gauge that converges uniformly to zero has
vanishing gauge norm. Uniform convergence of the values identifies all limiting chart derivatives
locally; the Cauchy property then forces the top Hölder seminorm to vanish by taking pointwise limits
of the normalized differences at each distinct pair of points. This includes the oscillation
seminorm at `α = 0`.
-/

@[expose] public section

noncomputable section

open scoped Manifold ContDiff NNReal ENNReal Topology

namespace KahlerForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Filter CalabiYau.Schauder

section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

private theorem smoothChartHolderC2TopJetSeminorm_eventually_le_of_pointwise_tendsto
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover 2 α) :
    letI : NormedAddCommGroup (SmoothChartHolderCore cover 2 α) :=
      smoothChartHolderCoreNormedAddCommGroup cover 2 α N
    letI : NormedSpace ℝ (SmoothChartHolderCore cover 2 α) :=
      smoothChartHolderCoreNormedSpace cover 2 α N
    ∀ (f : ℕ → SmoothChartHolderCore cover 2 α), CauchySeq f →
      (∀ (i : cover.ι) (z : E), z ∈ cover.piece i →
        Tendsto
          (fun n => iteratedFDeriv ℝ 2
            ((f n).smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z)
          atTop (𝓝 0)) →
      ∀ (i : cover.ι) (δ : ℝ≥0), 0 < δ →
        ∀ᶠ n in atTop,
          eHolderSeminormOn α (cover.piece i)
            (iteratedFDeriv ℝ 2
              ((f n).smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm)) ≤ δ := by
  classical
  let : NormedAddCommGroup (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedAddCommGroup cover 2 α N
  let : NormedSpace ℝ (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedSpace cover 2 α N
  intro f hfCauchy hjet i δ hδ
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  obtain ⟨Nδ, hNδ⟩ := Metric.cauchySeq_iff.mp hfCauchy (δ : ℝ) hδR
  let chart := (extChartAt 𝓘(ℝ, E) (cover.base i)).symm
  let jet (g : SmoothChartHolderCore cover 2 α) : E → E [×2]→L[ℝ] ℝ :=
    iteratedFDeriv ℝ 2 (g.smoothMap ∘ chart)
  have hseminorm (n : ℕ) (hn : Nδ ≤ n) :
      eHolderSeminormOn α (cover.piece i) (jet (f n)) ≤ δ := by
    have hHolderDiff (m : ℕ) (hm : Nδ ≤ m) :
        HolderOnWith δ α (jet (f n) - jet (f m)) (cover.piece i) := by
      have hjetSub : Set.EqOn (jet (f n) - jet (f m)) (jet (f n - f m))
          (cover.piece i) := by
        intro z hz
        dsimp [jet]
        have hchart (g : SmoothChartHolderCore cover 2 α) :
            ContDiffAt ℝ 2 (g.smoothMap ∘ chart) z := by
          have hcont : ContDiffOn ℝ (∞ : ℕ∞ω)
              (g.smoothMap ∘ chart) (extChartAt 𝓘(ℝ, E) (cover.base i)).target := by
            have h := (contMDiff_iff.mp g.smoothMap.contMDiff).2 (cover.base i) 0
            simpa [chart, extChartAt, chartAt_self_eq] using h
          have hopen : IsOpen (extChartAt 𝓘(ℝ, E) (cover.base i)).target :=
            isOpen_extChartAt_target (I := 𝓘(ℝ, E)) (cover.base i)
          have htarget := cover.piece_in_target i hz
          have horder : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
            change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
            exact WithTop.coe_le_coe.mpr le_top
          exact (hcont.contDiffAt (hopen.mem_nhds htarget)).of_le horder
        change iteratedFDeriv ℝ 2 ((f n).smoothMap ∘ chart) z -
            iteratedFDeriv ℝ 2 ((f m).smoothMap ∘ chart) z =
          iteratedFDeriv ℝ 2
            ((f n).smoothMap ∘ chart - (f m).smoothMap ∘ chart) z
        rw [iteratedFDeriv_sub_apply (hchart (f n)) (hchart (f m))]
      have hbound : eHolderSeminormOn α (cover.piece i)
          (jet (f n) - jet (f m)) ≤ (δ : ENNReal) := by
        calc
          eHolderSeminormOn α (cover.piece i) (jet (f n) - jet (f m)) =
              eHolderSeminormOn α (cover.piece i) (jet (f n - f m)) :=
                eHolderSeminormOn_congr hjetSub α
          _ ≤ CalabiYau.Schauder.eContDiffHolderGaugeOn 2 α (cover.piece i)
              ((f n - f m).smoothMap ∘ chart) :=
                CalabiYau.Schauder.holderSeminorm_le_eContDiffHolderGaugeOn
                  2 α (cover.piece i) ((f n - f m).smoothMap ∘ chart)
          _ ≤ smoothChartHolderGauge cover 2 α (f n - f m) := by
                change CalabiYau.Schauder.eContDiffHolderGaugeOn 2 α (cover.piece i)
                    ((f n - f m).smoothMap ∘ chart) ≤
                  ⨆ q, CalabiYau.Schauder.eContDiffHolderGaugeOn 2 α (cover.piece q)
                    ((f n - f m).smoothMap ∘
                      (extChartAt 𝓘(ℝ, E) (cover.base q)).symm)
                exact le_iSup (fun q : cover.ι =>
                  CalabiYau.Schauder.eContDiffHolderGaugeOn 2 α (cover.piece q)
                    ((f n - f m).smoothMap ∘
                      (extChartAt 𝓘(ℝ, E) (cover.base q)).symm)) i
          _ = ENNReal.ofReal ‖f n - f m‖ := by
                have hfinite := N.finiteGauge (f n - f m)
                calc
                  smoothChartHolderGauge cover 2 α (f n - f m) =
                      ENNReal.ofReal
                        (smoothChartHolderGauge cover 2 α (f n - f m)).toReal :=
                    (ENNReal.ofReal_toReal (ne_of_lt hfinite)).symm
                  _ = ENNReal.ofReal ‖f n - f m‖ := by
                    rw [← smoothChartHolderCore_norm_eq_gauge cover 2 α N (f n - f m)]
          _ ≤ (δ : ENNReal) := by
                rw [← ENNReal.ofReal_coe_nnreal]
                apply ENNReal.ofReal_le_ofReal
                have hdist := hNδ n hn m hm
                simpa [dist_eq_norm] using hdist.le
      exact HolderWith.restrict_iff.mp
        (holderWith_restrict_of_eHolderSeminormOn_le hbound)
    have hEventually : ∀ᶠ m in atTop,
        HolderOnWith δ α (jet (f n) - jet (f m)) (cover.piece i) := by
      filter_upwards [eventually_ge_atTop Nδ] with m hm
      exact hHolderDiff m hm
    have hlimit : HolderOnWith δ α (jet (f n)) (cover.piece i) := by
      have hlimit' := holderOnWith_of_tendsto hEventually (by
        intro z hz
        have hjet' : Tendsto (fun m => jet (f m) z) atTop (𝓝 0) := by
          simpa [jet, chart] using hjet i z hz
        exact tendsto_const_nhds.sub hjet')
      simpa using hlimit'
    have hrestr : HolderWith δ α ((cover.piece i).domRestrict (jet (f n))) :=
      HolderWith.restrict_iff.mpr hlimit
    simpa [eHolderSeminormOn] using hrestr.eHolderNorm_le
  filter_upwards [eventually_ge_atTop Nδ] with n hn
  exact hseminorm n hn

private theorem smoothChartHolderC2SpatialJet_eventually_le_of_pointwise_tendsto
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover 2 α) :
    letI : NormedAddCommGroup (SmoothChartHolderCore cover 2 α) :=
      smoothChartHolderCoreNormedAddCommGroup cover 2 α N
    letI : NormedSpace ℝ (SmoothChartHolderCore cover 2 α) :=
      smoothChartHolderCoreNormedSpace cover 2 α N
    ∀ (f : ℕ → SmoothChartHolderCore cover 2 α), CauchySeq f →
      (∀ (j : ℕ), j ≤ 2 → ∀ (i : cover.ι) (z : E), z ∈ cover.piece i →
        Tendsto
          (fun n => iteratedFDeriv ℝ j
            ((f n).smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z)
          atTop (𝓝 0)) →
      ∀ (i : cover.ι) (j : ℕ), j ≤ 2 → ∀ (δ : ℝ≥0), 0 < δ →
        ∀ᶠ n in atTop, ∀ z ∈ cover.piece i,
          ‖iteratedFDeriv ℝ j
            ((f n).smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z‖ ≤ δ := by
  classical
  let : NormedAddCommGroup (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedAddCommGroup cover 2 α N
  let : NormedSpace ℝ (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedSpace cover 2 α N
  intro f hfCauchy hjet i j hj δ hδ
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  obtain ⟨Nδ, hNδ⟩ := Metric.cauchySeq_iff.mp hfCauchy (δ : ℝ) hδR
  let chart := (extChartAt 𝓘(ℝ, E) (cover.base i)).symm
  let jet (g : SmoothChartHolderCore cover 2 α) (z : E) :=
    iteratedFDeriv ℝ j (g.smoothMap ∘ chart) z
  have hjetSub (g₁ g₂ : SmoothChartHolderCore cover 2 α) (z : E)
      (hz : z ∈ cover.piece i) : jet g₁ z - jet g₂ z = jet (g₁ - g₂) z := by
    dsimp [jet]
    have hchart (g : SmoothChartHolderCore cover 2 α) :
        ContDiffAt ℝ j (g.smoothMap ∘ chart) z := by
      have hcont : ContDiffOn ℝ (∞ : ℕ∞ω)
          (g.smoothMap ∘ chart) (extChartAt 𝓘(ℝ, E) (cover.base i)).target := by
        have h := (contMDiff_iff.mp g.smoothMap.contMDiff).2 (cover.base i) 0
        simpa [chart, extChartAt, chartAt_self_eq] using h
      have hopen : IsOpen (extChartAt 𝓘(ℝ, E) (cover.base i)).target :=
        isOpen_extChartAt_target (I := 𝓘(ℝ, E)) (cover.base i)
      have horder : (↑j : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
        change ((j : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
        exact WithTop.coe_le_coe.mpr le_top
      exact (hcont.contDiffAt (hopen.mem_nhds (cover.piece_in_target i hz))).of_le horder
    change iteratedFDeriv ℝ j (g₁.smoothMap ∘ chart) z -
        iteratedFDeriv ℝ j (g₂.smoothMap ∘ chart) z =
      iteratedFDeriv ℝ j (g₁.smoothMap ∘ chart - g₂.smoothMap ∘ chart) z
    rw [iteratedFDeriv_sub_apply (hchart g₁) (hchart g₂)]
  have hdiff (n m : ℕ) (hn : Nδ ≤ n) (hm : Nδ ≤ m)
      (z : E) (hz : z ∈ cover.piece i) : ‖jet (f n) z - jet (f m) z‖ ≤ δ := by
    have hjetEq := hjetSub (f n) (f m) z hz
    have hspatial := CalabiYau.Schauder.spatialJet_le_eContDiffHolderGaugeOn
      2 α (cover.piece i) ((f n - f m).smoothMap ∘ chart) hj z hz
    have hpiece : CalabiYau.Schauder.eContDiffHolderGaugeOn 2 α (cover.piece i)
        ((f n - f m).smoothMap ∘ chart) ≤ smoothChartHolderGauge cover 2 α (f n - f m) := by
      change CalabiYau.Schauder.eContDiffHolderGaugeOn 2 α (cover.piece i)
          ((f n - f m).smoothMap ∘ chart) ≤
        ⨆ q, CalabiYau.Schauder.eContDiffHolderGaugeOn 2 α (cover.piece q)
          ((f n - f m).smoothMap ∘
            (extChartAt 𝓘(ℝ, E) (cover.base q)).symm)
      exact le_iSup (fun q : cover.ι => CalabiYau.Schauder.eContDiffHolderGaugeOn 2 α
        (cover.piece q) ((f n - f m).smoothMap ∘
          (extChartAt 𝓘(ℝ, E) (cover.base q)).symm)) i
    have hfinite := N.finiteGauge (f n - f m)
    have hgauge : smoothChartHolderGauge cover 2 α (f n - f m) =
        ENNReal.ofReal ‖f n - f m‖ := by
      calc
        smoothChartHolderGauge cover 2 α (f n - f m) =
            ENNReal.ofReal (smoothChartHolderGauge cover 2 α (f n - f m)).toReal :=
          (ENNReal.ofReal_toReal (ne_of_lt hfinite)).symm
        _ = ENNReal.ofReal ‖f n - f m‖ := by
          rw [← smoothChartHolderCore_norm_eq_gauge cover 2 α N (f n - f m)]
    have hdist := hNδ n hn m hm
    have hnorm : ‖f n - f m‖ ≤ δ := by simpa [dist_eq_norm] using hdist.le
    have hreal : ‖jet (f n) z - jet (f m) z‖ ≤ ‖f n - f m‖ := by
      apply (ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)).mp
      calc
        ENNReal.ofReal ‖jet (f n) z - jet (f m) z‖ =
            ENNReal.ofReal ‖jet (f n - f m) z‖ := by rw [hjetEq]
        _ ≤ CalabiYau.Schauder.eContDiffHolderGaugeOn 2 α (cover.piece i)
            ((f n - f m).smoothMap ∘ chart) := hspatial
        _ ≤ smoothChartHolderGauge cover 2 α (f n - f m) := hpiece
        _ = ENNReal.ofReal ‖f n - f m‖ := hgauge
    exact hreal.trans hnorm
  have hpoint (n : ℕ) (hn : Nδ ≤ n) (z : E) (hz : z ∈ cover.piece i) :
      ‖jet (f n) z‖ ≤ δ := by
    have hlim : Tendsto (fun m => jet (f n) z - jet (f m) z) atTop
        (𝓝 (jet (f n) z)) := by
      have hjet' : Tendsto (fun m => jet (f m) z) atTop (𝓝 0) := by
        simpa [jet, chart] using hjet j hj i z hz
      have hconst : Tendsto (fun _ : ℕ => jet (f n) z) atTop (𝓝 (jet (f n) z)) :=
        tendsto_const_nhds
      simpa only [sub_zero] using hconst.sub hjet'
    have hmem : jet (f n) z ∈ Metric.closedBall (0 : E [×j]→L[ℝ] ℝ) δ :=
      Metric.isClosed_closedBall.mem_of_tendsto hlim (by
        filter_upwards [eventually_ge_atTop Nδ] with m hm
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hdiff n m hn hm z hz)
    simpa [Metric.mem_closedBall] using hmem
  filter_upwards [eventually_ge_atTop Nδ] with n hn
  intro z hz
  exact hpoint n hn z hz

private theorem smoothChartHolderCoreNorm_tendsto_zero_of_pointwiseJets_tendsto_zero
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover 2 α) :
    letI : NormedAddCommGroup (SmoothChartHolderCore cover 2 α) :=
      smoothChartHolderCoreNormedAddCommGroup cover 2 α N
    letI : NormedSpace ℝ (SmoothChartHolderCore cover 2 α) :=
      smoothChartHolderCoreNormedSpace cover 2 α N
    ∀ (f : ℕ → SmoothChartHolderCore cover 2 α), CauchySeq f →
      (∀ (j : ℕ), j ≤ 2 → ∀ (i : cover.ι) (z : E), z ∈ cover.piece i →
        Tendsto
          (fun n => iteratedFDeriv ℝ j
            ((f n).smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z)
          atTop (𝓝 0)) →
      Tendsto (fun n => ‖f n‖) atTop (𝓝 0) := by
  classical
  let : NormedAddCommGroup (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedAddCommGroup cover 2 α N
  let : NormedSpace ℝ (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedSpace cover 2 α N
  intro f hfCauchy hjet
  apply Metric.tendsto_atTop.2
  intro ε hε
  let δ : ℝ≥0 := ⟨ε / 8, by positivity⟩
  have hδ : 0 < δ := by
    dsimp [δ]
    exact_mod_cast (show (0 : ℝ) < ε / 8 by positivity)
  have hlocal (i : cover.ι) : ∀ᶠ n in atTop,
      CalabiYau.Schauder.eContDiffHolderGaugeOn 2 α (cover.piece i)
        ((f n).smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) ≤
          (4 : ℝ≥0∞) * (δ : ℝ≥0∞) := by
    have h0 := smoothChartHolderC2SpatialJet_eventually_le_of_pointwise_tendsto
      cover α N f hfCauchy hjet i 0 (by omega) δ hδ
    have h1 := smoothChartHolderC2SpatialJet_eventually_le_of_pointwise_tendsto
      cover α N f hfCauchy hjet i 1 (by omega) δ hδ
    have h2 := smoothChartHolderC2SpatialJet_eventually_le_of_pointwise_tendsto
      cover α N f hfCauchy hjet i 2 (by omega) δ hδ
    have htop := smoothChartHolderC2TopJetSeminorm_eventually_le_of_pointwise_tendsto
      cover α N f hfCauchy (fun i z hz => hjet 2 (by omega) i z hz) i δ hδ
    filter_upwards [h0, h1, h2, htop] with n h0 h1 h2 htop
    have hspatial : ∀ j ≤ 2, ∀ z ∈ cover.piece i,
        ‖iteratedFDeriv ℝ j
          ((f n).smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z‖ ≤ δ := by
      intro j hj z hz
      interval_cases j
      · simpa using h0 z hz
      · simpa using h1 z hz
      · simpa using h2 z hz
    have hholder : HolderWith δ α ((cover.piece i).domRestrict
        (iteratedFDeriv ℝ 2
          ((f n).smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm))) :=
      holderWith_restrict_of_eHolderSeminormOn_le htop
    have hbound := CalabiYau.Schauder.eContDiffHolderGaugeOn_le
      (fun _ => δ) δ hspatial hholder
    have hsum :
        (∑ j ∈ Finset.range (2 + 1), (δ : ℝ≥0∞)) + (δ : ℝ≥0∞) =
          (4 : ℝ≥0∞) * (δ : ℝ≥0∞) := by
      calc
        _ = (3 : ℝ≥0∞) * (δ : ℝ≥0∞) + δ := by simp
        _ = (4 : ℝ≥0∞) * (δ : ℝ≥0∞) := by ring
    exact hbound.trans_eq hsum
  have hglobal : ∀ᶠ n in atTop,
      smoothChartHolderGauge cover 2 α (f n) ≤ (4 : ℝ≥0∞) * (δ : ℝ≥0∞) := by
    have hall : ∀ᶠ n in atTop, ∀ i : cover.ι,
        CalabiYau.Schauder.eContDiffHolderGaugeOn 2 α (cover.piece i)
          ((f n).smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) ≤
            (4 : ℝ≥0∞) * (δ : ℝ≥0∞) :=
      Filter.eventually_all.2 hlocal
    filter_upwards [hall] with n hn
    unfold smoothChartHolderGauge finiteChartHolderGauge
    exact iSup_le hn
  obtain ⟨Nε, hNε⟩ := eventually_atTop.1 hglobal
  refine ⟨Nε, ?_⟩
  intro n hn
  have hnorm : ‖f n‖ ≤ 4 * (δ : ℝ) := by
    rw [smoothChartHolderCore_norm_eq_gauge cover 2 α N (f n)]
    calc
      (smoothChartHolderGauge cover 2 α (f n)).toReal ≤
          ((4 : ℝ≥0∞) * (δ : ℝ≥0∞)).toReal :=
        ENNReal.toReal_mono
          (ENNReal.mul_ne_top (by simp) ENNReal.coe_ne_top) (hNε n hn)
      _ = 4 * (δ : ℝ) := by simp
  have hsmall : (4 : ℝ) * (δ : ℝ) < ε := by
    change 4 * (ε / 8) < ε
    nlinarith
  have hnormlt : ‖f n‖ < ε := lt_of_le_of_lt hnorm hsmall
  simpa [Real.dist_eq] using hnormlt

end

variable [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] in
omit [FiniteDimensional ℝ E] in
private theorem smoothChartHolderCoreCauchySeq_pointwiseJets_tendsto_zero_on_interior_of_uniformEvaluation_tendsto_zero
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover 2 α) :
    letI : NormedAddCommGroup (SmoothChartHolderCore cover 2 α) :=
      smoothChartHolderCoreNormedAddCommGroup cover 2 α N
    letI : NormedSpace ℝ (SmoothChartHolderCore cover 2 α) :=
      smoothChartHolderCoreNormedSpace cover 2 α N
    ∀ (f : ℕ → SmoothChartHolderCore cover 2 α),
      CauchySeq (fun n => (f n : LittleHolder cover 2 α N)) →
      Filter.Tendsto
        (fun n => smoothChartHolderContinuousMapLinearMap cover 2 α (f n))
        atTop (𝓝 0) →
      ∀ (j : ℕ), j ≤ 2 → ∀ (i : cover.ι) (z : E),
        z ∈ interior (cover.piece i) →
        Filter.Tendsto
          (fun n => iteratedFDeriv ℝ j
            ((f n).smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z)
          atTop (𝓝 0) := by
  classical
  let : NormedAddCommGroup (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedAddCommGroup cover 2 α N
  let : NormedSpace ℝ (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedSpace cover 2 α N
  intro f hfCauchy hEval j hj i z hz
  obtain ⟨u, hu⟩ := cauchySeq_tendsto_of_complete hfCauchy
  let F := smoothChartHolderContinuousMapExtension cover 2 α N
  have hFseq : Tendsto (fun n => F (f n : LittleHolder cover 2 α N)) atTop (𝓝 (F u)) :=
    (F.continuous.tendsto u).comp hu
  have hFcore : Tendsto
      (fun n => smoothChartHolderContinuousMapLinearMap cover 2 α (f n))
      atTop (𝓝 (F u)) := by
    exact hFseq.congr' (Filter.Eventually.of_forall fun n => by
      dsimp [F]
      rw [smoothChartHolderContinuousMapExtension_coe])
  have hFzero : F u = 0 := tendsto_nhds_unique hFcore hEval
  let J := smoothChartHolderJetCanonicalExtension cover 2 α N j hj
  have hJseq : Tendsto
      (fun n => J (f n : LittleHolder cover 2 α N)) atTop (𝓝 (J u)) :=
    (J.continuous.tendsto u).comp hu
  let xz : cover.piece i := ⟨z, interior_subset hz⟩
  have hEvalJet : Continuous
      (fun v : SmoothChartHolderJetTarget cover j => v i xz) := by
    exact (ContinuousMap.evalCLM (R := ℝ) xz).continuous.comp (continuous_apply i)
  have hJpoint : Tendsto
      (fun n => J (f n : LittleHolder cover 2 α N) i xz) atTop (𝓝 (J u i xz)) :=
    (hEvalJet.tendsto (J u)).comp hJseq
  have hIdentity := smoothChartHolderCompletedJetIdentity cover α N u j hj i z hz
  have hJzero : J u i xz = 0 := by
    rw [← hIdentity]
    simp [F, hFzero]
  have hJpointZero : Tendsto
      (fun n => J (f n : LittleHolder cover 2 α N) i xz) atTop (𝓝 0) := by
    simpa [hJzero] using hJpoint
  have hcoreJet (n : ℕ) :
      J (f n : LittleHolder cover 2 α N) i xz =
        iteratedFDeriv ℝ j
          ((f n).smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z := by
    simp [J, xz, smoothChartHolderJetData]
  exact hJpointZero.congr' (Filter.Eventually.of_forall hcoreJet)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] in
private theorem smoothChartHolderTransition_contDiffAt
    (cover : CompactChartCover E M) (i j : cover.ι) (z w : E)
    (hz : z ∈ cover.piece i) (hw : w ∈ interior (cover.piece j))
    (hcoord : (extChartAt 𝓘(ℝ, E) (cover.base i)).symm z =
      (extChartAt 𝓘(ℝ, E) (cover.base j)).symm w) :
    ContDiffAt ℝ (∞ : ℕ∞ω)
      ((extChartAt 𝓘(ℝ, E) (cover.base j)) ∘
        (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z := by
  let ei := extChartAt 𝓘(ℝ, E) (cover.base i)
  let ej := extChartAt 𝓘(ℝ, E) (cover.base j)
  have hwTarget : w ∈ ej.target := cover.piece_in_target j (interior_subset hw)
  have hxSource : (ei.symm z : M) ∈ (chartAt E (cover.base j)).source := by
    rw [hcoord]
    simpa [ej, extChartAt_source] using ej.map_target hwTarget
  have hsymm : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) (∞ : ℕ∞ω) ei.symm z := by
    have hopen : IsOpen ei.target := isOpen_extChartAt_target (cover.base i)
    have hzTarget : z ∈ ei.target := cover.piece_in_target i hz
    have hOn : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) (∞ : ℕ∞ω) ei.symm ei.target :=
      contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, E)) (cover.base i)
    exact hOn.contMDiffAt (hopen.mem_nhds hzTarget)
  have hchart : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) (∞ : ℕ∞ω) ej (ei.symm z) :=
    contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) hxSource
  exact (hchart.comp z hsymm).contDiffAt

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] in
private theorem smoothChartHolderChartTransitionJet_tendsto_zero
    (G : ℕ → E → ℝ) (τ : E → E) (z : E) (r : ℕ) (hr : r ≤ 2)
    (hG : ∀ n, ContDiffAt ℝ (∞ : ℕ∞ω) (G n) (τ z))
    (hτ : ContDiffAt ℝ (∞ : ℕ∞ω) τ z)
    (hjet : ∀ (k : ℕ), k ≤ 2 → Filter.Tendsto
      (fun n => iteratedFDeriv ℝ k (G n) (τ z)) atTop (𝓝 0)) :
    Filter.Tendsto (fun n => iteratedFDeriv ℝ r (G n ∘ τ) z) atTop (𝓝 0) := by
  let p : ℕ → FormalMultilinearSeries ℝ E ℝ := fun n => ftaylorSeries ℝ (G n) (τ z)
  let q : FormalMultilinearSeries ℝ E E := ftaylorSeries ℝ τ z
  let control : ℕ → ℝ := fun n => ‖p n 0‖ + ‖p n 1‖ + ‖p n 2‖
  have h0 : Filter.Tendsto (fun n => ‖p n 0‖) atTop (𝓝 0) := by
    change Filter.Tendsto (fun n => ‖iteratedFDeriv ℝ 0 (G n) (τ z)‖) atTop (𝓝 0)
    simpa using (hjet 0 (by omega)).norm
  have h1 : Filter.Tendsto (fun n => ‖p n 1‖) atTop (𝓝 0) := by
    change Filter.Tendsto (fun n => ‖iteratedFDeriv ℝ 1 (G n) (τ z)‖) atTop (𝓝 0)
    simpa using (hjet 1 (by omega)).norm
  have h2 : Filter.Tendsto (fun n => ‖p n 2‖) atTop (𝓝 0) := by
    change Filter.Tendsto (fun n => ‖iteratedFDeriv ℝ 2 (G n) (τ z)‖) atTop (𝓝 0)
    simpa using (hjet 2 (by omega)).norm
  have hcontrol : Filter.Tendsto control atTop (𝓝 0) := by
    simpa [control, add_assoc] using (h0.add h1).add h2
  have hpBound : ∀ k ≤ 2, atTop.IsBoundedUnder (· ≤ ·) (fun n => ‖p n k‖) := by
    intro k hk
    have hk' := (hjet k hk).norm
    change atTop.IsBoundedUnder (· ≤ ·)
      (fun n => ‖iteratedFDeriv ℝ k (G n) (τ z)‖)
    exact hk'.isBoundedUnder_le
  have hpdiff : ∀ k ≤ 2,
      (fun n => p n k - (0 : FormalMultilinearSeries ℝ E ℝ) k) =O[atTop] control := by
    intro k hk
    apply Asymptotics.IsBigO.of_norm_le
    intro n
    have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk_cases with rfl | rfl | rfl
    · have hbound : ‖p n 0‖ ≤ ‖p n 0‖ + ‖p n 1‖ + ‖p n 2‖ := by
        calc
          ‖p n 0‖ ≤ ‖p n 0‖ + (‖p n 1‖ + ‖p n 2‖) :=
            le_add_of_nonneg_right (add_nonneg (norm_nonneg _) (norm_nonneg _))
          _ = ‖p n 0‖ + ‖p n 1‖ + ‖p n 2‖ := by ring
      simpa [control] using hbound
    · have hbound : ‖p n 1‖ ≤ ‖p n 0‖ + ‖p n 1‖ + ‖p n 2‖ := by
        calc
          ‖p n 1‖ ≤ ‖p n 0‖ + ‖p n 1‖ := le_add_of_nonneg_left (norm_nonneg _)
          _ ≤ (‖p n 0‖ + ‖p n 1‖) + ‖p n 2‖ :=
            le_add_of_nonneg_right (norm_nonneg _)
      simpa [control] using hbound
    · have hbound : ‖p n 2‖ ≤ ‖p n 0‖ + ‖p n 1‖ + ‖p n 2‖ :=
        le_add_of_nonneg_left (add_nonneg (norm_nonneg _) (norm_nonneg _))
      simpa [control] using hbound
  have hqBound : ∀ k ≤ 2, atTop.IsBoundedUnder (· ≤ ·)
      (fun _n : ℕ => ‖q k‖) := by
    intro k hk
    exact isBoundedUnder_const
  have hcontrol_nonneg (n : ℕ) : 0 ≤ control n := by
    dsimp [control]
    positivity
  have hqDiff : ∀ k ≤ 2, (fun n => q k - q k) =O[atTop] control := by
    intro k hk
    apply Asymptotics.IsBigO.of_norm_le
    intro n
    simpa using hcontrol_nonneg n
  have hbig : (fun n => (p n).taylorComp q r -
      (0 : FormalMultilinearSeries ℝ E ℝ).taylorComp q r) =O[atTop] control := by
    exact FormalMultilinearSeries.taylorComp_sub_taylorComp_isBigO
      (fun k hk => hpBound k (hk.trans hr))
      (fun k hk => hpdiff k (hk.trans hr))
      (fun k hk => hqBound k (hk.trans hr))
      (fun k hk => hqBound k (hk.trans hr))
      (fun k hk => hqDiff k (hk.trans hr))
  have hzero : (0 : FormalMultilinearSeries ℝ E ℝ).taylorComp q r = 0 := by
    unfold FormalMultilinearSeries.taylorComp
    apply Finset.sum_eq_zero
    intro c hc
    ext v
    rfl
  have hcomp : Filter.Tendsto (fun n => (p n).taylorComp q r) atTop (𝓝 0) := by
    have h := hbig.trans_tendsto hcontrol
    simpa [hzero] using h
  have hEq (n : ℕ) :
      iteratedFDeriv ℝ r (G n ∘ τ) z = (p n).taylorComp q r := by
    simpa [p, q] using iteratedFDeriv_comp (hG n) hτ (i := r) (by
      exact WithTop.coe_le_coe.mpr le_top)
  exact hcomp.congr' (Filter.Eventually.of_forall fun n => (hEq n).symm)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] in
private theorem smoothChartHolderCoreCauchySeq_pointwiseJets_tendsto_zero_across_chart_transition
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (f : ℕ → SmoothChartHolderCore cover 2 α)
    (i j : cover.ι) (z w : E)
    (hz : z ∈ cover.piece i) (hw : w ∈ interior (cover.piece j))
    (hcoord : (extChartAt 𝓘(ℝ, E) (cover.base i)).symm z =
      (extChartAt 𝓘(ℝ, E) (cover.base j)).symm w)
    (hjet : ∀ (r : ℕ), r ≤ 2 → Filter.Tendsto
      (fun n => iteratedFDeriv ℝ r
        ((f n).smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base j)).symm) w)
      atTop (𝓝 0)) :
    ∀ (r : ℕ), r ≤ 2 → Filter.Tendsto
      (fun n => iteratedFDeriv ℝ r
        ((f n).smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z)
      atTop (𝓝 0) := by
  let ei := extChartAt 𝓘(ℝ, E) (cover.base i)
  let ej := extChartAt 𝓘(ℝ, E) (cover.base j)
  let τ : E → E := ej ∘ ei.symm
  let G : ℕ → E → ℝ := fun n =>
    (f n).smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base j)).symm
  have hwTarget : w ∈ ej.target := cover.piece_in_target j (interior_subset hw)
  have hxSource : ei.symm z ∈ (chartAt E (cover.base j)).source := by
    rw [hcoord]
    simpa [ej, extChartAt_source] using ej.map_target hwTarget
  have hsymm : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) (∞ : ℕ∞ω) ei.symm z := by
    have hopen : IsOpen ei.target := isOpen_extChartAt_target (cover.base i)
    have hzTarget : z ∈ ei.target := cover.piece_in_target i hz
    have hOn : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) (∞ : ℕ∞ω) ei.symm ei.target :=
      contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, E)) (cover.base i)
    exact hOn.contMDiffAt (hopen.mem_nhds hzTarget)
  have hτ : ContDiffAt ℝ (∞ : ℕ∞ω) τ z := by
    have hchart : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) (∞ : ℕ∞ω) ej (ei.symm z) :=
      contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) hxSource
    have hcomp := hchart.comp z hsymm
    simpa [τ] using hcomp.contDiffAt
  have hτz : τ z = w := by
    calc
      τ z = ej (ei.symm z) := rfl
      _ = ej (ej.symm w) := by rw [hcoord]
      _ = w := ej.right_inv hwTarget
  have hG : ∀ n, ContDiffAt ℝ (∞ : ℕ∞ω) (G n) (τ z) := by
    intro n
    have hcont : ContDiffOn ℝ (∞ : ℕ∞ω)
        ((f n).smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base j)).symm)
        (extChartAt 𝓘(ℝ, E) (cover.base j)).target := by
      have h := (contMDiff_iff.mp (f n).smoothMap.contMDiff).2 (cover.base j) 0
      simpa [extChartAt, chartAt_self_eq] using h
    have hopen : IsOpen ej.target := isOpen_extChartAt_target (cover.base j)
    rw [hτz]
    exact hcont.contDiffAt (hopen.mem_nhds (cover.piece_in_target j (interior_subset hw)))
  have hjet' : ∀ (r : ℕ), r ≤ 2 → Filter.Tendsto
      (fun n => iteratedFDeriv ℝ r (G n) (τ z)) atTop (𝓝 0) := by
    intro r hr
    have heq : (fun n => iteratedFDeriv ℝ r (G n) (τ z)) =
        (fun n => iteratedFDeriv ℝ r
          ((f n).smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base j)).symm) w) := by
      funext n
      dsimp [G]
      rw [hτz]
    rw [heq]
    exact hjet r hr
  have hxSource' : ei.symm z ∈ ej.source := by
    simpa [ej, extChartAt_source] using hxSource
  have hnear : ∀ᶠ y in 𝓝 z, ei.symm y ∈ ej.source := by
    have hopen : IsOpen ej.source := isOpen_extChartAt_source (cover.base j)
    exact (hsymm.continuousAt.tendsto).eventually (hopen.mem_nhds hxSource')
  have hlocalEq (n : ℕ) :
      ((f n).smoothMap ∘ ei.symm) =ᶠ[𝓝 z] (G n ∘ τ) := by
    filter_upwards [hnear] with y hy
    change (f n).smoothMap (ei.symm y) = (f n).smoothMap (ej.symm (ej (ei.symm y)))
    rw [ej.left_inv hy]
  intro r hr
  have hcomp := smoothChartHolderChartTransitionJet_tendsto_zero G τ z r hr hG hτ hjet'
  exact hcomp.congr' (Filter.Eventually.of_forall fun n =>
    ((hlocalEq n).iteratedFDeriv ℝ r).self_of_nhds.symm)

section

variable [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]

omit [FiniteDimensional ℝ E] in
private theorem smoothChartHolderCoreCauchySeq_pointwiseJets_tendsto_zero_of_uniformEvaluation_tendsto_zero
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover 2 α) :
    letI : NormedAddCommGroup (SmoothChartHolderCore cover 2 α) :=
      smoothChartHolderCoreNormedAddCommGroup cover 2 α N
    letI : NormedSpace ℝ (SmoothChartHolderCore cover 2 α) :=
      smoothChartHolderCoreNormedSpace cover 2 α N
    ∀ (f : ℕ → SmoothChartHolderCore cover 2 α),
      CauchySeq (fun n => (f n : LittleHolder cover 2 α N)) →
      Filter.Tendsto
        (fun n => smoothChartHolderContinuousMapLinearMap cover 2 α (f n))
        atTop (𝓝 0) →
      ∀ (j : ℕ), j ≤ 2 → ∀ (i : cover.ι) (z : E), z ∈ cover.piece i →
        Filter.Tendsto
          (fun n => iteratedFDeriv ℝ j
            ((f n).smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z)
          atTop (𝓝 0) := by
  classical
  let : NormedAddCommGroup (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedAddCommGroup cover 2 α N
  let : NormedSpace ℝ (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedSpace cover 2 α N
  intro f hfCauchy hEval j hj i z hz
  by_cases hInterior : z ∈ interior (cover.piece i)
  · exact smoothChartHolderCoreCauchySeq_pointwiseJets_tendsto_zero_on_interior_of_uniformEvaluation_tendsto_zero
      cover α N f hfCauchy hEval j hj i z hInterior
  ·
    let x : M := (extChartAt 𝓘(ℝ, E) (cover.base i)).symm z
    obtain ⟨q, w, hw, hcoord⟩ := cover.interior_covers x
    have hjetj : ∀ (r : ℕ), r ≤ 2 → Filter.Tendsto
        (fun n => iteratedFDeriv ℝ r
          ((f n).smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base q)).symm) w)
        atTop (𝓝 0) := by
      intro r hr
      exact smoothChartHolderCoreCauchySeq_pointwiseJets_tendsto_zero_on_interior_of_uniformEvaluation_tendsto_zero
        cover α N f hfCauchy hEval r hr q w hw
    have htransfer := smoothChartHolderCoreCauchySeq_pointwiseJets_tendsto_zero_across_chart_transition
      cover α f i q z w hz hw hcoord.symm hjetj
    exact htransfer j hj

omit [FiniteDimensional ℝ E] in
/-- If a sequence is Cauchy in the order-two finite-chart gauge and its smooth evaluations converge
uniformly to zero on the compact manifold, then its full `C^{2,α}` gauge norm tends to zero. The
proof uses local uniform derivative limits and closability of the top-order Hölder seminorm; it does
not estimate that seminorm by the sup norm. -/
theorem smoothChartHolderCoreCauchySeq_tendsto_zero_of_uniformEvaluation_tendsto_zero
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover 2 α) :
    letI : NormedAddCommGroup (SmoothChartHolderCore cover 2 α) :=
      smoothChartHolderCoreNormedAddCommGroup cover 2 α N
    letI : NormedSpace ℝ (SmoothChartHolderCore cover 2 α) :=
      smoothChartHolderCoreNormedSpace cover 2 α N
    ∀ (f : ℕ → SmoothChartHolderCore cover 2 α),
      CauchySeq (fun n => (f n : LittleHolder cover 2 α N)) →
      Filter.Tendsto
        (fun n => smoothChartHolderContinuousMapLinearMap cover 2 α (f n))
        Filter.atTop (𝓝 0) →
      Filter.Tendsto (fun n => ‖f n‖) Filter.atTop (𝓝 0) := by
  classical
  let : NormedAddCommGroup (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedAddCommGroup cover 2 α N
  let : NormedSpace ℝ (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedSpace cover 2 α N
  intro f hfCauchy hEval
  have hfCoreCauchy : CauchySeq f :=
    (UniformSpace.Completion.isUniformInducing_coe
      (SmoothChartHolderCore cover 2 α)).cauchy_map_iff.mp hfCauchy
  have hjets := smoothChartHolderCoreCauchySeq_pointwiseJets_tendsto_zero_of_uniformEvaluation_tendsto_zero
    cover α N f hfCauchy hEval
  exact smoothChartHolderCoreNorm_tendsto_zero_of_pointwiseJets_tendsto_zero
    cover α N f hfCoreCauchy hjets

end

end KahlerForm
