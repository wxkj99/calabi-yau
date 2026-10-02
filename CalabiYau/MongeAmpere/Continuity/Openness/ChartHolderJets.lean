module

public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderCarrier
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Algebra.LinearMapCompletion
public import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Chart-jet bound for the finite-chart Hölder gauge

The finite-chart gauge controls each jet uniformly on every chosen compact chart piece. The target
below is the finite product of bounded continuous chart-jet functions, the concrete space needed
to extend these data to the little-Hölder completion.
-/

@[expose] public section

noncomputable section

open scoped Manifold ContDiff NNReal ENNReal Topology

namespace KahlerForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Pointwise jet fields on the selected compact chart pieces. -/
noncomputable instance finiteCompactChartCover_pieceCompactSpace
    (cover : CompactChartCover E M) (i : cover.ι) :
    CompactSpace (cover.piece i) :=
  isCompact_iff_compactSpace.mp (cover.isCompact_piece i)

/-- The finite product of continuous chart-jet functions, with the sup norm. -/
abbrev SmoothChartHolderJetTarget (cover : CompactChartCover E M) (j : ℕ) :=
  ∀ i, C(cover.piece i, E [×j]→L[ℝ] ℝ)

/-- The j-jets of smooth core functions define a linear map into the finite product of continuous
chart-jet functions. Its sup norm is bounded by the finite-chart gauge; for `j ≤ k` this is one of
the jet sup terms in that gauge. The compactness fields make each target ContinuousMap normed and
complete. -/
theorem exists_smoothChartHolderJetLinearMap
    (cover : CompactChartCover E M) (k : ℕ) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover k α) (j : ℕ) (hj : j ≤ k) :
    ∃ J : SmoothChartHolderCore cover k α →ₗ[ℝ]
      SmoothChartHolderJetTarget cover j,
      (∀ f, ‖J f‖ ≤ (smoothChartHolderGauge cover k α f).toReal) ∧
      ∀ (f : SmoothChartHolderCore cover k α) (i) (z : cover.piece i),
        J f i z = smoothChartHolderJetData cover k α j f i z := by
  classical
  let chartContDiffOn (f : SmoothChartHolderCore cover k α) (i : cover.ι) :
      ContDiffOn ℝ (∞ : ℕ∞ω)
        (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm)
        (extChartAt 𝓘(ℝ, E) (cover.base i)).target := by
    have h := (contMDiff_iff.mp f.smoothMap.contMDiff).2 (cover.base i) 0
    simpa [extChartAt, chartAt_self_eq] using h
  let chartJetContinuous (f : SmoothChartHolderCore cover k α) (i : cover.ι) :
      ContinuousOn
        (iteratedFDeriv ℝ j
          (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm))
        (cover.piece i) := by
    let e := extChartAt 𝓘(ℝ, E) (cover.base i)
    have hopen : IsOpen e.target := isOpen_extChartAt_target (cover.base i)
    have hcf : ContDiffOn ℝ (∞ : ℕ∞ω) (f.smoothMap ∘ e.symm) e.target := by
      simpa [e] using chartContDiffOn f i
    have hj : (↑j : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
      exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top)
    have hwithin : ContinuousOn (iteratedFDerivWithin ℝ j (f.smoothMap ∘ e.symm) e.target)
        e.target := hcf.continuousOn_iteratedFDerivWithin hj hopen.uniqueDiffOn
    have hEq : Set.EqOn (iteratedFDerivWithin ℝ j (f.smoothMap ∘ e.symm) e.target)
        (iteratedFDeriv ℝ j (f.smoothMap ∘ e.symm)) e.target := by
      intro z hz
      apply iteratedFDerivWithin_eq_iteratedFDeriv hopen.uniqueDiffOn
      · exact (hcf.contDiffAt (hopen.mem_nhds hz)).of_le hj
      · exact hz
    exact (hwithin.congr hEq.symm).mono (cover.piece_in_target i)
  let J : SmoothChartHolderCore cover k α →ₗ[ℝ]
      SmoothChartHolderJetTarget cover j := {
    toFun f := fun i => ⟨(cover.piece i).domRestrict
      (fun z => iteratedFDeriv ℝ j
        (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z),
      (chartJetContinuous f i).domRestrict⟩
    map_add' f g := by
      apply funext
      intro i
      apply ContinuousMap.ext
      intro z
      change iteratedFDeriv ℝ j
          ((f + g).smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z =
        iteratedFDeriv ℝ j
          (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z +
        iteratedFDeriv ℝ j
          (g.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z
      apply iteratedFDeriv_add_apply
      · exact (chartContDiffOn f i).contDiffAt
          ((isOpen_extChartAt_target (cover.base i)).mem_nhds
            (cover.piece_in_target i z.2)) |>.of_le
            (by exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top))
      · exact (chartContDiffOn g i).contDiffAt
          ((isOpen_extChartAt_target (cover.base i)).mem_nhds
            (cover.piece_in_target i z.2)) |>.of_le
            (by exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top))
    map_smul' c f := by
      apply funext
      intro i
      apply ContinuousMap.ext
      intro z
      change iteratedFDeriv ℝ j
          ((c • f).smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z =
        c • iteratedFDeriv ℝ j
          (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z
      apply iteratedFDeriv_const_smul_apply
      exact (chartContDiffOn f i).contDiffAt
        ((isOpen_extChartAt_target (cover.base i)).mem_nhds
          (cover.piece_in_target i z.2)) |>.of_le
          (by exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top))
  }
  refine ⟨J, ?_, ?_⟩
  · intro f
    rw [pi_norm_le_iff_of_nonneg (ENNReal.toReal_nonneg)]
    intro i
    apply (ContinuousMap.norm_le _ ENNReal.toReal_nonneg).2
    intro z
    have hjet := CalabiYau.Schauder.spatialJet_le_eContDiffHolderGaugeOn k α
      (cover.piece i)
      (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm)
      (j := j) hj z.1 z.2
    have hpiece : CalabiYau.Schauder.eContDiffHolderGaugeOn k α (cover.piece i)
        (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) ≤
        smoothChartHolderGauge cover k α f := by
      change CalabiYau.Schauder.eContDiffHolderGaugeOn k α (cover.piece i)
          (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) ≤
        ⨆ q, CalabiYau.Schauder.eContDiffHolderGaugeOn k α (cover.piece q)
          (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base q)).symm)
      exact le_iSup (fun q : cover.ι => CalabiYau.Schauder.eContDiffHolderGaugeOn k α
        (cover.piece q)
        (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base q)).symm)) i
    have hpoint : ENNReal.ofReal ‖iteratedFDeriv ℝ j
        (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z.1‖ ≤
        smoothChartHolderGauge cover k α f := hjet.trans hpiece
    exact (ENNReal.ofReal_le_iff_le_toReal (N.finiteGauge f).ne_top).mp hpoint
  · intro f i z
    rfl

/-- Upgrade a chart-jet linear map with the gauge bound to a continuous linear map on the smooth
core. The normed data fixes the source norm to the gauge, so no separate continuity hypothesis is
needed. -/
noncomputable def smoothChartHolderJetContinuousLinearMap
    (cover : CompactChartCover E M) (k : ℕ) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover k α) (j : ℕ)
    (J : SmoothChartHolderCore cover k α →ₗ[ℝ] SmoothChartHolderJetTarget cover j)
    (hJ : ∀ f, ‖J f‖ ≤ (smoothChartHolderGauge cover k α f).toReal) :
    letI : NormedAddCommGroup (SmoothChartHolderCore cover k α) :=
      smoothChartHolderCoreNormedAddCommGroup cover k α N
    letI : NormedSpace ℝ (SmoothChartHolderCore cover k α) :=
      smoothChartHolderCoreNormedSpace cover k α N
    SmoothChartHolderCore cover k α →L[ℝ] SmoothChartHolderJetTarget cover j := by
  letI : NormedAddCommGroup (SmoothChartHolderCore cover k α) :=
    smoothChartHolderCoreNormedAddCommGroup cover k α N
  letI : NormedSpace ℝ (SmoothChartHolderCore cover k α) :=
    smoothChartHolderCoreNormedSpace cover k α N
  refine J.mkContinuous 1 (fun f => ?_)
  calc
    ‖J f‖ ≤ (smoothChartHolderGauge cover k α f).toReal := hJ f
    _ = ‖f‖ := (smoothChartHolderCore_norm_eq_gauge cover k α N f).symm
    _ = 1 * ‖f‖ := by ring

/-- The canonical continuous-linear chart-jet map selected using the gauge bound. -/
noncomputable def smoothChartHolderJetCanonicalContinuousLinearMap
    (cover : CompactChartCover E M) (k : ℕ) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover k α) (j : ℕ) (hj : j ≤ k) :
    letI : NormedAddCommGroup (SmoothChartHolderCore cover k α) :=
      smoothChartHolderCoreNormedAddCommGroup cover k α N
    letI : NormedSpace ℝ (SmoothChartHolderCore cover k α) :=
      smoothChartHolderCoreNormedSpace cover k α N
    SmoothChartHolderCore cover k α →L[ℝ] SmoothChartHolderJetTarget cover j := by
  let h := exists_smoothChartHolderJetLinearMap cover k α N j hj
  let J := Classical.choose h
  have hJ : ∀ f, ‖J f‖ ≤ (smoothChartHolderGauge cover k α f).toReal :=
    (Classical.choose_spec h).1
  exact smoothChartHolderJetContinuousLinearMap cover k α N j J hJ

/-- The canonical continuous-linear chart-jet map extended to the little-Hölder completion. -/
noncomputable def smoothChartHolderJetCanonicalExtension
    (cover : CompactChartCover E M) (k : ℕ) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover k α) (j : ℕ) (hj : j ≤ k) :
    letI : NormedAddCommGroup (SmoothChartHolderCore cover k α) :=
      smoothChartHolderCoreNormedAddCommGroup cover k α N
    letI : NormedSpace ℝ (SmoothChartHolderCore cover k α) :=
      smoothChartHolderCoreNormedSpace cover k α N
    LittleHolder cover k α N →L[ℝ] SmoothChartHolderJetTarget cover j := by
  letI : NormedAddCommGroup (SmoothChartHolderCore cover k α) :=
    smoothChartHolderCoreNormedAddCommGroup cover k α N
  letI : NormedSpace ℝ (SmoothChartHolderCore cover k α) :=
    smoothChartHolderCoreNormedSpace cover k α N
  exact (smoothChartHolderJetCanonicalContinuousLinearMap cover k α N j hj).fromCompletion

@[simp]
theorem smoothChartHolderJetCanonicalContinuousLinearMap_apply
    (cover : CompactChartCover E M) (k : ℕ) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover k α) (j : ℕ) (hj : j ≤ k)
    (f : SmoothChartHolderCore cover k α) (i) (z : cover.piece i) :
    letI : NormedAddCommGroup (SmoothChartHolderCore cover k α) :=
      smoothChartHolderCoreNormedAddCommGroup cover k α N
    letI : NormedSpace ℝ (SmoothChartHolderCore cover k α) :=
      smoothChartHolderCoreNormedSpace cover k α N
    smoothChartHolderJetCanonicalContinuousLinearMap cover k α N j hj f i z =
      smoothChartHolderJetData cover k α j f i z := by
  let h := exists_smoothChartHolderJetLinearMap cover k α N j hj
  exact (Classical.choose_spec h).2 f i z

@[simp]
theorem smoothChartHolderJetCanonicalExtension_coe
    (cover : CompactChartCover E M) (k : ℕ) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover k α) (j : ℕ) (hj : j ≤ k)
    (f : SmoothChartHolderCore cover k α) (i) (z : cover.piece i) :
    letI : NormedAddCommGroup (SmoothChartHolderCore cover k α) :=
      smoothChartHolderCoreNormedAddCommGroup cover k α N
    letI : NormedSpace ℝ (SmoothChartHolderCore cover k α) :=
      smoothChartHolderCoreNormedSpace cover k α N
    smoothChartHolderJetCanonicalExtension cover k α N j hj f i z =
      smoothChartHolderJetData cover k α j f i z := by
  let : NormedAddCommGroup (SmoothChartHolderCore cover k α) :=
    smoothChartHolderCoreNormedAddCommGroup cover k α N
  let : NormedSpace ℝ (SmoothChartHolderCore cover k α) :=
    smoothChartHolderCoreNormedSpace cover k α N
  rw [smoothChartHolderJetCanonicalExtension, ContinuousLinearMap.fromCompletion_apply_coe]
  exact smoothChartHolderJetCanonicalContinuousLinearMap_apply cover k α N j hj f i z

end KahlerForm
