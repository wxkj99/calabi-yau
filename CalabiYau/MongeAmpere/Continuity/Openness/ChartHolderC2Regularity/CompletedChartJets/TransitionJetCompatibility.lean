module

public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderEvaluation
public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderJets
import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderC2Regularity.CompletedChartJets.Identity

/-!
# Completed chart jets under smooth coordinate transitions

At a point lying in the interior of one chart piece and in an arbitrary point of another piece,
completed first and second jets transform by the first and second derivatives of the chart
transition. The second-order formula includes the derivative of the function applied to the second
derivative of the transition.
-/

@[expose] public section

noncomputable section

open scoped Manifold ContDiff NNReal Topology
open Filter

namespace KahlerForm

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
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

section

variable [CompactSpace M]

private theorem smoothChartHolderTransitionChainRuleOrderOne
    (G : E → ℝ) (τ : E → E) (z : E)
    (hG : ContDiffAt ℝ (∞ : ℕ∞ω) G (τ z))
    (hτ : ContDiffAt ℝ (∞ : ℕ∞ω) τ z) :
    ∀ m : Fin 1 → E,
      iteratedFDeriv ℝ 1 (G ∘ τ) z m =
        iteratedFDeriv ℝ 1 G (τ z) (fun k => fderiv ℝ τ z (m k)) := by
  intro m
  have h := fderiv_comp (𝕜 := ℝ) (f := τ) (g := G) (x := z)
    (hG.differentiableAt (by simp)) (hτ.differentiableAt (by simp))
  have hm := congrArg (fun A : E →L[ℝ] ℝ => A (m 0)) h
  simpa only [iteratedFDeriv_one_apply, ContinuousLinearMap.comp_apply] using hm

private theorem smoothChartHolderTransitionChainRuleOrderTwo
    (G : E → ℝ) (τ : E → E) (z : E)
    (hG : ContDiffAt ℝ (∞ : ℕ∞ω) G (τ z))
    (hτ : ContDiffAt ℝ (∞ : ℕ∞ω) τ z) :
    ∀ m : Fin 2 → E,
      iteratedFDeriv ℝ 2 (G ∘ τ) z m =
        iteratedFDeriv ℝ 2 G (τ z) (fun k => fderiv ℝ τ z (m k)) +
          iteratedFDeriv ℝ 1 G (τ z)
            (fun _ => iteratedFDeriv ℝ 2 τ z m) := by
  let c : E → E →L[ℝ] ℝ := fun y => fderiv ℝ G (τ y)
  let d : E → E →L[ℝ] E := fun y => fderiv ℝ τ y
  have h2le : ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) :=
    WithTop.coe_le_coe.mpr ((WithTop.coe_lt_top (2 : ℕ)).le)
  have hG₂ : ContDiffAt ℝ (2 : ℕ∞ω) G (τ z) := hG.of_le h2le
  have hτ₂ : ContDiffAt ℝ (2 : ℕ∞ω) τ z := hτ.of_le h2le
  have hNearG : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ (2 : ℕ∞ω) G (τ y) :=
    hτ.continuousAt.eventually (hG₂.eventually (by norm_num))
  have hNearτ : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ (2 : ℕ∞ω) τ y :=
    hτ₂.eventually (by norm_num)
  have hEq : (fun y => fderiv ℝ (G ∘ τ) y) =ᶠ[𝓝 z]
      (fun y => (c y).comp (d y)) := by
    filter_upwards [hNearG, hNearτ] with y hyG hyτ
    simpa [c, d] using (fderiv_comp (𝕜 := ℝ) (f := τ) (g := G) (x := y)
      (hyG.differentiableAt (by norm_num)) (hyτ.differentiableAt (by norm_num)))
  have hGfderiv : DifferentiableAt ℝ (fderiv ℝ G) (τ z) := by
    have h := hG₂.fderiv_right (m := 1) (by norm_num)
    exact h.differentiableAt (by norm_num)
  have hτfderiv : DifferentiableAt ℝ (fderiv ℝ τ) z := by
    have h := hτ₂.fderiv_right (m := 1) (by norm_num)
    exact h.differentiableAt (by norm_num)
  have hc : DifferentiableAt ℝ c z := by
    change DifferentiableAt ℝ (fderiv ℝ G ∘ τ) z
    exact hGfderiv.comp z (hτ.differentiableAt (by norm_num))
  have hd : DifferentiableAt ℝ d z := hτfderiv
  have hEq' : fderiv ℝ (fun y => fderiv ℝ (G ∘ τ) y) z =
      fderiv ℝ (fun y => (c y).comp (d y)) z := hEq.fderiv_eq
  have hFormula := fderiv_clm_comp hc hd
  intro m
  rw [iteratedFDeriv_two_apply, hEq', hFormula]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, c, d]
  have hcEq : fderiv ℝ (fun y => fderiv ℝ G (τ y)) z =
      (fderiv ℝ (fderiv ℝ G) (τ z)).comp (fderiv ℝ τ z) := by
    simpa [Function.comp_def] using (fderiv_comp (𝕜 := ℝ) (f := τ)
      (g := fderiv ℝ G) (x := z) hGfderiv (hτ.differentiableAt (by norm_num)))
  rw [hcEq]
  simp [iteratedFDeriv_two_apply, iteratedFDeriv_one_apply,
    ContinuousLinearMap.comp_apply]
  ring

end

private theorem smoothChartHolderCoreTransitionJetCompatibility_orderOne
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (f : SmoothChartHolderCore cover 2 α) (i j : cover.ι) (z w : E)
    (hz : z ∈ cover.piece i) (hw : w ∈ interior (cover.piece j))
    (hcoord : (extChartAt 𝓘(ℝ, E) (cover.base i)).symm z =
      (extChartAt 𝓘(ℝ, E) (cover.base j)).symm w) :
    ∀ m : Fin 1 → E,
      iteratedFDeriv ℝ 1 (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z m =
      iteratedFDeriv ℝ 1 (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base j)).symm) w
        (fun k => fderiv ℝ
          ((extChartAt 𝓘(ℝ, E) (cover.base j)) ∘
            (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z (m k)) := by
  let ei := extChartAt 𝓘(ℝ, E) (cover.base i)
  let ej := extChartAt 𝓘(ℝ, E) (cover.base j)
  let τ : E → E := ej ∘ ei.symm
  let G : E → ℝ := f.smoothMap ∘ ej.symm
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
  have hnear : ∀ᶠ y in 𝓝 z, ei.symm y ∈ ej.source := by
    have hxSource' : ei.symm z ∈ ej.source := by
      simpa [ej, extChartAt_source] using hxSource
    have hopen : IsOpen ej.source := isOpen_extChartAt_source (cover.base j)
    exact (hsymm.continuousAt.tendsto).eventually (hopen.mem_nhds hxSource')
  have hlocalEq : (f.smoothMap ∘ ei.symm) =ᶠ[𝓝 z] (G ∘ τ) := by
    filter_upwards [hnear] with y hy
    change f.smoothMap (ei.symm y) = f.smoothMap (ej.symm (ej (ei.symm y)))
    rw [ej.left_inv hy]
  have hτ : ContDiffAt ℝ (∞ : ℕ∞ω) τ z :=
    smoothChartHolderTransition_contDiffAt cover i j z w hz hw hcoord
  have hτz : τ z = w := by
    calc
      τ z = ej (ei.symm z) := rfl
      _ = ej (ej.symm w) := by rw [hcoord]
      _ = w := ej.right_inv hwTarget
  have hG : ContDiffAt ℝ (∞ : ℕ∞ω) G (τ z) := by
    have hcont : ContDiffOn ℝ (∞ : ℕ∞ω) (f.smoothMap ∘ ej.symm) ej.target := by
      have h := (contMDiff_iff.mp f.smoothMap.contMDiff).2 (cover.base j) 0
      simpa [ej, extChartAt, chartAt_self_eq] using h
    have hopen : IsOpen ej.target := isOpen_extChartAt_target (cover.base j)
    rw [hτz]
    exact hcont.contDiffAt (hopen.mem_nhds hwTarget)
  have hfirst := (hlocalEq.iteratedFDeriv ℝ 1).self_of_nhds
  intro m
  rw [hfirst]
  have hchain := smoothChartHolderTransitionChainRuleOrderOne G τ z hG hτ m
  rw [hτz] at hchain
  simpa [G, τ, ei, ej, extChartAt] using hchain

private theorem smoothChartHolderCoreTransitionJetCompatibility_orderTwo
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (f : SmoothChartHolderCore cover 2 α) (i j : cover.ι) (z w : E)
    (hz : z ∈ cover.piece i) (hw : w ∈ interior (cover.piece j))
    (hcoord : (extChartAt 𝓘(ℝ, E) (cover.base i)).symm z =
      (extChartAt 𝓘(ℝ, E) (cover.base j)).symm w) :
    ∀ m : Fin 2 → E,
      iteratedFDeriv ℝ 2 (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z m =
      iteratedFDeriv ℝ 2 (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base j)).symm) w
          (fun k => fderiv ℝ
            ((extChartAt 𝓘(ℝ, E) (cover.base j)) ∘
              (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z (m k)) +
        iteratedFDeriv ℝ 1 (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base j)).symm) w
          (fun _ => iteratedFDeriv ℝ 2
            ((extChartAt 𝓘(ℝ, E) (cover.base j)) ∘
              (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z m) := by
  let ei := extChartAt 𝓘(ℝ, E) (cover.base i)
  let ej := extChartAt 𝓘(ℝ, E) (cover.base j)
  let τ : E → E := ej ∘ ei.symm
  let G : E → ℝ := f.smoothMap ∘ ej.symm
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
  have hnear : ∀ᶠ y in 𝓝 z, ei.symm y ∈ ej.source := by
    have hxSource' : ei.symm z ∈ ej.source := by
      simpa [ej, extChartAt_source] using hxSource
    have hopen : IsOpen ej.source := isOpen_extChartAt_source (cover.base j)
    exact (hsymm.continuousAt.tendsto).eventually (hopen.mem_nhds hxSource')
  have hlocalEq : (f.smoothMap ∘ ei.symm) =ᶠ[𝓝 z] (G ∘ τ) := by
    filter_upwards [hnear] with y hy
    change f.smoothMap (ei.symm y) = f.smoothMap (ej.symm (ej (ei.symm y)))
    rw [ej.left_inv hy]
  have hτ : ContDiffAt ℝ (∞ : ℕ∞ω) τ z :=
    smoothChartHolderTransition_contDiffAt cover i j z w hz hw hcoord
  have hτz : τ z = w := by
    calc
      τ z = ej (ei.symm z) := rfl
      _ = ej (ej.symm w) := by rw [hcoord]
      _ = w := ej.right_inv hwTarget
  have hG : ContDiffAt ℝ (∞ : ℕ∞ω) G (τ z) := by
    have hcont : ContDiffOn ℝ (∞ : ℕ∞ω) (f.smoothMap ∘ ej.symm) ej.target := by
      have h := (contMDiff_iff.mp f.smoothMap.contMDiff).2 (cover.base j) 0
      simpa [ej, extChartAt, chartAt_self_eq] using h
    have hopen : IsOpen ej.target := isOpen_extChartAt_target (cover.base j)
    rw [hτz]
    exact hcont.contDiffAt (hopen.mem_nhds hwTarget)
  have hsecond := (hlocalEq.iteratedFDeriv ℝ 2).self_of_nhds
  intro m
  rw [hsecond]
  have hchain := smoothChartHolderTransitionChainRuleOrderTwo G τ z hG hτ m
  rw [hτz] at hchain
  simpa [G, τ, ei, ej, extChartAt] using hchain

private theorem smoothChartHolderCanonicalTransitionJetOrderOne
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover 2 α)
    (u : LittleHolder cover 2 α N) (i j : cover.ι) (z w : E)
    (hz : z ∈ cover.piece i) (hw : w ∈ interior (cover.piece j))
    (hcoord : (extChartAt 𝓘(ℝ, E) (cover.base i)).symm z =
      (extChartAt 𝓘(ℝ, E) (cover.base j)).symm w) :
    ∀ m : Fin 1 → E,
      smoothChartHolderJetCanonicalExtension cover 2 α N 1 (by omega) u i
        ⟨z, hz⟩ m =
      smoothChartHolderJetCanonicalExtension cover 2 α N 1 (by omega) u j
        ⟨w, interior_subset hw⟩
        (fun k => fderiv ℝ
          ((extChartAt 𝓘(ℝ, E) (cover.base j)) ∘
            (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z (m k)) := by
  classical
  let : NormedAddCommGroup (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedAddCommGroup cover 2 α N
  let : NormedSpace ℝ (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedSpace cover 2 α N
  intro m
  let p : cover.piece i := ⟨z, hz⟩
  let q : cover.piece j := ⟨w, interior_subset hw⟩
  let A : LittleHolder cover 2 α N → ℝ := fun v =>
    smoothChartHolderJetCanonicalExtension cover 2 α N 1 (by omega) v i p m
  let B : LittleHolder cover 2 α N → ℝ := fun v =>
    smoothChartHolderJetCanonicalExtension cover 2 α N 1 (by omega) v j q
      (fun k => fderiv ℝ
        ((extChartAt 𝓘(ℝ, E) (cover.base j)) ∘
          (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z (m k))
  have hA : Continuous A := by
    change Continuous ((fun T : SmoothChartHolderJetTarget cover 1 => T i p m) ∘
      smoothChartHolderJetCanonicalExtension cover 2 α N 1 (by omega))
    fun_prop
  have hB : Continuous B := by
    change Continuous ((fun T : SmoothChartHolderJetTarget cover 1 =>
      T j q (fun k => fderiv ℝ
        ((extChartAt 𝓘(ℝ, E) (cover.base j)) ∘
          (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z (m k))) ∘
      smoothChartHolderJetCanonicalExtension cover 2 α N 1 (by omega))
    fun_prop
  have hclosed : IsClosed {v : LittleHolder cover 2 α N | A v = B v} :=
    isClosed_eq hA hB
  have hcore : ∀ f : SmoothChartHolderCore cover 2 α,
      A (f : LittleHolder cover 2 α N) = B (f : LittleHolder cover 2 α N) := by
    intro f
    simp only [A, B, smoothChartHolderJetCanonicalExtension_coe,
      smoothChartHolderJetData]
    exact (smoothChartHolderCoreTransitionJetCompatibility_orderOne
      cover α f i j z w hz hw hcoord) m
  exact UniformSpace.Completion.induction_on u hclosed hcore

private theorem smoothChartHolderCanonicalTransitionJetOrderTwo
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover 2 α)
    (u : LittleHolder cover 2 α N) (i j : cover.ι) (z w : E)
    (hz : z ∈ cover.piece i) (hw : w ∈ interior (cover.piece j))
    (hcoord : (extChartAt 𝓘(ℝ, E) (cover.base i)).symm z =
      (extChartAt 𝓘(ℝ, E) (cover.base j)).symm w) :
    ∀ m : Fin 2 → E,
      smoothChartHolderJetCanonicalExtension cover 2 α N 2 le_rfl u i
        ⟨z, hz⟩ m =
      smoothChartHolderJetCanonicalExtension cover 2 α N 2 le_rfl u j
        ⟨w, interior_subset hw⟩
          (fun k => fderiv ℝ
            ((extChartAt 𝓘(ℝ, E) (cover.base j)) ∘
              (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z (m k)) +
        smoothChartHolderJetCanonicalExtension cover 2 α N 1 (by omega) u j
          ⟨w, interior_subset hw⟩
          (fun _ => iteratedFDeriv ℝ 2
            ((extChartAt 𝓘(ℝ, E) (cover.base j)) ∘
              (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z m) := by
  classical
  let : NormedAddCommGroup (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedAddCommGroup cover 2 α N
  let : NormedSpace ℝ (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedSpace cover 2 α N
  intro m
  let p : cover.piece i := ⟨z, hz⟩
  let q : cover.piece j := ⟨w, interior_subset hw⟩
  let A : LittleHolder cover 2 α N → ℝ := fun v =>
    smoothChartHolderJetCanonicalExtension cover 2 α N 2 le_rfl v i p m
  let B : LittleHolder cover 2 α N → ℝ := fun v =>
    smoothChartHolderJetCanonicalExtension cover 2 α N 2 le_rfl v j q
        (fun k => fderiv ℝ
          ((extChartAt 𝓘(ℝ, E) (cover.base j)) ∘
            (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z (m k)) +
      smoothChartHolderJetCanonicalExtension cover 2 α N 1 (by omega) v j q
        (fun _ => iteratedFDeriv ℝ 2
          ((extChartAt 𝓘(ℝ, E) (cover.base j)) ∘
            (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z m)
  have hA : Continuous A := by
    change Continuous ((fun T : SmoothChartHolderJetTarget cover 2 => T i p m) ∘
      smoothChartHolderJetCanonicalExtension cover 2 α N 2 le_rfl)
    fun_prop
  have hB : Continuous B := by
    change Continuous (fun v =>
      smoothChartHolderJetCanonicalExtension cover 2 α N 2 le_rfl v j q
          (fun k => fderiv ℝ
            ((extChartAt 𝓘(ℝ, E) (cover.base j)) ∘
              (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z (m k)) +
        smoothChartHolderJetCanonicalExtension cover 2 α N 1 (by omega) v j q
          (fun _ => iteratedFDeriv ℝ 2
            ((extChartAt 𝓘(ℝ, E) (cover.base j)) ∘
              (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z m))
    fun_prop
  have hclosed : IsClosed {v : LittleHolder cover 2 α N | A v = B v} :=
    isClosed_eq hA hB
  have hcore : ∀ f : SmoothChartHolderCore cover 2 α,
      A (f : LittleHolder cover 2 α N) = B (f : LittleHolder cover 2 α N) := by
    intro f
    simp only [A, B, smoothChartHolderJetCanonicalExtension_coe,
      smoothChartHolderJetData]
    exact (smoothChartHolderCoreTransitionJetCompatibility_orderTwo
      cover α f i j z w hz hw hcoord) m
  exact UniformSpace.Completion.induction_on u hclosed hcore

section

variable [CompactSpace M]

private theorem smoothChartHolderTransitionFiniteChainRuleOrderOne
    (G : E → ℝ) (τ : E → E) (z : E)
    (hG : ContDiffAt ℝ (2 : ℕ∞ω) G (τ z))
    (hτ : ContDiffAt ℝ (2 : ℕ∞ω) τ z) :
    ∀ m : Fin 1 → E,
      iteratedFDeriv ℝ 1 (G ∘ τ) z m =
        iteratedFDeriv ℝ 1 G (τ z) (fun k => fderiv ℝ τ z (m k)) := by
  intro m
  have h := fderiv_comp (𝕜 := ℝ) (f := τ) (g := G) (x := z)
    (hG.differentiableAt (by norm_num)) (hτ.differentiableAt (by norm_num))
  have hm := congrArg (fun A : E →L[ℝ] ℝ => A (m 0)) h
  simpa only [iteratedFDeriv_one_apply, ContinuousLinearMap.comp_apply] using hm

private theorem smoothChartHolderTransitionFiniteChainRuleOrderTwo
    (G : E → ℝ) (τ : E → E) (z : E)
    (hG : ContDiffAt ℝ (2 : ℕ∞ω) G (τ z))
    (hτ : ContDiffAt ℝ (2 : ℕ∞ω) τ z) :
    ∀ m : Fin 2 → E,
      iteratedFDeriv ℝ 2 (G ∘ τ) z m =
        iteratedFDeriv ℝ 2 G (τ z) (fun k => fderiv ℝ τ z (m k)) +
          iteratedFDeriv ℝ 1 G (τ z)
            (fun _ => iteratedFDeriv ℝ 2 τ z m) := by
  let c : E → E →L[ℝ] ℝ := fun y => fderiv ℝ G (τ y)
  let d : E → E →L[ℝ] E := fun y => fderiv ℝ τ y
  have hNearG : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ (2 : ℕ∞ω) G (τ y) :=
    hτ.continuousAt.eventually (hG.eventually (by norm_num))
  have hNearτ : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ (2 : ℕ∞ω) τ y :=
    hτ.eventually (by norm_num)
  have hEq : (fun y => fderiv ℝ (G ∘ τ) y) =ᶠ[𝓝 z]
      (fun y => (c y).comp (d y)) := by
    filter_upwards [hNearG, hNearτ] with y hyG hyτ
    simpa [c, d] using (fderiv_comp (𝕜 := ℝ) (f := τ) (g := G) (x := y)
      (hyG.differentiableAt (by norm_num)) (hyτ.differentiableAt (by norm_num)))
  have hGfderiv : DifferentiableAt ℝ (fderiv ℝ G) (τ z) := by
    have h := hG.fderiv_right (m := 1) (by norm_num)
    exact h.differentiableAt (by norm_num)
  have hτfderiv : DifferentiableAt ℝ (fderiv ℝ τ) z := by
    have h := hτ.fderiv_right (m := 1) (by norm_num)
    exact h.differentiableAt (by norm_num)
  have hc : DifferentiableAt ℝ c z := by
    change DifferentiableAt ℝ (fderiv ℝ G ∘ τ) z
    exact hGfderiv.comp z (hτ.differentiableAt (by norm_num))
  have hd : DifferentiableAt ℝ d z := hτfderiv
  have hEq' : fderiv ℝ (fun y => fderiv ℝ (G ∘ τ) y) z =
      fderiv ℝ (fun y => (c y).comp (d y)) z := hEq.fderiv_eq
  have hFormula := fderiv_clm_comp hc hd
  intro m
  rw [iteratedFDeriv_two_apply, hEq', hFormula]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, c, d]
  have hcEq : fderiv ℝ (fun y => fderiv ℝ G (τ y)) z =
      (fderiv ℝ (fderiv ℝ G) (τ z)).comp (fderiv ℝ τ z) := by
    simpa [Function.comp_def] using (fderiv_comp (𝕜 := ℝ) (f := τ)
      (g := fderiv ℝ G) (x := z) hGfderiv (hτ.differentiableAt (by norm_num)))
  rw [hcEq]
  simp [iteratedFDeriv_two_apply, iteratedFDeriv_one_apply,
    ContinuousLinearMap.comp_apply]
  ring

end

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
section

variable [CompactSpace M]

omit [FiniteDimensional ℝ E] in
private theorem smoothChartHolderCompletedInteriorContDiffAt
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover 2 α)
    (u : LittleHolder cover 2 α N) (j : cover.ι) (q : E)
    (hq : q ∈ interior (cover.piece j)) :
    ContDiffAt ℝ (2 : ℕ∞ω)
      ((smoothChartHolderContinuousMapExtension cover 2 α N u : M → ℝ) ∘
        (extChartAt 𝓘(ℝ, E) (cover.base j)).symm) q := by
  exact KahlerForm.smoothChartHolderCompletedContDiffAt cover α N u j q hq

omit [FiniteDimensional ℝ E] in
private theorem smoothChartHolderActualTransitionJetCompatibility
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover 2 α)
    (u : LittleHolder cover 2 α N) (i j : cover.ι) (z q : E)
    (hz : z ∈ cover.piece i) (hq : q ∈ interior (cover.piece j))
    (hoverlap : (extChartAt 𝓘(ℝ, E) (cover.base i)).symm z =
      (extChartAt 𝓘(ℝ, E) (cover.base j)).symm q) :
    (∀ m : Fin 1 → E,
      iteratedFDeriv ℝ 1
          ((smoothChartHolderContinuousMapExtension cover 2 α N u : M → ℝ) ∘
            (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z m =
        smoothChartHolderJetCanonicalExtension cover 2 α N 1 (by omega) u j
          ⟨q, interior_subset hq⟩ (fun k =>
            fderiv ℝ ((fun y => (extChartAt 𝓘(ℝ, E) (cover.base j))
              ((extChartAt 𝓘(ℝ, E) (cover.base i)).symm y))) z (m k))) ∧
    (∀ m : Fin 2 → E,
      iteratedFDeriv ℝ 2
          ((smoothChartHolderContinuousMapExtension cover 2 α N u : M → ℝ) ∘
            (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z m =
        smoothChartHolderJetCanonicalExtension cover 2 α N 2 le_rfl u j
          ⟨q, interior_subset hq⟩ (fun k =>
            fderiv ℝ ((fun y => (extChartAt 𝓘(ℝ, E) (cover.base j))
              ((extChartAt 𝓘(ℝ, E) (cover.base i)).symm y))) z (m k)) +
          smoothChartHolderJetCanonicalExtension cover 2 α N 1 (by omega) u j
            ⟨q, interior_subset hq⟩
              (fun _ => iteratedFDeriv ℝ 2 ((fun y => (extChartAt 𝓘(ℝ, E) (cover.base j))
              ((extChartAt 𝓘(ℝ, E) (cover.base i)).symm y))) z m)) := by
  have hreg := smoothChartHolderCompletedInteriorContDiffAt cover α N u j q hq
  let ei := extChartAt 𝓘(ℝ, E) (cover.base i)
  let ej := extChartAt 𝓘(ℝ, E) (cover.base j)
  let τ : E → E := ej ∘ ei.symm
  let G : E → ℝ :=
    (smoothChartHolderContinuousMapExtension cover 2 α N u : M → ℝ) ∘ ej.symm
  have hqTarget : q ∈ ej.target := cover.piece_in_target j (interior_subset hq)
  have hzTarget : z ∈ ei.target := cover.piece_in_target i hz
  have hxSource : ei.symm z ∈ ej.source := by
    rw [hoverlap]
    exact ej.map_target hqTarget
  have hsymm : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) (∞ : ℕ∞ω) ei.symm z :=
    (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, E)) (cover.base i)).contMDiffAt
      ((isOpen_extChartAt_target (cover.base i)).mem_nhds hzTarget)
  have hnear : ∀ᶠ y in 𝓝 z, ei.symm y ∈ ej.source :=
    hsymm.continuousAt.tendsto.eventually
      ((isOpen_extChartAt_source (cover.base j)).mem_nhds hxSource)
  have hlocalEq :
      ((smoothChartHolderContinuousMapExtension cover 2 α N u : M → ℝ) ∘ ei.symm)
        =ᶠ[𝓝 z] (G ∘ τ) := by
    filter_upwards [hnear] with y hy
    change smoothChartHolderContinuousMapExtension cover 2 α N u (ei.symm y) =
      smoothChartHolderContinuousMapExtension cover 2 α N u (ej.symm (ej (ei.symm y)))
    rw [ej.left_inv hy]
  have hτz : τ z = q := by
    change ej (ei.symm z) = q
    rw [hoverlap, ej.right_inv hqTarget]
  have hτsmooth : ContDiffAt ℝ (∞ : ℕ∞ω) τ z := by
    have hx : ei.symm z ∈ (chartAt E (cover.base j)).source := by
      simpa [ej, extChartAt_source] using hxSource
    exact ((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) hx).comp z hsymm).contDiffAt
  have hτ : ContDiffAt ℝ (2 : ℕ∞ω) τ z := hτsmooth.of_le
    (WithTop.coe_le_coe.mpr ((WithTop.coe_lt_top (2 : ℕ)).le))
  have hG : ContDiffAt ℝ (2 : ℕ∞ω) G (τ z) := by
    rw [hτz]
    exact hreg
  have hG1 : iteratedFDeriv ℝ 1 G q =
      smoothChartHolderJetCanonicalExtension cover 2 α N 1 (by omega) u j
        ⟨q, interior_subset hq⟩ := by
    exact smoothChartHolderCompletedJetIdentity cover α N u 1 (by omega) j q hq
  have hG2 : iteratedFDeriv ℝ 2 G q =
      smoothChartHolderJetCanonicalExtension cover 2 α N 2 le_rfl u j
        ⟨q, interior_subset hq⟩ := by
    exact smoothChartHolderCompletedJetIdentity cover α N u 2 le_rfl j q hq
  constructor
  · intro m
    have hEq := congrArg (fun A : E [×1]→L[ℝ] ℝ => A m)
      ((hlocalEq.iteratedFDeriv ℝ 1).self_of_nhds)
    have hChain := smoothChartHolderTransitionFiniteChainRuleOrderOne G τ z hG hτ m
    rw [hτz, hG1] at hChain
    exact hEq.trans hChain
  · intro m
    have hEq := congrArg (fun A : E [×2]→L[ℝ] ℝ => A m)
      ((hlocalEq.iteratedFDeriv ℝ 2).self_of_nhds)
    have hChain := smoothChartHolderTransitionFiniteChainRuleOrderTwo G τ z hG hτ m
    rw [hτz, hG2, hG1] at hChain
    exact hEq.trans hChain

omit [FiniteDimensional ℝ E] in
/-- At an overlap where the point is interior to chart `j`'s compact piece, the actual first and
second coordinate derivatives in chart `i` and the canonical completed jets in chart `i` both agree
with the corresponding chain-rule transports of the canonical jets in chart `j`. The second-order
transport includes the essential `Dg · D²τ` term. The overlap hypotheses place both chart points in
their respective domains; smoothness of the transition follows from the standing smooth-manifold
assumption. No closure-of-interior assumption is made. -/
theorem smoothChartHolderCompletedTransitionJetCompatibility
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover 2 α)
    (u : LittleHolder cover 2 α N) (i j : cover.ι) (z q : E)
    (hz : z ∈ cover.piece i) (hq : q ∈ interior (cover.piece j))
    (hoverlap : (extChartAt 𝓘(ℝ, E) (cover.base i)).symm z =
      (extChartAt 𝓘(ℝ, E) (cover.base j)).symm q) :
    (∀ m : Fin 1 → E,
      iteratedFDeriv ℝ 1
          ((smoothChartHolderContinuousMapExtension cover 2 α N u : M → ℝ) ∘
            (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z m =
        smoothChartHolderJetCanonicalExtension cover 2 α N 1 (by omega) u j
          ⟨q, interior_subset hq⟩ (fun k =>
            fderiv ℝ ((fun y => (extChartAt 𝓘(ℝ, E) (cover.base j))
              ((extChartAt 𝓘(ℝ, E) (cover.base i)).symm y))) z (m k))) ∧
    (∀ m : Fin 1 → E,
      smoothChartHolderJetCanonicalExtension cover 2 α N 1 (by omega) u i
          ⟨z, hz⟩ m =
        smoothChartHolderJetCanonicalExtension cover 2 α N 1 (by omega) u j
          ⟨q, interior_subset hq⟩ (fun k =>
            fderiv ℝ ((fun y => (extChartAt 𝓘(ℝ, E) (cover.base j))
              ((extChartAt 𝓘(ℝ, E) (cover.base i)).symm y))) z (m k))) ∧
    (∀ m : Fin 2 → E,
      iteratedFDeriv ℝ 2
          ((smoothChartHolderContinuousMapExtension cover 2 α N u : M → ℝ) ∘
            (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z m =
        smoothChartHolderJetCanonicalExtension cover 2 α N 2 le_rfl u j
          ⟨q, interior_subset hq⟩ (fun k =>
            fderiv ℝ ((fun y => (extChartAt 𝓘(ℝ, E) (cover.base j))
              ((extChartAt 𝓘(ℝ, E) (cover.base i)).symm y))) z (m k)) +
          smoothChartHolderJetCanonicalExtension cover 2 α N 1 (by omega) u j
            ⟨q, interior_subset hq⟩
              (fun _ => iteratedFDeriv ℝ 2 ((fun y => (extChartAt 𝓘(ℝ, E) (cover.base j))
              ((extChartAt 𝓘(ℝ, E) (cover.base i)).symm y))) z m)) ∧
    (∀ m : Fin 2 → E,
      smoothChartHolderJetCanonicalExtension cover 2 α N 2 le_rfl u i
          ⟨z, hz⟩ m =
        smoothChartHolderJetCanonicalExtension cover 2 α N 2 le_rfl u j
          ⟨q, interior_subset hq⟩ (fun k =>
            fderiv ℝ ((fun y => (extChartAt 𝓘(ℝ, E) (cover.base j))
              ((extChartAt 𝓘(ℝ, E) (cover.base i)).symm y))) z (m k)) +
          smoothChartHolderJetCanonicalExtension cover 2 α N 1 (by omega) u j
            ⟨q, interior_subset hq⟩
              (fun _ => iteratedFDeriv ℝ 2 ((fun y => (extChartAt 𝓘(ℝ, E) (cover.base j))
              ((extChartAt 𝓘(ℝ, E) (cover.base i)).symm y))) z m)) := by
  rcases smoothChartHolderActualTransitionJetCompatibility
      cover α N u i j z q hz hq hoverlap with ⟨hfirst, hsecond⟩
  refine ⟨hfirst, ?_⟩
  refine ⟨?_, ?_⟩
  · intro m
    exact smoothChartHolderCanonicalTransitionJetOrderOne
      cover α N u i j z q hz hq hoverlap m
  · refine ⟨hsecond, ?_⟩
    intro m
    exact smoothChartHolderCanonicalTransitionJetOrderTwo
      cover α N u i j z q hz hq hoverlap m

end

end

end KahlerForm
