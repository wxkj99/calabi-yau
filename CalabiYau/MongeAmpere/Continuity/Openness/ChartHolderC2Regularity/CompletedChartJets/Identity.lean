module

import Mathlib.Analysis.Calculus.UniformLimitsDeriv

public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderEvaluation
public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderJets

/-!
# Identity of completed coordinate jets

On the interior of a fixed chart piece, the coordinate derivatives of completed evaluation agree
with the canonical extensions of the smooth-core jets.
-/

@[expose] public section

noncomputable section

open scoped Manifold ContDiff NNReal Topology
open Filter

namespace KahlerForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]

/-- Genuine first derivative of completed evaluation on the open chart-piece interior. The
uniform derivative-limit argument (Gilbarg–Trudinger, §4.1, pp. 51–53) gives `HasFDerivAt`, not merely
an equality of totalized `fderiv` values. The supplied normed data suffice even at exponent zero. -/
public theorem smoothChartHolderCompletedHasFDerivAt
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover 2 α)
    (u : LittleHolder cover 2 α N) (i) (z : E)
    (hz : z ∈ interior (cover.piece i)) :
    HasFDerivAt
      ((smoothChartHolderContinuousMapExtension cover 2 α N u : M → ℝ) ∘
        (extChartAt 𝓘(ℝ, E) (cover.base i)).symm)
      (continuousMultilinearCurryFin1 ℝ E ℝ
        (smoothChartHolderJetCanonicalExtension cover 2 α N 1
          (Nat.le_succ 1) u i ⟨z, interior_subset hz⟩)) z := by
  classical
  letI : NormedAddCommGroup (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedAddCommGroup cover 2 α N
  letI : NormedSpace ℝ (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedSpace cover 2 α N
  have hdense (n : ℕ) : ∃ f : SmoothChartHolderCore cover 2 α,
      dist (f : LittleHolder cover 2 α N) u < 1 / ((n : ℝ) + 1) := by
    have hcl := (Metric.mem_closure_iff.mp
      (UniformSpace.Completion.denseRange_coe u))
      (1 / ((n : ℝ) + 1)) (by positivity)
    rcases hcl with ⟨v, hv, hdist⟩
    rcases hv with ⟨f, rfl⟩
    exact ⟨f, by simpa [dist_comm] using hdist⟩
  choose f hf using hdense
  have hfseq : Tendsto (fun n => (f n : LittleHolder cover 2 α N)) atTop (𝓝 u) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    obtain ⟨Nε, hNε⟩ := exists_nat_gt (1 / ε)
    refine ⟨Nε, ?_⟩
    intro n hn
    have hlt : 1 / ((n : ℝ) + 1) < ε := by
      have hn' : (Nε : ℝ) ≤ n := by exact_mod_cast hn
      have hNε' : (1 / ε) < (Nε : ℝ) := by exact_mod_cast hNε
      have hdiv : (1 / ε) < (n : ℝ) + 1 := by linarith
      have hmul' : (1 : ℝ) < ((n : ℝ) + 1) * ε := (div_lt_iff₀ hε).mp hdiv
      have hmul : (1 : ℝ) < ε * ((n : ℝ) + 1) := by nlinarith [hmul']
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    exact (hf n).trans hlt
  let value := smoothChartHolderContinuousMapExtension cover 2 α N
  let jets := smoothChartHolderJetCanonicalExtension cover 2 α N 1 (by norm_num)
  let chart := (extChartAt 𝓘(ℝ, E) (cover.base i)).symm
  let g : E → ℝ := fun x => value u (chart x)
  let g' : E → E →L[ℝ] ℝ := fun x =>
    if hx : x ∈ cover.piece i then
      continuousMultilinearCurryFin1 ℝ E ℝ (jets u i ⟨x, hx⟩)
    else 0
  let d : ℕ → E → E →L[ℝ] ℝ := fun n x =>
    if hx : x ∈ cover.piece i then
      continuousMultilinearCurryFin1 ℝ E ℝ (jets (f n : LittleHolder cover 2 α N) i ⟨x, hx⟩)
    else 0
  have hvalue : Tendsto (fun n => value (f n : LittleHolder cover 2 α N))
      atTop (𝓝 (value u)) := (value.continuous.tendsto u).comp hfseq
  have hjets : Tendsto (fun n => jets (f n : LittleHolder cover 2 α N))
      atTop (𝓝 (jets u)) := (jets.continuous.tendsto u).comp hfseq
  have hjetAt : Tendsto (fun n => (jets (f n : LittleHolder cover 2 α N)) i)
      atTop (𝓝 ((jets u) i)) :=
    (continuous_apply i).tendsto _ |>.comp hjets
  have hjetUniform : TendstoUniformly
      (fun n p => (jets (f n : LittleHolder cover 2 α N)) i p)
      ((jets u) i) atTop :=
    ContinuousMap.tendsto_iff_tendstoUniformly.mp hjetAt
  have hderivUniform : TendstoUniformlyOn d g' atTop (interior (cover.piece i)) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    rw [Metric.tendstoUniformly_iff] at hjetUniform
    filter_upwards [hjetUniform ε hε] with n hn
    intro x hx
    have hxpiece : x ∈ cover.piece i := interior_subset hx
    simpa [d, g', hxpiece] using hn ⟨x, hxpiece⟩
  have hfunc n x : value (f n : LittleHolder cover 2 α N) (chart x) =
      (f n).smoothMap (chart x) := by
    dsimp [value]
    rw [smoothChartHolderContinuousMapExtension_coe]
    rfl
  have hfg : ∀ x : E, x ∈ interior (cover.piece i) →
      Tendsto (fun n => (f n).smoothMap (chart x)) atTop (𝓝 (g x)) := by
    intro x hx
    have heval := ((ContinuousMap.evalCLM (R := ℝ) (chart x)).continuous.tendsto
      (value u)).comp hvalue
    have heval' : Tendsto
        (fun n => value (f n : LittleHolder cover 2 α N) (chart x))
        atTop (𝓝 (value u (chart x))) := by
      change Tendsto ((fun q : C(M, ℝ) => q (chart x)) ∘
        (fun n => value (f n : LittleHolder cover 2 α N))) atTop _
      exact heval
    have heq : (fun n => value (f n : LittleHolder cover 2 α N) (chart x)) =
        (fun n => (f n).smoothMap (chart x)) := funext (fun n => hfunc n x)
    rw [← heq]
    simpa [g] using heval'
  have hfderiv (n : ℕ) (x : E) (hx : x ∈ interior (cover.piece i)) :
      HasFDerivAt (fun y => (f n).smoothMap (chart y)) (d n x) x := by
    let e := extChartAt 𝓘(ℝ, E) (cover.base i)
    have hopen : IsOpen e.target := isOpen_extChartAt_target (cover.base i)
    have hcf : ContDiffOn ℝ (∞ : ℕ∞ω) ((f n).smoothMap ∘ e.symm) e.target := by
      have h := (contMDiff_iff.mp (f n).smoothMap.contMDiff).2 (cover.base i) 0
      simpa [e, extChartAt, chartAt_self_eq] using h
    have hzpiece : x ∈ cover.piece i := interior_subset hx
    have hAt : ContDiffAt ℝ (∞ : ℕ∞ω) ((f n).smoothMap ∘ e.symm) x :=
      hcf.contDiffAt (hopen.mem_nhds (cover.piece_in_target i hzpiece))
    have hd : d n x = fderiv ℝ ((f n).smoothMap ∘ chart) x := by
      simp only [d, dif_pos hzpiece]
      change continuousMultilinearCurryFin1 ℝ E ℝ
          (smoothChartHolderJetCanonicalExtension cover 2 α N 1 (by norm_num)
            (f n : LittleHolder cover 2 α N) i ⟨x, hzpiece⟩) = _
      rw [smoothChartHolderJetCanonicalExtension_coe]
      change continuousMultilinearCurryFin1 ℝ E ℝ
          (iteratedFDeriv ℝ 1 ((f n).smoothMap ∘ chart) x) = _
      apply ContinuousLinearMap.ext
      intro v
      simp [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
    have hderiv := (hAt.differentiableAt (by simp)).hasFDerivAt
    change HasFDerivAt ((f n).smoothMap ∘ chart) (d n x) x
    rw [hd]
    simpa [chart, e] using hderiv
  have hHas : HasFDerivAt g (g' z) z :=
    hasFDerivAt_of_tendstoUniformlyOn isOpen_interior hderivUniform hfderiv hfg hz
  simpa only [g, g', dif_pos (interior_subset hz), value, jets, chart,
    Function.comp_def] using hHas

/-- First derivative identification on the interior of a chart piece. Its proof uses the
uniform limit of smooth-core first jets and the line-segment FTC. This statement is conditional only
on the supplied normed data, so it also covers exponent zero. -/
private theorem smoothChartHolderCompletedJetIdentity_orderOne
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover 2 α)
    (u : LittleHolder cover 2 α N) (i) (z : E)
    (hz : z ∈ interior (cover.piece i)) :
    iteratedFDeriv ℝ 1
      ((smoothChartHolderContinuousMapExtension cover 2 α N u : M → ℝ) ∘
        (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z =
      smoothChartHolderJetCanonicalExtension cover 2 α N 1
        (by norm_num) u i ⟨z, interior_subset hz⟩ := by
  apply (continuousMultilinearCurryFin1 ℝ E ℝ).injective
  calc
    continuousMultilinearCurryFin1 ℝ E ℝ
        (iteratedFDeriv ℝ 1
          ((smoothChartHolderContinuousMapExtension cover 2 α N u : M → ℝ) ∘
            (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z) =
        fderiv ℝ
          ((smoothChartHolderContinuousMapExtension cover 2 α N u : M → ℝ) ∘
            (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z := by
      apply ContinuousLinearMap.ext
      intro v
      simp [iteratedFDeriv_one_apply]
    _ = _ := (smoothChartHolderCompletedHasFDerivAt cover α N u i z hz).fderiv

/-- Genuine derivative of the first derivative of completed evaluation on the open chart-piece
interior. Apply the same uniform derivative-limit theorem to the first-jet extensions, then use
first-derivative identification throughout an open neighborhood. With the existing `curryRight`
convention the resulting map sends `v`, then `w`, to the second jet at `![v, w]`. -/
public theorem smoothChartHolderCompletedFDerivHasFDerivAt
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover 2 α)
    (u : LittleHolder cover 2 α N) (i) (z : E)
    (hz : z ∈ interior (cover.piece i)) :
    HasFDerivAt (fderiv ℝ
      ((smoothChartHolderContinuousMapExtension cover 2 α N u : M → ℝ) ∘
        (extChartAt 𝓘(ℝ, E) (cover.base i)).symm))
      (continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] ℝ)
        ((smoothChartHolderJetCanonicalExtension cover 2 α N 2
          (Nat.le_refl 2) u i ⟨z, interior_subset hz⟩).curryRight)) z := by
  classical
  letI : NormedAddCommGroup (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedAddCommGroup cover 2 α N
  letI : NormedSpace ℝ (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedSpace cover 2 α N
  have hdense (n : ℕ) : ∃ f : SmoothChartHolderCore cover 2 α,
      dist (f : LittleHolder cover 2 α N) u < 1 / ((n : ℝ) + 1) := by
    have hcl := (Metric.mem_closure_iff.mp
      (UniformSpace.Completion.denseRange_coe u))
      (1 / ((n : ℝ) + 1)) (by positivity)
    rcases hcl with ⟨v, hv, hdist⟩
    rcases hv with ⟨f, rfl⟩
    exact ⟨f, by simpa [dist_comm] using hdist⟩
  choose f hf using hdense
  have hfseq : Tendsto (fun n => (f n : LittleHolder cover 2 α N)) atTop (𝓝 u) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    obtain ⟨Nε, hNε⟩ := exists_nat_gt (1 / ε)
    refine ⟨Nε, ?_⟩
    intro n hn
    have hlt : 1 / ((n : ℝ) + 1) < ε := by
      have hn' : (Nε : ℝ) ≤ n := by exact_mod_cast hn
      have hNε' : (1 / ε) < (Nε : ℝ) := by exact_mod_cast hNε
      have hdiv : (1 / ε) < (n : ℝ) + 1 := by linarith
      have hmul' : (1 : ℝ) < ((n : ℝ) + 1) * ε := (div_lt_iff₀ hε).mp hdiv
      have hmul : (1 : ℝ) < ε * ((n : ℝ) + 1) := by nlinarith [hmul']
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    exact (hf n).trans hlt
  let jet₁ := smoothChartHolderJetCanonicalExtension cover 2 α N 1 (by norm_num)
  let jet₂ := smoothChartHolderJetCanonicalExtension cover 2 α N 2 (Nat.le_refl 2)
  let chart := (extChartAt 𝓘(ℝ, E) (cover.base i)).symm
  let q : E → E →L[ℝ] ℝ := fun x =>
    if hx : x ∈ cover.piece i then
      continuousMultilinearCurryFin1 ℝ E ℝ (jet₁ u i ⟨x, hx⟩)
    else 0
  let r : ℕ → E → E →L[ℝ] (E →L[ℝ] ℝ) := fun n x =>
    if hx : x ∈ cover.piece i then
      continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] ℝ)
        ((jet₂ (f n : LittleHolder cover 2 α N) i ⟨x, hx⟩).curryRight)
    else 0
  let rlim : E → E →L[ℝ] (E →L[ℝ] ℝ) := fun x =>
    if hx : x ∈ cover.piece i then
      continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] ℝ)
        ((jet₂ u i ⟨x, hx⟩).curryRight)
    else 0
  let qn : ℕ → E → E →L[ℝ] ℝ := fun n x =>
    fderiv ℝ ((f n).smoothMap ∘ chart) x
  have hjets₁ : Tendsto (fun n => jet₁ (f n : LittleHolder cover 2 α N))
      atTop (𝓝 (jet₁ u)) := (jet₁.continuous.tendsto u).comp hfseq
  have hjets₂ : Tendsto (fun n => jet₂ (f n : LittleHolder cover 2 α N))
      atTop (𝓝 (jet₂ u)) := (jet₂.continuous.tendsto u).comp hfseq
  have hjets₁i : Tendsto (fun n => (jet₁ (f n : LittleHolder cover 2 α N)) i)
      atTop (𝓝 ((jet₁ u) i)) := (continuous_apply i).tendsto _ |>.comp hjets₁
  have hjets₂i : Tendsto (fun n => (jet₂ (f n : LittleHolder cover 2 α N)) i)
      atTop (𝓝 ((jet₂ u) i)) := (continuous_apply i).tendsto _ |>.comp hjets₂
  have hjets₂Uniform : TendstoUniformly
      (fun n p => (jet₂ (f n : LittleHolder cover 2 α N)) i p)
      ((jet₂ u) i) atTop := ContinuousMap.tendsto_iff_tendstoUniformly.mp hjets₂i
  have hrUniform : TendstoUniformlyOn r rlim atTop (interior (cover.piece i)) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    rw [Metric.tendstoUniformly_iff] at hjets₂Uniform
    filter_upwards [hjets₂Uniform ε hε] with n hn
    intro x hx
    have hxpiece : x ∈ cover.piece i := interior_subset hx
    have hdist : dist (r n x) (rlim x) =
        dist ((jet₂ (f n : LittleHolder cover 2 α N) i ⟨x, hxpiece⟩))
          ((jet₂ u i ⟨x, hxpiece⟩)) := by
      simp only [r, rlim, dif_pos hxpiece]
      change dist
          (continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] ℝ)
            ((jet₂ (f n : LittleHolder cover 2 α N) i ⟨x, hxpiece⟩).curryRight))
          (continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] ℝ)
            ((jet₂ u i ⟨x, hxpiece⟩).curryRight)) = _
      simp only [dist_eq_norm]
      rw [← (continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] ℝ)).map_sub]
      rw [(continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] ℝ)).norm_map]
      change ‖(continuousMultilinearCurryRightEquiv' ℝ 1 E ℝ
          (jet₂ (f n : LittleHolder cover 2 α N) i ⟨x, hxpiece⟩)) -
        (continuousMultilinearCurryRightEquiv' ℝ 1 E ℝ (jet₂ u i ⟨x, hxpiece⟩))‖ = _
      rw [← (continuousMultilinearCurryRightEquiv' ℝ 1 E ℝ).map_sub]
      exact (continuousMultilinearCurryRightEquiv' ℝ 1 E ℝ).norm_map _
    calc
      dist (rlim x) (r n x) = dist (r n x) (rlim x) := dist_comm _ _
      _ = dist ((jet₂ (f n : LittleHolder cover 2 α N) i ⟨x, hxpiece⟩))
          ((jet₂ u i ⟨x, hxpiece⟩)) := hdist
      _ = dist ((jet₂ u i ⟨x, hxpiece⟩))
          ((jet₂ (f n : LittleHolder cover 2 α N) i ⟨x, hxpiece⟩)) := dist_comm _ _
      _ < ε := hn ⟨x, hxpiece⟩
  have hcore₁ (n : ℕ) (x : E) (hx : x ∈ cover.piece i) :
      qn n x = continuousMultilinearCurryFin1 ℝ E ℝ
        (jet₁ (f n : LittleHolder cover 2 α N) i ⟨x, hx⟩) := by
    change fderiv ℝ ((f n).smoothMap ∘ chart) x = _
    change _ = continuousMultilinearCurryFin1 ℝ E ℝ
      (smoothChartHolderJetCanonicalExtension cover 2 α N 1 (by norm_num)
        (f n : LittleHolder cover 2 α N) i ⟨x, hx⟩)
    rw [smoothChartHolderJetCanonicalExtension_coe]
    apply ContinuousLinearMap.ext
    intro v
    simp [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply,
      smoothChartHolderJetData, chart]
  have hfg : ∀ x : E, x ∈ interior (cover.piece i) →
      Tendsto (fun n => qn n x) atTop (𝓝 (q x)) := by
    intro x hx
    have hp := ((ContinuousMap.evalCLM (R := ℝ) (⟨x, interior_subset hx⟩ : cover.piece i)).continuous.tendsto
      ((jet₁ u) i)).comp hjets₁i
    have hp' : Tendsto
        (fun n => continuousMultilinearCurryFin1 ℝ E ℝ
          ((jet₁ (f n : LittleHolder cover 2 α N)) i ⟨x, interior_subset hx⟩))
        atTop (𝓝 (continuousMultilinearCurryFin1 ℝ E ℝ
          ((jet₁ u) i ⟨x, interior_subset hx⟩))) :=
      ((continuousMultilinearCurryFin1 ℝ E ℝ).continuous.tendsto _).comp hp
    have hleft : (fun n => qn n x) = fun n =>
        continuousMultilinearCurryFin1 ℝ E ℝ
          ((jet₁ (f n : LittleHolder cover 2 α N)) i ⟨x, interior_subset hx⟩) :=
      funext fun n => hcore₁ n x (interior_subset hx)
    rw [hleft]
    simpa [q, interior_subset hx] using hp'
  have hcore₂ (n : ℕ) (x : E) (hx : x ∈ cover.piece i) :
      r n x = fderiv ℝ (fderiv ℝ ((f n).smoothMap ∘ chart)) x := by
    simp only [r, dif_pos hx]
    change continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] ℝ)
        ((smoothChartHolderJetCanonicalExtension cover 2 α N 2 (Nat.le_refl 2)
          (f n : LittleHolder cover 2 α N) i ⟨x, hx⟩).curryRight) = _
    rw [smoothChartHolderJetCanonicalExtension_coe]
    change continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] ℝ)
        ((iteratedFDeriv ℝ 2 ((f n).smoothMap ∘ chart) x).curryRight) = _
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    simp [continuousMultilinearCurryFin1_apply,
      ContinuousMultilinearMap.curryRight_apply, iteratedFDeriv_two_apply]
  have hfderiv (n : ℕ) (x : E) (hx : x ∈ interior (cover.piece i)) :
      HasFDerivAt (qn n) (r n x) x := by
    let F : E → ℝ := (f n).smoothMap ∘ chart
    let e := extChartAt 𝓘(ℝ, E) (cover.base i)
    have hopen : IsOpen e.target := isOpen_extChartAt_target (cover.base i)
    have hcf : ContDiffOn ℝ (∞ : ℕ∞ω) ((f n).smoothMap ∘ e.symm) e.target := by
      have h := (contMDiff_iff.mp (f n).smoothMap.contMDiff).2 (cover.base i) 0
      simpa [e, extChartAt, chartAt_self_eq] using h
    have hxpiece : x ∈ cover.piece i := interior_subset hx
    have htarget : x ∈ e.target := by simpa [e] using cover.piece_in_target i hxpiece
    have hAt : ContDiffAt ℝ (∞ : ℕ∞ω) F x :=
      hcf.contDiffAt (hopen.mem_nhds htarget)
    have hAt' : ContDiffAt ℝ (1 : ℕ∞ω) (fderiv ℝ F) x :=
      hAt.fderiv_right (m := 1) (by
        change ((1 + 1 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
        exact WithTop.coe_le_coe.mpr ((WithTop.coe_lt_top (2 : ℕ)).le))
    have hderiv :=
      (hAt'.differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)).hasFDerivAt
    have hD : r n x = fderiv ℝ (fderiv ℝ F) x := by
      simpa [F] using hcore₂ n x hxpiece
    change HasFDerivAt (fun y => fderiv ℝ F y) (r n x) x
    rw [hD]
    simpa [F] using hderiv
  have hHas : HasFDerivAt q (rlim z) z :=
    hasFDerivAt_of_tendstoUniformlyOn isOpen_interior hrUniform hfderiv hfg hz
  let value := smoothChartHolderContinuousMapExtension cover 2 α N
  let F₀ : E → ℝ := fun x => value u (chart x)
  have hfirst (x : E) (hx : x ∈ interior (cover.piece i)) :
      fderiv ℝ F₀ x = continuousMultilinearCurryFin1 ℝ E ℝ
        (jet₁ u i ⟨x, interior_subset hx⟩) := by
    have h := smoothChartHolderCompletedJetIdentity_orderOne cover α N u i x hx
    have hCurry : continuousMultilinearCurryFin1 ℝ E ℝ
        (iteratedFDeriv ℝ 1 F₀ x) = fderiv ℝ F₀ x := by
      apply ContinuousLinearMap.ext
      intro v
      simp [F₀, chart, iteratedFDeriv_one_apply]
    rw [← hCurry]
    have h' : iteratedFDeriv ℝ 1 F₀ x =
        jet₁ u i ⟨x, interior_subset hx⟩ := by
      change iteratedFDeriv ℝ 1
        ((smoothChartHolderContinuousMapExtension cover 2 α N u : M → ℝ) ∘
          (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) x = _
      exact h
    exact congrArg (continuousMultilinearCurryFin1 ℝ E ℝ) h'
  have hqeq (x : E) (hx : x ∈ interior (cover.piece i)) : q x = fderiv ℝ F₀ x := by
    simpa [q, interior_subset hx] using (hfirst x hx).symm
  have hlocal : (fun x => fderiv ℝ F₀ x) =ᶠ[𝓝 z] q := by
    filter_upwards [isOpen_interior.mem_nhds hz] with x hx
    exact (hqeq x hx).symm
  have hFderiv := hHas.congr_of_eventuallyEq hlocal
  simpa only [F₀, value, chart, jet₂, rlim, dif_pos (interior_subset hz),
    Function.comp_def] using hFderiv

/-- Second derivative identification on the interior of a chart piece. It follows by applying the
uniform derivative-limit argument to the first-jet extensions, again without restricting the
exponent or assuming normed data exists at any additional exponent. -/
private theorem smoothChartHolderCompletedJetIdentity_orderTwo
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover 2 α)
    (u : LittleHolder cover 2 α N) (i) (z : E)
    (hz : z ∈ interior (cover.piece i)) :
    iteratedFDeriv ℝ 2
      ((smoothChartHolderContinuousMapExtension cover 2 α N u : M → ℝ) ∘
        (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z =
      smoothChartHolderJetCanonicalExtension cover 2 α N 2
        (Nat.le_refl 2) u i ⟨z, interior_subset hz⟩ := by
  have hFderiv := smoothChartHolderCompletedFDerivHasFDerivAt cover α N u i z hz
  apply ContinuousMultilinearMap.ext
  intro m
  have hpoint := congrArg (fun A : E →L[ℝ] E →L[ℝ] ℝ => A (m 0) (m 1)) hFderiv.fderiv
  have hm : (![m 0, m 1] : Fin 2 → E) = m := by
    ext j
    fin_cases j <;> simp
  simpa [hm, continuousMultilinearCurryFin1_apply,
    ContinuousMultilinearMap.curryRight_apply, iteratedFDeriv_two_apply] using hpoint

/-- Every chart-coordinate derivative through order two of the completed evaluation is its
canonical completed chart jet, for arbitrary exponent and supplied normed data. -/
theorem smoothChartHolderCompletedJetIdentity
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover 2 α)
    (u : LittleHolder cover 2 α N)
    (j : ℕ) (hj : j ≤ 2) (i) (z : E)
    (hz : z ∈ interior (cover.piece i)) :
    iteratedFDeriv ℝ j
      ((smoothChartHolderContinuousMapExtension cover 2 α N u : M → ℝ) ∘
        (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z =
      smoothChartHolderJetCanonicalExtension cover 2 α N j hj u i
        ⟨z, interior_subset hz⟩ := by
  classical
  by_cases hj0 : j = 0
  · subst j
    letI : NormedAddCommGroup (SmoothChartHolderCore cover 2 α) :=
      smoothChartHolderCoreNormedAddCommGroup cover 2 α N
    letI : NormedSpace ℝ (SmoothChartHolderCore cover 2 α) :=
      smoothChartHolderCoreNormedSpace cover 2 α N
    let x : M := (extChartAt 𝓘(ℝ, E) (cover.base i)).symm z
    let p : cover.piece i := ⟨z, interior_subset hz⟩
    let F : LittleHolder cover 2 α N → E [×0]→L[ℝ] ℝ := fun v =>
      ContinuousMultilinearMap.uncurry0 ℝ E
        ((smoothChartHolderContinuousMapExtension cover 2 α N v : C(M, ℝ)) x)
    let G : LittleHolder cover 2 α N → E [×0]→L[ℝ] ℝ := fun v =>
      smoothChartHolderJetCanonicalExtension cover 2 α N 0 (Nat.zero_le 2) v i p
    have hG : Continuous G := by
      change Continuous ((fun q : SmoothChartHolderJetTarget cover 0 => q i p) ∘
        smoothChartHolderJetCanonicalExtension cover 2 α N 0 (Nat.zero_le 2))
      fun_prop
    have hF : Continuous F := by
      change Continuous (ContinuousMultilinearMap.uncurry0 ℝ E ∘
        fun v : LittleHolder cover 2 α N =>
          (smoothChartHolderContinuousMapExtension cover 2 α N v : C(M, ℝ)) x)
      exact (continuousMultilinearCurryFin0 ℝ E ℝ).symm.continuous.comp (by continuity)
    have hclosed : IsClosed {v : LittleHolder cover 2 α N | F v = G v} :=
      isClosed_eq hF hG
    have hFG : F u = G u := by
      refine UniformSpace.Completion.induction_on (a := u)
        (p := fun v => F v = G v) hclosed ?_
      intro f
      change ContinuousMultilinearMap.uncurry0 ℝ E
          ((smoothChartHolderContinuousMapExtension cover 2 α N (f : LittleHolder cover 2 α N) : C(M, ℝ)) x) =
        smoothChartHolderJetCanonicalExtension cover 2 α N 0 (Nat.zero_le 2)
          (f : LittleHolder cover 2 α N) i p
      rw [smoothChartHolderContinuousMapExtension_coe,
        smoothChartHolderJetCanonicalExtension_coe]
      simp [x, p, smoothChartHolderContinuousMapLinearMap,
        smoothChartHolderJetData, iteratedFDeriv_zero_eq_comp]
    simpa [F, G, x, p, iteratedFDeriv_zero_eq_comp] using hFG
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    have hcases : j = 1 ∨ j = 2 := by omega
    rcases hcases with h1 | h2
    · subst j
      exact smoothChartHolderCompletedJetIdentity_orderOne cover α N u i z hz
    · subst j
      exact smoothChartHolderCompletedJetIdentity_orderTwo cover α N u i z hz

/-- The completed coordinate function is genuinely `C²` at every point in the open chart-piece
interior. The derivative witnesses hold throughout that neighborhood, and the second canonical
jet is continuous on it; identities for totalized derivative values alone would not suffice. -/
public theorem smoothChartHolderCompletedContDiffAt
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover 2 α)
    (u : LittleHolder cover 2 α N) (i) (z : E)
    (hz : z ∈ interior (cover.piece i)) :
    ContDiffAt ℝ 2
      ((smoothChartHolderContinuousMapExtension cover 2 α N u : M → ℝ) ∘
        (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) z := by
  classical
  let F : E → ℝ :=
    (smoothChartHolderContinuousMapExtension cover 2 α N u : M → ℝ) ∘
      (extChartAt 𝓘(ℝ, E) (cover.base i)).symm
  let jet₂ := smoothChartHolderJetCanonicalExtension cover 2 α N 2 (Nat.le_refl 2)
  let R : E → E →L[ℝ] (E →L[ℝ] ℝ) := fun x =>
    if hx : x ∈ cover.piece i then
      continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] ℝ)
        ((jet₂ u i ⟨x, hx⟩).curryRight)
    else 0
  have hF (y : E) (hy : y ∈ interior (cover.piece i)) :
      HasFDerivAt F (fderiv ℝ F y) y :=
    (smoothChartHolderCompletedHasFDerivAt cover α N u i y hy).differentiableAt.hasFDerivAt
  have hD (y : E) (hy : y ∈ interior (cover.piece i)) :
      HasFDerivAt (fderiv ℝ F) (R y) y := by
    simpa only [F, R, jet₂, dif_pos (interior_subset hy)] using
      smoothChartHolderCompletedFDerivHasFDerivAt cover α N u i y hy
  have hR : ContinuousOn R (interior (cover.piece i)) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hsub : Continuous (fun x : interior (cover.piece i) =>
        (⟨(x : E), interior_subset x.property⟩ : cover.piece i)) :=
      continuous_subtype_val.subtype_mk _
    have hjet := (jet₂ u i).continuous.comp hsub
    have hcur := (continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] ℝ)).continuous.comp
      ((continuousMultilinearCurryRightEquiv' ℝ 1 E ℝ).continuous.comp hjet)
    convert hcur using 1 <;> try rfl
    funext x
    simp only [Set.domRestrict, R, dif_pos (interior_subset x.property)]
    rfl
  change ContDiffAt ℝ (1 + 1 : ℕ) F z
  refine contDiffAt_succ_iff_hasFDerivAt.mpr
    ⟨fderiv ℝ F, ⟨interior (cover.piece i), isOpen_interior.mem_nhds hz, hF⟩, ?_⟩
  change ContDiffAt ℝ (0 + 1 : ℕ) (fderiv ℝ F) z
  exact contDiffAt_succ_iff_hasFDerivAt.mpr
    ⟨R, ⟨interior (cover.piece i), isOpen_interior.mem_nhds hz, hD⟩,
      contDiffAt_zero.mpr ⟨interior (cover.piece i), isOpen_interior.mem_nhds hz, hR⟩⟩

end KahlerForm
