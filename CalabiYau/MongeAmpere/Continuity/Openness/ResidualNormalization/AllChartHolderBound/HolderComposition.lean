module

public import CalabiYau.MongeAmpere.Continuity.Openness.HolderSpaces

/-!
# Local Hölder transfer through chart transitions

At each point of an arbitrary chart, a selected finite-cover chart gives a smooth transition on a
neighborhood.  Composition estimates through order two, followed by shrinking to a compact
neighborhood, transfer the finite-cover Hölder estimate locally.  The global C² assumption is kept
explicit because `HolderBoundOn` does not imply differentiability.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology

namespace KahlerForm

/-- A smooth derivative is Hölder on a compact subset of its open regularity domain.  The
Lipschitz estimate comes from local differentiability and compactness; the exponent is then lowered
using the finite diameter of the compact set. -/
private theorem exists_holderOnWith_and_bound_iteratedFDeriv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K U : Set E} {f : E → F} {α : ℝ≥0} {k : ℕ}
    (hα : α ≤ 1) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : ContDiffOn ℝ (k + 1) f U) :
    ∃ C B : ℝ≥0, HolderOnWith C α (iteratedFDeriv ℝ k f) K ∧
      ∀ x ∈ K, ‖iteratedFDeriv ℝ k f x‖ ≤ B := by
  have hcont : ContinuousOn (iteratedFDeriv ℝ k f) U := by
    intro x hx
    exact (hf.contDiffAt (hU.mem_nhds hx)).continuousAt_iteratedFDeriv
      (by exact_mod_cast (Nat.le_add_right k 1)) |>.continuousWithinAt
  have hnorm : ContinuousOn (fun x ↦ ‖iteratedFDeriv ℝ k f x‖) K :=
    (hcont.mono hKU).norm
  obtain ⟨B, hB₀, hB⟩ := hK.bddAbove_image hnorm |>.exists_ge 0
  let Bn : ℝ≥0 := ⟨B, hB₀⟩
  have hbound (x : E) (hx : x ∈ K) : ‖iteratedFDeriv ℝ k f x‖ ≤ (Bn : ℝ) := by
    exact_mod_cast hB (‖iteratedFDeriv ℝ k f x‖) ⟨x, hx, rfl⟩
  have hLoc : LocallyLipschitzOn K (iteratedFDeriv ℝ k f) := by
    intro x hx
    have hxU : x ∈ U := hKU hx
    have hAt : ContDiffAt ℝ (k + 1) f x := hf.contDiffAt (hU.mem_nhds hxU)
    have hDer : ContDiffAt ℝ 1 (iteratedFDeriv ℝ k f) x := by
      exact hAt.iteratedFDeriv_right
        (by exact_mod_cast (show (1 : ℕ) + k ≤ k + 1 by omega))
    obtain ⟨L, t, ht, hLip⟩ := hDer.exists_lipschitzOnWith
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp ht
    refine ⟨L, Metric.ball x δ ∩ K,
      Metric.mem_nhdsWithin_iff.mpr ⟨δ, hδ, ?_⟩, ?_⟩
    · intro y hy
      exact ⟨hy.1, hy.2⟩
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
  refine ⟨L * D ^ ((1 : ℝ) - (α : ℝ)), Bn, ?_, hbound⟩
  exact hLip.holderOnWith.of_le hdist hα

/-- A function differentiable on an open neighborhood of a compact set is Lipschitz on that set. -/
private theorem exists_lipschitzOnWith_of_contDiffOn_compact
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K U : Set E} {f : E → F}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) : ∃ L : ℝ≥0, LipschitzOnWith L f K := by
  have hLoc : LocallyLipschitzOn K f := by
    intro x hx
    have hAt : ContDiffAt ℝ 1 f x := hf.contDiffAt (hU.mem_nhds (hKU hx))
    obtain ⟨L, t, ht, hLip⟩ := hAt.exists_lipschitzOnWith
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp ht
    refine ⟨L, Metric.ball x δ ∩ K,
      Metric.mem_nhdsWithin_iff.mpr ⟨δ, hδ, ?_⟩, ?_⟩
    · intro y hy
      exact ⟨hy.1, hy.2⟩
    · apply hLip.mono
      intro y hy
      exact hball hy.1
  exact LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK hLoc

/-- Hölder control of the Taylor coefficients of two maps yields Hölder control of the second
Taylor coefficient of their composition.  The estimate is packaged over `K × K`, so it applies to
arbitrary compact sets, not just convex chart domains. -/
private theorem holderOnWith_taylorComp_two
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {K : Set E} {α : ℝ≥0} {p : E → FormalMultilinearSeries ℝ F G}
    {q : E → FormalMultilinearSeries ℝ E F}
    (hp : ∀ k ≤ 2, ∃ C : ℝ≥0, HolderOnWith C α (fun x ↦ p x k) K)
    (hq : ∀ k ≤ 2, ∃ C : ℝ≥0, HolderOnWith C α (fun x ↦ q x k) K)
    (hpb : ∀ k ≤ 2, ∃ B : ℝ≥0, ∀ x ∈ K, ‖p x k‖ ≤ B)
    (hqb : ∀ k ≤ 2, ∃ B : ℝ≥0, ∀ x ∈ K, ‖q x k‖ ≤ B) :
    ∃ C : ℝ≥0, HolderOnWith C α (fun x ↦ (p x).taylorComp (q x) 2) K := by
  let l : Filter (E × E) := Filter.principal (K ×ˢ K)
  let d : E × E → ℝ := fun a ↦ Real.rpow (dist a.1 a.2) (α : ℝ)
  have hpbdd : ∀ k ≤ 2, l.IsBoundedUnder (· ≤ ·) (fun a ↦ ‖p a.1 k‖) := by
    intro k hk
    obtain ⟨B, hB⟩ := hpb k hk
    apply Filter.isBoundedUnder_of_eventually_le
    rw [Filter.eventually_principal]
    intro a ha
    exact hB a.1 ha.1
  have hq1bdd : ∀ k ≤ 2, l.IsBoundedUnder (· ≤ ·) (fun a ↦ ‖q a.1 k‖) := by
    intro k hk
    obtain ⟨B, hB⟩ := hqb k hk
    apply Filter.isBoundedUnder_of_eventually_le
    rw [Filter.eventually_principal]
    intro a ha
    exact hB a.1 ha.1
  have hq2bdd : ∀ k ≤ 2, l.IsBoundedUnder (· ≤ ·) (fun a ↦ ‖q a.2 k‖) := by
    intro k hk
    obtain ⟨B, hB⟩ := hqb k hk
    apply Filter.isBoundedUnder_of_eventually_le
    rw [Filter.eventually_principal]
    intro a ha
    exact hB a.2 ha.2
  have hpf : ∀ k ≤ 2, (fun a : E × E ↦ p a.1 k - p a.2 k) =O[l] d := by
    intro k hk
    obtain ⟨C, hC⟩ := hp k hk
    rw [Asymptotics.isBigO_iff]
    refine ⟨(C : ℝ), ?_⟩
    rw [Filter.eventually_principal]
    intro a ha
    have h := hC.dist_le ha.1 ha.2
    rw [dist_eq_norm] at h
    change ‖p a.1 k - p a.2 k‖ ≤ (C : ℝ) * ‖d a‖
    simpa [d, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (dist_nonneg) _)] using h
  have hqf : ∀ k ≤ 2, (fun a : E × E ↦ q a.1 k - q a.2 k) =O[l] d := by
    intro k hk
    obtain ⟨C, hC⟩ := hq k hk
    rw [Asymptotics.isBigO_iff]
    refine ⟨(C : ℝ), ?_⟩
    rw [Filter.eventually_principal]
    intro a ha
    have h := hC.dist_le ha.1 ha.2
    rw [dist_eq_norm] at h
    change ‖q a.1 k - q a.2 k‖ ≤ (C : ℝ) * ‖d a‖
    simpa [d, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (dist_nonneg) _)] using h
  have hcomp := FormalMultilinearSeries.taylorComp_sub_taylorComp_isBigO
    hpbdd hpf hq1bdd hq2bdd hqf
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hcomp
  let C' : ℝ≥0 := ⟨max 0 C, le_max_left 0 C⟩
  refine ⟨C', ?_⟩
  intro x hx y hy
  have h := (Filter.eventually_principal.mp hC) (x, y) ⟨hx, hy⟩
  have h' : ‖(p x).taylorComp (q x) 2 - (p y).taylorComp (q y) 2‖ ≤
      C * Real.rpow (dist x y) (α : ℝ) := by
    simpa [d, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (dist_nonneg) _)] using h
  have hC' : C ≤ (C' : ℝ) := le_max_right 0 C
  have h'' := h'.trans (mul_le_mul_of_nonneg_right hC' (Real.rpow_nonneg (dist_nonneg) _))
  have hENN : ENNReal.ofReal (dist ((p x).taylorComp (q x) 2) ((p y).taylorComp (q y) 2)) ≤
      ENNReal.ofReal (C' * Real.rpow (dist x y) (α : ℝ)) := by
    apply ENNReal.ofReal_le_ofReal
    simpa only [dist_eq_norm] using h''
  change edist ((p x).taylorComp (q x) 2) ((p y).taylorComp (q y) 2) ≤
    (C' : ENNReal) * edist x y ^ (α : ℝ)
  simpa [edist_dist, ENNReal.ofReal_mul, ENNReal.ofReal_rpow_of_nonneg,
    Real.rpow_nonneg] using hENN

/-- Finite C²,α bounds compose with a smooth coordinate map on an explicit open domain.  Both
`U` and `V` are open: compactness of `K` and continuity of `τ` then give a neighborhood of `K`
whose image stays in `V`, so the ordinary chain rule applies.  Without open `V`, a cusp of `g`
centered at an isolated point of `τ '' K` is invisible to the ambient `iteratedFDeriv` junk values
on that set, while a critical point of `τ` can turn that cusp into a smooth composition with an
unbounded second derivative.  The `ContDiffOn` assumptions are stated independently of
`HolderBoundOn`, which does not imply regularity. -/
private theorem holderBoundOn_comp_contDiffOn_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {α C : ℝ≥0} {K U V : Set E} {τ : E → E} {g : E → ℝ}
    (hα : α ≤ 1) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hτ : ContDiffOn ℝ 3 τ U) (hV : IsOpen V) (hτV : τ '' K ⊆ V)
    (hg : ContDiffOn ℝ 2 g V)
    (hbound : HolderBoundOn 2 α C (τ '' K) g) :
    ∃ C' : ℝ≥0, HolderBoundOn 2 α C' K (g ∘ τ) := by
  classical
  let Kτ := τ '' K
  have hτcont : ContinuousOn τ K := hτ.continuousOn.mono hKU
  have hKτ : IsCompact Kτ := hK.image_of_continuousOn hτcont
  have hτLip : ∃ L : ℝ≥0, HolderOnWith L 1 τ K := by
    obtain ⟨L, hL⟩ := exists_lipschitzOnWith_of_contDiffOn_compact hK hU hKU
      (hτ.of_le (by norm_num))
    exact ⟨L, hL.holderOnWith⟩
  obtain ⟨Lτ, hτHolder1⟩ := hτLip
  let p : E → FormalMultilinearSeries ℝ E ℝ := fun y ↦ ftaylorSeries ℝ g (τ y)
  let q : E → FormalMultilinearSeries ℝ E E := fun y ↦ ftaylorSeries ℝ τ y
  have hqData : ∀ k ≤ 2, ∃ Ck Bk : ℝ≥0,
      HolderOnWith Ck α (fun y ↦ iteratedFDeriv ℝ k τ y) K ∧
      ∀ y ∈ K, ‖iteratedFDeriv ℝ k τ y‖ ≤ Bk := by
    intro k hk
    exact exists_holderOnWith_and_bound_iteratedFDeriv hα hK hU hKU
      (hτ.of_le (by exact_mod_cast (show k + 1 ≤ 3 by omega)))
  have hp : ∀ k ≤ 2, ∃ Ck : ℝ≥0,
      HolderOnWith Ck α (fun y ↦ p y k) K := by
    intro k hk
    by_cases hk2 : k = 2
    · subst k
      refine ⟨C * Lτ ^ (α : ℝ), ?_⟩
      have h := hbound.2.comp hτHolder1 (by
        intro y hy
        exact ⟨y, hy, rfl⟩)
      simpa [p, ftaylorSeries, Function.comp_def, mul_one] using h
    · have hk1 : k + 1 ≤ 2 := by omega
      obtain ⟨Ck, _, hG, _⟩ := exists_holderOnWith_and_bound_iteratedFDeriv hα hKτ hV
        (by simpa [Kτ] using hτV)
        (hg.of_le (by exact_mod_cast hk1))
      refine ⟨Ck * Lτ ^ (α : ℝ), ?_⟩
      have h := hG.comp hτHolder1 (by
        intro y hy
        exact ⟨y, hy, rfl⟩)
      simpa [p, ftaylorSeries, Function.comp_def, mul_one] using h
  have hq : ∀ k ≤ 2, ∃ Ck : ℝ≥0,
      HolderOnWith Ck α (fun y ↦ q y k) K := by
    intro k hk
    obtain ⟨Ck, _, hQ, _⟩ := hqData k hk
    exact ⟨Ck, by simpa [q, ftaylorSeries] using hQ⟩
  have hpb : ∀ k ≤ 2, ∃ Bk : ℝ≥0, ∀ y ∈ K, ‖p y k‖ ≤ Bk := by
    intro k hk
    refine ⟨C, ?_⟩
    intro y hy
    simpa [p, ftaylorSeries] using hbound.1 k hk (τ y) ⟨y, hy, rfl⟩
  have hqb : ∀ k ≤ 2, ∃ Bk : ℝ≥0, ∀ y ∈ K, ‖q y k‖ ≤ Bk := by
    intro k hk
    obtain ⟨_, Bk, _, hQ⟩ := hqData k hk
    exact ⟨Bk, by simpa [q, ftaylorSeries] using hQ⟩
  obtain ⟨Ccomp, hCompTaylor⟩ := holderOnWith_taylorComp_two hp hq hpb hqb
  have hCompEq (y : E) (hy : y ∈ K) :
      iteratedFDeriv ℝ 2 (g ∘ τ) y = (p y).taylorComp (q y) 2 := by
    dsimp [p, q]
    exact iteratedFDeriv_comp
      (hg.contDiffAt (hV.mem_nhds (hτV ⟨y, hy, rfl⟩)))
      ((hτ.contDiffAt (hU.mem_nhds (hKU hy))).of_le (by norm_num)) le_rfl
  have hTaylorJet : HolderOnWith Ccomp α (iteratedFDeriv ℝ 2 (g ∘ τ)) K := by
    intro y hy z hz
    rw [hCompEq y hy, hCompEq z hz]
    exact hCompTaylor y hy z hz
  let O := U ∩ τ ⁻¹' V
  have hOopen : IsOpen O := hτ.continuousOn.isOpen_inter_preimage hU hV
  have hKO : K ⊆ O := by
    intro y hy
    exact ⟨hKU hy, hτV ⟨y, hy, rfl⟩⟩
  have hτO : Set.MapsTo τ O V := by
    intro y hy
    exact hy.2
  have hCompDiff : ContDiffOn ℝ 2 (g ∘ τ) O :=
    hg.comp ((hτ.of_le (by norm_num)).mono (by intro y hy; exact hy.1)) hτO
  have hJetBound : ∀ k ≤ 2, ∃ Bk : ℝ≥0, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ k (g ∘ τ) y‖ ≤ Bk := by
    intro k hk
    have hCont : ContinuousOn (iteratedFDeriv ℝ k (g ∘ τ)) K := by
      intro y hy
      have hAt : ContDiffAt ℝ 2 (g ∘ τ) y :=
        hCompDiff.contDiffAt (hOopen.mem_nhds (hKO hy))
      exact hAt.continuousAt_iteratedFDeriv (by exact_mod_cast hk) |>.continuousWithinAt
    have hNorm : ContinuousOn (fun y ↦ ‖iteratedFDeriv ℝ k (g ∘ τ) y‖) K := hCont.norm
    obtain ⟨B, hB₀, hB⟩ := hK.bddAbove_image hNorm |>.exists_ge 0
    refine ⟨⟨B, hB₀⟩, ?_⟩
    intro y hy
    exact_mod_cast hB (‖iteratedFDeriv ℝ k (g ∘ τ) y‖) ⟨y, hy, rfl⟩
  obtain ⟨B0, hB0⟩ := hJetBound 0 (by omega)
  obtain ⟨B1, hB1⟩ := hJetBound 1 (by omega)
  obtain ⟨B2, hB2⟩ := hJetBound 2 (by omega)
  let B := max B0 (max B1 B2)
  let C' := max Ccomp B
  have hBound : ∀ k ≤ 2, ∀ y ∈ K, ‖iteratedFDeriv ℝ k (g ∘ τ) y‖ ≤ B := by
    intro k hk y hy
    interval_cases k
    · exact (hB0 y hy).trans (by exact_mod_cast (le_max_left B0 (max B1 B2)))
    · exact (hB1 y hy).trans (by exact_mod_cast
        (le_trans (le_max_left B1 B2) (le_max_right B0 (max B1 B2))))
    · exact (hB2 y hy).trans (by exact_mod_cast
        (le_trans (le_max_right B1 B2) (le_max_right B0 (max B1 B2))))
  refine ⟨C', ?_⟩
  constructor
  · intro k hk y hy
    exact (hBound k hk y hy).trans (by exact_mod_cast (le_max_right Ccomp B))
  · exact hTaylorJet.mono_const (le_max_left _ _)

/-- Near every point of any chart target, the finite-cover C²,α estimate transfers to a compact
neighborhood in the arbitrary chart.  The selected cover chart supplies the open set `V` required
by `holderBoundOn_comp_contDiffOn_two`: its target is open by `isOpen_extChartAt_target`, and the
transition is considered on the open overlap of the two chart domains.  The C² regularity of `f` is
explicit, since `HolderBoundOn` does not carry differentiability. -/
theorem exists_compact_chartTransition_holderBoundOn_neighborhood
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {α : ℝ≥0} (cover : CompactChartCover E M) (f : M → ℝ)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) 2 f) (hα : α ≤ 1)
    (hfixed : HolderBoundedOnFiniteChartCover cover 2 α {f})
    (x : M) (z : E) (hz : z ∈ (extChartAt 𝓘(ℝ, E) x).target) :
    ∃ W : Set E, IsCompact W ∧ z ∈ interior W ∧
      W ⊆ (extChartAt 𝓘(ℝ, E) x).target ∧
      ∃ C : ℝ≥0, HolderBoundOn 2 α C W
        (f ∘ (extChartAt 𝓘(ℝ, E) x).symm) := by
  let e := extChartAt 𝓘(ℝ, E) x
  obtain ⟨i, hi⟩ := cover.interior_covers (e.symm z)
  let e' := extChartAt 𝓘(ℝ, E) (cover.base i)
  let V := e'.target
  have hV : IsOpen V := isOpen_extChartAt_target (cover.base i)
  have hi' := hi
  rw [Set.mem_image] at hi'
  rcases hi' with ⟨w, hw, hwy⟩
  have hwt : w ∈ e'.target := cover.piece_in_target i (interior_subset hw)
  have hysource : e.symm z ∈ e'.source := by
    rw [← hwy]
    exact e'.map_target hwt
  let U := e.target ∩ e.symm ⁻¹' e'.source
  have hUopen : IsOpen U := by
    change IsOpen (e.target ∩ e.symm ⁻¹' e'.source)
    exact (continuousOn_extChartAt_symm (I := 𝓘(ℝ, E)) x).isOpen_inter_preimage
      (isOpen_extChartAt_target x) (isOpen_extChartAt_source (cover.base i))
  have hzU : z ∈ U := ⟨hz, hysource⟩
  let τ := e' ∘ e.symm
  have hτMD : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ τ U := by
    have hSymm : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) (∞ : ℕ∞ω) e.symm e.target :=
      contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, E)) (n := (∞ : ℕ∞ω)) x
    have hChart : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) (∞ : ℕ∞ω) e'
        (chartAt E (cover.base i)).source :=
      contMDiffOn_extChartAt (I := 𝓘(ℝ, E)) (n := (∞ : ℕ∞ω))
        (x := cover.base i)
    change ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (e' ∘ e.symm) U
    have hSymmU : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) (∞ : ℕ∞ω) e.symm U :=
      hSymm.mono (by intro y hy; exact hy.1)
    exact hChart.comp hSymmU (by
      intro y hy
      simpa [e', extChartAt_source] using hy.2)
  have hτ : ContDiffOn ℝ 3 τ U := hτMD.contDiffOn.of_le
    (inferInstance : ENat.LEInfty (3 : ℕ∞ω)).out
  have hτz : τ z = w := by
    dsimp [τ]
    calc
      e' (e.symm z) = e' (e'.symm w) := by rw [← hwy]
      _ = w := e'.right_inv hwt
  let T := U ∩ τ ⁻¹' interior (cover.piece i)
  have hTopen : IsOpen T := hτ.continuousOn.isOpen_inter_preimage hUopen isOpen_interior
  have hzT : z ∈ T := by
    change z ∈ U ∧ τ z ∈ interior (cover.piece i)
    exact ⟨hzU, by rw [hτz]; exact hw⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hTopen.mem_nhds hzT)
  let r : ℝ := δ / 2
  have hr : 0 < r := by dsimp [r]; linarith
  let W := Metric.closedBall z r
  have hWcompact : IsCompact W := by
    dsimp [W]
    exact isCompact_closedBall z r
  have hWsubT : W ⊆ T := by
    intro y hy
    apply hball
    have hyDist : dist z y ≤ r := by
      simpa [W, Metric.mem_closedBall, dist_comm] using hy
    have hyDist' : dist y z ≤ δ / 2 := by simpa [dist_comm, r] using hyDist
    exact Metric.mem_ball.mpr (lt_of_le_of_lt hyDist' (by linarith))
  have hzInterior : z ∈ interior W := by
    have hballW : Metric.ball z r ⊆ interior W :=
      Metric.isOpen_ball.subset_interior_iff.mpr (Metric.ball_subset_closedBall)
    exact hballW (Metric.mem_ball_self hr)
  have hWtarget : W ⊆ e.target := by
    intro y hy
    exact (hWsubT hy).1.1
  have hτWpiece : τ '' W ⊆ cover.piece i := by
    rintro y ⟨y', hy', rfl⟩
    exact interior_subset (hWsubT hy').2
  have hτWV : τ '' W ⊆ V := hτWpiece.trans (cover.piece_in_target i)
  let g : E → ℝ := f ∘ e'.symm
  have hgMD : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) 2 g V := by
    dsimp [g]
    exact (contMDiffOn_univ.mpr hf).comp
      (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, E)) (cover.base i))
      (by intro y hy; simp)
  have hg : ContDiffOn ℝ 2 g V := hgMD.contDiffOn.of_le (by norm_num)
  obtain ⟨Cfix, hfix⟩ := hfixed
  have hpieceHolder : HolderBoundOn 2 α Cfix (cover.piece i) g := by
    simpa [g, e'] using hfix f (by simp) i
  have hboundW : HolderBoundOn 2 α Cfix (τ '' W) g :=
    hpieceHolder.mono_set hτWpiece
  have hKU : W ⊆ U := by
    intro y hy
    exact (hWsubT hy).1
  obtain ⟨Cres, hCompHolder⟩ := holderBoundOn_comp_contDiffOn_two
    hα hWcompact hUopen hKU hτ hV hτWV hg hboundW
  have hEqT : Set.EqOn (g ∘ τ) (f ∘ e.symm) T := by
    intro y hy
    simpa [g, τ, Function.comp_def] using congrArg f (e'.left_inv hy.1.2)
  have hJetEq (k : ℕ) (y : E) (hy : y ∈ W) :
      iteratedFDeriv ℝ k (g ∘ τ) y = iteratedFDeriv ℝ k (f ∘ e.symm) y := by
    have hyT : y ∈ T := hWsubT hy
    have hWithin := hEqT.iteratedFDerivWithin (𝕜 := ℝ) k
    have hLeft : iteratedFDerivWithin ℝ k (g ∘ τ) T y =
        iteratedFDeriv ℝ k (g ∘ τ) y :=
      iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) k hTopen hyT
    have hRight : iteratedFDerivWithin ℝ k (f ∘ e.symm) T y =
        iteratedFDeriv ℝ k (f ∘ e.symm) y :=
      iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) k hTopen hyT
    calc
      iteratedFDeriv ℝ k (g ∘ τ) y = iteratedFDerivWithin ℝ k (g ∘ τ) T y := hLeft.symm
      _ = iteratedFDerivWithin ℝ k (f ∘ e.symm) T y := hWithin hyT
      _ = iteratedFDeriv ℝ k (f ∘ e.symm) y := hRight
  refine ⟨W, hWcompact, hzInterior, hWtarget, ⟨Cres, ?_⟩⟩
  constructor
  · intro k hk y hy
    rw [← hJetEq k y hy]
    exact hCompHolder.1 k hk y hy
  · intro y hy y' hy'
    rw [← hJetEq 2 y hy, ← hJetEq 2 y' hy']
    exact hCompHolder.2 y hy y' hy'

end KahlerForm
