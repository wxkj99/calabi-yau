module

public import CalabiYau.MongeAmpere.Continuity.Openness.HolderSpaces
public import CalabiYau.MongeAmpere.Continuity.Openness.C2Approximation.Smoothing.Localization
public import CalabiYau.MongeAmpere.Continuity.Openness.C2Approximation.Smoothing.EuclideanMollification
public import CalabiYau.MongeAmpere.Continuity.Openness.C2Approximation.Smoothing.Patching

/-!
# Chartwise C² smoothing of potentials

The analytic density statement is treated independently of positivity and the conversion to the
`HolderBoundOn` condition used in mass normalization.  The convergence below is uniform
convergence of every real coordinate jet through order two on each compact chart piece; it is not
merely uniform convergence of function values.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [T2Space M] [CompactSpace M]

/-- Smooth functions converging to `φ` with all coordinate derivatives through order two, uniformly
on one fixed finite relatively compact chart cover. -/
structure ChartwiseC2SmoothingData (φ : M → ℝ) where
  cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M
  approximation : ℕ → M → ℝ
  smooth : ∀ j, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (approximation j)
  jetsTendsto : ∀ ε : ℝ≥0, 0 < ε →
    ∃ N, ∀ j, N ≤ j → ∀ i, ∀ r ≤ 2, ∀ z ∈ cover.piece i,
      ‖iteratedFDeriv ℝ r
        ((approximation j - φ) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
          (cover.base i)).symm) z‖ ≤ ε

private theorem iteratedFDeriv_finset_sum_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} (s : Finset ι) (f : ι → E → ℝ) (z : E) {r : ℕ}
    (hr : r ≤ 2) {ε : ℝ} (hε : 0 ≤ ε)
    (hcont : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) z)
    (hbound : ∀ i ∈ s,
      ‖iteratedFDeriv ℝ r (f i) z‖ ≤ ε / ((s.card : ℝ) + 1)) :
    ‖iteratedFDeriv ℝ r (∑ i ∈ s, f i) z‖ ≤ ε := by
  have hsum :
      iteratedFDeriv ℝ r (fun x => ∑ i ∈ s, f i x) z =
        ∑ i ∈ s, iteratedFDeriv ℝ r (f i) z := by
    rw [iteratedFDeriv_fun_sum_apply]
    intro i hi
    exact (hcont i hi).of_le (by exact_mod_cast hr)
  have hfun : (∑ i ∈ s, f i) = fun x => ∑ i ∈ s, f i x := by
    funext x
    simp
  rw [hfun, hsum]
  calc
    ‖∑ i ∈ s, iteratedFDeriv ℝ r (f i) z‖ ≤
        ∑ i ∈ s, ‖iteratedFDeriv ℝ r (f i) z‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ s, ε / ((s.card : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hbound i hi
    _ = (s.card : ℝ) * (ε / ((s.card : ℝ) + 1)) := by simp [nsmul_eq_mul]
    _ ≤ ε := by
      have hden : 0 < (s.card : ℝ) + 1 := by positivity
      have hratio : (s.card : ℝ) / ((s.card : ℝ) + 1) ≤ 1 := by
        rw [div_le_iff₀ hden]
        nlinarith
      calc
        (s.card : ℝ) * (ε / ((s.card : ℝ) + 1)) =
            ε * ((s.card : ℝ) / ((s.card : ℝ) + 1)) := by ring
        _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hratio hε
        _ = ε := by ring

private theorem chartwise_finite_sum_jets_tendsto
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (cover : CompactChartCover E M)
    (e : ℕ → cover.ι → M → ℝ)
    (he : ∀ j i k z, z ∈ cover.piece k →
      ContDiffAt ℝ 2 (e j i ∘ (extChartAt 𝓘(ℝ, E) (cover.base k)).symm) z)
    (hsmall : ∀ ε : ℝ≥0, 0 < ε → ∀ i, ∃ N, ∀ j, N ≤ j → ∀ k, ∀ r ≤ 2,
      ∀ z ∈ cover.piece k,
        ‖iteratedFDeriv ℝ r
          ((e j i) ∘ (extChartAt 𝓘(ℝ, E) (cover.base k)).symm) z‖ ≤
            (ε : ℝ) / ((Fintype.card cover.ι : ℝ) + 1)) :
    ∀ ε : ℝ≥0, 0 < ε → ∃ N, ∀ j, N ≤ j → ∀ k, ∀ r ≤ 2,
      ∀ z ∈ cover.piece k,
        ‖iteratedFDeriv ℝ r
          ((fun x => ∑ i, e j i x) ∘
            (extChartAt 𝓘(ℝ, E) (cover.base k)).symm) z‖ ≤ ε := by
  classical
  intro ε hε
  let threshold : cover.ι → ℕ := fun i => Classical.choose (hsmall ε hε i)
  have hthreshold (i : cover.ι) :
      ∀ j, threshold i ≤ j → ∀ k, ∀ r ≤ 2, ∀ z ∈ cover.piece k,
        ‖iteratedFDeriv ℝ r
          ((e j i) ∘ (extChartAt 𝓘(ℝ, E) (cover.base k)).symm) z‖ ≤
            (ε : ℝ) / ((Fintype.card cover.ι : ℝ) + 1) :=
    Classical.choose_spec (hsmall ε hε i)
  let N : ℕ := ∑ i ∈ Finset.univ, threshold i
  have hthreshold_le (i : cover.ι) : threshold i ≤ N := by
    dsimp [N]
    exact Finset.single_le_sum (fun j hj => Nat.zero_le _) (Finset.mem_univ i)
  refine ⟨N, ?_⟩
  intro j hj k r hr z hz
  let chart := extChartAt 𝓘(ℝ, E) (cover.base k)
  let f : cover.ι → E → ℝ := fun i => e j i ∘ chart.symm
  have hcont : ∀ i ∈ Finset.univ, ContDiffAt ℝ 2 (f i) z := by
    intro i hi
    exact he j i k z hz
  have hbound : ∀ i ∈ Finset.univ,
      ‖iteratedFDeriv ℝ r (f i) z‖ ≤
        (ε : ℝ) / ((Fintype.card cover.ι : ℝ) + 1) := by
    intro i hi
    simpa [f, chart, Finset.card_univ] using
      hthreshold i j (le_trans (hthreshold_le i) hj) k r hr z hz
  have hsum := iteratedFDeriv_finset_sum_bound Finset.univ f z hr
    (by exact_mod_cast (le_of_lt hε)) hcont hbound
  have hfun : (∑ i ∈ Finset.univ, f i) =
      fun x => ∑ i ∈ Finset.univ, f i x := by
    funext x
    simp
  rw [hfun] at hsum
  simpa [f, chart, Function.comp_def] using hsum

/-- Hirsch's finite chart localization, obtained from a smooth partition of unity subordinate to
chart neighborhoods with compact closure.  This is kept separate from the Euclidean density input. -/
private theorem exists_compactChartC2Partition
    (ω₀ : KahlerForm n M)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    {φ : M → ℝ} (hφ : ω₀.IsC2Potential φ) :
    ∃ term : cover.ι → M → ℝ,
      (∀ x, (∑ i, term i x) = φ x) ∧
      (∀ i, IsCompact (tsupport (term i))) ∧
      (∀ i, tsupport (term i) ⊆
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).source) ∧
      (∀ i k z, z ∈ cover.piece k →
        ContDiffAt ℝ 2
          (term i ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base k)).symm) z) := by
  classical
  let I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
  let U : cover.ι → Set M := fun i =>
    (chartAt (EuclideanSpace ℂ (Fin n)) (cover.base i)).source ∩
      (extChartAt I (cover.base i)) ⁻¹' interior (cover.piece i)
  have hUopen (i : cover.ι) : IsOpen (U i) := by
    exact isOpen_extChartAt_preimage (I := I) (cover.base i) isOpen_interior
  have hUcover : (Set.univ : Set M) ⊆ ⋃ i, U i := by
    intro x hx
    obtain ⟨i, z, hz, hxz⟩ := cover.interior_covers x
    have hzTarget : z ∈ (extChartAt I (cover.base i)).target :=
      cover.piece_in_target i (interior_subset hz)
    have hxSource : x ∈ (chartAt (EuclideanSpace ℂ (Fin n)) (cover.base i)).source := by
      have hs : (extChartAt I (cover.base i)).source =
          (chartAt (EuclideanSpace ℂ (Fin n)) (cover.base i)).source :=
        extChartAt_source (I := I) (cover.base i)
      rw [← hs, ← hxz]
      exact (extChartAt I (cover.base i)).map_target hzTarget
    have hxCoord : extChartAt I (cover.base i) x = z := by
      rw [← hxz]
      exact (extChartAt I (cover.base i)).right_inv hzTarget
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    refine ⟨hxSource, ?_⟩
    change extChartAt I (cover.base i) x ∈ interior (cover.piece i)
    rw [hxCoord]
    exact hz
  obtain ⟨ρ, hρU⟩ : ∃ ρ : SmoothPartitionOfUnity cover.ι I M Set.univ,
      ρ.IsSubordinate U :=
    SmoothPartitionOfUnity.exists_isSubordinate (I := I) isClosed_univ U hUopen hUcover
  have hρsum (x : M) : (∑ i : cover.ι, ρ i x) = 1 := by
    exact ρ.sum_finsupport' x (Set.mem_univ x) (Finset.subset_univ _)
  refine ⟨(fun i x => ρ i x * φ x), ?_, ?_, ?_, ?_⟩
  · intro x
    calc
      (∑ i, ρ i x * φ x) = (∑ i, ρ i x) * φ x := by rw [Finset.sum_mul]
      _ = φ x := by rw [hρsum x]; simp
  · intro i
    have hsubset : tsupport (fun x => ρ i x * φ x) ⊆ tsupport (ρ i) :=
      tsupport_mul_subset_left
    exact isCompact_univ.of_isClosed_subset (isClosed_tsupport _) <|
      hsubset.trans (Set.subset_univ _)
  · intro i
    calc
      tsupport (fun x => ρ i x * φ x) ⊆ tsupport (ρ i) := tsupport_mul_subset_left
      _ ⊆ U i := hρU i
      _ ⊆ (extChartAt I (cover.base i)).source := by
        have hs : (extChartAt I (cover.base i)).source =
            (chartAt (EuclideanSpace ℂ (Fin n)) (cover.base i)).source :=
          extChartAt_source (I := I) (cover.base i)
        intro x hx
        rw [hs]
        exact hx.1
  · intro i k z hz
    let chart := extChartAt I (cover.base k)
    have hzTarget : z ∈ chart.target := cover.piece_in_target k hz
    have hopen : IsOpen chart.target := isOpen_extChartAt_target (I := I) (cover.base k)
    have hρOn : ContDiffOn ℝ ∞ ((ρ i : M → ℝ) ∘ chart.symm) chart.target := by
      have h := (contMDiff_iff.mp (ρ i).contMDiff).2 (cover.base k) 0
      simpa [chart, I, extChartAt, chartAt_self_eq] using h
    have hφOn : ContDiffOn ℝ 2 (φ ∘ chart.symm) chart.target := by
      have h := (contMDiff_iff.mp hφ.1).2 (cover.base k) 0
      simpa [chart, I, extChartAt, chartAt_self_eq] using h
    have htop : (2 : ℕ∞ω) ≤ ∞ := by
      change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top
    have hρAt : ContDiffAt ℝ 2 ((ρ i : M → ℝ) ∘ chart.symm) z :=
      (hρOn.contDiffAt (hopen.mem_nhds hzTarget)).of_le htop
    have hφAt : ContDiffAt ℝ 2 (φ ∘ chart.symm) z := hφOn.contDiffAt (hopen.mem_nhds hzTarget)
    change ContDiffAt ℝ 2
      (((ρ i : M → ℝ) ∘ chart.symm) * (φ ∘ chart.symm)) z
    exact hρAt.mul hφAt

omit [T2Space M] [CompactSpace M] in
private theorem contDiffAt_chart_of_contMDiff
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f)
    (k : cover.ι) {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ cover.piece k) :
    ContDiffAt ℝ 2
      (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base k)).symm) z := by
  let chart := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base k)
  have hzTarget : z ∈ chart.target := cover.piece_in_target k hz
  have hopen : IsOpen chart.target := isOpen_extChartAt_target
    (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (cover.base k)
  have hOn : ContDiffOn ℝ ∞ (f ∘ chart.symm) chart.target := by
    have h := (contMDiff_iff.mp hf).2 (cover.base k) 0
    simpa [chart, extChartAt, chartAt_self_eq] using h
  have htop : (2 : ℕ∞ω) ≤ ∞ := by
    change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  exact (hOn.contDiffAt (hopen.mem_nhds hzTarget)).of_le htop

omit [T2Space M] [CompactSpace M] in
private theorem contDiffAt_chart_sub_of_contMDiff
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    {f g : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f)
    (hg : ∀ k (z : EuclideanSpace ℂ (Fin n)), z ∈ cover.piece k →
      ContDiffAt ℝ 2
        (g ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base k)).symm) z)
    (k : cover.ι) {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ cover.piece k) :
    ContDiffAt ℝ 2
      ((f - g) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base k)).symm) z := by
  have h₁ := contDiffAt_chart_of_contMDiff cover hf k hz
  have h₂ := hg k z hz
  change ContDiffAt ℝ 2
    ((f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base k)).symm) -
      (g ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base k)).symm)) z
  exact h₁.sub h₂

theorem exists_chartwiseC2Smoothing (ω₀ : KahlerForm n M) {φ : M → ℝ}
    (hφ : ω₀.IsC2Potential φ) :
    Nonempty (ChartwiseC2SmoothingData (n := n) (M := M) φ) := by
  classical
  obtain ⟨L⟩ := exists_compactChartC2Localization (n := n) (M := M) (φ := φ) hφ.1
  have A : ∀ i, EuclideanC2MollificationData
      (EuclideanSpace ℂ (Fin n)) (L.localFunction i)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)).target := by
    intro i
    exact Classical.choice <| exists_euclideanC2MollificationData
      (E := EuclideanSpace ℂ (Fin n))
      (f := L.localFunction i)
      (U := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)).target)
      (isOpen_extChartAt_target (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
        (L.cover.base i))
      (L.localC2 i) (L.localCompactSupport i) (L.localSupportInTarget i)
  obtain ⟨B⟩ := exists_chartwiseLocalMollificationData_of_localMollifications L A
  let approximation : ℕ → M → ℝ := fun j x =>
    ∑ i ∈ Finset.univ, B.approximation i j x
  have hsmooth : ∀ j,
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (approximation j) := by
    intro j
    apply contMDiff_finsetSum
    intro i hi
    exact B.smooth i j
  refine ⟨⟨L.cover, approximation, hsmooth, ?_⟩⟩
  intro ε hε
  have hεR : 0 < (ε : ℝ) := by exact_mod_cast hε
  let δ : ℝ≥0 := ⟨(ε : ℝ) / (((Finset.univ : Finset L.cover.ι).card : ℝ) + 1), by positivity⟩
  have hδ : 0 < δ := by
    change 0 < (ε : ℝ) / (((Finset.univ : Finset L.cover.ι).card : ℝ) + 1)
    positivity
  have hδcast : (δ : ℝ) = (ε : ℝ) / (((Finset.univ : Finset L.cover.ι).card : ℝ) + 1) := rfl
  obtain ⟨N, hlocalJets⟩ := B.jetsTendsto δ hδ
  refine ⟨N, ?_⟩
  intro j hj i r hr z hz
  let chart := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)
  let localError (k : L.cover.ι) : EuclideanSpace ℂ (Fin n) → ℝ :=
    (B.approximation k j - L.localizedFunction k) ∘ chart.symm
  have hcont : ∀ k ∈ Finset.univ, ContDiffAt ℝ 2 (localError k) z := by
    intro k hk
    exact B.error_contDiffAt k j i z hz
  have hbound : ∀ k ∈ Finset.univ,
      ‖iteratedFDeriv ℝ r (localError k) z‖ ≤
        (ε : ℝ) / (((Finset.univ : Finset L.cover.ι).card : ℝ) + 1) := by
    intro k hk
    have h := hlocalJets j hj k i r hr z hz
    change ‖iteratedFDeriv ℝ r
      ((B.approximation k j - L.localizedFunction k) ∘ chart.symm) z‖ ≤ (δ : ℝ) at h
    rw [hδcast] at h
    simpa [localError, chart] using h
  have hsumBound := iteratedFDeriv_finset_sum_bound
    (s := Finset.univ) (f := localError) z hr (le_of_lt hεR) hcont hbound
  have hdecomp :
      ((approximation j - φ) ∘ chart.symm) = ∑ k ∈ Finset.univ, localError k := by
    funext y
    simp only [Function.comp_apply, approximation, Pi.sub_apply, localError, chart]
    rw [L.reconstruct (chart.symm y)]
    simp only [Finset.sum_apply, Function.comp_apply, Pi.sub_apply]
    rw [Finset.sum_sub_distrib]
  calc
    ‖iteratedFDeriv ℝ r ((approximation j - φ) ∘ chart.symm) z‖ =
        ‖iteratedFDeriv ℝ r (∑ k ∈ Finset.univ, localError k) z‖ := by rw [hdecomp]
    _ ≤ (ε : ℝ) := hsumBound

end KahlerForm
