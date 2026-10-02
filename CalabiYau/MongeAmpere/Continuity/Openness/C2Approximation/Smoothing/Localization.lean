module

public import CalabiYau.MongeAmpere.Continuity.Openness.CompactChartCover
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Compact chart localization for C² smoothing

A finite smooth partition of unity localizes a manifold function to compactly supported C² functions
in real chart coordinates.  The reconstruction identity is the only information needed by the
subsequent Euclidean convolution and finite-sum patching steps.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [T2Space M] [CompactSpace M]

/-- Finite partition-of-unity localization data for a real C² function on a compact manifold.
Each localized term is extended by zero in one real chart and has compact support strictly inside
the chart target. -/
structure CompactChartC2Localization (φ : M → ℝ) where
  cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M
  localizedFunction : cover.ι → M → ℝ
  localizedC2 : ∀ i,
    ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 (localizedFunction i)
  localizedSupportInSource : ∀ i, tsupport (localizedFunction i) ⊆
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).source
  localFunction : cover.ι → EuclideanSpace ℂ (Fin n) → ℝ
  localC2 : ∀ i, ContDiff ℝ 2 (localFunction i)
  localCompactSupport : ∀ i, HasCompactSupport (localFunction i)
  localSupportInTarget : ∀ i, tsupport (localFunction i) ⊆
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).target
  coordinate_eq : ∀ i x,
    x ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).source →
      localizedFunction i x =
        localFunction i (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i) x)
  reconstruct : ∀ x,
    φ x = Finset.sum (@Finset.univ cover.ι cover.fintype_ι)
      (fun i => localizedFunction i x)

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M] in
private theorem chart_zero_extension_c2_of_contDiffOn
    (i : M) (g : M → ℝ)
    (hcoord : ContDiffOn ℝ 2
      (g ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target)
    (hcompact : IsCompact (tsupport g))
    (hsupport : tsupport g ⊆
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).source) :
    ∃ u : EuclideanSpace ℂ (Fin n) → ℝ,
      ContDiff ℝ 2 u ∧ HasCompactSupport u ∧
      tsupport u ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target ∧
      ∀ x ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).source,
        u ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i) x) = g x := by
  classical
  let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i
  let K : Set (EuclideanSpace ℂ (Fin n)) := c '' tsupport g
  let u : EuclideanSpace ℂ (Fin n) → ℝ := fun z => if z ∈ c.target then g (c.symm z) else 0
  have hKcompact : IsCompact K := by
    dsimp [K, c]
    exact hcompact.image_of_continuousOn
      ((continuousOn_extChartAt (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) i).mono hsupport)
  have hKtarget : K ⊆ c.target := by
    rintro z ⟨x, hx, rfl⟩
    exact c.map_source (hsupport hx)
  have hUsupport : Function.support u ⊆ K := by
    intro z hz
    change u z ≠ 0 at hz
    have hzt : z ∈ c.target := by
      by_contra h
      simp [u, h] at hz
    have hgz : g (c.symm z) ≠ 0 := by simpa [u, hzt] using hz
    have hx : c.symm z ∈ tsupport g :=
      subset_tsupport g (Function.mem_support.mpr hgz)
    refine ⟨c.symm z, hx, ?_⟩
    exact c.right_inv hzt
  have hKclosed : IsClosed K := hKcompact.isClosed
  have hUtsupport : tsupport u ⊆ K := by
    change closure (Function.support u) ⊆ K
    exact (closure_mono hUsupport).trans hKclosed.closure_subset
  have huTarget : ContDiffOn ℝ 2 u c.target := by
    have heq : Set.EqOn u (g ∘ c.symm) c.target := by
      intro z hz
      simp [u, hz]
    exact hcoord.congr heq
  have huOutside : ContDiffOn ℝ 2 u Kᶜ := by
    apply contDiffOn_const.congr
    intro z hz
    have hzero : u z = 0 := by
      dsimp [u]
      split_ifs with hzt
      · by_contra hn
        apply hz
        have hx : c.symm z ∈ tsupport g :=
          subset_tsupport g (Function.mem_support.mpr hn)
        exact ⟨c.symm z, hx, c.right_inv hzt⟩
      · rfl
    exact hzero
  have hunion : c.target ∪ Kᶜ = Set.univ := by
    ext z
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_univ, iff_true]
    by_cases hz : z ∈ c.target
    · exact Or.inl hz
    · exact Or.inr (fun hk => hz (hKtarget hk))
  have hu : ContDiff ℝ 2 u :=
    contDiff_of_contDiffOn_union_of_isOpen huTarget huOutside hunion
      (isOpen_extChartAt_target (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) i) hKclosed.isOpen_compl
  refine ⟨u, hu, ?_, hUtsupport.trans hKtarget, ?_⟩
  · exact hKcompact.of_isClosed_subset (isClosed_tsupport u) hUtsupport
  · intro x hx
    change u (c x) = g x
    have hcx : c x ∈ c.target := c.map_source hx
    simp [u, hcx, c.left_inv hx]

omit [T2Space M] [CompactSpace M] in
private theorem real_manifold_infty :
    IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ M := by
  exact isManifold_of_contDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ M fun e e' he he' ↦ by
    have h := HasGroupoid.compatible
      (G := contDiffGroupoid ω 𝓘(ℂ, EuclideanSpace ℂ (Fin n))) he he'
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at h
    exact (h.1.of_le le_top).restrict_scalars ℝ

omit [T2Space M] [CompactSpace M] in
private theorem chart_coordinate_c2 (i : M) (g : M → ℝ)
    (hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 g) :
    ContDiffOn ℝ 2 (g ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target := by
  let : IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 2 M :=
    (real_manifold_infty (n := n) (M := M)).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  simpa only [mfld_simps, chartAt_self_eq] using (contMDiff_iff.mp hg).2 i (0 : ℝ)

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M] in
private theorem product_tsupport_subset (a b : M → ℝ) :
    tsupport (fun x => a x * b x) ⊆ tsupport a := by
  apply closure_mono
  intro x hx
  change a x * b x ≠ 0 at hx
  exact Function.mem_support.mpr (fun hzero => hx (by simp only [hzero, zero_mul]))

private theorem finite_subordinate_smooth_cutoffs
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M) :
    ∃ σ : cover.ι → M → ℝ,
      (∀ i, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (σ i)) ∧
      (∀ i, tsupport (σ i) ⊆
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).source) ∧
      ∀ x, Finset.sum (@Finset.univ cover.ι cover.fintype_ι) (fun i => σ i x) = 1 := by
  classical
  let : IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ M :=
    real_manifold_infty (n := n) (M := M)
  let := cover.fintype_ι
  let U : cover.ι → Set M := fun i =>
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).source
  have hU : ∀ i, IsOpen (U i) := by
    intro i
    dsimp only [U]
    rw [extChartAt_source]
    exact (chartAt (EuclideanSpace ℂ (Fin n)) (cover.base i)).open_source
  have hcover : Set.univ ⊆ ⋃ i, U i := by
    intro x _
    obtain ⟨i, z, hz, heq⟩ := cover.interior_covers x
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    have hzt := cover.piece_in_target i (interior_subset hz)
    exact heq ▸ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).map_target hzt
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, EuclideanSpace ℂ (Fin n)) isClosed_univ U hU hcover
  refine ⟨fun i x => ρ i x, ?_, ?_, ?_⟩
  · intro i
    exact (ρ i).contMDiff
  · intro i
    exact hρ i
  · intro x
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (Set.mem_univ x)

omit [T2Space M] in
private theorem localization_of_finite_smooth_cutoffs
    {φ : M → ℝ}
    (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 φ)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (σ : cover.ι → M → ℝ)
    (hσ : ∀ i, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (σ i))
    (hsupport : ∀ i, tsupport (σ i) ⊆
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).source)
    (hsum : ∀ x, Finset.sum (@Finset.univ cover.ι cover.fintype_ι)
      (fun i => σ i x) = 1) :
    Nonempty (CompactChartC2Localization (n := n) (M := M) φ) := by
  classical
  let := cover.fintype_ι
  let g : cover.ι → M → ℝ := fun i x => σ i x * φ x
  have hg : ∀ i, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 (g i) := by
    intro i
    have hσ₂ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 (σ i) :=
      (hσ i).of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
    exact hσ₂.mul hφ
  have hgsupport : ∀ i, tsupport (g i) ⊆
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).source := by
    intro i
    exact (product_tsupport_subset (σ i) φ).trans (hsupport i)
  have hcoord : ∀ i, ContDiffOn ℝ 2
      ((g i) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).target := by
    intro i
    exact chart_coordinate_c2 (cover.base i) (g i) (hg i)
  have hext : ∀ i, ∃ u : EuclideanSpace ℂ (Fin n) → ℝ,
      ContDiff ℝ 2 u ∧ HasCompactSupport u ∧
      tsupport u ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).target ∧
      ∀ x ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).source,
        u ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)) x) = g i x := by
    intro i
    exact chart_zero_extension_c2_of_contDiffOn (cover.base i) (g i) (hcoord i)
      ((isClosed_tsupport _).isCompact) (hgsupport i)
  choose u huC2 huCompact huTarget huEq using hext
  refine ⟨{
    cover := cover
    localizedFunction := g
    localizedC2 := hg
    localizedSupportInSource := hgsupport
    localFunction := u
    localC2 := huC2
    localCompactSupport := huCompact
    localSupportInTarget := huTarget
    coordinate_eq := ?_
    reconstruct := ?_
  }⟩
  · intro i x hx
    exact (huEq i x hx).symm
  · intro x
    change φ x = ∑ i, σ i x * φ x
    rw [← Finset.sum_mul, hsum x, one_mul]

/-- A smooth finite partition of unity gives compactly supported chart-local C² summands. -/
theorem exists_compactChartC2Localization {φ : M → ℝ}
    (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 φ) :
    Nonempty (CompactChartC2Localization (n := n) (M := M) φ) := by
  classical
  obtain ⟨cover⟩ := exists_compactChartCover
    (E := EuclideanSpace ℂ (Fin n)) (M := M)
  obtain ⟨σ, hσ, hsupport, hsum⟩ := finite_subordinate_smooth_cutoffs cover
  exact localization_of_finite_smooth_cutoffs hφ cover σ hσ hsupport hsum

end KahlerForm
