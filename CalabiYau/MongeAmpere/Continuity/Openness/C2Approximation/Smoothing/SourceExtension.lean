module

public import CalabiYau.Geometry.Complex.Basic
public import CalabiYau.MongeAmpere.Continuity.Openness.C2Approximation.Smoothing.EuclideanMollification
public import CalabiYau.MongeAmpere.Continuity.Openness.C2Approximation.Smoothing.Localization

/-!
# Extension by zero of chart-local mollifications

Hirsch, *Differential Topology*, Chapter 2, §2, Theorems 2.4 and 2.6, pp. 47–49:
a convolution supported in a compact subset of its source chart extends smoothly by
zero across the chart boundary. This gives the one-chart construction;
uniform bounds in other charts belong to `TransitionJets`.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [T2Space M] [CompactSpace M]

omit [CompactSpace M] in
/-- A compactly supported smooth chart function has a globally smooth zero
extension with closed support strictly inside the source chart. -/
private theorem exists_smooth_zero_extension_of_chart_support
    (i : M) (u : EuclideanSpace ℂ (Fin n) → ℝ) (hu : ContDiff ℝ ∞ u)
    (hcompact : IsCompact (tsupport u))
    (hsupport : tsupport u ⊆
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target) :
    ∃ F : M → ℝ,
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F ∧
      tsupport F ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).source ∧
      ∀ z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target,
        F ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm z) = u z := by
  classical
  let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i
  let F : M → ℝ := fun x => if x ∈ c.source then u (c x) else 0
  let K : Set M := c.symm '' tsupport u
  have hKcompact : IsCompact K := by
    dsimp [K, c]
    exact hcompact.image_of_continuousOn
      ((continuousOn_extChartAt_symm (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) i).mono hsupport)
  have hKsource : K ⊆ c.source := by
    rintro x ⟨z, hz, rfl⟩
    exact c.map_target (hsupport hz)
  have hFsupport : Function.support F ⊆ K := by
    intro x hx
    change F x ≠ 0 at hx
    by_cases hxs : x ∈ c.source
    · have hux : u (c x) ≠ 0 := by simpa [F, hxs] using hx
      have hxSupport : c x ∈ Function.support u := Function.mem_support.mpr hux
      exact ⟨c x, subset_tsupport u hxSupport, c.left_inv hxs⟩
    · simp [F, hxs] at hx
  have hKclosed : IsClosed K := hKcompact.isClosed
  have hFtsupport : tsupport F ⊆ K := by
    change closure (Function.support F) ⊆ K
    exact (closure_mono hFsupport).trans hKclosed.closure_subset
  have huMD : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u :=
    contMDiff_iff_contDiff.mpr hu
  have hFsource : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F c.source := by
    have hc : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
        𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ c c.source := by
      simpa [c, extChartAt_source] using
        (contMDiffOn_extChartAt
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (n := ∞) (x := i))
    have hcomp : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
        (fun x => u (c x)) c.source := huMD.comp_contMDiffOn hc
    apply hcomp.congr
    intro x hx
    simp [F, hx]
  have hFoutside : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F Kᶜ := by
    apply contMDiffOn_const.congr
    intro x hx
    have hxK : x ∉ K := hx
    have hxT : x ∉ tsupport F := fun ht => hxK (hFtsupport ht)
    exact (notMem_tsupport_iff_eventuallyEq.mp hxT).self_of_nhds
  have hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F := by
    apply contMDiff_of_locally_contMDiffOn
    intro x
    by_cases hx : x ∈ K
    · exact ⟨c.source,
        isOpen_extChartAt_source (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) i,
        hKsource hx, hFsource⟩
    · exact ⟨Kᶜ, hKclosed.isOpen_compl, hx, hFoutside⟩
  refine ⟨F, hF, hFtsupport.trans hKsource, ?_⟩
  intro z hz
  have hsymm : c.symm z ∈ c.source := c.map_target hz
  change (if c.symm z ∈ c.source then u (c (c.symm z)) else 0) = u z
  rw [ite_eq_left hsymm, c.right_inv hz]

/-- The zero extensions of all the local convolutions. On the source chart target,
the global extension agrees pointwise with its Euclidean convolution; outside
the source chart it vanishes in a neighborhood because its *closed* support is
strictly contained in the source. -/
structure ChartwiseSourceMollificationData {φ : M → ℝ}
    (L : CompactChartC2Localization (n := n) (M := M) φ)
    (A : ∀ i, EuclideanC2MollificationData
      (EuclideanSpace ℂ (Fin n)) (L.localFunction i)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)).target) where
  approximation : L.cover.ι → ℕ → M → ℝ
  smooth : ∀ i j,
    ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (approximation i j)
  support_in_source : ∀ i j, tsupport (approximation i j) ⊆
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)).source
  coordinate_eq : ∀ i j z,
    z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)).target →
      approximation i j
        ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)).symm z) =
          (A i).approximation j z

omit [CompactSpace M] in
/-- Construct global smooth zero extensions, one per chart index. The fixed
compact support bounds of `A i` prevent boundary artifacts. -/
theorem exists_chartwiseSourceMollificationData
    {φ : M → ℝ} (L : CompactChartC2Localization (n := n) (M := M) φ)
    (A : ∀ i, EuclideanC2MollificationData
      (EuclideanSpace ℂ (Fin n)) (L.localFunction i)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)).target) :
    Nonempty (ChartwiseSourceMollificationData L A) := by
  classical
  have hext (i : L.cover.ι) (j : ℕ) :
      ∃ F : M → ℝ,
        ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F ∧
        tsupport F ⊆
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)).source ∧
        ∀ z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)).target,
          F ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)).symm z) =
            (A i).approximation j z := by
    apply exists_smooth_zero_extension_of_chart_support
      (L.cover.base i) ((A i).approximation j) ((A i).smooth j)
    · exact ((A i).supportBound_compact).of_isClosed_subset
        (isClosed_tsupport ((A i).approximation j)) ((A i).support_in_bound j)
    · exact ((A i).support_in_bound j).trans (A i).supportBound_subset
  choose F hF using hext
  exact ⟨⟨F, (fun i j => (hF i j).1),
    (fun i j => (hF i j).2.1), (fun i j z hz => (hF i j).2.2 z hz)⟩⟩

end KahlerForm
