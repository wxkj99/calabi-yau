-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Chart/SmoothDensity/StrictCutoff.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Riemannian.Volume.Basic
public import Mathlib.Geometry.Manifold.PartitionOfUnity

@[expose] public section

-- Module-system compatibility: the extracted public definition refers to a private helper.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open Set Topology Bundle Manifold Filter
open scoped Manifold ContDiff

namespace CalabiYau
namespace Analysis
namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M] [CompactSpace M] [I.Boundaryless]

open CalabiYau.RiemannianVolume

omit [T2Space M] [CompactSpace M] in
private lemma isClosed_compl_chartAt_source (α : M) :
    IsClosed ((chartAt H α).sourceᶜ) :=
  (chartAt H α).open_source.isClosed_compl

omit [I.Boundaryless] in
private lemma isClosed_tsupport_chartAtlasPOU (α : M) :
    IsClosed (tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
  isClosed_tsupport _

omit [I.Boundaryless] in
private lemma tsupport_chartAtlasPOU_subset (α : M) :
    tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆
      (chartAt H α).source :=
  (chartAtlasPOU_isSubordinate I M) α

omit [I.Boundaryless] in
private lemma disjoint_complSource_tsupport_chartAtlasPOU (α : M) :
    Disjoint ((chartAt H α).sourceᶜ)
      (tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
  Set.disjoint_compl_left_iff_subset.mpr
    (tsupport_chartAtlasPOU_subset (I := I) α)

private def chartStrictCutoffBundled (α : M) : C^∞⟮I, M; ℝ⟯ :=
  ((Classical.choose
    (exists_contMDiffMap_zero_one_nhds_of_isClosed (I := I) (M := M)
      (n := (⊤ : ℕ∞))
      (isClosed_compl_chartAt_source (M := M) α)
      (isClosed_tsupport_chartAtlasPOU (I := I) α)
      (disjoint_complSource_tsupport_chartAtlasPOU (I := I) α))) :
        C^∞⟮I, M; ℝ⟯)

omit [I.Boundaryless] in
private lemma chartStrictCutoffBundled_spec (α : M) :
    (∀ᶠ x in 𝓝ˢ ((chartAt H α).sourceᶜ),
      ((chartStrictCutoffBundled (I := I) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0) ∧
    (∀ᶠ x in 𝓝ˢ (tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)),
      ((chartStrictCutoffBundled (I := I) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 1) ∧
    ∀ x, ((chartStrictCutoffBundled (I := I) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x ∈
        Set.Icc (0 : ℝ) 1 :=
  Classical.choose_spec
    (exists_contMDiffMap_zero_one_nhds_of_isClosed (I := I) (M := M)
      (n := (⊤ : ℕ∞))
      (isClosed_compl_chartAt_source (M := M) α)
      (isClosed_tsupport_chartAtlasPOU (I := I) α)
      (disjoint_complSource_tsupport_chartAtlasPOU (I := I) α))

def chartStrictCutoff (α : M) : M → ℝ :=
  ((chartStrictCutoffBundled (I := I) α : C^∞⟮I, M; ℝ⟯) : M → ℝ)

omit [I.Boundaryless] in
private lemma chartStrictCutoff_eq_bundled (α : M) :
    chartStrictCutoff (I := I) α =
      ((chartStrictCutoffBundled (I := I) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
  rfl

omit [I.Boundaryless] in
theorem chartStrictCutoff_contMDiff (α : M) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (chartStrictCutoff (I := I) α) :=
  (chartStrictCutoffBundled (I := I) α).contMDiff

omit [I.Boundaryless] in
theorem chartStrictCutoff_eventually_zero_nhdsSet_compl_source (α : M) :
    ∀ᶠ x in 𝓝ˢ ((chartAt H α).sourceᶜ), chartStrictCutoff (I := I) α x = 0 :=
  (chartStrictCutoffBundled_spec (I := I) α).1

omit [I.Boundaryless] in
theorem chartStrictCutoff_eventually_one_nhdsSet_tsupport_chartAtlasPOU (α : M) :
    ∀ᶠ x in 𝓝ˢ (tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)),
      chartStrictCutoff (I := I) α x = 1 :=
  (chartStrictCutoffBundled_spec (I := I) α).2.1

omit [I.Boundaryless] in
theorem chartStrictCutoff_eq_one_on_tsupport_chartAtlasPOU (α : M) {x : M}
    (hx : x ∈ tsupport
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :
    chartStrictCutoff (I := I) α x = 1 :=
  (chartStrictCutoff_eventually_one_nhdsSet_tsupport_chartAtlasPOU
    (I := I) α).self_of_nhdsSet _ hx

omit [I.Boundaryless] in
theorem chartStrictCutoff_tsupport_subset (α : M) :
    tsupport (chartStrictCutoff (I := I) α) ⊆ (chartAt H α).source := by
  classical
  have hev : ∀ᶠ x in 𝓝ˢ ((chartAt H α).sourceᶜ),
      chartStrictCutoff (I := I) α x = 0 :=
    chartStrictCutoff_eventually_zero_nhdsSet_compl_source (I := I) α
  rw [eventually_nhdsSet_iff_exists] at hev
  obtain ⟨U, hUopen, hUsub, hUzero⟩ := hev
  have hUcomp : IsClosed (Uᶜ) := hUopen.isClosed_compl
  have hsupp_sub : Function.support (chartStrictCutoff (I := I) α) ⊆ Uᶜ := by
    intro x hx
    by_contra hxU
    have hxU' : x ∈ U := by
      simpa using hxU
    exact hx (hUzero x hxU')
  have htsupp_sub : tsupport (chartStrictCutoff (I := I) α) ⊆ Uᶜ :=
    closure_minimal hsupp_sub hUcomp
  have hUcomp_sub : Uᶜ ⊆ (chartAt H α).source := by
    intro x hx
    by_contra hx_not
    have : x ∈ U := hUsub hx_not
    exact hx this
  exact htsupp_sub.trans hUcomp_sub

end Chart
end Sobolev
end Analysis
end CalabiYau
