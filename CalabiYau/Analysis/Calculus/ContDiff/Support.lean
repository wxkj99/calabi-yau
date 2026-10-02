-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Calculus/ContDiff/Support.lean
-- Locally modified.
module
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Topology.Algebra.Support

@[expose] public section

open Set

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞} {f : E → F} {s t : Set E}

theorem ContDiffOn.contDiffOn_of_tsupport_subset (hf : ContDiffOn 𝕜 n f (s ∩ t))
    (hs : IsOpen s) (hfs : tsupport f ∩ t ⊆ s) : ContDiffOn 𝕜 n f t := by
  intro x hx
  by_cases hfx : x ∈ tsupport f
  · have hxs : x ∈ s := hfs ⟨hfx, hx⟩
    apply (contDiffWithinAt_inter (hs.mem_nhds hxs)).mp
    exact (hf x ⟨hxs, hx⟩).mono (by rw [inter_comm])
  · exact contDiffAt_const.contDiffWithinAt.congr_of_eventuallyEq
      (Filter.EventuallyEq.filter_mono (notMem_tsupport_iff_eventuallyEq.mp hfx)
        nhdsWithin_le_nhds) (image_eq_zero_of_notMem_tsupport hfx)

theorem ContDiffOn.contDiff_of_tsupport_subset (hf : ContDiffOn 𝕜 n f s)
    (hs : IsOpen s) (hfs : tsupport f ⊆ s) : ContDiff 𝕜 n f := by
  rw [← contDiffOn_univ]
  apply ContDiffOn.contDiffOn_of_tsupport_subset (s := s)
  · simpa only [inter_univ] using hf
  · exact hs
  · simpa only [inter_univ] using hfs

theorem ContDiffOn.indicator_of_tsupport_subset (hf : ContDiffOn 𝕜 n f (s ∩ t))
    (hs : IsOpen s) (hfs : tsupport f ∩ t ⊆ s) :
    ContDiffOn 𝕜 n ((s ∩ t).indicator f) t := by
  classical
  have hsub : tsupport ((s ∩ t).indicator f) ⊆ tsupport f := by
    apply closure_mono
    rw [support_indicator]
    exact inter_subset_right
  apply ContDiffOn.contDiffOn_of_tsupport_subset
    (hf.congr fun x hx => indicator_of_mem hx f) hs
  intro x hx
  exact hfs ⟨hsub hx.1, hx.2⟩
