-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Calculus/Cutoff/Basic.lean
-- Locally modified.
module
public import Mathlib.Geometry.Manifold.PartitionOfUnity

@[expose] public section

set_option autoImplicit false

namespace CalabiYau

open Filter Set
open scoped ContDiff Manifold Topology

theorem contDiffOn_cutoff_smul
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞ω}
    {S U : Set E} (hU : IsOpen U) {χ : E → ℝ} {f : E → F}
    (hχ : ContDiff ℝ n χ) (hχU : tsupport χ ⊆ U)
    (hf : ContDiffOn ℝ n f (S ∩ U)) : ContDiffOn ℝ n (fun x => χ x • f x) S := by
  intro x hx
  by_cases hxχ : x ∈ tsupport χ
  · have hxU : x ∈ U := hχU hxχ
    exact hχ.contDiffWithinAt.smul ((hf x ⟨hx, hxU⟩).mono_of_mem_nhdsWithin
      (inter_mem_nhdsWithin S (hU.mem_nhds hxU)))
  · have heq : (fun y => χ y • f y) =ᶠ[𝓝 x] (fun _ => (0 : F)) := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hxχ] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]
    exact (contDiffAt_const.congr_of_eventuallyEq heq).contDiffWithinAt

theorem contDiff_cutoff_smul
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U)
    {χ : E → ℝ} {f : E → F}
    (hχ : ContDiff ℝ ∞ χ)
    (hχU : tsupport χ ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U) :
    ContDiff ℝ ∞ (fun x => χ x • f x) := by
  apply contDiffOn_univ.mp
  exact contDiffOn_cutoff_smul (S := univ) hU hχ hχU
    (by simpa only [univ_inter] using hf)

end CalabiYau
