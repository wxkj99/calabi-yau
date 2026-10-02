module

public import CalabiYau.Mathlib.Geometry.Manifold.Holder
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

/-!
# Compact Hölder bounds for smooth chart data

Smooth functions on a neighborhood of a compact set have bounded derivatives there. Their top
derivative is locally Lipschitz, hence globally Lipschitz on the compact set. A Lipschitz bound
implies a Hölder bound only for exponents at most one, which is stated explicitly below.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal ENNReal

namespace CompactSmoothHolder

/-- Smooth data on a neighborhood of a compact set have a finite local `C^{k,α}` bound when
`α ≤ 1`. -/
theorem exists_holderBoundOn_of_contDiffOn_neighborhood_of_compact
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {W K : Set E} {k : ℕ} {α : ℝ≥0}
    (f : E → F) (hW : IsOpen W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hα : α ≤ 1) (hf : ContDiffOn ℝ ∞ f W) :
    ∃ C : ℝ≥0, HolderBoundOn k α C K f := by
  classical
  have hlocal : LocallyLipschitzOn K (iteratedFDeriv ℝ k f) := by
    intro x hx
    have hfx : ContDiffAt ℝ ∞ f x := hf.contDiffAt (hW.mem_nhds (hKW hx))
    have hderiv : ContDiffAt ℝ 1 (iteratedFDeriv ℝ k f) x := by
      exact ContDiffAt.iteratedFDeriv_right hfx (m := 1) (i := k)
        (show (1 : ℕ∞ω) + k ≤ (∞ : ℕ∞ω) by
          exact_mod_cast (le_top : (1 + k : ℕ∞) ≤ ⊤))
    obtain ⟨L, t, ht, hLip⟩ := hderiv.exists_lipschitzOnWith
    exact ⟨L, K ∩ t, inter_mem_nhdsWithin K ht, hLip.mono Set.inter_subset_right⟩
  obtain ⟨L, hLip⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK hlocal
  have hcont (j : ℕ) : ContinuousOn (iteratedFDeriv ℝ j f) K := by
    intro z hz
    have hfz : ContDiffAt ℝ ∞ f z := hf.contDiffAt (hW.mem_nhds (hKW hz))
    exact (ContDiffAt.continuousAt_iteratedFDeriv hfz
      (show (j : ℕ∞ω) ≤ (∞ : ℕ∞ω) by
        exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).continuousWithinAt
  let b (j : ℕ) : ℝ := Classical.choose (hK.exists_bound_of_continuousOn (hcont j))
  have hb (j : ℕ) : ∀ z ∈ K, ‖iteratedFDeriv ℝ j f z‖ ≤ b j :=
    Classical.choose_spec (hK.exists_bound_of_continuousOn (hcont j))
  let B (j : ℕ) : ℝ≥0 := ⟨max (b j) 0, le_max_right _ _⟩
  have hB (j : ℕ) (z : E) (hz : z ∈ K) : ‖iteratedFDeriv ℝ j f z‖ ≤ B j := by
    exact (hb j z hz).trans (by exact_mod_cast (le_max_left (b j) 0))
  let js : Finset ℕ := Finset.range (k + 1)
  let C : ℝ≥0 := js.sup B
  have hC (j : ℕ) (hj : j ≤ k) : B j ≤ C := by
    exact Finset.le_sup (Finset.mem_range.mpr (by omega : j < k + 1))
  let D : ℝ≥0 := (Metric.ediam K).toNNReal
  have hdiamTop : Metric.ediam K ≠ ⊤ := hK.isBounded.ediam_ne_top
  have hdiam (x : E) (hx : x ∈ K) (y : E) (hy : y ∈ K) :
      edist x y ≤ (D : ℝ≥0∞) := by
    rw [show (D : ℝ≥0∞) = Metric.ediam K from ENNReal.coe_toNNReal hdiamTop]
    exact Metric.edist_le_ediam_of_mem hx hy
  let H : ℝ≥0 := L * D ^ ((1 : ℝ) - α)
  have hHolder : HolderOnWith H α (iteratedFDeriv ℝ k f) K :=
    hLip.holderOnWith.of_le hdiam hα
  refine ⟨max C H, ?_⟩
  refine ⟨?_, hHolder.mono_const (le_max_right C H)⟩
  intro j hj z hz
  exact (hB j z hz).trans ((hC j hj).trans (le_max_left C H))

/-- A finite family of smooth matrix entries has one common Hölder bound on a compact set,
provided `α ≤ 1`. -/
theorem exists_holderBoundOn_matrix_entries_of_contDiffOn_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n k : ℕ} {α : ℝ≥0} {W K : Set E}
    (A : E → Matrix (Fin n) (Fin n) ℂ) (hW : IsOpen W) (hK : IsCompact K)
    (hKW : K ⊆ W) (hα : α ≤ 1)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ A z i j) W) :
    ∃ C : ℝ≥0, ∀ i j, HolderBoundOn k α C K (fun z ↦ A z i j) := by
  classical
  let c (i j : Fin n) : ℝ≥0 := Classical.choose
    (exists_holderBoundOn_of_contDiffOn_neighborhood_of_compact (k := k)
      (fun z ↦ A z i j) hW hK hKW hα (hA i j))
  have hc (i j : Fin n) :
      HolderBoundOn k α (c i j) K (fun z ↦ A z i j) :=
    Classical.choose_spec
      (exists_holderBoundOn_of_contDiffOn_neighborhood_of_compact (k := k)
        (fun z ↦ A z i j) hW hK hKW hα (hA i j))
  let C : ℝ≥0 := Finset.univ.sup (fun i : Fin n ↦ Finset.univ.sup (c i))
  have hC (i j : Fin n) : c i j ≤ C := by
    calc
      c i j ≤ Finset.univ.sup (c i) :=
        Finset.le_sup (s := Finset.univ) (f := c i) (Finset.mem_univ j)
      _ ≤ Finset.univ.sup (fun p : Fin n ↦ Finset.univ.sup (c p)) :=
        Finset.le_sup (s := Finset.univ)
          (f := fun p : Fin n ↦ Finset.univ.sup (c p)) (Finset.mem_univ i)
  refine ⟨C, ?_⟩
  intro i j
  exact (hc i j).mono_const (hC i j)

/-- Directional derivatives of smooth matrix entries have one common Hölder bound over all
matrix indices on a compact set, provided `α ≤ 1`. -/
theorem exists_holderBoundOn_matrix_directional_derivative_entries_of_contDiffOn_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n k : ℕ} {α : ℝ≥0} {W K : Set E}
    (A : E → Matrix (Fin n) (Fin n) ℂ) (v : E)
    (hW : IsOpen W) (hK : IsCompact K) (hKW : K ⊆ W) (hα : α ≤ 1)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ A z i j) W) :
    ∃ C : ℝ≥0, ∀ i j,
      HolderBoundOn k α C K (fun z ↦ fderiv ℝ (fun z ↦ A z i j) z v) := by
  classical
  let d (i j : Fin n) : E → ℂ := fun z ↦ fderiv ℝ (fun z ↦ A z i j) z v
  have hd (i j : Fin n) : ContDiffOn ℝ ∞ (d i j) W := by
    have hderiv := (hA i j).fderiv_of_isOpen hW (m := ∞) (by simp)
    exact hderiv.clm_apply contDiffOn_const
  let c (i j : Fin n) : ℝ≥0 := Classical.choose
    (exists_holderBoundOn_of_contDiffOn_neighborhood_of_compact (k := k)
      (d i j) hW hK hKW hα (hd i j))
  have hc (i j : Fin n) : HolderBoundOn k α (c i j) K (d i j) :=
    Classical.choose_spec
      (exists_holderBoundOn_of_contDiffOn_neighborhood_of_compact (k := k)
        (d i j) hW hK hKW hα (hd i j))
  let C : ℝ≥0 := Finset.univ.sup (fun i : Fin n ↦ Finset.univ.sup (c i))
  have hC (i j : Fin n) : c i j ≤ C := by
    calc
      c i j ≤ Finset.univ.sup (c i) :=
        Finset.le_sup (s := Finset.univ) (f := c i) (Finset.mem_univ j)
      _ ≤ Finset.univ.sup (fun p : Fin n ↦ Finset.univ.sup (c p)) :=
        Finset.le_sup (s := Finset.univ)
          (f := fun p : Fin n ↦ Finset.univ.sup (c p)) (Finset.mem_univ i)
  refine ⟨C, ?_⟩
  intro i j
  exact (hc i j).mono_const (hC i j)

end CompactSmoothHolder

end
