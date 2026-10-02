module

public import CalabiYau.Mathlib.Geometry.Manifold.Holder
public import CalabiYau.Mathlib.Analysis.Holder.Bilinear

@[expose] public section

open Set
open scoped Manifold ContDiff NNReal Topology

namespace CalabiYau.Schauder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A `C^{k+1,α}` bound controls the `C^{k,α}` bound on a convex set of diameter at most one.
The differentiability assumption is essential because `HolderBoundOn` alone does not imply
that iterated derivatives are genuine derivatives. -/
theorem holderBoundOn_of_contDiffOn_succ
    {k : ℕ} {α C : ℝ≥0} {s : Set E} {f : E → F}
    (hs_open : IsOpen s) (hs_convex : Convex ℝ s)
    (hs_diam : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ 1)
    (hα : α ≤ 1) (hcont : ContDiffOn ℝ (k + 1) f s)
    (hbound : HolderBoundOn (k + 1) α C s f) :
    HolderBoundOn k α C s f := by
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    exact hbound.1 j (le_trans hj (Nat.le_succ k)) x hx
  · let g : E → _ := iteratedFDeriv ℝ k f
    have hklt : (↑k : ℕ∞ω) < (↑(k + 1) : ℕ∞ω) := by
      exact_mod_cast Nat.lt_succ_self k
    have hgDiff (x : E) (hx : x ∈ s) : DifferentiableAt ℝ g x := by
      have hfx : ContDiffAt ℝ (k + 1) f x :=
        hcont.contDiffAt (hs_open.mem_nhds hx)
      exact hfx.differentiableAt_iteratedFDeriv hklt
    have hgDeriv (x : E) (hx : x ∈ s) : ‖fderiv ℝ g x‖ ≤ (C : ℝ) := by
      rw [norm_fderiv_iteratedFDeriv]
      exact hbound.1 (k + 1) le_rfl x hx
    have hLip : LipschitzOnWith C g s := by
      apply hs_convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
      · exact hgDiff
      · exact hgDeriv
    have hdiam (x : E) (hx : x ∈ s) (y : E) (hy : y ∈ s) :
        edist x y ≤ (1 : ENNReal) := by
      rw [edist_dist]
      calc
        ENNReal.ofReal (dist x y) ≤ ENNReal.ofReal 1 :=
          ENNReal.ofReal_le_ofReal (by exact_mod_cast hs_diam x hx y hy)
        _ = 1 := ENNReal.ofReal_one
    simpa [g] using (hLip.holderOnWith.of_le hdiam hα)

variable {A B G : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {X : Type*} [MetricSpace X]

/-- Quantitative Hölder control of a bilinear commutator. The pointwise suprema are only needed
on `s`; the Hölder seminorms are local to `s`. -/
theorem holderOnWith_bilinear_of_opNorm_le_one
    {s : Set X} {α Kf Kg Mf Mg : ℝ≥0}
    (L : A →L[ℝ] B →L[ℝ] G) (hL : ‖L‖ ≤ 1)
    {f : X → A} {g : X → B}
    (hf : HolderOnWith Kf α f s) (hg : HolderOnWith Kg α g s)
    (hfnorm : ∀ x ∈ s, ‖f x‖ ≤ Mf) (hgnorm : ∀ x ∈ s, ‖g x‖ ≤ Mg) :
    HolderOnWith (Mf * Kg + Mg * Kf) α (fun x ↦ L (f x) (g x)) s := by
  have h := holderWith_bilinear_of_opNorm_le_one (X := s) L hL
    hf.holderWith hg.holderWith
    (fun x ↦ hfnorm x.1 x.2) (fun x ↦ hgnorm x.1 x.2)
  intro x hx y hy
  simpa only [Set.domRestrict_apply, Subtype.edist_eq] using
    h ⟨x, hx⟩ ⟨y, hy⟩

/-- A finite sum of locally Hölder functions has Hölder constant at most the sum of the constants. -/
theorem holderOnWith_finset_sum
    {X ι F : Type*} [MetricSpace X] [NormedAddCommGroup F]
    {s : Set X} {α : ℝ≥0} (t : Finset ι) (K : ι → ℝ≥0) (f : ι → X → F)
    (hf : ∀ i ∈ t, HolderOnWith (K i) α (f i) s) :
    HolderOnWith (t.sum K) α (fun x ↦ t.sum (fun i ↦ f i x)) s := by
  classical
  have hsum : ∀ u : Finset ι,
      (∀ i ∈ u, HolderOnWith (K i) α (f i) s) →
        HolderOnWith (u.sum K) α (fun x ↦ u.sum (fun i ↦ f i x)) s := by
    intro u
    induction u using Finset.induction_on with
    | empty =>
        intro hu x hx y hy
        simp
    | @insert i u hi ih =>
        intro hu x hx y hy
        have hhead := hu i (Finset.mem_insert_self i u) x hx y hy
        have htail : ∀ j ∈ u, HolderOnWith (K j) α (f j) s := by
          intro j hj
          exact hu j (Finset.mem_insert_of_mem hj)
        have hrest := ih htail x hx y hy
        change edist ((insert i u).sum (fun j ↦ f j x))
          ((insert i u).sum (fun j ↦ f j y)) ≤
            (↑((insert i u).sum K) : ENNReal) * edist x y ^ (α : ℝ)
        rw [Finset.sum_insert hi, Finset.sum_insert hi]
        grw [edist_add_add_le, hhead, hrest]
        rw [Finset.sum_insert hi, ENNReal.coe_add, ← add_mul]
  exact hsum t hf

end CalabiYau.Schauder
