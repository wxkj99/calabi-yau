module

public import CalabiYau.Geometry.Complex.Holder

/-!
# Addition of local Hölder bounds

Pointwise smoothness ensures that the iterated derivatives of a sum are the sums of the iterated
derivatives. Together with the triangle inequalities for the derivative bounds and Hölder
seminorm, this gives a local Hölder bound for the sum.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal

/-- Adding two functions with the same Hölder order preserves the bound, with the constants
added, provided both functions are `C^k` at each point of the set. The smoothness hypotheses are
needed because `HolderBoundOn` alone does not ensure that the derivative of a sum is the sum of
the derivatives at a point where the summands fail to be differentiable. -/
theorem holderBoundOn_add_same_order
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ} {α C D : ℝ≥0} {K : Set E} (f g : E → F)
    (hf : HolderBoundOn k α C K f) (hg : HolderBoundOn k α D K g)
    (hfSmooth : ∀ z ∈ K, ContDiffAt ℝ k f z)
    (hgSmooth : ∀ z ∈ K, ContDiffAt ℝ k g z) :
    HolderBoundOn k α (C + D) K (fun z ↦ f z + g z) := by
  refine ⟨?_, ?_⟩
  · intro j hj z hz
    have hj' : (j : ℕ∞ω) ≤ k := by exact_mod_cast hj
    have hfz : ContDiffAt ℝ j f z := (hfSmooth z hz).of_le hj'
    have hgz : ContDiffAt ℝ j g z := (hgSmooth z hz).of_le hj'
    have hadd := iteratedFDeriv_add_apply hfz hgz
    have hbound₁ := hf.1 j hj z hz
    have hbound₂ := hg.1 j hj z hz
    change ‖iteratedFDeriv ℝ j (f + g) z‖ ≤ (C + D : ℝ)
    rw [hadd]
    calc
      ‖iteratedFDeriv ℝ j f z + iteratedFDeriv ℝ j g z‖ ≤
          ‖iteratedFDeriv ℝ j f z‖ + ‖iteratedFDeriv ℝ j g z‖ := norm_add_le _ _
      _ ≤ (C : ℝ) + (D : ℝ) := add_le_add hbound₁ hbound₂
  · have hholder₁ : HolderWith C α (fun z : K ↦ iteratedFDeriv ℝ k f z) :=
      hf.2.holderWith
    have hholder₂ : HolderWith D α (fun z : K ↦ iteratedFDeriv ℝ k g z) :=
      hg.2.holderWith
    have hholder := hholder₁.add hholder₂
    intro z hz w hw
    have hfz : ContDiffAt ℝ k f z := hfSmooth z hz
    have hgz : ContDiffAt ℝ k g z := hgSmooth z hz
    have hfw : ContDiffAt ℝ k f w := hfSmooth w hw
    have hgw : ContDiffAt ℝ k g w := hgSmooth w hw
    have haddz := iteratedFDeriv_add_apply hfz hgz
    have haddw := iteratedFDeriv_add_apply hfw hgw
    change iteratedFDeriv ℝ k (f + g) z = _ at haddz
    change iteratedFDeriv ℝ k (f + g) w = _ at haddw
    change edist (iteratedFDeriv ℝ k (f + g) z)
      (iteratedFDeriv ℝ k (f + g) w) ≤ _
    rw [haddz, haddw]
    exact hholder ⟨z, hz⟩ ⟨w, hw⟩

end
