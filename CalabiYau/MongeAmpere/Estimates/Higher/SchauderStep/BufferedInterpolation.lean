module

public import CalabiYau.Geometry.Complex.Holder
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

/-!
# Buffered interpolation for compact Hölder bounds

Uniform derivative bounds on a compact outer buffer give a common Hölder bound on the inner open
set. The compact buffer supplies a uniform radius for segments starting in the closure of the
inner set.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal ENNReal

private theorem segment_dist_left_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y z : E} (hz : z ∈ segment ℝ x y) : dist x z ≤ dist x y := by
  rw [segment_eq_image] at hz
  rcases hz with ⟨t, ht, rfl⟩
  have hvec : x - ((1 - t) • x + t • y) = t • (x - y) := by module
  rw [dist_eq_norm, hvec, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1, dist_eq_norm]
  exact mul_le_of_le_one_left (norm_nonneg _) ht.2

private theorem exists_pos_segment_radius
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K U : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ δ → segment ℝ x y ⊆ U := by
  have hdisj : Disjoint K Uᶜ := by
    rw [Set.disjoint_left]
    intro z hzK hzC
    exact hzC (hKU hzK)
  obtain ⟨δ, hδ, hfar⟩ := Metric.exists_pos_forall_lt_edist hK hU.isClosed_compl hdisj
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy hxy z hz
  by_contra hzU
  have hzC : z ∈ Uᶜ := hzU
  have hfar' := hfar x hx z hzC
  have hnear : edist x z ≤ (δ : ENNReal) := by
    rw [edist_dist, ENNReal.ofReal_le_coe]
    exact (segment_dist_left_le hz).trans hxy
  exact (not_lt_of_ge hnear) hfar'

/-- Uniform bounds through one derivative on a compact buffer give a `C^{k,α}` bound on the
inner open set. The strict exponent range is recorded because it is the range used by interior
Schauder estimates. -/
@[deprecated "unused hypotheses `hU` and `hα₀`; will be removed" (since := "2026-10-02")]
theorem exists_uniform_holderBoundOn_family_of_buffered_derivative_bounds
    {P E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {W U L : Set E} {k : ℕ} {α C : ℝ≥0}
    (S : Set P) (f : P → E → F) (hW : IsOpen W) (hU : IsOpen U) (hL : IsCompact L)
    (hbuffer : closure U ⊆ interior L) (hLW : L ⊆ W)
    (hα₀ : 0 < α) (hα₁ : α < 1)
    (hf : ∀ p ∈ S, ContDiffOn ℝ ∞ (f p) W)
    (hbound : ∀ p ∈ S, ∀ j ≤ k + 1, ∀ z ∈ L,
      ‖iteratedFDeriv ℝ j (f p) z‖ ≤ C) :
    ∃ C' : ℝ≥0, ∀ p ∈ S, HolderBoundOn k α C' U (f p) := by
  classical
  have hK : IsCompact (closure U) :=
    hL.of_isClosed_subset isClosed_closure (hbuffer.trans interior_subset)
  obtain ⟨δ, hδ, hsegment⟩ :=
    exists_pos_segment_radius isOpen_interior hK hbuffer
  have hklt : (k : ℕ∞ω) < (k + 1 : ℕ∞ω) := by
    exact_mod_cast Nat.lt_succ_self k
  let L' : ℝ≥0 := max C (2 * C / δ)
  let D : ℝ≥0 := (Metric.ediam L).toNNReal
  have hdiamTop : Metric.ediam L ≠ ⊤ := hL.isBounded.ediam_ne_top
  have hdiam (x : E) (hx : x ∈ U) (y : E) (hy : y ∈ U) :
      edist x y ≤ (D : ℝ≥0∞) := by
    rw [show (D : ℝ≥0∞) = Metric.ediam L from ENNReal.coe_toNNReal hdiamTop]
    exact Metric.edist_le_ediam_of_mem (interior_subset (hbuffer (subset_closure hx)))
      (interior_subset (hbuffer (subset_closure hy)))
  let Cα : ℝ≥0 := L' * D ^ ((1 : ℝ) - (α : ℝ))
  let Ctot : ℝ≥0 := max C Cα
  have hαle : α ≤ 1 := by exact_mod_cast hα₁.le
  refine ⟨Ctot, ?_⟩
  intro p hp
  let g : E → E [×k]→L[ℝ] F := iteratedFDeriv ℝ k (f p)
  have hLip : LipschitzOnWith L' g U := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    by_cases hclose : dist x y ≤ δ
    · have hseg := hsegment x (subset_closure hx) y (subset_closure hy) hclose
      have hsegLip : LipschitzOnWith C g (segment ℝ x y) := by
        apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
        · intro z hz
          have hzL : z ∈ L := interior_subset (hseg hz)
          have hzW : z ∈ W := hLW hzL
          have hAtTop : ContDiffAt ℝ ∞ (f p) z :=
            (hf p hp).contDiffAt (hW.mem_nhds hzW)
          have hkTop : (↑(k + 1) : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
            exact_mod_cast (show ((k + 1 : ℕ) : ℕ∞) ≤ ⊤ from le_top)
          have hAt : ContDiffAt ℝ (k + 1) (f p) z := hAtTop.of_le hkTop
          exact hAt.differentiableAt_iteratedFDeriv hklt
        · intro z hz
          change ‖fderiv ℝ (iteratedFDeriv ℝ k (f p)) z‖₊ ≤ C
          have hreal : ‖fderiv ℝ (iteratedFDeriv ℝ k (f p)) z‖ ≤ (C : ℝ) := by
            rw [norm_fderiv_iteratedFDeriv]
            exact hbound p hp (k + 1) (Nat.le_refl _) z (interior_subset (hseg hz))
          exact_mod_cast hreal
        · exact convex_segment x y
      have hxseg : x ∈ segment ℝ x y := left_mem_segment ℝ x y
      have hyseg : y ∈ segment ℝ x y := right_mem_segment ℝ x y
      exact (hsegLip.dist_le_mul x hxseg y hyseg).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left C (2 * C / δ)) dist_nonneg)
    · have hfar : (δ : ℝ) < dist x y := lt_of_not_ge hclose
      have hxBound : ‖g x‖ ≤ C := by
        exact_mod_cast hbound p hp k (Nat.le_succ k) x
          (interior_subset (hbuffer (subset_closure hx)))
      have hyBound : ‖g y‖ ≤ C := by
        exact_mod_cast hbound p hp k (Nat.le_succ k) y
          (interior_subset (hbuffer (subset_closure hy)))
      have hratio : (↑(2 * C / δ) : ℝ) * (δ : ℝ) = 2 * (C : ℝ) := by
        rw [NNReal.coe_div, NNReal.coe_mul]
        field_simp [ne_of_gt (NNReal.coe_pos.mpr hδ)]
        exact mul_comm _ _
      calc
        dist (g x) (g y) ≤ ‖g x‖ + ‖g y‖ := dist_le_norm_add_norm _ _
        _ ≤ 2 * (C : ℝ) := by
          calc
            ‖g x‖ + ‖g y‖ ≤ (C : ℝ) + C := add_le_add hxBound hyBound
            _ = 2 * (C : ℝ) := by rw [two_mul]
        _ = (↑(2 * C / δ) : ℝ) * (δ : ℝ) := hratio.symm
        _ ≤ (↑(2 * C / δ) : ℝ) * dist x y :=
          mul_le_mul_of_nonneg_left hfar.le (by positivity)
        _ ≤ (L' : ℝ) * dist x y :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_right C (2 * C / δ))
            dist_nonneg
  have hholder : HolderOnWith Cα α g U := by
    simpa [Cα] using hLip.holderOnWith.of_le hdiam hαle
  refine ⟨?_, hholder.mono_const (le_max_right C Cα)⟩
  intro j hj z hz
  exact (hbound p hp j (le_trans hj (Nat.le_succ k)) z
    (interior_subset (hbuffer (subset_closure hz)))).trans <| by
      exact_mod_cast (le_max_left C Cα)

end
