module

public import CalabiYau.Mathlib.Geometry.Manifold.Holder
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

public section
open scoped NNReal Topology Manifold ContDiff
open Set
namespace KahlerForm

section CompactExtensionQuotientBounds

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem exists_contDiff_compact_extension_of_contDiffOn
    [FiniteDimensional ℝ E]
    (f : E → F) (S K : Set E) (hS : IsOpen S) (hK : IsCompact K)
    (hKS : K ⊆ S) (hf : ContDiffOn ℝ 2 f S) :
    ∃ g : E → F, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ EqOn g f K := by
  obtain ⟨V, hV, hKV, hVS, hVc⟩ :=
    exists_open_between_and_isCompact_closure hK hS hKS
  obtain ⟨χ, hχ, _, hχsupport, hχone⟩ :=
    exists_contMDiff_support_eq_eq_one_iff (𝓘(ℝ, E))
      (n := (2 : ℕ∞)) hV hK.isClosed hKV
  have hχdiff : ContDiff ℝ 2 χ := by
    exact contMDiff_iff_contDiff.mp hχ
  let g : E → F := fun x => χ x • f x
  have hsupp : tsupport χ ⊆ S := by
    simpa only [tsupport, hχsupport] using hVS
  refine ⟨g, ?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ S
    · exact hχdiff.contDiffAt.smul ((hf x hx).contDiffAt (hS.mem_nhds hx))
    · have hzero : χ =ᶠ[𝓝 x] (fun _ => 0) := by
        exact notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hsupp h))
      apply (contDiffAt_const : ContDiffAt ℝ 2 (fun _ : E => (0 : F)) x).congr_of_eventuallyEq
      filter_upwards [hzero] with y hy
      simp [g, hy]
  · apply HasCompactSupport.of_support_subset_isCompact hVc
    intro x hx
    have hχx : χ x ≠ 0 := by
      intro hz
      apply hx
      simp [g, hz]
    exact subset_closure (hχsupport ▸ hχx)
  · intro x hx
    simp only [g, (hχone x).mp hx, one_smul]

private theorem directionalQuotient_norm_le
    (f : E → F) (hf : Differentiable ℝ f) (B : ℝ≥0)
    (hB : ∀ x, ‖fderiv ℝ f x‖ ≤ (B : ℝ))
    (v : E) (h : ℝ) (hne : h ≠ 0) (x : E) :
    ‖h⁻¹ • (f (x + h • v) - f x)‖ ≤ (B : ℝ) * ‖v‖ := by
  let g : ℝ → F := fun t => f (x + t • v)
  have hg (t : ℝ) : HasDerivAt g (fderiv ℝ f (x + t • v) v) t := by
    have hp : HasDerivAt (fun t : ℝ => x + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    exact (hf (x + t • v)).hasFDerivAt.comp_hasDerivAt t hp
  have hgB (t : ℝ) : ‖fderiv ℝ f (x + t • v) v‖ ≤ (B : ℝ) * ‖v‖ :=
    ((fderiv ℝ f (x + t • v)).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _))
  have hm := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hg t).hasDerivWithinAt) (fun t _ => hgB t) (mem_univ 0) (mem_univ h)
  have hm' : ‖f (x + h • v) - f x‖ ≤ ((B : ℝ) * ‖v‖) * |h| := by
    simpa [g, Real.norm_eq_abs] using hm
  rw [norm_smul, norm_inv, Real.norm_eq_abs]
  have hpos : 0 < |h| := abs_pos.mpr hne
  calc
    |h|⁻¹ * ‖f (x + h • v) - f x‖ ≤ |h|⁻¹ * (((B : ℝ) * ‖v‖) * |h|) :=
      mul_le_mul_of_nonneg_left hm' (inv_nonneg.mpr (abs_nonneg h))
    _ = (B : ℝ) * ‖v‖ := by field_simp

private theorem directionalQuotient_lipschitzWith
    (f : E → F) (hf : Differentiable ℝ f) (B : ℝ≥0)
    (hB : LipschitzWith B (fderiv ℝ f))
    (v : E) (h : ℝ) (hne : h ≠ 0) :
    LipschitzWith (B * ‖v‖₊) (fun x => h⁻¹ • (f (x + h • v) - f x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let g : ℝ → F := fun t => f (x + t • v) - f (y + t • v)
  have hg (t : ℝ) : HasDerivAt g
      ((fderiv ℝ f (x + t • v) - fderiv ℝ f (y + t • v)) v) t := by
    have hpx : HasDerivAt (fun t : ℝ => x + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    have hpy : HasDerivAt (fun t : ℝ => y + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add y
    convert ((hf _).hasFDerivAt.comp_hasDerivAt t hpx).sub
      ((hf _).hasFDerivAt.comp_hasDerivAt t hpy) using 1
    · funext r
      rfl
    · rfl
  have hgB (t : ℝ) :
      ‖(fderiv ℝ f (x + t • v) - fderiv ℝ f (y + t • v)) v‖ ≤
        ((B : ℝ) * ‖x - y‖) * ‖v‖ := by
    have hLip := hB.dist_le_mul (x + t • v) (y + t • v)
    have hLip' : ‖fderiv ℝ f (x + t • v) - fderiv ℝ f (y + t • v)‖ ≤
        (B : ℝ) * ‖x - y‖ := by
      simpa [dist_eq_norm] using hLip
    exact ((fderiv ℝ f (x + t • v) - fderiv ℝ f (y + t • v)).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hLip' (norm_nonneg _))
  have hm := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hg t).hasDerivWithinAt) (fun t _ => hgB t) (mem_univ 0) (mem_univ h)
  have hm' : ‖g h - g 0‖ ≤ (((B : ℝ) * ‖x - y‖) * ‖v‖) * |h| := by
    simpa [Real.norm_eq_abs] using hm
  have hrewrite : (f (x + h • v) - f x) - (f (y + h • v) - f y) = g h - g 0 := by
    dsimp [g]
    simp only [zero_smul, add_zero]
    abel
  rw [dist_eq_norm, ← smul_sub, hrewrite, norm_smul, norm_inv, Real.norm_eq_abs]
  have hpos : 0 < |h| := abs_pos.mpr hne
  calc
    |h|⁻¹ * ‖g h - g 0‖ ≤ |h|⁻¹ * ((((B : ℝ) * ‖x - y‖) * ‖v‖) * |h|) :=
      mul_le_mul_of_nonneg_left hm' (inv_nonneg.mpr (abs_nonneg h))
    _ = ((B * ‖v‖₊ : ℝ≥0) : ℝ) * dist x y := by
      rw [NNReal.coe_mul, coe_nnnorm, dist_eq_norm]
      field_simp

private theorem directionalQuotient_uniform_holderBoundOn
    (f : E → F) (hf : Differentiable ℝ f) (B₀ B₁ : ℝ≥0)
    (hB₀ : ∀ x, ‖fderiv ℝ f x‖ ≤ (B₀ : ℝ))
    (hB₁ : LipschitzWith B₁ (fderiv ℝ f))
    (S : Set E) (D α : ℝ≥0) (hα : α ≤ 1)
    (hD : ∀ x ∈ S, ∀ y ∈ S, edist x y ≤ D) (v : E) :
    ∃ C : ℝ≥0, ∀ h : ℝ, h ≠ 0 →
      HolderBoundOn 0 α C S (fun x => h⁻¹ • (f (x + h • v) - f x)) := by
  let C₀ : ℝ≥0 := B₀ * ‖v‖₊
  let C₁ : ℝ≥0 := (B₁ * ‖v‖₊) * D ^ (1 - (α : ℝ))
  refine ⟨max C₀ C₁, ?_⟩
  intro h hne
  let q : E → F := fun x => h⁻¹ • (f (x + h • v) - f x)
  have hLip : LipschitzWith (B₁ * ‖v‖₊) q :=
    directionalQuotient_lipschitzWith f hf B₁ hB₁ v h hne
  have hHolder : HolderOnWith C₁ α q S := by
    exact (holderOnWith_one.mpr hLip.lipschitzOnWith).of_le hD hα
  have hHolder' : HolderOnWith (max C₀ C₁) α q S :=
    hHolder.mono_const (le_max_right _ _)
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    have hBound := directionalQuotient_norm_le f hf B₀ hB₀ v h hne x
    have hBound' : ‖q x‖ ≤ (C₀ : ℝ) := by
      simpa only [q, C₀, NNReal.coe_mul, coe_nnnorm] using hBound
    have hC : (C₀ : ℝ) ≤ ((max C₀ C₁ : ℝ≥0) : ℝ) := by
      exact_mod_cast (le_max_left C₀ C₁)
    simpa only [norm_iteratedFDeriv_zero] using hBound'.trans hC
  · let L := continuousMultilinearCurryFin0 ℝ E F
    intro x hx y hy
    rw [iteratedFDeriv_zero_eq_comp]
    change edist (L.symm (q x)) (L.symm (q y)) ≤ _
    rw [L.symm.edist_map]
    exact hHolder' x hx y hy

private theorem compactSource_directionalQuotient_uniform_holderBoundOn
    (f : E → F) (hf : ContDiff ℝ 2 f) (hcompact : HasCompactSupport f)
    (S : Set E) (D α : ℝ≥0) (hα : α ≤ 1)
    (hD : ∀ x ∈ S, ∀ y ∈ S, edist x y ≤ D) (v : E) :
    ∃ C : ℝ≥0, ∀ h : ℝ, h ≠ 0 →
      HolderBoundOn 0 α C S (fun x => h⁻¹ • (f (x + h • v) - f x)) := by
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hDDf : ContDiff ℝ 0 (fderiv ℝ (fderiv ℝ f)) :=
    hDf.fderiv_right (by norm_num)
  have hDcompact : HasCompactSupport (fderiv ℝ f) := hcompact.fderiv ℝ
  have hDDcompact : HasCompactSupport (fderiv ℝ (fderiv ℝ f)) := hDcompact.fderiv ℝ
  obtain ⟨b₀, hb₀⟩ := hDf.continuous.norm.bddAbove_range_of_hasCompactSupport
    (hDcompact.comp_left (by simp))
  obtain ⟨b₁, hb₁⟩ := hDDf.continuous.norm.bddAbove_range_of_hasCompactSupport
    (hDDcompact.comp_left (by simp))
  let B₀ : ℝ≥0 := ⟨max b₀ 0, le_max_right _ _⟩
  let B₁ : ℝ≥0 := ⟨max b₁ 0, le_max_right _ _⟩
  have hB₀ (x : E) : ‖fderiv ℝ f x‖ ≤ (B₀ : ℝ) :=
    (hb₀ ⟨x, rfl⟩).trans (le_max_left _ _)
  have hB₁ : LipschitzWith B₁ (fderiv ℝ f) := by
    apply lipschitzWith_of_nnnorm_fderiv_le (hDf.differentiable (by norm_num))
    intro x
    have hb : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ (B₁ : ℝ) :=
      (hb₁ ⟨x, rfl⟩).trans (le_max_left _ _)
    exact_mod_cast hb
  exact directionalQuotient_uniform_holderBoundOn f (hf.differentiable (by norm_num)) B₀ B₁
    hB₀ hB₁ S D α hα hD v

private theorem holderBoundOn_zero_congr
    {f g : E → F} {S : Set E} {α C : ℝ≥0}
    (hfg : Set.EqOn f g S) (hf : HolderBoundOn 0 α C S f) :
    HolderBoundOn 0 α C S g := by
  constructor
  · intro j hj x hx
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    have hbound := hf.1 0 (by simp) x hx
    simpa only [norm_iteratedFDeriv_zero, hfg hx] using hbound
  · intro x hx y hy
    rw [iteratedFDeriv_zero_eq_comp]
    let L := continuousMultilinearCurryFin0 ℝ E F
    change edist (L.symm (g x)) (L.symm (g y)) ≤ _
    rw [← hfg hx, ← hfg hy]
    exact hf.2 x hx y hy

private theorem local_directionalQuotient_uniform_holderBoundOn_of_compact_extension
    (f g : E → F) (hg : ContDiff ℝ 2 g) (hcompact : HasCompactSupport g)
    (S K : Set E) (hSK : S ⊆ K) (hgf : Set.EqOn g f K)
    (D α : ℝ≥0) (hα : α ≤ 1)
    (hD : ∀ x ∈ S, ∀ y ∈ S, edist x y ≤ D)
    (v : E) (δ : ℝ)
    (htranslate : ∀ h : ℝ, |h| < δ → ∀ x ∈ S, x + h • v ∈ K) :
    ∃ C : ℝ≥0, ∀ h : ℝ, h ≠ 0 → |h| < δ →
      HolderBoundOn 0 α C S (fun x => h⁻¹ • (f (x + h • v) - f x)) := by
  obtain ⟨C, hC⟩ :=
    compactSource_directionalQuotient_uniform_holderBoundOn
      g hg hcompact S D α hα hD v
  refine ⟨C, ?_⟩
  intro h hne hh
  apply holderBoundOn_zero_congr (hf := hC h hne)
  intro x hx
  change h⁻¹ • (g (x + h • v) - g x) = h⁻¹ • (f (x + h • v) - f x)
  rw [hgf (htranslate h hh x hx), hgf (hSK hx)]

theorem local_directionalQuotient_uniform_holderBoundOn_of_contDiffOn
    [FiniteDimensional ℝ E]
    (f : E → F) (S K K' : Set E) (hS : IsOpen S)
    (hK' : IsCompact K') (hK'S : K' ⊆ S) (hf : ContDiffOn ℝ 2 f S)
    (hKK' : K ⊆ K') (D α : ℝ≥0) (hα : α ≤ 1)
    (hD : ∀ x ∈ K, ∀ y ∈ K, edist x y ≤ D)
    (v : E) (δ : ℝ) (_hδ : 0 < δ)
    (htranslate : ∀ h : ℝ, |h| < δ → ∀ x ∈ K, x + h • v ∈ K') :
    ∃ C : ℝ≥0, ∀ h : ℝ, h ≠ 0 → |h| < δ →
      HolderBoundOn 0 α C K (fun x => h⁻¹ • (f (x + h • v) - f x)) := by
  obtain ⟨g, hg, hgcompact, hgEq⟩ := exists_contDiff_compact_extension_of_contDiffOn f S K' hS hK' hK'S hf
  exact local_directionalQuotient_uniform_holderBoundOn_of_compact_extension
    f g hg hgcompact K K' hKK' hgEq D α hα hD v δ htranslate

end CompactExtensionQuotientBounds

end KahlerForm
