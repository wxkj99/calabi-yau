module

public import CalabiYau.Geometry.Complex.Holder
public import Mathlib.Analysis.Matrix.Normed
import CalabiYau.MongeAmpere.Continuity.Openness.SmoothBootstrap.DifferenceQuotientBounds.HolderProducts
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section
open scoped NNReal Topology
open Set Matrix
namespace KahlerForm

theorem holderBoundOn_zero_of_localHolderOnWith
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set E}
    {α C : ℝ≥0} {f : E → F}
    (hf : HolderOnWith C α f K) (hBound : ∀ x ∈ K, ‖f x‖ ≤ C) :
    HolderBoundOn 0 α C K f := by
  let L := continuousMultilinearCurryFin0 ℝ E F
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    simpa [norm_iteratedFDeriv_zero] using hBound x hx
  · intro x hx y hy
    rw [iteratedFDeriv_zero_eq_comp]
    change edist (L.symm (f x)) (L.symm (f y)) ≤ _
    rw [L.symm.edist_map]
    exact hf x hx y hy

/-- A local `C^{0,α}` coefficient bound on a compact translated neighborhood gives a uniform
`C^{0,α}` bound for every segment interpolation. Only the inclusion of all small translates in `K'`
and the entrywise Holder bounds on `K'` are used; this lemma makes no forcing-term claim. -/
theorem holderBoundOn_affineTranslatedMatrix
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α C : ℝ≥0} (K K' : Set E)
    (B : E → Matrix (Fin n) (Fin n) ℂ)
    (hB : ∀ i j, HolderBoundOn 0 α C K' (fun z ↦ B z i j))
    (hBase : K ⊆ K') (v : E) (δ : ℝ) (_hδ : 0 < δ)
    (hTranslate : ∀ h : ℝ, |h| < δ → ∀ z ∈ K, z + h • v ∈ K') :
    ∀ h : ℝ, |h| < δ → ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i j,
      HolderBoundOn 0 α (3 * C) K
        (fun z ↦ (B z + s • (B (z + h • v) - B z)) i j) := by
  intro h hh s hs i j
  let f₀ : E → ℂ := fun z ↦ B z i j
  let f₁ : E → ℂ := fun z ↦ B (z + h • v) i j
  have hf₀Bound (z : E) (hz : z ∈ K) : ‖f₀ z‖ ≤ (C : ℝ) := by
    have hb := (hB i j).1 0 le_rfl z (hBase hz)
    simpa [f₀, norm_iteratedFDeriv_zero] using hb
  have hf₁Bound (z : E) (hz : z ∈ K) : ‖f₁ z‖ ≤ (C : ℝ) := by
    have hb := (hB i j).1 0 le_rfl (z + h • v) (hTranslate h hh z hz)
    simpa [f₁, norm_iteratedFDeriv_zero] using hb
  let L := continuousMultilinearCurryFin0 ℝ E ℂ
  have hf₀Holder : HolderOnWith C α f₀ K := by
    intro x hx y hy
    have hb := (hB i j).2 x (hBase hx) y (hBase hy)
    rw [iteratedFDeriv_zero_eq_comp] at hb
    change edist (L.symm (f₀ x)) (L.symm (f₀ y)) ≤ _ at hb
    rw [L.symm.edist_map] at hb
    exact hb
  have hf₁Holder : HolderOnWith C α f₁ K := by
    intro x hx y hy
    have hb := (hB i j).2 (x + h • v) (hTranslate h hh x hx)
      (y + h • v) (hTranslate h hh y hy)
    rw [iteratedFDeriv_zero_eq_comp] at hb
    change edist (L.symm (B (x + h • v) i j))
      (L.symm (B (y + h • v) i j)) ≤ _ at hb
    rw [L.symm.edist_map] at hb
    simpa [f₁, edist_add_right] using hb
  have hDiff : HolderOnWith (2 * C) α (fun z ↦ f₁ z - f₀ z) K := by
    intro x hx y hy
    calc
      edist (f₁ x - f₀ x) (f₁ y - f₀ y) =
          edist (f₁ x + -f₀ x) (f₁ y + -f₀ y) := by rfl
      _ ≤ edist (f₁ x) (f₁ y) + edist (-f₀ x) (-f₀ y) :=
        edist_add_add_le _ _ _ _
      _ = edist (f₁ x) (f₁ y) + edist (f₀ x) (f₀ y) := by rw [edist_neg_neg]
      _ ≤ (C : ENNReal) * edist x y ^ (α : ℝ) +
          (C : ENNReal) * edist x y ^ (α : ℝ) :=
        add_le_add (hf₁Holder x hx y hy) (hf₀Holder x hx y hy)
      _ = ((2 * C : ℝ≥0) : ENNReal) * edist x y ^ (α : ℝ) := by
        simp only [ENNReal.coe_mul, ENNReal.coe_ofNat]
        ring
  have hsNormR : ‖s‖ ≤ 1 := by
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
  have hsNorm : ‖s‖₊ ≤ 1 := by exact_mod_cast hsNormR
  have hScaled : HolderOnWith (2 * C) α
      (fun z ↦ s • (f₁ z - f₀ z)) K := by
    intro x hx y hy
    calc
      edist (s • (f₁ x - f₀ x)) (s • (f₁ y - f₀ y)) ≤
          (‖s‖₊ : ENNReal) * edist (f₁ x - f₀ x) (f₁ y - f₀ y) :=
        edist_smul_le _ _ _
      _ ≤ (1 : ENNReal) * ((2 * C : ℝ≥0) : ENNReal) *
          edist x y ^ (α : ℝ) := by
        calc
          _ ≤ (1 : ENNReal) * edist (f₁ x - f₀ x) (f₁ y - f₀ y) := by
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hsNorm) (by positivity)
          _ ≤ (1 : ENNReal) * ((2 * C : ℝ≥0) : ENNReal) *
              edist x y ^ (α : ℝ) := by
            simpa using hDiff x hx y hy
      _ = ((2 * C : ℝ≥0) : ENNReal) * edist x y ^ (α : ℝ) := by ring
  have hResult : HolderOnWith (3 * C) α
      (fun z ↦ f₀ z + s • (f₁ z - f₀ z)) K := by
    intro x hx y hy
    calc
      edist (f₀ x + s • (f₁ x - f₀ x)) (f₀ y + s • (f₁ y - f₀ y)) ≤
          edist (f₀ x) (f₀ y) + edist (s • (f₁ x - f₀ x))
            (s • (f₁ y - f₀ y)) := edist_add_add_le _ _ _ _
      _ ≤ (C : ENNReal) * edist x y ^ (α : ℝ) +
          ((2 * C : ℝ≥0) : ENNReal) * edist x y ^ (α : ℝ) :=
        add_le_add (hf₀Holder x hx y hy) (hScaled x hx y hy)
      _ = ((3 * C : ℝ≥0) : ENNReal) * edist x y ^ (α : ℝ) := by
        simp only [ENNReal.coe_mul, ENNReal.coe_ofNat]
        ring
  have hResultBound (z : E) (hz : z ∈ K) :
      ‖f₀ z + s • (f₁ z - f₀ z)‖ ≤ (3 * C : ℝ) := by
    calc
      ‖f₀ z + s • (f₁ z - f₀ z)‖ ≤ ‖f₀ z‖ + ‖s • (f₁ z - f₀ z)‖ := norm_add_le _ _
      _ = ‖f₀ z‖ + ‖s‖ * ‖f₁ z - f₀ z‖ := by rw [norm_smul]
      _ ≤ ‖f₀ z‖ + ‖s‖ * (‖f₁ z‖ + ‖f₀ z‖) := by
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _))
      _ ≤ C + 1 * (C + C) := by
        have hs' : ‖s‖ ≤ 1 := hsNormR
        have hf₁ := hf₁Bound z hz
        have hf₀ := hf₀Bound z hz
        nlinarith [norm_nonneg (f₀ z), norm_nonneg (f₁ z)]
      _ = (3 * C : ℝ) := by ring
  simpa [f₀, f₁, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply] using
    (holderBoundOn_zero_of_localHolderOnWith hResult hResultBound)

open scoped Matrix.Norms.Elementwise in
theorem holderBoundOn_zero_matrix_of_entrywise
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {K : Set E} {α C : ℝ≥0}
    (A : E → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, HolderBoundOn 0 α C K (fun z ↦ A z i j)) :
    HolderBoundOn 0 α C K A := by
  let : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) :=
    Matrix.normedAddCommGroup
  let : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    Matrix.normedSpace
  have hHolder : HolderOnWith C α A K := by
    intro x hx y hy
    have hEntry (i j : Fin n) : ‖A x i j - A y i j‖ ≤
        (C : ℝ) * dist x y ^ (α : ℝ) := by
      have h := ((CalabiYau.Schauder.holderBoundOn_zero_iff.mp (hA i j)).2).dist_le hx hy
      simpa only [dist_eq_norm, norm_sub_rev] using h
    have hnorm : ‖A x - A y‖ ≤ (C : ℝ) * dist x y ^ (α : ℝ) := by
      apply (Matrix.norm_le_iff (by positivity)).2
      intro i j
      simpa only [Matrix.sub_apply] using hEntry i j
    rw [edist_dist]
    calc
      ENNReal.ofReal (dist (A x) (A y)) ≤
          ENNReal.ofReal ((C : ℝ) * dist x y ^ (α : ℝ)) :=
        ENNReal.ofReal_le_ofReal (by simpa only [dist_eq_norm] using hnorm)
      _ = (C : ENNReal) * edist x y ^ (α : ℝ) := by
        rw [ENNReal.ofReal_mul (by positivity)]
        simp only [ENNReal.ofReal_coe_nnreal,
          ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
          edist_dist]
  have hBound (z : E) (hz : z ∈ K) : ‖A z‖ ≤ (C : ℝ) := by
    apply (Matrix.norm_le_iff (by positivity)).2
    intro i j
    simpa only [norm_iteratedFDeriv_zero] using (hA i j).1 0 le_rfl z hz
  exact holderBoundOn_zero_of_localHolderOnWith hHolder hBound

end KahlerForm
