module

import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import CalabiYau.Geometry.Complex.Schauder.OperatorCommutator
public import CalabiYau.Geometry.Complex.Schauder.DerivativeHolder

/-!
# Hölder estimates for matrix trace products

This theorem gives the iterated Leibniz estimate for the mixed-index trace contraction on a
convex localization.
-/

@[expose] public section

open Set Matrix
open scoped NNReal

namespace CalabiYau.Schauder

/-- The next iterated derivative of a bilinear product is the right-curried derivative of the
sum of the two first-order product-rule terms. -/
private theorem iteratedFDerivWithin_bilinear_succ_formula
    {E A B C : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    {k : ℕ} {V : Set E} {x : E} {f : E → A} {g : E → B}
    (L : A →L[ℝ] B →L[ℝ] C)
    (hf : ContDiffOn ℝ (k + 1) f V) (hg : ContDiffOn ℝ (k + 1) g V)
    (hV : UniqueDiffOn ℝ V) (hx : x ∈ V) :
    iteratedFDerivWithin ℝ (k + 1) (fun y ↦ L (f y) (g y)) V x =
      (continuousMultilinearCurryRightEquiv' ℝ k E C).symm
        (iteratedFDerivWithin ℝ k
          (fun y ↦ L.precompR E (f y) (fderivWithin ℝ g V y) +
            L.precompL E (fderivWithin ℝ f V y) (g y)) V x) := by
  rw [iteratedFDerivWithin_succ_eq_comp_right hV hx]
  have hEq : ∀ y ∈ V,
      fderivWithin ℝ (fun y ↦ L (f y) (g y)) V y =
        L.precompR E (f y) (fderivWithin ℝ g V y) +
          L.precompL E (fderivWithin ℝ f V y) (g y) := by
    intro y hy
    exact L.fderivWithin_of_bilinear
      (hf.differentiableOn (by positivity) y hy)
      (hg.differentiableOn (by positivity) y hy) (hV y hy)
  exact congrArg (continuousMultilinearCurryRightEquiv' ℝ k E C).symm
    (iteratedFDerivWithin_congr (𝕜 := ℝ) hEq hx k)

/-- On an open convex set, each strictly lower jet inherits an `α`-Hölder bound from the
uniform derivative bounds, by using Lipschitz control at short distances and the supremum bound
at long distances. -/
private theorem holderOnWith_lower_jet_convex
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k r : ℕ} {α C : ℝ≥0} {V : Set E} {f : E → F}
    (hα₀ : 0 < α) (hα₁ : α < 1)
    (hV : IsOpen V) (hVconvex : Convex ℝ V)
    (hf : ContDiffOn ℝ k f V) (hb : HolderBoundOn k α C V f)
    (hr : r < k) :
    HolderOnWith (2 * C) α (iteratedFDeriv ℝ r f) V := by
  let J : E → E [×r]→L[ℝ] F := fun x ↦ iteratedFDeriv ℝ r f x
  have hrl : r + 1 ≤ k := Nat.succ_le_of_lt hr
  have hrWithTop : (r : WithTop ℕ∞) < (k : WithTop ℕ∞) := by
    exact_mod_cast hr
  have hdiff (x : E) (hx : x ∈ V) : DifferentiableAt ℝ J x := by
    exact (hf.contDiffAt (hV.mem_nhds hx)).differentiableAt_iteratedFDeriv hrWithTop
  have hderiv (x : E) (hx : x ∈ V) : ‖fderiv ℝ J x‖ ≤ (C : ℝ) := by
    rw [norm_fderiv_iteratedFDeriv]
    exact hb.1 (r + 1) hrl x hx
  have hLip : LipschitzOnWith C J V :=
    hVconvex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ) hdiff hderiv
  intro x hx y hy
  by_cases hxy : dist x y ≤ 1
  · let P : Set E := {x, y}
    have hPV : P ⊆ V := by
      intro z hz
      simp only [P, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hx
      · exact hy
    have hPdiam : ∀ a ∈ P, ∀ b ∈ P, edist a b ≤ 1 := by
      intro a ha b hb
      simp only [P, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · simp
      · rw [edist_dist]
        simpa using ENNReal.ofReal_le_ofReal hxy
      · have hab : dist a b ≤ 1 := by simpa [dist_comm] using hxy
        rw [edist_dist]
        simpa using ENNReal.ofReal_le_ofReal hab
      · simp
    have hsmall := (hLip.holderOnWith.mono hPV).of_le hPdiam (by exact_mod_cast (le_of_lt hα₁))
    have hxySmall := hsmall x (by simp [P]) y (by simp [P])
    have hcoeff : C ≤ 2 * C := by
      rw [two_mul]
      exact le_add_of_nonneg_right (show 0 ≤ C from bot_le)
    calc
      edist (J x) (J y) ≤ (C : ENNReal) * edist x y ^ (α : ℝ) := by
        simpa using hxySmall
      _ ≤ ((2 * C : ℝ≥0) : ENNReal) * edist x y ^ (α : ℝ) := by
        gcongr
  · have hfar : 1 ≤ dist x y := le_of_not_ge hxy
    have hdist : dist (J x) (J y) ≤ (2 * C : ℝ) := by
      calc
        dist (J x) (J y) ≤ ‖J x‖ + ‖J y‖ := dist_le_norm_add_norm _ _
        _ ≤ (C : ℝ) + C := add_le_add (hb.1 r (Nat.le_of_lt hr) x hx)
          (hb.1 r (Nat.le_of_lt hr) y hy)
        _ = (2 * C : ℝ) := by ring
    have hxyE : (1 : ENNReal) ≤ edist x y := by
      rw [edist_dist]
      simpa using ENNReal.ofReal_le_ofReal hfar
    have hαReal : (0 : ℝ) < (α : ℝ) := by exact_mod_cast hα₀
    have hpow : (1 : ENNReal) ≤ edist x y ^ (α : ℝ) :=
      ENNReal.one_le_rpow hxyE hαReal
    calc
      edist (J x) (J y) = ENNReal.ofReal (dist (J x) (J y)) := edist_dist _ _
      _ ≤ ENNReal.ofReal (2 * (C : ℝ)) := ENNReal.ofReal_le_ofReal hdist
      _ = ((2 * C : ℝ≥0) : ENNReal) := by simp
      _ ≤ ((2 * C : ℝ≥0) : ENNReal) * edist x y ^ (α : ℝ) :=
        le_mul_of_one_le_right (by positivity) hpow

universe u

/-- The difference of the `k`-th jet of a bilinear product is bounded by the binomially weighted
sum of the differences of the two input jets. -/
private theorem bilinear_jet_difference_bound
    {E A B C : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    {k : ℕ} {V : Set E} {x y : E}
    (L : A →L[ℝ] B →L[ℝ] C)
    {f : E → A} {g : E → B}
    (hf : ContDiffOn ℝ k f V) (hg : ContDiffOn ℝ k g V)
    (hV : UniqueDiffOn ℝ V) (hx : x ∈ V) (hy : y ∈ V) :
    ‖iteratedFDerivWithin ℝ k (fun z ↦ L (f z) (g z)) V x -
      iteratedFDerivWithin ℝ k (fun z ↦ L (f z) (g z)) V y‖ ≤
      ‖L‖ * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        (‖iteratedFDerivWithin ℝ i f V x‖ *
            ‖iteratedFDerivWithin ℝ (k - i) g V x -
              iteratedFDerivWithin ℝ (k - i) g V y‖ +
          ‖iteratedFDerivWithin ℝ i f V x - iteratedFDerivWithin ℝ i f V y‖ *
            ‖iteratedFDerivWithin ℝ (k - i) g V y‖) := by
  induction k generalizing E A B C L f g V x y with
  | zero =>
      have hdecomp : L (f x) (g x) - L (f y) (g y) =
          L (f x) (g x - g y) + L (f x - f y) (g y) := by
        simp [map_sub]
      have hbasic : ‖L (f x) (g x) - L (f y) (g y)‖ ≤
          ‖L‖ * (‖f x‖ * ‖g x - g y‖ + ‖f x - f y‖ * ‖g y‖) := by
        rw [hdecomp]
        calc
          ‖L (f x) (g x - g y) + L (f x - f y) (g y)‖ ≤
              ‖L (f x) (g x - g y)‖ + ‖L (f x - f y) (g y)‖ := norm_add_le _ _
          _ ≤ ‖L‖ * ‖f x‖ * ‖g x - g y‖ +
              ‖L‖ * ‖f x - f y‖ * ‖g y‖ := by
            exact add_le_add (L.le_opNorm₂ _ _) (L.le_opNorm₂ _ _)
          _ = _ := by ring
      have hbasic' : dist (L (f x) (g x)) (L (f y) (g y)) ≤
          ‖L‖ * (‖f x‖ * dist (g x) (g y) + dist (f x) (f y) * ‖g y‖) := by
        simpa [dist_eq_norm] using hbasic
      have hprod : ‖iteratedFDerivWithin ℝ 0 (fun z ↦ L (f z) (g z)) V x -
          iteratedFDerivWithin ℝ 0 (fun z ↦ L (f z) (g z)) V y‖ =
          ‖L (f x) (g x) - L (f y) (g y)‖ := by
        rw [← dist_eq_norm, dist_iteratedFDerivWithin_zero, dist_eq_norm]
      have hfdiff : ‖iteratedFDerivWithin ℝ 0 f V x -
          iteratedFDerivWithin ℝ 0 f V y‖ = ‖f x - f y‖ := by
        rw [← dist_eq_norm, dist_iteratedFDerivWithin_zero, dist_eq_norm]
      have hgd : ‖iteratedFDerivWithin ℝ 0 g V x‖ = ‖g x‖ := by
        exact norm_iteratedFDerivWithin_zero
      have hgdif : ‖iteratedFDerivWithin ℝ 0 g V x -
          iteratedFDerivWithin ℝ 0 g V y‖ = ‖g x - g y‖ := by
        rw [← dist_eq_norm, dist_iteratedFDerivWithin_zero, dist_eq_norm]
      have hfn : ‖iteratedFDerivWithin ℝ 0 f V x‖ = ‖f x‖ := by
        exact norm_iteratedFDerivWithin_zero
      have hbasic'' : ‖L (f x) (g x) - L (f y) (g y)‖ ≤
          ‖L‖ * (‖f x‖ * ‖g x - g y‖ + ‖f x - f y‖ * ‖g y‖) := by
        simpa [dist_eq_norm] using hbasic'
      simpa [Finset.sum_range_one, hprod, hfdiff, hgd, hgdif, hfn] using hbasic''
  | succ k ih =>
      let p : E → E →L[ℝ] C := fun z =>
        L.precompR E (f z) (fderivWithin ℝ g V z)
      let q : E → E →L[ℝ] C := fun z =>
        L.precompL E (fderivWithin ℝ f V z) (g z)
      have hf' : ContDiffOn ℝ k f V := hf.of_le (by exact_mod_cast Nat.le_succ k)
      have hg' : ContDiffOn ℝ k g V := hg.of_le (by exact_mod_cast Nat.le_succ k)
      have hdfg : ContDiffOn ℝ k (fderivWithin ℝ g V) V :=
        hg.fderivWithin hV (by simp)
      have hdf : ContDiffOn ℝ k (fderivWithin ℝ f V) V :=
        hf.fderivWithin hV (by simp)
      have hp : ContDiffOn ℝ k p V := by
        exact (L.precompR E).isBoundedBilinearMap.contDiff.comp₂_contDiffOn hf' hdfg
      have hq : ContDiffOn ℝ k q V := by
        exact (L.precompL E).isBoundedBilinearMap.contDiff.comp₂_contDiffOn hdf hg'
      have hpBound := ih (L.precompR E) (f := f)
        (g := fun z => fderivWithin ℝ g V z) hf' hdfg hV hx hy
      have hqBound := ih (L.precompL E) (f := fun z => fderivWithin ℝ f V z)
        (g := g) hdf hg' hV hx hy
      have hformula (z : E) (hz : z ∈ V) :
          iteratedFDerivWithin ℝ (k + 1) (fun w => L (f w) (g w)) V z =
            (continuousMultilinearCurryRightEquiv' ℝ k E C).symm
              (iteratedFDerivWithin ℝ k (fun w => p w + q w) V z) := by
        simpa [p, q] using iteratedFDerivWithin_bilinear_succ_formula
          (k := k) L hf hg hV hz
      have hsum (z : E) (hz : z ∈ V) :
          iteratedFDerivWithin ℝ k (fun w => p w + q w) V z =
            iteratedFDerivWithin ℝ k p V z + iteratedFDerivWithin ℝ k q V z := by
        exact fun_iteratedFDerivWithin_add_apply (hp.contDiffWithinAt hz)
          (hq.contDiffWithinAt hz) hV hz
      have hjetEq :
          ‖iteratedFDerivWithin ℝ (k + 1) (fun z => L (f z) (g z)) V x -
            iteratedFDerivWithin ℝ (k + 1) (fun z => L (f z) (g z)) V y‖ =
            ‖iteratedFDerivWithin ℝ k p V x - iteratedFDerivWithin ℝ k p V y +
              (iteratedFDerivWithin ℝ k q V x - iteratedFDerivWithin ℝ k q V y)‖ := by
        rw [hformula x hx, hformula y hy, hsum x hx, hsum y hy]
        rw [← map_sub]
        rw [LinearIsometryEquiv.norm_map]
        congr 1
        abel
      have hfgJet (r : ℕ) (z : E) (hz : z ∈ V) :
          iteratedFDerivWithin ℝ r (fderivWithin ℝ g V) V z =
            (continuousMultilinearCurryRightEquiv' ℝ r E B)
              (iteratedFDerivWithin ℝ (r + 1) g V z) := by
        have h := iteratedFDerivWithin_succ_eq_comp_right (𝕜 := ℝ) (f := g)
          (s := V) (x := z) (n := r) hV hz
        simpa [Function.comp_apply] using
          (congrArg (continuousMultilinearCurryRightEquiv' ℝ r E B) h).symm
      have hffJet (r : ℕ) (z : E) (hz : z ∈ V) :
          iteratedFDerivWithin ℝ r (fderivWithin ℝ f V) V z =
            (continuousMultilinearCurryRightEquiv' ℝ r E A)
              (iteratedFDerivWithin ℝ (r + 1) f V z) := by
        have h := iteratedFDerivWithin_succ_eq_comp_right (𝕜 := ℝ) (f := f)
          (s := V) (x := z) (n := r) hV hz
        simpa [Function.comp_apply] using
          (congrArg (continuousMultilinearCurryRightEquiv' ℝ r E A) h).symm
      have hfgDiff (r : ℕ) :
          ‖iteratedFDerivWithin ℝ r (fderivWithin ℝ g V) V x -
            iteratedFDerivWithin ℝ r (fderivWithin ℝ g V) V y‖ =
          ‖iteratedFDerivWithin ℝ (r + 1) g V x -
            iteratedFDerivWithin ℝ (r + 1) g V y‖ := by
        rw [hfgJet r x hx, hfgJet r y hy, ← map_sub, LinearIsometryEquiv.norm_map]
      have hffDiff (r : ℕ) :
          ‖iteratedFDerivWithin ℝ r (fderivWithin ℝ f V) V x -
            iteratedFDerivWithin ℝ r (fderivWithin ℝ f V) V y‖ =
          ‖iteratedFDerivWithin ℝ (r + 1) f V x -
            iteratedFDerivWithin ℝ (r + 1) f V y‖ := by
        rw [hffJet r x hx, hffJet r y hy, ← map_sub, LinearIsometryEquiv.norm_map]
      have hfgNorm (r : ℕ) (z : E) (hz : z ∈ V) :
          ‖iteratedFDerivWithin ℝ r (fderivWithin ℝ g V) V z‖ =
            ‖iteratedFDerivWithin ℝ (r + 1) g V z‖ :=
        norm_iteratedFDerivWithin_fderivWithin hV hz
      have hffNorm (r : ℕ) (z : E) (hz : z ∈ V) :
          ‖iteratedFDerivWithin ℝ r (fderivWithin ℝ f V) V z‖ =
            ‖iteratedFDerivWithin ℝ (r + 1) f V z‖ :=
        norm_iteratedFDerivWithin_fderivWithin hV hz
      let Φ : ℕ → ℕ → ℝ := fun i j =>
        ‖iteratedFDerivWithin ℝ i f V x‖ *
            ‖iteratedFDerivWithin ℝ j g V x - iteratedFDerivWithin ℝ j g V y‖ +
          ‖iteratedFDerivWithin ℝ i f V x - iteratedFDerivWithin ℝ i f V y‖ *
            ‖iteratedFDerivWithin ℝ j g V y‖
      have hpSumEq :
          (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
            (‖iteratedFDerivWithin ℝ i f V x‖ *
                ‖iteratedFDerivWithin ℝ (k - i) (fderivWithin ℝ g V) V x -
                  iteratedFDerivWithin ℝ (k - i) (fderivWithin ℝ g V) V y‖ +
              ‖iteratedFDerivWithin ℝ i f V x - iteratedFDerivWithin ℝ i f V y‖ *
                ‖iteratedFDerivWithin ℝ (k - i) (fderivWithin ℝ g V) V y‖)) =
          ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Φ i (k + 1 - i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Nat.succ_sub (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)),
          hfgDiff (k - i), hfgNorm (k - i) y hy]
      have hqSumEq :
          (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
            (‖iteratedFDerivWithin ℝ i (fderivWithin ℝ f V) V x‖ *
                ‖iteratedFDerivWithin ℝ (k - i) g V x -
                  iteratedFDerivWithin ℝ (k - i) g V y‖ +
              ‖iteratedFDerivWithin ℝ i (fderivWithin ℝ f V) V x -
                iteratedFDerivWithin ℝ i (fderivWithin ℝ f V) V y‖ *
                ‖iteratedFDerivWithin ℝ (k - i) g V y‖)) =
          ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Φ (i + 1) (k - i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hffNorm i x hx, hffDiff i]
      have hpEstimate :
          ‖iteratedFDerivWithin ℝ k p V x - iteratedFDerivWithin ℝ k p V y‖ ≤
            ‖L‖ * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Φ i (k + 1 - i) := by
        calc
          _ ≤ ‖L.precompR E‖ * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
              (‖iteratedFDerivWithin ℝ i f V x‖ *
                  ‖iteratedFDerivWithin ℝ (k - i) (fderivWithin ℝ g V) V x -
                    iteratedFDerivWithin ℝ (k - i) (fderivWithin ℝ g V) V y‖ +
                ‖iteratedFDerivWithin ℝ i f V x - iteratedFDerivWithin ℝ i f V y‖ *
                  ‖iteratedFDerivWithin ℝ (k - i) (fderivWithin ℝ g V) V y‖) := hpBound
          _ ≤ ‖L‖ * _ := by
            rw [hpSumEq]
            exact mul_le_mul_of_nonneg_right (L.norm_precompR_le E) (by positivity)
      have hqEstimate :
          ‖iteratedFDerivWithin ℝ k q V x - iteratedFDerivWithin ℝ k q V y‖ ≤
            ‖L‖ * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Φ (i + 1) (k - i) := by
        calc
          _ ≤ ‖L.precompL E‖ * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
              (‖iteratedFDerivWithin ℝ i (fderivWithin ℝ f V) V x‖ *
                  ‖iteratedFDerivWithin ℝ (k - i) g V x -
                    iteratedFDerivWithin ℝ (k - i) g V y‖ +
                ‖iteratedFDerivWithin ℝ i (fderivWithin ℝ f V) V x -
                  iteratedFDerivWithin ℝ i (fderivWithin ℝ f V) V y‖ *
                  ‖iteratedFDerivWithin ℝ (k - i) g V y‖) := hqBound
          _ ≤ ‖L‖ * _ := by
            rw [hqSumEq]
            exact mul_le_mul_of_nonneg_right (L.norm_precompL_le E) (by positivity)
      have hchoose :
          (∑ i ∈ Finset.range (k + 2), ((k + 1).choose i : ℝ) * Φ i (k + 1 - i)) =
            (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Φ i (k + 1 - i)) +
              ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Φ (i + 1) (k - i) :=
        Finset.sum_choose_succ_mul Φ k
      rw [hjetEq]
      calc
        _ ≤ ‖iteratedFDerivWithin ℝ k p V x - iteratedFDerivWithin ℝ k p V y‖ +
            ‖iteratedFDerivWithin ℝ k q V x - iteratedFDerivWithin ℝ k q V y‖ := norm_add_le _ _
        _ ≤ ‖L‖ * (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Φ i (k + 1 - i)) +
              ‖L‖ * (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Φ (i + 1) (k - i)) :=
              add_le_add hpEstimate hqEstimate
        _ = ‖L‖ * (∑ i ∈ Finset.range (k + 2), ((k + 1).choose i : ℝ) * Φ i (k + 1 - i)) := by
              rw [← mul_add, ← hchoose]

/-- The top product jet is Hölder: expand its difference by the iterated Leibniz rule, use the
input top-jet Hölder bounds, and interpolate lower jets along convex segments. -/
private theorem holderOnWith_complex_mul_topJet_convex
    {E : Type 0} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} {α CF CG : ℝ≥0} {V : Set E}
    (hα₀ : 0 < α) (hα₁ : α < 1)
    (hV : IsOpen V) (hVconvex : Convex ℝ V)
    (f g : E → ℂ)
    (hf : ContDiffOn ℝ k f V ∧ HolderBoundOn k α CF V f)
    (hg : ContDiffOn ℝ k g V ∧ HolderBoundOn k α CG V g) :
    HolderOnWith (4 * (2 : ℝ≥0) ^ k * CF * CG) α
      (iteratedFDeriv ℝ k (fun x ↦ f x * g x)) V := by
  let B : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ
  have hB : ‖B‖ ≤ 1 := by exact ContinuousLinearMap.opNorm_mul_le _ _
  have hFJetHolder (r : ℕ) (hr : r ≤ k) :
      HolderOnWith (2 * CF) α (iteratedFDeriv ℝ r f) V := by
    by_cases heq : r = k
    · subst r
      apply hf.2.2.mono_const
      rw [two_mul]
      exact le_add_of_nonneg_right (show 0 ≤ CF from bot_le)
    · have hlt : r < k := Nat.lt_of_le_of_ne hr heq
      exact holderOnWith_lower_jet_convex hα₀ hα₁ hV hVconvex hf.1 hf.2 hlt
  have hGJetHolder (r : ℕ) (hr : r ≤ k) :
      HolderOnWith (2 * CG) α (iteratedFDeriv ℝ r g) V := by
    by_cases heq : r = k
    · subst r
      apply hg.2.2.mono_const
      rw [two_mul]
      exact le_add_of_nonneg_right (show 0 ≤ CG from bot_le)
    · have hlt : r < k := Nat.lt_of_le_of_ne hr heq
      exact holderOnWith_lower_jet_convex hα₀ hα₁ hV hVconvex hg.1 hg.2 hlt
  have hFjetNorm (r : ℕ) (hr : r ≤ k) (z : E) (hz : z ∈ V) :
      ‖iteratedFDerivWithin ℝ r f V z‖ ≤ (CF : ℝ) := by
    have hAt : ContDiffAt ℝ r f z :=
      (hf.1.contDiffAt (hV.mem_nhds hz)).of_le (by exact_mod_cast hr)
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hV.uniqueDiffOn hAt hz]
    exact hf.2.1 r hr z hz
  have hGjetNorm (r : ℕ) (hr : r ≤ k) (z : E) (hz : z ∈ V) :
      ‖iteratedFDerivWithin ℝ r g V z‖ ≤ (CG : ℝ) := by
    have hAt : ContDiffAt ℝ r g z :=
      (hg.1.contDiffAt (hV.mem_nhds hz)).of_le (by exact_mod_cast hr)
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hV.uniqueDiffOn hAt hz]
    exact hg.2.1 r hr z hz
  have hFjetDiff (r : ℕ) (hr : r ≤ k) (x : E) (hx : x ∈ V)
      (y : E) (hy : y ∈ V) :
      ‖iteratedFDerivWithin ℝ r f V x - iteratedFDerivWithin ℝ r f V y‖ ≤
        (2 * (CF : ℝ)) * dist x y ^ (α : ℝ) := by
    have h := (hFJetHolder r hr).dist_le hx hy
    have hAtx : ContDiffAt ℝ r f x :=
      (hf.1.contDiffAt (hV.mem_nhds hx)).of_le (by exact_mod_cast hr)
    have hAty : ContDiffAt ℝ r f y :=
      (hf.1.contDiffAt (hV.mem_nhds hy)).of_le (by exact_mod_cast hr)
    have hxEq := iteratedFDerivWithin_eq_iteratedFDeriv hV.uniqueDiffOn hAtx hx
    have hyEq := iteratedFDerivWithin_eq_iteratedFDeriv hV.uniqueDiffOn hAty hy
    calc
      ‖iteratedFDerivWithin ℝ r f V x - iteratedFDerivWithin ℝ r f V y‖ =
          dist (iteratedFDerivWithin ℝ r f V x) (iteratedFDerivWithin ℝ r f V y) :=
        (dist_eq_norm _ _).symm
      _ = dist (iteratedFDeriv ℝ r f x) (iteratedFDeriv ℝ r f y) := by rw [hxEq, hyEq]
      _ ≤ (2 * (CF : ℝ)) * dist x y ^ (α : ℝ) := h
  have hGjetDiff (r : ℕ) (hr : r ≤ k) (x : E) (hx : x ∈ V)
      (y : E) (hy : y ∈ V) :
      ‖iteratedFDerivWithin ℝ r g V x - iteratedFDerivWithin ℝ r g V y‖ ≤
        (2 * (CG : ℝ)) * dist x y ^ (α : ℝ) := by
    have h := (hGJetHolder r hr).dist_le hx hy
    have hAtx : ContDiffAt ℝ r g x :=
      (hg.1.contDiffAt (hV.mem_nhds hx)).of_le (by exact_mod_cast hr)
    have hAty : ContDiffAt ℝ r g y :=
      (hg.1.contDiffAt (hV.mem_nhds hy)).of_le (by exact_mod_cast hr)
    have hxEq := iteratedFDerivWithin_eq_iteratedFDeriv hV.uniqueDiffOn hAtx hx
    have hyEq := iteratedFDerivWithin_eq_iteratedFDeriv hV.uniqueDiffOn hAty hy
    calc
      ‖iteratedFDerivWithin ℝ r g V x - iteratedFDerivWithin ℝ r g V y‖ =
          dist (iteratedFDerivWithin ℝ r g V x) (iteratedFDerivWithin ℝ r g V y) :=
        (dist_eq_norm _ _).symm
      _ = dist (iteratedFDeriv ℝ r g x) (iteratedFDeriv ℝ r g y) := by rw [hxEq, hyEq]
      _ ≤ (2 * (CG : ℝ)) * dist x y ^ (α : ℝ) := h
  intro x hx y hy
  let p : ℝ := dist x y ^ (α : ℝ)
  let Φ : ℕ → ℕ → ℝ := fun i j =>
    ‖iteratedFDerivWithin ℝ i f V x‖ *
        ‖iteratedFDerivWithin ℝ j g V x - iteratedFDerivWithin ℝ j g V y‖ +
      ‖iteratedFDerivWithin ℝ i f V x - iteratedFDerivWithin ℝ i f V y‖ *
        ‖iteratedFDerivWithin ℝ j g V y‖
  have hPhi (i j : ℕ) (hi : i ≤ k) (hj : j ≤ k) :
      Φ i j ≤ (4 : ℝ) * (CF : ℝ) * (CG : ℝ) * p := by
    dsimp [Φ, p]
    have h₁ : ‖iteratedFDerivWithin ℝ i f V x‖ *
        ‖iteratedFDerivWithin ℝ j g V x - iteratedFDerivWithin ℝ j g V y‖ ≤
          (CF : ℝ) * (2 * (CG : ℝ) * dist x y ^ (α : ℝ)) := by
      calc
        _ ≤ (CF : ℝ) *
            ‖iteratedFDerivWithin ℝ j g V x - iteratedFDerivWithin ℝ j g V y‖ :=
          mul_le_mul_of_nonneg_right (hFjetNorm i hi x hx) (norm_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_left (hGjetDiff j hj x hx y hy) (by positivity)
    have h₂ : ‖iteratedFDerivWithin ℝ i f V x - iteratedFDerivWithin ℝ i f V y‖ *
        ‖iteratedFDerivWithin ℝ j g V y‖ ≤
          (2 * (CF : ℝ) * dist x y ^ (α : ℝ)) * (CG : ℝ) := by
      calc
        _ ≤ (2 * (CF : ℝ) * dist x y ^ (α : ℝ)) *
            ‖iteratedFDerivWithin ℝ j g V y‖ :=
          mul_le_mul_of_nonneg_right (hFjetDiff i hi x hx y hy) (norm_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_left (hGjetNorm j hj y hy) (by positivity)
    calc
      _ ≤ (CF : ℝ) * (2 * (CG : ℝ) * dist x y ^ (α : ℝ)) +
            (2 * (CF : ℝ) * dist x y ^ (α : ℝ)) * (CG : ℝ) := add_le_add h₁ h₂
      _ = (4 : ℝ) * (CF : ℝ) * (CG : ℝ) * dist x y ^ (α : ℝ) := by ring
  have hChoose : (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) = (2 : ℝ) ^ k := by
    exact_mod_cast Nat.sum_range_choose k
  have hsumBound :
      (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Φ i (k - i)) ≤
        (4 : ℝ) * (2 : ℝ) ^ k * (CF : ℝ) * (CG : ℝ) * p := by
    calc
      _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
            ((4 : ℝ) * (CF : ℝ) * (CG : ℝ) * p) := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left (hPhi i (k - i)
            (Nat.le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) (le_rfl))
            (Nat.sub_le k i)) (by positivity)
      _ = (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) *
            ((4 : ℝ) * (CF : ℝ) * (CG : ℝ) * p) := by rw [← Finset.sum_mul]
      _ = (4 : ℝ) * (2 : ℝ) ^ k * (CF : ℝ) * (CG : ℝ) * p := by rw [hChoose]; ring
  have hjet := bilinear_jet_difference_bound B hf.1 hg.1 hV.uniqueDiffOn hx hy
  have hprod : ContDiffOn ℝ k (fun z ↦ f z * g z) V := hf.1.mul hg.1
  have hAtx : ContDiffAt ℝ k (fun z ↦ f z * g z) x :=
    hprod.contDiffAt (hV.mem_nhds hx)
  have hAty : ContDiffAt ℝ k (fun z ↦ f z * g z) y :=
    hprod.contDiffAt (hV.mem_nhds hy)
  have hJetWithin :
      ‖iteratedFDerivWithin ℝ k (fun z ↦ f z * g z) V x -
          iteratedFDerivWithin ℝ k (fun z ↦ f z * g z) V y‖ ≤
        (4 : ℝ) * (2 : ℝ) ^ k * (CF : ℝ) * (CG : ℝ) * p := by
    calc
      _ ≤ ‖B‖ * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Φ i (k - i) := by
        simpa [B, Φ] using hjet
      _ ≤ 1 * ((4 : ℝ) * (2 : ℝ) ^ k * (CF : ℝ) * (CG : ℝ) * p) := by
        calc
          ‖B‖ * _ ≤ 1 * _ := mul_le_mul_of_nonneg_right hB (by positivity)
          _ ≤ 1 * _ := mul_le_mul_of_nonneg_left hsumBound (by norm_num)
      _ = (4 : ℝ) * (2 : ℝ) ^ k * (CF : ℝ) * (CG : ℝ) * p := by ring
  have hJetGlobal :
      ‖iteratedFDeriv ℝ k (fun z ↦ f z * g z) x -
          iteratedFDeriv ℝ k (fun z ↦ f z * g z) y‖ ≤
        (4 : ℝ) * (2 : ℝ) ^ k * (CF : ℝ) * (CG : ℝ) * p := by
    rw [← iteratedFDerivWithin_eq_iteratedFDeriv hV.uniqueDiffOn hAtx hx,
      ← iteratedFDerivWithin_eq_iteratedFDeriv hV.uniqueDiffOn hAty hy]
    exact hJetWithin
  have hConst : (4 : ℝ) * (2 : ℝ) ^ k * (CF : ℝ) * (CG : ℝ) =
      ((4 * (2 : ℝ≥0) ^ k * CF * CG : ℝ≥0) : ℝ) := by
    exact_mod_cast (show (4 : ℝ≥0) * (2 : ℝ≥0) ^ k * CF * CG =
      4 * (2 : ℝ≥0) ^ k * CF * CG by rfl)
  have hCoeff : ENNReal.ofReal ((4 : ℝ) * (2 : ℝ) ^ k * (CF : ℝ) * (CG : ℝ)) =
      ((4 * (2 : ℝ≥0) ^ k * CF * CG : ℝ≥0) : ENNReal) := by
    rw [hConst]
    exact ENNReal.ofReal_coe_nnreal
  rw [edist_dist]
  calc
    ENNReal.ofReal (dist (iteratedFDeriv ℝ k (fun z ↦ f z * g z) x)
        (iteratedFDeriv ℝ k (fun z ↦ f z * g z) y)) ≤
        ENNReal.ofReal ((4 : ℝ) * (2 : ℝ) ^ k * (CF : ℝ) * (CG : ℝ) * p) :=
      ENNReal.ofReal_le_ofReal (by simpa [dist_eq_norm, p] using hJetGlobal)
    _ = ((4 * (2 : ℝ≥0) ^ k * CF * CG : ℝ≥0) : ENNReal) *
        edist x y ^ (α : ℝ) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      rw [← ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) α.coe_nonneg, ← edist_dist]
      rw [hCoeff]

/-- Scalar multiplication preserves the quantitative `C^{k,α}` bound on a convex open set.
The mixed derivative terms are controlled by the binomial expansion, while the top-jet Hölder
seminorm is interpolated along convex segments for lower-order jets. -/
private theorem holderBoundOn_complex_mul_convex
    {E : Type 0} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} {α CF CG : ℝ≥0} {V : Set E}
    (hα₀ : 0 < α) (hα₁ : α < 1)
    (hV : IsOpen V) (hVconvex : Convex ℝ V)
    (f g : E → ℂ)
    (hf : ContDiffOn ℝ k f V ∧ HolderBoundOn k α CF V f)
    (hg : ContDiffOn ℝ k g V ∧ HolderBoundOn k α CG V g) :
    HolderBoundOn k α (4 * (2 : ℝ≥0) ^ k * CF * CG) V (fun x ↦ f x * g x) := by
  have hprod : ContDiffOn ℝ k (fun x ↦ f x * g x) V := hf.1.mul hg.1
  refine ⟨?_, ?_⟩
  · intro j hj z hz
    have hjk : j ≤ k := hj
    have hn : (j : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by exact_mod_cast hjk
    let B : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ
    have hwithin := B.norm_iteratedFDerivWithin_le_of_bilinear_of_le_one hf.1 hg.1
      hV.uniqueDiffOn hz hn (ContinuousLinearMap.opNorm_mul_le _ _)
    have hwithin' : ‖iteratedFDerivWithin ℝ j (fun y ↦ f y * g y) V z‖ ≤
        ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i f V z‖ *
          ‖iteratedFDerivWithin ℝ (j - i) g V z‖ := by
      simpa [B] using hwithin
    have hterm : ∀ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i f V z‖ *
          ‖iteratedFDerivWithin ℝ (j - i) g V z‖ ≤
        (j.choose i : ℝ) * (CF : ℝ) * (CG : ℝ) := by
      intro i hi
      have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hfiAt : ContDiffAt ℝ i f z :=
        (hf.1.contDiffAt (hV.mem_nhds hz)).of_le (by exact_mod_cast Nat.le_trans hij hjk)
      have hsub : ((j - i : ℕ) : WithTop ℕ∞) ≤ (j : WithTop ℕ∞) := by
        exact_mod_cast (Nat.sub_le j i)
      have hgiAt : ContDiffAt ℝ (j - i) g z :=
        (hg.1.contDiffAt (hV.mem_nhds hz)).of_le (hsub.trans hn)
      have hfi := hf.2.1 i (Nat.le_trans hij hjk) z hz
      have hgi := hg.2.1 (j - i) (Nat.le_trans (Nat.sub_le j i) hjk) z hz
      have hfi' := iteratedFDerivWithin_eq_iteratedFDeriv hV.uniqueDiffOn hfiAt hz
      have hgi' := iteratedFDerivWithin_eq_iteratedFDeriv hV.uniqueDiffOn hgiAt hz
      rw [hfi', hgi']
      gcongr
    have hsum := Finset.sum_le_sum hterm
    have hchoose : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = (2 : ℝ) ^ j := by
      exact_mod_cast Nat.sum_range_choose j
    have hfactor : (∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * (CF : ℝ) * (CG : ℝ)) =
        (2 : ℝ) ^ j * (CF : ℝ) * (CG : ℝ) := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, hchoose]
    have hpow : (2 : ℝ) ^ j ≤ 4 * (2 : ℝ) ^ k := by
      calc
        (2 : ℝ) ^ j ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hjk
        _ ≤ 4 * (2 : ℝ) ^ k := by
          have hp := pow_pos (by norm_num : (0 : ℝ) < 2) k
          nlinarith
    calc
      ‖iteratedFDeriv ℝ j (fun x ↦ f x * g x) z‖ =
          ‖iteratedFDerivWithin ℝ j (fun y ↦ f y * g y) V z‖ := by
            have hprodAt : ContDiffAt ℝ j (fun x ↦ f x * g x) z :=
              (hprod.contDiffAt (hV.mem_nhds hz)).of_le (by exact_mod_cast hjk)
            exact congrArg norm
              (iteratedFDerivWithin_eq_iteratedFDeriv hV.uniqueDiffOn hprodAt hz).symm
      _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
            ‖iteratedFDerivWithin ℝ i f V z‖ *
            ‖iteratedFDerivWithin ℝ (j - i) g V z‖ := hwithin'
      _ ≤ ∑ i ∈ Finset.range (j + 1),
            (j.choose i : ℝ) * (CF : ℝ) * (CG : ℝ) := hsum
      _ = (2 : ℝ) ^ j * (CF : ℝ) * (CG : ℝ) := hfactor
      _ ≤ (4 : ℝ) * (2 : ℝ) ^ k * (CF : ℝ) * (CG : ℝ) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hpow (by positivity)) (by positivity)
      _ = (4 * (2 : ℝ≥0) ^ k * CF * CG : ℝ) := by
            push_cast
            ring
  · exact holderOnWith_complex_mul_topJet_convex hα₀ hα₁ hV hVconvex f g hf hg

private theorem holderBoundOn_clm_comp_of_opNorm_le_one
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {V : Set E} {k : ℕ} {α C : ℝ≥0} {f : E → F}
    (hVopen : IsOpen V) (hcont : ContDiffOn ℝ k f V)
    (hf : HolderBoundOn k α C V f) (L : F →L[ℝ] G) (hL : ‖L‖ ≤ 1) :
    HolderBoundOn k α C V (L ∘ f) := by
  have hcontAt (x : E) (hx : x ∈ V) : ContDiffAt ℝ k f x :=
    hcont.contDiffAt (hVopen.mem_nhds hx)
  have hcomp (j : ℕ) (hj : j ≤ k) (x : E) (hx : x ∈ V) :
      iteratedFDeriv ℝ j (L ∘ f) x =
        L.compContinuousMultilinearMap (iteratedFDeriv ℝ j f x) :=
    L.iteratedFDeriv_comp_left (hcontAt x hx) (by exact_mod_cast hj)
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    rw [hcomp j hj x hx]
    calc
      ‖L.compContinuousMultilinearMap (iteratedFDeriv ℝ j f x)‖ ≤
          ‖L‖ * ‖iteratedFDeriv ℝ j f x‖ := L.norm_compContinuousMultilinearMap_le _
      _ ≤ 1 * C := mul_le_mul hL (hf.1 j hj x hx) (norm_nonneg _) (by positivity)
      _ = C := by simp
  · intro x hx y hy
    rw [hcomp k le_rfl x hx, hcomp k le_rfl y hy, edist_dist]
    have hmap :
        L.compContinuousMultilinearMap (iteratedFDeriv ℝ k f x) -
          L.compContinuousMultilinearMap (iteratedFDeriv ℝ k f y) =
        L.compContinuousMultilinearMap
          (iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k f y) := by
      ext m
      simp
    calc
      ENNReal.ofReal (dist
          (L.compContinuousMultilinearMap (iteratedFDeriv ℝ k f x))
          (L.compContinuousMultilinearMap (iteratedFDeriv ℝ k f y))) ≤
        ENNReal.ofReal (dist (iteratedFDeriv ℝ k f x) (iteratedFDeriv ℝ k f y)) := by
          apply ENNReal.ofReal_le_ofReal
          rw [dist_eq_norm, dist_eq_norm, hmap]
          calc
            ‖L.compContinuousMultilinearMap
                (iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k f y)‖ ≤
                ‖L‖ * ‖iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k f y‖ :=
              L.norm_compContinuousMultilinearMap_le _
            _ ≤ ‖iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k f y‖ :=
              mul_le_of_le_one_left (norm_nonneg _) hL
      _ = edist (iteratedFDeriv ℝ k f x) (iteratedFDeriv ℝ k f y) := (edist_dist _ _).symm
      _ ≤ (C : ENNReal) * edist x y ^ (α : ℝ) := hf.2 x hx y hy

private theorem holderBoundOn_finset_sum
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : Set E} {k : ℕ} {α C : ℝ≥0} (hVopen : IsOpen V)
    (t : Finset ι) (f : ι → E → F)
    (hf : ∀ i ∈ t, ContDiffOn ℝ k (f i) V ∧ HolderBoundOn k α C V (f i)) :
    HolderBoundOn k α ((t.card : ℝ≥0) * C) V (fun x ↦ ∑ i ∈ t, f i x) := by
  classical
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    have hderiv (i : ι) (hi : i ∈ t) : ContDiffAt ℝ j (f i) x :=
      ((hf i hi).1.contDiffAt (hVopen.mem_nhds hx)).of_le (by exact_mod_cast hj)
    have hsum := iteratedFDeriv_fun_sum_apply (u := t) (n := j) (x := x)
      (fun i hi => hderiv i hi)
    rw [hsum]
    calc
      ‖∑ i ∈ t, iteratedFDeriv ℝ j (f i) x‖ ≤
          ∑ i ∈ t, ‖iteratedFDeriv ℝ j (f i) x‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ t, (C : ℝ) := Finset.sum_le_sum fun i hi => (hf i hi).2.1 j hj x hx
      _ = ((t.card : ℝ≥0) * C : ℝ) := by simp [nsmul_eq_mul]
  · have hsum : HolderOnWith ((t.card : ℝ≥0) * C) α
        (fun x ↦ ∑ i ∈ t, iteratedFDeriv ℝ k (f i) x) V := by
      have h := holderOnWith_finset_sum t (fun _ => C)
        (fun i x => iteratedFDeriv ℝ k (f i) x)
        (fun i hi => (hf i hi).2.2)
      simpa using h
    have hderiv (i : ι) (hi : i ∈ t) (x : E) (hx : x ∈ V) : ContDiffAt ℝ k (f i) x :=
      (hf i hi).1.contDiffAt (hVopen.mem_nhds hx)
    have hsumEq (x : E) (hx : x ∈ V) :
        iteratedFDeriv ℝ k (fun y ↦ ∑ i ∈ t, f i y) x =
          ∑ i ∈ t, iteratedFDeriv ℝ k (f i) x := by
      exact iteratedFDeriv_fun_sum_apply (u := t) (n := k) (x := x)
        (fun i hi => hderiv i hi x hx)
    intro x hx y hy
    rw [hsumEq x hx, hsumEq y hy]
    exact hsum x hx y hy

/-- The real trace of a matrix product has a `C^{k,α}` bound bilinear in the entrywise bounds.
The constant depends only on the matrix size and derivative order. -/
theorem holderBoundOn_real_trace_product_convex
    {n k : ℕ} {α CF CG : ℝ≥0}
    (hα₀ : 0 < α) (hα₁ : α < 1)
    {V : Set (EuclideanSpace ℂ (Fin n))}
    (hV : IsOpen V) (hVconvex : Convex ℝ V)
    (F G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (hF : ∀ i j,
      ContDiffOn ℝ k (fun z ↦ F z i j) V ∧
        HolderBoundOn k α CF V (fun z ↦ F z i j))
    (hG : ∀ i j,
      ContDiffOn ℝ k (fun z ↦ G z i j) V ∧
        HolderBoundOn k α CG V (fun z ↦ G z i j)) :
    HolderBoundOn k α
      (8 * (2 : ℝ≥0) ^ k * (Fintype.card (Fin n × Fin n) : ℝ≥0) * CF * CG) V
      (fun z ↦ RCLike.re ((F z * G z).trace)) := by
  classical
  let t : Finset (Fin n × Fin n) := Finset.univ
  let D : ℝ≥0 := 4 * (2 : ℝ≥0) ^ k * CF * CG
  let q : Fin n × Fin n → EuclideanSpace ℂ (Fin n) → ℂ := fun p z =>
    F z p.1 p.2 * G z p.2 p.1
  have hq : ∀ p ∈ t, ContDiffOn ℝ k (q p) V ∧ HolderBoundOn k α D V (q p) := by
    intro p hp
    dsimp [q, D]
    exact ⟨(hF p.1 p.2).1.mul (hG p.2 p.1).1,
      (holderBoundOn_complex_mul_convex hα₀ hα₁ hV hVconvex
        (fun z ↦ F z p.1 p.2) (fun z ↦ G z p.2 p.1)
        (hF p.1 p.2) (hG p.2 p.1)).mono_const le_rfl⟩
  have hsum := holderBoundOn_finset_sum hV t q hq
  have hcontSum : ContDiffOn ℝ k
      (fun z ↦ ∑ p : Fin n × Fin n, q p z) V := by
    exact ContDiffOn.sum (by intro p hp; exact (hq p hp).1)
  have hreNorm : ‖(Complex.reCLM : ℂ →L[ℝ] ℝ)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro z
    simpa [Complex.reCLM_apply, Real.norm_eq_abs] using Complex.abs_re_le_norm z
  have hreal := holderBoundOn_clm_comp_of_opNorm_le_one hV hcontSum hsum
    Complex.reCLM hreNorm
  have hsmall : (t.card : ℝ≥0) * D ≤
      8 * (2 : ℝ≥0) ^ k * (Fintype.card (Fin n × Fin n) : ℝ≥0) * CF * CG := by
    dsimp [D, t]
    calc
      (Fintype.card (Fin n × Fin n) : ℝ≥0) *
          (4 * (2 : ℝ≥0) ^ k * CF * CG) =
          4 * (2 : ℝ≥0) ^ k * (Fintype.card (Fin n × Fin n) : ℝ≥0) * CF * CG := by ring
      _ ≤ 8 * (2 : ℝ≥0) ^ k * (Fintype.card (Fin n × Fin n) : ℝ≥0) * CF * CG := by
        gcongr
        norm_num
  have hreal' := hreal.mono_const hsmall
  have htrace (z : EuclideanSpace ℂ (Fin n)) :
      Matrix.trace (F z * G z) = ∑ p : Fin n × Fin n, q p z := by
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type, q]
  have hEq : (fun z ↦ Complex.reCLM (∑ p : Fin n × Fin n, q p z)) =
      (fun z ↦ RCLike.re ((F z * G z).trace)) := by
    funext z
    rw [htrace z]
    simp [Complex.reCLM_apply]
  rw [← hEq]
  exact hreal'

end CalabiYau.Schauder
