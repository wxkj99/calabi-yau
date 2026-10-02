module

public import CalabiYau.Geometry.Complex.Schauder

open scoped ContDiff NNReal Topology
open Set Matrix

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

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

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

private theorem ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear_aux {Du Eu Fu Gu : Type u}
    [NormedAddCommGroup Du] [NormedSpace 𝕜 Du] [NormedAddCommGroup Eu] [NormedSpace 𝕜 Eu]
    [NormedAddCommGroup Fu] [NormedSpace 𝕜 Fu] [NormedAddCommGroup Gu] [NormedSpace 𝕜 Gu]
    (B : Eu →L[𝕜] Fu →L[𝕜] Gu) {f : Du → Eu} {g : Du → Fu} {n : ℕ} {s : Set Du} {x : Du}
    (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    ‖iteratedFDerivWithin 𝕜 n (fun y => B (f y) (g y)) s x‖ ≤
      ‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDerivWithin 𝕜 i f s x‖ *
        ‖iteratedFDerivWithin 𝕜 (n - i) g s x‖ := by
  /- We argue by induction on `n`. The bound is trivial for `n = 0`. For `n + 1`, we write
    the `(n+1)`-th derivative as the `n`-th derivative of the derivative `B f g' + B f' g`,
    and apply the inductive assumption to each of those two terms. For this induction to make sense,
    the spaces of linear maps that appear in the induction should be in the same universe as the
    original spaces, which explains why we assume in the lemma that all spaces live in the same
    universe. -/
  induction n generalizing Eu Fu Gu with
  | zero =>
    simp only [norm_iteratedFDerivWithin_zero, zero_add, Finset.range_one,
      Finset.sum_singleton, Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_zero, ← mul_assoc]
    apply B.le_opNorm₂
  | succ n IH =>
    have In : ((n : WithTop ℕ∞) + 1) ≤ (n.succ : WithTop ℕ∞) := by simp only [Nat.cast_succ, le_refl]
    have I1 :
        ‖iteratedFDerivWithin 𝕜 n (fun y : Du => B.precompR Du (f y) (fderivWithin 𝕜 g s y)) s x‖ ≤
          ‖B‖ * ∑ i ∈ Finset.range (n + 1), n.choose i * ‖iteratedFDerivWithin 𝕜 i f s x‖ *
            ‖iteratedFDerivWithin 𝕜 (n + 1 - i) g s x‖ := by
      calc
        ‖iteratedFDerivWithin 𝕜 n (fun y : Du => B.precompR Du (f y) (fderivWithin 𝕜 g s y)) s x‖ ≤
            ‖B.precompR Du‖ * ∑ i ∈ Finset.range (n + 1),
              n.choose i * ‖iteratedFDerivWithin 𝕜 i f s x‖ *
                ‖iteratedFDerivWithin 𝕜 (n - i) (fderivWithin 𝕜 g s) s x‖ :=
          IH _ (hf.of_le (Nat.cast_le.2 (Nat.le_succ n))) (hg.fderivWithin hs In)
        _ ≤ ‖B‖ * ∑ i ∈ Finset.range (n + 1), n.choose i * ‖iteratedFDerivWithin 𝕜 i f s x‖ *
              ‖iteratedFDerivWithin 𝕜 (n - i) (fderivWithin 𝕜 g s) s x‖ := by
            gcongr; exact B.norm_precompR_le Du
        _ = _ := by
          congr 1
          apply Finset.sum_congr rfl fun i hi => ?_
          rw [Nat.succ_sub (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)),
            ← norm_iteratedFDerivWithin_fderivWithin hs hx]
    have I2 :
        ‖iteratedFDerivWithin 𝕜 n (fun y : Du => B.precompL Du (fderivWithin 𝕜 f s y) (g y)) s x‖ ≤
        ‖B‖ * ∑ i ∈ Finset.range (n + 1), n.choose i * ‖iteratedFDerivWithin 𝕜 (i + 1) f s x‖ *
          ‖iteratedFDerivWithin 𝕜 (n - i) g s x‖ :=
      calc
        ‖iteratedFDerivWithin 𝕜 n (fun y : Du => B.precompL Du (fderivWithin 𝕜 f s y) (g y)) s x‖ ≤
            ‖B.precompL Du‖ * ∑ i ∈ Finset.range (n + 1),
              n.choose i * ‖iteratedFDerivWithin 𝕜 i (fderivWithin 𝕜 f s) s x‖ *
                ‖iteratedFDerivWithin 𝕜 (n - i) g s x‖ :=
          IH _ (hf.fderivWithin hs In) (hg.of_le (Nat.cast_le.2 (Nat.le_succ n)))
        _ ≤ ‖B‖ * ∑ i ∈ Finset.range (n + 1),
            n.choose i * ‖iteratedFDerivWithin 𝕜 i (fderivWithin 𝕜 f s) s x‖ *
              ‖iteratedFDerivWithin 𝕜 (n - i) g s x‖ := by
          gcongr; exact B.norm_precompL_le Du
        _ = _ := by
          congr 1
          apply Finset.sum_congr rfl fun i _ => ?_
          rw [← norm_iteratedFDerivWithin_fderivWithin hs hx]
    have J : iteratedFDerivWithin 𝕜 n
        (fun y : Du => fderivWithin 𝕜 (fun y : Du => B (f y) (g y)) s y) s x =
          iteratedFDerivWithin 𝕜 n (fun y => B.precompR Du (f y)
            (fderivWithin 𝕜 g s y) + B.precompL Du (fderivWithin 𝕜 f s y) (g y)) s x := by
      apply iteratedFDerivWithin_congr (fun y hy => ?_) hx
      exact B.fderivWithin_of_bilinear (hf.differentiableOn (by positivity) y hy)
        (hg.differentiableOn (by positivity) y hy) (hs y hy)
    rw [← norm_iteratedFDerivWithin_fderivWithin hs hx, J]
    have A : ContDiffOn 𝕜 n (fun y => B.precompR Du (f y) (fderivWithin 𝕜 g s y)) s :=
      (B.precompR Du).isBoundedBilinearMap.contDiff.comp₂_contDiffOn
        (hf.of_le (Nat.cast_le.2 (Nat.le_succ n))) (hg.fderivWithin hs In)
    have A' : ContDiffOn 𝕜 n (fun y => B.precompL Du (fderivWithin 𝕜 f s y) (g y)) s :=
      (B.precompL Du).isBoundedBilinearMap.contDiff.comp₂_contDiffOn (hf.fderivWithin hs In)
        (hg.of_le (Nat.cast_le.2 (Nat.le_succ n)))
    rw [fun_iteratedFDerivWithin_add_apply (A.contDiffWithinAt hx) (A'.contDiffWithinAt hx) hs hx]
    apply (norm_add_le _ _).trans ((add_le_add I1 I2).trans (le_of_eq ?_))
    simp_rw [← mul_add, mul_assoc]
    congr 1
    exact (Finset.sum_choose_succ_mul
      (fun i j => ‖iteratedFDerivWithin 𝕜 i f s x‖ * ‖iteratedFDerivWithin 𝕜 j g s x‖) n).symm

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
    have hwithin₀ := ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear_aux
      (n := j) B (hf.1.of_le hn) (hg.1.of_le hn) hV.uniqueDiffOn hz
    have hwithin := hwithin₀.trans (mul_le_of_le_one_left (by positivity)
      (ContinuousLinearMap.opNorm_mul_le _ _))
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

private theorem holderOnWith_finset_sum
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
private theorem holderBoundOn_real_trace_product_convex
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

private theorem compact_derivative_bound_probe {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) {m : ℕ} {f : E → F}
    (hf : ContDiffOn ℝ m f U) {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ≥0, ∀ j ≤ m, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
  have htop (j : ℕ) (hj : j ≤ m) : (j : ℕ∞ω) ≤ (m : ℕ∞ω) := by
    exact_mod_cast hj
  have hcont (j : ℕ) (hj : j ≤ m) :
      ContinuousOn (fun x ↦ ‖iteratedFDeriv ℝ j f x‖) K := by
    have hwithin := hf.continuousOn_iteratedFDerivWithin (htop j hj) hU.uniqueDiffOn
    have heq : EqOn (iteratedFDerivWithin ℝ j f U) (iteratedFDeriv ℝ j f) U := by
      intro x hx
      exact iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
        ((hf.contDiffAt (hU.mem_nhds hx)).of_le (htop j hj)) hx
    exact (hwithin.congr heq.symm).mono hKU |>.norm
  let q : E → ℝ := fun x ↦ ∑ j ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ j f x‖
  have hq : ContinuousOn q K := by
    dsimp [q]
    exact continuousOn_finsetSum (Finset.range (m + 1)) fun j hj =>
      hcont j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  obtain ⟨B, hB0, hB⟩ := (hK.bddAbove_image hq).exists_ge 0
  let C : ℝ≥0 := ⟨B, hB0⟩
  refine ⟨C, ?_⟩
  intro j hj x hx
  have hqbound : q x ≤ B := hB (q x) (Set.mem_image_of_mem q hx)
  have hterm : ‖iteratedFDeriv ℝ j f x‖ ≤ q x := by
    dsimp [q]
    apply Finset.single_le_sum (f := fun i => ‖iteratedFDeriv ℝ i f x‖)
    · intro i hi
      exact norm_nonneg _
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  change ‖iteratedFDeriv ℝ j f x‖ ≤ B
  exact hterm.trans hqbound

private theorem holderBoundOn_succ_derivative_bound_probe
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {k : ℕ} {alpha C : ℝ≥0} {f : E → F}
    (hsOpen : IsOpen s) (hsConvex : Convex ℝ s)
    (hsDiam : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ 1)
    (hAlpha : alpha ≤ 1) (hf : ContDiffOn ℝ (k + 1) f s)
    (hbound : ∀ j ≤ k + 1, ∀ x ∈ s, ‖iteratedFDeriv ℝ j f x‖ ≤ C) :
    HolderBoundOn k alpha C s f := by
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    exact hbound j (le_trans hj (Nat.le_succ k)) x hx
  · let g : E → _ := iteratedFDeriv ℝ k f
    have hklt : (↑k : ℕ∞ω) < (↑(k + 1) : ℕ∞ω) := by
      exact_mod_cast Nat.lt_succ_self k
    have hgDiff (x : E) (hx : x ∈ s) : DifferentiableAt ℝ g x := by
      have hfx : ContDiffAt ℝ (k + 1) f x := hf.contDiffAt (hsOpen.mem_nhds hx)
      exact hfx.differentiableAt_iteratedFDeriv hklt
    have hgDeriv (x : E) (hx : x ∈ s) : ‖fderiv ℝ g x‖ ≤ (C : ℝ) := by
      rw [norm_fderiv_iteratedFDeriv]
      exact hbound (k + 1) le_rfl x hx
    have hLip : LipschitzOnWith C g s := by
      apply hsConvex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
      · exact hgDiff
      · exact hgDeriv
    have hdiam (x : E) (hx : x ∈ s) (y : E) (hy : y ∈ s) :
        edist x y ≤ (1 : ENNReal) := by
      rw [edist_dist]
      exact_mod_cast hsDiam x hx y hy
    simpa [g] using (hLip.holderOnWith.of_le hdiam hAlpha)

private theorem smooth_holder_on_ball_probe {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) {k : ℕ} {alpha : ℝ≥0}
    (_ha0 : 0 < alpha) (ha1 : alpha < 1) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) {z : E} {R : ℝ}
    (hR : 0 < R) (hRsmall : R ≤ 1 / 4)
    (hball : Metric.closedBall z R ⊆ U) :
    ∃ C : ℝ≥0, HolderBoundOn k alpha C (Metric.ball z R) f := by
  let K := Metric.closedBall z R
  have hK : IsCompact K := isCompact_closedBall z R
  obtain ⟨C, hC⟩ := compact_derivative_bound_probe hU
    (m := k + 1) (hf.of_le (WithTop.coe_le_coe.mpr le_top)) hK hball
  have hfinite : ContDiffOn ℝ (k + 1) f (Metric.ball z R) := by
    exact hf.mono (Metric.ball_subset_closedBall.trans hball) |>.of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hbound (j : ℕ) (hj : j ≤ k + 1) (x : E) (hx : x ∈ Metric.ball z R) :
      ‖iteratedFDeriv ℝ j f x‖ ≤ C := hC j (by omega) x (Metric.ball_subset_closedBall hx)
  refine ⟨C, ?_⟩
  apply holderBoundOn_succ_derivative_bound_probe Metric.isOpen_ball (convex_ball z R) ?_ ha1.le hfinite hbound
  intro x hx y hy
  have hx' : dist x z < R := by simpa [Metric.mem_ball] using hx
  have hy' : dist y z < R := by simpa [Metric.mem_ball] using hy
  have hdist := dist_triangle x z y
  have hdist' : dist x y < 2 * R := by
    have hyx : dist z y = dist y z := dist_comm z y
    linarith
  linarith

private theorem holderBoundOn_sub_probe
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U K : Set E} {k : ℕ} {α C D : ℝ≥0} {f g : E → F}
    (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : ContDiffOn ℝ k f U) (hg : ContDiffOn ℝ k g U)
    (hfb : HolderBoundOn k α C K f) (hgb : HolderBoundOn k α D K g) :
    HolderBoundOn k α (C + D) K (fun x ↦ f x - g x) := by
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    have hfj : ContDiffAt ℝ j f x :=
      (hf.contDiffAt (hU.mem_nhds (hKU hx))).of_le
        (WithTop.coe_le_coe.mpr (by exact_mod_cast hj))
    have hgj : ContDiffAt ℝ j g x :=
      (hg.contDiffAt (hU.mem_nhds (hKU hx))).of_le
        (WithTop.coe_le_coe.mpr (by exact_mod_cast hj))
    change ‖iteratedFDeriv ℝ j (f - g) x‖ ≤ (C + D : ℝ≥0)
    rw [iteratedFDeriv_sub_apply hfj hgj]
    exact (norm_sub_le _ _).trans (by
      simpa using add_le_add (hfb.1 j hj x hx) (hgb.1 j hj x hx))
  · intro x hx y hy
    have hfx := hf.contDiffAt (hU.mem_nhds (hKU hx))
    have hgx := hg.contDiffAt (hU.mem_nhds (hKU hx))
    have hfy := hf.contDiffAt (hU.mem_nhds (hKU hy))
    have hgy := hg.contDiffAt (hU.mem_nhds (hKU hy))
    change edist (iteratedFDeriv ℝ k (f - g) x) (iteratedFDeriv ℝ k (f - g) y) ≤ _
    rw [iteratedFDeriv_sub_apply hfx hgx, iteratedFDeriv_sub_apply hfy hgy]
    have hgb' : edist (-iteratedFDeriv ℝ k g x) (-iteratedFDeriv ℝ k g y) ≤
        (D : ENNReal) * edist x y ^ (α : ℝ) := by
      simpa only [edist_neg_neg] using hgb.2 x hx y hy
    calc
      edist (iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k g x)
          (iteratedFDeriv ℝ k f y - iteratedFDeriv ℝ k g y) ≤
        edist (iteratedFDeriv ℝ k f x) (iteratedFDeriv ℝ k f y) +
          edist (-iteratedFDeriv ℝ k g x) (-iteratedFDeriv ℝ k g y) := by
            simpa only [sub_eq_add_neg, edist_neg_neg] using
              (edist_add_add_le (iteratedFDeriv ℝ k f x) (-iteratedFDeriv ℝ k g x)
                (iteratedFDeriv ℝ k f y) (-iteratedFDeriv ℝ k g y))
      _ ≤ (C : ENNReal) * edist x y ^ (α : ℝ) +
          (D : ENNReal) * edist x y ^ (α : ℝ) := add_le_add (hfb.2 x hx y hy) hgb'
      _ = ((C + D : ℝ≥0) : ENNReal) * edist x y ^ (α : ℝ) := by
        rw [ENNReal.coe_add]
        ring

/-!
# Hölder jets of the differentiated log-determinant forcing

Smooth background data and a genuine finite Hölder coefficient jet give a finite
Hölder jet for the forcing. Matrix multiplication uses the swapped trace indices:
`re tr(A Dg) = re ∑ i, ∑ j, A i j * Dg j i`.
The assertion includes every lower-jet sup bound, not just the top seminorm.
-/

@[expose] public section

open scoped ContDiff NNReal Topology

/-- Local finite Hölder control of the smooth derivative minus the coefficient trace. -/
theorem locally_holder_directional_trace_forcing
    {n r : ℕ} {α K : ℝ≥0} {W : Set (EuclideanSpace ℂ (Fin n))}
    (hW : IsOpen W) (hα₀ : 0 < α) (hα₁ : α < 1)
    (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (H : EuclideanSpace ℂ (Fin n) → ℝ)
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, ContDiffOn ℝ r (fun w ↦ A w i j) W)
    (hAH : ∀ i j, HolderBoundOn r α K W (fun w ↦ A w i j))
    (hH : ContDiffOn ℝ ∞ H W)
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun w ↦ g w i j) W)
    (v z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ W) :
    ∃ V : Set (EuclideanSpace ℂ (Fin n)), ∃ C : ℝ≥0,
      IsOpen V ∧ z ∈ V ∧ V ⊆ W ∧
      HolderBoundOn r α C V (fun w ↦ fderiv ℝ H w v -
        RCLike.re (A w * fderiv ℝ g w v).trace) := by

  classical
  obtain ⟨R, hR, hRball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hz)
  let ρ : ℝ := min (R / 2) (1 / 8)
  let V : Set (EuclideanSpace ℂ (Fin n)) := Metric.ball z ρ
  let closedBall : Set (EuclideanSpace ℂ (Fin n)) := Metric.closedBall z ρ
  have hρpos : 0 < ρ := by dsimp [ρ]; positivity
  have hρlt : ρ < R := by dsimp [ρ]; simp only [min_lt_iff]; left; linarith
  have hρsmall : ρ ≤ 1 / 4 := by dsimp [ρ]; exact (min_le_right _ _).trans (by norm_num)
  have hVopen : IsOpen V := Metric.isOpen_ball
  have hzV : z ∈ V := by
    change z ∈ Metric.ball z ρ
    exact Metric.mem_ball_self hρpos
  have hVsubK : V ⊆ closedBall := Metric.ball_subset_closedBall
  have hKcompact : IsCompact closedBall := isCompact_closedBall z ρ
  have hKsubW : closedBall ⊆ W := by
    intro w hw
    apply hRball
    rw [Metric.mem_ball]
    have hw' : dist w z ≤ ρ := by
      simpa [closedBall, Metric.mem_closedBall] using hw
    exact lt_of_le_of_lt hw' hρlt
  have hVsubW : V ⊆ W := fun w hw ↦ hKsubW (hVsubK hw)
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedSpace
  let B : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w ↦ fderiv ℝ g w v
  have hgMatrix : ContDiffOn ℝ ∞ g W :=
    contDiffOn_pi.mpr fun i ↦ contDiffOn_pi.mpr fun j ↦ hg i j
  have hB : ContDiffOn ℝ ∞ B W := by
    dsimp [B]
    exact (hgMatrix.fderiv_of_isOpen hW (WithTop.coe_le_coe.mpr le_top)).clm_apply
      contDiffOn_const
  have hBentry : ∀ i j, ContDiffOn ℝ ∞ (fun w ↦ B w i j) W := by
    intro i j
    exact (contDiffOn_pi.mp (contDiffOn_pi.mp hB i)) j
  have hDgHolder (i j : Fin n) :
      ∃ C : ℝ≥0, HolderBoundOn r α C V (fun w ↦ B w i j) := by
    have hLocal := smooth_holder_on_ball_probe (k := r) hW hα₀ hα₁
      (hBentry i j) hρpos hρsmall hKsubW
    simpa [V] using hLocal
  let q : Fin n × Fin n → ℝ≥0 := fun p ↦ Classical.choose (hDgHolder p.1 p.2)
  let CB : ℝ≥0 := ∑ p : Fin n × Fin n, q p
  have hBbound (i j : Fin n) : HolderBoundOn r α CB V (fun w ↦ B w i j) := by
    have hq := Classical.choose_spec (hDgHolder i j)
    apply hq.mono_const
    change q (i, j) ≤ ∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)), q p
    exact Finset.single_le_sum (fun p hp ↦ by positivity) (Finset.mem_univ (i, j))
  have hHdir : ContDiffOn ℝ ∞ (fun w ↦ fderiv ℝ H w v) W := by
    exact (hH.fderiv_of_isOpen hW (WithTop.coe_le_coe.mpr le_top)).clm_apply
      contDiffOn_const
  have hHholder : ∃ CH : ℝ≥0,
      HolderBoundOn r α CH V (fun w ↦ fderiv ℝ H w v) := by
    have hLocal := smooth_holder_on_ball_probe (k := r) hW hα₀ hα₁
      hHdir hρpos hρsmall hKsubW
    simpa [V] using hLocal
  obtain ⟨CH, hHholder⟩ := hHholder
  have hHfinite : ContDiffOn ℝ r (fun w ↦ fderiv ℝ H w v) V :=
    hHdir.mono hVsubW |>.of_le (WithTop.coe_le_coe.mpr le_top)
  have hTrace : HolderBoundOn r α
      (8 * (2 : ℝ≥0) ^ r * (Fintype.card (Fin n × Fin n) : ℝ≥0) * K * CB) V
      (fun w ↦ RCLike.re ((A w * B w).trace)) := by
    apply holderBoundOn_real_trace_product_convex
      hα₀ hα₁ hVopen (convex_ball z ρ) A B
    · intro i j
      exact ⟨(hA i j).mono hVsubW, (hAH i j).mono_set hVsubW⟩
    · intro i j
      exact ⟨(hBentry i j).mono hVsubW |>.of_le
          (WithTop.coe_le_coe.mpr le_top), hBbound i j⟩
  have hTraceFinite : ContDiffOn ℝ r
      (fun w ↦ RCLike.re ((A w * B w).trace)) V := by
    have hsum : ContDiffOn ℝ r (fun w ↦
        ∑ i, ∑ j, Complex.reCLM (A w i j * B w j i)) V := by
      apply ContDiffOn.sum
      intro i hi
      apply ContDiffOn.sum
      intro j hj
      exact Complex.reCLM.contDiff.comp_contDiffOn
        ((hA i j).mono hVsubW |>.mul ((hBentry j i).mono hVsubW
          |>.of_le (WithTop.coe_le_coe.mpr le_top)))
    apply hsum.congr
    intro w hw
    simp [Matrix.mul_apply, Matrix.trace, Complex.reCLM_apply]
  have hResult := holderBoundOn_sub_probe hVopen Set.Subset.rfl
    hHfinite hTraceFinite hHholder hTrace
  exact ⟨V, CH + (8 * (2 : ℝ≥0) ^ r *
    (Fintype.card (Fin n × Fin n) : ℝ≥0) * K * CB),
    hVopen, hzV, hVsubW, hResult⟩

end
