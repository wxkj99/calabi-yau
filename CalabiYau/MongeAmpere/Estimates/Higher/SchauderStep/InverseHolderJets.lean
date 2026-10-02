module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.MetricSpace.Holder
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import CalabiYau.Mathlib.Analysis.Matrix.InverseHolder
import CalabiYau.MongeAmpere.Estimates.Higher.SchauderStep.InverseJetNorm
import CalabiYau.MongeAmpere.Estimates.Higher.SchauderStep.InverseJetHolder

/-!
# Higher-order Hölder bounds for inverse matrix coefficients

On a neighborhood where every matrix field in a family remains invertible, common local
`C^{k,α}` entry bounds and a common inverse-entry bound give ONE `C^{k,α}` bound for the
inverse entries throughout the family. All lower input jets are uniformly Hölder on the
comparison set: pointwise jet bounds alone cannot control nearby points across thin gaps.
Iterated differentiation of `A⁻¹ A = 1` expresses every inverse jet as a finite sum of products
of inverse entries and jets of `A`. The exponent is restricted to `0 < α < 1`.
-/

@[expose] public section

open scoped ContDiff NNReal

namespace KahlerForm

/-- The Leibniz convolution bounds every derivative of a product by the binomial convolution of
its two jet bounds. The explicit `2^k` constant is uniform in the point and in any external family
parameter, so this lemma can be applied to each factor in the inverse-jet recurrence. -/
private theorem product_iterated_jet_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} {C D : ℝ≥0} {W K : Set E}
    (hW : IsOpen W) (hKW : K ⊆ W)
    (f g : E → ℂ)
    (hf : ContDiffOn ℝ ∞ f W) (hg : ContDiffOn ℝ ∞ g W)
    (hfBound : ∀ m ≤ k, ∀ z ∈ K, ‖iteratedFDeriv ℝ m f z‖ ≤ C)
    (hgBound : ∀ m ≤ k, ∀ z ∈ K, ‖iteratedFDeriv ℝ m g z‖ ≤ D) :
    ∀ m ≤ k, ∀ z ∈ K,
      ‖iteratedFDeriv ℝ m (fun z ↦ f z * g z) z‖ ≤ (2 : ℝ≥0) ^ k * C * D := by
  intro m hm z hz
  have hWz : z ∈ W := hKW hz
  have hNatLeInf (r : ℕ) : (r : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    exact_mod_cast (le_top : (r : ℕ∞) ≤ (⊤ : ℕ∞))
  have hAtF : ContDiffAt ℝ ∞ f z :=
    (hf.contDiffWithinAt hWz).contDiffAt (hW.mem_nhds hWz)
  have hAtG : ContDiffAt ℝ ∞ g z :=
    (hg.contDiffWithinAt hWz).contDiffAt (hW.mem_nhds hWz)
  have hmul := norm_iteratedFDerivWithin_mul_le hf hg hW.uniqueDiffOn hWz
    (hNatLeInf m)
  have hleft (i : ℕ) (hi : i ≤ m) :
      ‖iteratedFDerivWithin ℝ i f W z‖ ≤ (C : ℝ) := by
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hW.uniqueDiffOn
      (hAtF.of_le (hNatLeInf i)) hWz]
    exact_mod_cast hfBound i (le_trans hi hm) z hz
  have hright (i : ℕ) (hi : i ≤ m) :
      ‖iteratedFDerivWithin ℝ i g W z‖ ≤ (D : ℝ) := by
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hW.uniqueDiffOn
      (hAtG.of_le (hNatLeInf i)) hWz]
    exact_mod_cast hgBound i (le_trans hi hm) z hz
  have hsum :
      ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i f W z‖ *
        ‖iteratedFDerivWithin ℝ (m - i) g W z‖ ≤
      (2 : ℝ) ^ m * (C : ℝ) * D := by
    calc
      _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * (C : ℝ) * D := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        have hmi : m - i ≤ m := Nat.sub_le _ _
        calc
          (m.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i f W z‖ *
              ‖iteratedFDerivWithin ℝ (m - i) g W z‖ ≤
              (m.choose i : ℝ) * (C : ℝ) *
                ‖iteratedFDerivWithin ℝ (m - i) g W z‖ := by
            gcongr
            exact hleft i hi'
          _ ≤ (m.choose i : ℝ) * (C : ℝ) * D := by
            gcongr
            exact hright (m - i) hmi
      _ = (2 : ℝ) ^ m * (C : ℝ) * D := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        have hchoose :
            (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ)) = (2 : ℝ) ^ m := by
          norm_cast
          exact Nat.sum_range_choose m
        rw [hchoose]
  have hbound : ‖iteratedFDerivWithin ℝ m (fun z ↦ f z * g z) W z‖ ≤
      (2 : ℝ) ^ k * (C : ℝ) * D := by
    calc
      _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i f W z‖ *
          ‖iteratedFDerivWithin ℝ (m - i) g W z‖ := hmul
      _ ≤ (2 : ℝ) ^ m * (C : ℝ) * D := hsum
      _ ≤ (2 : ℝ) ^ k * (C : ℝ) * D := by
        gcongr
        norm_num
  have hAtProd : ContDiffAt ℝ ∞ (fun z ↦ f z * g z) z :=
    ((hf.mul hg).contDiffWithinAt hWz).contDiffAt (hW.mem_nhds hWz)
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hW.uniqueDiffOn
    (hAtProd.of_le (hNatLeInf m)) hWz] at hbound
  exact_mod_cast hbound

/-- Matrix multiplication is controlled entrywise by the scalar product jet convolution and
its finite sum over the contracted index. -/
private theorem matrix_product_entry_iterated_jet_bound
    {P E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n k : ℕ} {C D : ℝ≥0} {W K : Set E}
    (S : Set P) (hW : IsOpen W) (hKW : K ⊆ W)
    (U V : P → E → Matrix (Fin n) (Fin n) ℂ)
    (hUSmooth : ∀ p ∈ S, ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ U p z i j) W)
    (hVSmooth : ∀ p ∈ S, ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ V p z i j) W)
    (hUJet : ∀ p ∈ S, ∀ i j, ∀ m ≤ k, ∀ z ∈ K,
      ‖iteratedFDeriv ℝ m (fun z ↦ U p z i j) z‖ ≤ C)
    (hVJet : ∀ p ∈ S, ∀ i j, ∀ m ≤ k, ∀ z ∈ K,
      ‖iteratedFDeriv ℝ m (fun z ↦ V p z i j) z‖ ≤ D) :
    ∀ p ∈ S, ∀ i j, ∀ m ≤ k, ∀ z ∈ K,
      ‖iteratedFDeriv ℝ m (fun z ↦ (U p z * V p z) i j) z‖ ≤
        (n : ℝ≥0) * (2 : ℝ≥0) ^ k * C * D := by
  intro p hp i j m hm z hz
  have hWz : z ∈ W := hKW hz
  have hNatLeInf (r : ℕ) : (r : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    exact_mod_cast (le_top : (r : ℕ∞) ≤ (⊤ : ℕ∞))
  have hsum : iteratedFDeriv ℝ m (fun z ↦ (U p z * V p z) i j) z =
      ∑ l : Fin n, iteratedFDeriv ℝ m
        (fun z ↦ U p z i l * V p z l j) z := by
    have hfun : (fun z ↦ (U p z * V p z) i j) =
        fun z ↦ ∑ l : Fin n, U p z i l * V p z l j := by
      funext z
      exact Matrix.mul_apply
    rw [hfun, iteratedFDeriv_fun_sum_apply]
    intro l hl
    exact (((hUSmooth p hp i l).contDiffWithinAt hWz).contDiffAt
      (hW.mem_nhds hWz)).mul (((hVSmooth p hp l j).contDiffWithinAt hWz).contDiffAt
      (hW.mem_nhds hWz)) |>.of_le (hNatLeInf m)
  have hterm (l : Fin n) : ‖iteratedFDeriv ℝ m
      (fun z ↦ U p z i l * V p z l j) z‖ ≤ (2 : ℝ) ^ k * (C : ℝ) * D := by
    have h := product_iterated_jet_bound hW hKW
      (fun z ↦ U p z i l) (fun z ↦ V p z l j)
      (hUSmooth p hp i l) (hVSmooth p hp l j)
      (fun r hr z hz ↦ hUJet p hp i l r hr z hz)
      (fun r hr z hz ↦ hVJet p hp l j r hr z hz)
    exact h m hm z hz
  have hnorm : ‖iteratedFDeriv ℝ m
      (fun z ↦ (U p z * V p z) i j) z‖ ≤
      (n : ℝ) * (2 : ℝ) ^ k * (C : ℝ) * D := by
    rw [hsum]
    calc
      ‖∑ l : Fin n, iteratedFDeriv ℝ m
          (fun z ↦ U p z i l * V p z l j) z‖ ≤
          ∑ l : Fin n, ‖iteratedFDeriv ℝ m
            (fun z ↦ U p z i l * V p z l j) z‖ := norm_sum_le _ _
      _ ≤ ∑ l : Fin n, (2 : ℝ) ^ k * (C : ℝ) * D := by
        apply Finset.sum_le_sum
        intro l hl
        exact hterm l
      _ = (n : ℝ) * (2 : ℝ) ^ k * (C : ℝ) * D := by
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
  exact_mod_cast hnorm

private theorem holderOnWith_complex_mul_bounded
    {E : Type*} [PseudoMetricSpace E] {K : Set E}
    {α Cf Cg Bf Bg : ℝ≥0} {f g : E → ℂ}
    (hf : HolderOnWith Cf α f K) (hg : HolderOnWith Cg α g K)
    (hfBound : ∀ x ∈ K, ‖f x‖₊ ≤ Bf) (hgBound : ∀ x ∈ K, ‖g x‖₊ ≤ Bg) :
    HolderOnWith (Bf * Cg + Bg * Cf) α (fun x ↦ f x * g x) K := by
  intro x hx y hy
  have hdecomp : f x * g x - f y * g y =
      f x * (g x - g y) + (f x - f y) * g y := by ring
  have hfirst : edist (f x * (g x - g y)) 0 ≤
      (‖f x‖₊ : ENNReal) * edist (g x) (g y) := by
    have h := edist_smul_le (f x) (g x - g y) 0
    have heq : f x * (g x - g y) = f x • (g x - g y) := by simp [smul_eq_mul]
    rw [heq]
    simp [enorm_eq_nnnorm, edist_dist, dist_eq_norm] at h ⊢
  have hsecond : edist ((f x - f y) * g y) 0 ≤
      (‖g y‖₊ : ENNReal) * edist (f x) (f y) := by
    have h := edist_smul_le (g y) (f x - f y) 0
    have heq : (f x - f y) * g y = g y • (f x - f y) := by
      simp [smul_eq_mul, mul_comm]
    rw [heq]
    simp [enorm_eq_nnnorm, edist_dist, dist_eq_norm] at h ⊢
  calc
    edist (f x * g x) (f y * g y) =
        edist (f x * (g x - g y) + (f x - f y) * g y) 0 := by
          rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm]
          congr 1
          rw [hdecomp]
          simp
    _ ≤ edist (f x * (g x - g y)) 0 + edist ((f x - f y) * g y) 0 := by
      simpa using edist_add_add_le (f x * (g x - g y)) ((f x - f y) * g y)
        (0 : ℂ) (0 : ℂ)
    _ ≤ (‖f x‖₊ : ENNReal) * edist (g x) (g y) +
        (‖g y‖₊ : ENNReal) * edist (f x) (f y) := add_le_add hfirst hsecond
    _ ≤ (Bf : ENNReal) * ((Cg : ENNReal) * edist x y ^ (α : ℝ)) +
        (Bg : ENNReal) * ((Cf : ENNReal) * edist x y ^ (α : ℝ)) := by
      apply add_le_add
      · have hnorm : (‖f x‖₊ : ENNReal) ≤ (Bf : ENNReal) := by exact_mod_cast hfBound x hx
        exact mul_le_mul hnorm (hg.edist_le hx hy) (by positivity) (by positivity)
      · have hnorm : (‖g y‖₊ : ENNReal) ≤ (Bg : ENNReal) := by exact_mod_cast hgBound y hy
        exact mul_le_mul hnorm (hf.edist_le hx hy) (by positivity) (by positivity)
    _ = ((Bf * Cg + Bg * Cf : ℝ≥0) : ENNReal) * edist x y ^ (α : ℝ) := by
      simp only [ENNReal.coe_add, ENNReal.coe_mul]
      ring

/-- The resolvent estimate controls the zero-order inverse jet uniformly over the family. -/
private theorem inverse_entry_zero_jet_holder_uniform
    {P E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n k : ℕ} {α C B : ℝ≥0} {W K : Set E}
    (S : Set P) (hKW : K ⊆ W)
    (A : P → E → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ p ∈ S, ∀ i j,
      (∀ m ≤ k, ∀ z ∈ K, ‖iteratedFDeriv ℝ m (fun z ↦ A p z i j) z‖ ≤ C) ∧
      (∀ m < k, HolderOnWith C α (iteratedFDeriv ℝ m (fun z ↦ A p z i j)) K) ∧
      HolderOnWith C α (iteratedFDeriv ℝ k (fun z ↦ A p z i j)) K)
    (hUnit : ∀ p ∈ S, ∀ z ∈ W, IsUnit (A p z))
    (hInv : ∀ p ∈ S, ∀ z ∈ K, ∀ i j, ‖(A p z)⁻¹ i j‖ ≤ B)
    (hk : 0 < k) (p : P) (hp : p ∈ S) (i j : Fin n) :
    HolderOnWith ((n : ℝ≥0) ^ 2 * B ^ 2 * C) α
      (fun z ↦ (A p z)⁻¹ i j) K := by
  let L := continuousMultilinearCurryFin0 ℝ E ℂ
  have hAHolder (q t : Fin n) :
      HolderOnWith C α (fun z ↦ A p z q t) K := by
    intro z hz w hw
    have h := (hA p hp q t).2.1 0 (by omega) z hz w hw
    rw [iteratedFDeriv_zero_eq_comp] at h
    change edist (L.symm (A p z q t)) (L.symm (A p w q t)) ≤ _ at h
    rw [L.symm.edist_map] at h
    exact h
  exact KahlerForm.holderOnWith_matrix_inv_entry_of_norm_bound
    (A p) hAHolder (fun z hz ↦ hUnit p hp z (hKW hz)) (hInv p hp) i j

/-- The remaining inverse-jet recurrence is isolated from the elementary zero-order resolvent
estimate. It is the induction target for the higher product-jet bounds above. -/
private theorem exists_uniform_positive_inverse_entry_jets
    {P E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n k : ℕ} {α C B : ℝ≥0} {W K : Set E}
    (S : Set P)
    (hW : IsOpen W) (hKW : K ⊆ W)
    (A : P → E → Matrix (Fin n) (Fin n) ℂ)
    (hASmooth : ∀ p ∈ S, ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ A p z i j) W)
    (hA : ∀ p ∈ S, ∀ i j,
      (∀ m ≤ k, ∀ z ∈ K, ‖iteratedFDeriv ℝ m (fun z ↦ A p z i j) z‖ ≤ C) ∧
      (∀ m < k, HolderOnWith C α (iteratedFDeriv ℝ m (fun z ↦ A p z i j)) K) ∧
      HolderOnWith C α (iteratedFDeriv ℝ k (fun z ↦ A p z i j)) K)
    (hUnit : ∀ p ∈ S, ∀ z ∈ W, IsUnit (A p z))
    (hInv : ∀ p ∈ S, ∀ z ∈ K, ∀ i j, ‖(A p z)⁻¹ i j‖ ≤ B)
    (_hk : 0 < k) :
    ∃ Cpos : ℝ≥0, ∀ p ∈ S, ∀ i j,
      (∀ m, 0 < m → m ≤ k → ∀ z ∈ K,
        ‖iteratedFDeriv ℝ m (fun z ↦ (A p z)⁻¹ i j) z‖ ≤ Cpos) ∧
      (∀ m, 0 < m → m < k → HolderOnWith Cpos α
        (iteratedFDeriv ℝ m (fun z ↦ (A p z)⁻¹ i j)) K) ∧
      HolderOnWith Cpos α (iteratedFDeriv ℝ k (fun z ↦ (A p z)⁻¹ i j)) K := by
  have hAJet := fun p hp i j ↦ (hA p hp i j).1
  obtain ⟨N, hN⟩ := exists_normBoundOn_matrix_inverse_entry_jets
    S hW hKW A hASmooth hAJet hUnit hInv
  have hAHolder : ∀ p ∈ S, ∀ i j, ∀ m ≤ k,
      HolderOnWith C α (iteratedFDeriv ℝ m (fun z ↦ A p z i j)) K := by
    intro p hp i j m hm
    by_cases hmk : m = k
    · subst m
      exact (hA p hp i j).2.2
    · exact (hA p hp i j).2.1 m (lt_of_le_of_ne hm hmk)
  obtain ⟨H, hH⟩ := exists_holderConstantOn_matrix_inverse_entry_jets
    S hW hKW A hASmooth hAHolder hUnit hN
  refine ⟨max N H, ?_⟩
  intro p hp i j
  refine ⟨?_, ?_, ?_⟩
  · intro m _ hm z hz
    exact (hN p hp i j m hm z hz).trans (le_max_left N H)
  · intro m _ hm
    exact (hH p hp i j m (Nat.le_of_lt hm)).mono_const (le_max_right N H)
  · exact (hH p hp i j k le_rfl).mono_const (le_max_right N H)

/-- One constant controls all inverse-entry jets, including their lower-order Hölder
seminorms, over an arbitrary family. The common bound must be chosen BEFORE the family member;
a per-field existential bound cannot be used for a uniform Schauder continuation. -/
theorem exists_holderBoundOn_matrix_inverse_entries
    {P E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n k : ℕ} {α C B : ℝ≥0} {W K : Set E}
    (S : Set P)
    (hW : IsOpen W) (hKW : K ⊆ W)
    (A : P → E → Matrix (Fin n) (Fin n) ℂ)
    (hASmooth : ∀ p ∈ S, ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ A p z i j) W)
    (hA : ∀ p ∈ S, ∀ i j,
      (∀ m ≤ k, ∀ z ∈ K, ‖iteratedFDeriv ℝ m (fun z ↦ A p z i j) z‖ ≤ C) ∧
      (∀ m < k, HolderOnWith C α (iteratedFDeriv ℝ m (fun z ↦ A p z i j)) K) ∧
      HolderOnWith C α (iteratedFDeriv ℝ k (fun z ↦ A p z i j)) K)
    (hUnit : ∀ p ∈ S, ∀ z ∈ W, IsUnit (A p z))
    (hInv : ∀ p ∈ S, ∀ z ∈ K, ∀ i j, ‖(A p z)⁻¹ i j‖ ≤ B) :
    ∃ C' : ℝ≥0, ∀ p ∈ S, ∀ i j,
      (∀ m ≤ k, ∀ z ∈ K, ‖iteratedFDeriv ℝ m (fun z ↦ (A p z)⁻¹ i j) z‖ ≤ C') ∧
      (∀ m < k, HolderOnWith C' α
        (iteratedFDeriv ℝ m (fun z ↦ (A p z)⁻¹ i j)) K) ∧
      HolderOnWith C' α (iteratedFDeriv ℝ k (fun z ↦ (A p z)⁻¹ i j)) K := by
  by_cases hk : k = 0
  · subst k
    let CInv : ℝ≥0 := (n : ℝ≥0) ^ 2 * B ^ 2 * C
    let C' : ℝ≥0 := max B CInv
    refine ⟨C', ?_⟩
    intro p hp i j
    refine ⟨?_, ?_, ?_⟩
    · intro m hm z hz
      have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
      subst m
      rw [norm_iteratedFDeriv_zero]
      exact (hInv p hp z hz i j).trans (le_max_left B CInv)
    · intro m hm
      exact (Nat.not_lt_zero m hm).elim
    · let L := continuousMultilinearCurryFin0 ℝ E ℂ
      have hAHolder (q t : Fin n) :
          HolderOnWith C α (fun z ↦ A p z q t) K := by
        intro z hz w hw
        have h := (hA p hp q t).2.2 z hz w hw
        rw [iteratedFDeriv_zero_eq_comp] at h
        change edist (L.symm (A p z q t)) (L.symm (A p w q t)) ≤ _ at h
        rw [L.symm.edist_map] at h
        exact h
      have hHolder := KahlerForm.holderOnWith_matrix_inv_entry_of_norm_bound
        (A p) hAHolder (fun z hz ↦ hUnit p hp z (hKW hz)) (hInv p hp) i j
      have hHolder' : HolderOnWith C' α (fun z ↦ (A p z)⁻¹ i j) K :=
        hHolder.mono_const (le_max_right B CInv)
      intro z hz w hw
      rw [iteratedFDeriv_zero_eq_comp]
      change edist (L.symm ((A p z)⁻¹ i j)) (L.symm ((A p w)⁻¹ i j)) ≤ _
      rw [L.symm.edist_map]
      exact hHolder' z hz w hw
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    let CInv : ℝ≥0 := (n : ℝ≥0) ^ 2 * B ^ 2 * C
    let C0 : ℝ≥0 := max B CInv
    obtain ⟨Cpos, hpos⟩ := exists_uniform_positive_inverse_entry_jets
      S hW hKW A hASmooth hA hUnit hInv hkpos
    let C' : ℝ≥0 := max C0 Cpos
    refine ⟨C', ?_⟩
    intro p hp i j
    refine ⟨?_, ?_, ?_⟩
    · intro m hm z hz
      by_cases hm0 : m = 0
      · subst m
        rw [norm_iteratedFDeriv_zero]
        exact (hInv p hp z hz i j).trans
          (le_trans (le_max_left B CInv) (le_max_left C0 Cpos))
      · exact (hpos p hp i j).1 m (Nat.pos_of_ne_zero hm0) hm z hz |>.trans
          (le_max_right C0 Cpos)
    · intro m hm
      by_cases hm0 : m = 0
      · subst m
        let L := continuousMultilinearCurryFin0 ℝ E ℂ
        have hZero := (inverse_entry_zero_jet_holder_uniform S hKW A
          hA hUnit hInv hkpos p hp i j).mono_const
            (le_trans (le_max_right B CInv) (le_max_left C0 Cpos))
        intro z hz w hw
        have h := hZero z hz w hw
        rw [iteratedFDeriv_zero_eq_comp]
        change edist (L.symm ((A p z)⁻¹ i j)) (L.symm ((A p w)⁻¹ i j)) ≤ _
        rw [L.symm.edist_map]
        exact h
      · exact ((hpos p hp i j).2.1 m (Nat.pos_of_ne_zero hm0) hm).mono_const
          (le_max_right C0 Cpos)
    · exact ((hpos p hp i j).2.2).mono_const (le_max_right C0 Cpos)

end KahlerForm

end
