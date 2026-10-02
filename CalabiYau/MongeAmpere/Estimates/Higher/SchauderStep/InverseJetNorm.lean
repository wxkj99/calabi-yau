module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import CalabiYau.Geometry.Kahler.MatrixInverse

/-!
# Uniform norms of inverse matrix coefficient jets

This is the norm half of the inverse-coefficient bootstrap, independent of the Hölder exponent.
The source is Mathlib's inverse derivative and finite bilinear Leibniz bound:
`hasFDerivAt_ringInverse`, `norm_iteratedFDerivWithin_smul_le`, and
`norm_iteratedFDeriv_fderiv`. The matrix entry bridge keeps matrix norms private.

Induct on the derivative order using
`D Inv_ij = -∑ a, ∑ b, (Inv_ia * Inv_bj) • D A_ab`.
If `R` bounds all inverse jets through order `m`, the next order is bounded by
`n² * 4^m * R² * C`. Taking the maximum with `R` retains all lower orders.
All constants are independent of the family parameter, and all derivatives are real Fréchet
jets of complex entries. No conjugation, transpose, or complex-Laplacian factor occurs.
-/

open scoped ContDiff NNReal

namespace KahlerForm

private theorem inverse_entry_fderiv_clm_formula
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {W : Set E} (hW : IsOpen W)
    (A : E → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ A z i j) W)
    (hUnit : ∀ z ∈ W, IsUnit (A z)) (x : E) (hx : x ∈ W)
    (i j : Fin n) :
    fderiv ℝ (fun z ↦ (A z)⁻¹ i j) x =
      -∑ a : Fin n, ∑ b : Fin n,
        ((A x)⁻¹ i a * (A x)⁻¹ b j) • fderiv ℝ (fun z ↦ A z a b) x := by
  ext v
  rw [Matrix.fderiv_inverse_entry_apply_of_contDiffOn hW hx hA (hUnit x hx) i j v]
  simp only [_root_.neg_apply, _root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

private theorem norm_smul_jet_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} {W K : Set E} {Q G : ℝ≥0}
    (hW : IsOpen W) (hKW : K ⊆ W) (q : E → ℂ)
    (g : E → E →L[ℝ] ℂ)
    (hqSmooth : ContDiffOn ℝ ∞ q W) (hgSmooth : ContDiffOn ℝ ∞ g W)
    (hqBound : ∀ m ≤ k, ∀ z ∈ K, ‖iteratedFDeriv ℝ m q z‖ ≤ Q)
    (hgBound : ∀ m ≤ k, ∀ z ∈ K, ‖iteratedFDeriv ℝ m g z‖ ≤ G)
    (x : E) (hx : x ∈ K) :
    ‖iteratedFDeriv ℝ k (fun z ↦ q z • g z) x‖ ≤
      (2 : ℝ≥0) ^ k * Q * G := by
  have hqWithin (m : ℕ) (hm : m ≤ k) :
      ‖iteratedFDerivWithin ℝ m q W x‖ ≤ (Q : ℝ) := by
    rw [iteratedFDerivWithin_of_isOpen m hW (hKW hx)]
    exact_mod_cast hqBound m hm x hx
  have hgWithin (m : ℕ) (hm : m ≤ k) :
      ‖iteratedFDerivWithin ℝ m g W x‖ ≤ (G : ℝ) := by
    rw [iteratedFDerivWithin_of_isOpen m hW (hKW hx)]
    exact_mod_cast hgBound m hm x hx
  have hn : (k : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    exact_mod_cast (le_top : (k : ℕ∞) ≤ (⊤ : ℕ∞))
  have hsmul := norm_iteratedFDerivWithin_smul_le hqSmooth hgSmooth
    hW.uniqueDiffOn (hKW hx) hn
  calc
    ‖iteratedFDeriv ℝ k (fun z ↦ q z • g z) x‖ =
        ‖iteratedFDerivWithin ℝ k (fun z ↦ q z • g z) W x‖ := by
      rw [iteratedFDerivWithin_of_isOpen k hW (hKW hx)]
    _ ≤ ∑ m ∈ Finset.range (k + 1), (k.choose m : ℝ) *
        ‖iteratedFDerivWithin ℝ m q W x‖ *
        ‖iteratedFDerivWithin ℝ (k - m) g W x‖ := hsmul
    _ ≤ ∑ m ∈ Finset.range (k + 1), (k.choose m : ℝ) * (Q : ℝ) * G := by
      apply Finset.sum_le_sum
      intro m hm
      have hm' : m ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
      have hkm : k - m ≤ k := Nat.sub_le _ _
      calc
        (k.choose m : ℝ) * ‖iteratedFDerivWithin ℝ m q W x‖ *
            ‖iteratedFDerivWithin ℝ (k - m) g W x‖ ≤
            (k.choose m : ℝ) * (Q : ℝ) *
              ‖iteratedFDerivWithin ℝ (k - m) g W x‖ := by
          gcongr
          exact hqWithin m hm'
        _ ≤ (k.choose m : ℝ) * (Q : ℝ) * G := by
          gcongr
          exact hgWithin (k - m) hkm
    _ = (2 : ℝ) ^ k * (Q : ℝ) * G := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      have hchoose :
          (∑ m ∈ Finset.range (k + 1), (k.choose m : ℝ)) = (2 : ℝ) ^ k := by
        norm_cast
        exact Nat.sum_range_choose k
      rw [hchoose]
    _ = ((2 : ℝ≥0) ^ k * Q * G : ℝ≥0) := by
      norm_cast

private theorem inverse_entry_successor_norm_from_factor_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n k : ℕ} {W K : Set E} {Q G : ℝ≥0}
    (hW : IsOpen W) (hKW : K ⊆ W)
    (A : E → Matrix (Fin n) (Fin n) ℂ)
    (hASmooth : ∀ a b, ContDiffOn ℝ ∞ (fun z ↦ A z a b) W)
    (hUnit : ∀ z ∈ W, IsUnit (A z)) (i j : Fin n)
    (hQJet : ∀ a b, ∀ m ≤ k, ∀ z ∈ K,
      ‖iteratedFDeriv ℝ m (fun z ↦ (A z)⁻¹ i a * (A z)⁻¹ b j) z‖ ≤ Q)
    (hGJet : ∀ a b, ∀ m ≤ k, ∀ z ∈ K,
      ‖iteratedFDeriv ℝ m (fun z ↦ fderiv ℝ (fun y ↦ A y a b) z) z‖ ≤ G)
    (x : E) (hx : x ∈ K) :
    ‖iteratedFDeriv ℝ (k + 1) (fun z ↦ (A z)⁻¹ i j) x‖ ≤
      (n : ℝ≥0) ^ 2 * (2 : ℝ≥0) ^ k * Q * G := by
  let F : E → E →L[ℝ] ℂ := fun z ↦ fderiv ℝ (fun y ↦ (A y)⁻¹ i j) z
  let q (a b : Fin n) : E → ℂ := fun z ↦ (A z)⁻¹ i a * (A z)⁻¹ b j
  let g (a b : Fin n) : E → E →L[ℝ] ℂ := fun z ↦ fderiv ℝ (fun y ↦ A y a b) z
  let term (a b : Fin n) : E → E →L[ℝ] ℂ := fun z ↦ q a b z • g a b z
  have hInvSmooth (a b : Fin n) :
      ContDiffOn ℝ ∞ (fun z ↦ (A z)⁻¹ a b) W :=
    Matrix.contDiffOn_inverse_entries (fun a b ↦ hASmooth a b)
      (fun z hz ↦ hUnit z hz) a b
  have hQSmooth (a b : Fin n) : ContDiffOn ℝ ∞ (q a b) W := by
    dsimp [q]
    exact (hInvSmooth i a).mul (hInvSmooth b j)
  have hGSmooth (a b : Fin n) : ContDiffOn ℝ ∞ (g a b) W := by
    dsimp [g]
    exact (hASmooth a b).fderiv_of_isOpen hW (by simp)
  have hTermSmooth (a b : Fin n) : ContDiffOn ℝ ∞ (term a b) W := by
    dsimp [term]
    exact (hQSmooth a b).smul (hGSmooth a b)
  have hn : (k : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    exact_mod_cast (le_top : (k : ℕ∞) ≤ (⊤ : ℕ∞))
  have hEqFun (z : E) (hz : z ∈ W) :
      F z = -∑ a : Fin n, ∑ b : Fin n, term a b z := by
    simpa [F, term, q, g] using
      inverse_entry_fderiv_clm_formula hW A hASmooth hUnit z hz i j
  have hInnerSmooth (a : Fin n) :
      ContDiffOn ℝ ∞ (fun z ↦ ∑ b : Fin n, term a b z) W := by
    apply ContDiffOn.sum
    intro b hb
    exact hTermSmooth a b
  have hJetEq : iteratedFDerivWithin ℝ k F W x =
      -∑ a : Fin n, ∑ b : Fin n, iteratedFDerivWithin ℝ k (term a b) W x := by
    calc
      _ = iteratedFDerivWithin ℝ k
          (fun z ↦ -∑ a : Fin n, ∑ b : Fin n, term a b z) W x :=
        iteratedFDerivWithin_congr (fun z hz ↦ hEqFun z hz) (hKW hx) k
      _ = -iteratedFDerivWithin ℝ k
          (fun z ↦ ∑ a : Fin n, ∑ b : Fin n, term a b z) W x :=
        iteratedFDerivWithin_neg_apply hW.uniqueDiffOn (hKW hx)
      _ = -∑ a : Fin n, iteratedFDerivWithin ℝ k
          (fun z ↦ ∑ b : Fin n, term a b z) W x := by
        congr 1
        exact iteratedFDerivWithin_fun_sum_apply hW.uniqueDiffOn (hKW hx)
          (fun a ha ↦ (hInnerSmooth a).contDiffWithinAt (hKW hx) |>.of_le hn)
      _ = -∑ a : Fin n, ∑ b : Fin n,
          iteratedFDerivWithin ℝ k (term a b) W x := by
        congr 1
        apply Finset.sum_congr rfl
        intro a ha
        exact iteratedFDerivWithin_fun_sum_apply hW.uniqueDiffOn (hKW hx)
          (fun b hb ↦ (hTermSmooth a b).contDiffWithinAt (hKW hx) |>.of_le hn)
  have hTermBound (a b : Fin n) :
      ‖iteratedFDeriv ℝ k (term a b) x‖ ≤ (2 : ℝ≥0) ^ k * Q * G := by
    exact norm_smul_jet_bound hW hKW (q a b) (g a b)
      (hQSmooth a b) (hGSmooth a b)
      (fun m hm z hz ↦ hQJet a b m hm z hz)
      (fun m hm z hz ↦ hGJet a b m hm z hz) x hx
  have hTermWithinBound (a b : Fin n) :
      ‖iteratedFDerivWithin ℝ k (term a b) W x‖ ≤
        (2 : ℝ) ^ k * (Q : ℝ) * G := by
    rw [iteratedFDerivWithin_of_isOpen k hW (hKW hx)]
    exact_mod_cast hTermBound a b
  have hWithinEq : iteratedFDerivWithin ℝ k F W x = iteratedFDeriv ℝ k F x :=
    iteratedFDerivWithin_of_isOpen k hW (hKW hx)
  have hnorm : ‖iteratedFDerivWithin ℝ k F W x‖ ≤
      (n : ℝ) ^ 2 * (2 : ℝ) ^ k * (Q : ℝ) * G := by
    rw [hJetEq]
    calc
      ‖-∑ a : Fin n, ∑ b : Fin n,
          iteratedFDerivWithin ℝ k (term a b) W x‖ ≤
        ∑ a : Fin n, ∑ b : Fin n,
          ‖iteratedFDerivWithin ℝ k (term a b) W x‖ := by
        rw [norm_neg]
        exact (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun a ha ↦ norm_sum_le _ _)
      _ ≤ ∑ a : Fin n, ∑ b : Fin n,
          (2 : ℝ) ^ k * (Q : ℝ) * G := by
        apply Finset.sum_le_sum
        intro a ha
        apply Finset.sum_le_sum
        intro b hb
        exact hTermWithinBound a b
      _ = (n : ℝ) ^ 2 * (2 : ℝ) ^ k * (Q : ℝ) * G := by
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
  calc
    ‖iteratedFDeriv ℝ (k + 1) (fun z ↦ (A z)⁻¹ i j) x‖ =
        ‖iteratedFDeriv ℝ k F x‖ := by
          exact (norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (n := k)
            (f := fun z ↦ (A z)⁻¹ i j) (x := x)).symm
    _ = ‖iteratedFDerivWithin ℝ k F W x‖ := by rw [hWithinEq]
    _ ≤ (n : ℝ) ^ 2 * (2 : ℝ) ^ k * (Q : ℝ) * G := hnorm
    _ = ((n : ℝ≥0) ^ 2 * (2 : ℝ≥0) ^ k * Q * G : ℝ≥0) := by norm_cast

private theorem inverse_entry_successor_norm_step
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n k : ℕ} {W K : Set E} {R C : ℝ≥0}
    (hW : IsOpen W) (hKW : K ⊆ W)
    (A : E → Matrix (Fin n) (Fin n) ℂ)
    (hASmooth : ∀ a b, ContDiffOn ℝ ∞ (fun z ↦ A z a b) W)
    (hUnit : ∀ z ∈ W, IsUnit (A z))
    (hAJet : ∀ a b, ∀ m ≤ k + 1, ∀ z ∈ K,
      ‖iteratedFDeriv ℝ m (fun z ↦ A z a b) z‖ ≤ C)
    (hInvJet : ∀ a b, ∀ m ≤ k, ∀ z ∈ K,
      ‖iteratedFDeriv ℝ m (fun z ↦ (A z)⁻¹ a b) z‖ ≤ R)
    (x : E) (hx : x ∈ K) (i j : Fin n) :
    ‖iteratedFDeriv ℝ (k + 1) (fun z ↦ (A z)⁻¹ i j) x‖ ≤
      (n : ℝ≥0) ^ 2 * (4 : ℝ≥0) ^ k * R ^ 2 * C := by
  have hInvSmooth (a b : Fin n) :
      ContDiffOn ℝ ∞ (fun z ↦ (A z)⁻¹ a b) W :=
    Matrix.contDiffOn_inverse_entries (fun a b ↦ hASmooth a b)
      (fun z hz ↦ hUnit z hz) a b
  have hn (m : ℕ) : (m : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    exact_mod_cast (le_top : (m : ℕ∞) ≤ (⊤ : ℕ∞))
  have hQJet (a b : Fin n) (m : ℕ) (hm : m ≤ k) (z : E) (hz : z ∈ K) :
      ‖iteratedFDeriv ℝ m
        (fun z ↦ (A z)⁻¹ i a * (A z)⁻¹ b j) z‖ ≤ (2 : ℝ≥0) ^ k * R ^ 2 := by
    have hwithin := norm_iteratedFDerivWithin_mul_le
      (hInvSmooth i a) (hInvSmooth b j) hW.uniqueDiffOn (hKW hz) (hn m)
    have hInvWithin (r : ℕ) (hr : r ≤ m) (u v : Fin n) :
        ‖iteratedFDerivWithin ℝ r (fun z ↦ (A z)⁻¹ u v) W z‖ ≤ (R : ℝ) := by
      rw [iteratedFDerivWithin_of_isOpen r hW (hKW hz)]
      exact_mod_cast hInvJet u v r (le_trans hr hm) z hz
    rw [← iteratedFDerivWithin_of_isOpen m hW (hKW hz)]
    calc
      ‖iteratedFDerivWithin ℝ m
          (fun z ↦ (A z)⁻¹ i a * (A z)⁻¹ b j) W z‖ ≤
        ∑ r ∈ Finset.range (m + 1), (m.choose r : ℝ) *
          ‖iteratedFDerivWithin ℝ r (fun z ↦ (A z)⁻¹ i a) W z‖ *
          ‖iteratedFDerivWithin ℝ (m - r) (fun z ↦ (A z)⁻¹ b j) W z‖ := hwithin
      _ ≤ ∑ r ∈ Finset.range (m + 1), (m.choose r : ℝ) * (R : ℝ) * R := by
        apply Finset.sum_le_sum
        intro r hr
        have hrm : r ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
        have hmr : m - r ≤ m := Nat.sub_le _ _
        calc
          (m.choose r : ℝ) *
              ‖iteratedFDerivWithin ℝ r (fun z ↦ (A z)⁻¹ i a) W z‖ *
              ‖iteratedFDerivWithin ℝ (m - r) (fun z ↦ (A z)⁻¹ b j) W z‖ ≤
              (m.choose r : ℝ) * (R : ℝ) *
                ‖iteratedFDerivWithin ℝ (m - r) (fun z ↦ (A z)⁻¹ b j) W z‖ := by
            gcongr
            exact hInvWithin r hrm i a
          _ ≤ (m.choose r : ℝ) * (R : ℝ) * R := by
            gcongr
            exact hInvWithin (m - r) hmr b j
      _ = (2 : ℝ) ^ m * (R : ℝ) ^ 2 := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        have hchoose :
            (∑ r ∈ Finset.range (m + 1), (m.choose r : ℝ)) = (2 : ℝ) ^ m := by
          norm_cast
          exact Nat.sum_range_choose m
        rw [hchoose]
        ring
      _ ≤ (2 : ℝ) ^ k * (R : ℝ) ^ 2 := by
        gcongr
        norm_num
  have hGJet (a b : Fin n) (m : ℕ) (hm : m ≤ k) (z : E) (hz : z ∈ K) :
      ‖iteratedFDeriv ℝ m (fun z ↦ fderiv ℝ (fun y ↦ A y a b) z) z‖ ≤ C := by
    rw [norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (n := m)
      (f := fun z ↦ A z a b) (x := z)]
    exact hAJet a b (m + 1) (by omega) z hz
  have hStep := inverse_entry_successor_norm_from_factor_bounds
    (Q := (2 : ℝ≥0) ^ k * R ^ 2) (G := C)
    hW hKW A hASmooth hUnit i j hQJet hGJet x hx
  have hStepReal :
      ‖iteratedFDeriv ℝ (k + 1) (fun z ↦ (A z)⁻¹ i j) x‖ ≤
        (n : ℝ) ^ 2 * (2 : ℝ) ^ k * ((2 : ℝ) ^ k * (R : ℝ) ^ 2) * C := by
    exact_mod_cast hStep
  have hpowReal : (2 : ℝ) ^ k * (2 : ℝ) ^ k = (4 : ℝ) ^ k := by
    calc
      (2 : ℝ) ^ k * (2 : ℝ) ^ k = (2 : ℝ) ^ (k + k) := by rw [pow_add]
      _ = ((2 : ℝ) ^ 2) ^ k := by
        rw [show k + k = 2 * k by omega, pow_mul]
      _ = (4 : ℝ) ^ k := by norm_num
  calc
    ‖iteratedFDeriv ℝ (k + 1) (fun z ↦ (A z)⁻¹ i j) x‖ ≤
        (n : ℝ) ^ 2 * (2 : ℝ) ^ k * ((2 : ℝ) ^ k * (R : ℝ) ^ 2) * C := hStepReal
    _ = (n : ℝ) ^ 2 * (4 : ℝ) ^ k * (R : ℝ) ^ 2 * C := by
      rw [← hpowReal]
      ring
    _ = ((n : ℝ≥0) ^ 2 * (4 : ℝ≥0) ^ k * R ^ 2 * C : ℝ≥0) := by norm_cast

/-- Uniform entrywise bounds on the input jets and on inverse values give a single finite
bound on every inverse-entry jet through order `k`. The set `K` need not be convex or compact;
ordinary derivatives are computed on its open neighborhood `W`. -/
public theorem exists_normBoundOn_matrix_inverse_entry_jets
    {P E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n k : ℕ} {C B : ℝ≥0} {W K : Set E}
    (S : Set P) (hW : IsOpen W) (hKW : K ⊆ W)
    (A : P → E → Matrix (Fin n) (Fin n) ℂ)
    (hASmooth : ∀ p ∈ S, ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ A p z i j) W)
    (hAJet : ∀ p ∈ S, ∀ i j, ∀ m ≤ k, ∀ z ∈ K,
      ‖iteratedFDeriv ℝ m (fun z ↦ A p z i j) z‖ ≤ C)
    (hUnit : ∀ p ∈ S, ∀ z ∈ W, IsUnit (A p z))
    (hInv : ∀ p ∈ S, ∀ z ∈ K, ∀ i j, ‖(A p z)⁻¹ i j‖ ≤ B) :
    ∃ D : ℝ≥0, ∀ p ∈ S, ∀ i j, ∀ m ≤ k, ∀ z ∈ K,
      ‖iteratedFDeriv ℝ m (fun z ↦ (A p z)⁻¹ i j) z‖ ≤ D := by
  induction k with
  | zero =>
      refine ⟨B, ?_⟩
      intro p hp i j m hm z hz
      have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
      subst m
      rw [norm_iteratedFDeriv_zero]
      exact hInv p hp z hz i j
  | succ k ih =>
      have hAJetPrev : ∀ p ∈ S, ∀ i j, ∀ m ≤ k, ∀ z ∈ K,
          ‖iteratedFDeriv ℝ m (fun z ↦ A p z i j) z‖ ≤ C := by
        intro p hp i j m hm z hz
        exact hAJet p hp i j m (Nat.le_succ_of_le hm) z hz
      obtain ⟨Dold, hOld⟩ := ih hAJetPrev
      let R : ℝ≥0 := max B Dold
      have hInvJet : ∀ p ∈ S, ∀ i j, ∀ m ≤ k, ∀ z ∈ K,
          ‖iteratedFDeriv ℝ m (fun z ↦ (A p z)⁻¹ i j) z‖ ≤ R := by
        intro p hp i j m hm z hz
        by_cases hm0 : m = 0
        · subst m
          rw [norm_iteratedFDeriv_zero]
          exact (hInv p hp z hz i j).trans (le_max_left B Dold)
        · exact (hOld p hp i j m hm z hz).trans (le_max_right B Dold)
      let Dnext : ℝ≥0 := (n : ℝ≥0) ^ 2 * (4 : ℝ≥0) ^ k * R ^ 2 * C
      let D : ℝ≥0 := max R Dnext
      refine ⟨D, ?_⟩
      intro p hp i j m hm z hz
      by_cases hmk : m ≤ k
      · exact (hInvJet p hp i j m hmk z hz).trans (le_max_left R Dnext)
      · have hmeq : m = k + 1 := by omega
        subst m
        have hstep := inverse_entry_successor_norm_step hW hKW (A p)
          (fun a b ↦ hASmooth p hp a b)
          (fun z hz ↦ hUnit p hp z hz)
          (fun a b m hm z hz ↦ hAJet p hp a b m (by omega) z hz)
          (fun a b m hm z hz ↦ hInvJet p hp a b m hm z hz)
          z hz i j
        exact hstep.trans (le_max_right R Dnext)

end KahlerForm
