module

public import CalabiYau.Mathlib.Geometry.Manifold.Holder
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Hölder control of finite inverse-matrix jets

The translated resolvent identity writes a difference of inverse jets as a finite
double sum of jets of products. The product rule and uniform inverse-jet bounds
then transfer entrywise Hölder control of all input jets to the top inverse jet.
-/

@[expose] public section

open Set
open scoped ContDiff NNReal Topology

private theorem product_jet_bound_at_zero
    {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedRing A] [NormedAlgebra ℝ A]
    {T : Set E} {r n : ℕ} {C D : ℝ≥0} {f g : E → A}
    (hT : IsOpen T) (h0 : (0 : E) ∈ T)
    (hf : ContDiffOn ℝ r f T) (hg : ContDiffOn ℝ r g T)
    (hfb : ∀ j ≤ r, ‖iteratedFDeriv ℝ j f (0 : E)‖ ≤ C)
    (hgb : ∀ j ≤ r, ‖iteratedFDeriv ℝ j g (0 : E)‖ ≤ D)
    (hn : n ≤ r) :
    ‖iteratedFDeriv ℝ n (fun x ↦ f x * g x) (0 : E)‖ ≤
      (2 : ℝ) ^ r * (C : ℝ) * (D : ℝ) := by
  have hprod : ContDiffOn ℝ r (fun x ↦ f x * g x) T := hf.mul hg
  have hn' : (n : ℕ∞ω) ≤ (r : ℕ∞ω) := by exact_mod_cast hn
  have hprodWithin := norm_iteratedFDerivWithin_mul_le hf hg hT.uniqueDiffOn h0 hn'
  have heq (j : ℕ) (hj : j ≤ r) (u : E → A) (hu : ContDiffOn ℝ r u T) :
      iteratedFDerivWithin ℝ j u T (0 : E) = iteratedFDeriv ℝ j u (0 : E) := by
    apply iteratedFDerivWithin_eq_iteratedFDeriv hT.uniqueDiffOn
    · exact (hu.contDiffAt (hT.mem_nhds h0)).of_le (by exact_mod_cast hj)
    · exact h0
  have hsum :
      (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i f T (0 : E)‖ *
          ‖iteratedFDerivWithin ℝ (n - i) g T (0 : E)‖) ≤
        (2 : ℝ) ^ n * (C : ℝ) * (D : ℝ) := by
    calc
      _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i f (0 : E)‖ *
            ‖iteratedFDeriv ℝ (n - i) g (0 : E)‖ := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        rw [heq i (le_trans hi' hn) f hf,
          heq (n - i) (le_trans (Nat.sub_le _ _) hn) g hg]
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (C : ℝ) * (D : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        have hfi : ‖iteratedFDeriv ℝ i f (0 : E)‖ ≤ C := hfb i (le_trans hi' hn)
        have hgi : ‖iteratedFDeriv ℝ (n - i) g (0 : E)‖ ≤ D :=
          hgb (n - i) (le_trans (Nat.sub_le _ _) hn)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hfi (by positivity)) hgi
          (by positivity) (by positivity)
      _ = (2 : ℝ) ^ n * (C : ℝ) * (D : ℝ) := by
        have hchoose :
            (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = (2 : ℝ) ^ n := by
          exact_mod_cast Nat.sum_range_choose n
        calc
          _ = (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) *
                ((C : ℝ) * (D : ℝ)) := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i hi
              ring
          _ = (2 : ℝ) ^ n * (C : ℝ) * (D : ℝ) := by rw [hchoose]; ring
  calc
    ‖iteratedFDeriv ℝ n (fun x ↦ f x * g x) (0 : E)‖ =
        ‖iteratedFDerivWithin ℝ n (fun x ↦ f x * g x) T (0 : E)‖ := by
      rw [heq n hn (fun x ↦ f x * g x) hprod]
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i f T (0 : E)‖ *
          ‖iteratedFDerivWithin ℝ (n - i) g T (0 : E)‖ := hprodWithin
    _ ≤ (2 : ℝ) ^ n * (C : ℝ) * (D : ℝ) := hsum
    _ ≤ (2 : ℝ) ^ r * (C : ℝ) * (D : ℝ) := by
      gcongr
      norm_num

private theorem triple_jet_bound_at_zero
    {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedRing A] [NormedAlgebra ℝ A]
    {T : Set E} {r n : ℕ} {C D E₀ : ℝ≥0} {f g h : E → A}
    (hT : IsOpen T) (h0 : (0 : E) ∈ T)
    (hf : ContDiffOn ℝ r f T) (hg : ContDiffOn ℝ r g T) (hh : ContDiffOn ℝ r h T)
    (hfb : ∀ j ≤ r, ‖iteratedFDeriv ℝ j f (0 : E)‖ ≤ C)
    (hgb : ∀ j ≤ r, ‖iteratedFDeriv ℝ j g (0 : E)‖ ≤ D)
    (hhb : ∀ j ≤ r, ‖iteratedFDeriv ℝ j h (0 : E)‖ ≤ E₀)
    (hn : n ≤ r) :
    ‖iteratedFDeriv ℝ n (fun x ↦ (f x * g x) * h x) (0 : E)‖ ≤
      ((2 : ℝ) ^ r) ^ 2 * (C : ℝ) * (D : ℝ) * (E₀ : ℝ) := by
  let B : ℝ≥0 := (2 : ℝ≥0) ^ r * C * D
  have hBcoe : (B : ℝ) = (2 : ℝ) ^ r * (C : ℝ) * (D : ℝ) := by simp [B]
  have hB : ∀ j ≤ r, ‖iteratedFDeriv ℝ j (fun x ↦ f x * g x) (0 : E)‖ ≤ B := by
    intro j hj
    have hjbound := product_jet_bound_at_zero hT h0 hf hg hfb hgb hj
    rw [hBcoe]
    exact hjbound
  have htriple := product_jet_bound_at_zero hT h0 (hf.mul hg) hh hB hhb hn
  calc
    ‖iteratedFDeriv ℝ n (fun x ↦ (f x * g x) * h x) (0 : E)‖ ≤
        (2 : ℝ) ^ r * (B : ℝ) * (E₀ : ℝ) := htriple
    _ = ((2 : ℝ) ^ r) ^ 2 * (C : ℝ) * (D : ℝ) * (E₀ : ℝ) := by
      rw [hBcoe]
      ring

private theorem finite_sum_jet_bound_at_zero
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {T : Set E} {r m : ℕ} {s : Finset ι}
    {C : ι → ℝ≥0} {f : ι → E → F}
    (hT : IsOpen T) (h0 : (0 : E) ∈ T)
    (hcont : ∀ i ∈ s, ContDiffOn ℝ r (f i) T)
    (hbound : ∀ i ∈ s, ∀ j ≤ r,
      ‖iteratedFDeriv ℝ j (f i) (0 : E)‖ ≤ C i)
    (hm : m ≤ r) :
    ‖iteratedFDeriv ℝ m (fun x ↦ ∑ i ∈ s, f i x) (0 : E)‖ ≤
      ∑ i ∈ s, (C i : ℝ) := by
  have hsumCont : ContDiffOn ℝ r (fun x ↦ ∑ i ∈ s, f i x) T := ContDiffOn.sum hcont
  have hwithinSum :
      iteratedFDerivWithin ℝ m (fun x ↦ ∑ i ∈ s, f i x) T (0 : E) =
        ∑ i ∈ s, iteratedFDerivWithin ℝ m (f i) T (0 : E) := by
    apply iteratedFDerivWithin_fun_sum_apply hT.uniqueDiffOn h0
    intro i hi
    exact (hcont i hi 0 h0).of_le (by exact_mod_cast hm)
  have hsumDeriv :
      iteratedFDeriv ℝ m (fun x ↦ ∑ i ∈ s, f i x) (0 : E) =
        ∑ i ∈ s, iteratedFDeriv ℝ m (f i) (0 : E) := by
    calc
      iteratedFDeriv ℝ m (fun x ↦ ∑ i ∈ s, f i x) (0 : E) =
          iteratedFDerivWithin ℝ m (fun x ↦ ∑ i ∈ s, f i x) T (0 : E) := by
        symm
        apply iteratedFDerivWithin_eq_iteratedFDeriv hT.uniqueDiffOn
        · exact (hsumCont.contDiffAt (hT.mem_nhds h0)).of_le (by exact_mod_cast hm)
        · exact h0
      _ = ∑ i ∈ s, iteratedFDerivWithin ℝ m (f i) T (0 : E) := hwithinSum
      _ = ∑ i ∈ s, iteratedFDeriv ℝ m (f i) (0 : E) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply iteratedFDerivWithin_eq_iteratedFDeriv hT.uniqueDiffOn
        · exact (hcont i hi).contDiffAt (hT.mem_nhds h0) |>.of_le (by exact_mod_cast hm)
        · exact h0
  calc
    ‖iteratedFDeriv ℝ m (fun x ↦ ∑ i ∈ s, f i x) (0 : E)‖ =
        ‖∑ i ∈ s, iteratedFDeriv ℝ m (f i) (0 : E)‖ := by rw [hsumDeriv]
    _ ≤ ∑ i ∈ s, ‖iteratedFDeriv ℝ m (f i) (0 : E)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, (C i : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hbound i hi m hm

/-- A finite n-by-n sum of triple products has a basepoint jet bound from local factor bounds. -/
private theorem auxiliary_double_sum_triple_jet_norm_bound_at_zero
    {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedRing A] [NormedAlgebra ℝ A]
    {T : Set E} {n r m : ℕ} {N D : ℝ≥0}
    {left right : Fin n → E → A} {middle : Fin n → Fin n → E → A}
    (hT : IsOpen T) (h0 : (0 : E) ∈ T)
    (hleft : ∀ i, ContDiffOn ℝ r (left i) T)
    (hmiddle : ∀ i j, ContDiffOn ℝ r (middle i j) T)
    (hright : ∀ j, ContDiffOn ℝ r (right j) T)
    (hleftBound : ∀ i k, k ≤ r →
      ‖iteratedFDeriv ℝ k (left i) (0 : E)‖ ≤ N)
    (hmiddleBound : ∀ i j k, k ≤ r →
      ‖iteratedFDeriv ℝ k (middle i j) (0 : E)‖ ≤ D)
    (hrightBound : ∀ j k, k ≤ r →
      ‖iteratedFDeriv ℝ k (right j) (0 : E)‖ ≤ N)
    (hm : m ≤ r) :
    ‖iteratedFDeriv ℝ m
        (fun x ↦ ∑ p : Fin n × Fin n,
          (left p.1 x * middle p.1 p.2 x) * right p.2 x) (0 : E)‖ ≤
      (n : ℝ) ^ 2 * ((2 : ℝ) ^ r) ^ 2 * (N : ℝ) ^ 2 * (D : ℝ) := by
  let B : ℝ≥0 := ((2 : ℝ≥0) ^ r) ^ 2 * N * D * N
  have hBcoe : (B : ℝ) = ((2 : ℝ) ^ r) ^ 2 * (N : ℝ) * (D : ℝ) * (N : ℝ) := by
    simp [B]
  let term : Fin n × Fin n → E → A :=
    fun (p : Fin n × Fin n) x ↦ (left p.1 x * middle p.1 p.2 x) * right p.2 x
  have htermCont : ∀ p ∈ Finset.univ, ContDiffOn ℝ r (term p) T := by
    intro p hp
    exact ((hleft p.1).mul (hmiddle p.1 p.2)).mul (hright p.2)
  have htermBound : ∀ p ∈ Finset.univ, ∀ k ≤ r,
      ‖iteratedFDeriv ℝ k (term p) (0 : E)‖ ≤ B := by
    intro p hp k hk
    obtain ⟨i, j⟩ := p
    have htriple := triple_jet_bound_at_zero hT h0
      (hleft i) (hmiddle i j) (hright j)
      (hleftBound i) (hmiddleBound i j) (hrightBound j) hk
    rw [hBcoe]
    exact htriple
  have hsum := finite_sum_jet_bound_at_zero hT h0 htermCont htermBound hm
  calc
    ‖iteratedFDeriv ℝ m (fun x ↦ ∑ p ∈ Finset.univ, term p x) (0 : E)‖ ≤
        ∑ p ∈ Finset.univ, (B : ℝ) := hsum
    _ = (n : ℝ) ^ 2 * ((2 : ℝ) ^ r) ^ 2 * (N : ℝ) ^ 2 * (D : ℝ) := by
      simp [Finset.sum_const, B]
      ring

/-- The top-order specialization, with its constant kept as an `ℝ≥0` expression. -/
private theorem auxiliary_double_sum_r_jet_nnreal_bound_at_zero
    {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedRing A] [NormedAlgebra ℝ A]
    {T : Set E} {n r : ℕ} {N D : ℝ≥0}
    {left right : Fin n → E → A} {middle : Fin n → Fin n → E → A}
    (hT : IsOpen T) (h0 : (0 : E) ∈ T)
    (hleft : ∀ i, ContDiffOn ℝ r (left i) T)
    (hmiddle : ∀ i j, ContDiffOn ℝ r (middle i j) T)
    (hright : ∀ j, ContDiffOn ℝ r (right j) T)
    (hleftBound : ∀ i k, k ≤ r →
      ‖iteratedFDeriv ℝ k (left i) (0 : E)‖ ≤ N)
    (hmiddleBound : ∀ i j k, k ≤ r →
      ‖iteratedFDeriv ℝ k (middle i j) (0 : E)‖ ≤ D)
    (hrightBound : ∀ j k, k ≤ r →
      ‖iteratedFDeriv ℝ k (right j) (0 : E)‖ ≤ N) :
    ‖iteratedFDeriv ℝ r
        (fun x ↦ ∑ p : Fin n × Fin n,
          (left p.1 x * middle p.1 p.2 x) * right p.2 x) (0 : E)‖ ≤
      (((n : ℝ≥0) ^ 2) * ((2 : ℝ≥0) ^ r) ^ 2 * N ^ 2 * D : ℝ) := by
  have h := auxiliary_double_sum_triple_jet_norm_bound_at_zero hT h0 hleft hmiddle hright
    hleftBound hmiddleBound hrightBound (Nat.le_refl r)
  convert h using 1
  · push_cast
    ring

/-- Real-norm form of the top-order double-sum estimate, with the power of four explicit. -/
private theorem auxiliary_double_sum_r_jet_real_bound_at_zero
    {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedRing A] [NormedAlgebra ℝ A]
    {T : Set E} {n r : ℕ} {N D : ℝ≥0}
    {left right : Fin n → E → A} {middle : Fin n → Fin n → E → A}
    (hT : IsOpen T) (h0 : (0 : E) ∈ T)
    (hleft : ∀ i, ContDiffOn ℝ r (left i) T)
    (hmiddle : ∀ i j, ContDiffOn ℝ r (middle i j) T)
    (hright : ∀ j, ContDiffOn ℝ r (right j) T)
    (hleftBound : ∀ i k, k ≤ r →
      ‖iteratedFDeriv ℝ k (left i) (0 : E)‖ ≤ N)
    (hmiddleBound : ∀ i j k, k ≤ r →
      ‖iteratedFDeriv ℝ k (middle i j) (0 : E)‖ ≤ D)
    (hrightBound : ∀ j k, k ≤ r →
      ‖iteratedFDeriv ℝ k (right j) (0 : E)‖ ≤ N) :
    ‖iteratedFDeriv ℝ r
        (fun x ↦ ∑ p : Fin n × Fin n,
          (left p.1 x * middle p.1 p.2 x) * right p.2 x) (0 : E)‖ ≤
      (n : ℝ) ^ 2 * (4 : ℝ) ^ r * (N : ℝ) ^ 2 * (D : ℝ) := by
  have h := auxiliary_double_sum_triple_jet_norm_bound_at_zero hT h0 hleft hmiddle hright
    hleftBound hmiddleBound hrightBound (Nat.le_refl r)
  have hpow : ((2 : ℝ) ^ r) ^ 2 = (4 : ℝ) ^ r := by
    calc
      ((2 : ℝ) ^ r) ^ 2 = (2 : ℝ) ^ (r * 2) := by rw [← pow_mul]
      _ = (2 : ℝ) ^ (2 * r) := by rw [Nat.mul_comm]
      _ = ((2 : ℝ) ^ 2) ^ r := by rw [← pow_mul]
      _ = (4 : ℝ) ^ r := by norm_num
  calc
    _ ≤ (n : ℝ) ^ 2 * ((2 : ℝ) ^ r) ^ 2 * (N : ℝ) ^ 2 * (D : ℝ) := h
    _ = (n : ℝ) ^ 2 * (4 : ℝ) ^ r * (N : ℝ) ^ 2 * (D : ℝ) := by rw [hpow]

/-- A shifted resolvent triple on the common translation neighborhood of two points. -/
private theorem auxiliary_shifted_resolvent_double_sum_bound
    {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedRing A] [NormedAlgebra ℝ A]
    {V : Set E} {x y : E} {n r : ℕ} {N D : ℝ≥0}
    (a b : Fin n)
    (hV : IsOpen V) (hx : x ∈ V) (hy : y ∈ V)
    {invX invY source : Fin n → Fin n → E → A}
    (hInvX : ∀ i j, ContDiffOn ℝ r (fun t => invX i j (x + t))
      {t | x + t ∈ V ∧ y + t ∈ V})
    (hInvY : ∀ i j, ContDiffOn ℝ r (fun t => invY i j (y + t))
      {t | x + t ∈ V ∧ y + t ∈ V})
    (hSourceDiff : ∀ i j, ContDiffOn ℝ r
      (fun t => source i j (y + t) - source i j (x + t))
      {t | x + t ∈ V ∧ y + t ∈ V})
    (hInvXBound : ∀ i j k, k ≤ r →
      ‖iteratedFDeriv ℝ k (fun t => invX i j (x + t)) (0 : E)‖ ≤ N)
    (hInvYBound : ∀ i j k, k ≤ r →
      ‖iteratedFDeriv ℝ k (fun t => invY i j (y + t)) (0 : E)‖ ≤ N)
    (hSourceDiffBound : ∀ i j k, k ≤ r →
      ‖iteratedFDeriv ℝ k
        (fun t => source i j (y + t) - source i j (x + t)) (0 : E)‖ ≤ D) :
    ‖iteratedFDeriv ℝ r
      (fun t => ∑ p : Fin n × Fin n,
        (invX a p.1 (x + t) *
          (source p.1 p.2 (y + t) - source p.1 p.2 (x + t))) *
          invY p.2 b (y + t)) (0 : E)‖ ≤
      (n : ℝ) ^ 2 * (4 : ℝ) ^ r * (N : ℝ) ^ 2 * (D : ℝ) := by
  let T : Set E := {t | x + t ∈ V ∧ y + t ∈ V}
  have hT : IsOpen T := by
    change IsOpen ({t : E | x + t ∈ V} ∩ {t : E | y + t ∈ V})
    exact (hV.preimage (continuous_const.add continuous_id)).inter
      (hV.preimage (continuous_const.add continuous_id))
  have h0 : (0 : E) ∈ T := by
    change x + 0 ∈ V ∧ y + 0 ∈ V
    simpa using And.intro hx hy
  have hleft : ∀ i, ContDiffOn ℝ r (fun t => invX a i (x + t)) T := by
    intro i
    exact hInvX a i
  have hmiddle : ∀ i j, ContDiffOn ℝ r
      (fun t => source i j (y + t) - source i j (x + t)) T := by
    intro i j
    exact hSourceDiff i j
  have hright : ∀ j, ContDiffOn ℝ r (fun t => invY j b (y + t)) T := by
    intro j
    exact hInvY j b
  have hleftBound : ∀ i k, k ≤ r →
      ‖iteratedFDeriv ℝ k (fun t => invX a i (x + t)) (0 : E)‖ ≤ N := by
    intro i k hk
    exact hInvXBound a i k hk
  have hmiddleBound : ∀ i j k, k ≤ r →
      ‖iteratedFDeriv ℝ k
        (fun t => source i j (y + t) - source i j (x + t)) (0 : E)‖ ≤ D := by
    intro i j k hk
    exact hSourceDiffBound i j k hk
  have hrightBound : ∀ j k, k ≤ r →
      ‖iteratedFDeriv ℝ k (fun t => invY j b (y + t)) (0 : E)‖ ≤ N := by
    intro j k hk
    exact hInvYBound j b k hk
  have hsum := auxiliary_double_sum_r_jet_real_bound_at_zero hT h0
    hleft hmiddle hright hleftBound hmiddleBound hrightBound
  exact hsum

private theorem holder_norm_probe
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {C α : ℝ≥0} {f : X → Y} {K : Set X} {x y : X}
    (h : HolderOnWith C α f K) (hx : x ∈ K) (hy : y ∈ K) :
    ‖f x - f y‖ ≤ (C : ℝ) * dist x y ^ (α : ℝ) := by
  have hh := h x hx y hy
  rw [edist_dist, dist_eq_norm] at hh
  have hpow : (ENNReal.ofReal (dist x y)) ^ (α : ℝ) =
      ENNReal.ofReal (dist x y ^ (α : ℝ)) :=
    ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) (NNReal.coe_nonneg α)
  rw [edist_dist, hpow, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul (NNReal.coe_nonneg C)] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh

private theorem auxiliary_shifted_resolvent_double_sum_holder_bound_exact
    {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedRing A] [NormedAlgebra ℝ A]
    {V : Set E} {x y : E} {n r : ℕ} {N C : ℝ≥0} {α : ℝ≥0}
    (a b : Fin n) (hV : IsOpen V) (hx : x ∈ V) (hy : y ∈ V)
    {invX invY source : Fin n → Fin n → E → A}
    (hInvX : ∀ i j, ContDiffOn ℝ r (fun t => invX i j (x + t))
      {t | x + t ∈ V ∧ y + t ∈ V})
    (hInvY : ∀ i j, ContDiffOn ℝ r (fun t => invY i j (y + t))
      {t | x + t ∈ V ∧ y + t ∈ V})
    (hSourceCont : ∀ i j, ContDiffOn ℝ r (source i j) V)
    (hSourceHolder : ∀ i j k, k ≤ r →
      HolderOnWith C α (fun z => iteratedFDeriv ℝ k (source i j) z) V)
    (hInvXBound : ∀ i j k, k ≤ r →
      ‖iteratedFDeriv ℝ k (fun t => invX i j (x + t)) (0 : E)‖ ≤ N)
    (hInvYBound : ∀ i j k, k ≤ r →
      ‖iteratedFDeriv ℝ k (fun t => invY i j (y + t)) (0 : E)‖ ≤ N) :
    ‖iteratedFDeriv ℝ r
      (fun t => ∑ p : Fin n × Fin n,
        (invX a p.1 (x + t) *
          (source p.1 p.2 (y + t) - source p.1 p.2 (x + t))) *
          invY p.2 b (y + t)) (0 : E)‖ ≤
      (n : ℝ) ^ 2 * ((2 : ℝ) ^ r) ^ 2 * (N : ℝ) ^ 2 * (C : ℝ) *
        Real.rpow (dist x y) (α : ℝ) := by
  let T : Set E := {t | x + t ∈ V ∧ y + t ∈ V}
  have hT : IsOpen T := by
    change IsOpen ({t : E | x + t ∈ V} ∩ {t : E | y + t ∈ V})
    exact (hV.preimage (continuous_const.add continuous_id)).inter
      (hV.preimage (continuous_const.add continuous_id))
  have h0 : (0 : E) ∈ T := by
    change x + 0 ∈ V ∧ y + 0 ∈ V
    simpa using And.intro hx hy
  have htransX : ContDiffOn ℝ r (fun t : E => x + t) T := by fun_prop
  have htransY : ContDiffOn ℝ r (fun t : E => y + t) T := by fun_prop
  have hsourceX : ∀ i j, ContDiffOn ℝ r (fun t => source i j (x + t)) T := by
    intro i j
    exact (hSourceCont i j).comp htransX (by intro t ht; exact ht.1)
  have hsourceY : ∀ i j, ContDiffOn ℝ r (fun t => source i j (y + t)) T := by
    intro i j
    exact (hSourceCont i j).comp htransY (by intro t ht; exact ht.2)
  have hSourceDiff : ∀ i j, ContDiffOn ℝ r
      (fun t => source i j (y + t) - source i j (x + t)) T := by
    intro i j
    exact (hsourceY i j).sub (hsourceX i j)
  let D : ℝ≥0 := ⟨(C : ℝ) * Real.rpow (dist x y) (α : ℝ),
    mul_nonneg (by positivity) (Real.rpow_nonneg (dist_nonneg) _)⟩
  have hD : (D : ℝ) = (C : ℝ) * Real.rpow (dist x y) (α : ℝ) := rfl
  have hSourceDiffBound : ∀ i j k, k ≤ r →
      ‖iteratedFDeriv ℝ k
        (fun t => source i j (y + t) - source i j (x + t)) (0 : E)‖ ≤ D := by
    intro i j k hk
    have hYat : ContDiffAt ℝ k (fun t => source i j (y + t)) (0 : E) :=
      (hsourceY i j).contDiffAt (hT.mem_nhds h0) |>.of_le (by exact_mod_cast hk)
    have hXat : ContDiffAt ℝ k (fun t => source i j (x + t)) (0 : E) :=
      (hsourceX i j).contDiffAt (hT.mem_nhds h0) |>.of_le (by exact_mod_cast hk)
    have hYshift : iteratedFDeriv ℝ k (fun t => source i j (y + t)) (0 : E) =
        iteratedFDeriv ℝ k (source i j) y := by
      simpa using (iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := source i j) k y (0 : E))
    have hXshift : iteratedFDeriv ℝ k (fun t => source i j (x + t)) (0 : E) =
        iteratedFDeriv ℝ k (source i j) x := by
      simpa using (iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := source i j) k x (0 : E))
    have hderivDiff := iteratedFDeriv_sub_apply hYat hXat
    rw [hYshift, hXshift] at hderivDiff
    have hderivDiff' : iteratedFDeriv ℝ k
        (fun t => source i j (y + t) - source i j (x + t)) (0 : E) =
        iteratedFDeriv ℝ k (source i j) y - iteratedFDeriv ℝ k (source i j) x := by
      have hfun : (fun t : E => source i j (y + t) - source i j (x + t)) =
          (fun t : E => source i j (y + t)) - (fun t : E => source i j (x + t)) := by
        funext t
        rfl
      rw [hfun]
      exact hderivDiff
    have hh := holder_norm_probe (hSourceHolder i j k hk) hy hx
    calc
      ‖iteratedFDeriv ℝ k
          (fun t => source i j (y + t) - source i j (x + t)) (0 : E)‖ =
          ‖iteratedFDeriv ℝ k (source i j) y - iteratedFDeriv ℝ k (source i j) x‖ := by
        rw [hderivDiff']
      _ ≤ (C : ℝ) * dist y x ^ (α : ℝ) := hh
      _ = (D : ℝ) := by rw [dist_comm, ← Real.rpow_eq_pow, hD]
  have hsum := auxiliary_shifted_resolvent_double_sum_bound
    (N := N) (D := D) a b hV hx hy hInvX hInvY hSourceDiff
    hInvXBound hInvYBound hSourceDiffBound
  have hpow : ((2 : ℝ) ^ r) ^ 2 = (4 : ℝ) ^ r := by
    calc
      ((2 : ℝ) ^ r) ^ 2 = (2 : ℝ) ^ (r * 2) := by rw [← pow_mul]
      _ = (2 : ℝ) ^ (2 * r) := by rw [Nat.mul_comm]
      _ = ((2 : ℝ) ^ 2) ^ r := by rw [← pow_mul]
      _ = (4 : ℝ) ^ r := by norm_num
  calc
    _ ≤ (n : ℝ) ^ 2 * (4 : ℝ) ^ r * (N : ℝ) ^ 2 * (D : ℝ) := hsum
    _ = (n : ℝ) ^ 2 * ((2 : ℝ) ^ r) ^ 2 * (N : ℝ) ^ 2 * (C : ℝ) *
        Real.rpow (dist x y) (α : ℝ) := by
          rw [hpow, hD]
          ring

/-- The resolved triple estimate packages as a Hölder bound for the top inverse jet. -/
private theorem auxiliary_top_inverse_jet_holder_bound
    {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedRing A] [NormedAlgebra ℝ A]
    {V : Set E} {n r : ℕ} {N C : ℝ≥0} {α : ℝ≥0}
    (a b : Fin n) (hV : IsOpen V)
    {inv source : Fin n → Fin n → E → A}
    (hInvCont : ∀ i j, ContDiffOn ℝ r (inv i j) V)
    (hSourceCont : ∀ i j, ContDiffOn ℝ r (source i j) V)
    (hSourceHolder : ∀ i j k, k ≤ r →
      HolderOnWith C α (fun z => iteratedFDeriv ℝ k (source i j) z) V)
    (hInvJetBound : ∀ i j k, k ≤ r → ∀ z ∈ V,
      ‖iteratedFDeriv ℝ k (inv i j) z‖ ≤ N)
    (hResolvent : ∀ i j x y, x ∈ V → y ∈ V →
      inv i j y - inv i j x =
        - ∑ p : Fin n × Fin n,
          (inv i p.1 x * (source p.1 p.2 y - source p.1 p.2 x)) * inv p.2 j y) :
    HolderOnWith
      (((n : ℝ≥0) ^ 2) * ((2 : ℝ≥0) ^ r) ^ 2 * N ^ 2 * C) α
      (iteratedFDeriv ℝ r (inv a b)) V := by
  let H : ℝ≥0 := ((n : ℝ≥0) ^ 2) * ((2 : ℝ≥0) ^ r) ^ 2 * N ^ 2 * C
  have hHcoe : (H : ℝ) = (n : ℝ) ^ 2 * ((2 : ℝ) ^ r) ^ 2 * (N : ℝ) ^ 2 * (C : ℝ) := by
    simp [H]
  have hHcoeENN : (H : ENNReal) = ENNReal.ofReal (H : ℝ) := by
    rw [ENNReal.ofReal_coe_nnreal]
  intro x hx y hy
  let T : Set E := {t | x + t ∈ V ∧ y + t ∈ V}
  have hT : IsOpen T := by
    change IsOpen ({t : E | x + t ∈ V} ∩ {t : E | y + t ∈ V})
    exact (hV.preimage (continuous_const.add continuous_id)).inter
      (hV.preimage (continuous_const.add continuous_id))
  have h0 : (0 : E) ∈ T := by
    change x + 0 ∈ V ∧ y + 0 ∈ V
    simpa using And.intro hx hy
  have htransX : ContDiffOn ℝ r (fun t : E => x + t) T := by fun_prop
  have htransY : ContDiffOn ℝ r (fun t : E => y + t) T := by fun_prop
  have hInvX : ∀ i j, ContDiffOn ℝ r (fun t => inv i j (x + t)) T := by
    intro i j
    exact (hInvCont i j).comp htransX (by intro t ht; exact ht.1)
  have hInvY : ∀ i j, ContDiffOn ℝ r (fun t => inv i j (y + t)) T := by
    intro i j
    exact (hInvCont i j).comp htransY (by intro t ht; exact ht.2)
  have hInvXBound : ∀ i j k, k ≤ r →
      ‖iteratedFDeriv ℝ k (fun t => inv i j (x + t)) (0 : E)‖ ≤ N := by
    intro i j k hk
    have hshift : iteratedFDeriv ℝ k (fun t => inv i j (x + t)) (0 : E) =
        iteratedFDeriv ℝ k (inv i j) x := by
      simpa using (iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := inv i j) k x (0 : E))
    rw [hshift]
    exact hInvJetBound i j k hk x hx
  have hInvYBound : ∀ i j k, k ≤ r →
      ‖iteratedFDeriv ℝ k (fun t => inv i j (y + t)) (0 : E)‖ ≤ N := by
    intro i j k hk
    have hshift : iteratedFDeriv ℝ k (fun t => inv i j (y + t)) (0 : E) =
        iteratedFDeriv ℝ k (inv i j) y := by
      simpa using (iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := inv i j) k y (0 : E))
    rw [hshift]
    exact hInvJetBound i j k hk y hy
  have hsumBound := auxiliary_shifted_resolvent_double_sum_holder_bound_exact
    a b hV hx hy hInvX hInvY hSourceCont hSourceHolder hInvXBound hInvYBound
  have hsumBound' :
      ‖iteratedFDeriv ℝ r
        (fun t => ∑ p : Fin n × Fin n,
          (inv a p.1 (x + t) *
            (source p.1 p.2 (y + t) - source p.1 p.2 (x + t))) *
            inv p.2 b (y + t)) (0 : E)‖ ≤
        (H : ℝ) * Real.rpow (dist x y) (α : ℝ) := by
    calc
      _ ≤ (n : ℝ) ^ 2 * ((2 : ℝ) ^ r) ^ 2 * (N : ℝ) ^ 2 * (C : ℝ) *
          Real.rpow (dist x y) (α : ℝ) := hsumBound
      _ = (H : ℝ) * Real.rpow (dist x y) (α : ℝ) := by
        rw [hHcoe]
  let f : E → A := fun t => inv a b (y + t) - inv a b (x + t)
  let g : E → A := fun t => -∑ p : Fin n × Fin n,
    (inv a p.1 (x + t) *
      (source p.1 p.2 (y + t) - source p.1 p.2 (x + t))) *
      inv p.2 b (y + t)
  have hformula : EqOn f g T := by
    intro t ht
    exact hResolvent a b (x + t) (y + t) ht.1 ht.2
  let term : Fin n × Fin n → E → A := fun p t =>
    (inv a p.1 (x + t) *
      (source p.1 p.2 (y + t) - source p.1 p.2 (x + t))) *
      inv p.2 b (y + t)
  have hsourceX : ∀ i j, ContDiffOn ℝ r (fun t => source i j (x + t)) T := by
    intro i j
    exact (hSourceCont i j).comp htransX (by intro t ht; exact ht.1)
  have hsourceY : ∀ i j, ContDiffOn ℝ r (fun t => source i j (y + t)) T := by
    intro i j
    exact (hSourceCont i j).comp htransY (by intro t ht; exact ht.2)
  have hsourceDiff : ∀ i j, ContDiffOn ℝ r
      (fun t => source i j (y + t) - source i j (x + t)) T := by
    intro i j
    exact (hsourceY i j).sub (hsourceX i j)
  have hterm : ∀ p ∈ Finset.univ, ContDiffOn ℝ r (term p) T := by
    intro p hp
    obtain ⟨i, j⟩ := p
    exact ((hInvX a i).mul (hsourceDiff i j)).mul (hInvY j b)
  have hsumCont : ContDiffOn ℝ r (fun t => ∑ p : Fin n × Fin n, term p t) T := by
    apply ContDiffOn.sum
    intro p hp
    exact hterm p hp
  have hfCont : ContDiffOn ℝ r f T := by
    dsimp [f]
    exact (hInvY a b).sub (hInvX a b)
  have hgCont : ContDiffOn ℝ r g T := by
    dsimp [g]
    exact hsumCont.neg
  have hformulaJet : iteratedFDeriv ℝ r f (0 : E) = iteratedFDeriv ℝ r g (0 : E) := by
    calc
      iteratedFDeriv ℝ r f (0 : E) = iteratedFDerivWithin ℝ r f T (0 : E) := by
        symm
        apply iteratedFDerivWithin_eq_iteratedFDeriv hT.uniqueDiffOn
        · exact (hfCont.contDiffAt (hT.mem_nhds h0)).of_le (by exact_mod_cast (le_rfl : r ≤ r))
        · exact h0
      _ = iteratedFDerivWithin ℝ r g T (0 : E) := iteratedFDerivWithin_congr hformula h0 r
      _ = iteratedFDeriv ℝ r g (0 : E) := by
        apply iteratedFDerivWithin_eq_iteratedFDeriv hT.uniqueDiffOn
        · exact (hgCont.contDiffAt (hT.mem_nhds h0)).of_le (by exact_mod_cast (le_rfl : r ≤ r))
        · exact h0
  have hYat : ContDiffAt ℝ r (fun t => inv a b (y + t)) (0 : E) :=
    (hInvY a b).contDiffAt (hT.mem_nhds h0)
  have hXat : ContDiffAt ℝ r (fun t => inv a b (x + t)) (0 : E) :=
    (hInvX a b).contDiffAt (hT.mem_nhds h0)
  have hderivDiff := iteratedFDeriv_sub_apply hYat hXat
  have hYshift : iteratedFDeriv ℝ r (fun t => inv a b (y + t)) (0 : E) =
      iteratedFDeriv ℝ r (inv a b) y := by
    simpa using (iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := inv a b) r y (0 : E))
  have hXshift : iteratedFDeriv ℝ r (fun t => inv a b (x + t)) (0 : E) =
      iteratedFDeriv ℝ r (inv a b) x := by
    simpa using (iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := inv a b) r x (0 : E))
  rw [hYshift, hXshift] at hderivDiff
  have hfun : f = (fun t : E => inv a b (y + t)) - (fun t : E => inv a b (x + t)) := by
    funext t
    rfl
  have hderivDiff' : iteratedFDeriv ℝ r f (0 : E) =
      iteratedFDeriv ℝ r (inv a b) y - iteratedFDeriv ℝ r (inv a b) x := by
    rw [hfun]
    exact hderivDiff
  have hjetdiff : iteratedFDeriv ℝ r (inv a b) y - iteratedFDeriv ℝ r (inv a b) x =
      -iteratedFDeriv ℝ r
        (fun t => ∑ p : Fin n × Fin n, term p t) (0 : E) := by
    calc
      _ = iteratedFDeriv ℝ r f (0 : E) := hderivDiff'.symm
      _ = iteratedFDeriv ℝ r g (0 : E) := hformulaJet
      _ = -iteratedFDeriv ℝ r (fun t => ∑ p : Fin n × Fin n, term p t) (0 : E) := by
        have hnegfun : (fun t : E => -∑ p : Fin n × Fin n,
            (inv a p.1 (x + t) *
              (source p.1 p.2 (y + t) - source p.1 p.2 (x + t))) *
              inv p.2 b (y + t)) =
            -(fun t : E => ∑ p : Fin n × Fin n, term p t) := by
          funext t
          rfl
        rw [show g = (fun t : E => -∑ p : Fin n × Fin n,
            (inv a p.1 (x + t) *
              (source p.1 p.2 (y + t) - source p.1 p.2 (x + t))) *
              inv p.2 b (y + t)) from rfl, hnegfun, iteratedFDeriv_neg_apply]
  have hdist : dist (iteratedFDeriv ℝ r (inv a b) x)
      (iteratedFDeriv ℝ r (inv a b) y) ≤
      (H : ℝ) * Real.rpow (dist x y) (α : ℝ) := by
    calc
      _ = dist (iteratedFDeriv ℝ r (inv a b) y)
          (iteratedFDeriv ℝ r (inv a b) x) := dist_comm _ _
      _ = ‖iteratedFDeriv ℝ r (inv a b) y - iteratedFDeriv ℝ r (inv a b) x‖ :=
        dist_eq_norm _ _
      _ = ‖iteratedFDeriv ℝ r
          (fun t => ∑ p : Fin n × Fin n, term p t) (0 : E)‖ := by rw [hjetdiff]; simp
      _ ≤ (H : ℝ) * Real.rpow (dist x y) (α : ℝ) := hsumBound'
  have hαReal : 0 ≤ (α : ℝ) := by exact_mod_cast α.2
  have hpowENN := ENNReal.ofReal_rpow_of_nonneg (dist_nonneg : 0 ≤ dist x y) hαReal
  have hdistENN : edist x y = ENNReal.ofReal (dist x y) := edist_dist x y
  calc
    edist (iteratedFDeriv ℝ r (inv a b) x) (iteratedFDeriv ℝ r (inv a b) y) =
        ENNReal.ofReal (dist (iteratedFDeriv ℝ r (inv a b) x)
          (iteratedFDeriv ℝ r (inv a b) y)) := edist_dist _ _
    _ ≤ ENNReal.ofReal ((H : ℝ) * Real.rpow (dist x y) (α : ℝ)) :=
      ENNReal.ofReal_le_ofReal hdist
    _ = (H : ENNReal) * edist x y ^ (α : ℝ) := by
      rw [hHcoeENN, hdistENN, hpowENN, ← ENNReal.ofReal_mul]
      · simp
      · positivity
set_option maxHeartbeats 1000000 in
private theorem matrix_inverse_resolvent_entry
    {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ)
    (hX : IsUnit X) (hY : IsUnit Y) (i j : Fin n) :
    (X⁻¹) i j - (Y⁻¹) i j =
      ∑ a : Fin n, ∑ b : Fin n, (X⁻¹) i a * (Y - X) a b * (Y⁻¹) b j := by
  have hXd : IsUnit X.det := X.isUnit_iff_isUnit_det.mp hX
  have hYd : IsUnit Y.det := Y.isUnit_iff_isUnit_det.mp hY
  have hXi : X⁻¹ * X = 1 := X.nonsing_inv_mul hXd
  have hYi : Y * Y⁻¹ = 1 := Y.mul_nonsing_inv hYd
  have hres : X⁻¹ - Y⁻¹ = X⁻¹ * (Y - X) * Y⁻¹ := by
    calc
      X⁻¹ - Y⁻¹ = X⁻¹ * (Y * Y⁻¹) - (X⁻¹ * X) * Y⁻¹ := by
        rw [hYi, hXi, mul_one, one_mul]
      _ = X⁻¹ * (Y - X) * Y⁻¹ := by noncomm_ring
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) hres
  change (X⁻¹ - Y⁻¹) i j = _ at h
  rw [Matrix.sub_apply] at h
  simp only [Matrix.mul_apply] at h
  simp only [Finset.sum_mul] at h
  rw [Finset.sum_comm] at h
  simpa [mul_assoc] using h

set_option maxHeartbeats 1000000 in
/-- The resolvent identity and finite product rule transfer entrywise Hölder
control of all matrix jets through order `r` to the top jet of the inverse.
The inverse jets are assumed uniformly bounded on the open set; no derivative
of order `r + 1` is required. -/
theorem matrix_inverse_top_jet_holder_from_jets
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n r : ℕ} {α N C : ℝ≥0} {V : Set E} (hV : IsOpen V)
    (B : E → Matrix (Fin n) (Fin n) ℂ)
    (hB : ∀ i j, ContDiffOn ℝ r (fun x ↦ B x i j) V)
    (hUnit : ∀ x ∈ V, IsUnit (B x))
    (hInv : ∀ i j, ContDiffOn ℝ r (fun x ↦ (B x)⁻¹ i j) V)
    (hInvBound : ∀ i j m, m ≤ r → ∀ x ∈ V,
      ‖iteratedFDeriv ℝ m (fun x ↦ (B x)⁻¹ i j) x‖ ≤ N)
    (hBHolder : ∀ i j m, m ≤ r → HolderOnWith C α
      (fun x ↦ iteratedFDeriv ℝ m (fun x ↦ B x i j) x) V) :
    ∀ i j, HolderOnWith
      (((n : ℝ≥0) ^ 2) * ((2 : ℝ≥0) ^ r) ^ 2 * N ^ 2 * C) α
      (fun x ↦ iteratedFDeriv ℝ r (fun x ↦ (B x)⁻¹ i j) x) V := by
  intro i j
  let inv : Fin n → Fin n → E → ℂ := fun a b x ↦ (B x)⁻¹ a b
  let source : Fin n → Fin n → E → ℂ := fun a b x ↦ B x a b
  have hinvCont : ∀ a b, ContDiffOn ℝ r (inv a b) V := by
    intro a b
    exact hInv a b
  have hsourceCont : ∀ a b, ContDiffOn ℝ r (source a b) V := by
    intro a b
    exact hB a b
  have hsourceHolder : ∀ a b k, k ≤ r →
      HolderOnWith C α (fun x ↦ iteratedFDeriv ℝ k (source a b) x) V := by
    intro a b k hk
    exact hBHolder a b k hk
  have hinvJetBound : ∀ a b k, k ≤ r → ∀ x ∈ V,
      ‖iteratedFDeriv ℝ k (inv a b) x‖ ≤ N := by
    intro a b k hk x hx
    exact hInvBound a b k hk x hx
  have hResolvent : ∀ a b x y, x ∈ V → y ∈ V →
      inv a b y - inv a b x =
        - ∑ p : Fin n × Fin n,
          (inv a p.1 x * (source p.1 p.2 y - source p.1 p.2 x)) * inv p.2 b y := by
    intro a b x y hx hy
    have hentry := matrix_inverse_resolvent_entry (B x) (B y)
      (hUnit x hx) (hUnit y hy) a b
    have hneg := congrArg Neg.neg hentry
    have hpack :
        (∑ k : Fin n, ∑ l : Fin n,
          (inv a k x * (source k l y - source k l x)) * inv l b y) =
          ∑ p : Fin n × Fin n,
            (inv a p.1 x * (source p.1 p.2 y - source p.1 p.2 x)) * inv p.2 b y := by
      rw [← Finset.univ_product_univ, Finset.sum_product]
    calc
      inv a b y - inv a b x = -((B x)⁻¹ a b - (B y)⁻¹ a b) := by simp [inv]
      _ = -(∑ k : Fin n, ∑ l : Fin n,
          (inv a k x * (source k l y - source k l x)) * inv l b y) := by
        simpa [inv, source, mul_assoc] using hneg
      _ = -∑ p : Fin n × Fin n,
          (inv a p.1 x * (source p.1 p.2 y - source p.1 p.2 x)) * inv p.2 b y := by
        rw [hpack]
  exact auxiliary_top_inverse_jet_holder_bound
    (E := E) (A := ℂ) (V := V) (n := n) (r := r) (N := N) (C := C) (α := α)
    i j hV (inv := inv) (source := source)
    hinvCont hsourceCont hsourceHolder hinvJetBound hResolvent
