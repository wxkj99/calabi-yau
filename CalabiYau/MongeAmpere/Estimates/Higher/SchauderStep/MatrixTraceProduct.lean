module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Topology.MetricSpace.Holder
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Hölder control of matrix trace products

Finite sums of products of smooth scalar matrix entries preserve local Hölder jet bounds,
provided all input jets through the top order satisfy uniform Hölder estimates. Pointwise bounds
on lower jets alone do not control nearby points separated by gaps in an arbitrary comparison set.
The uniform family formulation supplies the single constant needed by the differentiated
Monge–Ampère right-hand side.
-/

@[expose] public section

open scoped ContDiff NNReal

namespace KahlerForm

private theorem matrix_trace_mul_entries {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    (A * B).trace = ∑ i : Fin n, ∑ j : Fin n, A i j * B j i := by
  simp [Matrix.trace, Matrix.mul_apply]

private theorem real_matrix_trace_mul_entries {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    RCLike.re ((A * B).trace) =
      ∑ i : Fin n, ∑ j : Fin n, RCLike.re (A i j * B j i) := by
  rw [matrix_trace_mul_entries]
  simp only [map_sum]

private theorem complex_mul_holder_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} {α C D : ℝ≥0} (f g : E → ℂ)
    (hfBound : ∀ x ∈ K, ‖f x‖ ≤ C)
    (hgBound : ∀ x ∈ K, ‖g x‖ ≤ D)
    (hf : HolderOnWith C α f K) (hg : HolderOnWith D α g K) :
    HolderOnWith (2 * C * D) α (fun x ↦ f x * g x) K := by
  intro x hx y hy
  have hfxy : dist (f x) (f y) ≤ (C : ℝ) * dist x y ^ (α : ℝ) := hf.dist_le hx hy
  have hgxy : dist (g x) (g y) ≤ (D : ℝ) * dist x y ^ (α : ℝ) := hg.dist_le hx hy
  have hprod : dist (f x * g x) (f y * g y) ≤
      (2 * C * D : ℝ) * dist x y ^ (α : ℝ) := by
    rw [dist_eq_norm]
    calc
      ‖f x * g x - f y * g y‖ = ‖f x * (g x - g y) + (f x - f y) * g y‖ := by congr 1; ring
      _ ≤ ‖f x * (g x - g y)‖ + ‖(f x - f y) * g y‖ := norm_add_le _ _
      _ = ‖f x‖ * ‖g x - g y‖ + ‖f x - f y‖ * ‖g y‖ := by rw [norm_mul, norm_mul]
      _ ≤ (C : ℝ) * ((D : ℝ) * dist x y ^ (α : ℝ)) +
          ((C : ℝ) * dist x y ^ (α : ℝ)) * D := by
        gcongr
        · exact hfBound x hx
        · simpa [dist_eq_norm] using hgxy
        · simpa [dist_eq_norm] using hfxy
        · exact hgBound y hy
      _ = (2 * C * D : ℝ) * dist x y ^ (α : ℝ) := by ring
  rw [edist_dist, edist_dist (x := x) (y := y)]
  rw [ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) α.coe_nonneg]
  rw [ENNReal.coe_nnreal_eq (2 * C * D)]
  rw [← ENNReal.ofReal_mul (by positivity)]
  norm_cast
  exact ENNReal.ofReal_le_ofReal hprod

private theorem complex_mul_holder_bound_general
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} {α Bf Cf Bg Cg : ℝ≥0} (f g : E → ℂ)
    (hfBound : ∀ x ∈ K, ‖f x‖ ≤ Bf)
    (hgBound : ∀ x ∈ K, ‖g x‖ ≤ Bg)
    (hf : HolderOnWith Cf α f K) (hg : HolderOnWith Cg α g K) :
    HolderOnWith (Bf * Cg + Cf * Bg) α (fun x ↦ f x * g x) K := by
  intro x hx y hy
  have hfxy : dist (f x) (f y) ≤ (Cf : ℝ) * dist x y ^ (α : ℝ) := hf.dist_le hx hy
  have hgxy : dist (g x) (g y) ≤ (Cg : ℝ) * dist x y ^ (α : ℝ) := hg.dist_le hx hy
  have hprod : dist (f x * g x) (f y * g y) ≤
      ((Bf * Cg + Cf * Bg : ℝ≥0) : ℝ) * dist x y ^ (α : ℝ) := by
    rw [dist_eq_norm]
    calc
      ‖f x * g x - f y * g y‖ = ‖f x * (g x - g y) + (f x - f y) * g y‖ := by congr 1; ring
      _ ≤ ‖f x * (g x - g y)‖ + ‖(f x - f y) * g y‖ := norm_add_le _ _
      _ = ‖f x‖ * ‖g x - g y‖ + ‖f x - f y‖ * ‖g y‖ := by rw [norm_mul, norm_mul]
      _ ≤ (Bf : ℝ) * ((Cg : ℝ) * dist x y ^ (α : ℝ)) +
          ((Cf : ℝ) * dist x y ^ (α : ℝ)) * Bg := by
        gcongr
        · exact hfBound x hx
        · simpa [dist_eq_norm] using hgxy
        · simpa [dist_eq_norm] using hfxy
        · exact hgBound y hy
      _ = ((Bf * Cg + Cf * Bg : ℝ≥0) : ℝ) * dist x y ^ (α : ℝ) := by push_cast; ring
  rw [edist_dist, edist_dist (x := x) (y := y)]
  rw [ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) α.coe_nonneg]
  rw [ENNReal.coe_nnreal_eq (Bf * Cg + Cf * Bg)]
  rw [← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hprod

private theorem complex_finset_prod_norm_bound
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} {C : ℝ≥0} (s : Finset ι) (f : ι → E → ℂ)
    (hbound : ∀ i x, x ∈ K → ‖f i x‖ ≤ C) :
    ∀ x ∈ K, ‖∏ i ∈ s, f i x‖ ≤ (C : ℝ) ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
    intro x hx
    rw [Finset.prod_insert his]
    calc
      ‖f i x * ∏ j ∈ s, f j x‖ = ‖f i x‖ * ‖∏ j ∈ s, f j x‖ := norm_mul _ _
      _ ≤ (C : ℝ) * (C : ℝ) ^ s.card :=
        mul_le_mul (hbound i x hx) (ih x hx) (norm_nonneg _) C.coe_nonneg
      _ = (C : ℝ) ^ (Finset.card (insert i s)) := by
        rw [Finset.card_insert_of_notMem his, pow_succ]
        ring

private theorem complex_finset_prod_holder_bound
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} {α C : ℝ≥0} (s : Finset ι) (f : ι → E → ℂ)
    (hbound : ∀ i x, x ∈ K → ‖f i x‖ ≤ C)
    (hholder : ∀ i, HolderOnWith C α (f i) K) :
    HolderOnWith ((s.card : ℝ≥0) * C ^ s.card) α (fun x ↦ ∏ i ∈ s, f i x) K := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro x hx y hy
    simp [Finset.prod_empty]
  | @insert i s his ih =>
    have hprodBound : ∀ x ∈ K, ‖∏ j ∈ s, f j x‖ ≤ (C : ℝ≥0) ^ s.card := by
      intro x hx
      exact_mod_cast complex_finset_prod_norm_bound s f hbound x hx
    have hprodHolder := ih
    have hmul := complex_mul_holder_bound_general (Bf := C) (Cf := C)
      (Bg := C ^ s.card) (Cg := (s.card : ℝ≥0) * C ^ s.card)
      (f i) (fun x ↦ ∏ j ∈ s, f j x)
      (fun x hx ↦ hbound i x hx) hprodBound (hholder i) hprodHolder
    simpa [Finset.prod_insert his, Finset.card_insert_of_notMem his, pow_succ,
      mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm] using hmul

private theorem cmlm_eval_holderOnWith
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} {α C : ℝ≥0} {m : ℕ}
    (f : E → ContinuousMultilinearMap ℝ (fun _ : Fin m => E) ℂ)
    (v : Fin m → E) (hv : ∀ i, ‖v i‖ ≤ 1)
    (hf : HolderOnWith C α f K) :
    HolderOnWith C α (fun x ↦ f x v) K := by
  intro x hx y hy
  have heval : dist (f x v) (f y v) ≤ dist (f x) (f y) := by
    rw [dist_eq_norm, dist_eq_norm]
    have hnorm := (f x - f y).le_opNorm_mul_prod_of_le
      (b := fun _ : Fin m => (1 : ℝ)) hv
    simpa [sub_apply] using hnorm
  have hprod : dist (f x v) (f y v) ≤
      (C : ℝ) * dist x y ^ (α : ℝ) := heval.trans (hf.dist_le hx hy)
  rw [edist_dist, edist_dist (x := x) (y := y)]
  rw [ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) α.coe_nonneg]
  rw [ENNReal.coe_nnreal_eq C]
  rw [← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hprod

private theorem complex_re_holder_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} {α C : ℝ≥0} (f : E → ℂ)
    (hf : HolderOnWith C α f K) :
    HolderOnWith C α (fun x ↦ RCLike.re (f x)) K := by
  intro x hx y hy
  have hd : dist (RCLike.re (f x)) (RCLike.re (f y)) ≤ dist (f x) (f y) := by
    rw [dist_eq_norm, dist_eq_norm]
    have h := Complex.abs_re_le_norm (f x - f y)
    simpa [map_sub, abs_of_nonneg] using h
  have hprod : dist (RCLike.re (f x)) (RCLike.re (f y)) ≤
      (C : ℝ) * dist x y ^ (α : ℝ) := hd.trans (hf.dist_le hx hy)
  rw [edist_dist, edist_dist (x := x) (y := y)]
  rw [ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) α.coe_nonneg]
  rw [ENNReal.coe_nnreal_eq C]
  rw [← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hprod

private theorem holderOnWith_finset_sum
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} {α C : ℝ≥0} (s : Finset ι) (f : ι → E → ℝ)
    (hf : ∀ i, HolderOnWith C α (f i) K) :
    HolderOnWith (∑ _i ∈ s, C) α (fun x ↦ ∑ i ∈ s, f i x) K := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro x hx y hy
    simp [Finset.sum_empty]
  | @insert i s his ih =>
    simp only [Finset.sum_insert his]
    intro x hx y hy
    have hi := (hf i).edist_le hx hy
    have hs := ih x hx y hy
    calc
      edist (f i x + ∑ j ∈ s, f j x) (f i y + ∑ j ∈ s, f j y) ≤
          edist (f i x) (f i y) + edist (∑ j ∈ s, f j x) (∑ j ∈ s, f j y) := edist_add_add_le _ _ _ _
      _ ≤ (C : ENNReal) * edist x y ^ (α : ℝ) +
          (↑(∑ _j ∈ s, C) : ENNReal) * edist x y ^ (α : ℝ) := add_le_add hi hs
      _ = (↑(C + ∑ _j ∈ s, C) : ENNReal) * edist x y ^ (α : ℝ) := by
        rw [ENNReal.coe_add, add_mul]

private theorem holderOnWith_finset_sum_normed
    {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} {α C : ℝ≥0}
    (s : Finset ι) (f : ι → E → F)
    (hf : ∀ i, HolderOnWith C α (f i) K) :
    HolderOnWith ((s.card : ℝ≥0) * C) α (fun x ↦ ∑ i ∈ s, f i x) K := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro x hx y hy
      simp [Finset.sum_empty]
  | @insert i s his ih =>
      simp only [Finset.sum_insert his]
      intro x hx y hy
      have hi := (hf i).edist_le hx hy
      have hs := ih x hx y hy
      calc
        edist (f i x + ∑ j ∈ s, f j x) (f i y + ∑ j ∈ s, f j y) ≤
            edist (f i x) (f i y) + edist (∑ j ∈ s, f j x) (∑ j ∈ s, f j y) :=
          edist_add_add_le _ _ _ _
        _ ≤ (C : ENNReal) * edist x y ^ (α : ℝ) +
            (((s.card : ℝ≥0) * C : ℝ≥0) : ENNReal) * edist x y ^ (α : ℝ) := add_le_add hi hs
        _ = ((((insert i s).card : ℝ≥0) * C : ℝ≥0) : ENNReal) * edist x y ^ (α : ℝ) := by
          rw [ENNReal.coe_mul, ENNReal.coe_mul, Finset.card_insert_of_notMem his]
          push_cast
          ring

private theorem matrix_trace_holder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {α C D : ℝ≥0} {K : Set E}
    (A B : E → Matrix (Fin n) (Fin n) ℂ)
    (hABound : ∀ i j x, x ∈ K → ‖A x i j‖ ≤ C)
    (hBBound : ∀ i j x, x ∈ K → ‖B x i j‖ ≤ D)
    (hAHolder : ∀ i j, HolderOnWith C α (fun x ↦ A x i j) K)
    (hBHolder : ∀ i j, HolderOnWith D α (fun x ↦ B x i j) K) :
    HolderOnWith (∑ _i ∈ (Finset.univ : Finset (Fin n)),
      ∑ _j ∈ (Finset.univ : Finset (Fin n)), 2 * C * D) α
      (fun x ↦ RCLike.re ((A x * B x).trace)) K := by
  classical
  have hformula : (fun x ↦ RCLike.re ((A x * B x).trace)) =
      (fun x ↦ ∑ i : Fin n, ∑ j : Fin n, RCLike.re (A x i j * B x j i)) := by
    funext x
    exact real_matrix_trace_mul_entries (A x) (B x)
  rw [hformula]
  apply holderOnWith_finset_sum
  intro i
  apply holderOnWith_finset_sum
  intro j
  apply complex_re_holder_bound
  exact complex_mul_holder_bound (fun x ↦ A x i j) (fun x ↦ B x j i)
    (fun x hx ↦ hABound i j x hx) (fun x hx ↦ hBBound j i x hx)
    (hAHolder i j) (hBHolder j i)

private theorem matrix_trace_value_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {C D : ℝ≥0} {K : Set E}
    (A B : E → Matrix (Fin n) (Fin n) ℂ)
    (hABound : ∀ i j x, x ∈ K → ‖A x i j‖ ≤ C)
    (hBBound : ∀ i j x, x ∈ K → ‖B x i j‖ ≤ D) :
    ∀ x ∈ K, ‖RCLike.re ((A x * B x).trace)‖ ≤
      ∑ _i ∈ (Finset.univ : Finset (Fin n)),
        ∑ _j ∈ (Finset.univ : Finset (Fin n)), (C : ℝ) * D := by
  classical
  intro x hx
  have hformula : RCLike.re ((A x * B x).trace) =
      ∑ i : Fin n, ∑ j : Fin n, RCLike.re (A x i j * B x j i) :=
    real_matrix_trace_mul_entries (A x) (B x)
  rw [hformula]
  calc
    ‖∑ i ∈ (Finset.univ : Finset (Fin n)), ∑ j ∈ (Finset.univ : Finset (Fin n)), RCLike.re (A x i j * B x j i)‖
        ≤ ∑ i ∈ (Finset.univ : Finset (Fin n)),
            ‖∑ j ∈ (Finset.univ : Finset (Fin n)), RCLike.re (A x i j * B x j i)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin n)),
            ∑ j ∈ (Finset.univ : Finset (Fin n)), (C : ℝ) * D := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        ‖∑ j ∈ (Finset.univ : Finset (Fin n)), RCLike.re (A x i j * B x j i)‖
            ≤ ∑ j ∈ (Finset.univ : Finset (Fin n)), ‖RCLike.re (A x i j * B x j i)‖ := norm_sum_le _ _
        _ ≤ ∑ j ∈ (Finset.univ : Finset (Fin n)), (C : ℝ) * D := by
          apply Finset.sum_le_sum
          intro j hj
          have hre : ‖RCLike.re (A x i j * B x j i)‖ ≤ ‖A x i j * B x j i‖ := by
            simpa [Real.norm_eq_abs] using Complex.abs_re_le_norm (A x i j * B x j i)
          calc
            ‖RCLike.re (A x i j * B x j i)‖ ≤ ‖A x i j * B x j i‖ := hre
            _ = ‖A x i j‖ * ‖B x j i‖ := norm_mul _ _
            _ ≤ (C : ℝ) * D := mul_le_mul (hABound i j x hx) (hBBound j i x hx)
                  (norm_nonneg _) C.coe_nonneg

private theorem holderOnWith_zero_iteratedFDeriv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} {α C : ℝ≥0} (f : E → F)
    (h : HolderOnWith C α (iteratedFDeriv ℝ 0 f) K) :
    HolderOnWith C α f K := by
  intro x hx y hy
  have heq : edist (iteratedFDeriv ℝ 0 f x) (iteratedFDeriv ℝ 0 f y) = edist (f x) (f y) := by
    rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    exact (continuousMultilinearCurryFin0 ℝ E F).symm.edist_map _ _
  rw [← heq]
  exact h.edist_le hx hy

private theorem holderOnWith_zero_iteratedFDeriv_iff
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} {α C : ℝ≥0} (f : E → F) :
    HolderOnWith C α (iteratedFDeriv ℝ 0 f) K ↔ HolderOnWith C α f K := by
  constructor
  · exact holderOnWith_zero_iteratedFDeriv f
  · intro h x hx y hy
    have heq : edist (iteratedFDeriv ℝ 0 f x) (iteratedFDeriv ℝ 0 f y) = edist (f x) (f y) := by
      rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
      exact (continuousMultilinearCurryFin0 ℝ E F).symm.edist_map _ _
    rw [heq]
    exact h.edist_le hx hy

private theorem holderOnWith_bilinear_bound
    {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {K : Set E} {α Bf Cf Bg Cg : ℝ≥0}
    (B : F →L[ℝ] G →L[ℝ] H) (f : E → F) (g : E → G)
    (hfBound : ∀ x ∈ K, ‖f x‖ ≤ Bf)
    (hgBound : ∀ x ∈ K, ‖g x‖ ≤ Bg)
    (hf : HolderOnWith Cf α f K) (hg : HolderOnWith Cg α g K) :
    HolderOnWith (‖B‖₊ * (Bf * Cg + Cf * Bg)) α (fun x ↦ B (f x) (g x)) K := by
  intro x hx y hy
  have hfxy := hf.dist_le hx hy
  have hgxy := hg.dist_le hx hy
  have hprod : dist (B (f x) (g x)) (B (f y) (g y)) ≤
      ((‖B‖₊ * (Bf * Cg + Cf * Bg) : ℝ≥0) : ℝ) * dist x y ^ (α : ℝ) := by
    rw [dist_eq_norm]
    have hdecomp : B (f x) (g x) - B (f y) (g y) =
        B (f x) (g x - g y) + B (f x - f y) (g y) := by
      calc
        B (f x) (g x) - B (f y) (g y) =
            (B (f x) (g x) - B (f x) (g y)) +
              (B (f x) (g y) - B (f y) (g y)) := by abel
        _ = B (f x) (g x - g y) + B (f x - f y) (g y) := by
          simp only [map_sub, sub_apply]
    rw [hdecomp]
    calc
      ‖B (f x) (g x - g y) + B (f x - f y) (g y)‖ ≤
          ‖B (f x) (g x - g y)‖ + ‖B (f x - f y) (g y)‖ := norm_add_le _ _
      _ ≤ ‖B‖ * ‖f x‖ * ‖g x - g y‖ + ‖B‖ * ‖f x - f y‖ * ‖g y‖ := by
        exact add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _)
      _ ≤ ‖B‖ * (Bf : ℝ) * ((Cg : ℝ) * dist x y ^ (α : ℝ)) +
          ‖B‖ * ((Cf : ℝ) * dist x y ^ (α : ℝ)) * Bg := by
        gcongr
        · exact hfBound x hx
        · simpa [dist_eq_norm] using hgxy
        · simpa [dist_eq_norm] using hfxy
        · exact hgBound y hy
      _ = ((‖B‖₊ * (Bf * Cg + Cf * Bg) : ℝ≥0) : ℝ) * dist x y ^ (α : ℝ) := by
        push_cast
        ring
  rw [edist_dist, edist_dist (x := x) (y := y)]
  rw [ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) α.coe_nonneg]
  rw [ENNReal.coe_nnreal_eq (‖B‖₊ * (Bf * Cg + Cf * Bg))]
  rw [← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hprod

private theorem holderOnWith_add_normed
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} {α C D : ℝ≥0} {f g : E → F}
    (hf : HolderOnWith C α f K) (hg : HolderOnWith D α g K) :
    HolderOnWith (C + D) α (fun x ↦ f x + g x) K := by
  intro x hx y hy
  calc
    edist (f x + g x) (f y + g y) ≤ edist (f x) (f y) + edist (g x) (g y) :=
      edist_add_add_le _ _ _ _
    _ ≤ (C : ENNReal) * edist x y ^ (α : ℝ) +
        (D : ENNReal) * edist x y ^ (α : ℝ) :=
      add_le_add (hf.edist_le hx hy) (hg.edist_le hx hy)
    _ = ((C + D : ℝ≥0) : ENNReal) * edist x y ^ (α : ℝ) := by
      rw [ENNReal.coe_add, add_mul]

universe u v w z t

private theorem iteratedFDeriv_add_of_contDiffOn
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {W : Set E} (hW : IsOpen W) (n : ℕ) (f g : E → F)
    (hf : ContDiffOn ℝ ∞ f W) (hg : ContDiffOn ℝ ∞ g W)
    {x : E} (hx : x ∈ W) :
    iteratedFDeriv ℝ n (fun z ↦ f z + g z) x =
      iteratedFDeriv ℝ n f x + iteratedFDeriv ℝ n g x := by
  have hn : (n : ℕ∞ω) ≤ ∞ := by
    exact_mod_cast (le_top : (n : ℕ∞) ≤ (⊤ : ℕ∞))
  exact iteratedFDeriv_add_apply
    ((hf x hx).contDiffAt (hW.mem_nhds hx) |>.of_le hn)
    ((hg x hx).contDiffAt (hW.mem_nhds hx) |>.of_le hn)

private theorem holderOnWith_comp_linearIsometryEquiv
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {K : Set E} {α C : ℝ≥0} (Q : F ≃ₗᵢ[ℝ] G) (f : E → F)
    (hf : HolderOnWith C α f K) : HolderOnWith C α (fun x ↦ Q (f x)) K := by
  intro x hx y hy
  rw [Q.edist_map]
  exact hf.edist_le hx hy

private theorem iteratedFDeriv_fderiv_eq_curryRight
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (n : ℕ) (x : E) :
    iteratedFDeriv ℝ n (fun y ↦ fderiv ℝ f y) x =
      continuousMultilinearCurryRightEquiv' ℝ n E F (iteratedFDeriv ℝ (n + 1) f x) := by
  rw [iteratedFDeriv_succ_eq_comp_right]
  simp

private theorem holderOnWith_iteratedFDeriv_fderiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} {α C : ℝ≥0} (f : E → F) (n : ℕ)
    (hf : HolderOnWith C α (iteratedFDeriv ℝ (n + 1) f) K) :
    HolderOnWith C α (iteratedFDeriv ℝ n (fun y ↦ fderiv ℝ f y)) K := by
  have hEq : (fun x ↦ iteratedFDeriv ℝ n (fun y ↦ fderiv ℝ f y) x) =
      (fun x ↦ continuousMultilinearCurryRightEquiv' ℝ n E F
        (iteratedFDeriv ℝ (n + 1) f x)) := by
    funext x
    exact iteratedFDeriv_fderiv_eq_curryRight f n x
  change HolderOnWith C α
    (fun x ↦ iteratedFDeriv ℝ n (fun y ↦ fderiv ℝ f y) x) K
  rw [hEq]
  exact holderOnWith_comp_linearIsometryEquiv
    (continuousMultilinearCurryRightEquiv' ℝ n E F) _ hf

set_option linter.checkUnivs false in
private theorem exists_common_holder_iteratedFDeriv_bilinear
    {P : Type t} {E : Type u}
    {F G H : Type (max (max (max u v) w) z)}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {S : Set P} {W K : Set E} {α C D : ℝ≥0} (n : ℕ)
    (hW : IsOpen W) (hKW : K ⊆ W) (B : F →L[ℝ] G →L[ℝ] H)
    (f : P → E → F) (g : P → E → G)
    (hfSmooth : ∀ p ∈ S, ContDiffOn ℝ ∞ (f p) W)
    (hgSmooth : ∀ p ∈ S, ContDiffOn ℝ ∞ (g p) W)
    (hfBound : ∀ p ∈ S, ∀ m ≤ n, ∀ x ∈ K, ‖iteratedFDeriv ℝ m (f p) x‖ ≤ C)
    (hgBound : ∀ p ∈ S, ∀ m ≤ n, ∀ x ∈ K, ‖iteratedFDeriv ℝ m (g p) x‖ ≤ D)
    (hfHolder : ∀ p ∈ S, ∀ m ≤ n, HolderOnWith C α (iteratedFDeriv ℝ m (f p)) K)
    (hgHolder : ∀ p ∈ S, ∀ m ≤ n, HolderOnWith D α (iteratedFDeriv ℝ m (g p)) K) :
    ∃ C' : ℝ≥0, ∀ p ∈ S,
      HolderOnWith C' α (iteratedFDeriv ℝ n (fun x ↦ B (f p x) (g p x))) K := by
  induction n generalizing F G H B f g C D with
  | zero =>
      refine ⟨‖B‖₊ * (C * D + C * D), ?_⟩
      intro p hp
      have hf0Bound : ∀ x ∈ K, ‖f p x‖ ≤ C := by
        intro x hx
        simpa only [norm_iteratedFDeriv_zero] using hfBound p hp 0 (by omega) x hx
      have hg0Bound : ∀ x ∈ K, ‖g p x‖ ≤ D := by
        intro x hx
        simpa only [norm_iteratedFDeriv_zero] using hgBound p hp 0 (by omega) x hx
      have hf0Holder : HolderOnWith C α (f p) K :=
        (holderOnWith_zero_iteratedFDeriv_iff (f p)).1 (hfHolder p hp 0 (by omega))
      have hg0Holder : HolderOnWith D α (g p) K :=
        (holderOnWith_zero_iteratedFDeriv_iff (g p)).1 (hgHolder p hp 0 (by omega))
      exact (holderOnWith_zero_iteratedFDeriv_iff
        (fun x ↦ B (f p x) (g p x))).2
        (holderOnWith_bilinear_bound B (f p) (g p)
          hf0Bound hg0Bound hf0Holder hg0Holder)
  | succ n ih =>
      let B₁ := ContinuousLinearMap.precompR E B
      let B₂ := ContinuousLinearMap.precompL E B
      have hfSmooth' : ∀ p ∈ S, ContDiffOn ℝ ∞ (fun z ↦ fderiv ℝ (f p) z) W := by
        intro p hp
        exact (hfSmooth p hp).fderiv_of_isOpen hW (by simp)
      have hgSmooth' : ∀ p ∈ S, ContDiffOn ℝ ∞ (fun z ↦ fderiv ℝ (g p) z) W := by
        intro p hp
        exact (hgSmooth p hp).fderiv_of_isOpen hW (by simp)
      have hfBound' : ∀ p ∈ S, ∀ m ≤ n, ∀ x ∈ K, ‖iteratedFDeriv ℝ m (f p) x‖ ≤ C := by
        intro p hp m hm x hx
        exact hfBound p hp m (by omega) x hx
      have hgBound' : ∀ p ∈ S, ∀ m ≤ n, ∀ x ∈ K, ‖iteratedFDeriv ℝ m (g p) x‖ ≤ D := by
        intro p hp m hm x hx
        exact hgBound p hp m (by omega) x hx
      have hfHolder' : ∀ p ∈ S, ∀ m ≤ n, HolderOnWith C α (iteratedFDeriv ℝ m (f p)) K := by
        intro p hp m hm
        exact hfHolder p hp m (by omega)
      have hgHolder' : ∀ p ∈ S, ∀ m ≤ n, HolderOnWith D α (iteratedFDeriv ℝ m (g p)) K := by
        intro p hp m hm
        exact hgHolder p hp m (by omega)
      have hfDerivBound' : ∀ p ∈ S, ∀ m ≤ n, ∀ x ∈ K,
          ‖iteratedFDeriv ℝ m (fun z ↦ fderiv ℝ (f p) z) x‖ ≤ C := by
        intro p hp m hm x hx
        rw [norm_iteratedFDeriv_fderiv]
        exact hfBound p hp (m + 1) (by omega) x hx
      have hgDerivBound' : ∀ p ∈ S, ∀ m ≤ n, ∀ x ∈ K,
          ‖iteratedFDeriv ℝ m (fun z ↦ fderiv ℝ (g p) z) x‖ ≤ D := by
        intro p hp m hm x hx
        rw [norm_iteratedFDeriv_fderiv]
        exact hgBound p hp (m + 1) (by omega) x hx
      have hfDerivHolder' : ∀ p ∈ S, ∀ m ≤ n,
          HolderOnWith C α (iteratedFDeriv ℝ m (fun z ↦ fderiv ℝ (f p) z)) K := by
        intro p hp m hm
        exact holderOnWith_iteratedFDeriv_fderiv (f p) m (hfHolder p hp (m + 1) (by omega))
      have hgDerivHolder' : ∀ p ∈ S, ∀ m ≤ n,
          HolderOnWith D α (iteratedFDeriv ℝ m (fun z ↦ fderiv ℝ (g p) z)) K := by
        intro p hp m hm
        exact holderOnWith_iteratedFDeriv_fderiv (g p) m (hgHolder p hp (m + 1) (by omega))
      obtain ⟨C₁, h₁⟩ := ih B₁ f (fun p z ↦ fderiv ℝ (g p) z)
        hfSmooth hgSmooth' hfBound' hgDerivBound' hfHolder' hgDerivHolder'
      obtain ⟨C₂, h₂⟩ := ih B₂ (fun p z ↦ fderiv ℝ (f p) z) g
        hfSmooth' hgSmooth hfDerivBound' hgBound' hfDerivHolder' hgHolder'
      refine ⟨C₁ + C₂, ?_⟩
      intro p hp
      have htermSmooth₁ : ContDiffOn ℝ ∞
          (fun z ↦ B₁ (f p z) (fderiv ℝ (g p) z)) W := by
        exact (ContinuousLinearMap.precompR E B).isBoundedBilinearMap.contDiff.comp₂_contDiffOn
          (hfSmooth p hp) (hgSmooth' p hp)
      have htermSmooth₂ : ContDiffOn ℝ ∞
          (fun z ↦ B₂ (fderiv ℝ (f p) z) (g p z)) W := by
        exact (ContinuousLinearMap.precompL E B).isBoundedBilinearMap.contDiff.comp₂_contDiffOn
          (hfSmooth' p hp) (hgSmooth p hp)
      have hderivEq : Set.EqOn (fderiv ℝ (fun z ↦ B (f p z) (g p z)))
          (fun z ↦ B₁ (f p z) (fderiv ℝ (g p) z) +
            B₂ (fderiv ℝ (f p) z) (g p z)) W := by
        intro z hz
        exact ContinuousLinearMap.fderiv_of_bilinear B
          ((hfSmooth p hp).contDiffAt (hW.mem_nhds hz) |>.differentiableAt (by simp))
          ((hgSmooth p hp).contDiffAt (hW.mem_nhds hz) |>.differentiableAt (by simp))
      have hjetEq (x : E) (hx : x ∈ W) :
          iteratedFDeriv ℝ n (fderiv ℝ (fun z ↦ B (f p z) (g p z))) x =
            iteratedFDeriv ℝ n
              (fun z ↦ B₁ (f p z) (fderiv ℝ (g p) z) +
                B₂ (fderiv ℝ (f p) z) (g p z)) x := by
        calc
          iteratedFDeriv ℝ n (fderiv ℝ (fun z ↦ B (f p z) (g p z))) x =
              iteratedFDerivWithin ℝ n (fderiv ℝ (fun z ↦ B (f p z) (g p z))) W x :=
            (iteratedFDerivWithin_of_isOpen n hW hx).symm
          _ = iteratedFDerivWithin ℝ n
              (fun z ↦ B₁ (f p z) (fderiv ℝ (g p) z) +
                B₂ (fderiv ℝ (f p) z) (g p z)) W x :=
            iteratedFDerivWithin_congr hderivEq hx n
          _ = iteratedFDeriv ℝ n
              (fun z ↦ B₁ (f p z) (fderiv ℝ (g p) z) +
                B₂ (fderiv ℝ (f p) z) (g p z)) x :=
            iteratedFDerivWithin_of_isOpen n hW hx
      have hjetAdd (x : E) (hx : x ∈ W) :
          iteratedFDeriv ℝ n
              (fun z ↦ B₁ (f p z) (fderiv ℝ (g p) z) +
                B₂ (fderiv ℝ (f p) z) (g p z)) x =
          iteratedFDeriv ℝ n (fun z ↦ B₁ (f p z) (fderiv ℝ (g p) z)) x +
            iteratedFDeriv ℝ n (fun z ↦ B₂ (fderiv ℝ (f p) z) (g p z)) x := by
        exact iteratedFDeriv_add_of_contDiffOn hW n _ _ htermSmooth₁ htermSmooth₂ hx
      let Q := continuousMultilinearCurryRightEquiv' ℝ n E H
      have h₁' : HolderOnWith C₁ α
          (fun x ↦ Q.symm
            (iteratedFDeriv ℝ n (fun z ↦ B₁ (f p z) (fderiv ℝ (g p) z)) x)) K :=
        holderOnWith_comp_linearIsometryEquiv Q.symm _ (h₁ p hp)
      have h₂' : HolderOnWith C₂ α
          (fun x ↦ Q.symm
            (iteratedFDeriv ℝ n (fun z ↦ B₂ (fderiv ℝ (f p) z) (g p z)) x)) K :=
        holderOnWith_comp_linearIsometryEquiv Q.symm _ (h₂ p hp)
      have hsum := holderOnWith_add_normed h₁' h₂'
      intro x hx y hy
      have hpoint (z : E) (hz : z ∈ K) :
          iteratedFDeriv ℝ (n + 1) (fun z ↦ B (f p z) (g p z)) z =
            Q.symm (iteratedFDeriv ℝ n (fun z ↦ B₁ (f p z) (fderiv ℝ (g p) z)) z) +
              Q.symm (iteratedFDeriv ℝ n (fun z ↦ B₂ (fderiv ℝ (f p) z) (g p z)) z) := by
        rw [iteratedFDeriv_succ_eq_comp_right]
        change Q.symm (iteratedFDeriv ℝ n (fderiv ℝ (fun z ↦ B (f p z) (g p z))) z) = _
        rw [hjetEq z (hKW hz), hjetAdd z (hKW hz)]
        simp only [LinearIsometryEquiv.map_add]
      rw [hpoint x hx, hpoint y hy]
      exact hsum.edist_le hx hy

private theorem holderOnWith_iteratedFDeriv_comp_linearIsometry
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {W K : Set E} {α C : ℝ≥0} {m : ℕ}
    (hW : IsOpen W) (hKW : K ⊆ W) (L : F ≃ₗᵢ[ℝ] G) (f : E → F)
    (hfSmooth : ContDiffOn ℝ ∞ f W)
    (hfHolder : HolderOnWith C α (iteratedFDeriv ℝ m f) K) :
    HolderOnWith C α (iteratedFDeriv ℝ m (fun x ↦ L (f x))) K := by
  have hm : (m : ℕ∞ω) ≤ ∞ := by
    exact_mod_cast (le_top : (m : ℕ∞) ≤ (⊤ : ℕ∞))
  have hjet (x : E) (hx : x ∈ K) :
      iteratedFDeriv ℝ m (fun x ↦ L (f x)) x =
        (L : F →L[ℝ] G).compContinuousMultilinearMap
          (iteratedFDeriv ℝ m f x) := by
    change iteratedFDeriv ℝ m ((L : F →L[ℝ] G) ∘ f) x = _
    exact (L : F →L[ℝ] G).iteratedFDeriv_comp_left
      ((hfSmooth x (hKW hx)).contDiffAt (hW.mem_nhds (hKW hx))) hm
  have hdist (T U : E [×m]→L[ℝ] F) :
      dist ((L : F →L[ℝ] G).compContinuousMultilinearMap T)
        ((L : F →L[ℝ] G).compContinuousMultilinearMap U) = dist T U := by
    rw [dist_eq_norm, dist_eq_norm]
    have hsub : (L : F →L[ℝ] G).compContinuousMultilinearMap T -
        (L : F →L[ℝ] G).compContinuousMultilinearMap U =
        (L : F →L[ℝ] G).compContinuousMultilinearMap (T - U) := by
      ext v
      simp
    rw [hsub]
    exact L.toLinearIsometry.norm_compContinuousMultilinearMap (T - U)
  have hEdist (T U : E [×m]→L[ℝ] F) :
      edist ((L : F →L[ℝ] G).compContinuousMultilinearMap T)
        ((L : F →L[ℝ] G).compContinuousMultilinearMap U) = edist T U := by
    rw [edist_dist, edist_dist, hdist]
  intro x hx y hy
  rw [hjet x hx, hjet y hy, hEdist]
  exact hfHolder.edist_le hx hy

private theorem exists_common_holder_iteratedFDeriv_bilinear_ulift
    {P : Type t} {E : Type u} {F : Type v} {G : Type w} {H : Type z}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {S : Set P} {W K : Set E} {α C D : ℝ≥0} {n : ℕ}
    (hW : IsOpen W) (hKW : K ⊆ W) (B : F →L[ℝ] G →L[ℝ] H)
    (f : P → E → F) (g : P → E → G)
    (hfSmooth : ∀ p ∈ S, ContDiffOn ℝ ∞ (f p) W)
    (hgSmooth : ∀ p ∈ S, ContDiffOn ℝ ∞ (g p) W)
    (hfBound : ∀ p ∈ S, ∀ m ≤ n, ∀ x ∈ K, ‖iteratedFDeriv ℝ m (f p) x‖ ≤ C)
    (hgBound : ∀ p ∈ S, ∀ m ≤ n, ∀ x ∈ K, ‖iteratedFDeriv ℝ m (g p) x‖ ≤ D)
    (hfHolder : ∀ p ∈ S, ∀ m ≤ n,
      HolderOnWith C α (iteratedFDeriv ℝ m (f p)) K)
    (hgHolder : ∀ p ∈ S, ∀ m ≤ n,
      HolderOnWith D α (iteratedFDeriv ℝ m (g p)) K) :
    ∃ C' : ℝ≥0, ∀ p ∈ S,
      HolderOnWith C' α
        (iteratedFDeriv ℝ n (fun x ↦ B (f p x) (g p x))) K := by
  let F' : Type (max (max (max u v) w) z) := ULift.{max u w z, v} F
  let G' : Type (max (max (max u v) w) z) := ULift.{max u v z, w} G
  let H' : Type (max (max (max u v) w) z) := ULift.{max u v w, z} H
  let isoF : F' ≃ₗᵢ[ℝ] F := LinearIsometryEquiv.ulift ℝ F
  let isoG : G' ≃ₗᵢ[ℝ] G := LinearIsometryEquiv.ulift ℝ G
  let isoH : H' ≃ₗᵢ[ℝ] H := LinearIsometryEquiv.ulift ℝ H
  let fu : P → E → F' := fun p x ↦ isoF.symm (f p x)
  let gu : P → E → G' := fun p x ↦ isoG.symm (g p x)
  let B₀ : F' →L[ℝ] G' →L[ℝ] H :=
    (B.flip.comp ((isoG : G' →L[ℝ] G))).flip.comp (isoF : F' →L[ℝ] F)
  let Bu : F' →L[ℝ] G' →L[ℝ] H' :=
    ContinuousLinearMap.compL ℝ F' (G' →L[ℝ] H) (G' →L[ℝ] H')
      (ContinuousLinearMap.compL ℝ G' H H' (isoH.symm : H →L[ℝ] H')) B₀
  have hfuSmooth : ∀ p ∈ S, ContDiffOn ℝ ∞ (fu p) W := by
    intro p hp
    change ContDiffOn ℝ ∞ (isoF.symm ∘ f p) W
    exact (isoF.symm : F →L[ℝ] F').contDiff.comp_contDiffOn (hfSmooth p hp)
  have hguSmooth : ∀ p ∈ S, ContDiffOn ℝ ∞ (gu p) W := by
    intro p hp
    change ContDiffOn ℝ ∞ (isoG.symm ∘ g p) W
    exact (isoG.symm : G →L[ℝ] G').contDiff.comp_contDiffOn (hgSmooth p hp)
  have hfuBound : ∀ p ∈ S, ∀ m ≤ n, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ m (fu p) x‖ ≤ C := by
    intro p hp m hm x hx
    change ‖iteratedFDeriv ℝ m (isoF.symm ∘ f p) x‖ ≤ C
    rw [isoF.symm.norm_iteratedFDeriv_comp_left (f p) x m]
    exact hfBound p hp m hm x hx
  have hguBound : ∀ p ∈ S, ∀ m ≤ n, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ m (gu p) x‖ ≤ D := by
    intro p hp m hm x hx
    change ‖iteratedFDeriv ℝ m (isoG.symm ∘ g p) x‖ ≤ D
    rw [isoG.symm.norm_iteratedFDeriv_comp_left (g p) x m]
    exact hgBound p hp m hm x hx
  have hfuHolder : ∀ p ∈ S, ∀ m ≤ n,
      HolderOnWith C α (iteratedFDeriv ℝ m (fu p)) K := by
    intro p hp m hm
    change HolderOnWith C α
      (iteratedFDeriv ℝ m (fun x ↦ isoF.symm (f p x))) K
    exact holderOnWith_iteratedFDeriv_comp_linearIsometry hW hKW
      isoF.symm (f p) (hfSmooth p hp) (hfHolder p hp m hm)
  have hguHolder : ∀ p ∈ S, ∀ m ≤ n,
      HolderOnWith D α (iteratedFDeriv ℝ m (gu p)) K := by
    intro p hp m hm
    change HolderOnWith D α
      (iteratedFDeriv ℝ m (fun x ↦ isoG.symm (g p x))) K
    exact holderOnWith_iteratedFDeriv_comp_linearIsometry hW hKW
      isoG.symm (g p) (hgSmooth p hp) (hgHolder p hp m hm)
  obtain ⟨C', hprod⟩ := exists_common_holder_iteratedFDeriv_bilinear.{u, v, w, z, t}
    (P := P) (E := E) (F := F') (G := G') (H := H')
    (S := S) (W := W) (K := K) (α := α) (C := C) (D := D) n
    hW hKW Bu fu gu hfuSmooth hguSmooth hfuBound hguBound hfuHolder hguHolder
  refine ⟨C', ?_⟩
  intro p hp
  have hBuValue (x : E) : Bu (fu p x) (gu p x) = isoH.symm (B (f p x) (g p x)) := by
    simp [Bu, B₀, fu, gu, ContinuousLinearMap.compL_apply]
  have hLiftSmooth : ContDiffOn ℝ ∞ (fun x ↦ Bu (fu p x) (gu p x)) W := by
    exact Bu.isBoundedBilinearMap.contDiff.comp₂_contDiffOn
      (hfuSmooth p hp) (hguSmooth p hp)
  have hdown := holderOnWith_iteratedFDeriv_comp_linearIsometry hW hKW
    isoH (fun x ↦ Bu (fu p x) (gu p x)) hLiftSmooth (hprod p hp)
  have hfun : (fun x ↦ isoH (Bu (fu p x) (gu p x))) =
      (fun x ↦ B (f p x) (g p x)) := by
    funext x
    rw [hBuValue x]
    simp
  simpa only [hfun] using hdown

private theorem exists_common_holder_real_part_product
    {P E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set P} {W K : Set E} {α C D : ℝ≥0} {k : ℕ}
    (hW : IsOpen W) (hKW : K ⊆ W)
    (f g : P → E → ℂ)
    (hfSmooth : ∀ p ∈ S, ContDiffOn ℝ ∞ (f p) W)
    (hgSmooth : ∀ p ∈ S, ContDiffOn ℝ ∞ (g p) W)
    (hfBound : ∀ p ∈ S, ∀ m ≤ k, ∀ x ∈ K, ‖iteratedFDeriv ℝ m (f p) x‖ ≤ C)
    (hgBound : ∀ p ∈ S, ∀ m ≤ k, ∀ x ∈ K, ‖iteratedFDeriv ℝ m (g p) x‖ ≤ D)
    (hfHolder : ∀ p ∈ S, ∀ m ≤ k,
      HolderOnWith C α (iteratedFDeriv ℝ m (f p)) K)
    (hgHolder : ∀ p ∈ S, ∀ m ≤ k,
      HolderOnWith D α (iteratedFDeriv ℝ m (g p)) K) :
    ∃ C' : ℝ≥0, ∀ p ∈ S,
      HolderOnWith C' α
        (iteratedFDeriv ℝ k (fun z ↦ RCLike.re (f p z * g p z))) K := by
  let realPartMulBilinear : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ ℂ ℂ ℝ Complex.reCLM).comp
      (ContinuousLinearMap.mul ℝ ℂ)
  have hRealPartMulBilinear (z w : ℂ) :
      realPartMulBilinear z w = RCLike.re (z * w) := by
    simp [realPartMulBilinear, Complex.reCLM_apply]
  obtain ⟨C', hprod⟩ := exists_common_holder_iteratedFDeriv_bilinear_ulift
    hW hKW realPartMulBilinear f g hfSmooth hgSmooth
    hfBound hgBound hfHolder hgHolder
  refine ⟨C', ?_⟩
  intro p hp
  have heq : (fun z ↦ realPartMulBilinear (f p z) (g p z)) =
      (fun z ↦ RCLike.re (f p z * g p z)) := by
    funext z
    exact hRealPartMulBilinear (f p z) (g p z)
  simpa only [heq] using hprod p hp

private theorem iteratedFDeriv_finset_sum_of_contDiffOn
    {E ι F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {W : Set E} (hW : IsOpen W) (n : ℕ) (s : Finset ι)
    (f : ι → E → F) (hSmooth : ∀ i ∈ s, ContDiffOn ℝ ∞ (f i) W)
    {x : E} (hx : x ∈ W) :
    iteratedFDeriv ℝ n (fun z ↦ ∑ i ∈ s, f i z) x =
      ∑ i ∈ s, iteratedFDeriv ℝ n (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
      have hiSmooth : ContDiffOn ℝ ∞ (f i) W := hSmooth i (Finset.mem_insert_self i s)
      have hsSmooth : ContDiffOn ℝ ∞ (fun z ↦ ∑ j ∈ s, f j z) W := by
        apply ContDiffOn.sum
        intro j hj
        exact hSmooth j (Finset.mem_insert_of_mem hj)
      have hfun : (fun z ↦ ∑ j ∈ insert i s, f j z) =
          (fun z ↦ f i z + ∑ j ∈ s, f j z) := by
        funext z
        simp [Finset.sum_insert, his]
      rw [hfun]
      rw [iteratedFDeriv_add_of_contDiffOn hW n (f i)
        (fun z ↦ ∑ j ∈ s, f j z) hiSmooth hsSmooth hx]
      rw [ih (fun j hj ↦ hSmooth j (Finset.mem_insert_of_mem hj))]
      simp [Finset.sum_insert, his]

private def matrixTraceBilinearJetCoefficientSum (k : ℕ) : ℝ≥0 :=
  ∑ m ∈ Finset.range (k + 1),
    ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ≥0)

private theorem complex_product_jet_norm_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W K : Set E} {k : ℕ} {C D : ℝ≥0}
    (hW : IsOpen W) (hKW : K ⊆ W) (f g : E → ℂ)
    (hfSmooth : ContDiffOn ℝ ∞ f W) (hgSmooth : ContDiffOn ℝ ∞ g W)
    (hfBound : ∀ m ≤ k, ∀ x ∈ K, ‖iteratedFDeriv ℝ m f x‖ ≤ C)
    (hgBound : ∀ m ≤ k, ∀ x ∈ K, ‖iteratedFDeriv ℝ m g x‖ ≤ D) :
    ∀ m ≤ k, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ m (fun z ↦ f z * g z) x‖ ≤
        matrixTraceBilinearJetCoefficientSum k * C * D := by
  intro m hm x hx
  let T : ℝ≥0 := matrixTraceBilinearJetCoefficientSum k
  have hCoeff :
      (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ≥0)) ≤ T := by
    let a : ℕ → ℝ≥0 := fun j =>
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ≥0)
    dsimp [T, matrixTraceBilinearJetCoefficientSum]
    change a m ≤ ∑ j ∈ Finset.range (k + 1), a j
    exact Finset.single_le_sum (fun j hj ↦ by positivity)
      (Finset.mem_range.mpr (by omega))
  have hCoeffR :
      (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ)) ≤ (T : ℝ) := by
    exact_mod_cast hCoeff
  have hn : (m : ℕ∞ω) ≤ ∞ := by
    exact_mod_cast (le_top : (m : ℕ∞) ≤ (⊤ : ℕ∞))
  have hRaw := norm_iteratedFDerivWithin_mul_le
    hfSmooth hgSmooth hW.uniqueDiffOn (hKW hx) (n := m) hn
  have hOutEq : iteratedFDerivWithin ℝ m (fun z ↦ f z * g z) W x =
      iteratedFDeriv ℝ m (fun z ↦ f z * g z) x :=
    iteratedFDerivWithin_of_isOpen m hW (hKW hx)
  have hFbound (i : ℕ) (hi : i ∈ Finset.range (m + 1)) :
      ‖iteratedFDerivWithin ℝ i f W x‖ ≤ C := by
    rw [iteratedFDerivWithin_of_isOpen i hW (hKW hx)]
    exact hfBound i (Nat.le_trans (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hm) x hx
  have hGbound (i : ℕ) (hi : i ∈ Finset.range (m + 1)) :
      ‖iteratedFDerivWithin ℝ (m - i) g W x‖ ≤ D := by
    rw [iteratedFDerivWithin_of_isOpen (m - i) hW (hKW hx)]
    exact hgBound (m - i) (Nat.le_trans (Nat.sub_le _ _) hm) x hx
  calc
    ‖iteratedFDeriv ℝ m (fun z ↦ f z * g z) x‖ =
        ‖iteratedFDerivWithin ℝ m (fun z ↦ f z * g z) W x‖ := by rw [hOutEq]
    _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i f W x‖ *
          ‖iteratedFDerivWithin ℝ (m - i) g W x‖ := hRaw
    _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * C * D := by
      apply Finset.sum_le_sum
      intro i hi
      have hci : 0 ≤ (m.choose i : ℝ) := by positivity
      have hfg := mul_le_mul (hFbound i hi) (hGbound i hi)
        (norm_nonneg _) C.coe_nonneg
      calc
        (m.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i f W x‖ *
            ‖iteratedFDerivWithin ℝ (m - i) g W x‖ =
          (m.choose i : ℝ) *
            (‖iteratedFDerivWithin ℝ i f W x‖ *
              ‖iteratedFDerivWithin ℝ (m - i) g W x‖) := by ring
        _ ≤ (m.choose i : ℝ) * (C * D) := mul_le_mul_of_nonneg_left hfg hci
        _ = (m.choose i : ℝ) * C * D := by ring
    _ = (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ)) * C * D := by
      calc
        (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * C * D) =
            (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * C) * D := by
          rw [← Finset.sum_mul]
        _ = ((∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ)) * C) * D := by
          rw [← Finset.sum_mul]
        _ = (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ)) * C * D := by ring
    _ ≤ (T : ℝ) * C * D := by gcongr

private theorem realPart_iteratedFDeriv_norm_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : Set E} {f : E → ℂ} {x : E}
    (hW : IsOpen W) (hx : x ∈ W) (hf : ContDiffOn ℝ ∞ f W) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun z ↦ RCLike.re (f z)) x‖ ≤
      ‖iteratedFDeriv ℝ m f x‖ := by
  have hm : (m : ℕ∞ω) ≤ ∞ := by
    exact_mod_cast (le_top : (m : ℕ∞) ≤ (⊤ : ℕ∞))
  have hjet : iteratedFDeriv ℝ m (fun z ↦ RCLike.re (f z)) x =
      Complex.reCLM.compContinuousMultilinearMap (iteratedFDeriv ℝ m f x) := by
    change iteratedFDeriv ℝ m (Complex.reCLM ∘ f) x = _
    exact Complex.reCLM.iteratedFDeriv_comp_left
      ((hf x hx).contDiffAt (hW.mem_nhds hx)) hm
  rw [hjet]
  apply (ContinuousMultilinearMap.opNorm_le_iff
    (show 0 ≤ ‖iteratedFDeriv ℝ m f x‖ by positivity)).2
  intro v
  calc
    ‖Complex.reCLM.compContinuousMultilinearMap (iteratedFDeriv ℝ m f x) v‖ ≤
        ‖iteratedFDeriv ℝ m f x v‖ := by
      have h := Complex.abs_re_le_norm (iteratedFDeriv ℝ m f x v)
      simpa [Complex.reCLM_apply, Real.norm_eq_abs] using h
    _ ≤ ‖iteratedFDeriv ℝ m f x‖ * ∏ i, ‖v i‖ :=
      (iteratedFDeriv ℝ m f x).le_opNorm_mul_prod_of_le (fun i ↦ le_rfl)

private theorem matrix_trace_product_jet_norm_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n k : ℕ} {W K : Set E} {C D : ℝ≥0}
    (hW : IsOpen W) (hKW : K ⊆ W)
    (A B : E → Matrix (Fin n) (Fin n) ℂ)
    (hASmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x ↦ A x i j) W)
    (hBSmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x ↦ B x i j) W)
    (hAjet : ∀ i j m, m ≤ k → ∀ x ∈ K,
      ‖iteratedFDeriv ℝ m (fun x ↦ A x i j) x‖ ≤ C)
    (hBjet : ∀ i j m, m ≤ k → ∀ x ∈ K,
      ‖iteratedFDeriv ℝ m (fun x ↦ B x i j) x‖ ≤ D) :
    ∀ m ≤ k, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ m (fun x ↦ RCLike.re ((A x * B x).trace)) x‖ ≤
        (n : ℝ≥0)^2 * matrixTraceBilinearJetCoefficientSum k * C * D := by
  classical
  let term (i j : Fin n) (x : E) := RCLike.re (A x i j * B x j i)
  let inner (i : Fin n) (x : E) := ∑ j : Fin n, term i j x
  let total (x : E) := ∑ i : Fin n, inner i x
  have htermSmooth (i j : Fin n) : ContDiffOn ℝ ∞ (term i j) W := by
    have hmul := (hASmooth i j).mul (hBSmooth j i)
    change ContDiffOn ℝ ∞ (fun x ↦ Complex.re (A x i j * B x j i)) W
    exact Complex.reCLM.contDiff.comp_contDiffOn hmul
  have hinnerSmooth (i : Fin n) : ContDiffOn ℝ ∞ (inner i) W := by
    apply ContDiffOn.sum
    intro j hj
    exact htermSmooth i j
  have htotalSmooth : ContDiffOn ℝ ∞ total W := by
    apply ContDiffOn.sum
    intro i hi
    exact hinnerSmooth i
  have hformula (x : E) :
      RCLike.re ((A x * B x).trace) = total x := by
    simpa [total, inner, term] using real_matrix_trace_mul_entries (A x) (B x)
  have hjetEq (m : ℕ) (x : E) (hx : x ∈ K) :
      iteratedFDeriv ℝ m (fun x ↦ RCLike.re ((A x * B x).trace)) x =
        ∑ i : Fin n, ∑ j : Fin n, iteratedFDeriv ℝ m (term i j) x := by
    have hsum :
        iteratedFDeriv ℝ m total x = ∑ i : Fin n, iteratedFDeriv ℝ m (inner i) x :=
      iteratedFDeriv_finset_sum_of_contDiffOn hW m Finset.univ inner
        (fun i hi ↦ hinnerSmooth i) (hKW hx)
    have hinnerJet (i : Fin n) :
        iteratedFDeriv ℝ m (inner i) x =
          ∑ j : Fin n, iteratedFDeriv ℝ m (term i j) x :=
      iteratedFDeriv_finset_sum_of_contDiffOn hW m Finset.univ
        (term i) (fun j hj ↦ htermSmooth i j) (hKW hx)
    have htraceFun : (fun x ↦ RCLike.re ((A x * B x).trace)) = total := by
      funext y
      exact hformula y
    rw [htraceFun, hsum]
    simp_rw [hinnerJet]
  have htermBound (i j : Fin n) (m : ℕ) (hm : m ≤ k) (x : E) (hx : x ∈ K) :
      ‖iteratedFDeriv ℝ m (term i j) x‖ ≤
        matrixTraceBilinearJetCoefficientSum k * C * D := by
    have hmulSmooth : ContDiffOn ℝ ∞ (fun y ↦ A y i j * B y j i) W :=
      (hASmooth i j).mul (hBSmooth j i)
    have hmulBound := complex_product_jet_norm_bound hW hKW
      (fun y ↦ A y i j) (fun y ↦ B y j i)
      (hASmooth i j) (hBSmooth j i)
      (fun l hl y hy ↦ hAjet i j l hl y hy)
      (fun l hl y hy ↦ hBjet j i l hl y hy)
      m hm x hx
    exact (realPart_iteratedFDeriv_norm_bound hW (hKW hx) hmulSmooth m).trans hmulBound
  let Cterm : ℝ≥0 := matrixTraceBilinearJetCoefficientSum k * C * D
  let Ctrace : ℝ≥0 := (n : ℝ≥0)^2 * Cterm
  intro m hm x hx
  rw [hjetEq m x hx]
  calc
    ‖∑ i : Fin n, ∑ j : Fin n, iteratedFDeriv ℝ m (term i j) x‖ ≤
        ∑ i : Fin n, ‖∑ j : Fin n, iteratedFDeriv ℝ m (term i j) x‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, (Cterm : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        ‖∑ j : Fin n, iteratedFDeriv ℝ m (term i j) x‖ ≤
            ∑ j : Fin n, ‖iteratedFDeriv ℝ m (term i j) x‖ := norm_sum_le _ _
        _ ≤ ∑ j : Fin n, (Cterm : ℝ) := by
          apply Finset.sum_le_sum
          intro j hj
          exact htermBound i j m hm x hx
    _ = (Ctrace : ℝ) := by
      simp [Ctrace, Cterm, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Fintype.card_fin]
      ring
    _ = ((n : ℝ≥0)^2 * matrixTraceBilinearJetCoefficientSum k * C * D : ℝ) := by
      simp [Ctrace, Cterm, NNReal.coe_mul]
      ring

/-- Uniform bounds on every input jet, including Hölder control of all lower jets, yield a
single `C^{k,α}` bound on the real trace of products throughout a family. The common output
constant precedes the family parameter and is independent of its members. -/
theorem exists_holderBoundOn_matrix_trace_product
    {P E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n k : ℕ} {α C D : ℝ≥0} {W K : Set E}
    (S : Set P) (hW : IsOpen W) (hKW : K ⊆ W)
    (A B : P → E → Matrix (Fin n) (Fin n) ℂ)
    (hASmooth : ∀ p ∈ S, ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ A p z i j) W)
    (hBSmooth : ∀ p ∈ S, ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ B p z i j) W)
    (hA : ∀ p ∈ S, ∀ i j,
      (∀ m ≤ k, ∀ z ∈ K, ‖iteratedFDeriv ℝ m (fun z ↦ A p z i j) z‖ ≤ C) ∧
      (∀ m < k, HolderOnWith C α (iteratedFDeriv ℝ m (fun z ↦ A p z i j)) K) ∧
      HolderOnWith C α (iteratedFDeriv ℝ k (fun z ↦ A p z i j)) K)
    (hB : ∀ p ∈ S, ∀ i j,
      (∀ m ≤ k, ∀ z ∈ K, ‖iteratedFDeriv ℝ m (fun z ↦ B p z i j) z‖ ≤ D) ∧
      (∀ m < k, HolderOnWith D α (iteratedFDeriv ℝ m (fun z ↦ B p z i j)) K) ∧
      HolderOnWith D α (iteratedFDeriv ℝ k (fun z ↦ B p z i j)) K) :
    ∃ C' : ℝ≥0, ∀ p ∈ S,
      (∀ m ≤ k, ∀ z ∈ K,
        ‖iteratedFDeriv ℝ m (fun z ↦ RCLike.re ((A p z * B p z).trace)) z‖ ≤ C') ∧
      HolderOnWith C' α
        (iteratedFDeriv ℝ k (fun z ↦ RCLike.re ((A p z * B p z).trace))) K := by
  by_cases hk : k = 0
  · subst k
    let C' : ℝ≥0 := ∑ _i ∈ (Finset.univ : Finset (Fin n)),
      ∑ _j ∈ (Finset.univ : Finset (Fin n)), 2 * C * D
    have hsum :
        ∑ _i ∈ (Finset.univ : Finset (Fin n)),
          ∑ _j ∈ (Finset.univ : Finset (Fin n)), (C : ℝ) * D ≤ (C' : ℝ) := by
      dsimp [C']
      push_cast
      gcongr
      nlinarith [C.coe_nonneg]
    refine ⟨C', ?_⟩
    intro p hp
    constructor
    · intro m hm z hz
      have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
      subst m
      rw [norm_iteratedFDeriv_zero]
      have hABound : ∀ i j z, z ∈ K → ‖A p z i j‖ ≤ C := by
        intro i j z hz
        simpa only [norm_iteratedFDeriv_zero] using
          (hA p hp i j).1 0 (by omega) z hz
      have hBBound : ∀ i j z, z ∈ K → ‖B p z i j‖ ≤ D := by
        intro i j z hz
        simpa only [norm_iteratedFDeriv_zero] using
          (hB p hp i j).1 0 (by omega) z hz
      exact (matrix_trace_value_bound (fun z ↦ A p z) (fun z ↦ B p z)
        hABound hBBound z hz).trans hsum
    · have hABound : ∀ i j z, z ∈ K → ‖A p z i j‖ ≤ C := by
        intro i j z hz
        simpa only [norm_iteratedFDeriv_zero] using
          (hA p hp i j).1 0 (by omega) z hz
      have hBBound : ∀ i j z, z ∈ K → ‖B p z i j‖ ≤ D := by
        intro i j z hz
        simpa only [norm_iteratedFDeriv_zero] using
          (hB p hp i j).1 0 (by omega) z hz
      have hAHolder : ∀ i j, HolderOnWith C α (fun z ↦ A p z i j) K := by
        intro i j
        exact (holderOnWith_zero_iteratedFDeriv_iff
          (fun z ↦ A p z i j)).1 (hA p hp i j).2.2
      have hBHolder : ∀ i j, HolderOnWith D α (fun z ↦ B p z i j) K := by
        intro i j
        exact (holderOnWith_zero_iteratedFDeriv_iff
          (fun z ↦ B p z i j)).1 (hB p hp i j).2.2
      have htrace := matrix_trace_holder (fun z ↦ A p z) (fun z ↦ B p z)
        hABound hBBound hAHolder hBHolder
      exact (holderOnWith_zero_iteratedFDeriv_iff
        (fun z ↦ RCLike.re ((A p z * B p z).trace))).2 htrace
  · let Q := P × (Fin n × Fin n)
    let S' : Set Q := {q | q.1 ∈ S}
    let f : Q → E → ℂ := fun q z ↦ A q.1 z q.2.1 q.2.2
    let g : Q → E → ℂ := fun q z ↦ B q.1 z q.2.2 q.2.1
    have hfSmooth : ∀ q ∈ S', ContDiffOn ℝ ∞ (f q) W := by
      intro q hq
      exact hASmooth q.1 hq q.2.1 q.2.2
    have hgSmooth : ∀ q ∈ S', ContDiffOn ℝ ∞ (g q) W := by
      intro q hq
      exact hBSmooth q.1 hq q.2.2 q.2.1
    have hfBound : ∀ q ∈ S', ∀ m ≤ k, ∀ z ∈ K,
        ‖iteratedFDeriv ℝ m (f q) z‖ ≤ C := by
      intro q hq m hm z hz
      exact (hA q.1 hq q.2.1 q.2.2).1 m hm z hz
    have hgBound : ∀ q ∈ S', ∀ m ≤ k, ∀ z ∈ K,
        ‖iteratedFDeriv ℝ m (g q) z‖ ≤ D := by
      intro q hq m hm z hz
      exact (hB q.1 hq q.2.2 q.2.1).1 m hm z hz
    have hfHolder : ∀ q ∈ S', ∀ m ≤ k,
        HolderOnWith C α (iteratedFDeriv ℝ m (f q)) K := by
      intro q hq m hm
      by_cases hmEq : m = k
      · subst m
        exact (hA q.1 hq q.2.1 q.2.2).2.2
      · exact (hA q.1 hq q.2.1 q.2.2).2.1 m (by omega)
    have hgHolder : ∀ q ∈ S', ∀ m ≤ k,
        HolderOnWith D α (iteratedFDeriv ℝ m (g q)) K := by
      intro q hq m hm
      by_cases hmEq : m = k
      · subst m
        exact (hB q.1 hq q.2.2 q.2.1).2.2
      · exact (hB q.1 hq q.2.2 q.2.1).2.1 m (by omega)
    obtain ⟨Cterm, hterm⟩ := exists_common_holder_real_part_product
      hW hKW f g hfSmooth hgSmooth hfBound hgBound hfHolder hgHolder
    let Cjet : ℝ≥0 := (n : ℝ≥0)^2 *
      matrixTraceBilinearJetCoefficientSum k * C * D
    let Ctop : ℝ≥0 := (n : ℝ≥0) * ((n : ℝ≥0) * Cterm)
    let C' : ℝ≥0 := max Cjet Ctop
    refine ⟨C', ?_⟩
    intro p hp
    constructor
    · intro m hm z hz
      have hpoint := matrix_trace_product_jet_norm_bound hW hKW (A p) (B p)
        (fun i j ↦ hASmooth p hp i j) (fun i j ↦ hBSmooth p hp i j)
        (fun i j m hm z hz ↦ (hA p hp i j).1 m hm z hz)
        (fun i j m hm z hz ↦ (hB p hp i j).1 m hm z hz)
        m hm z hz
      exact hpoint.trans (le_max_left Cjet Ctop)
    · let term (i j : Fin n) (z : E) := RCLike.re (A p z i j * B p z j i)
      have hTerm (i j : Fin n) :
          HolderOnWith Cterm α (iteratedFDeriv ℝ k (term i j)) K := by
        let q : Q := (p, (i, j))
        have hq : q ∈ S' := hp
        have h := hterm q hq
        simpa [term, f, g, q] using h
      have hInner (i : Fin n) :
          HolderOnWith ((n : ℝ≥0) * Cterm) α
            (fun z ↦ ∑ j : Fin n, iteratedFDeriv ℝ k (term i j) z) K := by
        have h := holderOnWith_finset_sum_normed (Finset.univ : Finset (Fin n))
          (fun j z ↦ iteratedFDeriv ℝ k (term i j) z) (fun j ↦ hTerm i j)
        simpa [Finset.card_univ, Fintype.card_fin] using h
      have hSum : HolderOnWith Ctop α
          (fun z ↦ ∑ i : Fin n, ∑ j : Fin n, iteratedFDeriv ℝ k (term i j) z) K := by
        have h := holderOnWith_finset_sum_normed (Finset.univ : Finset (Fin n))
          (fun i z ↦ ∑ j : Fin n, iteratedFDeriv ℝ k (term i j) z) hInner
        simpa [Ctop, Finset.card_univ, Fintype.card_fin] using h
      have htraceFun : (fun z ↦ RCLike.re ((A p z * B p z).trace)) =
          (fun z ↦ ∑ i : Fin n, ∑ j : Fin n, term i j z) := by
        funext z
        simpa [term] using real_matrix_trace_mul_entries (A p z) (B p z)
      have hJetEq (z : E) (hz : z ∈ K) :
          iteratedFDeriv ℝ k (fun z ↦ RCLike.re ((A p z * B p z).trace)) z =
            ∑ i : Fin n, ∑ j : Fin n, iteratedFDeriv ℝ k (term i j) z := by
        calc
          iteratedFDeriv ℝ k (fun z ↦ RCLike.re ((A p z * B p z).trace)) z =
              iteratedFDeriv ℝ k (fun z ↦ ∑ i : Fin n, ∑ j : Fin n, term i j z) z := by
                rw [htraceFun]
          _ = ∑ i : Fin n, iteratedFDeriv ℝ k (fun z ↦ ∑ j : Fin n, term i j z) z :=
            iteratedFDeriv_finset_sum_of_contDiffOn hW k Finset.univ
              (fun i z ↦ ∑ j : Fin n, term i j z)
              (by
                intro i hi
                apply ContDiffOn.sum
                intro j hj
                exact Complex.reCLM.contDiff.comp_contDiffOn
                  ((hASmooth p hp i j).mul (hBSmooth p hp j i))) (hKW hz)
          _ = ∑ i : Fin n, ∑ j : Fin n, iteratedFDeriv ℝ k (term i j) z := by
            apply Finset.sum_congr rfl
            intro i hi
            exact iteratedFDeriv_finset_sum_of_contDiffOn hW k Finset.univ
              (term i) (by
                intro j hj
                exact Complex.reCLM.contDiff.comp_contDiffOn
                  ((hASmooth p hp i j).mul (hBSmooth p hp j i))) (hKW hz)
      have hTop : HolderOnWith Ctop α
          (iteratedFDeriv ℝ k (fun z ↦ RCLike.re ((A p z * B p z).trace))) K := by
        intro x hx y hy
        rw [hJetEq x hx, hJetEq y hy]
        exact hSum.edist_le hx hy
      exact hTop.mono_const (le_max_right Cjet Ctop)

end KahlerForm

end
