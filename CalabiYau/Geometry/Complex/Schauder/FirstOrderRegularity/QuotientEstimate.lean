module

public import CalabiYau.Geometry.Complex.Schauder.InteriorProvider.Order
public import CalabiYau.Geometry.Complex.Schauder.FiniteDifferenceHolder
import CalabiYau.Geometry.Complex.Schauder.DerivativeHolder
import CalabiYau.Geometry.Complex.Schauder.OperatorCommutator.HolderBound.ComplexHessianEntry
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# First-order quotient estimates

This leaf proves the finite-difference estimate required by the frozen first-order Schauder step.
The solution is initially only C²: its quotients remain C², and the forcing equation retains the
negative coefficient commutator with the translated Hessian. No derivative of the equation is used.
-/

open Set Matrix Metric
open scoped ContDiff NNReal ENNReal Topology

@[expose] public section

namespace CalabiYau.Schauder

/-- The quotient estimates used by `FirstOrderRegularity`. The final local clause
is the expanded uniform-quotient condition. -/
private theorem quotient_complexHessian_differenceQuotient_entry {n : ℕ}
    (u : EuclideanSpace ℂ (Fin n) → ℝ) (v : EuclideanSpace ℂ (Fin n))
    (h : ℝ) (x : EuclideanSpace ℂ (Fin n))
    (hu₀ : ContDiffAt ℝ 2 u x) (hu₁ : ContDiffAt ℝ 2 u (x + h • v))
    (j k : Fin n) :
    complexHessian (fun z ↦ (u (z + h • v) - u z) / h) x j k =
      ((1 / h : ℝ) : ℂ) *
        (complexHessian u (x + h • v) j k - complexHessian u x j k) := by
  have hshift : ContDiffAt ℝ 2 (fun z ↦ u (z + h • v)) x := by
    exact hu₁.comp x (by fun_prop)
  have hq : ContDiffAt ℝ 2 (fun z ↦ (u (z + h • v) - u z) / h) x :=
    (hshift.sub hu₀).div_const h
  rw [complexHessian_apply hq, complexHessian_apply hu₁, complexHessian_apply hu₀]
  have hF (f : EuclideanSpace ℂ (Fin n) → ℝ) (y a b : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fderiv ℝ f) y a b = iteratedFDeriv ℝ 2 f y ![a, b] :=
    (iteratedFDeriv_two_apply f y ![a, b]).symm
  simp_rw [hF]
  have hqfun : (fun z ↦ (u (z + h • v) - u z) / h) =
      h⁻¹ • (fun z ↦ u (z + h • v) - u z) := by
    funext z
    simp [div_eq_mul_inv, mul_comm]
  have hdiff : iteratedFDeriv ℝ 2 (fun z ↦ u (z + h • v) - u z) x =
      iteratedFDeriv ℝ 2 (fun z ↦ u (z + h • v)) x - iteratedFDeriv ℝ 2 u x := by
    change iteratedFDeriv ℝ 2 ((fun z ↦ u (z + h • v)) - u) x = _
    exact iteratedFDeriv_sub_apply (i := 2) hshift hu₀
  have hshiftI : iteratedFDeriv ℝ 2 (fun z ↦ u (z + h • v)) x =
      iteratedFDeriv ℝ 2 u (x + h • v) :=
    iteratedFDeriv_comp_add_right 2 (h • v) x
  rw [hqfun]
  rw [iteratedFDeriv_const_smul_apply (i := 2) (a := h⁻¹) (hshift.sub hu₀)]
  simp only [_root_.smul_apply]
  rw [hdiff, hshiftI]
  have hEval (F G : EuclideanSpace ℂ (Fin n) [×2]→L[ℝ] ℝ)
      (m : Fin 2 → EuclideanSpace ℂ (Fin n)) : (F - G) m = F m - G m := rfl
  simp only [hEval]
  simp only [smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_inv]
  simp_rw [← Complex.ofReal_inv]
  ring_nf

private theorem quotient_complexEllipticOp_differenceQuotient {n : ℕ}
    (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (u : EuclideanSpace ℂ (Fin n) → ℝ) (v : EuclideanSpace ℂ (Fin n))
    (h : ℝ) (x : EuclideanSpace ℂ (Fin n)) (_hh : h ≠ 0)
    (hu₀ : ContDiffAt ℝ 2 u x) (hu₁ : ContDiffAt ℝ 2 u (x + h • v)) :
    complexEllipticOp A (fun z ↦ (u (z + h • v) - u z) / h) x =
      (complexEllipticOp A u (x + h • v) - complexEllipticOp A u x) / h -
        RCLike.re (((A (x + h • v) - A x) * complexHessian u (x + h • v)).trace) / h := by
  have hH : complexHessian (fun z ↦ (u (z + h • v) - u z) / h) x =
      ((1 / h : ℝ) : ℂ) •
        (complexHessian u (x + h • v) - complexHessian u x) := by
    ext j k
    change complexHessian (fun z ↦ (u (z + h • v) - u z) / h) x j k =
      ((1 / h : ℝ) : ℂ) *
        (complexHessian u (x + h • v) j k - complexHessian u x j k)
    exact quotient_complexHessian_differenceQuotient_entry u v h x hu₀ hu₁ j k
  have hmat :
      A x * (complexHessian u (x + h • v) - complexHessian u x) =
        A (x + h • v) * complexHessian u (x + h • v) -
          A x * complexHessian u x -
          (A (x + h • v) - A x) * complexHessian u (x + h • v) := by
    noncomm_ring
  have htrace := congrArg Matrix.trace hmat
  simp only [complexEllipticOp]
  rw [hH]
  simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  change Complex.re (((1 / h : ℝ) : ℂ) *
      (A x * (complexHessian u (x + h • v) - complexHessian u x)).trace) =
    (Complex.re (A (x + h • v) * complexHessian u (x + h • v)).trace -
      Complex.re (A x * complexHessian u x).trace) / h -
      Complex.re ((A (x + h • v) - A x) * complexHessian u (x + h • v)).trace / h
  have hre (z : ℂ) :
      Complex.re (((1 / h : ℝ) : ℂ) * z) = (1 / h) * Complex.re z := by
    simp [Complex.mul_re]
  rw [hre, htrace]
  simp only [Complex.sub_re, Matrix.trace_sub]
  ring

private theorem qsrc_holderOn_zero {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {α C : ℝ≥0} {K : Set E} {f : E → F}
    (hf : HolderBoundOn 0 α C K f) : HolderOnWith C α f K := by
  have hs : HolderOnWith C α (iteratedFDeriv ℝ 0 f) K := hf.2
  rw [iteratedFDeriv_zero_eq_comp] at hs
  let c := continuousMultilinearCurryFin0 ℝ E F
  intro x hx y hy
  have h := hs x hx y hy
  change edist (c.symm (f x)) (c.symm (f y)) ≤ _ at h
  rw [c.symm.edist_map] at h
  exact h

private theorem qsrc_holderBoundOn_zero_sub {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {α C D : ℝ≥0} {K : Set E} {f g : E → ℝ}
    (hf : HolderBoundOn 0 α C K f) (hg : HolderBoundOn 0 α D K g) :
    HolderBoundOn 0 α (C + D) K (fun x ↦ f x - g x) := by
  have hsub : HolderOnWith (C + D) α (fun x ↦ f x - g x) K := by
    intro x hx y hy
    calc
      edist (f x - g x) (f y - g y) = edist (f x + -g x) (f y + -g y) := by simp [sub_eq_add_neg]
      _ ≤ edist (f x) (f y) + edist (-g x) (-g y) := edist_add_add_le _ _ _ _
      _ = edist (f x) (f y) + edist (g x) (g y) := by simp
      _ ≤ (C : ℝ≥0∞) * edist x y ^ (α : ℝ) + (D : ℝ≥0∞) * edist x y ^ (α : ℝ) :=
        add_le_add ((qsrc_holderOn_zero hf) x hx y hy) ((qsrc_holderOn_zero hg) x hx y hy)
      _ = ((C + D : ℝ≥0) : ℝ≥0∞) * edist x y ^ (α : ℝ) := by rw [ENNReal.coe_add, add_mul]
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    rw [norm_iteratedFDeriv_zero]
    have hfx : ‖f x‖ ≤ C := by simpa [norm_iteratedFDeriv_zero] using hf.1 0 le_rfl x hx
    have hgx : ‖g x‖ ≤ D := by simpa [norm_iteratedFDeriv_zero] using hg.1 0 le_rfl x hx
    calc
      ‖f x - g x‖ ≤ ‖f x‖ + ‖g x‖ := norm_sub_le _ _
      _ ≤ C + D := add_le_add hfx hgx
  · rw [iteratedFDeriv_zero_eq_comp]
    let c := continuousMultilinearCurryFin0 ℝ E ℝ
    intro x hx y hy
    change edist (c.symm (f x - g x)) (c.symm (f y - g y)) ≤ _
    rw [c.symm.edist_map]
    exact hsub x hx y hy

private theorem qsrc_holderBoundOn_zero_translate {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α C : ℝ≥0} {K S : Set E} {f : E → F} {c : E}
    (hf : HolderBoundOn 0 α C K f)
    (hshift : ∀ x ∈ S, x + c ∈ K) :
    HolderBoundOn 0 α C S (fun x ↦ f (x + c)) := by
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    rw [norm_iteratedFDeriv_zero]
    simpa [norm_iteratedFDeriv_zero] using hf.1 0 le_rfl (x + c) (hshift x hx)
  · have hholder := qsrc_holderOn_zero hf
    change HolderOnWith C α (iteratedFDeriv ℝ 0 (fun x ↦ f (x + c))) S
    rw [iteratedFDeriv_zero_eq_comp]
    let L := continuousMultilinearCurryFin0 ℝ E F
    intro x hx y hy
    change edist (L.symm (f (x + c))) (L.symm (f (y + c))) ≤ _
    rw [L.symm.edist_map]
    have hdist : edist (x + c) (y + c) = edist x y := by
      rw [edist_dist, edist_dist, dist_add_right]
    simpa only [hdist] using hholder (x + c) (hshift x hx) (y + c) (hshift y hy)

private theorem qsrc_holderOnWith_re_mul {E : Type*} [MetricSpace E]
    {α C D M N : ℝ≥0} {K : Set E} {f g : E → ℂ}
    (hf : HolderOnWith C α f K) (hg : HolderOnWith D α g K)
    (hfNorm : ∀ x ∈ K, ‖f x‖ ≤ M) (hgNorm : ∀ x ∈ K, ‖g x‖ ≤ N) :
    HolderOnWith (M * D + N * C) α (fun x ↦ Complex.re (f x * g x)) K := by
  have hprod : HolderOnWith (M * D + N * C) α (fun x ↦ f x * g x) K :=
    holderOnWith_bilinear_of_opNorm_le_one (ContinuousLinearMap.mul ℝ ℂ)
      (ContinuousLinearMap.opNorm_mul_le ℝ ℂ) hf hg hfNorm hgNorm
  intro x hx y hy
  rw [edist_dist, Real.dist_eq, ← Complex.sub_re]
  calc
    ENNReal.ofReal |((f x * g x) - (f y * g y)).re| ≤
        ENNReal.ofReal ‖(f x * g x) - (f y * g y)‖ :=
      ENNReal.ofReal_le_ofReal (Complex.abs_re_le_norm _)
    _ = edist (f x * g x) (f y * g y) := by rw [edist_dist, dist_eq_norm]
    _ ≤ (↑(M * D + N * C) : ℝ≥0∞) * edist x y ^ (α : ℝ) := hprod x hx y hy

private theorem qsrc_holderOnWith_realTraceProduct {n : ℕ}
    {α KA KH : ℝ≥0} {s : Set (EuclideanSpace ℂ (Fin n))}
    {Q H : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    (hQ : ∀ i j, HolderBoundOn 0 α KA s (fun x ↦ Q x i j))
    (hH : ∀ i j, HolderOnWith KH α (fun x ↦ H x i j) s)
    (hQbound : ∀ i j x, x ∈ s → ‖Q x i j‖ ≤ KA)
    (hHbound : ∀ i j x, x ∈ s → ‖H x i j‖ ≤ KH) :
    HolderOnWith ((n * n : ℕ) * (KA * KH + KH * KA)) α
      (fun x ↦ Complex.re ((Q x * H x).trace)) s := by
  let I := Fin n × Fin n
  let term : I → EuclideanSpace ℂ (Fin n) → ℝ := fun ij x =>
    Complex.re (Q x ij.1 ij.2 * H x ij.2 ij.1)
  have hterm (ij : I) : HolderOnWith (KA * KH + KH * KA) α (term ij) s := by
    exact qsrc_holderOnWith_re_mul (qsrc_holderOn_zero (hQ ij.1 ij.2))
      (hH ij.2 ij.1) (fun x hx => hQbound ij.1 ij.2 x hx)
      (fun x hx => hHbound ij.2 ij.1 x hx)
  have hsum : HolderOnWith (∑ _ij : I, (KA * KH + KH * KA)) α
      (fun x ↦ ∑ ij : I, term ij x) s :=
    holderOnWith_finset_sum Finset.univ (fun _ : I => KA * KH + KH * KA)
      term (fun ij _ => hterm ij)
  have htrace : (fun x ↦ Complex.re ((Q x * H x).trace)) =
      (fun x ↦ ∑ ij : I, term ij x) := by
    funext x
    simp [term, I, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type]
  have hcard : (∑ _ij : I, (KA * KH + KH * KA)) =
      (n * n : ℕ) * (KA * KH + KH * KA) := by
    simp [I, Fintype.card_prod]
    ring
  rw [htrace, ← hcard]
  exact hsum

private theorem qsrc_holderBoundOn_zero_realTraceProduct {n : ℕ}
    {α KA KH : ℝ≥0} {s : Set (EuclideanSpace ℂ (Fin n))}
    {Q H : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    (hQ : ∀ i j, HolderBoundOn 0 α KA s (fun x ↦ Q x i j))
    (hH : ∀ i j, HolderOnWith KH α (fun x ↦ H x i j) s)
    (hQbound : ∀ i j x, x ∈ s → ‖Q x i j‖ ≤ KA)
    (hHbound : ∀ i j x, x ∈ s → ‖H x i j‖ ≤ KH) :
    HolderBoundOn 0 α ((n * n : ℕ) * (KA * KH + KH * KA)) s
      (fun x ↦ Complex.re ((Q x * H x).trace)) := by
  let C : ℝ≥0 := (n * n : ℕ) * (KA * KH + KH * KA)
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    rw [norm_iteratedFDeriv_zero]
    have htrace : Complex.re ((Q x * H x).trace) =
        ∑ ij : Fin n × Fin n, Complex.re (Q x ij.1 ij.2 * H x ij.2 ij.1) := by
      simp [Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type]
    rw [htrace]
    calc
      |∑ ij : Fin n × Fin n, Complex.re (Q x ij.1 ij.2 * H x ij.2 ij.1)| ≤
          ∑ ij : Fin n × Fin n, |Complex.re (Q x ij.1 ij.2 * H x ij.2 ij.1)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ij : Fin n × Fin n, ‖Q x ij.1 ij.2‖ * ‖H x ij.2 ij.1‖ := by
        apply Finset.sum_le_sum
        intro ij _
        calc
          |Complex.re (Q x ij.1 ij.2 * H x ij.2 ij.1)| ≤
              ‖Q x ij.1 ij.2 * H x ij.2 ij.1‖ := Complex.abs_re_le_norm _
          _ = ‖Q x ij.1 ij.2‖ * ‖H x ij.2 ij.1‖ := by rw [Complex.norm_mul]
      _ ≤ ∑ _ij : Fin n × Fin n, (KA : ℝ) * KH := by
        exact Finset.sum_le_sum fun ij _ =>
          mul_le_mul (hQbound ij.1 ij.2 x hx) (hHbound ij.2 ij.1 x hx)
            (norm_nonneg _) (by positivity)
      _ = (n * n : ℕ) * ((KA : ℝ) * KH) := by simp [Fintype.card_prod]
      _ ≤ C := by
        dsimp [C]
        push_cast
        gcongr
        exact le_add_of_nonneg_right
          (mul_nonneg (NNReal.coe_nonneg KH) (NNReal.coe_nonneg KA))
  · change HolderOnWith C α
      (iteratedFDeriv ℝ 0 (fun x ↦ Complex.re ((Q x * H x).trace))) s
    rw [iteratedFDeriv_zero_eq_comp]
    let c := continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℂ (Fin n)) ℝ
    have htraceHolder := qsrc_holderOnWith_realTraceProduct hQ hH hQbound hHbound
    intro x hx y hy
    change edist (c.symm (Complex.re ((Q x * H x).trace)))
      (c.symm (Complex.re ((Q y * H y).trace))) ≤ _
    rw [c.symm.edist_map]
    exact htraceHolder x hx y hy

private theorem quotient_holderBoundOn_zero_congr_generic {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α C : ℝ≥0} {s : Set E} {f g : E → F}
    (hf : HolderBoundOn 0 α C s f) (hfg : EqOn f g s) :
    HolderBoundOn 0 α C s g := by
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    have h := hf.1 0 (by norm_num) x hx
    simpa [norm_iteratedFDeriv_zero, hfg hx] using h
  · rw [iteratedFDeriv_zero_eq_comp]
    let c := continuousMultilinearCurryFin0 ℝ E F
    intro x hx y hy
    have h := hf.2 x hx y hy
    change edist (c.symm (f x)) (c.symm (f y)) ≤
      (C : ℝ≥0∞) * edist x y ^ (α : ℝ) at h
    rw [hfg hx, hfg hy] at h
    exact h

private theorem quotient_holderBoundOn_one_translate {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α C : ℝ≥0} {K S : Set E} {f : E → F} {c : E}
    (hf : HolderBoundOn 1 α C K f)
    (hshift : ∀ x ∈ S, x + c ∈ K) :
    HolderBoundOn 1 α C S (fun x ↦ f (x + c)) := by
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    by_cases hj0 : j = 0
    · subst j
      rw [norm_iteratedFDeriv_zero]
      simpa [norm_iteratedFDeriv_zero] using hf.1 0 (by norm_num) (x + c) (hshift x hx)
    · have hj1 : j = 1 := by omega
      subst j
      rw [iteratedFDeriv_comp_add_right]
      exact hf.1 1 le_rfl (x + c) (hshift x hx)
  · intro x hx y hy
    have hJetx : iteratedFDeriv ℝ 1 (fun z ↦ f (z + c)) x =
        iteratedFDeriv ℝ 1 f (x + c) := iteratedFDeriv_comp_add_right 1 c x
    have hJety : iteratedFDeriv ℝ 1 (fun z ↦ f (z + c)) y =
        iteratedFDeriv ℝ 1 f (y + c) := iteratedFDeriv_comp_add_right 1 c y
    rw [hJetx, hJety]
    have hdist : edist (x + c) (y + c) = edist x y := by
      rw [edist_dist, edist_dist, dist_add_right]
    simpa only [hdist] using hf.2 (x + c) (hshift x hx) (y + c) (hshift y hy)

private theorem quotient_holderBoundOn_differenceQuotient_centered
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {center : E} {r R : ℝ} {α K : ℝ≥0} {f : E → F}
    (hr : 0 < r) (hR : r < R) (hα₀ : 0 < α) (hα₁ : α < 1)
    (hf : ContDiffOn ℝ 1 f (Metric.ball center R))
    (hbound : HolderBoundOn 1 α K (Metric.closedBall center R) f)
    {v : E} {h : ℝ} (hv : ‖v‖ ≤ 1) (hh₀ : 0 < |h|) (hhR : |h| < R - r) :
    HolderBoundOn 0 α K (Metric.closedBall center r)
      (fun x ↦ h⁻¹ • (f (x + h • v) - f x)) := by
  let g : E → F := fun x ↦ f (x + center)
  have htrans : ContDiffOn ℝ 1 (fun x : E ↦ x + center) (Metric.ball (0 : E) R) := by
    fun_prop
  have hmap : ∀ x ∈ Metric.ball (0 : E) R, x + center ∈ Metric.ball center R := by
    intro x hx
    rw [Metric.mem_ball] at hx ⊢
    have hdist : dist (x + center) center = dist x 0 := by
      simpa using (dist_add_right x 0 center)
    simpa [hdist] using hx
  have hg : ContDiffOn ℝ 1 g (Metric.ball (0 : E) R) := by
    exact hf.comp htrans hmap
  have hballmap : ∀ x ∈ Metric.closedBall (0 : E) R,
      x + center ∈ Metric.closedBall center R := by
    intro x hx
    rw [Metric.mem_closedBall] at hx ⊢
    have hdist : dist (x + center) center = dist x 0 := by
      simpa using (dist_add_right x 0 center)
    simpa [hdist] using hx
  have hboundg : HolderBoundOn 1 α K (Metric.closedBall (0 : E) R) g :=
    quotient_holderBoundOn_one_translate hbound hballmap
  have hqg := holderBoundOn_differenceQuotient hr hR hα₀ hα₁ hg hboundg hv hh₀ hhR
  have hshift : ∀ x ∈ Metric.closedBall center r,
      x + (-center) ∈ Metric.closedBall (0 : E) r := by
    intro x hx
    rw [Metric.mem_closedBall] at hx ⊢
    have hdist : dist (x + (-center)) 0 = dist x center := by
      simpa [sub_eq_add_neg] using (dist_add_right x center (-center))
    simpa [hdist] using hx
  have hq := qsrc_holderBoundOn_zero_translate hqg hshift
  have heq : EqOn (fun x ↦ h⁻¹ • (g (x + (-center) + h • v) - g (x + (-center))))
      (fun x ↦ h⁻¹ • (f (x + h • v) - f x)) (Metric.closedBall center r) := by
    intro x hx
    change h⁻¹ • (f ((x + (-center) + h • v) + center) -
      f ((x + (-center)) + center)) = _
    rw [show (x + (-center) + h • v) + center = x + h • v by abel,
      show (x + (-center)) + center = x by abel]
  exact quotient_holderBoundOn_zero_congr_generic hq heq

 private theorem quotientSource_holder0_budget_centered {n : ℕ}
    {α KA H K₁ : ℝ≥0} {center : EuclideanSpace ℂ (Fin n)} {r R S : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1) (hr : 0 < r) (hR : r < R) (hS : R < S)
    {A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    {u : EuclideanSpace ℂ (Fin n) → ℝ}
    (hU : IsOpen (Metric.ball center S))
    (hA : ∀ i j, ContDiffOn ℝ 1 (fun z ↦ A z i j) (Metric.ball center S))
    (hAbound : ∀ i j, HolderBoundOn 1 α KA (Metric.closedBall center S) (fun z ↦ A z i j))
    (hu : ContDiffOn ℝ 2 u (Metric.ball center S))
    (hbase : HolderBoundOn 2 α H (Metric.closedBall center R) u)
    (hLu : ContDiffOn ℝ 1 (complexEllipticOp A u) (Metric.ball center S))
    (hLuBound : HolderBoundOn 1 α K₁ (Metric.closedBall center S) (complexEllipticOp A u))
    {v : EuclideanSpace ℂ (Fin n)} {h : ℝ}
    (hv : ‖v‖ ≤ 1) (hh₀ : 0 < |h|) (hhR : |h| < R - r) :
    HolderBoundOn 0 α
      (K₁ + (n * n : ℕ) * (KA * (4 * H) + (4 * H) * KA))
      (Metric.ball center r)
      (fun x ↦ h⁻¹ • (complexEllipticOp A u (x + h • v) - complexEllipticOp A u x) -
        Complex.re (((h⁻¹ : ℝ) • (A (x + h • v) - A x) *
          complexHessian u (x + h • v)).trace)) := by
  have hrS : r < S := hR.trans hS
  have hstepS : |h| < S - r := by linarith
  have hvstep : ‖h • v‖ ≤ |h| := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg h) hv
  have hshiftR : ∀ x : EuclideanSpace ℂ (Fin n),
      x ∈ Metric.ball center r →
      x + h • v ∈ Metric.closedBall center R := by
    intro x hx
    rw [Metric.mem_closedBall]
    have hxnorm : dist x center < r := Metric.mem_ball.mp hx
    have hnorm : dist (x + h • v) center < R := by
      calc
        dist (x + h • v) center ≤ dist (x + h • v) x + dist x center := dist_triangle _ _ _
        _ = ‖h • v‖ + dist x center := by simp [dist_eq_norm, add_sub_cancel_left]
        _ ≤ |h| + r := add_le_add hvstep hxnorm.le
        _ < R := by linarith
    exact hnorm.le
  have hclosedRballS : Metric.closedBall center R ⊆
      Metric.ball center S := Metric.closedBall_subset_ball hS
  let B : Set (EuclideanSpace ℂ (Fin n)) := Metric.ball center r
  let Q : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun x ↦ h⁻¹ • (A (x + h • v) - A x)
  let G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun x ↦ complexHessian u (x + h • v)
  have hHess := holderBoundOn_complexHessian_entry hU hclosedRballS hu hbase
  have hQbound (i j : Fin n) : HolderBoundOn 0 α KA B (fun x ↦ Q x i j) := by
    have hAij : ContDiffOn ℝ 1 (fun z ↦ A z i j) (Metric.ball center S) := hA i j
    have hAijBound : HolderBoundOn 1 α KA (Metric.closedBall center S)
        (fun z ↦ A z i j) := hAbound i j
    have hq := quotient_holderBoundOn_differenceQuotient_centered (center := center) hr hrS hα₀ hα₁ hAij hAijBound
      hv hh₀ hstepS
    simpa [B, Q, Matrix.sub_apply, Matrix.smul_apply] using
      hq.mono_set Metric.ball_subset_closedBall
  have hQcont (i j : Fin n) : ContDiffOn ℝ 0 (fun x ↦ Q x i j) B := by
    have htrans : ContDiffOn ℝ 1
        (fun x : EuclideanSpace ℂ (Fin n) ↦ x + h • v) B := by fun_prop
    have hshiftA : ContDiffOn ℝ 1 (fun x ↦ A (x + h • v) i j) B := by
      apply (hA i j).comp htrans
      intro x hx
      exact hclosedRballS (hshiftR x (by simpa [B] using hx))
    have hbaseA : ContDiffOn ℝ 1 (fun x ↦ A x i j) B :=
      (hA i j).mono (Metric.ball_subset_ball hrS.le)
    have hdiffA : ContDiffOn ℝ 1
        (fun x ↦ A (x + h • v) i j - A x i j) B := hshiftA.sub hbaseA
    change ContDiffOn ℝ 0
      (fun x ↦ (h⁻¹ : ℝ) • (A (x + h • v) i j - A x i j)) B
    exact (hdiffA.const_smul (h⁻¹ : ℝ)).of_le (by norm_num)
  have hGbound (i j : Fin n) : HolderBoundOn 0 α (4 * H) B (fun x ↦ G x i j) := by
    have hshift := qsrc_holderBoundOn_zero_translate (hHess i j).2
      (S := B) (c := h • v) (fun x hx => by simpa [B] using hshiftR x hx)
    simpa [G, B] using hshift
  have hGcont (i j : Fin n) : ContDiffOn ℝ 0 (fun x ↦ G x i j) B := by
    have htrans : ContDiffOn ℝ 0
        (fun x : EuclideanSpace ℂ (Fin n) ↦ x + h • v) B := by fun_prop
    have hcomp := (hHess i j).1.comp htrans
      (fun x hx => by simpa [B] using hshiftR x hx)
    change ContDiffOn ℝ 0
      ((fun z ↦ complexHessian u z i j) ∘ (fun x ↦ x + h • v)) B
    exact hcomp
  have hQholder (i j : Fin n) : HolderOnWith KA α (fun x ↦ Q x i j) B :=
    qsrc_holderOn_zero (hQbound i j)
  have hGholder (i j : Fin n) : HolderOnWith (4 * H) α
      (fun x ↦ G x i j) B := qsrc_holderOn_zero (hGbound i j)
  have hQnorm (i j : Fin n) (x : EuclideanSpace ℂ (Fin n)) (hx : x ∈ B) :
      ‖Q x i j‖ ≤ KA := by
    have hb := (hQbound i j).1 0 (by norm_num) x hx
    simpa [norm_iteratedFDeriv_zero] using hb
  have hGnorm (i j : Fin n) (x : EuclideanSpace ℂ (Fin n)) (hx : x ∈ B) :
      ‖G x i j‖ ≤ (4 * H : ℝ) := by
    have hb := (hGbound i j).1 0 (by norm_num) x hx
    simpa [norm_iteratedFDeriv_zero] using hb
  have hLuQuot : HolderBoundOn 0 α K₁ B
      (fun x ↦ h⁻¹ • (complexEllipticOp A u (x + h • v) - complexEllipticOp A u x)) := by
    have hq := quotient_holderBoundOn_differenceQuotient_centered (center := center) hr hrS hα₀ hα₁ hLu hLuBound hv hh₀ hstepS
    simpa [B] using hq.mono_set Metric.ball_subset_closedBall
  have htrace' : HolderBoundOn 0 α
      ((n * n : ℕ) * (KA * (4 * H) + (4 * H) * KA)) B
      (fun x ↦ Complex.re ((Q x * G x).trace)) :=
    qsrc_holderBoundOn_zero_realTraceProduct hQbound hGholder hQnorm hGnorm
  have hsource := qsrc_holderBoundOn_zero_sub hLuQuot htrace'
  simpa [B, Q, G] using hsource
private theorem local_base_bound_at {n : ℕ}
    (α : ℝ≥0) (_hα₀ : 0 < α) (hα₁ : α < 1)
    (lam K : ℝ≥0) (_hlam : 0 < lam)
    {U : Set (EuclideanSpace ℂ (Fin n))} {center : EuclideanSpace ℂ (Fin n)}
    {R S : ℝ} (hR : R ≤ 1 / 2) (hS₀ : 0 < S) (_hSR : S < R)
    (hRU : Metric.closedBall center R ⊆ U) (Cbase : ℝ≥0)
    (hCbase : ∀ (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
      (u : EuclideanSpace ℂ (Fin n) → ℝ),
      (∀ i j, ContDiffOn ℝ 0 (fun z ↦ A z i j) (Metric.ball center R)) →
      ContDiffOn ℝ 2 u (Metric.ball center R) →
      IsUniformlyEllipticOn A lam (Metric.ball center R) →
      (∀ i j, HolderBoundOn 0 α K (Metric.ball center R) (fun z ↦ A z i j)) →
      ∀ K₀ K₁ : ℝ≥0, ContDiffOn ℝ 0 (complexEllipticOp A u) (Metric.ball center R) →
        HolderBoundOn 0 α K₁ (Metric.ball center R) (complexEllipticOp A u) →
        (∀ z ∈ Metric.ball center R, |u z| ≤ (K₀ : ℝ)) →
        HolderBoundOn 2 α (Cbase * (K₁ + K₀)) (Metric.ball center S) u)
    {A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    {u : EuclideanSpace ℂ (Fin n) → ℝ}
    (hA : ∀ i j, ContDiffOn ℝ 1 (fun z ↦ A z i j) U)
    (hu : ContDiffOn ℝ 2 u U)
    (hEll : IsUniformlyEllipticOn A lam U)
    (hAHolder : ∀ i j, HolderBoundOn 1 α K U (fun z ↦ A z i j))
    (K₀ K₁ : ℝ≥0)
    (hLu : ContDiffOn ℝ 1 (complexEllipticOp A u) U)
    (hLuHolder : HolderBoundOn 1 α K₁ U (complexEllipticOp A u))
    (huBound : ∀ z ∈ U, |u z| ≤ (K₀ : ℝ)) :
    HolderBoundOn 2 α (Cbase * (K₁ + K₀))
      (Metric.closedBall center (S / 2)) u := by
  let Uloc := Metric.ball center R
  have hUloc : IsOpen Uloc := Metric.isOpen_ball
  have hUlocSub : Uloc ⊆ U := Metric.ball_subset_closedBall.trans hRU
  have hAloc (i j : Fin n) : ContDiffOn ℝ 1 (fun z ↦ A z i j) Uloc :=
    (hA i j).mono hUlocSub
  have hAlocHolder (i j : Fin n) : HolderBoundOn 1 α K (Metric.closedBall center R)
      (fun z ↦ A z i j) := (hAHolder i j).mono_set hRU
  have hdiam : ∀ x ∈ Uloc, ∀ y ∈ Uloc, dist x y ≤ 1 := by
    intro x hx y hy
    have hx' : dist x center < R := Metric.mem_ball.mp hx
    have hy' : dist center y < R := by simpa [dist_comm] using Metric.mem_ball.mp hy
    have hdist : dist x y < 1 := by
      calc
        dist x y ≤ dist x center + dist center y := dist_triangle _ _ _
        _ < R + R := add_lt_add hx' hy'
        _ ≤ 1 := by linarith
    exact hdist.le
  have hA0 (i j : Fin n) : HolderBoundOn 0 α K (Metric.ball center R)
      (fun z ↦ A z i j) := by
    exact CalabiYau.Schauder.holderBoundOn_of_contDiffOn_succ Metric.isOpen_ball
      (convex_ball center R) hdiam (le_of_lt hα₁) (hAloc i j)
      ((hAlocHolder i j).mono_set Metric.ball_subset_closedBall)
  have hLloc : ContDiffOn ℝ 1 (complexEllipticOp A u) Uloc := hLu.mono hUlocSub
  have hLlocHolder : HolderBoundOn 1 α K₁ (Metric.closedBall center R)
      (complexEllipticOp A u) := hLuHolder.mono_set hRU
  have hL0 : HolderBoundOn 0 α K₁ (Metric.ball center R)
      (complexEllipticOp A u) :=
    CalabiYau.Schauder.holderBoundOn_of_contDiffOn_succ Metric.isOpen_ball
      (convex_ball center R) hdiam (le_of_lt hα₁) hLloc
      (hLlocHolder.mono_set Metric.ball_subset_closedBall)
  have huLoc : ContDiffOn ℝ 2 u Uloc := hu.mono hUlocSub
  have hEllLoc : IsUniformlyEllipticOn A lam Uloc := fun z hz => hEll z (hUlocSub hz)
  have hAcont0 : ∀ i j, ContDiffOn ℝ 0 (fun z ↦ A z i j) Uloc := by
    intro i j
    exact (hAloc i j).of_le (by norm_num)
  have hLcont0 : ContDiffOn ℝ 0 (complexEllipticOp A u) Uloc := hLloc.of_le (by norm_num)
  have huBoundLoc : ∀ z ∈ Uloc, |u z| ≤ (K₀ : ℝ) := fun z hz => huBound z (hUlocSub hz)
  have hbase := hCbase A u hAcont0 huLoc hEllLoc hA0 K₀ K₁ hLcont0 hL0 huBoundLoc
  have hsmall : Metric.closedBall center (S / 2) ⊆ Metric.ball center S := by
    exact Metric.closedBall_subset_ball (by linarith)
  exact hbase.mono_set hsmall

private theorem quotient_value_bound_on_convex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} {H : ℝ≥0} {u : E → ℝ}
    (hs_open : IsOpen s) (hs_convex : Convex ℝ s)
    (hu : ContDiffOn ℝ 1 u s)
    (hu_deriv : ∀ z ∈ s, ‖fderiv ℝ u z‖ ≤ (H : ℝ))
    {x v : E} {h : ℝ}
    (hv : ‖v‖ ≤ 1)
    (hxpath : ∀ θ ∈ Set.Icc (0 : ℝ) 1, x + θ • (h • v) ∈ s)
    (hh : h ≠ 0) :
    |(u (x + h • v) - u x) / h| ≤ (H : ℝ) := by
  have hdiff (z : E) (hz : z ∈ s) : DifferentiableAt ℝ u z :=
    (hu.contDiffAt (hs_open.mem_nhds hz)).differentiableAt (by norm_num)
  have hbound (z : E) (hz : z ∈ s) : ‖fderiv ℝ u z‖ ≤ (H : ℝ) :=
    hu_deriv z hz
  have hLip : LipschitzOnWith H u s :=
    hs_convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ) hdiff hbound
  have hx : x ∈ s := by simpa using hxpath 0 (by norm_num)
  have hy : x + h • v ∈ s := by simpa using hxpath 1 (by norm_num)
  have hdist : dist (x + h • v) x = |h| * ‖v‖ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  have hdiff_bound : dist (u (x + h • v)) (u x) ≤ (H : ℝ) * dist (x + h • v) x :=
    (lipschitzOnWith_iff_dist_le_mul.mp hLip) _ hy _ hx
  rw [Real.dist_eq] at hdiff_bound
  rw [hdist] at hdiff_bound
  rw [abs_div]
  have habsh : 0 < |h| := abs_pos.mpr hh
  calc
    |u (x + h • v) - u x| / |h| ≤ ((H : ℝ) * (|h| * ‖v‖)) / |h| :=
      div_le_div_of_nonneg_right hdiff_bound (abs_nonneg h)
    _ = (H : ℝ) * ‖v‖ := by field_simp
    _ ≤ (H : ℝ) := mul_le_of_le_one_right (by exact_mod_cast H.2) hv

private theorem quotient_complexEllipticOp_contDiffOn_zero_of_C2
    {n : ℕ} {A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    {u : EuclideanSpace ℂ (Fin n) → ℝ} {U : Set (EuclideanSpace ℂ (Fin n))}
    (hU : IsOpen U) (hA : ∀ i j, ContDiffOn ℝ 1 (fun z ↦ A z i j) U)
    (hu : ContDiffOn ℝ 2 u U) :
    ContDiffOn ℝ 0 (complexEllipticOp A u) U := by
  have hD1 : ContDiffOn ℝ 1 (fderiv ℝ u) U :=
    hu.fderiv_of_isOpen hU (by norm_num)
  have hD2 : ContDiffOn ℝ 0 (fderiv ℝ (fderiv ℝ u)) U :=
    hD1.fderiv_of_isOpen hU (by norm_num)
  have hD2eval (v w : EuclideanSpace ℂ (Fin n)) :
      ContDiffOn ℝ 0 (fun z ↦ fderiv ℝ (fderiv ℝ u) z v w) U := by
    exact (hD2.clm_apply contDiffOn_const).clm_apply contDiffOn_const
  have hEntry (i j : Fin n) :
      ContDiffOn ℝ 0 (fun z ↦ complexHessian u z i j) U := by
    have hFormula : ContDiffOn ℝ 0 (fun z ↦
        ((fderiv ℝ (fderiv ℝ u) z (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1) : ℂ) +
          fderiv ℝ (fderiv ℝ u) z (Complex.I • EuclideanSpace.single i 1)
            (Complex.I • EuclideanSpace.single j 1) +
          Complex.I * (fderiv ℝ (fderiv ℝ u) z (EuclideanSpace.single i 1)
            (Complex.I • EuclideanSpace.single j 1) -
          fderiv ℝ (fderiv ℝ u) z (Complex.I • EuclideanSpace.single i 1)
            (EuclideanSpace.single j 1))) / 4) U := by
      simp only [← Complex.ofRealCLM_apply]
      fun_prop
    apply hFormula.congr
    intro z hz
    rw [complexHessian_apply
      (((hu z hz).contDiffAt (hU.mem_nhds hz)).of_le (by norm_num)) i j]
  have hAcont (i j : Fin n) : ContinuousOn (fun z ↦ A z i j) U :=
    (hA i j).continuousOn
  have hEntryCont (i j : Fin n) :
      ContinuousOn (fun z ↦ complexHessian u z i j) U := (hEntry i j).continuousOn
  have hterm (i j : Fin n) : ContinuousOn
      (fun z ↦ Complex.reCLM (A z i j * complexHessian u z j i)) U := by
    exact Complex.reCLM.continuous.comp_continuousOn
      ((hAcont i j).mul (hEntryCont j i))
  have hsumj (i : Fin n) : ContinuousOn
      (fun z ↦ ∑ j, Complex.reCLM (A z i j * complexHessian u z j i)) U := by
    apply continuousOn_finsetSum Finset.univ
    intro j hj
    exact hterm i j
  have hSum : ContinuousOn (fun z ↦
      ∑ i, ∑ j, Complex.reCLM (A z i j * complexHessian u z j i)) U := by
    apply continuousOn_finsetSum Finset.univ
    intro i hi
    exact hsumj i
  have hOp : ContinuousOn
      (fun z ↦ Complex.reCLM ((A z * complexHessian u z).trace)) U := by
    apply hSum.congr
    intro z hz
    simp [Matrix.mul_apply, Matrix.trace, Complex.reCLM_apply]
  change ContDiffOn ℝ 0
    (fun z ↦ Complex.reCLM ((A z * complexHessian u z).trace)) U
  exact contDiffOn_zero.mpr hOp

private theorem quotient_realTrace_matrix_smul_eq_div
    {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (h : ℝ) :
    Complex.re (((h⁻¹ : ℝ) • A * B).trace) = Complex.re (A * B).trace / h := by
  rw [smul_mul_assoc, Matrix.trace_smul]
  by_cases hh : h = 0
  · subst h
    simp
  · rw [div_eq_mul_inv]
    simp [Complex.mul_re]
    exact mul_comm _ _

 private theorem quotient_holderBoundOn_zero_congr {n : ℕ}
    {α C : ℝ≥0} {s : Set (EuclideanSpace ℂ (Fin n))}
    {f g : EuclideanSpace ℂ (Fin n) → ℝ}
    (hf : HolderBoundOn 0 α C s f) (hfg : EqOn f g s) :
    HolderBoundOn 0 α C s g := by
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    have h := hf.1 0 le_rfl x hx
    simpa [norm_iteratedFDeriv_zero, hfg hx] using h
  · change HolderOnWith C α (iteratedFDeriv ℝ 0 g) s
    rw [iteratedFDeriv_zero_eq_comp]
    let c := continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℂ (Fin n)) ℝ
    intro x hx y hy
    have h := hf.2 x hx y hy
    change edist (c.symm (f x)) (c.symm (f y)) ≤
      (C : ℝ≥0∞) * edist x y ^ (α : ℝ) at h
    rw [hfg hx, hfg hy] at h
    exact h

private theorem quotient_local_estimate {n : ℕ}
    (α : ℝ≥0) (hα₀ : 0 < α) (hα₁ : α < 1)
    (lam K : ℝ≥0) (hlam : 0 < lam)
    {U : Set (EuclideanSpace ℂ (Fin n))} {center : EuclideanSpace ℂ (Fin n)}
    {R S : ℝ} (hR : R ≤ 1 / 2) (hS₀ : 0 < S) (hSR : S < R)
    (hRU : Metric.closedBall center R ⊆ U)
    (Cbase Corder : ℝ≥0)
    (hCbase : ∀ (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
      (u : EuclideanSpace ℂ (Fin n) → ℝ),
      (∀ i j, ContDiffOn ℝ 0 (fun z ↦ A z i j) (Metric.ball center R)) →
      ContDiffOn ℝ 2 u (Metric.ball center R) →
      IsUniformlyEllipticOn A lam (Metric.ball center R) →
      (∀ i j, HolderBoundOn 0 α K (Metric.ball center R) (fun z ↦ A z i j)) →
      ∀ K₀ K₁ : ℝ≥0, ContDiffOn ℝ 0 (complexEllipticOp A u) (Metric.ball center R) →
        HolderBoundOn 0 α K₁ (Metric.ball center R) (complexEllipticOp A u) →
        (∀ z ∈ Metric.ball center R, |u z| ≤ (K₀ : ℝ)) →
        HolderBoundOn 2 α (Cbase * (K₁ + K₀)) (Metric.ball center S) u)
    {rQ : ℝ} (hrQ : rQ = S / 8)
    (hCorder : ∀ (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
      (q : EuclideanSpace ℂ (Fin n) → ℝ),
      (∀ i j, ContDiffOn ℝ 0 (fun z ↦ A z i j) (Metric.ball center (S / 4))) →
      ContDiffOn ℝ 2 q (Metric.ball center (S / 4)) →
      IsUniformlyEllipticOn A lam (Metric.ball center (S / 4)) →
      (∀ i j, HolderBoundOn 0 α K (Metric.ball center (S / 4)) (fun z ↦ A z i j)) →
      ∀ Kq Ksource : ℝ≥0,
        ContDiffOn ℝ 0 (complexEllipticOp A q) (Metric.ball center (S / 4)) →
        HolderBoundOn 0 α Ksource (Metric.ball center (S / 4)) (complexEllipticOp A q) →
        (∀ z ∈ Metric.ball center (S / 4), |q z| ≤ Kq) →
        HolderBoundOn 2 α (Corder * (Ksource + Kq))
          (Metric.closedBall center rQ) q)
    {A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    {u : EuclideanSpace ℂ (Fin n) → ℝ}
    (hA : ∀ i j, ContDiffOn ℝ 1 (fun z ↦ A z i j) U)
    (hu : ContDiffOn ℝ 2 u U)
    (hEll : IsUniformlyEllipticOn A lam U)
    (hAHolder : ∀ i j, HolderBoundOn 1 α K U (fun z ↦ A z i j))
    (K₀ K₁ : ℝ≥0)
    (hLu : ContDiffOn ℝ 1 (complexEllipticOp A u) U)
    (hLuHolder : HolderBoundOn 1 α K₁ U (complexEllipticOp A u))
    (huBound : ∀ z ∈ U, |u z| ≤ (K₀ : ℝ)) :
    0 < S / 8 ∧
      ∀ (v : EuclideanSpace ℂ (Fin n)) (h : ℝ), ‖v‖ = 1 →
        0 < |h| → |h| < S / 8 →
        HolderBoundOn 2 α
          ((Corder * (1 + Cbase + (n * n : ℕ) *
            (K * (4 * Cbase) + (4 * Cbase) * K))) * (K₁ + K₀))
          (Metric.closedBall center (S / 8))
          (fun z ↦ (u (z + h • v) - u z) / h) := by
  have hbase := local_base_bound_at α hα₀ hα₁ lam K hlam
    hR hS₀ hSR hRU Cbase hCbase hA hu hEll hAHolder K₀ K₁ hLu hLuHolder huBound
  let rb : ℝ := S / 2
  let rq : ℝ := S / 4
  let rV : ℝ := S / 8
  let scale : ℝ≥0 := K₁ + K₀
  let H : ℝ≥0 := Cbase * scale
  let D : ℝ≥0 := (n * n : ℕ) * (K * (4 * Cbase) + (4 * Cbase) * K)
  have hrb_pos : 0 < rb := by dsimp [rb]; linarith
  have hrq_pos : 0 < rq := by dsimp [rq]; linarith
  have hrbR : rb < R := by dsimp [rb]; linarith
  have hrqrb : rq < rb := by dsimp [rq, rb]; linarith
  have hhalfU : Metric.closedBall center rb ⊆ U :=
    (Metric.closedBall_subset_closedBall (le_of_lt hrbR)).trans hRU
  have hballRU : Metric.ball center R ⊆ U :=
    (show Metric.ball center R ⊆ Metric.closedBall center R from Metric.ball_subset_closedBall).trans hRU
  have hsmallHalf : Metric.closedBall center rq ⊆ Metric.closedBall center rb :=
    Metric.closedBall_subset_closedBall hrqrb.le
  have houterA (i j : Fin n) :
      ContDiffOn ℝ 1 (fun z ↦ A z i j) (Metric.ball center R) :=
    (hA i j).mono hballRU
  have houterAH (i j : Fin n) :
      HolderBoundOn 1 α K (Metric.closedBall center R) (fun z ↦ A z i j) :=
    (hAHolder i j).mono_set hRU
  have houterLu : ContDiffOn ℝ 1 (complexEllipticOp A u) (Metric.ball center R) :=
    hLu.mono hballRU
  have houterLuH : HolderBoundOn 1 α K₁ (Metric.closedBall center R)
      (complexEllipticOp A u) := hLuHolder.mono_set hRU
  have houterU : ContDiffOn ℝ 2 u (Metric.ball center R) :=
    hu.mono hballRU
  have hAloc (i j : Fin n) : ContDiffOn ℝ 1 (fun z ↦ A z i j) (Metric.ball center rq) :=
    (hA i j).mono (Metric.ball_subset_closedBall.trans (hsmallHalf.trans hhalfU))
  have hAlocHolder (i j : Fin n) :
      HolderBoundOn 1 α K (Metric.closedBall center rq) (fun z ↦ A z i j) :=
    (hAHolder i j).mono_set (hsmallHalf.trans hhalfU)
  have hdiam : ∀ x ∈ Metric.ball center rq, ∀ y ∈ Metric.ball center rq,
      dist x y ≤ 1 := by
    intro x hx y hy
    have hx' : dist x center < rq := Metric.mem_ball.mp hx
    have hy' : dist center y < rq := by simpa [dist_comm] using Metric.mem_ball.mp hy
    have hdist : dist x y < 1 := by
      calc
        dist x y ≤ dist x center + dist center y := dist_triangle _ _ _
        _ < rq + rq := add_lt_add hx' hy'
        _ ≤ 1 := by dsimp [rq]; linarith
    exact hdist.le
  have hA0 (i j : Fin n) : HolderBoundOn 0 α K (Metric.ball center rq)
      (fun z ↦ A z i j) := by
    exact CalabiYau.Schauder.holderBoundOn_of_contDiffOn_succ Metric.isOpen_ball
      (convex_ball center rq) hdiam (le_of_lt hα₁) (hAloc i j)
      ((hAlocHolder i j).mono_set Metric.ball_subset_closedBall)
  have hAcont0 (i j : Fin n) : ContDiffOn ℝ 0 (fun z ↦ A z i j)
      (Metric.ball center rq) := (hAloc i j).of_le (by norm_num)
  have hUq : IsOpen (Metric.ball center rq) := Metric.isOpen_ball
  have hEllq : IsUniformlyEllipticOn A lam (Metric.ball center rq) :=
    fun z hz => hEll z ((Metric.ball_subset_closedBall.trans (hsmallHalf.trans hhalfU)) hz)
  have hsmall : ∀ (v : EuclideanSpace ℂ (Fin n)) (h : ℝ), ‖v‖ = 1 →
      |h| < S / 8 → ∀ x ∈ Metric.ball center rq, x + h • v ∈ Metric.ball center rb := by
    intro v h hv hh x hx
    have hx' : dist x center < rq := Metric.mem_ball.mp hx
    have hstep : ‖h • v‖ = |h| := by rw [norm_smul, hv, mul_one, Real.norm_eq_abs]
    have hstep' : ‖h • v‖ < S / 8 := by rw [hstep]; exact hh
    rw [Metric.mem_ball]
    calc
      dist (x + h • v) center ≤ dist (x + h • v) x + dist x center := dist_triangle _ _ _
      _ = ‖h • v‖ + dist x center := by simp [dist_eq_norm, add_sub_cancel_left]
      _ < S / 8 + S / 4 := add_lt_add hstep' hx'
      _ < rb := by dsimp [rb]; linarith
  have hShiftR (v : EuclideanSpace ℂ (Fin n)) (h : ℝ) (hv : ‖v‖ = 1)
      (hh : |h| < S / 8) :
      ∀ x ∈ Metric.ball center rq, x + h • v ∈ Metric.ball center R := by
    intro x hx
    exact (Metric.ball_subset_ball hrbR.le) (hsmall v h hv hh x hx)
  have hqCont (v : EuclideanSpace ℂ (Fin n)) (h : ℝ)
      (hv : ‖v‖ = 1) (hh : |h| < S / 8) :
      ContDiffOn ℝ 2 (fun z ↦ (u (z + h • v) - u z) / h) (Metric.ball center rq) := by
    have ht : ContDiffOn ℝ 2 (fun z : EuclideanSpace ℂ (Fin n) ↦ z + h • v)
        (Metric.ball center rq) := by fun_prop
    have hsmooth := houterU.comp ht (hShiftR v h hv hh)
    have hbaseU := houterU.mono (Metric.ball_subset_ball (hrqrb.trans hrbR).le)
    exact (hsmooth.sub hbaseU).div_const h
  have hqBound (v : EuclideanSpace ℂ (Fin n)) (h : ℝ)
      (hv : ‖v‖ = 1) (hh₀ : 0 < |h|) (hh : |h| < S / 8) :
      ∀ x ∈ Metric.ball center rq,
        |(u (x + h • v) - u x) / h| ≤ (H : ℝ) := by
    intro x hx
    have hderiv (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ Metric.ball center rb) :
        ‖fderiv ℝ u z‖ ≤ (H : ℝ) := by
      have h := hbase.1 1 (by norm_num) z (Metric.ball_subset_closedBall hz)
      simpa only [norm_iteratedFDeriv_one] using h
    have hpath : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
        x + θ • (h • v) ∈ Metric.ball center rb := by
      intro θ hθ
      have hx' : dist x center < rq := Metric.mem_ball.mp hx
      have ht : |θ| ≤ 1 := abs_le.mpr ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
      have hmove : ‖θ • (h • v)‖ ≤ |h| := by
        rw [norm_smul, Real.norm_eq_abs, norm_smul, Real.norm_eq_abs, hv]
        calc
          |θ| * (|h| * 1) ≤ 1 * (|h| * 1) :=
            mul_le_mul_of_nonneg_right ht (by positivity)
          _ = |h| := by ring
      rw [Metric.mem_ball]
      calc
        dist (x + θ • (h • v)) center ≤ dist (x + θ • (h • v)) x + dist x center :=
          dist_triangle _ _ _
        _ = ‖θ • (h • v)‖ + dist x center := by simp [dist_eq_norm, add_sub_cancel_left]
        _ < S / 8 + rq := add_lt_add (lt_of_le_of_lt hmove hh) hx'
        _ < rb := by dsimp [rq, rb]; linarith
    have hu1rb : ContDiffOn ℝ 1 u (Metric.ball center rb) :=
      (houterU.mono (Metric.ball_subset_ball hrbR.le)).of_le (by norm_num)
    have hne : h ≠ 0 := by
      intro hz
      subst h
      simp at hh₀
    exact quotient_value_bound_on_convex Metric.isOpen_ball (convex_ball center rb)
      hu1rb hderiv (le_of_eq hv) hpath (x := x) (v := v) (h := h) hne
  let Vq := Metric.closedBall center rV
  let Kq : ℝ≥0 := H
  let Ksource : ℝ≥0 := K₁ + (n * n : ℕ) * (K * (4 * H) + (4 * H) * K)
  have hK₁scale : K₁ ≤ scale := by
    dsimp [scale]
    exact le_add_of_nonneg_right (NNReal.coe_nonneg K₀)
  have hcoeff : Kq + Ksource ≤ (1 + Cbase + D) * scale := by
    calc
      Kq + Ksource = (Cbase + D) * scale + K₁ := by
        dsimp [Kq, Ksource, H, D, scale]
        ring
      _ ≤ (Cbase + D) * scale + scale := by
        gcongr
      _ = (1 + Cbase + D) * scale := by ring
  let Cq : ℝ≥0 := Corder * (1 + Cbase + D)
  have hδ : 0 < S / 8 := by positivity
  refine ⟨hδ, ?_⟩
  intro v h hv hh₀ hh
  let q : EuclideanSpace ℂ (Fin n) → ℝ := fun z ↦ (u (z + h • v) - u z) / h
  have hqC2 : ContDiffOn ℝ 2 q (Metric.ball center rq) := by
    simpa [q] using hqCont v h hv hh
  have hqBound' : ∀ z ∈ Metric.ball center rq, |q z| ≤ H := by
    intro z hz
    simpa [q] using hqBound v h hv hh₀ hh z hz
  have hsource := quotientSource_holder0_budget_centered (center := center)
    hα₀ hα₁ hrq_pos hrqrb hrbR Metric.isOpen_ball houterA houterAH houterU hbase
    houterLu houterLuH hv.le hh₀ (by dsimp [rq, rb]; linarith [hh])
  have hrqR : rq < R := hrqrb.trans hrbR
  have hqOpHolder : HolderBoundOn 0 α Ksource
      (Metric.ball center rq) (complexEllipticOp A q) := by
    apply quotient_holderBoundOn_zero_congr hsource
    intro x hx
    have hne : h ≠ 0 := by
      intro hz
      subst h
      simp at hh₀
    have hxR : x ∈ Metric.ball center R :=
      Metric.ball_subset_ball hrqR.le hx
    have hshiftR : x + h • v ∈ Metric.ball center R := hShiftR v h hv hh x hx
    have hu₀ : ContDiffAt ℝ 2 u x :=
      houterU.contDiffAt (Metric.isOpen_ball.mem_nhds hxR)
    have hu₁ : ContDiffAt ℝ 2 u (x + h • v) :=
      houterU.contDiffAt (Metric.isOpen_ball.mem_nhds hshiftR)
    have hidentity := quotient_complexEllipticOp_differenceQuotient A u v h x hne hu₀ hu₁
    have hfirst : h⁻¹ • (complexEllipticOp A u (x + h • v) - complexEllipticOp A u x) =
        (complexEllipticOp A u (x + h • v) - complexEllipticOp A u x) / h := by
      simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
    have htrace := quotient_realTrace_matrix_smul_eq_div
      (A (x + h • v) - A x) (complexHessian u (x + h • v)) h
    calc
      h⁻¹ • (complexEllipticOp A u (x + h • v) - complexEllipticOp A u x) -
          Complex.re (((h⁻¹ : ℝ) • (A (x + h • v) - A x) *
            complexHessian u (x + h • v)).trace) =
          (complexEllipticOp A u (x + h • v) - complexEllipticOp A u x) / h -
            Complex.re ((A (x + h • v) - A x) * complexHessian u (x + h • v)).trace / h := by
        rw [hfirst, htrace]
      _ = complexEllipticOp A q x := by simpa [q] using hidentity.symm
  have hLuQCont : ContDiffOn ℝ 0 (complexEllipticOp A q) (Metric.ball center rq) := by
    apply quotient_complexEllipticOp_contDiffOn_zero_of_C2 hUq
    · intro i j
      exact (hA i j).mono (Metric.ball_subset_closedBall.trans (hsmallHalf.trans hhalfU))
    · exact hqC2
  have hAOn (i j : Fin n) : HolderBoundOn 0 α K (Metric.ball center rq)
      (fun z ↦ A z i j) := hA0 i j
  have hLuQ : HolderBoundOn 0 α Ksource (Metric.ball center rq)
      (complexEllipticOp A q) := by simpa [Ksource] using hqOpHolder
  have hq_bound : ∀ z ∈ Metric.ball center rq, |q z| ≤ Kq := by
    intro z hz
    simpa [Kq] using hqBound' z hz
  have hbound : HolderBoundOn 2 α
      (Corder * (Kq + Ksource)) Vq q := by
    simpa [Vq, rV, hrQ, Kq, Ksource, add_comm] using
      hCorder A q hAcont0 hqC2 hEllq hAOn Kq Ksource hLuQCont hLuQ hq_bound
  have hbound' : HolderBoundOn 2 α (Cq * scale) Vq q := by
    apply hbound.mono_const
    calc
      Corder * (Kq + Ksource) ≤ Corder * ((1 + Cbase + D) * scale) :=
        mul_le_mul_of_nonneg_left hcoeff (NNReal.coe_nonneg Corder)
      _ = Cq * scale := by dsimp [Cq]; ring
  simpa [Vq, Cq, scale, rV, hrQ, q, D] using hbound'

private theorem quotient_finite_ball_cover {n : ℕ}
    {K U : Set (EuclideanSpace ℂ (Fin n))}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (R : {x // x ∈ K} → ℝ),
      (∀ p, 0 < R p ∧ R p ≤ 1 / 2 ∧
        Metric.closedBall (p : EuclideanSpace ℂ (Fin n)) (R p) ⊆ U) ∧
      ∃ s : Finset {x // x ∈ K},
        K ⊆ ⋃ p ∈ s, Metric.ball (p : EuclideanSpace ℂ (Fin n)) (R p / 16) := by
  classical
  let radius (p : {x // x ∈ K}) : ℝ := Classical.choose
    (Metric.isOpen_iff.mp hU p (hKU p.property))
  have hradius (p : {x // x ∈ K}) : 0 < radius p ∧
      Metric.ball (p : EuclideanSpace ℂ (Fin n)) (radius p) ⊆ U :=
    Classical.choose_spec (Metric.isOpen_iff.mp hU p (hKU p.property))
  let R : {x // x ∈ K} → ℝ := fun p ↦ min (radius p / 2) (1 / 2)
  have hRpos (p : {x // x ∈ K}) : 0 < R p := by
    dsimp [R]
    apply lt_min
    · exact half_pos (hradius p).1
    · norm_num
  have hRle (p : {x // x ∈ K}) : R p ≤ 1 / 2 := by
    exact min_le_right _ _
  have hRlt (p : {x // x ∈ K}) : R p < radius p := by
    calc
      R p ≤ radius p / 2 := min_le_left _ _
      _ < radius p := half_lt_self (hradius p).1
  have hclosed (p : {x // x ∈ K}) :
      Metric.closedBall (p : EuclideanSpace ℂ (Fin n)) (R p) ⊆ U :=
    (Metric.closedBall_subset_ball (hRlt p)).trans (hradius p).2
  let V (p : {x // x ∈ K}) :=
    Metric.ball (p : EuclideanSpace ℂ (Fin n)) (R p / 16)
  have hopen (p : {x // x ∈ K}) : IsOpen (V p) := Metric.isOpen_ball
  have hcover : K ⊆ ⋃ p : {x // x ∈ K}, V p := by
    intro x hx
    let p : {x // x ∈ K} := ⟨x, hx⟩
    refine Set.mem_iUnion.mpr ⟨p, ?_⟩
    exact Metric.mem_ball_self (div_pos (hRpos p) (by norm_num))
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover V hopen hcover
  refine ⟨R, ?_, s, ?_⟩
  · intro p
    exact ⟨hRpos p, hRle p, hclosed p⟩
  · intro x hx
    have hx' := hs hx
    rcases Set.mem_iUnion₂.mp hx' with ⟨p, hp, hxp⟩
    exact Set.mem_iUnion₂.mpr ⟨p, hp, hxp⟩

private theorem quotient_holderBoundOn_of_finiteCover_scaled
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ι : Type*} [Fintype ι] {k : ℕ} {α D B : ℝ≥0}
    {K : Set E} {U : ι → Set E}
    (hK : IsCompact K)
    (hUopen : ∀ i, IsOpen (U i))
    (hcover : K ⊆ ⋃ i : ι, U i) :
    ∃ C : ℝ≥0, ∀ S : ℝ≥0, ∀ f : E → F,
      (∀ i, HolderBoundOn k α (D * S) (U i) f) →
      (∀ x ∈ K, ‖iteratedFDeriv ℝ k f x‖ ≤ (B * S : ℝ)) →
      HolderBoundOn k α (C * S) K f := by
  obtain ⟨V, hV, hLebesgue⟩ := lebesgue_number_lemma hK hUopen hcover
  obtain ⟨epsilon, hepsilon, hepsilonV⟩ := Metric.mem_uniformity_dist.mp hV
  let delta : ℝ≥0 := Real.toNNReal (epsilon / 2)
  have hdeltaPos : 0 < delta := Real.toNNReal_pos.mpr (by linarith)
  have hdeltaEq : (delta : ℝ) = epsilon / 2 := by
    simp [delta, Real.coe_toNNReal (epsilon / 2) (by positivity)]
  have hnear : ∀ x ∈ K, ∀ y ∈ K, nndist x y ≤ delta →
      ∃ i, x ∈ U i ∧ y ∈ U i := by
    intro x hx y hy hxy
    obtain ⟨i, hball⟩ := hLebesgue x hx
    have hdist : dist x y ≤ (delta : ℝ) := by exact_mod_cast hxy
    have hdistlt : dist x y < epsilon := by rw [hdeltaEq] at hdist; linarith
    have hyV : y ∈ UniformSpace.ball x V := by
      change (x, y) ∈ V
      exact hepsilonV hdistlt
    exact ⟨i, hball (UniformSpace.mem_ball_self x hV), hball hyV⟩
  let Cfar : ℝ≥0 := (2 * B) / delta ^ (α : ℝ)
  let C : ℝ≥0 := max D Cfar
  refine ⟨C, ?_⟩
  intro S f hlocal hglobal
  have hfarCoeff (x y : E) (hxy : delta ≤ nndist x y) :
      2 * (B * S) ≤ (Cfar * S) * nndist x y ^ (α : ℝ) := by
    have hpowpos : 0 < delta ^ (α : ℝ) := NNReal.rpow_pos hdeltaPos
    have hpowle : delta ^ (α : ℝ) ≤ nndist x y ^ (α : ℝ) :=
      NNReal.rpow_le_rpow hxy (NNReal.coe_nonneg α)
    dsimp [Cfar]
    calc
      2 * (B * S) = ((2 * B) / delta ^ (α : ℝ)) * delta ^ (α : ℝ) * S := by field_simp
      _ ≤ ((2 * B) / delta ^ (α : ℝ)) * nndist x y ^ (α : ℝ) * S := by gcongr
      _ = ((2 * B) / delta ^ (α : ℝ)) * S * nndist x y ^ (α : ℝ) := by ring
  have hfarENN (x y : E) (hxy : delta ≤ nndist x y) :
      (↑(2 * (B * S)) : ENNReal) ≤
        (↑(Cfar * S) : ENNReal) * edist x y ^ (α : ℝ) := by
    rw [edist_nndist, ← ENNReal.coe_rpow_of_nonneg (nndist x y) (NNReal.coe_nonneg α),
      ← ENNReal.coe_mul]
    exact_mod_cast hfarCoeff x y hxy
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hcover hx)
    exact ((hlocal i).1 j hj x hxi).trans (by
      exact_mod_cast (mul_le_mul_of_nonneg_right (le_max_left D Cfar) (NNReal.coe_nonneg S)))
  · intro x hx y hy
    by_cases hxy : nndist x y ≤ delta
    · obtain ⟨i, hxi, hyi⟩ := hnear x hx y hy hxy
      have hlocal' := (hlocal i).mono_const
        (mul_le_mul_of_nonneg_right (le_max_left D Cfar) (NNReal.coe_nonneg S))
      exact hlocal'.2 x hxi y hyi
    · have htopx : ‖iteratedFDeriv ℝ k f x‖ ≤ (B * S : ℝ) := hglobal x hx
      have htopy : ‖iteratedFDeriv ℝ k f y‖ ≤ (B * S : ℝ) := hglobal y hy
      calc
        edist (iteratedFDeriv ℝ k f x) (iteratedFDeriv ℝ k f y) =
            ENNReal.ofReal (dist (iteratedFDeriv ℝ k f x) (iteratedFDeriv ℝ k f y)) :=
          edist_dist _ _
        _ ≤ ENNReal.ofReal (‖iteratedFDeriv ℝ k f x‖ + ‖iteratedFDeriv ℝ k f y‖) :=
          ENNReal.ofReal_le_ofReal (dist_le_norm_add_norm _ _)
        _ ≤ ENNReal.ofReal (2 * (B * S : ℝ)) := ENNReal.ofReal_le_ofReal (by linarith)
        _ = (↑(2 * (B * S)) : ENNReal) := by rw [ENNReal.ofReal_mul (by positivity)]; simp
        _ ≤ (↑(Cfar * S) : ENNReal) * edist x y ^ (α : ℝ) := hfarENN x y (le_of_not_ge hxy)
        _ ≤ (↑(C * S) : ENNReal) * edist x y ^ (α : ℝ) := by
          exact mul_le_mul_of_nonneg_right
            (ENNReal.coe_le_coe.mpr
              (mul_le_mul_of_nonneg_right (le_max_right D Cfar) (NNReal.coe_nonneg S)))
            (by positivity)

private theorem quotient_estimates_on_compact {n : ℕ}
    (hOrder : InteriorSchauderOrder n 0)
    (α : ℝ≥0) (hα₀ : 0 < α) (hα₁ : α < 1)
    (lam K : ℝ≥0) (hlam : 0 < lam)
    {U Kset : Set (EuclideanSpace ℂ (Fin n))}
    (hU : IsOpen U) (hK : IsCompact Kset) (hKU : Kset ⊆ U) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
        (u : EuclideanSpace ℂ (Fin n) → ℝ),
        (∀ i j, ContDiffOn ℝ 1 (fun z ↦ A z i j) U) → ContDiffOn ℝ 2 u U →
        IsUniformlyEllipticOn A lam U →
        (∀ i j, HolderBoundOn 1 α K U (fun z ↦ A z i j)) →
        ∀ K₀ K₁ : ℝ≥0, ContDiffOn ℝ 1 (complexEllipticOp A u) U →
          HolderBoundOn 1 α K₁ U (complexEllipticOp A u) →
          (∀ z ∈ U, |u z| ≤ K₀) →
          HolderBoundOn 2 α (C * (K₁ + K₀)) Kset u ∧
            ∀ (v : EuclideanSpace ℂ (Fin n)) (h : ℝ), ‖v‖ = 1 →
              0 < |h| → |h| < δ →
              HolderBoundOn 2 α (C * (K₁ + K₀)) Kset
                (fun z ↦ (u (z + h • v) - u z) / h) := by
  classical
  by_cases hKempty : Kset = ∅
  · refine ⟨0, 1, by norm_num, ?_⟩
    intro A u hA hu hEll hAHolder K₀ K₁ hLu hLuHolder huBound
    refine ⟨?_, ?_⟩
    · simp [HolderBoundOn, hKempty]
    · intro v h hv hh₀ hh
      simp [HolderBoundOn, hKempty]
  · have hKne : Kset.Nonempty := Set.nonempty_iff_ne_empty.mpr hKempty
    obtain ⟨R, hRdata, s, hcover⟩ := quotient_finite_ball_cover hK hU hKU
    have hsne : s.Nonempty := by
      obtain ⟨x, hx⟩ := hKne
      obtain ⟨p, hp, _⟩ := Set.mem_iUnion₂.mp (hcover hx)
      exact ⟨p, hp⟩
    have hbaseOrder (p : {x // x ∈ Kset}) :
        ∃ Cbase : ℝ≥0, ∀ (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
          (u : EuclideanSpace ℂ (Fin n) → ℝ),
          (∀ i j, ContDiffOn ℝ 0 (fun z ↦ A z i j) (Metric.ball (p : EuclideanSpace ℂ (Fin n)) (R p))) →
          ContDiffOn ℝ 2 u (Metric.ball (p : EuclideanSpace ℂ (Fin n)) (R p)) →
          IsUniformlyEllipticOn A lam (Metric.ball (p : EuclideanSpace ℂ (Fin n)) (R p)) →
          (∀ i j, HolderBoundOn 0 α K (Metric.ball (p : EuclideanSpace ℂ (Fin n)) (R p))
            (fun z ↦ A z i j)) →
          ∀ K₀ K₁ : ℝ≥0,
            ContDiffOn ℝ 0 (complexEllipticOp A u)
              (Metric.ball (p : EuclideanSpace ℂ (Fin n)) (R p)) →
            HolderBoundOn 0 α K₁ (Metric.ball (p : EuclideanSpace ℂ (Fin n)) (R p))
              (complexEllipticOp A u) →
            (∀ z ∈ Metric.ball (p : EuclideanSpace ℂ (Fin n)) (R p), |u z| ≤ (K₀ : ℝ)) →
            HolderBoundOn 2 α (Cbase * (K₁ + K₀))
              (Metric.ball (p : EuclideanSpace ℂ (Fin n)) (R p / 2)) u := by
      rcases hRdata p with ⟨hRp, hRhalf, hRpU⟩
      let Uloc := Metric.ball (p : EuclideanSpace ℂ (Fin n)) (R p)
      let Vloc := Metric.ball (p : EuclideanSpace ℂ (Fin n)) (R p / 2)
      have hUloc : IsOpen Uloc := Metric.isOpen_ball
      have hVcompact : IsCompact (closure Vloc) := by
        apply (isCompact_closedBall (p : EuclideanSpace ℂ (Fin n)) (R p / 2)).of_isClosed_subset
          isClosed_closure
        exact Metric.closure_ball_subset_closedBall
      have hVsub : closure Vloc ⊆ Uloc := by
        exact Metric.closure_ball_subset_closedBall.trans
          (Metric.closedBall_subset_ball (by linarith [hRp]))
      obtain ⟨Cbase, hCbase⟩ := hOrder α hα₀ hα₁ lam K hlam Uloc Vloc
        hUloc hVcompact hVsub
      refine ⟨Cbase, ?_⟩
      intro A u hA0 hu hEll hA0Holder K₀ K₁ hLu0 hLu0Holder huBound0
      exact (hCbase A u hA0 hu hEll hA0Holder K₀ K₁ hLu0 hLu0Holder huBound0).2
    choose Cbase hCbase using hbaseOrder
    have hquotOrder (p : {x // x ∈ Kset}) :
        ∃ Corder : ℝ≥0, ∀ (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
          (q : EuclideanSpace ℂ (Fin n) → ℝ),
          (∀ i j, ContDiffOn ℝ 0 (fun z ↦ A z i j)
            (Metric.ball (p : EuclideanSpace ℂ (Fin n)) (R p / 8))) →
          ContDiffOn ℝ 2 q (Metric.ball (p : EuclideanSpace ℂ (Fin n)) (R p / 8)) →
          IsUniformlyEllipticOn A lam
            (Metric.ball (p : EuclideanSpace ℂ (Fin n)) (R p / 8)) →
          (∀ i j, HolderBoundOn 0 α K
            (Metric.ball (p : EuclideanSpace ℂ (Fin n)) (R p / 8)) (fun z ↦ A z i j)) →
          ∀ Kq Ksource : ℝ≥0,
            ContDiffOn ℝ 0 (complexEllipticOp A q)
              (Metric.ball (p : EuclideanSpace ℂ (Fin n)) (R p / 8)) →
            HolderBoundOn 0 α Ksource
              (Metric.ball (p : EuclideanSpace ℂ (Fin n)) (R p / 8)) (complexEllipticOp A q) →
            (∀ z ∈ Metric.ball (p : EuclideanSpace ℂ (Fin n)) (R p / 8), |q z| ≤ Kq) →
            HolderBoundOn 2 α (Corder * (Ksource + Kq))
              (Metric.closedBall (p : EuclideanSpace ℂ (Fin n)) (R p / 16)) q := by
      rcases hRdata p with ⟨hRp, hRhalf, hRpU⟩
      let Uq := Metric.ball (p : EuclideanSpace ℂ (Fin n)) (R p / 8)
      let Vq := Metric.closedBall (p : EuclideanSpace ℂ (Fin n)) (R p / 16)
      have hUq : IsOpen Uq := Metric.isOpen_ball
      have hVqCompact : IsCompact (closure Vq) := by
        rw [closure_eq_iff_isClosed.mpr isClosed_closedBall]
        exact isCompact_closedBall (p : EuclideanSpace ℂ (Fin n)) (R p / 16)
      have hVqSub : closure Vq ⊆ Uq := by
        rw [closure_eq_iff_isClosed.mpr isClosed_closedBall]
        exact Metric.closedBall_subset_ball (by linarith [hRp])
      obtain ⟨Corder, hCorderFull⟩ := hOrder α hα₀ hα₁ lam K hlam Uq Vq hUq hVqCompact hVqSub
      refine ⟨Corder, ?_⟩
      intro A q hA0 hqC2 hEllq hAHolder0 Kq Ksource hLq0 hLqHolder hqBound
      exact (hCorderFull A q hA0 hqC2 hEllq hAHolder0 Kq Ksource
        hLq0 hLqHolder hqBound).2
    choose Corder hCorder using hquotOrder
    let DquotAt (p : {x // x ∈ Kset}) : ℝ≥0 :=
      (n * n : ℕ) * (K * (4 * Cbase p) + (4 * Cbase p) * K)
    let Cquot (p : {x // x ∈ Kset}) : ℝ≥0 :=
      Corder p * (1 + Cbase p + DquotAt p)
    have hδp (p : {x // x ∈ Kset}) : 0 < R p / 16 := by
      have h := (hRdata p).1
      positivity
    let ι := {p : {x // x ∈ Kset} // p ∈ s}
    let : Fintype ι := Fintype.ofFinite ι
    let Uloc : ι → Set (EuclideanSpace ℂ (Fin n)) := fun i ↦
      Metric.ball (i.val : EuclideanSpace ℂ (Fin n)) (R i.val / 16)
    have hopenLoc (i : ι) : IsOpen (Uloc i) := Metric.isOpen_ball
    have hcoverLoc : Kset ⊆ ⋃ i : ι, Uloc i := by
      intro x hx
      obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp (hcover hx)
      exact Set.mem_iUnion.mpr ⟨⟨p, hp⟩, hxp⟩
    let Dbase : ℝ≥0 := ∑ p ∈ s, Cbase p
    let Dquot : ℝ≥0 := ∑ p ∈ s, Cquot p
    have hbaseC (i : ι) : Cbase i.val ≤ Dbase := by
      dsimp [Dbase]
      exact Finset.single_le_sum (fun p hp => bot_le) i.property
    have hquotC (i : ι) : Cquot i.val ≤ Dquot := by
      dsimp [Dquot]
      exact Finset.single_le_sum (fun p hp => bot_le) i.property
    have hradBase (i : ι) :
        Uloc i ⊆ Metric.closedBall (i.val : EuclideanSpace ℂ (Fin n)) (R i.val / 4) := by
      exact Metric.ball_subset_closedBall.trans
        (Metric.closedBall_subset_closedBall (by
          have h := (hRdata i.val).1
          linarith))
    obtain ⟨CbaseGlobal, hbaseGlobalForall⟩ :=
      quotient_holderBoundOn_of_finiteCover_scaled
        (E := EuclideanSpace ℂ (Fin n)) (F := ℝ) (k := 2) (α := α)
        (D := Dbase) (B := Dbase) hK hopenLoc hcoverLoc
    obtain ⟨CquotGlobal, hquotGlobalForall⟩ :=
      quotient_holderBoundOn_of_finiteCover_scaled
        (E := EuclideanSpace ℂ (Fin n)) (F := ℝ) (k := 2) (α := α)
        (D := Dquot) (B := Dquot) hK hopenLoc hcoverLoc
    let δlocal : {x // x ∈ Kset} → ℝ := fun p ↦ R p / 16
    have hδlocal (p : {x // x ∈ Kset}) : 0 < δlocal p :=
      div_pos (hRdata p).1 (by norm_num)
    let delta : ℝ := s.inf' hsne δlocal
    have hdelta : 0 < delta := by
      dsimp [delta]
      rw [Finset.lt_inf'_iff]
      intro p hp
      exact hδlocal p
    have hdeltaLe (i : ι) : delta ≤ δlocal i.val := by
      have hproof : hsne = ⟨i.val, i.property⟩ := Subsingleton.elim _ _
      have heq : s.inf' hsne δlocal = s.inf' ⟨i.val, i.property⟩ δlocal :=
        congrArg (fun hs : s.Nonempty => s.inf' hs δlocal) hproof
      change s.inf' hsne δlocal ≤ δlocal i.val
      rw [heq]
      exact Finset.inf'_le (f := δlocal) i.property
    let C : ℝ≥0 := max CbaseGlobal CquotGlobal
    refine ⟨C, delta, hdelta, ?_⟩
    intro A u hA hu hEll hAHolder K₀ K₁ hLu hLuHolder huBound
    let scale : ℝ≥0 := K₁ + K₀
    have hbaseP (p : {x // x ∈ Kset}) :
        HolderBoundOn 2 α (Cbase p * scale)
          (Metric.closedBall (p : EuclideanSpace ℂ (Fin n)) (R p / 4)) u := by
      rcases hRdata p with ⟨hRp, hRhalf, hRpU⟩
      have hbase := local_base_bound_at α hα₀ hα₁ lam K hlam
        hRhalf (by positivity : 0 < R p / 2) (by linarith [hRp]) hRpU
        (Cbase p) (hCbase p) hA hu hEll hAHolder K₀ K₁ hLu hLuHolder huBound
      have hrad : (R p / 2) / 2 = R p / 4 := by ring
      simpa [scale, hrad] using hbase
    have hbaseLoc (i : ι) : HolderBoundOn 2 α (Dbase * scale) (Uloc i) u := by
      have hlocal := (hbaseP i.val).mono_set (hradBase i)
      exact hlocal.mono_const
        (mul_le_mul_of_nonneg_right (hbaseC i) (NNReal.coe_nonneg scale))
    have hbaseGlobalJet : ∀ x ∈ Kset,
        ‖iteratedFDeriv ℝ 2 u x‖ ≤ (Dbase * scale : ℝ) := by
      intro x hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hcoverLoc hx)
      exact (hbaseLoc i).1 2 (by norm_num) x hxi
    have hbaseGlobal := hbaseGlobalForall scale u hbaseLoc hbaseGlobalJet
    have hquotP (p : {x // x ∈ Kset}) :
        ∀ (v : EuclideanSpace ℂ (Fin n)) (h : ℝ), ‖v‖ = 1 →
          0 < |h| → |h| < δlocal p →
          HolderBoundOn 2 α (Cquot p * scale)
            (Metric.closedBall (p : EuclideanSpace ℂ (Fin n)) (R p / 16))
            (fun z ↦ (u (z + h • v) - u z) / h) := by
      rcases hRdata p with ⟨hRp, hRhalf, hRpU⟩
      have hradOrder : R p / 8 = R p / (2 * 4) := by norm_num
      have hCorderLocal :
          ∀ (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
            (q : EuclideanSpace ℂ (Fin n) → ℝ),
            (∀ i j, ContDiffOn ℝ 0 (fun z ↦ A z i j)
              (Metric.ball (p : EuclideanSpace ℂ (Fin n)) ((R p / 2) / 4))) →
            ContDiffOn ℝ 2 q (Metric.ball (p : EuclideanSpace ℂ (Fin n)) ((R p / 2) / 4)) →
            IsUniformlyEllipticOn A lam
              (Metric.ball (p : EuclideanSpace ℂ (Fin n)) ((R p / 2) / 4)) →
            (∀ i j, HolderBoundOn 0 α K
              (Metric.ball (p : EuclideanSpace ℂ (Fin n)) ((R p / 2) / 4))
              (fun z ↦ A z i j)) →
            ∀ Kq Ksource : ℝ≥0,
              ContDiffOn ℝ 0 (complexEllipticOp A q)
                (Metric.ball (p : EuclideanSpace ℂ (Fin n)) ((R p / 2) / 4)) →
              HolderBoundOn 0 α Ksource
                (Metric.ball (p : EuclideanSpace ℂ (Fin n)) ((R p / 2) / 4))
                (complexEllipticOp A q) →
              (∀ z ∈ Metric.ball (p : EuclideanSpace ℂ (Fin n)) ((R p / 2) / 4),
                |q z| ≤ Kq) →
              HolderBoundOn 2 α (Corder p * (Ksource + Kq))
                (Metric.closedBall (p : EuclideanSpace ℂ (Fin n)) (R p / 16)) q := by
        simpa [div_div, hradOrder] using hCorder p
      have hLocal := quotient_local_estimate α hα₀ hα₁ lam K hlam
        hRhalf (by positivity : 0 < R p / 2) (by linarith [hRp]) hRpU
        (Cbase p) (Corder p) (hCbase p) (rQ := R p / 16) (by ring)
        (by simpa [div_div] using hCorderLocal)
        hA hu hEll hAHolder K₀ K₁ hLu hLuHolder huBound
      rcases hLocal with ⟨hδ, hquot⟩
      have hrad : R p / 16 = (R p / 2) / 8 := by ring
      intro v h hv hh₀ hh
      have hh' : |h| < (R p / 2) / 8 := by
        change |h| < R p / 16 at hh
        simpa [hrad] using hh
      have hbound := hquot v h hv hh₀ hh'
      simpa [Cquot, DquotAt, scale, hrad] using hbound
    have hquotLoc (v : EuclideanSpace ℂ (Fin n)) (h : ℝ)
        (hv : ‖v‖ = 1) (hh₀ : 0 < |h|) (hh : |h| < delta) :
        ∀ i : ι, HolderBoundOn 2 α (Dquot * scale) (Uloc i)
          (fun z ↦ (u (z + h • v) - u z) / h) := by
      intro i
      have hsmall : |h| < δlocal i.val := lt_of_lt_of_le hh (hdeltaLe i)
      have hlocal := (hquotP i.val v h hv hh₀ hsmall).mono_set
        (Metric.ball_subset_closedBall : Uloc i ⊆
          Metric.closedBall (i.val : EuclideanSpace ℂ (Fin n)) (R i.val / 16))
      exact hlocal.mono_const
        (mul_le_mul_of_nonneg_right (hquotC i) (NNReal.coe_nonneg scale))
    have hquotGlobalJet (v : EuclideanSpace ℂ (Fin n)) (h : ℝ)
        (hv : ‖v‖ = 1) (hh₀ : 0 < |h|) (hh : |h| < delta) :
        ∀ x ∈ Kset,
          ‖iteratedFDeriv ℝ 2 (fun z ↦ (u (z + h • v) - u z) / h) x‖ ≤
            (Dquot * scale : ℝ) := by
      intro x hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hcoverLoc hx)
      exact (hquotLoc v h hv hh₀ hh i).1 2 (by norm_num) x hxi
    have hquotGlobal (v : EuclideanSpace ℂ (Fin n)) (h : ℝ)
        (hv : ‖v‖ = 1) (hh₀ : 0 < |h|) (hh : |h| < delta) :
        HolderBoundOn 2 α (CquotGlobal * scale) Kset
          (fun z ↦ (u (z + h • v) - u z) / h) :=
      hquotGlobalForall scale (fun z ↦ (u (z + h • v) - u z) / h)
        (hquotLoc v h hv hh₀ hh) (hquotGlobalJet v h hv hh₀ hh)
    have hbaseFinal : HolderBoundOn 2 α (C * scale) Kset u :=
      hbaseGlobal.mono_const
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (NNReal.coe_nonneg scale))
    refine ⟨hbaseFinal, ?_⟩
    intro v h hv hh₀ hh
    exact (hquotGlobal v h hv hh₀ hh).mono_const
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (NNReal.coe_nonneg scale))

theorem firstOrderRegularity_differenceQuotientEstimates {n : ℕ}
    (hOrder : InteriorSchauderOrder n 0) :
    ∀ (α : ℝ≥0), 0 < α → α < 1 →
      ∀ (lam K : ℝ≥0), 0 < lam →
        ∀ U V : Set (EuclideanSpace ℂ (Fin n)), IsOpen U → IsCompact (closure V) →
          closure V ⊆ U →
          ∃ C : ℝ≥0, ∀ (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
            (u : EuclideanSpace ℂ (Fin n) → ℝ),
            (∀ j l, ContDiffOn ℝ 1 (fun z ↦ A z j l) U) → ContDiffOn ℝ 2 u U →
            IsUniformlyEllipticOn A lam U →
            (∀ j l, HolderBoundOn 1 α K U fun z ↦ A z j l) →
            ∀ K₀ K₁ : ℝ≥0, ContDiffOn ℝ 1 (complexEllipticOp A u) U →
              HolderBoundOn 1 α K₁ U (complexEllipticOp A u) →
              (∀ z ∈ U, |u z| ≤ K₀) →
              HolderBoundOn 2 α (C * (K₁ + K₀)) (closure V) u ∧
                (∃ δ : ℝ, 0 < δ ∧
                  ∀ (v : EuclideanSpace ℂ (Fin n)) (h : ℝ), ‖v‖ = 1 →
                    0 < |h| → |h| < δ →
                    (∀ z ∈ closure V, z + h • v ∈ U) →
                    HolderBoundOn 2 α (C * (K₁ + K₀)) (closure V)
                      (fun z ↦ (u (z + h • v) - u z) / h)) ∧
                (∀ W : Set (EuclideanSpace ℂ (Fin n)), IsOpen W →
                  IsCompact (closure W) → closure W ⊆ U →
                  ∃ C' : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
                    ∀ (v : EuclideanSpace ℂ (Fin n)) (h : ℝ), ‖v‖ = 1 →
                      0 < |h| → |h| < δ →
                      (∀ z ∈ closure W, z + h • v ∈ U) →
                      HolderBoundOn 2 α C' (closure W)
                        (fun z ↦ (u (z + h • v) - u z) / h)) := by
  intro α hα₀ hα₁ lam K hlam U V hU hV hVU
  obtain ⟨C, δ, hδ, hCompact⟩ := quotient_estimates_on_compact hOrder α hα₀ hα₁
    lam K hlam hU hV hVU
  refine ⟨C, ?_⟩
  intro A u hA hu hEll hAHolder K₀ K₁ hLu hLuHolder huBound
  obtain ⟨hbase, hquot⟩ := hCompact A u hA hu hEll hAHolder K₀ K₁
    hLu hLuHolder huBound
  refine ⟨hbase, ⟨δ, hδ, ?_⟩, ?_⟩
  · intro v h hv hh₀ hh hshift
    exact hquot v h hv hh₀ hh
  · intro W hW hWcompact hWU
    obtain ⟨CW, δW, hδW, hCompactW⟩ := quotient_estimates_on_compact hOrder α hα₀ hα₁
      lam K hlam hU hWcompact hWU
    obtain ⟨_, hquotW⟩ := hCompactW A u hA hu hEll hAHolder K₀ K₁
      hLu hLuHolder huBound
    refine ⟨CW * (K₁ + K₀), δW, hδW, ?_⟩
    intro v h hv hh₀ hh hshift
    exact hquotW v h hv hh₀ hh

end CalabiYau.Schauder
