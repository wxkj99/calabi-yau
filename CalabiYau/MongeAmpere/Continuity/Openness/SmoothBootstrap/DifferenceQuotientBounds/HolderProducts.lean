module

public import CalabiYau.Mathlib.Geometry.Manifold.Holder
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Zero-order Hölder product bounds for difference-quotient forcing

This proved algebra cluster is a private implementation dependency of `BackgroundSecant`.
The bilinear constant includes both terms of the product difference. The trace specialization
uses the elementwise matrix norm and the real part of `tr(A B)`, including in dimension zero.
No differentiability or positivity is inferred from the zero-order Hölder hypotheses.

Source: Gilbarg–Trudinger, 2nd ed., §4.1, pp. 51–53, applied to the forcing in §6.4,
Theorem 6.17, pp. 109–111. Extracted from the already-proved parent algebra.
-/

public section

open scoped ContDiff NNReal Topology
open Matrix Set

namespace CalabiYau.Schauder

theorem holderBoundOn_zero_iff
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} {α C : ℝ≥0} {f : E → F} :
    HolderBoundOn 0 α C U f ↔
      (∀ x ∈ U, ‖f x‖ ≤ C) ∧ HolderOnWith C α f U := by
  let L := continuousMultilinearCurryFin0 ℝ E F
  constructor
  · intro hf
    refine ⟨?_, ?_⟩
    · intro x hx
      simpa only [norm_iteratedFDeriv_zero] using hf.1 0 le_rfl x hx
    · intro x hx y hy
      have h := hf.2 x hx y hy
      rw [iteratedFDeriv_zero_eq_comp] at h
      change edist (L.symm (f x)) (L.symm (f y)) ≤ _ at h
      rwa [L.symm.edist_map] at h
  · rintro ⟨hb, hh⟩
    refine ⟨?_, ?_⟩
    · intro j hj x hx
      have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
      subst j
      simpa only [norm_iteratedFDeriv_zero] using hb x hx
    · intro x hx y hy
      rw [iteratedFDeriv_zero_eq_comp]
      change edist (L.symm (f x)) (L.symm (f y)) ≤ _
      rw [L.symm.edist_map]
      exact hh x hx y hy

theorem holderBoundOn_zero_bilinear
    {E A B F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} {α Cf Cg : ℝ≥0} {f : E → A} {g : E → B}
    (L : A →L[ℝ] B →L[ℝ] F)
    (hf : HolderBoundOn 0 α Cf U f) (hg : HolderBoundOn 0 α Cg U g) :
    HolderBoundOn 0 α (2 * ‖L‖₊ * Cf * Cg) U (fun x => L (f x) (g x)) := by
  obtain ⟨hfb, hfh⟩ := holderBoundOn_zero_iff.mp hf
  obtain ⟨hgb, hgh⟩ := holderBoundOn_zero_iff.mp hg
  have hL (a : A) (b : B) : ‖L a b‖ ≤ ‖L‖ * ‖a‖ * ‖b‖ := by
    exact ((L a).le_opNorm b).trans
      (mul_le_mul_of_nonneg_right (L.le_opNorm a) (norm_nonneg b))
  apply holderBoundOn_zero_iff.mpr
  refine ⟨?_, ?_⟩
  · intro x hx
    calc
      ‖L (f x) (g x)‖ ≤ ‖L‖ * ‖f x‖ * ‖g x‖ := hL _ _
      _ ≤ ‖L‖ * Cf * Cg := by gcongr; exact hfb x hx; exact hgb x hx
      _ ≤ (2 * ‖L‖₊ * Cf * Cg : ℝ≥0) := by
        simp only [NNReal.coe_mul, NNReal.coe_ofNat, coe_nnnorm]
        nlinarith [mul_nonneg (mul_nonneg (norm_nonneg L) Cf.coe_nonneg) Cg.coe_nonneg]
  · intro x hx y hy
    have hreal : dist (L (f x) (g x)) (L (f y) (g y)) ≤
        ((2 * ‖L‖₊ * Cf * Cg : ℝ≥0) : ℝ) * dist x y ^ (α : ℝ) := by
      rw [dist_eq_norm]
      calc
        ‖L (f x) (g x) - L (f y) (g y)‖ =
            ‖L (f x) (g x - g y) + L (f x - f y) (g y)‖ := by
          congr 1
          simp only [map_sub, _root_.sub_apply]
          abel
        _ ≤ ‖L (f x) (g x - g y)‖ + ‖L (f x - f y) (g y)‖ := norm_add_le _ _
        _ ≤ ‖L‖ * ‖f x‖ * ‖g x - g y‖ +
            ‖L‖ * ‖f x - f y‖ * ‖g y‖ := add_le_add (hL _ _) (hL _ _)
        _ ≤ ‖L‖ * Cf * (Cg * dist x y ^ (α : ℝ)) +
            ‖L‖ * (Cf * dist x y ^ (α : ℝ)) * Cg := by
          gcongr
          · exact hfb x hx
          · simpa only [dist_eq_norm] using hgh.dist_le hx hy
          · simpa only [dist_eq_norm] using hfh.dist_le hx hy
          · exact hgb y hy
        _ = ((2 * ‖L‖₊ * Cf * Cg : ℝ≥0) : ℝ) * dist x y ^ (α : ℝ) := by
          simp only [NNReal.coe_mul, NNReal.coe_ofNat, coe_nnnorm]
          ring
    rw [edist_dist, edist_dist]
    calc
      ENNReal.ofReal (dist (L (f x) (g x)) (L (f y) (g y))) ≤
          ENNReal.ofReal (((2 * ‖L‖₊ * Cf * Cg : ℝ≥0) : ℝ) * dist x y ^ (α : ℝ)) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = ((2 * ‖L‖₊ * Cf * Cg : ℝ≥0) : ENNReal) *
          ENNReal.ofReal (dist x y) ^ (α : ℝ) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal,
          ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) α.coe_nonneg]

open scoped Matrix.Norms.Elementwise in
theorem holderBoundOn_zero_realTraceMatrixProduct
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (U : Set E) (α CA CB : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ A B : E → Matrix (Fin n) (Fin n) ℂ,
      HolderBoundOn 0 α CA U A → HolderBoundOn 0 α CB U B →
      HolderBoundOn 0 α C U (fun z => RCLike.re (A z * B z).trace) := by
  let mulL : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ]
      Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp
      (LinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℂ))
  let mulCLM : Matrix (Fin n) (Fin n) ℂ →L[ℝ]
      Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    mulL.toContinuousLinearMap
  let traceCLM : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ :=
    ((Matrix.traceLinearMap (Fin n) ℂ ℂ).restrictScalars ℝ).toContinuousLinearMap
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ :=
    ((ContinuousLinearMap.compL ℝ (Matrix (Fin n) (Fin n) ℂ)
      (Matrix (Fin n) (Fin n) ℂ) ℝ) (Complex.reCLM.comp traceCLM)).comp mulCLM
  exact ⟨_, fun A B hA hB => holderBoundOn_zero_bilinear L hA hB⟩

theorem holderBoundOn_zero_sub
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} {α Cf Cg : ℝ≥0} {f g : E → F}
    (hf : HolderBoundOn 0 α Cf U f) (hg : HolderBoundOn 0 α Cg U g) :
    HolderBoundOn 0 α (Cf + Cg) U (fun z => f z - g z) := by
  obtain ⟨hfb, hfh⟩ := holderBoundOn_zero_iff.mp hf
  obtain ⟨hgb, hgh⟩ := holderBoundOn_zero_iff.mp hg
  apply holderBoundOn_zero_iff.mpr
  refine ⟨?_, ?_⟩
  · intro x hx
    have hb : ‖f x‖ + ‖g x‖ ≤ (Cf : ℝ) + Cg :=
      add_le_add (hfb x hx) (hgb x hx)
    simpa only [NNReal.coe_add] using (norm_sub_le (f x) (g x)).trans hb
  · intro x hx y hy
    calc
      edist (f x - g x) (f y - g y) ≤ edist (f x) (f y) + edist (g x) (g y) :=
        by simpa only [sub_eq_add_neg, edist_neg_neg] using
          edist_add_add_le (f x) (-g x) (f y) (-g y)
      _ ≤ (Cf : ENNReal) * edist x y ^ (α : ℝ) +
          (Cg : ENNReal) * edist x y ^ (α : ℝ) :=
        add_le_add (hfh x hx y hy) (hgh x hx y hy)
      _ = ((Cf + Cg : ℝ≥0) : ENNReal) * edist x y ^ (α : ℝ) := by
        rw [ENNReal.coe_add, add_mul]

theorem holderBoundOn_zero_add
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} {α Cf Cg : ℝ≥0} {f g : E → F}
    (hf : HolderBoundOn 0 α Cf U f) (hg : HolderBoundOn 0 α Cg U g) :
    HolderBoundOn 0 α (Cf + Cg) U (fun z => f z + g z) := by
  have hneg : HolderBoundOn 0 α Cg U (fun z => -g z) := by
    obtain ⟨hgb, hgh⟩ := holderBoundOn_zero_iff.mp hg
    apply holderBoundOn_zero_iff.mpr
    refine ⟨?_, ?_⟩
    · intro x hx
      simpa only [norm_neg] using hgb x hx
    · intro x hx y hy
      simpa only [edist_neg_neg] using hgh x hx y hy
  simpa only [sub_neg_eq_add] using holderBoundOn_zero_sub hf hneg

end CalabiYau.Schauder
