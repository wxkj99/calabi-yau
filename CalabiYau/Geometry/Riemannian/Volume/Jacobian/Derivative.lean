-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Integration/Measure/Jacobian/Derivative.lean
-- Locally modified.
module
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section


noncomputable section

open Matrix
open scoped Matrix BigOperators

namespace CalabiYau.RiemannianVolume

section Jacobi

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma hasDerivAt_prod_of_entries
    (G : ℝ → Matrix n n ℝ) (G' : Matrix n n ℝ) (t : ℝ)
    (hG : ∀ i j, HasDerivAt (fun t => G t i j) (G' i j) t)
    (σ : Equiv.Perm n) :
    HasDerivAt (fun t => ∏ i, G t (σ i) i)
      (∑ k, (∏ i ∈ Finset.univ.erase k, G t (σ i) i) • G' (σ k) k) t := by
  classical
  have hfactor : ∀ k ∈ (Finset.univ : Finset n),
      HasDerivAt (fun t : ℝ => G t (σ k) k) (G' (σ k) k) t :=
    fun k _ => hG (σ k) k
  exact HasDerivAt.fun_finsetProd hfactor

theorem hasDerivAt_det_of_entries
    (G : ℝ → Matrix n n ℝ) (G' : Matrix n n ℝ) (t : ℝ)
    (hG : ∀ i j, HasDerivAt (fun t => G t i j) (G' i j) t) :
    HasDerivAt (fun t => (G t).det)
      (∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∑ k, (∏ i ∈ Finset.univ.erase k, G t (σ i) i) * G' (σ k) k) t := by
  classical
  have hexpand : (fun s : ℝ => (G s).det)
      = (fun s : ℝ =>
          ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
            ∏ i, G s (σ i) i) := by
    funext s
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexpand]
  have hterm : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm n)),
      HasDerivAt
        (fun s : ℝ => ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, G s (σ i) i)
        (((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∑ k, (∏ i ∈ Finset.univ.erase k, G t (σ i) i) * G' (σ k) k) t := by
    intro σ _
    have hprod := hasDerivAt_prod_of_entries (n := n) G G' t hG σ
    have hmul := hprod.const_mul (((Equiv.Perm.sign σ : ℤ) : ℝ))
    have hsum_eq :
        ((Equiv.Perm.sign σ : ℤ) : ℝ) *
            ∑ k, (∏ i ∈ Finset.univ.erase k, G t (σ i) i) • G' (σ k) k
          = ((Equiv.Perm.sign σ : ℤ) : ℝ) *
            ∑ k, (∏ i ∈ Finset.univ.erase k, G t (σ i) i) * G' (σ k) k := by
      simp [smul_eq_mul]
    rw [← hsum_eq]
    exact hmul
  exact HasDerivAt.fun_sum hterm

theorem perm_sum_eq_trace_adjugate_mul
    (A B : Matrix n n ℝ) :
    (∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∑ k, (∏ i ∈ Finset.univ.erase k, A (σ i) i) * B (σ k) k)
      = trace (adjugate A * B) := by
  classical
  have hrhs :
      trace (adjugate A * B)
        = ∑ k, ∑ v, adjugate A k v * B v k := by
    simp [Matrix.trace, Matrix.mul_apply, Matrix.diag]
  rw [hrhs]
  have hLHS_rewrite :
      (∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∑ k, (∏ i ∈ Finset.univ.erase k, A (σ i) i) * B (σ k) k)
        = ∑ σ : Equiv.Perm n, ∑ k,
            ((Equiv.Perm.sign σ : ℤ) : ℝ) *
              ((∏ i ∈ Finset.univ.erase k, A (σ i) i) * B (σ k) k) := by
    refine Finset.sum_congr rfl ?_
    intro σ _
    rw [Finset.mul_sum]
  rw [hLHS_rewrite, Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro k _
  have hpart :
      (Finset.univ : Finset (Equiv.Perm n)) =
        Finset.univ.biUnion fun v : n =>
          (Finset.univ : Finset (Equiv.Perm n)).filter fun σ => σ k = v := by
    ext σ; simp
  have hdisj :
      ∀ v ∈ (Finset.univ : Finset n), ∀ w ∈ (Finset.univ : Finset n), v ≠ w →
        Disjoint
          ((Finset.univ : Finset (Equiv.Perm n)).filter fun σ => σ k = v)
          ((Finset.univ : Finset (Equiv.Perm n)).filter fun σ => σ k = w) := by
    intro v _ w _ hvw
    refine Finset.disjoint_left.mpr ?_
    intro σ hσv hσw
    rw [Finset.mem_filter] at hσv hσw
    exact hvw (hσv.2.symm.trans hσw.2)
  rw [hpart, Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl ?_
  intro v _
  have hBpull :
      (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm n)).filter fun σ => σ k = v,
          ((Equiv.Perm.sign σ : ℤ) : ℝ) *
            ((∏ i ∈ Finset.univ.erase k, A (σ i) i) * B (σ k) k))
        = (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm n)).filter fun σ => σ k = v,
            ((Equiv.Perm.sign σ : ℤ) : ℝ) *
              ∏ i ∈ Finset.univ.erase k, A (σ i) i) * B v k := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro σ hσ
    rw [Finset.mem_filter] at hσ
    rw [hσ.2]
    ring
  rw [hBpull]
  congr 1
  rw [adjugate_apply, Matrix.det_apply']
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := (Finset.univ : Finset (Equiv.Perm n)))
    (p := fun τ => τ k = v)]
  have hsecond :
      ∀ τ ∈ (Finset.univ : Finset (Equiv.Perm n)).filter fun τ => ¬ τ k = v,
        ((Equiv.Perm.sign τ : ℤ) : ℝ) *
          ∏ i, (A.updateRow v (Pi.single k 1)) (τ i) i = 0 := by
    intro τ hτ
    rw [Finset.mem_filter] at hτ
    have hinv : τ⁻¹ v ≠ k := by
      intro h
      apply hτ.2
      have hτkv : τ (τ⁻¹ v) = v := by
        change (τ * τ⁻¹) v = v
        rw [mul_inv_cancel]; rfl
      have := congrArg τ h
      rw [hτkv] at this
      exact this.symm
    have hzero :
        (A.updateRow v (Pi.single k 1)) (τ (τ⁻¹ v)) (τ⁻¹ v) = 0 := by
      have hτv : τ (τ⁻¹ v) = v := by
        change (τ * τ⁻¹) v = v
        rw [mul_inv_cancel]; rfl
      rw [hτv, Matrix.updateRow_self]
      exact Pi.single_eq_of_ne (M := fun _ : n => ℝ) hinv 1
    have hprod_zero :
        (∏ i, (A.updateRow v (Pi.single k 1)) (τ i) i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ (τ⁻¹ v)) hzero
    rw [hprod_zero, mul_zero]
  rw [Finset.sum_eq_zero hsecond, add_zero]
  symm
  refine Finset.sum_congr rfl ?_
  intro τ hτ
  rw [Finset.mem_filter] at hτ
  have hsplit_prod :
      (∏ i, (A.updateRow v (Pi.single k 1)) (τ i) i)
        = (A.updateRow v (Pi.single k 1)) (τ k) k *
            ∏ i ∈ Finset.univ.erase k,
              (A.updateRow v (Pi.single k 1)) (τ i) i :=
    (Finset.mul_prod_erase (Finset.univ : Finset n)
      (fun i => (A.updateRow v (Pi.single k 1)) (τ i) i)
      (Finset.mem_univ k)).symm
  rw [hsplit_prod]
  have h_topfactor :
      (A.updateRow v (Pi.single k 1)) (τ k) k = 1 := by
    rw [hτ.2, Matrix.updateRow_self]
    simp
  rw [h_topfactor, one_mul]
  have hrest :
      (∏ i ∈ Finset.univ.erase k, (A.updateRow v (Pi.single k 1)) (τ i) i)
        = ∏ i ∈ Finset.univ.erase k, A (τ i) i := by
    refine Finset.prod_congr rfl ?_
    intro i hi
    have hi_ne_k : i ≠ k := (Finset.mem_erase.mp hi).1
    have hτi_ne_v : τ i ≠ v := by
      intro hτiv
      have hinv_self : ∀ y, τ⁻¹ (τ y) = y := by
        intro y
        change (τ⁻¹ * τ) y = y
        rw [inv_mul_cancel]; rfl
      have h1 : i = τ⁻¹ v := by
        have := congrArg (⇑(τ⁻¹ : Equiv.Perm n)) hτiv
        rw [hinv_self i] at this
        exact this
      have hkinv : τ⁻¹ v = k := by
        have := congrArg (⇑(τ⁻¹ : Equiv.Perm n)) hτ.2
        rw [hinv_self k] at this
        exact this.symm
      exact hi_ne_k (h1.trans hkinv)
    rw [Matrix.updateRow_apply]
    exact if_neg hτi_ne_v
  rw [hrest]

theorem hasDerivAt_det_eq_trace_adjugate_mul
    (G : ℝ → Matrix n n ℝ) (G' : Matrix n n ℝ) (t : ℝ)
    (hG : ∀ i j, HasDerivAt (fun t => G t i j) (G' i j) t) :
    HasDerivAt (fun t => (G t).det)
      (trace (adjugate (G t) * G')) t := by
  have h := hasDerivAt_det_of_entries (n := n) G G' t hG
  rw [perm_sum_eq_trace_adjugate_mul (n := n) (G t) G'] at h
  exact h

lemma adjugate_eq_det_smul_inv
    {A : Matrix n n ℝ} (h : IsUnit A.det) :
    adjugate A = A.det • A⁻¹ := by
  rw [Matrix.inv_def]
  rw [smul_smul]
  rw [Ring.mul_inverse_cancel _ h]
  rw [one_smul]

theorem hasDerivAt_det_eq_det_mul_trace_inv_mul
    (G : ℝ → Matrix n n ℝ) (G' : Matrix n n ℝ) (t : ℝ)
    (hG : ∀ i j, HasDerivAt (fun t => G t i j) (G' i j) t)
    (hunit : IsUnit (G t).det) :
    HasDerivAt (fun t => (G t).det)
      ((G t).det * trace ((G t)⁻¹ * G')) t := by
  have h := hasDerivAt_det_eq_trace_adjugate_mul (n := n) G G' t hG
  have hadj := adjugate_eq_det_smul_inv (n := n) (A := G t) hunit
  have hrewrite : trace (adjugate (G t) * G') = (G t).det * trace ((G t)⁻¹ * G') := by
    rw [hadj]
    rw [Matrix.smul_mul]
    rw [Matrix.trace_smul]
    rfl
  rw [hrewrite] at h
  exact h

theorem hasDerivAt_sqrt_det_of_entries
    (G : ℝ → Matrix n n ℝ) (G' : Matrix n n ℝ) (t : ℝ)
    (hG : ∀ i j, HasDerivAt (fun t => G t i j) (G' i j) t)
    (hpos : 0 < (G t).det) :
    HasDerivAt (fun s => Real.sqrt (G s).det)
      ((1 / (2 * Real.sqrt (G t).det)) *
        ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∑ k, (∏ i ∈ Finset.univ.erase k, G t (σ i) i) * G' (σ k) k) t := by
  have hdet := hasDerivAt_det_of_entries (n := n) G G' t hG
  have hne : (G t).det ≠ 0 := ne_of_gt hpos
  have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (G t).det)) (G t).det :=
    Real.hasDerivAt_sqrt hne
  have hcomp := hsqrt.comp t hdet
  simpa [Function.comp] using! hcomp

theorem hasDerivAt_sqrt_det_eq_half_trace_inv_mul
    (G : ℝ → Matrix n n ℝ) (G' : Matrix n n ℝ) (t : ℝ)
    (hG : ∀ i j, HasDerivAt (fun t => G t i j) (G' i j) t)
    (hpos : 0 < (G t).det) :
    HasDerivAt (fun s => Real.sqrt (G s).det)
      ((1 / 2) * trace ((G t)⁻¹ * G') * Real.sqrt (G t).det) t := by
  have hunit : IsUnit (G t).det := (ne_of_gt hpos).isUnit
  have hdet := hasDerivAt_det_eq_det_mul_trace_inv_mul (n := n) G G' t hG hunit
  have hne : (G t).det ≠ 0 := ne_of_gt hpos
  have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (G t).det)) (G t).det :=
    Real.hasDerivAt_sqrt hne
  have hcomp := hsqrt.comp t hdet
  have hsqrt_ne : Real.sqrt (G t).det ≠ 0 := Real.sqrt_ne_zero'.mpr hpos
  have hkey :
      (1 / (2 * Real.sqrt (G t).det)) * ((G t).det * trace ((G t)⁻¹ * G'))
        = (1 / 2) * trace ((G t)⁻¹ * G') * Real.sqrt (G t).det := by
    have hdiv : (G t).det / Real.sqrt (G t).det = Real.sqrt (G t).det := by
      rw [eq_comm, eq_div_iff hsqrt_ne]
      exact Real.mul_self_sqrt hpos.le
    calc (1 / (2 * Real.sqrt (G t).det))
            * ((G t).det * trace ((G t)⁻¹ * G'))
        = ((G t).det / Real.sqrt (G t).det) * ((1 / 2) * trace ((G t)⁻¹ * G')) := by
          ring
      _ = Real.sqrt (G t).det * ((1 / 2) * trace ((G t)⁻¹ * G')) := by
          rw [hdiv]
      _ = (1 / 2) * trace ((G t)⁻¹ * G') * Real.sqrt (G t).det := by ring
  rw [hkey] at hcomp
  simpa [Function.comp] using! hcomp

end Jacobi

end CalabiYau.RiemannianVolume
