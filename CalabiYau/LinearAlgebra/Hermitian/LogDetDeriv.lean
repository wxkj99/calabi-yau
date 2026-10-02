module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Derivatives of `det` and `log det`

**Jacobi's formula** `d/dt det (A + t H) = tr (adj (A + t H) H)` and its consequence
`d (log det)_A [H] = tr (A⁻¹ H)` for positive definite `A`, which is the linearization of the
complex Monge–Ampère operator `φ ↦ log det (g + ∂∂̄φ)`, together with the second derivative
`d/dt tr ((A + t H)⁻¹ H) = -tr (A⁻¹ H A⁻¹ H)` that expresses the concavity of `log det`.

## Norms

`Matrix n n 𝕜` has no global norm. The directional statements (`HasDerivAt` along the affine line
`t ↦ A + t • H`) need none. The Fréchet statements (`Matrix.contDiffAt_inv`,
`Matrix.PosDef.contDiffAt_log_det`, `Matrix.PosDef.fderiv_log_det_apply`) use the elementwise sup
norm, `open scoped Matrix.Norms.Elementwise`, which is the norm the
extracted Hölder and Schauder theory (`CalabiYau.Analysis.Holder`) uses; importers must open the
same scope to use them. Smoothness and derivatives do not depend on this choice, since all norms on
a finite-dimensional space are equivalent.

## Main statements

* `Matrix.hasDerivAt_det_add_smul`: Jacobi's formula along a line.
* `Matrix.PosDef.hasDerivAt_log_det_add_smul`: `d/dt|₀ log det (A + t H) = re tr (A⁻¹ H)`.
* `Matrix.PosDef.hasDerivAt_trace_inv_add_smul_mul`:
  `d/dt|₀ re tr ((A + t H)⁻¹ H) = -re tr (A⁻¹ H A⁻¹ H)`.
* `Matrix.contDiffAt_inv`, `Matrix.PosDef.contDiffAt_log_det`,
  `Matrix.PosDef.fderiv_log_det_apply`: Fréchet smoothness and derivative.

Smoothness of `det` itself is `Matrix.contDiff_det` in the extracted
`CalabiYau.Analysis.Calculus.Matrix.Determinant` (same norm scope); it is not restated here.

## References

* J. R. Magnus, H. Neudecker, *Matrix Differential Calculus*, §8.3 (Jacobi's formula).
* G. Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §3.1 (linearization of the
  Monge–Ampère operator).
-/

public section

open scoped ComplexOrder ContDiff Matrix.Norms.Elementwise
open Filter Topology

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem jacobi_leibniz_coeff {K : Type*} [NontriviallyNormedField K]
    (B H : Matrix n n K) :
    (∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : K) *
      ∑ k, (∏ i ∈ Finset.univ.erase k, B (σ i) i) * H (σ k) k) =
      (adjugate B * H).trace := by
  classical
  have hrhs :
      trace (adjugate B * H) = ∑ k, ∑ v, adjugate B k v * H v k := by
    simp [Matrix.trace, Matrix.mul_apply, Matrix.diag]
  rw [hrhs]
  have hLHS_rewrite :
      (∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : K) *
          ∑ k, (∏ i ∈ Finset.univ.erase k, B (σ i) i) * H (σ k) k) =
        ∑ σ : Equiv.Perm n, ∑ k,
          ((Equiv.Perm.sign σ : ℤ) : K) *
            ((∏ i ∈ Finset.univ.erase k, B (σ i) i) * H (σ k) k) := by
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
    ext σ
    simp
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
          ((Equiv.Perm.sign σ : ℤ) : K) *
            ((∏ i ∈ Finset.univ.erase k, B (σ i) i) * H (σ k) k)) =
        (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm n)).filter fun σ => σ k = v,
            ((Equiv.Perm.sign σ : ℤ) : K) *
              ∏ i ∈ Finset.univ.erase k, B (σ i) i) * H v k := by
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
        ((Equiv.Perm.sign τ : ℤ) : K) *
          ∏ i, (B.updateRow v (Pi.single k 1)) (τ i) i = 0 := by
    intro τ hτ
    rw [Finset.mem_filter] at hτ
    have hinv : τ⁻¹ v ≠ k := by
      intro h
      apply hτ.2
      have hτkv : τ (τ⁻¹ v) = v := by
        change (τ * τ⁻¹) v = v
        rw [mul_inv_cancel]
        rfl
      have := congrArg τ h
      rw [hτkv] at this
      exact this.symm
    have hzero : (B.updateRow v (Pi.single k 1)) (τ (τ⁻¹ v)) (τ⁻¹ v) = 0 := by
      have hτv : τ (τ⁻¹ v) = v := by
        change (τ * τ⁻¹) v = v
        rw [mul_inv_cancel]
        rfl
      rw [hτv, Matrix.updateRow_self]
      exact Pi.single_eq_of_ne (M := fun _ : n => K) hinv 1
    have hprod_zero :
        (∏ i, (B.updateRow v (Pi.single k 1)) (τ i) i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ (τ⁻¹ v)) hzero
    rw [hprod_zero, mul_zero]
  rw [Finset.sum_eq_zero hsecond, add_zero]
  symm
  refine Finset.sum_congr rfl ?_
  intro τ hτ
  rw [Finset.mem_filter] at hτ
  have hsplit_prod :
      (∏ i, (B.updateRow v (Pi.single k 1)) (τ i) i) =
        (B.updateRow v (Pi.single k 1)) (τ k) k *
          ∏ i ∈ Finset.univ.erase k,
            (B.updateRow v (Pi.single k 1)) (τ i) i :=
    (Finset.mul_prod_erase (Finset.univ : Finset n)
      (fun i => (B.updateRow v (Pi.single k 1)) (τ i) i)
      (Finset.mem_univ k)).symm
  rw [hsplit_prod]
  have h_topfactor : (B.updateRow v (Pi.single k 1)) (τ k) k = 1 := by
    rw [hτ.2, Matrix.updateRow_self]
    simp
  rw [h_topfactor, one_mul]
  have hrest :
      (∏ i ∈ Finset.univ.erase k, (B.updateRow v (Pi.single k 1)) (τ i) i) =
        ∏ i ∈ Finset.univ.erase k, B (τ i) i := by
    refine Finset.prod_congr rfl ?_
    intro i hi
    have hi_ne_k : i ≠ k := (Finset.mem_erase.mp hi).1
    have hτi_ne_v : τ i ≠ v := by
      intro hτiv
      have hinv_self : ∀ y, τ⁻¹ (τ y) = y := by
        intro y
        change (τ⁻¹ * τ) y = y
        rw [inv_mul_cancel]
        rfl
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

/-- **Jacobi's formula** along a line: `d/ds det (A + s H) = tr (adj (A + s H) H)`. -/
theorem hasDerivAt_det_add_smul {K : Type*} [NontriviallyNormedField K] (A H : Matrix n n K)
    (t : K) : HasDerivAt (fun s : K ↦ (A + s • H).det) (adjugate (A + t • H) * H).trace t := by
  have hentry (i j : n) : HasDerivAt (fun s : K ↦ (A + s • H) i j) (H i j) t := by
    have hid : HasDerivAt (fun s : K ↦ s) 1 t := hasDerivAt_id t
    have hmul : HasDerivAt (fun s : K ↦ s * H i j) (H i j) t := by
      simpa using (hid.mul_const (H i j))
    simpa [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using hmul.const_add (A i j)
  have hprod (σ : Equiv.Perm n) :
      HasDerivAt (fun s : K ↦ ∏ i, (A + s • H) (σ i) i)
        (∑ k, (∏ i ∈ Finset.univ.erase k, (A + t • H) (σ i) i) * H (σ k) k) t := by
    have h := HasDerivAt.fun_finsetProd
      (u := (Finset.univ : Finset n))
      (fun i hi => hentry (σ i) i)
    simpa [smul_eq_mul] using h
  have hterm (σ : Equiv.Perm n) :
      HasDerivAt
        (fun s : K ↦ ((Equiv.Perm.sign σ : ℤ) : K) * ∏ i, (A + s • H) (σ i) i)
        (((Equiv.Perm.sign σ : ℤ) : K) *
          ∑ k, (∏ i ∈ Finset.univ.erase k, (A + t • H) (σ i) i) * H (σ k) k) t := by
    simpa [Finset.mul_sum] using
      (hprod σ).const_mul ((Equiv.Perm.sign σ : ℤ) : K)
  have hsum : HasDerivAt
      (fun s : K ↦ ∑ σ : Equiv.Perm n,
        ((Equiv.Perm.sign σ : ℤ) : K) * ∏ i, (A + s • H) (σ i) i)
      (∑ σ : Equiv.Perm n,
        ((Equiv.Perm.sign σ : ℤ) : K) *
          ∑ k, (∏ i ∈ Finset.univ.erase k, (A + t • H) (σ i) i) * H (σ k) k) t := by
    exact HasDerivAt.fun_sum (u := Finset.univ) (fun σ _ => hterm σ)
  have heq : (fun s : K ↦ (A + s • H).det) =
      fun s ↦ ∑ σ : Equiv.Perm n,
        ((Equiv.Perm.sign σ : ℤ) : K) * ∏ i, (A + s • H) (σ i) i := by
    funext s
    rw [Matrix.det_apply']
  rw [heq]
  exact hsum.congr_deriv (jacobi_leibniz_coeff (A + t • H) H)

variable {𝕜 : Type*} [RCLike 𝕜] {A : Matrix n n 𝕜}

private theorem hasDerivAt_re_det_add_smul_jacobi (hA : A.PosDef) (H : Matrix n n 𝕜) :
    HasDerivAt (fun t : ℝ ↦ RCLike.re (A + t • H).det)
      (RCLike.re (adjugate A * H).trace) 0 := by
  let M : Matrix n n 𝕜 := A⁻¹ * H
  have hcore : HasDerivAt (fun z : 𝕜 ↦ (1 + z • M).det) (trace M) 0 := by
    let p : Polynomial 𝕜 := det (1 + (Polynomial.X : Polynomial 𝕜) • M.map Polynomial.C)
    have hp := p.hasDerivAt (0 : 𝕜)
    have hp' : HasDerivAt (fun z : 𝕜 ↦ p.eval z) (trace M) 0 := by
      simpa [p] using hp.congr_deriv (Matrix.derivative_det_one_add_X_smul M)
    have heq : (fun z : 𝕜 ↦ (1 + z • M).det) = fun z ↦ p.eval z := by
      funext z
      simp [p, eval_det, matPolyEquiv_map_smul]
      congr 1
      ext i j
      simp [Matrix.mul_apply, Matrix.diagonal]
      ring_nf
    rw [heq]
    exact hp'
  have hcast : HasDerivAt (fun t : ℝ ↦ (t : 𝕜)) 1 0 := by
    simpa using (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).hasDerivAt
  have hcoreF := hcore.hasFDerivAt.restrictScalars ℝ
  have hcoreReal : HasDerivAt (fun t : ℝ ↦ (1 + (t : 𝕜) • M).det)
      (trace M) 0 := by
    simpa [Function.comp_def] using hcoreF.comp_hasDerivAt_of_eq 0 hcast (by simp)
  have hunit : IsUnit A.det := (ne_of_gt hA.det_pos).isUnit
  have hmul : A * (A⁻¹ * H) = H := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv A hunit, Matrix.one_mul]
  have hfactor (t : ℝ) : A + t • H = A * (1 + (t : 𝕜) • M) := by
    calc
      A + t • H = A + (t : 𝕜) • H := by simp
      _ = A * 1 + (t : 𝕜) • (A * (A⁻¹ * H)) := by
        rw [hmul]
        simp
      _ = A * 1 + A * ((t : 𝕜) • (A⁻¹ * H)) := by rw [← Matrix.mul_smul]
      _ = A * (1 + (t : 𝕜) • M) := by simp [M, Matrix.mul_add]
  have hdetline : HasDerivAt (fun t : ℝ ↦ (A + t • H).det)
      (A.det * trace M) 0 := by
    have heq : (fun t : ℝ ↦ (A + t • H).det) =
        fun t : ℝ ↦ A.det * (1 + (t : 𝕜) • M).det := by
      funext t
      rw [hfactor t, Matrix.det_mul]
    rw [heq]
    exact hcoreReal.const_mul A.det
  have hreal : HasDerivAt (fun t : ℝ ↦ RCLike.re (A + t • H).det)
      (RCLike.re (A.det * trace M)) 0 := by
    have hmap : HasFDerivAt (RCLike.reCLM : 𝕜 →L[ℝ] ℝ)
        RCLike.reCLM A.det := (RCLike.reCLM : 𝕜 →L[ℝ] ℝ).hasFDerivAt
    simpa [Function.comp_def] using hmap.comp_hasDerivAt_of_eq 0 hdetline (by simp)
  have hadj : adjugate A = A.det • A⁻¹ := by
    rw [Matrix.inv_def, smul_smul, Ring.mul_inverse_cancel _ hunit, one_smul]
  have htrace : RCLike.re (adjugate A * H).trace =
      RCLike.re A.det * RCLike.re (A⁻¹ * H).trace := by
    rw [hadj, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, RCLike.mul_re]
    simp [(RCLike.pos_iff.mp hA.det_pos).2]
  have hderiv : RCLike.re (A.det * trace M) = RCLike.re (adjugate A * H).trace := by
    rw [RCLike.mul_re]
    simpa [M, (RCLike.pos_iff.mp hA.det_pos).2] using htrace.symm
  exact hreal.congr_deriv hderiv

namespace PosDef

/-- The derivative of `log det` at a positive definite matrix along a line:
`d/dt|₀ log det (A + t H) = re tr (A⁻¹ H)`. The direction `H` is arbitrary. -/
theorem hasDerivAt_log_det_add_smul (hA : A.PosDef) (H : Matrix n n 𝕜) :
    HasDerivAt (fun t : ℝ ↦ Real.log (RCLike.re (A + t • H).det))
      (RCLike.re (A⁻¹ * H).trace) 0 := by
  have hdet := hasDerivAt_re_det_add_smul_jacobi hA H
  have hpos : 0 < RCLike.re A.det := (RCLike.pos_iff.mp hA.det_pos).1
  have hpos0 : 0 < RCLike.re (A + (0 : ℝ) • H).det := by simpa using hpos
  have hlog := hdet.log (ne_of_gt hpos0)
  have hadj : adjugate A = A.det • A⁻¹ := by
    rw [Matrix.inv_def, smul_smul, Ring.mul_inverse_cancel _ ((ne_of_gt hA.det_pos).isUnit),
      one_smul]
  have htrace : RCLike.re (adjugate A * H).trace =
      RCLike.re A.det * RCLike.re (A⁻¹ * H).trace := by
    rw [hadj, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, RCLike.mul_re]
    simp [(RCLike.pos_iff.mp hA.det_pos).2]
  have hden : RCLike.re (A + (0 : ℝ) • H).det = RCLike.re A.det := by simp
  have hderiv : RCLike.re (A⁻¹ * H).trace =
      RCLike.re (adjugate A * H).trace / RCLike.re (A + (0 : ℝ) • H).det := by
    rw [htrace, hden]
    field_simp [ne_of_gt hpos]
  convert hlog using 1

/-- Second derivative of `log det` along a line:
`d/dt|₀ re tr ((A + t H)⁻¹ H) = -re tr (A⁻¹ H A⁻¹ H)`. -/
private theorem hasDerivAt_trace_inv_line (hA : A.PosDef) (H : Matrix n n 𝕜) :
    HasDerivAt (fun t : ℝ ↦ RCLike.re ((A + t • H)⁻¹ * H).trace)
      (-RCLike.re (A⁻¹ * H * A⁻¹ * H).trace) 0 := by
  let F : ℝ → ℝ := fun t ↦ RCLike.re ((A + t • H)⁻¹ * H).trace
  let Q : ℝ → ℝ := fun t ↦ RCLike.re (A⁻¹ * H * (A + t • H)⁻¹ * H).trace
  have hline : HasDerivAt (fun t : ℝ ↦ A + t • H) H 0 := by
    exact (((hasDerivAt_id (0 : ℝ)).smul_const H).const_add A).congr_deriv
      (one_smul ℝ H)
  have hdetLineCont : ContinuousAt (fun t : ℝ ↦ (A + t • H).det) 0 :=
    continuous_id.matrix_det.continuousAt.comp hline.continuousAt
  have hdet_ne : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), (A + t • H).det ≠ 0 := by
    have hmem : (fun t : ℝ ↦ (A + t • H).det) 0 ∈ {z : 𝕜 | z ≠ 0} := by
      simpa using ne_of_gt hA.det_pos
    exact hdetLineCont.eventually (isOpen_ne.mem_nhds hmem)
  have hRingInv : ContinuousAt Ring.inverse A.det := by
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ (ne_of_gt hA.det_pos)
  have hAdj : ContDiff ℝ ∞ (fun B : Matrix n n 𝕜 ↦ adjugate B) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    simp_rw [adjugate_apply, det_apply']
    refine ContDiff.sum fun σ _ => ?_
    exact contDiff_const.mul (contDiff_prod fun k _ => by
      by_cases h : σ k = j
      · simp [updateRow_apply, h, Pi.single_apply]
        exact contDiff_const
      · simpa [updateRow_apply, h, Pi.single_apply] using
          (contDiff_pi.mp (contDiff_pi.mp contDiff_id (σ k)) k))
  have hAdjLineCont : ContinuousAt (fun t : ℝ ↦ adjugate (A + t • H)) 0 :=
    hAdj.continuous.continuousAt.comp hline.continuousAt
  have hRingInvLine : ContinuousAt Ring.inverse ((A + (0 : ℝ) • H).det) := by
    simpa using hRingInv
  have hinvAt : ContinuousAt (fun z : 𝕜 ↦ z⁻¹) ((A + (0 : ℝ) • H).det) := by
    simpa only [Ring.inverse_eq_inv'] using hRingInvLine
  have hdetInvAt : ContinuousAt (fun B : Matrix n n 𝕜 ↦ B.det⁻¹) (A + (0 : ℝ) • H) := by
    simpa only [Function.comp_def] using
      hinvAt.comp (continuous_id.matrix_det.continuousAt)
  have hdetInvAddCont : ContinuousAt (fun X : Matrix n n 𝕜 ↦ (A + X).det⁻¹)
      ((0 : ℝ) • H) := by
    convert hdetInvAt.comp (continuousAt_const.add continuousAt_id) using 1
    ext X
    rfl
  have hsmul : ContinuousAt (fun t : ℝ ↦ t • H) 0 := by
    convert (continuousAt_id.smul
      (continuousAt_const : ContinuousAt (fun _ : ℝ ↦ H) 0)) using 1
    ext t
    rfl
  have hdetInvLineCont : ContinuousAt (fun t : ℝ ↦ (A + t • H).det⁻¹) 0 := by
    simpa only [Function.comp_def] using ContinuousAt.comp
      (f := fun t : ℝ ↦ t • H) (g := fun X : Matrix n n 𝕜 ↦ (A + X).det⁻¹)
      hdetInvAddCont hsmul
  have hinv_repr (B : Matrix n n 𝕜) : B⁻¹ = B.det⁻¹ • adjugate B := by
    rw [inv_def, Ring.inverse_eq_inv]
  have hInvLineCont : ContinuousAt (fun t : ℝ ↦ (A + t • H)⁻¹) 0 := by
    convert hdetInvLineCont.smul hAdjLineCont using 1
    funext t
    exact hinv_repr _
  have hQmat : ContinuousAt (fun t : ℝ ↦ A⁻¹ * H * (A + t • H)⁻¹ * H) 0 := by
    have hconst : ContinuousAt (fun _ : ℝ ↦ A⁻¹ * H) 0 := continuousAt_const
    exact (hconst.mul hInvLineCont).mul continuousAt_const
  have hQcont : ContinuousAt Q 0 := by
    have htr : Continuous (fun M : Matrix n n 𝕜 ↦ M.trace) := continuous_id.matrix_trace
    exact (RCLike.continuous_re.continuousAt).comp (htr.continuousAt.comp hQmat)
  have hresolvent : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
      (A + t • H)⁻¹ - A⁻¹ = -(t • (A⁻¹ * H * (A + t • H)⁻¹)) := by
    filter_upwards [hdet_ne] with t ht
    let B := A + t • H
    have hAiA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A (ne_of_gt hA.det_pos).isUnit
    have hBBi : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B ht.isUnit
    have hAB : A - B = -(t • H) := by simp [B]
    calc
      B⁻¹ - A⁻¹ = A⁻¹ * A * B⁻¹ - A⁻¹ * (B * B⁻¹) := by
        rw [hAiA, hBBi]
        simp
      _ = A⁻¹ * (A - B) * B⁻¹ := by noncomm_ring
      _ = -(t • (A⁻¹ * H * B⁻¹)) := by
        rw [hAB]
        simp [Matrix.mul_assoc]
  have hFdiff : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), F t - F 0 = -t * Q t := by
    filter_upwards [hresolvent] with t ht
    have hmul := congrArg (fun M : Matrix n n 𝕜 ↦ M * H) ht
    have htr := congrArg Matrix.trace hmul
    have hre := congrArg RCLike.re htr
    simpa [F, Q, Matrix.sub_mul, Matrix.trace_sub, Matrix.trace_smul,
      Matrix.smul_mul, Matrix.mul_assoc, RCLike.smul_re] using hre
  have hslopeEq : (fun t : ℝ ↦ t⁻¹ * (F (0 + t) - F 0)) =ᶠ[𝓝[≠] (0 : ℝ)]
      fun t ↦ -Q t := by
    filter_upwards [hFdiff.filter_mono inf_le_left, self_mem_nhdsWithin] with t hfd ht
    rw [zero_add, hfd]
    have ht0 : t ≠ 0 := by simpa using ht
    field_simp [ht0]
  have hFderiv : HasDerivAt F (-Q 0) 0 := by
    apply hasDerivAt_iff_tendsto_slope_zero.mpr
    have hlim : Tendsto (fun t : ℝ ↦ -Q t) (𝓝[≠] 0) (𝓝 (-Q 0)) :=
      (hQcont.tendsto.neg).mono_left nhdsWithin_le_nhds
    exact hlim.congr' hslopeEq.symm
  simpa [F, Q] using hFderiv

theorem hasDerivAt_trace_inv_add_smul_mul (hA : A.PosDef) (H : Matrix n n 𝕜) :
    HasDerivAt (fun t : ℝ ↦ RCLike.re ((A + t • H)⁻¹ * H).trace)
      (-RCLike.re (A⁻¹ * H * A⁻¹ * H).trace) 0 := by
  exact hasDerivAt_trace_inv_line hA H

end PosDef

section Frechet

open scoped Matrix.Norms.Elementwise

/-- Matrix inversion is smooth near an invertible matrix. -/
theorem contDiffAt_inv (hA : IsUnit A.det) :
    ContDiffAt ℝ ∞ (fun B : Matrix n n 𝕜 ↦ B⁻¹) A := by
  have hdet : ContDiff ℝ ∞ (fun B : Matrix n n 𝕜 ↦ B.det) := by
    simp_rw [det_apply']
    refine ContDiff.sum fun σ _ => ?_
    exact contDiff_const.mul (contDiff_prod fun i _ =>
      contDiff_pi.mp (contDiff_pi.mp contDiff_id (σ i)) i)
  have hadj : ContDiff ℝ ∞ (fun B : Matrix n n 𝕜 ↦ adjugate B) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    simp_rw [adjugate_apply, det_apply']
    refine ContDiff.sum fun σ _ => ?_
    exact contDiff_const.mul (contDiff_prod fun k _ => by
      by_cases h : σ k = j
      · simp [updateRow_apply, h, Pi.single_apply]
        exact contDiff_const
      · simpa [updateRow_apply, h, Pi.single_apply] using
          (contDiff_pi.mp (contDiff_pi.mp contDiff_id (σ k)) k))
  have hdet_ne : A.det ≠ 0 := hA.ne_zero
  have hscalar : ContDiffAt ℝ ∞ (fun B : Matrix n n 𝕜 ↦ B.det⁻¹) A :=
    (_root_.contDiffAt_inv (𝕜 := ℝ) (𝕜' := 𝕜) hdet_ne).comp A hdet.contDiffAt
  have hrepr : (fun B : Matrix n n 𝕜 ↦ B⁻¹) =
      fun B ↦ B.det⁻¹ • adjugate B := by
    funext B
    rw [inv_def, Ring.inverse_eq_inv]
  rw [hrepr]
  exact hscalar.smul hadj.contDiffAt

/-- `log det` is smooth near a positive definite matrix. -/
theorem PosDef.contDiffAt_log_det (hA : A.PosDef) :
    ContDiffAt ℝ ∞ (fun B : Matrix n n 𝕜 ↦ Real.log (RCLike.re B.det)) A := by
  have hdet : ContDiff ℝ ∞ (fun B : Matrix n n 𝕜 ↦ RCLike.re B.det) := by
    have hpoly : ContDiff ℝ ∞ (fun B : Matrix n n 𝕜 ↦ B.det) := by
      simp_rw [det_apply']
      refine ContDiff.sum fun σ _ => ?_
      exact contDiff_const.mul (contDiff_prod fun i _ =>
        contDiff_pi.mp (contDiff_pi.mp contDiff_id (σ i)) i)
    change ContDiff ℝ ∞ (fun B : Matrix n n 𝕜 ↦ (RCLike.reCLM : 𝕜 →L[ℝ] ℝ) (B.det))
    exact RCLike.reCLM.contDiff.comp hpoly
  have hdet_ne : RCLike.re A.det ≠ 0 := by
    exact ne_of_gt (RCLike.pos_iff.mp hA.det_pos).1
  exact (Real.contDiffAt_log.2 hdet_ne).comp A hdet.contDiffAt

/-- The Fréchet derivative of `log det` at a positive definite matrix:
`d (log det)_A [H] = re tr (A⁻¹ H)`. -/
theorem PosDef.fderiv_log_det_apply (hA : A.PosDef) (H : Matrix n n 𝕜) :
    fderiv ℝ (fun B : Matrix n n 𝕜 ↦ Real.log (RCLike.re B.det)) A H =
      RCLike.re (A⁻¹ * H).trace := by
  have hdiff := (PosDef.contDiffAt_log_det hA).differentiableAt (by simp)
  have hline : HasDerivAt (fun t : ℝ ↦ A + t • H) H 0 := by
    exact (((hasDerivAt_id (0 : ℝ)).smul_const H).const_add A).congr_deriv
      (one_smul ℝ H)
  have hchain := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hchain' : HasDerivAt (fun t : ℝ ↦ Real.log (RCLike.re (A + t • H).det))
      (fderiv ℝ (fun B : Matrix n n 𝕜 ↦ Real.log (RCLike.re B.det)) A H) 0 := by
    convert hchain using 1 <;> rfl
  exact (PosDef.hasDerivAt_log_det_add_smul hA H).unique hchain' |>.symm

end Frechet

end Matrix
