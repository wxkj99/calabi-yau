module

public import CalabiYau.Geometry.Complex.Forms.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Order

import CalabiYau.Mathlib.Analysis.Matrix.PosDef.LogDet
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Real `(1,1)`-forms on `ℂⁿ`

A real `2`-form `α` on `ℂⁿ` (viewed as a real vector space) is of type `(1,1)` iff it is invariant
under the complex structure `J v = I • v`. Such a form can be written uniquely as
`α = i ∑ⱼₖ a_{jk̄} dzⱼ ∧ dz̄ₖ` with `(a_{jk̄})` a Hermitian matrix, its **coefficient matrix**.

We record the pointwise linear algebra needed for Kähler geometry, all in terms of the
coefficient matrix, so that the Hermitian matrix inequalities of `CalabiYau.LinearAlgebra.Hermitian`
apply directly:

* `ContinuousAlternatingMap.IsOneOne`: `J`-invariance;
* `ContinuousAlternatingMap.IsPositive`, `IsNonneg`: `α(v, Jv) > 0` (resp. `≥ 0`);
* `ContinuousAlternatingMap.coeffMatrix`: `a_{jk̄} = (α(eⱼ, J eₖ) - i α(eⱼ, eₖ)) / 2`;
* `ContinuousAlternatingMap.relDet ω α = αⁿ / ωⁿ = det a / det g`;
* `ContinuousAlternatingMap.relTrace ω α = tr_ω α = n α ∧ ωⁿ⁻¹ / ωⁿ = re tr (g⁻¹ a)`;
* `ContinuousAlternatingMap.dWedgeDBar ℓ = i ∂f ∧ ∂̄f` for `ℓ = df`, with coefficients `fⱼ f̄ₖ`.

`relDet` and `relTrace` do not depend on the choice of complex linear coordinates
(`relDet_compContinuousLinearMap`, `relTrace_compContinuousLinearMap`), so they are intrinsic at
each point of a complex manifold. For `α = ω + i∂∂̄φ` they are the Monge–Ampère ratio
`(ω + i∂∂̄φ)ⁿ / ωⁿ` and the complex Laplacian, without any `(p,q)`-form calculus.

## Conventions

`α(v, Jv) = 2 ∑ a_{jk̄} vⱼ v̄ₖ`, so `IsPositive α ↔ IsOneOne α ∧ (coeffMatrix α).PosDef`. For the
Euclidean form `ω₀ = i ∑ dzⱼ ∧ dz̄ⱼ = 2 ∑ dxⱼ ∧ dyⱼ` the coefficient matrix is `1`.
-/

@[expose] public section

open Complex Matrix
open scoped ComplexOrder MatrixOrder

/-- The complex structure `J v = I • v` of `ℂⁿ`, as a real linear map. -/
noncomputable def EuclideanSpace.complexStructure (n : ℕ) :
    EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) :=
  Complex.I • ContinuousLinearMap.id ℝ (EuclideanSpace ℂ (Fin n))

namespace ContinuousAlternatingMap

variable {n : ℕ}

/-- A real `2`-form on `ℂⁿ` is of type `(1,1)` iff it is invariant under `J`. -/
def IsOneOne (α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) : Prop :=
  ∀ u v : EuclideanSpace ℂ (Fin n), α ![I • u, I • v] = α ![u, v]

/-- A positive `(1,1)`-form: `α(v, Jv) > 0` for `v ≠ 0`. Positive `(1,1)`-forms are exactly the
Kähler forms at a point. -/
def IsPositive (α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) : Prop :=
  α.IsOneOne ∧ ∀ v : EuclideanSpace ℂ (Fin n), v ≠ 0 → 0 < α ![v, I • v]

/-- A semipositive `(1,1)`-form: `α(v, Jv) ≥ 0`. -/
def IsNonneg (α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) : Prop :=
  α.IsOneOne ∧ ∀ v : EuclideanSpace ℂ (Fin n), 0 ≤ α ![v, I • v]

/-- The coefficient matrix `(a_{jk̄})` of a real `2`-form, `α = i ∑ a_{jk̄} dzⱼ ∧ dz̄ₖ` when `α` is
of type `(1,1)`. -/
noncomputable def coeffMatrix (α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun j k ↦
    ((α ![EuclideanSpace.single j 1, I • EuclideanSpace.single k 1] : ℂ) -
      I * (α ![EuclideanSpace.single j 1, EuclideanSpace.single k 1] : ℂ)) / 2

/-- The ratio of top powers `αⁿ / ωⁿ = det a / det g`. -/
noncomputable def relDet (ω α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) : ℝ :=
  RCLike.re (coeffMatrix α).det / RCLike.re (coeffMatrix ω).det

/-- The trace of `α` with respect to `ω`, `tr_ω α = g^{jk̄} a_{jk̄} = n α ∧ ωⁿ⁻¹ / ωⁿ`. -/
noncomputable def relTrace (ω α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) : ℝ :=
  RCLike.re ((coeffMatrix ω)⁻¹ * coeffMatrix α).trace

/-- The semipositive `(1,1)`-form `i ∂f ∧ ∂̄f` at a point, as a function of `ℓ = df`:
`(u, v) ↦ (ℓ(Ju) ℓ(v) - ℓ(u) ℓ(Jv)) / 2`. Its coefficient matrix is `fⱼ f̄ₖ`, `fⱼ = ∂f/∂zⱼ`. -/
noncomputable def dWedgeDBar (ℓ : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) :
    EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ :=
  (1 / 2 : ℝ) • alternatizeUncurryFin
    ((ℓ.comp (EuclideanSpace.complexStructure n)).smulRight
      (ofSubsingleton ℝ (EuclideanSpace ℂ (Fin n)) ℝ (0 : Fin 1) ℓ))

/-- The complex matrix of a complex linear map of `ℂⁿ` in the standard basis:
`A eⱼ = ∑ₐ (matrix A)ₐⱼ eₐ`. -/
noncomputable def _root_.EuclideanSpace.clmMatrix
    (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a j ↦ A (EuclideanSpace.single j 1) a

variable {α β ω : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ}

/-! ### `(1,1)`-forms -/

theorem isOneOne_zero : (0 : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ).IsOneOne := by
  intro u v
  simp

theorem IsOneOne.add (hα : α.IsOneOne) (hβ : β.IsOneOne) : (α + β).IsOneOne := by
  intro u v
  simp [hα u v, hβ u v]

theorem IsOneOne.smul (hα : α.IsOneOne) (c : ℝ) : (c • α).IsOneOne := by
  intro u v
  simp [hα u v]

theorem IsOneOne.neg (hα : α.IsOneOne) : (-α).IsOneOne := by
  intro u v
  simp [hα u v]

theorem IsOneOne.sub (hα : α.IsOneOne) (hβ : β.IsOneOne) : (α - β).IsOneOne := by
  intro u v
  simp [hα u v, hβ u v]

private theorem IsOneOne.apply_eq_aux (hα : α.IsOneOne) (u v : EuclideanSpace ℂ (Fin n)) :
    α ![u, v] = -2 * (∑ j, ∑ k, α.coeffMatrix j k * u j * star (v k)).im := by
  classical
  let E (p : Fin n × Bool) : EuclideanSpace ℂ (Fin n) :=
    if p.2 then I • EuclideanSpace.single p.1 1 else EuclideanSpace.single p.1 1
  let c (x : EuclideanSpace ℂ (Fin n)) (p : Fin n × Bool) : ℝ :=
    if p.2 then (x p.1).im else (x p.1).re
  have hdecomp (x : EuclideanSpace ℂ (Fin n)) :
      x = ∑ p : Fin n × Bool, c x p • E p := by
    ext i
    simp [c, E, Fintype.sum_prod_type, Pi.single_apply,
      Finset.sum_ite_eq, Finset.sum_add_distrib]
    conv_lhs => rw [← RCLike.re_add_im (x.ofLp i)]
    change (RCLike.re (x.ofLp i) : ℂ) + RCLike.im (x.ofLp i) * I =
      (RCLike.im (x.ofLp i) : ℂ) * I + RCLike.re (x.ofLp i)
    ring_nf
  have hu := hdecomp u
  have hv := hdecomp v
  have hsumFirst (x : EuclideanSpace ℂ (Fin n)) :
      α ![∑ p, c u p • E p, x] = ∑ p, c u p * α ![E p, x] := by
    have hvect : ![∑ p, c u p • E p, x] =
        Function.update ![0, x] 0 (∑ p, c u p • E p) := by
      funext i
      fin_cases i <;> simp [Function.update]
    rw [hvect]
    change α.toMultilinearMap
      (Function.update ![0, x] 0 (∑ p, c u p • E p)) = _
    rw [α.toMultilinearMap.map_update_sum Finset.univ 0
      (fun p : Fin n × Bool ↦ c u p • E p) ![0, x]]
    simp only [MultilinearMap.map_update_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro p hp
    have hvec : Function.update ![0, x] 0 (E p) = ![E p, x] := by
      funext i
      fin_cases i <;> simp [Function.update]
    rw [hvec]
    rfl
  have hsumSecond (p : Fin n × Bool) :
      α ![E p, ∑ q, c v q • E q] = ∑ q, c v q * α ![E p, E q] := by
    have hvect : ![E p, ∑ q, c v q • E q] =
        Function.update ![E p, 0] 1 (∑ q, c v q • E q) := by
      funext i
      fin_cases i <;> simp [Function.update]
    rw [hvect]
    change α.toMultilinearMap
      (Function.update ![E p, 0] 1 (∑ q, c v q • E q)) = _
    rw [α.toMultilinearMap.map_update_sum Finset.univ 1
      (fun q : Fin n × Bool ↦ c v q • E q) ![E p, 0]]
    simp only [MultilinearMap.map_update_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro q hq
    have hvec : Function.update ![E p, 0] 1 (E q) = ![E p, E q] := by
      funext i
      fin_cases i <;> simp [Function.update]
    rw [hvec]
    rfl
  have hbilin : α ![u, v] = ∑ p, ∑ q,
      (c u p * c v q) * α ![E p, E q] := by
    have hvecUV : ![u, v] = ![∑ p, c u p • E p, ∑ q, c v q • E q] := by
      funext i
      fin_cases i
      · exact hu
      · exact hv
    calc
      α ![u, v] = α ![∑ p, c u p • E p, ∑ q, c v q • E q] := by rw [hvecUV]
      _ = ∑ p, ∑ q, (c u p * c v q) * α ![E p, E q] := by
        rw [hsumFirst]
        simp_rw [hsumSecond, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro q hq
        ring_nf
  have hnegLeft (a b : EuclideanSpace ℂ (Fin n)) :
      α ![-a, b] = -α ![a, b] := by
    change α.toContinuousMultilinearMap ![-a, b] =
      -α.toContinuousMultilinearMap ![a, b]
    have hvec : ![-a, b] = Function.update ![a, b] 0 ((-1 : ℝ) • a) := by
      funext i
      fin_cases i <;> simp [Function.update]
    rw [hvec]
    have hvec' : Function.update ![a, b] 0 a = ![a, b] := by
      funext i
      fin_cases i <;> simp [Function.update]
    have h := α.toContinuousMultilinearMap.map_update_smul ![a, b] 0 (-1 : ℝ) a
    rw [hvec'] at h
    simpa only [neg_one_smul, smul_eq_mul, neg_one_mul] using h
  have hnegRight (a b : EuclideanSpace ℂ (Fin n)) :
      α ![a, -b] = -α ![a, b] := by
    change α.toContinuousMultilinearMap ![a, -b] =
      -α.toContinuousMultilinearMap ![a, b]
    have hvec : ![a, -b] = Function.update ![a, b] 1 ((-1 : ℝ) • b) := by
      funext i
      fin_cases i <;> simp [Function.update]
    rw [hvec]
    have hvec' : Function.update ![a, b] 1 b = ![a, b] := by
      funext i
      fin_cases i <;> simp [Function.update]
    have h := α.toContinuousMultilinearMap.map_update_smul ![a, b] 1 (-1 : ℝ) b
    rw [hvec'] at h
    simpa only [neg_one_smul, smul_eq_mul, neg_one_mul] using h
  have hleft (j k : Fin n) :
      α ![(Complex.I : ℂ) • EuclideanSpace.single j 1, EuclideanSpace.single k 1] =
        -α ![EuclideanSpace.single j 1, (Complex.I : ℂ) • EuclideanSpace.single k 1] := by
    let ej : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j (1 : ℂ)
    let ek : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single k (1 : ℂ)
    have h := hα ((Complex.I : ℂ) • ej) ek
    have hI : (Complex.I : ℂ) • ((Complex.I : ℂ) • ej) = -ej := by
      simp [smul_smul, Complex.I_mul_I]
    rw [hI, hnegLeft] at h
    linarith
  have hdouble (j k : Fin n) :
      α ![I • EuclideanSpace.single j 1, I • EuclideanSpace.single k 1] =
        α ![EuclideanSpace.single j 1, EuclideanSpace.single k 1] :=
    hα (EuclideanSpace.single j 1) (EuclideanSpace.single k 1)
  have hcoeff (j k : Fin n) : α.coeffMatrix j k =
      (((α ![EuclideanSpace.single j 1, I • EuclideanSpace.single k 1] : ℝ) : ℂ) -
        I * ((α ![EuclideanSpace.single j 1, EuclideanSpace.single k 1] : ℝ) : ℂ)) / 2 := rfl
  have hRe (j k : Fin n) :
      α ![EuclideanSpace.single j 1, I • EuclideanSpace.single k 1] =
        2 * (α.coeffMatrix j k).re := by
    have hh := congrArg RCLike.re (hcoeff j k)
    simp [Complex.mul_re] at hh
    nlinarith
  have hIm (j k : Fin n) :
      α ![EuclideanSpace.single j 1, EuclideanSpace.single k 1] =
        -2 * (α.coeffMatrix j k).im := by
    have hh := congrArg RCLike.im (hcoeff j k)
    simp [Complex.mul_im] at hh
    nlinarith
  have hval (j k : Fin n) (b d : Bool) :
      α ![E (j, b), E (k, d)] =
        if b = d then -2 * (α.coeffMatrix j k).im
        else if b then -2 * (α.coeffMatrix j k).re
        else 2 * (α.coeffMatrix j k).re := by
    cases b <;> cases d <;> simp [E, hleft, hdouble, hIm, hRe]
  have hpair (j k : Fin n) :
      (∑ b : Bool, ∑ d : Bool,
        c u (j, b) * c v (k, d) * α ![E (j, b), E (k, d)]) =
        -2 * (α.coeffMatrix j k * u j * star (v k)).im := by
    simp [c, hval]
    ring_nf
  have hImSum :
      (∑ j : Fin n, ∑ k : Fin n, α.coeffMatrix j k * u j * star (v k)).im =
        ∑ j, ∑ k, (α.coeffMatrix j k * u j * star (v k)).im := by
    have hsumIm (s : Finset (Fin n)) (f : Fin n → ℂ) :
        (∑ j ∈ s, f j).im = ∑ j ∈ s, (f j).im := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih => simp [ha, ih]
    calc
      (∑ j : Fin n, ∑ k : Fin n, α.coeffMatrix j k * u j * star (v k)).im =
        ∑ j, (∑ k, α.coeffMatrix j k * u j * star (v k)).im := by
        exact hsumIm Finset.univ (fun j ↦ ∑ k, α.coeffMatrix j k * u j * star (v k))
      _ = ∑ j, ∑ k, (α.coeffMatrix j k * u j * star (v k)).im := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hsumIm Finset.univ (fun k ↦ α.coeffMatrix j k * u j * star (v k))
  rw [hbilin]
  simp only [Fintype.sum_prod_type]
  rw [hImSum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]
  simp_rw [hpair]

/-- A `(1,1)`-form is determined by its coefficient matrix. -/
theorem IsOneOne.ext (hα : α.IsOneOne) (hβ : β.IsOneOne) (h : α.coeffMatrix = β.coeffMatrix) :
  α = β := by
  ext u
  have hvec : u = ![u 0, u 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hvec]
  rw [IsOneOne.apply_eq_aux hα (u 0) (u 1), IsOneOne.apply_eq_aux hβ (u 0) (u 1), h]

/-! ### The coefficient matrix -/

@[simp]
theorem coeffMatrix_zero : (0 : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ).coeffMatrix = 0 := by
  ext j k
  change ((0 : ℂ) - I * (0 : ℂ)) / 2 = 0
  norm_num

@[simp]
theorem coeffMatrix_add (α β : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) :
    (α + β).coeffMatrix = α.coeffMatrix + β.coeffMatrix := by
  ext j k
  change (((α + β) ![EuclideanSpace.single j 1, I • EuclideanSpace.single k 1] : ℝ) -
      I * ((α + β) ![EuclideanSpace.single j 1, EuclideanSpace.single k 1] : ℝ)) / 2 =
    (((α ![EuclideanSpace.single j 1, I • EuclideanSpace.single k 1] : ℝ) -
        I * (α ![EuclideanSpace.single j 1, EuclideanSpace.single k 1] : ℝ)) / 2) +
      (((β ![EuclideanSpace.single j 1, I • EuclideanSpace.single k 1] : ℝ) -
        I * (β ![EuclideanSpace.single j 1, EuclideanSpace.single k 1] : ℝ)) / 2)
  rw [add_apply, add_apply]
  push_cast
  ring_nf

@[simp]
theorem coeffMatrix_smul (c : ℝ) (α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) :
    (c • α).coeffMatrix = c • α.coeffMatrix := by
  ext j k
  change (((c • α) ![EuclideanSpace.single j 1, I • EuclideanSpace.single k 1] : ℝ) -
      I * ((c • α) ![EuclideanSpace.single j 1, EuclideanSpace.single k 1] : ℝ)) / 2 =
    c • (((α ![EuclideanSpace.single j 1, I • EuclideanSpace.single k 1] : ℝ) -
      I * (α ![EuclideanSpace.single j 1, EuclideanSpace.single k 1] : ℝ)) / 2)
  rw [smul_apply, smul_apply]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_eq_mul]
  push_cast
  field_simp
  simp [mul_comm]

@[simp]
theorem coeffMatrix_neg (α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) :
    (-α).coeffMatrix = -α.coeffMatrix := by
  ext j k
  change (((-α) ![EuclideanSpace.single j 1, I • EuclideanSpace.single k 1] : ℝ) -
      I * ((-α) ![EuclideanSpace.single j 1, EuclideanSpace.single k 1] : ℝ)) / 2 =
    - (((α ![EuclideanSpace.single j 1, I • EuclideanSpace.single k 1] : ℝ) -
      I * (α ![EuclideanSpace.single j 1, EuclideanSpace.single k 1] : ℝ)) / 2)
  rw [neg_apply, neg_apply]
  push_cast
  ring_nf

@[simp]
theorem coeffMatrix_sub (α β : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) :
    (α - β).coeffMatrix = α.coeffMatrix - β.coeffMatrix := by
  ext j k
  change (((α - β) ![EuclideanSpace.single j 1, I • EuclideanSpace.single k 1] : ℝ) -
      I * ((α - β) ![EuclideanSpace.single j 1, EuclideanSpace.single k 1] : ℝ)) / 2 =
    (((α ![EuclideanSpace.single j 1, I • EuclideanSpace.single k 1] : ℝ) -
      I * (α ![EuclideanSpace.single j 1, EuclideanSpace.single k 1] : ℝ)) / 2) -
      (((β ![EuclideanSpace.single j 1, I • EuclideanSpace.single k 1] : ℝ) -
      I * (β ![EuclideanSpace.single j 1, EuclideanSpace.single k 1] : ℝ)) / 2)
  rw [sub_apply, sub_apply]
  push_cast
  ring_nf

theorem IsOneOne.isHermitian_coeffMatrix (hα : α.IsOneOne) : α.coeffMatrix.IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff]
  intro j k
  let eⱼ : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j 1
  let eₖ : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single k 1
  have hswap (u v : EuclideanSpace ℂ (Fin n)) : α ![u, v] = -α ![v, u] := by
    have h : α ![v, u] = -α ![u, v] := by
      simpa using α.map_swap ![u, v] Fin.zero_ne_one
    linarith
  have hmix : α ![eₖ, I • eⱼ] = α ![eⱼ, I • eₖ] := by
    calc
      α ![eₖ, I • eⱼ] = -α ![I • eⱼ, eₖ] := hswap _ _
      _ = α ![eⱼ, I • eₖ] := by
        have h := hα eⱼ (I • eₖ)
        have hneg : α ![I • eⱼ, -eₖ] = -α ![I • eⱼ, eₖ] := by
          change α.toContinuousMultilinearMap ![I • eⱼ, -eₖ] =
            -α.toContinuousMultilinearMap ![I • eⱼ, eₖ]
          have hvec : ![I • eⱼ, -eₖ] = Function.update ![I • eⱼ, eₖ] 1 (-eₖ) := by
            funext i
            fin_cases i <;> simp [Function.update]
          rw [hvec]
          have hvec' : Function.update ![I • eⱼ, eₖ] 1 eₖ = ![I • eⱼ, eₖ] := by
            funext i
            fin_cases i <;> simp [Function.update]
          have h := α.toContinuousMultilinearMap.map_update_smul ![I • eⱼ, eₖ]
            (1 : Fin 2) (-1 : ℝ) eₖ
          rw [hvec'] at h
          simpa only [neg_one_smul] using h
        have hI : I • (I • eₖ) = -eₖ := by simp [smul_smul]
        rw [hI] at h
        rw [hneg] at h
        exact h
  have hskew : α ![eₖ, eⱼ] = -α ![eⱼ, eₖ] := by
    exact hswap _ _
  change star (((α ![eₖ, I • eⱼ] : ℝ) - I * (α ![eₖ, eⱼ] : ℝ)) / 2) =
    ((α ![eⱼ, I • eₖ] : ℝ) - I * (α ![eⱼ, eₖ] : ℝ)) / 2
  simp [hmix, hskew]
  ring

/-- Evaluation of a `(1,1)`-form in terms of its coefficients:
`α(u, v) = -2 im (∑ a_{jk̄} uⱼ v̄ₖ)`. -/
theorem IsOneOne.apply_eq (hα : α.IsOneOne) (u v : EuclideanSpace ℂ (Fin n)) :
    α ![u, v] = -2 * (∑ j, ∑ k, α.coeffMatrix j k * u j * star (v k)).im := by
  exact IsOneOne.apply_eq_aux hα u v
/-- `α(v, Jv) = 2 ∑ a_{jk̄} vⱼ v̄ₖ`. -/
theorem IsOneOne.apply_I_smul (hα : α.IsOneOne) (v : EuclideanSpace ℂ (Fin n)) :
    α ![v, I • v] = 2 * (∑ j, ∑ k, α.coeffMatrix j k * v j * star (v k)).re := by
  rw [IsOneOne.apply_eq hα]
  have hstarI : star (I : ℂ) = -I := by
    apply Complex.ext <;> simp
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, star_mul, hstarI]
  let S : ℂ := ∑ j, ∑ k, α.coeffMatrix j k * v j * star (v k)
  have hsum :
      (∑ j, ∑ k, α.coeffMatrix j k * v j * (star (v k) * -I)) = -I * S := by
    calc
      (∑ j, ∑ k, α.coeffMatrix j k * v j * (star (v k) * -I)) =
          ∑ j, ∑ k, (-I) * (α.coeffMatrix j k * v j * star (v k)) := by
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = -I * S := by simp [S, Finset.mul_sum]
  rw [hsum]
  have him : (-I * S).im = -S.re := by
    simp [Complex.I_mul]
  rw [him]
  ring

theorem isPositive_iff : α.IsPositive ↔ α.IsOneOne ∧ α.coeffMatrix.PosDef := by
  have hsum (x : Fin n → ℂ) :
      (∑ j, ∑ k, α.coeffMatrix j k * star (x j) * x k) =
        star x ⬝ᵥ (α.coeffMatrix *ᵥ x) := by
    conv_rhs => rw [Matrix.dot_mulVec_eq_sum_sum, Finset.sum_comm]
    simp only [Pi.star_apply]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  constructor
  · rintro ⟨hα, hpos⟩
    refine ⟨hα, Matrix.posDef_iff_dotProduct_mulVec.mpr
      ⟨hα.isHermitian_coeffMatrix, fun {x} hx ↦ ?_⟩⟩
    let v : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (star x)
    have hv : v ≠ 0 := by
      intro hv
      apply hx
      have hs : star x = 0 := by
        simpa [v] using congrArg (fun w : EuclideanSpace ℂ (Fin n) => w.ofLp) hv
      exact star_eq_zero.mp hs
    have hEval := hα.apply_I_smul v
    simp only [v, Pi.star_apply, star_star] at hEval
    rw [hsum x] at hEval
    have hqRe : 0 < (star x ⬝ᵥ (α.coeffMatrix *ᵥ x)).re := by
      have hp := hpos v hv
      rw [hEval] at hp
      nlinarith
    exact RCLike.pos_iff.mpr
      ⟨hqRe, hα.isHermitian_coeffMatrix.im_star_dotProduct_mulVec_self x⟩
  · rintro ⟨hα, hM⟩
    refine ⟨hα, ?_⟩
    intro v hv
    let x : Fin n → ℂ := star v.ofLp
    have hx : x ≠ 0 := by
      intro hx
      apply hv
      ext i
      have hi := congrArg (fun f : Fin n → ℂ => f i) hx
      exact star_eq_zero.mp (by simpa [x] using hi)
    have hEval := hα.apply_I_smul v
    have hsum' := hsum x
    simp only [x, Pi.star_apply, star_star] at hsum'
    rw [hsum'] at hEval
    have hq := (Matrix.posDef_iff_dotProduct_mulVec.mp hM).2 hx
    have hqRe := (RCLike.pos_iff.mp hq).1
    have hqRe' : 0 < (v.ofLp ⬝ᵥ (α.coeffMatrix *ᵥ star v.ofLp)).re := by
      simpa [x, Pi.star_apply, star_star] using hqRe
    rw [hEval]
    exact mul_pos (by norm_num) hqRe'

theorem isNonneg_iff : α.IsNonneg ↔ α.IsOneOne ∧ α.coeffMatrix.PosSemidef := by
  have hsum (x : Fin n → ℂ) :
      (∑ j, ∑ k, α.coeffMatrix j k * star (x j) * x k) =
        star x ⬝ᵥ (α.coeffMatrix *ᵥ x) := by
    conv_rhs => rw [Matrix.dot_mulVec_eq_sum_sum, Finset.sum_comm]
    simp only [Pi.star_apply]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  constructor
  · rintro ⟨hα, hpos⟩
    refine ⟨hα, Matrix.posSemidef_iff_dotProduct_mulVec.mpr
      ⟨hα.isHermitian_coeffMatrix, fun x ↦ ?_⟩⟩
    let v : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (star x)
    have hEval := hα.apply_I_smul v
    simp only [v, Pi.star_apply, star_star] at hEval
    rw [hsum x] at hEval
    have hq : 0 ≤ (star x ⬝ᵥ (α.coeffMatrix *ᵥ x)).re := by
      have := hpos v
      rw [hEval] at this
      nlinarith
    exact RCLike.nonneg_iff.mpr
      ⟨hq, hα.isHermitian_coeffMatrix.im_star_dotProduct_mulVec_self x⟩
  · rintro ⟨hα, hM⟩
    refine ⟨hα, ?_⟩
    intro v
    let x : Fin n → ℂ := star v.ofLp
    have hEval := hα.apply_I_smul v
    have hsum' := hsum x
    simp only [x, Pi.star_apply, star_star] at hsum'
    rw [hsum'] at hEval
    have hq : 0 ≤ star x ⬝ᵥ (α.coeffMatrix *ᵥ x) :=
      (Matrix.posSemidef_iff_dotProduct_mulVec.mp hM).2 x
    have hqRe := (RCLike.nonneg_iff.mp hq).1
    have hqRe' : 0 ≤ (v.ofLp ⬝ᵥ (α.coeffMatrix *ᵥ star v.ofLp)).re := by
      simpa [x, Pi.star_apply, star_star] using hqRe
    rw [hEval]
    exact mul_nonneg (by norm_num) hqRe'

/-- For `(1,1)`-forms, `α - ω` is semipositive iff `g ≤ a` in the Loewner order. -/
theorem isNonneg_sub_iff (hα : α.IsOneOne) (hω : ω.IsOneOne) :
    (α - ω).IsNonneg ↔ ω.coeffMatrix ≤ α.coeffMatrix := by
  have hsub : (α - ω).IsOneOne := hα.sub hω
  rw [isNonneg_iff, Matrix.le_iff, coeffMatrix_sub]
  constructor
  · rintro ⟨_, hpsd⟩
    exact hpsd
  · intro hpsd
    exact ⟨hsub, hpsd⟩

theorem IsPositive.isOneOne (hα : α.IsPositive) : α.IsOneOne := hα.1

theorem IsPositive.isNonneg (hα : α.IsPositive) : α.IsNonneg := by
  refine ⟨hα.1, ?_⟩
  intro v
  by_cases hv : v = 0
  · subst v
    simp only [smul_zero]
    rw [α.map_eq_zero_of_eq ![0, 0] (i := 0) (j := 1) (by simp) (by decide)]
  · exact le_of_lt (hα.2 v hv)

theorem IsPositive.add_isNonneg (hα : α.IsPositive) (hβ : β.IsNonneg) : (α + β).IsPositive := by
  refine ⟨hα.1.add hβ.1, ?_⟩
  intro v hv
  have hp := hα.2 v hv
  have hn := hβ.2 v
  simpa using add_pos_of_pos_of_nonneg hp hn

theorem IsPositive.smul (hα : α.IsPositive) {c : ℝ} (hc : 0 < c) : (c • α).IsPositive := by
  refine ⟨hα.1.smul c, ?_⟩
  intro v hv
  have hp := hα.2 v hv
  simpa using mul_pos hc hp

/-- Positive `(1,1)`-forms form a convex cone. -/
theorem IsPositive.add (hα : α.IsPositive) (hβ : β.IsPositive) : (α + β).IsPositive := by
  exact hα.add_isNonneg hβ.isNonneg

/-- Transformation law under a complex linear change of coordinates `A`:
`a' = Aᵀ a Ā`. -/
theorem IsOneOne.coeffMatrix_compContinuousLinearMap (hα : α.IsOneOne)
    (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
    (α.compContinuousLinearMap (A.restrictScalars ℝ)).coeffMatrix =
      (EuclideanSpace.clmMatrix A)ᵀ * α.coeffMatrix * (EuclideanSpace.clmMatrix A).map star := by
  ext j k
  change (((α.compContinuousLinearMap (A.restrictScalars ℝ) ![
      EuclideanSpace.single j 1, I • EuclideanSpace.single k 1] : ℝ) -
      I * (α.compContinuousLinearMap (A.restrictScalars ℝ) ![
      EuclideanSpace.single j 1, EuclideanSpace.single k 1] : ℝ)) / 2) =
    ((EuclideanSpace.clmMatrix A)ᵀ * α.coeffMatrix *
      (EuclideanSpace.clmMatrix A).map star) j k
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  let u : EuclideanSpace ℂ (Fin n) := A (EuclideanSpace.single j 1)
  let v : EuclideanSpace ℂ (Fin n) := A (EuclideanSpace.single k 1)
  let S : ℂ := ∑ p, ∑ q, α.coeffMatrix p q * u p * star (v q)
  have hclm (a b : Fin n) : (EuclideanSpace.clmMatrix A) a b = A (EuclideanSpace.single b 1) a := rfl
  have hmatrix :
      ((EuclideanSpace.clmMatrix A)ᵀ * α.coeffMatrix *
        (EuclideanSpace.clmMatrix A).map star) j k = S := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, hclm]
    simp only [S, u, v]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    ring
  have hstarI : star (I : ℂ) = -I := by
    apply Complex.ext <;> simp
  have hsumI :
      (∑ p, ∑ q, α.coeffMatrix p q * u p * star ((I • v).ofLp q)) = -I * S := by
    calc
      (∑ p, ∑ q, α.coeffMatrix p q * u p * star ((I • v).ofLp q)) =
          ∑ p, ∑ q, (-I) * (α.coeffMatrix p q * u p * star (v q)) := by
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro q hq
        have hcoord : (I • v).ofLp q = I * v.ofLp q := by rfl
        rw [hcoord, star_mul, hstarI]
        ring
      _ = -I * S := by simp [S, Finset.mul_sum]
  have h1 : α ![u, I • v] = -2 * (-I * S).im := by
    rw [hα.apply_eq u (I • v)]
    rw [hsumI]
  have h2 : α ![u, v] = -2 * S.im := by
    rw [hα.apply_eq u v]
  have hvec1 : (A.restrictScalars ℝ) ∘ ![EuclideanSpace.single j 1,
      I • EuclideanSpace.single k 1] = ![u, I • v] := by
    funext i
    fin_cases i <;> simp [u, v, Function.comp_apply, map_smul]
  have hvec2 : (A.restrictScalars ℝ) ∘ ![EuclideanSpace.single j 1,
      EuclideanSpace.single k 1] = ![u, v] := by
    funext i
    fin_cases i <;> simp [u, v, Function.comp_apply]
  rw [hvec1, hvec2]
  change ((α ![u, I • v] : ℝ) - I * (α ![u, v] : ℝ)) / 2 = _
  rw [h1, h2, ← hmatrix]
  push_cast
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

theorem IsOneOne.compContinuousLinearMap (hα : α.IsOneOne)
    (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
    (α.compContinuousLinearMap (A.restrictScalars ℝ)).IsOneOne := by
  intro u v
  change α ((A.restrictScalars ℝ) ∘ ![I • u, I • v]) =
    α ((A.restrictScalars ℝ) ∘ ![u, v])
  have hu : A (I • u) = I • A u := map_smul A I u
  have hv : A (I • v) = I • A v := map_smul A I v
  have hL : (A.restrictScalars ℝ) ∘ ![I • u, I • v] = ![I • A u, I • A v] := by
    funext i
    fin_cases i <;> simp [Function.comp_apply, hu, hv]
  have hR : (A.restrictScalars ℝ) ∘ ![u, v] = ![A u, A v] := by
    funext i
    fin_cases i <;> rfl
  rw [hL, hR]
  exact hα (A u) (A v)

theorem IsPositive.compContinuousLinearMap (hα : α.IsPositive)
    (A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n)) :
    ContinuousAlternatingMap.IsPositive (α.compContinuousLinearMap
      ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)) := by
  refine ⟨hα.1.compContinuousLinearMap
    (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)), ?_⟩
  intro v hv
  have hvA : A v ≠ 0 := by
    intro hz
    apply hv
    apply A.injective
    simpa using hz
  change 0 < α ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ ∘
    ![v, I • v])
  have hJ : A (I • v) = I • A v := map_smul A I v
  have hEval :
      (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ ∘
        ![v, I • v] = ![A v, I • A v] := by
    funext i
    fin_cases i <;> simp [Function.comp_apply, hJ]
  rw [hEval]
  exact hα.2 (A v) hvA

/-! ### Relative determinant and trace -/

theorem relDet_self (hω : ω.IsPositive) : relDet ω ω = 1 := by
  have hωdet : RCLike.re ω.coeffMatrix.det ≠ 0 :=
    ((RCLike.pos_iff.1 ((isPositive_iff (α := ω)).mp hω).2.det_pos).1).ne'
  change RCLike.re ω.coeffMatrix.det / RCLike.re ω.coeffMatrix.det = 1
  exact div_self hωdet

theorem relDet_pos (hω : ω.IsPositive) (hα : α.IsPositive) : 0 < relDet ω α := by
  change 0 < RCLike.re α.coeffMatrix.det / RCLike.re ω.coeffMatrix.det
  apply div_pos
  · exact (RCLike.pos_iff.1 ((isPositive_iff (α := α)).mp hα).2.det_pos).1
  · exact (RCLike.pos_iff.1 ((isPositive_iff (α := ω)).mp hω).2.det_pos).1

/-- Cocycle property: `αⁿ/ωⁿ · βⁿ/αⁿ = βⁿ/ωⁿ`. -/
theorem relDet_mul_relDet (hω : ω.IsPositive) (hα : α.IsPositive) :
    relDet ω α * relDet α β = relDet ω β := by
  have hωdet : RCLike.re ω.coeffMatrix.det ≠ 0 :=
    ((RCLike.pos_iff.1 ((isPositive_iff (α := ω)).mp hω).2.det_pos).1).ne'
  have hαdet : RCLike.re α.coeffMatrix.det ≠ 0 :=
    ((RCLike.pos_iff.1 ((isPositive_iff (α := α)).mp hα).2.det_pos).1).ne'
  change (RCLike.re α.coeffMatrix.det / RCLike.re ω.coeffMatrix.det) *
      (RCLike.re β.coeffMatrix.det / RCLike.re α.coeffMatrix.det) =
    RCLike.re β.coeffMatrix.det / RCLike.re ω.coeffMatrix.det
  field_simp

theorem relDet_smul (c : ℝ) : relDet ω (c • α) = c ^ n * relDet ω α := by
  change RCLike.re ((coeffMatrix (c • α)).det) / RCLike.re ((coeffMatrix ω).det) =
    c ^ n * (RCLike.re ((coeffMatrix α).det) / RCLike.re ((coeffMatrix ω).det))
  rw [coeffMatrix_smul, RCLike.real_smul_eq_coe_smul (K := ℂ) c, Matrix.det_smul]
  rw [← RCLike.ofReal_pow, RCLike.re_ofReal_mul]
  simp
  ring

theorem relTrace_self (hω : ω.IsPositive) : relTrace ω ω = n := by
  have hωA : ω.coeffMatrix.PosDef := (isPositive_iff (α := ω)).mp hω |>.2
  have hunit : IsUnit ω.coeffMatrix.det :=
    (Matrix.isUnit_iff_isUnit_det ω.coeffMatrix).1 hωA.isUnit
  change RCLike.re ((ω.coeffMatrix)⁻¹ * ω.coeffMatrix).trace = n
  rw [Matrix.nonsing_inv_mul _ hunit]
  simp

@[simp]
theorem relTrace_zero : relTrace ω 0 = 0 := by
  change RCLike.re ((coeffMatrix ω)⁻¹ * coeffMatrix 0).trace = 0
  rw [coeffMatrix_zero]
  simp

theorem relTrace_add : relTrace ω (α + β) = relTrace ω α + relTrace ω β := by
  change RCLike.re ((coeffMatrix ω)⁻¹ * coeffMatrix (α + β)).trace =
    RCLike.re ((coeffMatrix ω)⁻¹ * coeffMatrix α).trace +
      RCLike.re ((coeffMatrix ω)⁻¹ * coeffMatrix β).trace
  rw [coeffMatrix_add, Matrix.mul_add, Matrix.trace_add]
  simp

theorem relTrace_smul (c : ℝ) : relTrace ω (c • α) = c * relTrace ω α := by
  change RCLike.re ((coeffMatrix ω)⁻¹ * coeffMatrix (c • α)).trace =
    c * RCLike.re ((coeffMatrix ω)⁻¹ * coeffMatrix α).trace
  rw [coeffMatrix_smul]
  simp [Matrix.trace_smul]

theorem relTrace_neg : relTrace ω (-α) = -relTrace ω α := by
  change RCLike.re ((coeffMatrix ω)⁻¹ * coeffMatrix (-α)).trace =
    -RCLike.re ((coeffMatrix ω)⁻¹ * coeffMatrix α).trace
  rw [coeffMatrix_neg]
  simp [Matrix.trace_neg]

theorem relTrace_sub : relTrace ω (α - β) = relTrace ω α - relTrace ω β := by
  change RCLike.re ((coeffMatrix ω)⁻¹ * coeffMatrix (α - β)).trace =
    RCLike.re ((coeffMatrix ω)⁻¹ * coeffMatrix α).trace -
      RCLike.re ((coeffMatrix ω)⁻¹ * coeffMatrix β).trace
  rw [coeffMatrix_sub, Matrix.mul_sub, Matrix.trace_sub]
  simp

theorem relTrace_nonneg (hω : ω.IsPositive) (hα : α.IsNonneg) : 0 ≤ relTrace ω α := by
  change 0 ≤ RCLike.re ((ω.coeffMatrix)⁻¹ * α.coeffMatrix).trace
  have hωpd : ω.coeffMatrix.PosDef := (isPositive_iff.mp hω).2
  have hωinv : (ω.coeffMatrix⁻¹).PosSemidef := hωpd.posSemidef.inv
  have hαpsd : α.coeffMatrix.PosSemidef := (isNonneg_iff.mp hα).2
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hαpsd.nonneg
  have htrace :
      (ω.coeffMatrix⁻¹ * (star B * B)).trace =
        (B * ω.coeffMatrix⁻¹ * star B).trace := by
    calc
      (ω.coeffMatrix⁻¹ * (star B * B)).trace =
          ((ω.coeffMatrix⁻¹ * star B) * B).trace := by rw [Matrix.mul_assoc]
      _ = (B * (ω.coeffMatrix⁻¹ * star B)).trace := by rw [Matrix.trace_mul_comm]
      _ = (B * ω.coeffMatrix⁻¹ * star B).trace := by rw [Matrix.mul_assoc]
  rw [hB, htrace]
  exact (RCLike.nonneg_iff.mp (hωinv.mul_mul_conjTranspose_same B).trace_nonneg).1

theorem relTrace_pos [NeZero n] (hω : ω.IsPositive) (hα : α.IsPositive) : 0 < relTrace ω α := by
  change 0 < RCLike.re ((ω.coeffMatrix)⁻¹ * α.coeffMatrix).trace
  have hωpd : ω.coeffMatrix.PosDef := (isPositive_iff.mp hω).2
  have hαpd : α.coeffMatrix.PosDef := (isPositive_iff.mp hα).2
  have hωinv : (ω.coeffMatrix⁻¹).PosDef := hωpd.inv
  have hωinvpsd : (ω.coeffMatrix⁻¹).PosSemidef := hωinv.posSemidef
  obtain ⟨B, hB⟩ :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hαpd.posSemidef.nonneg
  let S : Matrix (Fin n) (Fin n) ℂ := B * ω.coeffMatrix⁻¹ * star B
  have hSpsd : S.PosSemidef := by
    exact hωinvpsd.mul_mul_conjTranspose_same B
  have htrace : (ω.coeffMatrix⁻¹ * α.coeffMatrix).trace = S.trace := by
    rw [hB]
    change (ω.coeffMatrix⁻¹ * (star B * B)).trace =
      (B * ω.coeffMatrix⁻¹ * star B).trace
    calc
      (ω.coeffMatrix⁻¹ * (star B * B)).trace =
          ((ω.coeffMatrix⁻¹ * star B) * B).trace := by rw [Matrix.mul_assoc]
      _ = (B * (ω.coeffMatrix⁻¹ * star B)).trace := by rw [Matrix.trace_mul_comm]
      _ = (B * ω.coeffMatrix⁻¹ * star B).trace := by rw [Matrix.mul_assoc]
  have hdetA : α.coeffMatrix.det ≠ 0 := by
    intro h
    exact (RCLike.pos_iff.mp hαpd.det_pos).1.ne' (by simp [h])
  have hdetStarB : (star B).det = star B.det := by
    simp [star_eq_conjTranspose, Matrix.det_conjTranspose]
  have hdetB : B.det ≠ 0 := by
    intro hz
    apply hdetA
    rw [hB, Matrix.det_mul, hdetStarB, hz]
    simp
  have hωinvdet : (ω.coeffMatrix⁻¹).det ≠ 0 := by
    intro h
    exact (RCLike.pos_iff.mp hωinv.det_pos).1.ne' (by simp [h])
  have hdetS : S.det ≠ 0 := by
    have hfactor : (B * ω.coeffMatrix⁻¹ * star B).det ≠ 0 := by
      rw [Matrix.det_mul, Matrix.det_mul, hdetStarB]
      exact mul_ne_zero (mul_ne_zero hdetB hωinvdet) (star_ne_zero.mpr hdetB)
    exact hfactor
  have htraceNe : S.trace ≠ 0 := by
    intro htr
    apply hdetS
    have hSzero := hSpsd.trace_eq_zero_iff.mp htr
    simp [hSzero]
  have htraceNonneg := hSpsd.trace_nonneg
  have hRe := (RCLike.nonneg_iff.mp htraceNonneg).1
  have hIm := (RCLike.nonneg_iff.mp htraceNonneg).2
  have hReNe : RCLike.re S.trace ≠ 0 := by
    intro hz
    apply htraceNe
    exact RCLike.ext hz hIm
  rw [htrace]
  exact lt_of_le_of_ne hRe (Ne.symm hReNe)

/-- `relDet` does not depend on the choice of complex linear coordinates. -/
theorem relDet_compContinuousLinearMap (hω : ω.IsOneOne) (hα : α.IsOneOne)
    (A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n)) :
    relDet (ω.compContinuousLinearMap
        ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ))
      (α.compContinuousLinearMap
        ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)) =
      relDet ω α := by
  let C : Matrix (Fin n) (Fin n) ℂ := EuclideanSpace.clmMatrix A
  let b : Module.Basis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)) :=
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
  let Ae : EuclideanSpace ℂ (Fin n) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) := A.toLinearEquiv
  have hclm (i j : Fin n) : C i j = A (EuclideanSpace.single j 1) i := rfl
  have hC : C = LinearMap.toMatrix b b (Ae : EuclideanSpace ℂ (Fin n) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin n)) := by
    ext i j
    rw [hclm, LinearMap.toMatrix_apply]
    simp [b, Ae, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
  have hdetC : C.det ≠ 0 := by
    rw [hC, LinearMap.det_toMatrix]
    simpa only [LinearEquiv.coe_det] using (LinearEquiv.det Ae).ne_zero
  have hdetMap : (C.map star).det = star C.det := by
    simpa using ((starRingEnd ℂ).map_det C).symm
  have hnorm : C.det * star C.det = (‖C.det‖ : ℂ) ^ 2 := by
    exact RCLike.mul_conj C.det
  have hdetCong (M : Matrix (Fin n) (Fin n) ℂ) :
      (Cᵀ * M * C.map star).det = (‖C.det‖ : ℂ) ^ 2 * M.det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdetMap]
    calc
      C.det * M.det * star C.det = (C.det * star C.det) * M.det := by ring
      _ = (‖C.det‖ ^ 2 : ℂ) * M.det := by rw [hnorm]
  have hωc := hω.coeffMatrix_compContinuousLinearMap
    (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
  have hαc := hα.coeffMatrix_compContinuousLinearMap
    (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
  change RCLike.re ((α.compContinuousLinearMap
      ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)).coeffMatrix.det) /
      RCLike.re ((ω.compContinuousLinearMap
      ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)).coeffMatrix.det) =
    RCLike.re α.coeffMatrix.det / RCLike.re ω.coeffMatrix.det
  rw [hαc, hωc]
  change RCLike.re ((Cᵀ * α.coeffMatrix * C.map star).det) /
      RCLike.re ((Cᵀ * ω.coeffMatrix * C.map star).det) = _
  rw [hdetCong, hdetCong]
  have hre (z : ℂ) : RCLike.re ((‖C.det‖ : ℂ) ^ 2 * z) =
      ‖C.det‖ ^ 2 * RCLike.re z := by
    rw [← Complex.ofReal_pow]
    rw [mul_comm]
    calc
      RCLike.re (z * ((‖C.det‖ ^ 2 : ℝ) : ℂ)) = RCLike.re z * ‖C.det‖ ^ 2 :=
        RCLike.re_mul_ofReal z _
      _ = ‖C.det‖ ^ 2 * RCLike.re z := by ring
  rw [hre, hre]
  have hr : ‖C.det‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hdetC)
  exact mul_div_mul_left _ _ hr

/-- `relTrace` does not depend on the choice of complex linear coordinates. -/
theorem relTrace_compContinuousLinearMap (hω : ω.IsOneOne) (hα : α.IsOneOne)
    (A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n)) :
    relTrace (ω.compContinuousLinearMap
        ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ))
      (α.compContinuousLinearMap
        ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)) =
      relTrace ω α := by
  let C : Matrix (Fin n) (Fin n) ℂ := EuclideanSpace.clmMatrix A
  let D : Matrix (Fin n) (Fin n) ℂ := Cᵀ
  let B : Matrix (Fin n) (Fin n) ℂ := C.map star
  let b : Module.Basis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)) :=
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
  let Ae : EuclideanSpace ℂ (Fin n) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) := A.toLinearEquiv
  have hclm (i j : Fin n) : C i j = A (EuclideanSpace.single j 1) i := rfl
  have hC : C = LinearMap.toMatrix b b (Ae : EuclideanSpace ℂ (Fin n) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin n)) := by
    ext i j
    rw [hclm, LinearMap.toMatrix_apply]
    simp [b, Ae, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
  have hdetC : C.det ≠ 0 := by
    rw [hC, LinearMap.det_toMatrix]
    simpa only [LinearEquiv.coe_det] using (LinearEquiv.det Ae).ne_zero
  have hdetD : D.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact hdetC
  have hdetB : B.det ≠ 0 := by
    change (C.map star).det ≠ 0
    rw [show (C.map star).det = star C.det by
      simpa using ((starRingEnd ℂ).map_det C).symm]
    exact star_ne_zero.mpr hdetC
  have hDunit : IsUnit D :=
    (Matrix.isUnit_iff_isUnit_det D).mpr (isUnit_iff_ne_zero.mpr hdetD)
  have hBunit : IsUnit B :=
    (Matrix.isUnit_iff_isUnit_det B).mpr (isUnit_iff_ne_zero.mpr hdetB)
  have hωc := hω.coeffMatrix_compContinuousLinearMap
    (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
  have hαc := hα.coeffMatrix_compContinuousLinearMap
    (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
  change RCLike.re (((ω.compContinuousLinearMap
      ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)).coeffMatrix)⁻¹ *
      (α.compContinuousLinearMap
      ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)).coeffMatrix).trace =
    RCLike.re ((ω.coeffMatrix)⁻¹ * α.coeffMatrix).trace
  rw [hωc, hαc]
  have hDinv : D⁻¹ * D = 1 :=
    Matrix.nonsing_inv_mul D ((Matrix.isUnit_iff_isUnit_det D).mp hDunit)
  have hmatrix :
      (D * ω.coeffMatrix * B)⁻¹ * (D * α.coeffMatrix * B) =
        B⁻¹ * (ω.coeffMatrix⁻¹ * α.coeffMatrix) * B := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc]
    conv_lhs =>
      arg 2
      arg 2
      rw [← Matrix.mul_assoc]
    rw [hDinv]
    simp
  rw [show (Cᵀ * ω.coeffMatrix * C.map star)⁻¹ *
      (Cᵀ * α.coeffMatrix * C.map star) =
        B⁻¹ * (ω.coeffMatrix⁻¹ * α.coeffMatrix) * B by simpa [D, B] using hmatrix]
  exact congrArg RCLike.re (Matrix.trace_conj' hBunit (ω.coeffMatrix⁻¹ * α.coeffMatrix))

/-- Linearization of the Monge–Ampère ratio: `d/dt|₀ log ((α + tβ)ⁿ/ωⁿ) = tr_α β`. -/
theorem hasDerivAt_log_relDet (hω : ω.IsPositive) (hα : α.IsPositive) :
    HasDerivAt (fun t : ℝ ↦ Real.log (relDet ω (α + t • β))) (relTrace α β) 0 := by
  change HasDerivAt
    (fun t : ℝ ↦ Real.log
      (RCLike.re ((α + t • β).coeffMatrix).det / RCLike.re ω.coeffMatrix.det))
    (RCLike.re (α.coeffMatrix⁻¹ * β.coeffMatrix).trace) 0
  have hαpd : α.coeffMatrix.PosDef := (isPositive_iff.mp hα).2
  have hωpd : ω.coeffMatrix.PosDef := (isPositive_iff.mp hω).2
  have hωdet : 0 < RCLike.re ω.coeffMatrix.det :=
    (RCLike.pos_iff.mp hωpd.det_pos).1
  have hαdet : 0 < RCLike.re α.coeffMatrix.det :=
    (RCLike.pos_iff.mp hαpd.det_pos).1
  have hcoef (t : ℝ) : (α + t • β).coeffMatrix =
      α.coeffMatrix + t • β.coeffMatrix := by
    rw [coeffMatrix_add, coeffMatrix_smul]
  have hdetcont : ContinuousAt
      (fun t : ℝ ↦ RCLike.re (α.coeffMatrix + t • β.coeffMatrix).det) 0 := by
    fun_prop
  have hαdet0 : 0 < RCLike.re (α.coeffMatrix + (0 : ℝ) • β.coeffMatrix).det := by
    simpa using hαdet
  have hdetpos : ∀ᶠ t : ℝ in nhds (0 : ℝ),
      0 < RCLike.re (α.coeffMatrix + t • β.coeffMatrix).det :=
    hdetcont.eventually (isOpen_Ioi.mem_nhds hαdet0)
  have hlog := Matrix.PosDef.hasDerivAt_log_det_add_smul hαpd β.coeffMatrix
  have hlog' := hlog.sub_const (Real.log (RCLike.re ω.coeffMatrix.det))
  have heq : (fun t : ℝ ↦ Real.log
      (RCLike.re ((α + t • β).coeffMatrix).det / RCLike.re ω.coeffMatrix.det)) =ᶠ[nhds 0]
      (fun t ↦ Real.log (RCLike.re (α.coeffMatrix + t • β.coeffMatrix).det) -
        Real.log (RCLike.re ω.coeffMatrix.det)) := by
    filter_upwards [hdetpos] with t ht
    rw [hcoef t]
    exact Real.log_div (ne_of_gt ht) (ne_of_gt hωdet)
  exact hlog'.congr_of_eventuallyEq heq

/-- Along a segment, `d/ds ((α + sβ)ⁿ/ωⁿ) = (α + sβ)ⁿ/ωⁿ · tr_{α+sβ} β` wherever `α + sβ > 0`. -/
theorem hasDerivAt_relDet_add_smul (hω : ω.IsPositive) {s : ℝ}
    (hs : (α + s • β).IsPositive) :
    HasDerivAt (fun t : ℝ ↦ relDet ω (α + t • β))
      (relDet ω (α + s • β) * relTrace (α + s • β) β) s := by
  let f : ℝ → ℝ := fun t ↦ relDet ω (α + t • β)
  have hlog0 := hasDerivAt_log_relDet (ω := ω) (α := α + s • β) (β := β) hω hs
  have hshift : HasDerivAt (fun t : ℝ ↦ t - s) 1 s := by
    simpa using (hasDerivAt_id s).sub_const s
  have hlogShift := hlog0.comp_of_eq s hshift (by simp)
  have hpath (t : ℝ) : (α + s • β) + (t - s) • β = α + t • β := by
    module
  have hlog : HasDerivAt (fun t : ℝ ↦ Real.log (f t))
      (relTrace (α + s • β) β) s := by
    have hfun : (fun t : ℝ ↦ Real.log (relDet ω ((α + s • β) + (t - s) • β))) =
        (fun t ↦ Real.log (f t)) := by
      funext t
      rw [hpath]
    change HasDerivAt (fun t : ℝ ↦ Real.log (relDet ω ((α + s • β) + (t - s) • β)))
      _ s at hlogShift
    rw [hfun] at hlogShift
    simpa using hlogShift
  have hpos : 0 < f s := relDet_pos hω hs
  have hcont : ContinuousAt f s := by
    have hcoeff : ContinuousAt (fun t : ℝ ↦ (α + t • β).coeffMatrix) s := by
      have hfun : (fun t : ℝ ↦ (α + t • β).coeffMatrix) =
          (fun t ↦ α.coeffMatrix + t • β.coeffMatrix) := by
        funext t
        rw [coeffMatrix_add, coeffMatrix_smul]
      rw [hfun]
      fun_prop
    change ContinuousAt (fun t : ℝ ↦
      RCLike.re ((α + t • β).coeffMatrix.det) / RCLike.re ω.coeffMatrix.det) s
    fun_prop
  have hposNear : ∀ᶠ t in nhds s, 0 < f t :=
    hcont.eventually (isOpen_Ioi.mem_nhds hpos)
  have hexp := (hasDerivAt_exp (x := Real.log (f s))).comp s hlog
  have hval : NormedSpace.exp (Real.log (f s)) = f s := by
    rw [← Real.exp_eq_exp_ℝ, Real.exp_log hpos]
  rw [hval] at hexp
  have heq : f =ᶠ[nhds s] (fun t ↦ NormedSpace.exp (Real.log (f t))) := by
    filter_upwards [hposNear] with t ht
    rw [← Real.exp_eq_exp_ℝ]
    exact (Real.exp_log ht).symm
  exact hexp.congr_of_eventuallyEq heq

/-! ### `i ∂f ∧ ∂̄f` -/

theorem isNonneg_dWedgeDBar (ℓ : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) : (dWedgeDBar ℓ).IsNonneg := by
  refine ⟨?_, ?_⟩
  · intro u v
    change ((1 / 2 : ℝ) • ContinuousAlternatingMap.alternatizeUncurryFin
      ((ℓ.comp (Complex.I • ContinuousLinearMap.id ℝ (EuclideanSpace ℂ (Fin n)))).smulRight
        (ofSubsingleton ℝ (EuclideanSpace ℂ (Fin n)) ℝ (0 : Fin 1) ℓ)))
      ![I • u, I • v] =
      ((1 / 2 : ℝ) • ContinuousAlternatingMap.alternatizeUncurryFin
      ((ℓ.comp (Complex.I • ContinuousLinearMap.id ℝ (EuclideanSpace ℂ (Fin n)))).smulRight
        (ofSubsingleton ℝ (EuclideanSpace ℂ (Fin n)) ℝ (0 : Fin 1) ℓ))) ![u, v]
    simp [ContinuousAlternatingMap.alternatizeUncurryFin_apply, smul_smul, Fin.removeNth,
      Complex.I_mul_I]
    ring_nf
  · intro v
    change 0 ≤ ((1 / 2 : ℝ) • ContinuousAlternatingMap.alternatizeUncurryFin
      ((ℓ.comp (Complex.I • ContinuousLinearMap.id ℝ (EuclideanSpace ℂ (Fin n)))).smulRight
        (ofSubsingleton ℝ (EuclideanSpace ℂ (Fin n)) ℝ (0 : Fin 1) ℓ))) ![v, I • v]
    simp [ContinuousAlternatingMap.alternatizeUncurryFin_apply, smul_smul, Fin.removeNth,
      Complex.I_mul_I]
    nlinarith [sq_nonneg (ℓ (I • v)), sq_nonneg (ℓ v)]

/-- The coefficients of `i ∂f ∧ ∂̄f` are `fⱼ f̄ₖ` with `fⱼ = ∂f/∂zⱼ = (ℓ eⱼ - i ℓ(i eⱼ)) / 2`. -/
theorem coeffMatrix_dWedgeDBar (ℓ : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) :
    (dWedgeDBar ℓ).coeffMatrix = Matrix.vecMulVec
      (fun j ↦ ((ℓ (EuclideanSpace.single j 1) : ℂ) - I * ℓ (I • EuclideanSpace.single j 1)) / 2)
      (fun k ↦ ((ℓ (EuclideanSpace.single k 1) : ℂ) + I * ℓ (I • EuclideanSpace.single k 1)) / 2) :=
    by
  have hEval (u v : EuclideanSpace ℂ (Fin n)) :
      (dWedgeDBar ℓ) ![u, v] = (ℓ (I • u) * ℓ v - ℓ (I • v) * ℓ u) / 2 := by
    change ((1 / 2 : ℝ) • ContinuousAlternatingMap.alternatizeUncurryFin
      ((ℓ.comp (Complex.I • ContinuousLinearMap.id ℝ (EuclideanSpace ℂ (Fin n)))).smulRight
        (ofSubsingleton ℝ (EuclideanSpace ℂ (Fin n)) ℝ (0 : Fin 1) ℓ))) ![u, v] =
      (ℓ (I • u) * ℓ v - ℓ (I • v) * ℓ u) / 2
    simp [ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.removeNth]
    ring_nf
  ext j k
  change (((dWedgeDBar ℓ) ![EuclideanSpace.single j 1, I • EuclideanSpace.single k 1] : ℝ) -
      I * ((dWedgeDBar ℓ) ![EuclideanSpace.single j 1, EuclideanSpace.single k 1] : ℝ)) / 2 =
    (((ℓ (EuclideanSpace.single j 1) : ℂ) - I * ℓ (I • EuclideanSpace.single j 1)) / 2) *
      (((ℓ (EuclideanSpace.single k 1) : ℂ) + I * ℓ (I • EuclideanSpace.single k 1)) / 2)
  rw [hEval, hEval]
  rw [show I • (I • EuclideanSpace.single k 1) =
    -(EuclideanSpace.single k 1 : EuclideanSpace ℂ (Fin n)) by simp [smul_smul]]
  push_cast
  field_simp
  simp [map_neg]
  ring_nf
  simp [Complex.I_sq]

/-- `|∂f|²_ω = tr_ω (i ∂f ∧ ∂̄f)` vanishes only if `df = 0`. -/
theorem relTrace_dWedgeDBar_eq_zero_iff (hω : ω.IsPositive)
    (ℓ : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) : relTrace ω (dWedgeDBar ℓ) = 0 ↔ ℓ = 0 := by
  let z : Fin n → ℂ := fun j ↦
    ((ℓ (EuclideanSpace.single j 1) : ℂ) - I * ℓ (I • EuclideanSpace.single j 1)) / 2
  have hstar :
      (fun k ↦ ((ℓ (EuclideanSpace.single k 1) : ℂ) +
        I * ℓ (I • EuclideanSpace.single k 1)) / 2) = star z := by
    funext k
    simp [z]
  have hωA : ω.coeffMatrix.PosDef := (isPositive_iff (α := ω)).mp hω |>.2
  have hInv : (ω.coeffMatrix⁻¹).PosDef := hωA.inv
  have hTrace : relTrace ω (dWedgeDBar ℓ) =
      RCLike.re (star z ⬝ᵥ (ω.coeffMatrix⁻¹ *ᵥ z)) := by
    change RCLike.re ((ω.coeffMatrix)⁻¹ * coeffMatrix (dWedgeDBar ℓ)).trace = _
    rw [coeffMatrix_dWedgeDBar, hstar]
    have hmul : ω.coeffMatrix⁻¹ * Matrix.vecMulVec z (star z) =
        Matrix.vecMulVec (ω.coeffMatrix⁻¹ *ᵥ z) (star z) := by
      ext i j
      simp [Matrix.mul_apply, Matrix.vecMulVec, Matrix.mulVec_eq_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [hmul, Matrix.trace_vecMulVec, dotProduct_comm]
  constructor
  · intro hzero
    by_contra hℓ
    have hz : z ≠ 0 := by
      intro hz
      apply hℓ
      ext x
      have hspan (w : EuclideanSpace ℂ (Fin n)) :
          w = ∑ j, ((w j).re • EuclideanSpace.single j (1 : ℂ) +
            (w j).im • (I • EuclideanSpace.single j (1 : ℂ))) := by
        calc
          w = ∑ j, (w j) • EuclideanSpace.single j 1 := by
            simpa [EuclideanSpace.basisFun_apply] using
              (EuclideanSpace.basisFun (Fin n) ℂ).sum_repr w |>.symm
          _ = ∑ j, ((w j).re • EuclideanSpace.single j 1 +
                (w j).im • (I • EuclideanSpace.single j 1)) := by
            apply Finset.sum_congr rfl
            intro j hj
            conv_lhs => rw [← Complex.re_add_im (w j)]
            rw [add_smul, RCLike.real_smul_eq_coe_smul (K := ℂ) ((w j).re)]
            have hs : (((w j).im : ℂ) * I) • EuclideanSpace.single j (1 : ℂ) =
                (w j).im • (I • EuclideanSpace.single j (1 : ℂ)) := by
              have hc : ((w j).im : ℂ) * I = (w j).im • I :=
                (RCLike.real_smul_eq_coe_mul ((w j).im) I).symm
              rw [hc, smul_assoc]
            rw [hs]
            rfl
      have hcomponent (j : Fin n) : ℓ (EuclideanSpace.single j 1) = 0 ∧
          ℓ (I • EuclideanSpace.single j 1) = 0 := by
        have hj := congrFun hz j
        have hjre := congrArg Complex.re hj
        have hjim := congrArg Complex.im hj
        constructor
        · norm_num [z] at hjre
          linarith
        · norm_num [z] at hjim
          linarith
      rw [hspan x]
      simp [hcomponent]
    have hp := hInv.re_dotProduct_pos hz
    rw [← hTrace] at hp
    linarith
  · intro hℓ
    subst ℓ
    rw [hTrace]
    simp [z, dotProduct, Matrix.mulVec_eq_sum]

end ContinuousAlternatingMap

/-! ### Fields of `(1,1)`-forms on a complex manifold -/

namespace FormField

variable {n : ℕ} {M : Type*}

/-- A field of real `(1,1)`-forms. -/
def IsOneOne (α : FormField (EuclideanSpace ℂ (Fin n)) M 2) : Prop :=
  ∀ x, (α x).IsOneOne

/-- A field of positive `(1,1)`-forms. -/
def IsPositive (α : FormField (EuclideanSpace ℂ (Fin n)) M 2) : Prop :=
  ∀ x, (α x).IsPositive

/-- A field of semipositive `(1,1)`-forms. -/
def IsNonneg (α : FormField (EuclideanSpace ℂ (Fin n)) M 2) : Prop :=
  ∀ x, (α x).IsNonneg

theorem IsPositive.isOneOne {α : FormField (EuclideanSpace ℂ (Fin n)) M 2} (h : α.IsPositive) :
    α.IsOneOne := fun x ↦ (h x).1

end FormField
