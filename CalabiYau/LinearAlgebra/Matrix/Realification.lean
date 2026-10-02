module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Data.Matrix.Composition
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity

/-!
# Realification of complex matrices

A complex `m × n` matrix `M` acts `ℝ`-linearly on `n → ℂ ≅ (n × Fin 2) → ℝ`, where `z ∈ ℂ` has real
coordinates `(re z, im z)` in the basis `Complex.basisOneI = ![1, I]`. Its matrix is
`Matrix.realify M : Matrix (m × Fin 2) (n × Fin 2) ℝ`, which replaces each entry `z = x + i y` by
the block `!![x, -y; y, x]`.

On a Hermitian vector space `ℂⁿ` with Hermitian form `h(v, w) = vᴴ M w`, the real inner product is
`g = Re h`, and its Gram matrix in the real basis `(e₁, i e₁, …, eₙ, i eₙ)` is `M.realify`.
Thus this file is the coordinate form of the correspondence between Hermitian metrics and
`J`-invariant Riemannian metrics:

* `Matrix.IsHermitian.isSymm_realify`, `Matrix.posDef_realify_iff`: `M` is Hermitian (positive
  definite) iff `g` is symmetric (positive definite);
* `Matrix.det_realify`, `Matrix.IsHermitian.det_realify`: `det_ℝ M.realify = |det M|²`, which is
  `(det M)²` for Hermitian `M` (volume forms: `√(det g) = det h`);
* `Matrix.realify_I_smul_one`, `Matrix.exists_realify_eq_iff_commute`: the complex structure is
  `J = 1 ⊗ₖ !![0, -1; 1, 0]`, and a real matrix is the realification of a complex one iff it
  commutes with `J`.

The abstract (basis-free) form of `g = Re h` is `InnerProductSpace.rclikeToReal` and
`real_inner_eq_re_inner` in Mathlib.

## Main definitions

* `Matrix.realify`: the realification of a complex matrix.

## References

* D. Huybrechts, *Complex Geometry*, §1.2 (linear algebra of complex structures and Hermitian
  forms).
-/

public section

open scoped Kronecker ComplexOrder

namespace Matrix

variable {l m n : Type*}

/-- The realification of a complex matrix: its matrix as an `ℝ`-linear map, with respect to the
real bases `(eᵢ, I • eᵢ)`. Each entry `z` becomes the `2 × 2` block
`!![re z, -im z; im z, re z]`. -/
noncomputable def realify (M : Matrix m n ℂ) : Matrix (m × Fin 2) (n × Fin 2) ℝ :=
  comp m n (Fin 2) (Fin 2) ℝ (M.map (Algebra.leftMulMatrix Complex.basisOneI))

theorem realify_apply (M : Matrix m n ℂ) (i : m) (a : Fin 2) (j : n) (b : Fin 2) :
    M.realify (i, a) (j, b) = !![(M i j).re, -(M i j).im; (M i j).im, (M i j).re] a b := by
  simp only [realify, comp_apply, map_apply, Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply,
    Complex.coe_basisOneI, Complex.coe_basisOneI_repr, Algebra.coe_lmul_eq_mul,
    LinearMap.mul_apply']
  fin_cases a <;> fin_cases b <;> simp

/-- `realify M` is the matrix of `M`, viewed as an `ℝ`-linear map, in the basis
`Complex.basisOneI.smulTower' (Pi.basisFun ℂ n)`. -/
theorem toMatrix_restrictScalars_toLin' [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) :
    LinearMap.toMatrix (Complex.basisOneI.smulTower' (Pi.basisFun ℂ n))
        (Complex.basisOneI.smulTower' (Pi.basisFun ℂ n))
        ((Matrix.toLin' M).restrictScalars ℝ) = M.realify := by
  rw [LinearMap.restrictScalars_toMatrix, LinearMap.toMatrix_eq_toMatrix',
    LinearMap.toMatrix'_toLin']
  rfl

@[simp]
theorem realify_mul [Fintype m] (M : Matrix l m ℂ) (N : Matrix m n ℂ) :
    (M * N).realify = M.realify * N.realify := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [realify_apply, mul_apply, Fintype.sum_prod_type, Complex.re_sum, Complex.im_sum,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib] <;> ring

@[simp]
theorem realify_one [DecidableEq n] : (1 : Matrix n n ℂ).realify = 1 := by
  ext ⟨i, a⟩ ⟨j, b⟩
  by_cases h : i = j <;> fin_cases a <;> fin_cases b <;> simp [realify_apply, one_apply, h]

@[simp]
theorem realify_add (M N : Matrix m n ℂ) : (M + N).realify = M.realify + N.realify := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases a <;> fin_cases b <;> simp [realify_apply, add_comm]

@[simp]
theorem realify_smul (c : ℝ) (M : Matrix m n ℂ) : (c • M).realify = c • M.realify := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases a <;> fin_cases b <;> simp [realify_apply]

@[simp]
theorem realify_conjTranspose (M : Matrix m n ℂ) : Mᴴ.realify = M.realifyᵀ := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases a <;> fin_cases b <;> simp [realify_apply]

@[simp]
theorem trace_realify [Fintype n] (M : Matrix n n ℂ) : M.realify.trace = 2 * M.trace.re := by
  simp [trace, Fintype.sum_prod_type, realify_apply, Complex.re_sum, Finset.mul_sum, two_mul]

/-- `det_ℝ (realify M) = |det M|²`. -/
@[simp]
theorem det_realify [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) :
    M.realify.det = Complex.normSq M.det := by
  rw [← toMatrix_restrictScalars_toLin', LinearMap.det_toMatrix, LinearMap.det_restrictScalars,
    LinearMap.det_toLin', Algebra.norm_complex_apply]

/-- The realification of a Hermitian matrix is symmetric. -/
theorem IsHermitian.isSymm_realify {M : Matrix n n ℂ} (hM : M.IsHermitian) : M.realify.IsSymm := by
  rw [IsSymm, ← realify_conjTranspose, hM.eq]

/-- The real quadratic form of `realify M` at the real coordinates `(re v, im v)` of `v` is
`re (vᴴ M v)`. -/
theorem dotProduct_realify_mulVec [Fintype n] (M : Matrix n n ℂ) (v : n → ℂ) :
    (fun p : n × Fin 2 ↦ Complex.basisOneI.repr (v p.1) p.2) ⬝ᵥ
        (M.realify *ᵥ fun p : n × Fin 2 ↦ Complex.basisOneI.repr (v p.1) p.2) =
      (star v ⬝ᵥ (M *ᵥ v)).re := by
  simp only [dotProduct, mulVec, Fintype.sum_prod_type, Fin.sum_univ_two, realify_apply,
    Finset.mul_sum, Complex.re_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp [Complex.mul_re, Complex.mul_im]
  ring

@[simp]
theorem posDef_realify_iff [Fintype n] {M : Matrix n n ℂ} :
    M.realify.PosDef ↔ M.PosDef := by
  rw [posDef_iff_dotProduct_mulVec, posDef_iff_dotProduct_mulVec]
  constructor
  · rintro ⟨hR, hpos⟩
    have hinj : Function.Injective (fun A : Matrix n n ℂ => A.realify) := by
      intro A B h
      ext i j
      apply Complex.ext
      · have hh := congrArg (fun T : Matrix (n × Fin 2) (n × Fin 2) ℝ => T (i, 0) (j, 0)) h
        simpa [realify_apply] using hh
      · have hh := congrArg (fun T : Matrix (n × Fin 2) (n × Fin 2) ℝ => T (i, 1) (j, 0)) h
        simpa [realify_apply] using hh
    have hM : M.IsHermitian := by
      change Mᴴ = M
      apply hinj
      change Mᴴ.realify = M.realify
      have hs : M.realifyᵀ = M.realify := by
        simpa [IsHermitian, star_eq_conjTranspose] using hR.eq
      rw [realify_conjTranspose]
      exact hs
    refine ⟨hM, ?_⟩
    intro v hv
    let x : n × Fin 2 → ℝ := fun p => Complex.basisOneI.repr (v p.1) p.2
    have hx : x ≠ 0 := by
      intro hx0
      apply hv
      funext i
      apply Complex.ext
      · have hh := congrFun hx0 (i, 0)
        simpa [x] using hh
      · have hh := congrFun hx0 (i, 1)
        simpa [x] using hh
    have hval := hpos hx
    simp only [star_trivial] at hval
    rw [dotProduct_realify_mulVec] at hval
    exact Complex.pos_iff.mpr ⟨hval, (hM.im_star_dotProduct_mulVec_self v).symm⟩
  · rintro ⟨hM, hpos⟩
    refine ⟨IsHermitian.isSymm_realify hM, ?_⟩
    intro x hx
    let v : n → ℂ := fun i => (x (i, 0) : ℂ) + (x (i, 1) : ℂ) * Complex.I
    have hv : v ≠ 0 := by
      intro hv0
      apply hx
      funext p
      rcases p with ⟨i, a⟩
      fin_cases a
      · have hh := congrFun hv0 i
        simpa [v] using congrArg Complex.re hh
      · have hh := congrFun hv0 i
        simpa [v] using congrArg Complex.im hh
    have hval := hpos hv
    have hcoords : (fun p : n × Fin 2 => Complex.basisOneI.repr (v p.1) p.2) = x := by
      funext p
      rcases p with ⟨i, a⟩
      fin_cases a <;> simp [v, Complex.coe_basisOneI_repr]
    rw [← hcoords]
    simp only [star_trivial]
    rw [dotProduct_realify_mulVec]
    exact (Complex.pos_iff.mp hval).1

end Matrix
