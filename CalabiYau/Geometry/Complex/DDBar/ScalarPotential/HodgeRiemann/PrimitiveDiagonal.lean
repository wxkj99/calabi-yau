module

public import CalabiYau.Geometry.Complex.Forms.OneOne
import CalabiYau.Mathlib.Analysis.Matrix.Hermitian.SimultaneousDiagonalization

/-!
# Pointwise simultaneous normal frame for real `(1,1)`-forms

A positive real `(1,1)`-form `ω` and a real `(1,1)`-form `γ` admit a common complex
frame in which the coefficient matrix of `ω` is the identity and that of `γ`
is diagonal with real entries. The change of frame is a continuous *equivalence*,
not necessarily an isometry of the ambient Euclidean metric. The primitive
condition is deliberately absent: the parent separately obtains `∑ i, d i = 0`
from `relTrace ω γ = 0` by trace invariance.

The coefficient convention of `Forms.OneOne` has pullback matrix
`Cᵀ * B * C.map star`, so the matrix-congruence witness `Pᴴ * B * P` uses
`C = P.map star`. This also fixes the factors of two: `γ(e_j,I e_k) =
2 * (coeffMatrix γ j k).re`.

References: Horn–Johnson, *Matrix Analysis*, 2nd ed., Theorem 7.6.4;
Ballmann, *Lectures on Kähler Manifolds*, §5.2, Theorem 5.42.
-/

@[expose] public section

open Complex Matrix

namespace ContinuousAlternatingMap

private noncomputable def complexFrameMap {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  (Matrix.toEuclideanLin (P.map star)).toContinuousLinearMap

private theorem complexFrameMap_isUnit {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ)
    (hP : IsUnit P) : IsUnit (P.map star) := by
  simpa using hP.map ((starRingEnd ℂ).mapMatrix (m := Fin n))

private noncomputable def complexFrameEquiv {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ)
    (hP : IsUnit P) :
    EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n) := by
  classical
  let C : Matrix (Fin n) (Fin n) ℂ := P.map star
  have hC : IsUnit C := complexFrameMap_isUnit P hP
  have hd : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp hC
  exact (Matrix.toLinOfInv
      (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
      (Matrix.mul_nonsing_inv C hd) (Matrix.nonsing_inv_mul C hd)).toContinuousLinearEquiv

private theorem complexFrameEquiv_toContinuousLinearMap {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) :
    (complexFrameEquiv P hP).toContinuousLinearMap = complexFrameMap P := by
  rfl

private theorem complexFrameMap_matrix {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) :
    EuclideanSpace.clmMatrix (complexFrameMap P) = P.map star := by
  ext i j
  simp [EuclideanSpace.clmMatrix, complexFrameMap, Matrix.toLpLin_apply,
    EuclideanSpace.single]

private theorem complexFrameMap_congr {n : ℕ}
    {γ : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ}
    (hγ : γ.IsOneOne) (P : Matrix (Fin n) (Fin n) ℂ) :
    (γ.compContinuousLinearMap ((complexFrameMap P).restrictScalars ℝ)).coeffMatrix =
      Pᴴ * γ.coeffMatrix * P := by
  rw [hγ.coeffMatrix_compContinuousLinearMap, complexFrameMap_matrix]
  have hct : (P.map star)ᵀ = Pᴴ := by
    ext i j
    simp [Matrix.conjTranspose]
  have hmap : (P.map star).map star = P := by
    ext i j
    simp
  rw [hct, hmap]

private theorem exists_normalFrame_diagonal {n : ℕ}
    (ω γ : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (hω : ω.IsPositive) (hγ : γ.IsOneOne) :
    ∃ (P : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ),
      Pᴴ * ω.coeffMatrix * P = 1 ∧
      (ω.compContinuousLinearMap ((complexFrameMap P).restrictScalars ℝ)).coeffMatrix = 1 ∧
      (γ.compContinuousLinearMap ((complexFrameMap P).restrictScalars ℝ)).coeffMatrix =
        Matrix.diagonal ((↑) ∘ d : Fin n → ℂ) := by
  obtain ⟨P, d, hPω, hPγ⟩ :=
    ((ContinuousAlternatingMap.isPositive_iff.mp hω).2).exists_simultaneous_diagonalization
      hγ.isHermitian_coeffMatrix
  refine ⟨P, d, hPω, ?_, ?_⟩
  · simpa [complexFrameMap_congr hω.1 P] using hPω
  · simpa [complexFrameMap_congr hγ P] using hPγ

/-- A positive real `(1,1)`-form and a real `(1,1)`-form admit a common normal
frame. Its complex linear equivalence preserves the positive form's metric, not
necessarily the standard Euclidean metric. No primitive trace hypothesis is
needed for diagonalization itself. -/
theorem exists_normalFrame_diagonal_equiv {n : ℕ}
    (ω γ : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (hω : ω.IsPositive) (hγ : γ.IsOneOne) :
    ∃ (A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n))
      (d : Fin n → ℝ),
      (ω.compContinuousLinearMap (A.toContinuousLinearMap.restrictScalars ℝ)).coeffMatrix = 1 ∧
      (γ.compContinuousLinearMap (A.toContinuousLinearMap.restrictScalars ℝ)).coeffMatrix =
        Matrix.diagonal (fun i => (d i : ℂ)) := by
  obtain ⟨P, d, hPω, hωDiag, hγDiag⟩ := exists_normalFrame_diagonal ω γ hω hγ
  have hP : IsUnit P :=
    @isUnit_of_invertible _ _ P
      (invertibleOfLeftInverse P (Pᴴ * ω.coeffMatrix) hPω)
  refine ⟨complexFrameEquiv P hP, d, ?_, ?_⟩
  · simpa only [complexFrameEquiv_toContinuousLinearMap] using hωDiag
  · rw [complexFrameEquiv_toContinuousLinearMap]
    convert hγDiag using 1
    ext i j
    simp [Matrix.diagonal_apply]

end ContinuousAlternatingMap
