module

public import CalabiYau.Geometry.Manifold.DifferentialForm.Pullback
public import Mathlib.LinearAlgebra.Determinant

/-!
# Coefficient of a top form under a coordinate derivative

Lee, *Introduction to Smooth Manifolds*, 2nd ed., §16, change of
coordinates for top-degree forms. The operation `compContinuousLinearMap`
is precisely the pointwise operation in `CalabiYau.DifferentialForm.pullback_apply`.
The ordered `Fin n` basis fixes the sign, including in dimension zero.
No absolute value is permitted in the alternating coefficient identity.
-/

@[expose] public section

namespace ContinuousAlternatingMap

/-- At a point of a smooth coordinate transition, pulling back a top form
multiplies its coefficient in the ordered standard basis by the **signed**
determinant of the derivative. This is valid also for `n = 0`. -/
theorem compContinuousLinearMap_apply_standardBasis
    {n : ℕ} (ω : (Fin n → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    (ω.compContinuousLinearMap A) (fun i : Fin n => Pi.single i (1 : ℝ)) =
      A.det * ω (fun i : Fin n => Pi.single i (1 : ℝ)) := by
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  let b : Module.Basis (Fin n) ℝ (Fin n → ℝ) := Pi.basisFun ℝ (Fin n)
  have hb (i : Fin n) : b i = Pi.single i (1 : ℝ) := by
    simp [b, Pi.basisFun_apply]
  have hstd : (fun i : Fin n => Pi.single i (1 : ℝ)) = b := by
    funext i
    exact (hb i).symm
  have hω := congrArg (fun f : (Fin n → ℝ) [⋀^Fin n]→ₗ[ℝ] ℝ => f (A ∘ b))
    (ω.toAlternatingMap.eq_smul_basis_det b)
  have hdet : b.det (A.toLinearMap ∘ b) = A.det := by
    rw [Module.Basis.det_comp, Module.Basis.det_self, mul_one]
  change ω.toAlternatingMap (A ∘ (fun i : Fin n => Pi.single i (1 : ℝ))) =
    A.det * ω.toAlternatingMap (fun i : Fin n => Pi.single i (1 : ℝ))
  rw [hstd]
  rw [hω]
  simp only [AlternatingMap.smul_apply]
  rw [show b.det (A ∘ b) = A.det by simpa using hdet]
  ring

end ContinuousAlternatingMap
