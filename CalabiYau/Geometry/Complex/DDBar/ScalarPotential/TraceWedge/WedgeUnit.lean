module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import CalabiYau.Geometry.Manifold.Tensor.Alternating.Wedge

/-!
# Degree-zero right unit for the normalized alternating wedge

The exterior-algebra unit identity `α ∧ 1 = α` holds for the real continuous
alternating forms used by the scalar trace–wedge route. The project's wedge is
normalized by factorials; its alternatization formula cancels the degree-`k`
factorial even when `k = 2`, as in the complex-dimension-one application.

Source: upstream `ContinuousAlternatingMap.wedge_product_eq_alternatization`
in `CalabiYau.Geometry.Manifold.Tensor.Alternating.Wedge` and Mathlib's
`AlternatingMap.coe_alternatization` in `LinearAlgebra.Alternating.Basic`.
-/

@[expose] public section

namespace ContinuousAlternatingMap

/-- Right wedging with the normalized degree-zero scalar form one changes no form. -/
theorem wedge_right_unit {n k : ℕ}
    (α : EuclideanSpace ℂ (Fin n) [⋀^Fin k]→L[ℝ] ℝ) :
    (α ∧[ℝ] constOfIsEmpty ℝ (EuclideanSpace ℂ (Fin n)) (Fin 0) (1 : ℝ)) = α := by
  have hten :
      (tensorProductMap α
        (constOfIsEmpty ℝ (EuclideanSpace ℂ (Fin n)) (Fin 0) (1 : ℝ))
        (ContinuousLinearMap.mul ℝ ℝ)).toMultilinearMap =
        α.toAlternatingMap.toMultilinearMap := by
    ext v
    change (tensorProductMap α
      (constOfIsEmpty ℝ (EuclideanSpace ℂ (Fin n)) (Fin 0) (1 : ℝ))
      (ContinuousLinearMap.mul ℝ ℝ)) v = α v
    rw [tensorProductMap_apply]
    simp
  ext v
  rw [wedge_product_eq_alternatization, hten]
  rw [AlternatingMap.coe_alternatization]
  simp only [Fintype.card_fin, Nat.factorial_zero, mul_one,
    AlternatingMap.smul_apply]
  have hf : (↑k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  simpa [Nat.add_zero, smul_eq_mul] using (inv_smul_smul₀ hf (α v))

end ContinuousAlternatingMap
