module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.Basic

/-!
# Raising Ricci indices in a normalized frame

The exact index conversion for the Ricci commutator in Székelyhidi §3.3,
following (3.14), printed p. 45. This concerns the actual chart Ricci tensor:
normalizing a frame does not replace the metric function by a constant.
The normalization equation itself implies the needed matrix invertibility.
The endomorphism definition raises the Ricci tensor's antiholomorphic index;
its output is therefore the transpose of the covariant frame matrix.
-/

@[expose] public section

namespace KahlerForm

open scoped BigOperators

/-- With the existing inverse-index convention, the covariant frame entries
are transposed, not conjugated. -/
theorem c3RicciEndomorphism_normalizedFrame_apply {n : ℕ}
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (P : Matrix (Fin n) (Fin n) ℂ)
    (hP : P.transpose * g z * P.map star = 1) (i j : Fin n) :
    (P⁻¹ * Matrix.of (c3RicciEndomorphism g z) * P) i j =
      c3TwoCovariantFrame P (c3RicciInChart g z) j i := by
  have hInv : (g z)⁻¹ = P.map star * P.transpose := by
    apply Matrix.inv_eq_left_inv
    have hreverse : P.map star * (P.transpose * g z) = 1 :=
      mul_eq_one_comm.mp hP
    simpa only [Matrix.mul_assoc] using hreverse
  have hPinv : P⁻¹ * P = 1 := by
    have ht : (P.map star).transpose * (g z).transpose * P = 1 := by
      have h := congrArg Matrix.transpose hP
      simpa only [Matrix.transpose_mul, Matrix.transpose_transpose,
        Matrix.transpose_one, Matrix.mul_assoc] using h
    exact Matrix.nonsing_inv_mul P (Matrix.isUnit_det_of_left_inverse ht)
  have hCov (Q : Matrix (Fin n) (Fin n) ℂ) :
      Matrix.of (c3TwoCovariantFrame P Q) = P.transpose * Q * P.map star := by
    ext a b
    change (∑ c, ∑ d, P c a * star (P d b) * Q c d) = _
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro d hd
    ring
  have hE : Matrix.of (c3RicciEndomorphism g z) =
      (g z)⁻¹.transpose * Matrix.transpose (Matrix.of (c3RicciInChart g z)) := by
    ext a b
    rfl
  have hFrame : P⁻¹ * Matrix.of (c3RicciEndomorphism g z) * P =
      Matrix.transpose (Matrix.of (c3TwoCovariantFrame P (Matrix.of (c3RicciInChart g z)))) := by
    rw [hE, hInv, Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [hCov (Matrix.of (c3RicciInChart g z)), Matrix.transpose_mul,
      Matrix.transpose_mul, Matrix.transpose_transpose]
    calc
      P⁻¹ * (P * (P.map star).transpose * Matrix.transpose (Matrix.of (c3RicciInChart g z))) * P =
          (P⁻¹ * P) * (P.map star).transpose * Matrix.transpose (Matrix.of (c3RicciInChart g z)) * P := by
        noncomm_ring
      _ = (P.map star).transpose * (Matrix.transpose (Matrix.of (c3RicciInChart g z)) * P) := by
        rw [hPinv]
        simp only [Matrix.one_mul, Matrix.mul_assoc]
  rw [hFrame]
  rfl

end KahlerForm
