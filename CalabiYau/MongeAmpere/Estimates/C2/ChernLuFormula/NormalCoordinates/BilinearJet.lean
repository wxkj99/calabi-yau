module

public import CalabiYau.Geometry.Kahler.Laplacian.Cofactor

/-!
# Realizing a finite symmetric quadratic jet

A symmetric array of complex coefficients specifies a symmetric complex-bilinear map on a
finite-dimensional coordinate model. Finite dimensionality makes this map continuous, so it
can be used as the quadratic part of a holomorphic polynomial chart. This is the coefficient
realization implicit in Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §1.3,
Proposition 1.16, pp. 9–10. The first argument of the array is the output coordinate, and
the remaining two are the holomorphic input coordinates. At `n = 0` both conditions are
vacuous; in dimension one the map sends `(u,v)` to the unique coefficient times `u*v`.
-/

@[expose] public section

namespace KahlerForm

/-- Turn a symmetric array of prescribed second coordinate derivatives into a continuous
symmetric complex-bilinear quadratic jet. -/
private noncomputable def continuousBilinearJet {n : ℕ}
    (C : Fin n → Fin n → Fin n → ℂ) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) →L[ℂ]
      EuclideanSpace ℂ (Fin n) := by
  classical
  let B : EuclideanSpace ℂ (Fin n) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
    { toFun := fun u =>
        { toFun := fun v => WithLp.toLp 2 (fun a => ∑ p : Fin n, ∑ j : Fin n,
            C a p j * u p * v j)
          map_add' := by
            intro v w
            ext a
            change (∑ p : Fin n, ∑ j : Fin n, C a p j * u p * (v j + w j)) =
              (∑ p : Fin n, ∑ j : Fin n, C a p j * u p * v j) +
                ∑ p : Fin n, ∑ j : Fin n, C a p j * u p * w j
            simp_rw [mul_add]
            simp only [Finset.sum_add_distrib]
          map_smul' := by
            intro z v
            ext a
            change (∑ p : Fin n, ∑ j : Fin n, C a p j * u p * (z * v j)) =
              z * ∑ p : Fin n, ∑ j : Fin n, C a p j * u p * v j
            simp_rw [mul_assoc]
            simp_rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro p hp
            apply Finset.sum_congr rfl
            intro j hj
            ring }
      map_add' := by
        intro u v
        ext w a
        change (∑ p : Fin n, ∑ j : Fin n, C a p j * (u p + v p) * w j) =
          (∑ p : Fin n, ∑ j : Fin n, C a p j * u p * w j) +
            ∑ p : Fin n, ∑ j : Fin n, C a p j * v p * w j
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro p hp
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      map_smul' := by
        intro z u
        ext v a
        change (∑ p : Fin n, ∑ j : Fin n, C a p j * (z * u p) * v j) =
          z * ∑ p : Fin n, ∑ j : Fin n, C a p j * u p * v j
        simp_rw [mul_assoc]
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro j hj
        ring }
  let B1 : EuclideanSpace ℂ (Fin n) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    { toFun := fun u => LinearMap.toContinuousLinearMap (B u)
      map_add' := by
        intro u v
        ext w a
        change (∑ p : Fin n, ∑ j : Fin n, C a p j * (u p + v p) * w j) =
          (∑ p : Fin n, ∑ j : Fin n, C a p j * u p * w j) +
            ∑ p : Fin n, ∑ j : Fin n, C a p j * v p * w j
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro p hp
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      map_smul' := by
        intro z u
        ext v a
        change (∑ p : Fin n, ∑ j : Fin n, C a p j * (z * u p) * v j) =
          z * ∑ p : Fin n, ∑ j : Fin n, C a p j * u p * v j
        simp_rw [mul_assoc]
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro j hj
        ring }
  exact LinearMap.toContinuousLinearMap B1

private theorem continuousBilinearJet_apply {n : ℕ}
    (C : Fin n → Fin n → Fin n → ℂ) (u v : EuclideanSpace ℂ (Fin n)) :
    continuousBilinearJet C u v = WithLp.toLp 2 (fun a =>
      ∑ p : Fin n, ∑ j : Fin n, C a p j * u p * v j) := rfl

theorem exists_continuous_symmetric_bilinear_jet {n : ℕ}
    (C : Fin n → Fin n → Fin n → ℂ)
    (hC : ∀ a p j, C a p j = C a j p) :
    ∃ Q : EuclideanSpace ℂ (Fin n) →L[ℂ]
        EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n),
      (∀ u v, Q u v = Q v u) ∧
      ∀ p j a, Q (EuclideanSpace.single p 1) (EuclideanSpace.single j 1) a = C a p j := by
  refine ⟨continuousBilinearJet C, ?_, ?_⟩
  · intro u v
    ext a
    rw [continuousBilinearJet_apply, continuousBilinearJet_apply]
    change (∑ p : Fin n, ∑ j : Fin n, C a p j * u p * v j) =
      ∑ p : Fin n, ∑ j : Fin n, C a p j * v p * u j
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro j hj
    rw [hC a p j]
    ring
  · intro p j a
    rw [continuousBilinearJet_apply]
    simp

end KahlerForm
