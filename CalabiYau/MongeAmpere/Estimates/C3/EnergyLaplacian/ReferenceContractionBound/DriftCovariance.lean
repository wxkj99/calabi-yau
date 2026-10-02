module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceContractionBound.LinearCovariance
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceContractionBound.ActionCovariance
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceContractionBound.RaisedCurvature
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceContractionBound.Diagonal
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceContractionBound.Energy

/-!
# Covariance of the complete reference drift

Székelyhidi, §3.3, Lemma 3.9 proof, terms following (3.15), printed p. 45.
The reference inverse raises the last raw curvature slot. The perturbed
inverse contracts the derivative slot. The action signs are +, −, −.
-/

@[expose] public section

open scoped BigOperators

namespace KahlerForm

/-- Both the fixed derivative and the three connection corrections transform
into the same diagonal-frame drift; no curvature symmetry is used. -/
theorem referenceContraction_drift_frame {n : ℕ}
    (P Q G₀ G : Matrix (Fin n) (Fin n) ℂ)
    (X : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ)
    (R : Fin n → Fin n → Fin n → Fin n → ℂ)
    (T : Fin n → Fin n → Fin n → ℂ) (d : Fin n → ℝ)
    (hd : ∀ i, 0 < d i) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hframe : linearPullbackMetric P G₀ = 1)
    (hdiag : linearPullbackMetric P G = Matrix.diagonal (fun i ↦ (d i : ℂ))) :
    referenceContractionTensorFrameTransform Q P
      (fun i j k => linearReferenceDrift G₀ G X i j k +
        referenceAction_contract G⁻¹ T (fun a b c e => ∑ l, G₀⁻¹ l a * R b e c l) i j k) =
      referenceContractionDiagonalDrift d
        (referenceContractionFiveSlotTransform P X)
        (referenceContractionFourSlotTransform P R)
        (referenceContractionTensorFrameTransform Q P T) := by
  classical
  let U := fun a b c e => ∑ l, G₀⁻¹ l a * R b e c l
  have hU : referenceAction_tauU P Q U =
      (fun i j k q => referenceContractionFourSlotTransform P R j q k i) := by
    funext i j k q
    exact referenceContraction_raised_frame P Q G₀ R hPQ hQP hframe i j k q
  have hmetric := linear_pullback_first_contraction P Q G hPQ hQP
  funext i j k
  change linearPullbackThreeTensor P Q
    (fun a b c => linearReferenceDrift G₀ G X a b c +
      referenceAction_contract G⁻¹ T U a b c) i j k = _
  have hadd (F H : Fin n → Fin n → Fin n → ℂ) :
      linearPullbackThreeTensor P Q (fun a b c => F a b c + H a b c) i j k =
        linearPullbackThreeTensor P Q F i j k +
          linearPullbackThreeTensor P Q H i j k := by
    simp only [linearPullbackThreeTensor, mul_add, Finset.sum_add_distrib]
  rw [hadd, linearReferenceDrift_pullback_covariant P Q G₀ G X hPQ hQP i j k]
  have ha := referenceAction_action_covariance P Q G⁻¹
    (linearPullbackMetric P G)⁻¹ T U hPQ hmetric i j k
  change referenceAction_tauT P Q (referenceAction_contract G⁻¹ T U) i j k = _ at ha
  change linearReferenceDrift (linearPullbackMetric P G₀) (linearPullbackMetric P G)
    (linearPullbackFiveTensor P X) i j k +
    referenceAction_tauT P Q (referenceAction_contract G⁻¹ T U) i j k = _
  rw [ha, hU, hframe, hdiag]
  simp only [linearReferenceDrift, inv_one, c3_diagonal_inverse d hd,
    Matrix.diagonal_apply, Matrix.one_apply, linearPullbackFiveTensor,
    referenceAction_contract, referenceAction_tauT, referenceContractionDiagonalDrift,
    referenceContractionFiveSlotTransform, referenceContractionTensorFrameTransform]
  simp only [ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, mul_one]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

end KahlerForm
