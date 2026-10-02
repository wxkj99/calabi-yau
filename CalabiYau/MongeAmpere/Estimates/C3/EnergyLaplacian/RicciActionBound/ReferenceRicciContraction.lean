module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.Basic

/-!
# Order-zero reference Ricci coefficients

The trace of the fixed reference curvature is bounded in reference-unitary
frames. This is the order-zero contraction needed in the general-MA version
of Székelyhidi §3.3, the commutator after (3.14), printed p. 45.
No covariant derivative of Ricci is asserted here.
-/

open scoped Manifold ContDiff BigOperators

namespace KahlerForm

/-- The frame normalization supplies the inverse in the inverse-slot convention. -/
private theorem referenceRicciZero_frame_inverse {n : ℕ}
    (g : Matrix (Fin n) (Fin n) ℂ) (P : Matrix (Fin n) (Fin n) ℂ)
    (hP : P.transpose * g * P.map star = 1) :
    g⁻¹ = P.map star * P.transpose := by
  apply Matrix.inv_eq_left_inv
  have hLeft : P.map star * (P.transpose * g) = 1 := by
    exact mul_eq_one_comm.mp (by simpa only [Matrix.mul_assoc] using hP)
  simpa only [Matrix.mul_assoc] using hLeft

/-- Ricci contracts the first two curvature slots: Székelyhidi §1.4, printed p. 12.
This is only the order-zero trace, with no covariant derivative premise. -/
private theorem referenceRicciZero_frame_trace {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₀ : KahlerForm n M) (x : M)
    (P : Matrix (Fin n) (Fin n) ℂ)
    (hP : IsReferenceOrthonormalFrame ω₀ x P) (j l : Fin n) :
    c3TwoCovariantFrame P
      (c3RicciInChart (ω₀.metricInChart x)
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x)) j l =
      ∑ s, referenceCurvatureComponent ω₀ x P s s j l := by
  have hInv : (ω₀.metricInChart x
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x))⁻¹ = P.map star * P.transpose :=
    referenceRicciZero_frame_inverse _ P hP
  unfold c3TwoCovariantFrame c3RicciInChart referenceCurvatureComponent
  rw [hInv]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_lhs =>
    arg 2; intro a; arg 2; intro b; arg 2; intro c; rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; intro a; arg 2; intro b; rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; intro a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; intro a; arg 2; intro b; rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; intro a; rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; intro a; arg 2; intro b; arg 2; intro c; rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; intro a; arg 2; intro b; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x1 hx1
  apply Finset.sum_congr rfl
  intro x2 hx2
  apply Finset.sum_congr rfl
  intro x3 hx3
  apply Finset.sum_congr rfl
  intro x4 hx4
  apply Finset.sum_congr rfl
  intro x5 hx5
  ring

end KahlerForm

@[expose] public section

open scoped Manifold ContDiff

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

omit [T2Space M] in
/-- A finite bound on the reference Ricci tensor in every reference-unitary
frame, uniformly in the point. -/
theorem exists_uniform_referenceRicciZero_frame_component_bound (ω₀ : KahlerForm n M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x U,
      IsReferenceOrthonormalFrame ω₀ x U →
        ∀ j l,
          ‖c3TwoCovariantFrame U
            (c3RicciInChart (ω₀.metricInChart x)
              (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x)) j l‖ ≤ K := by
  obtain ⟨K, hK, hCurv⟩ := ω₀.exists_uniform_reference_curvature_component_bound
  refine ⟨(n : ℝ) * K, mul_nonneg (Nat.cast_nonneg n) hK, ?_⟩
  intro x U hU j l
  rw [referenceRicciZero_frame_trace ω₀ x U hU j l]
  calc
    ‖∑ s, referenceCurvatureComponent ω₀ x U s s j l‖ ≤
        ∑ s, ‖referenceCurvatureComponent ω₀ x U s s j l‖ := norm_sum_le _ _
    _ ≤ ∑ _s : Fin n, K := Finset.sum_le_sum fun s _hs => hCurv x U hU s s j l
    _ = (n : ℝ) * K := by simp

end KahlerForm
