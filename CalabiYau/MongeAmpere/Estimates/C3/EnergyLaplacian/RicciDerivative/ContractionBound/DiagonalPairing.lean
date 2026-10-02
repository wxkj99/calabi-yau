module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.Basic
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.ContractionBound.MetricFrame
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.ContractionBound.DiagonalWeights

/-!
# DiagonalPairing for the differentiated Ricci contraction

Székelyhidi, An Introduction to Extremal Kähler Metrics, §3.3, proof of
Lemma 3.9, printed pp. 44–45: two-sided metric comparison and the
linear-plus-quadratic connection correction.

The diagonal frame gives a three-slot weight `d_i/(d_j*d_k)`, which is `1/d` when `n = 1`. The unweighted energy and Hilbert norm identities introduce no real-versus-complex Laplacian factor.
-/

public section

open scoped Manifold ContDiff BigOperators ComplexOrder MatrixOrder
open ContinuousAlternatingMap
open Matrix

namespace KahlerForm

/-- In a simultaneous diagonal frame, the perturbed-metric tensor pairing is
exactly the weighted finite component energy, with one metric factor upstairs
and two downstairs. -/
theorem c3_pair_diagonal_metric_eq_weighted_sum {n : ℕ}
    (d : Fin n → ℝ) (T : Fin n → Fin n → Fin n → ℂ)
    (hd : ∀ i, 0 < d i) :
    (c3Pair (fun _ : EuclideanSpace ℂ (Fin n) ↦
      Matrix.diagonal (fun i ↦ (d i : ℂ))) (0 : EuclideanSpace ℂ (Fin n)) T T).re =
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (d i / (d j * d k)) * ‖T i j k‖ ^ 2 := by
  have hInv : (Matrix.diagonal (fun i : Fin n ↦ (d i : ℂ)))⁻¹ =
      Matrix.diagonal (fun i : Fin n ↦ ((d i)⁻¹ : ℂ)) := by
    have hu : IsUnit (fun i : Fin n ↦ (d i : ℂ)) := by
      rw [Pi.isUnit_iff]
      intro i
      exact isUnit_iff_ne_zero.mpr (by exact_mod_cast ne_of_gt (hd i))
    have hfun : Ring.inverse (fun i : Fin n ↦ (d i : ℂ)) =
        (fun i : Fin n ↦ ((d i)⁻¹ : ℂ)) := by
      funext i
      rw [Ring.inverse_of_isUnit hu]
      simp [IsUnit.val_inv_apply hu i]
    rw [Matrix.inv_diagonal]
    ext i j
    simp [Matrix.diagonal_apply, hfun]
  classical
  rw [c3Pair]
  simp_rw [hInv]
  simp [Matrix.diagonal_apply, Complex.normSq_apply, ← Complex.normSq_eq_norm_sq,
    div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  field_simp [ne_of_gt (hd i), ne_of_gt (hd j), ne_of_gt (hd k)]

/-- In a simultaneous diagonal frame, the full tensor pairing is exactly its
abstract weighted component pairing. -/
theorem c3_pair_diagonal_metric_eq_weighted_pairing {n : ℕ}
    (d : Fin n → ℝ) (T U : Fin n → Fin n → Fin n → ℂ)
    (hd : ∀ i, 0 < d i) :
    c3Pair (fun _ : EuclideanSpace ℂ (Fin n) ↦
      Matrix.diagonal (fun i ↦ (d i : ℂ))) (0 : EuclideanSpace ℂ (Fin n)) T U =
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (d i / (d j * d k) : ℂ) * T i j k * star (U i j k) := by
  have hInv : (Matrix.diagonal (fun i : Fin n ↦ (d i : ℂ)))⁻¹ =
      Matrix.diagonal (fun i : Fin n ↦ ((d i)⁻¹ : ℂ)) := by
    have hu : IsUnit (fun i : Fin n ↦ (d i : ℂ)) := by
      rw [Pi.isUnit_iff]
      intro i
      exact isUnit_iff_ne_zero.mpr (by exact_mod_cast ne_of_gt (hd i))
    have hfun : Ring.inverse (fun i : Fin n ↦ (d i : ℂ)) =
        (fun i : Fin n ↦ ((d i)⁻¹ : ℂ)) := by
      funext i
      rw [Ring.inverse_of_isUnit hu]
      simp [IsUnit.val_inv_apply hu i]
    rw [Matrix.inv_diagonal]
    ext i j
    simp [Matrix.diagonal_apply, hfun]
  classical
  rw [c3Pair]
  simp_rw [hInv]
  simp [Matrix.diagonal_apply, div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  field_simp [ne_of_gt (hd i), ne_of_gt (hd j), ne_of_gt (hd k)]

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

end KahlerForm
