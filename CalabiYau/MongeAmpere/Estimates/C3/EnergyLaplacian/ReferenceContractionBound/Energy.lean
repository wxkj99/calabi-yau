module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceContractionBound.Pairing

/-!
# Energy for the reference-curvature contraction

Székelyhidi, An Introduction to Extremal Kähler Metrics, §3.3, proof of Lemma 3.9, terms following (3.15), printed p. 45; finite tensor contraction algebra implementing that proof.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal BigOperators ComplexOrder MatrixOrder
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

theorem c3_diagonal_inverse {n : ℕ} (d : Fin n → ℝ)
    (hd : ∀ i, 0 < d i) :
    (Matrix.diagonal (fun i ↦ (d i : ℂ)))⁻¹ =
      Matrix.diagonal (fun i ↦ ((d i)⁻¹ : ℂ)) := by
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

theorem c3_metric_frame_factorizations {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (P Q : Matrix (Fin n) (Fin n) ℂ)
    (d : Fin n → ℝ) (hd : ∀ i, 0 < d i)
    (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hdiag : c3PullbackMetric P G = Matrix.diagonal (fun i ↦ (d i : ℂ))) :
    (∀ i a, G i a = ∑ r,
      ((Real.sqrt (d r) : ℝ) : ℂ) * Q r i *
        star (((Real.sqrt (d r) : ℝ) : ℂ) * Q r a)) ∧
    (∀ b j, G⁻¹ b j = ∑ r,
      (((Real.sqrt (d r))⁻¹ : ℝ) : ℂ) * P j r *
        star ((((Real.sqrt (d r))⁻¹ : ℝ) : ℂ) * P b r)) := by
  have htranspose : Q.transpose * P.transpose = 1 := by
    rw [← Matrix.transpose_mul, hPQ, Matrix.transpose_one]
  have hstar : P.map star * Q.map star = 1 := by
    ext a b
    have h := congrArg star (congrFun (congrFun hPQ a) b)
    simpa [Matrix.mul_apply, Matrix.one_apply, star_sum, star_mul, mul_comm] using h
  have hpull : c3PullbackMetric Q (Matrix.diagonal (fun i ↦ (d i : ℂ))) = G := by
    rw [c3PullbackMetric, ← hdiag]
    calc
      Q.transpose * (P.transpose * G * P.map star) * Q.map star =
          (Q.transpose * P.transpose) * G * (P.map star * Q.map star) := by noncomm_ring
      _ = G := by rw [htranspose, hstar]; simp
  have hinvD := c3_diagonal_inverse d hd
  constructor
  · intro i a
    rw [← hpull]
    simp [c3PullbackMetric, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Matrix.diagonal_apply]
    apply Finset.sum_congr rfl
    intro r hr
    have hsqrt := Real.sq_sqrt (le_of_lt (hd r))
    have hcast : ((Real.sqrt (d r) : ℝ) : ℂ) *
        ((Real.sqrt (d r) : ℝ) : ℂ) = (d r : ℂ) := by
      exact_mod_cast (by simpa [pow_two] using hsqrt)
    rw [← hcast]
    ring
  · intro b j
    rw [← hpull, c3_pullback_inverse_entry Q P
      (Matrix.diagonal (fun i ↦ (d i : ℂ))) hQP hPQ b j, hinvD]
    simp only [Matrix.diagonal_apply]
    have hterm (r : Fin n) :
        star (P b r) * ((d r)⁻¹ : ℂ) * P j r =
          (((Real.sqrt (d r))⁻¹ : ℝ) : ℂ) * P j r *
            star ((((Real.sqrt (d r))⁻¹ : ℝ) : ℂ) * P b r) := by
      have hsqrt := Real.sq_sqrt (le_of_lt (hd r))
      have hsqrtpos := Real.sqrt_pos.2 (hd r)
      have hsquare : (Real.sqrt (d r))⁻¹ * (Real.sqrt (d r))⁻¹ = (d r)⁻¹ := by
        field_simp [hsqrtpos.ne', (ne_of_gt (hd r))]
        rw [hsqrt]
      have hcast :
          (((Real.sqrt (d r))⁻¹ : ℝ) : ℂ) *
            (((Real.sqrt (d r))⁻¹ : ℝ) : ℂ) = ((d r)⁻¹ : ℂ) := by
        exact_mod_cast hsquare
      calc
        star (P b r) * ((d r)⁻¹ : ℂ) * P j r =
            ((((Real.sqrt (d r))⁻¹ : ℝ) : ℂ) *
              (((Real.sqrt (d r))⁻¹ : ℝ) : ℂ)) * P j r * star (P b r) := by
          rw [← hcast]
          ring
        _ = (((Real.sqrt (d r))⁻¹ : ℝ) : ℂ) * P j r *
            star ((((Real.sqrt (d r))⁻¹ : ℝ) : ℂ) * P b r) := by
          simp [star_mul, mul_comm, mul_left_comm, mul_assoc]
    apply Finset.sum_congr rfl
    intro r hr
    simpa [Complex.star_def] using hterm r

theorem c3_pair_diagonalized_frame_weighted {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (z : EuclideanSpace ℂ (Fin n))
    (P Q : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ)
    (hd : ∀ i, 0 < d i) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hdiag : c3PullbackMetric P G = Matrix.diagonal (fun i ↦ (d i : ℂ)))
    (T : Fin n → Fin n → Fin n → ℂ) :
    c3Pair (fun _ : EuclideanSpace ℂ (Fin n) ↦ G) z T T =
      ∑ i, ∑ j, ∑ k,
        ((d i / (d j * d k) : ℝ) : ℂ) *
          referenceContraction_tensorFrameTransform Q P T i j k *
            star (referenceContraction_tensorFrameTransform Q P T i j k) := by
  rcases c3_metric_frame_factorizations G P Q d hd hPQ hQP hdiag with
    ⟨hUpper, hLower⟩
  exact c3_pair_arbitrary_frame_weighted d hd G z P Q T hUpper hLower

theorem c3_pair_diagonalized_frame_energy {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (z : EuclideanSpace ℂ (Fin n))
    (P Q : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ)
    (hd : ∀ i, 0 < d i) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hdiag : c3PullbackMetric P G = Matrix.diagonal (fun i ↦ (d i : ℂ)))
    (T : Fin n → Fin n → Fin n → ℂ) :
    (c3Pair (fun _ : EuclideanSpace ℂ (Fin n) ↦ G) z T T).re =
      ∑ i, ∑ j, ∑ k,
        (d i / (d j * d k)) *
          ‖referenceContraction_tensorFrameTransform Q P T i j k‖ ^ 2 := by
  rw [c3_pair_diagonalized_frame_weighted G z P Q d hd hPQ hQP hdiag T]
  have hterm (i j k : Fin n) :
      (((d i / (d j * d k) : ℝ) : ℂ) *
          referenceContraction_tensorFrameTransform Q P T i j k *
            star (referenceContraction_tensorFrameTransform Q P T i j k)).re =
        (d i / (d j * d k)) * ‖referenceContraction_tensorFrameTransform Q P T i j k‖ ^ 2 := by
    have hz (i j k : Fin n) :
        referenceContraction_tensorFrameTransform Q P T i j k *
          star (referenceContraction_tensorFrameTransform Q P T i j k) =
            ((‖referenceContraction_tensorFrameTransform Q P T i j k‖ ^ 2 : ℝ) : ℂ) := by
      simpa [Complex.star_def] using
        Complex.mul_conj' (referenceContraction_tensorFrameTransform Q P T i j k)
    calc
      _ = (((d i / (d j * d k) : ℝ) : ℂ) *
          ((‖referenceContraction_tensorFrameTransform Q P T i j k‖ ^ 2 : ℝ) : ℂ)).re := by
        rw [mul_assoc, hz]
      _ = ((((d i / (d j * d k)) *
          ‖referenceContraction_tensorFrameTransform Q P T i j k‖ ^ 2 : ℝ) : ℂ)).re := by
        congr 1
        exact (Complex.ofReal_mul (d i / (d j * d k))
          (‖referenceContraction_tensorFrameTransform Q P T i j k‖ ^ 2)).symm
      _ = (d i / (d j * d k)) *
          ‖referenceContraction_tensorFrameTransform Q P T i j k‖ ^ 2 := Complex.ofReal_re _
  change RCLike.re (∑ i, ∑ j, ∑ k,
    ((d i / (d j * d k) : ℝ) : ℂ) *
      referenceContraction_tensorFrameTransform Q P T i j k *
        star (referenceContraction_tensorFrameTransform Q P T i j k)) = _
  simp_rw [map_sum (RCLike.re : ℂ →+ ℝ)]
  simp_rw [← hterm]
  rfl

end KahlerForm
