module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceContractionBound.Energy

/-!
# MixedPairing for the reference-curvature contraction

Székelyhidi, An Introduction to Extremal Kähler Metrics, §3.3, proof of Lemma 3.9, terms following (3.15), printed p. 45; finite tensor contraction algebra implementing that proof.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal BigOperators ComplexOrder MatrixOrder
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

theorem referenceContraction_mixed_weighted_pair {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (z : EuclideanSpace ℂ (Fin n))
    (P Q : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ)
    (hd : ∀ i, 0 < d i) (hPQ : P * Q = 1)
    (hdiag : c3PullbackMetric P G = Matrix.diagonal (fun i ↦ (d i : ℂ)))
    (U T : Fin n → Fin n → Fin n → ℂ) :
    c3Pair (fun _ : EuclideanSpace ℂ (Fin n) ↦ G) z U T =
      ∑ i, ∑ j, ∑ k, ((d i / (d j * d k) : ℝ) : ℂ) *
        referenceContractionTensorFrameTransform Q P U i j k *
          star (referenceContractionTensorFrameTransform Q P T i j k) := by
  rcases c3_metric_frame_factorizations G P Q d hd hPQ hdiag with
    ⟨hUpper, hLower⟩
  let B : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i ↦ (Real.sqrt (d i) : ℂ)) * Q
  let C : Matrix (Fin n) (Fin n) ℂ :=
    P * Matrix.diagonal (fun i ↦ ((Real.sqrt (d i))⁻¹ : ℂ))
  have hUpp : ∀ i a, G i a = ∑ r, B r i * star (B r a) := by
    intro i a
    simpa [B, Matrix.mul_apply, Matrix.diagonal_apply] using hUpper i a
  have hCentry (b j : Fin n) : C b j =
      P b j * (((Real.sqrt (d j))⁻¹ : ℝ) : ℂ) := by
    simp [C, Matrix.mul_apply, Matrix.diagonal_apply]
  have hBentry (i a : Fin n) : B i a =
      ((Real.sqrt (d i) : ℝ) : ℂ) * Q i a := by
    simp [B, Matrix.mul_apply, Matrix.diagonal_apply]
  have hLower' : ∀ b j, G⁻¹ b j = ∑ r, C j r * star (C b r) := by
    intro b j
    rw [hLower b j]
    apply Finset.sum_congr rfl
    intro r hr
    rw [hCentry, hCentry]
    simp only [star_mul]
    simp
    ring
  have hframe := referenceContraction_pair_eq_frame_components G z B C U T hUpp hLower'
  have hscale (i j k : Fin n) :
      ((Real.sqrt (d i) : ℝ) : ℂ) *
          (((Real.sqrt (d j))⁻¹ : ℝ) : ℂ) *
          (((Real.sqrt (d k))⁻¹ : ℝ) : ℂ) =
        ((Real.sqrt (d i) / (Real.sqrt (d j) * Real.sqrt (d k)) : ℝ) : ℂ) := by
    have hreal : Real.sqrt (d i) * (Real.sqrt (d j))⁻¹ *
        (Real.sqrt (d k))⁻¹ =
        Real.sqrt (d i) / (Real.sqrt (d j) * Real.sqrt (d k)) := by
      field_simp [ne_of_gt (Real.sqrt_pos.2 (hd j)),
        ne_of_gt (Real.sqrt_pos.2 (hd k))]
    exact_mod_cast hreal
  have htransform (W : Fin n → Fin n → Fin n → ℂ) (i j k : Fin n) :
      referenceContractionTensorFrameTransform B C W i j k =
        (((Real.sqrt (d i) / (Real.sqrt (d j) * Real.sqrt (d k)) : ℝ) : ℂ) *
          referenceContractionTensorFrameTransform Q P W i j k) := by
    have hscale' :
        ((Real.sqrt (d i) : ℝ) : ℂ) *
            (((Real.sqrt (d j))⁻¹ : ℝ) : ℂ) *
            (((Real.sqrt (d k))⁻¹ : ℝ) : ℂ) =
          ((Real.sqrt (d i) / (Real.sqrt (d j) * Real.sqrt (d k)) : ℝ) : ℂ) := hscale i j k
    simp only [referenceContractionTensorFrameTransform]
    simp_rw [hBentry, hCentry]
    have hterm (a b c : Fin n) :
        (((Real.sqrt (d i) : ℝ) : ℂ) * Q i a) *
            (P b j * (((Real.sqrt (d j))⁻¹ : ℝ) : ℂ)) *
            (P c k * (((Real.sqrt (d k))⁻¹ : ℝ) : ℂ)) * W a b c =
          (((Real.sqrt (d i) : ℝ) : ℂ) *
            (((Real.sqrt (d j))⁻¹ : ℝ) : ℂ) *
            (((Real.sqrt (d k))⁻¹ : ℝ) : ℂ)) *
            (Q i a * P b j * P c k * W a b c) := by ring
    calc
      _ = ∑ a, ∑ b, ∑ c,
          (((Real.sqrt (d i) : ℝ) : ℂ) *
            (((Real.sqrt (d j))⁻¹ : ℝ) : ℂ) *
            (((Real.sqrt (d k))⁻¹ : ℝ) : ℂ)) *
            (Q i a * P b j * P c k * W a b c) := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        apply Finset.sum_congr rfl
        intro c hc
        exact hterm a b c
      _ = (((Real.sqrt (d i) : ℝ) : ℂ) *
          (((Real.sqrt (d j))⁻¹ : ℝ) : ℂ) *
          (((Real.sqrt (d k))⁻¹ : ℝ) : ℂ)) *
          referenceContractionTensorFrameTransform Q P W i j k := by
        simp_rw [← Finset.mul_sum]
        rfl
      _ = (((Real.sqrt (d i) / (Real.sqrt (d j) * Real.sqrt (d k)) : ℝ) : ℂ) *
          referenceContractionTensorFrameTransform Q P W i j k) := by rw [hscale']
  rw [hframe]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [htransform U i j k, htransform T i j k]
  let s : ℝ := Real.sqrt (d i) / (Real.sqrt (d j) * Real.sqrt (d k))
  have hsquare : s ^ 2 = d i / (d j * d k) := by
    dsimp [s]
    have hi' := Real.sq_sqrt (le_of_lt (hd i))
    have hj' := Real.sq_sqrt (le_of_lt (hd j))
    have hk' := Real.sq_sqrt (le_of_lt (hd k))
    have hden : Real.sqrt (d j) * Real.sqrt (d k) ≠ 0 :=
      ne_of_gt (mul_pos (Real.sqrt_pos.2 (hd j)) (Real.sqrt_pos.2 (hd k)))
    rw [div_pow, hi', mul_pow, hj', hk']
  have hsstar : star ((s : ℝ) : ℂ) = ((s : ℝ) : ℂ) := by simp
  have hcast : (((s : ℝ) : ℂ) ^ 2) = ((d i / (d j * d k) : ℝ) : ℂ) := by
    exact_mod_cast hsquare
  change ((s : ℝ) : ℂ) * referenceContractionTensorFrameTransform Q P U i j k *
      star (((s : ℝ) : ℂ) * referenceContractionTensorFrameTransform Q P T i j k) = _
  have hstar : star (((s : ℝ) : ℂ) * referenceContractionTensorFrameTransform Q P T i j k) =
      ((s : ℝ) : ℂ) * star (referenceContractionTensorFrameTransform Q P T i j k) := by
    simp [hsstar]
  rw [hstar]
  rw [show ((s : ℝ) : ℂ) * referenceContractionTensorFrameTransform Q P U i j k *
      (((s : ℝ) : ℂ) * star (referenceContractionTensorFrameTransform Q P T i j k)) =
      ((s : ℝ) : ℂ) ^ 2 * referenceContractionTensorFrameTransform Q P U i j k *
        star (referenceContractionTensorFrameTransform Q P T i j k) by ring]
  rw [hcast]

end KahlerForm
