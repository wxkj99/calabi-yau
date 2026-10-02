module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.Basic
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.ContractionBound.MetricFrame

/-!
# RaisedCovariance for the differentiated Ricci contraction

Székelyhidi, An Introduction to Extremal Kähler Metrics, §3.3, proof of
Lemma 3.9, printed pp. 44–45: two-sided metric comparison and the
linear-plus-quadratic connection correction.

Raised barred-index identities under a positive diagonal perturbed metric and two-sided inverse for the frame. In n=1, raising multiplies the residual by 1/d; both transpose and complex conjugation are explicit.
-/

public section

open scoped Manifold ContDiff BigOperators ComplexOrder MatrixOrder
open ContinuousAlternatingMap
open Matrix

namespace KahlerForm

theorem c3_raised_inverse_frame_identity {n : ℕ}
    (P B G : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ)
    (hPB : P * B = 1) (hBP : B * P = 1) (hd : ∀ i, 0 < d i)
    (hdiag : P.transpose * G * P.map star =
      Matrix.diagonal (fun i ↦ (d i : ℂ))) (i l : Fin n) :
    ∑ a : Fin n, B i a * G⁻¹ l a =
      ((d i)⁻¹ : ℂ) * star (P l i) := by
  let D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun i ↦ (d i : ℂ))
  have hD : P.transpose * G * P.map star = D := by simpa [D] using hdiag
  have hframe := c3_frame_metric_sum_identities G D P B (fun i ↦ (d i : ℂ))
    hPB hBP rfl hD
  have hDinv : D⁻¹ = Matrix.diagonal (fun x : Fin n ↦ ((d x)⁻¹ : ℂ)) := by
    have hu : IsUnit (fun x : Fin n ↦ (d x : ℂ)) := by
      rw [Pi.isUnit_iff]
      intro x
      exact isUnit_iff_ne_zero.mpr (by exact_mod_cast ne_of_gt (hd x))
    have hfun : Ring.inverse (fun x : Fin n ↦ (d x : ℂ)) =
        (fun x : Fin n ↦ ((d x)⁻¹ : ℂ)) := by
      funext x
      rw [Ring.inverse_of_isUnit hu]
      simp [IsUnit.val_inv_apply hu x]
    rw [Matrix.inv_diagonal]
    ext x y
    simp [Matrix.diagonal_apply, hfun]
  have hentry (a : Fin n) : G⁻¹ l a =
      ∑ x : Fin n, (d x)⁻¹ * P a x * star (P l x) := by
    calc
      G⁻¹ l a = ∑ y : Fin n × Fin n,
          D⁻¹ y.1 y.2 * P a y.2 * star (P l y.1) := (hframe.2 a l).symm
      _ = ∑ x : Fin n, (d x)⁻¹ * P a x * star (P l x) := by
        simp [hDinv, D, Matrix.diagonal_apply, Fintype.sum_prod_type]
  simp_rw [hentry]
  calc
    ∑ a : Fin n, B i a *
        ∑ x : Fin n, (d x)⁻¹ * P a x * star (P l x) =
      ∑ x : Fin n, (d x)⁻¹ * star (P l x) *
        (∑ a : Fin n, B i a * P a x) := by
          conv_lhs => simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro x hx
          calc
            ∑ a : Fin n, B i a * ((d x)⁻¹ * P a x * star (P l x)) =
                ∑ a : Fin n, (B i a * P a x) * ((d x)⁻¹ * star (P l x)) := by
              apply Finset.sum_congr rfl
              intro a ha
              ring
            _ = (∑ a : Fin n, B i a * P a x) *
                ((d x)⁻¹ * star (P l x)) := by rw [Finset.sum_mul]
            _ = ((d x)⁻¹ * star (P l x)) *
                (∑ a : Fin n, B i a * P a x) := by ring
    _ = ∑ x : Fin n, (d x)⁻¹ * star (P l x) * (if i = x then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro x hx
          have hBPentry := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i x) hBP
          simpa [Matrix.mul_apply, Matrix.one_apply] using congrArg
            (fun q : ℂ => (d x)⁻¹ * star (P l x) * q) hBPentry
    _ = ((d i)⁻¹ : ℂ) * star (P l i) := by simp
theorem c3_raised_three_tensor_covariance {n : ℕ}
    (P B G : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ)
    (hPB : P * B = 1) (hBP : B * P = 1) (hd : ∀ i, 0 < d i)
    (hdiag : P.transpose * G * P.map star =
      Matrix.diagonal (fun i ↦ (d i : ℂ)))
    (Y : Fin n → Fin n → Fin n → ℂ) (i j k : Fin n) :
    ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, B i a * P b j * P c k *
      (∑ l : Fin n, G⁻¹ l a * Y c b l) = ((d i)⁻¹ : ℂ) * ∑ b : Fin n, ∑ c : Fin n,
        P c k * P b j * (∑ l : Fin n, star (P l i) * Y c b l) := by
  classical
  have hRaise : ∀ i l, ∑ a : Fin n, B i a * G⁻¹ l a = ((d i)⁻¹ : ℂ) * star (P l i) := fun i l =>
    c3_raised_inverse_frame_identity P B G d hPB hBP hd hdiag i l
  have hbc (b c : Fin n) :
      ∑ a : Fin n, B i a * (∑ l : Fin n, G⁻¹ l a * Y c b l) =
        ((d i)⁻¹ : ℂ) * ∑ l : Fin n, star (P l i) * Y c b l := by
    calc
      _ = ∑ a : Fin n, ∑ l : Fin n, (B i a * G⁻¹ l a) * Y c b l := by
        apply Finset.sum_congr rfl
        · intro a ha
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l hl
          ring
      _ = ∑ l : Fin n, (∑ a : Fin n, B i a * G⁻¹ l a) * Y c b l := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro l hl
        rw [← Finset.sum_mul]
      _ = _ := by
        simp_rw [hRaise]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l hl
        ring
  calc
    _ = ∑ b : Fin n, ∑ c : Fin n, ∑ a : Fin n,
        B i a * P b j * P c k * (∑ l : Fin n, G⁻¹ l a * Y c b l) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun b _ ↦ Finset.sum_comm)
    _ = ∑ b : Fin n, ∑ c : Fin n,
        P b j * P c k * (∑ a : Fin n,
          B i a * (∑ l : Fin n, G⁻¹ l a * Y c b l)) := by
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      calc
        _ = ∑ a : Fin n, (P b j * P c k) *
            (B i a * (∑ l : Fin n, G⁻¹ l a * Y c b l)) := by
          apply Finset.sum_congr rfl; intro a ha; ring
        _ = _ := by rw [Finset.mul_sum]
    _ = ∑ b : Fin n, ∑ c : Fin n,
        P b j * P c k * (((d i)⁻¹ : ℂ) *
          ∑ l : Fin n, star (P l i) * Y c b l) := by
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      rw [hbc b c]
    _ = ((d i)⁻¹ : ℂ) *
        ∑ b : Fin n, ∑ c : Fin n,
          P c k * P b j * (∑ l : Fin n, star (P l i) * Y c b l) := by
      calc
        _ = ∑ b : Fin n, ∑ c : Fin n,
            ((d i)⁻¹ : ℂ) *
              (P c k * P b j * (∑ l : Fin n, star (P l i) * Y c b l)) := by
          apply Finset.sum_congr rfl
          intro b hb
          apply Finset.sum_congr rfl
          intro c hc
          ring
        _ = _ := by simp_rw [← Finset.mul_sum]

end KahlerForm
