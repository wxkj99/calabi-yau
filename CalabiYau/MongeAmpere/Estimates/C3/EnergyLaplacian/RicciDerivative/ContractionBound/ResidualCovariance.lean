module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.Basic
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.ContractionBound.MixedFrame

/-!
# ResidualCovariance for the differentiated Ricci contraction

Székelyhidi, An Introduction to Extremal Kähler Metrics, §3.3, proof of
Lemma 3.9, printed pp. 44–45: two-sided metric comparison and the
linear-plus-quadratic connection correction.

Contraction cancellation under P*B=1. Input order is T(output,k,j) and two-tensor(output,bar i); the conjugate is on the barred slot. P=1 gives the original residual; in n=1 a scalar change gives p*p*conjugate(p) for the covariant residual.
-/

public section

open scoped Manifold ContDiff BigOperators ComplexOrder MatrixOrder
open ContinuousAlternatingMap
open Matrix

namespace KahlerForm

theorem c3_frame_tensor_cancellation {n : ℕ}
    (P B : Matrix (Fin n) (Fin n) ℂ)
    (T : Fin n → Fin n → Fin n → ℂ)
    (Q : Fin n → Fin n → ℂ)
    (hPB : P * B = 1) (k j i : Fin n) :
    (∑ r : Fin n,
      (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
        B r a * P b k * P c j * T a b c) *
      (∑ u : Fin n, ∑ v : Fin n,
        P u r * star (P v i) * Q u v)) =
    ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ v : Fin n,
      P b k * P c j * star (P v i) * T a b c * Q a v := by
  classical
  have hcancel (u a : Fin n) :
      (∑ r : Fin n, P u r * B r a) = if u = a then 1 else 0 := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M u a) hPB
    simpa [Matrix.mul_apply, Matrix.one_apply] using h
  let F : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → ℂ :=
    fun r a b c u v =>
      (B r a * P b k * P c j * T a b c) *
        (P u r * star (P v i) * Q u v)
  have hExpanded :
      (∑ r : Fin n,
        (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
          B r a * P b k * P c j * T a b c) *
        (∑ u : Fin n, ∑ v : Fin n,
          P u r * star (P v i) * Q u v)) =
      ∑ r : Fin n, ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
        ∑ u : Fin n, ∑ v : Fin n, F r a b c u v := by
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum, F]
  have hReorder :
      (∑ r : Fin n, ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
        ∑ u : Fin n, ∑ v : Fin n, F r a b c u v) =
      ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ v : Fin n,
        ∑ u : Fin n, ∑ r : Fin n, F r a b c u v := by
    calc
      _ = ∑ a : Fin n, ∑ r : Fin n, ∑ b : Fin n, ∑ c : Fin n,
            ∑ u : Fin n, ∑ v : Fin n, F r a b c u v := Finset.sum_comm
      _ = ∑ a : Fin n, ∑ b : Fin n, ∑ r : Fin n, ∑ c : Fin n,
            ∑ u : Fin n, ∑ v : Fin n, F r a b c u v := by
          apply Finset.sum_congr rfl
          intro a ha
          exact Finset.sum_comm
      _ = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ r : Fin n,
            ∑ u : Fin n, ∑ v : Fin n, F r a b c u v := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          exact Finset.sum_comm
      _ = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ u : Fin n,
            ∑ r : Fin n, ∑ v : Fin n, F r a b c u v := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          apply Finset.sum_congr rfl
          intro c hc
          exact Finset.sum_comm
      _ = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ u : Fin n,
            ∑ v : Fin n, ∑ r : Fin n, F r a b c u v := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          apply Finset.sum_congr rfl
          intro c hc
          apply Finset.sum_congr rfl
          intro u hu
          exact Finset.sum_comm
      _ = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ v : Fin n,
            ∑ u : Fin n, ∑ r : Fin n, F r a b c u v := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          apply Finset.sum_congr rfl
          intro c hc
          exact Finset.sum_comm
  have hfactor (r a b c u v : Fin n) :
      F r a b c u v = (P u r * B r a) *
        (P b k * P c j * star (P v i) * T a b c * Q u v) := by
    simp only [F]
    ring
  calc
    _ = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ v : Fin n,
          ∑ u : Fin n, ∑ r : Fin n, F r a b c u v := hExpanded.trans hReorder
    _ = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ v : Fin n,
          ∑ u : Fin n, ∑ r : Fin n,
            (P u r * B r a) *
              (P b k * P c j * star (P v i) * T a b c * Q u v) := by
        simp_rw [hfactor]
    _ = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ v : Fin n,
          ∑ u : Fin n, (∑ r : Fin n, P u r * B r a) *
            (P b k * P c j * star (P v i) * T a b c * Q u v) := by
        simp_rw [← Finset.sum_mul]
    _ = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ v : Fin n,
          P b k * P c j * star (P v i) * T a b c * Q a v := by
        simp [hcancel]

theorem c3_frame_residual_tensor_identity {n : ℕ}
    (P B : Matrix (Fin n) (Fin n) ℂ)
    (T : Fin n → Fin n → Fin n → ℂ)
    (Y : Fin n → Fin n → Fin n → ℂ)
    (S : Fin n → Fin n → ℂ)
    (hPB : P * B = 1) (k j i : Fin n) :
    c3ThreeCovariantFrame P Y k j i -
      ∑ r, c3MixedFrameChange P B T r k j * c3TwoCovariantFrame P S r i =
    (∑ a, ∑ b, ∑ c, P a k * P b j * star (P c i) * Y a b c) -
      ∑ a, ∑ b, ∑ c, ∑ v,
        P b k * P c j * star (P v i) * T a b c * S a v := by
  classical
  unfold c3ThreeCovariantFrame c3TwoCovariantFrame c3MixedFrameChange
  simp only [Fintype.sum_prod_type]
  rw [c3_frame_tensor_cancellation P B T S hPB k j i]

end KahlerForm
