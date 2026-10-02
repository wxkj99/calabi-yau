module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.Basic

/-!
# FrameBounds for the differentiated Ricci contraction

Székelyhidi, An Introduction to Extremal Kähler Metrics, §3.3, proof of
Lemma 3.9, printed pp. 44–45: two-sided metric comparison and the
linear-plus-quadratic connection correction.

Reference/forcing component differences and finite energy component/action bounds; E nonnegative and finite real bounds are hypotheses. Fin 0 sums vanish; n=1 norm(T)<=sqrt(E) has coefficient one, and zero tensors produce zero contractions.
-/

public section

open scoped Manifold ContDiff BigOperators ComplexOrder MatrixOrder
open ContinuousAlternatingMap
open Matrix

namespace KahlerForm

theorem c3_frame_difference_bounds {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℂ)
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (X Y : Fin n → Fin n → Fin n → ℂ) (R H : ℝ)
    (hA2 : ∀ j l, ‖c3TwoCovariantFrame P A j l‖ ≤ R)
    (hB2 : ∀ j l, ‖c3TwoCovariantFrame P B j l‖ ≤ H)
    (hA3 : ∀ k j l, ‖c3ThreeCovariantFrame P X k j l‖ ≤ R)
    (hB3 : ∀ k j l, ‖c3ThreeCovariantFrame P Y k j l‖ ≤ H) :
    (∀ j l, ‖c3TwoCovariantFrame P (fun a b ↦ A a b - B a b) j l‖ ≤ R + H) ∧
    (∀ k j l, ‖c3ThreeCovariantFrame P
      (fun a b c ↦ X a b c - Y a b c) k j l‖ ≤ R + H) := by
  constructor
  · intro j l
    have hlin : c3TwoCovariantFrame P (fun a b ↦ A a b - B a b) j l =
        c3TwoCovariantFrame P A j l - c3TwoCovariantFrame P B j l := by
      simp only [c3TwoCovariantFrame, Finset.sum_sub_distrib, mul_sub]
    rw [hlin]
    calc
      ‖c3TwoCovariantFrame P A j l - c3TwoCovariantFrame P B j l‖ ≤
          ‖c3TwoCovariantFrame P A j l‖ + ‖c3TwoCovariantFrame P B j l‖ :=
        norm_sub_le _ _
      _ ≤ R + H := add_le_add (hA2 j l) (hB2 j l)
  · intro k j l
    have hlin : c3ThreeCovariantFrame P (fun a b c ↦ X a b c - Y a b c) k j l =
        c3ThreeCovariantFrame P X k j l - c3ThreeCovariantFrame P Y k j l := by
      simp only [c3ThreeCovariantFrame, Finset.sum_sub_distrib, mul_sub]
    rw [hlin]
    calc
      ‖c3ThreeCovariantFrame P X k j l - c3ThreeCovariantFrame P Y k j l‖ ≤
          ‖c3ThreeCovariantFrame P X k j l‖ + ‖c3ThreeCovariantFrame P Y k j l‖ :=
        norm_sub_le _ _
      _ ≤ R + H := add_le_add (hA3 k j l) (hB3 k j l)

/-- A unitary-frame tensor energy controls every individual component. -/
theorem c3_frame_tensor_component_bound_of_energy_sum
    {n : ℕ} (T : Fin n → Fin n → Fin n → ℂ) (E : ℝ) (hE : 0 ≤ E)
    (henergy : ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ‖T i j k‖ ^ 2 ≤ E) :
    ∀ i j k, ‖T i j k‖ ≤ Real.sqrt E := by
  intro i j k
  have hk : ‖T i j k‖ ^ 2 ≤ ∑ l : Fin n, ‖T i j l‖ ^ 2 :=
    Finset.single_le_sum (fun l hl => sq_nonneg ‖T i j l‖) (Finset.mem_univ k)
  have hj : ∑ l : Fin n, ‖T i j l‖ ^ 2 ≤
      ∑ b : Fin n, ∑ l : Fin n, ‖T i b l‖ ^ 2 := by
    calc
      ∑ l : Fin n, ‖T i j l‖ ^ 2 =
          (fun b : Fin n => ∑ l : Fin n, ‖T i b l‖ ^ 2) j := rfl
      _ ≤ ∑ b : Fin n, (fun b : Fin n => ∑ l : Fin n, ‖T i b l‖ ^ 2) b :=
        Finset.single_le_sum
          (fun b hb => Finset.sum_nonneg fun l hl => sq_nonneg ‖T i b l‖)
          (Finset.mem_univ j)
      _ = ∑ b : Fin n, ∑ l : Fin n, ‖T i b l‖ ^ 2 := by rfl
  have hi : ∑ b : Fin n, ∑ l : Fin n, ‖T i b l‖ ^ 2 ≤
      ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ‖T a b l‖ ^ 2 := by
    calc
      ∑ b : Fin n, ∑ l : Fin n, ‖T i b l‖ ^ 2 =
          (fun a : Fin n => ∑ b : Fin n, ∑ l : Fin n, ‖T a b l‖ ^ 2) i := rfl
      _ ≤ ∑ a : Fin n, (fun a : Fin n => ∑ b : Fin n, ∑ l : Fin n, ‖T a b l‖ ^ 2) a :=
        Finset.single_le_sum
          (fun a ha => Finset.sum_nonneg fun b hb =>
            Finset.sum_nonneg fun l hl => sq_nonneg ‖T a b l‖)
          (Finset.mem_univ i)
      _ = ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ‖T a b l‖ ^ 2 := by rfl
  have hsq : ‖T i j k‖ ^ 2 ≤ E := hk.trans (hj.trans (hi.trans henergy))
  have hsqrt : 0 ≤ Real.sqrt E := Real.sqrt_nonneg E
  have hnorm : 0 ≤ ‖T i j k‖ := norm_nonneg _
  nlinarith [Real.sq_sqrt hE]

end KahlerForm
