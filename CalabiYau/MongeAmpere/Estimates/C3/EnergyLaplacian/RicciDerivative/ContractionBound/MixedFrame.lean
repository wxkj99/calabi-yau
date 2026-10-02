module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.Basic

/-!
# MixedFrame for the differentiated Ricci contraction

Székelyhidi, An Introduction to Extremal Kähler Metrics, §3.3, proof of
Lemma 3.9, printed pp. 44–45: two-sided metric comparison and the
linear-plus-quadratic connection correction.

Mixed (1,2) frame change uses the inverse on the output index and P on both input indices. At n=1 and scalar P=p, Q=1/p it transforms T to p*T. Sum factorization retains the original proved helpers.
-/

public section

open scoped Manifold ContDiff BigOperators ComplexOrder MatrixOrder
open ContinuousAlternatingMap
open Matrix

namespace KahlerForm

abbrev C3Pair (n : ℕ) := Fin n × Fin n × Fin n

abbrev C3PairTriple (n : ℕ) :=
  (Fin n × Fin n) × (Fin n × Fin n) × (Fin n × Fin n)

@[expose] noncomputable def c3MixedFrameChange {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) (T : Fin n → Fin n → Fin n → ℂ)
    (i j k : Fin n) : ℂ :=
  ∑ p : C3Pair n, B i p.1 * A p.2.1 j * A p.2.2 k * T p.1 p.2.1 p.2.2

theorem c3SumThreeFactor
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → ℂ) (g : β → ℂ) (h : γ → ℂ) :
    (∑ a, ∑ b, ∑ c, f a * g b * h c) =
      (∑ a, f a) * (∑ b, g b) * (∑ c, h c) := by
  have hp :
      (∑ a, f a) * (∑ b, g b) * (∑ c, h c) =
        ∑ a, ∑ b, ∑ c, f a * g b * h c := by
    calc
      _ = (∑ p : α × β, f p.1 * g p.2) * (∑ c, h c) := by
        rw [Fintype.sum_mul_sum, Fintype.sum_prod_type]
      _ = ∑ p : α × β, ∑ c, (f p.1 * g p.2) * h c := by
        rw [Fintype.sum_mul_sum]
      _ = _ := by simp only [Fintype.sum_prod_type]
  exact hp.symm

theorem c3SumPairTripleFactor {n : ℕ}
    (f g h : Fin n × Fin n → ℂ) (d : ℂ) :
    (∑ z : C3PairTriple n, f z.1 * g z.2.1 * h z.2.2 * d) =
      (∑ z, f z) * (∑ z, g z) * (∑ z, h z) * d := by
  rw [← Finset.sum_mul]
  have hh :
      (∑ z : C3PairTriple n, f z.1 * g z.2.1 * h z.2.2) =
        (∑ z, f z) * (∑ z, g z) * (∑ z, h z) := by
    simpa only [Fintype.sum_prod_type] using c3SumThreeFactor f g h
  exact congrArg (fun z : ℂ => z * d) hh

end KahlerForm
