module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ConnectionLaplacian.Basic

/-!
# Finite chart jets for the covariant-curvature calculation

Székelyhidi, §3.3, proof of Lemma 3.9, the Bianchi calculation following
(3.15), printed p. 45. The identities here describe finite algebraic
expressions in metric jets; they do not involve derivatives of an actual metric.

`H` is an arbitrary ordered complex matrix, with no symmetry or invertibility
assumption. `P` and `Q` are independent arrays. The normalized metric jets
are Z, bar, Z-bar, ZZ, and ZZ-bar. The decomposition is
`-W + PureZZ + Mixed - Quartic`, with both lower connection corrections.
-/

public section

open scoped Manifold ContDiff BigOperators ComplexOrder MatrixOrder

namespace KahlerForm

variable {n : ℕ}

@[expose]
noncomputable def c3JetChristoffel
    (H : Matrix (Fin n) (Fin n) ℂ)
    (P : Fin n → Fin n → Fin n → ℂ) (i p j : Fin n) : ℂ :=
  ∑ l, H l i * P p j l

@[expose]
noncomputable def c3JetCurvature
    (H : Matrix (Fin n) (Fin n) ℂ)
    (P Q : Fin n → Fin n → Fin n → ℂ)
    (S : Fin n → Fin n → Fin n → Fin n → ℂ) (j q k l : Fin n) : ℂ :=
  -S j q k l + ∑ a, ∑ b, H b a * P j k b * Q q a l

@[expose]
noncomputable def c3JetCurvatureDerivative
    (H : Matrix (Fin n) (Fin n) ℂ)
    (P Q : Fin n → Fin n → Fin n → ℂ)
    (S V : Fin n → Fin n → Fin n → Fin n → ℂ)
    (W : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ)
    (s j q k l : Fin n) : ℂ :=
  -W s j q k l + ∑ a, ∑ b,
    ((-(∑ c, ∑ d, H b c * P s c d * H d a)) * P j k b * Q q a l +
      H b a * V s j k b * Q q a l + H b a * P j k b * S s q a l)

@[expose]
noncomputable def c3JetCovariantCurvature
    (H : Matrix (Fin n) (Fin n) ℂ)
    (P Q : Fin n → Fin n → Fin n → ℂ)
    (S V : Fin n → Fin n → Fin n → Fin n → ℂ)
    (W : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ)
    (s j q k l : Fin n) : ℂ :=
  c3JetCurvatureDerivative H P Q S V W s j q k l -
    ∑ r, c3JetChristoffel H P r s j * c3JetCurvature H P Q S r q k l -
    ∑ r, c3JetChristoffel H P r s k * c3JetCurvature H P Q S j q r l

@[expose]
noncomputable def c3JetMixed
    (H : Matrix (Fin n) (Fin n) ℂ)
    (P : Fin n → Fin n → Fin n → ℂ)
    (S : Fin n → Fin n → Fin n → Fin n → ℂ)
    (s j q k l : Fin n) : ℂ :=
  (∑ a, ∑ b, H b a * P j k b * S s q a l) +
    (∑ r, c3JetChristoffel H P r s j * S r q k l) +
    (∑ r, c3JetChristoffel H P r s k * S j q r l)

@[expose]
noncomputable def c3JetPureZZ
    (H : Matrix (Fin n) (Fin n) ℂ)
    (Q : Fin n → Fin n → Fin n → ℂ)
    (V : Fin n → Fin n → Fin n → Fin n → ℂ)
    (s j q k l : Fin n) : ℂ :=
  ∑ a, ∑ b, H b a * V s j k b * Q q a l

@[expose]
noncomputable def c3JetQuartic
    (H : Matrix (Fin n) (Fin n) ℂ)
    (P Q : Fin n → Fin n → Fin n → ℂ)
    (s j q k l : Fin n) : ℂ :=
  (∑ a, ∑ b, (∑ c, ∑ d, H b c * P s c d * H d a) *
    P j k b * Q q a l) +
  (∑ r, c3JetChristoffel H P r s j *
    (∑ a, ∑ b, H b a * P r k b * Q q a l)) +
  (∑ r, c3JetChristoffel H P r s k *
    (∑ a, ∑ b, H b a * P j r b * Q q a l))

@[expose]
noncomputable def c3MetricJetZ
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (p k l : Fin n) : ℂ :=
  chartPartialZComplex (fun w => g w k l) z p

@[expose]
noncomputable def c3MetricJetBar
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (q k l : Fin n) : ℂ :=
  chartPartialBarComplex (fun w => g w k l) z q

@[expose]
noncomputable def c3MetricJetZBar
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (p q k l : Fin n) : ℂ :=
  chartPartialZComplex
    (fun w => chartPartialBarComplex (fun v => g v k l) w q) z p

@[expose]
noncomputable def c3MetricJetZZ
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (s p k l : Fin n) : ℂ :=
  chartPartialZComplex
    (fun w => chartPartialZComplex (fun v => g v k l) w p) z s

@[expose]
noncomputable def c3MetricJetZZBar
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (s p q k l : Fin n) : ℂ :=
  chartPartialZComplex
    (fun w => chartPartialZComplex
      (fun v => chartPartialBarComplex (fun u => g u k l) v q) w p) z s

theorem c3JetCovariantCurvature_eq_decomposition
    (H : Matrix (Fin n) (Fin n) ℂ)
    (P Q : Fin n → Fin n → Fin n → ℂ)
    (S V : Fin n → Fin n → Fin n → Fin n → ℂ)
    (W : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ)
    (s j q k l : Fin n) :
    c3JetCovariantCurvature H P Q S V W s j q k l =
      -W s j q k l + c3JetPureZZ H Q V s j q k l +
        c3JetMixed H P S s j q k l - c3JetQuartic H P Q s j q k l := by
  classical
  unfold c3JetCovariantCurvature c3JetCurvatureDerivative
    c3JetChristoffel c3JetCurvature c3JetPureZZ c3JetMixed c3JetQuartic
  simp only [c3JetChristoffel, Finset.sum_add_distrib, mul_add, mul_neg,
    Finset.sum_neg_distrib]
  simp only [neg_mul, Finset.sum_neg_distrib]
  ring_nf

theorem c3JetPureZZ_permute
    (H : Matrix (Fin n) (Fin n) ℂ)
    (Q : Fin n → Fin n → Fin n → ℂ)
    (V : Fin n → Fin n → Fin n → Fin n → ℂ)
    (hV : ∀ s p k b, V s p k b = V k s p b)
    (p j q k l : Fin n) :
    c3JetPureZZ H Q V p j q k l = c3JetPureZZ H Q V k p q j l := by
  simp [c3JetPureZZ, hV]

theorem c3JetCovariantCurvature_sub_permuted
    (H : Matrix (Fin n) (Fin n) ℂ)
    (P Q : Fin n → Fin n → Fin n → ℂ)
    (S V : Fin n → Fin n → Fin n → Fin n → ℂ)
    (W : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ)
    (hV : ∀ s p k b, V s p k b = V k s p b)
    (hMixed : ∀ p j q k l,
      c3JetMixed H P S p j q k l = c3JetMixed H P S k p q j l)
    (hQuartic : ∀ p j q k l,
      c3JetQuartic H P Q p j q k l = c3JetQuartic H P Q k p q j l)
    (p j q k l : Fin n) :
    c3JetCovariantCurvature H P Q S V W p j q k l -
      c3JetCovariantCurvature H P Q S V W k p q j l =
    -W p j q k l + W k p q j l := by
  simp only [c3JetCovariantCurvature_eq_decomposition]
  rw [c3JetPureZZ_permute H Q V hV p j q k l,
    hMixed p j q k l, hQuartic p j q k l]
  ring

end KahlerForm
