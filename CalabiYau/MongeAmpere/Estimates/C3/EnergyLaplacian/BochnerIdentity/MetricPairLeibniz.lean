module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.BochnerIdentity.OrderedJets
import CalabiYau.Mathlib.Analysis.Matrix.EntrywiseSmoothness
import Mathlib.Analysis.Calculus.FDeriv.Star

/-!
# Metric-compatible first differentiation of the tensor pairing

Székelyhidi, §3.3, proof of Lemma 3.9, printed pp. 44–45, (3.14).
The inverse entry is [q,p]; curvature begins with -partialZ_p(partialBar_q g).
The pairing is linear on the left and conjugate-linear on the right.
This computation uses only the stated
No off-target smoothness is assumed.
-/

@[expose] public section

open scoped Manifold ContDiff BigOperators ComplexOrder

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

private theorem c3Pair_sum_wirtinger_product
    (A B C : Fin n → ℂ) :
    (∑ i, ((A i - Complex.I * B i) / 2) * C i) =
      ((∑ i, A i * C i) - Complex.I * (∑ i, B i * C i)) / 2 := by
  calc
    _ = ∑ i, (A i * C i - Complex.I * B i * C i) / 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by
      have hI : (∑ i, Complex.I * B i * C i) =
          Complex.I * (∑ i, B i * C i) := by
        calc
          _ = ∑ i, Complex.I * (B i * C i) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = _ := (Finset.mul_sum _ _ _).symm
      rw [← Finset.sum_div, Finset.sum_sub_distrib, hI]

private theorem c3Pair_double_sum_wirtinger_product
    (A B C : Fin n → Fin n → ℂ) :
    (∑ i, ∑ j, ((A i j - Complex.I * B i j) / 2) * C i j) =
      ((∑ i, ∑ j, A i j * C i j) -
        Complex.I * (∑ i, ∑ j, B i j * C i j)) / 2 := by
  calc
    _ = ∑ i, ((∑ j, A i j * C i j) -
        Complex.I * (∑ j, B i j * C i j)) / 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact c3Pair_sum_wirtinger_product (A i) (B i) (C i)
    _ = _ := by
      simpa using c3Pair_sum_wirtinger_product
        (fun i ↦ ∑ j, A i j * C i j)
        (fun i ↦ ∑ j, B i j * C i j)
        (fun _ ↦ (1 : ℂ))

private theorem c3Pair_inverse_entry_partialZ
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hDiff : ∀ a b, DifferentiableAt ℝ (fun w ↦ g w a b) z)
    (hUnit : IsUnit (g z)) (p b j : Fin n) :
    wirtingerDerivInChart (fun w ↦ (g w)⁻¹ b j) z p =
      -(∑ a, ∑ l, (g z)⁻¹ b a *
        wirtingerDerivInChart (fun w ↦ g w a l) z p * (g z)⁻¹ l j) := by
  let vR := EuclideanSpace.single p (1 : ℂ)
  let vI := Complex.I • EuclideanSpace.single p (1 : ℂ)
  let dR := fun a l ↦ fderiv ℝ (fun w ↦ g w a l) z vR
  let dI := fun a l ↦ fderiv ℝ (fun w ↦ g w a l) z vI
  have hRe := Matrix.fderiv_inverse_entry_apply hDiff hUnit b j vR
  have hIm := Matrix.fderiv_inverse_entry_apply hDiff hUnit b j vI
  have hsum := c3Pair_double_sum_wirtinger_product
    (fun a l ↦ (g z)⁻¹ b a * dR a l * (g z)⁻¹ l j)
    (fun a l ↦ (g z)⁻¹ b a * dI a l * (g z)⁻¹ l j)
    (fun _ _ ↦ (1 : ℂ))
  have hweights :
      (∑ a, ∑ l, (g z)⁻¹ b a *
        wirtingerDerivInChart (fun w ↦ g w a l) z p * (g z)⁻¹ l j) =
        ((∑ a, ∑ l, (g z)⁻¹ b a * dR a l * (g z)⁻¹ l j) -
          Complex.I * (∑ a, ∑ l,
            (g z)⁻¹ b a * dI a l * (g z)⁻¹ l j)) / 2 := by
    calc
      _ = ∑ a, ∑ l,
          (((g z)⁻¹ b a * dR a l * (g z)⁻¹ l j) -
            Complex.I * ((g z)⁻¹ b a * dI a l * (g z)⁻¹ l j)) / 2 := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro l hl
        simp [wirtingerDerivInChart, dR, dI]
        ring
      _ = _ := by simpa [dR, dI] using hsum
  unfold wirtingerDerivInChart
  rw [show fderiv ℝ (fun w ↦ (g w)⁻¹ b j) z
      (EuclideanSpace.single p (1 : ℂ)) = fderiv ℝ (fun w ↦ (g w)⁻¹ b j) z vR from rfl]
  rw [show Complex.I • EuclideanSpace.single p (1 : ℂ) = vI from rfl]
  rw [hRe, hIm]
  have hweights' := hweights
  unfold wirtingerDerivInChart at hweights'
  simp only [dR, dI, vR, vI] at hweights'
  rw [hweights']
  ring

private theorem c3Pair_inverse_weight_christoffel_lower_slot
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hDiff : ∀ a b, DifferentiableAt ℝ (fun w ↦ g w a b) z)
    (hUnit : IsUnit (g z)) (p b : Fin n) (T : Fin n → ℂ) :
    (∑ j, wirtingerDerivInChart (fun w ↦ (g w)⁻¹ b j) z p * T j) =
      -(∑ j, (g z)⁻¹ b j *
        (∑ r, christoffelInChart g z r p j * T r)) := by
  have hEntry j := c3Pair_inverse_entry_partialZ g z hDiff hUnit p b j
  unfold christoffelInChart
  calc
    _ = -(∑ j, ∑ a, ∑ l,
        (g z)⁻¹ b a * wirtingerDerivInChart (fun w ↦ g w a l) z p *
          (g z)⁻¹ l j * T j) := by
      simp_rw [hEntry]
      simp only [Finset.sum_mul, neg_mul, Finset.sum_neg_distrib]
    _ = -(∑ a, ∑ j, ∑ l,
        (g z)⁻¹ b a * wirtingerDerivInChart (fun w ↦ g w a l) z p *
          (g z)⁻¹ l j * T j) := by
      congr 1
      exact Finset.sum_comm
    _ = _ := by
      congr 1
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro l hl
      ring

private theorem c3Pair_partialZ_weighted_term
    (g h k A B : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (p : Fin n)
    (hg : DifferentiableAt ℝ g z) (hh : DifferentiableAt ℝ h z)
    (hk : DifferentiableAt ℝ k z) (hA : DifferentiableAt ℝ A z)
    (hB : DifferentiableAt ℝ B z) :
    wirtingerDerivInChart (fun w ↦ g w * h w * k w * A w * star (B w)) z p =
      wirtingerDerivInChart g z p * h z * k z * A z * star (B z) +
        g z * wirtingerDerivInChart h z p * k z * A z * star (B z) +
        g z * h z * wirtingerDerivInChart k z p * A z * star (B z) +
        g z * h z * k z * wirtingerDerivInChart A z p * star (B z) +
        g z * h z * k z * A z * star (c3PartialBar B z p) := by
  let W₁ : EuclideanSpace ℂ (Fin n) → ℂ := fun w ↦ g w * h w
  let W₂ : EuclideanSpace ℂ (Fin n) → ℂ := fun w ↦ W₁ w * k w
  let W₃ : EuclideanSpace ℂ (Fin n) → ℂ := fun w ↦ W₂ w * A w
  have hW₁ : DifferentiableAt ℝ W₁ z :=
    (hg.hasFDerivAt.mul hh.hasFDerivAt).differentiableAt
  have hW₂ : DifferentiableAt ℝ W₂ z :=
    (hW₁.hasFDerivAt.mul hk.hasFDerivAt).differentiableAt
  have hW₃ : DifferentiableAt ℝ W₃ z :=
    (hW₂.hasFDerivAt.mul hA.hasFDerivAt).differentiableAt
  have hd₁ : wirtingerDerivInChart W₁ z p =
      wirtingerDerivInChart g z p * h z + g z * wirtingerDerivInChart h z p := by
    exact c3Pair_partialZ_mul g h z p hg hh
  have hd₂ : wirtingerDerivInChart W₂ z p =
      wirtingerDerivInChart W₁ z p * k z + W₁ z * wirtingerDerivInChart k z p := by
    exact c3Pair_partialZ_mul W₁ k z p hW₁ hk
  have hd₃ : wirtingerDerivInChart W₃ z p =
      wirtingerDerivInChart W₂ z p * A z + W₂ z * wirtingerDerivInChart A z p := by
    exact c3Pair_partialZ_mul W₂ A z p hW₂ hA
  change wirtingerDerivInChart (fun w ↦ W₃ w * star (B w)) z p = _
  rw [c3Pair_partialZ_mul W₃ (fun w ↦ star (B w)) z p hW₃ hB.star,
    c3Pair_partialZ_star B z p hB, hd₃, hd₂, hd₁]
  dsimp [W₁, W₂, W₃]
  ring

private theorem c3Pair_component_jet
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (A B : EuclideanSpace ℂ (Fin n) → Fin n → Fin n → Fin n → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (p i j k a b c : Fin n)
    (hg : DifferentiableAt ℝ (fun w ↦ g w i a) z)
    (hInv₁ : DifferentiableAt ℝ (fun w ↦ (g w)⁻¹ b j) z)
    (hInv₂ : DifferentiableAt ℝ (fun w ↦ (g w)⁻¹ c k) z)
    (hA : DifferentiableAt ℝ (fun w ↦ A w i j k) z)
    (hB : DifferentiableAt ℝ (fun w ↦ B w a b c) z) :
    wirtingerDerivInChart (fun w ↦ g w i a * (g w)⁻¹ b j * (g w)⁻¹ c k *
      A w i j k * star (B w a b c)) z p =
      wirtingerDerivInChart (fun w ↦ g w i a) z p * (g z)⁻¹ b j * (g z)⁻¹ c k *
          A z i j k * star (B z a b c) +
        g z i a * wirtingerDerivInChart (fun w ↦ (g w)⁻¹ b j) z p * (g z)⁻¹ c k *
          A z i j k * star (B z a b c) +
        g z i a * (g z)⁻¹ b j * wirtingerDerivInChart (fun w ↦ (g w)⁻¹ c k) z p *
          A z i j k * star (B z a b c) +
        g z i a * (g z)⁻¹ b j * (g z)⁻¹ c k *
          wirtingerDerivInChart (fun w ↦ A w i j k) z p * star (B z a b c) +
        g z i a * (g z)⁻¹ b j * (g z)⁻¹ c k * A z i j k *
          star (c3PartialBar (fun w ↦ B w a b c) z p) := by
  exact c3Pair_partialZ_weighted_term
    (fun w ↦ g w i a) (fun w ↦ (g w)⁻¹ b j) (fun w ↦ (g w)⁻¹ c k)
    (fun w ↦ A w i j k) (fun w ↦ B w a b c) z p hg hInv₁ hInv₂ hA hB

private theorem c3Pair_metric_upper_slot
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (p i a : Fin n)
    (hUnit : IsUnit (g z)) :
    wirtingerDerivInChart (fun w ↦ g w i a) z p =
      ∑ r, christoffelInChart g z r p i * g z r a := by
  have hinvMul : (g z)⁻¹ * g z = 1 := by
    obtain ⟨u, hu⟩ := hUnit
    rw [← hu]
    simp
  have hdelta (l : Fin n) :
      (∑ r, (g z)⁻¹ l r * g z r a) = if l = a then 1 else 0 := by
    have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A l a) hinvMul
    simpa [Matrix.mul_apply, Matrix.one_apply] using h
  unfold christoffelInChart
  calc
    wirtingerDerivInChart (fun w ↦ g w i a) z p =
        ∑ l, wirtingerDerivInChart (fun w ↦ g w i l) z p *
          (∑ r, (g z)⁻¹ l r * g z r a) := by
      simp_rw [hdelta]
      simp
    _ = ∑ r, (∑ l, (g z)⁻¹ l r *
          wirtingerDerivInChart (fun w ↦ g w i l) z p) * g z r a := by
      calc
        _ = ∑ l, ∑ r, wirtingerDerivInChart (fun w ↦ g w i l) z p *
              ((g z)⁻¹ l r * g z r a) := by
          apply Finset.sum_congr rfl
          intro l hl
          rw [Finset.mul_sum]
        _ = ∑ r, ∑ l, (g z)⁻¹ l r *
              wirtingerDerivInChart (fun w ↦ g w i l) z p * g z r a := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro r hr
          apply Finset.sum_congr rfl
          intro l hl
          ring
        _ = ∑ r, (∑ l, (g z)⁻¹ l r *
              wirtingerDerivInChart (fun w ↦ g w i l) z p) * g z r a := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [← Finset.sum_mul]

private theorem c3Pair_upper_weight_one_slot
    (G dG : Fin n → Fin n → ℂ) (Γ : Fin n → Fin n → ℂ)
    (a : Fin n) (T : Fin n → ℂ)
    (hG : ∀ i a, dG i a = ∑ r, Γ r i * G r a) :
    (∑ i, dG i a * T i) =
      ∑ r, G r a * (∑ i, Γ r i * T i) := by
  calc
    _ = ∑ i, ∑ r, Γ r i * G r a * T i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hG i a, Finset.sum_mul]
    _ = ∑ r, ∑ i, Γ r i * G r a * T i := Finset.sum_comm
    _ = ∑ r, G r a * (∑ i, Γ r i * T i) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

private theorem auxiliarySixSum_iLast
    (F : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c, F i j k a b c) =
      ∑ j, ∑ k, ∑ a, ∑ b, ∑ c, ∑ i, F i j k a b c := by
  calc
    _ = ∑ j, ∑ i, ∑ k, ∑ a, ∑ b, ∑ c, F i j k a b c := by
      exact Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ i, ∑ a, ∑ b, ∑ c, F i j k a b c := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ a, ∑ i, ∑ b, ∑ c, F i j k a b c := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      exact Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ a, ∑ b, ∑ i, ∑ c, F i j k a b c := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact Finset.sum_comm

private theorem auxiliaryUpperCompat
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (p : Fin n)
    (A B : Fin n → Fin n → Fin n → ℂ) (hUnit : IsUnit (g z)) :
    (∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
      wirtingerDerivInChart (fun w ↦ g w i a) z p * (g z)⁻¹ b j * (g z)⁻¹ c k *
        A i j k * star (B a b c)) =
    (∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
      g z i a * (g z)⁻¹ b j * (g z)⁻¹ c k *
        (∑ r, christoffelInChart g z i p r * A r j k) * star (B a b c)) := by
  have hm i a := c3Pair_metric_upper_slot g z p i a hUnit
  have hi (j k a b c : Fin n) :
      (∑ i, wirtingerDerivInChart (fun w ↦ g w i a) z p * (g z)⁻¹ b j *
        (g z)⁻¹ c k * A i j k * star (B a b c)) =
      ∑ i, g z i a * (g z)⁻¹ b j * (g z)⁻¹ c k *
        (∑ r, christoffelInChart g z i p r * A r j k) * star (B a b c) := by
    let Q := (g z)⁻¹ b j * (g z)⁻¹ c k * star (B a b c)
    calc
      _ = (∑ i, wirtingerDerivInChart (fun w ↦ g w i a) z p * A i j k) * Q := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [Q]
        ring
      _ = (∑ r, g z r a * (∑ i, christoffelInChart g z r p i * A i j k)) * Q := by
        exact congrArg (fun t : ℂ => t * Q)
          (c3Pair_upper_weight_one_slot (fun i a ↦ g z i a)
            (fun i a ↦ wirtingerDerivInChart (fun w ↦ g w i a) z p)
            (fun r i ↦ christoffelInChart g z r p i) a
            (fun i ↦ A i j k) hm)
      _ = _ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [Q]
        ring
  calc
    _ = ∑ j, ∑ k, ∑ a, ∑ b, ∑ c, ∑ i,
        wirtingerDerivInChart (fun w ↦ g w i a) z p * (g z)⁻¹ b j * (g z)⁻¹ c k *
          A i j k * star (B a b c) := auxiliarySixSum_iLast _
    _ = ∑ j, ∑ k, ∑ a, ∑ b, ∑ c, ∑ i,
        g z i a * (g z)⁻¹ b j * (g z)⁻¹ c k *
          (∑ r, christoffelInChart g z i p r * A r j k) * star (B a b c) := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      exact hi j k a b c
    _ = _ := (auxiliarySixSum_iLast _).symm

private theorem auxiliarySixSum_jLast
    (F : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c, F i j k a b c) =
      ∑ i, ∑ k, ∑ a, ∑ b, ∑ c, ∑ j, F i j k a b c := by
  calc
    _ = ∑ i, ∑ k, ∑ j, ∑ a, ∑ b, ∑ c, F i j k a b c := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ i, ∑ k, ∑ a, ∑ j, ∑ b, ∑ c, F i j k a b c := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk
      exact Finset.sum_comm
    _ = ∑ i, ∑ k, ∑ a, ∑ b, ∑ j, ∑ c, F i j k a b c := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact Finset.sum_comm

private theorem auxiliarySixSum_kLast
    (F : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c, F i j k a b c) =
      ∑ i, ∑ j, ∑ a, ∑ b, ∑ c, ∑ k, F i j k a b c := by
  calc
    _ = ∑ i, ∑ j, ∑ a, ∑ k, ∑ b, ∑ c, F i j k a b c := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ a, ∑ b, ∑ k, ∑ c, F i j k a b c := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact Finset.sum_comm

private theorem auxiliaryLowerKCompat
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (p : Fin n)
    (A B : Fin n → Fin n → Fin n → ℂ)
    (hDiff : ∀ a b, DifferentiableAt ℝ (fun w ↦ g w a b) z)
    (hUnit : IsUnit (g z)) :
    (∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
      g z i a * (g z)⁻¹ b j * wirtingerDerivInChart (fun w ↦ (g w)⁻¹ c k) z p *
        A i j k * star (B a b c)) =
    -(∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
      g z i a * (g z)⁻¹ b j * (g z)⁻¹ c k *
        (∑ r, christoffelInChart g z r p k * A i j r) * star (B a b c)) := by
  have hEach (i j a b c : Fin n) :
      (∑ k, g z i a * (g z)⁻¹ b j *
        wirtingerDerivInChart (fun w ↦ (g w)⁻¹ c k) z p * A i j k * star (B a b c)) =
      -(∑ k, g z i a * (g z)⁻¹ b j * (g z)⁻¹ c k *
        (∑ r, christoffelInChart g z r p k * A i j r) * star (B a b c)) := by
    calc
      _ = (∑ k, wirtingerDerivInChart (fun w ↦ (g w)⁻¹ c k) z p * A i j k) *
          (g z i a * (g z)⁻¹ b j * star (B a b c)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = -(∑ k, (g z)⁻¹ c k *
          (∑ r, christoffelInChart g z r p k * A i j r)) *
          (g z i a * (g z)⁻¹ b j * star (B a b c)) := by
        exact congrArg (fun t : ℂ => t * (g z i a * (g z)⁻¹ b j * star (B a b c)))
          (c3Pair_inverse_weight_christoffel_lower_slot g z hDiff hUnit p c
            (fun k ↦ A i j k))
      _ = _ := by
        rw [neg_mul, Finset.sum_mul]
        apply congrArg (fun t : ℂ => -(t))
        apply Finset.sum_congr rfl
        intro k hk
        ring
  calc
    _ = ∑ i, ∑ j, ∑ a, ∑ b, ∑ c, ∑ k,
        g z i a * (g z)⁻¹ b j * wirtingerDerivInChart (fun w ↦ (g w)⁻¹ c k) z p *
          A i j k * star (B a b c) := auxiliarySixSum_kLast _
    _ = ∑ i, ∑ j, ∑ a, ∑ b, ∑ c, ∑ k,
        -(g z i a * (g z)⁻¹ b j * (g z)⁻¹ c k *
          (∑ r, christoffelInChart g z r p k * A i j r) * star (B a b c)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.sum_neg_distrib]
      exact hEach i j a b c
    _ = -(∑ i, ∑ j, ∑ a, ∑ b, ∑ c, ∑ k,
        g z i a * (g z)⁻¹ b j * (g z)⁻¹ c k *
          (∑ r, christoffelInChart g z r p k * A i j r) * star (B a b c)) := by
      simp only [Finset.sum_neg_distrib]
    _ = _ := by
      congr 1
      exact (auxiliarySixSum_kLast _).symm

private theorem auxiliaryLowerJCompat
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (p : Fin n)
    (A B : Fin n → Fin n → Fin n → ℂ)
    (hDiff : ∀ a b, DifferentiableAt ℝ (fun w ↦ g w a b) z)
    (hUnit : IsUnit (g z)) :
    (∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
      g z i a * wirtingerDerivInChart (fun w ↦ (g w)⁻¹ b j) z p * (g z)⁻¹ c k *
        A i j k * star (B a b c)) =
    -(∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
      g z i a * (g z)⁻¹ b j * (g z)⁻¹ c k *
        (∑ r, christoffelInChart g z r p j * A i r k) * star (B a b c)) := by
  have hEach (i k a b c : Fin n) :
      (∑ j, g z i a * wirtingerDerivInChart (fun w ↦ (g w)⁻¹ b j) z p *
        (g z)⁻¹ c k * A i j k * star (B a b c)) =
      -(∑ j, g z i a * (g z)⁻¹ b j * (g z)⁻¹ c k *
        (∑ r, christoffelInChart g z r p j * A i r k) * star (B a b c)) := by
    calc
      _ = (∑ j, wirtingerDerivInChart (fun w ↦ (g w)⁻¹ b j) z p * A i j k) *
          (g z i a * (g z)⁻¹ c k * star (B a b c)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = -(∑ j, (g z)⁻¹ b j *
          (∑ r, christoffelInChart g z r p j * A i r k)) *
          (g z i a * (g z)⁻¹ c k * star (B a b c)) := by
        exact congrArg (fun t : ℂ => t * (g z i a * (g z)⁻¹ c k * star (B a b c)))
          (c3Pair_inverse_weight_christoffel_lower_slot g z hDiff hUnit p b
            (fun j ↦ A i j k))
      _ = _ := by
        rw [neg_mul, Finset.sum_mul]
        apply congrArg (fun t : ℂ => -(t))
        apply Finset.sum_congr rfl
        intro j hj
        ring
  calc
    _ = ∑ i, ∑ k, ∑ a, ∑ b, ∑ c, ∑ j,
        g z i a * wirtingerDerivInChart (fun w ↦ (g w)⁻¹ b j) z p *
          (g z)⁻¹ c k * A i j k * star (B a b c) := auxiliarySixSum_jLast _
    _ = ∑ i, ∑ k, ∑ a, ∑ b, ∑ c, -(∑ j,
        g z i a * (g z)⁻¹ b j * (g z)⁻¹ c k *
          (∑ r, christoffelInChart g z r p j * A i r k) * star (B a b c)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      exact hEach i k a b c
    _ = -(∑ i, ∑ k, ∑ a, ∑ b, ∑ c, ∑ j,
        g z i a * (g z)⁻¹ b j * (g z)⁻¹ c k *
          (∑ r, christoffelInChart g z r p j * A i r k) * star (B a b c)) := by
      simp only [Finset.sum_neg_distrib]
    _ = _ := by
      congr 1
      exact (auxiliarySixSum_jLast _).symm

omit [T2Space M] [CompactSpace M] in
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
theorem metricPairLeibnizOn_perturbed (ω₀ : KahlerForm n M)
    {φ : M → ℝ} (hφ : ω₀.IsPotential φ) (x : M) :
    MetricPairLeibnizOn (c3PerturbedMetricInChart ω₀ φ x)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
  let g := c3PerturbedMetricInChart ω₀ φ x
  let U := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target
  intro A B hA hB z hz p
  have hUopen : IsOpen U := isOpen_extChartAt_target x
  have hnb : U ∈ nhds z := hUopen.mem_nhds hz
  have hG (i a : Fin n) : DifferentiableAt ℝ (fun w ↦ g w i a) z := by
    have hcont := ((ω₀.perturb φ hφ).contDiffOn_metricInChart x i a).contDiffAt hnb
    have hevent : (fun w ↦ (ω₀.perturb φ hφ).metricInChart x w i a) =ᶠ[nhds z]
        (fun w ↦ g w i a) := by
      filter_upwards [hnb] with w hw
      rw [ω₀.metricInChart_perturb hφ x hw]
      rfl
    exact (hcont.congr_of_eventuallyEq hevent.symm).differentiableAt (by simp)
  have hUnit : IsUnit (g z) := by
    have hpos : (g z).PosDef := by
      simpa [g, c3PerturbedMetricInChart, ω₀.metricInChart_perturb hφ x hz] using
        (ω₀.perturb φ hφ).posDef_metricInChart x hz
    exact Matrix.PosDef.isUnit hpos
  have hInv (b j : Fin n) : DifferentiableAt ℝ (fun w ↦ (g w)⁻¹ b j) z := by
    exact (Matrix.hasFDerivAt_inverse_entry (fun a b ↦ (hG a b).hasFDerivAt)
      hUnit b j).differentiableAt
  have hAd (i j k : Fin n) : DifferentiableAt ℝ (fun w ↦ A w i j k) z := by
    exact ((hA i j k).contDiffAt hnb).differentiableAt (by simp)
  have hBd (a b c : Fin n) : DifferentiableAt ℝ (fun w ↦ B w a b c) z := by
    exact ((hB a b c).contDiffAt hnb).differentiableAt (by simp)
  have hSixSum
      (F : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n →
        EuclideanSpace ℂ (Fin n) → ℂ)
      (hF : ∀ i j k a b c, DifferentiableAt ℝ (fun w ↦ F i j k a b c w) z) :
      wirtingerDerivInChart (fun w ↦ ∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
        F i j k a b c w) z p =
        ∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
          wirtingerDerivInChart (fun w ↦ F i j k a b c w) z p := by
    have hC i j k a b : DifferentiableAt ℝ (fun w ↦ ∑ c, F i j k a b c w) z := by
      apply DifferentiableAt.fun_sum
      intro c hc
      exact hF i j k a b c
    have hB i j k a : DifferentiableAt ℝ (fun w ↦ ∑ b, ∑ c, F i j k a b c w) z := by
      apply DifferentiableAt.fun_sum
      intro b hb
      exact DifferentiableAt.fun_sum (fun c hc ↦ hF i j k a b c)
    have hA i j k : DifferentiableAt ℝ (fun w ↦ ∑ a, ∑ b, ∑ c, F i j k a b c w) z := by
      apply DifferentiableAt.fun_sum
      intro a ha
      exact DifferentiableAt.fun_sum (fun b hb ↦
        DifferentiableAt.fun_sum (fun c hc ↦ hF i j k a b c))
    have hK i j : DifferentiableAt ℝ (fun w ↦ ∑ k, ∑ a, ∑ b, ∑ c,
        F i j k a b c w) z := by
      apply DifferentiableAt.fun_sum
      intro k hk
      exact DifferentiableAt.fun_sum (fun a ha ↦
        DifferentiableAt.fun_sum (fun b hb ↦
          DifferentiableAt.fun_sum (fun c hc ↦ hF i j k a b c)))
    have hJ i : DifferentiableAt ℝ (fun w ↦ ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
        F i j k a b c w) z := by
      apply DifferentiableAt.fun_sum
      intro j hj
      exact DifferentiableAt.fun_sum (fun k hk ↦
        DifferentiableAt.fun_sum (fun a ha ↦
          DifferentiableAt.fun_sum (fun b hb ↦
            DifferentiableAt.fun_sum (fun c hc ↦ hF i j k a b c))))
    have eC i j k a b :
        wirtingerDerivInChart (fun w ↦ ∑ c, F i j k a b c w) z p =
          ∑ c, wirtingerDerivInChart (fun w ↦ F i j k a b c w) z p := by
      simpa using c3Pair_partialZ_finset_sum (s := Finset.univ)
        (fun c w ↦ F i j k a b c w) z p (by intro c hc; exact hF i j k a b c)
    have eB i j k a :
        wirtingerDerivInChart (fun w ↦ ∑ b, ∑ c, F i j k a b c w) z p =
          ∑ b, wirtingerDerivInChart (fun w ↦ ∑ c, F i j k a b c w) z p := by
      simpa using c3Pair_partialZ_finset_sum (s := Finset.univ)
        (fun b w ↦ ∑ c, F i j k a b c w) z p (by intro b hb; exact hC i j k a b)
    have eA i j k :
        wirtingerDerivInChart (fun w ↦ ∑ a, ∑ b, ∑ c, F i j k a b c w) z p =
          ∑ a, wirtingerDerivInChart (fun w ↦ ∑ b, ∑ c, F i j k a b c w) z p := by
      simpa using c3Pair_partialZ_finset_sum (s := Finset.univ)
        (fun a w ↦ ∑ b, ∑ c, F i j k a b c w) z p (by intro a ha; exact hB i j k a)
    have eK i j :
        wirtingerDerivInChart (fun w ↦ ∑ k, ∑ a, ∑ b, ∑ c, F i j k a b c w) z p =
          ∑ k, wirtingerDerivInChart (fun w ↦ ∑ a, ∑ b, ∑ c, F i j k a b c w) z p := by
      simpa using c3Pair_partialZ_finset_sum (s := Finset.univ)
        (fun k w ↦ ∑ a, ∑ b, ∑ c, F i j k a b c w) z p (by intro k hk; exact hA i j k)
    have eJ i :
        wirtingerDerivInChart (fun w ↦ ∑ j, ∑ k, ∑ a, ∑ b, ∑ c, F i j k a b c w) z p =
          ∑ j, wirtingerDerivInChart (fun w ↦ ∑ k, ∑ a, ∑ b, ∑ c, F i j k a b c w) z p := by
      simpa using c3Pair_partialZ_finset_sum (s := Finset.univ)
        (fun j w ↦ ∑ k, ∑ a, ∑ b, ∑ c, F i j k a b c w) z p (by intro j hj; exact hK i j)
    calc
      wirtingerDerivInChart (fun w ↦ ∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
          F i j k a b c w) z p =
          ∑ i, wirtingerDerivInChart (fun w ↦ ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
            F i j k a b c w) z p := by
        simpa using c3Pair_partialZ_finset_sum (s := Finset.univ)
          (fun i w ↦ ∑ j, ∑ k, ∑ a, ∑ b, ∑ c, F i j k a b c w) z p
          (by intro i hi; exact hJ i)
      _ = ∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
          wirtingerDerivInChart (fun w ↦ F i j k a b c w) z p := by
        simp_rw [eJ, eK, eA, eB, eC]
  let F : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n →
      EuclideanSpace ℂ (Fin n) → ℂ := fun i j k a b c w ↦
    g w i a * (g w)⁻¹ b j * (g w)⁻¹ c k * A w i j k * star (B w a b c)
  have hF (i j k a b c : Fin n) : DifferentiableAt ℝ (fun w ↦ F i j k a b c w) z := by
    dsimp [F]
    have h₁ : DifferentiableAt ℝ (fun w ↦ g w i a * (g w)⁻¹ b j) z :=
      ((hG i a).hasFDerivAt.mul (hInv b j).hasFDerivAt).differentiableAt
    have h₂ : DifferentiableAt ℝ
        (fun w ↦ g w i a * (g w)⁻¹ b j * (g w)⁻¹ c k) z :=
      (h₁.hasFDerivAt.mul (hInv c k).hasFDerivAt).differentiableAt
    have h₃ : DifferentiableAt ℝ
        (fun w ↦ g w i a * (g w)⁻¹ b j * (g w)⁻¹ c k * A w i j k) z :=
      (h₂.hasFDerivAt.mul (hAd i j k).hasFDerivAt).differentiableAt
    exact (h₃.hasFDerivAt.mul (hBd a b c).star.hasFDerivAt).differentiableAt
  have hJet := hSixSum F hF
  change wirtingerDerivInChart (fun w ↦ ∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
      F i j k a b c w) z p = _ at hJet
  have hJet' : wirtingerDerivInChart (fun w ↦ c3Pair g w (A w) (B w)) z p =
      ∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
        wirtingerDerivInChart (fun w ↦ F i j k a b c w) z p := by
    simpa only [c3Pair, F] using hJet
  have hTermJet (i j k a b c : Fin n) :=
    c3Pair_component_jet g A B z p i j k a b c (hG i a) (hInv b j) (hInv c k)
      (hAd i j k) (hBd a b c)
  have hJetExpanded : wirtingerDerivInChart (fun w ↦ c3Pair g w (A w) (B w)) z p =
      ∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
        (wirtingerDerivInChart (fun w ↦ g w i a) z p * (g z)⁻¹ b j * (g z)⁻¹ c k *
            A z i j k * star (B z a b c) +
          g z i a * wirtingerDerivInChart (fun w ↦ (g w)⁻¹ b j) z p * (g z)⁻¹ c k *
            A z i j k * star (B z a b c) +
          g z i a * (g z)⁻¹ b j * wirtingerDerivInChart (fun w ↦ (g w)⁻¹ c k) z p *
            A z i j k * star (B z a b c) +
          g z i a * (g z)⁻¹ b j * (g z)⁻¹ c k *
            wirtingerDerivInChart (fun w ↦ A w i j k) z p * star (B z a b c) +
          g z i a * (g z)⁻¹ b j * (g z)⁻¹ c k * A z i j k *
            star (c3PartialBar (fun w ↦ B w a b c) z p)) := by
    calc
      _ = ∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
          wirtingerDerivInChart (fun w ↦ F i j k a b c w) z p := hJet'
      _ = _ := by
        dsimp [F]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        apply Finset.sum_congr rfl
        intro c hc
        exact hTermJet i j k a b c
  let W : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → ℂ :=
    fun i j k a b c ↦ g z i a * (g z)⁻¹ b j * (g z)⁻¹ c k
  let Uterm : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → ℂ :=
    fun i j k a b c ↦ wirtingerDerivInChart (fun w ↦ g w i a) z p * (g z)⁻¹ b j *
      (g z)⁻¹ c k * A z i j k * star (B z a b c)
  let Vterm : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → ℂ :=
    fun i j k a b c ↦ g z i a * wirtingerDerivInChart (fun w ↦ (g w)⁻¹ b j) z p *
      (g z)⁻¹ c k * A z i j k * star (B z a b c)
  let Xterm : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → ℂ :=
    fun i j k a b c ↦ g z i a * (g z)⁻¹ b j *
      wirtingerDerivInChart (fun w ↦ (g w)⁻¹ c k) z p * A z i j k * star (B z a b c)
  let dA : Fin n → Fin n → Fin n → ℂ :=
    fun i j k ↦ wirtingerDerivInChart (fun w ↦ A w i j k) z p
  let dBbar : Fin n → Fin n → Fin n → ℂ :=
    fun a b c ↦ c3PartialBar (fun w ↦ B w a b c) z p
  let Γ : Fin n → Fin n → Fin n → ℂ := christoffelInChart g z
  have hU : (∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c, Uterm i j k a b c) =
      ∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
        W i j k a b c * (∑ r, Γ i p r * A z r j k) * star (B z a b c) := by
    simpa [Uterm, W, Γ] using
      auxiliaryUpperCompat g z p (A z) (B z) hUnit
  have hV : (∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c, Vterm i j k a b c) =
      -(∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
        W i j k a b c * (∑ r, Γ r p j * A z i r k) * star (B z a b c)) := by
    simpa [Vterm, W, Γ] using
      auxiliaryLowerJCompat g z p (A z) (B z) hG hUnit
  have hX : (∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c, Xterm i j k a b c) =
      -(∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
        W i j k a b c * (∑ r, Γ r p k * A z i j r) * star (B z a b c)) := by
    simpa [Xterm, W, Γ] using
      auxiliaryLowerKCompat g z p (A z) (B z) hG hUnit
  have hCov :
      (∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
        W i j k a b c *
          (dA i j k + (∑ r, Γ i p r * A z r j k) -
            (∑ r, Γ r p j * A z i r k) -
            (∑ r, Γ r p k * A z i j r)) * star (B z a b c)) =
      (∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
        W i j k a b c * dA i j k * star (B z a b c)) +
        (∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
          W i j k a b c * (∑ r, Γ i p r * A z r j k) * star (B z a b c)) -
        (∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
          W i j k a b c * (∑ r, Γ r p j * A z i r k) * star (B z a b c)) -
        (∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
          W i j k a b c * (∑ r, Γ r p k * A z i j r) * star (B z a b c)) := by
    have hterm (i j k a b c : Fin n) :
        W i j k a b c *
          (dA i j k + (∑ r, Γ i p r * A z r j k) -
            (∑ r, Γ r p j * A z i r k) -
            (∑ r, Γ r p k * A z i j r)) * star (B z a b c) =
          W i j k a b c * dA i j k * star (B z a b c) +
            W i j k a b c * (∑ r, Γ i p r * A z r j k) * star (B z a b c) -
            W i j k a b c * (∑ r, Γ r p j * A z i r k) * star (B z a b c) -
            W i j k a b c * (∑ r, Γ r p k * A z i j r) * star (B z a b c) := by ring
    calc
      _ = ∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
          (W i j k a b c * dA i j k * star (B z a b c) +
            W i j k a b c * (∑ r, Γ i p r * A z r j k) * star (B z a b c) -
            W i j k a b c * (∑ r, Γ r p j * A z i r k) * star (B z a b c) -
            W i j k a b c * (∑ r, Γ r p k * A z i j r) * star (B z a b c)) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        apply Finset.sum_congr rfl
        intro c hc
        exact hterm i j k a b c
      _ = _ := by simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hAssembly :
      (∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
        ((Uterm i j k a b c + Vterm i j k a b c) +
          (Xterm i j k a b c + W i j k a b c * dA i j k * star (B z a b c) +
            W i j k a b c * A z i j k * star (dBbar a b c)))) =
      c3Pair g z (c3TensorCovariantZ g A z p) (B z) +
        c3Pair g z (A z) (fun i j k ↦ c3PartialBar (fun w ↦ B w i j k) z p) := by
    simp_rw [Finset.sum_add_distrib] at hU hV hX ⊢
    rw [hU, hV, hX]
    simp_rw [c3Pair, c3TensorCovariantZ, W, Γ, dA, dBbar]
    rw [hCov]
    ring
  calc
    wirtingerDerivInChart (fun w ↦ c3Pair g w (A w) (B w)) z p =
        ∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
          ((((Uterm i j k a b c + Vterm i j k a b c) + Xterm i j k a b c) +
            W i j k a b c * dA i j k * star (B z a b c)) +
              W i j k a b c * A z i j k * star (dBbar a b c)) := by
      simpa only [c3Pair, Uterm, Vterm, Xterm, W, dA, dBbar] using hJetExpanded
    _ = c3Pair g z (c3TensorCovariantZ g A z p) (B z) +
        c3Pair g z (A z) (fun i j k ↦ c3PartialBar (fun w ↦ B w i j k) z p) := by
      simpa only [add_assoc] using hAssembly

end KahlerForm
