module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceCurvatureDerivative.Basic

/-!
# Cancellation of the two holomorphic curvature connection terms

Székelyhidi, §3.3, proof of Lemma 3.9, printed pp. 44–45. The hypotheses
are precisely the four-slot law, its first jet, and the lowered connection
law. No geometric covariance is assumed in the conclusion's guise.
-/

public section

open scoped BigOperators

namespace KahlerForm
/-- The two inhomogeneous Jacobian-derivative terms cancel the connection
corrections on the holomorphic curvature slots. Arbitrary finite arrays
suffice; no positivity, smoothness, or invertibility is used here. -/
theorem c3_covariant_curvature_pullback_algebra {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (dA : Fin n → Fin n → Fin n → ℂ)
    (Rx Ry : Fin n → Fin n → Fin n → Fin n → ℂ)
    (dx dy : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ)
    (Γx Γy : Fin n → Fin n → Fin n → ℂ)
    (hR : Ry = c3FourSlotPullback A Rx)
    (hdR : dy = c3FourSlotPullbackZJet A dA Rx dx)
    (hΓ : ∀ a s p : Fin n,
      (∑ i, A a i * Γy i s p) =
        dA s a p + ∑ u, ∑ v, A u s * A v p * Γx a u v) :
    c3CovariantFourTensorZJet Γy Ry dy =
      c3FiveSlotFrameContraction A (c3CovariantFourTensorZJet Γx Rx dx) := by
  classical
  have c3_complex_mul_expand_right
      (a b c d e f g : ℂ) :
      a * b * c * d * e * (f * g) = a * b * c * d * e * f * g := by
    simp [mul_assoc]

  have c3_lowered_gamma_curvature_contraction
      (A : Matrix (Fin n) (Fin n) ℂ)
      (GammaSource : Fin n → ℂ) (GammaTarget : Fin n → Fin n → Fin n → ℂ)
      (D F : Fin n → ℂ) (s r : Fin n)
      (hGamma : ∀ a, ∑ i, A a i * GammaSource i =
        D a + ∑ e, ∑ v, A e s * A v r * GammaTarget a e v) :
      ∑ i, GammaSource i * (∑ a, A a i * F a) =
        (∑ a, D a * F a) +
          ∑ e, ∑ v, A e s * A v r * (∑ a, GammaTarget a e v * F a) := by
    classical
    calc
      ∑ i, GammaSource i * (∑ a, A a i * F a) =
          ∑ a, (∑ i, A a i * GammaSource i) * F a := by
        calc
          _ = ∑ i, ∑ a, (A a i * GammaSource i) * F a := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a ha
            ring
          _ = ∑ a, ∑ i, (A a i * GammaSource i) * F a := Finset.sum_comm
          _ = ∑ a, (∑ i, A a i * GammaSource i) * F a := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [Finset.sum_mul]
      _ = ∑ a, (D a + ∑ e, ∑ v, A e s * A v r * GammaTarget a e v) * F a := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hGamma a]
      _ = (∑ a, D a * F a) +
          ∑ a, (∑ e, ∑ v, A e s * A v r * GammaTarget a e v) * F a := by
        calc
          _ = ∑ a, (D a * F a +
              (∑ e, ∑ v, A e s * A v r * GammaTarget a e v) * F a) := by
            apply Finset.sum_congr rfl
            intro a ha
            ring
          _ = _ := Finset.sum_add_distrib
      _ = (∑ a, D a * F a) +
          ∑ e, ∑ v, A e s * A v r * (∑ a, GammaTarget a e v * F a) := by
        congr 1
        calc
          ∑ a, (∑ e, ∑ v, A e s * A v r * GammaTarget a e v) * F a =
              ∑ a, ∑ e, ∑ v, (A e s * A v r * GammaTarget a e v) * F a := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro e he
            rw [Finset.sum_mul]
          _ = ∑ e, ∑ v, ∑ a, (A e s * A v r * GammaTarget a e v) * F a := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro e he
            rw [Finset.sum_comm]
          _ = ∑ e, ∑ v, A e s * A v r * (∑ a, GammaTarget a e v * F a) := by
            apply Finset.sum_congr rfl
            intro e he
            apply Finset.sum_congr rfl
            intro v hv
            calc
              _ = ∑ a, (A e s * A v r) * (GammaTarget a e v * F a) := by
                apply Finset.sum_congr rfl
                intro a ha
                ring
              _ = _ := by rw [Finset.mul_sum]

  have c3_scalar_mul_sum3 (c : ℂ)
      (F : Fin n → Fin n → Fin n → ℂ) :
      (∑ a, ∑ b, ∑ d, c * F a b d) = c * ∑ a, ∑ b, ∑ d, F a b d := by
    calc
      _ = ∑ a, ∑ b, c * ∑ d, F a b d := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        exact (Finset.mul_sum Finset.univ _ _).symm
      _ = ∑ a, c * ∑ b, ∑ d, F a b d := by
        apply Finset.sum_congr rfl
        intro a ha
        exact (Finset.mul_sum Finset.univ _ _).symm
      _ = c * ∑ a, ∑ b, ∑ d, F a b d := (Finset.mul_sum Finset.univ _ _).symm

  have c3_sum_swap_second_third4 {n : ℕ}
      (F : Fin n → Fin n → Fin n → Fin n → ℂ) :
      (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) =
        ∑ c, ∑ a, ∑ b, ∑ d, F a b c d := by
    calc
      _ = ∑ a, ∑ c, ∑ b, ∑ d, F a b c d := by
        apply Finset.sum_congr rfl
        intro a ha
        exact Finset.sum_comm
      _ = ∑ c, ∑ a, ∑ b, ∑ d, F a b c d := Finset.sum_comm

  have c3_move_last_sum_to_front5
      (F : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ) :
      (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, F a b c d e) =
        ∑ e, ∑ a, ∑ b, ∑ c, ∑ d, F a b c d e := by
    calc
      _ = ∑ a, ∑ b, ∑ c, ∑ e, ∑ d, F a b c d e := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        apply Finset.sum_congr rfl
        intro c hc
        exact Finset.sum_comm
      _ = ∑ a, ∑ b, ∑ e, ∑ c, ∑ d, F a b c d e := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        exact Finset.sum_comm
      _ = ∑ a, ∑ e, ∑ b, ∑ c, ∑ d, F a b c d e := by
        apply Finset.sum_congr rfl
        intro a ha
        exact Finset.sum_comm
      _ = ∑ e, ∑ a, ∑ b, ∑ c, ∑ d, F a b c d e := Finset.sum_comm

  /- Reindex the chain-rule derivative slot as the leading holomorphic slot in
  `∇R`'s fivefold transformed component. -/
  have c3_five_slot_chain_reindex
      (A : Matrix (Fin n) (Fin n) ℂ)
      (Q : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ)
      (s p q j k : Fin n) :
      ∑ a, ∑ b, ∑ c, ∑ d,
        A a p * star (A b q) * A c j * star (A d k) *
          (∑ e, A e s * Q e a b c d) =
      ∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
        A e s * A a p * star (A b q) * A c j * star (A d k) * Q e a b c d := by
    classical
    calc
      _ = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
          A a p * star (A b q) * A c j * star (A d k) * (A e s * Q e a b c d) := by
        simp only [Finset.mul_sum]
      _ = ∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
          A a p * star (A b q) * A c j * star (A d k) * (A e s * Q e a b c d) :=
        c3_move_last_sum_to_front5 _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro e he
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        apply Finset.sum_congr rfl
        intro c hc
        apply Finset.sum_congr rfl
        intro d hd
        ring

  have c3_five_slot_covariance_assembly
      (A : Matrix (Fin n) (Fin n) ℂ)
      (D : Fin n → Fin n → Fin n → ℂ)
      (R : Fin n → Fin n → Fin n → Fin n → ℂ)
      (dR : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ)
      (Rsource : Fin n → Fin n → Fin n → Fin n → ℂ)
      (dRsource : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ)
      (GammaTarget : Fin n → Fin n → Fin n → ℂ)
      (GammaSource : Fin n → Fin n → Fin n → ℂ)
      (s p q j k : Fin n)
      (hR : ∀ i q j k, Rsource i q j k =
        ∑ a, ∑ b, ∑ c, ∑ d,
          A a i * star (A b q) * A c j * star (A d k) * R a b c d)
      (hGamma : ∀ a s r,
        ∑ i, A a i * GammaSource i s r =
          D a s r + ∑ e, ∑ v, A e s * A v r * GammaTarget a e v)
      (Fp Fj : Fin n → ℂ)
      (hFp : ∀ a, Fp a = ∑ b, ∑ c, ∑ d,
        star (A b q) * A c j * star (A d k) * R a b c d)
      (hFj : ∀ c, Fj c = ∑ a, ∑ b, ∑ d,
        A a p * star (A b q) * star (A d k) * R a b c d)
      (hFirst : dRsource s p q j k =
        (∑ a, ∑ b, ∑ c, ∑ d,
          D a s p * star (A b q) * A c j * star (A d k) * R a b c d) +
        (∑ a, ∑ b, ∑ c, ∑ d,
          A a p * star (A b q) * D c s j * star (A d k) * R a b c d) +
        (∑ a, ∑ b, ∑ c, ∑ d,
          A a p * star (A b q) * A c j * star (A d k) *
            (∑ e, A e s * dR e a b c d))) :
      dRsource s p q j k -
        ∑ i, GammaSource i s p * Rsource i q j k -
          ∑ i, GammaSource i s j * Rsource p q i k =
        (∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
          A e s * A a p * star (A b q) * A c j * star (A d k) * dR e a b c d) -
        (∑ e, ∑ v, A e s * A v p * (∑ a, GammaTarget a e v * Fp a)) -
        (∑ e, ∑ v, A e s * A v j * (∑ c, GammaTarget c e v * Fj c)) := by
    classical
    have hRsourceP (i : Fin n) : Rsource i q j k = ∑ a, A a i * Fp a := by
      rw [hR i q j k]
      apply Finset.sum_congr rfl
      intro a ha
      calc
        _ = ∑ b, ∑ c, ∑ d,
            A a i * (star (A b q) * A c j * star (A d k) * R a b c d) := by
          apply Finset.sum_congr rfl
          intro b hb
          apply Finset.sum_congr rfl
          intro c hc
          apply Finset.sum_congr rfl
          intro d hd
          ring
        _ = A a i * Fp a := by
          rw [hFp a]
          exact c3_scalar_mul_sum3 (A a i)
            (fun b c d => star (A b q) * A c j * star (A d k) * R a b c d)
    have hRsourceJ (i : Fin n) : Rsource p q i k = ∑ c, A c i * Fj c := by
      rw [hR p q i k]
      calc
        _ = ∑ c, ∑ a, ∑ b, ∑ d,
            A a p * star (A b q) * A c i * star (A d k) * R a b c d :=
          c3_sum_swap_second_third4 _
        _ = ∑ c, ∑ a, ∑ b, ∑ d,
            A c i * (A a p * star (A b q) * star (A d k) * R a b c d) := by
          apply Finset.sum_congr rfl
          intro c hc
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          apply Finset.sum_congr rfl
          intro d hd
          ring
        _ = ∑ c, A c i * Fj c := by
          apply Finset.sum_congr rfl
          intro c hc
          rw [hFj c]
          exact c3_scalar_mul_sum3 (A c i)
            (fun a b d => A a p * star (A b q) * star (A d k) * R a b c d)
    have hGammaSourceP :
        ∑ i, GammaSource i s p * Rsource i q j k =
          (∑ a, D a s p * Fp a) +
            ∑ e, ∑ v, A e s * A v p * (∑ a, GammaTarget a e v * Fp a) := by
      calc
        _ = ∑ i, GammaSource i s p * (∑ a, A a i * Fp a) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hRsourceP i]
        _ = _ := c3_lowered_gamma_curvature_contraction A
          (fun i => GammaSource i s p) GammaTarget (fun a => D a s p) Fp s p
          (fun a => hGamma a s p)
    have hGammaSourceJ :
        ∑ i, GammaSource i s j * Rsource p q i k =
          (∑ c, D c s j * Fj c) +
            ∑ e, ∑ v, A e s * A v j * (∑ c, GammaTarget c e v * Fj c) := by
      calc
        _ = ∑ i, GammaSource i s j * (∑ c, A c i * Fj c) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hRsourceJ i]
        _ = _ := c3_lowered_gamma_curvature_contraction A
          (fun i => GammaSource i s j) GammaTarget (fun c => D c s j) Fj s j
          (fun c => hGamma c s j)
    have hDcancel :
        (∑ a, ∑ b, ∑ c, ∑ d,
          D a s p * star (A b q) * A c j * star (A d k) * R a b c d) +
        (∑ a, ∑ b, ∑ c, ∑ d,
          A a p * star (A b q) * D c s j * star (A d k) * R a b c d) =
          (∑ a, D a s p * Fp a) + (∑ c, D c s j * Fj c) := by
      have hp :
          (∑ a, ∑ b, ∑ c, ∑ d,
            D a s p * star (A b q) * A c j * star (A d k) * R a b c d) =
            ∑ a, D a s p * Fp a := by
        apply Finset.sum_congr rfl
        intro a ha
        calc
          _ = ∑ b, ∑ c, ∑ d,
              D a s p * (star (A b q) * A c j * star (A d k) * R a b c d) := by
            apply Finset.sum_congr rfl
            intro b hb
            apply Finset.sum_congr rfl
            intro c hc
            apply Finset.sum_congr rfl
            intro d hd
            ring
          _ = D a s p * Fp a := by
            rw [hFp a]
            exact c3_scalar_mul_sum3 (D a s p)
              (fun b c d => star (A b q) * A c j * star (A d k) * R a b c d)
      have hj :
          (∑ a, ∑ b, ∑ c, ∑ d,
            A a p * star (A b q) * D c s j * star (A d k) * R a b c d) =
            ∑ c, D c s j * Fj c := by
        calc
          _ = ∑ c, ∑ a, ∑ b, ∑ d,
              A a p * star (A b q) * D c s j * star (A d k) * R a b c d :=
            c3_sum_swap_second_third4 _
          _ = ∑ c, ∑ a, ∑ b, ∑ d,
              D c s j * (A a p * star (A b q) * star (A d k) * R a b c d) := by
            apply Finset.sum_congr rfl
            intro c hc
            apply Finset.sum_congr rfl
            intro a ha
            apply Finset.sum_congr rfl
            intro b hb
            apply Finset.sum_congr rfl
            intro d hd
            ring
          _ = ∑ c, D c s j * Fj c := by
            apply Finset.sum_congr rfl
            intro c hc
            rw [hFj c]
            exact c3_scalar_mul_sum3 (D c s j)
              (fun a b d => A a p * star (A b q) * star (A d k) * R a b c d)
      rw [hp, hj]
    let chain := ∑ a, ∑ b, ∑ c, ∑ d,
      A a p * star (A b q) * A c j * star (A d k) * (∑ e, A e s * dR e a b c d)
    let chainFive := ∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
      A e s * A a p * star (A b q) * A c j * star (A d k) * dR e a b c d
    have hchain : chain = chainFive := by
      dsimp [chain, chainFive]
      exact c3_five_slot_chain_reindex A dR s p q j k
    calc
      _ = (chain +
          ((∑ a, ∑ b, ∑ c, ∑ d,
              D a s p * star (A b q) * A c j * star (A d k) * R a b c d) +
            ∑ a, ∑ b, ∑ c, ∑ d,
              A a p * star (A b q) * D c s j * star (A d k) * R a b c d)) -
          ((∑ i, GammaSource i s p * Rsource i q j k) +
            ∑ i, GammaSource i s j * Rsource p q i k) := by
        rw [hFirst]
        dsimp [chain]
        ring
      _ = chain +
          ((∑ a, ∑ b, ∑ c, ∑ d,
              D a s p * star (A b q) * A c j * star (A d k) * R a b c d) +
            ∑ a, ∑ b, ∑ c, ∑ d,
              A a p * star (A b q) * D c s j * star (A d k) * R a b c d) -
          (((∑ a, D a s p * Fp a) +
              ∑ e, ∑ v, A e s * A v p * (∑ a, GammaTarget a e v * Fp a)) +
            ((∑ c, D c s j * Fj c) +
              ∑ e, ∑ v, A e s * A v j * (∑ c, GammaTarget c e v * Fj c))) := by
        rw [hGammaSourceP, hGammaSourceJ]
      _ = chain -
          (∑ e, ∑ v, A e s * A v p * (∑ a, GammaTarget a e v * Fp a)) -
          (∑ e, ∑ v, A e s * A v j * (∑ c, GammaTarget c e v * Fj c)) := by
        rw [hDcancel]
        ring
      _ = chainFive -
          (∑ e, ∑ v, A e s * A v p * (∑ a, GammaTarget a e v * Fp a)) -
          (∑ e, ∑ v, A e s * A v j * (∑ c, GammaTarget c e v * Fj c)) := by
        rw [hchain]

  have c3_move_third_to_last6 {n : ℕ}
      (F : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → ℂ) :
      (∑ e, ∑ v, ∑ x, ∑ b, ∑ c, ∑ d, F e v x b c d) =
        ∑ e, ∑ v, ∑ b, ∑ c, ∑ d, ∑ x, F e v x b c d := by
    calc
      _ = ∑ e, ∑ v, ∑ b, ∑ x, ∑ c, ∑ d, F e v x b c d := by
        apply Finset.sum_congr rfl
        intro e he
        apply Finset.sum_congr rfl
        intro v hv
        exact Finset.sum_comm
      _ = ∑ e, ∑ v, ∑ b, ∑ c, ∑ x, ∑ d, F e v x b c d := by
        apply Finset.sum_congr rfl
        intro e he
        apply Finset.sum_congr rfl
        intro v hv
        apply Finset.sum_congr rfl
        intro b hb
        exact Finset.sum_comm
      _ = ∑ e, ∑ v, ∑ b, ∑ c, ∑ d, ∑ x, F e v x b c d := by
        apply Finset.sum_congr rfl
        intro e he
        apply Finset.sum_congr rfl
        intro v hv
        apply Finset.sum_congr rfl
        intro b hb
        apply Finset.sum_congr rfl
        intro c hc
        exact Finset.sum_comm

  /- Expand the p-slot target connection correction in the same order as the
  five-slot frame contraction. -/
  have c3_p_gamma_contraction_expand
      (A : Matrix (Fin n) (Fin n) ℂ)
      (Gamma : Fin n → Fin n → Fin n → ℂ)
      (R : Fin n → Fin n → Fin n → Fin n → ℂ)
      (s p q j k : Fin n) :
      ∑ e, ∑ v, A e s * A v p *
        (∑ x, Gamma x e v *
          (∑ b, ∑ c, ∑ d,
            star (A b q) * A c j * star (A d k) * R x b c d)) =
      ∑ e, ∑ v, ∑ b, ∑ c, ∑ d, ∑ x,
        A e s * A v p * Gamma x e v * star (A b q) * A c j * star (A d k) * R x b c d := by
    classical
    simp only [Finset.mul_sum]
    rw [c3_move_third_to_last6]
    apply Finset.sum_congr rfl
    intro e he
    apply Finset.sum_congr rfl
    intro v hv
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro x hx
    ring

  /- Expand the j-slot target connection correction in the same order as the
  five-slot frame contraction. -/
  have auxiliary_j_gamma_contraction_expand
      (A : Matrix (Fin n) (Fin n) ℂ)
      (Gamma : Fin n → Fin n → Fin n → ℂ)
      (R : Fin n → Fin n → Fin n → Fin n → ℂ)
      (s p q j k : Fin n) :
      ∑ e, ∑ v, A e s * A v j *
        (∑ x, Gamma x e v *
          (∑ a, ∑ b, ∑ d,
            A a p * star (A b q) * star (A d k) * R a b x d)) =
      ∑ e, ∑ v, ∑ a, ∑ b, ∑ d, ∑ x,
        A e s * A v j * Gamma x e v * A a p * star (A b q) * star (A d k) * R a b x d := by
    classical
    simp only [Finset.mul_sum]
    rw [c3_move_third_to_last6]
    apply Finset.sum_congr rfl
    intro e he
    apply Finset.sum_congr rfl
    intro v hv
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro x hx
    ring

  have c3_move_second_to_fourth6 {n : ℕ}
      (F : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → ℂ) :
      (∑ e, ∑ v, ∑ a, ∑ b, ∑ d, ∑ x, F e v a b d x) =
        ∑ e, ∑ a, ∑ b, ∑ v, ∑ d, ∑ x, F e v a b d x := by
    calc
      _ = ∑ e, ∑ a, ∑ v, ∑ b, ∑ d, ∑ x, F e v a b d x := by
        apply Finset.sum_congr rfl
        intro e he
        exact Finset.sum_comm
      _ = ∑ e, ∑ a, ∑ b, ∑ v, ∑ d, ∑ x, F e v a b d x := by
        apply Finset.sum_congr rfl
        intro e he
        apply Finset.sum_congr rfl
        intro a ha
        exact Finset.sum_comm

  have c3_j_gamma_contraction_expand_frame_order
      (A : Matrix (Fin n) (Fin n) ℂ)
      (Gamma : Fin n → Fin n → Fin n → ℂ)
      (R : Fin n → Fin n → Fin n → Fin n → ℂ)
      (s p q j k : Fin n) :
      ∑ e, ∑ v, A e s * A v j *
        (∑ x, Gamma x e v *
          (∑ a, ∑ b, ∑ d,
            A a p * star (A b q) * star (A d k) * R a b x d)) =
      ∑ e, ∑ a, ∑ b, ∑ c, ∑ d, ∑ x,
        A e s * A a p * star (A b q) * A c j * star (A d k) *
          Gamma x e c * R a b x d := by
    calc
      _ = ∑ e, ∑ v, ∑ a, ∑ b, ∑ d, ∑ x,
          A e s * A v j * Gamma x e v * A a p * star (A b q) *
            star (A d k) * R a b x d :=
        auxiliary_j_gamma_contraction_expand A Gamma R s p q j k
      _ = ∑ e, ∑ a, ∑ b, ∑ c, ∑ d, ∑ x,
          A e s * A c j * Gamma x e c * A a p * star (A b q) *
            star (A d k) * R a b x d := by
        exact c3_move_second_to_fourth6 _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro e he
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        apply Finset.sum_congr rfl
        intro c hc
        apply Finset.sum_congr rfl
        intro d hd
        apply Finset.sum_congr rfl
        intro x hx
        ring
  funext s p q j k
  let Fp : Fin n → ℂ := fun a =>
    ∑ b, ∑ c, ∑ d, star (A b q) * A c j * star (A d k) * Rx a b c d
  let Fj : Fin n → ℂ := fun c =>
    ∑ a, ∑ b, ∑ d, A a p * star (A b q) * star (A d k) * Rx a b c d
  let pTarget := ∑ t, ∑ u, ∑ v, ∑ w, ∑ x, ∑ y,
    A t s * A u p * star (A v q) * A w j * star (A x k) *
      Γx y t u * Rx y v w x
  let jTarget := ∑ t, ∑ u, ∑ v, ∑ w, ∑ x, ∑ y,
    A t s * A u p * star (A v q) * A w j * star (A x k) *
      Γx y t w * Rx u v y x
  let pOuter := ∑ t, ∑ u, ∑ v, ∑ w, ∑ x,
    A t s * A u p * star (A v q) * A w j * star (A x k) *
      (∑ y, Γx y t u * Rx y v w x)
  let jOuter := ∑ t, ∑ u, ∑ v, ∑ w, ∑ x,
    A t s * A u p * star (A v q) * A w j * star (A x k) *
      (∑ y, Γx y t w * Rx u v y x)
  have hRarray : ∀ i q j k, Ry i q j k =
      ∑ a, ∑ b, ∑ c, ∑ d,
        A a i * star (A b q) * A c j * star (A d k) * Rx a b c d := by
    intro i q j k
    have h := congrArg (fun T : Fin n → Fin n → Fin n → Fin n → ℂ => T i q j k) hR
    change Ry i q j k =
      ∑ a, ∑ b, ∑ c, ∑ d,
        A a i * star (A b q) * A c j * star (A d k) * Rx a b c d at h
    exact h
  have hFp : ∀ a, Fp a = ∑ b, ∑ c, ∑ d,
      star (A b q) * A c j * star (A d k) * Rx a b c d := by
    intro a
    rfl
  have hFj : ∀ c, Fj c = ∑ a, ∑ b, ∑ d,
      A a p * star (A b q) * star (A d k) * Rx a b c d := by
    intro c
    rfl
  have hPexpand :
      (∑ t, ∑ u, A t s * A u p *
        (∑ y, Γx y t u * Fp y)) = pTarget := by
    have h0 :
        (∑ t, ∑ u, A t s * A u p *
          (∑ y, Γx y t u * Fp y)) =
        ∑ t, ∑ u, ∑ v, ∑ w, ∑ x, ∑ y,
          A t s * A u p * Γx y t u * star (A v q) * A w j *
            star (A x k) * Rx y v w x := by
      simpa [Fp] using
        (c3_p_gamma_contraction_expand A Γx Rx s p q j k)
    calc
      _ = ∑ t, ∑ u, ∑ v, ∑ w, ∑ x, ∑ y,
          A t s * A u p * Γx y t u * star (A v q) * A w j *
            star (A x k) * Rx y v w x := h0
      _ = pTarget := by
        apply Finset.sum_congr rfl
        intro t ht
        apply Finset.sum_congr rfl
        intro u hu
        apply Finset.sum_congr rfl
        intro v hv
        apply Finset.sum_congr rfl
        intro w hw
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        ac_rfl
  have hJexpand :
      (∑ t, ∑ u, A t s * A u j *
        (∑ y, Γx y t u * Fj y)) = jTarget := by
    simpa [jTarget, Fj] using
      (c3_j_gamma_contraction_expand_frame_order A Γx Rx s p q j k)
  have hpOuter : pOuter = pTarget := by
    dsimp [pOuter, pTarget]
    apply Finset.sum_congr rfl
    intro t ht
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    apply Finset.sum_congr rfl
    intro w hw
    apply Finset.sum_congr rfl
    intro x hx
    calc
      _ = ∑ y, (A t s * A u p * star (A v q) * A w j * star (A x k)) *
          (Γx y t u * Rx y v w x) :=
        Finset.mul_sum Finset.univ _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro y hy
        exact c3_complex_mul_expand_right (A t s) (A u p) (star (A v q))
          (A w j) (star (A x k)) (Γx y t u) (Rx y v w x)
  have hjOuter : jOuter = jTarget := by
    dsimp [jOuter, jTarget]
    apply Finset.sum_congr rfl
    intro t ht
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    apply Finset.sum_congr rfl
    intro w hw
    apply Finset.sum_congr rfl
    intro x hx
    calc
      _ = ∑ y, (A t s * A u p * star (A v q) * A w j * star (A x k)) *
          (Γx y t w * Rx u v y x) :=
        Finset.mul_sum Finset.univ _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro y hy
        exact c3_complex_mul_expand_right (A t s) (A u p) (star (A v q))
          (A w j) (star (A x k)) (Γx y t w) (Rx u v y x)
  have hsplit :
      (∑ a, ∑ b, ∑ c, ∑ d,
        (dA s a p * star (A b q) * A c j * star (A d k) +
          A a p * star (A b q) * dA s c j * star (A d k)) * Rx a b c d) =
      (∑ a, ∑ b, ∑ c, ∑ d,
        dA s a p * star (A b q) * A c j * star (A d k) * Rx a b c d) +
      (∑ a, ∑ b, ∑ c, ∑ d,
        A a p * star (A b q) * dA s c j * star (A d k) * Rx a b c d) := by
    calc
      _ = ∑ a, ∑ b, ∑ c, ∑ d,
          ((dA s a p * star (A b q) * A c j * star (A d k) * Rx a b c d) +
            (A a p * star (A b q) * dA s c j * star (A d k) * Rx a b c d)) := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        apply Finset.sum_congr rfl
        intro c hc
        apply Finset.sum_congr rfl
        intro d hd
        ring
      _ = _ := by simp only [Finset.sum_add_distrib]
  have hchain :
      (∑ a, ∑ b, ∑ c, ∑ d,
        A a p * star (A b q) * A c j * star (A d k) *
          (∑ e, A e s * dx e a b c d)) =
      ∑ e, ∑ a, ∑ b, ∑ c, ∑ d,
        A e s * A a p * star (A b q) * A c j * star (A d k) * dx e a b c d :=
    c3_five_slot_chain_reindex A dx s p q j k
  have hFirst : dy s p q j k =
      (∑ a, ∑ b, ∑ c, ∑ d,
        dA s a p * star (A b q) * A c j * star (A d k) * Rx a b c d) +
      (∑ a, ∑ b, ∑ c, ∑ d,
        A a p * star (A b q) * dA s c j * star (A d k) * Rx a b c d) +
      (∑ a, ∑ b, ∑ c, ∑ d,
        A a p * star (A b q) * A c j * star (A d k) *
          (∑ e, A e s * dx e a b c d)) := by
    have hjet := congrArg
      (fun T : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ => T s p q j k) hdR
    calc
      dy s p q j k = c3FourSlotPullbackZJet A dA Rx dx s p q j k := hjet
      _ = _ := by
        change
          (∑ a, ∑ b, ∑ c, ∑ d,
            (dA s a p * star (A b q) * A c j * star (A d k) +
              A a p * star (A b q) * dA s c j * star (A d k)) * Rx a b c d) +
            (∑ t, ∑ a, ∑ b, ∑ c, ∑ d,
              A t s * A a p * star (A b q) * A c j * star (A d k) * dx t a b c d) =
          (∑ a, ∑ b, ∑ c, ∑ d,
            dA s a p * star (A b q) * A c j * star (A d k) * Rx a b c d) +
          (∑ a, ∑ b, ∑ c, ∑ d,
            A a p * star (A b q) * dA s c j * star (A d k) * Rx a b c d) +
          (∑ a, ∑ b, ∑ c, ∑ d,
            A a p * star (A b q) * A c j * star (A d k) *
              (∑ e, A e s * dx e a b c d))
        rw [hsplit, ← hchain]
  let chainFive := ∑ t, ∑ u, ∑ v, ∑ w, ∑ x,
    A t s * A u p * star (A v q) * A w j * star (A x k) * dx t u v w x
  have hTargetOuter :
      c3FiveSlotFrameContraction A (c3CovariantFourTensorZJet Γx Rx dx) s p q j k =
        chainFive - pOuter - jOuter := by
    dsimp only [c3FiveSlotFrameContraction, c3CovariantFourTensorZJet,
      chainFive, pOuter, jOuter]
    simp only [mul_sub, Finset.sum_sub_distrib]
  have hTarget :
      c3FiveSlotFrameContraction A (c3CovariantFourTensorZJet Γx Rx dx) s p q j k =
        chainFive - pTarget - jTarget := by
    calc
      _ = chainFive - pOuter - jOuter := hTargetOuter
      _ = chainFive - pTarget - jTarget := by rw [hpOuter, hjOuter]
  calc
    _ = chainFive -
        (∑ t, ∑ u, A t s * A u p * (∑ y, Γx y t u * Fp y)) -
        (∑ t, ∑ u, A t s * A u j * (∑ y, Γx y t u * Fj y)) := by
      change dy s p q j k -
        (∑ i, Γy i s p * Ry i q j k) -
        (∑ i, Γy i s j * Ry p q i k) = _
      simpa [chainFive] using
        (c3_five_slot_covariance_assembly A (fun a s r => dA s a r)
          Rx dx Ry dy Γx Γy s p q j k hRarray hΓ Fp Fj hFp hFj hFirst)
    _ = chainFive - pTarget - jTarget := by rw [hPexpand, hJexpand]
    _ = c3FiveSlotFrameContraction A (c3CovariantFourTensorZJet Γx Rx dx) s p q j k :=
      hTarget.symm

end KahlerForm
