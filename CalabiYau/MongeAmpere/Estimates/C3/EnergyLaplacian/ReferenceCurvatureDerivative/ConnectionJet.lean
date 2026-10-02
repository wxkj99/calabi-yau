module

public import CalabiYau.MongeAmpere.Estimates.C3.CalabiEnergy.Basic
public import CalabiYau.Geometry.Kahler.Curvature.Chart.ConnectionGerm

/-!
# The lowered connection law used in curvature covariance

The existing connection germ accepts real smoothness and holomorphicity.
After evaluating it at the center, multiply by the forward Jacobian to
remove its inverse. The resulting inhomogeneous term has a plus sign.
Source: Székelyhidi, §1.4, pp. 10–11, and §3.3, proof of Lemma 3.9,
printed pp. 44–45 (GSM152 PDF physical pages 62–63).
-/

public section

open scoped Manifold ContDiff BigOperators

namespace KahlerForm

private theorem connectionJet_left_inverse_action {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) (hAB : A * B = 1)
    (F : Fin n → ℂ) (a : Fin n) :
    ∑ i, A a i * ∑ p, B i p * F p = F a := by
  classical
  have hcoef (p : Fin n) : ∑ i, A a i * B i p = if a = p then 1 else 0 := by
    have hentry := congrArg (fun X : Matrix (Fin n) (Fin n) ℂ => X a p) hAB
    simpa [Matrix.mul_apply, Matrix.one_apply] using hentry
  calc
    ∑ i, A a i * ∑ p, B i p * F p =
        ∑ i, ∑ p, (A a i * B i p) * F p := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ = ∑ p, (∑ i, A a i * B i p) * F p := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_mul]
    _ = ∑ p, (if a = p then 1 else 0) * F p := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [hcoef p]
    _ = F a := by simp

/-- Lower the output index in the actual nonlinear Christoffel pullback.
No complex-C² hypothesis is added: the closed public germ API supplies the
necessary local conversion from real smoothness plus holomorphicity. -/
theorem c3_connection_pullback_lowered {n : ℕ}
    (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (f : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (hf : ContDiffOn ℝ ∞ f U) (hhol : DifferentiableOn ℂ f U)
    (g g' : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (hg' : ∀ a b, ContDiffOn ℝ ∞ (fun w => g' w a b) (f '' U))
    (hmetric : ∀ w ∈ U, g w =
      (EuclideanSpace.clmMatrix (fderiv ℂ f w)).transpose * g' (f w) *
        (EuclideanSpace.clmMatrix (fderiv ℂ f w)).map star)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U)
    (hjac : IsUnit (EuclideanSpace.clmMatrix (fderiv ℂ f z)).det)
    (hgdet : IsUnit (g' (f z)).det) :
    let A := fun w => EuclideanSpace.clmMatrix (fderiv ℂ f w)
    ∀ a s p : Fin n,
      (∑ i, A z a i * christoffelInChart g z i s p) =
        chartPartialZComplex (fun w => A w a p) z s +
          ∑ u, ∑ v, A z u s * A z v p * christoffelInChart g' (f z) a u v := by
  classical
  dsimp only
  let A := fun w => EuclideanSpace.clmMatrix (fderiv ℂ f w)
  let B := (A z)⁻¹
  intro a s p
  have hAB : A z * B = 1 := Matrix.mul_nonsing_inv _ hjac
  have htrans := chartChristoffel_pullback_eventuallyEq U hU f hf hhol g g' hg' hmetric
    z hz hjac hgdet
  have htransAt (i : Fin n) :
      (∑ l, (g z)⁻¹ l i * chartPartialZComplex (fun v => g v p l) z s) =
      (∑ t, ∑ c, ∑ b, B i t * A z c s * A z b p *
        (∑ l, (g' (f z))⁻¹ l t * chartPartialZComplex (fun v => g' v b l) (f z) c)) +
      ∑ t, B i t * chartPartialZComplex (fun w => A w t p) z s := by
    have hh := (htrans i s p).eq_of_nhds
    exact hh
  have hGamma (i : Fin n) :
      christoffelInChart g z i s p =
        ∑ t, B i t *
          ((∑ c, ∑ b, A z c s * A z b p * christoffelInChart g' (f z) t c b) +
            chartPartialZComplex (fun w => A w t p) z s) := by
    change (∑ l, (g z)⁻¹ l i *
        chartPartialZComplex (fun v => g v p l) z s) =
      ∑ t, B i t *
        ((∑ c, ∑ b, A z c s * A z b p *
          (∑ l, (g' (f z))⁻¹ l t *
            chartPartialZComplex (fun v => g' v b l) (f z) c)) +
          chartPartialZComplex (fun w => A w t p) z s)
    rw [htransAt i, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    have hprod :
        (∑ c, ∑ b, B i t * A z c s * A z b p *
          (∑ l, (g' (f z))⁻¹ l t *
            chartPartialZComplex (fun v => g' v b l) (f z) c)) =
        B i t * (∑ c, ∑ b, A z c s * A z b p *
          (∑ l, (g' (f z))⁻¹ l t *
            chartPartialZComplex (fun v => g' v b l) (f z) c)) := by
      calc
        _ = ∑ c, ∑ b, B i t *
            (A z c s * A z b p *
              (∑ l, (g' (f z))⁻¹ l t *
                chartPartialZComplex (fun v => g' v b l) (f z) c)) := by
              apply Finset.sum_congr rfl
              intro c hc
              apply Finset.sum_congr rfl
              intro b hb
              ring
        _ = ∑ c, B i t *
            (∑ b, A z c s * A z b p *
              (∑ l, (g' (f z))⁻¹ l t *
                chartPartialZComplex (fun v => g' v b l) (f z) c)) := by
              apply Finset.sum_congr rfl
              intro c hc
              rw [Finset.mul_sum]
        _ = B i t * (∑ c, ∑ b, A z c s * A z b p *
            (∑ l, (g' (f z))⁻¹ l t *
              chartPartialZComplex (fun v => g' v b l) (f z) c)) := by
              rw [Finset.mul_sum]
    rw [hprod]
    ring
  calc
    ∑ i, A z a i * christoffelInChart g z i s p =
        ∑ i, A z a i *
          ∑ t, B i t *
            ((∑ c, ∑ b, A z c s * A z b p * christoffelInChart g' (f z) t c b) +
              chartPartialZComplex (fun w => A w t p) z s) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hGamma i]
    _ = (∑ c, ∑ b, A z c s * A z b p *
          christoffelInChart g' (f z) a c b) +
          chartPartialZComplex (fun w => A w a p) z s := by
      simpa using connectionJet_left_inverse_action (A z) B hAB
        (fun t => (∑ c, ∑ b, A z c s * A z b p *
          christoffelInChart g' (f z) t c b) +
          chartPartialZComplex (fun w => A w t p) z s) a
    _ = _ := by ring

end KahlerForm
