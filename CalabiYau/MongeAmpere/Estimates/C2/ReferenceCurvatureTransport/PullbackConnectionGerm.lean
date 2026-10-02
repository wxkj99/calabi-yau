module

public import CalabiYau.MongeAmpere.Estimates.C2.ReferenceCurvatureTransport.HolomorphicJacobianJet

/-!
# Connection of the actual coefficient pullback, as a germ

Székelyhidi §1.4, pp.11–12 (PDF 29–30). Expanding Γ = g⁻¹ ∂g in the convention
`G = J.transpose * (H ∘ f) * J.map star` gives a derivative-Jacobian term and a
three-index transformed source connection. Equality must hold on a neighborhood: its
antiholomorphic derivative cannot be inferred from equality only at the center.
-/

@[expose] public section

open scoped ContDiff ComplexOrder MatrixOrder
open Filter Topology

namespace KahlerForm

variable {n : ℕ}

private theorem pullbackMetric_c2_at
    (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (f : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (hf : ContDiffOn ℝ 3 f U)
    (H : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U)
    (hH : ∀ a b, ContDiffAt ℝ ∞ (fun w => H w a b) (f z))
    (hmetric : ∀ w ∈ U, G w = (holomorphicJacobianMatrix f w).transpose *
      H (f w) * (holomorphicJacobianMatrix f w).map star)
    (hjet : HolomorphicJacobianJetAt f z) :
    ∀ a b, ContDiffAt ℝ 2 (fun w => G w a b) z := by
  have hfz : ContDiffAt ℝ 2 f z := by
    exact ((hf z hz).contDiffAt (hU.mem_nhds hz)).of_le (by norm_num)
  have hHcomp (a b : Fin n) :
      ContDiffAt ℝ 2 (fun w => H (f w) a b) z := by
    have hHa : ContDiffAt ℝ 2 (fun y => H y a b) (f z) :=
      (hH a b).of_le
        (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
    exact hHa.comp z hfz
  have hJ (a b : Fin n) :
      ContDiffAt ℝ 2 (fun w => holomorphicJacobianMatrix f w a b) z :=
    hjet.jacobian_contDiff a b
  have hJstar (a b : Fin n) :
      ContDiffAt ℝ 2 (fun w => Complex.conjCLE (holomorphicJacobianMatrix f w a b)) z :=
    (Complex.conjCLE.contDiff.contDiffAt).comp z (hJ a b)
  intro a b
  have hformula : ContDiffAt ℝ 2
      (fun w => ((holomorphicJacobianMatrix f w).transpose * H (f w) *
        (holomorphicJacobianMatrix f w).map star) a b) z := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Complex.star_def,
      ← Complex.conjCLE_apply]
    change ContDiffAt ℝ 2
      (fun w => ∑ c, (∑ d, holomorphicJacobianMatrix f w d a * H (f w) d c) *
        Complex.conjCLE (holomorphicJacobianMatrix f w c b)) z
    apply ContDiffAt.sum (s := Finset.univ)
    intro c hc
    apply ContDiffAt.mul
    · apply ContDiffAt.sum (s := Finset.univ)
      intro d hd
      exact (hJ d a).mul (hHcomp d c)
    · exact hJstar c b
  have heq : (fun w => G w a b) =ᶠ[nhds z]
      (fun w => ((holomorphicJacobianMatrix f w).transpose * H (f w) *
        (holomorphicJacobianMatrix f w).map star) a b) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact congrFun (congrFun (hmetric w hw) a) b
  exact hformula.congr_of_eventuallyEq heq

/-- Chern connection with upper slot `i`, derivative slot `p`, and lower slot `j`.
The matrix inverse is indexed `[l,i]` for the row-holomorphic metric convention. -/
noncomputable def chartChernConnection
    (G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (i p j : Fin n) : ℂ :=
  ∑ l, (G z)⁻¹ l i * chartPartialZComplex (fun v => G v j l) z p

/-- Full connection transformation, including the inhomogeneous Jacobian derivative. -/
noncomputable def pullbackChernConnectionExpression
    (H : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (f : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) (i p j : Fin n) : ℂ :=
  (∑ s, ((holomorphicJacobianMatrix f z).transpose)⁻¹ s i *
    chartPartialZComplex (fun v => holomorphicJacobianMatrix f v s j) z p) +
  ∑ s, ∑ c, ∑ a, ((holomorphicJacobianMatrix f z).transpose)⁻¹ s i *
    holomorphicJacobianMatrix f z a j * holomorphicJacobianMatrix f z c p *
      chartChernConnection H (f z) s c a

/-- Finite regularity and the connection germ for an actual pullback.
The source is smooth only at the image center; the conclusion needs only C2 of `G`.
The pointwise pullback relation on the open domain prevents arbitrary off-center jets. -/

theorem pullbackConnection_germ
    (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (f : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (hf : ContDiffOn ℝ 3 f U) (hhol : DifferentiableOn ℂ f U)
    (G H : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U)
    (hH : ∀ a b, ContDiffAt ℝ ∞ (fun w => H w a b) (f z))
    (hjac : IsUnit (holomorphicJacobianMatrix f z).det)
    (hdet : IsUnit (H (f z)).det)
    (hmetric : ∀ w ∈ U, G w = (holomorphicJacobianMatrix f w).transpose *
      H (f w) * (holomorphicJacobianMatrix f w).map star)
    (hjet : HolomorphicJacobianJetAt f z) :
    (∀ a b, ContDiffAt ℝ 2 (fun w => G w a b) z) ∧
    (∀ i p j, (fun w => chartChernConnection G w i p j) =ᶠ[nhds z]
      (fun w => pullbackChernConnectionExpression H f w i p j)) := by
  refine ⟨pullbackMetric_c2_at U hU f hf H G z hz hH hmetric hjet, ?_⟩
  have hfz : ContDiffAt ℝ 2 f z := by
    exact ((hf z hz).contDiffAt (hU.mem_nhds hz)).of_le (by norm_num)
  have hHcomp (a b : Fin n) :
      ContDiffAt ℝ 2 (fun w => H (f w) a b) z := by
    have hHa : ContDiffAt ℝ 2 (fun y => H y a b) (f z) :=
      (hH a b).of_le
        (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
    exact hHa.comp z hfz
  let J := holomorphicJacobianMatrix f
  have hJentry (a b : Fin n) : ContDiffAt ℝ 2 (fun w => J w a b) z :=
    hjet.jacobian_contDiff a b
  have hJdet : ContDiffAt ℝ 2 (fun w => (J w).det) z := by
    simp_rw [Matrix.det_apply]
    fun_prop (disch := assumption)
  have hx : ∀ k l, ContDiffAt ℝ 2 (fun w => H (f w) k l) z := hHcomp
  have hHdet' : ContDiffAt ℝ 2
      (fun w => ∑ σ : Equiv.Perm (Fin n),
        Equiv.Perm.sign σ • ∏ i, H (f w) (σ i) i) z := by
    apply ContDiffAt.sum (s := Finset.univ)
    intro σ hσ
    apply ContDiffAt.const_smul
    apply contDiffAt_prod (t := Finset.univ)
    intro i hi
    exact hx (σ i) i
  have hHdet : ContDiffAt ℝ 2 (fun w => (H (f w)).det) z := by
    convert hHdet' using 1
    funext w
    exact Matrix.det_apply (H (f w))
  have hJdet_ne : ∀ᶠ w in nhds z, (J w).det ≠ 0 :=
    hJdet.continuousAt.eventually_ne hjac.ne_zero
  have hHdet_ne : ∀ᶠ w in nhds z, (H (f w)).det ≠ 0 :=
    hHdet.continuousAt.eventually_ne hdet.ne_zero
  have hdetUnits : ∀ᶠ w in nhds z,
      IsUnit (J w).det ∧ IsUnit (H (f w)).det := by
    filter_upwards [hJdet_ne, hHdet_ne] with w hwJ hwH
    exact ⟨isUnit_iff_ne_zero.mpr hwJ, isUnit_iff_ne_zero.mpr hwH⟩
  have hsumMove4 (g : Fin n → Fin n → Fin n → Fin n → ℂ) :
      (∑ x, ∑ a, ∑ b, ∑ r, g x a b r) = ∑ a, ∑ b, ∑ r, ∑ x, g x a b r := by
    calc
      _ = ∑ a, ∑ x, ∑ b, ∑ r, g x a b r := Finset.sum_comm
      _ = ∑ a, ∑ b, ∑ x, ∑ r, g x a b r := by
        apply Finset.sum_congr rfl
        intro a ha
        exact Finset.sum_comm
      _ = ∑ a, ∑ b, ∑ r, ∑ x, g x a b r := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        exact Finset.sum_comm
  have hsumMove5 (g : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ) :
      (∑ x, ∑ a, ∑ b, ∑ r, ∑ s, g x a b r s) =
        ∑ a, ∑ b, ∑ r, ∑ s, ∑ x, g x a b r s := by
    calc
      _ = ∑ a, ∑ x, ∑ b, ∑ r, ∑ s, g x a b r s := Finset.sum_comm
      _ = ∑ a, ∑ b, ∑ x, ∑ r, ∑ s, g x a b r s := by
        apply Finset.sum_congr rfl
        intro a ha
        exact Finset.sum_comm
      _ = ∑ a, ∑ b, ∑ r, ∑ x, ∑ s, g x a b r s := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        exact Finset.sum_comm
      _ = ∑ a, ∑ b, ∑ r, ∑ s, ∑ x, g x a b r s := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        apply Finset.sum_congr rfl
        intro r hr
        exact Finset.sum_comm
  have hFrameFormula
      (A AbarInv H₀ Hinv Ainv Ginv : Matrix (Fin n) (Fin n) ℂ)
      (dA : Fin n → Fin n → Fin n → ℂ)
      (dH : Fin n → Fin n → Fin n → ℂ)
      (p i k : Fin n)
      (hGinv : ∀ l, Ginv l i = ∑ r, ∑ s,
        AbarInv l r * Hinv r s * Ainv s i)
      (hBar : ∀ r b, ∑ l, AbarInv l r * star (A b l) = if b = r then 1 else 0)
      (hH : ∀ a s, ∑ b, Hinv b s * H₀ a b = if a = s then 1 else 0) :
      (∑ l, Ginv l i * (∑ a, ∑ b,
        (dA p a k * H₀ a b + A a k * (∑ c, A c p * dH c a b)) * star (A b l))) =
      (∑ s, Ainv s i * dA p s k) +
        ∑ s, ∑ c, ∑ a, Ainv s i * A a k * A c p *
          (∑ b, Hinv b s * dH c a b) := by
    classical
    have hcontract (a b r s : Fin n) :
        (∑ l, AbarInv l r * Hinv r s * Ainv s i *
          ((dA p a k * H₀ a b + A a k * (∑ c, A c p * dH c a b)) * star (A b l))) =
        Hinv r s * Ainv s i *
          (dA p a k * H₀ a b + A a k * (∑ c, A c p * dH c a b)) *
            (if b = r then 1 else 0) := by
      calc
        _ = ∑ l, (Hinv r s * Ainv s i *
            (dA p a k * H₀ a b + A a k * (∑ c, A c p * dH c a b))) *
              (AbarInv l r * star (A b l)) := by
          apply Finset.sum_congr rfl
          intro l hl
          ring
        _ = (Hinv r s * Ainv s i *
            (dA p a k * H₀ a b + A a k * (∑ c, A c p * dH c a b))) *
              ∑ l, AbarInv l r * star (A b l) := by rw [← Finset.mul_sum]
        _ = _ := by rw [hBar r b]
    simp_rw [hGinv]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [hsumMove5]
    have hcontractAll :
        (∑ a, ∑ b, ∑ r, ∑ s, ∑ l,
          AbarInv l r * Hinv r s * Ainv s i *
            ((dA p a k * H₀ a b + ∑ c, A a k * (A c p * dH c a b)) * star (A b l))) =
        ∑ a, ∑ b, ∑ r, ∑ s,
          Hinv r s * Ainv s i *
            (dA p a k * H₀ a b + A a k * (∑ c, A c p * dH c a b)) *
              (if b = r then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro s hs
      convert hcontract a b r s using 1
      rw [← Finset.mul_sum]
    rw [hcontractAll]
    simp_rw [mul_add, add_mul]
    simp_rw [Finset.sum_add_distrib]
    have hfirst :
        (∑ a, ∑ b, ∑ r, ∑ s,
          Hinv r s * Ainv s i * (dA p a k * H₀ a b) * if b = r then 1 else 0) =
        ∑ s, Ainv s i * dA p s k := by
      calc
        _ = ∑ a, ∑ r, ∑ s, ∑ b,
            Hinv r s * Ainv s i * (dA p a k * H₀ a b) * if b = r then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro r hr
          exact Finset.sum_comm
        _ = ∑ a, ∑ r, ∑ s, Hinv r s * Ainv s i * (dA p a k * H₀ a r) := by
          simp [Finset.sum_ite_eq', Finset.mem_univ]
        _ = ∑ a, ∑ s, ∑ r, Hinv r s * Ainv s i * (dA p a k * H₀ a r) := by
          apply Finset.sum_congr rfl
          intro a ha
          exact Finset.sum_comm
        _ = ∑ a, ∑ s, ∑ r,
            (Ainv s i * dA p a k) * (Hinv r s * H₀ a r) := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro s hs
          apply Finset.sum_congr rfl
          intro r hr
          ring
        _ = ∑ a, ∑ s, (Ainv s i * dA p a k) *
            (∑ r, Hinv r s * H₀ a r) := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro s hs
          rw [Finset.mul_sum]
        _ = ∑ a, ∑ s, (Ainv s i * dA p a k) * (if a = s then 1 else 0) := by
          simp_rw [hH]
        _ = ∑ s, Ainv s i * dA p s k := by
          simp [Finset.mem_univ]
    have hsecond :
        (∑ a, ∑ b, ∑ r, ∑ s,
          Hinv r s * Ainv s i * A a k * (∑ c, A c p * dH c a b) *
            if b = r then 1 else 0) =
        ∑ s, ∑ c, ∑ a, ∑ b,
          Ainv s i * A a k * A c p * Hinv b s * dH c a b := by
      calc
        _ = ∑ a, ∑ r, ∑ s, ∑ b,
            Hinv r s * Ainv s i * A a k * (∑ c, A c p * dH c a b) *
              if b = r then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro r hr
          exact Finset.sum_comm
        _ = ∑ a, ∑ r, ∑ s,
            Hinv r s * Ainv s i * A a k * (∑ c, A c p * dH c a r) := by
          simp [Finset.sum_ite_eq', Finset.mem_univ]
        _ = ∑ a, ∑ r, ∑ s, ∑ c,
            Hinv r s * Ainv s i * A a k * A c p * dH c a r := by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro r hr
          apply Finset.sum_congr rfl
          intro s hs
          apply Finset.sum_congr rfl
          intro c hc
          ring
        _ = ∑ r, ∑ s, ∑ c, ∑ a,
            Hinv r s * Ainv s i * A a k * A c p * dH c a r := by
          rw [hsumMove4]
        _ = ∑ s, ∑ c, ∑ a, ∑ r,
            Hinv r s * Ainv s i * A a k * A c p * dH c a r := by
          rw [hsumMove4]
        _ = ∑ s, ∑ c, ∑ a, ∑ r,
            Ainv s i * A a k * A c p * Hinv r s * dH c a r := by
          apply Finset.sum_congr rfl
          intro s hs
          apply Finset.sum_congr rfl
          intro c hc
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro r hr
          ring
    have hsecond' :
        (∑ a, ∑ b, ∑ r, ∑ s,
          Hinv r s * Ainv s i * (A a k * (∑ c, A c p * dH c a b)) *
            if b = r then 1 else 0) =
        ∑ s, ∑ c, ∑ a, ∑ b,
          Ainv s i * A a k * A c p * Hinv b s * dH c a b := by
      simpa [mul_assoc] using hsecond
    rw [hfirst, hsecond']
    simp [mul_assoc]
  have hDirectional (D : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ) (c : ℂ)
      (v : EuclideanSpace ℂ (Fin n)) :
      D (c • v) - Complex.I * D (Complex.I • (c • v)) =
        c * (D v - Complex.I * D (Complex.I • v)) := by
    have hc₁ : c • v = c.re • v + c.im • (Complex.I • v) := by
      calc
        c • v = ((c.re : ℂ) + (c.im : ℂ) * Complex.I) • v :=
          congrArg (fun z : ℂ => z • v) (Complex.re_add_im c).symm
        _ = c.re • v + c.im • (Complex.I • v) := by
          rw [RCLike.real_smul_eq_coe_smul (K := ℂ) c.re,
            RCLike.real_smul_eq_coe_smul (K := ℂ) c.im]
          rw [add_smul, smul_smul]
          rfl
    have hc₂ : Complex.I • (c • v) = -c.im • v + c.re • (Complex.I • v) := by
      have hscalar : Complex.I * c = ((-c.im : ℝ) : ℂ) + (c.re : ℝ) * Complex.I := by
        apply Complex.ext <;> simp
      calc
        Complex.I • (c • v) = (Complex.I * c) • v := by rw [smul_smul]
        _ = (((-c.im : ℝ) : ℂ) + (c.re : ℝ) * Complex.I) • v := by rw [hscalar]
        _ = -c.im • v + c.re • (Complex.I • v) := by
          rw [RCLike.real_smul_eq_coe_smul (K := ℂ) (-c.im),
            RCLike.real_smul_eq_coe_smul (K := ℂ) c.re]
          rw [add_smul, smul_smul]
          rfl
    rw [hc₂, hc₁]
    simp only [ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul]
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_eq_mul]
    conv_rhs => rw [← Complex.re_add_im c]
    ring_nf
    simp only [Complex.I_sq]
    push_cast
    linear_combination
  have hpartialZComp
      (F : EuclideanSpace ℂ (Fin n) → ℂ)
      (f : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
      (w : EuclideanSpace ℂ (Fin n)) (j : Fin n)
      (hF : DifferentiableAt ℝ F (f w)) (hf : DifferentiableAt ℂ f w) :
      chartPartialZComplex (fun v => F (f v)) w j =
        ∑ a, EuclideanSpace.clmMatrix (fderiv ℂ f w) a j *
          chartPartialZComplex F (f w) a := by
    let L := fderiv ℂ f w
    have hfℝ : DifferentiableAt ℝ f w := hf.restrictScalars ℝ
    have hreal : fderiv ℝ f w = L.restrictScalars ℝ := by
      simpa [L] using hf.fderiv_restrictScalars ℝ
    have hcomp := fderiv_comp (f := f) (g := F) (x := w) hF hfℝ
    have hcomp' : fderiv ℝ (fun v => F (f v)) w =
        (fderiv ℝ F (f w)).comp (fderiv ℝ f w) := by
      simpa [Function.comp_def] using hcomp
    let D := fderiv ℝ F (f w)
    let A := EuclideanSpace.clmMatrix L
    let e := EuclideanSpace.single j (1 : ℂ)
    have hvec : L e = ∑ a, (A a j) • EuclideanSpace.single a (1 : ℂ) := by
      ext b
      simp [A, e, EuclideanSpace.clmMatrix, Pi.single_apply]
    unfold chartPartialZComplex
    rw [hcomp', hreal]
    simp only [ContinuousLinearMap.comp_apply]
    change (D (L e) - Complex.I * D (L (Complex.I • e))) / 2 = _
    rw [map_smul, hvec]
    simp only [map_sum, Finset.smul_sum]
    have hsum :
        (∑ a, D ((A a j) • EuclideanSpace.single a (1 : ℂ))) -
          Complex.I * ∑ a, D (Complex.I • ((A a j) • EuclideanSpace.single a (1 : ℂ))) =
        ∑ a, (D ((A a j) • EuclideanSpace.single a (1 : ℂ)) -
          Complex.I * D (Complex.I • ((A a j) • EuclideanSpace.single a (1 : ℂ)))) := by
      rw [Finset.mul_sum, Finset.sum_sub_distrib]
    rw [hsum]
    simp_rw [hDirectional]
    simp only [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have hpartialZSum
      (F : Fin n → EuclideanSpace ℂ (Fin n) → ℂ)
      (w : EuclideanSpace ℂ (Fin n)) (j : Fin n)
      (hF : ∀ i, DifferentiableAt ℝ (F i) w) :
      chartPartialZComplex (fun v => ∑ i, F i v) w j =
        ∑ i, chartPartialZComplex (F i) w j := by
    unfold chartPartialZComplex
    have hfd : fderiv ℝ (fun v => ∑ i, F i v) w = ∑ i, fderiv ℝ (F i) w := by
      simpa using fderiv_fun_sum (u := Finset.univ) (fun i hi => hF i)
    rw [hfd]
    simp only [sum_apply]
    have hsum :
        (∑ i, fderiv ℝ (F i) w (EuclideanSpace.single j 1)) -
          Complex.I * ∑ i, fderiv ℝ (F i) w (Complex.I • EuclideanSpace.single j 1) =
        ∑ i, (fderiv ℝ (F i) w (EuclideanSpace.single j 1) -
          Complex.I * fderiv ℝ (F i) w (Complex.I • EuclideanSpace.single j 1)) := by
      rw [Finset.mul_sum, Finset.sum_sub_distrib]
    rw [hsum]
    simp only [div_eq_mul_inv, Finset.sum_mul]
  have hpartialZMul
      (F G : EuclideanSpace ℂ (Fin n) → ℂ)
      (w : EuclideanSpace ℂ (Fin n)) (j : Fin n)
      (hF : DifferentiableAt ℝ F w) (hG : DifferentiableAt ℝ G w) :
      chartPartialZComplex (fun v => F v * G v) w j =
        chartPartialZComplex F w j * G w + F w * chartPartialZComplex G w j := by
    unfold chartPartialZComplex
    rw [fderiv_fun_mul hF hG]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    ring
  have hstarPartialZ (F : EuclideanSpace ℂ (Fin n) → ℂ)
      (w : EuclideanSpace ℂ (Fin n)) (q : Fin n)
      (hF : DifferentiableAt ℝ F w) :
      chartPartialZComplex (fun v => Complex.conjCLE (F v)) w q =
        Complex.conjCLE (chartPartialBarComplex F w q) := by
    have hcomp : fderiv ℝ (fun v => Complex.conjCLE (F v)) w =
        Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ F w) := by
      exact (Complex.conjCLE.hasFDerivAt.comp w hF.hasFDerivAt).fderiv
    unfold chartPartialZComplex chartPartialBarComplex
    rw [hcomp]
    change (star (fderiv ℝ F w (EuclideanSpace.single q 1)) -
        Complex.I * star (fderiv ℝ F w (Complex.I • EuclideanSpace.single q 1))) / 2 =
      star ((fderiv ℝ F w (EuclideanSpace.single q 1) +
        Complex.I * fderiv ℝ F w (Complex.I • EuclideanSpace.single q 1)) / 2)
    simp [star_add, star_mul, Complex.conj_I]
    ring
  have hGinvFormula (w : EuclideanSpace ℂ (Fin n)) (hw : w ∈ U)
      (hunit : IsUnit (J w).det ∧ IsUnit (H (f w)).det) :
      (G w)⁻¹ = ((J w).map star)⁻¹ * (H (f w))⁻¹ * (J w).transpose⁻¹ := by
    have hBdet : ((J w).map star).det = star ((J w).det) := by
      simpa using ((starRingEnd ℂ).map_det (J w)).symm
    have hBunit : IsUnit ((J w).map star) := by
      apply (Matrix.isUnit_iff_isUnit_det _).2
      rw [hBdet]
      exact hunit.1.map (starRingEnd ℂ)
    have hHunit : IsUnit (H (f w)) :=
      (Matrix.isUnit_iff_isUnit_det _).2 hunit.2
    have hTunit : IsUnit ((J w).transpose) := by
      apply (Matrix.isUnit_iff_isUnit_det _).2
      simpa [Matrix.det_transpose] using hunit.1
    apply Matrix.inv_eq_right_inv
    rw [hmetric w hw]
    change ((J w).transpose * H (f w) * (J w).map star) *
      (((J w).map star)⁻¹ * (H (f w))⁻¹ * (J w).transpose⁻¹) = 1
    calc
      _ = (J w).transpose * H (f w) *
          ((J w).map star * ((J w).map star)⁻¹ * (H (f w))⁻¹ * (J w).transpose⁻¹) := by
        simp only [Matrix.mul_assoc]
      _ = (J w).transpose * H (f w) *
          (1 * (H (f w))⁻¹ * (J w).transpose⁻¹) := by
        rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hBunit)]
      _ = (J w).transpose * H (f w) *
          ((H (f w))⁻¹ * (J w).transpose⁻¹) := by simp
      _ = (J w).transpose *
          (H (f w) * ((H (f w))⁻¹ * (J w).transpose⁻¹)) := by
        rw [Matrix.mul_assoc]
      _ = (J w).transpose *
          ((H (f w) * (H (f w))⁻¹) * (J w).transpose⁻¹) := by
        rw [Matrix.mul_assoc]
      _ = (J w).transpose *
          (1 * (J w).transpose⁻¹) := by
        rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hHunit)]
      _ = (J w).transpose * (J w).transpose⁻¹ := by simp
      _ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hTunit)
  have hmetricDerivative (w : EuclideanSpace ℂ (Fin n)) (hw : w ∈ U)
      (a b p : Fin n) :
      chartPartialZComplex (fun v => G v a b) w p =
        chartPartialZComplex
          (fun v => ((J v).transpose * H (f v) * (J v).map star) a b)
          w p := by
    have heq : (fun v => G v a b) =ᶠ[nhds w]
        (fun v => ((J v).transpose * H (f v) * (J v).map star) a b) := by
      filter_upwards [hU.mem_nhds hw] with v hv
      exact congrFun (congrFun (hmetric v hv) a) b
    unfold chartPartialZComplex
    rw [heq.fderiv_eq]
  have hmetricDerivExpansion
      (w : EuclideanSpace ℂ (Fin n)) (p k l : Fin n)
      (hmetricD : chartPartialZComplex (fun v => G v k l) w p =
        chartPartialZComplex (fun v => ((J v).transpose * H (f v) * (J v).map star) k l) w p)
      (hJcont : ∀ a b, ContDiffAt ℝ 2 (fun v => J v a b) w)
      (hKdiff : ∀ a b, DifferentiableAt ℝ (fun v => H (f v) a b) w)
      (hstarZero : ∀ b, chartPartialZComplex
        (fun v => Complex.conjCLE (J v b l)) w p = 0) :
      chartPartialZComplex (fun v => G v k l) w p =
        ∑ b, ∑ a,
          (chartPartialZComplex (fun v => J v a k) w p * H (f w) a b +
            J w a k * chartPartialZComplex (fun v => H (f v) a b) w p) *
              Complex.conjCLE (J w b l) := by
    rw [hmetricD]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    change chartPartialZComplex
        (fun v => ∑ b, (∑ a, J v a k * H (f v) a b) *
          Complex.conjCLE (J v b l)) w p = _
    have hJdiff (a b : Fin n) : DifferentiableAt ℝ (fun v => J v a b) w :=
      (hJcont a b).differentiableAt (by norm_num)
    have hprodDiff (a b : Fin n) : DifferentiableAt ℝ
        (fun v => J v a k * H (f v) a b) w := (hJdiff a k).mul (hKdiff a b)
    have hsumDiff (b : Fin n) : DifferentiableAt ℝ
        (fun v => ∑ a, J v a k * H (f v) a b) w :=
      DifferentiableAt.fun_sum (fun a ha => hprodDiff a b)
    have hconjDiff (b : Fin n) : DifferentiableAt ℝ
        (fun v => Complex.conjCLE (J v b l)) w :=
      (Complex.conjCLE.contDiff.contDiffAt).comp w (hJcont b l) |>.differentiableAt
        (by norm_num)
    have houterDiff (b : Fin n) : DifferentiableAt ℝ
        (fun v => (∑ a, J v a k * H (f v) a b) *
          Complex.conjCLE (J v b l)) w := hsumDiff b |>.mul (hconjDiff b)
    rw [hpartialZSum _ w p houterDiff]
    apply Finset.sum_congr rfl
    intro b hb
    rw [hpartialZMul (fun v => ∑ a, J v a k * H (f v) a b)
        (fun v => Complex.conjCLE (J v b l)) w p (hsumDiff b) (hconjDiff b),
      hstarZero b, mul_zero, add_zero]
    rw [hpartialZSum (fun a v => J v a k * H (f v) a b) w p
      (fun a => hprodDiff a b)]
    rw [← Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro a ha
    rw [hpartialZMul (fun v => J v a k) (fun v => H (f v) a b) w p
      (hJdiff a k) (hKdiff a b)]
  have hHsourceDiff (a b : Fin n) : ∀ᶠ w in nhds z,
      DifferentiableAt ℝ (fun y => H y a b) (f w) := by
    obtain ⟨V, hV, hCV⟩ := (hH a b).contDiffOn (m := 1) (by norm_num)
      (by intro h; norm_num at h)
    rcases mem_nhds_iff.mp hV with ⟨s, hsV, hsopen, hsz⟩
    have hpre : ∀ᶠ w in nhds z, f w ∈ s :=
      hfz.continuousAt.preimage_mem_nhds (hsopen.mem_nhds hsz)
    have hCVs : ContDiffOn ℝ 1 (fun y => H y a b) s := hCV.mono hsV
    filter_upwards [hpre] with w hw
    have hAt : ContDiffAt ℝ 1 (fun y => H y a b) (f w) :=
      (hCVs (f w) hw).contDiffAt (hsopen.mem_nhds hw)
    exact hAt.differentiableAt (by norm_num)
  have hHsourceDiffAll : ∀ᶠ w in nhds z, ∀ a b,
      DifferentiableAt ℝ (fun y => H y a b) (f w) := by
    rw [Filter.eventually_all]
    intro a
    rw [Filter.eventually_all]
    intro b
    exact hHsourceDiff a b
  have hJdiff (a b : Fin n) : ∀ᶠ w in nhds z,
      DifferentiableAt ℝ (fun v => J v a b) w := by
    have hcont := (hjet.jacobian_contDiff a b).eventually (by norm_num)
    filter_upwards [hcont] with w hw
    exact hw.differentiableAt (by norm_num)
  have hJdiffAll : ∀ᶠ w in nhds z, ∀ a b,
      DifferentiableAt ℝ (fun v => J v a b) w := by
    rw [Filter.eventually_all]
    intro a
    rw [Filter.eventually_all]
    intro b
    exact hJdiff a b
  have hgood : ∀ᶠ w in nhds z,
      w ∈ U ∧ (IsUnit (J w).det ∧ IsUnit (H (f w)).det) := by
    filter_upwards [hU.mem_nhds hz, hdetUnits] with w hw hunit
    exact ⟨hw, hunit⟩
  have hconnection : ∀ i p j,
      (fun w => chartChernConnection G w i p j) =ᶠ[nhds z]
        (fun w => pullbackChernConnectionExpression H f w i p j) := by
    intro i p j
    filter_upwards [hgood, hHsourceDiffAll, hJdiffAll] with w hwGood hHdiff hJdiff
    rcases hwGood with ⟨hw, hunit⟩
    have hGinv := hGinvFormula w hw hunit
    have hjetW := holomorphicJacobianJetAt_of_contDiffOn
      U hU f hf hhol w hw hunit.1
    have hstarJzero (a b : Fin n) :
        chartPartialZComplex (fun v => Complex.conjCLE (J v a b)) w p = 0 := by
      rw [hstarPartialZ (fun v => J v a b) w p (hJdiff a b)]
      rw [hjetW.jacobian_bar_zero a b p]
      simp
    have hfAt : DifferentiableAt ℂ f w :=
      (hhol w hw).differentiableAt (hU.mem_nhds hw)
    have hfReal : DifferentiableAt ℝ f w := hfAt.restrictScalars ℝ
    have hKdiff (a b : Fin n) : DifferentiableAt ℝ
        (fun v => H (f v) a b) w := (hHdiff a b).comp w hfReal
    have hKderiv (a b : Fin n) :
        chartPartialZComplex (fun v => H (f v) a b) w p =
          ∑ c, J w c p * chartPartialZComplex (fun y => H y a b) (f w) c := by
      simpa [J, holomorphicJacobianMatrix] using
        hpartialZComp (fun y => H y a b) f w p (hHdiff a b) hfAt
    have hGderiv (k l : Fin n) :
        chartPartialZComplex (fun v => G v k l) w p =
          ∑ b, ∑ a,
            (chartPartialZComplex (fun v => J v a k) w p * H (f w) a b +
              J w a k * (∑ c, J w c p * chartPartialZComplex
                (fun y => H y a b) (f w) c)) * Complex.conjCLE (J w b l) := by
      calc
        _ = ∑ b, ∑ a,
            (chartPartialZComplex (fun v => J v a k) w p * H (f w) a b +
              J w a k * chartPartialZComplex (fun v => H (f v) a b) w p) *
                Complex.conjCLE (J w b l) :=
          hmetricDerivExpansion w p k l (hmetricDerivative w hw k l p)
            (fun a b => hjetW.jacobian_contDiff a b) hKdiff
            (fun b => hstarJzero b l)
        _ = _ := by
          apply Finset.sum_congr rfl
          intro b hb
          apply Finset.sum_congr rfl
          intro a ha
          rw [hKderiv a b]
    have hGderivAB (k l : Fin n) :
        chartPartialZComplex (fun v => G v k l) w p =
          ∑ a, ∑ b,
            (chartPartialZComplex (fun v => J v a k) w p * H (f w) a b +
              J w a k * (∑ c, J w c p * chartPartialZComplex
                (fun y => H y a b) (f w) c)) * star (J w b l) := by
      calc
        _ = ∑ b, ∑ a,
            (chartPartialZComplex (fun v => J v a k) w p * H (f w) a b +
              J w a k * (∑ c, J w c p * chartPartialZComplex
                (fun y => H y a b) (f w) c)) * Complex.conjCLE (J w b l) := hGderiv k l
        _ = _ := by
          simpa [Complex.conjCLE_apply] using (Finset.sum_comm :
            (∑ b, ∑ a,
              (chartPartialZComplex (fun v => J v a k) w p * H (f w) a b +
                J w a k * (∑ c, J w c p * chartPartialZComplex
                  (fun y => H y a b) (f w) c)) * Complex.conjCLE (J w b l)) =
            ∑ a, ∑ b,
              (chartPartialZComplex (fun v => J v a k) w p * H (f w) a b +
                J w a k * (∑ c, J w c p * chartPartialZComplex
                  (fun y => H y a b) (f w) c)) * Complex.conjCLE (J w b l))
    let A : Matrix (Fin n) (Fin n) ℂ := J w
    let AbarInv : Matrix (Fin n) (Fin n) ℂ := (A.map star)⁻¹
    let H₀ : Matrix (Fin n) (Fin n) ℂ := H (f w)
    let Hinv : Matrix (Fin n) (Fin n) ℂ := H₀⁻¹
    let Ainv : Matrix (Fin n) (Fin n) ℂ := A.transpose⁻¹
    let Ginv : Matrix (Fin n) (Fin n) ℂ := (G w)⁻¹
    let dA : Fin n → Fin n → Fin n → ℂ := fun q a j =>
      chartPartialZComplex (fun v => J v a j) w q
    let dH : Fin n → Fin n → Fin n → ℂ := fun c a b =>
      chartPartialZComplex (fun y => H y a b) (f w) c
    have hGinvEntries (l : Fin n) :
        Ginv l i = ∑ r, ∑ s, AbarInv l r * Hinv r s * Ainv s i := by
      calc
        Ginv l i = (AbarInv * Hinv * Ainv) l i := by
          simpa [AbarInv, Hinv, Ainv, Ginv, Matrix.mul_assoc] using
            congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M l i) hGinv
        _ = ∑ s, ∑ r, AbarInv l r * Hinv r s * Ainv s i := by
          simp only [Matrix.mul_apply]
          apply Finset.sum_congr rfl
          intro s hs
          rw [Finset.sum_mul]
        _ = ∑ r, ∑ s, AbarInv l r * Hinv r s * Ainv s i := by
          rw [Finset.sum_comm]
    have hBdetEq : (A.map star).det = star A.det := by
      simpa using ((starRingEnd ℂ).map_det A).symm
    have hBdetUnit : IsUnit (A.map star).det := by
      rw [hBdetEq]
      exact hunit.1.map (starRingEnd ℂ)
    have hBar (r b : Fin n) :
        ∑ l, AbarInv l r * star (A b l) = if b = r then 1 else 0 := by
      have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M b r)
        (Matrix.mul_nonsing_inv (A.map star) hBdetUnit)
      simpa [A, AbarInv, Matrix.mul_apply, Matrix.map_apply, Matrix.one_apply,
        mul_comm] using he
    have hH (a s : Fin n) :
        ∑ b, Hinv b s * H₀ a b = if a = s then 1 else 0 := by
      have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M a s)
        (Matrix.mul_nonsing_inv H₀ hunit.2)
      simpa [H₀, Hinv, Matrix.mul_apply, Matrix.one_apply, mul_comm] using he
    have hframe := hFrameFormula A AbarInv H₀ Hinv Ainv Ginv dA dH p i j
      hGinvEntries hBar hH
    have hconnEq : chartChernConnection G w i p j =
        pullbackChernConnectionExpression H f w i p j := by
      calc
        _ = ∑ l, Ginv l i * (∑ a, ∑ b,
            (dA p a j * H₀ a b + A a j * (∑ c, A c p * dH c a b)) *
              star (A b l)) := by
          unfold chartChernConnection
          apply Finset.sum_congr rfl
          intro l hl
          rw [hGderivAB j l]
        _ = _ := by
          simpa [A, AbarInv, H₀, Hinv, Ainv, Ginv, dA, dH,
            pullbackChernConnectionExpression, chartChernConnection] using hframe
    exact hconnEq
  exact hconnection

end KahlerForm
