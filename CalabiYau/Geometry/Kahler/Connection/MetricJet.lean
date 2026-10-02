module

public import CalabiYau.Geometry.Kahler.Laplacian.Cofactor

/-!
# First derivatives of the metric under a holomorphic coordinate change

Differentiate `g' = Aᵀ (g ∘ F) conjugate(A)` on an open coordinate overlap.
Only the metric is real-smooth; its entries are not assumed holomorphic.
The Jacobian `A = DF` is holomorphic, so its conjugate has zero holomorphic
Wirtinger derivative. The derivative of `A` itself must be retained.

Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §1.1,
holomorphic overlaps (p. 1); §1.4, product rule (p. 10) and Lemma 1.19 (p. 11).
-/

public section

open scoped BigOperators ContDiff

namespace KahlerForm

private theorem wirtinger_star_zero {n : ℕ}
    (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (p : Fin n)
    (hf : DifferentiableAt ℂ f z) :
    chartPartialZComplex (fun w ↦ star (f w)) z p = 0 := by
  have hreal : HasFDerivAt f ((fderiv ℂ f z).restrictScalars ℝ) z :=
    hf.hasFDerivAt.restrictScalars ℝ
  have hconj : HasFDerivAt (Complex.conjCLE : ℂ → ℂ)
      (Complex.conjCLE : ℂ →L[ℝ] ℂ) (f z) :=
    Complex.conjCLE.hasFDerivAt (x := f z)
  have hcomp := hconj.comp z hreal
  have hstar : fderiv ℝ (fun w ↦ star (f w)) z =
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((fderiv ℂ f z).restrictScalars ℝ) := by
    simpa [Function.comp_def, Complex.conjCLE_apply, Complex.star_def] using hcomp.fderiv
  have hI : ((fderiv ℂ f z).restrictScalars ℝ)
      (Complex.I • EuclideanSpace.single p (1 : ℂ)) =
      Complex.I * ((fderiv ℂ f z).restrictScalars ℝ)
        (EuclideanSpace.single p (1 : ℂ)) := by
    change fderiv ℂ f z (Complex.I • EuclideanSpace.single p (1 : ℂ)) = _
    exact (fderiv ℂ f z).map_smul Complex.I _
  unfold chartPartialZComplex
  rw [hstar]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hI]
  simp
  rw [← mul_assoc, Complex.I_mul_I]
  ring

private theorem wirtinger_directional_smul {n : ℕ}
    (D : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ) (c : ℂ)
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
      _ = (((-c.im : ℝ) : ℂ) + (c.re : ℂ) * Complex.I) • v := by rw [hscalar]
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

private theorem chartPartialZComplex_comp {n : ℕ}
    (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) (p : Fin n)
    (hF : DifferentiableAt ℝ F (ψ z)) (hψ : DifferentiableAt ℂ ψ z) :
    chartPartialZComplex (fun w ↦ F (ψ w)) z p =
      ∑ a, (EuclideanSpace.clmMatrix (fderiv ℂ ψ z)) a p *
        chartPartialZComplex F (ψ z) a := by
  have hψR : HasFDerivAt ψ ((fderiv ℂ ψ z).restrictScalars ℝ) z :=
    hψ.hasFDerivAt.restrictScalars ℝ
  have hψreal : fderiv ℝ ψ z = (fderiv ℂ ψ z).restrictScalars ℝ := by
    simpa using hψ.fderiv_restrictScalars ℝ
  have hcomp := fderiv_comp (f := ψ) (g := F) (x := z) hF hψR.differentiableAt
  have hcomp' : fderiv ℝ (fun w ↦ F (ψ w)) z =
      (fderiv ℝ F (ψ z)).comp (fderiv ℝ ψ z) := by
    simpa [Function.comp_def] using hcomp
  let D := fderiv ℝ F (ψ z)
  let L := fderiv ℂ ψ z
  let A := EuclideanSpace.clmMatrix L
  let e := EuclideanSpace.single p (1 : ℂ)
  have hvec : L e = ∑ a, (A a p) • EuclideanSpace.single a (1 : ℂ) := by
    ext a
    simp [A, e, Pi.single_apply]
    change (L (EuclideanSpace.single p (1 : ℂ))).ofLp a =
      (Matrix.of fun (b : Fin n) (c : Fin n) =>
        (L (EuclideanSpace.single c (1 : ℂ))).ofLp b) a p
    simp only [Matrix.of_apply]
  unfold chartPartialZComplex
  rw [hcomp', hψreal]
  simp only [ContinuousLinearMap.comp_apply]
  change (D (L e) - Complex.I * D (L (Complex.I • e))) / 2 = _
  rw [map_smul, hvec]
  simp only [_root_.map_sum, Finset.smul_sum]
  have hsum :
      (∑ a, D ((A a p) • EuclideanSpace.single a (1 : ℂ))) -
        Complex.I * ∑ a, D (Complex.I • ((A a p) • EuclideanSpace.single a (1 : ℂ))) =
      ∑ a, (D ((A a p) • EuclideanSpace.single a (1 : ℂ)) -
        Complex.I * D (Complex.I • ((A a p) • EuclideanSpace.single a (1 : ℂ)))) := by
    rw [Finset.mul_sum, Finset.sum_sub_distrib]
  rw [hsum]
  simp_rw [wirtinger_directional_smul]
  simp only [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  ring

private theorem chartPartialZComplex_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (F : ι → EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (p : Fin n)
    (hF : ∀ i, DifferentiableAt ℝ (F i) z) :
    chartPartialZComplex (fun w ↦ ∑ i, F i w) z p =
      ∑ i, chartPartialZComplex (F i) z p := by
  unfold chartPartialZComplex
  have hfd : fderiv ℝ (fun w ↦ ∑ i, F i w) z = ∑ i, fderiv ℝ (F i) z := by
    simpa using fderiv_fun_sum (u := Finset.univ) (fun i hi ↦ hF i)
  rw [hfd]
  simp only [sum_apply]
  have hsum :
      (∑ i, fderiv ℝ (F i) z (EuclideanSpace.single p 1)) -
        Complex.I * ∑ i, fderiv ℝ (F i) z (Complex.I • EuclideanSpace.single p 1) =
      ∑ i, (fderiv ℝ (F i) z (EuclideanSpace.single p 1) -
        Complex.I * fderiv ℝ (F i) z (Complex.I • EuclideanSpace.single p 1)) := by
    rw [Finset.mul_sum, Finset.sum_sub_distrib]
  rw [hsum]
  simp only [div_eq_mul_inv, Finset.sum_mul]

private theorem pullback_summand {n : ℕ}
    (u v : EuclideanSpace ℂ (Fin n) → ℂ)
    (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) (p : Fin n)
    (hu : DifferentiableAt ℂ u z) (hv : DifferentiableAt ℂ v z)
    (hF : DifferentiableAt ℝ F (ψ z)) (hψ : DifferentiableAt ℂ ψ z) :
    chartPartialZComplex (fun w ↦ u w * F (ψ w) * star (v w)) z p =
      chartPartialZComplex u z p * F (ψ z) * star (v z) +
        u z * (∑ a, (EuclideanSpace.clmMatrix (fderiv ℂ ψ z)) a p *
          chartPartialZComplex F (ψ z) a) * star (v z) := by
  have hψR : HasFDerivAt ψ ((fderiv ℂ ψ z).restrictScalars ℝ) z :=
    hψ.hasFDerivAt.restrictScalars ℝ
  have hcompDiff : DifferentiableAt ℝ (fun w ↦ F (ψ w)) z :=
    (hF.hasFDerivAt.comp z hψR).differentiableAt
  have huR : DifferentiableAt ℝ u z := hu.hasFDerivAt.restrictScalars ℝ |>.differentiableAt
  have hvStar : DifferentiableAt ℝ (fun w ↦ star (v w)) z := by
    have hvr : HasFDerivAt v ((fderiv ℂ v z).restrictScalars ℝ) z :=
      hv.hasFDerivAt.restrictScalars ℝ
    exact (Complex.conjCLE.hasFDerivAt (x := v z)).comp z hvr |>.differentiableAt
  have hleft : DifferentiableAt ℝ (fun w ↦ u w * F (ψ w)) z := huR.mul hcompDiff
  rw [chartPartialZComplex_mul hleft hvStar p,
    chartPartialZComplex_mul huR hcompDiff p,
    wirtinger_star_zero v z p hv,
    chartPartialZComplex_comp F ψ z p hF hψ]
  ring

private theorem pullback_entry_derivative {n : ℕ}
    (J : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) (p j k : Fin n)
    (hJ : ∀ r s, DifferentiableAt ℂ (fun w ↦ J w r s) z)
    (hG : ∀ r s, DifferentiableAt ℝ (fun w ↦ G w r s) (ψ z))
    (hψ : DifferentiableAt ℂ ψ z) :
    chartPartialZComplex
        (fun w ↦ ((J w).transpose * G (ψ w) * (J w).map star) j k) z p =
      ∑ r, ∑ s,
        (chartPartialZComplex (fun w ↦ J w r j) z p * G (ψ z) r s * star (J z s k) +
          J z r j * (∑ a, (EuclideanSpace.clmMatrix (fderiv ℂ ψ z)) a p *
            chartPartialZComplex (fun w ↦ G w r s) (ψ z) a) * star (J z s k)) := by
  let T (rs : Fin n × Fin n) (w : EuclideanSpace ℂ (Fin n)) : ℂ :=
    (J w rs.1 j * star (J w rs.2 k)) * G (ψ w) rs.1 rs.2
  have hentry (w : EuclideanSpace ℂ (Fin n)) :
      ((J w).transpose * G (ψ w) * (J w).map star) j k =
        ∑ r, ∑ s, (J w r j * star (J w s k)) * G (ψ w) r s := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro s hs
    ring
  have hTdiff (rs : Fin n × Fin n) : DifferentiableAt ℝ (T rs) z := by
    have hJ1 : DifferentiableAt ℝ (fun w ↦ J w rs.1 j) z :=
      (hJ rs.1 j).hasFDerivAt.restrictScalars ℝ |>.differentiableAt
    have hJ2 : DifferentiableAt ℝ (fun w ↦ star (J w rs.2 k)) z := by
      have h := (hJ rs.2 k).hasFDerivAt.restrictScalars ℝ
      have hc := Complex.conjCLE.hasFDerivAt (x := J z rs.2 k)
      simpa [Function.comp_def, Complex.star_def, Complex.conjCLE_apply] using
        (hc.comp z h).differentiableAt
    have hGcomp : DifferentiableAt ℝ (fun w ↦ G (ψ w) rs.1 rs.2) z := by
      have hψR := hψ.hasFDerivAt.restrictScalars ℝ
      exact (hG rs.1 rs.2).comp z hψR.differentiableAt
    exact (hJ1.mul hJ2).mul hGcomp
  have hfun :
      (fun w ↦ ((J w).transpose * G (ψ w) * (J w).map star) j k) =
        fun w ↦ ∑ rs : Fin n × Fin n, T rs w := by
    funext w
    rw [hentry w]
    simp only [T, Fintype.sum_prod_type]
  rw [hfun]
  rw [chartPartialZComplex_sum T z p hTdiff]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  simp only [T]
  have hT_eq : (fun w ↦ (J w r j * star (J w s k)) * G (ψ w) r s) =
      fun w ↦ J w r j * G (ψ w) r s * star (J w s k) := by
    funext w
    ring
  rw [hT_eq]
  exact pullback_summand (fun w ↦ J w r j) (fun w ↦ J w s k)
    (fun w ↦ G w r s) ψ z p (hJ r j) (hJ s k) (hG r s) hψ

/-- The actual first jet of a holomorphic metric pullback, with local equality
of the metric functions on the open overlap. Nothing is assumed about their
values or regularity outside `U` and `V`. The derivative `∂z` includes `1/2`. -/
theorem chartPartialZComplex_metric_pullback {n : ℕ}
    (F : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (g g' : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (U V : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U) (hV : IsOpen V)
    (hF : ContDiffOn ℂ 2 F U)
    (hg : ∀ a b, ContDiffOn ℝ 1 (fun w => g w a b) V)
    (hFV : Set.MapsTo F U V)
    (hmetric : ∀ w ∈ U, g' w =
      (EuclideanSpace.clmMatrix (fderiv ℂ F w)).transpose * g (F w) *
        (EuclideanSpace.clmMatrix (fderiv ℂ F w)).map star)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U) (j k l : Fin n) :
    let A := fun w => EuclideanSpace.clmMatrix (fderiv ℂ F w)
    chartPartialZComplex (fun w => g' w k l) z j =
      (∑ r, ∑ s,
        chartPartialZComplex (fun w => A w r k) z j * g (F z) r s * star (A z s l)) +
      ∑ p, ∑ r, ∑ s, A z p j * A z r k *
        chartPartialZComplex (fun w => g w r s) (F z) p * star (A z s l) := by
  dsimp only
  let A := fun w => EuclideanSpace.clmMatrix (fderiv ℂ F w)
  have hzV : F z ∈ V := hFV hz
  have hA (r s : Fin n) : DifferentiableAt ℂ (fun w ↦ A w r s) z := by
    have hFz : ContDiffAt ℂ 2 F z := hF.contDiffAt (hU.mem_nhds hz)
    have hfd : ContDiffAt ℂ 1 (fderiv ℂ F) z :=
      hFz.fderiv_right (m := 1) (by norm_num)
    have happly : ContDiffAt ℂ 1
        (fun w ↦ fderiv ℂ F w (EuclideanSpace.single s (1 : ℂ))) z :=
      hfd.clm_apply contDiffAt_const
    have hpi : DifferentiableAt ℂ
        (fun w ↦ EuclideanSpace.equiv (Fin n) ℂ
          (fderiv ℂ F w (EuclideanSpace.single s (1 : ℂ)))) z := by
      fun_prop
    have hentry' : DifferentiableAt ℂ
        (fun w ↦ (fderiv ℂ F w (EuclideanSpace.single s (1 : ℂ))) r) z := by
      have hcoord := differentiableAt_pi.1 hpi r
      simpa [EuclideanSpace.equiv] using hcoord
    have hentry'' : DifferentiableAt ℂ (fun w ↦ A w r s) z := by
      change DifferentiableAt ℂ
        (fun w ↦ (Matrix.of fun (a : Fin n) (b : Fin n) =>
          (fderiv ℂ F w (EuclideanSpace.single b (1 : ℂ))).ofLp a) r s) z
      simpa only [Matrix.of_apply] using hentry'
    exact hentry''
  have hgF (r s : Fin n) : DifferentiableAt ℝ (fun w ↦ g w r s) (F z) :=
    (hg r s).contDiffAt (hV.mem_nhds (hFV hz)) |>.differentiableAt (by norm_num)
  have hFdiff : DifferentiableAt ℂ F z :=
    (hF.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)
  have hevent : (fun w ↦ g' w k l) =ᶠ[nhds z]
      fun w ↦ ((A w).transpose * g (F w) * (A w).map star) k l := by
    filter_upwards [hU.mem_nhds hz] with w hw
    rw [hmetric w hw]
  have hderivEq : fderiv ℝ (fun w ↦ g' w k l) z =
      fderiv ℝ (fun w ↦ ((A w).transpose * g (F w) * (A w).map star) k l) z :=
    hevent.fderiv_eq
  change (fderiv ℝ (fun w ↦ g' w k l) z (EuclideanSpace.single j 1) -
      Complex.I * fderiv ℝ (fun w ↦ g' w k l) z
        (Complex.I • EuclideanSpace.single j 1)) / 2 = _
  rw [hderivEq]
  change chartPartialZComplex
      (fun w ↦ ((A w).transpose * g (F w) * (A w).map star) k l) z j = _
  let P : Fin n → Fin n → ℂ := fun r s =>
    chartPartialZComplex (fun w ↦ A w r k) z j * g (F z) r s * star (A z s l)
  let Q : Fin n → Fin n → ℂ := fun r s =>
    A z r k * (∑ p, A z p j * chartPartialZComplex (fun w ↦ g w r s) (F z) p) *
      star (A z s l)
  let R : Fin n → Fin n → Fin n → ℂ := fun p r s =>
    A z p j * A z r k * chartPartialZComplex (fun w ↦ g w r s) (F z) p *
      star (A z s l)
  have hformula : chartPartialZComplex
      (fun w ↦ ((A w).transpose * g (F w) * (A w).map star) k l) z j =
      ∑ r, ∑ s, (P r s + Q r s) := by
    simpa [P, Q, A, mul_assoc] using
      pullback_entry_derivative A g F z j k l hA hgF hFdiff
  have hq : (∑ r, ∑ s, Q r s) = ∑ p, ∑ r, ∑ s, R p r s := by
    calc
      ∑ r, ∑ s, Q r s = ∑ r, ∑ s, ∑ p, R p r s := by
        apply Finset.sum_congr rfl
        intro r hr
        apply Finset.sum_congr rfl
        intro s hs
        dsimp [Q, R]
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p hp
        ring
      _ = ∑ p, ∑ r, ∑ s, R p r s := by
        calc
          ∑ r, ∑ s, ∑ p, R p r s = ∑ r, ∑ p, ∑ s, R p r s := by
            apply Finset.sum_congr rfl
            intro r hr
            exact Finset.sum_comm
          _ = ∑ p, ∑ r, ∑ s, R p r s := Finset.sum_comm
  calc
    chartPartialZComplex
        (fun w ↦ ((A w).transpose * g (F w) * (A w).map star) k l) z j =
        ∑ r, ∑ s, (P r s + Q r s) := hformula
    _ = (∑ r, ∑ s, P r s) + ∑ p, ∑ r, ∑ s, R p r s := by
      calc
        ∑ r, ∑ s, (P r s + Q r s) = ∑ r, (∑ s, P r s + ∑ s, Q r s) := by
          apply Finset.sum_congr rfl
          intro r hr
          exact Finset.sum_add_distrib
        _ = (∑ r, ∑ s, P r s) + ∑ r, ∑ s, Q r s := Finset.sum_add_distrib
        _ = _ := by rw [hq]
    _ = _ := by simp [P, R, A, mul_assoc]

end KahlerForm
