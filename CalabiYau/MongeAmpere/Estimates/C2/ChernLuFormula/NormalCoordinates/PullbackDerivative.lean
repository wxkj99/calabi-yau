module

public import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.NormalCoordinates.HolomorphicPatch

/-!
# First Wirtinger derivative of the quadratic pullback metric

This child isolates the chain rule for the coefficient matrix of a metric under a holomorphic
quadratic coordinate map. If `J` is the linear part and `Q` the symmetric quadratic jet, the
holomorphic derivative of `Jᵀ (G ∘ f) J̄` has two terms: differentiating the coordinate Jacobian
contributes `Q(eₚ,eⱼ)ᵀ G J̄`, and differentiating the metric contributes
`Jᵀ (∂G·J eₚ) J̄`. The antiholomorphic Jacobian factor has zero holomorphic derivative.

The local patch hypotheses keep the map inside the fixed chart near zero, where the metric
coefficients are smooth. The statement uses the repository convention `J.transpose * G * J.map
star`; the row/column order and conjugation in the second term are explicit. Check a flat metric,
where only the quadratic correction remains, and `n=1` with `J=i`, where the normalized coefficient
is unchanged and the chain rule has the expected single-index terms.
-/

@[expose] public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

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
    have hscalar : Complex.I * c = ((-c.im : ℝ) : ℂ) + (c.re : ℂ) * Complex.I := by
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
    simp [A, e, EuclideanSpace.clmMatrix, Pi.single_apply]
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
  simp only [_root_.sum_apply]
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
  exact pullback_summand
    (u := fun w ↦ J w r j) (v := fun w ↦ J w s k)
    (F := fun w ↦ G w r s) ψ z p (hJ r j) (hJ s k) (hG r s) hψ

private theorem quadratic_chart_map_fderiv {n : ℕ}
    (z₀ : EuclideanSpace ℂ (Fin n))
    (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (Q : EuclideanSpace ℂ (Fin n) →L[ℂ]
      EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hQ : ∀ u v, Q u v = Q v u)
    (v : EuclideanSpace ℂ (Fin n)) :
    fderiv ℂ (quadraticChartMap z₀ A Q) v = A + Q v := by
  have hquad := Q.hasFDerivAt_of_bilinear
    (hasFDerivAt_id v) (hasFDerivAt_id v)
  have hdf : HasFDerivAt (quadraticChartMap z₀ A Q)
      (0 + A + (1 / 2 : ℂ) •
        (Q.precompR (EuclideanSpace ℂ (Fin n)) v
          (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin n))) +
        Q.precompL (EuclideanSpace ℂ (Fin n))
          (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin n))) v)) v := by
    convert (((hasFDerivAt_const z₀ v).add A.hasFDerivAt).add
      (hquad.const_smul (1 / 2 : ℂ))) using 1
    all_goals rfl
  rw [hdf.fderiv]
  ext w
  simp [ContinuousLinearMap.precompR, ContinuousLinearMap.precompL, hQ]
  ring

private theorem quadratic_jacobian_entry_formula {n : ℕ}
    (z₀ : EuclideanSpace ℂ (Fin n))
    (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (Q : EuclideanSpace ℂ (Fin n) →L[ℂ]
      EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hQ : ∀ u v, Q u v = Q v u)
    (a j : Fin n) (z : EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace.clmMatrix (fderiv ℂ (quadraticChartMap z₀ A Q) z) a j =
      (A (EuclideanSpace.single j 1)) a +
        ((EuclideanSpace.proj a).comp
          ((ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ (Fin n))
            (EuclideanSpace.single j 1)).comp Q)) z := by
  rw [quadratic_chart_map_fderiv z₀ A Q hQ z]
  simp [EuclideanSpace.clmMatrix, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply]

private theorem quadratic_jacobian_entry_partial {n : ℕ}
    (z₀ : EuclideanSpace ℂ (Fin n))
    (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (Q : EuclideanSpace ℂ (Fin n) →L[ℂ]
      EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hQ : ∀ u v, Q u v = Q v u)
    (a j p : Fin n) :
    chartPartialZComplex
      (fun w ↦ EuclideanSpace.clmMatrix (fderiv ℂ (quadraticChartMap z₀ A Q) w) a j)
      0 p = Q (EuclideanSpace.single p 1) (EuclideanSpace.single j 1) a := by
  let ej := EuclideanSpace.single j (1 : ℂ)
  let L : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ :=
    (EuclideanSpace.proj a).comp
      ((ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ (Fin n)) ej).comp Q)
  have hentry (w : EuclideanSpace ℂ (Fin n)) :
      EuclideanSpace.clmMatrix (fderiv ℂ (quadraticChartMap z₀ A Q) w) a j =
        (A ej) a + L w := by
    rw [quadratic_jacobian_entry_formula z₀ A Q hQ a j w]
  have hfun :
      (fun w ↦ EuclideanSpace.clmMatrix
        (fderiv ℂ (quadraticChartMap z₀ A Q) w) a j) =
        fun w ↦ (A ej) a + L w := by
    funext w
    exact hentry w
  have hfd : fderiv ℝ (fun w : EuclideanSpace ℂ (Fin n) ↦ (A ej) a + L w) 0 =
      L.restrictScalars ℝ := by
    rw [fderiv_const_add]
    simpa using L.differentiableAt.fderiv_restrictScalars ℝ
  have hI : (L.restrictScalars ℝ) (Complex.I • EuclideanSpace.single p (1 : ℂ)) =
      Complex.I * (L.restrictScalars ℝ) (EuclideanSpace.single p (1 : ℂ)) := by
    change L (Complex.I • EuclideanSpace.single p (1 : ℂ)) = _
    exact L.map_smul Complex.I _
  unfold chartPartialZComplex
  rw [hfun, hfd]
  simp only
  rw [hI]
  simp
  rw [← mul_assoc, Complex.I_mul_I]
  ring_nf
  change (Q (EuclideanSpace.single p (1 : ℂ))
    (EuclideanSpace.single j (1 : ℂ))) a = _
  rfl

/-- Wirtinger chain rule for a coefficient of the pullback metric of a quadratic holomorphic map. -/
theorem chartPartialZ_quadratic_pullback_metric
    (ω₀ : KahlerForm n M) (x : M) (z₀ : EuclideanSpace ℂ (Fin n))
    (hz₀ : z₀ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (Q : EuclideanSpace ℂ (Fin n) →L[ℂ]
      EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hQ : ∀ u v, Q u v = Q v u) (p j k : Fin n) :
    chartPartialZComplex
        (fun v ↦ pulledBackMetricInChart ω₀ x (quadraticChartMap z₀ A Q) v j k) 0 p =
      (∑ a, ∑ b,
          Q (EuclideanSpace.single p 1) (EuclideanSpace.single j 1) a *
            (ω₀.metricInChart x z₀) a b * star (EuclideanSpace.clmMatrix A b k)) +
        ∑ a, ∑ b, ∑ c,
          (EuclideanSpace.clmMatrix A a j) * star (EuclideanSpace.clmMatrix A b k) *
            (EuclideanSpace.clmMatrix A c p) *
              chartPartialZComplex (fun w ↦ ω₀.metricInChart x w a b) z₀ c := by
  let ψ := quadraticChartMap z₀ A Q
  let G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun z ↦ ω₀.metricInChart x z
  let J : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun z ↦ EuclideanSpace.clmMatrix (fderiv ℂ ψ z)
  have hz₀' : z₀ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := hz₀
  have hGentry (a b : Fin n) : DifferentiableAt ℝ (fun z ↦ G z a b) z₀ := by
    have hcont := (ω₀.contDiffOn_metricInChart x a b).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz₀')
    exact hcont.differentiableAt (by norm_num)
  have hψ : DifferentiableAt ℂ ψ 0 := by
    have hquad : Differentiable ℂ (fun v : EuclideanSpace ℂ (Fin n) ↦ Q v v) :=
      Q.differentiable.clm_apply differentiable_id
    have hcoef : Differentiable ℂ
        (fun _ : EuclideanSpace ℂ (Fin n) ↦ (1 / 2 : ℂ)) := differentiable_const _
    have hlinear : Differentiable ℂ (fun v : EuclideanSpace ℂ (Fin n) ↦ z₀ + A v) :=
      (differentiable_const z₀).add A.differentiable
    have hquadratic : Differentiable ℂ
        (fun v : EuclideanSpace ℂ (Fin n) ↦ (1 / 2 : ℂ) • Q v v) := hcoef.smul hquad
    exact (hlinear.add hquadratic).differentiableAt
  have hJentry (a b : Fin n) : DifferentiableAt ℂ (fun z ↦ J z a b) 0 := by
    let L : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ :=
      (EuclideanSpace.proj a).comp
        ((ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ (Fin n))
          (EuclideanSpace.single b 1)).comp Q)
    have hformula : (fun z ↦ J z a b) =
        fun z ↦ (A (EuclideanSpace.single b 1)) a + L z := by
      funext z
      exact quadratic_jacobian_entry_formula z₀ A Q hQ a b z
    rw [hformula]
    exact (differentiableAt_const _).add L.differentiableAt
  have hGcomp (a b : Fin n) :
      DifferentiableAt ℝ (fun z ↦ G z a b) (ψ 0) := by
    simpa [ψ, quadraticChartMap] using hGentry a b
  have hPull := pullback_entry_derivative J G ψ 0 p j k hJentry hGcomp hψ
  have hderiv0 : fderiv ℂ ψ 0 = A := by
    simpa [ψ, quadraticChartMap] using quadratic_chart_map_fderiv z₀ A Q hQ 0
  have hJ0 : J 0 = EuclideanSpace.clmMatrix A := by
    change EuclideanSpace.clmMatrix (fderiv ℂ ψ 0) = _
    rw [hderiv0]
  have hJpartial (a b : Fin n) :
      chartPartialZComplex (fun z ↦ J z a b) 0 p =
        Q (EuclideanSpace.single p 1) (EuclideanSpace.single b 1) a := by
    exact quadratic_jacobian_entry_partial z₀ A Q hQ a b p
  have hψ0 : ψ 0 = z₀ := by simp [ψ, quadraticChartMap]
  rw [show (fun v ↦ pulledBackMetricInChart ω₀ x ψ v j k) =
      fun v ↦ ((J v).transpose * G (ψ v) * (J v).map star) j k by
        funext v
        rfl]
  rw [hPull]
  simp_rw [hJpartial]
  rw [hderiv0, hJ0, hψ0]
  simp only [G]
  let qterm : Fin n → Fin n → ℂ := fun a b ↦
    (Q (EuclideanSpace.single p 1) (EuclideanSpace.single j 1)).ofLp a *
      (ω₀.metricInChart x z₀) a b * star (EuclideanSpace.clmMatrix A b k)
  let aterm : Fin n → Fin n → ℂ := fun a b ↦
    (EuclideanSpace.clmMatrix A a j *
      (∑ c, EuclideanSpace.clmMatrix A c p *
        chartPartialZComplex (fun w ↦ ω₀.metricInChart x w a b) z₀ c)) *
      star (EuclideanSpace.clmMatrix A b k)
  let cterm : Fin n → Fin n → Fin n → ℂ := fun a b c ↦
    EuclideanSpace.clmMatrix A a j * star (EuclideanSpace.clmMatrix A b k) *
      EuclideanSpace.clmMatrix A c p *
        chartPartialZComplex (fun w ↦ ω₀.metricInChart x w a b) z₀ c
  have hsplit : (∑ a, ∑ b, (qterm a b + aterm a b)) =
      (∑ a, ∑ b, qterm a b) + (∑ a, ∑ b, aterm a b) := by
    calc
      _ = ∑ a, ((∑ b, qterm a b) + (∑ b, aterm a b)) := by
        apply Finset.sum_congr rfl
        intro a ha
        exact Finset.sum_add_distrib
      _ = _ := by rw [Finset.sum_add_distrib]
  have hterm (a b : Fin n) : aterm a b = ∑ c, cterm a b c := by
    dsimp [aterm, cterm]
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c hc
    simp only [starRingEnd_apply]
    ring_nf
  have hsumTerm : (∑ a, ∑ b, aterm a b) = ∑ a, ∑ b, ∑ c, cterm a b c := by
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    exact hterm a b
  rw [hsplit, hsumTerm]

end KahlerForm
