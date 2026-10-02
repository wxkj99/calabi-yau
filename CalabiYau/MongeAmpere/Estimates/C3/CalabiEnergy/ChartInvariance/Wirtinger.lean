module

public import CalabiYau.MongeAmpere.Estimates.C3.CalabiEnergy.Basic

@[expose] public section

open scoped BigOperators Manifold ContDiff ComplexOrder

namespace KahlerForm.ChartInvariance

theorem calabiEnergy_c3PartialZ_mul {m : ℕ}
    {u v : EuclideanSpace ℂ (Fin m) → ℂ} {z : EuclideanSpace ℂ (Fin m)}
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) (j : Fin m) :
    c3PartialZ (fun w ↦ u w * v w) z j =
      c3PartialZ u z j * v z + u z * c3PartialZ v z j := by
  unfold c3PartialZ
  rw [fderiv_fun_mul hu hv]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

theorem wirtinger_star_zero {n : ℕ}
    (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (p : Fin n)
    (hf : DifferentiableAt ℂ f z) :
    c3PartialZ (fun w ↦ star (f w)) z p = 0 := by
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
  unfold c3PartialZ
  rw [hstar]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hI]
  simp
  rw [← mul_assoc, Complex.I_mul_I]
  ring

theorem wirtinger_directional_smul {n : ℕ}
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

theorem c3PartialZ_comp {n : ℕ}
    (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) (p : Fin n)
    (hF : DifferentiableAt ℝ F (ψ z)) (hψ : DifferentiableAt ℂ ψ z) :
    c3PartialZ (fun w ↦ F (ψ w)) z p =
      ∑ a, (EuclideanSpace.clmMatrix (fderiv ℂ ψ z)) a p *
        c3PartialZ F (ψ z) a := by
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
  unfold c3PartialZ
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

theorem c3PartialZ_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (F : ι → EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (p : Fin n)
    (hF : ∀ i, DifferentiableAt ℝ (F i) z) :
    c3PartialZ (fun w ↦ ∑ i, F i w) z p =
      ∑ i, c3PartialZ (F i) z p := by
  unfold c3PartialZ
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

theorem pullback_summand {n : ℕ}
    (u v : EuclideanSpace ℂ (Fin n) → ℂ)
    (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) (p : Fin n)
    (hu : DifferentiableAt ℂ u z) (hv : DifferentiableAt ℂ v z)
    (hF : DifferentiableAt ℝ F (ψ z)) (hψ : DifferentiableAt ℂ ψ z) :
    c3PartialZ (fun w ↦ u w * F (ψ w) * star (v w)) z p =
      c3PartialZ u z p * F (ψ z) * star (v z) +
        u z * (∑ a, (EuclideanSpace.clmMatrix (fderiv ℂ ψ z)) a p *
          c3PartialZ F (ψ z) a) * star (v z) := by
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
  rw [calabiEnergy_c3PartialZ_mul hleft hvStar p,
    calabiEnergy_c3PartialZ_mul huR hcompDiff p,
    wirtinger_star_zero v z p hv,
    c3PartialZ_comp F ψ z p hF hψ]
  ring

end KahlerForm.ChartInvariance
