module

public import CalabiYau.Geometry.Kahler.Riemannian.Volume
public import CalabiYau.Geometry.Complex.DDBar.HermitianAdjoint.IntegratedPairing.Definiteness
import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.IntegralZero.ExactWedgePower
import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.IntegralZero.PrimitiveCoefficient
import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.TopFormIntegral.NativeStokesConsumption

/-!
# Integral of the squared norm of a primitive exact `(1,1)`-form

For `n ≥ 2`, an exact primitive real `(1,1)`-form `γ = dβ` satisfies
`∫ γ ∧ γ ∧ ωⁿ⁻² = 0` by Stokes and `dω = 0`. Pointwise Hodge–Riemann states
`γ ∧ γ ∧ ωⁿ⁻² = -|γ|² ωⁿ / (n(n-1))`, using the standard exterior squared norm
and complex orientation. With `ω.volume = ωⁿ/n!`, the resulting integral of the
nonnegative squared norm vanishes. The latter, weaker *integral identity* is
what this module asserts; pointwise vanishing is proved by the parent using the
existing integrated-definiteness theorem and volume comparison.

Handle `n = 0` (all degree-two fibers vanish) and `n = 1` (trace-free real `(1,1)`
forms vanish) separately before writing `ωⁿ⁻²`. The proof explicitly uses the
published normalized primitive coefficient identity and native Stokes consumption;
neither is assumed as a hypothesis.

Source: Huybrechts, *Complex Geometry*, §3.1 (primitive Hodge–Riemann);
Wells, *Differential Analysis on Complex Manifolds*, IV §5 (Stokes and Leibniz).
-/

@[expose] public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder
open MeasureTheory

namespace KahlerForm

private theorem degree_two_zero_zero_dim
    {M : Type*} (α : FormField (EuclideanSpace ℂ (Fin 0)) M 2) :
    α = 0 := by
  funext x
  ext u
  have hu : u = (0 : Fin 2 → EuclideanSpace ℂ (Fin 0)) := Subsingleton.elim _ _
  rw [hu]
  simp

private theorem primitive_oneone_zero_one
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin 1)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 1)) ω M]
    (ω₀ : KahlerForm 1 M)
    (γ : FormField (EuclideanSpace ℂ (Fin 1)) M 2)
    (hγone : γ.IsOneOne)
    (hγtrace : ∀ x, ContinuousAlternatingMap.relTrace (ω₀ x) (γ x) = 0) :
    γ = 0 := by
  funext x
  let w := ω₀ x
  let a := γ x
  have hw : w.IsPositive := ω₀.isPositive x
  have ha : a.IsOneOne := hγone x
  have htrace : ContinuousAlternatingMap.relTrace w a = 0 := hγtrace x
  have htrace' : RCLike.re ((w.coeffMatrix)⁻¹ 0 0 * a.coeffMatrix 0 0) = 0 := by
    change RCLike.re ((w.coeffMatrix)⁻¹ * a.coeffMatrix).trace = 0 at htrace
    simpa [Matrix.trace, Matrix.mul_apply] using htrace
  have hwHerm : w.coeffMatrix.IsHermitian :=
    (ContinuousAlternatingMap.isPositive_iff.mp hw).1.isHermitian_coeffMatrix
  have haHerm : a.coeffMatrix.IsHermitian := ha.isHermitian_coeffMatrix
  have hwdiag : w.coeffMatrix 0 0 = (w.coeffMatrix 0 0).re :=
    (hwHerm.coe_re_apply_self 0).symm
  have hadiag : a.coeffMatrix 0 0 = (a.coeffMatrix 0 0).re :=
    (haHerm.coe_re_apply_self 0).symm
  have hωpd : w.coeffMatrix.PosDef := (ContinuousAlternatingMap.isPositive_iff.mp hw).2
  have hunit : IsUnit w.coeffMatrix.det :=
    (Matrix.isUnit_iff_isUnit_det w.coeffMatrix).1 hωpd.isUnit
  have hw00ne : w.coeffMatrix 0 0 ≠ 0 := by
    intro hz
    apply hunit.ne_zero
    rw [Matrix.det_fin_one, hz]
  have hentry : (w.coeffMatrix)⁻¹ 0 0 * w.coeffMatrix 0 0 = 1 := by
    have hid := Matrix.nonsing_inv_mul w.coeffMatrix hunit
    have heq := congrArg (fun B : Matrix (Fin 1) (Fin 1) ℂ => B 0 0) hid
    simpa [Matrix.mul_apply] using heq
  have hinv : (w.coeffMatrix)⁻¹ 0 0 = (w.coeffMatrix 0 0)⁻¹ := by
    calc
      (w.coeffMatrix)⁻¹ 0 0 =
          (w.coeffMatrix)⁻¹ 0 0 * (w.coeffMatrix 0 0 * (w.coeffMatrix 0 0)⁻¹) := by
        rw [mul_inv_cancel₀ hw00ne]
        ring
      _ = ((w.coeffMatrix)⁻¹ 0 0 * w.coeffMatrix 0 0) *
          (w.coeffMatrix 0 0)⁻¹ := by ring
      _ = (w.coeffMatrix 0 0)⁻¹ := by rw [hentry]; exact one_mul _
  rw [hinv, hwdiag, hadiag] at htrace'
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul] at htrace'
  change (w.coeffMatrix 0 0).re⁻¹ * (a.coeffMatrix 0 0).re = 0 at htrace'
  have hwre_ne : (w.coeffMatrix 0 0).re ≠ 0 := by
    intro hz
    apply hw00ne
    rw [hwdiag, hz]
    simp
  have hare : (a.coeffMatrix 0 0).re = 0 := by
    exact (mul_eq_zero.mp htrace').resolve_left (inv_ne_zero hwre_ne)
  have hmat : a.coeffMatrix =
      (0 : EuclideanSpace ℂ (Fin 1) [⋀^Fin 2]→L[ℝ] ℝ).coeffMatrix := by
    ext i j
    fin_cases i
    fin_cases j
    change a.coeffMatrix 0 0 =
      (0 : EuclideanSpace ℂ (Fin 1) [⋀^Fin 2]→L[ℝ] ℝ).coeffMatrix 0 0
    rw [hadiag, hare]
    simp
  have ha0 := ha.ext (ContinuousAlternatingMap.isOneOne_zero (n := 1)) hmat
  simpa [a] using ha0

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

local instance scalarRouteIntegralZeroMeasurable : MeasurableSpace M := borel M
local instance scalarRouteIntegralZeroBorel : BorelSpace M := ⟨rfl⟩

variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
private theorem integrable_primitive_sq_integrand (ω₀ : KahlerForm n M)
    {γ : FormField (EuclideanSpace ℂ (Fin n)) M 2}
    (hγsmooth : γ.IsSmooth) :
    Integrable (fun x => ComplexFormField.pointwiseHermitianInner ω₀.toRiemannianMetric 2 x
      (γ, 0) (γ, 0)) ω₀.volume := by
  rw [ω₀.volume_eq_riemannianVolumeMeasure]
  exact ComplexFormField.integrable_pointwiseHermitianInner ω₀.toRiemannianMetric 2
    (γ, 0) (γ, 0) ⟨hγsmooth, FormField.isSmooth_zero⟩
    ⟨hγsmooth, FormField.isSmooth_zero⟩

private theorem real_pairing_complex (ω₀ : KahlerForm n M)
    (γ : FormField (EuclideanSpace ℂ (Fin n)) M 2) (x : M) :
    ComplexFormField.pointwiseHermitianInner ω₀.toRiemannianMetric 2 x (γ, 0) (γ, 0) =
      (FormField.pointwiseRealInner ω₀.toRiemannianMetric 2 x γ γ : ℂ) := by
  simp [ComplexFormField.pointwiseHermitianInner, FormField.pointwiseRealInner,
    CalabiYau.L2.tensorInnerPointwise_0s_zero_left,
    CalabiYau.L2.tensorInnerPointwise_0s_zero_right]

variable [T2Space M] [SigmaCompactSpace M] in
private theorem complex_integral_zero_of_scaled_real_norm (ω₀ : KahlerForm n M)
    (γ : FormField (EuclideanSpace ℂ (Fin n)) M 2)
    (hz : (∫ x, -((n - 2).factorial : ℝ) *
      FormField.pointwiseRealInner ω₀.toRiemannianMetric 2 x γ γ ∂ω₀.volume) = 0) :
    (∫ x, ComplexFormField.pointwiseHermitianInner ω₀.toRiemannianMetric 2 x
      (γ, 0) (γ, 0) ∂ω₀.volume) = 0 := by
  rw [integral_const_mul] at hz
  have hfac : -((n - 2).factorial : ℝ) ≠ 0 := by
    apply neg_ne_zero.mpr
    exact_mod_cast (Nat.factorial_ne_zero (n - 2))
  have hq0 : (∫ x, FormField.pointwiseRealInner ω₀.toRiemannianMetric 2 x γ γ
      ∂ω₀.volume) = 0 := (mul_eq_zero.mp hz).resolve_left hfac
  simp_rw [real_pairing_complex]
  rw [integral_complex_ofReal, hq0]
  rfl

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M] [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] in
private theorem primitive_top_field_cast_apply {k l : ℕ} (h : k = l)
    (β : FormField (EuclideanSpace ℂ (Fin n)) M k) (x : M) :
    cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M) h) β x =
      (β x).domDomCongr (Fin.castOrderIso h) := by
  cases h
  rfl

private theorem primitive_square_signed_density (hn : 2 ≤ n) (ω₀ : KahlerForm n M)
    {γ : FormField (EuclideanSpace ℂ (Fin n)) M 2} (hγone : γ.IsOneOne)
    (x : M) (htrace : (ω₀ x).relTrace (γ x) = 0) :
    ω₀.signedTopFormDensity
      (cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M)
        (by omega : 2 + (2 + 2 * (n - 2)) = 2 * n))
        (FormField.wedge γ (FormField.wedge γ
          (FormField.wedgePow ω₀.toFormField (n - 2))))) x =
      -((n - 2).factorial : ℝ) *
        FormField.pointwiseRealInner ω₀.toRiemannianMetric 2 x γ γ := by
  unfold KahlerForm.signedTopFormDensity
  have hcoef := primitive_exact_wedge_topFormCoeff hn ω₀ hγone x htrace
  have hden : ContinuousAlternatingMap.topFormCoeff (ω₀.topFormVolume x) ≠ 0 := by
    have hpos : 0 < ContinuousAlternatingMap.topFormCoeff (ω₀.topFormVolume x) := by
      rw [← FormField.chartRep_self ω₀.topFormVolume x,
        ω₀.topFormVolume_chartCoeff x (mem_extChartAt_target x)]
      rw [KahlerForm.volumeDensityInChart]
      exact mul_pos (by positivity)
        (RCLike.pos_iff.mp (ω₀.posDef_metricInChart x (mem_extChartAt_target x)).det_pos).1
    exact hpos.ne'
  have hnum :
      ContinuousAlternatingMap.topFormCoeff
        (cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M)
          (by omega : 2 + (2 + 2 * (n - 2)) = 2 * n))
          (FormField.wedge γ (FormField.wedge γ
            (FormField.wedgePow ω₀.toFormField (n - 2)))) x) =
      -((n - 2).factorial : ℝ) *
        FormField.pointwiseRealInner ω₀.toRiemannianMetric 2 x γ γ *
          ContinuousAlternatingMap.topFormCoeff (ω₀.topFormVolume x) := by
    rw [primitive_top_field_cast_apply]
    simpa [FormField.wedge_apply, FormField.wedgePow_apply] using hcoef
  rw [hnum]
  field_simp [hden]

private theorem primitive_square_top_signed_density_eq_norm (hn : 2 ≤ n)
    (ω₀ : KahlerForm n M) {γ : FormField (EuclideanSpace ℂ (Fin n)) M 2}
    (hγone : γ.IsOneOne) (htrace : ∀ x, (ω₀ x).relTrace (γ x) = 0)
    (θ : FormField (EuclideanSpace ℂ (Fin n)) M (2 * n - 1))
    (hθd : cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M)
        (by omega : (2 * n - 1) + 1 = 2 * n)) θ.extDeriv =
      cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M)
        (by omega : 2 + (2 + 2 * (n - 2)) = 2 * n))
        (FormField.wedge γ (FormField.wedge γ
          (FormField.wedgePow ω₀.toFormField (n - 2)))))
    (x : M) :
    ω₀.signedTopFormDensity
      (cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M)
        (by omega : (2 * n - 1) + 1 = 2 * n)) θ.extDeriv) x =
      -((n - 2).factorial : ℝ) *
        FormField.pointwiseRealInner ω₀.toRiemannianMetric 2 x γ γ := by
  rw [hθd]
  exact primitive_square_signed_density hn ω₀ hγone x (htrace x)

variable [T2Space M] [SigmaCompactSpace M] in
private theorem primitive_square_top_signed_density_integral_eq_norm (hn : 2 ≤ n)
    (ω₀ : KahlerForm n M) {γ : FormField (EuclideanSpace ℂ (Fin n)) M 2}
    (hγone : γ.IsOneOne) (htrace : ∀ x, (ω₀ x).relTrace (γ x) = 0)
    (θ : FormField (EuclideanSpace ℂ (Fin n)) M (2 * n - 1))
    (hθd : cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M)
        (by omega : (2 * n - 1) + 1 = 2 * n)) θ.extDeriv =
      cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M)
        (by omega : 2 + (2 + 2 * (n - 2)) = 2 * n))
        (FormField.wedge γ (FormField.wedge γ
          (FormField.wedgePow ω₀.toFormField (n - 2))))) :
    (∫ x, ω₀.signedTopFormDensity
      (cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M)
        (by omega : (2 * n - 1) + 1 = 2 * n)) θ.extDeriv) x ∂ω₀.volume) =
    (∫ x, -((n - 2).factorial : ℝ) *
      FormField.pointwiseRealInner ω₀.toRiemannianMetric 2 x γ γ ∂ω₀.volume) := by
  apply integral_congr_ae
  filter_upwards with x
  exact primitive_square_top_signed_density_eq_norm hn ω₀ hγone htrace θ hθd x

private theorem primitive_toFormField_cast {k l : ℕ}
    (h : k = l)
    (β : CalabiYau.DifferentialForm 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M k) :
    (cast (congrArg (CalabiYau.DifferentialForm 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M) h) β).toFormField =
      cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M) h) β.toFormField := by
  cases h
  rfl
section

variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M]


/-- Consume the published normalized primitive coefficient identity, followed by
native Stokes on the actual smooth primitive `θ`. -/
private theorem integral_scaled_norm_eq_zero_of_primitive_top (hn : 2 ≤ n)
    (ω₀ : KahlerForm n M) {γ : FormField (EuclideanSpace ℂ (Fin n)) M 2}
    (_hγsmooth : γ.IsSmooth) (hγone : γ.IsOneOne)
    (hγtrace : ∀ x, ContinuousAlternatingMap.relTrace (ω₀ x) (γ x) = 0)
    (_hγintegrable : Integrable (fun x => -((n - 2).factorial : ℝ) *
      FormField.pointwiseRealInner ω₀.toRiemannianMetric 2 x γ γ) ω₀.volume)
    (θ : FormField (EuclideanSpace ℂ (Fin n)) M (2 * n - 1)) (hθsmooth : θ.IsSmooth)
    (hθd : cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M)
        (by omega : (2 * n - 1) + 1 = 2 * n)) θ.extDeriv =
      cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M)
        (by omega : 2 + (2 + 2 * (n - 2)) = 2 * n))
        (FormField.wedge γ (FormField.wedge γ
          (FormField.wedgePow ω₀.toFormField (n - 2))))) :
    (∫ x, -((n - 2).factorial : ℝ) *
      FormField.pointwiseRealInner ω₀.toRiemannianMetric 2 x γ γ ∂ω₀.volume) = 0 := by
  have hHR := primitive_square_top_signed_density_integral_eq_norm
    hn ω₀ hγone hγtrace θ hθd
  rw [← hHR]
  have hStokes := ω₀.signedTopFormIntegral_cast_exteriorDerivative_eq_zero
    (by omega : 0 < n) (by omega : (2 * n - 1) + 1 = 2 * n)
    (θ.toDifferentialForm hθsmooth)
  rw [KahlerForm.signedTopFormIntegral_apply] at hStokes
  change (∫ x, ω₀.signedTopFormDensity
    (cast (congrArg (CalabiYau.DifferentialForm
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M)
      (by omega : (2 * n - 1) + 1 = 2 * n))
      (CalabiYau.DifferentialForm.exteriorDerivative
        (θ.toDifferentialForm hθsmooth))).toFormField x ∂ω₀.volume) = 0 at hStokes
  rw [primitive_toFormField_cast, CalabiYau.DifferentialForm.toFormField_exteriorDerivative,
    CalabiYau.DifferentialForm.toFormField_toDifferentialForm] at hStokes
  all_goals omega

/-- Convert the vanishing scaled real norm integral to the actual complex pairing,
then cancel the nonzero factorial. -/
private theorem integral_norm_eq_zero_of_primitive_top (hn : 2 ≤ n)
    (ω₀ : KahlerForm n M) {γ : FormField (EuclideanSpace ℂ (Fin n)) M 2}
    (hγsmooth : γ.IsSmooth) (hγone : γ.IsOneOne)
    (hγtrace : ∀ x, ContinuousAlternatingMap.relTrace (ω₀ x) (γ x) = 0)
    (hγintegrable : Integrable (fun x => ComplexFormField.pointwiseHermitianInner
      ω₀.toRiemannianMetric 2 x (γ, 0) (γ, 0)) ω₀.volume)
    (θ : FormField (EuclideanSpace ℂ (Fin n)) M (2 * n - 1)) (hθsmooth : θ.IsSmooth)
    (hθd : cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M)
        (by omega : (2 * n - 1) + 1 = 2 * n)) θ.extDeriv =
      cast (congrArg (FormField (EuclideanSpace ℂ (Fin n)) M)
        (by omega : 2 + (2 + 2 * (n - 2)) = 2 * n))
        (FormField.wedge γ (FormField.wedge γ
          (FormField.wedgePow ω₀.toFormField (n - 2))))) :
    (∫ x, ComplexFormField.pointwiseHermitianInner ω₀.toRiemannianMetric 2 x
      (γ, 0) (γ, 0) ∂ω₀.volume) = 0 := by
  have hrealInt : Integrable
      (fun x => FormField.pointwiseRealInner ω₀.toRiemannianMetric 2 x γ γ)
      ω₀.volume := by
    have hreal := hγintegrable.re
    simpa [real_pairing_complex] using hreal
  have hscaledInt : Integrable
      (fun x => -((n - 2).factorial : ℝ) *
        FormField.pointwiseRealInner ω₀.toRiemannianMetric 2 x γ γ)
      ω₀.volume := hrealInt.const_mul _
  have hscaled := integral_scaled_norm_eq_zero_of_primitive_top hn ω₀
    hγsmooth hγone hγtrace hscaledInt θ hθsmooth hθd
  exact complex_integral_zero_of_scaled_real_norm ω₀ γ hscaled

/-- The Stokes–Hodge–Riemann *integral identity* for an exact primitive real `(1,1)`-form.
This does not assume that the form itself vanishes. -/
theorem integral_primitive_sq_eq_zero (ω₀ : KahlerForm n M)
    {γ : FormField (EuclideanSpace ℂ (Fin n)) M 2}
    (hγsmooth : γ.IsSmooth) (hγone : γ.IsOneOne) (hγexact : γ.IsExact)
    (hγtrace : ∀ x, ContinuousAlternatingMap.relTrace (ω₀ x) (γ x) = 0) :
    (∫ x, ComplexFormField.pointwiseHermitianInner ω₀.toRiemannianMetric 2 x
      (γ, 0) (γ, 0) ∂ω₀.volume) = 0 := by
  by_cases hn0 : n = 0
  · subst n
    have hγ0 := degree_two_zero_zero_dim γ
    simp [hγ0, ComplexFormField.pointwiseHermitianInner, FormField.pointwiseRealInner,
      CalabiYau.L2.tensorInnerPointwise_0s_zero_left]
  · by_cases hn1 : n = 1
    · subst n
      have hγ0 := primitive_oneone_zero_one ω₀ γ hγone hγtrace
      simp [hγ0, ComplexFormField.pointwiseHermitianInner, FormField.pointwiseRealInner,
      CalabiYau.L2.tensorInnerPointwise_0s_zero_left]
    · have hn : 2 ≤ n := by omega
      obtain ⟨θ, hθsmooth, hθd⟩ := FormField.exists_primitive_wedge_sq_wedgePow hn
        ω₀.toFormField γ ω₀.isSmooth ω₀.isClosed hγsmooth hγexact
      exact integral_norm_eq_zero_of_primitive_top hn ω₀ hγsmooth hγone hγtrace
        (integrable_primitive_sq_integrand ω₀ hγsmooth) θ hθsmooth hθd

end

end KahlerForm
