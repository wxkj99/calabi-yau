module

public import CalabiYau.Geometry.Kahler.Riemannian.Metric
public import CalabiYau.Geometry.Kahler.Laplacian.Cofactor
public import CalabiYau.Geometry.Riemannian.Operator.Gradient.Basic
public import CalabiYau.Geometry.Riemannian.Volume.Chart.Density
import CalabiYau.Geometry.Kahler.Laplacian
import CalabiYau.Geometry.Kahler.Riemannian.Volume.GramHaarNormalization
import CalabiYau.Geometry.Kahler.Riemannian.Laplacian.ComplexTrace.RealCofactorTransport

/-!
# From weighted real divergence to the Kähler complex trace

In a Kähler chart, the real inverse-Gram weighted divergence is twice the
complex trace of the Hessian. The positive chart density differs from
`2^n det(metricInChart)` by the *constant* chart-model-basis Jacobian `J`;
this factor cancels under differentiation and division. Kähler closedness
makes the complex cofactor divergence vanish.

The real inverse Gram uses `i j` (gradient coefficient `i`, derivative `j`).
The complex trace uses the inverse Hermitian entry `k j` on Hessian `j k`.
In complex dimension zero both sides vanish. In dimension one with
`ω = i dz ∧ dż` and `f = x² + y²`, the real expression is `2` and the
complex trace is `1`. The chart-model basis may have `J ≠ 1`: the real
basis `(2,i)` has `J=2`, Gram determinant `16` and density `4`.

Source: Ballmann, *Lectures on Kähler Manifolds*, §5, Exercise 5.51(1),
printed p. 75. Ballmann uses `Δ_B = −div grad` and gives a *negative*
complex trace; this project's `ΔG = +div grad` reverses the sign.
Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §§1.1, 1.3,
provides the positive real metric and volume conventions.
-/

@[expose] public section

open scoped Manifold ContDiff Topology ComplexOrder

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

private theorem chartPartialZComplex_chartPartialBar_eq_complexHessian
    {u : EuclideanSpace ℂ (Fin n) → ℝ} {z : EuclideanSpace ℂ (Fin n)}
    (hu : ContDiffAt ℝ 2 u z) (j k : Fin n) :
    chartPartialZComplex (fun w ↦ chartPartialBar u w k) z j =
      complexHessian u z j k := by
  let ej : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j 1
  let ek : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single k 1
  have hu1 : ContDiffAt ℝ 1 (fderiv ℝ u) z :=
    hu.fderiv_right (m := 1) (by norm_num)
  have hfdDiff : DifferentiableAt ℝ (fderiv ℝ u) z :=
    hu1.differentiableAt (by norm_num)
  have hA : DifferentiableAt ℝ (fun w ↦ fderiv ℝ u w ek) z :=
    hfdDiff.clm_apply (differentiableAt_const _)
  have hB : DifferentiableAt ℝ (fun w ↦ fderiv ℝ u w (Complex.I • ek)) z :=
    hfdDiff.clm_apply (differentiableAt_const _)
  have hAcomplex : DifferentiableAt ℝ (fun w ↦ (fderiv ℝ u w ek : ℂ)) z := by
    exact Complex.ofRealCLM.differentiableAt.comp z hA
  have hBcomplex : DifferentiableAt ℝ (fun w ↦
      (fderiv ℝ u w (Complex.I • ek) : ℂ)) z := by
    exact Complex.ofRealCLM.differentiableAt.comp z hB
  have hD (v q : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ fderiv ℝ u w q) z v =
        fderiv ℝ (fderiv ℝ u) z v q := by
    have h := fderiv_clm_apply (u := fun _ : EuclideanSpace ℂ (Fin n) ↦ q)
      hfdDiff (differentiableAt_const _)
    have h' := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ ↦ L v) h
    simpa using h'
  have hAc (v : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ (fderiv ℝ u w ek : ℂ)) z v =
        (fderiv ℝ (fderiv ℝ u) z v ek : ℂ) := by
    have hcomp := (Complex.ofRealCLM.hasFDerivAt.comp z hA.hasFDerivAt).fderiv
    have heval := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L v) hcomp
    simpa [Function.comp_def, hD v ek] using heval
  have hBc (v : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ (fderiv ℝ u w (Complex.I • ek) : ℂ)) z v =
        (fderiv ℝ (fderiv ℝ u) z v (Complex.I • ek) : ℂ) := by
    have hcomp := (Complex.ofRealCLM.hasFDerivAt.comp z hB.hasFDerivAt).fderiv
    have heval := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L v) hcomp
    simpa [Function.comp_def, hD v (Complex.I • ek)] using heval
  have hnum : DifferentiableAt ℝ (fun w ↦
      (fderiv ℝ u w ek : ℂ) + Complex.I * fderiv ℝ u w (Complex.I • ek)) z :=
    hAcomplex.add (hBcomplex.const_mul Complex.I)
  have hbar : (fun w ↦ chartPartialBar u w k) =
      fun w ↦ (2 : ℂ)⁻¹ * ((fderiv ℝ u w ek : ℂ) +
        Complex.I * fderiv ℝ u w (Complex.I • ek)) := by
    funext w
    simp only [chartPartialBar, ek, div_eq_mul_inv]
    ring
  have hpartial (v : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ chartPartialBar u w k) z v =
        (2 : ℂ)⁻¹ * ((fderiv ℝ (fderiv ℝ u) z v ek : ℂ) +
          Complex.I * fderiv ℝ (fderiv ℝ u) z v (Complex.I • ek)) := by
    rw [hbar, fderiv_const_mul hnum (2 : ℂ)⁻¹,
      fderiv_fun_add hAcomplex (hBcomplex.const_mul Complex.I),
      fderiv_const_mul hBcomplex Complex.I]
    simp only [add_apply, smul_apply, smul_eq_mul, hAc, hBc]
  unfold chartPartialZComplex
  rw [hpartial ej, hpartial (Complex.I • ej)]
  rw [complexHessian_apply hu j k]
  simp only [ej, ek, div_eq_mul_inv]
  have hsymm := hu.isSymmSndFDerivAt (by norm_num [minSmoothness])
  have hsymm₁ : fderiv ℝ (fderiv ℝ u) z (Complex.I • ej) ek =
      fderiv ℝ (fderiv ℝ u) z ek (Complex.I • ej) := hsymm _ _
  have hsymm₂ : fderiv ℝ (fderiv ℝ u) z (Complex.I • ej) (Complex.I • ek) =
      fderiv ℝ (fderiv ℝ u) z (Complex.I • ek) (Complex.I • ej) := hsymm _ _
  rw [hsymm₁, hsymm₂]
  ring_nf
  rw [Complex.I_sq]
  ring_nf

private theorem chartCofactor_divergence_complexHessian
    {G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    {u : EuclideanSpace ℂ (Fin n) → ℝ} {z : EuclideanSpace ℂ (Fin n)}
    {U : Set (EuclideanSpace ℂ (Fin n))}
    (hG : ∀ a b, ContDiffAt ℝ 1 (fun w ↦ G w a b) z)
    (hunit : IsUnit (G z))
    (hdiv : ChartCofactorDivergenceFree G U) (hz : z ∈ U)
    (hu : ContDiffAt ℝ 2 u z) :
    ∑ k, ∑ j, chartPartialZComplex
      (fun w ↦ (G w).det * (G w)⁻¹ k j * chartPartialBar u w k) z j =
      (G z).det * Matrix.trace ((G z)⁻¹ * complexHessian u z) := by
  have hdetDiff : DifferentiableAt ℝ (fun w ↦ (G w).det) z := by
    simp_rw [Matrix.det_apply]
    fun_prop
  have hbarDiff (k : Fin n) :
      DifferentiableAt ℝ (fun w ↦ chartPartialBar u w k) z := by
    unfold chartPartialBar
    fun_prop
  have hcoefDiff (k j : Fin n) :
      DifferentiableAt ℝ (fun w ↦ (G w).det * (G w)⁻¹ k j) z :=
    hdetDiff.mul (chartInv_differentiableAt hG hunit k j)
  have hterm (k j : Fin n) :
      chartPartialZComplex
          (fun w ↦ (G w).det * (G w)⁻¹ k j * chartPartialBar u w k) z j =
        chartPartialZComplex (fun w ↦ (G w).det * (G w)⁻¹ k j) z j *
            chartPartialBar u z k +
          ((G z).det * (G z)⁻¹ k j) *
            chartPartialZComplex (fun w ↦ chartPartialBar u w k) z j := by
    simpa using chartPartialZComplex_mul (hcoefDiff k j) (hbarDiff k) j
  have hsum (k : Fin n) :
      (∑ j, chartPartialZComplex
        (fun w ↦ (G w).det * (G w)⁻¹ k j * chartPartialBar u w k) z j) =
        (G z).det * ∑ j, (G z)⁻¹ k j * complexHessian u z j k := by
    have hdivk := hdiv z hz k
    calc
      _ = ∑ j, (chartPartialZComplex
            (fun w ↦ (G w).det * (G w)⁻¹ k j) z j * chartPartialBar u z k +
          ((G z).det * (G z)⁻¹ k j) * complexHessian u z j k) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hterm k j, chartPartialZComplex_chartPartialBar_eq_complexHessian hu j k]
      _ = (∑ j, chartPartialZComplex
            (fun w ↦ (G w).det * (G w)⁻¹ k j) z j) * chartPartialBar u z k +
          ∑ j, ((G z).det * (G z)⁻¹ k j) * complexHessian u z j k := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      _ = (G z).det * ∑ j, (G z)⁻¹ k j * complexHessian u z j k := by
        rw [hdivk]
        simp only [zero_mul, zero_add]
        rw [show (∑ j, ((G z).det * (G z)⁻¹ k j) * complexHessian u z j k) =
            ∑ j, (G z).det * ((G z)⁻¹ k j * complexHessian u z j k) by
              apply Finset.sum_congr rfl
              intro j hj
              ring,
          ← Finset.mul_sum]
  calc
    _ = ∑ k, (G z).det * ∑ j, (G z)⁻¹ k j * complexHessian u z j k := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hsum k
    _ = (G z).det * ∑ k, ∑ j, (G z)⁻¹ k j * complexHessian u z j k := by
      rw [Finset.mul_sum]
    _ = (G z).det * Matrix.trace ((G z)⁻¹ * complexHessian u z) := by
      congr 1

private theorem linearMapAt_symmL_eq_tangentCoordChange
    {x₀ x z : M}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source)
    (hz₀ : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).source) :
    (trivializationAt (EuclideanSpace ℂ (Fin n))
        (TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x₀).continuousLinearMapAt ℝ z ∘L
      (trivializationAt (EuclideanSpace ℂ (Fin n))
        (TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x).symmL ℝ z =
      tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x₀ z := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
      (by simpa [extChartAt_source] using hz₀),
    TangentBundle.symmL_trivializationAt_eq_core
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
      (by simpa [extChartAt_source] using hz)]
  apply ContinuousLinearMap.ext
  intro v
  have hw : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source ∩
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) z).source ∩
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).source :=
    ⟨⟨hz, mem_extChartAt_source z⟩, hz₀⟩
  change tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) z x₀ z
      (tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x z z v) = _
  exact tangentCoordChange_comp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
    (w := x) (x := z) (y := x₀) (z := z) hw

private theorem chartBasisVecFiber_model_eq_tangentCoordChange
    (x y : M) {i : Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))}
    (hyx : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source) :
    CalabiYau.tangentSpaceModelContinuousLinearEquiv
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) y
      (CalabiYau.Tensor.Coordinates.chartBasisVecFiber
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x i y) =
      tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y
        (CalabiYau.Tensor.Coordinates.chartModelBasis
          (EuclideanSpace ℂ (Fin n)) i) := by
  have hyx' : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source := by
    simpa [extChartAt_source] using hyx
  have hyy : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).source :=
    mem_extChartAt_source y
  have hcomp := linearMapAt_symmL_eq_tangentCoordChange
    (x₀ := y) (x := x) (z := y) hyx' hyy
  have hycenter :
      (trivializationAt (EuclideanSpace ℂ (Fin n))
        (TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) y).continuousLinearMapAt ℝ y =
        ContinuousLinearMap.id ℝ (EuclideanSpace ℂ (Fin n)) := by
    rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
      (by simp)]
    apply ContinuousLinearMap.ext
    intro v
    exact (tangentBundleCore 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M).coordChange_self
      (achart (EuclideanSpace ℂ (Fin n)) y) y (mem_chart_source _ y) v
  change (CalabiYau.tangentSpaceModelContinuousLinearEquiv
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) y)
      ((trivializationAt (EuclideanSpace ℂ (Fin n))
        (TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x).symmL ℝ y
        (CalabiYau.Tensor.Coordinates.chartModelBasis
          (EuclideanSpace ℂ (Fin n)) i)) = _
  rw [CalabiYau.tangentSpaceModelContinuousLinearEquiv_apply]
  calc
    _ = (ContinuousLinearMap.id ℝ (EuclideanSpace ℂ (Fin n)))
        ((trivializationAt (EuclideanSpace ℂ (Fin n))
          (TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x).symmL ℝ y
          (CalabiYau.Tensor.Coordinates.chartModelBasis
            (EuclideanSpace ℂ (Fin n)) i)) := rfl
    _ = (trivializationAt (EuclideanSpace ℂ (Fin n))
        (TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) y).continuousLinearMapAt ℝ y
          ((trivializationAt (EuclideanSpace ℂ (Fin n))
            (TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x).symmL ℝ y
            (CalabiYau.Tensor.Coordinates.chartModelBasis
              (EuclideanSpace ℂ (Fin n)) i)) := by
      rw [hycenter]
      rfl
    _ = tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y
          (CalabiYau.Tensor.Coordinates.chartModelBasis
            (EuclideanSpace ℂ (Fin n)) i) :=
      DFunLike.congr_fun hcomp (CalabiYau.Tensor.Coordinates.chartModelBasis
        (EuclideanSpace ℂ (Fin n)) i)

private theorem chartGramOnE_eq_complexChartModelGram
    (ω₀ : KahlerForm n M) (x : M) {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    CalabiYau.Tensor.Coordinates.chartGramMatrix
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) ω₀.toRiemannianMetric x
        ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z) =
      (ω₀.toFormField.chartRep x z).complexChartModelGram := by
  let E := EuclideanSpace ℂ (Fin n)
  let b := CalabiYau.Tensor.Coordinates.chartModelBasis E
  let y := (extChartAt 𝓘(ℝ, E) x).symm z
  have hyx : y ∈ (chartAt E x).source := by
    simpa only [extChartAt_source] using (extChartAt 𝓘(ℝ, E) x).map_target hz
  have hchange (v : E) :
      tangentCoordChange 𝓘(ℝ, E) x y y (EuclideanSpace.complexStructure n v) =
        EuclideanSpace.complexStructure n (tangentCoordChange 𝓘(ℝ, E) x y y v) := by
    exact tangentCoordChange_I_smul (x := x) (y := y) (z := y)
      ⟨(by simpa only [extChartAt_source] using hyx), mem_extChartAt_source y⟩ v
  ext i j
  rw [CalabiYau.Tensor.Coordinates.chartGramMatrix_apply,
    toRiemannianMetric_inner_apply]
  change (ω₀ y) ![
      (CalabiYau.tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) y)
        (CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := 𝓘(ℝ, E)) x i y),
      EuclideanSpace.complexStructure n
        ((CalabiYau.tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) y)
          (CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := 𝓘(ℝ, E)) x j y))] = _
  rw [chartBasisVecFiber_model_eq_tangentCoordChange x y (i := i) hyx,
    chartBasisVecFiber_model_eq_tangentCoordChange x y (i := j) hyx]
  change (ω₀ y) ![tangentCoordChange 𝓘(ℝ, E) x y y (b i),
    EuclideanSpace.complexStructure n (tangentCoordChange 𝓘(ℝ, E) x y y (b j))] =
    (ω₀.toFormField.chartRep x z)
      ![b i, EuclideanSpace.complexStructure n (b j)]
  rw [FormField.chartRep]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  rw [← hchange (b j)]
  congr 1
  funext k
  fin_cases k <;> rfl

open scoped ComplexOrder in
private theorem chartDensityOnE_eq_complexDet
    (ω₀ : KahlerForm n M) (x : M) {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    CalabiYau.RiemannianVolume.chartDensityOnE
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) ω₀.toRiemannianMetric x z =
      (CalabiYau.RiemannianVolume.complexChartBasisVolume n).toReal *
        (2 : ℝ) ^ n * (ω₀.metricInChart x z).det.re := by
  let E := EuclideanSpace ℂ (Fin n)
  have hmatrix := chartGramOnE_eq_complexChartModelGram ω₀ x hz
  let α := ω₀.toFormField.chartRep x z
  have hα₁ : α.IsOneOne := ω₀.chartRep_isOneOne x hz
  have hα₂ : α.coeffMatrix.PosDef := by
    change (ω₀.metricInChart x z).PosDef
    exact ω₀.posDef_metricInChart x hz
  have hα : α.IsPositive :=
    (ContinuousAlternatingMap.isPositive_iff (α := α)).mpr ⟨hα₁, hα₂⟩
  have hgram := CalabiYau.RiemannianVolume.gramDet_chartModelBasis n
    (ω₀.toFormField.chartRep x z) hα
  have hdetReal : (ω₀.metricInChart x z).det.im = 0 := by
    have hstar : star (ω₀.metricInChart x z).det = (ω₀.metricInChart x z).det := by
      calc
        star (ω₀.metricInChart x z).det =
            (Matrix.conjTranspose (ω₀.metricInChart x z)).det :=
          (Matrix.det_conjTranspose (ω₀.metricInChart x z)).symm
        _ = (ω₀.metricInChart x z).det :=
          congrArg Matrix.det (ω₀.posDef_metricInChart x hz).isHermitian.eq
    have him := congrArg Complex.im hstar
    have him' : -(ω₀.metricInChart x z).det.im = (ω₀.metricInChart x z).det.im := by
      simpa using him
    linarith
  have hdetReal' : α.coeffMatrix.det.im = 0 := by
    simpa [α, metricInChart] using hdetReal
  have hdetPos : 0 < (ω₀.metricInChart x z).det.re := by
    have hpos := (ω₀.posDef_metricInChart x hz).det_pos
    exact (RCLike.pos_iff.mp hpos).1
  have hJnonneg : 0 ≤ (CalabiYau.RiemannianVolume.complexChartBasisVolume n).toReal :=
    ENNReal.toReal_nonneg
  rw [CalabiYau.RiemannianVolume.chartDensityOnE,
    CalabiYau.RiemannianVolume.chartDensity, hmatrix]
  rw [ContinuousAlternatingMap.complexChartModelGram,
    hgram, Complex.normSq_apply, hdetReal']
  simp only [mul_zero, add_zero]
  have hpow : (2 : ℝ) ^ (2 * n) = ((2 : ℝ) ^ n) ^ 2 := by
    rw [show 2 * n = n * 2 by omega, pow_mul]
  calc
    Real.sqrt ((CalabiYau.RiemannianVolume.complexChartBasisVolume n).toReal ^ 2 *
        (2 : ℝ) ^ (2 * n) *
          ((ω₀.toFormField.chartRep x z).coeffMatrix.det.re *
            (ω₀.toFormField.chartRep x z).coeffMatrix.det.re)) =
      Real.sqrt ((CalabiYau.RiemannianVolume.complexChartBasisVolume n).toReal ^ 2 *
        (ω₀.metricInChart x z).det.re ^ 2 * (2 : ℝ) ^ (2 * n)) := by
          congr 1
          simp [metricInChart, pow_two]
          ring_nf
    _ = Real.sqrt (((CalabiYau.RiemannianVolume.complexChartBasisVolume n).toReal *
        (ω₀.metricInChart x z).det.re * (2 : ℝ) ^ n) ^ 2) := by
          congr 1
          rw [hpow]
          ring
    _ = |(CalabiYau.RiemannianVolume.complexChartBasisVolume n).toReal *
        (ω₀.metricInChart x z).det.re * (2 : ℝ) ^ n| := Real.sqrt_sq_eq_abs _
    _ = (CalabiYau.RiemannianVolume.complexChartBasisVolume n).toReal *
        (2 : ℝ) ^ n * (ω₀.metricInChart x z).det.re := by
          rw [abs_of_nonneg (mul_nonneg
            (mul_nonneg hJnonneg (le_of_lt hdetPos)) (by positivity))]
          ring

/-- The chart-level Kähler cancellation: weighted inverse real Gram divergence
equals twice the real part of the complex Hessian trace. -/
theorem real_chart_weighted_divergence_eq_complex_trace
    (ω₀ : KahlerForm n M) (f : M → ℝ)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f) (x : M) :
    let I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
    let g := ω₀.toRiemannianMetric
    let z := extChartAt I x x
    (∑ i : Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))),
      CalabiYau.Tensor.Coordinates.partialDeriv (E := EuclideanSpace ℂ (Fin n)) i
        (fun w : EuclideanSpace ℂ (Fin n) =>
          CalabiYau.RiemannianVolume.chartDensityOnE (I := I) g x w *
            ∑ j : Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))),
              CalabiYau.Riemannian.chartInvGramMatrix (I := I) g x
                  ((extChartAt I x).symm w) i j *
                CalabiYau.Tensor.Coordinates.partialDeriv (E := EuclideanSpace ℂ (Fin n)) j
                  (f ∘ (extChartAt I x).symm) w)
        z) /
      CalabiYau.RiemannianVolume.chartDensity (I := I) g x x =
      2 * RCLike.re
        (((ω₀.metricInChart x z)⁻¹ *
          complexHessian (f ∘ (extChartAt I x).symm) z).trace) := by
  let E := EuclideanSpace ℂ (Fin n)
  let I := 𝓘(ℝ, E)
  let ψ := extChartAt I x
  let z := ψ x
  let u : E → ℝ := f ∘ ψ.symm
  let α : E → E [⋀^Fin 2]→L[ℝ] ℝ := ω₀.toFormField.chartRep x
  let G : E → Matrix (Fin n) (Fin n) ℂ := ω₀.metricInChart x
  let J : ℝ := (CalabiYau.RiemannianVolume.complexChartBasisVolume n).toReal
  have hz : z ∈ ψ.target := mem_extChartAt_target x
  have hpos (w : E) (hw : w ∈ ψ.target) : (α w).IsPositive :=
    ContinuousAlternatingMap.isPositive_iff.mpr
      ⟨ω₀.chartRep_isOneOne x hw, ω₀.posDef_metricInChart x hw⟩
  have hposEv : ∀ᶠ w in 𝓝 z, (α w).IsPositive := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds hz] with w hw
    exact hpos w hw
  have hα : ContDiffAt ℝ 1 α z := by
    have ht := (ω₀.isSmooth x).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz)
    exact ht.of_le (by norm_num)
  have hu : ContDiffAt ℝ 2 u z := by
    have hfOn : ContMDiffOn I 𝓘(ℝ) ∞ f Set.univ := contMDiffOn_univ.mpr hf
    have huOn : ContDiffOn ℝ ∞ u ψ.target := by
      exact (hfOn.comp (contMDiffOn_extChartAt_symm x)
        (by intro w hw; simp)).contDiffOn
    exact (huOn.contDiffAt ((isOpen_extChartAt_target x).mem_nhds hz)).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hcontract : ∀ᶠ w in 𝓝 z,
      ContinuousAlternatingMap.ComplexChartInverseGramContraction
        (α w) (fderiv ℝ u w) :=
    hposEv.mono (fun w hw => hw.inverse_complexChartModelGram_contract (fderiv ℝ u w))
  have htransport := formGram_weighted_divergence_eq_complex_cofactor α u z
    hα hu hposEv hcontract
  have hflux (w : E) (hw : w ∈ ψ.target)
      (i : Fin (Module.finrank ℝ E)) :
      CalabiYau.RiemannianVolume.chartDensityOnE (I := I)
          ω₀.toRiemannianMetric x w *
        (∑ j : Fin (Module.finrank ℝ E),
          CalabiYau.Riemannian.chartInvGramMatrix (I := I)
              ω₀.toRiemannianMetric x (ψ.symm w) i j *
            CalabiYau.Tensor.Coordinates.partialDeriv j u w) =
      J * (2 : ℝ) ^ n * (G w).det.re *
        (∑ j : Fin (Module.finrank ℝ E),
          ((α w).complexChartModelGram)⁻¹ i j *
            CalabiYau.Tensor.Coordinates.partialDeriv j u w) := by
    have hdens := chartDensityOnE_eq_complexDet ω₀ x hw
    have hgram := chartGramOnE_eq_complexChartModelGram ω₀ x hw
    dsimp only [CalabiYau.Riemannian.chartInvGramMatrix]
    rw [hgram, hdens]
  have hden : CalabiYau.RiemannianVolume.chartDensity (I := I)
      ω₀.toRiemannianMetric x x = J * (2 : ℝ) ^ n * (G z).det.re := by
    have hdens := chartDensityOnE_eq_complexDet ω₀ x hz
    calc
      _ = CalabiYau.RiemannianVolume.chartDensityOnE (I := I)
          ω₀.toRiemannianMetric x z := by
            change CalabiYau.RiemannianVolume.chartDensity (I := I)
                ω₀.toRiemannianMetric x x =
              CalabiYau.RiemannianVolume.chartDensity (I := I)
                ω₀.toRiemannianMetric x (ψ.symm z)
            rw [ψ.left_inv (mem_extChartAt_source x)]
      _ = _ := hdens
  have hG : ∀ a b : Fin n, ContDiffAt ℝ 1 (fun w => G w a b) z := by
    intro a b
    exact ((ω₀.contDiffOn_metricInChart x a b).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz)).of_le (by norm_num)
  have hunit : IsUnit (G z) := (ω₀.posDef_metricInChart x hz).isUnit
  have hcofactor :
      (∑ k : Fin n, ∑ j : Fin n,
        chartPartialZComplex
          (fun w : E => (G w).det * (G w)⁻¹ k j * chartPartialBar u w k) z j) =
        (G z).det * Matrix.trace ((G z)⁻¹ * complexHessian u z) := by
    exact chartCofactor_divergence_complexHessian hG hunit
      (ω₀.kahler_chart_cofactor_divergence x) hz hu
  have hdiverge :
      (∑ i : Fin (Module.finrank ℝ E),
        CalabiYau.Tensor.Coordinates.partialDeriv i
          (fun w : E =>
            CalabiYau.RiemannianVolume.chartDensityOnE (I := I)
                ω₀.toRiemannianMetric x w *
              ∑ j : Fin (Module.finrank ℝ E),
                CalabiYau.Riemannian.chartInvGramMatrix (I := I)
                    ω₀.toRiemannianMetric x (ψ.symm w) i j *
                  CalabiYau.Tensor.Coordinates.partialDeriv j u w) z) =
        2 * J * (2 : ℝ) ^ n *
          RCLike.re (∑ k : Fin n, ∑ j : Fin n,
            chartPartialZComplex
              (fun w : E => (G w).det * (G w)⁻¹ k j * chartPartialBar u w k) z j) := by
    calc
      _ = ∑ i : Fin (Module.finrank ℝ E),
          CalabiYau.Tensor.Coordinates.partialDeriv i
            (fun w : E => J * (2 : ℝ) ^ n * (G w).det.re *
              ∑ j : Fin (Module.finrank ℝ E),
                ((α w).complexChartModelGram)⁻¹ i j *
                  CalabiYau.Tensor.Coordinates.partialDeriv j u w) z := by
            apply Finset.sum_congr rfl
            intro i hi
            have heq :
                (fun w : E =>
                  CalabiYau.RiemannianVolume.chartDensityOnE (I := I)
                      ω₀.toRiemannianMetric x w *
                    ∑ j : Fin (Module.finrank ℝ E),
                      CalabiYau.Riemannian.chartInvGramMatrix (I := I)
                          ω₀.toRiemannianMetric x (ψ.symm w) i j *
                        CalabiYau.Tensor.Coordinates.partialDeriv j u w) =ᶠ[𝓝 z]
                (fun w : E => J * (2 : ℝ) ^ n * (G w).det.re *
                  ∑ j : Fin (Module.finrank ℝ E),
                    ((α w).complexChartModelGram)⁻¹ i j *
                      CalabiYau.Tensor.Coordinates.partialDeriv j u w) := by
              filter_upwards [(isOpen_extChartAt_target x).mem_nhds hz] with w hw
              exact hflux w hw i
            exact congrArg (fun L : E →L[ℝ] ℝ =>
              L (CalabiYau.Tensor.Coordinates.chartModelBasis E i)) heq.fderiv_eq
      _ = _ := htransport
  have hdetIm : (G z).det.im = 0 := by
    have hs : star (G z).det = (G z).det := by
      calc
        star (G z).det = (Matrix.conjTranspose (G z)).det :=
          (Matrix.det_conjTranspose (G z)).symm
        _ = (G z).det :=
          congrArg Matrix.det (ω₀.posDef_metricInChart x hz).isHermitian.eq
    have him := congrArg Complex.im hs
    have him' : -(G z).det.im = (G z).det.im := by simpa using him
    linarith
  have hdetPos : 0 < (G z).det.re :=
    (RCLike.pos_iff.mp (ω₀.posDef_metricInChart x hz).det_pos).1
  have hJpos : 0 < J :=
    ENNReal.toReal_pos
      (ne_of_gt (CalabiYau.RiemannianVolume.complexChartBasisVolume_pos n))
      (ne_of_lt (CalabiYau.RiemannianVolume.complexChartBasisVolume_lt_top n))
  have hdenPos : 0 < J * (2 : ℝ) ^ n * (G z).det.re := by positivity
  change (∑ i : Fin (Module.finrank ℝ E),
      CalabiYau.Tensor.Coordinates.partialDeriv i
        (fun w : E =>
          CalabiYau.RiemannianVolume.chartDensityOnE (I := I)
              ω₀.toRiemannianMetric x w *
            ∑ j : Fin (Module.finrank ℝ E),
              CalabiYau.Riemannian.chartInvGramMatrix (I := I)
                  ω₀.toRiemannianMetric x (ψ.symm w) i j *
                CalabiYau.Tensor.Coordinates.partialDeriv j u w) z) /
      CalabiYau.RiemannianVolume.chartDensity (I := I) ω₀.toRiemannianMetric x x =
      2 * RCLike.re (((G z)⁻¹ * complexHessian u z).trace)
  rw [hdiverge, hden, hcofactor]
  change 2 * J * (2 : ℝ) ^ n *
      ((G z).det * ((G z)⁻¹ * complexHessian u z).trace).re /
      (J * (2 : ℝ) ^ n * (G z).det.re) =
    2 * ((G z)⁻¹ * complexHessian u z).trace.re
  rw [Complex.mul_re, hdetIm]
  simp only [zero_mul, sub_zero]
  have hfactor (r : ℝ) :
      2 * J * (2 : ℝ) ^ n * ((G z).det.re * r) =
        (J * (2 : ℝ) ^ n * (G z).det.re) * (2 * r) := by ring
  rw [hfactor, mul_div_cancel_left₀ _ (ne_of_gt hdenPos)]

end KahlerForm
