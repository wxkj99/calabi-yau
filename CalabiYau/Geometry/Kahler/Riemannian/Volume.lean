module

public import CalabiYau.Geometry.Kahler.Volume
public import CalabiYau.Geometry.Riemannian.Volume.Basic
public import CalabiYau.Geometry.Riemannian.Volume.Invariance
public import CalabiYau.Geometry.Kahler.Riemannian.Metric
import CalabiYau.Geometry.Kahler.Riemannian.Volume.GramHaarNormalization
import CalabiYau.Geometry.Kahler.Laplacian.Cofactor

/-!
# Kähler and Riemannian volume measures

For the convention `ω = i ∑ gⱼₖ̄ dzⱼ ∧ dżₖ`, the Kähler measure `ωⁿ / n!` has local density
`2ⁿ det(g)` with respect to Lebesgue measure on `ℂⁿ ≃ ℝ²ⁿ`. In the canonical real orthonormal frame,
the metric associated by `g_R(u,v) = ω(u,Jv)` has Gram determinant `2^(2n) |det(g)|²`. The
`chartModelBasis` used by the Riemannian measure need not be orthonormal: its Jacobian `J` contributes
`J²` to the Gram determinant and `J⁻¹` to `modelHaar`, so these factors cancel in the local measure.
In particular, for `n = 1` and the flat form `i dz ∧ dż = 2 dx ∧ dy`, both canonical densities are
`2`, not `1` or `1/2`.

The measure construction in the extracted Riemannian API is explicitly indexed by a smooth
partition of unity. Accordingly, the comparison below uses the same partition on both sides. The
subordination hypothesis is necessary to identify the Kähler gluing with its local chart measures;
no compactness is required beyond the `T2Space` and `SigmaCompactSpace` hypotheses needed to obtain
an atlas-subordinate smooth partition.
-/

@[expose] public section

open scoped Manifold ContDiff ComplexOrder

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

local instance : MeasurableSpace M := borel M
local instance : BorelSpace M := ⟨rfl⟩

private lemma linearMapAt_symmL_eq_tangentCoordChange
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
        (CalabiYau.Tensor.Coordinates.chartModelBasis (EuclideanSpace ℂ (Fin n)) i) := by
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
        (CalabiYau.Tensor.Coordinates.chartModelBasis (EuclideanSpace ℂ (Fin n)) i)) = _
  rw [CalabiYau.tangentSpaceModelContinuousLinearEquiv_apply]
  calc
    _ = (ContinuousLinearMap.id ℝ (EuclideanSpace ℂ (Fin n)))
        ((trivializationAt (EuclideanSpace ℂ (Fin n))
          (TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x).symmL ℝ y
          (CalabiYau.Tensor.Coordinates.chartModelBasis (EuclideanSpace ℂ (Fin n)) i)) := rfl
    _ = (trivializationAt (EuclideanSpace ℂ (Fin n))
        (TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) y).continuousLinearMapAt ℝ y
          ((trivializationAt (EuclideanSpace ℂ (Fin n))
            (TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x).symmL ℝ y
            (CalabiYau.Tensor.Coordinates.chartModelBasis (EuclideanSpace ℂ (Fin n)) i)) := by
      rw [hycenter]
      rfl
    _ = tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y
          (CalabiYau.Tensor.Coordinates.chartModelBasis (EuclideanSpace ℂ (Fin n)) i) :=
      DFunLike.congr_fun hcomp (CalabiYau.Tensor.Coordinates.chartModelBasis
        (EuclideanSpace ℂ (Fin n)) i)

private noncomputable def chartModelBasisJacobian (n : ℕ) : ℝ :=
  let b := CalabiYau.Tensor.Coordinates.chartModelBasis
    (EuclideanSpace ℂ (Fin n))
  Real.sqrt (Matrix.det (Matrix.of fun i j => Inner.inner ℝ (b i) (b j)))

/-- The chart Gram determinant has the squared Jacobian of `chartModelBasis` relative to the
canonical real orthonormal frame. -/
private theorem chartGramMatrix_det_eq_jacobian_sq_mul_two_pow_mul_normSq_det
    (ω₀ : KahlerForm n M) (x : M) {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    (CalabiYau.Tensor.Coordinates.chartGramMatrix
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) ω₀.toRiemannianMetric x
      ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z)).det =
      (chartModelBasisJacobian n) ^ 2 * (2 : ℝ) ^ (2 * n) *
        Complex.normSq ((ω₀.metricInChart x z).det) := by
  classical
  let E := EuclideanSpace ℂ (Fin n)
  let b := CalabiYau.Tensor.Coordinates.chartModelBasis E
  let y := (extChartAt 𝓘(ℝ, E) x).symm z
  have hyx : y ∈ (chartAt E x).source := by
    simpa only [extChartAt_source] using
      (extChartAt 𝓘(ℝ, E) x).map_target hz
  have hyy : y ∈ (extChartAt 𝓘(ℝ, E) y).source := mem_extChartAt_source y
  have hchange (v : E) :
      tangentCoordChange 𝓘(ℝ, E) x y y (EuclideanSpace.complexStructure n v) =
        EuclideanSpace.complexStructure n (tangentCoordChange 𝓘(ℝ, E) x y y v) := by
    exact tangentCoordChange_I_smul (x := x) (y := y) (z := y)
      ⟨(by simpa only [extChartAt_source] using hyx), hyy⟩ v
  have hmatrix :
      CalabiYau.Tensor.Coordinates.chartGramMatrix
        (I := 𝓘(ℝ, E)) ω₀.toRiemannianMetric x y =
        Matrix.of (fun (i j : Fin (Module.finrank ℝ E)) =>
          (ω₀.toFormField.chartRep x z)
            ![b i, EuclideanSpace.complexStructure n (b j)]) := by
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
  have hα : (ω₀.toFormField.chartRep x z).IsPositive :=
    ContinuousAlternatingMap.isPositive_iff.mpr
      ⟨ω₀.chartRep_isOneOne x hz, ω₀.posDef_metricInChart x hz⟩
  rw [hmatrix, CalabiYau.RiemannianVolume.gramDet_chartModelBasis n _ hα]
  have hJreal :
      (CalabiYau.RiemannianVolume.complexChartBasisVolume n).toReal =
        chartModelBasisJacobian n :=
    CalabiYau.RiemannianVolume.complexChartBasisVolume_toReal_eq_sqrt_gram n
  rw [hJreal]
  rfl

private theorem chartDensity_eq_jacobian_mul_volumeDensityInChart (ω₀ : KahlerForm n M)
    (x : M) {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    CalabiYau.RiemannianVolume.chartDensity
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) ω₀.toRiemannianMetric x
        ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z) =
      chartModelBasisJacobian n * ω₀.volumeDensityInChart x z := by
  have hdetReal : (ω₀.metricInChart x z).det.im = 0 := by
    have hstar : star (ω₀.metricInChart x z).det = (ω₀.metricInChart x z).det := by
      calc
        star (ω₀.metricInChart x z).det = (Matrix.conjTranspose (ω₀.metricInChart x z)).det :=
          (Matrix.det_conjTranspose (ω₀.metricInChart x z)).symm
        _ = (ω₀.metricInChart x z).det :=
          congrArg Matrix.det (ω₀.posDef_metricInChart x hz).isHermitian.eq
    have him := congrArg Complex.im hstar
    have him' : -(ω₀.metricInChart x z).det.im = (ω₀.metricInChart x z).det.im := by
      simpa using him
    linarith
  have hdetPos : 0 < RCLike.re (ω₀.metricInChart x z).det := by
    have hpos := (ω₀.posDef_metricInChart x hz).det_pos
    exact (RCLike.pos_iff.mp hpos).1
  have hJnonneg : 0 ≤ chartModelBasisJacobian n := Real.sqrt_nonneg _
  rw [CalabiYau.RiemannianVolume.chartDensity,
    chartGramMatrix_det_eq_jacobian_sq_mul_two_pow_mul_normSq_det ω₀ x hz,
    volumeDensityInChart, Complex.normSq_apply, hdetReal]
  ring_nf
  have hpow : (2 : ℝ) ^ (n * 2) = ((2 : ℝ) ^ n) ^ 2 := by
    rw [pow_mul]
  calc
    Real.sqrt ((chartModelBasisJacobian n) ^ 2 *
        (RCLike.re (ω₀.metricInChart x z).det) ^ 2 * (2 : ℝ) ^ (n * 2)) =
      Real.sqrt ((chartModelBasisJacobian n *
        RCLike.re (ω₀.metricInChart x z).det * (2 : ℝ) ^ n) ^ 2) := by
          congr 1
          rw [hpow]
          ring
    _ = |chartModelBasisJacobian n * RCLike.re (ω₀.metricInChart x z).det *
        (2 : ℝ) ^ n| := Real.sqrt_sq_eq_abs _
    _ = chartModelBasisJacobian n * RCLike.re (ω₀.metricInChart x z).det *
        (2 : ℝ) ^ n := by
          rw [abs_of_nonneg (mul_nonneg
            (mul_nonneg hJnonneg (le_of_lt hdetPos)) (by positivity))]

open MeasureTheory

/-- The canonical inner-product volume is independent of which *equal* Borel instance is used.
This is a transport of the measurable-space argument, not a comparison of two Haar normalizations. -/
private theorem innerProductMeasureSpace_eq_of_measurableSpace_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (m₁ m₂ : MeasurableSpace E)
    (h₁ : @BorelSpace E _ m₁) (h₂ : @BorelSpace E _ m₂)
    (hm : m₁ = m₂) :
    (@measureSpaceOfInnerProductSpace E _ _ _ m₁ h₁) =
      (@measureSpaceOfInnerProductSpace E _ _ _ m₂ h₂) := by
  subst m₂
  rfl

noncomputable local instance : MeasurableSpace (EuclideanSpace ℂ (Fin n)) := borel _
local instance : BorelSpace (EuclideanSpace ℂ (Fin n)) := ⟨rfl⟩

private theorem map_withDensity_of_leftInverse
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : α → β) (g : β → α) (hf : Measurable f) (hg : Measurable g)
    (hgf : ∀ x, g (f x) = x) (μ : Measure α) (p : α → ENNReal)
    (hp : Measurable p) :
    Measure.map f (μ.withDensity p) =
      (Measure.map f μ).withDensity (p ∘ g) := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hs.preimage hf),
    withDensity_apply _ hs,
    MeasureTheory.setLIntegral_map hs (hp.comp hg) hf]
  exact MeasureTheory.setLIntegral_congr_fun (hs.preimage hf) (by
    intro y hy
    simp [hgf y])

private theorem map_restrict_withDensity_of_leftInverse
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : α → β) (g : β → α) (hf : Measurable f) (hg : Measurable g)
    (hgf : ∀ x, g (f x) = x) (μ : Measure α) (K : Set α)
    (hK : MeasurableSet K) (p : α → ENNReal)
    (hpK : Measurable (K.indicator p)) :
    Measure.map f ((μ.restrict K).withDensity p) =
      (Measure.map f μ).withDensity (K.indicator p ∘ g) := by
  rw [← withDensity_indicator hK p]
  exact map_withDensity_of_leftInverse f g hf hg hgf μ _ hpK

/-- Compare chart-source weighted measures after pushing both across an injective coordinate map.
The scalar `q` may account for a non-orthonormal model Haar measure; it cancels against the density. -/
private theorem map_restricted_density_eq_of_ratio
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : α → β) (g : β → α) (hf : Measurable f) (hg : Measurable g)
    (hgf : ∀ x, g (f x) = x) (μ ν : Measure α) (rho : Measure β)
    (K : Set α) (hK : MeasurableSet K) (q : ENNReal)
    (hμ : Measure.map f μ = q • rho) (hν : Measure.map f ν = rho)
    (p r : α → ENNReal)
    (hpK : Measurable (K.indicator p)) (hrK : Measurable (K.indicator r))
    (hpoint : ∀ x ∈ K, r x = q * p x) :
    Measure.map f ((μ.restrict K).withDensity p) =
      Measure.map f ((ν.restrict K).withDensity r) := by
  rw [map_restrict_withDensity_of_leftInverse f g hf hg hgf μ K hK p hpK,
    map_restrict_withDensity_of_leftInverse f g hf hg hgf ν K hK r hrK, hμ, hν,
    withDensity_smul_measure]
  have hdensity : K.indicator r ∘ g = q • (K.indicator p ∘ g) := by
    funext y
    by_cases hy : g y ∈ K
    · simp [hy, hpoint _ hy, smul_eq_mul]
    · simp [hy, smul_eq_mul]
  rw [hdensity, withDensity_smul q (hpK.comp hg)]

/-- Compare the two restricted weighted measures after both are transported to canonical real
Euclidean coordinates. The chart-model Jacobian occurs in complex volume and in metric density,
so it cancels before transporting the measures back to the manifold. -/
private theorem chartSources_map_toEuclidean_eq (ω₀ : KahlerForm n M) (x : M)
    (J : ℝ) (hJ : 0 < J)
    (hJvol : Measure.map (toEuclidean (E := EuclideanSpace ℂ (Fin n)))
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) =
        ENNReal.ofReal J •
          (MeasureTheory.volume : Measure (EuclideanSpace ℝ
            (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))))
    (hden : ∀ z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target,
      CalabiYau.RiemannianVolume.chartDensity
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) ω₀.toRiemannianMetric x
          ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z) =
        J * ω₀.volumeDensityInChart x z)
    (hpK : Measurable ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target.indicator
      (fun z => ENNReal.ofReal (ω₀.volumeDensityInChart x z))))
    (hrK : Measurable ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target.indicator
      (fun z => ENNReal.ofReal (CalabiYau.RiemannianVolume.chartDensity
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) ω₀.toRiemannianMetric x
        ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z))))) :
    Measure.map (toEuclidean (E := EuclideanSpace ℂ (Fin n)))
      (((MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))).restrict
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target).withDensity
        (fun z => ENNReal.ofReal (ω₀.volumeDensityInChart x z))) =
    Measure.map (toEuclidean (E := EuclideanSpace ℂ (Fin n)))
      (((CalabiYau.RiemannianVolume.modelHaar
          (E := EuclideanSpace ℂ (Fin n))).restrict
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target).withDensity
        (fun z => ENNReal.ofReal (CalabiYau.RiemannianVolume.chartDensity
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) ω₀.toRiemannianMetric x
          ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z)))) := by
  let K := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target
  let p : EuclideanSpace ℂ (Fin n) → ENNReal :=
    fun z => ENNReal.ofReal (ω₀.volumeDensityInChart x z)
  let r : EuclideanSpace ℂ (Fin n) → ENNReal :=
    fun z => ENNReal.ofReal (CalabiYau.RiemannianVolume.chartDensity
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) ω₀.toRiemannianMetric x
      ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z))
  have hK : MeasurableSet K := (isOpen_extChartAt_target x).measurableSet
  have hpoint : ∀ z ∈ K, r z = ENNReal.ofReal J * p z := by
    intro z hz
    change ENNReal.ofReal
        (CalabiYau.RiemannianVolume.chartDensity
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) ω₀.toRiemannianMetric x
          ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z)) = _
    rw [hden z hz, ENNReal.ofReal_mul (le_of_lt hJ)]
  exact map_restricted_density_eq_of_ratio
    (toEuclidean (E := EuclideanSpace ℂ (Fin n)))
    (toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm
    (toEuclidean (E := EuclideanSpace ℂ (Fin n))).continuous.measurable
    (toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm.continuous.measurable
    (fun z => (toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm_apply_apply z)
    (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n)))
    (CalabiYau.RiemannianVolume.modelHaar (E := EuclideanSpace ℂ (Fin n)))
    (MeasureTheory.volume : Measure (EuclideanSpace ℝ
      (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))))))
    K hK (ENNReal.ofReal J) hJvol
    (CalabiYau.RiemannianVolume.map_toEuclidean_modelHaar_eq_volume
      (E := EuclideanSpace ℂ (Fin n)))
    p r hpK hrK hpoint

private theorem chartVolume_eq_chartLocalMeasure (ω₀ : KahlerForm n M) (x : M) :
    ω₀.chartVolume x = CalabiYau.RiemannianVolume.chartLocalMeasure
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) ω₀.toRiemannianMetric x := by
  classical
  let K := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target
  have hK : MeasurableSet K := (isOpen_extChartAt_target x).measurableSet
  have hpcont : ContinuousOn
      (fun z : EuclideanSpace ℂ (Fin n) => ENNReal.ofReal (ω₀.volumeDensityInChart x z))
      K := by
    have hdet : ContinuousOn (fun z => (ω₀.metricInChart x z).det) K := by
      simp_rw [Matrix.det_apply]
      exact continuousOn_finsetSum Finset.univ fun σ _ =>
        continuousOn_const.smul <| continuousOn_finsetProd Finset.univ fun i _ =>
          (ω₀.contDiffOn_metricInChart x (σ i) i).continuousOn
    have hreal : ContinuousOn (ω₀.volumeDensityInChart x) K := by
      change ContinuousOn (fun z => (2 : ℝ) ^ n * (ω₀.metricInChart x z).det.re) K
      exact continuousOn_const.mul
        (Complex.continuous_re.continuousOn.comp hdet (fun _ _ => Set.mem_univ _))
    exact ENNReal.continuous_ofReal.continuousOn.comp hreal
      (fun _ _ => Set.mem_univ _)
  have hrcont : ContinuousOn
      (fun z : EuclideanSpace ℂ (Fin n) => ENNReal.ofReal
        (CalabiYau.RiemannianVolume.chartDensity
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) ω₀.toRiemannianMetric x
          ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z))) K := by
    exact ENNReal.continuous_ofReal.continuousOn.comp
      (CalabiYau.RiemannianVolume.chartDensityOnE_contDiffOn
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) ω₀.toRiemannianMetric x).continuousOn
      (fun _ _ => Set.mem_univ _)
  have hpK : Measurable (K.indicator
      (fun z : EuclideanSpace ℂ (Fin n) => ENNReal.ofReal (ω₀.volumeDensityInChart x z))) := by
    have heq : K.indicator
        (fun z : EuclideanSpace ℂ (Fin n) => ENNReal.ofReal (ω₀.volumeDensityInChart x z)) =
        K.piecewise (fun z => ENNReal.ofReal (ω₀.volumeDensityInChart x z))
          (fun _ => (0 : ENNReal)) := by
      funext z
      by_cases hz : z ∈ K <;> simp [Set.indicator, Set.piecewise, hz]
    rw [heq]
    exact ContinuousOn.measurable_piecewise hpcont continuousOn_const hK
  have hrK : Measurable (K.indicator
      (fun z : EuclideanSpace ℂ (Fin n) => ENNReal.ofReal
        (CalabiYau.RiemannianVolume.chartDensity
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) ω₀.toRiemannianMetric x
          ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z)))) := by
    have heq : K.indicator
        (fun z : EuclideanSpace ℂ (Fin n) => ENNReal.ofReal
          (CalabiYau.RiemannianVolume.chartDensity
            (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) ω₀.toRiemannianMetric x
            ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z))) =
        K.piecewise (fun z => ENNReal.ofReal (CalabiYau.RiemannianVolume.chartDensity
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) ω₀.toRiemannianMetric x
          ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z)))
          (fun _ => (0 : ENNReal)) := by
      funext z
      by_cases hz : z ∈ K <;> simp [Set.indicator, Set.piecewise, hz]
    rw [heq]
    exact ContinuousOn.measurable_piecewise hrcont continuousOn_const hK
  have hJ : 0 < chartModelBasisJacobian n := by
    rw [chartModelBasisJacobian,
      ← CalabiYau.RiemannianVolume.complexChartBasisVolume_toReal_eq_sqrt_gram]
    exact ENNReal.toReal_pos_iff.mpr
      ⟨CalabiYau.RiemannianVolume.complexChartBasisVolume_pos n,
        CalabiYau.RiemannianVolume.complexChartBasisVolume_lt_top n⟩
  have hJvol : Measure.map (toEuclidean (E := EuclideanSpace ℂ (Fin n)))
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) =
      ENNReal.ofReal (chartModelBasisJacobian n) •
        (MeasureTheory.volume : Measure (EuclideanSpace ℝ
          (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))) := by
    rw [chartModelBasisJacobian,
      ← CalabiYau.RiemannianVolume.complexChartBasisVolume_toReal_eq_sqrt_gram,
      ENNReal.ofReal_toReal
        (CalabiYau.RiemannianVolume.complexChartBasisVolume_lt_top n).ne]
    have hcanonical : (borel (EuclideanSpace ℂ (Fin n))) =
        (WithLp.measurableSpace 2 (Fin n → ℂ)) :=
      (PiLp.borelSpace (p := 2) (X := fun _ : Fin n => ℂ)).measurable_eq.symm
    convert CalabiYau.RiemannianVolume.map_toEuclidean_complexVolume_eq_chartBasisVolume_smul_volume n
      using 1
    congr 1
    congr 1
    exact innerProductMeasureSpace_eq_of_measurableSpace_eq
      (WithLp.measurableSpace 2 (Fin n → ℂ))
      (borel (EuclideanSpace ℂ (Fin n)))
      (PiLp.borelSpace (p := 2) (X := fun _ : Fin n => ℂ))
      ⟨rfl⟩ hcanonical.symm |>.symm
  have hSources := chartSources_map_toEuclidean_eq ω₀ x (chartModelBasisJacobian n)
    hJ hJvol (fun z hz => chartDensity_eq_jacobian_mul_volumeDensityInChart ω₀ x hz)
    hpK hrK
  have hsourceEq :
      ((MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))).restrict K).withDensity
        (fun z => ENNReal.ofReal (ω₀.volumeDensityInChart x z)) =
      ((CalabiYau.RiemannianVolume.modelHaar
        (E := EuclideanSpace ℂ (Fin n))).restrict K).withDensity
        (fun z => ENNReal.ofReal (CalabiYau.RiemannianVolume.chartDensity
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) ω₀.toRiemannianMetric x
          ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z))) := by
    have h := congrArg
      (Measure.map (toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm) hSources
    dsimp only [K]
    simpa [Measure.map_map
      (toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm.continuous.measurable
      (toEuclidean (E := EuclideanSpace ℂ (Fin n))).continuous.measurable] using h
  have hcanonical : (borel (EuclideanSpace ℂ (Fin n))) =
      (WithLp.measurableSpace 2 (Fin n → ℂ)) :=
    (PiLp.borelSpace (p := 2) (X := fun _ : Fin n => ℂ)).measurable_eq.symm
  rw [chartVolume, CalabiYau.RiemannianVolume.chartLocalMeasure_def]
  convert congrArg (Measure.map (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
    hsourceEq using 1
  dsimp only [K]
  congr 1
  · change (WithLp.measurableSpace 2 (Fin n → ℂ)) =
        borel (EuclideanSpace ℂ (Fin n))
    exact hcanonical.symm
  · congr 1
    · exact hcanonical.symm
    · congr 1
      · change (WithLp.measurableSpace 2 (Fin n → ℂ)) =
            borel (EuclideanSpace ℂ (Fin n))
        exact hcanonical.symm
      · congr 1
        exact innerProductMeasureSpace_eq_of_measurableSpace_eq
          (WithLp.measurableSpace 2 (Fin n → ℂ))
          (borel (EuclideanSpace ℂ (Fin n)))
          (PiLp.borelSpace (p := 2) (X := fun _ : Fin n => ℂ))
          ⟨rfl⟩ hcanonical.symm

section

variable [T2Space M] [SigmaCompactSpace M]

/-- The Kähler measure `ω₀ⁿ / n!` agrees with the measure of the associated Riemannian metric,
when both are assembled using the same smooth partition of unity subordinate to chart domains.

This formulation makes the choice of partition explicit: the extracted Riemannian measure is
`CalabiYau.RiemannianVolume.riemannianMeasure I g ρ`, rather than a measure independent of `ρ`.
-/
theorem volume_eq_riemannianMeasure (ω₀ : KahlerForm n M)
    (ρ : SmoothPartitionOfUnity M 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M Set.univ)
    (hρ : ρ.IsSubordinate fun x ↦ (chartAt (EuclideanSpace ℂ (Fin n)) x).source) :
    ω₀.volume = CalabiYau.RiemannianVolume.riemannianMeasure
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) ω₀.toRiemannianMetric ρ := by
  rw [ω₀.volume_eq_sum_of_isSubordinate ρ hρ,
    CalabiYau.RiemannianVolume.riemannianMeasure_def]
  congr 1
  funext x
  rw [chartVolume_eq_chartLocalMeasure ω₀ x]

/-- The Kähler measure agrees with the Riemannian measure using the canonical chart-atlas
partition of unity. This is the form that can be applied without choosing a new partition. -/
theorem volume_eq_riemannianMeasure_chartAtlasPOU (ω₀ : KahlerForm n M) :
    ω₀.volume = CalabiYau.RiemannianVolume.riemannianMeasure
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) ω₀.toRiemannianMetric
      (CalabiYau.RiemannianVolume.chartAtlasPOU
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) M) := by
  exact volume_eq_riemannianMeasure ω₀ _
    (CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) M)

/-- The Kähler measure is the canonical Riemannian volume measure. The equality follows from
`riemannianVolumeMeasure_def`, which is definitional after expanding the atlas partition. -/
theorem volume_eq_riemannianVolumeMeasure (ω₀ : KahlerForm n M) :
    ω₀.volume = CalabiYau.RiemannianVolume.riemannianVolumeMeasure
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) ω₀.toRiemannianMetric := by
  rw [CalabiYau.RiemannianVolume.riemannianVolumeMeasure_def]
  exact volume_eq_riemannianMeasure_chartAtlasPOU ω₀

end

end KahlerForm
