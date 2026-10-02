module

public import CalabiYau.Geometry.Kahler.Basic
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import CalabiYau.Mathlib.LinearAlgebra.Matrix.Realification
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# The volume form `ωⁿ / n!`

The volume measure of a Kähler form is the measure with density `ωⁿ / n!` with respect to the
complex orientation. In the chart at `x` this is `2ⁿ det(g_{jk̄}) dλ`, where `dλ` is Lebesgue
measure on `ℂⁿ ≅ ℝ²ⁿ` (`volume` on `EuclideanSpace ℂ (Fin n)`, for which the real orthonormal
basis `eⱼ, i eⱼ` spans a unit cube) and `ω = i ∑ g_{jk̄} dzⱼ ∧ dz̄ₖ`: indeed
`(i ∑ⱼ dzⱼ ∧ dz̄ⱼ)ⁿ / n! = 2ⁿ dx₁ ∧ dy₁ ∧ ⋯ ∧ dxₙ ∧ dyₙ`. It is also the Riemannian volume of
`g(u, v) = ω(u, Jv)`.

`KahlerForm.volume` assembles the chart measures `KahlerForm.chartVolume` with a smooth partition of
unity subordinate to the charts. The choice of partition is irrelevant
(`volume_eq_sum_of_isSubordinate`), and the measure has the expected local expression
(`volume_apply_of_subset_source`).

Since only ratios of volumes enter the main theorems (the normalization
`∫ e^F ωⁿ = ∫ ωⁿ` is scale invariant), the constant `2ⁿ / n!` is immaterial there; it is kept so
that `ω.volume` is literally the Riemannian volume measure.
-/

@[expose] public section

open scoped Manifold ContDiff ENNReal
open Set MeasureTheory ContinuousAlternatingMap Filter

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M] [BorelSpace M]
  (ω₀ : KahlerForm n M)

/-- The density `2ⁿ det(g_{jk̄})` of `ω₀ⁿ / n!` with respect to Lebesgue measure, in the chart at
`x`. -/
noncomputable def volumeDensityInChart (x : M) (z : EuclideanSpace ℂ (Fin n)) : ℝ :=
  2 ^ n * RCLike.re (ω₀.metricInChart x z).det

/-- The measure `ω₀ⁿ / n!` on the domain of the chart at `x`, transported to `M`. -/
noncomputable def chartVolume (x : M) : Measure M :=
  (((MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))).restrict
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target).withDensity
    fun z ↦ ENNReal.ofReal (ω₀.volumeDensityInChart x z)).map
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm

/-- The volume measure `ω₀ⁿ / n!` of a Kähler form, assembled from the chart measures with a smooth
partition of unity subordinate to the chart domains. -/
noncomputable def volume [T2Space M] [SigmaCompactSpace M] : Measure M :=
  Measure.sum fun x : M ↦ (ω₀.chartVolume x).withDensity fun y ↦ ENNReal.ofReal
    ((SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M).choose x y)

variable [T2Space M] [SigmaCompactSpace M]

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M] in
private theorem volumeDensityInChart_continuousOn (x : M) :
    ContinuousOn (ω₀.volumeDensityInChart x)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
  change ContinuousOn
    (fun z ↦ (2 : ℝ) ^ n * (ω₀.metricInChart x z).det.re)
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target
  have hdet : ContinuousOn (fun z ↦ (ω₀.metricInChart x z).det)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
    classical
    simp_rw [Matrix.det_apply]
    exact continuousOn_finsetSum Finset.univ fun σ _ ↦
      continuousOn_const.smul <| continuousOn_finsetProd Finset.univ fun i _ ↦
        (ω₀.contDiffOn_metricInChart x (σ i) i).continuousOn
  have hre : ContinuousOn (fun z ↦ (ω₀.metricInChart x z).det.re)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
    exact Complex.continuous_re.continuousOn.comp hdet (fun _ _ ↦ Set.mem_univ _)
  exact continuousOn_const.mul hre

omit [T2Space M] [SigmaCompactSpace M] in
private theorem chartVolume_apply_of_measurable_subset_source (x : M) {A : Set M}
    (hA : MeasurableSet A)
    (hAx : A ⊆ (chartAt (EuclideanSpace ℂ (Fin n)) x).source) :
    ω₀.chartVolume x A =
      ∫⁻ z in extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x '' A,
        ENNReal.ofReal (ω₀.volumeDensityInChart x z) := by
  classical
  let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let D := c '' A
  have hAx' : A ⊆ c.source := by
    rw [extChartAt_source]
    exact hAx
  have hsymm : AEMeasurable c.symm (MeasureTheory.volume.restrict c.target) := by
    exact (continuousOn_extChartAt_symm x).aemeasurable
      (isOpen_extChartAt_target x).measurableSet
  let d : EuclideanSpace ℂ (Fin n) → ℝ≥0∞ :=
    fun z ↦ ENNReal.ofReal (ω₀.volumeDensityInChart x z)
  have hsymm' : AEMeasurable c.symm
      ((MeasureTheory.volume.restrict c.target).withDensity d) := by
    exact hsymm.mono_ac (withDensity_absolutelyContinuous _ _)
  have hpre : NullMeasurableSet (c.symm ⁻¹' A)
      (MeasureTheory.volume.restrict c.target) :=
    hsymm.nullMeasurableSet_preimage hA
  have hpreEq : c.symm ⁻¹' A ∩ c.target = D := by
    ext z
    constructor
    · rintro ⟨hzA, hzT⟩
      exact ⟨c.symm z, hzA, c.right_inv hzT⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨?_, c.map_source (hAx' hy)⟩
      change c.symm (c y) ∈ A
      rw [c.left_inv (hAx' hy)]
      exact hy
  rw [chartVolume, Measure.map_apply_of_aemeasurable hsymm' hA,
    withDensity_apply₀ d hpre]
  calc
    ∫⁻ z in c.symm ⁻¹' A, d z ∂MeasureTheory.volume.restrict c.target =
        ∫⁻ z in c.symm ⁻¹' A ∩ c.target, d z ∂MeasureTheory.volume := by
      rw [Measure.restrict_restrict₀ hpre]
    _ = ∫⁻ z in D, d z ∂MeasureTheory.volume := by rw [hpreEq]

omit [T2Space M] [SigmaCompactSpace M] in
private theorem chartVolume_lintegral (x : M) {f : M → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂ω₀.chartVolume x =
      ∫⁻ z in (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target,
        ENNReal.ofReal (ω₀.volumeDensityInChart x z) *
          f ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z)
          ∂MeasureTheory.volume := by
  let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let μ : Measure (EuclideanSpace ℂ (Fin n)) :=
    (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))).restrict c.target
  let d : EuclideanSpace ℂ (Fin n) → ℝ≥0∞ :=
    fun z ↦ ENNReal.ofReal (ω₀.volumeDensityInChart x z)
  have hsymm : AEMeasurable c.symm μ := by
    exact (continuousOn_extChartAt_symm x).aemeasurable
      (isOpen_extChartAt_target x).measurableSet
  have hdcont : ContinuousOn d c.target := by
    exact ENNReal.continuous_ofReal.continuousOn.comp
      (ω₀.volumeDensityInChart_continuousOn x) (fun _ _ ↦ Set.mem_univ _)
  have hd : AEMeasurable d μ := hdcont.aemeasurable (isOpen_extChartAt_target x).measurableSet
  have hsymm' : AEMeasurable c.symm (μ.withDensity d) :=
    hsymm.mono_ac (withDensity_absolutelyContinuous μ d)
  have hfg : AEMeasurable (fun z ↦ f (c.symm z)) μ :=
    (hf.aemeasurable : AEMeasurable f (μ.map c.symm)).comp_aemeasurable hsymm
  calc
    ∫⁻ y, f y ∂ω₀.chartVolume x = ∫⁻ z, f (c.symm z) ∂μ.withDensity d := by
      rw [chartVolume, MeasureTheory.lintegral_map' hf.aemeasurable
        hsymm']
    _ = ∫⁻ z, d z * f (c.symm z) ∂μ :=
      MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀ hd hfg
    _ = ∫⁻ z in c.target, d z * f (c.symm z) ∂MeasureTheory.volume := rfl

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] in
private theorem extChartAt_image_measurableSet_of_open_subset_source
    (x₀ : M) {U : Set M} (hUopen : IsOpen U)
    (hUsub : U ⊆ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source) :
    MeasurableSet
      ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀) '' U) := by
  have hchart_image : IsOpen ((chartAt (EuclideanSpace ℂ (Fin n)) x₀) '' U) :=
    (chartAt (EuclideanSpace ℂ (Fin n)) x₀).isOpen_image_of_subset_source hUopen hUsub
  have himg_eq :
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀) '' U =
        (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) ''
          ((chartAt (EuclideanSpace ℂ (Fin n)) x₀) '' U) := by
    rw [extChartAt]
    simp only [OpenPartialHomeomorph.extend_coe]
    rw [image_comp]
  rw [himg_eq]
  exact (𝓘(ℝ, EuclideanSpace ℂ (Fin n))).isClosedEmbedding.measurableEmbedding.measurableSet_image.mpr
    hchart_image.measurableSet

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] in
private theorem extChartAt_transition_image
    (x₀ x₁ : M) {U : Set M}
    (hUsub₀ : U ⊆ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source) :
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁ ∘
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm) ''
        ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀) '' U) =
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁) '' U := by
  rw [← Set.image_comp]
  refine Set.image_congr ?_
  intro x hx
  have hxsrc₀ : x ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).source := by
    rw [extChartAt_source]
    exact hUsub₀ hx
  change extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁
    ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ x)) = _
  rw [(extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).left_inv hxsrc₀]

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] in
private theorem extChartAt_transition_injOn_overlap_image
    (x₀ x₁ : M) {U : Set M}
    (hUsub₀ : U ⊆ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source)
    (hUsub₁ : U ⊆ (chartAt (EuclideanSpace ℂ (Fin n)) x₁).source) :
    Set.InjOn
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁ ∘
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm)
      ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀) '' U) := by
  intro y hy z hz hyz
  obtain ⟨a, haU, rfl⟩ := hy
  obtain ⟨b, hbU, rfl⟩ := hz
  have haSrc₀ : a ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).source := by
    rw [extChartAt_source]
    exact hUsub₀ haU
  have hbSrc₀ : b ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).source := by
    rw [extChartAt_source]
    exact hUsub₀ hbU
  have haSrc₁ : a ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁).source := by
    rw [extChartAt_source]
    exact hUsub₁ haU
  have hbSrc₁ : b ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁).source := by
    rw [extChartAt_source]
    exact hUsub₁ hbU
  simp only [Function.comp_apply,
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).left_inv haSrc₀,
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).left_inv hbSrc₀] at hyz
  have hab : a = b :=
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁).injOn haSrc₁ hbSrc₁ hyz
  subst b
  rfl

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M] in
private theorem extChartAt_transition_hasFDerivWithinAt_on_overlap_image
    (x₀ x₁ : M) {U : Set M}
    (hUsub₀ : U ⊆ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source)
    (hUsub₁ : U ⊆ (chartAt (EuclideanSpace ℂ (Fin n)) x₁).source) :
    ∀ y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀) '' U,
      HasFDerivWithinAt
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁ ∘
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm)
        (tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ x₁
          ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm y))
        ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀) '' U) y := by
  intro y hy
  obtain ⟨x, hxU, rfl⟩ := hy
  have hxSrc₀ : x ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).source := by
    rw [extChartAt_source]
    exact hUsub₀ hxU
  have hxSrc₁ : x ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁).source := by
    rw [extChartAt_source]
    exact hUsub₁ hxU
  have hfull := hasFDerivWithinAt_tangentCoordChange
    (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (x := x₀) (y := x₁) (z := x)
    ⟨hxSrc₀, hxSrc₁⟩
  have himage_sub :
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀) '' U ⊆
        Set.range (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) := by
    intro y' hy'
    obtain ⟨z, hzU, rfl⟩ := hy'
    have hzSrc₀ : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).source := by
      rw [extChartAt_source]
      exact hUsub₀ hzU
    exact extChartAt_target_subset_range (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x₀
      ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).map_source hzSrc₀)
  have hsymm :
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ x) = x :=
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).left_inv hxSrc₀
  rw [hsymm]
  exact hfull.mono himage_sub

omit [T2Space M] [SigmaCompactSpace M] in
private theorem chartVolume_lintegral_U_eq_image (x : M)
    {U : Set M} (hUopen : IsOpen U)
    (hUsub : U ⊆ (chartAt (EuclideanSpace ℂ (Fin n)) x).source)
    {F : M → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ y in U, F y ∂ω₀.chartVolume x =
      ∫⁻ z in (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x) '' U,
        ENNReal.ofReal (ω₀.volumeDensityInChart x z) *
          F ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z)
          ∂MeasureTheory.volume := by
  let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let D := c '' U
  let d : EuclideanSpace ℂ (Fin n) → ℝ≥0∞ :=
    fun z ↦ ENNReal.ofReal (ω₀.volumeDensityInChart x z)
  have hUsub' : U ⊆ c.source := by
    rw [extChartAt_source]
    exact hUsub
  have hDmeas : MeasurableSet D := by
    dsimp [D, c]
    exact extChartAt_image_measurableSet_of_open_subset_source x hUopen hUsub
  have himg : D = c.target ∩ c.symm ⁻¹' U :=
    c.image_eq_target_inter_inv_preimage hUsub'
  have hDsub : D ⊆ c.target := by
    intro z hz
    rw [himg] at hz
    exact hz.1
  rw [← MeasureTheory.lintegral_indicator hUopen.measurableSet]
  rw [ω₀.chartVolume_lintegral x (hF.indicator hUopen.measurableSet)]
  have hpointwise : ∀ z ∈ c.target,
      d z * U.indicator F (c.symm z) =
        D.indicator (fun z ↦ d z * F (c.symm z)) z := by
    intro z hz
    by_cases hzU : c.symm z ∈ U
    · have hzD : z ∈ D := by
        rw [himg]
        exact ⟨hz, hzU⟩
      rw [Set.indicator_of_mem hzU, Set.indicator_of_mem hzD]
    · have hzD : z ∉ D := by
        rw [himg]
        exact fun h ↦ hzU h.2
      rw [Set.indicator_of_notMem hzU, Set.indicator_of_notMem hzD]
      simp
  rw [MeasureTheory.setLIntegral_congr_fun (isOpen_extChartAt_target x).measurableSet
    hpointwise]
  rw [MeasureTheory.setLIntegral_indicator hDmeas]
  rw [show D ∩ c.target = D from Set.inter_eq_left.mpr hDsub]

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M] in
private theorem chartRep_isOneOne_in_chart (x : M) {y : M}
    (hy : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source) :
    (ω₀.toFormField.chartRep x
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)).IsOneOne := by
  have hyxR : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source := by
    rw [extChartAt_source]
    exact hy
  have hyyR : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).source :=
    mem_extChartAt_source y
  have hyxC : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source := by
    simpa only [← extChartAt_real_eq] using hyxR
  have hyyC : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source := by
    simpa only [← extChartAt_real_eq] using hyyR
  let A := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y
  let B := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y x y
  have hBA : ∀ v, B (A v) = v := by
    intro v
    calc
      B (A v) = tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x x y v := by
        exact tangentCoordChange_comp (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
          (w := x) (x := y) (y := x) (z := y) (v := v)
          ⟨⟨hyxC, hyyC⟩, hyxC⟩
      _ = v := tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
        (x := x) (z := y) (v := v) hyxC
  have hAB : ∀ v, A (B v) = v := by
    intro v
    calc
      A (B v) = tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y y y v := by
        exact tangentCoordChange_comp (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
          (w := y) (x := x) (y := y) (z := y) (v := v)
          ⟨⟨hyyC, hyxC⟩, hyyC⟩
      _ = v := tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
        (x := y) (z := y) (v := v) hyyC
  let AEquiv : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n) := {
    toLinearEquiv := {
      toFun := A
      invFun := B
      left_inv := hBA
      right_inv := hAB
      map_add' := A.map_add
      map_smul' := A.map_smul }
    continuous_toFun := A.continuous
    continuous_invFun := B.continuous }
  have hrep := FormField.chartRep_eq_chartRep_comp (α := ω₀.toFormField)
    (x := x) (x' := y) (z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)
    ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).map_source hyxR)
    (by rw [(extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).left_inv hyxR]; exact hyyR)
  have hAreal : tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y =
      A.restrictScalars ℝ := tangentCoordChange_real_eq ⟨hyxR, hyyR⟩
  have hderiv : fderiv ℝ
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y ∘
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y) = A.restrictScalars ℝ := by
    have h := hAreal
    rw [tangentCoordChange_def, extChartAt_real_eq] at h
    simpa [ModelWithCorners.range_eq_univ, fderivWithin_univ] using h
  rw [hderiv] at hrep
  have hcenter : extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y
      ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)) =
      extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y := by
    rw [(extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).left_inv hyxR]
  rw [hcenter, FormField.chartRep_self] at hrep
  have hbase := (ω₀.isOneOne y).compContinuousLinearMap AEquiv
  have hAEquiv : (AEquiv : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) = A := by
    ext v
    rfl
  rw [hAEquiv] at hbase
  rw [← hrep] at hbase
  exact hbase

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M] in
private theorem metricInChart_transition_eq (x₀ x₁ : M) {y : M}
    (hy₀ : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source)
    (hy₁ : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₁).source) :
    ω₀.metricInChart x₀ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ y) =
      Matrix.transpose (EuclideanSpace.clmMatrix
        (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀ x₁ y)) *
        ω₀.metricInChart x₁ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁ y) *
        (EuclideanSpace.clmMatrix
          (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀ x₁ y)).map star := by
  let c₀ := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀
  let c₁ := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁
  let A := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀ x₁ y
  have hy₀' : y ∈ c₀.source := by
    rw [extChartAt_source]
    exact hy₀
  have hy₁' : y ∈ c₁.source := by
    rw [extChartAt_source]
    exact hy₁
  have hz₀ : c₀ y ∈ c₀.target := c₀.map_source hy₀'
  have hAreal : tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ x₁ y =
      A.restrictScalars ℝ := by
    exact tangentCoordChange_real_eq ⟨hy₀', hy₁'⟩
  have hderiv : fderiv ℝ (c₁ ∘ c₀.symm) (c₀ y) = A.restrictScalars ℝ := by
    have h := hAreal
    dsimp [A, c₀, c₁] at h ⊢
    rw [tangentCoordChange_def, extChartAt_real_eq] at h
    simpa [ModelWithCorners.range_eq_univ, fderivWithin_univ] using h
  have hrep := FormField.chartRep_eq_chartRep_comp (α := ω₀.toFormField)
    (x := x₀) (x' := x₁) (z := c₀ y) hz₀ (by rw [c₀.left_inv hy₀']; exact hy₁')
  rw [hderiv] at hrep
  have hcenter :
      extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁
          ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ y)) =
        extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁ y := by
    rw [(extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).left_inv hy₀']
  rw [hcenter] at hrep
  have hcoeff := congrArg (fun α : _ [⋀^Fin 2]→L[ℝ] ℝ => α.coeffMatrix) hrep
  rw [ContinuousAlternatingMap.IsOneOne.coeffMatrix_compContinuousLinearMap
    (chartRep_isOneOne_in_chart ω₀ x₁ hy₁) A] at hcoeff
  change (ω₀.toFormField.chartRep x₀
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ y)).coeffMatrix =
    (EuclideanSpace.clmMatrix A).transpose *
      (ω₀.toFormField.chartRep x₁
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁ y)).coeffMatrix *
      (EuclideanSpace.clmMatrix A).map star
  exact hcoeff

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M] in
private theorem volumeDensityInChart_transition_normSq (x₀ x₁ : M) {y : M}
    (hy₀ : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source)
    (hy₁ : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₁).source) :
    ω₀.volumeDensityInChart x₀
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ y) =
      Complex.normSq
          (EuclideanSpace.clmMatrix
            (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀ x₁ y)).det *
        ω₀.volumeDensityInChart x₁
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁ y) := by
  let A := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀ x₁ y
  let B := EuclideanSpace.clmMatrix A
  let G₀ := ω₀.metricInChart x₀ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ y)
  let G₁ := ω₀.metricInChart x₁ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁ y)
  have hmat := metricInChart_transition_eq ω₀ x₀ x₁ hy₀ hy₁
  have hmat' : G₀ = B.transpose * G₁ * B.map star := by
    simpa [A, B, G₀, G₁] using hmat
  have hmapdet : (B.map star).det = star B.det := by
    simpa [B] using ((starRingEnd ℂ).map_det (EuclideanSpace.clmMatrix A)).symm
  have hdet : G₀.det = (B.det * G₁.det) * star B.det := by
    calc
      G₀.det = (B.transpose * G₁ * B.map star).det := congrArg Matrix.det hmat'
      _ = (B.det * G₁.det) * star B.det := by
        rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hmapdet]
  have hdet' : G₀.det = (Complex.normSq B.det : ℂ) * G₁.det := by
    calc
      G₀.det = (B.det * G₁.det) * star B.det := hdet
      _ = (B.det * star B.det) * G₁.det := by
        ring
      _ = (Complex.normSq B.det : ℂ) * G₁.det := by
        exact congrArg (fun z : ℂ => z * G₁.det) (Complex.mul_conj B.det)
  have hre : G₀.det.re = Complex.normSq B.det * G₁.det.re := by
    have h := congrArg Complex.re hdet'
    simpa using h
  change 2 ^ n * G₀.det.re =
    Complex.normSq B.det * (2 ^ n * G₁.det.re)
  rw [hre]
  ring

private theorem clmMatrix_eq_toMatrix_basisFun
    (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace.clmMatrix A =
      LinearMap.toMatrix ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis)
        ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis) A.toLinearMap := by
  ext i j
  simp [EuclideanSpace.clmMatrix, LinearMap.toMatrix_apply]

private theorem clm_det_restrictScalars_eq_normSq
    (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
    (A.restrictScalars ℝ).det = Complex.normSq (EuclideanSpace.clmMatrix A).det := by
  let bC : Module.Basis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)) :=
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
  let bR := Complex.basisOneI.smulTower' bC
  have hclm : LinearMap.toMatrix bC bC A.toLinearMap = EuclideanSpace.clmMatrix A := by
    simpa [bC] using (clmMatrix_eq_toMatrix_basisFun (n := n) A).symm
  have hreal : LinearMap.toMatrix bR bR (A.toLinearMap.restrictScalars ℝ) =
      (EuclideanSpace.clmMatrix A).realify := by
    rw [LinearMap.restrictScalars_toMatrix]
    rw [hclm]
    ext ⟨i, a⟩ ⟨j, b⟩
    rw [Matrix.comp_apply, Matrix.realify_apply]
    simp only [Matrix.map_apply, Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply,
      Complex.coe_basisOneI, Complex.coe_basisOneI_repr, Algebra.coe_lmul_eq_mul,
      LinearMap.mul_apply']
    fin_cases a <;> fin_cases b <;> simp
  change (A.toLinearMap.restrictScalars ℝ).det = _
  calc
    (A.toLinearMap.restrictScalars ℝ).det =
        Matrix.det (LinearMap.toMatrix bR bR (A.toLinearMap.restrictScalars ℝ)) := by
      rw [LinearMap.det_toMatrix]
    _ = (EuclideanSpace.clmMatrix A).realify.det := congrArg Matrix.det hreal
    _ = Complex.normSq (EuclideanSpace.clmMatrix A).det := Matrix.det_realify _

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M] in
private theorem tangentCoordChange_det_eq_normSq (x₀ x₁ : M) {y : M}
    (hy₀ : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source)
    (hy₁ : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₁).source) :
    (tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ x₁ y).det =
      Complex.normSq
        (EuclideanSpace.clmMatrix
          (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀ x₁ y)).det := by
  have hy₀' : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).source := by
    rw [extChartAt_source]
    exact hy₀
  have hy₁' : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁).source := by
    rw [extChartAt_source]
    exact hy₁
  rw [tangentCoordChange_real_eq ⟨hy₀', hy₁'⟩]
  exact clm_det_restrictScalars_eq_normSq
    (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀ x₁ y)

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M] in
private theorem volumeDensityInChart_transition_absDet (x₀ x₁ : M) {y : M}
    (hy₀ : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source)
    (hy₁ : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₁).source) :
    ω₀.volumeDensityInChart x₀
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ y) =
      |(tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ x₁ y).det| *
        ω₀.volumeDensityInChart x₁
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁ y) := by
  rw [tangentCoordChange_det_eq_normSq x₀ x₁ hy₀ hy₁]
  rw [abs_of_nonneg (Complex.normSq_nonneg _)]
  exact volumeDensityInChart_transition_normSq ω₀ x₀ x₁ hy₀ hy₁

omit [T2Space M] [SigmaCompactSpace M] in
private theorem chartVolume_lintegral_U_eq_of_overlap (x₀ x₁ : M)
    {F : M → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ y in (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source ∩
        (chartAt (EuclideanSpace ℂ (Fin n)) x₁).source,
        F y ∂ω₀.chartVolume x₀ =
      ∫⁻ y in (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source ∩
        (chartAt (EuclideanSpace ℂ (Fin n)) x₁).source,
        F y ∂ω₀.chartVolume x₁ := by
  classical
  set U : Set M :=
    (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source ∩
      (chartAt (EuclideanSpace ℂ (Fin n)) x₁).source with hUdef
  let c₀ := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀
  let c₁ := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁
  let T := c₁ ∘ c₀.symm
  have hUopen : IsOpen U := by
    rw [hUdef]
    exact (chartAt (EuclideanSpace ℂ (Fin n)) x₀).open_source.inter
      (chartAt (EuclideanSpace ℂ (Fin n)) x₁).open_source
  have hUsub₀ : U ⊆ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source := by
    rw [hUdef]
    exact Set.inter_subset_left
  have hUsub₁ : U ⊆ (chartAt (EuclideanSpace ℂ (Fin n)) x₁).source := by
    rw [hUdef]
    exact Set.inter_subset_right
  rw [ω₀.chartVolume_lintegral_U_eq_image x₀ hUopen hUsub₀ hF]
  rw [ω₀.chartVolume_lintegral_U_eq_image x₁ hUopen hUsub₁ hF]
  have hD₀meas : MeasurableSet (c₀ '' U) := by
    dsimp [c₀]
    exact extChartAt_image_measurableSet_of_open_subset_source x₀ hUopen hUsub₀
  have hTimage : T '' (c₀ '' U) = c₁ '' U := by
    exact extChartAt_transition_image x₀ x₁ hUsub₀
  have hTinjOn : Set.InjOn T (c₀ '' U) := by
    exact extChartAt_transition_injOn_overlap_image x₀ x₁ hUsub₀ hUsub₁
  have hTderiv : ∀ z ∈ c₀ '' U,
      HasFDerivWithinAt T
        (tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ x₁ (c₀.symm z))
        (c₀ '' U) z := by
    exact extChartAt_transition_hasFDerivWithinAt_on_overlap_image x₀ x₁
      hUsub₀ hUsub₁
  rw [← hTimage]
  rw [MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (μ := MeasureTheory.volume) hD₀meas hTderiv hTinjOn
    (g := fun z : EuclideanSpace ℂ (Fin n) ↦
      ENNReal.ofReal (ω₀.volumeDensityInChart x₁ z) * F (c₁.symm z))]
  refine MeasureTheory.setLIntegral_congr_fun hD₀meas ?_
  intro z hz
  obtain ⟨y, hyU, rfl⟩ := hz
  have hy₀ : y ∈ c₀.source := by
    rw [extChartAt_source]
    exact hUsub₀ hyU
  have hy₁ : y ∈ c₁.source := by
    rw [extChartAt_source]
    exact hUsub₁ hyU
  have hsymm₀ : c₀.symm (c₀ y) = y := c₀.left_inv hy₀
  have hTcoord : T (c₀ y) = c₁ y := by
    simp [T, hsymm₀]
  have hsymm₁ : c₁.symm (T (c₀ y)) = y := by
    rw [hTcoord]
    exact c₁.left_inv hy₁
  have hdens := volumeDensityInChart_transition_absDet ω₀ x₀ x₁
    (hUsub₀ hyU) (hUsub₁ hyU)
  have hdensReal : ω₀.volumeDensityInChart x₀ (c₀ y) =
      |(tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ x₁ y).det| *
        ω₀.volumeDensityInChart x₁ (c₁ y) := by
    simpa [c₀, c₁] using hdens
  have hdens' :
      ENNReal.ofReal (ω₀.volumeDensityInChart x₀ (c₀ y)) =
        ENNReal.ofReal |(tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
          x₀ x₁ y).det| * ENNReal.ofReal (ω₀.volumeDensityInChart x₁ (c₁ y)) := by
    rw [hdensReal, ENNReal.ofReal_mul (abs_nonneg _)]
  change ENNReal.ofReal (ω₀.volumeDensityInChart x₀ (c₀ y)) *
      F (c₀.symm (c₀ y)) =
    ENNReal.ofReal |(tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      x₀ x₁ (c₀.symm (c₀ y))).det| *
      (ENNReal.ofReal (ω₀.volumeDensityInChart x₁ (T (c₀ y))) *
        F (c₁.symm (T (c₀ y))))
  simp only [hsymm₀, hTcoord]
  rw [hdens']
  rw [c₁.left_inv hy₁]
  ac_rfl

omit [SigmaCompactSpace M] in
private theorem chartVolume_lt_top_of_isCompact_subset_source (x : M) {K : Set M}
    (hK : IsCompact K) (hKx : K ⊆ (chartAt (EuclideanSpace ℂ (Fin n)) x).source) :
    ω₀.chartVolume x K < ⊤ := by
  classical
  let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let D := c '' K
  have hKx' : K ⊆ c.source := by
    rw [extChartAt_source]
    exact hKx
  have hDcomp : IsCompact D :=
    hK.image_of_continuousOn
      ((continuousOn_extChartAt (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x).mono hKx')
  have hDsub : D ⊆ c.target := by
    rintro z ⟨y, hy, rfl⟩
    exact c.map_source (hKx' hy)
  have hDmeas : MeasurableSet D := hDcomp.isClosed.measurableSet
  have hdcont : ContinuousOn (ω₀.volumeDensityInChart x) c.target :=
    ω₀.volumeDensityInChart_continuousOn x
  have hrange : BddAbove (ω₀.volumeDensityInChart x '' D) :=
    (hDcomp.image_of_continuousOn (hdcont.mono hDsub)).bddAbove
  obtain ⟨C, hC⟩ := hrange
  by_cases hKne : K.Nonempty
  · obtain ⟨y, hy⟩ := hKne
    have hcpos : 0 < C := by
      have hz : c y ∈ c.target := c.map_source (hKx' hy)
      have hpos : 0 < ω₀.volumeDensityInChart x (c y) := by
        rw [volumeDensityInChart]
        have hdet := (ω₀.posDef_metricInChart x hz).det_pos
        have hreal : 0 < RCLike.re (ω₀.metricInChart x (c y)).det :=
          (RCLike.pos_iff.mp hdet).1
        positivity
      have hle := hC ⟨c y, ⟨y, hy, rfl⟩, rfl⟩
      exact lt_of_lt_of_le hpos hle
    let μ : Measure (EuclideanSpace ℂ (Fin n)) :=
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))).restrict c.target
    let d : EuclideanSpace ℂ (Fin n) → ℝ≥0∞ :=
      fun z ↦ ENNReal.ofReal (ω₀.volumeDensityInChart x z)
    have hsymm : AEMeasurable c.symm μ := by
      exact (continuousOn_extChartAt_symm x).aemeasurable
        (isOpen_extChartAt_target x).measurableSet
    have hsymm' : AEMeasurable c.symm (μ.withDensity d) := by
      exact hsymm.mono_ac (withDensity_absolutelyContinuous μ d)
    have hpre : NullMeasurableSet (c.symm ⁻¹' K) μ :=
      hsymm.nullMeasurableSet_preimage hK.measurableSet
    have hpreEq : c.symm ⁻¹' K ∩ c.target = D := by
      ext z
      constructor
      · rintro ⟨hzK, hzT⟩
        exact ⟨c.symm z, hzK, c.right_inv hzT⟩
      · rintro ⟨y, hy, rfl⟩
        refine ⟨?_, c.map_source (hKx' hy)⟩
        change c.symm (c y) ∈ K
        rw [c.left_inv (hKx' hy)]
        exact hy
    have hbound : ∀ z ∈ D,
        ENNReal.ofReal (ω₀.volumeDensityInChart x z) ≤ ENNReal.ofReal C := by
      intro z hz
      exact ENNReal.ofReal_le_ofReal (hC ⟨z, hz, rfl⟩)
    have hle : (μ.withDensity d) (c.symm ⁻¹' K) ≤
        ENNReal.ofReal C * (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) D := by
      rw [withDensity_apply₀ d hpre]
      calc
        ∫⁻ z in c.symm ⁻¹' K, d z ∂ μ =
            ∫⁻ z in c.symm ⁻¹' K ∩ c.target, d z
              ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := by
          rw [Measure.restrict_restrict₀ hpre]
        _ = ∫⁻ z in D, d z ∂ (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := by
          rw [hpreEq]
        _ ≤ ∫⁻ z in D, ENNReal.ofReal C
              ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := by
          refine MeasureTheory.setLIntegral_mono_ae (measurable_const.aemeasurable) ?_
          exact Filter.Eventually.of_forall fun z ↦ hbound z
        _ = ENNReal.ofReal C * (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) D :=
          MeasureTheory.setLIntegral_const D (ENNReal.ofReal C)
    have hfinite : ENNReal.ofReal C *
        (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) D < ⊤ :=
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hDcomp.measure_lt_top
    rw [chartVolume, Measure.map_apply_of_aemeasurable hsymm' hK.measurableSet]
    exact lt_of_le_of_lt hle hfinite
  · have hKempty : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hKne
    simp [chartVolume, hKempty]

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M] in
theorem volumeDensityInChart_pos (x : M) {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    0 < ω₀.volumeDensityInChart x z := by
  rw [volumeDensityInChart]
  have hdet := (ω₀.posDef_metricInChart x hz).det_pos
  have hreal : 0 < RCLike.re (ω₀.metricInChart x z).det := by
    exact (RCLike.pos_iff.mp hdet).1
  positivity

/-- Local expression of the volume: on a measurable subset of a chart domain, `ω₀ⁿ / n!` is
`2ⁿ det(g_{jk̄}) dλ` in that chart. -/
theorem volume_apply_of_subset_source (x : M) {A : Set M} (hA : MeasurableSet A)
    (hAx : A ⊆ (chartAt (EuclideanSpace ℂ (Fin n)) x).source) :
    ω₀.volume A = ∫⁻ z in extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x '' A,
      ENNReal.ofReal (ω₀.volumeDensityInChart x z) := by
  classical
  let ρ : SmoothPartitionOfUnity M 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M univ :=
    (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M).choose
  have hρ : ρ.IsSubordinate fun i ↦ (chartAt (EuclideanSpace ℂ (Fin n)) i).source :=
    (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M).choose_spec
  let S : Set M := {i | (Function.support (ρ i)).Nonempty}
  have : Countable S := by
    have hlocal : LocallyFinite (fun i : S ↦ Function.support (ρ i.1)) :=
      ρ.locallyFinite.comp_injective Subtype.val_injective
    exact Set.countable_univ_iff.mp (hlocal.countable_univ fun i ↦ i.2)
  let f : S → M → ℝ≥0∞ := fun i y ↦ A.indicator (fun z ↦ ENNReal.ofReal (ρ i.1 z)) y
  have hfmeas (i : S) : Measurable (f i) := by
    dsimp [f]
    exact (ENNReal.measurable_ofReal.comp
      ((ρ i.1).contMDiff.continuous.measurable)).indicator hA
  have hρzero_off_source (i : S) {y : M}
      (hy : y ∉ (chartAt (EuclideanSpace ℂ (Fin n)) i.1).source) : ρ i.1 y = 0 := by
    by_contra hne
    exact hy (hρ i.1 (subset_tsupport _ hne))
  have hzero_off_overlap (i : S) {y : M}
      (hy : y ∉ (chartAt (EuclideanSpace ℂ (Fin n)) x).source ∩
        (chartAt (EuclideanSpace ℂ (Fin n)) i.1).source) : f i y = 0 := by
    by_cases hyA : y ∈ A
    · have hyx : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source := hAx hyA
      have hyi : y ∉ (chartAt (EuclideanSpace ℂ (Fin n)) i.1).source := by
        intro h
        exact hy ⟨hyx, h⟩
      simp [f, hyA, hρzero_off_source i hyi]
    · simp [f, hyA]
  have hUiopen (i : S) : IsOpen ((chartAt (EuclideanSpace ℂ (Fin n)) x).source ∩
      (chartAt (EuclideanSpace ℂ (Fin n)) i.1).source) :=
    (chartAt (EuclideanSpace ℂ (Fin n)) x).open_source.inter
      (chartAt (EuclideanSpace ℂ (Fin n)) i.1).open_source
  have hfull_to_set (i : S) (μ : Measure M) :
      ∫⁻ y, f i y ∂μ =
        ∫⁻ y in (chartAt (EuclideanSpace ℂ (Fin n)) x).source ∩
          (chartAt (EuclideanSpace ℂ (Fin n)) i.1).source, f i y ∂μ := by
    calc
      ∫⁻ y, f i y ∂μ =
          ∫⁻ y, ((chartAt (EuclideanSpace ℂ (Fin n)) x).source ∩
            (chartAt (EuclideanSpace ℂ (Fin n)) i.1).source).indicator (f i) y ∂μ := by
        apply lintegral_congr
        intro y
        by_cases hy : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source ∩
            (chartAt (EuclideanSpace ℂ (Fin n)) i.1).source
        · simp [hy]
        · simp [hy, hzero_off_overlap i hy]
      _ = _ := by rw [lintegral_indicator (hUiopen i).measurableSet]
  have hterm (i : S) :
      (ω₀.chartVolume i.1).withDensity (fun y ↦ ENNReal.ofReal (ρ i.1 y)) A =
        ∫⁻ y, f i y ∂ω₀.chartVolume x := by
    calc
      _ = ∫⁻ y in A, ENNReal.ofReal (ρ i.1 y) ∂ω₀.chartVolume i.1 :=
        withDensity_apply _ hA
      _ = ∫⁻ y, f i y ∂ω₀.chartVolume i.1 := by
        rw [← lintegral_indicator hA]
      _ = ∫⁻ y in (chartAt (EuclideanSpace ℂ (Fin n)) x).source ∩
            (chartAt (EuclideanSpace ℂ (Fin n)) i.1).source,
            f i y ∂ω₀.chartVolume i.1 := hfull_to_set i _
      _ = ∫⁻ y in (chartAt (EuclideanSpace ℂ (Fin n)) x).source ∩
            (chartAt (EuclideanSpace ℂ (Fin n)) i.1).source,
            f i y ∂ω₀.chartVolume x :=
        (ω₀.chartVolume_lintegral_U_eq_of_overlap x i.1 (hfmeas i)).symm
      _ = ∫⁻ y, f i y ∂ω₀.chartVolume x := (hfull_to_set i _).symm
  let term : M → ℝ≥0∞ := fun i ↦
    (ω₀.chartVolume i).withDensity (fun y ↦ ENNReal.ofReal (ρ i y)) A
  have hterm_zero (i : M) (hi : i ∉ S) : term i = 0 := by
    have hρzero : ∀ y, ρ i y = 0 := by
      intro y
      by_contra hne
      exact hi ⟨y, hne⟩
    change (ω₀.chartVolume i).withDensity
      (fun y ↦ ENNReal.ofReal (ρ i y)) A = 0
    rw [withDensity_apply _ hA]
    simp [hρzero]
  have hterm_support : Function.support term ⊆ S := by
    intro i hi
    by_contra hnot
    exact hi (hterm_zero i hnot)
  rw [volume]
  change Measure.sum (fun i : M ↦
    (ω₀.chartVolume i).withDensity (fun y ↦ ENNReal.ofReal (ρ i y))) A = _
  rw [Measure.sum_apply _ hA]
  change (∑' i : M, term i) = _
  rw [← tsum_subtype_eq_of_support_subset hterm_support]
  calc
    ∑' i : S, term i.1 = ∑' i : S, ∫⁻ y, f i y ∂ω₀.chartVolume x :=
      tsum_congr fun i ↦ hterm i
    _ = ∫⁻ y, ∑' i : S, f i y ∂ω₀.chartVolume x := by
      symm
      apply lintegral_tsum
      intro i
      exact (hfmeas i).aemeasurable
    _ = ∫⁻ y, A.indicator (fun _ ↦ (1 : ℝ≥0∞)) y ∂ω₀.chartVolume x := by
      apply lintegral_congr
      intro y
      by_cases hyA : y ∈ A
      · simp only [f, Set.indicator_of_mem hyA]
        have hPOU : ∑ᶠ i : M, ρ i y = 1 := ρ.sum_eq_one (mem_univ y)
        have hρfinite : Function.HasFiniteSupport (fun i : M ↦ ρ i y) :=
          hasFiniteSupport_of_finsum_eq_one hPOU
        have hρtsum : ∑' i : M, ρ i y = 1 := by
          rw [tsum_eq_finsum hρfinite, hPOU]
        have hENNtsum : ∑' i : M, ENNReal.ofReal (ρ i y) = 1 := by
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun i ↦ ρ.nonneg i y)
            (summable_of_hasFiniteSupport hρfinite),
            hρtsum]
          simp
        have hsupport : Function.support (fun i : M ↦ ENNReal.ofReal (ρ i y)) ⊆ S := by
          intro i hi
          have hρne : ρ i y ≠ 0 := by
            intro hz
            simp [hz] at hi
          exact ⟨y, hρne⟩
        exact (tsum_subtype_eq_of_support_subset hsupport).trans hENNtsum
      · simp [f, hyA]
    _ = ω₀.chartVolume x A := by
      rw [lintegral_indicator hA]
      rw [setLIntegral_const]
      simp
    _ = ∫⁻ z in extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x '' A,
        ENNReal.ofReal (ω₀.volumeDensityInChart x z) :=
      ω₀.chartVolume_apply_of_measurable_subset_source x hA hAx

/-- On the source of the chart centered at `x`, the chart volume agrees with the global volume.

This is the measure form of the local coordinate expression for `ω₀ⁿ / n!`; it lets local
Bochner integrals on a chart domain be computed with the global volume measure. -/
theorem chartVolume_restrict_chartSource_eq_volume_restrict (x : M) :
    (ω₀.chartVolume x).restrict (chartAt (EuclideanSpace ℂ (Fin n)) x).source =
      ω₀.volume.restrict (chartAt (EuclideanSpace ℂ (Fin n)) x).source := by
  have hsource : MeasurableSet ((chartAt (EuclideanSpace ℂ (Fin n)) x).source) :=
    (chartAt (EuclideanSpace ℂ (Fin n)) x).open_source.measurableSet
  apply Measure.ext
  intro A hA
  have hA' : MeasurableSet (A ∩ (chartAt (EuclideanSpace ℂ (Fin n)) x).source) :=
    hA.inter hsource
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
  rw [ω₀.volume_apply_of_subset_source x hA' Set.inter_subset_right,
    ω₀.chartVolume_apply_of_measurable_subset_source x hA' Set.inter_subset_right]

/-- Bochner integrals over a chart domain can be computed using the global volume measure. -/
theorem integral_chartVolume_restrict_chartSource_eq_integral_volume_restrict
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (x : M) (f : M → E) :
    ∫ y, f y ∂(ω₀.chartVolume x).restrict (chartAt (EuclideanSpace ℂ (Fin n)) x).source =
      ∫ y, f y ∂ω₀.volume.restrict (chartAt (EuclideanSpace ℂ (Fin n)) x).source := by
  rw [ω₀.chartVolume_restrict_chartSource_eq_volume_restrict x]

omit [TopologicalSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M] in
private theorem withDensity_eq_of_restrict_eq (μ ν : Measure M) (S : Set M)
    (hS : MeasurableSet S) (d : M → ℝ≥0∞) (hd : ∀ y ∉ S, d y = 0)
    (hμν : μ.restrict S = ν.restrict S) :
    μ.withDensity d = ν.withDensity d := by
  have hindicator : S.indicator d = d := by
    funext y
    by_cases hy : y ∈ S
    · simp [hy]
    · simp [hy, hd y hy]
  calc
    μ.withDensity d = μ.withDensity (S.indicator d) := by rw [hindicator]
    _ = (μ.restrict S).withDensity d := withDensity_indicator hS d
    _ = (ν.restrict S).withDensity d := by rw [hμν]
    _ = ν.withDensity (S.indicator d) := (withDensity_indicator hS d).symm
    _ = ν.withDensity d := by rw [hindicator]

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M] in
private theorem pou_ennreal_tsum_eq_one
    (ρ : SmoothPartitionOfUnity M 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M univ) (y : M) :
    ∑' i : M, ENNReal.ofReal (ρ i y) = 1 := by
  have hPOU : ∑ᶠ i : M, ρ i y = 1 := ρ.sum_eq_one (mem_univ y)
  have hρfinite : Function.HasFiniteSupport (fun i : M ↦ ρ i y) :=
    hasFiniteSupport_of_finsum_eq_one hPOU
  have hρtsum : ∑' i : M, ρ i y = 1 := by
    rw [tsum_eq_finsum hρfinite, hPOU]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i ↦ ρ.nonneg i y)
    (summable_of_hasFiniteSupport hρfinite), hρtsum]
  simp

/-- The volume does not depend on the partition of unity used to define it. -/
theorem volume_eq_sum_of_isSubordinate
    (ρ : SmoothPartitionOfUnity M 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M univ)
    (hρ : ρ.IsSubordinate fun x ↦ (chartAt (EuclideanSpace ℂ (Fin n)) x).source) :
    ω₀.volume = Measure.sum fun x : M ↦
      (ω₀.chartVolume x).withDensity fun y ↦ ENNReal.ofReal (ρ x y) := by
  classical
  let S : Set M := {i | (Function.support (ρ i)).Nonempty}
  have : Countable S := by
    have hlocal : LocallyFinite (fun i : S ↦ Function.support (ρ i.1)) :=
      ρ.locallyFinite.comp_injective Subtype.val_injective
    exact Set.countable_univ_iff.mp (hlocal.countable_univ fun i ↦ i.2)
  have hsource_meas (i : M) :
      MeasurableSet ((chartAt (EuclideanSpace ℂ (Fin n)) i).source) :=
    (chartAt (EuclideanSpace ℂ (Fin n)) i).open_source.measurableSet
  have hρzero_off_source (i : M) {y : M}
      (hy : y ∉ (chartAt (EuclideanSpace ℂ (Fin n)) i).source) : ρ i y = 0 := by
    by_contra hne
    exact hy (hρ i (subset_tsupport _ hne))
  have hrestrict (i : M) :
      (ω₀.chartVolume i).restrict (chartAt (EuclideanSpace ℂ (Fin n)) i).source =
        ω₀.volume.restrict (chartAt (EuclideanSpace ℂ (Fin n)) i).source := by
    exact chartVolume_restrict_chartSource_eq_volume_restrict ω₀ i
  have hterm_measure (i : M) :
      (ω₀.chartVolume i).withDensity (fun y ↦ ENNReal.ofReal (ρ i y)) =
        ω₀.volume.withDensity (fun y ↦ ENNReal.ofReal (ρ i y)) := by
    apply withDensity_eq_of_restrict_eq
      (ω₀.chartVolume i) ω₀.volume (chartAt (EuclideanSpace ℂ (Fin n)) i).source
      (hsource_meas i) (fun y ↦ ENNReal.ofReal (ρ i y))
    · intro y hy
      rw [hρzero_off_source i hy, ENNReal.ofReal_zero]
    · exact hrestrict i
  let ν : M → Measure M := fun i ↦
    ω₀.volume.withDensity (fun y ↦ ENNReal.ofReal (ρ i y))
  have hsum_chart_eq_volume :
      Measure.sum (fun i : M ↦
        (ω₀.chartVolume i).withDensity (fun y ↦ ENNReal.ofReal (ρ i y))) =
      Measure.sum ν := by
    apply Measure.ext
    intro A hA
    rw [Measure.sum_apply _ hA, Measure.sum_apply _ hA]
    exact tsum_congr fun i ↦ congrArg (fun μ : Measure M ↦ μ A) (hterm_measure i)
  have hzero (i : M) (hi : i ∉ S) : ν i = 0 := by
    have hρzero : ∀ y, ρ i y = 0 := by
      intro y
      by_contra hne
      exact hi ⟨y, hne⟩
    simp [ν, hρzero]
  have hνsupport : Function.support ν ⊆ S := by
    intro i hi
    by_contra hnot
    exact hi (hzero i hnot)
  have hsum_subtype : Measure.sum (fun i : S ↦ ν i.1) = Measure.sum ν := by
    apply Measure.ext
    intro A hA
    rw [Measure.sum_apply _ hA, Measure.sum_apply _ hA]
    have hsupportA : Function.support (fun i : M ↦ ν i A) ⊆ S := by
      intro i hi
      by_contra hnot
      exact hi (congrArg (fun μ : Measure M ↦ μ A) (hzero i hnot))
    exact tsum_subtype_eq_of_support_subset hsupportA
  have hdensity_meas (i : S) : Measurable (fun y ↦ ENNReal.ofReal (ρ i.1 y)) := by
    exact ENNReal.measurable_ofReal.comp ((ρ i.1).contMDiff.continuous.measurable)
  have hsum_density :
      Measure.sum (fun i : S ↦ ν i.1) =
        ω₀.volume.withDensity (fun y ↦ ∑' i : S, ENNReal.ofReal (ρ i.1 y)) := by
    change Measure.sum (fun i : S ↦
      ω₀.volume.withDensity (fun y ↦ ENNReal.ofReal (ρ i.1 y))) = _
    rw [← withDensity_tsum hdensity_meas]
    congr 1
    funext y
    exact tsum_apply (Pi.summable.2 fun _ ↦ ENNReal.summable)
  have hpointwise : ∀ y, ∑' i : S, ENNReal.ofReal (ρ i.1 y) = 1 := by
    intro y
    have hsupport : Function.support (fun i : M ↦ ENNReal.ofReal (ρ i y)) ⊆ S := by
      intro i hi
      have hρne : ρ i y ≠ 0 := by
        intro hzero
        simp [hzero] at hi
      exact ⟨y, hρne⟩
    exact (tsum_subtype_eq_of_support_subset hsupport).trans
      (pou_ennreal_tsum_eq_one ρ y)
  have hdensity : (fun y ↦ ∑' i : S, ENNReal.ofReal (ρ i.1 y)) = fun _ ↦ (1 : ℝ≥0∞) :=
    funext hpointwise
  have hwithDensityOne : ω₀.volume.withDensity (fun _ : M ↦ (1 : ℝ≥0∞)) = ω₀.volume :=
    withDensity_one
  calc
    ω₀.volume = Measure.sum (fun i : S ↦ ν i.1) := by
      calc
        ω₀.volume = ω₀.volume.withDensity (fun _ : M ↦ (1 : ℝ≥0∞)) := hwithDensityOne.symm
        _ = ω₀.volume.withDensity (fun y ↦ ∑' i : S, ENNReal.ofReal (ρ i.1 y)) := by
          rw [hdensity]
        _ = Measure.sum (fun i : S ↦ ν i.1) := hsum_density.symm
    _ = Measure.sum ν := hsum_subtype
    _ = Measure.sum (fun i : M ↦
          (ω₀.chartVolume i).withDensity (fun y ↦ ENNReal.ofReal (ρ i y))) :=
      hsum_chart_eq_volume.symm

omit [T2Space M] [SigmaCompactSpace M] in
private theorem chartVolume_withDensity_le
    (ρ : SmoothPartitionOfUnity M 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M univ) (i : M)
    {K : Set M} (hK : MeasurableSet K) :
    (ω₀.chartVolume i).withDensity (fun y ↦ ENNReal.ofReal (ρ i y)) K ≤
      ω₀.chartVolume i (K ∩ tsupport (ρ i)) := by
  have htsup_closed : IsClosed (tsupport (ρ i)) := isClosed_tsupport _
  have htsup_meas : MeasurableSet (tsupport (ρ i)) := htsup_closed.measurableSet
  have hρ_zero_off : ∀ y, y ∉ tsupport (ρ i) → ρ i y = 0 := by
    intro y hy
    by_contra hne
    exact hy (subset_tsupport _ hne)
  have hpoint : ∀ y, ENNReal.ofReal (ρ i y) ≤
      (tsupport (ρ i)).indicator (fun _ ↦ (1 : ℝ≥0∞)) y := by
    intro y
    by_cases hy : y ∈ tsupport (ρ i)
    · rw [Set.indicator_of_mem hy]
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (ρ.le_one i y)
    · rw [Set.indicator_of_notMem hy, hρ_zero_off y hy, ENNReal.ofReal_zero]
  rw [withDensity_apply _ hK]
  calc
    ∫⁻ y in K, ENNReal.ofReal (ρ i y) ∂ω₀.chartVolume i
      ≤ ∫⁻ y in K, (tsupport (ρ i)).indicator (fun _ ↦ (1 : ℝ≥0∞)) y
          ∂ω₀.chartVolume i := by
        refine MeasureTheory.setLIntegral_mono_ae
          ((measurable_const.indicator htsup_meas).aemeasurable) ?_
        exact Filter.Eventually.of_forall fun y _ ↦ hpoint y
    _ = ω₀.chartVolume i (K ∩ tsupport (ρ i)) := by
        rw [lintegral_indicator htsup_meas, Measure.restrict_restrict htsup_meas,
          setLIntegral_const, one_mul, Set.inter_comm]

omit [T2Space M] [SigmaCompactSpace M] in
private theorem chartVolume_pos_of_open_subset_source (x : M) {U : Set M}
    (hU : IsOpen U) (hUne : U.Nonempty)
    (hUx : U ⊆ (chartAt (EuclideanSpace ℂ (Fin n)) x).source) :
    0 < ω₀.chartVolume x U := by
  classical
  let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let D := c '' U
  have hUx' : U ⊆ c.source := by
    rw [extChartAt_source]
    exact hUx
  have hDopen : IsOpen D := by
    have hpre := (continuousOn_extChartAt_symm x).isOpen_inter_preimage
      (isOpen_extChartAt_target (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x) hU
    change IsOpen (c '' U)
    rw [c.image_eq_target_inter_inv_preimage hUx']
    exact hpre
  have hDne : D.Nonempty := by
    rcases hUne with ⟨y, hy⟩
    exact ⟨c y, y, hy, rfl⟩
  have hDsub : D ⊆ c.target := by
    rintro z ⟨y, hy, rfl⟩
    exact c.map_source (hUx' hy)
  have hDmeas : MeasurableSet D := hDopen.measurableSet
  have hdcont : ContinuousOn (ω₀.volumeDensityInChart x) D :=
    (ω₀.volumeDensityInChart_continuousOn x).mono hDsub
  let g : EuclideanSpace ℂ (Fin n) → ℝ≥0∞ :=
    D.indicator (fun z ↦ ENNReal.ofReal (ω₀.volumeDensityInChart x z))
  have hgcont : ContinuousOn (fun z ↦ ENNReal.ofReal (ω₀.volumeDensityInChart x z)) D :=
    ENNReal.continuous_ofReal.continuousOn.comp hdcont (fun _ _ ↦ Set.mem_univ _)
  have hconst : ContinuousOn (fun _ : EuclideanSpace ℂ (Fin n) ↦ (0 : ℝ≥0∞)) Dᶜ :=
    continuousOn_const
  have hpiece : Measurable (D.piecewise
      (fun z ↦ ENNReal.ofReal (ω₀.volumeDensityInChart x z)) fun _ ↦ (0 : ℝ≥0∞)) :=
    hgcont.measurable_piecewise hconst hDmeas
  have hgmeas : Measurable g := by
    change Measurable (D.piecewise
      (fun z ↦ ENNReal.ofReal (ω₀.volumeDensityInChart x z)) fun _ ↦ (0 : ℝ≥0∞))
    exact hpiece
  have hDsupport : D ⊆ Function.support g := by
    intro z hz
    change g z ≠ 0
    simp only [g, Set.indicator_of_mem hz]
    exact (ENNReal.ofReal_pos.mpr (ω₀.volumeDensityInChart_pos x (hDsub hz))).ne'
  have hDpos : 0 < (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) D :=
    hDopen.measure_pos _ hDne
  have hlinpos : 0 < ∫⁻ z, g z ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) :=
    (lintegral_pos_iff_support hgmeas).2
      (lt_of_lt_of_le hDpos (measure_mono hDsupport))
  have hlinpos' : 0 < ∫⁻ z in D, ENNReal.ofReal (ω₀.volumeDensityInChart x z)
      ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := by
    rw [lintegral_indicator hDmeas] at hlinpos
    exact hlinpos
  rw [chartVolume_apply_of_measurable_subset_source ω₀ x hU.measurableSet hUx]
  exact hlinpos'

instance isFiniteMeasure_volume [CompactSpace M] : IsFiniteMeasure ω₀.volume := by
  classical
  refine ⟨?_⟩
  let ρ : SmoothPartitionOfUnity M 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M univ :=
    (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M).choose
  have hρ : ρ.IsSubordinate fun x ↦ (chartAt (EuclideanSpace ℂ (Fin n)) x).source :=
    (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M).choose_spec
  let S : Finset M :=
    (ρ.locallyFinite.closure.finite_nonempty_inter_compact isCompact_univ).toFinset
  have hterm (i : M) :
      (ω₀.chartVolume i).withDensity (fun y ↦ ENNReal.ofReal (ρ i y)) univ < ⊤ := by
    have hKcompact : IsCompact (tsupport (ρ i)) := isClosed_tsupport _ |>.isCompact
    have hKsubset : tsupport (ρ i) ⊆ (chartAt (EuclideanSpace ℂ (Fin n)) i).source := hρ i
    have hchart := chartVolume_lt_top_of_isCompact_subset_source ω₀ i hKcompact hKsubset
    have hle := chartVolume_withDensity_le ω₀ ρ i MeasurableSet.univ
    have hle' :
        (ω₀.chartVolume i).withDensity (fun y ↦ ENNReal.ofReal (ρ i y)) univ ≤
          ω₀.chartVolume i (tsupport (ρ i)) := by
      simpa only [Set.univ_inter] using hle
    exact lt_of_le_of_lt hle' hchart
  have hzero (i : M) (hi : i ∉ S) :
      (ω₀.chartVolume i).withDensity (fun y ↦ ENNReal.ofReal (ρ i y)) univ = 0 := by
    rw [withDensity_apply _ MeasurableSet.univ]
    have hρzero : ∀ y, ρ i y = 0 := by
      intro y
      by_contra hne
      have hy : y ∈ tsupport (ρ i) := subset_tsupport _ hne
      apply hi
      have hS : i ∈ (ρ.locallyFinite.closure.finite_nonempty_inter_compact
          isCompact_univ).toFinset := by
        simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
        exact ⟨y, hy, mem_univ y⟩
      simpa only [S] using hS
    simp [hρzero]
  rw [volume]
  change Measure.sum
    (fun i : M ↦ (ω₀.chartVolume i).withDensity fun y ↦ ENNReal.ofReal (ρ i y)) univ < ⊤
  rw [Measure.sum_apply _ MeasurableSet.univ,
    tsum_eq_sum (s := S) (fun i hi ↦ hzero i hi)]
  exact ENNReal.sum_lt_top.mpr (fun i _ ↦ hterm i)

instance isOpenPosMeasure_volume : ω₀.volume.IsOpenPosMeasure := by
  classical
  refine ⟨?_⟩
  intro U hU hUne
  let ρ : SmoothPartitionOfUnity M 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M univ :=
    (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M).choose
  have hρ : ρ.IsSubordinate fun x ↦ (chartAt (EuclideanSpace ℂ (Fin n)) x).source :=
    (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M).choose_spec
  rcases hUne with ⟨x, hxU⟩
  obtain ⟨i, hi⟩ := ρ.exists_pos_of_mem (mem_univ x)
  have hxsupport : x ∈ tsupport (ρ i) := subset_tsupport _ hi.ne'
  have hchart : x ∈ (chartAt (EuclideanSpace ℂ (Fin n)) i).source := hρ i hxsupport
  let a : ℝ := ρ i x / 2
  have ha : 0 < a := by positivity
  have hρcont : Continuous fun y ↦ ρ i y := (ρ i).contMDiff.continuous
  have hpositiveOpen : IsOpen {y | a < ρ i y} := isOpen_lt continuous_const hρcont
  have hchartOpen : IsOpen ((chartAt (EuclideanSpace ℂ (Fin n)) i).source) := by
    rw [← extChartAt_source (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))]
    exact isOpen_extChartAt_source (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) i
  let V := U ∩ (chartAt (EuclideanSpace ℂ (Fin n)) i).source ∩ {y | a < ρ i y}
  have hVopen : IsOpen V := by
    change IsOpen (U ∩ (chartAt (EuclideanSpace ℂ (Fin n)) i).source ∩ {y | a < ρ i y})
    exact (hU.inter hchartOpen).inter hpositiveOpen
  have hxV : x ∈ V := by
    refine ⟨⟨hxU, hchart⟩, ?_⟩
    dsimp [a]
    linarith
  have hVne : V.Nonempty := ⟨x, hxV⟩
  have hVsource : V ⊆ (chartAt (EuclideanSpace ℂ (Fin n)) i).source :=
    fun _ hy ↦ hy.1.2
  have hchartV : 0 < ω₀.chartVolume i V :=
    chartVolume_pos_of_open_subset_source ω₀ i hVopen hVne hVsource
  have hweight : ∀ y ∈ V, ENNReal.ofReal a ≤ ENNReal.ofReal (ρ i y) := by
    intro y hy
    exact ENNReal.ofReal_le_ofReal (le_of_lt hy.2)
  have hterm : 0 <
      (ω₀.chartVolume i).withDensity (fun y ↦ ENNReal.ofReal (ρ i y)) V := by
    rw [withDensity_apply _ hVopen.measurableSet]
    have hρmeas : Measurable (fun y ↦ ENNReal.ofReal (ρ i y)) :=
      ENNReal.measurable_ofReal.comp hρcont.measurable
    calc
      ∫⁻ y in V, ENNReal.ofReal (ρ i y) ∂ω₀.chartVolume i
        ≥ ∫⁻ y in V, ENNReal.ofReal a ∂ω₀.chartVolume i := by
          refine MeasureTheory.setLIntegral_mono_ae hρmeas.aemeasurable ?_
          exact Filter.Eventually.of_forall fun y hy ↦ hweight y hy
      _ = ENNReal.ofReal a * ω₀.chartVolume i V :=
          setLIntegral_const V (ENNReal.ofReal a)
      _ > 0 := ENNReal.mul_pos (ENNReal.ofReal_pos.mpr ha).ne' hchartV.ne'
  have hVle :
      (ω₀.chartVolume i).withDensity (fun y ↦ ENNReal.ofReal (ρ i y)) V ≤ ω₀.volume V :=
    Measure.le_sum _ i V
  have hUV : V ⊆ U := fun _ hy ↦ hy.1.1
  have hpos : 0 < ω₀.volume U := lt_of_lt_of_le hterm (hVle.trans (measure_mono hUV))
  exact hpos.ne'

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M] in
/-- Comparison of two volume forms: `ω₁ⁿ = (ω₁ⁿ / ω₀ⁿ) ω₀ⁿ`. -/
private theorem relDet_eq_chartRep (ω₁ : KahlerForm n M) {x y : M}
    (hy : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source) :
    relDet (ω₀ y) (ω₁ y) =
      relDet (ω₀.toFormField.chartRep x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y))
        (ω₁.toFormField.chartRep x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)) := by
  let A₀ := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y
  let B₀ := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y x y
  have hyy : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source :=
    mem_extChartAt_source y
  have hyyR : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).source :=
    mem_extChartAt_source y
  have hyC : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source := by
    simpa only [extChartAt_real_eq] using hy
  have hab : ∀ v, A₀ (B₀ v) = v := by
    intro v
    calc
      A₀ (B₀ v) = tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y y y v := by
        exact tangentCoordChange_comp ⟨⟨hyy, hyC⟩, hyy⟩
      _ = v := tangentCoordChange_self hyy
  have hba : ∀ v, B₀ (A₀ v) = v := by
    intro v
    calc
      B₀ (A₀ v) = tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x x y v := by
        exact tangentCoordChange_comp ⟨⟨hyC, hyy⟩, hyC⟩
      _ = v := tangentCoordChange_self hy
  have hAinj : Function.Injective A₀ := by
    intro u v huv
    calc
      u = B₀ (A₀ u) := (hba u).symm
      _ = B₀ (A₀ v) := congrArg B₀ huv
      _ = v := hba v
  have hAsurj : Function.Surjective A₀ := by
    intro v
    exact ⟨B₀ v, hab v⟩
  let Alinear : EuclideanSpace ℂ (Fin n) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) := {
    toFun := A₀
    invFun := B₀
    left_inv := hba
    right_inv := hab
    map_add' := A₀.map_add
    map_smul' := A₀.map_smul }
  let A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n) := {
    __ := Alinear
    continuous_toFun := A₀.continuous
    continuous_invFun := B₀.continuous }
  have hA : (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) = A₀ := by
    ext v
    rfl
  have hcoord : tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y =
      (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ := by
    rw [tangentCoordChange_real_eq ⟨hy, hyyR⟩, hA]
  have hy' : (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y) ∈
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).source := by
    rw [(extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).left_inv hy]
    exact mem_extChartAt_source y
  have hz : extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y ∈
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target :=
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).map_source hy
  have hrep0 := FormField.chartRep_eq_chartRep_comp (α := ω₀.toFormField)
    (x := x) (x' := y) (z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)
      hz hy'
  have hrep1 := FormField.chartRep_eq_chartRep_comp (α := ω₁.toFormField)
    (x := x) (x' := y) (z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)
      hz hy'
  have hderiv : fderiv ℝ
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y ∘
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y) =
      (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ := by
    have h := hcoord
    rw [tangentCoordChange_def, extChartAt_real_eq] at h
    simpa [ModelWithCorners.range_eq_univ, fderivWithin_univ] using h
  rw [hderiv] at hrep0 hrep1
  have hrep0' : ω₀.toFormField.chartRep x
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y) =
      (ω₀ y).compContinuousLinearMap
        ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ) := by
    have hzcenter : extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y
        ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)) =
        extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y := by
      rw [(extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).left_inv hy]
    rw [hzcenter, FormField.chartRep_self] at hrep0
    exact hrep0
  have hrep1' : ω₁.toFormField.chartRep x
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y) =
      (ω₁ y).compContinuousLinearMap
        ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ) := by
    have hzcenter : extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y
        ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)) =
        extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y := by
      rw [(extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).left_inv hy]
    rw [hzcenter, FormField.chartRep_self] at hrep1
    exact hrep1
  have hrel := relDet_compContinuousLinearMap (ω₀.isOneOne y) (ω₁.isOneOne y) A
  calc
    relDet (ω₀ y) (ω₁ y) = relDet
        ((ω₀ y).compContinuousLinearMap
          ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ))
        ((ω₁ y).compContinuousLinearMap
          ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)) :=
      hrel.symm
    _ = relDet (ω₀.toFormField.chartRep x
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y))
        (ω₁.toFormField.chartRep x
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)) := by rw [hrep0', hrep1']

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M] in
private theorem volumeDensityInChart_eq_relDet_mul (ω₁ : KahlerForm n M) (x : M)
    {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    ω₁.volumeDensityInChart x z =
      relDet (ω₀ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z))
        (ω₁ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z)) *
        ω₀.volumeDensityInChart x z := by
  let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  have hy := c.map_target hz
  have hrel := relDet_eq_chartRep ω₀ ω₁ hy
  have hden : RCLike.re (ω₀.metricInChart x z).det ≠ 0 := by
    have hpos := ω₀.volumeDensityInChart_pos x hz
    rw [volumeDensityInChart] at hpos
    exact ne_of_gt ((mul_pos_iff_of_pos_left (by positivity : 0 < (2 : ℝ) ^ n)).mp hpos)
  rw [hrel]
  rw [volumeDensityInChart, volumeDensityInChart, c.right_inv hz]
  change (2 : ℝ) ^ n * RCLike.re (ω₁.metricInChart x z).det =
    (RCLike.re (ω₁.metricInChart x z).det / RCLike.re (ω₀.metricInChart x z).det) *
      ((2 : ℝ) ^ n * RCLike.re (ω₀.metricInChart x z).det)
  field_simp [hden]

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M] in
theorem continuous_relDet (ω₁ : KahlerForm n M) : Continuous fun x ↦ relDet (ω₀ x) (ω₁ x) := by
  rw [continuous_iff_continuousAt]
  intro x
  let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let q : EuclideanSpace ℂ (Fin n) → ℝ := fun z ↦
    RCLike.re (ω₁.metricInChart x z).det / RCLike.re (ω₀.metricInChart x z).det
  have hdet₀ : ContinuousOn (fun z ↦ (ω₀.metricInChart x z).det) c.target := by
    classical
    simp_rw [Matrix.det_apply]
    exact continuousOn_finsetSum Finset.univ fun σ _ ↦
      continuousOn_const.smul <| continuousOn_finsetProd Finset.univ fun i _ ↦
        (ω₀.contDiffOn_metricInChart x (σ i) i).continuousOn
  have hdet₁ : ContinuousOn (fun z ↦ (ω₁.metricInChart x z).det) c.target := by
    classical
    simp_rw [Matrix.det_apply]
    exact continuousOn_finsetSum Finset.univ fun σ _ ↦
      continuousOn_const.smul <| continuousOn_finsetProd Finset.univ fun i _ ↦
        (ω₁.contDiffOn_metricInChart x (σ i) i).continuousOn
  have hden : ∀ z ∈ c.target, 0 < RCLike.re (ω₀.metricInChart x z).det := by
    intro z hz
    have h := ω₀.volumeDensityInChart_pos x hz
    dsimp [volumeDensityInChart] at h
    exact (mul_pos_iff_of_pos_left (by positivity : 0 < (2 : ℝ) ^ n)).mp h
  have hq : ContinuousOn q c.target := by
    have hnum : ContinuousOn (fun z ↦ (ω₁.metricInChart x z).det.re) c.target :=
      Complex.continuous_re.continuousOn.comp hdet₁ (fun _ _ ↦ Set.mem_univ _)
    have hden' : ContinuousOn (fun z ↦ (ω₀.metricInChart x z).det.re) c.target :=
      Complex.continuous_re.continuousOn.comp hdet₀ (fun _ _ ↦ Set.mem_univ _)
    exact hnum.div hden' fun z hz ↦ (hden z hz).ne'
  have hlocal : ∀ y ∈ c.source,
      relDet (ω₀ y) (ω₁ y) = q (c y) := by
    intro y hy
    rw [relDet_eq_chartRep ω₀ ω₁ hy]
    rfl
  have hz : c x ∈ c.target := c.map_source (mem_extChartAt_source x)
  have hqAt : ContinuousAt q (c x) :=
    (hq.continuousWithinAt hz).continuousAt ((isOpen_extChartAt_target x).mem_nhds hz)
  have heq : (fun y ↦ relDet (ω₀ y) (ω₁ y)) =ᶠ[nhds x] fun y ↦ q (c y) := by
    filter_upwards [extChartAt_source_mem_nhds (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x] with y hy
    exact hlocal y hy
  exact (hqAt.comp (continuousAt_extChartAt x)).congr_of_eventuallyEq heq

omit [T2Space M] [SigmaCompactSpace M] in
private theorem chartVolume_eq_withDensity_relDet (ω₁ : KahlerForm n M) (x : M) :
    ω₁.chartVolume x = (ω₀.chartVolume x).withDensity
      (fun y ↦ ENNReal.ofReal (relDet (ω₀ y) (ω₁ y))) := by
  let r : M → ℝ≥0∞ := fun y ↦ ENNReal.ofReal (relDet (ω₀ y) (ω₁ y))
  have hr : Measurable r := by
    dsimp [r]
    exact ENNReal.measurable_ofReal.comp (ω₀.continuous_relDet ω₁).measurable
  refine Measure.ext_of_lintegral _ ?_
  intro f hf
  rw [MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀ hr.aemeasurable hf.aemeasurable]
  calc
    ∫⁻ y, f y ∂ω₁.chartVolume x =
        ∫⁻ z in (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target,
          ENNReal.ofReal (ω₁.volumeDensityInChart x z) *
            f ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z)
            ∂MeasureTheory.volume := chartVolume_lintegral ω₁ x hf
    _ = ∫⁻ z in (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target,
          ENNReal.ofReal (ω₀.volumeDensityInChart x z) *
            (r ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z) *
              f ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z))
            ∂MeasureTheory.volume := by
      refine MeasureTheory.setLIntegral_congr_fun
        (isOpen_extChartAt_target x).measurableSet ?_
      intro z hz
      have hy := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).map_target hz
      have hdens := volumeDensityInChart_eq_relDet_mul ω₀ ω₁ x hz
      have hrelpos := relDet_pos (ω₀.isPositive ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z))
        (ω₁.isPositive ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z))
      have hcast : ENNReal.ofReal (ω₁.volumeDensityInChart x z) =
          r ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z) *
            ENNReal.ofReal (ω₀.volumeDensityInChart x z) := by
        rw [hdens, ENNReal.ofReal_mul (le_of_lt hrelpos)]
      change ENNReal.ofReal (ω₁.volumeDensityInChart x z) *
          f ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z) =
        ENNReal.ofReal (ω₀.volumeDensityInChart x z) *
          (r ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z) *
            f ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z))
      calc
        _ = (r ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z) *
            ENNReal.ofReal (ω₀.volumeDensityInChart x z)) *
            f ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z) := by rw [hcast]
        _ = _ := by ac_rfl
    _ = ∫⁻ y, r y * f y ∂ω₀.chartVolume x := by
      symm
      exact chartVolume_lintegral ω₀ x (hr.mul hf)

/-- Comparison of two volume forms: `ω₁ⁿ = (ω₁ⁿ / ω₀ⁿ) ω₀ⁿ`. -/
theorem volume_eq_withDensity_relDet (ω₁ : KahlerForm n M) :
    ω₁.volume = ω₀.volume.withDensity fun x ↦ ENNReal.ofReal (relDet (ω₀ x) (ω₁ x)) := by
  classical
  let ρ : SmoothPartitionOfUnity M 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M univ :=
    (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M).choose
  let r : M → ℝ≥0∞ := fun y ↦ ENNReal.ofReal (relDet (ω₀ y) (ω₁ y))
  have hr : Measurable r := by
    dsimp [r]
    exact ENNReal.measurable_ofReal.comp (ω₀.continuous_relDet ω₁).measurable
  have hp (i : M) : Measurable (fun y ↦ ENNReal.ofReal (ρ i y)) := by
    exact ENNReal.measurable_ofReal.comp (ρ i).contMDiff.continuous.measurable
  have hterm (i : M) :
      (ω₁.chartVolume i).withDensity (fun y ↦ ENNReal.ofReal (ρ i y)) =
        ((ω₀.chartVolume i).withDensity (fun y ↦ ENNReal.ofReal (ρ i y))).withDensity r := by
    rw [chartVolume_eq_withDensity_relDet ω₀ ω₁ i]
    rw [← withDensity_mul (ω₀.chartVolume i) hr (hp i),
      ← withDensity_mul (ω₀.chartVolume i) (hp i) hr]
    congr 1
    ext y
    simp [mul_comm]
  change (Measure.sum fun i : M ↦
      (ω₁.chartVolume i).withDensity (fun y ↦ ENNReal.ofReal (ρ i y))) =
    (Measure.sum fun i : M ↦
      (ω₀.chartVolume i).withDensity (fun y ↦ ENNReal.ofReal (ρ i y))).withDensity r
  rw [withDensity_sum]
  apply Measure.ext
  intro s hs
  rw [Measure.sum_apply _ hs, Measure.sum_apply _ hs]
  exact tsum_congr fun i ↦ congrArg (fun μ : Measure M ↦ μ s) (hterm i)

end KahlerForm
