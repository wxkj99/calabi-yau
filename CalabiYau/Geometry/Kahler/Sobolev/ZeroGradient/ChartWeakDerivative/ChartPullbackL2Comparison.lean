module

public import CalabiYau.Analysis.Sobolev.Manifold.Rellich.OnManifold
public import CalabiYau.Geometry.Kahler.Volume
import CalabiYau.Geometry.Kahler.Sobolev.ChartVolumeIntegral

/-!
# L² comparison for Kähler chart pullbacks

A positive lower bound for the Kähler volume density on a compact subset of a chart controls the
Euclidean `L²` norm of the chart pullback by the global Kähler `L²` norm, with a finite constant
that also accounts for the realification's Haar/Jacobian factor.
-/

@[expose] public section

open scoped Manifold ContDiff ENNReal NNReal
open MeasureTheory Filter Topology

namespace KahlerForm

private lemma eLpNorm_restrict_le_of_density_lower
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (K : Set X)
    (d : X → ℝ≥0∞) (c : ℝ≥0∞) (f : X → ℝ)
    (hK : MeasurableSet K) (hc₀ : c ≠ 0) (hcTop : c ≠ ⊤)
    (hd : ∀ y ∈ K, c ≤ d y) :
    eLpNorm f (ENNReal.ofReal 2) (μ.restrict K) ≤
      c⁻¹ ^ (1 / ENNReal.ofReal 2).toReal *
        eLpNorm f (ENNReal.ofReal 2) ((μ.withDensity d).restrict K) := by
  let ν := (μ.withDensity d).restrict K
  have hmeasure : μ.restrict K ≤ c⁻¹ • ν := by
    rw [Measure.le_iff]
    intro A hA
    have hAK : MeasurableSet (A ∩ K) := hA.inter hK
    have hlin :
        ∫⁻ y in A ∩ K, (1 : ℝ≥0∞) ∂μ ≤
          ∫⁻ y in A ∩ K, c⁻¹ * (d y * 1) ∂μ := by
      apply MeasureTheory.setLIntegral_mono' hAK
      intro y hy
      have hmul : 1 ≤ c⁻¹ * d y := by
        calc
          1 = c⁻¹ * c := by rw [ENNReal.inv_mul_cancel hc₀ hcTop]
          _ ≤ c⁻¹ * d y := by
            gcongr
            exact hd y hy.2
      calc
        1 = 1 * 1 := by simp
        _ ≤ (c⁻¹ * d y) * 1 := by gcongr
        _ = c⁻¹ * (d y * 1) := by ac_rfl
    have hlin' : μ (A ∩ K) ≤ c⁻¹ * ∫⁻ y in A ∩ K, d y ∂μ := by
      calc
        μ (A ∩ K) = ∫⁻ y in A ∩ K, (1 : ℝ≥0∞) ∂μ := by
          rw [MeasureTheory.setLIntegral_one]
        _ ≤ ∫⁻ y in A ∩ K, c⁻¹ * (d y * 1) ∂μ := hlin
        _ = c⁻¹ * ∫⁻ y in A ∩ K, d y ∂μ := by
          simp only [mul_one]
          have hind : (A ∩ K).indicator (fun y => c⁻¹ * d y) =
              fun y => c⁻¹ * (A ∩ K).indicator d y := by
            funext y
            by_cases hy : y ∈ A ∩ K <;> simp [hy]
          rw [← MeasureTheory.lintegral_indicator hAK, hind,
            MeasureTheory.lintegral_const_mul' c⁻¹ _ (ENNReal.inv_ne_top.mpr hc₀),
            MeasureTheory.lintegral_indicator hAK]
    calc
      μ.restrict K A = μ (A ∩ K) := by rw [Measure.restrict_apply hA]
      _ ≤ c⁻¹ * ∫⁻ y in A ∩ K, d y ∂μ := hlin'
      _ = c⁻¹ * (μ.withDensity d).restrict K A := by
        rw [Measure.restrict_apply hA, withDensity_apply _ hAK]
      _ = (c⁻¹ • ν) A := by rw [Measure.smul_apply, smul_eq_mul]
  calc
    eLpNorm f (ENNReal.ofReal 2) (μ.restrict K) ≤
        eLpNorm f (ENNReal.ofReal 2) (c⁻¹ • ν) :=
      eLpNorm_mono_measure f hmeasure
    _ ≤ c⁻¹ ^ (1 / ENNReal.ofReal 2).toReal •
          eLpNorm f (ENNReal.ofReal 2) ν :=
      eLpNorm_smul_measure_le c⁻¹ f (ENNReal.ofReal 2) ν
    _ = _ := by simp [ν, smul_eq_mul]

private noncomputable def realificationHaarFactor (n : ℕ) : ℝ≥0 :=
  MeasureTheory.Measure.addHaarScalarFactor
    (Measure.map (toEuclidean (E := EuclideanSpace ℂ (Fin n)))
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))))
    (MeasureTheory.volume : Measure
      (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))))))

private lemma realificationHaarFactor_pos (n : ℕ) : 0 < realificationHaarFactor n := by
  let : (Measure.map (toEuclidean (E := EuclideanSpace ℂ (Fin n)))
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n)))).IsAddHaarMeasure :=
    ContinuousLinearEquiv.isAddHaarMeasure_map
      (toEuclidean (E := EuclideanSpace ℂ (Fin n)))
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n)))
  exact MeasureTheory.Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

private lemma map_toEuclidean_volume_eq_smul (n : ℕ) :
    Measure.map (toEuclidean (E := EuclideanSpace ℂ (Fin n)))
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) =
    (realificationHaarFactor n : ℝ≥0∞) • (MeasureTheory.volume : Measure
      (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))) := by
  let : (Measure.map (toEuclidean (E := EuclideanSpace ℂ (Fin n)))
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n)))).IsAddHaarMeasure :=
    ContinuousLinearEquiv.isAddHaarMeasure_map
      (toEuclidean (E := EuclideanSpace ℂ (Fin n)))
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n)))
  exact MeasureTheory.Measure.isAddLeftInvariant_eq_smul _ _

private theorem chartVolume_source_compl_zero
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M]
    (ω₀ : KahlerForm n M) (a : M) :
    ω₀.chartVolume a ((chartAt (EuclideanSpace ℂ (Fin n)) a).sourceᶜ) = 0 := by
  let chart := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a
  let S := (chartAt (EuclideanSpace ℂ (Fin n)) a).sourceᶜ
  let f : M → ℝ≥0∞ := S.indicator (fun _ => 1)
  have hS : MeasurableSet S :=
    (chartAt (EuclideanSpace ℂ (Fin n)) a).open_source.measurableSet.compl
  have hf : Measurable f := measurable_const.indicator hS
  have hformula := chartVolume_lintegral_formula ω₀ a hf
  have hmeasure : ω₀.chartVolume a S = ∫⁻ y, f y ∂ω₀.chartVolume a := by
    calc
      ω₀.chartVolume a S = ∫⁻ y in S, (1 : ℝ≥0∞) ∂ω₀.chartVolume a := by
        rw [MeasureTheory.setLIntegral_const]
        simp
      _ = ∫⁻ y, f y ∂ω₀.chartVolume a := by
        symm
        exact MeasureTheory.lintegral_indicator hS (fun _ => (1 : ℝ≥0∞))
  rw [hmeasure, hformula]
  calc
    _ = ∫⁻ z in chart.target, (0 : ℝ≥0∞) ∂MeasureTheory.volume := by
      apply MeasureTheory.setLIntegral_congr_fun
        (isOpen_extChartAt_target a).measurableSet
      intro z hz
      have hsymm : chart.symm z ∈ (chartAt (EuclideanSpace ℂ (Fin n)) a).source := by
        have h := chart.map_target hz
        rwa [CalabiYau.Tensor.Coordinates.extChartAt_source_eq_chartAt_source] at h
      have hzero : f (chart.symm z) = 0 := by simp [f, S, hsymm]
      change ENNReal.ofReal (ω₀.volumeDensityInChart a z) * f (chart.symm z) = 0
      rw [hzero, mul_zero]
    _ = 0 := by simp

private theorem chartVolume_le_global_volume
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M]
    (ω₀ : KahlerForm n M) (a : M) : ω₀.chartVolume a ≤ ω₀.volume := by
  have hsource : MeasurableSet ((chartAt (EuclideanSpace ℂ (Fin n)) a).source) :=
    (chartAt (EuclideanSpace ℂ (Fin n)) a).open_source.measurableSet
  have hzero : ω₀.chartVolume a
      ((chartAt (EuclideanSpace ℂ (Fin n)) a).sourceᶜ) = 0 :=
    chartVolume_source_compl_zero ω₀ a
  have hsource_ae : ∀ᵐ y ∂ω₀.chartVolume a,
      y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) a).source := by
    rw [ae_iff]
    change ω₀.chartVolume a ((chartAt (EuclideanSpace ℂ (Fin n)) a).sourceᶜ) = 0
    exact hzero
  have hsupport : (ω₀.chartVolume a).restrict
      (chartAt (EuclideanSpace ℂ (Fin n)) a).source = ω₀.chartVolume a :=
    Measure.restrict_eq_self_of_ae_mem hsource_ae
  have hrestrict := ω₀.chartVolume_restrict_chartSource_eq_volume_restrict a
  calc
    ω₀.chartVolume a = (ω₀.chartVolume a).restrict
        (chartAt (EuclideanSpace ℂ (Fin n)) a).source := hsupport.symm
    _ = ω₀.volume.restrict (chartAt (EuclideanSpace ℂ (Fin n)) a).source := hrestrict
    _ ≤ ω₀.volume := Measure.restrict_le_self

private theorem realVolume_restrict_le_scaled_chartMeasure
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M]
    [CompactSpace M] [SigmaCompactSpace M]
    (ω₀ : KahlerForm n M) (a : M)
    (K : Set (EuclideanSpace ℝ
      (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))))))
    (hKcompact : IsCompact K)
    (hK : K ⊆ Sobolev.Chart.chartTargetEuclid
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) a)
    (c : ℝ) (hc : 0 < c)
    (hden : ∀ y ∈ K, c ≤ ω₀.volumeDensityInChart a
      ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y)) :
    (MeasureTheory.volume : Measure
      (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))).restrict K ≤
      (ENNReal.ofReal c * (realificationHaarFactor n : ℝ≥0∞))⁻¹ •
        Measure.map (toEuclidean (E := EuclideanSpace ℂ (Fin n)))
          ((MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))).withDensity
            ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).target.indicator
              (fun z => ENNReal.ofReal (ω₀.volumeDensityInChart a z)))) := by
  classical
  let T := toEuclidean (E := EuclideanSpace ℂ (Fin n))
  let D := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).target
  let d : EuclideanSpace ℂ (Fin n) → ℝ≥0∞ :=
    fun z ↦ ENNReal.ofReal (ω₀.volumeDensityInChart a z)
  let ν : Measure (EuclideanSpace ℂ (Fin n)) :=
    (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))).withDensity (D.indicator d)
  let r : ℝ≥0∞ := ENNReal.ofReal c * (realificationHaarFactor n : ℝ≥0∞)
  have hKmeas : MeasurableSet K := hKcompact.measurableSet
  have hS (A : Set (EuclideanSpace ℝ
      (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))) : T ⁻¹' (A ∩ K) ⊆ D := by
    intro x hx
    change T x ∈ A ∩ K at hx
    obtain ⟨z, hzD, hzx⟩ := hK hx.2
    have hz_eq : z = x := T.injective hzx
    rw [← hz_eq]
    exact hzD
  have hdenS (A : Set (EuclideanSpace ℝ
      (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))) {x}
      (hx : x ∈ T ⁻¹' (A ∩ K)) : ENNReal.ofReal c ≤ d x := by
    change T x ∈ A ∩ K at hx
    have h := hden (T x) hx.2
    rw [T.symm_apply_apply x] at h
    exact ENNReal.ofReal_le_ofReal h
  have hfactorPos : 0 < (realificationHaarFactor n : ℝ≥0∞) := by
    exact_mod_cast realificationHaarFactor_pos n
  have hcENN : 0 < ENNReal.ofReal c := ENNReal.ofReal_pos.mpr hc
  have hrPos : 0 < r := ENNReal.mul_pos hcENN.ne' hfactorPos.ne'
  have hr0 : r ≠ 0 := hrPos.ne'
  have hrTop : r ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top
  apply Measure.le_iff.mpr
  intro A hA
  have hAK : MeasurableSet (A ∩ K) := hA.inter hKmeas
  let S := T ⁻¹' (A ∩ K)
  have hSmeas : MeasurableSet S := by
    dsimp [S]
    exact T.continuous.measurable hAK
  have hlin : ∫⁻ x in S, ENNReal.ofReal c
        ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) ≤
      ∫⁻ x in S, d x ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) :=
    MeasureTheory.setLIntegral_mono' hSmeas (fun x hx ↦ hdenS A hx)
  have hνS : ν S = ∫⁻ x in S, D.indicator d x
      ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := by
    change (MeasureTheory.volume.withDensity (D.indicator d)) S = _
    rw [MeasureTheory.withDensity_apply _ hSmeas]
  have hνS' : ν S = ∫⁻ x in S, d x
      ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := by
    rw [hνS]
    apply MeasureTheory.setLIntegral_congr_fun hSmeas
    intro x hx
    simp [hS A hx]
  have hconst : ∫⁻ x in S, ENNReal.ofReal c
        ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) =
      ENNReal.ofReal c * (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) S :=
    MeasureTheory.setLIntegral_const S (ENNReal.ofReal c)
  have hvolMap : (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) S =
      (realificationHaarFactor n : ℝ≥0∞) *
        (MeasureTheory.volume : Measure
          (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))) (A ∩ K) := by
    have h := congrArg (fun μ : Measure _ => μ (A ∩ K)) (map_toEuclidean_volume_eq_smul n)
    rw [Measure.map_apply T.continuous.measurable hAK,
      Measure.smul_apply, smul_eq_mul] at h
    simpa [S] using h
  have hmass : r * (MeasureTheory.volume : Measure
        (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))) (A ∩ K) ≤
      (Measure.map T ν) (A ∩ K) := by
    change r * (MeasureTheory.volume : Measure
          (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))) (A ∩ K) ≤
        (Measure.map T ((MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))).withDensity
          (D.indicator d))) (A ∩ K)
    rw [Measure.map_apply T.continuous.measurable hAK,
      MeasureTheory.withDensity_apply _ hSmeas]
    calc
      r * (MeasureTheory.volume : Measure
          (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))) (A ∩ K) =
          ENNReal.ofReal c * (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) S := by
            rw [hvolMap]
            simp [r, mul_assoc]
      _ = ∫⁻ x in S, ENNReal.ofReal c
            ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := hconst.symm
      _ ≤ ∫⁻ x in S, d x ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := hlin
      _ = ν S := hνS'.symm
      _ = ∫⁻ x in S, D.indicator d x
          ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := hνS
  have hfinal := (ENNReal.mul_le_iff_le_inv hr0 hrTop).mp hmass
  have hfinal' : (MeasureTheory.volume : Measure
      (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))) (A ∩ K) ≤
      r⁻¹ * (Measure.map T ν) A := by
    calc
      _ ≤ r⁻¹ * (Measure.map T ν) (A ∩ K) := hfinal
      _ ≤ r⁻¹ * (Measure.map T ν) A := by
        gcongr
        exact Set.inter_subset_left
  rw [Measure.restrict_apply hA, Measure.smul_apply, smul_eq_mul]
  change (MeasureTheory.volume : Measure
      (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))) (A ∩ K) ≤
    r⁻¹ * (Measure.map T ν) A
  exact hfinal'

/-- A positive lower bound for the chart density controls the local Euclidean `L²` norm of a
chart pullback by the global Kähler `L²` norm with a finite constant independent of the function.
The constant includes the Haar scaling of the chosen real-linear coordinate equivalence. -/
theorem chartPullback_eLpNorm_le_of_compact_density_lower
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M]
    [CompactSpace M] [SigmaCompactSpace M]
    (ω₀ : KahlerForm n M) (a : M)
    (K : Set (EuclideanSpace ℝ
      (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))))))
    (hKcompact : IsCompact K)
    (hK : K ⊆ Sobolev.Chart.chartTargetEuclid
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) a)
    (c : ℝ) (hc : 0 < c)
    (hden : ∀ y ∈ K, c ≤ ω₀.volumeDensityInChart a
      ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : M → ℝ), MemLp f (ENNReal.ofReal 2) ω₀.volume →
      eLpNorm
        (fun y => f ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).symm
          ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y)))
        (ENNReal.ofReal 2)
        ((MeasureTheory.volume : Measure (EuclideanSpace ℝ
          (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))).restrict K) ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal 2) ω₀.volume := by
  classical
  let T := toEuclidean (E := EuclideanSpace ℂ (Fin n))
  let chart := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a
  let D := chart.target
  let density : EuclideanSpace ℂ (Fin n) → ℝ≥0∞ :=
    fun z ↦ ENNReal.ofReal (ω₀.volumeDensityInChart a z)
  let μWeighted : Measure (EuclideanSpace ℂ (Fin n)) :=
    ((MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))).restrict D).withDensity density
  let μDensity : Measure (EuclideanSpace ℂ (Fin n)) :=
    (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))).withDensity
      (D.indicator density)
  let μReal : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))))) :=
    Measure.map T μDensity
  let r : ℝ≥0∞ := ENNReal.ofReal c * (realificationHaarFactor n : ℝ≥0∞)
  let q : ℝ≥0∞ := r⁻¹ ^ (1 / ENNReal.ofReal 2).toReal
  let C : ℝ := q.toReal
  have hμeq : μDensity = μWeighted := by
    exact MeasureTheory.withDensity_indicator
      (isOpen_extChartAt_target a).measurableSet density
  have hfactorPos : 0 < (realificationHaarFactor n : ℝ≥0∞) := by
    exact_mod_cast realificationHaarFactor_pos n
  have hcENN : 0 < ENNReal.ofReal c := ENNReal.ofReal_pos.mpr hc
  have hrPos : 0 < r := ENNReal.mul_pos hcENN.ne' hfactorPos.ne'
  have hr0 : r ≠ 0 := hrPos.ne'
  have hrTop : r ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top
  have hqTop : q ≠ ⊤ := by
    apply (ENNReal.rpow_lt_top_of_nonneg (by positivity)
      (ENNReal.inv_ne_top.mpr hr0)).ne
  have hq : ENNReal.ofReal C = q := by
    exact ENNReal.ofReal_toReal hqTop
  refine ⟨C, ?_, ?_⟩
  · exact ENNReal.toReal_nonneg
  · intro f hf
    let g : EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))) → ℝ :=
      fun y ↦ f (chart.symm (T.symm y))
    have hdom := realVolume_restrict_le_scaled_chartMeasure
      ω₀ a K hKcompact hK c hc hden
    have hmeasure : (MeasureTheory.volume : Measure
        (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))).restrict K ≤
        r⁻¹ • μReal := by
      simpa [r, μReal, μDensity, density, D, chart, T] using hdom
    have hchartle : ω₀.chartVolume a ≤ ω₀.volume :=
      chartVolume_le_global_volume ω₀ a
    have hchartStrong : AEStronglyMeasurable f (ω₀.chartVolume a) :=
      hf.aestronglyMeasurable.mono_measure hchartle
    have hsymm : AEMeasurable chart.symm
        ((MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))).restrict D) := by
      exact (continuousOn_extChartAt_symm a).aemeasurable
        (isOpen_extChartAt_target a).measurableSet
    have hsymm' : AEMeasurable chart.symm μWeighted :=
      hsymm.mono_ac (MeasureTheory.withDensity_absolutelyContinuous _ _)
    have hchartnorm :
        eLpNorm f (ENNReal.ofReal 2) (ω₀.chartVolume a) =
          eLpNorm (fun z ↦ f (chart.symm z)) (ENNReal.ofReal 2) μWeighted := by
      change eLpNorm f (ENNReal.ofReal 2) (Measure.map chart.symm μWeighted) = _
      exact eLpNorm_map_measure hchartStrong hsymm'
    have hcomplexStrong : AEStronglyMeasurable
        (fun z ↦ f (chart.symm z)) μWeighted :=
      hchartStrong.comp_aemeasurable hsymm'
    have hpres : MeasurePreserving T.symm (Measure.map T μWeighted) μWeighted := by
      refine ⟨T.symm.continuous.measurable, ?_⟩
      calc
        Measure.map T.symm (Measure.map T μWeighted) =
            Measure.map (T.symm ∘ T) μWeighted :=
          Measure.map_map T.symm.continuous.measurable T.continuous.measurable
        _ = μWeighted := by simp
    have hmapnorm : eLpNorm g (ENNReal.ofReal 2) (Measure.map T μDensity) =
        eLpNorm (fun z ↦ f (chart.symm z)) (ENNReal.ofReal 2) μWeighted := by
      rw [hμeq]
      change eLpNorm ((fun z ↦ f (chart.symm z)) ∘ T.symm)
        (ENNReal.ofReal 2) (Measure.map T μWeighted) = _
      exact eLpNorm_comp_measurePreserving hcomplexStrong hpres
    have hglobalnorm :
        eLpNorm g (ENNReal.ofReal 2) μReal ≤ eLpNorm f (ENNReal.ofReal 2) ω₀.volume := by
      change eLpNorm g (ENNReal.ofReal 2) (Measure.map T μDensity) ≤ _
      calc
        _ = eLpNorm (fun z ↦ f (chart.symm z)) (ENNReal.ofReal 2) μWeighted := hmapnorm
        _ = eLpNorm f (ENNReal.ofReal 2) (ω₀.chartVolume a) := hchartnorm.symm
        _ ≤ eLpNorm f (ENNReal.ofReal 2) ω₀.volume := eLpNorm_mono_measure f hchartle
    calc
      eLpNorm g (ENNReal.ofReal 2)
          ((MeasureTheory.volume : Measure
            (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))).restrict K)
          ≤ eLpNorm g (ENNReal.ofReal 2) (r⁻¹ • μReal) :=
            eLpNorm_mono_measure g hmeasure
      _ ≤ q * eLpNorm g (ENNReal.ofReal 2) μReal := by
        simpa [q, smul_eq_mul] using
          (eLpNorm_smul_measure_le r⁻¹ g (ENNReal.ofReal 2) μReal)
      _ ≤ q * eLpNorm f (ENNReal.ofReal 2) ω₀.volume := by
        gcongr
      _ = ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal 2) ω₀.volume := by rw [hq]

end KahlerForm
