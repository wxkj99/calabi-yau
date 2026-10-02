module

public import CalabiYau.Analysis.Sobolev.Manifold.Rellich.OnManifold
public import CalabiYau.Geometry.Kahler.Volume
import CalabiYau.Geometry.Kahler.Sobolev.ChartVolumeIntegral

/-!
# Local chart `L²` membership from global Kähler `L²` membership

On a compact subset of a realified chart target, the smooth positive Kähler volume density has a
strictly positive lower bound. The intended conclusion transfers global `L²` membership to the
Euclidean chart pullback; `MemLp` includes the required `AEStronglyMeasurable` property.
-/

@[expose] public section

open scoped Manifold ContDiff ENNReal NNReal
open MeasureTheory Filter Topology

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M]

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma chartDensity_lower_bound_on_compact
    (ω₀ : KahlerForm n M) (a : M)
    (K : Set (EuclideanSpace ℝ
      (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))))))
    (hKcompact : IsCompact K)
    (hK : K ⊆ Sobolev.Chart.chartTargetEuclid
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) a) :
    ∃ c : ℝ, 0 < c ∧ ∀ y ∈ K,
      c ≤ ω₀.volumeDensityInChart a
        ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y) := by
  classical
  let c₀ := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a
  let g : EuclideanSpace ℝ
      (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))) → ℝ :=
    fun y ↦ ω₀.volumeDensityInChart a
      ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y)
  have hdet : ContinuousOn (fun z ↦ (ω₀.metricInChart a z).det) c₀.target := by
    simp_rw [Matrix.det_apply]
    exact continuousOn_finsetSum Finset.univ fun σ _ ↦
      continuousOn_const.smul <| continuousOn_finsetProd Finset.univ fun i _ ↦
        (ω₀.contDiffOn_metricInChart a (σ i) i).continuousOn
  have hden : ContinuousOn (ω₀.volumeDensityInChart a) c₀.target := by
    change ContinuousOn (fun z ↦ (2 : ℝ) ^ n * (ω₀.metricInChart a z).det.re) c₀.target
    have hre : ContinuousOn (fun z ↦ (ω₀.metricInChart a z).det.re) c₀.target :=
      Complex.continuous_re.continuousOn.comp hdet (fun _ _ ↦ Set.mem_univ _)
    exact continuousOn_const.mul hre
  have hKtarget : K ⊆
      (toEuclidean (E := EuclideanSpace ℂ (Fin n))) '' c₀.target := by
    simpa [Sobolev.Chart.chartTargetEuclid, c₀] using hK
  have hcont : ContinuousOn g K := by
    apply hden.comp (toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm.continuous.continuousOn
    intro y hy
    obtain ⟨z, hz, hzy⟩ := hKtarget hy
    have hsymm : (toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y = z := by
      rw [← hzy]
      exact (toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm_apply_apply z
    simpa [g, hsymm] using hz
  by_cases hne : K.Nonempty
  · obtain ⟨y₀, hy₀, hmin⟩ := hKcompact.exists_isMinOn hne hcont
    have hpos : 0 < g y₀ := by
      apply ω₀.volumeDensityInChart_pos a
      obtain ⟨z, hz, hzy⟩ := hKtarget hy₀
      have hsymm : (toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y₀ = z := by
        rw [← hzy]
        exact (toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm_apply_apply z
      have hz' : z ∈ c₀.target := by simpa [c₀] using hz
      rw [hsymm]
      exact hz'
    refine ⟨g y₀ / 2, by linarith, ?_⟩
    intro y hy
    have hle : g y₀ ≤ g y := hmin hy
    dsimp [g] at hpos ⊢
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro y hy
    exact (hne ⟨y, hy⟩).elim

private theorem chartVolume_source_compl_zero
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
      have hzero : f (chart.symm z) = 0 := by
        simp [f, S, hsymm]
      change ENNReal.ofReal (ω₀.volumeDensityInChart a z) * f (chart.symm z) = 0
      rw [hzero, mul_zero]
    _ = 0 := by simp

private theorem chartVolume_le_global_volume
    (ω₀ : KahlerForm n M) (a : M) :
    ω₀.chartVolume a ≤ ω₀.volume := by
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

private theorem chartPullback_memLp_weighted
    (ω₀ : KahlerForm n M) (u : M → ℝ)
    (hu : MemLp u (ENNReal.ofReal 2) ω₀.volume) (a : M) :
    MemLp (fun z => u ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).symm z))
      (ENNReal.ofReal 2)
      (((MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))).restrict
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).target).withDensity
        (fun z => ENNReal.ofReal (ω₀.volumeDensityInChart a z))) := by
  classical
  let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a
  let μ : Measure (EuclideanSpace ℂ (Fin n)) :=
    (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))).restrict c.target
  let d : EuclideanSpace ℂ (Fin n) → ℝ≥0∞ :=
    fun z ↦ ENNReal.ofReal (ω₀.volumeDensityInChart a z)
  let ν : Measure (EuclideanSpace ℂ (Fin n)) := μ.withDensity d
  have hsymm : AEMeasurable c.symm μ := by
    exact (continuousOn_extChartAt_symm a).aemeasurable
      (isOpen_extChartAt_target a).measurableSet
  have hsymm' : AEMeasurable c.symm ν :=
    hsymm.mono_ac (withDensity_absolutelyContinuous μ d)
  have hνtarget : ∀ᵐ z ∂ν, z ∈ c.target := by
    have hμtarget : ∀ᵐ z ∂μ, z ∈ c.target :=
      ae_restrict_mem (isOpen_extChartAt_target a).measurableSet
    exact hμtarget.filter_mono (withDensity_absolutelyContinuous μ d).ae_le
  let e : EuclideanSpace ℂ (Fin n) → M :=
    c.target.piecewise c.symm (fun _ => a)
  have hemeas : Measurable e := by
    exact (continuousOn_extChartAt_symm a).measurable_piecewise
      continuousOn_const (isOpen_extChartAt_target a).measurableSet
  have heq : e =ᵐ[ν] c.symm := by
    filter_upwards [hνtarget] with z hz
    change c.target.piecewise c.symm (fun _ => a) z = c.symm z
    exact Set.piecewise_eq_of_mem _ _ _ hz
  have hmap : Measure.map e ν = ω₀.chartVolume a := by
    change Measure.map e ν = Measure.map c.symm ν
    exact Measure.map_congr heq
  have hMP : MeasurePreserving e ν (ω₀.chartVolume a) := ⟨hemeas, hmap⟩
  have huChart : MemLp u (ENNReal.ofReal 2) (ω₀.chartVolume a) := by
    apply hu.mono_measure
    exact chartVolume_le_global_volume ω₀ a
  have hcomp := huChart.comp_measurePreserving hMP
  have heqf : (u ∘ e) =ᵐ[ν] fun z => u (c.symm z) := by
    filter_upwards [hνtarget] with z hz
    change u (c.target.piecewise c.symm (fun _ => a) z) = u (c.symm z)
    rw [Set.piecewise_eq_of_mem _ _ _ hz]
  exact (memLp_congr_ae heqf).mp hcomp

private noncomputable def realificationHaarFactor (n : ℕ) : ℝ≥0 :=
  Measure.addHaarScalarFactor
    (Measure.map (toEuclidean (E := EuclideanSpace ℂ (Fin n)))
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))))
    (MeasureTheory.volume : Measure
      (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))))))

private theorem realificationHaarFactor_pos (n : ℕ) :
    0 < realificationHaarFactor n := by
  let : (Measure.map (toEuclidean (E := EuclideanSpace ℂ (Fin n)))
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n)))).IsAddHaarMeasure :=
    ContinuousLinearEquiv.isAddHaarMeasure_map
      (toEuclidean (E := EuclideanSpace ℂ (Fin n)))
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n)))
  exact Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

private theorem map_toEuclidean_volume_eq_smul (n : ℕ) :
    Measure.map (toEuclidean (E := EuclideanSpace ℂ (Fin n)))
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) =
    (realificationHaarFactor n : ℝ≥0∞) • (MeasureTheory.volume : Measure
      (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))) := by
  let : (Measure.map (toEuclidean (E := EuclideanSpace ℂ (Fin n)))
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n)))).IsAddHaarMeasure :=
    ContinuousLinearEquiv.isAddHaarMeasure_map
      (toEuclidean (E := EuclideanSpace ℂ (Fin n)))
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n)))
  exact Measure.isAddLeftInvariant_eq_smul _ _

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M] in
private theorem realVolume_restrict_le_scaled_chartMeasure
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
      (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))) :
      T ⁻¹' (A ∩ K) ⊆ D := by
    intro x hx
    change T x ∈ A ∩ K at hx
    obtain ⟨z, hzD, hzx⟩ := hK hx.2
    have hz_eq : z = x := T.injective hzx
    rw [← hz_eq]
    exact hzD
  have hdenS (A : Set (EuclideanSpace ℝ
      (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))) {x} (hx : x ∈ T ⁻¹' (A ∩ K)) :
      ENNReal.ofReal c ≤ d x := by
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
      r * (MeasureTheory.volume : MeasureTheory.Measure
          (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))) (A ∩ K) =
          ENNReal.ofReal c * (MeasureTheory.volume : Measure
            (EuclideanSpace ℂ (Fin n))) S := by
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

/-- The local measure-theoretic transfer, isolated from the compact density bound. `MemLp`
includes the required `AEStronglyMeasurable` property for the chart pullback. -/
private theorem chartPullback_memLp_of_density_lower_bound
    (ω₀ : KahlerForm n M) (u : M → ℝ)
    (hu : MemLp u (ENNReal.ofReal 2) ω₀.volume)
    (a : M)
    (K : Set (EuclideanSpace ℝ
      (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))))))
    (hKcompact : IsCompact K)
    (hK : K ⊆ Sobolev.Chart.chartTargetEuclid
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) a)
    (c : ℝ) (hc : 0 < c)
    (hden : ∀ y ∈ K,
      c ≤ ω₀.volumeDensityInChart a
        ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y)) :
    MemLp (fun y => u ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).symm
      ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y)))
      (ENNReal.ofReal 2)
      (MeasureTheory.volume.restrict K) := by
  let chart := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a
  let D := chart.target
  let density : EuclideanSpace ℂ (Fin n) → ℝ≥0∞ :=
    fun z ↦ ENNReal.ofReal (ω₀.volumeDensityInChart a z)
  let μWeighted : Measure (EuclideanSpace ℂ (Fin n)) :=
    ((MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))).restrict D).withDensity density
  let μDensity : Measure (EuclideanSpace ℂ (Fin n)) :=
    (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))).withDensity
      (D.indicator density)
  let T := toEuclidean (E := EuclideanSpace ℂ (Fin n))
  have hweighted : MemLp (fun z => u (chart.symm z)) (ENNReal.ofReal 2) μWeighted := by
    simpa [μWeighted, density, chart, D] using chartPullback_memLp_weighted ω₀ u hu a
  have hμeq : μDensity = μWeighted := by
    exact withDensity_indicator (isOpen_extChartAt_target a).measurableSet density
  have hpres : MeasurePreserving T.symm (Measure.map T μWeighted) μWeighted := by
    refine ⟨T.symm.continuous.measurable, ?_⟩
    calc
      Measure.map T.symm (Measure.map T μWeighted) = Measure.map (T.symm ∘ T) μWeighted :=
        Measure.map_map T.symm.continuous.measurable T.continuous.measurable
      _ = μWeighted := by simp
  have hreal : MemLp (fun y => u (chart.symm (T.symm y))) (ENNReal.ofReal 2)
      (Measure.map T μWeighted) := by
    change MemLp ((fun z => u (chart.symm z)) ∘ T.symm) (ENNReal.ofReal 2)
      (Measure.map T μWeighted)
    exact hweighted.comp_measurePreserving hpres
  have hmapEq : Measure.map T μDensity = Measure.map T μWeighted :=
    congrArg (Measure.map T) hμeq
  have hreal' : MemLp (fun y => u (chart.symm (T.symm y))) (ENNReal.ofReal 2)
      (Measure.map T μDensity) := by
    rw [hmapEq]
    exact hreal
  have hdom := realVolume_restrict_le_scaled_chartMeasure
    ω₀ a K hKcompact hK c hc hden
  let r : ℝ≥0∞ := ENNReal.ofReal c * (realificationHaarFactor n : ℝ≥0∞)
  have hcENN : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  have hqENN : (realificationHaarFactor n : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (ne_of_gt (realificationHaarFactor_pos n))
  have hrENN : r ≠ 0 := mul_ne_zero hcENN hqENN
  have hscaled : MemLp (fun y => u (chart.symm (T.symm y))) (ENNReal.ofReal 2)
      (r⁻¹ • Measure.map T μDensity) :=
    hreal'.smul_measure (ENNReal.inv_ne_top.mpr hrENN)
  exact hscaled.mono_measure (by simpa [r, μDensity, density, D, chart, T] using hdom)

/-- Global `L²` membership with respect to Kähler volume implies `L²` membership of the pullback
of `u` to every compact subset of a realified chart target. -/
theorem chartLocal_memLp_of_global_memLp
    (ω₀ : KahlerForm n M) (u : M → ℝ)
    (hu : MemLp u (ENNReal.ofReal 2) ω₀.volume)
    (a : M)
    (K : Set (EuclideanSpace ℝ
      (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))))))
    (hKcompact : IsCompact K)
    (hK : K ⊆ Sobolev.Chart.chartTargetEuclid
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) a) :
    MemLp (fun y => u ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).symm
      ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y)))
      (ENNReal.ofReal 2)
      (MeasureTheory.volume.restrict K) := by
  obtain ⟨c, hc, hden⟩ := chartDensity_lower_bound_on_compact ω₀ a K hKcompact hK
  exact chartPullback_memLp_of_density_lower_bound ω₀ u hu a K hKcompact hK c hc hden

end KahlerForm
