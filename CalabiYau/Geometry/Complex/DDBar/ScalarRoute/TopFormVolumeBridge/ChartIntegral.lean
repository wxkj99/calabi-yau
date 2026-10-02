module

public import CalabiYau.Geometry.Kahler.Volume
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Real Bochner integration in a Kähler chart

This is the scalar chart-source formula for the already defined `ω.volume`,
not a new integral or a global Stokes theorem. Integrability is an explicit
hypothesis so no nonintegrable Bochner integral can silently stand for zero.

Source: Morita, *Geometry of Differential Forms*, §3.2(a), pp. 104–107;
the coordinate measure is realized here by `KahlerForm.chartVolume` and
`chartVolume_restrict_chartSource_eq_volume_restrict`. The analytic steps are
Mathlib's `integral_map` and `integral_withDensity_eq_integral_toReal_smul₀`.
-/

@[expose] public section

open scoped Manifold ContDiff
open MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M]

/-- Integrating a genuinely integrable real function over a chart source is
integration of its inverse-chart pullback times the positive chart density. -/
theorem integral_volume_chart_source (ω₀ : KahlerForm n M) (f : M → ℝ) (c : M)
    (hf : IntegrableOn f (chartAt (EuclideanSpace ℂ (Fin n)) c).source ω₀.volume) :
    (∫ y in (chartAt (EuclideanSpace ℂ (Fin n)) c).source, f y ∂ω₀.volume) =
      ∫ z in (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) c).target,
        ω₀.volumeDensityInChart c z * f
          ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) c).symm z)
          ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := by
  let chart := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) c
  let source := (chartAt (EuclideanSpace ℂ (Fin n)) c).source
  let d : EuclideanSpace ℂ (Fin n) → ENNReal :=
    fun z ↦ ENNReal.ofReal (ω₀.volumeDensityInChart c z)
  have hs : MeasurableSet source := (chartAt (EuclideanSpace ℂ (Fin n)) c).open_source.measurableSet
  have ht : MeasurableSet chart.target := isOpen_extChartAt_target c |>.measurableSet
  have hrestrict := ω₀.chartVolume_restrict_chartSource_eq_volume_restrict c
  have hfi : Integrable (source.indicator f) (ω₀.chartVolume c) := by
    rw [integrable_indicator_iff hs]
    change IntegrableOn f source (ω₀.chartVolume c)
    change Integrable f ((ω₀.chartVolume c).restrict source)
    rw [hrestrict]
    exact hf
  have hden_cont : ContinuousOn (ω₀.volumeDensityInChart c) chart.target := by
    change ContinuousOn
      (fun z ↦ (2 : ℝ) ^ n * (ω₀.metricInChart c z).det.re) chart.target
    have hdet : ContinuousOn (fun z ↦ (ω₀.metricInChart c z).det) chart.target := by
      classical
      simp_rw [Matrix.det_apply]
      exact continuousOn_finsetSum Finset.univ fun σ _ ↦
        continuousOn_const.smul <| continuousOn_finsetProd Finset.univ fun i _ ↦
          (ω₀.contDiffOn_metricInChart c (σ i) i).continuousOn
    exact continuousOn_const.mul <|
      Complex.continuous_re.continuousOn.comp hdet (fun _ _ ↦ Set.mem_univ _)
  have hd : AEMeasurable d (MeasureTheory.volume.restrict chart.target) := by
    exact (ENNReal.continuous_ofReal.continuousOn.comp hden_cont
      (fun _ _ ↦ Set.mem_univ _)).aemeasurable ht
  have hsymm : AEMeasurable chart.symm (MeasureTheory.volume.restrict chart.target) := by
    exact (continuousOn_extChartAt_symm c).aemeasurable ht
  have hsymm' : AEMeasurable chart.symm
      ((MeasureTheory.volume.restrict chart.target).withDensity d) :=
    hsymm.mono_ac (withDensity_absolutelyContinuous _ _)
  calc
    (∫ y in source, f y ∂ω₀.volume) =
        ∫ y, source.indicator f y ∂ω₀.chartVolume c := by
      rw [← integral_indicator hs]
      rw [integral_indicator hs]
      rw [integral_indicator hs]
      change ∫ y, f y ∂ω₀.volume.restrict source =
        ∫ y, f y ∂(ω₀.chartVolume c).restrict source
      rw [hrestrict]
    _ = ∫ z, source.indicator f (chart.symm z) ∂
        ((MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))).restrict chart.target).withDensity d := by
      rw [chartVolume]
      exact integral_map hsymm' hfi.aestronglyMeasurable
    _ = ∫ z in chart.target,
        (d z).toReal • source.indicator f (chart.symm z)
        ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := by
      simpa only [Function.comp_apply] using
        (integral_withDensity_eq_integral_toReal_smul₀ hd
          (Filter.Eventually.of_forall fun z ↦ ENNReal.ofReal_lt_top)
          (source.indicator f ∘ chart.symm))
    _ = ∫ z in chart.target, ω₀.volumeDensityInChart c z * f (chart.symm z)
        ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := by
      apply setIntegral_congr_fun ht
      intro z hz
      have hsource : chart.symm z ∈ source := by
        dsimp [source]
        simpa only [chart, extChartAt_source] using chart.map_target hz
      change (d z).toReal • source.indicator f (chart.symm z) =
        ω₀.volumeDensityInChart c z * f (chart.symm z)
      rw [Set.indicator_of_mem hsource]
      have hpos := ω₀.volumeDensityInChart_pos c hz
      have htoReal : (d z).toReal = ω₀.volumeDensityInChart c z := by
        change (ENNReal.ofReal (ω₀.volumeDensityInChart c z)).toReal = _
        rw [ENNReal.toReal_ofReal (le_of_lt hpos)]
      rw [htoReal, smul_eq_mul]

end KahlerForm
