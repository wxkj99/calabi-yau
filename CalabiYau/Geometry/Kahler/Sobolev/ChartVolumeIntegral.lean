module

public import Mathlib.Topology.Defs.Basic
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import CalabiYau.Geometry.Kahler.Volume

/-!
# Chart-volume integration

The Kähler chart-volume measure integrates nonnegative measurable functions by its coordinate
volume density.
-/

@[expose] public section

open scoped Manifold ContDiff ENNReal
open MeasureTheory

namespace KahlerForm

theorem chartVolume_lintegral_formula {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [SigmaCompactSpace M] (ω₀ : KahlerForm n M) (x : M)
    {f : M → ℝ≥0∞} (hf : Measurable f) :
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
  have hvolumeDensity : ContinuousOn (ω₀.volumeDensityInChart x) c.target := by
    change ContinuousOn
      (fun z ↦ (2 : ℝ) ^ n * (ω₀.metricInChart x z).det.re) c.target
    have hdet : ContinuousOn (fun z ↦ (ω₀.metricInChart x z).det) c.target := by
      classical
      simp_rw [Matrix.det_apply]
      exact continuousOn_finsetSum Finset.univ fun σ _ ↦
        continuousOn_const.smul <| continuousOn_finsetProd Finset.univ fun i _ ↦
          (ω₀.contDiffOn_metricInChart x (σ i) i).continuousOn
    have hre : ContinuousOn (fun z ↦ (ω₀.metricInChart x z).det.re) c.target := by
      exact Complex.continuous_re.continuousOn.comp hdet (fun _ _ ↦ Set.mem_univ _)
    exact continuousOn_const.mul hre
  have hdcont : ContinuousOn d c.target := by
    exact ENNReal.continuous_ofReal.continuousOn.comp hvolumeDensity
      (fun _ _ ↦ Set.mem_univ _)
  have hd : AEMeasurable d μ := hdcont.aemeasurable (isOpen_extChartAt_target x).measurableSet
  have hsymm' : AEMeasurable c.symm (μ.withDensity d) :=
    hsymm.mono_ac (withDensity_absolutelyContinuous μ d)
  have hfg : AEMeasurable (fun z ↦ f (c.symm z)) μ :=
    (hf.aemeasurable : AEMeasurable f (μ.map c.symm)).comp_aemeasurable hsymm
  calc
    ∫⁻ y, f y ∂ω₀.chartVolume x = ∫⁻ z, f (c.symm z) ∂μ.withDensity d := by
      rw [chartVolume, MeasureTheory.lintegral_map' hf.aemeasurable hsymm']
    _ = ∫⁻ z, d z * f (c.symm z) ∂μ :=
      MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀ hd hfg
    _ = ∫⁻ z in c.target, d z * f (c.symm z) ∂MeasureTheory.volume := rfl

end KahlerForm
