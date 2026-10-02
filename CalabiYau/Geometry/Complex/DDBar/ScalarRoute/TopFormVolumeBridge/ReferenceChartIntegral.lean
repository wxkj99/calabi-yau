module

public import CalabiYau.Geometry.Complex.DDBar.ScalarRoute.TopFormVolumeBridge.ReferenceVolume
public import CalabiYau.Geometry.Complex.DDBar.ScalarRoute.TopFormVolumeBridge.ReferenceChartCoefficient
public import CalabiYau.Geometry.Complex.DDBar.ScalarRoute.SignedTopFormIntegral
import CalabiYau.Geometry.Complex.DDBar.ScalarRoute.TopFormVolumeBridge.ChartIntegral
public import CalabiYau.Geometry.Manifold.DifferentialForm.Stokes.LocalChart

/-!
# Actual weighted native/reference chart integral comparison

Morita, Geometry of Differential Forms, section 3.2(a), pp. 104-107.
The only local comparison needed by finite partition assembly is proved here.
Empty chart domains are treated without forcing sign +1. On nonempty positive
domains the reference coefficient fixes the sign. The actual fixed-centre
coefficient, explicit inverse point, measure-preserving e_n with multiplier 1,
and existing scalar Kahler chart-volume formula give the equality.
No Stokes, derivative, target-equality, arbitrary-density or global-functional
hypothesis, and no cutoff-transport construction, enters this comparison.
The chart-density determinant identity is assumed in the imported results.
-/

@[expose] public section

open scoped Manifold ContDiff
open MeasureTheory

noncomputable section

namespace KahlerForm

open CalabiYau.DifferentialForm HTopFormVolumeBridge

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

local instance referenceChartPiCharts : ChartedSpace (Fin (2 * n) → ℝ) M :=
  nativePiCharts (n := n) (M := M)
local instance referenceChartPiIsManifold : IsManifold 𝓘(ℝ, Fin (2 * n) → ℝ) ∞ M :=
  nativePiIsManifold

variable [MeasurableSpace M] [BorelSpace M] [T2Space M]
  [SigmaCompactSpace M] [CompactSpace M]

/-- This is the actual chart integral equality consumed by
finite partition assembly. Empty chart domains are allowed; support containment
then makes the cutoff zero. Reference positivity alone must not force sign +1
on an empty domain. The inverse-chart point is fixed by C.center throughout. -/
theorem integral_chart_weight_eq_native_signedDensity
    (ω₀ : KahlerForm n M)
    (C : OrientedLocalChart (2 * n) M)
    (hC : C.IsPositiveFor (referenceVolumeForm ω₀))
    (ρ : C^∞⟮𝓘(ℝ, Fin (2 * n) → ℝ), M; 𝓘(ℝ), ℝ⟯)
    (hρ : tsupport ρ ⊆ C.domain)
    (ξ : CalabiYau.DifferentialForm 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M (2 * n)) :
    (∫ y : Fin (2 * n) → ℝ, C.sign.val *
      (ρ ((extChartAt 𝓘(ℝ, Fin (2 * n) → ℝ) C.center).symm y) *
        chartTopCoefficient C.center (nativeToPiForms (2 * n) ξ) y)
      ∂(MeasureTheory.volume : Measure (Fin (2 * n) → ℝ))) =
    ∫ x, ρ x * ω₀.signedTopFormDensity
      (CalabiYau.DifferentialForm.toFormFieldLinearMap ξ) x ∂ω₀.volume := by
  classical
  by_cases hD : C.domain.Nonempty
  swap
  · have hzero : ∀ x : M, ρ x = 0 := by
      intro x
      by_contra hx
      exact hD ⟨x, hρ (subset_tsupport ρ hx)⟩
    simp only [hzero, zero_mul, mul_zero, integral_zero]
  let e := hTopPiToComplexEquiv n
  let target := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) C.center).target
  have htarget (z : Fin (2 * n) → ℝ) :
      z ∈ (extChartAt 𝓘(ℝ, Fin (2 * n) → ℝ) C.center).target ↔ e z ∈ target := by
    dsimp only [target]
    simp only [extChartAt_target]
    rw [nativePiChartAt]
    simp [e]
  obtain ⟨p, hp⟩ := hD
  have hpP : C.chart p ∈ (extChartAt 𝓘(ℝ, Fin (2 * n) → ℝ) C.center).target := by
    simpa [OrientedLocalChart.chart, extChartAt_target] using
      (chartAt (Fin (2 * n) → ℝ) C.center).map_source (C.domain_subset hp)
  have hpE := (htarget (C.chart p)).mp hpP
  have hcoeff := HTopFormVolumeBridge.nativeToPi_chartTopCoefficient_eq_nativeChartRep
    (bundledTopFormVolume ω₀) C.center hpP
  change chartTopCoefficient C.center (referenceVolumeForm ω₀) (C.chart p) = _ at hcoeff
  rw [bundledTopFormVolume, CalabiYau.DifferentialForm.toFormField_toDifferentialForm,
    ω₀.topFormVolume_chartCoeff C.center hpE] at hcoeff
  have hpos := ω₀.volumeDensityInChart_pos C.center hpE
  have hsigned := hC p hp
  rw [hcoeff] at hsigned
  have hsign : C.sign.val = 1 := by
    rcases C.sign.property with hs | hs
    · exact hs
    · rw [hs] at hsigned
      nlinarith
  let f : M → ℝ := fun x => ρ x * ω₀.signedTopFormDensity ξ.toFormField x
  have hf : Integrable f ω₀.volume := by
    have hcont := ρ.contMDiff.continuous.mul
      (ω₀.continuous_signedTopFormDensity ξ.isSmooth_toFormField)
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfzero : ∀ x : M, x ∉ (chartAt (EuclideanSpace ℂ (Fin n)) C.center).source → f x = 0 := by
    intro x hx
    have hρx : ρ x = 0 := by
      by_contra hn
      have hxs := C.domain_subset (hρ (subset_tsupport ρ hn))
      exact hx (by simpa only [nativePiChartAt_source] using hxs)
    simp only [f, hρx, zero_mul]
  let g : EuclideanSpace ℂ (Fin n) → ℝ := target.indicator (fun z =>
    ω₀.volumeDensityInChart C.center z *
      f ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) C.center).symm z))
  have hfun (z : Fin (2 * n) → ℝ) :
      C.sign.val *
        (ρ ((extChartAt 𝓘(ℝ, Fin (2 * n) → ℝ) C.center).symm z) *
          chartTopCoefficient C.center (nativeToPiForms (2 * n) ξ) z) = g (e z) := by
    rw [hsign, one_mul]
    exact native_chart_weight_coefficient_eq_density ω₀ C.center ρ ξ z
  let eM := e.toHomeomorph.toMeasurableEquiv
  have he : MeasurePreserving eM := by
    change MeasurePreserving e
    exact hTopPiToComplexEquiv_measurePreserving
  calc
    _ = ∫ z : Fin (2 * n) → ℝ, g (e z) ∂MeasureTheory.volume := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hfun
    _ = ∫ z : EuclideanSpace ℂ (Fin n), g z ∂MeasureTheory.volume := he.integral_comp' g
    _ = ∫ z in target, ω₀.volumeDensityInChart C.center z *
          f ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) C.center).symm z) ∂MeasureTheory.volume := by
      exact integral_indicator (isOpen_extChartAt_target C.center).measurableSet
    _ = ∫ x in (chartAt (EuclideanSpace ℂ (Fin n)) C.center).source, f x ∂ω₀.volume :=
      (ω₀.integral_volume_chart_source f C.center hf.integrableOn).symm
    _ = ∫ x, f x ∂ω₀.volume := setIntegral_eq_integral_of_forall_compl_eq_zero hfzero

end KahlerForm
