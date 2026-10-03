module

public import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.TopFormIntegral.NativeChartCoefficient
public import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.TopFormIntegral.Basic
public import CalabiYau.Geometry.Kahler.Volume
import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.TopFormIntegral.ChartDensity

/-!
# Weighted reference chart coefficients and the actual Kähler density

Morita, *Geometry of Differential Forms*, §3.2(a), pp. 104–107.
This is the pointwise integrand identity used by ReferenceChartIntegral, with
canonical native-to-Pi transport, a fixed chart centre, and the target indicator.
Neither smoothness nor support of the weight is needed until integration.
The actual Kähler coefficient normalization is inherited from ChartDensity;
this file does not discharge that determinant proof.
-/

@[expose] public section

open scoped Manifold ContDiff
open CalabiYau.DifferentialForm HTopFormVolumeBridge

noncomputable section

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

local instance referenceCoefficientPiCharts : ChartedSpace (Fin (2 * n) → ℝ) M :=
  nativePiCharts (n := n) (M := M)
local instance referenceCoefficientPiIsManifold : IsManifold 𝓘(ℝ, Fin (2 * n) → ℝ) ∞ M :=
  nativePiIsManifold

/-- The weighted coefficient of the actual transported form is the target-indicated
native density integrand. Both inverse points use the same fixed centre. -/
theorem native_chart_weight_coefficient_eq_density
    (ω₀ : KahlerForm n M) (c : M) (ρ : M → ℝ)
    (ξ : CalabiYau.DifferentialForm 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M (2 * n))
    (z : Fin (2 * n) → ℝ) :
    ρ ((extChartAt 𝓘(ℝ, Fin (2 * n) → ℝ) c).symm z) *
        chartTopCoefficient c (nativeToPiForms (2 * n) ξ) z =
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) c).target.indicator
        (fun w => ω₀.volumeDensityInChart c w *
          (ρ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) c).symm w) *
            ω₀.signedTopFormDensity ξ.toFormField
              ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) c).symm w)))
        (hTopPiToComplexEquiv n z) := by
  let e := hTopPiToComplexEquiv n
  have htarget :
      z ∈ (extChartAt 𝓘(ℝ, Fin (2 * n) → ℝ) c).target ↔
        e z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) c).target := by
    simp only [extChartAt_target]
    rw [nativePiChartAt]
    simp [e]
  have hpoint :
      (extChartAt 𝓘(ℝ, Fin (2 * n) → ℝ) c).symm z =
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) c).symm (e z) := by
    change (chartAt (Fin (2 * n) → ℝ) c).symm z =
      (chartAt (EuclideanSpace ℂ (Fin n)) c).symm (e z)
    rw [nativePiChartAt]
    rfl
  by_cases hz : z ∈ (extChartAt 𝓘(ℝ, Fin (2 * n) → ℝ) c).target
  · have hzE := htarget.mp hz
    dsimp only [e] at hzE
    rw [nativeToPi_chartTopCoefficient_eq_nativeChartRep ξ c hz,
      ω₀.topFormCoeff_chartRep_eq_density_mul ξ.toFormField c hzE,
      ω₀.topFormVolume_chartCoeff c hzE, hpoint]
    simp only [Set.indicator_of_mem hzE]
    ring
  · have hzE : e z ∉ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) c).target :=
      fun h => hz (htarget.mpr h)
    dsimp only [e] at hzE
    simp only [chartTopCoefficient, ite_eq_right hz, mul_zero,
      Set.indicator_of_notMem hzE]

end KahlerForm
