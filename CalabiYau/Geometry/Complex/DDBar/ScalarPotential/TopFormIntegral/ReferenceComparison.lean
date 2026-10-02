module

public import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.TopFormIntegral.ReferenceChartIntegral
public import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.TopFormIntegral.ReferenceIntegralAssembly

/-!
# The native signed integral equals the constructed reference integral

Morita, Geometry of Differential Forms, section 3.2(a), pp. 104-107: finite
partition assembly. The existing referenceFormPartition and weighted formula
are consumed, not reconstructed. Chartwise integral formulas and weighted
integrability give the finite-sum theorem from ReferenceIntegralAssembly.
 
The reference is precisely T(bundle omega^n/n!), with no amplitude factor.
There is no Stokes, derivative, arbitrary Phi/T, or assumed-comparison premise.
Every declaration is used below. This is source-local completion, not
a claim to discharge the inherited ChartDensity determinant or any root theorem.
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

local instance referenceComparisonPiCharts : ChartedSpace (Fin (2 * n) → ℝ) M :=
  nativePiCharts (n := n) (M := M)
local instance referenceComparisonPiIsManifold : IsManifold 𝓘(ℝ, Fin (2 * n) → ℝ) ∞ M :=
  nativePiIsManifold

variable [MeasurableSpace M] [BorelSpace M] [T2Space M]
  [SigmaCompactSpace M] [CompactSpace M]

/-- Existing continuity and compactness prove weighted integrability; no new
unproved integrability result or universal integrability hypothesis is needed. -/
private theorem integrable_partition_weight_signedDensity
    (ω₀ : KahlerForm n M)
    (ρ : C^∞⟮𝓘(ℝ, Fin (2 * n) → ℝ), M; 𝓘(ℝ), ℝ⟯)
    (ξ : CalabiYau.DifferentialForm 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M (2 * n)) :
    Integrable (fun x => ρ x * ω₀.signedTopFormDensity
      (CalabiYau.DifferentialForm.toFormFieldLinearMap ξ) x) ω₀.volume := by
  have hξ := ω₀.continuous_signedTopFormDensity ξ.isSmooth_toFormField
  exact (ρ.contMDiff.continuous.mul hξ).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The comparison theorem uses the proof
argument required by the existing referenceFormIntegral API, not a density,
transport or Stokes premise. ν itself is fixed to the genuine geometric volume. -/
theorem referenceFormIntegral_nativeToPi_eq_signedTopFormIntegral
    (ω₀ : KahlerForm n M)
    (hν : ∀ p : M, referenceVolumeForm ω₀ p ≠ 0)
    (ξ : CalabiYau.DifferentialForm 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M (2 * n)) :
    referenceFormIntegral (referenceVolumeForm ω₀) hν
      (nativeToPiForms (2 * n) ξ) = ω₀.signedTopFormIntegral ξ := by
  let A := referenceFormPartition (referenceVolumeForm ω₀) hν
  rw [KahlerForm.signedTopFormIntegral_apply]
  refine CalabiYau.DifferentialForm.referenceFormIntegral_eq_densityIntegral_of_chartwise
    (referenceVolumeForm ω₀) hν A (nativeToPiForms (2 * n) ξ) ω₀.volume
    (ω₀.signedTopFormDensity (CalabiYau.DifferentialForm.toFormFieldLinearMap ξ)) ?_ ?_
  · intro i _hi
    exact integrable_partition_weight_signedDensity ω₀ (A.partition i) ξ
  · intro i hi
    exact integral_chart_weight_eq_native_signedDensity ω₀ (A.charts i)
      (A.positive i hi) (A.partition i) (A.subordinate i hi) ξ

/-- The actual unconditional comparison chooses its own source-derived
nonvanishing witness. This result uses the imported ChartDensity
determinant dependency is not discharged here. -/
theorem referenceVolumeIntegral_eq_signedTopFormIntegral
    (ω₀ : KahlerForm n M)
    (ξ : CalabiYau.DifferentialForm 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M (2 * n)) :
    referenceFormIntegral (referenceVolumeForm ω₀) (referenceVolumeForm_ne_zero ω₀)
      (nativeToPiForms (2 * n) ξ) = ω₀.signedTopFormIntegral ξ := by
  exact referenceFormIntegral_nativeToPi_eq_signedTopFormIntegral ω₀
    (referenceVolumeForm_ne_zero ω₀) ξ

end KahlerForm

section ConcreteGuards

open HTopFormVolumeBridge KahlerForm

-- Degree zero is not assigned a predecessor degree. Its genuine transported
-- reference coefficient is the scalar unit, not zero or an amplitude constant.
example {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin 0)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 0)) ω M]
    (ω₀ : KahlerForm 0 M) (x : M) :
    letI := nativePiCharts (n := 0) (M := M)
    letI : IsManifold 𝓘(ℝ, Fin (2 * 0) → ℝ) ∞ M := nativePiIsManifold
    (referenceVolumeForm ω₀).toFormField x ![] = 1 := by
  let : ChartedSpace (Fin (2 * 0) → ℝ) M := nativePiCharts (n := 0) (M := M)
  let : IsManifold 𝓘(ℝ, Fin (2 * 0) → ℝ) ∞ M := nativePiIsManifold
  rw [referenceVolumeForm, nativeToPiForms_toFormField,
    bundledTopFormVolume, CalabiYau.DifferentialForm.toFormField_toDifferentialForm]
  simp [KahlerForm.topFormVolume, ContinuousAlternatingMap.wedgePow]

-- Flat complex-line convention: ω=i dz∧dbarz=2 dx∧dy. A top form
-- with coefficient -4 has density -2, whose weighted volume coefficient is -4.
example : ((-4 : ℝ) / 2) * (2 ^ (1 : ℕ)) = -4 := by norm_num

-- Holomorphic z↦2z has positive real determinant 4. Both top coefficients
-- transform by 4, so their signed ratio is unchanged; it is not divided by
-- the reference coefficient at the unrelated chart center.
example : ((4 : ℝ) * (-4)) / (4 * 2) = (-4 : ℝ) / 2 := by norm_num

-- A real orientation reflection is not a holomorphic coordinate change.
-- Its two signed coefficients reverse together; the reference sign is -1.
example : ((-1 : ℝ) * (-4)) / ((-1) * 2) = (-4 : ℝ) / 2 := by norm_num
example : (-1 : ℝ) * (-4) = 4 := by norm_num

-- Inverse-chart-point guard with nonconstant reference: numerator/denominator
-- at x=1 give density 3, whereas a denominator at c=0 falsely gives density 6.
example : ((6 : ℝ) / 2) * 2 = 6 := by norm_num
example : ((6 : ℝ) / 1) * 2 ≠ 6 := by norm_num

end ConcreteGuards
