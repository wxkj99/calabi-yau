module

public import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.TopFormIntegral.NativeModel
public import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.TopFormIntegral.Basic
import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.TopFormIntegral.ChartDensity
import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.IntegralZero.ExactWedgePower

/-!
# The actual transported Kahler reference volume form

Morita, Geometry of Differential Forms, section 3.2(a), pp. 104-107; Wells,
Differential Analysis on Complex Manifolds, V section 1, pp. 157-159.
The reference is exactly geometric T applied to bundled omega^n/n!, not an
amplitude-adjusted reference or an arbitrary linear transport. Smoothness and
nonvanishing are proved. Nonvanishing imports the existing ChartDensity
determinant coefficient identity.
No measurable, T2, compact, connected, positive-dimension or Stokes premise is
required for the reference construction.
-/

@[expose] public section

open scoped Manifold ContDiff

noncomputable section

namespace KahlerForm

open CalabiYau.DifferentialForm HTopFormVolumeBridge

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- The existing raw wedge-power smoothness theorem bundles the genuine volume field. -/
theorem isSmooth_topFormVolume (ω₀ : KahlerForm n M) : ω₀.topFormVolume.IsSmooth := by
  change (((Nat.factorial n : ℝ)⁻¹) • FormField.wedgePow ω₀.toFormField n).IsSmooth
  exact (ω₀.isSmooth.wedgePow n).smul ((Nat.factorial n : ℝ)⁻¹)

/-- No new native wedge or normalization is introduced. -/
def bundledTopFormVolume (ω₀ : KahlerForm n M) :
    CalabiYau.DifferentialForm 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M (2 * n) :=
  ω₀.topFormVolume.toDifferentialForm (isSmooth_topFormVolume ω₀)

local instance referenceVolumePiCharts : ChartedSpace (Fin (2 * n) → ℝ) M :=
  nativePiCharts (n := n) (M := M)
local instance referenceVolumePiIsManifold : IsManifold 𝓘(ℝ, Fin (2 * n) → ℝ) ∞ M :=
  nativePiIsManifold

/-- Exactly T(ωⁿ/n!), where T is geometric pullback along the two-model identity. -/
def referenceVolumeForm (ω₀ : KahlerForm n M) :
    CalabiYau.DifferentialForm 𝓘(ℝ, Fin (2 * n) → ℝ) M (2 * n) :=
  nativeToPiForms (2 * n) (bundledTopFormVolume ω₀)

/-- The source coefficient positivity and the invertibility of e prove actual
nonvanishing. This imports the c02-owned ChartDensity determinant hole; it does
not duplicate or discharge that algebra. -/
theorem referenceVolumeForm_ne_zero (ω₀ : KahlerForm n M) (p : M) :
    referenceVolumeForm ω₀ p ≠ 0 := by
  intro hz
  have hf : (referenceVolumeForm ω₀).toFormField p = 0 := by
    unfold CalabiYau.DifferentialForm.toFormField
    rw [hz]
    ext v
    rfl
  rw [referenceVolumeForm, nativeToPiForms_toFormField, bundledTopFormVolume,
    CalabiYau.DifferentialForm.toFormField_toDifferentialForm] at hf
  have hzero : ω₀.topFormVolume p = 0 := by
    ext v
    have hv := congrArg (fun α => α (fun i => (hTopPiToComplexEquiv n).symm (v i))) hf
    simpa only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousLinearEquiv.coe_coe, Function.comp_def,
      ContinuousLinearEquiv.apply_symm_apply, ContinuousAlternatingMap.coe_zero,
      Pi.zero_apply] using hv
  have hp : 0 < ContinuousAlternatingMap.topFormCoeff (ω₀.topFormVolume p) := by
    rw [← FormField.chartRep_self ω₀.topFormVolume p,
      ω₀.topFormVolume_chartCoeff p (mem_extChartAt_target p)]
    rw [KahlerForm.volumeDensityInChart]
    exact mul_pos (by positivity)
      (RCLike.pos_iff.mp (ω₀.posDef_metricInChart p (mem_extChartAt_target p)).det_pos).1
  rw [hzero] at hp
  simp only [ContinuousAlternatingMap.topFormCoeff,
    ContinuousAlternatingMap.coe_zero, Pi.zero_apply, lt_self_iff_false] at hp

end KahlerForm
