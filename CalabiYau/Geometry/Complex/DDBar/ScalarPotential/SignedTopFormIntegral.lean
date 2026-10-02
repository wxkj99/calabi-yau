module

public import CalabiYau.Geometry.Complex.Forms.DifferentialForm
public import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.TopFormIntegral.DensityContinuity

/-!
# The native signed integral of smooth Kähler top forms

The integral is a real linear map on the project's bundled smooth differential
forms, not a Hilbert-space completion or a measure obtained by taking an absolute
value of a form. Its integrand is the signed coefficient relative to the actual
positive top form `ωⁿ/n!`, and its measure is the existing `KahlerForm.volume`.

Smoothness is supplied by the proved `FormFieldBridge`. Integrability is derived
from density continuity, compactness, and the finite Kähler volume instance;
it is not an assumed universal integrability or Stokes hypothesis. Both additive
summands are integrable before Bochner integral additivity is used.

This definition includes complex dimension zero. It does not assert a
predecessor-degree Stokes formula there, a global Stokes theorem in positive
dimension, or a change of the manifold's charted-space instance.

Sources: Morita, *Geometry of Differential Forms*, §3.2(a), pp. 104–107;
Wells, *Differential Analysis on Complex Manifolds*, V §1, pp. 157–159.
-/

@[expose] public section

open scoped Manifold ContDiff
open MeasureTheory ContinuousAlternatingMap

noncomputable section

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- Signed density, as a real linear map on actual unbundled top forms. -/
def signedTopFormDensityLinearMap (ω₀ : KahlerForm n M) :
    FormField (EuclideanSpace ℂ (Fin n)) M (2 * n) →ₗ[ℝ] (M → ℝ) where
  toFun := ω₀.signedTopFormDensity
  map_add' Θ Ψ := by
    funext x
    simp [signedTopFormDensity, topFormCoeff, add_div]
  map_smul' c Θ := by
    funext x
    simp [signedTopFormDensity, topFormCoeff, mul_div_assoc]

/-- The geometric signed-density map on the existing smooth bundled-form domain. -/
def bundledSignedTopFormDensityLinearMap (ω₀ : KahlerForm n M) :
    CalabiYau.DifferentialForm 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M (2 * n) →ₗ[ℝ] (M → ℝ) :=
  ω₀.signedTopFormDensityLinearMap.comp CalabiYau.DifferentialForm.toFormFieldLinearMap

@[simp] theorem bundledSignedTopFormDensityLinearMap_apply (ω₀ : KahlerForm n M)
    (θ : CalabiYau.DifferentialForm 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M (2 * n)) :
    ω₀.bundledSignedTopFormDensityLinearMap θ =
      ω₀.signedTopFormDensity (CalabiYau.DifferentialForm.toFormFieldLinearMap θ) := rfl

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-- Every bundled smooth top form has integrable actual signed Kähler density
on a compact manifold. This is derived from smoothness, not a hypothesis. -/
theorem integrable_signedTopFormDensity_toFormField (ω₀ : KahlerForm n M)
    (θ : CalabiYau.DifferentialForm 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M (2 * n)) :
    Integrable (ω₀.signedTopFormDensity
      (CalabiYau.DifferentialForm.toFormFieldLinearMap θ)) ω₀.volume := by
  have hθ : (CalabiYau.DifferentialForm.toFormFieldLinearMap θ).IsSmooth :=
    θ.isSmooth_toFormField
  have hcont := ω₀.continuous_signedTopFormDensity hθ
  exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The actual signed top-form integral, real-linear on all project smooth top forms. -/
def signedTopFormIntegral (ω₀ : KahlerForm n M) :
    CalabiYau.DifferentialForm 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M (2 * n) →ₗ[ℝ] ℝ where
  toFun θ := ∫ x, (ω₀.bundledSignedTopFormDensityLinearMap θ) x ∂ω₀.volume
  map_add' θ η := by
    rw [map_add]
    exact integral_add (ω₀.integrable_signedTopFormDensity_toFormField θ)
      (ω₀.integrable_signedTopFormDensity_toFormField η)
  map_smul' c θ := by
    rw [map_smul]
    exact integral_smul c (ω₀.bundledSignedTopFormDensityLinearMap θ)

@[simp] theorem signedTopFormIntegral_apply (ω₀ : KahlerForm n M)
    (θ : CalabiYau.DifferentialForm 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M (2 * n)) :
    ω₀.signedTopFormIntegral θ = ∫ x, ω₀.signedTopFormDensity
      (CalabiYau.DifferentialForm.toFormFieldLinearMap θ) x ∂ω₀.volume := rfl

end KahlerForm
