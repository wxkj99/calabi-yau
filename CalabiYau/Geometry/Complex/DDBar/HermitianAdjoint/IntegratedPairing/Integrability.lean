module

public import CalabiYau.Geometry.Complex.DDBar.HermitianAdjoint.IntegratedPairing.PairingContinuity
public import CalabiYau.Geometry.Riemannian.Volume.Properties
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integrability of smooth form pairings on compact Riemannian manifolds

We integrate with the canonical differential-geometry Riemannian volume measure of the *supplied* metric; no
Kähler-to-Riemannian volume comparison or Hilbert completion is used.
Source: Morita, *Geometry of Differential Forms*, Ch. 4 §4.2.
-/

@[expose] public section

open scoped Manifold ContDiff
open MeasureTheory

namespace ComplexFormField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

local instance : MeasurableSpace M := borel M
local instance : BorelSpace M := ⟨rfl⟩

/-- The pointwise Hermitian pairing of smooth forms is Bochner-integrable for the finite canonical
Riemannian volume of a compact manifold. -/
theorem integrable_pointwiseHermitianInner
    (g : CalabiYau.SmoothRiemannianMetric 𝓘(ℝ, E) M) (k : ℕ)
    (α β : ComplexFormField E M k) (hα : α.IsSmooth) (hβ : β.IsSmooth) :
    Integrable (fun x : M => pointwiseHermitianInner g k x α β)
      (CalabiYau.RiemannianVolume.riemannianVolumeMeasure
        (I := 𝓘(ℝ, E)) (M := M) g) := by
  have hfinite : IsFiniteMeasure (CalabiYau.RiemannianVolume.riemannianVolumeMeasure
      (I := 𝓘(ℝ, E)) (M := M) g) :=
    CalabiYau.RiemannianVolume.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  let := hfinite
  exact (continuous_pointwiseHermitianInner g k α β hα hβ).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

end ComplexFormField
