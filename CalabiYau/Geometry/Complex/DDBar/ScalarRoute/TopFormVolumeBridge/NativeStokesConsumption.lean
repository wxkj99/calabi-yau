module

public import CalabiYau.Geometry.Complex.DDBar.ScalarRoute.SignedTopFormIntegral
import CalabiYau.Geometry.Complex.DDBar.ScalarRoute.TopFormVolumeBridge.ReferenceComparison
import CalabiYau.Geometry.Manifold.DifferentialForm.Stokes.Global.ConstructedStokes

/-!
# Consumption of constructed Stokes by the native Kähler volume

Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 16.11,
pp. 411–414; Wells, *Differential Analysis on Complex Manifolds*, V §1,
pp. 157–159, with volume `ωⁿ/n!`.

This theorem applies the constructed real-Pi top-form integral and
Stokes theorem. Its reference is the actual `referenceVolumeForm ω₀`, namely
`nativeToPiForms (2 * n) (bundledTopFormVolume ω₀)`. The published comparison
returns to the existing native `signedTopFormIntegral`; no new functional,
arbitrary transport, comparison premise or Stokes hypothesis is introduced.

The model dimension is `2 * n`, independently of the syntactic degree of the
primitive. Eliminate positive dimension as a successor before invoking the
real-Pi Stokes theorem; casting only the form degree does not cast the atlas.
The displayed cast preserves the ordered Fin slots and has no permutation sign.
In dimension zero, separate algebraic arguments apply.
-/

@[expose] public section

open scoped Manifold ContDiff
open CalabiYau.DifferentialForm HTopFormVolumeBridge

noncomputable section

private theorem reference_stokes_cast {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (Fin d → ℝ) M] [IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ M]
    [BoundarylessManifold 𝓘(ℝ, Fin d → ℝ) M] [T2Space M] [CompactSpace M]
    (hd : 0 < d) {k : ℕ} (hdegree : k + 1 = d)
    (ν : CalabiYau.DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d)
    (hν : ∀ p : M, ν p ≠ 0)
    (η : CalabiYau.DifferentialForm 𝓘(ℝ, Fin d → ℝ) M k) :
    referenceFormIntegral ν hν
      (cast (congrArg (CalabiYau.DifferentialForm 𝓘(ℝ, Fin d → ℝ) M)
        hdegree) (exteriorDerivative η)) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  have hk : k = m := Nat.add_right_cancel hdegree
  subst k
  simpa only [cast_eq] using referenceFormIntegral_stokes ν hν η

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

private theorem transport_degree_cast {k l : ℕ} (h : k = l)
    (η : CalabiYau.DifferentialForm 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M k) :
    letI := nativePiCharts (n := n) (M := M)
    letI : IsManifold 𝓘(ℝ, Fin (2 * n) → ℝ) ∞ M := nativePiIsManifold
    nativeToPiForms l
      (cast (congrArg (CalabiYau.DifferentialForm
        𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M) h) η) =
      cast (congrArg (CalabiYau.DifferentialForm 𝓘(ℝ, Fin (2 * n) → ℝ) M) h)
        (nativeToPiForms k η) := by
  cases h
  rfl

variable [MeasurableSpace M] [BorelSpace M] [T2Space M]
  [SigmaCompactSpace M] [CompactSpace M]

/-- The actual native signed integral vanishes on the degree-cast derivative
of an actual bundled primitive. The degree equality covers both scalar-route
primitives without changing the native or transported manifold model. -/
theorem signedTopFormIntegral_cast_exteriorDerivative_eq_zero
    (ω₀ : KahlerForm n M) (hn : 0 < n) {k : ℕ}
    (hdegree : k + 1 = 2 * n)
    (η : CalabiYau.DifferentialForm 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M k) :
    ω₀.signedTopFormIntegral
      (cast (congrArg
        (CalabiYau.DifferentialForm 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M)
        hdegree) (CalabiYau.DifferentialForm.exteriorDerivative η)) = 0 := by
  let : ChartedSpace (Fin (2 * n) → ℝ) M := nativePiCharts (n := n) (M := M)
  let : IsManifold 𝓘(ℝ, Fin (2 * n) → ℝ) ∞ M := nativePiIsManifold
  rw [← referenceVolumeIntegral_eq_signedTopFormIntegral]
  rw [transport_degree_cast hdegree, nativeToPiForms_exteriorDerivative]
  exact reference_stokes_cast (by omega : 0 < 2 * n) hdegree
    (referenceVolumeForm ω₀) (referenceVolumeForm_ne_zero ω₀)
    (nativeToPiForms k η)

end KahlerForm
