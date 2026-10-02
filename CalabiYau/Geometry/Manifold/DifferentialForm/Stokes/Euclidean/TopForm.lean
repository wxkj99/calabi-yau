module

public import CalabiYau.Geometry.Manifold.DifferentialForm.Stokes.Euclidean.CoordinateFlux
public import CalabiYau.Geometry.Manifold.DifferentialForm.Stokes.Euclidean.FluxSupport
public import CalabiYau.Geometry.Manifold.DifferentialForm.Stokes.Euclidean.CompactDivergence

@[expose] public section

open MeasureTheory

namespace ContinuousAlternatingMap

variable {n : ℕ}

/-- Euclidean compact-support Stokes in the standard oriented coordinates:
for an `n`-form on real `(n+1)`-space, the coefficient of its exact top form
has zero Lebesgue integral. This does not assert global manifold Stokes. -/
theorem integral_extDeriv_standardBasis_eq_zero
    {ω : (Fin (n + 1) → ℝ) →
      (Fin (n + 1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ}
    (hω : ContDiff ℝ 1 ω) (hcompact : HasCompactSupport ω) :
    ∫ x, extDeriv ω x (fun j : Fin (n + 1) =>
      (Pi.single j (1 : ℝ) : Fin (n + 1) → ℝ))
      ∂(volume : Measure (Fin (n + 1) → ℝ)) = 0 := by
  obtain ⟨hfluxDiff, hfluxCompact⟩ :=
    contDiff_hasCompactSupport_stokesCoordinateFlux hω hcompact
  calc
    _ = ∫ x, (∑ i : Fin (n + 1),
        fderiv ℝ (fun y => stokesCoordinateFlux ω y i) x
          (Pi.single i (1 : ℝ)))
        ∂(volume : Measure (Fin (n + 1) → ℝ)) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun x =>
            extDeriv_apply_standardBasis_eq_coordinateDivergence x
              (hω.differentiable (by norm_num) x))
    _ = 0 := MeasureTheory.integral_coordinateDivergence_eq_zero
      hfluxDiff hfluxCompact

end ContinuousAlternatingMap
