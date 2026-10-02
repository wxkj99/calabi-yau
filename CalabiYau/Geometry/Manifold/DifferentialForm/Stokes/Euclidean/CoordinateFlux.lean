module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic

@[expose] public section

namespace ContinuousAlternatingMap

variable {n : ℕ}

/-- The signed coordinate flux of an `n`-form on real `(n+1)`-space.
The coefficient of the omitted `i`-th coordinate vector has sign `(-1)^i`. -/
noncomputable def stokesCoordinateFlux
    (ω : (Fin (n + 1) → ℝ) →
      (Fin (n + 1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ) :
    (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ :=
  fun x i => (-1 : ℝ) ^ i.val *
    ω x (i.removeNth (fun j : Fin (n + 1) =>
      (Pi.single j (1 : ℝ) : Fin (n + 1) → ℝ)))

/-- The coordinate formula `dω(e₀,…,eₙ) = ∑ᵢ ∂ᵢ((-1)^i ω(e₀,…,êᵢ,…,eₙ))`.
In particular the index removed from the tuple and the derivative index are the same. -/
theorem extDeriv_apply_standardBasis_eq_coordinateDivergence
    {ω : (Fin (n + 1) → ℝ) →
      (Fin (n + 1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ}
    (x : Fin (n + 1) → ℝ) (hω : DifferentiableAt ℝ ω x) :
    extDeriv ω x (fun j : Fin (n + 1) =>
      (Pi.single j (1 : ℝ) : Fin (n + 1) → ℝ)) =
      ∑ i : Fin (n + 1),
        fderiv ℝ (fun y => stokesCoordinateFlux ω y i) x
          (Pi.single i (1 : ℝ)) := by
  rw [extDeriv_apply hω]
  dsimp only [stokesCoordinateFlux]
  simp [fderiv_const_mul, hω.continuousAlternatingMap_apply_const]

end ContinuousAlternatingMap
